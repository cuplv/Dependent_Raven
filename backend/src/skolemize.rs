//! backend/src/skolemize.rs
//! Skolemization Pass
//!
//! [ENG] This pass traverses the negated verification condition (VC).
//!       Since the original VCs are universally quantified (Forall),
//!       the negated VC has existential quantifiers (Exists) at the top-levels 
//!       of its OR-branches. 
//!       This pass extracts all these Exists binders and pulls them to the 
//!       global scope to be declared as SMT constants (`declare-const`),
//!       effectively Skolemizing the formula. This is a crucial step for CEGQI,
//!       as manual instantiations must refer to these top-level Skolem constants.

use frontend::ast::{Expr, Ident, BaseType};

/// [ENG] Extracts all existential quantifiers from the expression and returns
///       a list of Skolem variables along with the quantifier-free expression.
pub fn skolemize_expr(expr: &Expr) -> (Vec<(Ident, BaseType)>, Expr) {
    let mut skolem_vars = Vec::new();
    let flat_expr = extract_exists(expr, &mut skolem_vars);
    (skolem_vars, flat_expr)
}

fn extract_exists(expr: &Expr, skolem_vars: &mut Vec<(Ident, BaseType)>) -> Expr {
    match expr {
        // [ENG] When an Exists node is found, collect its binders and bypass the node,
        //       recursively extracting from its body.
        Expr::Exists { binders, body } => {
            for b in binders {
                // [ENG] Check for name collisions. If users reuse variable names in different 
                //       Match branches, we only declare the SMT constant once.
                if !skolem_vars.iter().any(|(name, _)| name == &b.0) {
                    skolem_vars.push(b.clone());
                }
            }
            extract_exists(body, skolem_vars)
        }

        // [ENG] Recursively traverse the rest of the AST to find deep Exists nodes 
        //       (e.g., inside OR branches of the negated VC).
        Expr::BinOp { op, left, right } => {
            Expr::BinOp {
                op: op.clone(),
                left: Box::new(extract_exists(left, skolem_vars)),
                right: Box::new(extract_exists(right, skolem_vars)),
            }
        }
        Expr::UnOp { op, expr: inner } => {
            Expr::UnOp {
                op: op.clone(),
                expr: Box::new(extract_exists(inner, skolem_vars)),
            }
        }
        Expr::If { cond, then_expr, else_expr } => {
            Expr::If {
                cond: Box::new(extract_exists(cond, skolem_vars)),
                then_expr: Box::new(extract_exists(then_expr, skolem_vars)),
                else_expr: Box::new(extract_exists(else_expr, skolem_vars)),
            }
        }
        Expr::Let { pat, bound_expr, body } => {
            Expr::Let {
                pat: pat.clone(),
                bound_expr: Box::new(extract_exists(bound_expr, skolem_vars)),
                body: Box::new(extract_exists(body, skolem_vars)),
            }
        }
        Expr::Match { expr: target, arms } => {
            let new_arms = arms.iter().map(|(p, e)| {
                (p.clone(), extract_exists(e, skolem_vars))
            }).collect();
            Expr::Match {
                expr: Box::new(extract_exists(target, skolem_vars)),
                arms: new_arms,
            }
        }
        Expr::Forall { binders, body } => {
            Expr::Forall {
                binders: binders.clone(),
                body: Box::new(extract_exists(body, skolem_vars)),
            }
        }
        Expr::Tuple(elems) => {
            let new_elems = elems.iter().map(|e| extract_exists(e, skolem_vars)).collect();
            Expr::Tuple(new_elems)
        }
        Expr::Call { func, args } => {
            let new_args = args.iter().map(|e| extract_exists(e, skolem_vars)).collect();
            Expr::Call { func: func.clone(), args: new_args }
        }
        Expr::Constructor { name, args } => {
            let new_args = args.iter().map(|e| extract_exists(e, skolem_vars)).collect();
            Expr::Constructor { name: name.clone(), args: new_args }
        }
        Expr::ApplyRel { relation, args } => {
            let new_args = args.iter().map(|e| extract_exists(e, skolem_vars)).collect();
            Expr::ApplyRel { relation: relation.clone(), args: new_args }
        }
        Expr::Instantiate(inner) => {
            Expr::Instantiate(Box::new(extract_exists(inner, skolem_vars)))
        }
        Expr::ExistentialBindings(bindings) => {
            let new_bindings = bindings.iter().map(|(id, e)| {
                (id.clone(), extract_exists(e, skolem_vars))
            }).collect();
            Expr::ExistentialBindings(new_bindings)
        }

        // [ENG] Leaf nodes are returned as-is.
        Expr::BoolConst(_) | Expr::Var(_) => {
            expr.clone()
        }
    }
}