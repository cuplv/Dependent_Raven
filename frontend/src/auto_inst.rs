//! frontend/src/auto_inst.rs
//! Automatic Quantifier Instantiation Engine (CEGQI Collector)
//!
//! [ENG] This module implements the AST traversal logic to automatically find and collect
//!       all ground terms (function calls and constructor applications) present in the 
//!       logical context and expected target of a VC.
//!       These collected terms are then automatically pushed as instantiation hints to the SMT solver,
//!       achieving completeness as described in the CEGQI paper without manual `instantiate!` annotations.

use std::collections::HashSet;
use crate::ast::{Expr, Ident, Pattern};

/// [ENG] Recursively traverses an expression and collects all safe ground terms.
///       A ground term is considered "safe" if it does NOT contain any variables 
///       that are locally bound by quantifiers (Forall/Exists) or local bindings (Let/Match) 
///       within this specific expression.
pub fn collect_ground_terms(expr: &Expr) -> Vec<Expr> {
    let mut collected = Vec::new();
    let blacklist = HashSet::new();
    collect_rec(expr, &blacklist, &mut collected);
    collected
}

/// [ENG] Internal recursive collector.
fn collect_rec(expr: &Expr, blacklist: &HashSet<Ident>, collected: &mut Vec<Expr>) {
    match expr {
        // [ENG] 1. Target Nodes: Function Calls and Constructors
        Expr::Call { args, .. } | Expr::Constructor { args, .. } => {
            // [ENG] First, collect terms from arguments (Bottom-Up collection)
            for arg in args {
                collect_rec(arg, blacklist, collected);
            }

            // [ENG] Skip empty constructors (e.g., Nat::Z) since they don't need totality instantiations.
            if let Expr::Constructor { args, .. } = expr {
                if args.is_empty() {
                    return;
                }
            }

            // [ENG] If the term contains ANY blacklisted (locally bound) variables, we MUST NOT extract it.
            //       Pulling a locally bound variable to the global instantiation list would cause
            //       an "unknown constant" error in the SMT solver.
            if !contains_blacklisted_var(expr, blacklist) {
                // [ENG] Avoid duplicates to keep the SMT query lean.
                if !collected.contains(expr) {
                    collected.push(expr.clone());
                }
            }
        }

        // [ENG] 2. Scoping Nodes: Forall, Exists, Let, Match
        //       We must add the newly bound variables to the blacklist before exploring their bodies.
        Expr::Forall { binders, body } | Expr::Exists { binders, body } => {
            let mut new_blacklist = blacklist.clone();
            for (name, _) in binders {
                new_blacklist.insert(name.clone());
            }
            collect_rec(body, &new_blacklist, collected);
        }
        Expr::Let { pat, bound_expr, body } => {
            // [ENG] The bound expression evaluates in the outer scope
            collect_rec(bound_expr, blacklist, collected);
            
            // [ENG] The body evaluates in the inner scope
            let mut new_blacklist = blacklist.clone();
            add_pat_vars_to_blacklist(pat, &mut new_blacklist);
            collect_rec(body, &new_blacklist, collected);
        }
        Expr::Match { expr: target, arms } => {
            collect_rec(target, blacklist, collected);
            for (pat, arm_expr) in arms {
                let mut new_blacklist = blacklist.clone();
                add_pat_vars_to_blacklist(pat, &mut new_blacklist);
                collect_rec(arm_expr, &new_blacklist, collected);
            }
        }

        // [ENG] 3. Transparent Nodes: Just traverse their children
        Expr::Tuple(elems) => {
            for e in elems { collect_rec(e, blacklist, collected); }
        }
        Expr::BinOp { left, right, .. } => {
            collect_rec(left, blacklist, collected);
            collect_rec(right, blacklist, collected);
        }
        Expr::UnOp { expr: inner, .. } => {
            collect_rec(inner, blacklist, collected);
        }
        Expr::If { cond, then_expr, else_expr } => {
            collect_rec(cond, blacklist, collected);
            collect_rec(then_expr, blacklist, collected);
            collect_rec(else_expr, blacklist, collected);
        }
        Expr::ApplyRel { args, .. } => {
            for arg in args { collect_rec(arg, blacklist, collected); }
        }
        Expr::Instantiate(inner) => {
            collect_rec(inner, blacklist, collected);
        }
        Expr::ExistentialBindings(bindings) => {
            for (_, e) in bindings { collect_rec(e, blacklist, collected); }
        }

        // [ENG] 4. Leaf Nodes: Do nothing
        Expr::BoolConst(_) | Expr::Var(_) => {}
    }
}

/// [ENG] Helper function to recursively add all variables defined in a pattern to the blacklist.
fn add_pat_vars_to_blacklist(pat: &Pattern, blacklist: &mut HashSet<Ident>) {
    match pat {
        Pattern::Ident(name) => { 
            blacklist.insert(name.clone()); 
        }
        Pattern::Constructor(_, args) | Pattern::Tuple(args) => {
            for a in args { 
                add_pat_vars_to_blacklist(a, blacklist); 
            }
        }
        Pattern::Wildcard => {}
    }
}

/// [ENG] Deeply checks if an expression contains ANY variable present in the blacklist.
fn contains_blacklisted_var(expr: &Expr, blacklist: &HashSet<Ident>) -> bool {
    if blacklist.is_empty() { return false; }
    
    match expr {
        Expr::Var(name) => blacklist.contains(name),
        Expr::Tuple(elems) => elems.iter().any(|e| contains_blacklisted_var(e, blacklist)),
        Expr::BinOp { left, right, .. } => {
            contains_blacklisted_var(left, blacklist) || contains_blacklisted_var(right, blacklist)
        }
        Expr::UnOp { expr: inner, .. } => contains_blacklisted_var(inner, blacklist),
        Expr::If { cond, then_expr, else_expr } => {
            contains_blacklisted_var(cond, blacklist) || 
            contains_blacklisted_var(then_expr, blacklist) || 
            contains_blacklisted_var(else_expr, blacklist)
        }
        Expr::Let { bound_expr, body, .. } => {
            contains_blacklisted_var(bound_expr, blacklist) || contains_blacklisted_var(body, blacklist)
        }
        Expr::Match { expr: target, arms } => {
            contains_blacklisted_var(target, blacklist) || 
            arms.iter().any(|(_, e)| contains_blacklisted_var(e, blacklist))
        }
        Expr::Call { args, .. } | Expr::Constructor { args, .. } | Expr::ApplyRel { args, .. } => {
            args.iter().any(|e| contains_blacklisted_var(e, blacklist))
        }
        Expr::Forall { body, .. } | Expr::Exists { body, .. } => {
            contains_blacklisted_var(body, blacklist)
        }
        Expr::Instantiate(inner) => contains_blacklisted_var(inner, blacklist),
        Expr::ExistentialBindings(bindings) => {
            bindings.iter().any(|(_, e)| contains_blacklisted_var(e, blacklist))
        }
        Expr::BoolConst(_) => false,
    }
}