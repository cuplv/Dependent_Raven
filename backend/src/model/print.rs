//! backend/src/model/print.rs
//! [KOR] 모델을 CamlStar의 `cex.ml`이 출력하는 것과 같은 JSON으로 씁니다:
//!       sort별 우주, 프로그램 변수의 값, 관계별 유한 맵.
//! [ENG] Renders a model as the JSON CamlStar's `cex.ml` prints, section by
//!       section: each datatype's universe, each program variable's element,
//!       and each relation as a finite map `"(args)": "result"` under its
//!       source name. Elements are displayed by `name::tags_only`.

use super::name::{tags_only, Names};
use super::Model;
use crate::smt::builder::{render_sort, sanitize_id};
use crate::smt::get_fun_types;
use frontend::ast::{BaseType, Ident, Program};

/// [ENG] The three sections as one JSON object. `variables` are the goal's
///       binders (the counterexample's own skolems); Unit-typed plumbing and the
///       subtyping variable are left out, as they are not program variables.
pub fn camlstar_json(model: &Model, program: &Program, variables: &[(Ident, BaseType)]) -> String {
    let names = tags_only(model, program);
    let mut items: Vec<String> = Vec::new();

    // 1. universes, one per datatype (declared sorts included), in name order
    let mut datatypes: Vec<_> = program.datatypes.iter().collect();
    datatypes.sort_by(|a, b| a.0.cmp(b.0));
    for (enum_name, _) in &datatypes {
        let sort = render_sort(&BaseType::Custom((*enum_name).clone()));
        if let Some(universe) = model.universes.get(&sort) {
            let elems: Vec<String> = universe.iter().map(|e| quoted(&names.get(e))).collect();
            items.push(format!("  {}: [{}]", quoted(enum_name), elems.join(", ")));
        }
    }

    // 2. program variables
    for (name, ty) in variables {
        if *ty == BaseType::Unit || name == "v_sub" {
            continue;
        }
        if let Some(elem) = model.consts.get(&sanitize_id(name)) {
            items.push(format!("  {}: {}", quoted(name), quoted(&names.get(elem))));
        }
    }

    // 3. relations: user functions under their names, constructors under theirs
    let mut relations: Vec<(String, String)> = Vec::new(); // (display name, SMT relation)
    let mut functions: Vec<_> = program.functions.iter().collect();
    functions.sort_by(|a, b| a.0.cmp(b.0));
    for (fn_name, def) in functions {
        if get_fun_types(&def.signature).1 == BaseType::Unit {
            continue; // a lemma's relation carries no information
        }
        relations.push((fn_name.clone(), format!("{}_rel", fn_name)));
    }
    for (enum_name, variants) in &datatypes {
        for (variant, fields) in variants.iter() {
            if !fields.is_empty() {
                relations.push((variant.clone(), sanitize_id(&format!("{}::{}_rel", enum_name, variant))));
            }
        }
    }
    for (display, relation) in relations {
        let Some(table) = model.rels.get(&relation) else { continue };
        let entries: Vec<String> = table
            .entries
            .iter()
            .filter(|(_, v)| v == "true")
            .map(|(tuple, _)| {
                let (result, args) = tuple.split_last().expect("a relation has a result column");
                format!("    {}: {}", quoted(&key_string(args, &names)), quoted(&names.get(result)))
            })
            .collect();
        if !entries.is_empty() {
            items.push(format!("  {}: {{\n{}\n  }}", quoted(&display), entries.join(",\n")));
        }
    }

    if items.is_empty() {
        "{}".to_string()
    } else {
        format!("{{\n{}\n}}", items.join(",\n"))
    }
}

/// [ENG] CamlStar's key form: a single argument bare, several as `(a, b)`.
fn key_string(args: &[String], names: &Names) -> String {
    let parts: Vec<String> = args.iter().map(|a| names.get(a)).collect();
    match parts.as_slice() {
        [one] => one.clone(),
        many => format!("({})", many.join(", ")),
    }
}

fn quoted(s: &str) -> String {
    let mut out = String::from("\"");
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            c => out.push(c),
        }
    }
    out.push('"');
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::model::Table;
    use std::collections::HashMap;

    #[test]
    fn prints_universes_variables_and_relations_like_camlstar() {
        let mut program = Program { datatypes: HashMap::new(), functions: HashMap::new(), goals: Vec::new() };
        frontend::api::register_enum(&mut program, "Peano", "enum Peano { Zero, Succ(Box<Peano>) }");
        frontend::api::register_val(
            &mut program,
            "twice",
            None,
            "fn twice(n: Peano) -> Peano { Peano::Succ(Box::new(Peano::Succ(Box::new(n)))) }",
            false,
        );
        let peano = render_sort(&BaseType::Custom("Peano".into()));
        let e: Vec<String> = (0..3).map(|k| format!("{}!val!{}", peano, k)).collect();

        let mut m = Model::default();
        m.universes.insert(peano.clone(), e.clone());
        m.consts.insert(sanitize_id("Peano::Zero"), e[0].clone());
        m.consts.insert("n".to_string(), e[1].clone());
        m.rels.insert(
            sanitize_id("Peano::Succ_rel"),
            Table { entries: vec![(vec![e[0].clone(), e[1].clone()], "true".into())], else_value: Some("false".into()) },
        );
        m.rels.insert(
            "twice_rel".to_string(),
            Table { entries: vec![(vec![e[1].clone(), e[2].clone()], "true".into())], else_value: Some("false".into()) },
        );

        let json = camlstar_json(&m, &program, &[("n".to_string(), BaseType::Custom("Peano".into())), ("v_sub".to_string(), BaseType::Unit)]);
        let expected = "{\n  \"Peano\": [\"Zero\", \"Peano!1\", \"Peano!2\"],\n  \"n\": \"Peano!1\",\n  \"twice\": {\n    \"Peano!1\": \"Peano!2\"\n  },\n  \"Succ\": {\n    \"Zero\": \"Peano!1\"\n  }\n}";
        assert_eq!(json, expected);
    }
}
