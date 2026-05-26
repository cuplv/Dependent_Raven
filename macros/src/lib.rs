use proc_macro::TokenStream;
use quote::quote;
use syn::{parse_macro_input, ItemMod, Item, Meta};

#[proc_macro_attribute]
pub fn module(_attrs: TokenStream, input: TokenStream) -> TokenStream {
    let mut module = parse_macro_input!(input as ItemMod);
    
    let mut stmts = Vec::new();
    
    // 1. 모듈 레벨 속성 처리 (#[declare_types(..)])
    let mut new_attrs = Vec::new();
    for attr in module.attrs.drain(..) {
        if attr.path().is_ident("declare_types") {
            if let Meta::List(list) = &attr.meta {
                let tokens = &list.tokens;
                stmts.push(quote! {
                    let types_str = stringify!(#tokens);
                    for ty in types_str.split(',') {
                        let ty = ty.trim();
                        if !ty.is_empty() {
                            program.datatypes.insert(ty.to_string(), vec![]);
                        }
                    }
                });
            }
        } else {
            new_attrs.push(attr);
        }
    }
    module.attrs = new_attrs;

    if let Some((_, items)) = &mut module.content {
        let mut new_items = Vec::new();
        
        for mut item in items.drain(..) {
            
            match &mut item {
                Item::Fn(f) => {
                    let mut attrs_to_keep = Vec::new();
                    let mut is_declare = false;
                    let mut is_recursive = false;
                    let mut val_attr: Option<Option<proc_macro2::TokenStream>> = None;
                    let mut lemma_attr: Option<Option<proc_macro2::TokenStream>> = None;
                    
                    for attr in f.attrs.drain(..) {
                        if attr.path().is_ident("declare") {
                            is_declare = true;
                        } else if attr.path().is_ident("recursive") {
                            is_recursive = true;
                        } else if attr.path().is_ident("val") {
                            if let Meta::List(list) = &attr.meta {
                                val_attr = Some(Some(list.tokens.clone()));
                            } else {
                                val_attr = Some(None);
                            }
                        } else if attr.path().is_ident("lemma") {
                            if let Meta::List(list) = &attr.meta {
                                lemma_attr = Some(Some(list.tokens.clone()));
                            } else {
                                lemma_attr = Some(None);
                            }
                        } else {
                            attrs_to_keep.push(attr);
                        }
                    }
                    f.attrs = attrs_to_keep;
                    
                    let fn_name = f.sig.ident.to_string();
                    let fn_str = quote!(#f).to_string();
                    
                    if is_declare {
                        stmts.push(quote! {
                            frontend::api::register_declare(&mut program, #fn_name, #fn_str);
                        });
                    } else if let Some(tokens_opt) = val_attr {
                        let sig_str_opt = match tokens_opt {
                            Some(tokens) => {
                                let s = quote!(#tokens).to_string();
                                quote!(Some(#s))
                            },
                            None => quote!(None),
                        };
                        stmts.push(quote! {
                            frontend::api::register_val(&mut program, #fn_name, #sig_str_opt, #fn_str, #is_recursive);
                        });
                    } else if let Some(tokens_opt) = lemma_attr {
                        let sig_str_opt = match tokens_opt {
                            Some(tokens) => {
                                let s = quote!(#tokens).to_string();
                                quote!(Some(#s))
                            },
                            None => quote!(None),
                        };
                        stmts.push(quote! {
                            frontend::api::register_lemma(&mut program, #fn_name, #sig_str_opt, #fn_str, #is_recursive);
                        });
                    }
                },
                Item::Type(t) => {
                    let mut is_declare = false;
                    let mut attrs_to_keep = Vec::new();
                    for attr in t.attrs.drain(..) {
                        if attr.path().is_ident("declare") {
                            is_declare = true;
                        } else {
                            attrs_to_keep.push(attr);
                        }
                    }
                    t.attrs = attrs_to_keep;
                    
                    let type_name = t.ident.to_string();
                    if is_declare {
                        stmts.push(quote! {
                            program.datatypes.insert(#type_name.to_string(), vec![]);
                        });
                    }
                },
                Item::Enum(e) => {
                    let mut is_define = false;
                    let mut attrs_to_keep = Vec::new();
                    for attr in e.attrs.drain(..) {
                        if attr.path().is_ident("define") {
                            is_define = true;
                        } else {
                            attrs_to_keep.push(attr);
                        }
                    }
                    e.attrs = attrs_to_keep;
                    
                    let enum_name = e.ident.to_string();
                    let enum_str = quote!(#e).to_string();
                    
                    if is_define {
                        stmts.push(quote! {
                            frontend::api::register_enum(&mut program, #enum_name, #enum_str);
                        });
                    }
                },
                _ => {}
            }
            
            new_items.push(item);
        }
        
        *items = new_items;
    }
    
    // 원래 모듈의 이름을 가져와서 테스트 모듈 이름을 동적으로 생성합니다.
    let mod_name = &module.ident;
    let test_mod_name = syn::Ident::new(&format!("{}_tests", mod_name), mod_name.span());

    // 런타임에 실행될 #[test] 함수 생성 (모듈 바깥으로 뺌)
    let test_mod = quote! {
        #[cfg(test)]
        mod #test_mod_name {
            use super::*;
            
            #[test]
            fn check_properties() {
                let mut program = frontend::ast::Program {
                    datatypes: std::collections::HashMap::new(),
                    functions: std::collections::HashMap::new(),
                    goals: std::vec::Vec::new(),
                };
                
                #(#stmts)*
                
                // 백엔드 컴파일러 파이프라인 진입점 호출
                match backend::smt::encode_and_solve(program) {
                    Ok(_) => {}
                    Err(e) => {
                        let mut s = String::new();
                        s.push_str("\n\n#########[ verification failed ]#########\n");
                        s.push_str("##\n");
                        s.push_str(&format!("## > {}\n", e));
                        s.push_str("##\n");
                        s.push_str("#########################################\n\n");
                        
                        panic!("{}", s);
                    }
                }
            }
        }
    };

    // 원래 모듈(#module)과 테스트 모듈(#test_mod)을 나란히 배치
    quote! {
        #module
        #test_mod
    }.into()
}
