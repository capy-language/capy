extern crate proc_macro;
use std::{fs, path::PathBuf, str::FromStr};

use litrs::StringLit;
use proc_macro::TokenStream;
use quote::{format_ident, quote, quote_spanned};

enum EnumTy {
    Full,
    Stripped,
}

/// We have to maintain two different Token enums across two different crates
/// (one in the lexer crate and one in the syntax crate),
/// and we also need to be able to transmute these enums.
/// 
/// So this is a proc macro that can easily generate these enums for us from a `.lex` file,
/// ensuring that they are transmutable
#[proc_macro]
pub fn define_token_enum(input: TokenStream) -> TokenStream {
    let input = input.into_iter().collect::<Vec<_>>();
    if input.len() != 5 {
        let msg = format!("expected exactly five input tokens, got {}", input.len());
        return quote! { compile_error!(#msg) }.into();
    }

    let enum_name = match &input[0] {
        proc_macro::TokenTree::Ident(ident) => ident.to_string(),
        other => {
            let msg = format!("expected the first token to be an ident, not {:?}", other);
            return quote_spanned! { input[0].span().into() => compile_error!(#msg) }.into();
        }
    };
    let enum_name = format_ident!("{}", enum_name);

    match &input[1] {
        proc_macro::TokenTree::Punct(punct) if punct.as_char() == ',' => {}
        other => {
            let msg = format!("expected an `,`, not {:?}", other);
            return quote_spanned! { input[1].span().into() => compile_error!(#msg) }.into();
        }
    }

    let enum_ty = match &input[2] {
        proc_macro::TokenTree::Ident(ident) => ident.to_string(),
        other => {
            let msg = format!("expected an ident, not {:?}", other);
            return quote_spanned! { input[2].span().into() => compile_error!(#msg) }.into();
        }
    };
    let enum_ty = match enum_ty.as_str() {
        "full" => EnumTy::Full,
        "stripped" => EnumTy::Stripped,
        other => {
            let msg = format!("expected `full` or `stripped`, not {}", other);
            return quote_spanned! { input[2].span().into() => compile_error!(#msg) }.into();
        }
    };

    match &input[3] {
        proc_macro::TokenTree::Punct(punct) if punct.as_char() == ',' => {}
        other => {
            let msg = format!("expected an `,`, not {:?}", other);
            return quote_spanned! { input[3].span().into() => compile_error!(#msg) }.into();
        }
    }

    let string_lit = match StringLit::try_from(&input[4]) {
        Ok(lit) => lit,
        Err(err) => return err.to_compile_error(),
    };

    let path = match PathBuf::from_str(string_lit.value()) {
        Ok(file_name) => file_name,
        Err(why) => {
            let msg = format!("{}: {}", string_lit.value(), why);
            return quote_spanned! {
                input[4].span().into() => compile_error!(#msg)
            }
            .into();
        }
    };

    // this removes differences between testing and non-testing
    let _ = std::env::set_current_dir(env!("CARGO_MANIFEST_DIR"));

    let file = match fs::read_to_string(&path) {
        Ok(file) => file,
        Err(why) => {
            let msg = format!("{}: {}", path.display(), why);
            return quote_spanned! {
                input[4].span().into() => compile_error!(#msg)
            }
            .into();
        }
    };

    let mut at_end = false;
    let mut entries = quote!();
    for line in file
        .lines()
        .filter(|line| !line.is_empty() && !line.starts_with("//"))
    {
        let parts = line.splitn(3, ' ').collect::<Vec<_>>();
        if parts.len() != 1 && parts.len() != 3 {
            let msg = format!("`{}` not one or three parts", line);
            return quote_spanned! {
                input[4].span().into() => compile_error!(#msg)
            }
            .into();
        }

        let name = format_ident!("{}", parts[0]);

        if parts[0].starts_with("__") {
            at_end = true
        } else if at_end {
            return quote_spanned! {
                input[4].span().into() => compile_error!("Tokens that start with `__` must be at the very end of the file")
            }
            .into();
        }

        match enum_ty {
            EnumTy::Full if parts.len() == 3 => {
                let equals = parts[1];
                if equals != "=" {
                    let msg = format!("expected equals sign, found `{}`", equals);
                    return quote_spanned! {
                        input[4].span().into() => compile_error!(#msg)
                    }
                    .into();
                }
                let value = parts[2].trim();
                let docs = format!("represents `{}`", value);

                let tag = if value.starts_with('/') {
                    let regex = value
                        .strip_prefix('/')
                        .unwrap()
                        .strip_suffix('/')
                        .unwrap()
                        .replace("\\r", "\r")
                        .replace("\\n", "\n");

                    quote! {
                        #[doc = #docs]
                        #[regex(#regex)]
                    }
                } else if value.starts_with('\'') {
                    let token = value
                        .strip_prefix('\'')
                        .unwrap()
                        .strip_suffix('\'')
                        .unwrap()
                        .replace("\\r", "\r")
                        .replace("\\n", "\n");

                    quote! {
                        #[doc = #docs]
                        #[token(#token)]
                    }
                } else if value == "!" {
                    quote! {
                        #[doc = "represents an error value"]
                        #[error]
                    }
                } else {
                    let msg = format!("expected regex, token, or `!`, but found {}", value);
                    return quote_spanned! {
                        input[4].span().into() => compile_error!(#msg)
                    }
                    .into();
                };
                entries.extend(quote! {
                    #tag
                    #name,
                });
            }
            EnumTy::Full => {
                entries.extend(quote! {
                    #[doc = "custom defined token"]
                    #name,
                });
            }
            EnumTy::Stripped => {
                let tag = if parts.len() == 3 {
                    let value = parts[2].trim();

                    let doc = if value == "!" {
                        "represents an error value".to_string()
                    } else {
                        format!("represents `{}`", value)
                    };
                    quote! {
                        #[doc = #doc]
                    }
                } else {
                    quote! {
                        #[doc = "custom defined token"]
                    }
                };

                if parts[0].starts_with("__") {
                    continue;
                } else if parts[0].starts_with('_') {
                    let name = format_ident!("{}", parts[0].strip_prefix('_').unwrap());
                    entries.extend(quote! {
                        #tag
                        #name,
                    });
                } else {
                    entries.extend(quote! {
                        #tag
                        #name,
                    });
                }
            }
        }
    }

    let derive = match enum_ty {
        EnumTy::Full => quote! {
            #[derive(Debug, Copy, Clone, PartialEq, Logos)]
        },
        EnumTy::Stripped => quote! {
            #[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
        },
    };

    quote! {
        #derive
        pub enum #enum_name {
            #entries
        }
    }
    .into()
}

#[proc_macro]
pub fn define_token_set(input: TokenStream) -> TokenStream {
    let input = input.into_iter().collect::<Vec<_>>();
    if input.len() != 1 {
        let msg = format!("expected exactly one input token, got {}", input.len());
        return quote! { compile_error!(#msg) }.into();
    }

    let string_lit = match StringLit::try_from(&input[0]) {
        Ok(lit) => lit,
        Err(err) => return err.to_compile_error(),
    };

    let path = match PathBuf::from_str(string_lit.value()) {
        Ok(file_name) => file_name,
        Err(why) => {
            let msg = format!("{}: {}", string_lit.value(), why);
            return quote_spanned! {
                input[0].span().into() => compile_error!(#msg)
            }
            .into();
        }
    };

    // this removes differences between testing and non-testing
    let _ = std::env::set_current_dir(env!("CARGO_MANIFEST_DIR"));

    let file = match fs::read_to_string(&path) {
        Ok(file) => file,
        Err(why) => {
            let msg = format!("{}: {}", path.display(), why,);
            return quote_spanned! {
                input[0].span().into() => compile_error!(#msg)
            }
            .into();
        }
    };

    let number_of_tokens = file
        .lines()
        .filter(|line| !line.is_empty() && !line.starts_with("//"))
        .count();

    const INT_SIZES: &[(usize, &str)] = &[
        (8, "u8"),
        (16, "u16"),
        (32, "u32"),
        (64, "u64"),
        (128, "u128"),
    ];

    let (_, ty_name) = match INT_SIZES
        .iter()
        .filter_map(|(bit_width, ty_name)| {
            bit_width
                .checked_sub(number_of_tokens)
                .map(|diff| (diff, ty_name))
        })
        .min_by_key(|(difference, _)| *difference)
    {
        Some(result) => result,
        None => {
            let msg = format!("There are {} different tokens in {}, but rust's maximum int type is u128. Not all tokens can be covered in TokenSet", number_of_tokens, path.display());
            return quote_spanned! {
                input[0].span().into() => compile_error!(#msg)
            }
            .into();
        }
    };

    let ty_name = format_ident!("{}", ty_name);

    quote! {
        #[derive(Debug, Clone, Copy)]
        pub(crate) struct TokenSet(#ty_name);

        impl TokenSet {
            pub(crate) const ALL: Self = Self(#ty_name::MAX);
            pub(crate) const NONE: Self = Self(0);
        }

        const fn mask(kind: TokenKind) -> #ty_name {
            1 << kind as #ty_name
        }
    }
    .into()
}
