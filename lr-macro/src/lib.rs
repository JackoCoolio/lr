#![allow(unused)]

use proc_macro::{Ident, TokenStream};
use proc_macro2::Literal;
use syn::{
    braced,
    parse::Parse,
    parse_macro_input,
    punctuated::{self, Punctuated},
    DataEnum, DeriveInput, LitStr, Token,
};

#[proc_macro_derive(Nonterminal)]
pub fn nonterminal_derive_macro(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let DeriveInput { ident, data, .. } = parse_macro_input!(input);

    let syn::Data::Enum(DataEnum { variants, .. }) = data else {
        panic!("`Nonterminal` can only be derived on enums");
    };

    let mut annotated = None;

    for variant in variants.iter() {
        for attr in variant.attrs.iter() {
            let Some(ident) = attr.path().get_ident() else {
                continue;
            };

            if *ident == "start" {
                if annotated.is_some() {
                    panic!("only one nonterminal can be marked as the start nonterminal")
                }
                annotated = Some(variant.ident.clone());
            }
        }
    }

    let annotated =
        annotated.expect("mark a variant with `#[start]` to use it as the start nonterminal");

    quote::quote! {
        impl lr::lang::Nonterminal for #ident {
            fn start() -> #ident {
                #ident::#annotated
            }
        }
    }
    .into()
}

pub(crate) mod kw {
    syn::custom_keyword!(terminals);
}

struct GrammarData {
    nonterminals: Vec<Ident>,
    terminals: Vec<Ident>,
}

impl Parse for GrammarData {
    fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
        let mut data = GrammarData {
            terminals: Vec::new(),
            nonterminals: Vec::new(),
        };

        loop {
            if !parse_section(&mut data, &input)? {
                break;
            }
        }

        Ok(data)
    }
}

fn parse_section(
    grammar_data: &mut GrammarData,
    input: &syn::parse::ParseStream,
) -> syn::Result<bool> {
    if input.is_empty() {
        return Ok(false);
    }

    let lookahead = input.lookahead1();
    if lookahead.peek(kw::terminals) {
        input.parse::<kw::terminals>()?;
        let content;
        braced!(content in input);
        parse_terminals_section(grammar_data, &&content)?;
        Ok(true)
    } else {
        unimplemented!()
    }
}

fn parse_terminals_section(
    grammar_data: &mut GrammarData,
    input: &syn::parse::ParseStream,
) -> syn::Result<Punctuated<TerminalDecl, Token![,]>> {
    Punctuated::<TerminalDecl, Token![,]>::parse_terminated(input)
}

struct TerminalDecl {
    ident: proc_macro2::Ident,
    colon: Token![:],
    kind: TerminalDeclKind,
}

enum TerminalDeclKind {
    StringLiteral(LitStr),
}

impl Parse for TerminalDecl {
    fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
        let lookahead = input.lookahead1();
        let ident = input.parse::<proc_macro2::Ident>()?;
        let colon = input.parse::<Token![:]>()?;
        if lookahead.peek(LitStr) {
            let lit = input.parse::<LitStr>()?;
            Ok(TerminalDecl {
                ident,
                colon,
                kind: TerminalDeclKind::StringLiteral(lit),
            })
        } else {
            unimplemented!()
        }
    }
}

enum ParseExpectation {
    NonterminalIdentifier,
    CloseParen,
    DeclareEquals,
}

#[proc_macro]
pub fn grammar(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    grammar_impl(input)
}

fn grammar_impl(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let grammar_data: GrammarData = parse_macro_input!(input);

    codegen(grammar_data)
}

fn codegen(grammar_data: GrammarData) -> proc_macro::TokenStream {
    quote::quote! {
        fn foo() {}
    }
    .into()
}

/// Generates the Nonterminal and Terminal enum
fn enum_codegen(
    ident: proc_macro2::Ident,
    variants: &[proc_macro2::Ident],
) -> proc_macro2::TokenStream {
    let iter = variants.iter();
    quote::quote! {
        enum #ident {
            #(#iter,)*
        }
    }
}
