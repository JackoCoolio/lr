#![allow(unused)]

use proc_macro2::{Ident, Literal, Span, TokenStream};
use syn::{
    braced,
    parse::Parse,
    parse_macro_input,
    punctuated::{self, Punctuated},
    DataEnum, DeriveInput, ExprClosure, LitStr, Pat, PatIdent, Token,
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
#[proc_macro]
pub fn grammar(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    grammar_impl(input)
}

pub(crate) mod kw {
    syn::custom_keyword!(terminals);
    syn::custom_keyword!(rules);
}

struct GrammarData {
    nonterminals: Vec<Ident>,
    token_struct_ident: Ident,
    terminal_enum_ident: Ident,
    terminals: Vec<TerminalDecl>,
    rules: Vec<RuleDecl>,
}

impl Parse for GrammarData {
    fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
        let mut data = GrammarData {
            nonterminals: Vec::new(),
            token_struct_ident: Ident::new("Token", Span::call_site()),
            terminal_enum_ident: Ident::new("Terminal", Span::call_site()),
            terminals: Vec::new(),
            rules: Vec::new(),
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
        panic!("unexpected token {:?}", input.span().source_text().unwrap());
    }
}

fn parse_terminals_section(
    grammar_data: &mut GrammarData,
    input: &syn::parse::ParseStream,
) -> syn::Result<()> {
    let terminal_decls = Punctuated::<TerminalDecl, Token![,]>::parse_terminated(input)?;

    grammar_data.terminals = terminal_decls.into_iter().collect();

    Ok(())
}

fn parse_rules_section(
    grammar_data: &mut GrammarData,
    input: &syn::parse::ParseStream,
) -> syn::Result<()> {
    let rules = Punctuated::<RuleDecl, Token![;]>::parse_terminated(input)?;

    grammar_data.rules = rules.into_iter().collect();

    Ok(())
}

/*
X = A B C;
*/

struct RuleDecl {
    ident: Ident,
}

impl Parse for RuleDecl {
    fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
        let rule_ident = input.parse::<Ident>()?;
        input.parse::<Token![=]>()?;
        input.peek()
    }
}

struct TerminalDecl {
    ident: proc_macro2::Ident,
    colon: Token![:],
    kind: TerminalDeclKind,
}

enum TerminalDeclKind {
    StringLiteral(LitStr),
    ParseFunction { closure: ExprClosure },
}

impl Parse for TerminalDecl {
    fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
        let ident = input.parse::<proc_macro2::Ident>()?;
        println!("{:?}", ident);
        let colon = input.parse::<Token![:]>()?;
        let lookahead = input.lookahead1();
        if lookahead.peek(LitStr) {
            let lit = input.parse::<LitStr>()?;
            Ok(TerminalDecl {
                ident,
                colon,
                kind: TerminalDeclKind::StringLiteral(lit),
            })
        } else if lookahead.peek(Token![|]) {
            let closure = input.parse::<ExprClosure>()?;
            Ok(TerminalDecl {
                ident,
                colon,
                kind: TerminalDeclKind::ParseFunction { closure },
            })
        } else {
            unimplemented!("only literal string and closure terminal declarations supported");
        }
    }
}

fn grammar_impl(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let grammar_data: GrammarData = parse_macro_input!(input);

    let code = codegen(grammar_data).into();
    println!("{:?}", code);
    code
}

/*
mod grammar {
    enum Terminal {
        ...,
        INVALID,
    }

    mod terminal_parsers {
        pub(super) fn PLUS(input: &str) -> nom::IResult<&str, Terminal> {
            let (input, _) = tag("+")(input)?;
            Ok((input, super::Terminal::PLUS))
        }
    }

    fn token(input: &str) -> nom::IResult<&str, Token> {
        let (input, _) = nom::bytes::complete::take_while(is_whitespace)(input)?;

        if input.is_empty() {
            return Err(nom::Err::Error(nom::error::Error {
                input,
                code: nom::error::ErrorKind::Eof,
            }));
        }

        let parsers = [
            terminal_parsers::PLUS,
        ];

        let mut longest_token: Option<(&str, Token)> = None;
        for parser in parsers {
            let longest_len = longest_token.as_ref().map(|tok| tok.1.span.len()).unwrap_or(0);
            let Ok(res) = parser(input) else {
                continue;
            };
            if res.1.span.len() > longest_len {
                longest_len = Some(res);
            }
        }

        Ok(longest_token.unwrap_or((
            &input[1..],
            Token {
                kind: Terminal::INVALID,
                span: &input[0..1],
            }
        )))
    }

    enum Nonterminal {
        ...
    }

    struct Token<'input> {
        span: &'input str,
        kind: Terminal,
    }
}
*/

fn codegen(grammar_data: GrammarData) -> proc_macro2::TokenStream {
    let mut token_stream = proc_macro2::TokenStream::new();

    let terminals_enum = enum_codegen(
        &grammar_data.terminal_enum_ident,
        grammar_data
            .terminals
            .iter()
            .map(|decl| &decl.ident)
            .chain(std::iter::once(&Ident::new("INVALID", Span::call_site())))
            .chain(std::iter::once(&Ident::new("EOF", Span::call_site()))),
    );

    token_stream.extend(terminals_enum);

    let parsers = parsers_codegen(&grammar_data.terminal_enum_ident, &grammar_data.terminals);
    token_stream.extend(quote::quote! {
        pub mod parsers {
            use super::*;
            #parsers
        }
    });

    token_stream.extend(token_parser_codegen(
        &grammar_data.terminal_enum_ident,
        &grammar_data.token_struct_ident,
        grammar_data.terminals.iter().map(|decl| &decl.ident),
    ));

    token_stream.extend(token_struct_codegen(
        &grammar_data.token_struct_ident,
        &grammar_data.terminal_enum_ident,
    ));

    token_stream.extend(lexer_codegen(
        &grammar_data.terminal_enum_ident,
        &grammar_data.token_struct_ident,
    ));

    quote::quote! {
        mod grammar {
            use super::*;
            #token_stream
        }
    }
}

fn token_struct_codegen(token_struct_ident: &Ident, terminal_enum_ident: &Ident) -> TokenStream {
    quote::quote! {
        pub struct #token_struct_ident<'input> {
            span: &'input str,
            kind: #terminal_enum_ident,
        }
    }
}

/// Generates the Nonterminal and Terminal enum
fn enum_codegen<'i>(
    ident: &proc_macro2::Ident,
    variants: impl Iterator<Item = &'i proc_macro2::Ident>,
) -> proc_macro2::TokenStream {
    quote::quote! {
        pub enum #ident {
            #(#variants,)*
        }
    }
}

fn lexer_codegen(terminal_enum_ident: &Ident, token_struct_ident: &Ident) -> TokenStream {
    quote::quote! {
        pub struct Lexer<'input> {
            input: &'input str,
            eof: bool,
        }

        impl<'i> Lexer<'i> {
            pub fn new(input: &'i str) -> Self {
                Self { input, eof: false }
            }
        }

        impl<'i> Iterator for Lexer<'i> {
            type Item = #token_struct_ident<'i>;

            fn next(&mut self) -> Option<Self::Item> {
                if self.eof {
                    return None;
                }

                let Ok((input, tok)) = token(self.input) else {
                    self.eof = true;
                    return Some(#token_struct_ident {
                        kind: #terminal_enum_ident::EOF,
                        span: self.input,
                    });
                };

                self.input = input;

                Some(tok)
            }
        }
    }
}

fn token_parser_codegen<'i>(
    terminal_enum_ident: &Ident,
    token_struct_ident: &Ident,
    terminal_idents: impl Iterator<Item = &'i proc_macro2::Ident>,
) -> TokenStream {
    quote::quote! {
        fn is_whitespace(c: char) -> bool {
            matches! {
                c,
                ' '          // space
                | '\t'       // horizontal tab
                | '\n'       // LF
                | '\r'       // CR
                | '\u{000B}' // vertical tab
                | '\u{000C}' // form feed
            }
        }

        pub fn token_kind(input: &str) -> nom::IResult<&str, #terminal_enum_ident> {
            let parsers = [
                #(parsers::#terminal_idents,)*
            ];

            let mut longest_token: Option<(&str, #terminal_enum_ident)> = None;
            for parser in parsers {
                let longest_len = longest_token.as_ref().map(|tok| input.len() - tok.0.len()).unwrap_or(0);
                let Ok(res) = parser(input) else {
                    continue;
                };
                let token_len = input.len() - res.0.len();
                if token_len > longest_len {
                    longest_token = Some(res);
                }
            }

            Ok(longest_token.unwrap_or((
                &input[1..],
                #terminal_enum_ident::INVALID,
            )))
        }

        pub fn token(original_input: &str) -> nom::IResult<&str, #token_struct_ident> {
            let (original_input, _) = ::nom::bytes::complete::take_while(is_whitespace)(original_input)?;

            if original_input.is_empty() {
                return Err(::nom::Err::Error(::nom::error::Error {
                    input: original_input,
                    code: ::nom::error::ErrorKind::Eof,
                }));
            }

            let (input, kind) = token_kind(original_input)?;
            let len = original_input.len() - input.len();
            let span = &original_input[0..len];
            Ok((input, #token_struct_ident {
                kind,
                span,
            }))
        }
    }
}

fn parsers_codegen(terminal_enum_ident: &Ident, terminal_decls: &[TerminalDecl]) -> TokenStream {
    let mut token_stream = TokenStream::new();

    for decl in terminal_decls {
        token_stream.extend(parser_codegen(terminal_enum_ident, decl));
    }

    token_stream
}

fn parser_codegen(terminal_enum_ident: &Ident, terminal_decl: &TerminalDecl) -> TokenStream {
    let ident = &terminal_decl.ident;

    match &terminal_decl.kind {
        TerminalDeclKind::StringLiteral(litstr) => {
            litstr_parser_codegen(terminal_enum_ident, ident, litstr)
        }
        TerminalDeclKind::ParseFunction { closure } => {
            parsefn_parser_codegen(terminal_enum_ident, ident, closure)
        }
    }
}

fn parsefn_parser_codegen(
    terminal_enum_ident: &Ident,
    ident: &Ident,
    closure: &ExprClosure,
) -> TokenStream {
    if closure.inputs.len() != 1 {
        panic!("parser closures must have only one parameter, input &str");
    }
    let Some(Pat::Ident(PatIdent { ident: input_ident, .. })) = closure.inputs.iter().next() else {
        panic!("the parser closure input must be an identifier!");
    };

    let body = &closure.body;

    quote::quote! {
        #[allow(non_snake_case)]
        pub fn #ident(#input_ident: &str) -> ::nom::IResult<&str, super::#terminal_enum_ident> {
            use super::*;
            #body
        }
    }
}

fn litstr_parser_codegen(
    terminal_enum_ident: &Ident,
    ident: &Ident,
    litstr: &LitStr,
) -> TokenStream {
    quote::quote! {
        #[allow(non_snake_case)]
        pub fn #ident(input: &str) -> ::nom::IResult<&str, super::#terminal_enum_ident> {
            let (input, _) = ::nom::bytes::complete::tag(#litstr)(input)?;
            Ok((input, super::#terminal_enum_ident::#ident))
        }
    }
}
