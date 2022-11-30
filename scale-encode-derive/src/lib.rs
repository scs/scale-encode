use proc_macro2::TokenStream as TokenStream2;
use quote::{quote, format_ident};
use syn::{parse_macro_input, DeriveInput};

const ATTR_NAME: &str = "encode_as_type";

#[proc_macro_derive(EncodeAsType, attributes(encode_as_type))]
pub fn derive(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let input = parse_macro_input!(input as DeriveInput);

    // parse top level attrs.
    let attrs = match TopLevelAttrs::parse(&input.attrs) {
        Ok(attrs) => attrs,
        Err(e) => return e.write_errors().into()
    };

    let path_to_scale_encode = attrs.path;

    // what type is the derive macro declared on?
    match input.data {
        syn::Data::Enum(details) => {
            derive_enum(&path_to_scale_encode, input.ident, details).into()
        },
        syn::Data::Struct(details) => {
            derive_struct(&path_to_scale_encode, input.ident, details).into()
        },
        syn::Data::Union(_) => {
            syn::Error::new(input.ident.span(), "Unions are not supported by the EncodeAsType derive macro")
                .into_compile_error()
                .into()
        }
    }
}

fn derive_enum(path_to_scale_encode: &syn::Path, name: syn::Ident, details: syn::DataEnum) -> TokenStream2 {
    // For each variant we want to spit out a match arm.
    let match_arms = details.variants.into_iter().map(|variant| {
        let variant_name = variant.ident;
        let variant_name_str = variant_name.to_string();

        let (matcher, composite) = fields_to_matcher_and_composite(path_to_scale_encode, &variant.fields);
        quote!(
            Self::#variant_name #matcher => {
                #path_to_scale_encode::__internal::Variant { name: #variant_name_str, fields: #composite }
                    .encode_as_type_to(
                        __encode_as_type_type_id,
                        __encode_as_type_types,
                        __encode_as_type_context,
                        __encode_as_type_out
                    )
            }
        )
    });

    quote!(
        impl #path_to_scale_encode::EncodeAsType for #name {
            fn encode_as_type_to(
                &self,
                __encode_as_type_type_id: u32,
                __encode_as_type_types: &#path_to_scale_encode::__internal::PortableRegistry,
                __encode_as_type_context: #path_to_scale_encode::Context,
                __encode_as_type_out: &mut Vec<u8>
            ) -> Result<(), #path_to_scale_encode::Error> {
                match self {
                    #( #match_arms ),*
                }
            }
        }
    )
}

fn derive_struct(path_to_scale_encode: &syn::Path, name: syn::Ident, details: syn::DataStruct) -> TokenStream2 {
    let (matcher, composite) = fields_to_matcher_and_composite(path_to_scale_encode, &details.fields);

    quote!(
        impl #path_to_scale_encode::EncodeAsType for #name {
            fn encode_as_type_to(
                &self,
                __encode_as_type_type_id: u32,
                __encode_as_type_types: &#path_to_scale_encode::__internal::PortableRegistry,
                __encode_as_type_context: #path_to_scale_encode::Context,
                __encode_as_type_out: &mut Vec<u8>
            ) -> Result<(), #path_to_scale_encode::Error> {
                let #name #matcher = self;
                #composite.encode_as_type_to(
                    __encode_as_type_type_id,
                    __encode_as_type_types,
                    __encode_as_type_context,
                    __encode_as_type_out
                )
            }
        }
    )
}

fn fields_to_matcher_and_composite(path_to_scale_encode: &syn::Path, fields: &syn::Fields) -> (TokenStream2, TokenStream2) {
    match fields {
        syn::Fields::Named(fields) => {
            let match_body = fields.named
                .iter()
                .map(|f| {
                    let field_name = &f.ident;
                    quote!(#field_name)
                });
            let tuple_body = fields.named
                .iter()
                .map(|f| {
                    let field_name_str = f.ident.as_ref().unwrap().to_string();
                    let field_name = &f.ident;
                    quote!((Some(#field_name_str), #field_name))
                });
            // add a closing comma if one field to make sure it's still parsed as
            // a tuple and not just brackets around a field:
            let closing_comma = if fields.named.len() == 1 {
                quote!(,)
            } else {
                quote!()
            };
            (
                quote!({#( #match_body ),*}),
                quote!(#path_to_scale_encode::__internal::Composite((#( #tuple_body ),* #closing_comma)))
            )
        },
        syn::Fields::Unnamed(fields) => {
            let field_idents: Vec<syn::Ident> = fields.unnamed
                .iter()
                .enumerate()
                .map(|(idx, _)| format_ident!("_{idx}"))
                .collect();
            let match_body = field_idents
                .iter()
                .map(|i| quote!(#i));
            let tuple_body = field_idents
                .iter()
                .map(|i| {
                    quote!((None as Option<&'static str>, #i))
                });
            // add a closing comma if one field to make sure it's still parsed as
            // a tuple and not just brackets around a field:
            let closing_comma = if fields.unnamed.len() == 1 {
                quote!(,)
            } else {
                quote!()
            };
            (
                quote!((#( #match_body ),*)),
                quote!(#path_to_scale_encode::__internal::Composite((#( #tuple_body ),* #closing_comma)))
            )
        },
        syn::Fields::Unit => {
            (
                quote!(),
                quote!(#path_to_scale_encode::__internal::Composite(()))
            )
        }
    }
}

#[derive(darling::FromMeta)]
struct TopLevelAttrs {
    // path to the scale_encode crate, in case it's not a top level dependency.
    path: syn::Path
}

impl TopLevelAttrs {
    fn parse(attrs: &[syn::Attribute]) -> darling::Result<Self> {
        use darling::FromMeta;

        #[derive(FromMeta)]
        struct TopLevelAttrsInner {
            #[darling(default)]
            path: Option<syn::Path>
        }

        let mut res = TopLevelAttrs {
            path: syn::parse_quote!(::scale_encode)
        };

        for attr in attrs {
            if !attr.path.is_ident(ATTR_NAME) {
                continue
            }
            let meta = attr.parse_meta()?;
            let parsed_attrs = TopLevelAttrsInner::from_meta(&meta)?;

            if let Some(path) = parsed_attrs.path {
                res.path = path;
            }
        }

        Ok(res)
    }
}