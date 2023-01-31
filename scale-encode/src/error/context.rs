//! This module provides a [`Context`] type that must be provided with every
//! attempt to encode some type. Internally, the [`Context`] tracks the path
//! that we're attempting to encode to aid in error reporting.

use std::borrow::Cow;
use super::linkedlist::{ LinkedList };

/// A cheaply clonable opaque context which allows us to track the current
/// location into a type that we're trying to encode, to aid in
/// error reporting.
#[derive(Clone, Default, Debug)]
pub struct Context {
    path: LinkedList<Location>
}

impl Context {
    /// Construct a new, empty context.
    pub fn new() -> Context {
        Default::default()
    }
    /// Return a new context with the given location appended.
    pub fn at(&self, loc: Location) -> Context {
        let path = self.path.clone().push(loc);
        Context { path }
    }
    /// Return the current path.
    pub fn path(&self) -> Path<'_> {
        Path(Cow::Borrowed(&self.path))
    }
}

/// The current path that we're trying to encode.
pub struct Path<'a>(Cow<'a, LinkedList<Location>>);

impl <'a> Path<'a> {
    /// Cheaply convert the path to an owned version.
    pub fn to_owned(self) -> Path<'static> {
        Path(Cow::Owned(self.0.into_owned()))
    }
    /// Return each location visited, most recent first.
    pub fn locations(&self) -> impl Iterator<Item = &Location> {
        self.0.iter_back()
    }
}

impl <'a> std::fmt::Display for Path<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut items = Vec::with_capacity(self.0.len());
        for item in self.0.iter_back() {
            items.push(item);
        }

        for (idx, loc) in items.iter().rev().enumerate() {
            if idx != 0 {
                f.write_str(".")?;
            }
            match &loc.inner {
                Loc::Field(name) => f.write_str(&*name)?,
                Loc::Index(i) => write!(f, "[{i}]")?,
                Loc::Variant(name) => write!(f, "({name})")?
            }
        }
        Ok(())
    }
}

/// Some location, like a field, variant or index in an array.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Location {
    inner: Loc
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum Loc {
    Field(Cow<'static, str>),
    Index(usize),
    Variant(Cow<'static, str>)
}

impl Location {
    /// This represents some struct field.
    pub fn field(name: impl Into<Cow<'static,str>>) -> Self {
        Location {
            inner: Loc::Field(name.into())
        }
    }
    /// This represents some variant name.
    pub fn variant(name: impl Into<Cow<'static,str>>) -> Self {
        Location {
            inner: Loc::Variant(name.into())
        }
    }
    /// This represents a tuple or array index.
    pub fn idx(i: usize) -> Self {
        Location {
            inner: Loc::Index(i)
        }
    }
}
