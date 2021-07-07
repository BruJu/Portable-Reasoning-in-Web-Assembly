//! This crate defines a forest structure to store an [RDF] [dataset] as a set of
//! b-trees.
//!
//! An [RDF dataset] is often seen as a set of *quads*, each composed of a
//! subject S, a predicate P, an object O, and a graph name G.
//! While in [RDF], these components are [RDF term]s, the quads handled by this
//! crate are composed of 4 identifiers (`u32` values).
//! The semantics of the identifiers (i.e. their corresponding [RDF term]s)
//! must be stored separately by the user of this crate.
//!
//! All b-trees in the forest contain the same quads, but in different orders,
//! for the purpose of efficiently replying to different queries.
//!
//! The main types of this crate are :
//! - *Identifier*: A `u32` (because Web Assembly is good at manipulating
//! these)
//! - `[u32; NB_OF_TERMS=4]`: Quads are represented by arrays of four
//! identifiers, where the elements represent S, P, O and G respectively.
//! - [`IndexingForest4`]: A forest designed to index quads of identifiers. It
//! can be used to store arrays of 4 `u32`s and query them from any pattern
//! (for example [*, 7, *, 3] will retrieve every previously
//! stored quads whose predicate is 7 and whose graph name is 3).
//! - [`Block`]: An qand of identifiers whete the SPOG components are stored in
//! a different order. A [`BlockOrder`] is required to reorder them.
//! - [`BlockOrder`]: A structure that enables to convert between [`Block`]s
//! and "canonical" (SPOG) quad of identfiers.
//!
//! [RDF]: https://www.w3.org/TR/rdf11-primer/
//! [dataset]: https://www.w3.org/TR/rdf11-concepts/#dfn-rdf-dataset
//! [RDF Term]: https://www.w3.org/TR/rdf11-concepts/#dfn-rdf-term


pub mod order;

pub mod tree;

mod identifier;
pub use crate::identifier::*;

pub mod compile_time_forest;

pub mod run_time_forest;
