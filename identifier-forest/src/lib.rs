//! This crate defines data structures designed to store a [RDF] [graph]s and [dataset]s,
//! using b-trees for indexing: [`triple::TripleForest`] and [`quad::QuadForest`].
//!
//! An [RDF] [dataset] is often seen as a set of *quads*, each composed of a
//! subject S, a predicate P, an object O, and a graph name G.
//! While in [RDF], these components are [RDF term]s, the quads handled by this
//! crate are composed of 4 [`Identifier`]s (typically `usize` values).
//! The semantics of the identifiers (i.e. their corresponding [RDF term]s)
//! must be stored separately by the user of this crate.
//!
//! All b-trees in the forest contain the same quads, but in different orders,
//! for the purpose of efficiently replying to different queries.
//!
//! [graph]: https://www.w3.org/TR/rdf11-concepts/#dfn-rdf-graph
//! [dataset]: https://www.w3.org/TR/rdf11-concepts/#dfn-rdf-dataset
//! [RDF]: https://www.w3.org/TR/rdf11-primer/
//! [RDF Term]: https://www.w3.org/TR/rdf11-concepts/#dfn-rdf-term
#![deny(missing_docs)]

mod identifier;
pub use crate::identifier::Identifier;

/// Implementation for quads and datasets.
pub mod quad {
    pub mod block;
    pub use self::block::*;

    pub mod rt_block;
    pub use self::rt_block::*;

    mod quad_forest;
    pub use self::quad_forest::*;
}

/// Implementation for triples and graphs. **TODO**: not implemented yet.
pub mod triple {
    /// TODO: this is just a dummy definition for the sake of having links in the crate documentation.
    pub struct TripleForest;
}

pub mod compat;
