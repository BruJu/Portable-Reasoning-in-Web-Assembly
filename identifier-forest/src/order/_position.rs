//! Define the trait [`Position`]. 

/// A [`Position`] is an index in an array of identifiers.
///
/// This trait is mainly used as a workaround as const integers in generics are
/// not supported in Rust. It also provides added semantic on the indexes.
/// 
/// The semantic is never actually enforced by the implementation, so each
/// position implementation with the same `VALUE` can be used interchangeably.
pub trait Position {
    /// Index of this [`Position`] in an array of [`crate::Identifier`]s
    const VALUE: usize;
}

// ----------------------------------------------------------------------------
// ---- Array of identifiers seen as a SPO(G= ordered RDF triple or quad.

/// The subject position in a SPO ordered [RDF] triple / SPOG ordered [RDF]
/// quad, which is the 0th in an array of 3 or 4 identifiers (couting from 0).
///
/// [RDF]: https://www.w3.org/TR/rdf11-primer/
#[derive(Debug)]
pub struct Subject {}
impl Position for Subject {
    /// in SPO(G), the **S**ubject is at the 0th position
    const VALUE: usize = 0;
}

/// The predicate position in a SPO ordered [RDF] triple / SPOG ordered [RDF]
/// quad, which is the 1st in an array of 3 or 4 identifiers (couting from 0).
///
/// [RDF]: https://www.w3.org/TR/rdf11-primer/
#[derive(Debug)]
pub struct Predicate {}
impl Position for Predicate {
    /// in SPO(G), the **P**redicate is at the 1st position
    const VALUE: usize = 1;
}

/// The object position in a SPO ordered [RDF] triple / SPOG ordered [RDF]
/// quad, which is the 2nd in an array of 3 or 4 identifiers (couting from 0).
///
/// [RDF]: https://www.w3.org/TR/rdf11-primer/
#[derive(Debug)]
pub struct Object {}
impl Position for Object {
    /// in SPO(G), the **O**bject is at the 2nd position
    const VALUE: usize = 2;
}

/// The graph position in a SPOG ordered [RDF] quad
/// which is the 3rd in an array of 4 identifiers (couting from 0).
///
/// [RDF]: https://www.w3.org/TR/rdf11-primer/
#[derive(Debug)]
pub struct Graph {}
impl Position for Graph {
    /// in SPOG, the **G**raph is at the 3rd position
    const VALUE: usize = 3;
}

/*

// ----------------------------------------------------------------------------
// ---- Zero abstraction

// We do not actually provide these implementation as the implemented trees and
// forests actually use the RDF related ones.
//
// Users that do not use RDF can just see Subject / Predicate / ... as a cute
// way to name the elements at the index 0, index 1, ... of an array.

/// The zero-th element
pub struct IndexZero {}

/// The first element
pub struct IndexOne {}

/// The second element
pub struct IndexTwo {}

/// The third element
pub struct IndexThree {}

impl Position for IndexZero  { const VALUE: usize = 0; }
impl Position for IndexOne   { const VALUE: usize = 1; }
impl Position for IndexTwo   { const VALUE: usize = 2; }
impl Position for IndexThree { const VALUE: usize = 3; }

*/
