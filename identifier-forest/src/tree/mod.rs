//! This module defines the features offered by a structure that stores arrays
//! of fours identifiers.
//!
//! It provides:
//! - A trait, [`MaybeTree4`] which enables to insert, remove, ... quads.
//! The specifity of this trait is that it accepts implementation that can
//! produce no result, and also a method that forces to populate the tree
//! - Implementations using both OnceCell and BTreeSet to produce BTreeSet
//! based implementation that can be populated while still using a const
//! reference. The main purpose is to provide duplicates version of the same
//! list of quads, and to pick the most efficient order when a certain
//! quad pattern is requested



mod _tree_trait;
mod _tree_predefined;

pub use self::_tree_trait::*;
pub use self::_tree_predefined::*;
