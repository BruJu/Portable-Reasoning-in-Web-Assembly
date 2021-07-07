//! Given arrays of four [`Identifier`](`crate::Identifier`)s, named
//! *identifier quad* or quad for short, this module
//! defines a way to name the different values (meaning the [`Position`] of a
//! value in the array has a semantic) and a [`Block`] wrapper class around
//! them to sort them in any order defined at compile time.
//!
//! The [`FixedOrder4`] class also provides methods to retrieve more efficiently the
//! arrays from sorted structure, by building the appropriate range and providing methods
//! to filter extraneous values.
#![deny(missing_docs)]

mod _order;
mod _position;

pub use self::_order::*;
pub use self::_position::*;
