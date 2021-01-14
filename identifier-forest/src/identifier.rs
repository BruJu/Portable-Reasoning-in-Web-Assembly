//! Define the trait [`Identifier`].
use std::fmt::Debug;
use std::hash::Hash;

/// A short value (usually an integer)
/// representing a term in a graph or dataset.
///
/// NB: for convenience, [`Option`]`<I>`
/// also implements [`Identifier`] when `I` does.
/// This allows for patterns (where `None` is used as a wildcard)
/// to be described,
/// using the same structures as those designed for identifiers.
pub trait Identifier: Copy + Debug + Default + Hash + Eq + Ord + 'static {
    /// The minimum value of this identifier type
    const MIN: Self;
    /// The maximum value of this identifier type
    const MAX: Self;
}

macro_rules! impl_identifier {
    ($typ: ident) => {
        impl Identifier for $typ {
            const MIN: Self = Self::MIN;
            const MAX: Self = Self::MAX;
        }
    };
}

impl_identifier!(usize);
impl_identifier!(u64);
impl_identifier!(u32);
impl_identifier!(u16);
impl_identifier!(isize);
impl_identifier!(i64);
impl_identifier!(i32);
impl_identifier!(i16);
