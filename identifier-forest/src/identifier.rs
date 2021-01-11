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
pub trait Identifier: Copy + Debug + Hash + Eq + Ord + 'static {
    /// The minimum value of this identifier type
    const MIN: Self;
    /// The maximum value of this identifier type
    const MAX: Self;
}

impl Identifier for u16 {
    const MIN: Self = Self::MIN;
    const MAX: Self = Self::MAX;
}

impl Identifier for u32 {
    const MIN: Self = Self::MIN;
    const MAX: Self = Self::MAX;
}

impl Identifier for u64 {
    const MIN: Self = Self::MIN;
    const MAX: Self = Self::MAX;
}

impl Identifier for usize {
    const MIN: Self = Self::MIN;
    const MAX: Self = Self::MAX;
}

impl Identifier for i16 {
    const MIN: Self = Self::MIN;
    const MAX: Self = Self::MAX;
}

impl Identifier for i32 {
    const MIN: Self = Self::MIN;
    const MAX: Self = Self::MAX;
}

impl Identifier for i64 {
    const MIN: Self = Self::MIN;
    const MAX: Self = Self::MAX;
}

impl Identifier for isize {
    const MIN: Self = Self::MIN;
    const MAX: Self = Self::MAX;
}

impl<T: Identifier> Identifier for Option<T> {
    const MIN: Self = Self::MIN;
    const MAX: Self = Some(T::MAX);
}
