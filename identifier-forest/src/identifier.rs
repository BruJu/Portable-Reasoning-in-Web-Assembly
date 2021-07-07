//! Define the trait [`Identifier`]. 

#![deny(missing_docs)]

/// Identifiers are values that are comparable between each other, and that
/// both have an associated minimal value and maximum value.
///
/// This enables them to both store them in BTreeSets and search for every
/// possible values for an identifier (making the range MIN..=MAX a wildcare).
pub trait Identifier : Ord + Copy {
    /// Minimal value an identifier of this type can be
    const MIN: Self;
    /// Maximal value an identifier of this type can be
    const MAX: Self;
}

impl Identifier for u8 {
    const MIN: Self = Self::MIN;
    const MAX: Self = Self::MAX;
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
