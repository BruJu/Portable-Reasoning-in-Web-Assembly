//! This file defines how an array of four identifiers / an identifier quad can
//! be ordered

use crate::order::Position;
use crate::Identifier;

use std::cmp::Ordering;
use std::marker::PhantomData;

/// An utility struct that provides static method to manipulate quads sorted in
/// the ABCD order
pub struct FixedOrder4<A, B, C, D>
where A: Position, B: Position, C: Position, D: Position {
    _a: PhantomData<*const (A, B, C, D)>,
}

impl<A, B, C, D> FixedOrder4<A, B, C, D>
where A: Position, B: Position, C: Position, D: Position {
    const IS_VALID: bool = {
        let a: usize = A::VALUE;
        let b: usize = B::VALUE;
        let c: usize = C::VALUE;
        let d: usize = D::VALUE;
    
        a < 4 && b < 4 && c < 4 && d < 4
        && a != b && a != c && a != d
        && b != c && b != d
        && c != d
    };

    /// Return the list of indexes described by the generic parameters.
    pub fn to_slice() -> [usize; 4] {
        [A::VALUE, B::VALUE, C::VALUE, D::VALUE]
    }
    
    /// Compare two arrays of four orderable values by their `A::VALUE`-th
    /// term, then their `B::VALUE`-th term, then their `C::VALUE`-th term,
    /// then their `D::VALUE`-th term.
    pub fn compare<I>(lhs: &[I; 4], rhs: &[I; 4]) -> Ordering 
    where I: Ord
    {
        (&lhs[A::VALUE]).cmp(&rhs[A::VALUE])
            .then_with(|| (&lhs[B::VALUE]).cmp(&rhs[B::VALUE]))
            .then_with(|| (&lhs[C::VALUE]).cmp(&rhs[C::VALUE]))
            .then_with(|| (&lhs[D::VALUE]).cmp(&rhs[D::VALUE]))
    }

    /// Return the number of terms that can be used as a prefix, with this
    /// order, to filter the quads matching the given pattern.
    ///
    /// In other words, if a collection is sorted, how many terms are fixed in
    /// this order before we have to start iterating on all terms between two
    /// bounds.
    ///
    /// This gives an indication of how efficient the
    /// [`range()`](Self::range()) method will be. The higher, the better
    /// suited this order is to answer this pattern.
    pub fn index_conformance<T>(pattern: &[Option<T>; 4]) -> usize {
        Self::to_slice()
            .iter()
            .take_while(|tr| pattern[**tr as usize].is_some())
            .count()
    }
    
    /// Assuming that we have a structure ordered by the order A, B, C, D,
    /// and that we want to extract every array that matches the given
    /// pattern (None is a wildcard, else we want the specified value),
    /// return the smallest possible range to retrieve every quads from the
    /// structure and a new pattern which contains values only on non wildcard
    /// indexes that are not already filtered by the range.
    pub fn range<T>(
        mut pattern: [Option<T>; 4],
    ) -> (std::ops::RangeInclusive<Block<T, A, B, C, D>>, [Option<T>; 4])
    where T: Identifier
    {
        // Initial range (checks every values)
        let mut min = Block::<T, A, B, C, D>::new([T::MIN; 4]);
        let mut max = Block::<T, A, B, C, D>::new([T::MAX; 4]);

        // Restrict it as much as possible
        for term_role in Self::to_slice().iter() {
            match pattern[*term_role] {
                None => {
                    break;
                }
                Some(set_value) => {
                    min.values[*term_role] = set_value;
                    max.values[*term_role] = set_value;
                    pattern[*term_role] = None;
                }
            }
        }

        // Return the range and the filter block
        (
            min..=max,
            pattern,
        )
    }
}

// ============================================================================
// ============================================================================

/// Wrapper for an array of 4 values of the same type whose purpose is to
/// provide a compile time defined order on these arrays.
///
/// If the generic type `I` is an [`Identifier`], and the `A`, `B`, `C` and `D`
/// generics types are Identifiers, then ordered by A then B then C the nD
#[derive(Debug)]
pub struct Block<I, A, B, C, D>
where I: Identifier, A: Position, B: Position, C: Position, D: Position 
{
    /// The wrapped array of four values.
    pub values: [I; 4],
    _boilerplate: PhantomData<*const FixedOrder4<A, B, C, D>>,
}

impl<I, A, B, C, D> Block<I, A, B, C, D>
where I: Identifier, A: Position, B: Position, C: Position, D: Position 
{
    /// Wraps an array of four values
    pub fn new(elements: [I; 4]) -> Self {
        debug_assert!(FixedOrder4::<A, B, C, D>::IS_VALID);
        Self {
            values: elements,
            _boilerplate: PhantomData{}
        }
    }
}

/// The order on [`Block`]s is a total order.
impl<T, A, B, C, D> PartialOrd for Block<T, A, B, C, D>
where T: Identifier, A: Position, B: Position, C: Position, D: Position 
{
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

/// Compare two arrays of four [`Identifier`]s using the A::VALUE-th term.
/// If it is equals, compares the B::VALUE-th term, ... until the
/// D::VALUE-th term.
///
/// See [`FixedOrder4::compare`].
impl<T, A, B, C, D> Ord for Block<T, A, B, C, D>
where T: Identifier, A: Position, B: Position, C: Position, D: Position 
{
    fn cmp(&self, other: &Self) -> Ordering {
        FixedOrder4::<A, B, C, D>::compare(&self.values, &other.values)
    }
}

impl<T, A, B, C, D> Eq for Block<T, A, B, C, D>
where T: Identifier, A: Position, B: Position, C: Position, D: Position 
{}

impl<T, A, B, C, D> PartialEq for Block<T, A, B, C, D>
where T: Identifier, A: Position, B: Position, C: Position, D: Position 
{
    fn eq(&self, other: &Self) -> bool {
        // Order of comparison is not important here
        &self.values == &other.values
    }
}

// ============================================================================
// ============================================================================

/// Return true if the non None values of the given pattern are equals
/// to the values in quad. In other words, it can be seen as an
/// equality check where none serves as a wildcard.
pub fn pattern_match<T>(quad: &[T; 4], pattern: &[Option<T>; 4]) -> bool
where T: Identifier {
    quad.iter()
        .zip(pattern.iter())
        .all(|(val, opt)| match opt {
            None => true,
            Some(other) => val == other,
        }) 
}


// ============================================================================

#[cfg(test)]
mod test {
    use crate::order::{Subject, Predicate, Object, Graph};
    use super::*;
    use std::fmt::Debug;

    // Basic tests

    #[test]
    fn test_order4_validity() {
        // Valid permutations
        assert!(FixedOrder4::<Subject, Predicate, Object, Graph>::IS_VALID);
        assert!(FixedOrder4::<Graph, Object, Predicate, Subject>::IS_VALID);
        assert!(FixedOrder4::<Subject, Graph, Object, Predicate>::IS_VALID);
        assert!(FixedOrder4::<Predicate, Graph, Object, Subject>::IS_VALID);
        assert!(FixedOrder4::<Predicate, Subject, Object, Graph>::IS_VALID);
        assert!(FixedOrder4::<Object, Predicate, Subject, Graph>::IS_VALID);
        assert!(FixedOrder4::<Object, Predicate, Graph, Subject>::IS_VALID);
        assert!(FixedOrder4::<Graph, Predicate, Object, Subject>::IS_VALID);
        
        // Duplicates
        assert!(!FixedOrder4::<Graph, Graph, Graph, Graph>::IS_VALID);
        assert!(!FixedOrder4::<Subject, Subject, Subject, Subject>::IS_VALID);
        assert!(!FixedOrder4::<Object, Object, Object, Object>::IS_VALID);
        assert!(!FixedOrder4::<Predicate, Predicate, Predicate, Predicate>::IS_VALID);
        assert!(!FixedOrder4::<Subject, Subject, Predicate, Object>::IS_VALID);
        assert!(!FixedOrder4::<Subject, Predicate, Predicate, Object>::IS_VALID);
        assert!(!FixedOrder4::<Subject, Graph, Predicate, Graph>::IS_VALID);

        // Out of bound position
        struct Fourth {}
        impl Position for Fourth {
            const VALUE: usize = 4;
        }

        assert!(!FixedOrder4::<Fourth, Predicate, Object, Graph>::IS_VALID);
        assert!(!FixedOrder4::<Subject, Fourth, Object, Graph>::IS_VALID);
        assert!(!FixedOrder4::<Subject, Predicate, Fourth, Graph>::IS_VALID);
        assert!(!FixedOrder4::<Subject, Predicate, Object, Fourth>::IS_VALID);
    }

    #[test]
    fn test_order4_to_slice() {
        assert_eq!(
            FixedOrder4::<Subject, Predicate, Object, Graph>::to_slice(),
            [Subject::VALUE, Predicate::VALUE, Object::VALUE, Graph::VALUE]
        );

        assert_eq!(
            FixedOrder4::<Graph, Object, Predicate, Subject>::to_slice(),
            [Graph::VALUE, Object::VALUE, Predicate::VALUE, Subject::VALUE]
        );

        assert_eq!(
            FixedOrder4::<Subject, Graph, Object, Predicate>::to_slice(),
            [Subject::VALUE, Graph::VALUE, Object::VALUE, Predicate::VALUE]
        );

        assert_eq!(
            FixedOrder4::<Predicate, Graph, Object, Subject>::to_slice(),
            [Predicate::VALUE, Graph::VALUE, Object::VALUE, Subject::VALUE]
        );

        assert_eq!(
            FixedOrder4::<Predicate, Subject, Object, Graph>::to_slice(),
            [Predicate::VALUE, Subject::VALUE, Object::VALUE, Graph::VALUE]
        );

        assert_eq!(
            FixedOrder4::<Object, Predicate, Subject, Graph>::to_slice(),
            [Object::VALUE, Predicate::VALUE, Subject::VALUE, Graph::VALUE]
        );

        assert_eq!(
            FixedOrder4::<Object, Predicate, Graph, Subject>::to_slice(),
            [Object::VALUE, Predicate::VALUE, Graph::VALUE, Subject::VALUE]
        );

        assert_eq!(
            FixedOrder4::<Graph, Predicate, Object, Subject>::to_slice(),
            [Graph::VALUE, Predicate::VALUE, Object::VALUE, Subject::VALUE]
        );
    }

    #[test]
    fn test_order4_compare() {
        // FixedOrder4::compare is further tested in Block Ord tests
        type SPOG = FixedOrder4<Subject, Predicate, Object, Graph>;

        let m1234 = [1, 2, 3, 4];
        let m1324 = [1, 2, 4, 3];

        assert_eq!(SPOG::compare(&m1234, &m1234), std::cmp::Ordering::Equal);
        assert_eq!(SPOG::compare(&m1234, &m1324), std::cmp::Ordering::Less);
        assert_eq!(SPOG::compare(&m1324, &m1234), std::cmp::Ordering::Greater);

        type SPGO = FixedOrder4<Subject, Predicate, Graph, Object>;

        assert_eq!(SPGO::compare(&m1234, &m1234), std::cmp::Ordering::Equal);
        assert_eq!(SPGO::compare(&m1234, &m1324), std::cmp::Ordering::Greater);
        assert_eq!(SPGO::compare(&m1324, &m1234), std::cmp::Ordering::Less);
    }

    #[test]
    fn test_index_conformance() {
        // SPOG order
        type SPOG = FixedOrder4<Subject, Predicate, Object, Graph>;
        assert_eq!(SPOG::index_conformance::<i64>(&[None, None, None, None]), 0);
        assert_eq!(SPOG::index_conformance(&[Some(0), None, None, None]), 1);
        assert_eq!(SPOG::index_conformance(&[Some(0), Some(1), None, None]), 2);
        assert_eq!(SPOG::index_conformance(&[Some(0), Some(1), Some(2), None]), 3);
        assert_eq!(SPOG::index_conformance(&[Some(0), Some(1), Some(2), Some(3)]), 4);
        assert_eq!(SPOG::index_conformance(&[Some(6546), Some(1234), Some(8976), Some(324)]), 4);
        assert_eq!(SPOG::index_conformance(&[Some(0), Some(1), None, Some(3)]), 2);
        assert_eq!(SPOG::index_conformance(&[None, Some(1), Some(2), Some(3)]), 0);
    
        // Reverse order
        type GOPS = FixedOrder4<Graph, Object, Predicate, Subject>;
        assert_eq!(GOPS::index_conformance::<u64>(&[None, None, None, None]), 0);
        assert_eq!(GOPS::index_conformance(&[Some(0), None, None, None]), 0);
        assert_eq!(GOPS::index_conformance(&[Some(0), Some(1), None, None]), 0);
        assert_eq!(GOPS::index_conformance(&[Some(0), Some(1), Some(2), None]), 0);
        assert_eq!(GOPS::index_conformance(&[Some(0), Some(1), Some(2), Some(3)]), 4);
        assert_eq!(GOPS::index_conformance(&[Some(6546), Some(1234), Some(8976), Some(324)]), 4);
        assert_eq!(GOPS::index_conformance(&[Some(0), Some(1), None, Some(3)]), 1);
        assert_eq!(GOPS::index_conformance(&[None, Some(1), Some(2), Some(3)]), 3);
        assert_eq!(GOPS::index_conformance(&[None, None, Some(2), Some(3)]), 2);
    
        // Other types (values in option should be ignored)
        assert_eq!(GOPS::index_conformance(&[Some(44_u8), Some(33_u8), Some(3_u8), Some(2_u8)]), 4);
        assert_eq!(SPOG::index_conformance(&[Some(44_u32), Some(33_u32), Some(3_u32), Some(2_u32)]), 4);
        assert_eq!(SPOG::index_conformance(&[Some(1000000_usize), Some(2000000_usize), Some(20000_usize), Some(3333_usize)]), 4);
        assert_eq!(SPOG::index_conformance(&[Some(1000000_usize), Some(2000000_usize), None, Some(3333_usize)]), 2);

        // Another order
        type PSGO = FixedOrder4<Predicate, Subject, Graph, Object>;
        assert_eq!(PSGO::index_conformance(&[Some(100), Some(75), Some(125), Some(99)]), 4);
        assert_eq!(PSGO::index_conformance(&[None, Some(75), Some(125), None]), 1);
        assert_eq!(PSGO::index_conformance(&[Some(22), None, Some(33), Some(99884)]), 0);
        assert_eq!(PSGO::index_conformance(&[Some(1234), Some(21347), None, Some(0)]), 3);
    }

    #[test]
    fn test_range() {
        type SPOG = FixedOrder4<Subject, Predicate, Object, Graph>;

        type Block32SPOG = Block<u32, Subject, Predicate, Object, Graph>;

        // Simple filter

        assert_eq!(
            SPOG::range::<u32>([None, None, None, None]),
            (
                Block32SPOG::new([u32::MIN, u32::MIN, u32::MIN, u32::MIN])
                ..=
                Block32SPOG::new([u32::MAX, u32::MAX, u32::MAX, u32::MAX]),
                [None, None, None, None]
            )
        );

        assert_eq!(
            SPOG::range::<u32>([Some(77), Some(33), None, None]),
            (
                Block32SPOG::new([77_u32, 33_u32, u32::MIN, u32::MIN])
                ..=
                Block32SPOG::new([77_u32, 33_u32, u32::MAX, u32::MAX]),
                [None, None, None, None]
            )
        );

        assert_eq!(
            SPOG::range::<u32>([Some(77), Some(33), Some(44), None]),
            (
                Block32SPOG::new([77_u32, 33_u32, 44_u32, u32::MIN])
                ..=
                Block32SPOG::new([77_u32, 33_u32, 44_u32, u32::MAX]),
                [None, None, None, None]
            )
        );
        
        assert_eq!(
            SPOG::range::<u32>([Some(444), Some(12), Some(8888), Some(123)]),
            (
                Block32SPOG::new([444_u32, 12_u32, 8888_u32, 123_u32])
                ..=
                Block32SPOG::new([444_u32, 12_u32, 8888_u32, 123_u32]),
                [None, None, None, None]
            )
        );

        // With leftovers
        assert_eq!(
            SPOG::range::<u32>([None, Some(7777), Some(8888), Some(9999)]),
            (
                Block32SPOG::new([u32::MIN, u32::MIN, u32::MIN, u32::MIN])
                ..=
                Block32SPOG::new([u32::MAX, u32::MAX, u32::MAX, u32::MAX]),
                [None, Some(7777), Some(8888), Some(9999)]
            )
        );
        
        assert_eq!(
            SPOG::range::<u32>([Some(444), Some(12), None, Some(123)]),
            (
                Block32SPOG::new([444_u32, 12_u32, u32::MIN, u32::MIN])
                ..=
                Block32SPOG::new([444_u32, 12_u32, u32::MAX, u32::MAX]),
                [None, None, None, Some(123)]
            )
        );

        // A different order
        type OSGP = FixedOrder4<Object, Subject, Graph, Predicate>;
        type BlockSizeOGPS = Block<usize, Object, Subject, Graph, Predicate>;

        assert_eq!(
            OSGP::range::<usize>([Some(444_usize), None, Some(12_usize), None]),
            (
                BlockSizeOGPS::new([444_usize, usize::MIN, 12_usize, usize::MIN])
                ..=
                BlockSizeOGPS::new([444_usize, usize::MAX, 12_usize, usize::MAX]),
                [None, None, None, None]
            )
        );

        assert_eq!(
            OSGP::range::<usize>([Some(10_usize), Some(12_usize), Some(14_usize), None]),
            (
                BlockSizeOGPS::new([10_usize, usize::MIN, 14_usize, usize::MIN])
                ..=
                BlockSizeOGPS::new([10_usize, usize::MAX, 14_usize, usize::MAX]),
                [None, Some(12_usize), None, None]
            )
        );

        assert_eq!(
            OSGP::range::<usize>([Some(1_usize), None, Some(2_usize), Some(3_usize)]),
            (
                BlockSizeOGPS::new([1_usize, usize::MIN, 2_usize, 3_usize])
                ..=
                BlockSizeOGPS::new([1_usize, usize::MAX, 2_usize, 3_usize]),
                [None, None, None, None]
            )
        );
    }
    
    #[test]
    fn test_block_memory_footprint() {
        assert!(
            std::mem::size_of::<Block<u32, Subject, Predicate, Object, Graph>>() ==
            std::mem::size_of::<[u32; 4]>()
        );

        assert!(
            std::mem::size_of::<Block<u8, Subject, Predicate, Object, Graph>>() ==
            std::mem::size_of::<[u8; 4]>()
        );
        
        assert!(
            std::mem::size_of::<Block<u64, Subject, Predicate, Object, Graph>>() ==
            std::mem::size_of::<[u64; 4]>()
        );
        assert!(
            std::mem::size_of::<Block<usize, Subject, Predicate, Object, Graph>>() ==
            std::mem::size_of::<[usize; 4]>()
        );
    }

    #[test]
    fn test_block_is_a_wrapper() {
        fn one_test<A, B, C, D, I>(values: [I; 4])
        where I: Identifier + Debug, A: Position + Debug, B: Position + Debug, C: Position + Debug, D: Position + Debug {
            assert_eq!(
                &Block::<I, A, B, C, D>::new(values.clone()).values,
                &values
            );
        }

        one_test::<Subject, Predicate, Object, Graph, u32>([11, 22, 33, 44]);
        one_test::<Subject, Predicate, Object, Graph, usize>([33, 121, 544, 88]);
        one_test::<Subject, Graph, Object, Predicate, usize>([21, 8795, 134, 124]);
        one_test::<Graph, Object, Predicate, Subject, u8>([7, 13, 42, 3]);
    }

    #[test]
    fn test_pattern_match() {
        // Match
        assert!(pattern_match(&[556, 120, 325, 636], &[Some(556), Some(120), Some(325), Some(636)]));
        assert!(pattern_match(&[816, 302, 514, 288], &[None, None, None, Some(288)]));
        assert!(pattern_match(&[557, 846, 923, 37], &[None, None, Some(923), Some(37)]));
        assert!(pattern_match(&[771, 941, 722, 703], &[None, None, None, Some(703)]));
        assert!(pattern_match(&[940, 774, 170, 581], &[None, Some(774), Some(170), Some(581)]));
        assert!(pattern_match(&[790, 57, 727, 781], &[None, None, None, Some(781)]));
        assert!(pattern_match(&[432, 14, 851, 802], &[None, None, Some(851), Some(802)]));
        assert!(pattern_match(&[478, 379, 842, 174], &[None, None, None, Some(174)]));
        assert!(pattern_match(&[665, 274, 228, 298], &[Some(665), Some(274), Some(228), Some(298)]));
        assert!(pattern_match(&[907, 975, 968, 416], &[None, None, None, Some(416)]));
        assert!(pattern_match(&[225, 883, 971, 545], &[None, None, Some(971), Some(545)]));
        assert!(pattern_match(&[327, 699, 549, 540], &[None, None, None, Some(540)]));
        assert!(pattern_match(&[998, 717, 753, 607], &[None, Some(717), Some(753), Some(607)]));
        assert!(pattern_match(&[850, 630, 951, 618], &[None, None, None, Some(618)]));
        assert!(pattern_match(&[169, 181, 614, 514], &[None, None, Some(614), Some(514)]));
        assert!(pattern_match(&[924, 420, 423, 370], &[None, None, None, Some(370)]));

        // Do not match
        assert!(!pattern_match(&[4456, 92, 545, 635], &[Some(534), Some(654), Some(564), Some(847)]));
        assert!(!pattern_match(&[534, 92, 545, 635], &[Some(534), Some(654), Some(564), Some(847)]));
        assert!(!pattern_match(&[761, 633, 613, 857], &[None, None, None, Some(459)]));
        assert!(!pattern_match(&[443, 554, 54, 999], &[None, None, Some(54), Some(359)]));
        assert!(!pattern_match(&[752, 324, 152, 477], &[None, None, None, Some(982)]));
        assert!(!pattern_match(&[390, 964, 345, 528], &[None, Some(964), Some(345), Some(863)]));
        assert!(!pattern_match(&[976, 218, 55, 279], &[None, None, None, Some(684)]));
        assert!(!pattern_match(&[520, 831, 47, 285], &[None, None, Some(144), Some(470)]));
        assert!(!pattern_match(&[818, 987, 703, 313], &[None, None, None, Some(463)]));
        assert!(!pattern_match(&[341, 456, 889, 403], &[Some(341), Some(200), Some(940), Some(584)]));
        assert!(!pattern_match(&[560, 140, 359, 673], &[None, None, Some(138), Some(94)]));
        assert!(!pattern_match(&[631, 498, 187, 470], &[None, None, None, Some(431)]));
        assert!(!pattern_match(&[610, 142, 406, 410], &[None, Some(142), Some(983), Some(464)]));
        assert!(!pattern_match(&[725, 105, 474, 274], &[None, None, None, Some(348)]));
        assert!(!pattern_match(&[546, 718, 513, 238], &[None, None, Some(359), Some(238)]));
        assert!(!pattern_match(&[565, 466, 157, 41], &[None, None, None, Some(952)]));
        assert!(!pattern_match(&[598, 76, 513, 307], &[None, None, None, Some(485)]));
        assert!(!pattern_match(&[28, 108, 582, 134], &[None, None, Some(994), Some(134)]));
        assert!(!pattern_match(&[369, 325, 189, 863], &[None, None, None, Some(351)]));
        assert!(!pattern_match(&[852, 23, 430, 292], &[None, Some(23), Some(882), Some(292)]));
        assert!(!pattern_match(&[445, 355, 836, 184], &[None, None, Some(570), Some(278)]));
        assert!(!pattern_match(&[48, 113, 784, 609], &[None, None, None, Some(464)]));
        assert!(!pattern_match(&[149, 402, 66, 687], &[None, None, None, Some(173)]));
        assert!(!pattern_match(&[755, 502, 905, 361], &[None, None, Some(905), Some(61)]));
        assert!(!pattern_match(&[762, 607, 263, 493], &[None, None, None, Some(677)]));
        assert!(!pattern_match(&[655, 815, 951, 172], &[None, None, Some(282), Some(72)]));
    }

    // More tests

    #[test]
    fn spog_cmp() {
        let spog = |quad| Block::<u32, Subject, Predicate, Object, Graph>::new(quad);
        assert!(spog([1, 1, 1, 1]) <= spog([1, 1, 1, 1]));
        assert!(spog([1, 1, 1, 1]) < spog([1, 1, 1, 2]));
        assert!(spog([1, 1, 1, 1]) < spog([1, 1, 2, 0]));
        assert!(spog([1, 1, 1, 1]) < spog([1, 2, 0, 0]));
        assert!(spog([1, 1, 1, 1]) < spog([2, 0, 0, 0]));
    }

    #[test]
    fn gspo_cmp() {
        let gspo = |quad| Block::<u32, Graph, Subject, Predicate, Object>::new(quad);
        assert!(gspo([1, 1, 1, 1]) <= gspo([1, 1, 1, 1]));
        assert!(gspo([1, 1, 1, 1]) < gspo([1, 1, 2, 1]));
        assert!(gspo([1, 1, 1, 1]) < gspo([1, 2, 0, 1]));
        assert!(gspo([1, 1, 1, 1]) < gspo([2, 0, 0, 1]));
        assert!(gspo([1, 1, 1, 1]) < gspo([0, 0, 0, 2]));
    }

    #[test]
    fn opsg_cmp() {
        let opsg = |quad| Block::<u32, Object, Predicate, Subject, Graph>::new(quad);
        assert!(opsg([1, 1, 1, 1]) <= opsg([1, 1, 1, 1]));
        assert!(opsg([1, 1, 1, 1]) < opsg([1, 1, 1, 2]));
        assert!(opsg([1, 1, 1, 1]) < opsg([2, 1, 1, 0]));
        assert!(opsg([1, 1, 1, 1]) < opsg([0, 2, 1, 0]));
        assert!(opsg([1, 1, 1, 1]) < opsg([0, 0, 2, 0]));
    }

    #[test]
    fn pgso_cmp() {
        let pgso = |quad| Block::<u32, Predicate, Graph, Subject, Object>::new(quad);
        assert!(pgso([1, 1, 1, 1]) <= pgso([1, 1, 1, 1]));
        assert!(pgso([1, 1, 1, 1]) < pgso([1, 1, 2, 1]));
        assert!(pgso([1, 1, 1, 1]) < pgso([2, 1, 0, 1]));
        assert!(pgso([1, 1, 1, 1]) < pgso([0, 1, 0, 2]));
        assert!(pgso([1, 1, 1, 1]) < pgso([0, 2, 0, 0]));
    }

    #[test]
    fn gops_cmp() {
        let gops = |quad| Block::<u32, Graph, Object, Predicate, Subject>::new(quad);
        assert!(gops([1, 1, 1, 1]) <= gops([1, 1, 1, 1]));
        assert!(gops([1, 1, 1, 1]) < gops([2, 1, 1, 1]));
        assert!(gops([1, 1, 1, 1]) < gops([0, 2, 1, 1]));
        assert!(gops([1, 1, 1, 1]) < gops([0, 0, 2, 1]));
        assert!(gops([1, 1, 1, 1]) < gops([0, 0, 0, 2]));
    }

    #[test]
    fn sogp_cmp() {
        let sogp = |quad| Block::<u32, Subject, Object, Graph, Predicate>::new(quad);
        assert!(sogp([1, 1, 1, 1]) <= sogp([1, 1, 1, 1]));
        assert!(sogp([1, 1, 1, 1]) < sogp([1, 2, 1, 1]));
        assert!(sogp([1, 1, 1, 1]) < sogp([1, 0, 1, 2]));
        assert!(sogp([1, 1, 1, 1]) < sogp([1, 0, 2, 0]));
        assert!(sogp([1, 1, 1, 1]) < sogp([2, 0, 0, 0]));
    }

    // TODO: Other tests from
    // https://github.com/pchampin/Portable-Reasoning-in-Web-Assembly/blob/new_api/identifier-forest/src/quad/block.rs
}
