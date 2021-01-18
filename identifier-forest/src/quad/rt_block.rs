//! Define the type [`RtfBlock`] and the associated enum [`Order`].
use super::*;
use crate::Identifier;
use std::cmp::{Ord, Ordering, PartialOrd};
use std::ops::RangeInclusive;

/// "RunTime Fat Block":
/// a [`Block`] implementation where the sorting order is decided at runtime,
/// and managed through an additional components in blocks.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct RtfBlock<I: Identifier> {
    data: [I; 4],
    order: Order,
}

impl<I: Identifier> From<RtfBlock<I>> for [I; 4] {
    fn from(other: RtfBlock<I>) -> Self {
        other.data
    }
}

impl<I: Identifier> Ord for RtfBlock<I> {
    fn cmp(&self, other: &Self) -> Ordering {
        debug_assert_eq!(self.order, other.order);
        // TODO: different order based on self.0[4]
        let [i0, i1, i2, i3] = self.order.idx();
        self.data[i0]
            .cmp(&other.data[i0])
            .then_with(|| self.data[i1].cmp(&other.data[i1]))
            .then_with(|| self.data[i2].cmp(&other.data[i2]))
            .then_with(|| self.data[i3].cmp(&other.data[i3]))
    }
}

impl<I: Identifier> PartialOrd for RtfBlock<I> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<I: Identifier> Block<I> for RtfBlock<I> {
    type Param = Order;

    fn new(data: [I; 4], order: Order) -> Self {
        RtfBlock { data, order }
    }

    fn spog(&self, _order: Order) -> [I; 4] {
        self.data
    }

    fn priority_for(spog_pattern: &[Option<I>; 4], param: Order) -> u8 {
        let mut ret = 0;
        for i in param.idx().iter() {
            match spog_pattern[*i] {
                Some(_) => ret += 1,
                None => break,
            }
        }
        ret
    }

    fn range_and_filter(
        mut spog_pattern: [Option<I>; 4],
        param: Order,
    ) -> (RangeInclusive<Self>, [Option<I>; 4]) {
        let mut bmin = Self::new([I::MIN; 4], param);
        let mut bmax = Self::new([I::MAX; 4], param);
        for i in param.idx().iter() {
            let i = *i;
            match spog_pattern[i] {
                None => break,
                Some(val) => {
                    bmin.data[i] = val;
                    bmax.data[i] = val;
                    spog_pattern[i] = None;
                }
            }
        }
        (bmin..=bmax, spog_pattern)
    }
}

//

/// Order parameter for [`RtfBlock`].
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Order {
    /// SPOG
    SPOG,
    /// SPGO
    SPGO,
    /// SOPG
    SOPG,
    /// SOGP
    SOGP,
    /// SGPO
    SGPO,
    /// SGOP
    SGOP,
    /// PSOG
    PSOG,
    /// PSGO
    PSGO,
    /// POSG
    POSG,
    /// POGS
    POGS,
    /// PGSO
    PGSO,
    /// PGOS
    PGOS,
    /// OSPG
    OSPG,
    /// OSGP
    OSGP,
    /// OPSG
    OPSG,
    /// OPGS
    OPGS,
    /// OGSP
    OGSP,
    /// OGPS
    OGPS,
    /// GSPO
    GSPO,
    /// GSOP
    GSOP,
    /// GPSO
    GPSO,
    /// GPOS
    GPOS,
    /// GOSP
    GOSP,
    /// GOPS
    GOPS,
}

impl Order {
    /// Index to be used for sorting, by decreasing order of relevance
    pub fn idx(&self) -> [usize; 4] {
        use Order::*;
        match self {
            SPOG => [0, 1, 2, 3],
            SPGO => [0, 1, 3, 2],
            SOPG => [0, 2, 1, 3],
            SOGP => [0, 2, 3, 1],
            SGPO => [0, 3, 1, 2],
            SGOP => [0, 3, 2, 1],
            PSOG => [1, 0, 2, 3],
            PSGO => [1, 0, 3, 2],
            POSG => [1, 2, 0, 3],
            POGS => [1, 2, 3, 0],
            PGSO => [1, 3, 0, 2],
            PGOS => [1, 3, 2, 0],
            OSPG => [2, 0, 1, 3],
            OSGP => [2, 0, 3, 1],
            OPSG => [2, 1, 0, 3],
            OPGS => [2, 1, 3, 0],
            OGSP => [2, 3, 0, 1],
            OGPS => [2, 3, 1, 0],
            GSPO => [3, 0, 1, 2],
            GSOP => [3, 0, 2, 1],
            GPSO => [3, 1, 0, 2],
            GPOS => [3, 1, 2, 0],
            GOSP => [3, 2, 0, 1],
            GOPS => [3, 2, 1, 0],
        }
    }
}

impl Default for Order {
    fn default() -> Order {
        Order::SPOG
    }
}

//

/// "RunTime Slim Block":
/// a [`Block`] implementation where the sorting order is decided at runtime
/// and managed by permutating the elements of the block.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct RtsBlock<I: Identifier>([I; 4]);

impl<I: Identifier> Block<I> for RtsBlock<I> {
    type Param = Order;

    fn new(spog: [I; 4], order: Order) -> Self {
        let mut inner = [I::MIN; 4];
        for (i, j) in order.idx().iter().enumerate() {
            inner[i] = spog[*j];
        }
        RtsBlock(inner)
    }

    fn spog(&self, param: Order) -> [I; 4] {
        let mut spog = [I::MIN; 4];
        for (i, j) in param.idx().iter().enumerate() {
            spog[*j] = self.0[i];
        }
        spog
    }

    fn priority_for(spog_pattern: &[Option<I>; 4], param: Order) -> u8 {
        let mut ret = 0;
        for i in param.idx().iter() {
            match spog_pattern[*i] {
                Some(_) => ret += 1,
                None => break,
            }
        }
        ret
    }

    fn range_and_filter(
        mut spog_pattern: [Option<I>; 4],
        param: Order,
    ) -> (RangeInclusive<Self>, [Option<I>; 4]) {
        let mut bmin = Self::new([I::MIN; 4], param);
        let mut bmax = Self::new([I::MAX; 4], param);
        for (i, j) in param.idx().iter().copied().enumerate() {
            match spog_pattern[j] {
                None => break,
                Some(val) => {
                    bmin.0[i] = val;
                    bmax.0[i] = val;
                    spog_pattern[j] = None;
                }
            }
        }
        (bmin..=bmax, spog_pattern)
    }
}

//
// #####  #####   ####  #####   ####
//   #    #      #        #    #
//   #    ###     ###     #     ###
//   #    #          #    #        #
//   #    #####  ####     #    ####
//

macro_rules! rtblock_test {
    ($mod: ident, $typ: ident) => {
        #[cfg(test)]
        mod $mod {
            use super::*;
            use Order::{GSPO, SPOG};

            type RtBlock<I> = $typ<I>;

            #[test]
            fn spog_cmp() {
                assert!(RtBlock::new([1, 1, 1, 1], SPOG) <= RtBlock::new([1, 1, 1, 1], SPOG));
                assert!(RtBlock::new([1, 1, 1, 1], SPOG) < RtBlock::new([1, 1, 1, 2], SPOG));
                assert!(RtBlock::new([1, 1, 1, 1], SPOG) < RtBlock::new([1, 1, 2, 0], SPOG));
                assert!(RtBlock::new([1, 1, 1, 1], SPOG) < RtBlock::new([1, 2, 0, 0], SPOG));
                assert!(RtBlock::new([1, 1, 1, 1], SPOG) < RtBlock::new([2, 0, 0, 0], SPOG));
            }

            #[test]
            fn spog_priority() {
                assert_eq!(RtBlock::priority_for(&p(0, 0, 0, 0), SPOG), 0);
                assert_eq!(RtBlock::priority_for(&p(1, 0, 0, 0), SPOG), 1);
                assert_eq!(RtBlock::priority_for(&p(0, 1, 0, 0), SPOG), 0);
                assert_eq!(RtBlock::priority_for(&p(0, 0, 1, 0), SPOG), 0);
                assert_eq!(RtBlock::priority_for(&p(0, 0, 0, 1), SPOG), 0);
                assert_eq!(RtBlock::priority_for(&p(1, 1, 0, 0), SPOG), 2);
                assert_eq!(RtBlock::priority_for(&p(0, 1, 1, 0), SPOG), 0);
                assert_eq!(RtBlock::priority_for(&p(0, 0, 1, 1), SPOG), 0);
                assert_eq!(RtBlock::priority_for(&p(1, 1, 0, 1), SPOG), 2);
                assert_eq!(RtBlock::priority_for(&p(1, 1, 1, 0), SPOG), 3);
                assert_eq!(RtBlock::priority_for(&p(1, 1, 1, 1), SPOG), 4);
            }

            #[test]
            fn spog_range_and_filter() {
                let rf = |p| RtBlock::range_and_filter(p, SPOG);
                let b = |s, p, o, g| bo(s, p, o, g, SPOG);
                assert_eq!(
                    rf(p(0, 0, 0, 0)),
                    (b(0, 0, 0, 0)..=b(9, 9, 9, 9), p(0, 0, 0, 0))
                );
                assert_eq!(
                    rf(p(1, 0, 0, 0)),
                    (b(1, 0, 0, 0)..=b(1, 9, 9, 9), p(0, 0, 0, 0))
                );
                assert_eq!(
                    rf(p(0, 2, 0, 0)),
                    (b(0, 0, 0, 0)..=b(9, 9, 9, 9), p(0, 2, 0, 0))
                );
                assert_eq!(
                    rf(p(0, 0, 3, 0)),
                    (b(0, 0, 0, 0)..=b(9, 9, 9, 9), p(0, 0, 3, 0))
                );
                assert_eq!(
                    rf(p(0, 0, 0, 4)),
                    (b(0, 0, 0, 0)..=b(9, 9, 9, 9), p(0, 0, 0, 4))
                );
                assert_eq!(
                    rf(p(1, 2, 0, 0)),
                    (b(1, 2, 0, 0)..=b(1, 2, 9, 9), p(0, 0, 0, 0))
                );
                assert_eq!(
                    rf(p(0, 2, 3, 0)),
                    (b(0, 0, 0, 0)..=b(9, 9, 9, 9), p(0, 2, 3, 0))
                );
                assert_eq!(
                    rf(p(0, 0, 3, 4)),
                    (b(0, 0, 0, 0)..=b(9, 9, 9, 9), p(0, 0, 3, 4))
                );
                assert_eq!(
                    rf(p(1, 2, 0, 4)),
                    (b(1, 2, 0, 0)..=b(1, 2, 9, 9), p(0, 0, 0, 4))
                );
                assert_eq!(
                    rf(p(1, 2, 3, 0)),
                    (b(1, 2, 3, 0)..=b(1, 2, 3, 9), p(0, 0, 0, 0))
                );
                assert_eq!(
                    rf(p(1, 2, 3, 4)),
                    (b(1, 2, 3, 4)..=b(1, 2, 3, 4), p(0, 0, 0, 0))
                );
            }

            #[test]
            fn gspo_cmp() {
                assert!(RtBlock::new([1, 1, 1, 1], GSPO) <= RtBlock::new([1, 1, 1, 1], GSPO));
                assert!(RtBlock::new([1, 1, 1, 1], GSPO) < RtBlock::new([1, 1, 2, 1], GSPO));
                assert!(RtBlock::new([1, 1, 1, 1], GSPO) < RtBlock::new([1, 2, 0, 1], GSPO));
                assert!(RtBlock::new([1, 1, 1, 1], GSPO) < RtBlock::new([2, 0, 0, 1], GSPO));
                assert!(RtBlock::new([1, 1, 1, 1], GSPO) < RtBlock::new([0, 0, 0, 2], GSPO));
            }

            #[test]
            fn gspo_priority() {
                assert_eq!(RtBlock::priority_for(&p(0, 0, 0, 0), GSPO), 0);
                assert_eq!(RtBlock::priority_for(&p(1, 0, 0, 0), GSPO), 0);
                assert_eq!(RtBlock::priority_for(&p(0, 1, 0, 0), GSPO), 0);
                assert_eq!(RtBlock::priority_for(&p(0, 0, 1, 0), GSPO), 0);
                assert_eq!(RtBlock::priority_for(&p(0, 0, 0, 1), GSPO), 1);
                assert_eq!(RtBlock::priority_for(&p(1, 1, 0, 0), GSPO), 0);
                assert_eq!(RtBlock::priority_for(&p(0, 1, 1, 0), GSPO), 0);
                assert_eq!(RtBlock::priority_for(&p(0, 0, 1, 1), GSPO), 1);
                assert_eq!(RtBlock::priority_for(&p(1, 0, 1, 1), GSPO), 2);
                assert_eq!(RtBlock::priority_for(&p(1, 1, 0, 1), GSPO), 3);
                assert_eq!(RtBlock::priority_for(&p(1, 1, 1, 1), GSPO), 4);
            }

            #[test]
            fn gspo_range_and_filter() {
                let rf = |p| RtBlock::range_and_filter(p, GSPO);
                let b = |s, p, o, g| bo(s, p, o, g, GSPO);
                assert_eq!(
                    rf(p(0, 0, 0, 0)),
                    (b(0, 0, 0, 0)..=b(9, 9, 9, 9), p(0, 0, 0, 0))
                );
                assert_eq!(
                    rf(p(1, 0, 0, 0)),
                    (b(0, 0, 0, 0)..=b(9, 9, 9, 9), p(1, 0, 0, 0))
                );
                assert_eq!(
                    rf(p(0, 2, 0, 0)),
                    (b(0, 0, 0, 0)..=b(9, 9, 9, 9), p(0, 2, 0, 0))
                );
                assert_eq!(
                    rf(p(0, 0, 3, 0)),
                    (b(0, 0, 0, 0)..=b(9, 9, 9, 9), p(0, 0, 3, 0))
                );
                assert_eq!(
                    rf(p(0, 0, 0, 4)),
                    (b(0, 0, 0, 4)..=b(9, 9, 9, 4), p(0, 0, 0, 0))
                );
                assert_eq!(
                    rf(p(1, 2, 0, 0)),
                    (b(0, 0, 0, 0)..=b(9, 9, 9, 9), p(1, 2, 0, 0))
                );
                assert_eq!(
                    rf(p(0, 2, 3, 0)),
                    (b(0, 0, 0, 0)..=b(9, 9, 9, 9), p(0, 2, 3, 0))
                );
                assert_eq!(
                    rf(p(0, 0, 3, 4)),
                    (b(0, 0, 0, 4)..=b(9, 9, 9, 4), p(0, 0, 3, 0))
                );
                assert_eq!(
                    rf(p(1, 0, 3, 4)),
                    (b(1, 0, 0, 4)..=b(1, 9, 9, 4), p(0, 0, 3, 0))
                );
                assert_eq!(
                    rf(p(1, 2, 0, 4)),
                    (b(1, 2, 0, 4)..=b(1, 2, 9, 4), p(0, 0, 0, 0))
                );
                assert_eq!(
                    rf(p(1, 2, 3, 4)),
                    (b(1, 2, 3, 4)..=b(1, 2, 3, 4), p(0, 0, 0, 0))
                );
            }

            /// Block constructor, where 9 is interpreted as usize::MAX
            fn bo(s: usize, p: usize, o: usize, g: usize, ord: Order) -> RtBlock<usize> {
                [max9(s), max9(p), max9(o), max9(g)].into_block(ord)
            }

            /// Pattern constructor, where
            /// - 0 is interpreted as None,
            /// - other values are interpreted as Some(value),
            /// - 9 is interpreted as Some(usize::MAX)
            fn p(s: usize, p: usize, o: usize, g: usize) -> [Option<usize>; 4] {
                [i2opt(s), i2opt(p), i2opt(o), i2opt(g)]
            }

            /// Convenient conversion of usize where 9 is interpretted as MAX, used by b(), p() and p() above.
            fn max9(i: usize) -> usize {
                match i {
                    9 => usize::MAX,
                    n => n,
                }
            }

            /// Convenient conversion of usize to Option<usize>, used by p() and p() above.
            fn i2opt(i: usize) -> Option<usize> {
                match i {
                    0 => None,
                    n => Some(max9(n)),
                }
            }
        }
    };
}

rtblock_test!(test_rtf, RtfBlock);
rtblock_test!(test_rts, RtsBlock);
