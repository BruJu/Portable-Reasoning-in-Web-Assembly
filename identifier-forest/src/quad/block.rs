//! Define the trait [`Block`] and a number of implementations.
use crate::Identifier;
use std::cmp::Ordering;
use std::fmt::Debug;
use std::hash::Hash;
use std::ops::{Deref, DerefMut, RangeInclusive};

/// A wrapper around `[I; 4]` providing its own sorting order.
///
/// # Contract
///
/// Implementations of this trait MUST provide zero-cost conversion to and from `[I; 4]`,
/// via [`From`] and [`Into`].
pub trait Block<I: Identifier>:
    Clone
    + Copy
    + Debug
    + Eq
    + From<[I; 4]>
    + Into<[I; 4]>
    + Hash
    + Ord
    + PartialEq
    + PartialOrd
    + Deref<Target = [I; 4]>
    + DerefMut
{
    /// From most significant to least significant, the index of a SPOG pattern considered by this [`Block`]'s order.
    const IDX: [usize; 4];

    /// Return true if this block matches the given pattern.
    ///
    /// See [`iter_matching`](super::QuadForest::iter_matching)
    fn matches(&self, spog_pattern: &[Option<I>; 4]) -> bool {
        self.iter()
            .zip(spog_pattern.iter())
            .all(|(val, opt)| match opt {
                None => true,
                Some(other) => val == other,
            })
    }

    /// Return the number of initial `Some`s in the given pattern,
    /// in the order specified for this [`Block`] type.
    fn priority_for(spog_pattern: &[Option<I>; 4]) -> u8 {
        let mut ret = 0;
        for i in Self::IDX.iter() {
            match spog_pattern[*i] {
                Some(_) => ret += 1,
                None => break,
            }
        }
        ret
    }

    /// Return, for the given pattern:
    /// * the most specific range (according to the order of this [`Block`])
    ///   containing all matching quads, and
    /// * the simplest pattern required to filter spurious quads from this range.
    fn range_and_filter(
        mut spog_pattern: [Option<I>; 4],
    ) -> (RangeInclusive<Self>, [Option<I>; 4]) {
        let mut bmin = Self::from([I::MIN; 4]);
        let mut bmax = Self::from([I::MAX; 4]);
        for i in Self::IDX.iter() {
            let i = *i;
            match spog_pattern[i] {
                None => break,
                Some(val) => {
                    bmin[i] = val;
                    bmax[i] = val;
                    spog_pattern[i] = None;
                }
            }
        }
        (bmin..=bmax, spog_pattern)
    }

    /// Zero-cost conversion from one type of [`Block`] to another.
    fn convert<B: Block<I>>(self) -> B {
        let a: [I; 4] = self.into();
        a.into()
    }
}

macro_rules! make_block_impl {
    ($typ: ident, $i0: expr, $i1: expr, $i2: expr, $i3: expr, $mod: ident) => {
        mod $mod {
            use super::*;

            /// A [`Block`] implementation.
            #[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
            pub struct $typ<I = usize>(pub [I; 4]);

            impl<I: Identifier> Deref for $typ<I> {
                type Target = [I; 4];
                fn deref(&self) -> &Self::Target {
                    &self.0
                }
            }

            impl<I: Identifier> DerefMut for $typ<I> {
                fn deref_mut(&mut self) -> &mut Self::Target {
                    &mut self.0
                }
            }

            impl<I: Identifier> From<[I; 4]> for $typ<I> {
                fn from(other: [I; 4]) -> Self {
                    $typ(other)
                }
            }

            impl<I: Identifier> From<$typ<I>> for [I; 4] {
                fn from(other: $typ<I>) -> Self {
                    other.0
                }
            }

            impl<I: Identifier> Ord for $typ<I> {
                fn cmp(&self, other: &Self) -> Ordering {
                    self[$i0]
                        .cmp(&other[$i0])
                        .then_with(|| self[$i1].cmp(&other[$i1]))
                        .then_with(|| self[$i2].cmp(&other[$i2]))
                        .then_with(|| self[$i3].cmp(&other[$i3]))
                }
            }

            impl<I: Identifier> PartialOrd for $typ<I> {
                fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
                    Some(self.cmp(other))
                }
            }

            impl<I: Identifier> Block<I> for $typ<I> {
                const IDX: [usize; 4] = [$i0, $i1, $i2, $i3];
            }

            #[cfg(test)]
            mod test {
                #[test]
                fn is_consistent() {
                    let idx = [$i0, $i1, $i2, $i3];
                    assert!(idx.contains(&0));
                    assert!(idx.contains(&1));
                    assert!(idx.contains(&2));
                    assert!(idx.contains(&3));
                }
            }
        }
        pub use self::$mod::$typ;
    };
}

make_block_impl!(SPOG, 0, 1, 2, 3, spog);
make_block_impl!(GSPO, 3, 0, 1, 2, gspo);
make_block_impl!(OPSG, 2, 1, 0, 3, opsg);
make_block_impl!(PGSO, 1, 3, 0, 2, pgso);
make_block_impl!(GOPS, 3, 2, 1, 0, gops);
make_block_impl!(SOGP, 0, 2, 3, 1, sogp);

//
// #####  #####   ####  #####   ####
//   #    #      #        #    #
//   #    ###     ###     #     ###
//   #    #          #    #        #
//   #    #####  ####     #    ####
//

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn spog_cmp() {
        assert!(SPOG([1, 1, 1, 1]) <= SPOG([1, 1, 1, 1]));
        assert!(SPOG([1, 1, 1, 1]) < SPOG([1, 1, 1, 2]));
        assert!(SPOG([1, 1, 1, 1]) < SPOG([1, 1, 2, 0]));
        assert!(SPOG([1, 1, 1, 1]) < SPOG([1, 2, 0, 0]));
        assert!(SPOG([1, 1, 1, 1]) < SPOG([2, 0, 0, 0]));
    }

    #[test]
    fn spog_priority() {
        assert_eq!(SPOG::priority_for(&p(0, 0, 0, 0)), 0);
        assert_eq!(SPOG::priority_for(&p(1, 0, 0, 0)), 1);
        assert_eq!(SPOG::priority_for(&p(0, 1, 0, 0)), 0);
        assert_eq!(SPOG::priority_for(&p(0, 0, 1, 0)), 0);
        assert_eq!(SPOG::priority_for(&p(0, 0, 0, 1)), 0);
        assert_eq!(SPOG::priority_for(&p(1, 1, 0, 0)), 2);
        assert_eq!(SPOG::priority_for(&p(0, 1, 1, 0)), 0);
        assert_eq!(SPOG::priority_for(&p(0, 0, 1, 1)), 0);
        assert_eq!(SPOG::priority_for(&p(1, 1, 0, 1)), 2);
        assert_eq!(SPOG::priority_for(&p(1, 1, 1, 0)), 3);
        assert_eq!(SPOG::priority_for(&p(1, 1, 1, 1)), 4);
    }

    #[test]
    fn spog_range_and_filter() {
        let rf = SPOG::range_and_filter;
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
        assert!(GSPO([1, 1, 1, 1]) <= GSPO([1, 1, 1, 1]));
        assert!(GSPO([1, 1, 1, 1]) < GSPO([1, 1, 2, 1]));
        assert!(GSPO([1, 1, 1, 1]) < GSPO([1, 2, 0, 1]));
        assert!(GSPO([1, 1, 1, 1]) < GSPO([2, 0, 0, 1]));
        assert!(GSPO([1, 1, 1, 1]) < GSPO([0, 0, 0, 2]));
    }

    #[test]
    fn gspo_priority() {
        assert_eq!(GSPO::priority_for(&p(0, 0, 0, 0)), 0);
        assert_eq!(GSPO::priority_for(&p(1, 0, 0, 0)), 0);
        assert_eq!(GSPO::priority_for(&p(0, 1, 0, 0)), 0);
        assert_eq!(GSPO::priority_for(&p(0, 0, 1, 0)), 0);
        assert_eq!(GSPO::priority_for(&p(0, 0, 0, 1)), 1);
        assert_eq!(GSPO::priority_for(&p(1, 1, 0, 0)), 0);
        assert_eq!(GSPO::priority_for(&p(0, 1, 1, 0)), 0);
        assert_eq!(GSPO::priority_for(&p(0, 0, 1, 1)), 1);
        assert_eq!(GSPO::priority_for(&p(1, 0, 1, 1)), 2);
        assert_eq!(GSPO::priority_for(&p(1, 1, 0, 1)), 3);
        assert_eq!(GSPO::priority_for(&p(1, 1, 1, 1)), 4);
    }

    #[test]
    fn gspo_range_and_filter() {
        let rf = GSPO::range_and_filter;
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

    #[test]
    fn opsg_cmp() {
        assert!(OPSG([1, 1, 1, 1]) <= OPSG([1, 1, 1, 1]));
        assert!(OPSG([1, 1, 1, 1]) < OPSG([1, 1, 1, 2]));
        assert!(OPSG([1, 1, 1, 1]) < OPSG([2, 1, 1, 0]));
        assert!(OPSG([1, 1, 1, 1]) < OPSG([0, 2, 1, 0]));
        assert!(OPSG([1, 1, 1, 1]) < OPSG([0, 0, 2, 0]));
    }

    #[test]
    fn opsg_priority() {
        assert_eq!(OPSG::priority_for(&p(0, 0, 0, 0)), 0);
        assert_eq!(OPSG::priority_for(&p(1, 0, 0, 0)), 0);
        assert_eq!(OPSG::priority_for(&p(0, 1, 0, 0)), 0);
        assert_eq!(OPSG::priority_for(&p(0, 0, 1, 0)), 1);
        assert_eq!(OPSG::priority_for(&p(0, 0, 0, 1)), 0);
        assert_eq!(OPSG::priority_for(&p(1, 1, 0, 0)), 0);
        assert_eq!(OPSG::priority_for(&p(0, 1, 1, 0)), 2);
        assert_eq!(OPSG::priority_for(&p(0, 0, 1, 1)), 1);
        assert_eq!(OPSG::priority_for(&p(0, 1, 1, 1)), 2);
        assert_eq!(OPSG::priority_for(&p(1, 1, 1, 0)), 3);
        assert_eq!(OPSG::priority_for(&p(1, 1, 1, 1)), 4);
    }

    #[test]
    fn opsg_range_and_filter() {
        let rf = OPSG::range_and_filter;
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
            (b(0, 0, 3, 0)..=b(9, 9, 3, 9), p(0, 0, 0, 0))
        );
        assert_eq!(
            rf(p(0, 0, 0, 4)),
            (b(0, 0, 0, 0)..=b(9, 9, 9, 9), p(0, 0, 0, 4))
        );
        assert_eq!(
            rf(p(1, 2, 0, 0)),
            (b(0, 0, 0, 0)..=b(9, 9, 9, 9), p(1, 2, 0, 0))
        );
        assert_eq!(
            rf(p(0, 2, 3, 0)),
            (b(0, 2, 3, 0)..=b(9, 2, 3, 9), p(0, 0, 0, 0))
        );
        assert_eq!(
            rf(p(0, 0, 3, 4)),
            (b(0, 0, 3, 0)..=b(9, 9, 3, 9), p(0, 0, 0, 4))
        );
        assert_eq!(
            rf(p(0, 2, 3, 4)),
            (b(0, 2, 3, 0)..=b(9, 2, 3, 9), p(0, 0, 0, 4))
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
    fn pgso_cmp() {
        assert!(PGSO([1, 1, 1, 1]) <= PGSO([1, 1, 1, 1]));
        assert!(PGSO([1, 1, 1, 1]) < PGSO([1, 1, 2, 1]));
        assert!(PGSO([1, 1, 1, 1]) < PGSO([2, 1, 0, 1]));
        assert!(PGSO([1, 1, 1, 1]) < PGSO([0, 1, 0, 2]));
        assert!(PGSO([1, 1, 1, 1]) < PGSO([0, 2, 0, 0]));
    }

    #[test]
    fn pgso_priority() {
        assert_eq!(PGSO::priority_for(&p(0, 0, 0, 0)), 0);
        assert_eq!(PGSO::priority_for(&p(1, 0, 0, 0)), 0);
        assert_eq!(PGSO::priority_for(&p(0, 1, 0, 0)), 1);
        assert_eq!(PGSO::priority_for(&p(0, 0, 1, 0)), 0);
        assert_eq!(PGSO::priority_for(&p(0, 0, 0, 1)), 0);
        assert_eq!(PGSO::priority_for(&p(1, 1, 0, 0)), 1);
        assert_eq!(PGSO::priority_for(&p(0, 1, 1, 0)), 1);
        assert_eq!(PGSO::priority_for(&p(0, 0, 1, 1)), 0);
        assert_eq!(PGSO::priority_for(&p(0, 1, 1, 1)), 2);
        assert_eq!(PGSO::priority_for(&p(1, 1, 0, 1)), 3);
        assert_eq!(PGSO::priority_for(&p(1, 1, 1, 1)), 4);
    }

    #[test]
    fn pgso_range_and_filter() {
        let rf = PGSO::range_and_filter;
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
            (b(0, 2, 0, 0)..=b(9, 2, 9, 9), p(0, 0, 0, 0))
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
            (b(0, 2, 0, 0)..=b(9, 2, 9, 9), p(1, 0, 0, 0))
        );
        assert_eq!(
            rf(p(0, 2, 3, 0)),
            (b(0, 2, 0, 0)..=b(9, 2, 9, 9), p(0, 0, 3, 0))
        );
        assert_eq!(
            rf(p(0, 0, 3, 4)),
            (b(0, 0, 0, 0)..=b(9, 9, 9, 9), p(0, 0, 3, 4))
        );
        assert_eq!(
            rf(p(0, 2, 3, 4)),
            (b(0, 2, 0, 4)..=b(9, 2, 9, 4), p(0, 0, 3, 0))
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

    #[test]
    fn gops_cmp() {
        assert!(GOPS([1, 1, 1, 1]) <= GOPS([1, 1, 1, 1]));
        assert!(GOPS([1, 1, 1, 1]) < GOPS([2, 1, 1, 1]));
        assert!(GOPS([1, 1, 1, 1]) < GOPS([0, 2, 1, 1]));
        assert!(GOPS([1, 1, 1, 1]) < GOPS([0, 0, 2, 1]));
        assert!(GOPS([1, 1, 1, 1]) < GOPS([0, 0, 0, 2]));
    }

    #[test]
    fn gops_priority() {
        assert_eq!(GOPS::priority_for(&p(0, 0, 0, 0)), 0);
        assert_eq!(GOPS::priority_for(&p(1, 0, 0, 0)), 0);
        assert_eq!(GOPS::priority_for(&p(0, 1, 0, 0)), 0);
        assert_eq!(GOPS::priority_for(&p(0, 0, 1, 0)), 0);
        assert_eq!(GOPS::priority_for(&p(0, 0, 0, 1)), 1);
        assert_eq!(GOPS::priority_for(&p(1, 1, 0, 0)), 0);
        assert_eq!(GOPS::priority_for(&p(0, 1, 1, 0)), 0);
        assert_eq!(GOPS::priority_for(&p(0, 0, 1, 1)), 2);
        assert_eq!(GOPS::priority_for(&p(1, 0, 1, 1)), 2);
        assert_eq!(GOPS::priority_for(&p(0, 1, 1, 1)), 3);
        assert_eq!(GOPS::priority_for(&p(1, 1, 1, 1)), 4);
    }

    #[test]
    fn gops_range_and_filter() {
        let rf = GOPS::range_and_filter;
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
            (b(0, 0, 3, 4)..=b(9, 9, 3, 4), p(0, 0, 0, 0))
        );
        assert_eq!(
            rf(p(1, 0, 3, 4)),
            (b(0, 0, 3, 4)..=b(9, 9, 3, 4), p(1, 0, 0, 0))
        );
        assert_eq!(
            rf(p(0, 2, 3, 4)),
            (b(0, 2, 3, 4)..=b(9, 2, 3, 4), p(0, 0, 0, 0))
        );
        assert_eq!(
            rf(p(1, 2, 3, 4)),
            (b(1, 2, 3, 4)..=b(1, 2, 3, 4), p(0, 0, 0, 0))
        );
    }

    #[test]
    fn sogp_cmp() {
        assert!(SOGP([1, 1, 1, 1]) <= SOGP([1, 1, 1, 1]));
        assert!(SOGP([1, 1, 1, 1]) < SOGP([1, 2, 1, 1]));
        assert!(SOGP([1, 1, 1, 1]) < SOGP([1, 0, 1, 2]));
        assert!(SOGP([1, 1, 1, 1]) < SOGP([1, 0, 2, 0]));
        assert!(SOGP([1, 1, 1, 1]) < SOGP([2, 0, 0, 0]));
    }

    #[test]
    fn sogp_priority() {
        assert_eq!(SOGP::priority_for(&p(0, 0, 0, 0)), 0);
        assert_eq!(SOGP::priority_for(&p(1, 0, 0, 0)), 1);
        assert_eq!(SOGP::priority_for(&p(0, 1, 0, 0)), 0);
        assert_eq!(SOGP::priority_for(&p(0, 0, 1, 0)), 0);
        assert_eq!(SOGP::priority_for(&p(0, 0, 0, 1)), 0);
        assert_eq!(SOGP::priority_for(&p(1, 1, 0, 0)), 1);
        assert_eq!(SOGP::priority_for(&p(0, 1, 1, 0)), 0);
        assert_eq!(SOGP::priority_for(&p(0, 0, 1, 1)), 0);
        assert_eq!(SOGP::priority_for(&p(1, 1, 1, 0)), 2);
        assert_eq!(SOGP::priority_for(&p(1, 0, 1, 1)), 3);
        assert_eq!(SOGP::priority_for(&p(1, 1, 1, 1)), 4);
    }

    #[test]
    fn sogp_range_and_filter() {
        let rf = SOGP::range_and_filter;
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
            (b(1, 0, 0, 0)..=b(1, 9, 9, 9), p(0, 2, 0, 0))
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
            rf(p(1, 2, 3, 0)),
            (b(1, 0, 3, 0)..=b(1, 9, 3, 9), p(0, 2, 0, 0))
        );
        assert_eq!(
            rf(p(1, 0, 3, 4)),
            (b(1, 0, 3, 4)..=b(1, 9, 3, 4), p(0, 0, 0, 0))
        );
        assert_eq!(
            rf(p(1, 2, 3, 4)),
            (b(1, 2, 3, 4)..=b(1, 2, 3, 4), p(0, 0, 0, 0))
        );
    }

    /// Block constructor, where 9 is interpreted as usize::MAX
    fn b<B: Block<usize>>(s: usize, p: usize, o: usize, g: usize) -> B {
        [max9(s), max9(p), max9(o), max9(g)].into()
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
