//! Define the trait [`Block`] and a number of implementations.
use crate::Identifier;
use std::cmp::Ordering;
use std::fmt::Debug;
use std::hash::Hash;
use std::ops::RangeInclusive;

/// A wrapper around `[I; 4]` providing its own sorting order.
pub trait Block<I: Identifier>:
    Clone + Copy + Debug + Eq + Hash + Ord + PartialEq + PartialOrd
{
    /// Parameter type
    ///
    /// This type can be used to fine-tune the behaviour or some implementations,
    /// for example decide on the sorting order at runtime for
    /// [`RtfBlock`](super::RtfBlock) and [`RtsBlock`](super::RtsBlock).
    ///
    type Param: Copy + Clone + Default;

    /// Build a new block from the given data and parameter
    fn new(data: [I; 4], param: Self::Param) -> Self;

    /// Get a copy of the content of this block, in SPOG order.
    fn spog(&self, param: Self::Param) -> [I; 4];

    /// Return the number of initial `Some`s in the given pattern,
    /// in the order specified for this [`Block`] type.
    fn priority_for(spog_pattern: &[Option<I>; 4], param: Self::Param) -> u8;

    /// Return, for the given pattern:
    /// * the most specific range (according to the order of this [`Block`])
    ///   containing all matching quads, and
    /// * the simplest pattern required to filter spurious quads from this range.
    fn range_and_filter(
        spog_pattern: [Option<I>; 4],
        param: Self::Param,
    ) -> (RangeInclusive<Self>, [Option<I>; 4]);

    /// Return true if this block matches the given pattern.
    ///
    /// See [`iter_matching`](super::QuadForest::iter_matching)
    fn matches(&self, spog_pattern: &[Option<I>; 4], param: Self::Param) -> bool {
        self.spog(param)
            .iter()
            .zip(spog_pattern.iter())
            .all(|(val, opt)| match opt {
                None => true,
                Some(other) => val == other,
            })
    }
}

macro_rules! make_block_impl {
    ($typ: ident, $i0: expr, $i1: expr, $i2: expr, $i3: expr, $mod: ident) => {
        mod $mod {
            use super::*;

            /// A [`Block`] implementation.
            #[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
            pub struct $typ<I = usize>(pub [I; 4]);

            impl<I: Identifier> Ord for $typ<I> {
                fn cmp(&self, other: &Self) -> Ordering {
                    self.0[$i0]
                        .cmp(&other.0[$i0])
                        .then_with(|| self.0[$i1].cmp(&other.0[$i1]))
                        .then_with(|| self.0[$i2].cmp(&other.0[$i2]))
                        .then_with(|| self.0[$i3].cmp(&other.0[$i3]))
                }
            }

            impl<I: Identifier> PartialOrd for $typ<I> {
                fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
                    Some(self.cmp(other))
                }
            }

            impl<I: Identifier> Block<I> for $typ<I> {
                type Param = ();

                fn new(data: [I; 4], _param: ()) -> Self {
                    $typ(data)
                }

                fn spog(&self, _param: ()) -> [I; 4] {
                    self.0
                }

                fn priority_for(spog_pattern: &[Option<I>; 4], _param: ()) -> u8 {
                    let mut ret = 0;
                    for i in [$i0, $i1, $i2, $i3].iter() {
                        match spog_pattern[*i] {
                            Some(_) => ret += 1,
                            None => break,
                        }
                    }
                    ret
                }

                fn range_and_filter(
                    mut spog_pattern: [Option<I>; 4],
                    _param: (),
                ) -> (RangeInclusive<Self>, [Option<I>; 4]) {
                    let mut bmin = Self::new([I::MIN; 4], ());
                    let mut bmax = Self::new([I::MAX; 4], ());
                    for i in [$i0, $i1, $i2, $i3].iter().copied() {
                        match spog_pattern[i] {
                            None => break,
                            Some(val) => {
                                bmin.0[i] = val;
                                bmax.0[i] = val;
                                spog_pattern[i] = None;
                            }
                        }
                    }
                    (bmin..=bmax, spog_pattern)
                }
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

/// Extension trait to add a method for `[I; 4]`, where `I` implements [`Identifier`].
pub trait IntoBlock<I: Identifier, B: Block<I>> {
    /// Convert this array into a [`Block`] using the given parameter
    fn into_block(self, param: B::Param) -> B;
}
impl<I: Identifier, B: Block<I>> IntoBlock<I, B> for [I; 4] {
    fn into_block(self, param: B::Param) -> B {
        B::new(self, param)
    }
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
        assert_eq!(SPOG::priority_for(&p(0, 0, 0, 0), ()), 0);
        assert_eq!(SPOG::priority_for(&p(1, 0, 0, 0), ()), 1);
        assert_eq!(SPOG::priority_for(&p(0, 1, 0, 0), ()), 0);
        assert_eq!(SPOG::priority_for(&p(0, 0, 1, 0), ()), 0);
        assert_eq!(SPOG::priority_for(&p(0, 0, 0, 1), ()), 0);
        assert_eq!(SPOG::priority_for(&p(1, 1, 0, 0), ()), 2);
        assert_eq!(SPOG::priority_for(&p(0, 1, 1, 0), ()), 0);
        assert_eq!(SPOG::priority_for(&p(0, 0, 1, 1), ()), 0);
        assert_eq!(SPOG::priority_for(&p(1, 1, 0, 1), ()), 2);
        assert_eq!(SPOG::priority_for(&p(1, 1, 1, 0), ()), 3);
        assert_eq!(SPOG::priority_for(&p(1, 1, 1, 1), ()), 4);
    }

    #[test]
    fn spog_range_and_filter() {
        let rf = |p| SPOG::range_and_filter(p, ());
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
        assert_eq!(GSPO::priority_for(&p(0, 0, 0, 0), ()), 0);
        assert_eq!(GSPO::priority_for(&p(1, 0, 0, 0), ()), 0);
        assert_eq!(GSPO::priority_for(&p(0, 1, 0, 0), ()), 0);
        assert_eq!(GSPO::priority_for(&p(0, 0, 1, 0), ()), 0);
        assert_eq!(GSPO::priority_for(&p(0, 0, 0, 1), ()), 1);
        assert_eq!(GSPO::priority_for(&p(1, 1, 0, 0), ()), 0);
        assert_eq!(GSPO::priority_for(&p(0, 1, 1, 0), ()), 0);
        assert_eq!(GSPO::priority_for(&p(0, 0, 1, 1), ()), 1);
        assert_eq!(GSPO::priority_for(&p(1, 0, 1, 1), ()), 2);
        assert_eq!(GSPO::priority_for(&p(1, 1, 0, 1), ()), 3);
        assert_eq!(GSPO::priority_for(&p(1, 1, 1, 1), ()), 4);
    }

    #[test]
    fn gspo_range_and_filter() {
        let rf = |p| GSPO::range_and_filter(p, ());
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
        assert_eq!(OPSG::priority_for(&p(0, 0, 0, 0), ()), 0);
        assert_eq!(OPSG::priority_for(&p(1, 0, 0, 0), ()), 0);
        assert_eq!(OPSG::priority_for(&p(0, 1, 0, 0), ()), 0);
        assert_eq!(OPSG::priority_for(&p(0, 0, 1, 0), ()), 1);
        assert_eq!(OPSG::priority_for(&p(0, 0, 0, 1), ()), 0);
        assert_eq!(OPSG::priority_for(&p(1, 1, 0, 0), ()), 0);
        assert_eq!(OPSG::priority_for(&p(0, 1, 1, 0), ()), 2);
        assert_eq!(OPSG::priority_for(&p(0, 0, 1, 1), ()), 1);
        assert_eq!(OPSG::priority_for(&p(0, 1, 1, 1), ()), 2);
        assert_eq!(OPSG::priority_for(&p(1, 1, 1, 0), ()), 3);
        assert_eq!(OPSG::priority_for(&p(1, 1, 1, 1), ()), 4);
    }

    #[test]
    fn opsg_range_and_filter() {
        let rf = |p| OPSG::range_and_filter(p, ());
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
        assert_eq!(PGSO::priority_for(&p(0, 0, 0, 0), ()), 0);
        assert_eq!(PGSO::priority_for(&p(1, 0, 0, 0), ()), 0);
        assert_eq!(PGSO::priority_for(&p(0, 1, 0, 0), ()), 1);
        assert_eq!(PGSO::priority_for(&p(0, 0, 1, 0), ()), 0);
        assert_eq!(PGSO::priority_for(&p(0, 0, 0, 1), ()), 0);
        assert_eq!(PGSO::priority_for(&p(1, 1, 0, 0), ()), 1);
        assert_eq!(PGSO::priority_for(&p(0, 1, 1, 0), ()), 1);
        assert_eq!(PGSO::priority_for(&p(0, 0, 1, 1), ()), 0);
        assert_eq!(PGSO::priority_for(&p(0, 1, 1, 1), ()), 2);
        assert_eq!(PGSO::priority_for(&p(1, 1, 0, 1), ()), 3);
        assert_eq!(PGSO::priority_for(&p(1, 1, 1, 1), ()), 4);
    }

    #[test]
    fn pgso_range_and_filter() {
        let rf = |p| PGSO::range_and_filter(p, ());
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
        assert_eq!(GOPS::priority_for(&p(0, 0, 0, 0), ()), 0);
        assert_eq!(GOPS::priority_for(&p(1, 0, 0, 0), ()), 0);
        assert_eq!(GOPS::priority_for(&p(0, 1, 0, 0), ()), 0);
        assert_eq!(GOPS::priority_for(&p(0, 0, 1, 0), ()), 0);
        assert_eq!(GOPS::priority_for(&p(0, 0, 0, 1), ()), 1);
        assert_eq!(GOPS::priority_for(&p(1, 1, 0, 0), ()), 0);
        assert_eq!(GOPS::priority_for(&p(0, 1, 1, 0), ()), 0);
        assert_eq!(GOPS::priority_for(&p(0, 0, 1, 1), ()), 2);
        assert_eq!(GOPS::priority_for(&p(1, 0, 1, 1), ()), 2);
        assert_eq!(GOPS::priority_for(&p(0, 1, 1, 1), ()), 3);
        assert_eq!(GOPS::priority_for(&p(1, 1, 1, 1), ()), 4);
    }

    #[test]
    fn gops_range_and_filter() {
        let rf = |p| GOPS::range_and_filter(p, ());
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
        assert_eq!(SOGP::priority_for(&p(0, 0, 0, 0), ()), 0);
        assert_eq!(SOGP::priority_for(&p(1, 0, 0, 0), ()), 1);
        assert_eq!(SOGP::priority_for(&p(0, 1, 0, 0), ()), 0);
        assert_eq!(SOGP::priority_for(&p(0, 0, 1, 0), ()), 0);
        assert_eq!(SOGP::priority_for(&p(0, 0, 0, 1), ()), 0);
        assert_eq!(SOGP::priority_for(&p(1, 1, 0, 0), ()), 1);
        assert_eq!(SOGP::priority_for(&p(0, 1, 1, 0), ()), 0);
        assert_eq!(SOGP::priority_for(&p(0, 0, 1, 1), ()), 0);
        assert_eq!(SOGP::priority_for(&p(1, 1, 1, 0), ()), 2);
        assert_eq!(SOGP::priority_for(&p(1, 0, 1, 1), ()), 3);
        assert_eq!(SOGP::priority_for(&p(1, 1, 1, 1), ()), 4);
    }

    #[test]
    fn sogp_range_and_filter() {
        let rf = |p| SOGP::range_and_filter(p, ());
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
        [max9(s), max9(p), max9(o), max9(g)].into_block(B::Param::default())
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
