//! Define the type [`QuadForest`] and the trait [`QuadForestProfile`],
//! as well as a number of implementation of the latter.
use super::*;
use crate::Identifier;

use once_cell::sync::OnceCell;
use std::collections::BTreeSet;
use std::marker::PhantomData;
use std::mem::transmute;

/// A [`QuadForestProfile`] specifies how many trees a [`QuadForest`] will store,
/// which indexing order those trees will use,
/// and which of them must be built from the start
/// (others being built lazily, when required).
pub trait QuadForestProfile {
    /// The type of [`Identifier`]s used in the [`QuadForest`]
    type Identifier: Identifier;
    /// [`Block`]s used in the default tree
    type OrderDflt: Block<Self::Identifier>;
    /// [`Block`]s used in the first additional trees (if any, see [`USED`](Self::USED))
    type Order0: Block<Self::Identifier>;
    /// [`Block`]s used in the second additional trees (if any, see [`USED`](Self::USED))
    type Order1: Block<Self::Identifier>;
    /// [`Block`]s used in the third additional trees (if any, see [`USED`](Self::USED))
    type Order2: Block<Self::Identifier>;
    /// [`Block`]s used in the fourth additional trees (if any, see [`USED`](Self::USED))
    type Order3: Block<Self::Identifier>;
    /// [`Block`]s used in the fifth additional trees (if any, see [`USED`](Self::USED))
    type Order4: Block<Self::Identifier>;
    /// Number of additional trees to be actually used (between 0 and 5)
    const USED: usize;
    /// Number of additional trees that must be built from the start (between 0 and [`USED`](Self::USED))
    const PREBUILT: usize;
}

/// Type alias for the parameter type of the default order of a profile.
pub type ParamDflt<P> =
    <<P as QuadForestProfile>::OrderDflt as Block<<P as QuadForestProfile>::Identifier>>::Param;
/// Type alias for the parameter type of the first additional order of a profile.
pub type Param0<P> =
    <<P as QuadForestProfile>::Order0 as Block<<P as QuadForestProfile>::Identifier>>::Param;
/// Type alias for the parameter type of the second additional order of a profile.
pub type Param1<P> =
    <<P as QuadForestProfile>::Order1 as Block<<P as QuadForestProfile>::Identifier>>::Param;
/// Type alias for the parameter type of the third additional order of a profile.
pub type Param2<P> =
    <<P as QuadForestProfile>::Order2 as Block<<P as QuadForestProfile>::Identifier>>::Param;
/// Type alias for the parameter type of the fourth additional order of a profile.
pub type Param3<P> =
    <<P as QuadForestProfile>::Order3 as Block<<P as QuadForestProfile>::Identifier>>::Param;
/// Type alias for the parameter type of the fifth additional order of a profile.
pub type Param4<P> =
    <<P as QuadForestProfile>::Order4 as Block<<P as QuadForestProfile>::Identifier>>::Param;

/// A [`QuadForestProfile`] using SPOG order for the default tree,
/// and 5 more additional trees built lasily.
pub struct GSPOLazy<I = usize>(PhantomData<I>);
impl<I: Identifier> QuadForestProfile for GSPOLazy<I> {
    type Identifier = I;
    type OrderDflt = GSPO<I>;
    type Order0 = SPOG<I>;
    type Order1 = PGSO<I>;
    type Order2 = OPSG<I>;
    type Order3 = SOGP<I>;
    type Order4 = GOPS<I>;
    const USED: usize = 5;
    const PREBUILT: usize = 0;
}

/// A [`QuadForestProfile`] using SPOG order for the default tree,
/// and 5 more additional trees built from the start.
pub struct GSPOGreedy<I = usize>(PhantomData<I>);
impl<I: Identifier> QuadForestProfile for GSPOGreedy<I> {
    type Identifier = I;
    type OrderDflt = GSPO<I>;
    type Order0 = SPOG<I>;
    type Order1 = PGSO<I>;
    type Order2 = OPSG<I>;
    type Order3 = SOGP<I>;
    type Order4 = GOPS<I>;
    const USED: usize = 5;
    const PREBUILT: usize = 5;
}

/// A [`QuadForestProfile`] using SPOG order for the default tree,
/// and no additional tree.
pub struct GSPOLight<I = usize>(PhantomData<I>);
impl<I: Identifier> QuadForestProfile for GSPOLight<I> {
    type Identifier = I;
    type OrderDflt = GSPO<I>;
    type Order0 = SPOG<I>; // UNUSED
    type Order1 = PGSO<I>; // UNUSED
    type Order2 = OPSG<I>; // UNUSED
    type Order3 = SOGP<I>; // UNUSED
    type Order4 = GOPS<I>; // UNUSED
    const USED: usize = 0;
    const PREBUILT: usize = 0;
}

/// A [`QuadForestProfile`] using GSPO order for the default tree,
/// and no additional tree.
pub struct SPOGLight<I = usize>(PhantomData<I>);
impl<I: Identifier> QuadForestProfile for SPOGLight<I> {
    type Identifier = I;
    type OrderDflt = SPOG<I>;
    type Order0 = GSPO<I>; // UNUSED
    type Order1 = PGSO<I>; // UNUSED
    type Order2 = OPSG<I>; // UNUSED
    type Order3 = SOGP<I>; // UNUSED
    type Order4 = GOPS<I>; // UNUSED
    const USED: usize = 0;
    const PREBUILT: usize = 0;
}

/// A [`QuadForestProfile`] using runtime-defined orders,
/// and building up to 5 additional trees lazily.
///
/// In order to limit the number of indexes,
/// set the param of some additional tree to the same [`Order`](super::rt_block::Order)
/// as the default tree.
pub struct LazyRt<I = usize>(PhantomData<I>);
impl<I: Identifier> QuadForestProfile for LazyRt<I> {
    type Identifier = I;
    type OrderDflt = RtBlock<I>;
    type Order0 = RtBlock<I>;
    type Order1 = RtBlock<I>;
    type Order2 = RtBlock<I>;
    type Order3 = RtBlock<I>;
    type Order4 = RtBlock<I>;
    const USED: usize = 5;
    const PREBUILT: usize = 0;
}

/// A [`QuadForestProfile`] using runtime-defined orders,
/// and building 5 additional trees from the start.
pub struct GreedyRt<I = usize>(PhantomData<I>);
impl<I: Identifier> QuadForestProfile for GreedyRt<I> {
    type Identifier = I;
    type OrderDflt = RtBlock<I>;
    type Order0 = RtBlock<I>;
    type Order1 = RtBlock<I>;
    type Order2 = RtBlock<I>;
    type Order3 = RtBlock<I>;
    type Order4 = RtBlock<I>;
    const USED: usize = 5;
    const PREBUILT: usize = 5;
}

/// A [`QuadForest`] stores [`Identifier`] quads in up to 6 trees,
/// containing different types of [`Block`]s (sorted differently).
///
/// There are exactly 24 possible block orders (4!),
/// but optimally iterating over all quads matching a given pattern
/// (see [`iter_matching`](QuadForest::iter_matching))
/// only requires an appropriate selection of 6 indexing order.
/// This is because the fixed elements of a given pattern can be indexed in any order,
/// without changing the performances.
/// For example, in order to optimally find all quads matching (s, p, *, *),
/// any block order starting with SP or PS could be used.
pub struct QuadForest<P: QuadForestProfile> {
    default_tree: BTreeSet<P::OrderDflt>,
    trees: Vec<OnceCell<BTreeSet<P::OrderDflt>>>,
    param_default: ParamDflt<P>,
    #[allow(clippy::type_complexity)]
    params: (Param0<P>, Param1<P>, Param2<P>, Param3<P>, Param4<P>),
}

impl<P: QuadForestProfile> QuadForest<P> {
    /// Build an empty [`QuadForest`] complying with the profile `P`,
    /// using default values for the parameters of block orders.
    pub fn new() -> Self {
        Self::new_param(
            ParamDflt::<P>::default(),
            Param0::<P>::default(),
            Param1::<P>::default(),
            Param2::<P>::default(),
            Param3::<P>::default(),
            Param4::<P>::default(),
        )
    }

    /// Build an empty [`QuadForest`] complying with the profile `P`,
    /// providing explicit the parameters of block orders.
    pub fn new_param(
        param_default: ParamDflt<P>,
        param0: Param0<P>,
        param1: Param1<P>,
        param2: Param2<P>,
        param3: Param3<P>,
        param4: Param4<P>,
    ) -> Self {
        let this = Self::new_lazy(
            BTreeSet::new(),
            param_default,
            param0,
            param1,
            param2,
            param3,
            param4,
        );
        for i in 0..P::PREBUILT {
            this.trees[i].set(BTreeSet::new()).unwrap()
        }
        this
    }

    /// Build an empty [`QuadForest`] with no additional tree built.
    fn new_lazy(
        default_tree: BTreeSet<P::OrderDflt>,
        param_default: ParamDflt<P>,
        param0: Param0<P>,
        param1: Param1<P>,
        param2: Param2<P>,
        param3: Param3<P>,
        param4: Param4<P>,
    ) -> Self {
        debug_assert!(
            (0..=5).contains(&P::USED),
            "This profile is inconsistent, USED must be in [0;5]"
        );
        debug_assert!(
            (0..=P::USED).contains(&P::PREBUILT),
            "This profile is inconsistent, PREBUILT must be in [0;USED]"
        );
        debug_assert_eq!(
            std::mem::size_of::<P::OrderDflt>(),
            std::mem::size_of::<P::Order0>(),
            "All block orders of a profile must have the same size."
        );
        debug_assert_eq!(
            std::mem::size_of::<P::OrderDflt>(),
            std::mem::size_of::<P::Order1>(),
            "All block orders of a profile must have the same size."
        );
        debug_assert_eq!(
            std::mem::size_of::<P::OrderDflt>(),
            std::mem::size_of::<P::Order2>(),
            "All block orders of a profile must have the same size."
        );
        debug_assert_eq!(
            std::mem::size_of::<P::OrderDflt>(),
            std::mem::size_of::<P::Order3>(),
            "All block orders of a profile must have the same size."
        );
        debug_assert_eq!(
            std::mem::size_of::<P::OrderDflt>(),
            std::mem::size_of::<P::Order4>(),
            "All block orders of a profile must have the same size."
        );
        QuadForest {
            default_tree,
            trees: vec![OnceCell::new(); P::USED],
            param_default,
            params: (param0, param1, param2, param3, param4),
        }
    }

    /// The number of quads stored in this [`QuadForest`].
    pub fn len(&self) -> usize {
        self.default_tree.len()
    }

    /// Whether this [`QuadForest`] contains no quad.
    pub fn is_empty(&self) -> bool {
        self.default_tree.is_empty()
    }

    /// Whether this forest contains a given quad.
    pub fn contains(&self, spog_quad: [P::Identifier; 4]) -> bool {
        self.default_tree
            .contains(&spog_quad.into_block(self.param_default))
    }

    /// Iter over all the quads stored in this [`QuadForest`],
    /// using the default tree (see [`QuadForestProfile::OrderDflt`]).
    pub fn iter(&self) -> impl Iterator<Item = [P::Identifier; 4]> + '_ {
        self.default_tree.iter().copied().map(P::OrderDflt::into)
    }

    /// Iter over all the quads matching the given pattern,
    /// relying only on the already allocated trees.
    ///
    /// See also [`iter_matching`](Self::iter_matching).
    pub fn iter_matching_no_build(
        &self,
        spog_pattern: [Option<P::Identifier>; 4],
    ) -> Box<dyn Iterator<Item = [P::Identifier; 4]> + '_> {
        match dbg!(self.best_tree_no_build(&spog_pattern)) {
            -1 => iter_matching(&self.default_tree, spog_pattern, self.param_default),
            0 => iter_matching(self.get_tree0().unwrap(), spog_pattern, self.params.0),
            1 => iter_matching(self.get_tree1().unwrap(), spog_pattern, self.params.1),
            2 => iter_matching(self.get_tree2().unwrap(), spog_pattern, self.params.2),
            3 => iter_matching(self.get_tree3().unwrap(), spog_pattern, self.params.3),
            4 => iter_matching(self.get_tree4().unwrap(), spog_pattern, self.params.4),
            _ => unreachable!(),
        }
    }

    /// Iter over all the quads matching the given pattern.
    ///
    /// A quad matches the pattern if, for each position S, P, O and G:
    /// * the item of the pattern is `None`, or
    /// * the item of the pattern is `Some(value)`
    ///   and the corresponding item of the quad is `value`.
    ///
    /// This method will use the most suitable tree to find the matching quads,
    /// building it if necessary.
    ///
    /// See also [`iter_matching_no_build`](Self::iter_matching_no_build).
    pub fn iter_matching(
        &self,
        spog_pattern: [Option<P::Identifier>; 4],
    ) -> Box<dyn Iterator<Item = [P::Identifier; 4]> + '_> {
        match dbg!(self.best_tree(&spog_pattern)) {
            -1 => iter_matching(&self.default_tree, spog_pattern, self.param_default),
            0 => iter_matching(self.ensure_tree0(), spog_pattern, self.params.0),
            1 => iter_matching(self.ensure_tree1(), spog_pattern, self.params.1),
            2 => iter_matching(self.ensure_tree2(), spog_pattern, self.params.2),
            3 => iter_matching(self.ensure_tree3(), spog_pattern, self.params.3),
            4 => iter_matching(self.ensure_tree4(), spog_pattern, self.params.4),
            _ => unreachable!(),
        }
    }

    /// Insert a new quad in this [`QuadForest`].
    ///
    /// Return `true` if the quad was actually inserted,
    /// or `false` if it was already present before.
    pub fn insert(&mut self, spog: [P::Identifier; 4]) -> bool {
        let params = self.params; // copy required by the borrow checker
        if let Some(tree) = self.get_tree0_mut() {
            tree.insert(spog.into_block(params.0));
        }
        if let Some(tree) = self.get_tree1_mut() {
            tree.insert(spog.into_block(params.1));
        }
        if let Some(tree) = self.get_tree2_mut() {
            tree.insert(spog.into_block(params.2));
        }
        if let Some(tree) = self.get_tree3_mut() {
            tree.insert(spog.into_block(params.3));
        }
        if let Some(tree) = self.get_tree4_mut() {
            tree.insert(spog.into_block(params.4));
        }
        self.default_tree
            .insert(spog.into_block(self.param_default))
    }

    /// Remove a new quad from this [`QuadForest`].
    ///
    /// Return `true` if the quad was actually removed,
    /// or `false` if it was not found.
    pub fn remove(&mut self, spog: [P::Identifier; 4]) -> bool {
        let params = self.params; // copy required by the borrow checker
        if let Some(tree) = self.get_tree0_mut() {
            tree.remove(&spog.into_block(params.0));
        }
        if let Some(tree) = self.get_tree1_mut() {
            tree.remove(&spog.into_block(params.1));
        }
        if let Some(tree) = self.get_tree2_mut() {
            tree.remove(&spog.into_block(params.2));
        }
        if let Some(tree) = self.get_tree3_mut() {
            tree.remove(&spog.into_block(params.3));
        }
        if let Some(tree) = self.get_tree4_mut() {
            tree.remove(&spog.into_block(params.4));
        }
        self.default_tree
            .remove(&spog.into_block(self.param_default))
    }

    /// Borrow the underlying default tree
    pub fn default_tree(&self) -> &BTreeSet<P::OrderDflt> {
        &self.default_tree
    }

    /// Number of trees currently allocated (counting the default tree)
    pub fn nb_additional_trees(&self) -> usize {
        1 + self.trees.iter().filter(|i| i.get().is_some()).count()
    }

    fn get_tree0(&self) -> Option<&BTreeSet<P::Order0>> {
        unsafe { transmute(self.trees[0].get()) }
    }

    fn get_tree1(&self) -> Option<&BTreeSet<P::Order1>> {
        unsafe { transmute(self.trees[1].get()) }
    }

    fn get_tree2(&self) -> Option<&BTreeSet<P::Order2>> {
        unsafe { transmute(self.trees[2].get()) }
    }

    fn get_tree3(&self) -> Option<&BTreeSet<P::Order3>> {
        unsafe { transmute(self.trees[3].get()) }
    }

    fn get_tree4(&self) -> Option<&BTreeSet<P::Order4>> {
        unsafe { transmute(self.trees[4].get()) }
    }

    fn get_tree0_mut(&mut self) -> Option<&mut BTreeSet<P::Order0>> {
        if P::USED > 0 {
            unsafe { transmute(self.trees[0].get_mut()) }
        } else {
            None
        }
    }

    fn get_tree1_mut(&mut self) -> Option<&mut BTreeSet<P::Order1>> {
        if P::USED > 1 {
            unsafe { transmute(self.trees[1].get_mut()) }
        } else {
            None
        }
    }

    fn get_tree2_mut(&mut self) -> Option<&mut BTreeSet<P::Order2>> {
        if P::USED > 2 {
            unsafe { transmute(self.trees[2].get_mut()) }
        } else {
            None
        }
    }

    fn get_tree3_mut(&mut self) -> Option<&mut BTreeSet<P::Order3>> {
        if P::USED > 3 {
            unsafe { transmute(self.trees[3].get_mut()) }
        } else {
            None
        }
    }

    fn get_tree4_mut(&mut self) -> Option<&mut BTreeSet<P::Order4>> {
        if P::USED > 4 {
            unsafe { transmute(self.trees[4].get_mut()) }
        } else {
            None
        }
    }

    fn ensure_tree0(&self) -> &BTreeSet<P::Order0> {
        let tree = self.trees[0].get_or_init(|| {
            let tree: BTreeSet<P::Order0> = self
                .default_tree
                .iter()
                .map(|blk| blk.convert_with(self.params.0))
                .collect();
            unsafe { transmute(tree) }
        });
        unsafe { &*(tree as *const _ as *const _) } // convert from BTreeSet<[I;4]> to BTreeSet<Block>
    }

    fn ensure_tree1(&self) -> &BTreeSet<P::Order1> {
        let tree = self.trees[1].get_or_init(|| {
            let tree: BTreeSet<P::Order1> = self
                .default_tree
                .iter()
                .map(|blk| blk.convert_with(self.params.1))
                .collect();
            unsafe { transmute(tree) }
        });
        unsafe { &*(tree as *const _ as *const _) } // convert from BTreeSet<[I;4]> to BTreeSet<Block>
    }

    fn ensure_tree2(&self) -> &BTreeSet<P::Order2> {
        let tree = self.trees[2].get_or_init(|| {
            let tree: BTreeSet<P::Order2> = self
                .default_tree
                .iter()
                .map(|blk| blk.convert_with(self.params.2))
                .collect();
            unsafe { transmute(tree) }
        });
        unsafe { &*(tree as *const _ as *const _) } // convert from BTreeSet<[I;4]> to BTreeSet<Block>
    }

    fn ensure_tree3(&self) -> &BTreeSet<P::Order3> {
        let tree = self.trees[3].get_or_init(|| {
            let tree: BTreeSet<P::Order3> = self
                .default_tree
                .iter()
                .map(|blk| blk.convert_with(self.params.3))
                .collect();
            unsafe { transmute(tree) }
        });
        unsafe { &*(tree as *const _ as *const _) } // convert from BTreeSet<[I;4]> to BTreeSet<Block>
    }

    fn ensure_tree4(&self) -> &BTreeSet<P::Order4> {
        let tree = self.trees[4].get_or_init(|| {
            let tree: BTreeSet<P::Order4> = self
                .default_tree
                .iter()
                .map(|blk| blk.convert_with(self.params.4))
                .collect();
            unsafe { transmute(tree) }
        });
        unsafe { &*(tree as *const _ as *const _) } // convert from BTreeSet<[I;4]> to BTreeSet<Block>
    }

    /// Find the most appropriate tree that is already allocated for handling the given pattern
    fn best_tree_no_build(&self, spog_pattern: &[Option<P::Identifier>; 4]) -> isize {
        let mut smax = P::OrderDflt::priority_for(&spog_pattern, self.param_default);
        let mut imax = -1;
        let scores = self.make_scores(spog_pattern);
        for (i, score) in scores.iter().enumerate() {
            if score.1 == 0 {
                continue;
            }
            if smax < score.0 {
                smax = score.0;
                imax = i as isize;
            }
        }
        imax
    }

    /// Find the most appropriate tree, allocated or not, for handling the given pattern
    fn best_tree(&self, spog_pattern: &[Option<P::Identifier>; 4]) -> isize {
        let mut smax = (
            P::OrderDflt::priority_for(&spog_pattern, self.param_default),
            1_u8,
        );
        let mut imax = -1;
        let scores = self.make_scores(spog_pattern);
        for (i, score) in scores.iter().enumerate() {
            if smax < *score {
                smax = *score;
                imax = i as isize;
            }
        }
        imax
    }

    fn make_scores(&self, spog_pattern: &[Option<P::Identifier>; 4]) -> Vec<(u8, u8)> {
        let mut scores = Vec::with_capacity(P::USED);
        if P::USED > 0 {
            scores.push(index_conformance(
                &spog_pattern,
                self.get_tree0(),
                self.params.0,
            ));
        }
        if P::USED > 1 {
            scores.push(index_conformance(
                &spog_pattern,
                self.get_tree1(),
                self.params.1,
            ));
        }
        if P::USED > 2 {
            scores.push(index_conformance(
                &spog_pattern,
                self.get_tree2(),
                self.params.2,
            ));
        }
        if P::USED > 3 {
            scores.push(index_conformance(
                &spog_pattern,
                self.get_tree3(),
                self.params.3,
            ));
        }
        if P::USED > 4 {
            scores.push(index_conformance(
                &spog_pattern,
                self.get_tree4(),
                self.params.4,
            ));
        }
        scores
    }
}

impl<P: QuadForestProfile> Default for QuadForest<P> {
    fn default() -> Self {
        Self::new()
    }
}

impl<P: QuadForestProfile> std::iter::FromIterator<[P::Identifier; 4]> for QuadForest<P> {
    fn from_iter<T>(iter: T) -> Self
    where
        T: IntoIterator<Item = [P::Identifier; 4]>,
    {
        let pdef = ParamDflt::<P>::default();
        let this = Self::new_lazy(
            iter.into_iter()
                .map(|data| P::OrderDflt::new(data, pdef))
                .collect(),
            pdef,
            Param0::<P>::default(),
            Param1::<P>::default(),
            Param2::<P>::default(),
            Param3::<P>::default(),
            Param4::<P>::default(),
        );
        if P::PREBUILT > 0 {
            this.ensure_tree0();
        }
        if P::PREBUILT > 1 {
            this.ensure_tree1();
        }
        if P::PREBUILT > 2 {
            this.ensure_tree2();
        }
        if P::PREBUILT > 3 {
            this.ensure_tree3();
        }
        if P::PREBUILT > 4 {
            this.ensure_tree4();
        }
        this
    }
}

/// Return a score measuring how `tree` is appropriate for answering `spog_pattern`.
///
/// The first component is the result of `Block::priority_for`;
/// the second component, used to break ties, indicates whether the tree is already allocated or not.
fn index_conformance<B: Block<I>, I: Identifier>(
    spog_pattern: &[Option<I>; 4],
    tree: Option<&BTreeSet<B>>,
    param: B::Param,
) -> (u8, u8) {
    let c = B::priority_for(spog_pattern, param);
    let built = match tree {
        None => 0,
        Some(_) => 1,
    };
    (c, built)
}

fn iter_matching<B: Block<I>, I: Identifier>(
    tree: &BTreeSet<B>,
    spog_pattern: [Option<I>; 4],
    param: B::Param,
) -> Box<dyn Iterator<Item = [I; 4]> + '_> {
    let (range, filter) = dbg!(B::range_and_filter(spog_pattern, param));
    let ranged = tree.range(range).copied();
    if filter[..] == [None, None, None, None] {
        Box::new(ranged.map(B::into))
    } else {
        Box::new(ranged.filter(move |blk| blk.matches(&filter)).map(B::into))
    }
}

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
    fn best_tree_no_build() {
        let qf = QuadForest::<GSPOGreedy>::new();
        assert_eq!(qf.best_tree_no_build(&p(1, 0, 0, 0)), 0);
        assert_eq!(qf.best_tree_no_build(&p(0, 2, 0, 0)), 1);
        assert_eq!(qf.best_tree_no_build(&p(0, 0, 3, 0)), 2);
        assert_eq!(qf.best_tree_no_build(&p(0, 0, 0, 4)), -1);
        assert_eq!(qf.best_tree_no_build(&p(1, 2, 0, 0)), 0);
        assert_eq!(qf.best_tree_no_build(&p(0, 2, 3, 0)), 2);
        assert_eq!(qf.best_tree_no_build(&p(0, 0, 3, 4)), 4);
        assert_eq!(qf.best_tree_no_build(&p(1, 0, 3, 4)), 3);
        assert_eq!(qf.best_tree_no_build(&p(1, 2, 3, 4)), -1);

        let qf = QuadForest::<GSPOLazy>::new();
        assert_eq!(qf.best_tree_no_build(&p(1, 0, 0, 0)), -1);
        assert_eq!(qf.best_tree_no_build(&p(0, 2, 0, 0)), -1);
        assert_eq!(qf.best_tree_no_build(&p(0, 0, 3, 0)), -1);
        assert_eq!(qf.best_tree_no_build(&p(0, 0, 0, 4)), -1);
        assert_eq!(qf.best_tree_no_build(&p(1, 2, 0, 0)), -1);
        assert_eq!(qf.best_tree_no_build(&p(0, 2, 3, 0)), -1);
        assert_eq!(qf.best_tree_no_build(&p(0, 0, 3, 4)), -1);
        assert_eq!(qf.best_tree_no_build(&p(1, 0, 3, 4)), -1);
        assert_eq!(qf.best_tree_no_build(&p(1, 2, 3, 4)), -1);
        qf.ensure_tree1();
        assert_eq!(qf.best_tree_no_build(&p(1, 0, 0, 0)), -1);
        assert_eq!(qf.best_tree_no_build(&p(0, 2, 0, 0)), 1);
        assert_eq!(qf.best_tree_no_build(&p(0, 0, 3, 0)), -1);
        assert_eq!(qf.best_tree_no_build(&p(0, 0, 0, 4)), -1);
        assert_eq!(qf.best_tree_no_build(&p(1, 2, 0, 0)), 1);
        assert_eq!(qf.best_tree_no_build(&p(0, 2, 3, 0)), 1);
        assert_eq!(qf.best_tree_no_build(&p(0, 0, 3, 4)), -1);
        assert_eq!(qf.best_tree_no_build(&p(1, 0, 3, 4)), -1);
        assert_eq!(qf.best_tree_no_build(&p(1, 2, 3, 4)), -1);

        let qf = QuadForest::<GSPOLight>::new();
        assert_eq!(qf.best_tree_no_build(&p(1, 0, 0, 0)), -1);
        assert_eq!(qf.best_tree_no_build(&p(0, 2, 0, 0)), -1);
        assert_eq!(qf.best_tree_no_build(&p(0, 0, 3, 0)), -1);
        assert_eq!(qf.best_tree_no_build(&p(0, 0, 0, 4)), -1);
        assert_eq!(qf.best_tree_no_build(&p(1, 2, 0, 0)), -1);
        assert_eq!(qf.best_tree_no_build(&p(0, 2, 3, 0)), -1);
        assert_eq!(qf.best_tree_no_build(&p(0, 0, 3, 4)), -1);
        assert_eq!(qf.best_tree_no_build(&p(1, 0, 3, 4)), -1);
        assert_eq!(qf.best_tree_no_build(&p(1, 2, 3, 4)), -1);

        let qf = QuadForest::<SPOGLight>::new();
        assert_eq!(qf.best_tree_no_build(&p(1, 0, 0, 0)), -1);
        assert_eq!(qf.best_tree_no_build(&p(0, 2, 0, 0)), -1);
        assert_eq!(qf.best_tree_no_build(&p(0, 0, 3, 0)), -1);
        assert_eq!(qf.best_tree_no_build(&p(0, 0, 0, 4)), -1);
        assert_eq!(qf.best_tree_no_build(&p(1, 2, 0, 0)), -1);
        assert_eq!(qf.best_tree_no_build(&p(0, 2, 3, 0)), -1);
        assert_eq!(qf.best_tree_no_build(&p(0, 0, 3, 4)), -1);
        assert_eq!(qf.best_tree_no_build(&p(1, 0, 3, 4)), -1);
        assert_eq!(qf.best_tree_no_build(&p(1, 2, 3, 4)), -1);

        use Order::*;
        let qf = QuadForest::<LazyRt>::new_param(GSPO, SPOG, PGSO, OPSG, SOGP, GOPS);
        assert_eq!(qf.best_tree_no_build(&p(1, 0, 0, 0)), -1);
        assert_eq!(qf.best_tree_no_build(&p(0, 2, 0, 0)), -1);
        assert_eq!(qf.best_tree_no_build(&p(0, 0, 3, 0)), -1);
        assert_eq!(qf.best_tree_no_build(&p(0, 0, 0, 4)), -1);
        assert_eq!(qf.best_tree_no_build(&p(1, 2, 0, 0)), -1);
        assert_eq!(qf.best_tree_no_build(&p(0, 2, 3, 0)), -1);
        assert_eq!(qf.best_tree_no_build(&p(0, 0, 3, 4)), -1);
        assert_eq!(qf.best_tree_no_build(&p(1, 0, 3, 4)), -1);
        assert_eq!(qf.best_tree_no_build(&p(1, 2, 3, 4)), -1);
        qf.ensure_tree1();
        assert_eq!(qf.best_tree_no_build(&p(1, 0, 0, 0)), -1);
        assert_eq!(qf.best_tree_no_build(&p(0, 2, 0, 0)), 1);
        assert_eq!(qf.best_tree_no_build(&p(0, 0, 3, 0)), -1);
        assert_eq!(qf.best_tree_no_build(&p(0, 0, 0, 4)), -1);
        assert_eq!(qf.best_tree_no_build(&p(1, 2, 0, 0)), 1);
        assert_eq!(qf.best_tree_no_build(&p(0, 2, 3, 0)), 1);
        assert_eq!(qf.best_tree_no_build(&p(0, 0, 3, 4)), -1);
        assert_eq!(qf.best_tree_no_build(&p(1, 0, 3, 4)), -1);
        assert_eq!(qf.best_tree_no_build(&p(1, 2, 3, 4)), -1);
    }

    #[test]
    fn best_tree() {
        let qf = QuadForest::<GSPOGreedy>::new();
        assert_eq!(qf.best_tree(&p(1, 0, 0, 0)), 0);
        assert_eq!(qf.best_tree(&p(0, 2, 0, 0)), 1);
        assert_eq!(qf.best_tree(&p(0, 0, 3, 0)), 2);
        assert_eq!(qf.best_tree(&p(0, 0, 0, 4)), -1);
        assert_eq!(qf.best_tree(&p(1, 2, 0, 0)), 0);
        assert_eq!(qf.best_tree(&p(0, 2, 3, 0)), 2);
        assert_eq!(qf.best_tree(&p(0, 0, 3, 4)), 4);
        assert_eq!(qf.best_tree(&p(1, 0, 3, 4)), 3);
        assert_eq!(qf.best_tree(&p(1, 2, 3, 4)), -1);

        let qf = QuadForest::<GSPOLazy>::new();
        assert_eq!(qf.best_tree(&p(1, 0, 0, 0)), 0);
        assert_eq!(qf.best_tree(&p(0, 2, 0, 0)), 1);
        assert_eq!(qf.best_tree(&p(0, 0, 3, 0)), 2);
        assert_eq!(qf.best_tree(&p(0, 0, 0, 4)), -1);
        assert_eq!(qf.best_tree(&p(1, 2, 0, 0)), 0);
        assert_eq!(qf.best_tree(&p(0, 2, 3, 0)), 2);
        assert_eq!(qf.best_tree(&p(0, 0, 3, 4)), 4);
        assert_eq!(qf.best_tree(&p(1, 0, 3, 4)), 3);
        assert_eq!(qf.best_tree(&p(1, 2, 3, 4)), -1);

        let qf = QuadForest::<GSPOLight>::new();
        assert_eq!(qf.best_tree(&p(1, 0, 0, 0)), -1);
        assert_eq!(qf.best_tree(&p(0, 2, 0, 0)), -1);
        assert_eq!(qf.best_tree(&p(0, 0, 3, 0)), -1);
        assert_eq!(qf.best_tree(&p(0, 0, 0, 4)), -1);
        assert_eq!(qf.best_tree(&p(1, 2, 0, 0)), -1);
        assert_eq!(qf.best_tree(&p(0, 2, 3, 0)), -1);
        assert_eq!(qf.best_tree(&p(0, 0, 3, 4)), -1);
        assert_eq!(qf.best_tree(&p(1, 0, 3, 4)), -1);
        assert_eq!(qf.best_tree(&p(1, 2, 3, 4)), -1);

        let qf = QuadForest::<SPOGLight>::new();
        assert_eq!(qf.best_tree(&p(1, 0, 0, 0)), -1);
        assert_eq!(qf.best_tree(&p(0, 2, 0, 0)), -1);
        assert_eq!(qf.best_tree(&p(0, 0, 3, 0)), -1);
        assert_eq!(qf.best_tree(&p(0, 0, 0, 4)), -1);
        assert_eq!(qf.best_tree(&p(1, 2, 0, 0)), -1);
        assert_eq!(qf.best_tree(&p(0, 2, 3, 0)), -1);
        assert_eq!(qf.best_tree(&p(0, 0, 3, 4)), -1);
        assert_eq!(qf.best_tree(&p(1, 0, 3, 4)), -1);
        assert_eq!(qf.best_tree(&p(1, 2, 3, 4)), -1);

        use Order::*;
        let qf = QuadForest::<LazyRt>::new_param(GSPO, SPOG, PGSO, OPSG, SOGP, GOPS);
        assert_eq!(qf.best_tree(&p(1, 0, 0, 0)), 0);
        assert_eq!(qf.best_tree(&p(0, 2, 0, 0)), 1);
        assert_eq!(qf.best_tree(&p(0, 0, 3, 0)), 2);
        assert_eq!(qf.best_tree(&p(0, 0, 0, 4)), -1);
        assert_eq!(qf.best_tree(&p(1, 2, 0, 0)), 0);
        assert_eq!(qf.best_tree(&p(0, 2, 3, 0)), 2);
        assert_eq!(qf.best_tree(&p(0, 0, 3, 4)), 4);
        assert_eq!(qf.best_tree(&p(1, 0, 3, 4)), 3);
        assert_eq!(qf.best_tree(&p(1, 2, 3, 4)), -1);
    }

    #[test]
    fn iter_matching_greedy_forest() {
        let mut qf = QuadForest::<GSPOGreedy>::new();
        populate(&mut qf);
        for (pattern, expected) in iter_matching_tests() {
            assert_eq!(
                set(qf.iter_matching_no_build(pattern)),
                set(expected.clone()),
                "for pattern {:?}",
                pattern
            );
            assert_eq!(
                set(qf.iter_matching(pattern)),
                set(expected),
                "for pattern {:?}",
                pattern
            );
        }
    }

    #[test]
    fn iter_matching_lazy_forest() {
        let mut qf = QuadForest::<GSPOLazy>::new();
        populate(&mut qf);
        for (pattern, expected) in iter_matching_tests() {
            assert_eq!(
                set(qf.iter_matching_no_build(pattern)),
                set(expected),
                "for pattern {:?}",
                pattern
            );
        }
        assert!(qf.trees[0].get().is_none());
        qf.ensure_tree0();
        assert!(qf.trees[0].get().is_some());
        for (pattern, expected) in iter_matching_tests() {
            assert_eq!(
                set(qf.iter_matching_no_build(pattern)),
                set(expected),
                "for pattern {:?}",
                pattern
            );
        }
        assert!(qf.trees[4].get().is_none());
        for (pattern, expected) in iter_matching_tests() {
            assert_eq!(
                set(qf.iter_matching(pattern)),
                set(expected),
                "for pattern {:?}",
                pattern
            );
        }
        assert!(qf.trees[4].get().is_some());
    }

    #[test]
    fn iter_matching_light_forest() {
        let mut qf = QuadForest::<SPOGLight>::new();
        populate(&mut qf);
        for (pattern, expected) in iter_matching_tests() {
            assert_eq!(
                set(qf.iter_matching_no_build(pattern)),
                set(expected.clone()),
                "for pattern {:?}",
                pattern
            );
            assert_eq!(set(qf.iter_matching(pattern)), set(expected));
        }
    }

    #[test]
    fn iter_matching_lazy_runtime_forest() {
        use Order::*;
        let mut qf = QuadForest::<LazyRt>::new_param(GSPO, SPOG, PGSO, OPSG, SOGP, GOPS);
        populate(&mut qf);
        for (pattern, expected) in iter_matching_tests() {
            dbg!(pattern);
            assert_eq!(
                set(qf.iter_matching_no_build(pattern)),
                set(expected),
                "for pattern {:?}",
                pattern
            );
        }
        assert!(qf.trees[0].get().is_none());
        qf.ensure_tree0();
        assert!(qf.trees[0].get().is_some());
        for (pattern, expected) in iter_matching_tests() {
            assert_eq!(
                set(qf.iter_matching_no_build(pattern)),
                set(expected),
                "for pattern {:?}",
                pattern
            );
        }
        assert!(qf.trees[4].get().is_none());
        for (pattern, expected) in iter_matching_tests() {
            assert_eq!(
                set(qf.iter_matching(pattern)),
                set(expected),
                "for pattern {:?}",
                pattern
            );
        }
        assert!(qf.trees[4].get().is_some());
    }

    fn iter_matching_tests() -> impl Iterator<Item = ([Option<usize>; 4], Vec<[usize; 4]>)> {
        vec![
            (
                p(4, 0, 0, 0),
                vec![
                    [4, 1, 5, 1],
                    [4, 1, 4, 2],
                    [4, 2, 8, 2],
                    [4, 1, 1, 3],
                    [4, 1, 2, 3],
                ],
            ),
            (
                p(0, 4, 0, 0),
                vec![[1, 4, 5, 1], [1, 4, 4, 2], [2, 4, 8, 2]],
            ),
            (
                p(0, 0, 4, 0),
                vec![
                    [1, 3, 4, 1],
                    [2, 2, 4, 1],
                    [3, 1, 4, 1],
                    [1, 4, 4, 2],
                    [2, 2, 4, 2],
                    [4, 1, 4, 2],
                    [8, 1, 4, 3],
                ],
            ),
            (p(0, 0, 0, 4), vec![[1, 2, 3, 4]]),
            (p(2, 3, 0, 0), vec![[2, 3, 5, 1], [2, 3, 6, 2]]),
            (p(2, 2, 4, 0), vec![[2, 2, 4, 1], [2, 2, 4, 2]]),
            (
                p(0, 0, 4, 2),
                vec![[1, 4, 4, 2], [2, 2, 4, 2], [4, 1, 4, 2]],
            ),
        ]
        .into_iter()
    }

    fn set<I: IntoIterator<Item = [usize; 4]>>(it: I) -> BTreeSet<[usize; 4]> {
        it.into_iter().collect()
    }

    fn populate<P: QuadForestProfile<Identifier = usize>>(qf: &mut QuadForest<P>) {
        // graph 1 contains additions (up to 5)
        qf.insert([1, 1, 2, 1]);
        qf.insert([1, 2, 3, 1]);
        qf.insert([1, 3, 4, 1]);
        qf.insert([1, 4, 5, 1]);
        qf.insert([2, 1, 3, 1]);
        qf.insert([2, 2, 4, 1]);
        qf.insert([2, 3, 5, 1]);
        qf.insert([3, 1, 4, 1]);
        qf.insert([3, 2, 5, 1]);
        qf.insert([4, 1, 5, 1]);
        // graph 2 contains multiplications (up to 8, factors from 1 to 4)
        qf.insert([1, 1, 1, 2]);
        qf.insert([1, 2, 2, 2]);
        qf.insert([1, 3, 3, 2]);
        qf.insert([1, 4, 4, 2]);
        qf.insert([2, 1, 2, 2]);
        qf.insert([2, 2, 4, 2]);
        qf.insert([2, 3, 6, 2]);
        qf.insert([2, 4, 8, 2]);
        qf.insert([3, 1, 3, 2]);
        qf.insert([3, 2, 6, 2]);
        qf.insert([4, 1, 4, 2]);
        qf.insert([4, 2, 8, 2]);
        // graph 3 contains divisibility (up to 8, with predicate 1)
        qf.insert([1, 1, 1, 3]);
        qf.insert([2, 1, 1, 3]);
        qf.insert([3, 1, 1, 3]);
        qf.insert([4, 1, 1, 3]);
        qf.insert([4, 1, 2, 3]);
        qf.insert([5, 1, 1, 3]);
        qf.insert([6, 1, 1, 3]);
        qf.insert([6, 1, 2, 3]);
        qf.insert([6, 1, 3, 3]);
        qf.insert([7, 1, 7, 3]);
        qf.insert([8, 1, 1, 3]);
        qf.insert([8, 1, 2, 3]);
        qf.insert([8, 1, 4, 3]);
        // graph 4 contains only one quad
        qf.insert([1, 2, 3, 4]);
    }

    /// Pattern constructor, where
    /// - 0 is interpreted as None,
    /// - other values are interpreted as Some(value),
    fn p(s: usize, p: usize, o: usize, g: usize) -> [Option<usize>; 4] {
        [i2opt(s), i2opt(p), i2opt(o), i2opt(g)]
    }

    /// Convenient conversion of usize to Option<usize>, used by p() and p() above.
    fn i2opt(i: usize) -> Option<usize> {
        match i {
            0 => None,
            n => Some(n),
        }
    }
}
