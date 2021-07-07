//! This module provide an implementation of an identifier forest in which
//! the trees are chosen at compile time instead of run time: [`CTForest`].
//!
//! The purpose of this implementation is to be faster, at the cost of
//! having of less flexible structure to pick the desired trees.

use crate::Identifier;
use crate::order::{ Position, Subject, Predicate, Object, Graph };
use crate::tree::{ LazyStructure, MaybeTree4, Tree4Iterator, Forest4 };
use crate::tree::OnceTreeSet;

pub mod profile4;

/// Helper trait to define which kind of [`OnceTreeSet`](crate::tree::OnceTreeSet)s
/// must be used in a [`CTForest`].
///
/// The order of the tree and whetever it can be lazy is specified as bound
/// types and constants, which serves as the configuration input.
pub trait Tree4Profile {
    /// The first position of the [`FixedOrder4`](crate::order::FixedOrder4), corresponding to `A`
    type First: Position;
    /// The second position of the [`FixedOrder4`](crate::order::FixedOrder4), corresponding to `B`
    type Second: Position;
    /// The third position of the [`FixedOrder4`](crate::order::FixedOrder4), corresponding to `C`
    type Third: Position;
    /// The fourth position of the [`FixedOrder4`](crate::order::FixedOrder4), corresponding to `D`
    type Fourth: Position;
    /// True if the corresponding [`MaybeTree4`](crate::tree::MaybeTree4) must always be instanciated (it can not be a lazy implementation).
    const ALWAYS_INSTANCIATED: bool;
}

/// Build a [`OnceTreeSet`](crate::tree::OnceTreeSet) instance for quads of `I`
/// using the order and strategy specified in the [`Tree4Profile`] `P`
pub fn make_once_tree_set<I, P>() -> OnceTreeSet<I, P::First, P::Second, P::Third, P::Fourth>
where I: Identifier, P: Tree4Profile {
    if P::ALWAYS_INSTANCIATED {
        OnceTreeSet::<I, P::First, P::Second, P::Third, P::Fourth>::new_instanciated()
    } else {
        OnceTreeSet::<I, P::First, P::Second, P::Third, P::Fourth>::new()
    }
}

/// A [`CTForest`] with an [`OGPS`](profile4::OGPS) tree, and 5 other trees that can be
/// instanciated depending on the patterns requested by the users. The other trees
/// have been chosen to be able to have an optimal tree for each kind of pattern.
pub type CTForestLazy6<I> = CTForest<I, 
    profile4::OGPSAlways,
    profile4::SPOG,
    profile4::GPSO,
    profile4::POGS,
    profile4::GSPO,
    profile4::OSGP
>;

/// A [`CTForest`] instanciated with 6 always instanciated subtrees. The trees are chosen
/// to be able to answer any kind of pattern.
pub type CTForestGreedy6<I> = CTForest<I,
    profile4::OGPSAlways,
    profile4::SPOGAlways,
    profile4::GPSOAlways,
    profile4::POGSAlways,
    profile4::GSPOAlways,
    profile4::OSGPAlways
>;

/// A `CTForest` (Compile Time Forest) is a forest composed of 6 trees determined at
/// compile time.
///
/// 6 trees is chosen because it is the minimal number to be able to have an optimal
/// tree for each quad query pattern.
///
/// The chosen implementation of [`MaybeTree4`](crate::tree::MaybeTree4) is always
/// [`OnceTreeSet`](crate::tree::OnceTreeSet).
// TODO: used a non OnceCell base implementation for always instanciated tree?
pub struct CTForest<I, Order1, Order2, Order3, Order4, Order5, Order6>
where
I: Identifier,
Order1: Tree4Profile,
// Order1::ALWAYS_INSTANCIATED = true
Order2: Tree4Profile,
Order3: Tree4Profile,
Order4: Tree4Profile,
Order5: Tree4Profile,
Order6: Tree4Profile
{
    tree1: OnceTreeSet<I, Order1::First, Order1::Second, Order1::Third, Order1::Fourth>,
    tree2: OnceTreeSet<I, Order2::First, Order2::Second, Order2::Third, Order2::Fourth>,
    tree3: OnceTreeSet<I, Order3::First, Order3::Second, Order3::Third, Order3::Fourth>,
    tree4: OnceTreeSet<I, Order4::First, Order4::Second, Order4::Third, Order4::Fourth>,
    tree5: OnceTreeSet<I, Order5::First, Order5::Second, Order5::Third, Order5::Fourth>,
    tree6: OnceTreeSet<I, Order6::First, Order6::Second, Order6::Third, Order6::Fourth>,
}

impl<I, Order1, Order2, Order3, Order4, Order5, Order6> CTForest<I, Order1, Order2, Order3, Order4, Order5, Order6>
where
I: Identifier,
Order1: Tree4Profile,
// Order1::ALWAYS_INSTANCIATED = true
Order2: Tree4Profile,
Order3: Tree4Profile,
Order4: Tree4Profile,
Order5: Tree4Profile,
Order6: Tree4Profile
{

    pub fn new() -> Self {
        Self {
            tree1: make_once_tree_set::<I, Order1>(),
            tree2: make_once_tree_set::<I, Order2>(),
            tree3: make_once_tree_set::<I, Order3>(),
            tree4: make_once_tree_set::<I, Order4>(),
            tree5: make_once_tree_set::<I, Order5>(),
            tree6: make_once_tree_set::<I, Order6>(),
        }
    }


    fn best_conformance(&self, can_build: bool, pattern_layout: &[Option<I>; 4]) -> (usize, usize) {

        [
            self.tree1.index_conformance(can_build, pattern_layout),
            self.tree2.index_conformance(can_build, pattern_layout),
            self.tree3.index_conformance(can_build, pattern_layout),
            self.tree4.index_conformance(can_build, pattern_layout),
            self.tree5.index_conformance(can_build, pattern_layout),
            self.tree6.index_conformance(can_build, pattern_layout),
        ]
            .iter()
            .enumerate()
            .filter_map(|(i, opt)| opt.map(|score| (i+1, score)))
            .max_by_key(|(_, score)| *score)
            .unwrap()
    }

    

}


impl<I, Order1, Order2, Order3, Order4, Order5, Order6> Forest4<I>
for CTForest<I, Order1, Order2, Order3, Order4, Order5, Order6>
where
I: Identifier,
Order1: Tree4Profile,
// Order1::ALWAYS_INSTANCIATED = true
Order2: Tree4Profile,
Order3: Tree4Profile,
Order4: Tree4Profile,
Order5: Tree4Profile,
Order6: Tree4Profile
{
    fn get_number_of_living_trees(&self) -> usize {
        [self.tree1.exists(), self.tree2.exists(), self.tree3.exists(), self.tree4.exists(), self.tree5.exists(), self.tree6.exists()]
            .iter()
            .filter(|tree| **tree)
            .count()
    }

    fn ensure_has_index_for(&self, pattern: &[Option<I>; 4]) {
        let best = self.best_conformance(true, &pattern).0;

        match best {
            2 => ensure_existence(&self, &self.tree2),
            3 => ensure_existence(&self, &self.tree3),
            4 => ensure_existence(&self, &self.tree4),
            5 => ensure_existence(&self, &self.tree5),
            6 => ensure_existence(&self, &self.tree6),
            _ => {} /* noop */
        }
    }

    fn get_quads_unamortized<'a>(&'a self, pattern: [Option<I>; 4]) -> Tree4Iterator<'a, I> {
        let best = self.best_conformance(false, &pattern).0;

        match best {
            2 => get_quad_from(&self, &self.tree2, pattern),
            3 => get_quad_from(&self, &self.tree3, pattern),
            4 => get_quad_from(&self, &self.tree4, pattern),
            5 => get_quad_from(&self, &self.tree5, pattern),
            6 => get_quad_from(&self, &self.tree6, pattern),
            _ => get_quad_from(&self, &self.tree1, pattern)
        }
    }
}


/// If best_btree exists, extract the quads that match the pattern
///
/// If it doesn't, takes the first btree of this, fills best_btree and then
/// extract the quads.
fn ensure_existence<'a, I, MT, Order1, Order2, Order3, Order4, Order5, Order6>(
    this: &'a CTForest<I, Order1, Order2, Order3, Order4, Order5, Order6>,
    best_btree: &'a MT
)
where MT: MaybeTree4<I>, I: Identifier,
Order1: Tree4Profile,
// Order1::ALWAYS_INSTANCIATED = true
Order2: Tree4Profile,
Order3: Tree4Profile,
Order4: Tree4Profile,
Order5: Tree4Profile,
Order6: Tree4Profile
{
    if !best_btree.exists() {
        best_btree.ensure_exists(|| this.tree1.get_quads([None, None, None, None]));
    }
}



impl<I, Order1, Order2, Order3, Order4, Order5, Order6> Default 
for CTForest<I, Order1, Order2, Order3, Order4, Order5, Order6>
where
I: Identifier,
Order1: Tree4Profile,
// Order1::ALWAYS_INSTANCIATED = true
Order2: Tree4Profile,
Order3: Tree4Profile,
Order4: Tree4Profile,
Order5: Tree4Profile,
Order6: Tree4Profile
{
    fn default() -> Self {
        Self::new()
    }
}

/// If best_btree exists, extract the quads that match the pattern
///
/// If it doesn't, takes the first btree of this, fills best_btree and then
/// extract the quads.
fn get_quad_from<'a, I, MT, Order1, Order2, Order3, Order4, Order5, Order6>(
    this: &'a CTForest<I, Order1, Order2, Order3, Order4, Order5, Order6>,
    best_btree: &'a MT,
    pattern: [Option<I>; 4])
-> Tree4Iterator<'a, I>
where MT: MaybeTree4<I>, I: Identifier,
Order1: Tree4Profile,
// Order1::ALWAYS_INSTANCIATED = true
Order2: Tree4Profile,
Order3: Tree4Profile,
Order4: Tree4Profile,
Order5: Tree4Profile,
Order6: Tree4Profile
{
    if !best_btree.exists() {
        best_btree.ensure_exists(|| this.tree1.get_quads([None, None, None, None]));
    }

    best_btree.get_quads(pattern)
}

impl<I, Order1, Order2, Order3, Order4, Order5, Order6> MaybeTree4<I>
for CTForest<I, Order1, Order2, Order3, Order4, Order5, Order6>
where
I: Identifier,
Order1: Tree4Profile,
// Order1::ALWAYS_INSTANCIATED = true
Order2: Tree4Profile,
Order3: Tree4Profile,
Order4: Tree4Profile,
Order5: Tree4Profile,
Order6: Tree4Profile
{
    fn exists(&self) -> bool {
        true
    }

    fn ensure_exists<'a, F>(&self, _f: F) where F: FnOnce() -> Tree4Iterator<'a, I> {
        // noop
    }

    fn get_quads<'a>(&'a self, pattern: [Option<I>; 4]) -> Tree4Iterator<'a, I> {
        let best = self.best_conformance(true, &pattern).0;

        match best {
            2 => get_quad_from(&self, &self.tree2, pattern),
            3 => get_quad_from(&self, &self.tree3, pattern),
            4 => get_quad_from(&self, &self.tree4, pattern),
            5 => get_quad_from(&self, &self.tree5, pattern),
            6 => get_quad_from(&self, &self.tree6, pattern),
            _ => get_quad_from(&self, &self.tree1, pattern)
        }
    }

    fn index_conformance(&self, can_build: bool, pattern_layout: &[Option<I>; 4]) -> Option<usize> {
        Some(self.best_conformance(can_build, pattern_layout).1)
    }

    fn insert(&mut self, id_quad: &[I; 4]) -> Option<bool> {
        self.tree6.insert(&id_quad);
        self.tree5.insert(&id_quad);
        self.tree4.insert(&id_quad);
        self.tree3.insert(&id_quad);
        self.tree2.insert(&id_quad);
        self.tree1.insert(&id_quad)
    }

    fn delete(&mut self, id_quad: &[I; 4]) -> Option<bool> {
        self.tree6.delete(&id_quad);
        self.tree5.delete(&id_quad);
        self.tree4.delete(&id_quad);
        self.tree3.delete(&id_quad);
        self.tree2.delete(&id_quad);
        self.tree1.delete(&id_quad)
    }

    fn size(&self) -> Option<usize> {
        self.tree1.size()
    }

    fn has(&self, id_quad: &[I; 4]) -> Option<bool> {
        self.tree1.has(&id_quad)
    }
}




#[cfg(test)]
mod test {
    use super::*;

    use profile4::*;


    #[test]
    fn test_implem_() {
        type T = CTForest<u32, OGPSAlways, SPOG, GPSO, POGS, GSPO, OSGP>;

        // Insertion
        {
            let mut tree = T::default();
            assert_eq!(tree.size(), Some(0_usize));
            tree.insert(&[0_u32, 1_u32, 2_u32, 3_u32]);
            assert_eq!(tree.size(), Some(1_usize));
            tree.insert(&[0_u32, 1_u32, 2_u32, 3_u32]);
            assert_eq!(tree.size(), Some(1_usize), "Duplicates should not be stored");
            tree.insert(&[0_u32, 1_u32, 2_u32, 4_u32]);
            assert_eq!(tree.size(), Some(2_usize));
        }

        // Deletion
        {
            let mut tree = T::default();
            tree.insert(&[0_u32, 1_u32, 2_u32, 3_u32]);
            tree.insert(&[0_u32, 1_u32, 2_u32, 4_u32]);
            assert_eq!(tree.size(), Some(2_usize));
            assert!(tree.delete(&[0_u32, 1_u32, 2_u32, 4_u32]).unwrap(), "Should return true if the quad was present");
            assert_eq!(tree.size(), Some(1_usize));
            assert!(!tree.delete(&[0_u32, 1_u32, 2_u32, 4_u32]).unwrap(), "Should return true if the quad was not present");
            assert_eq!(tree.size(), Some(1_usize));
        }

        // Has
        {
            let mut tree = T::default();
            tree.insert(&[0_u32, 1_u32, 2_u32, 3_u32]);
            tree.insert(&[0_u32, 1_u32, 2_u32, 4_u32]);
            assert!(tree.has(&[0_u32, 1_u32, 2_u32, 3_u32]).unwrap());
            assert!(!tree.has(&[8_u32, 1_u32, 2_u32, 8_u32]).unwrap());
        }

        // Consistancy of new
        {
            let quad = [0_u32, 1_u32, 2_u32, 3_u32];

            let mut tree = T::default();
            if tree.exists() {
                assert!(tree.size().is_some());
                assert!(tree.insert(&quad).is_some());
                assert!(tree.has(&quad).is_some());
                assert!(tree.delete(&quad).is_some());
                assert!(tree.index_conformance(true, &[None, None, None, None]).is_some());
            } else {
                assert!(tree.size().is_none());
                assert!(tree.insert(&quad).is_none());
                assert!(tree.has(&quad).is_none());
                assert!(tree.delete(&quad).is_none());
                assert!(tree.index_conformance(false, &[None, None, None, None]).is_none());
            }
        }

        // Filter
        {
            let mut tree = T::default();
            tree.insert(&[10_u32, 20_u32, 30_u32, 40_u32]);
            tree.insert(&[10_u32, 21_u32, 30_u32, 40_u32]);
            tree.insert(&[10_u32, 20_u32, 31_u32, 40_u32]);
            tree.insert(&[10_u32, 20_u32, 30_u32, 41_u32]);
            tree.insert(&[11_u32, 20_u32, 30_u32, 40_u32]);
            tree.insert(&[11_u32, 21_u32, 30_u32, 40_u32]);
            tree.insert(&[11_u32, 20_u32, 31_u32, 40_u32]);
            tree.insert(&[11_u32, 20_u32, 30_u32, 41_u32]);
            tree.insert(&[11_u32, 20_u32, 30_u32, 42_u32]);

            assert_eq!(tree.get_quads([None, None, None, None]).count(), 9);
            assert_eq!(tree.get_quads([Some(10_u32), None, None, None]).count(), 4);
            assert_eq!(tree.get_quads([Some(11_u32), None, None, None]).count(), 5);
            assert_eq!(tree.get_quads([Some(77_u32), None, None, None]).count(), 0);
            assert_eq!(tree.get_quads([None, Some(20_u32), None, None]).count(), 7);
            assert_eq!(tree.get_quads([None, Some(20_u32), None, Some(41_u32)]).count(), 2);

            assert!(tree.get_number_of_living_trees() >= 2);
        }
    }

}
