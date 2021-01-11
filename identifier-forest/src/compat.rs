//! This module provides type aliases and shallow adapters to comply with the old API of the crate.
//!
//! It is discouraged to use these types in new code.
#![allow(missing_docs)]

use crate::quad::{GSPOLazy, QuadForest, GSPO};
use std::collections::BTreeSet;

pub type IndexingForest4Filter<'a> = Box<dyn Iterator<Item = [u32; 4]> + 'a>;

#[derive(Default)]
pub struct IndexingForest4(pub QuadForest<GSPOLazy<u32>>);

/// Dummy type, not used anymore.
pub struct TermRole();

/// Shallow adapter for [`QuadForest`].
impl IndexingForest4 {
    pub fn new() -> Self {
        todo!()
    }

    #[deprecated(
        note = "Provided for compatibility only. Ignores the parameters and does the same as new()"
    )]
    pub fn new_with_indexes(
        _default_initialized: &[[TermRole; 4]],
        _optional_indexes: Option<&Vec<[TermRole; 4]>>,
    ) -> Self {
        Self::new()
    }

    #[deprecated(
        note = "Provided for compatibility only. Ignores the parameters and does the same as new()"
    )]
    pub fn new_anti(_s: bool, _p: bool, _o: bool, _g: bool) -> Self {
        Self::new()
    }

    pub fn search_all_matching_quads(
        &self,
        identifier_quad_pattern: [Option<u32>; 4],
        can_build_new_tree: bool,
    ) -> IndexingForest4Filter<'_> {
        if can_build_new_tree {
            self.0.iter_matching(identifier_quad_pattern)
        } else {
            self.0.iter_matching_no_build(identifier_quad_pattern)
        }
    }

    pub fn filter(&self, identifier_quad_pattern: [Option<u32>; 4]) -> IndexingForest4Filter<'_> {
        self.0.iter_matching(identifier_quad_pattern)
    }

    pub fn insert(&mut self, identifier_quad: [u32; 4]) -> bool {
        self.0.insert(identifier_quad)
    }

    pub fn delete(&mut self, identifier_quad: [u32; 4]) -> bool {
        self.0.remove(identifier_quad)
    }

    pub fn get_number_of_living_trees(&self) -> usize {
        self.0.nb_additional_trees()
    }

    pub fn ensure_has_index_for(&mut self, s: bool, p: bool, o: bool, g: bool) {
        let pattern = [
            if s { Some(1) } else { None },
            if p { Some(1) } else { None },
            if o { Some(1) } else { None },
            if g { Some(1) } else { None },
        ];
        self.0.iter_matching(pattern).next();
    }

    pub fn base_tree(&self) -> &BTreeSet<GSPO<u32>> {
        self.0.default_tree()
    }
}
