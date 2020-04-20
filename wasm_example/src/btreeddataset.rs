﻿use once_cell::unsync::OnceCell;
use std::collections::BTreeMap;


use sophia::dataset::MutableDataset;
use std::convert::Infallible;
use sophia::dataset::DQuadSource;
use sophia::dataset::Dataset;
use sophia::dataset::MDResult;
use sophia::graph::inmem::TermIndexMapU;
use sophia::quad::streaming_mode::ByValue;
use sophia::quad::streaming_mode::StreamedQuad;
use sophia::term::factory::RcTermFactory;
use sophia::term::index_map::TermIndexMap;
use sophia::term::RefTerm;
use sophia::term::Term;
use sophia::term::TermData;
use std::iter::empty;
use sophia::dataset::DResult;
use sophia::dataset::DQuad;

use crate::datamodel_quad::SophiaExportQuad;

#[cfg(test)]
use sophia::test_dataset_impl;

#[derive(Debug)]
pub enum TermKind {
    Subject,
    Predicate,
    Object,
    Graph
}

impl PartialEq for TermKind {
    fn eq(&self, other: &Self) -> bool {
        std::mem::discriminant(self) == std::mem::discriminant(other)
    }
}

impl TermKind {
    pub fn get_spog_position(&self) -> usize {
        match self {
            TermKind::Subject => 0,
            TermKind::Predicate => 1,
            TermKind::Object => 2,
            TermKind::Graph => 3
        }
    }
}

/// A block is a structure that can be stored in a BTreeMap to store quads in
/// a certain order
#[derive(PartialEq, PartialOrd, Eq, Ord)]
pub struct Block {
    data: [u32; 4],
}

impl Block {
    /// Creates a block with the given values
    pub fn new(values: [u32; 4]) -> Block {
        Block { data: values }
    }
}


/// A block order enables to convert a SPOG quad into a block and get back
/// the SPOG quad.
/// 
/// It provides methods to manipulate the elements of a `BTreeMap<Block, ()>`
/// by using functions that takes as input or returns an array of four u32
/// representing the quad indexes
pub struct BlockOrder {
    term_kinds: [TermKind; 4],
    to_block_index_to_destination: [usize; 4],
    to_indices_index_to_destination: [usize; 4]
}

impl BlockOrder {
    /// Returns a string that represents the block order
    pub fn name(&self) -> String {
        format!(
            "{:?} {:?} {:?} {:?}",
            self.term_kinds[0],
            self.term_kinds[1],
            self.term_kinds[2],
            self.term_kinds[3]
        )
    }

    /// Builds a block builder from an order of SPOG
    pub fn new(term_kinds: [TermKind; 4]) -> BlockOrder {
        let mut to_block_index_to_destination: [usize; 4] = [0, 0, 0, 0];
        let mut to_indices_index_to_destination: [usize; 4] = [0, 0, 0, 0];

        for term_kind in [TermKind::Subject, TermKind::Predicate, TermKind::Object, TermKind::Graph].iter() {
            let position = term_kinds.iter().position(|x| x == term_kind);
            let position = position.unwrap();

            to_indices_index_to_destination[term_kind.get_spog_position()] = position;
            to_block_index_to_destination[position] = term_kind.get_spog_position();
        }
        
        BlockOrder { term_kinds, to_block_index_to_destination, to_indices_index_to_destination }
    }

    /// Builds a block from SPPOG indices
    pub fn to_block(&self, indices: &[u32; 4]) -> Block {
        Block{
            data: [
                indices[self.to_block_index_to_destination[0]],
                indices[self.to_block_index_to_destination[1]],
                indices[self.to_block_index_to_destination[2]],
                indices[self.to_block_index_to_destination[3]]
            ]
        }
    }

    /// Buids SPOG indices from a block
    pub fn to_indices(&self, block: &Block) -> [u32; 4] {
        return [
            block.data[self.to_indices_index_to_destination[0]],
            block.data[self.to_indices_index_to_destination[1]],
            block.data[self.to_indices_index_to_destination[2]],
            block.data[self.to_indices_index_to_destination[3]],
        ]
    }

    /// Returns the number of term kinds in the array request_terms that can be
    /// used as a prefix
    pub fn index_conformance(&self, request: &[&Option<u32>; 4]) -> usize {
        for (i, term_kind) in self.term_kinds.iter().enumerate() {
            let spog_position = term_kind.get_spog_position();
            
            if request[spog_position].is_none() {
                return i;
            }
        }

        self.term_kinds.len()
    }

    /// Returns a range on every block that matches the given spog. The range
    /// is restricted as much as possible. Returned indexes are the spog indexes
    /// that are not strictly filtered by the range (other spog that do not
    /// match can be returned)
    pub fn range(&self, mut spog: [Option<u32>; 4]) -> (std::ops::RangeInclusive<Block>, Option<u32>, Option<u32>, Option<u32>, Option<u32>) {
        // Restrict range as much as possible
        let mut min = [u32::min_value(), u32::min_value(), u32::min_value(), u32::min_value()];
        let mut max = [u32::max_value(), u32::max_value(), u32::max_value(), u32::max_value()];

        for (i, term_kind) in self.term_kinds.iter().enumerate() {
            let spog_position = term_kind.get_spog_position();
            
            if spog[spog_position].is_none() {
                break;
            }

            let set_value = spog[spog_position].take().unwrap();

            min[i] = set_value;
            max[i] = set_value;
        }

        // Return range + spog that have to be filtered
        (Block::new(min)..=Block::new(max), spog[0], spog[1], spog[2], spog[3])
    }

    /// Inserts the given quad in the passed tree, using this quad ordering
    /// 
    /// Returns true if the quad was already present
    pub fn insert_into(&self, tree: &mut BTreeMap<Block, ()>, spog: &[u32; 4]) -> bool {
        let block = self.to_block(spog);

        let insert_result = tree.insert(block, ());

        insert_result.is_some()
    }

    /// Deletes the given quad from the passed tree, using this quad ordering
    /// 
    /// Returns true if the quad has been deleted
    pub fn delete_from(&self, tree: &mut BTreeMap<Block, ()>, spog: &[u32; 4]) -> bool {
        let block = self.to_block(spog);

        let delete_result = tree.remove(&block);

        delete_result.is_some()
    }

    /// Returns true if the passed tree contains the passed quad
    pub fn contains(&self, tree: &BTreeMap<Block, ()>, spog: &[u32; 4]) -> bool {
        let block = self.to_block(spog);

        tree.contains_key(&block)
    }

    /// Inserts every quads in iterator in the passed tree
    pub fn insert_all_into<'a>(&self, tree: &mut BTreeMap<Block, ()>, iterator: QuadIndexFromSubTreeDataset<'a>) {
        for block in iterator.map(|spog| self.to_block(&spog)) {
            tree.insert(block, ());
        }
    }

    /// Returns an iterator on every quads that matches the given filter.
    /// 
    /// The filter in an array of four optional quad indexes, None means every
    /// quad must be matched, a given value on a term position that only quads
    /// that have the specified value have to be returned.
    /// 
    /// The filtering tries to be smart by iterating on the less possible number
    /// of quads in the tree. For several trees, the result of
    /// `index_conformance` indicates how many quads will be iterated on : for
    /// two block order, the block order that returns the greater
    /// `index_conformance` will return an iterator that looks over less
    /// different quads.
    pub fn filter<'a>(&'a self, tree: &'a BTreeMap<Block, ()>, spog: [Option<u32>; 4]) -> QuadIndexFromSubTreeDataset {
        let (range, subject, predicate, object, graph) = self.range(spog);
        let tree_range = tree.range(range);

        QuadIndexFromSubTreeDataset {
            range: tree_range,
            block_order: self,
            term_filter: TermFilter {
                filtered_position: [subject, predicate, object, graph]
            }
        }
    }
}

/// A filter on indexes
pub struct TermFilter {
    pub filtered_position: [Option<u32>; 4]
}

impl TermFilter {
    /// Returns an empty term filter
    pub fn empty() -> TermFilter {
        TermFilter {
            filtered_position: [ None, None, None, None ]
        }
    }

    /// Returns true of the given spog is accepted by this filter (the non Some
    /// values of the filter are equals to the corresponding spog value)
    pub fn filter(&self, spog: &[u32; 4]) -> bool {
        for i in 0..self.filtered_position.len() {
            if let Some(term) = self.filtered_position[i] {
                if spog[i] != term {
                    return false;
                }
            }
        }

        true
    }
}

/// An iterator on a sub tree
pub struct QuadIndexFromSubTreeDataset<'a> {
    /// Iterator
    range: std::collections::btree_map::Range<'a, Block, ()>,
    /// Used block order
    block_order: &'a BlockOrder,
    /// Term filter for quads that can't be restricted by the range
    term_filter: TermFilter
}

impl<'a> Iterator for QuadIndexFromSubTreeDataset<'a> {
    type Item = [u32; 4];

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            let next = self.range.next().map(|(block, _) | self.block_order.to_indices(block));

            match next.as_ref() {
                Some(spog) => if self.term_filter.filter(spog) {
                    return next;
                },
                None => return None
            }
        }
    }
}

/// A treed dataset is a forest of trees that implements the Dataset trait
/// of Sophia.
/// 
/// It is composed of several trees, with a main tree and sveral optional
/// subtrees.
pub struct TreedDataset {
    /// The tree that is always instancied
    base_tree: (BlockOrder, BTreeMap<Block, ()>),
    /// A list of optional trees that can be instancied ot improve look up
    /// performances at the cost of further insert and deletions
    optional_trees: Vec<(BlockOrder, OnceCell<BTreeMap<Block, ()>>)>,
    /// A term index map that matches RcTerms with u32 indexes
    term_index: TermIndexMapU<u32, RcTermFactory>
}

impl TreedDataset {
    pub fn new() -> TreedDataset {
        TreedDataset {
            base_tree: (
                BlockOrder::new([TermKind::Object, TermKind::Graph, TermKind::Predicate, TermKind::Subject]),
                BTreeMap::new()
            ),
            optional_trees: vec!(
                (BlockOrder::new([TermKind::Graph, TermKind::Subject, TermKind::Predicate, TermKind::Object]), OnceCell::new())
            ),
            term_index: TermIndexMapU::new()
        }
    }

    /// Returns an iterator on quads represented by their indexes from the 
    pub fn filter<'a>(&'a self, spog: [Option<u32>; 4]) -> QuadIndexFromSubTreeDataset {
        // Find best index
        let term_kinds = [&spog[0], &spog[1], &spog[2], &spog[3]];

        let mut best_alt_tree_pos = None;
        let mut best_index_score = self.base_tree.0.index_conformance(&term_kinds);
        
        for i in 0..self.optional_trees.len() {
            let score = self.optional_trees[i].0.index_conformance(&term_kinds);
            if score > best_index_score {
                best_alt_tree_pos = Some(i);
                best_index_score = score;
            }
        }

        // Split research

        let tree_description = match best_alt_tree_pos {
            Some(x) => {
                let alternative_tree_description = &self.optional_trees[x];

                (
                    &alternative_tree_description.0,
                    alternative_tree_description.1.get_or_init(|| {
                        let content = self.base_tree.0.filter(&self.base_tree.1, [None, None, None, None]);

                        let mut map = BTreeMap::new();
                        alternative_tree_description.0.insert_all_into(&mut map, content);
                        map
                    })
                )
            }
            None => (&self.base_tree.0, &self.base_tree.1)
        };

        tree_description.0.filter(&tree_description.1, spog)
    }

    /// Inserts in the dataset the quad described by the given array of indexes.
    /// 
    /// Returns true if the quad has been inserted in the dataset (it was not
    /// already in it)
    pub fn insert_by_index(&mut self, spog: [u32; 4]) -> bool {
        if self.base_tree.0.insert_into(&mut self.base_tree.1, &spog) {
            return false;
        }

        for i in 0..self.optional_trees.len() {
            let optional_tree_tuple = &mut self.optional_trees[i];

            if let Some(instancied_tree) = optional_tree_tuple.1.get_mut() {
                optional_tree_tuple.0.insert_into(instancied_tree, &spog); // assert false
            }
        }

        true
    }

    /// Deletes from the dataset the quad described by the given array of
    /// indexes.
    /// 
    /// Returns true if the quad was in the dataset (and was deleted)
    pub fn delete_by_index(&mut self, spog: [u32; 4]) -> bool {
        if !self.base_tree.0.delete_from(&mut self.base_tree.1, &spog) {
            return false;
        }

        for i in 0..self.optional_trees.len() {
            let optional_tree_tuple = &mut self.optional_trees[i];

            if let Some(instancied_tree) = optional_tree_tuple.1.get_mut() {
                optional_tree_tuple.0.delete_from(instancied_tree, &spog); // assert true
            }
        }

        true
    }
}

impl TreedDataset {
    /// Returns an iterator on Sophia Quads that matches the given pattern of indexes.
    /// 
    /// indexes is in the format on four term indexes, in the order Subject,
    /// Prdicate, Object, Graph. None means every term must be matched, a given
    /// value that only the given term must be matched.
    fn quads_with_opt_spog<'s>(&'s self, indexes: [Option<u32>; 4]) -> DQuadSource<'s, Self> {
        let quads = self.filter(indexes);
        InflatedQuadsIterator::new_box(quads, &self.term_index)
    }
}

impl Dataset for TreedDataset {
    type Quad = ByValue<SophiaExportQuad>;
    type Error = Infallible;

    fn quads<'a>(&'a self) -> DQuadSource<'a, Self> {
        self.quads_with_opt_spog([None, None, None, None])
    }

    // One term
    fn quads_with_s<'s, TS>(&'s self, s: &'s Term<TS>) -> DQuadSource<'s, Self>
    where TS: TermData {
        let s = self.term_index.get_index(&s.into());
        if s.is_none() {
            return Box::new(empty());
        } else {
            self.quads_with_opt_spog([s, None, None, None])
        }
    }

    fn quads_with_p<'s, TP>(&'s self, p: &'s Term<TP>) -> DQuadSource<'s, Self>
    where TP: TermData {
        let p = self.term_index.get_index(&p.into());
        if p.is_none() {
            return Box::new(empty());
        } else {
            self.quads_with_opt_spog([None, p, None, None])
        }
    }

    fn quads_with_o<'s, TO>(&'s self, o: &'s Term<TO>) -> DQuadSource<'s, Self>
    where TO: TermData {
        let o = self.term_index.get_index(&o.into());
        if o.is_none() {
            return Box::new(empty());
        } else {
            self.quads_with_opt_spog([None, None, o, None])
        }
    }

    fn quads_with_g<'s, TG>(&'s self, g: Option<&'s Term<TG>>) -> DQuadSource<'s, Self>
    where TG: TermData
    {
        let g = self.term_index.get_index_for_graph_name(g.map(RefTerm::from).as_ref());
        if g.is_none() {
            return Box::new(empty());
        } else {
            self.quads_with_opt_spog([None, None, None, g])
        }
    }

    // Two terms
    fn quads_with_sp<'s, TS, TP>(&'s self, s: &'s Term<TS>, p: &'s Term<TP>) -> DQuadSource<'s, Self>
    where TS: TermData, TP: TermData {
        let s = self.term_index.get_index(&s.into());
        if s.is_none() {
            return Box::new(empty());
        }

        let p = self.term_index.get_index(&p.into());
        if p.is_none() {
            return Box::new(empty());
        }
        
        self.quads_with_opt_spog([s, p, None, None])
    }

    fn quads_with_so<'s, TS, TO>(&'s self, s: &'s Term<TS>, o: &'s Term<TO>) -> DQuadSource<'s, Self>
    where TS: TermData, TO: TermData {
        let s = self.term_index.get_index(&s.into());
        if s.is_none() {
            return Box::new(empty());
        }

        let o = self.term_index.get_index(&o.into());
        if o.is_none() {
            return Box::new(empty());
        }
        
        self.quads_with_opt_spog([s, None, o, None])
    }

    fn quads_with_sg<'s, TS, TG>(&'s self, s: &'s Term<TS>, g: Option<&'s Term<TG>>) -> DQuadSource<'s, Self>
    where TS: TermData, TG: TermData {
        let s = self.term_index.get_index(&s.into());
        if s.is_none() {
            return Box::new(empty());
        }

        let g = self.term_index.get_index_for_graph_name(g.map(RefTerm::from).as_ref());
        if g.is_none() {
            return Box::new(empty());
        }
        
        self.quads_with_opt_spog([s, None, None, g])
    }

    fn quads_with_po<'s, TP, TO>(&'s self, p: &'s Term<TP>, o: &'s Term<TO>) -> DQuadSource<'s, Self>
    where TP: TermData, TO: TermData {
        let p = self.term_index.get_index(&p.into());
        if p.is_none() {
            return Box::new(empty());
        }

        let o = self.term_index.get_index(&o.into());
        if o.is_none() {
            return Box::new(empty());
        }
        
        self.quads_with_opt_spog([None, p, o, None])
    }

    fn quads_with_pg<'s, TP, TG>(&'s self, p: &'s Term<TP>, g: Option<&'s Term<TG>>) -> DQuadSource<'s, Self>
    where TP: TermData, TG: TermData {
        let p = self.term_index.get_index(&p.into());
        if p.is_none() {
            return Box::new(empty());
        }

        let g = self.term_index.get_index_for_graph_name(g.map(RefTerm::from).as_ref());
        if g.is_none() {
            return Box::new(empty());
        }
        
        self.quads_with_opt_spog([None, p, None, g])
    }

    fn quads_with_og<'s, TO, TG>(&'s self, o: &'s Term<TO>, g: Option<&'s Term<TG>>) -> DQuadSource<'s, Self>
    where TO: TermData, TG: TermData {
        let o = self.term_index.get_index(&o.into());
        if o.is_none() {
            return Box::new(empty());
        }

        let g = self.term_index.get_index_for_graph_name(g.map(RefTerm::from).as_ref());
        if g.is_none() {
            return Box::new(empty());
        }
        
        self.quads_with_opt_spog([None, None, o, g])
    }

    // Three terms
    fn quads_with_spo<'s, TS, TP, TO>(&'s self, s: &'s Term<TS>, p: &'s Term<TP>, o: &'s Term<TO>) -> DQuadSource<'s, Self>
    where TS: TermData, TP: TermData, TO: TermData {
        let s = self.term_index.get_index(&s.into());
        if s.is_none() {
            return Box::new(empty());
        }

        let p = self.term_index.get_index(&p.into());
        if p.is_none() {
            return Box::new(empty());
        }

        let o = self.term_index.get_index(&o.into());
        if o.is_none() {
            return Box::new(empty());
        }
        
        self.quads_with_opt_spog([s, p, o, None])
    }

    fn quads_with_spg<'s, TS, TP, TG>(&'s self, s: &'s Term<TS>, p: &'s Term<TP>, g: Option<&'s Term<TG>>) -> DQuadSource<'s, Self>
    where TS: TermData, TP: TermData, TG: TermData {
        let s = self.term_index.get_index(&s.into());
        if s.is_none() {
            return Box::new(empty());
        }

        let p = self.term_index.get_index(&p.into());
        if p.is_none() {
            return Box::new(empty());
        }

        let g = self.term_index.get_index_for_graph_name(g.map(RefTerm::from).as_ref());
        if g.is_none() {
            return Box::new(empty());
        }
        
        self.quads_with_opt_spog([s, p, None, g])
    }

    fn quads_with_sog<'s, TS, TO, TG>(&'s self, s: &'s Term<TS>, o: &'s Term<TO>, g: Option<&'s Term<TG>>) -> DQuadSource<'s, Self>
    where TS: TermData, TO: TermData, TG: TermData {
        let s = self.term_index.get_index(&s.into());
        if s.is_none() {
            return Box::new(empty());
        }

        let o = self.term_index.get_index(&o.into());
        if o.is_none() {
            return Box::new(empty());
        }

        let g = self.term_index.get_index_for_graph_name(g.map(RefTerm::from).as_ref());
        if g.is_none() {
            return Box::new(empty());
        }
        
        self.quads_with_opt_spog([s, None, o, g])
    }

    fn quads_with_pog<'s, TP, TO, TG>(&'s self, p: &'s Term<TP>, o: &'s Term<TO>, g: Option<&'s Term<TG>>) -> DQuadSource<'s, Self>
    where TP: TermData, TO: TermData, TG: TermData {
        let p = self.term_index.get_index(&p.into());
        if p.is_none() {
            return Box::new(empty());
        }
        
        let o = self.term_index.get_index(&o.into());
        if o.is_none() {
            return Box::new(empty());
        }

        let g = self.term_index.get_index_for_graph_name(g.map(RefTerm::from).as_ref());
        if g.is_none() {
            return Box::new(empty());
        }
        
        self.quads_with_opt_spog([None, p, o, g])
    }
    
    // Four terms

    fn quads_with_spog<'s, T1, T2, T3, T4>(&'s self, t1: &'s Term<T1>, t2: &'s Term<T2>, t3: &'s Term<T3>, t4: Option<&'s Term<T4>>) -> DQuadSource<'s, Self>
    where T1: TermData, T2: TermData, T3: TermData, T4: TermData
    {
        let t1 = self.term_index.get_index(&t1.into());
        let t2 = self.term_index.get_index(&t2.into());
        let t3 = self.term_index.get_index(&t3.into());
        let t4 = self.term_index.get_index_for_graph_name(t4.map(RefTerm::from).as_ref());
        match (t1, t2, t3, t4) {
            (Some(_), Some(_), Some(_), Some(_)) => {
                self.quads_with_opt_spog([t1, t2, t3, t4])
            },
            (_, _, _, _) => Box::new(empty())
        }
    }
}

/// An adapter that transforms an iterator on four term indexes into an iterator
/// of Sophia Quads
pub struct InflatedQuadsIterator<'a> {
    base_iterator: QuadIndexFromSubTreeDataset<'a>,
    term_index: &'a TermIndexMapU<u32, RcTermFactory>
}

impl<'a> InflatedQuadsIterator<'a> {
    /// Builds a Box of InflatedQuadsIterator from an iterator on term indexes
    /// and a `TermIndexMap` to match the `DQuadSource` interface.
    pub fn new_box(
        base_iterator: QuadIndexFromSubTreeDataset<'a>,
        term_index: &'a TermIndexMapU<u32, RcTermFactory>
    ) -> Box<InflatedQuadsIterator<'a>> {
        Box::new(InflatedQuadsIterator {
            base_iterator: base_iterator,
            term_index: term_index
        })
    }
}

impl<'a> Iterator for InflatedQuadsIterator<'a> {
    type Item = DResult<TreedDataset, DQuad<'a, TreedDataset>>;

    fn next(&mut self) -> Option<Self::Item> {
        self.base_iterator.next().map(|spog| {
            let s = self.term_index.get_term(spog[0]).unwrap();
            let p = self.term_index.get_term(spog[1]).unwrap();
            let o = self.term_index.get_term(spog[2]).unwrap();
            let g = self.term_index.get_graph_name(spog[3]).unwrap();
            Ok(StreamedQuad::by_value(SophiaExportQuad::new(&s, &p, &o, g)))
        })
    }
}

impl MutableDataset for TreedDataset {
    type MutationError = Infallible;

    fn insert<T, U, V, W>(
        &mut self,
        s: &Term<T>,
        p: &Term<U>,
        o: &Term<V>,
        g: Option<&Term<W>>,
    ) -> MDResult<Self, bool>
    where
        T: TermData,
        U: TermData,
        V: TermData,
        W: TermData,
    {
        let si = self.term_index.make_index(&s.into());
        let pi = self.term_index.make_index(&p.into());
        let oi = self.term_index.make_index(&o.into());
        let gi = self
            .term_index
            .make_index_for_graph_name(g.map(RefTerm::from).as_ref());
        let modified = self.insert_by_index([si, pi, oi, gi]);
        if modified {
            //Some([si, pi, oi, gi])
        } else {
            self.term_index.dec_ref(si);
            self.term_index.dec_ref(pi);
            self.term_index.dec_ref(oi);
            self.term_index.dec_ref(gi);
            //None
        };

        Ok(modified)
    }

    fn remove<T, U, V, W>(
        &mut self,
        s: &Term<T>,
        p: &Term<U>,
        o: &Term<V>,
        g: Option<&Term<W>>,
    ) -> MDResult<Self, bool>
    where
        T: TermData,
        U: TermData,
        V: TermData,
        W: TermData,
    {
        let si = self.term_index.get_index(&s.into());
        let pi = self.term_index.get_index(&p.into());
        let oi = self.term_index.get_index(&o.into());
        let gi = self
            .term_index
            .get_index_for_graph_name(g.map(RefTerm::from).as_ref());
        if let (Some(si), Some(pi), Some(oi), Some(gi)) = (si, pi, oi, gi) {
            let modified = self.delete_by_index([si, pi, oi, gi]);
            if modified {
                self.term_index.dec_ref(si);
                self.term_index.dec_ref(pi);
                self.term_index.dec_ref(oi);
                self.term_index.dec_ref(gi);
                return Ok(true);
            }
        }
 
        Ok(false)
    }
}


#[cfg(test)]
sophia::test_dataset_impl!(test_fulldataset, TreedDataset);