use crate::RcQuad;

use identifier_forest::run_time_forest::IndexingForest4;
use identifier_forest::tree::{ Tree4Iterator, MaybeTree4, Forest4 };
use sophia::dataset::MutableDataset;
use sophia::dataset::DQuad;
use sophia::dataset::DQuadSource;
use sophia::dataset::Dataset;
use sophia::dataset::DResult;
use sophia::dataset::MDResult;
use sophia::graph::inmem::TermIndexMapU;
use sophia::quad::streaming_mode::ByValue;
use sophia::quad::streaming_mode::StreamedQuad;
use sophia::term::factory::RcTermFactory;
use sophia::term::index_map::TermIndexMap;
use sophia::term::RcTerm;
use sophia::term::RefTerm;
use sophia::term::Term;
use sophia::term::TermData;

use std::convert::Infallible;
use std::iter::empty;

#[cfg(test)]
use sophia::test_dataset_impl;


#[derive(Default)]
pub struct TreeDataset {
    /// Underlying trees that manipulates identifiers
    forest: IndexingForest4<u32>,
    /// A `TermIndexMapU` that matches RcTerms with u32 identifiers
    term_id_map: TermIndexMapU<u32, RcTermFactory>
}

impl TreeDataset {
    pub fn new() -> Self {
        Self::default()
    }

    /// Returns an iterator on Sophia Quads that matches the given pattern of indexes.
    /// 
    /// indexes is in the format on four term indexes, in the order Subject,
    /// Prdicate, Object, Graph. None means every term must be matched, a given
    /// value that only the given term must be matched.
    fn quads_with_opt_spog<'s>(&'s self, indexes: [Option<u32>; 4]) -> DQuadSource<'s, Self> {
        let quads = self.forest.get_quads(indexes);
        InflatedQuadsIterator::new_box(quads, &self.term_id_map)
    }
}

impl Dataset for TreeDataset {
    type Quad = ByValue<RcQuad>;
    type Error = Infallible;

    fn quads<'a>(&'a self) -> DQuadSource<'a, Self> {
        self.quads_with_opt_spog([None, None, None, None])
    }

    // One term
    fn quads_with_s<'s, TS>(&'s self, s: &'s Term<TS>) -> DQuadSource<'s, Self>
    where TS: TermData {
        let s = self.term_id_map.get_index(&s.into());
        if s.is_none() {
            return Box::new(empty());
        } else {
            self.quads_with_opt_spog([s, None, None, None])
        }
    }

    fn quads_with_p<'s, TP>(&'s self, p: &'s Term<TP>) -> DQuadSource<'s, Self>
    where TP: TermData {
        let p = self.term_id_map.get_index(&p.into());
        if p.is_none() {
            return Box::new(empty());
        } else {
            self.quads_with_opt_spog([None, p, None, None])
        }
    }

    fn quads_with_o<'s, TO>(&'s self, o: &'s Term<TO>) -> DQuadSource<'s, Self>
    where TO: TermData {
        let o = self.term_id_map.get_index(&o.into());
        if o.is_none() {
            return Box::new(empty());
        } else {
            self.quads_with_opt_spog([None, None, o, None])
        }
    }

    fn quads_with_g<'s, TG>(&'s self, g: Option<&'s Term<TG>>) -> DQuadSource<'s, Self>
    where TG: TermData
    {
        let g = self.term_id_map.get_index_for_graph_name(g.map(RefTerm::from).as_ref());
        if g.is_none() {
            return Box::new(empty());
        } else {
            self.quads_with_opt_spog([None, None, None, g])
        }
    }

    // Two terms
    fn quads_with_sp<'s, TS, TP>(&'s self, s: &'s Term<TS>, p: &'s Term<TP>) -> DQuadSource<'s, Self>
    where TS: TermData, TP: TermData {
        let s = self.term_id_map.get_index(&s.into());
        if s.is_none() {
            return Box::new(empty());
        }

        let p = self.term_id_map.get_index(&p.into());
        if p.is_none() {
            return Box::new(empty());
        }
        
        self.quads_with_opt_spog([s, p, None, None])
    }

    fn quads_with_so<'s, TS, TO>(&'s self, s: &'s Term<TS>, o: &'s Term<TO>) -> DQuadSource<'s, Self>
    where TS: TermData, TO: TermData {
        let s = self.term_id_map.get_index(&s.into());
        if s.is_none() {
            return Box::new(empty());
        }

        let o = self.term_id_map.get_index(&o.into());
        if o.is_none() {
            return Box::new(empty());
        }
        
        self.quads_with_opt_spog([s, None, o, None])
    }

    fn quads_with_sg<'s, TS, TG>(&'s self, s: &'s Term<TS>, g: Option<&'s Term<TG>>) -> DQuadSource<'s, Self>
    where TS: TermData, TG: TermData {
        let s = self.term_id_map.get_index(&s.into());
        if s.is_none() {
            return Box::new(empty());
        }

        let g = self.term_id_map.get_index_for_graph_name(g.map(RefTerm::from).as_ref());
        if g.is_none() {
            return Box::new(empty());
        }
        
        self.quads_with_opt_spog([s, None, None, g])
    }

    fn quads_with_po<'s, TP, TO>(&'s self, p: &'s Term<TP>, o: &'s Term<TO>) -> DQuadSource<'s, Self>
    where TP: TermData, TO: TermData {
        let p = self.term_id_map.get_index(&p.into());
        if p.is_none() {
            return Box::new(empty());
        }

        let o = self.term_id_map.get_index(&o.into());
        if o.is_none() {
            return Box::new(empty());
        }
        
        self.quads_with_opt_spog([None, p, o, None])
    }

    fn quads_with_pg<'s, TP, TG>(&'s self, p: &'s Term<TP>, g: Option<&'s Term<TG>>) -> DQuadSource<'s, Self>
    where TP: TermData, TG: TermData {
        let p = self.term_id_map.get_index(&p.into());
        if p.is_none() {
            return Box::new(empty());
        }

        let g = self.term_id_map.get_index_for_graph_name(g.map(RefTerm::from).as_ref());
        if g.is_none() {
            return Box::new(empty());
        }
        
        self.quads_with_opt_spog([None, p, None, g])
    }

    fn quads_with_og<'s, TO, TG>(&'s self, o: &'s Term<TO>, g: Option<&'s Term<TG>>) -> DQuadSource<'s, Self>
    where TO: TermData, TG: TermData {
        let o = self.term_id_map.get_index(&o.into());
        if o.is_none() {
            return Box::new(empty());
        }

        let g = self.term_id_map.get_index_for_graph_name(g.map(RefTerm::from).as_ref());
        if g.is_none() {
            return Box::new(empty());
        }
        
        self.quads_with_opt_spog([None, None, o, g])
    }

    // Three terms
    fn quads_with_spo<'s, TS, TP, TO>(&'s self, s: &'s Term<TS>, p: &'s Term<TP>, o: &'s Term<TO>) -> DQuadSource<'s, Self>
    where TS: TermData, TP: TermData, TO: TermData {
        let s = self.term_id_map.get_index(&s.into());
        if s.is_none() {
            return Box::new(empty());
        }

        let p = self.term_id_map.get_index(&p.into());
        if p.is_none() {
            return Box::new(empty());
        }

        let o = self.term_id_map.get_index(&o.into());
        if o.is_none() {
            return Box::new(empty());
        }
        
        self.quads_with_opt_spog([s, p, o, None])
    }

    fn quads_with_spg<'s, TS, TP, TG>(&'s self, s: &'s Term<TS>, p: &'s Term<TP>, g: Option<&'s Term<TG>>) -> DQuadSource<'s, Self>
    where TS: TermData, TP: TermData, TG: TermData {
        let s = self.term_id_map.get_index(&s.into());
        if s.is_none() {
            return Box::new(empty());
        }

        let p = self.term_id_map.get_index(&p.into());
        if p.is_none() {
            return Box::new(empty());
        }

        let g = self.term_id_map.get_index_for_graph_name(g.map(RefTerm::from).as_ref());
        if g.is_none() {
            return Box::new(empty());
        }
        
        self.quads_with_opt_spog([s, p, None, g])
    }

    fn quads_with_sog<'s, TS, TO, TG>(&'s self, s: &'s Term<TS>, o: &'s Term<TO>, g: Option<&'s Term<TG>>) -> DQuadSource<'s, Self>
    where TS: TermData, TO: TermData, TG: TermData {
        let s = self.term_id_map.get_index(&s.into());
        if s.is_none() {
            return Box::new(empty());
        }

        let o = self.term_id_map.get_index(&o.into());
        if o.is_none() {
            return Box::new(empty());
        }

        let g = self.term_id_map.get_index_for_graph_name(g.map(RefTerm::from).as_ref());
        if g.is_none() {
            return Box::new(empty());
        }
        
        self.quads_with_opt_spog([s, None, o, g])
    }

    fn quads_with_pog<'s, TP, TO, TG>(&'s self, p: &'s Term<TP>, o: &'s Term<TO>, g: Option<&'s Term<TG>>) -> DQuadSource<'s, Self>
    where TP: TermData, TO: TermData, TG: TermData {
        let p = self.term_id_map.get_index(&p.into());
        if p.is_none() {
            return Box::new(empty());
        }
        
        let o = self.term_id_map.get_index(&o.into());
        if o.is_none() {
            return Box::new(empty());
        }

        let g = self.term_id_map.get_index_for_graph_name(g.map(RefTerm::from).as_ref());
        if g.is_none() {
            return Box::new(empty());
        }
        
        self.quads_with_opt_spog([None, p, o, g])
    }
    
    // Four terms

    fn quads_with_spog<'s, T1, T2, T3, T4>(&'s self, t1: &'s Term<T1>, t2: &'s Term<T2>, t3: &'s Term<T3>, t4: Option<&'s Term<T4>>) -> DQuadSource<'s, Self>
    where T1: TermData, T2: TermData, T3: TermData, T4: TermData
    {
        let t1 = self.term_id_map.get_index(&t1.into());
        let t2 = self.term_id_map.get_index(&t2.into());
        let t3 = self.term_id_map.get_index(&t3.into());
        let t4 = self.term_id_map.get_index_for_graph_name(t4.map(RefTerm::from).as_ref());
        match (t1, t2, t3, t4) {
            (Some(_), Some(_), Some(_), Some(_)) => {
                self.quads_with_opt_spog([t1, t2, t3, t4])
            },
            (_, _, _, _) => Box::new(empty())
        }
    }
}

/// An adapter that transforms an iterator on identifier quads into an iterator
/// of Sophia Quads
pub struct InflatedQuadsIterator<'a> {
    base_iterator: Tree4Iterator<'a, u32>,
    term_id_map: &'a TermIndexMapU<u32, RcTermFactory>,
    last_tuple: Option<[(u32, &'a RcTerm); 3]>,
    last_graph: Option<(u32, &'a RcTerm)>
}

impl<'a> InflatedQuadsIterator<'a> {
    /// Builds a Box of InflatedQuadsIterator from an iterator on identifier quad
    /// and a `TermIndexMap` to match the `DQuadSource` interface.
    pub fn new_box(
        base_iterator: Tree4Iterator<'a, u32>,
        term_id_map: &'a TermIndexMapU<u32, RcTermFactory>
    ) -> Box<InflatedQuadsIterator<'a>> {
        Box::new(InflatedQuadsIterator {
            base_iterator: base_iterator,
            term_id_map: term_id_map,
            last_tuple: None,
            last_graph: None
        })
    }
}

impl<'a> Iterator for InflatedQuadsIterator<'a> {
    type Item = DResult<TreeDataset, DQuad<'a, TreeDataset>>;

    fn next(&mut self) -> Option<Self::Item> {
        self.base_iterator.next().map(|spog| {
            let s = match self.last_tuple {
                Some([(a, x), _, _]) if a == spog[0] => x,
                _ => self.term_id_map.get_term(spog[0]).unwrap()
            };
            let p = match self.last_tuple {
                Some([_, (a, x), _]) if a == spog[1] => x,
                _ => self.term_id_map.get_term(spog[1]).unwrap()
            };
            let o = match self.last_tuple {
                Some([_, _, (a, x)]) if a == spog[2] => x,
                _ => self.term_id_map.get_term(spog[2]).unwrap()
            };

            self.last_tuple = Some([(spog[0], s), (spog[1], p), (spog[2], o)]);

            let g = match (spog[3], self.last_graph) {
                (x, _) if x == TermIndexMapU::<u32, RcTermFactory>::NULL_INDEX => None,
                (x, Some((y, value))) if x == y => Some(value),
                (_, _) => {
                    let g = self.term_id_map.get_graph_name(spog[3]).unwrap();
                    self.last_graph = Some((spog[3], g.unwrap()));
                    g
                }
            };

            Ok(StreamedQuad::by_value(RcQuad::new(&s, &p, &o, g)))
        })
    }
}

impl MutableDataset for TreeDataset {
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
        let si = self.term_id_map.make_index(&s.into());
        let pi = self.term_id_map.make_index(&p.into());
        let oi = self.term_id_map.make_index(&o.into());
        let gi = self
            .term_id_map
            .make_index_for_graph_name(g.map(RefTerm::from).as_ref());
        let modified = self.forest.insert(&[si, pi, oi, gi]);
        if modified != Some(true) {
            self.term_id_map.dec_ref(si);
            self.term_id_map.dec_ref(pi);
            self.term_id_map.dec_ref(oi);
            self.term_id_map.dec_ref(gi);

            return Ok(false);
        };

        Ok(true)
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
        let si = self.term_id_map.get_index(&s.into());
        let pi = self.term_id_map.get_index(&p.into());
        let oi = self.term_id_map.get_index(&o.into());
        let gi = self
            .term_id_map
            .get_index_for_graph_name(g.map(RefTerm::from).as_ref());
        if let (Some(si), Some(pi), Some(oi), Some(gi)) = (si, pi, oi, gi) {
            let modified = self.forest.delete(&[si, pi, oi, gi]);
            if  modified == Some(true) {
                self.term_id_map.dec_ref(si);
                self.term_id_map.dec_ref(pi);
                self.term_id_map.dec_ref(oi);
                self.term_id_map.dec_ref(gi);
                return Ok(true);
            }
        }
 
        Ok(false)
    }
}

impl TreeDataset {
    /// Returns the number of currently instancied trees
    pub fn get_number_of_living_trees(&self) -> usize {
        self.forest.get_number_of_living_trees()
    }

    /// Ensure the optimal index tree for this forest is built for the given
    /// request pattern.
    pub fn ensure_has_index_for(&mut self, s: bool, p: bool, o: bool, g: bool) {
        self.forest.ensure_has_index_for(
            &[
                if s { Some(1_u32) } else { None },
                if p { Some(1_u32) } else { None },
                if o { Some(1_u32) } else { None },
                if g { Some(1_u32) } else { None }
            ]
        );
    }
}


#[cfg(test)]
sophia::test_dataset_impl!(test_treedataset, TreeDataset);
