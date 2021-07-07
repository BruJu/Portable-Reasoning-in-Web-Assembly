//! This module exports some wrappers of datasets that have some methods
//! redefined

use crate::datamodel::term::JsImportTerm;
use crate::wrapping::ExportableDataset;
use crate::wrapping::MatchRequestOnRcTerm;
use bjdatasets::vecordataset::VecOrDataset;

use sophia::dataset::Dataset;
use sophia::dataset::MutableDataset;
use sophia::quad::stream::QuadSource;

/// A dataset instanciated as a `D` when using the default constructor, but as
/// a vector when the `match_quad` function is used.
#[derive(Default)]
pub struct VecOrDatasetWrapper<D> where D: Dataset + MutableDataset + Default {
    base: VecOrDataset<D>
}

impl<D> ExportableDataset<VecOrDataset<D>> for VecOrDatasetWrapper<D>
    where D: Dataset + MutableDataset + Default,
     <D as MutableDataset>::MutationError: From<<D as Dataset>::Error>,
     <D as MutableDataset>::MutationError: From<std::convert::Infallible> {
    
    fn wrap(dataset: VecOrDataset<D>) -> Self {
        Self { base: dataset }
    }

    fn dataset(&self) -> &VecOrDataset<D> {
        &self.base
    }

    fn mutable_dataset(&mut self) -> &mut VecOrDataset<D> {
        &mut self.base
    }

    fn match_quad(&self, subject: &JsImportTerm, predicate: &JsImportTerm, object: &JsImportTerm, graph: &JsImportTerm) -> Self {
        let m = MatchRequestOnRcTerm::new(subject, predicate, object, graph);
        let mut quads_iter = self.dataset().quads_matching(&m.s, &m.p, &m.o, &m.g);
        let mut dataset = VecOrDataset::<D>::new_vector();
        quads_iter.in_dataset(&mut dataset).unwrap();
    
        Self::wrap(dataset)
    }
}
