//! This modules implements the DatasetCore interface from the RDF.JS
//! specification. The implementation also offers many services from the
//! Dataset class.

//#![deny(missing_docs)]

use crate::wasm_bindgen_dataset;
use crate::wasm_bindgen_wrappeddataset;
use crate::wrappers_example::VecOrDatasetWrapper;
use crate::wrapping::*;

extern crate wasm_bindgen;
use wasm_bindgen::prelude::*;

use sophia::dataset::inmem::FastDataset;
use sophia::dataset::inmem::LightDataset;
use sophia::term::BoxTerm;

use bjdatasets::treedataset::TreeDataset;
use bjdatasets::fulldataset::FullIndexDataset;


// Dataset structure created by the factory
wasm_bindgen_dataset!(TreeDataset, "TreeDataset", SophiaExportDataset);

#[wasm_bindgen(js_class="TreeDataset")]
impl SophiaExportDataset {
    #[wasm_bindgen(js_name = getNumberOfLivingTrees)]
    pub fn get_number_of_living_trees(&self) -> usize {
        self.base.dataset().get_number_of_living_trees()
    }

    #[wasm_bindgen(js_name = ensureHasIndexFor)]
    pub fn ensure_has_index_for(&mut self, s: bool, p: bool, o: bool, g: bool) {
        self.base.mutable_dataset().ensure_has_index_for(s, p, o, g);
    }
}

// Other usable datasets
wasm_bindgen_dataset!(FastDataset, "FastDataset");
wasm_bindgen_dataset!(LightDataset, "LightDataset");
wasm_bindgen_dataset!(FullIndexDataset, "FullDataset");

// Array Dataset (which is not a real set)
type ArrayDataset = Vec<([BoxTerm; 3], Option<BoxTerm>)>;
wasm_bindgen_dataset!(ArrayDataset, "ArrayDataset");

// Datasets that fills an array instead of the base complicated structure
type TreeDatasetIntoArrayWrapper = VecOrDatasetWrapper<TreeDataset>;
type FastDatasetIntoArrayWrapper = VecOrDatasetWrapper<FastDataset>;
type LightDatasetIntoArrayWrapper = VecOrDatasetWrapper<LightDataset>;
type FullIndexDatasetIntoArrayWrapper = VecOrDatasetWrapper<FullIndexDataset>;

wasm_bindgen_wrappeddataset!(TreeDatasetIntoArrayWrapper, "TreeDatasetToA");
wasm_bindgen_wrappeddataset!(FastDatasetIntoArrayWrapper, "FastDatasetToA");
wasm_bindgen_wrappeddataset!(LightDatasetIntoArrayWrapper, "LightDatasetToA");
wasm_bindgen_wrappeddataset!(FullIndexDatasetIntoArrayWrapper, "FullDatasetToA");
