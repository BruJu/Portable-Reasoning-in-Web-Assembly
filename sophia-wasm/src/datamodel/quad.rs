//! This modules contains the quad importation and exportation from Sophia and
//! javascript.

#![deny(missing_docs)]

extern crate wasm_bindgen;

use crate::datamodel::term::*;

use sophia::term::*;
use std::rc::Rc;
use wasm_bindgen::prelude::*;
use sophia::quad::Quad;


// ============================================================================
//   ==== IMPORTATION ==== IMPORTATION ==== IMPORTATION ==== IMPORTATION ====

#[wasm_bindgen]
extern "C" {
    /// A quad imported from the Javascript world
    #[wasm_bindgen(js_name = Quad)]
    pub type JsImportQuad;
    
    /// Returns the subject of the quad
    #[wasm_bindgen(method, getter)]
    pub fn subject(this: &JsImportQuad) -> JsImportTerm;

    /// Modifies the subject of the quad
    #[wasm_bindgen(method, setter)]
    pub fn set_subject(this: &JsImportQuad, value: &JsImportTerm);

    /// Returns the object of the quad
    #[wasm_bindgen(method, getter)]
    pub fn object(this: &JsImportQuad) -> JsImportTerm;

    /// Modifies the object of the quad
    #[wasm_bindgen(method, setter)]
    pub fn set_object(this: &JsImportQuad, value: &JsImportTerm);

    /// Returns the predicate of the quad
    #[wasm_bindgen(method, getter)]
    pub fn predicate(this: &JsImportQuad) -> JsImportTerm;

    /// Modifies the predicate of the quad
    #[wasm_bindgen(method, setter)]
    pub fn set_predicate(this: &JsImportQuad, value: &JsImportTerm);

    /// Returns the graph of the quad
    #[wasm_bindgen(method, getter)]
    pub fn graph(this: &JsImportQuad) -> JsImportTerm;

    /// Modifies the graph of the quad
    #[wasm_bindgen(method, setter)]
    pub fn set_graph(this: &JsImportQuad, value: &JsImportTerm);

    /// Returns true if the two quads are equals according to RDF.JS specification
    #[wasm_bindgen(js_name=equals)]
    pub fn quads_equals(this: &JsImportQuad, other_quad: &JsImportQuad);
    
    /// Returns a pointer to this quad.
    /// 
    /// This is mainly used to be able to detect a Rust managed quad from an
    /// imported quad (as wasm_bindgen doesn't let us use polymorphism).
    /// 
    /// Using this method can be very unsafe because it supposes only this
    /// object has a method called getRustPtr in the Javascript world. 
    #[wasm_bindgen(method, getter=getRustPtr)]
    pub fn quads_get_rust_ptr(this: &JsImportQuad) -> JsValue;
}


// ============================================================================
//   ==== EXPORTATION ==== EXPORTATION ==== EXPORTATION ==== EXPORTATION ====

/// A SophiaExportQuad owns its data in the form of four RcTerms.
#[wasm_bindgen(js_name = Quad)]
pub struct SophiaExportQuad {
    /// Subject of the quad
    #[wasm_bindgen(skip)]
    pub _subject: RcTerm,
    /// Predicate of the quad
    #[wasm_bindgen(skip)]
    pub _predicate: RcTerm,
    /// Object of the quad
    #[wasm_bindgen(skip)]
    pub _object: RcTerm,
    /// Graph of the quad. The default graph is represented as None
    #[wasm_bindgen(skip)]
    pub _graph: Option<RcTerm>
}

// A SophiaExportQuad is a trivial to implement as a quad
impl sophia::quad::Quad for SophiaExportQuad {
    type TermData = Rc<str>;

    fn s(&self) -> &RcTerm { &self._subject }
    fn p(&self) -> &RcTerm { &self._predicate }
    fn o(&self) -> &RcTerm { &self._object }
    fn g(&self) -> Option<&RcTerm> { self._graph.as_ref() }
}

impl SophiaExportQuad {
    /// Creates a new quad by cloning the passed RcTerms
    pub fn new(s: &RcTerm, p: &RcTerm, o: &RcTerm, g: Option<&RcTerm>) -> SophiaExportQuad {
        SophiaExportQuad {
            _subject: s.clone(),
            _predicate: p.clone(),
            _object: o.clone(),
            _graph: g.cloned()
        }
    }

    /// Creates a new SophiaExportQuad from a Quad which terms are RcTerm
    pub fn new_from_rcquad<Q>(quad: &Q) -> SophiaExportQuad
        where Q: Quad<TermData = Rc<str>> {
        SophiaExportQuad {
            _subject: quad.s().clone(),
            _predicate: quad.p().clone(),
            _object: quad.o().clone(),
            _graph: quad.g().cloned()
        }
    }

    /// Creates a new quad from a Sophia Quad
    pub fn new_from_quad<Q>(quad: &Q) -> SophiaExportQuad
        where Q: Quad {
        SophiaExportQuad {
            _subject: quad.s().into(),
            _predicate: quad.p().into(),
            _object: quad.o().into(),
            _graph: quad.g().clone().map(|t| t.into())
        }
    }
}

#[wasm_bindgen(js_class = Quad)]
impl SophiaExportQuad {
    /// Returns the subject of the quad
    #[wasm_bindgen(method, getter)]
    pub fn subject(&self) -> SophiaExportTerm {
        SophiaExportTerm::new(&self._subject)
    }

    /// Returns the predicate of the quad
    #[wasm_bindgen(method, getter)]
    pub fn predicate(&self) -> SophiaExportTerm {
        SophiaExportTerm::new(&self._predicate)
    }

    /// Returns the object of the quad
    #[wasm_bindgen(method, getter)]
    pub fn object(&self) -> SophiaExportTerm {
        SophiaExportTerm::new(&self._object)
    }

    /// Returns the graph of the quad
    #[wasm_bindgen(method, getter)]
    pub fn graph(&self) -> SophiaExportTerm {
        match &self._graph {
            None => SophiaExportTerm::default_graph(),
            Some(term) => SophiaExportTerm::new(term)
        }
    }
}

#[wasm_bindgen(js_class = Quad)]
impl SophiaExportQuad {
    /// Returns a N-Quad representation of the quad 
    #[wasm_bindgen(js_name = toString)]
    pub fn to_string(&self) -> String {
        match &self._graph {
            Some(g) => format!("{0} {1} {2} {3} .", self._subject, self._predicate, self._object, g),
            None    => format!("{0} {1} {2} ."    , self._subject, self._predicate, self._object)
        }
    }
}

#[wasm_bindgen(js_class = Quad)]
impl SophiaExportQuad {
    /// Returns true if the passed quad is identical to this quad according to
    /// RDF.JS specification ie the subject, predicate, object and graph are
    /// the same.
    #[wasm_bindgen(js_name = equals)]
    pub fn equals(&self, other: &JsImportQuad) -> bool {
        if other.is_null() {
            false
        } else {
            let ptr = other.quads_get_rust_ptr().as_f64();

            let ptr = match ptr {
                None => None,
                Some(ptr_val) => {
                    let ptr_u32 = ptr_val as u32;
                    let ptr_ptr = ptr_u32 as *const SophiaExportQuad;
                    unsafe { ptr_ptr.as_ref() }
                }
            };

            match ptr {
                None => self.subject().equals(&other.subject())
                        && self.predicate().equals(&other.predicate())
                        && self.object().equals(&other.object())
                        && self.graph().equals(&other.graph()),
                Some(exported_rust_quad) => {
                        self._subject == exported_rust_quad._subject
                        && self._predicate == exported_rust_quad._predicate
                        && self._object == exported_rust_quad._object
                        && self._graph == exported_rust_quad._graph
                }
            }
        }
    }
}

#[wasm_bindgen(js_class = Quad)]
impl SophiaExportQuad {
    /// Modifies the subject of this quad
    #[wasm_bindgen(method, setter)]
    pub fn set_subject(&mut self, other: &JsImportTerm) {
        self._subject = build_rcterm_from_js_import_term(other).unwrap();
    }
    
    /// Modifies the predicate of this quad
    #[wasm_bindgen(method, setter)]
    pub fn set_predicate(&mut self, other: &JsImportTerm) {
        self._predicate = build_rcterm_from_js_import_term(other).unwrap();
    }

    /// Modifies the object of this quad
    #[wasm_bindgen(method, setter)]
    pub fn set_object(&mut self, other: &JsImportTerm) {
        self._object = build_rcterm_from_js_import_term(other).unwrap();
    }
    
    /// Modifies the graph of this quad
    #[wasm_bindgen(method, setter)]
    pub fn set_graph(&mut self, other: &JsImportTerm) {
        self._graph = build_rcterm_from_js_import_term(other);
    }
}

#[wasm_bindgen(js_class = Quad)]
impl SophiaExportQuad {
    /// Returns a pointer to this quad.
    /// 
    /// This is mainly used to be able to detect a Rust managed quad from an
    /// imported quad (as wasm_bindgen doesn't let us use polymorphism).
    /// 
    /// Using this method can be very unsafe because it supposes only this
    /// object has a method called getRustPtr in the Javascript world. 
    #[wasm_bindgen(method, getter=getRustPtr)]
    pub fn quads_get_rust_ptr(&self) -> *const SophiaExportQuad {
        self
    }
}
