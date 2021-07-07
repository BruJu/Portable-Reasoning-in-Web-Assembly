//! This module lists every possible permutation of
//! [`Tree4Profile`](crate::compile_time_forest::Tree4Profile)
//! order for a tree of quads.
//! 
//! These permutation are intented to be used
//! as parameters for the [`CTForest`](crate::compile_time_forest::CTForest)
//! class
use super::*;


/// Profile for a lazy tree whose order
/// will be Subject > Predicate > Object > Graph
pub struct SPOG {}
impl Tree4Profile for SPOG {
    type First = Subject;
    type Second = Predicate;
    type Third = Object;
    type Fourth = Graph;
    const ALWAYS_INSTANCIATED: bool = false;
}

/// Profile for a tree that is always instanciated and whose order
/// is Subject > Predicate > Object > Graph
pub struct SPOGAlways {}
impl Tree4Profile for SPOGAlways {
    type First = Subject;
    type Second = Predicate;
    type Third = Object;
    type Fourth = Graph;
    const ALWAYS_INSTANCIATED: bool = true;
}

/// Profile for a lazy tree whose order
/// will be Subject > Predicate > Graph > Object
pub struct SPGO {}
impl Tree4Profile for SPGO {
    type First = Subject;
    type Second = Predicate;
    type Third = Graph;
    type Fourth = Object;
    const ALWAYS_INSTANCIATED: bool = false;
}

/// Profile for a tree that is always instanciated and whose order
/// is Subject > Predicate > Graph > Object
pub struct SPGOAlways {}
impl Tree4Profile for SPGOAlways {
    type First = Subject;
    type Second = Predicate;
    type Third = Graph;
    type Fourth = Object;
    const ALWAYS_INSTANCIATED: bool = true;
}

/// Profile for a lazy tree whose order
/// will be Subject > Object > Predicate > Graph
pub struct SOPG {}
impl Tree4Profile for SOPG {
    type First = Subject;
    type Second = Object;
    type Third = Predicate;
    type Fourth = Graph;
    const ALWAYS_INSTANCIATED: bool = false;
}

/// Profile for a tree that is always instanciated and whose order
/// is Subject > Object > Predicate > Graph
pub struct SOPGAlways {}
impl Tree4Profile for SOPGAlways {
    type First = Subject;
    type Second = Object;
    type Third = Predicate;
    type Fourth = Graph;
    const ALWAYS_INSTANCIATED: bool = true;
}

/// Profile for a lazy tree whose order
/// will be Subject > Object > Graph > Predicate
pub struct SOGP {}
impl Tree4Profile for SOGP {
    type First = Subject;
    type Second = Object;
    type Third = Graph;
    type Fourth = Predicate;
    const ALWAYS_INSTANCIATED: bool = false;
}

/// Profile for a tree that is always instanciated and whose order
/// is Subject > Object > Graph > Predicate
pub struct SOGPAlways {}
impl Tree4Profile for SOGPAlways {
    type First = Subject;
    type Second = Object;
    type Third = Graph;
    type Fourth = Predicate;
    const ALWAYS_INSTANCIATED: bool = true;
}

/// Profile for a lazy tree whose order
/// will be Subject > Graph > Predicate > Object
pub struct SGPO {}
impl Tree4Profile for SGPO {
    type First = Subject;
    type Second = Graph;
    type Third = Predicate;
    type Fourth = Object;
    const ALWAYS_INSTANCIATED: bool = false;
}

/// Profile for a tree that is always instanciated and whose order
/// is Subject > Graph > Predicate > Object
pub struct SGPOAlways {}
impl Tree4Profile for SGPOAlways {
    type First = Subject;
    type Second = Graph;
    type Third = Predicate;
    type Fourth = Object;
    const ALWAYS_INSTANCIATED: bool = true;
}

/// Profile for a lazy tree whose order
/// will be Subject > Graph > Object > Predicate
pub struct SGOP {}
impl Tree4Profile for SGOP {
    type First = Subject;
    type Second = Graph;
    type Third = Object;
    type Fourth = Predicate;
    const ALWAYS_INSTANCIATED: bool = false;
}

/// Profile for a tree that is always instanciated and whose order
/// is Subject > Graph > Object > Predicate
pub struct SGOPAlways {}
impl Tree4Profile for SGOPAlways {
    type First = Subject;
    type Second = Graph;
    type Third = Object;
    type Fourth = Predicate;
    const ALWAYS_INSTANCIATED: bool = true;
}

/// Profile for a lazy tree whose order
/// will be Predicate > Subject > Object > Graph
pub struct PSOG {}
impl Tree4Profile for PSOG {
    type First = Predicate;
    type Second = Subject;
    type Third = Object;
    type Fourth = Graph;
    const ALWAYS_INSTANCIATED: bool = false;
}

/// Profile for a tree that is always instanciated and whose order
/// is Predicate > Subject > Object > Graph
pub struct PSOGAlways {}
impl Tree4Profile for PSOGAlways {
    type First = Predicate;
    type Second = Subject;
    type Third = Object;
    type Fourth = Graph;
    const ALWAYS_INSTANCIATED: bool = true;
}

/// Profile for a lazy tree whose order
/// will be Predicate > Subject > Graph > Object
pub struct PSGO {}
impl Tree4Profile for PSGO {
    type First = Predicate;
    type Second = Subject;
    type Third = Graph;
    type Fourth = Object;
    const ALWAYS_INSTANCIATED: bool = false;
}

/// Profile for a tree that is always instanciated and whose order
/// is Predicate > Subject > Graph > Object
pub struct PSGOAlways {}
impl Tree4Profile for PSGOAlways {
    type First = Predicate;
    type Second = Subject;
    type Third = Graph;
    type Fourth = Object;
    const ALWAYS_INSTANCIATED: bool = true;
}

/// Profile for a lazy tree whose order
/// will be Predicate > Object > Subject > Graph
pub struct POSG {}
impl Tree4Profile for POSG {
    type First = Predicate;
    type Second = Object;
    type Third = Subject;
    type Fourth = Graph;
    const ALWAYS_INSTANCIATED: bool = false;
}

/// Profile for a tree that is always instanciated and whose order
/// is Predicate > Object > Subject > Graph
pub struct POSGAlways {}
impl Tree4Profile for POSGAlways {
    type First = Predicate;
    type Second = Object;
    type Third = Subject;
    type Fourth = Graph;
    const ALWAYS_INSTANCIATED: bool = true;
}

/// Profile for a lazy tree whose order
/// will be Predicate > Object > Graph > Subject
pub struct POGS {}
impl Tree4Profile for POGS {
    type First = Predicate;
    type Second = Object;
    type Third = Graph;
    type Fourth = Subject;
    const ALWAYS_INSTANCIATED: bool = false;
}

/// Profile for a tree that is always instanciated and whose order
/// is Predicate > Object > Graph > Subject
pub struct POGSAlways {}
impl Tree4Profile for POGSAlways {
    type First = Predicate;
    type Second = Object;
    type Third = Graph;
    type Fourth = Subject;
    const ALWAYS_INSTANCIATED: bool = true;
}

/// Profile for a lazy tree whose order
/// will be Predicate > Graph > Subject > Object
pub struct PGSO {}
impl Tree4Profile for PGSO {
    type First = Predicate;
    type Second = Graph;
    type Third = Subject;
    type Fourth = Object;
    const ALWAYS_INSTANCIATED: bool = false;
}

/// Profile for a tree that is always instanciated and whose order
/// is Predicate > Graph > Subject > Object
pub struct PGSOAlways {}
impl Tree4Profile for PGSOAlways {
    type First = Predicate;
    type Second = Graph;
    type Third = Subject;
    type Fourth = Object;
    const ALWAYS_INSTANCIATED: bool = true;
}

/// Profile for a lazy tree whose order
/// will be Predicate > Graph > Object > Subject
pub struct PGOS {}
impl Tree4Profile for PGOS {
    type First = Predicate;
    type Second = Graph;
    type Third = Object;
    type Fourth = Subject;
    const ALWAYS_INSTANCIATED: bool = false;
}

/// Profile for a tree that is always instanciated and whose order
/// is Predicate > Graph > Object > Subject
pub struct PGOSAlways {}
impl Tree4Profile for PGOSAlways {
    type First = Predicate;
    type Second = Graph;
    type Third = Object;
    type Fourth = Subject;
    const ALWAYS_INSTANCIATED: bool = true;
}

/// Profile for a lazy tree whose order
/// will be Object > Subject > Predicate > Graph
pub struct OSPG {}
impl Tree4Profile for OSPG {
    type First = Object;
    type Second = Subject;
    type Third = Predicate;
    type Fourth = Graph;
    const ALWAYS_INSTANCIATED: bool = false;
}

/// Profile for a tree that is always instanciated and whose order
/// is Object > Subject > Predicate > Graph
pub struct OSPGAlways {}
impl Tree4Profile for OSPGAlways {
    type First = Object;
    type Second = Subject;
    type Third = Predicate;
    type Fourth = Graph;
    const ALWAYS_INSTANCIATED: bool = true;
}

/// Profile for a lazy tree whose order
/// will be Object > Subject > Graph > Predicate
pub struct OSGP {}
impl Tree4Profile for OSGP {
    type First = Object;
    type Second = Subject;
    type Third = Graph;
    type Fourth = Predicate;
    const ALWAYS_INSTANCIATED: bool = false;
}

/// Profile for a tree that is always instanciated and whose order
/// is Object > Subject > Graph > Predicate
pub struct OSGPAlways {}
impl Tree4Profile for OSGPAlways {
    type First = Object;
    type Second = Subject;
    type Third = Graph;
    type Fourth = Predicate;
    const ALWAYS_INSTANCIATED: bool = true;
}

/// Profile for a lazy tree whose order
/// will be Object > Predicate > Subject > Graph
pub struct OPSG {}
impl Tree4Profile for OPSG {
    type First = Object;
    type Second = Predicate;
    type Third = Subject;
    type Fourth = Graph;
    const ALWAYS_INSTANCIATED: bool = false;
}

/// Profile for a tree that is always instanciated and whose order
/// is Object > Predicate > Subject > Graph
pub struct OPSGAlways {}
impl Tree4Profile for OPSGAlways {
    type First = Object;
    type Second = Predicate;
    type Third = Subject;
    type Fourth = Graph;
    const ALWAYS_INSTANCIATED: bool = true;
}

/// Profile for a lazy tree whose order
/// will be Object > Predicate > Graph > Subject
pub struct OPGS {}
impl Tree4Profile for OPGS {
    type First = Object;
    type Second = Predicate;
    type Third = Graph;
    type Fourth = Subject;
    const ALWAYS_INSTANCIATED: bool = false;
}

/// Profile for a tree that is always instanciated and whose order
/// is Object > Predicate > Graph > Subject
pub struct OPGSAlways {}
impl Tree4Profile for OPGSAlways {
    type First = Object;
    type Second = Predicate;
    type Third = Graph;
    type Fourth = Subject;
    const ALWAYS_INSTANCIATED: bool = true;
}

/// Profile for a lazy tree whose order
/// will be Object > Graph > Subject > Predicate
pub struct OGSP {}
impl Tree4Profile for OGSP {
    type First = Object;
    type Second = Graph;
    type Third = Subject;
    type Fourth = Predicate;
    const ALWAYS_INSTANCIATED: bool = false;
}

/// Profile for a tree that is always instanciated and whose order
/// is Object > Graph > Subject > Predicate
pub struct OGSPAlways {}
impl Tree4Profile for OGSPAlways {
    type First = Object;
    type Second = Graph;
    type Third = Subject;
    type Fourth = Predicate;
    const ALWAYS_INSTANCIATED: bool = true;
}

/// Profile for a lazy tree whose order
/// will be Object > Graph > Predicate > Subject
pub struct OGPS {}
impl Tree4Profile for OGPS {
    type First = Object;
    type Second = Graph;
    type Third = Predicate;
    type Fourth = Subject;
    const ALWAYS_INSTANCIATED: bool = false;
}

/// Profile for a tree that is always instanciated and whose order
/// is Object > Graph > Predicate > Subject
pub struct OGPSAlways {}
impl Tree4Profile for OGPSAlways {
    type First = Object;
    type Second = Graph;
    type Third = Predicate;
    type Fourth = Subject;
    const ALWAYS_INSTANCIATED: bool = true;
}

/// Profile for a lazy tree whose order
/// will be Graph > Subject > Predicate > Object
pub struct GSPO {}
impl Tree4Profile for GSPO {
    type First = Graph;
    type Second = Subject;
    type Third = Predicate;
    type Fourth = Object;
    const ALWAYS_INSTANCIATED: bool = false;
}

/// Profile for a tree that is always instanciated and whose order
/// is Graph > Subject > Predicate > Object
pub struct GSPOAlways {}
impl Tree4Profile for GSPOAlways {
    type First = Graph;
    type Second = Subject;
    type Third = Predicate;
    type Fourth = Object;
    const ALWAYS_INSTANCIATED: bool = true;
}

/// Profile for a lazy tree whose order
/// will be Graph > Subject > Object > Predicate
pub struct GSOP {}
impl Tree4Profile for GSOP {
    type First = Graph;
    type Second = Subject;
    type Third = Object;
    type Fourth = Predicate;
    const ALWAYS_INSTANCIATED: bool = false;
}

/// Profile for a tree that is always instanciated and whose order
/// is Graph > Subject > Object > Predicate
pub struct GSOPAlways {}
impl Tree4Profile for GSOPAlways {
    type First = Graph;
    type Second = Subject;
    type Third = Object;
    type Fourth = Predicate;
    const ALWAYS_INSTANCIATED: bool = true;
}

/// Profile for a lazy tree whose order
/// will be Graph > Predicate > Subject > Object
pub struct GPSO {}
impl Tree4Profile for GPSO {
    type First = Graph;
    type Second = Predicate;
    type Third = Subject;
    type Fourth = Object;
    const ALWAYS_INSTANCIATED: bool = false;
}

/// Profile for a tree that is always instanciated and whose order
/// is Graph > Predicate > Subject > Object
pub struct GPSOAlways {}
impl Tree4Profile for GPSOAlways {
    type First = Graph;
    type Second = Predicate;
    type Third = Subject;
    type Fourth = Object;
    const ALWAYS_INSTANCIATED: bool = true;
}

/// Profile for a lazy tree whose order
/// will be Graph > Predicate > Object > Subject
pub struct GPOS {}
impl Tree4Profile for GPOS {
    type First = Graph;
    type Second = Predicate;
    type Third = Object;
    type Fourth = Subject;
    const ALWAYS_INSTANCIATED: bool = false;
}

/// Profile for a tree that is always instanciated and whose order
/// is Graph > Predicate > Object > Subject
pub struct GPOSAlways {}
impl Tree4Profile for GPOSAlways {
    type First = Graph;
    type Second = Predicate;
    type Third = Object;
    type Fourth = Subject;
    const ALWAYS_INSTANCIATED: bool = true;
}

/// Profile for a lazy tree whose order
/// will be Graph > Object > Subject > Predicate
pub struct GOSP {}
impl Tree4Profile for GOSP {
    type First = Graph;
    type Second = Object;
    type Third = Subject;
    type Fourth = Predicate;
    const ALWAYS_INSTANCIATED: bool = false;
}

/// Profile for a tree that is always instanciated and whose order
/// is Graph > Object > Subject > Predicate
pub struct GOSPAlways {}
impl Tree4Profile for GOSPAlways {
    type First = Graph;
    type Second = Object;
    type Third = Subject;
    type Fourth = Predicate;
    const ALWAYS_INSTANCIATED: bool = true;
}

/// Profile for a lazy tree whose order
/// will be Graph > Object > Predicate > Subject
pub struct GOPS {}
impl Tree4Profile for GOPS {
    type First = Graph;
    type Second = Object;
    type Third = Predicate;
    type Fourth = Subject;
    const ALWAYS_INSTANCIATED: bool = false;
}

/// Profile for a tree that is always instanciated and whose order
/// is Graph > Object > Predicate > Subject
pub struct GOPSAlways {}
impl Tree4Profile for GOPSAlways {
    type First = Graph;
    type Second = Object;
    type Third = Predicate;
    type Fourth = Subject;
    const ALWAYS_INSTANCIATED: bool = true;
}
