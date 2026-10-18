//! Untrusted certificate producer for the cubical theory, moved from kamo3
//! (src/*.rs at 199d677 plus the bool extension). It emits ordinary
//! derivations; nothing here is trusted. Each module is one construction.
#![allow(dead_code, clippy::all)]

pub mod canonical_code_frontend;
pub mod canonical_map_frontend;
pub mod canonical_ua_frontend;
pub mod canonicity_frontend;
pub mod compute_frontend;
pub mod constant_equiv_frontend;
pub mod constant_transport_frontend;
pub mod contr_prop_frontend;
pub mod deep_univalence_frontend;
pub mod equivalence_frontend;
pub mod equiv_ext_frontend;
pub mod face_frontend;
pub mod frontend;
pub mod glue_comp_frontend;
pub mod glue_fiber_frontend;
pub mod glue_frontend;
pub mod homotopy_frontend;
pub mod identity_frontend;
pub mod isequiv_prop_frontend;
pub mod iso_equiv_frontend;
pub mod path_frontend;
pub mod restricted_frontend;
pub mod to_pathp_frontend;
pub mod transport_equiv_frontend;
pub mod transport_frontend;
pub mod ua_beta_frontend;
pub mod ua_eta_frontend;
pub mod ua_frontend;
pub mod ua_graph_frontend;
pub mod ua_transport_frontend;
pub mod ua_unglue_frontend;
pub mod univalence_frontend;
