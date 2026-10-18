//! Explicit cubical theory data and frozen certificates. This module adds no
//! inference or reduction algorithm to the generic kernel. See docs/CUBICAL.md.

/// Order matters: later fragments use declarations from earlier fragments.
pub const FRAGMENTS: &[(&str, &str)] = &[
    ("path", include_str!("../theories/cubical/path.horn")),
    ("faces", include_str!("../theories/cubical/faces.horn")),
    (
        "face-ops",
        include_str!("../theories/cubical/face-ops.horn"),
    ),
    (
        "restricted",
        include_str!("../theories/cubical/restricted.horn"),
    ),
    ("systems", include_str!("../theories/cubical/systems.horn")),
    (
        "composition",
        include_str!("../theories/cubical/composition.horn"),
    ),
    ("sigma", include_str!("../theories/cubical/sigma.horn")),
    (
        "equivalence-defs",
        include_str!("../theories/cubical/equivalence-defs.horn"),
    ),
    ("glue", include_str!("../theories/cubical/glue.horn")),
    (
        "equality",
        include_str!("../theories/cubical/equality.horn"),
    ),
    (
        "canonical-map",
        include_str!("../theories/cubical/canonical-map.horn"),
    ),
    (
        "computation",
        include_str!("../theories/cubical/computation.horn"),
    ),
];

pub fn theory() -> String {
    FRAGMENTS
        .iter()
        .map(|(_, source)| format!("{source}\n"))
        .collect()
}

pub struct Example {
    pub name: &'static str,
    pub description: &'static str,
    pub goals: &'static str,
    pub oracle: &'static [u8],
}

pub const EXAMPLES: &[Example] = &[
    Example {
        name: "univalence",
        description: "U0 univalence and its canonical-map function component",
        goals: include_str!("../examples/cubical/deep-univalence.goals"),
        oracle: include_bytes!("../examples/cubical/deep-univalence.oracle"),
    },
    Example {
        name: "ua-transport",
        description: "judgmental transport along ua via Glue composition",
        goals: include_str!("../examples/cubical/ua-transport.goals"),
        oracle: include_bytes!("../examples/cubical/ua-transport.oracle"),
    },
];
