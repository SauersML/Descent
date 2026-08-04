//! Minimal compilation boundary for the executable correctability calculator.
//!
//! Keeping this crate independent from the application workspace lets proof CI
//! validate the numerical contract without compiling unrelated application code.

// The path is relative to the directory holding THIS file, so it needs four
// levels to reach the repository root:
//   correctability_calculator -> empirical -> validation -> proofs -> <root>
// It carried three for as long as the step has been required, which made the
// crate fail to compile -- `couldn't find file ../../../map/correctability.rs`
// -- so the one CI gate that executes the shipped calculator never executed
// anything. A `cargo test` that cannot build is not a weaker check than one
// that builds; it is no check at all, and it fails in a way that reads like
// infrastructure noise rather than a corpus finding.
#[path = "../../../../map/correctability.rs"]
pub mod correctability;
