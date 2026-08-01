//! Minimal compilation boundary for the executable correctability calculator.
//!
//! Keeping this crate independent from the application workspace lets proof CI
//! validate the numerical contract without compiling unrelated application code.

#[path = "../../../map/correctability.rs"]
pub mod correctability;
