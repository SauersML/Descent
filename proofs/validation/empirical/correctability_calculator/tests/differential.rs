//! Numeric differential: every Calibrator.PCCorrectability definition evaluated
//! against the shipped calculator on one shared fixture grid.
//!
//! The Lean side cannot be executed -- those definitions are `noncomputable`
//! over `ℝ` -- so its answers arrive as `lean_code_map/expected.json`, which
//! `lean_code_map/map_check.py` regenerates from the transcribed bodies and
//! refuses to let drift. This test runs the REAL `map/correctability.rs` on
//! `lean_code_map/fixtures.json` and requires the two to agree.
//!
//! Both files are `include_str!`d, so a moved or deleted fixture set is a
//! compile error rather than a silently skipped test. That failure mode is not
//! hypothetical here: this crate reached the implementation through a `#[path]`
//! that was one directory short, so the required CI step could not compile and
//! executed nothing at all for as long as it had existed.
//!
//! What the grid is for: the corpus's own reference-point theorems pin its
//! definitions only where they are evaluated, and two of them were evaluated at
//! `m = n`, where the spike collapses to zero and every constant satisfies them.
//! A `4 -> 2` spike constant passes all sixteen reference points. It does not
//! survive one pass over this grid.

use correctability_calculator_contract::correctability::{calculate, CorrectabilityInput};
use serde::Deserialize;

const FIXTURES: &str = include_str!("../../lean_code_map/fixtures.json");
const EXPECTED: &str = include_str!("../../lean_code_map/expected.json");

/// Relative tolerance. The two sides evaluate the same expressions in the same
/// order but in different languages, so `x.powi(2)` against `x ** 2` is the
/// kind of last-bit difference that is not a finding. It is tight enough to
/// have caught every planted one-character mutation of the Lean bodies,
/// including dropping a single `sqrt`.
const TOLERANCE: f64 = 1e-12;

#[derive(Deserialize)]
struct Fixture {
    tag: String,
    #[serde(flatten)]
    input: CorrectabilityInput,
}

#[derive(Deserialize)]
struct ExpectedReport {
    effective_subgroup_size: f64,
    total_frequency_information: f64,
    combined_information_index: f64,
    marker_classes: Vec<ExpectedClass>,
}

#[derive(Deserialize)]
struct ExpectedClass {
    aspect_ratio: f64,
    bbp_spike: f64,
    bbp_threshold: f64,
    margin: f64,
    detectable_by_sample_pca: bool,
    included_by_fitted_pcs: bool,
    sample_pc_overlap_squared: f64,
    removed_axis_fraction: f64,
    residual_axis_fraction: f64,
    matched_weight: f64,
    information: f64,
    residual_susceptibility: Option<f64>,
    standardized_bias: Option<f64>,
    critical_confounding: Option<f64>,
}

fn close(actual: f64, expected: f64) -> bool {
    if actual == expected {
        return true;
    }
    if !actual.is_finite() || !expected.is_finite() {
        return false;
    }
    let scale = actual.abs().max(expected.abs());
    (actual - expected).abs() <= TOLERANCE * scale
}

fn close_opt(actual: Option<f64>, expected: Option<f64>) -> bool {
    match (actual, expected) {
        (None, None) => true,
        (Some(a), Some(b)) => close(a, b),
        _ => false,
    }
}

#[test]
fn every_lean_body_agrees_with_the_shipped_calculator() {
    let fixtures: Vec<Fixture> = serde_json::from_str(FIXTURES).expect("fixtures.json");
    let expected: Vec<ExpectedReport> = serde_json::from_str(EXPECTED).expect("expected.json");
    assert_eq!(
        fixtures.len(),
        expected.len(),
        "fixtures.json and expected.json disagree on how many designs there are; \
         regenerate both with lean_code_map/gen_fixtures.py"
    );
    assert!(
        fixtures.len() >= 100,
        "the fixture grid has shrunk to {}; a grid small enough to miss a wrong \
         constant is worse than no differential, because it reports PASS",
        fixtures.len()
    );

    let mut disagreements = Vec::new();
    let mut comparisons = 0usize;

    for (fixture, want) in fixtures.iter().zip(expected.iter()) {
        let report = match calculate(&fixture.input) {
            Ok(report) => report,
            Err(error) => {
                disagreements.push(format!(
                    "{}: the calculator rejected a fixture the corpus scores: {error}",
                    fixture.tag
                ));
                continue;
            }
        };

        let mut check = |field: &str, actual: f64, expected: f64| {
            comparisons += 1;
            if !close(actual, expected) {
                disagreements.push(format!(
                    "{} {field}: implementation {actual:?}, corpus {expected:?}",
                    fixture.tag
                ));
            }
        };
        check(
            "effective_subgroup_size",
            report.effective_subgroup_size,
            want.effective_subgroup_size,
        );
        check(
            "total_frequency_information",
            report.total_frequency_information,
            want.total_frequency_information,
        );
        check(
            "combined_information_index",
            report.combined_information_index,
            want.combined_information_index,
        );

        assert_eq!(
            report.marker_classes.len(),
            want.marker_classes.len(),
            "{}: marker class count",
            fixture.tag
        );
        for (index, (got, wanted)) in report
            .marker_classes
            .iter()
            .zip(want.marker_classes.iter())
            .enumerate()
        {
            let mut check = |field: &str, actual: f64, expected: f64| {
                comparisons += 1;
                if !close(actual, expected) {
                    disagreements.push(format!(
                        "{}[{index}] {field}: implementation {actual:?}, corpus {expected:?}",
                        fixture.tag
                    ));
                }
            };
            check("aspect_ratio", got.aspect_ratio, wanted.aspect_ratio);
            check("bbp_spike", got.bbp_spike, wanted.bbp_spike);
            check("bbp_threshold", got.bbp_threshold, wanted.bbp_threshold);
            check("margin", got.margin, wanted.margin);
            check(
                "sample_pc_overlap_squared",
                got.sample_pc_overlap_squared,
                wanted.sample_pc_overlap_squared,
            );
            check(
                "removed_axis_fraction",
                got.removed_axis_fraction,
                wanted.removed_axis_fraction,
            );
            check(
                "residual_axis_fraction",
                got.residual_axis_fraction,
                wanted.residual_axis_fraction,
            );
            check("matched_weight", got.matched_weight, wanted.matched_weight);
            check("information", got.information, wanted.information);

            for (field, actual, expected) in [
                (
                    "detectable_by_sample_pca",
                    got.detectable_by_sample_pca,
                    wanted.detectable_by_sample_pca,
                ),
                (
                    "included_by_fitted_pcs",
                    got.included_by_fitted_pcs,
                    wanted.included_by_fitted_pcs,
                ),
            ] {
                comparisons += 1;
                if actual != expected {
                    disagreements.push(format!(
                        "{}[{index}] {field}: implementation {actual}, corpus {expected}",
                        fixture.tag
                    ));
                }
            }

            for (field, actual, expected) in [
                (
                    "residual_susceptibility",
                    got.residual_susceptibility,
                    wanted.residual_susceptibility,
                ),
                (
                    "standardized_bias",
                    got.standardized_bias,
                    wanted.standardized_bias,
                ),
                (
                    "critical_confounding",
                    got.critical_confounding,
                    wanted.critical_confounding,
                ),
            ] {
                comparisons += 1;
                if !close_opt(actual, expected) {
                    disagreements.push(format!(
                        "{}[{index}] {field}: implementation {actual:?}, corpus {expected:?}",
                        fixture.tag
                    ));
                }
            }
        }
    }

    assert!(
        comparisons >= 3000,
        "only {comparisons} comparisons ran; the grid is not exercising the report"
    );
    assert!(
        disagreements.is_empty(),
        "{} of {comparisons} comparisons disagree between the corpus and the \
         implementation. Decide which side is right and fix that side; do not \
         re-bless expected.json to make this pass.\n{}",
        disagreements.len(),
        disagreements
            .iter()
            .take(20)
            .cloned()
            .collect::<Vec<_>>()
            .join("\n")
    );
}

/// Every shipped output must be finite on the whole grid, including the designs
/// placed at a relative distance of `1e-15` from the BBP edge.
///
/// The detectability test compares `spike` with `sqrt(aspect)` while the overlap
/// formula divides by `spike^2`, and those two are not equivalent in binary
/// floating point. If they ever come apart, a shipped report carries a negative
/// `removed_axis_fraction` -- a fraction of an ancestry axis removed that is
/// less than none -- and the `critical_signal / coefficient` division loses the
/// `overlap < 1` guarantee that keeps it finite.
#[test]
fn no_shipped_output_is_non_finite_or_out_of_range() {
    let fixtures: Vec<Fixture> = serde_json::from_str(FIXTURES).expect("fixtures.json");
    let mut problems = Vec::new();

    for fixture in &fixtures {
        let Ok(report) = calculate(&fixture.input) else {
            continue;
        };
        for value in [
            report.effective_subgroup_size,
            report.total_frequency_information,
            report.combined_information_index,
        ] {
            if !value.is_finite() {
                problems.push(format!("{}: non-finite summary {value:?}", fixture.tag));
            }
        }
        for class in &report.marker_classes {
            for (field, value) in [
                ("aspect_ratio", class.aspect_ratio),
                ("bbp_spike", class.bbp_spike),
                ("bbp_threshold", class.bbp_threshold),
                ("margin", class.margin),
                ("sample_pc_overlap_squared", class.sample_pc_overlap_squared),
                ("removed_axis_fraction", class.removed_axis_fraction),
                ("residual_axis_fraction", class.residual_axis_fraction),
                ("matched_weight", class.matched_weight),
                ("information", class.information),
            ] {
                if !value.is_finite() {
                    problems.push(format!("{}: non-finite {field} {value:?}", fixture.tag));
                }
            }
            for (field, value) in [
                ("sample_pc_overlap_squared", class.sample_pc_overlap_squared),
                ("removed_axis_fraction", class.removed_axis_fraction),
                ("residual_axis_fraction", class.residual_axis_fraction),
            ] {
                if !(0.0..=1.0).contains(&value) {
                    problems.push(format!(
                        "{}: {field} outside [0, 1]: {value:?}",
                        fixture.tag
                    ));
                }
            }
            for (field, value) in [
                ("residual_susceptibility", class.residual_susceptibility),
                ("standardized_bias", class.standardized_bias),
                ("critical_confounding", class.critical_confounding),
            ] {
                if let Some(value) = value {
                    if !value.is_finite() {
                        problems.push(format!("{}: non-finite {field} {value:?}", fixture.tag));
                    }
                }
            }
        }
    }

    assert!(problems.is_empty(), "{}", problems.join("\n"));
}
