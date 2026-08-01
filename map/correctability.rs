use serde::{Deserialize, Serialize};
use std::fmt;
use std::fs;
use std::path::Path;

pub const CORRECTABILITY_FORMULA_CONTRACT: &str =
    "rank_one_hudson_fst_independent_markers_v2";

#[derive(Debug, Clone, Deserialize)]
pub struct MarkerClassInput {
    pub name: String,
    /// Effectively independent marker count for this class, after accounting for
    /// linkage disequilibrium. This is NOT a raw SNP count. Feeding a raw count
    /// is measured to overstate correctability by roughly twentyfold in M: at
    /// Fst = 0.001 the raw count predicts eigenvector overlap 0.87 where the
    /// simulated truth is 0.014. The field is named unambiguously, and the
    /// rename is deliberately breaking, so that existing inputs supplying a raw
    /// count fail to parse rather than silently producing an optimistic answer.
    pub effective_independent_markers: f64,
    pub differentiation: f64,
    pub theoretical_pc_rank: usize,
}

#[derive(Debug, Clone, Deserialize)]
pub struct ApplicationRiskInput {
    pub susceptibility: f64,
    pub expected_pgs_variants: f64,
    pub effect_sd: f64,
    pub directional_amplification: f64,
    pub count_inflation: f64,
    pub confounder: f64,
    pub critical_signal: f64,
}

#[derive(Debug, Clone, Deserialize)]
pub struct CorrectabilityInput {
    pub sample_size: f64,
    pub subgroup_size: f64,
    pub fitted_pcs: usize,
    pub marker_classes: Vec<MarkerClassInput>,
    pub application: Option<ApplicationRiskInput>,
}

#[derive(Debug, Clone, Serialize)]
pub struct MarkerClassReport {
    pub name: String,
    pub aspect_ratio: f64,
    pub bbp_spike: f64,
    pub bbp_threshold: f64,
    pub margin: f64,
    pub detectable_by_sample_pca: bool,
    pub included_by_fitted_pcs: bool,
    pub minimum_pcs_to_include_axis: Option<usize>,
    pub no_pc_count_suffices: bool,
    /// Intrinsic sample/population eigenvector overlap in the rank-one model.
    /// This does not depend on how many PCs the analyst chooses to include.
    pub sample_pc_overlap_squared: f64,
    /// Fraction of the target axis actually removed by the requested PC set.
    /// This is zero when the relevant sample PC exists but is not included.
    pub removed_axis_fraction: f64,
    pub residual_axis_fraction: f64,
    pub matched_weight: f64,
    pub information: f64,
    pub residual_susceptibility: Option<f64>,
    pub standardized_bias: Option<f64>,
    pub critical_confounding: Option<f64>,
}

#[derive(Debug, Clone, Serialize)]
pub struct CorrectabilityReport {
    pub formula_contract: &'static str,
    pub sample_size: f64,
    pub subgroup_size: f64,
    pub fitted_pcs: usize,
    pub effective_subgroup_size: f64,
    pub total_frequency_information: f64,
    /// Optimal independent-class information index. This is not reported as a
    /// combined BBP overlap because the single-spike overlap theorem does not
    /// identify that quantity for heterogeneous marker classes.
    pub combined_information_index: f64,
    pub any_single_class_detectable: bool,
    pub marker_classes: Vec<MarkerClassReport>,
}

#[derive(Debug)]
pub enum CorrectabilityError {
    Io(std::io::Error),
    Json(serde_json::Error),
    InvalidInput(String),
}

impl fmt::Display for CorrectabilityError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Io(error) => write!(formatter, "I/O error: {error}"),
            Self::Json(error) => write!(formatter, "JSON error: {error}"),
            Self::InvalidInput(message) => {
                write!(formatter, "invalid correctability input: {message}")
            }
        }
    }
}

impl std::error::Error for CorrectabilityError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::Io(error) => Some(error),
            Self::Json(error) => Some(error),
            Self::InvalidInput(_) => None,
        }
    }
}

impl From<std::io::Error> for CorrectabilityError {
    fn from(error: std::io::Error) -> Self {
        Self::Io(error)
    }
}

impl From<serde_json::Error> for CorrectabilityError {
    fn from(error: serde_json::Error) -> Self {
        Self::Json(error)
    }
}

fn require_finite_positive(value: f64, name: &str) -> Result<(), CorrectabilityError> {
    if value.is_finite() && value > 0.0 {
        Ok(())
    } else {
        Err(CorrectabilityError::InvalidInput(format!(
            "{name} must be finite and positive"
        )))
    }
}

fn require_finite_nonnegative(value: f64, name: &str) -> Result<(), CorrectabilityError> {
    if value.is_finite() && value >= 0.0 {
        Ok(())
    } else {
        Err(CorrectabilityError::InvalidInput(format!(
            "{name} must be finite and nonnegative"
        )))
    }
}

fn validate(input: &CorrectabilityInput) -> Result<(), CorrectabilityError> {
    require_finite_positive(input.sample_size, "sample_size")?;
    require_finite_positive(input.subgroup_size, "subgroup_size")?;
    if input.subgroup_size >= input.sample_size {
        return Err(CorrectabilityError::InvalidInput(
            "subgroup_size must be smaller than sample_size".to_owned(),
        ));
    }
    if input.marker_classes.is_empty() {
        return Err(CorrectabilityError::InvalidInput(
            "marker_classes must contain at least one class".to_owned(),
        ));
    }

    let mut has_differentiated_class = false;
    for marker_class in &input.marker_classes {
        if marker_class.name.trim().is_empty() {
            return Err(CorrectabilityError::InvalidInput(
                "marker class names must not be empty".to_owned(),
            ));
        }
        require_finite_positive(marker_class.effective_independent_markers, "effective_independent_markers")?;
        require_finite_nonnegative(marker_class.differentiation, "differentiation")?;
        if marker_class.differentiation > 1.0 {
            return Err(CorrectabilityError::InvalidInput(
                "differentiation must be on the Hudson F_ST scale in [0, 1]".to_owned(),
            ));
        }
        if marker_class.theoretical_pc_rank == 0 {
            return Err(CorrectabilityError::InvalidInput(
                "theoretical_pc_rank is one-based and must be positive".to_owned(),
            ));
        }
        has_differentiated_class |= marker_class.differentiation > 0.0;
    }
    if !has_differentiated_class {
        return Err(CorrectabilityError::InvalidInput(
            "at least one marker class must have positive differentiation".to_owned(),
        ));
    }

    if let Some(application) = &input.application {
        require_finite_positive(application.susceptibility, "application.susceptibility")?;
        require_finite_positive(
            application.expected_pgs_variants,
            "application.expected_pgs_variants",
        )?;
        require_finite_positive(application.effect_sd, "application.effect_sd")?;
        require_finite_nonnegative(
            application.directional_amplification,
            "application.directional_amplification",
        )?;
        require_finite_nonnegative(application.count_inflation, "application.count_inflation")?;
        if !application.confounder.is_finite() {
            return Err(CorrectabilityError::InvalidInput(
                "application.confounder must be finite".to_owned(),
            ));
        }
        require_finite_positive(application.critical_signal, "application.critical_signal")?;
    }

    Ok(())
}

pub fn calculate(input: &CorrectabilityInput) -> Result<CorrectabilityReport, CorrectabilityError> {
    validate(input)?;

    let effective_subgroup_size =
        input.subgroup_size * (input.sample_size - input.subgroup_size) / input.sample_size;
    let total_frequency_information = input
        .marker_classes
        .iter()
        .map(|class| class.effective_independent_markers * class.differentiation.powi(2))
        .sum::<f64>();
    let total_matched_weight = input
        .marker_classes
        .iter()
        .map(|class| class.effective_independent_markers * class.differentiation)
        .sum::<f64>();

    let marker_classes = input
        .marker_classes
        .iter()
        .map(|class| {
            let aspect_ratio = input.sample_size / class.effective_independent_markers;
            let bbp_threshold = aspect_ratio.sqrt();
            let bbp_spike = 4.0 * class.differentiation * effective_subgroup_size;
            let detectable_by_sample_pca = bbp_spike > bbp_threshold;
            let included_by_fitted_pcs =
                detectable_by_sample_pca && class.theoretical_pc_rank <= input.fitted_pcs;
            let sample_pc_overlap_squared = if detectable_by_sample_pca {
                (1.0 - aspect_ratio / bbp_spike.powi(2)) / (1.0 + aspect_ratio / bbp_spike)
            } else {
                0.0
            };
            let removed_axis_fraction = if included_by_fitted_pcs {
                sample_pc_overlap_squared
            } else {
                0.0
            };
            let residual_axis_fraction = 1.0 - removed_axis_fraction;
            let matched_weight =
                class.effective_independent_markers * class.differentiation / total_matched_weight;
            let information = class.effective_independent_markers * class.differentiation.powi(2);

            let (residual_susceptibility, standardized_bias, critical_confounding) = match &input
                .application
            {
                Some(application) => {
                    let residual = application.susceptibility * residual_axis_fraction;
                    let amplification =
                        (1.0 + application.directional_amplification + application.count_inflation)
                            / (1.0 + application.count_inflation).sqrt();
                    let coefficient = application.expected_pgs_variants.sqrt() * residual.sqrt()
                        / application.effect_sd
                        * amplification;
                    (
                        Some(residual),
                        Some(coefficient * application.confounder),
                        Some(application.critical_signal / coefficient),
                    )
                }
                None => (None, None, None),
            };

            MarkerClassReport {
                name: class.name.clone(),
                aspect_ratio,
                bbp_spike,
                bbp_threshold,
                margin: bbp_spike - bbp_threshold,
                detectable_by_sample_pca,
                included_by_fitted_pcs,
                minimum_pcs_to_include_axis: detectable_by_sample_pca
                    .then_some(class.theoretical_pc_rank),
                no_pc_count_suffices: !detectable_by_sample_pca,
                sample_pc_overlap_squared,
                removed_axis_fraction,
                residual_axis_fraction,
                matched_weight,
                information,
                residual_susceptibility,
                standardized_bias,
                critical_confounding,
            }
        })
        .collect::<Vec<_>>();

    Ok(CorrectabilityReport {
        formula_contract: CORRECTABILITY_FORMULA_CONTRACT,
        sample_size: input.sample_size,
        subgroup_size: input.subgroup_size,
        fitted_pcs: input.fitted_pcs,
        effective_subgroup_size,
        total_frequency_information,
        combined_information_index: 4.0
            * effective_subgroup_size
            * (total_frequency_information / input.sample_size).sqrt(),
        any_single_class_detectable: marker_classes
            .iter()
            .any(|class| class.detectable_by_sample_pca),
        marker_classes,
    })
}

pub fn calculate_json_file(path: &Path) -> Result<String, CorrectabilityError> {
    let input: CorrectabilityInput = serde_json::from_slice(&fs::read(path)?)?;
    let report = calculate(&input)?;
    Ok(serde_json::to_string_pretty(&report)?)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn distinguishes_subthreshold_common_from_detectable_rare_structure() {
        let input = CorrectabilityInput {
            sample_size: 400_000.0,
            subgroup_size: 1_000.0,
            fitted_pcs: 40,
            marker_classes: vec![
                MarkerClassInput {
                    name: "common".to_owned(),
                    effective_independent_markers: 100_000.0,
                    differentiation: 0.0001,
                    theoretical_pc_rank: 1,
                },
                MarkerClassInput {
                    name: "rare".to_owned(),
                    effective_independent_markers: 1_000_000.0,
                    differentiation: 0.001,
                    theoretical_pc_rank: 1,
                },
            ],
            application: None,
        };

        let report = calculate(&input).expect("valid design");
        assert!(!report.marker_classes[0].detectable_by_sample_pca);
        assert!(report.marker_classes[1].detectable_by_sample_pca);
        assert!(report.marker_classes[1].matched_weight > report.marker_classes[0].matched_weight);
    }

    #[test]
    fn residual_susceptibility_drives_critical_confounding() {
        let input = CorrectabilityInput {
            sample_size: 100_000.0,
            subgroup_size: 1_000.0,
            fitted_pcs: 40,
            marker_classes: vec![MarkerClassInput {
                name: "common".to_owned(),
                effective_independent_markers: 100_000.0,
                differentiation: 0.0001,
                theoretical_pc_rank: 1,
            }],
            application: Some(ApplicationRiskInput {
                susceptibility: 1e-5,
                expected_pgs_variants: 10_000.0,
                effect_sd: 0.1,
                directional_amplification: 2.0,
                count_inflation: 0.0,
                confounder: 0.5,
                critical_signal: 3.85,
            }),
        };

        let report = calculate(&input).expect("valid design");
        let class = &report.marker_classes[0];
        assert_eq!(class.residual_susceptibility, Some(1e-5));
        assert!(class.standardized_bias.expect("application output") > 0.0);
        assert!(class.critical_confounding.expect("application output") > 0.0);
    }

    #[test]
    fn balanced_contrast_and_overlap_match_the_rank_one_formulas() {
        let input = CorrectabilityInput {
            sample_size: 1_000.0,
            subgroup_size: 500.0,
            fitted_pcs: 2,
            marker_classes: vec![MarkerClassInput {
                name: "channel".to_owned(),
                effective_independent_markers: 4_000.0,
                differentiation: 0.01,
                theoretical_pc_rank: 3,
            }],
            application: None,
        };

        let report = calculate(&input).expect("valid design");
        let class = &report.marker_classes[0];
        let expected_spike: f64 = 4.0 * 0.01 * 250.0;
        let expected_aspect_ratio: f64 = 1_000.0 / 4_000.0;

        assert_eq!(report.effective_subgroup_size, 250.0);
        assert_eq!(class.bbp_spike, expected_spike);
        assert_eq!(class.bbp_threshold, expected_aspect_ratio.sqrt());
        assert!(class.detectable_by_sample_pca);
        assert!(!class.included_by_fitted_pcs);
        assert_eq!(class.minimum_pcs_to_include_axis, Some(3));
        assert!(!class.no_pc_count_suffices);
        assert!(class.sample_pc_overlap_squared > 0.0);
        assert_eq!(class.removed_axis_fraction, 0.0);
        assert_eq!(class.residual_axis_fraction, 1.0);

        let mut included_input = input;
        included_input.fitted_pcs = 3;
        let included = calculate(&included_input).expect("valid design");
        let included_class = &included.marker_classes[0];
        let expected_overlap = (1.0 - expected_aspect_ratio / expected_spike.powi(2))
            / (1.0 + expected_aspect_ratio / expected_spike);

        assert!((included_class.sample_pc_overlap_squared - expected_overlap).abs() < 1e-15);
        assert!((included_class.removed_axis_fraction - expected_overlap).abs() < 1e-15);
        assert!((included_class.residual_axis_fraction - (1.0 - expected_overlap)).abs() < 1e-15);
    }

    #[test]
    fn rejects_differentiation_outside_the_hudson_fst_scale() {
        let input = CorrectabilityInput {
            sample_size: 1_000.0,
            subgroup_size: 100.0,
            fitted_pcs: 1,
            marker_classes: vec![MarkerClassInput {
                name: "invalid".to_owned(),
                effective_independent_markers: 10_000.0,
                differentiation: 1.01,
                theoretical_pc_rank: 1,
            }],
            application: None,
        };

        assert!(matches!(calculate(&input), Err(CorrectabilityError::InvalidInput(_))));
    }
}
