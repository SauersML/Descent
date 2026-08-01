use serde::{Deserialize, Serialize};
use std::fmt;
use std::fs;
use std::path::Path;

#[derive(Debug, Clone, Deserialize)]
pub struct MarkerClassInput {
    pub name: String,
    pub effective_markers: f64,
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
    pub eigenvector_overlap_squared: f64,
    pub residual_axis_fraction: f64,
    pub matched_weight: f64,
    pub information: f64,
    pub residual_susceptibility: Option<f64>,
    pub standardized_bias: Option<f64>,
    pub critical_confounding: Option<f64>,
}

#[derive(Debug, Clone, Serialize)]
pub struct CorrectabilityReport {
    pub sample_size: f64,
    pub subgroup_size: f64,
    pub fitted_pcs: usize,
    pub effective_subgroup_size: f64,
    pub total_frequency_information: f64,
    pub combined_signal_to_threshold_ratio: f64,
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
        require_finite_positive(marker_class.effective_markers, "effective_markers")?;
        require_finite_nonnegative(marker_class.differentiation, "differentiation")?;
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
        .map(|class| class.effective_markers * class.differentiation.powi(2))
        .sum::<f64>();
    let total_matched_weight = input
        .marker_classes
        .iter()
        .map(|class| class.effective_markers * class.differentiation)
        .sum::<f64>();

    let marker_classes = input
        .marker_classes
        .iter()
        .map(|class| {
            let aspect_ratio = input.sample_size / class.effective_markers;
            let bbp_threshold = aspect_ratio.sqrt();
            let bbp_spike = 2.0 * class.differentiation * effective_subgroup_size;
            let detectable_by_sample_pca = bbp_spike > bbp_threshold;
            let included_by_fitted_pcs =
                detectable_by_sample_pca && class.theoretical_pc_rank <= input.fitted_pcs;
            let eigenvector_overlap_squared = if included_by_fitted_pcs {
                (1.0 - aspect_ratio / bbp_spike.powi(2)) / (1.0 + aspect_ratio / bbp_spike)
            } else {
                0.0
            };
            let residual_axis_fraction = 1.0 - eigenvector_overlap_squared;
            let matched_weight =
                class.effective_markers * class.differentiation / total_matched_weight;
            let information = class.effective_markers * class.differentiation.powi(2);

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
                eigenvector_overlap_squared,
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
        sample_size: input.sample_size,
        subgroup_size: input.subgroup_size,
        fitted_pcs: input.fitted_pcs,
        effective_subgroup_size,
        total_frequency_information,
        combined_signal_to_threshold_ratio: 2.0
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
                    effective_markers: 100_000.0,
                    differentiation: 0.0001,
                    theoretical_pc_rank: 1,
                },
                MarkerClassInput {
                    name: "rare".to_owned(),
                    effective_markers: 1_000_000.0,
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
                effective_markers: 100_000.0,
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
}
