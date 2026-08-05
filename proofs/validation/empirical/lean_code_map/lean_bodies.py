"""Transcriptions of the Calibrator.PCCorrectability definitions that describe
`map/correctability.rs`, plus the reference points the corpus itself proves.

WHY A TRANSCRIPTION.  These definitions are `noncomputable` over `ℝ`, so `#eval`
cannot run them; there is no way to execute the Lean side directly.  A
transcription is therefore unavoidable, and an unchecked transcription is worse
than no differential at all -- it silently tests the transcriber's reading
against the implementation.  Two things pin it:

  * REFERENCE_POINTS below.  Each entry names a theorem in the corpus that
    proves a specific VALUE of the definition, including the junk-value theorems
    that pin Lean's `x / 0 = 0` convention.  The Lean build checks those
    theorems; `map_check.py` checks that this file reproduces them.  A
    transcription that drifts from the corpus fails here.
  * The body checksums in `correspondence.json`.  If a Lean body changes at all,
    the correspondence is marked unverified until someone re-reads it.

WHAT A REFERENCE POINT CANNOT DO.  It only pins the definition where it is
evaluated.  The corpus previously evaluated `demographicSpike` at `m = n`, where
the effective subgroup size is zero and the whole body collapses, so every
constant satisfied it; the differential caught a `4 -> 2` mutant that passed all
sixteen reference points.  Reference points are a transcription check, not a
substitute for the numeric differential against the implementation.
"""

import math

# Mathlib totalises division and the square root: `x / 0 = 0` and
# `Real.sqrt x = 0` for `x < 0`.  A transcription using Python semantics would
# raise where Lean returns a (junk) number, and the junk-value reference points
# below are what force this to be modelled rather than assumed away.


def ldiv(a, b):
    return 0.0 if b == 0 else a / b


def lsqrt(x):
    return 0.0 if x < 0 else math.sqrt(x)


# --- Calibrator/PCCorrectability/Threshold.lean ---------------------------

def effectiveSubgroupSize(n, m):
    """`m * (n - m) / n`"""
    return ldiv(m * (n - m), n)


def demographicSpike(n, F, m):
    """`4 * F * effectiveSubgroupSize n m`"""
    return 4 * F * effectiveSubgroupSize(n, m)


def bbpProxyThreshold(n, M):
    """`Real.sqrt (n / M)`"""
    return lsqrt(ldiv(n, M))


def pcCorrectabilityMargin(n, M, F, m):
    """`demographicSpike n F m - bbpProxyThreshold n M`"""
    return demographicSpike(n, F, m) - bbpProxyThreshold(n, M)


# --- Calibrator/PCCorrectability/Overlap.lean -----------------------------

def samplePCOverlapSq(n, M, spike):
    """`if bbpProxyThreshold n M < spike then
          (1 - (n / M) / spike ^ 2) / (1 + (n / M) / spike) else 0`"""
    if not (bbpProxyThreshold(n, M) < spike):
        return 0.0
    c = ldiv(n, M)
    return ldiv(1 - ldiv(c, spike ** 2), 1 + ldiv(c, spike))


def samplePCResidualAxisFraction(n, M, spike):
    """`1 - samplePCOverlapSq n M spike`"""
    return 1 - samplePCOverlapSq(n, M, spike)


def removedAxisFraction(n, M, spike, pcRank, fittedPCs):
    """`if pcRank ≤ fittedPCs then samplePCOverlapSq n M spike else 0`"""
    return samplePCOverlapSq(n, M, spike) if pcRank <= fittedPCs else 0.0


def fittedResidualAxisFraction(n, M, spike, pcRank, fittedPCs):
    """`1 - removedAxisFraction n M spike pcRank fittedPCs`"""
    return 1 - removedAxisFraction(n, M, spike, pcRank, fittedPCs)


# --- Calibrator/PCCorrectability/Frequency.lean ---------------------------

def classInformation(markers, differentiation):
    """`effectiveMarkers i * differentiation i ^ 2`"""
    return markers * differentiation ** 2


def informationMatchedWeight(markers, differentiation):
    """`effectiveMarkers i * differentiation i`"""
    return markers * differentiation


def totalInformation(classes):
    """`∑ i, classInformation i`"""
    return sum(classInformation(c["effective_independent_markers"], c["differentiation"])
               for c in classes)


def combinedInformationIndex(n, m, total_information):
    """`4 * effectiveSubgroupSize sampleSize subgroupSize *
        Real.sqrt (totalInformation / sampleSize)`"""
    return 4 * effectiveSubgroupSize(n, m) * lsqrt(ldiv(total_information, n))


# --- Calibrator/PCCorrectability/Diagnostic.lean --------------------------

def ancestryGradientSusceptibility(markerAxisVariance, ancestryVariance):
    """`markerAxisVariance * ancestryVariance`"""
    return markerAxisVariance * ancestryVariance


def ascertainmentAmplification(phi, lam):
    """`(1 + Φ + Λ) / Real.sqrt (1 + Λ)`"""
    return ldiv(1 + phi + lam, lsqrt(1 + lam))


def pgsStratificationRiskCoefficient(expectedSNPCount, Hres, effectSD, phi, lam):
    """`Real.sqrt expectedSNPCount * Real.sqrt Hres / effectSD
        * ascertainmentAmplification Φ Λ`"""
    return ldiv(lsqrt(expectedSNPCount) * lsqrt(Hres), effectSD) * \
        ascertainmentAmplification(phi, lam)


def standardizedResidualPGSBias(expectedSNPCount, Hres, effectSD, phi, lam, confounding):
    """`pgsStratificationRiskCoefficient ... * confounding`"""
    return pgsStratificationRiskCoefficient(
        expectedSNPCount, Hres, effectSD, phi, lam) * confounding


def criticalConfoundingMagnitude(criticalSignal, expectedSNPCount, Hres, effectSD, phi, lam):
    """`criticalSignal / pgsStratificationRiskCoefficient ...`"""
    return ldiv(criticalSignal, pgsStratificationRiskCoefficient(
        expectedSNPCount, Hres, effectSD, phi, lam))


# --- values the corpus proves ---------------------------------------------
# (theorem, computed, expected).  The theorem name is checked to exist in the
# corpus by map_check.py, so a renamed or deleted theorem stops being usable as
# evidence instead of quietly remaining a comment.

REFERENCE_POINTS = [
    ("Calibrator.effectiveSubgroupSize_zero_n_is_junk",
     lambda: effectiveSubgroupSize(0, 7.0), 0.0),
    ("Calibrator.inv_effectiveSubgroupSize",
     lambda: 1 / effectiveSubgroupSize(10.0, 4.0), 1 / 4.0 + 1 / 6.0),
    ("Calibrator.demographicSpike_at_reference_point",
     lambda: demographicSpike(4, 1, 1), 3.0),
    ("Calibrator.bbpProxyThreshold_zero_dimension_is_junk",
     lambda: bbpProxyThreshold(5.0, 0.0), 0.0),
    ("Calibrator.bbpProxyThreshold_aspect_invariant",
     lambda: bbpProxyThreshold(3 * 800.0, 3 * 4000.0), bbpProxyThreshold(800.0, 4000.0)),
    ("Calibrator.bbpProxyThreshold_sq",
     lambda: bbpProxyThreshold(800.0, 4000.0) ** 2, 800.0 / 4000.0),
    ("Calibrator.pcCorrectabilityMargin_at_reference_point",
     lambda: pcCorrectabilityMargin(4, 1, 1, 1), 1.0),
    ("Calibrator.samplePCOverlapSq_eq_zero_of_subthreshold",
     lambda: samplePCOverlapSq(1000.0, 4000.0, 0.1), 0.0),
    ("Calibrator.samplePCResidualAxisFraction_eq_rational",
     lambda: samplePCResidualAxisFraction(1000.0, 4000.0, 10.0),
     (1000.0 / 4000.0) * 11.0 / (10.0 * (10.0 + 1000.0 / 4000.0))),
    ("Calibrator.fittedResidualAxisFraction_eq_one_of_rank_exceeds_budget",
     lambda: fittedResidualAxisFraction(1000.0, 4000.0, 10.0, 3, 2), 1.0),
    ("Calibrator.fittedResidualAxisFraction_eq_samplePC",
     lambda: fittedResidualAxisFraction(1000.0, 4000.0, 10.0, 2, 2),
     samplePCResidualAxisFraction(1000.0, 4000.0, 10.0)),
    ("Calibrator.combinedInformationIndex_mul_threshold_eq_spike",
     lambda: combinedInformationIndex(1000.0, 500.0, 4000.0 * 0.01 ** 2) *
     bbpProxyThreshold(1000.0, 4000.0),
     demographicSpike(1000.0, 0.01, 500.0)),
    ("Calibrator.ancestryGradientSusceptibility_at_reference_point",
     lambda: ancestryGradientSusceptibility(0.5, 0.5), 0.25),
    ("Calibrator.ascertainmentAmplification_unit_negative_lambda_is_junk",
     lambda: ascertainmentAmplification(2.0, -1.0), 0.0),
    ("Calibrator.pgsStratificationRiskCoefficient_at_zero_effect_scale_is_junk",
     lambda: pgsStratificationRiskCoefficient(10000.0, 1e-5, 0.0, 2.0, 0.0), 0.0),
    ("Calibrator.criticalConfoundingMagnitude_null_effect_sd_is_junk",
     lambda: criticalConfoundingMagnitude(3.85, 10000.0, 1e-5, 0.0, 2.0, 0.0), 0.0),
    ("Calibrator.standardized_bias_at_critical_confounding",
     lambda: standardizedResidualPGSBias(
         10000.0, 1e-5, 0.1, 2.0, 0.0,
         criticalConfoundingMagnitude(3.85, 10000.0, 1e-5, 0.1, 2.0, 0.0)), 3.85),
    ("Calibrator.balanced_superthreshold_iff_information",
     lambda: float(bbpProxyThreshold(1000.0, 4000.0) < 0.01 * 1000.0),
     float(1 < 4000.0 * 0.01 ** 2 * 1000.0)),
    ("Calibrator.pcCorrectabilityMargin_le_balanced",
     lambda: float(pcCorrectabilityMargin(1000.0, 4000.0, 0.01, 100.0)
                   <= pcCorrectabilityMargin(1000.0, 4000.0, 0.01, 500.0)), 1.0),
]


def report(design):
    """The whole `CorrectabilityReport`, computed only from the bodies above.

    Field names are the shipped JSON field names, so `map_check.py` and the Rust
    differential test compare like with like without a translation layer.
    """
    n = design["sample_size"]
    m = design["subgroup_size"]
    fitted = design["fitted_pcs"]
    classes = design["marker_classes"]
    app = design.get("application")

    info_total = totalInformation(classes)
    weight_total = sum(informationMatchedWeight(c["effective_independent_markers"],
                                                c["differentiation"]) for c in classes)

    out = {
        "effective_subgroup_size": effectiveSubgroupSize(n, m),
        "total_frequency_information": info_total,
        "combined_information_index": combinedInformationIndex(n, m, info_total),
        "marker_classes": [],
    }
    for c in classes:
        M = c["effective_independent_markers"]
        F = c["differentiation"]
        rank = c["theoretical_pc_rank"]
        spike = demographicSpike(n, F, m)
        threshold = bbpProxyThreshold(n, M)
        detectable = threshold < spike
        included = detectable and rank <= fitted
        removed = removedAxisFraction(n, M, spike, rank, fitted)
        residual_fraction = fittedResidualAxisFraction(n, M, spike, rank, fitted)
        entry = {
            "aspect_ratio": ldiv(n, M),
            "bbp_spike": spike,
            "bbp_threshold": threshold,
            "margin": pcCorrectabilityMargin(n, M, F, m),
            "detectable_by_sample_pca": detectable,
            "included_by_fitted_pcs": included,
            "sample_pc_overlap_squared": samplePCOverlapSq(n, M, spike),
            "removed_axis_fraction": removed,
            "residual_axis_fraction": residual_fraction,
            "matched_weight": ldiv(informationMatchedWeight(M, F), weight_total),
            "information": classInformation(M, F),
            "residual_susceptibility": None,
            "standardized_bias": None,
            "critical_confounding": None,
        }
        if app is not None:
            residual = ancestryGradientSusceptibility(app["susceptibility"], residual_fraction)
            entry["residual_susceptibility"] = residual
            entry["standardized_bias"] = standardizedResidualPGSBias(
                app["expected_pgs_variants"], residual, app["effect_sd"],
                app["directional_amplification"], app["count_inflation"], app["confounder"])
            entry["critical_confounding"] = criticalConfoundingMagnitude(
                app["critical_signal"], app["expected_pgs_variants"], residual,
                app["effect_sd"], app["directional_amplification"], app["count_inflation"])
        out["marker_classes"].append(entry)
    return out
