"""THE RELATION TABLE: which metamorphic relations each definition must satisfy.

A metamorphic relation is a transformation of the INPUT whose effect on the
OUTPUT is known exactly.  It needs no oracle, so unlike a simulation verdict it
admits no convention argument: if `hudsonFst` changed when you relabel which
allele is called reference, that would be a defect under every convention, and
there is nothing to negotiate.  That is what makes this table gateable.

WHAT IS DECLARED HERE

  SWEPT_MODULES   Lean modules I have gone through definition by definition.
                  Every extractable scalar `ℝ → ℝ` definition in a swept module
                  MUST appear in RELATIONS or in NO_RELATIONS.  A new definition
                  landing in a swept module with no declaration FAILS the gate.
                  That is the point: the table is a commitment about a region of
                  the corpus, not a bag of examples.

  RELATIONS       fqn -> [relation, ...].  Each must hold on the fixed grid.

  NO_RELATIONS    fqn -> reason.  A definition in a swept module for which none
                  of the relation kinds applies.  Writing the reason down is the
                  work; it is what stops "no relations" from meaning "nobody
                  looked".

  EXPECTED_VIOLATIONS
                  (fqn, relation-id) -> reason.  A relation the definition
                  legitimately does NOT satisfy, pinned so that a silent change
                  of behaviour is caught in BOTH directions: if a pinned
                  violation starts holding, that is a regression too.  Same
                  discipline as the differential battery's expected
                  disagreements.

  NOT_EXTRACTABLE fqn -> reason.  In a swept module but `extract/api.py` cannot
                  build a callable, so no relation can be evaluated.  Recorded
                  rather than skipped, because a silently unevaluated definition
                  is the failure mode this whole directory exists to prevent.

HOW TO CHOOSE WHAT TO DECLARE NEXT, which matters more than it sounds.

Sweeping modules alphabetically and targeting weak verdicts are not two orders of
the same work.  Measured over six batches here: four alphabetical module sweeps
found ZERO gaps in this table's vocabulary; two batches targeted at definitions
whose verdict was FALSIFIED or absent found TWO.  The reason is structural rather
than lucky --

    a sweep finds definitions that fit the existing kinds, because "declarable"
    is defined by the kinds.  An instrument swept over the cases it can already
    express measures its own vocabulary, not the corpus.

So order by the weakness of the verdict: bodies still marked FALSIFIED first
(a relation there either survives a correction, which is evidence the correction
kept the right structure, or fails it, which is evidence it did not), then bodies
carrying no verdict at all, which nothing in the corpus can contradict today.

THE TWO KNOWN VOCABULARY GAPS, which are a specification for anyone extending
the kinds rather than a list of shortfalls:

  * REFLECTION ABOUT AN ANCHOR.  `|slope - 1|` is even about `slope = 1`; the
    negation kinds here reflect about zero.  A real family: calibration slope,
    `Ns` from an observed correlation, and most "distance from ideal" quantities.
    See `calibrationSlopeDeviation`.
  * SCALING OF THE LOGARITHM OF AN ARGUMENT.  `maxSafeEpistaticOrder` satisfies
    `f(N^c, q) = c · f(N, q)`; every kind here transforms arguments
    multiplicatively or by complement.

Neither is approximated with a nearby kind.  Declaring a plain `scales` for
either would assert something false, which is worse than declaring nothing.

UNSWEPT MODULES ARE VISIBLE DEBT, NOT ZERO.  `run.py --coverage` prints how many
extractable scalar definitions live outside SWEPT_MODULES.  Extending the sweep
is additive and never weakens an existing gate.  Do not add a module to
SWEPT_MODULES without declaring every definition in it.
"""

from fractions import Fraction as Q

# ---------------------------------------------------------------------------
# Vocabulary: which argument names denote what, so a transformation knows what
# to do to them.  Deliberately explicit per definition rather than inferred from
# the name -- `q` is an allele frequency in one module and a forecast
# probability in another, and guessing is how a checker invents its own findings.
# ---------------------------------------------------------------------------

# --- relation constructors -------------------------------------------------


def invariant_under_allele_swap(freq_args, effect_args=()):
    """f(1-p ..., -β ...) == f(p ..., β ...).

    Which allele a panel calls REFERENCE is a property of the assembly, not of
    the biology.  Swapping it sends every allele frequency to its complement AND
    every effect direction to its negation, simultaneously -- never one without
    the other.  Allele-frequency-symmetric quantities must not move.
    """
    return {"kind": "allele_swap", "rel": "invariant",
            "freq": tuple(freq_args), "effect": tuple(effect_args),
            "id": f"allele_swap/invariant/{'+'.join(freq_args)}"}


def negated_under_allele_swap(freq_args, effect_args=()):
    """f(1-p ..., -β ...) == -f(p ..., β ...) -- effect-DIRECTION quantities."""
    return {"kind": "allele_swap", "rel": "negated",
            "freq": tuple(freq_args), "effect": tuple(effect_args),
            "id": f"allele_swap/negated/{'+'.join(freq_args)}"}


def complement_under_allele_swap(freq_args):
    """f(1-p ...) == 1 - f(p ...) -- a frequency-valued output."""
    return {"kind": "allele_swap", "rel": "complement",
            "freq": tuple(freq_args), "effect": (),
            "id": f"allele_swap/complement/{'+'.join(freq_args)}"}


def scales(arg, exponent):
    """f(..., c*arg, ...) == c**exponent * f(..., arg, ...).

    Pins the EXPONENT, which monotonicity does not: a body linear in an argument
    and a body quadratic in it are both monotone in it.
    """
    return {"kind": "scale", "arg": arg, "exp": Q(exponent),
            "id": f"scale/{arg}^{Q(exponent)}"}


def jointly_scales(args, exponent):
    """Scaling ALL of `args` by the same c multiplies the output by c**exponent.

    With exponent 0 this is a rescaling invariance: `coalFst t Ne` measures time
    in units of Nₑ, so doubling both must not move it.  This is the coalescent
    rescaling relation in the form that survives this corpus's conventions.
    """
    return {"kind": "joint_scale", "args": tuple(args), "exp": Q(exponent),
            "id": f"joint_scale/{'*'.join(args)}^{Q(exponent)}"}


def invariant_under_reciprocal_scaling(up, down):
    """Scaling `up` by c and `down` by 1/c leaves the output alone.

    This is "hold 4·Nₑ·m fixed": the compound parameter is what the process
    depends on, and a body that depended on Nₑ and m separately would be
    modelling something else.  The single most informative relation in the
    migration/mutation family.
    """
    return {"kind": "reciprocal_scale", "up": tuple(up), "down": tuple(down),
            "id": f"reciprocal_scale/{'*'.join(up)}|{'*'.join(down)}"}


def symmetric_in(a, b):
    """f(..., a, ..., b, ...) == f(..., b, ..., a, ...) -- argument exchange."""
    return {"kind": "swap", "a": a, "b": b, "id": f"swap/{a}<->{b}"}


def odd_under_negation(args):
    """f(-args) == -f(args)."""
    return {"kind": "negate", "args": tuple(args), "rel": "negated",
            "id": f"negate/odd/{'+'.join(args)}"}


def even_under_negation(args):
    """f(-args) == f(args).

    Distinct from every scaling relation: a density, a squared deviation or an
    absolute difference is even in its argument, and a body carrying a stray odd
    term satisfies every scaling relation it should while failing this one.
    """
    return {"kind": "negate", "args": tuple(args), "rel": "invariant",
            "id": f"negate/even/{'+'.join(args)}"}


# ---------------------------------------------------------------------------
# SWEPT MODULES
# ---------------------------------------------------------------------------

SWEPT_MODULES = (
    "Descent/Foundations/Conventions.lean",
    "Descent/PopGen/PopulationGeneticsFoundations.lean",
    "Descent/Portability/AncestrySpecificPower.lean",
    "Descent/PopGen/GeneticArchitectureDiscovery.lean",
    "Descent/Blindness/BlindnessRegistry.lean",
    "Descent/Portability/TransferLearningPGS.lean",
    "Descent/Spectral/Permeability.lean",
    "Descent/Portability/PortabilityDrift.lean",
    "Descent/PopGen/DGP.lean",
    "Descent/Portability/MetricSpecificPortability.lean",
    "Descent/Portability/RareVariantPortability.lean",
    "Descent/Portability/PGSCalibrationTheory.lean",
    "Descent/PopGen/SelectionArchitecture.lean",
    "Descent/PopGen/HaplotypeTheory.lean",
)

# ---------------------------------------------------------------------------
# THE TABLE
# ---------------------------------------------------------------------------

RELATIONS = {
    # --- Conventions ------------------------------------------------------
    # Reachable only since the nullary-def extraction fix (0f4de2f7). A bare
    # mention of `ploidy` translated to the function's NAME rather than a call,
    # so one factor made the corpus's headline F_ST convention unexecutable and
    # therefore invisible to every empirical checker: differential, identity and
    # metamorphic alike. No amount of adding checks closes a hole of that shape.
    "Descent.neiGst": [
        invariant_under_allele_swap(["p₁", "p₂"]),
        symmetric_in("p₁", "p₂"),
    ],
    "Descent.hweGenotypeVariance": [
        invariant_under_allele_swap(["p"]),
    ],
    "Descent.coalescentTimeScale": [
        scales("Ne", 1),
    ],
    "Descent.neiContrastSpike": [
        invariant_under_allele_swap(["p₁", "p₂"]),
        symmetric_in("p₁", "p₂"),
    ],
    "Descent.meanAlleleFreq": [
        complement_under_allele_swap(["p₁", "p₂"]),
        symmetric_in("p₁", "p₂"),
        jointly_scales(["p₁", "p₂"], 1),
    ],
    "Descent.hudsonFst": [
        invariant_under_allele_swap(["p₁", "p₂"]),
        symmetric_in("p₁", "p₂"),
    ],
    "Descent.betweenSubgroupVariance": [
        invariant_under_allele_swap(["p₁", "p₂"]),
        symmetric_in("p₁", "p₂"),
        jointly_scales(["p₁", "p₂"], 2),
    ],
    "Descent.hudsonBbpSpike": [
        invariant_under_allele_swap(["p₁", "p₂"]),
        symmetric_in("p₁", "p₂"),
    ],
    "Descent.convexMix": [
        jointly_scales(["x", "y"], 1),
        odd_under_negation(["x", "y"]),
    ],
    "Descent.oneMinusRatio": [
        jointly_scales(["a", "b"], 0),
    ],
    "Descent.retainedFraction": [
        scales("total", 1),
    ],

    # --- PopulationGeneticsFoundations ------------------------------------
    "Descent.neiFst": [
        # A ratio of heterozygosities: the unit of heterozygosity cancels.
        jointly_scales(["H_T", "H_S"], 0),
    ],
    "Descent.neiGstFromFrequencies": [
        invariant_under_allele_swap(["p₁", "p₂"]),
        symmetric_in("p₁", "p₂"),
    ],
    "Descent.coalFst": [
        # Time measured in units of Nₑ: the coalescent rescaling relation.
        jointly_scales(["t", "Ne"], 0),
    ],
    "Descent.fstFromHetRatio": [
        jointly_scales(["H", "H₀"], 0),
    ],
    "Descent.wrightFIT": [
        symmetric_in("f_IS", "f_ST"),
    ],
    "Descent.scaledIdentityStep": [
        invariant_under_reciprocal_scaling(["scaledRate"], ["F"]),
    ],
    "Descent.expectedNewMutations": [
        scales("θ", 1),
        scales("t", 1),
        jointly_scales(["θ", "t"], 2),
    ],
    "Descent.islandFstFiniteDemes": [
        # The process depends on 4·Nₑ·m, not on Nₑ and m separately.
        invariant_under_reciprocal_scaling(["Ne"], ["m"]),
    ],
    "Descent.fstMigrationMutationEquilibriumManyDemes": [
        invariant_under_reciprocal_scaling(["Ne"], ["m", "μ"]),
    ],
    "Descent.fstIslandEquilibriumFiniteDemes": [
        invariant_under_reciprocal_scaling(["Ne"], ["m", "μ"]),
    ],
    "Descent.fstMutationDriftTransient": [
        # The plateau is set by θ alone; the approach is in units of Nₑ.
        jointly_scales(["t", "Ne"], 0),
    ],
    "Descent.steppingStoneCharacteristicLength": [
        scales("m", Q(1, 2)),
        scales("σ_sq", Q(1, 2)),
        scales("μ", Q(-1, 2)),
    ],

    # --- AncestrySpecificPower --------------------------------------------
    "Descent.genotypeVarianceHWE": [
        invariant_under_allele_swap(["p"]),
    ],
    "Descent.hweHeterozygosity": [
        invariant_under_allele_swap(["p"]),
    ],
    "Descent.ncp": [
        scales("β", 2),
        scales("n_eff", 1),
    ],
    "Descent.portableFraction": [
        jointly_scales(["r2_causal", "r2_total"], 0),
    ],
    "Descent.proportionalAllocation": [
        jointly_scales(["pop_size", "total_pop"], 0),
        scales("total_n", 1),
    ],

    # --- GeneticArchitectureDiscovery -------------------------------------
    "Descent.discoveryNCP": [
        # Mirrors the Lean theorems discoveryNCP_allele_swap / _scale_effect /
        # _scale_ld / _scale_n.  Proved there, executed here: the Lean statement
        # constrains the body, this constrains the transcription of the body
        # that every other empirical checker consumes.
        invariant_under_allele_swap(["maf_causal"], effect_args=["β"]),
        scales("β", 2),
        scales("ld", 2),
        scales("n", 1),
    ],
    "Descent.multiTraitDiscoveryNCP": [
        invariant_under_allele_swap(["maf"], effect_args=["β"]),
        scales("β", 2),
        scales("ld", 2),
    ],
    "Descent.multiTraitEffectiveSampleSize": [
        # `jointly_scales(["n₁", "n₂"], 1)` WAS here and is now FALSE, which is
        # the point rather than an oversight. It held of the old body
        # `n₁ + rg²·n₂`, which has no absolute scale: double both sample sizes
        # and the effective one doubles. The corrected body
        # `n₁ + rg²/((1-rg²)·priorVariance + 1/n₂)` carries the effect prior
        # variance, and a variance IS an absolute scale -- the borrowed
        # precision saturates at `rg²/((1-rg²)·priorVariance)` however large the
        # other study grows, because past that point the limit is the other
        # trait's effect scatter and not its sampling error. Degree-1
        # homogeneity returns only if `priorVariance` is scaled by `1/c` at the
        # same time, and no relation in this file expresses a mixed-direction
        # joint scaling. Asserting the old relation against the new body would
        # fail this gate for the correct body, which is worse than not
        # asserting it.
        #
        # Deliberately asymmetric: only the SECOND trait is discounted by rg².
        symmetric_in("n₁", "n₂"),
    ],
    "Descent.expectedLinearEffectEstimate": [
        odd_under_negation(["β_true", "meanEstimationError"]),
        jointly_scales(["β_true", "meanEstimationError"], 1),
    ],
    "Descent.olsEffectEstimationVariance": [
        scales("σ2", 1),
        scales("varX", -1),
        scales("n", -1),
    ],
    "Descent.perCausalLocusSignal": [
        jointly_scales(["h2", "k"], 0),
    ],
    "Descent.geneticCorrelation": [
        scales("cov_g", 1),
        # cov / sqrt(vg₁·vg₂): scaling BOTH variances by c divides by c, not by
        # sqrt(c) -- the square root is taken of the product, so the two factors
        # of c combine before it. Declared as -1/2 on first writing and caught
        # by this gate, which is the cheapest evidence that it evaluates.
        jointly_scales(["vg₁", "vg₂"], -1),
        symmetric_in("vg₁", "vg₂"),
    ],

    # --- BlindnessRegistry -------------------------------------------------
    "Descent.pairwiseCoalescentSurvival": [
        # Survival depends on the compound lam·t, so time units cancel.
        invariant_under_reciprocal_scaling(["lam"], ["t"]),
    ],

    # --- TransferLearningPGS ----------------------------------------------
    "Descent.pgsR2": [
        scales("cov_pgs_y", 2),
        scales("var_pgs", -1),
        scales("var_y", -1),
    ],
    "Descent.benDavidUpperBound": [
        jointly_scales(["err_source", "divergence", "lambda_star"], 1),
        symmetric_in("err_source", "divergence"),
    ],
    "Descent.importanceWeightESS": [
        scales("sum_w", 2),
        scales("sum_w_sq", -1),
    ],
    "Descent.pcaSignalLossPenalty": [
        scales("lossWeight", 1),
        jointly_scales(["signalBaseline", "signalRetained"], 1),
    ],
    "Descent.pcaBiasReduction": [
        jointly_scales(["ancestryBiasWith", "ancestryBiasWithout"], 1),
        odd_under_negation(["ancestryBiasWith", "ancestryBiasWithout"]),
    ],
    "Descent.pcaNetTargetError": [
        jointly_scales(["ancestryBias", "signalBaseline", "signalRetained"], 1),
    ],
    "Descent.infoBottleneckObjective": [
        jointly_scales(["I_phi_Y", "I_phi_A"], 1),
        odd_under_negation(["I_phi_Y", "I_phi_A"]),
    ],
    "Descent.pinskerAncestryDivergenceCap": [
        scales("I_phi_A", Q(1, 2)),
    ],
    "Descent.fineTunedTargetR2": [
        jointly_scales(["r2_source", "divergence_penalty", "adaptation_gain"], 1),
        odd_under_negation(["r2_source", "divergence_penalty",
                            "adaptation_gain"]),
    ],
    "Descent.scratchTargetR2": [
        jointly_scales(["oracle_target_r2", "estimation_penalty"], 1),
        odd_under_negation(["oracle_target_r2", "estimation_penalty"]),
    ],
    "Descent.deployedTransferTargetR2": [
        jointly_scales(["transported_r2", "adaptation_gain",
                        "estimation_penalty"], 1),
    ],
    "Descent.oracleTransportAdaptationGain": [
        jointly_scales(["transported_r2", "oracle_target_r2"], 1),
        odd_under_negation(["transported_r2", "oracle_target_r2"]),
    ],
    "Descent.transportPenalty": [
        jointly_scales(["source_r2", "transported_r2"], 1),
        odd_under_negation(["source_r2", "transported_r2"]),
    ],
    "Descent.sampleLimitedScratchTargetR2": [
        # noiseVar and nTarget enter only through their ratio.
        jointly_scales(["noiseVar", "nTarget"], 0),
    ],
    "Descent.sourceShrinkageMSE": [
        jointly_scales(["noiseVar", "nTarget"], 0),
    ],
    "Descent.optimalSourceShrinkageWeight": [
        # A weight, so it is scale-free in the risks; and the sample size enters
        # only through noiseVar/nTarget.
        jointly_scales(["gapSq", "noiseVar"], 0),
        jointly_scales(["noiseVar", "nTarget"], 0),
    ],
    "Descent.optimalFineTuningMSE": [
        jointly_scales(["gapSq", "noiseVar"], 1),
        jointly_scales(["noiseVar", "nTarget"], 0),
    ],
    "Descent.requiredTargetSamplesForOptimalFineTuningMSE": [
        scales("noiseVar", 1),
        jointly_scales(["gapSq", "tau"], -1),
    ],
    "Descent.privateArchitectureTransferCeiling": [
        scales("h2_target", 1),
    ],
    "Descent.scratchVsFineTuningCriticalSampleSize": [
        scales("noiseVar", 1),
    ],

    # --- Permeability ------------------------------------------------------
    "Descent.scalarPermeability": [
        # A squared LOG-derivative, so the covariance's unit cancels.
        jointly_scales(["covariance", "covarianceDerivative"], 0),
        scales("covarianceDerivative", 2),
        scales("covariance", -2),
    ],
    "Descent.momentPermeability": [
        scales("response", 2),
        scales("noiseVariance", -1),
    ],
    "Descent.covarianceMomentPermeability": [
        scales("covarianceDerivative", 2),
    ],
    "Descent.replicatesForEqualPermeability": [
        scales("sourceReplicates", 1),
        jointly_scales(["sourcePermeability", "targetPermeability"], 0),
    ],
    "Descent.twoChannelMomentNoiseDet": [
        jointly_scales(["firstNoise", "secondNoise", "sharedNoise"], 2),
    ],
    "Descent.twoChannelConditionalMomentNoise": [
        jointly_scales(["firstNoise", "secondNoise", "sharedNoise"], 1),
    ],
    "Descent.twoChannelConditionalMomentResponse": [
        jointly_scales(["firstResponse", "secondResponse"], 1),
        jointly_scales(["firstNoise", "sharedNoise"], 0),
        odd_under_negation(["firstResponse", "secondResponse"]),
    ],
    "Descent.twoChannelMomentInnovationInformation": [
        jointly_scales(["firstResponse", "secondResponse"], 2),
    ],
    "Descent.informationPerUnitCost": [
        jointly_scales(["information", "cost"], 0),
        scales("information", 1),
        scales("cost", -1),
    ],
    "Descent.informationAtBudget": [
        scales("budget", 1),
        jointly_scales(["information", "cost"], 0),
    ],
    "Descent.totalGaussianInformation": [
        scales("m", 1),
        jointly_scales(["covariance", "covarianceDerivative"], 0),
    ],
    "Descent.totalCovarianceMomentInformation": [
        scales("m", 1),
        scales("covarianceDerivative", 2),
    ],
    "Descent.totalBinaryOrientationArrowPermeability": [
        scales("m", 1),
    ],
    "Descent.covarianceTangentEstimatorVarianceFromMoments": [
        scales("m", -1),
        scales("covarianceDerivative", -2),
    ],
    "Descent.gaussianCovarianceTangentEstimatorVariance": [
        scales("m", -1),
    ],
    "Descent.gaussianCovarianceHalfSquaredRisk": [
        scales("m", -1),
    ],
    "Descent.quadraticChannel": [
        scales("θ", 2),
    ],
    "Descent.covarianceScoreInformationFromMoments": [
        scales("covarianceDerivative", 2),
        scales("covariance", -4),
    ],

    # --- PortabilityDrift --------------------------------------------------
    # The corpus's largest scalar module. Its recurring structure is that
    # quantities depend on COMPOUND parameters -- 4·Nₑ·m, t/Nₑ, a variance ratio
    # -- and the relations below are what pin the compound rather than the
    # factors, which is the one thing a per-argument monotonicity result cannot
    # do.
    "Descent.coalescentTau": [
        jointly_scales(["t", "Ne"], 0),
        scales("t", 1),
        scales("Ne", -1),
    ],
    "Descent.fstFromGenerations": [
        jointly_scales(["t", "Ne"], 0),
    ],
    "Descent.pairwiseFstFromBranches": [
        symmetric_in("fstS", "fstT"),
    ],
    "Descent.pairwiseFstFromBranchTaus": [
        symmetric_in("tauS", "tauT"),
    ],
    "Descent.hudsonFstFromCoalescenceTimes": [
        # A ratio of coalescence times: the unit of time cancels.
        jointly_scales(["ETss", "ETst"], 0),
    ],
    "Descent.hetMutationFloor": [
        # Depends on 4·Nₑ·μ alone.
        invariant_under_reciprocal_scaling(["Ne"], ["mu"]),
    ],
    "Descent.pgsVarianceFromHet": [
        symmetric_in("β_sq_sum", "het"),
        jointly_scales(["β_sq_sum", "het"], 2),
        scales("β_sq_sum", 1),
    ],
    "Descent.targetHetFromFst": [
        scales("het_source", 1),
    ],
    "Descent.presentDayPGSVariance": [
        scales("V_A", 1),
    ],
    "Descent.Var_Delta_Mu": [
        scales("V_A", 1),
        scales("fst", 1),
        jointly_scales(["V_A", "fst"], 2),
    ],
    "Descent.Expected_Abs_Shift": [
        # A standard deviation, so half a power of the variance.
        scales("V_A", Q(1, 2)),
        symmetric_in("fstS", "fstT"),
    ],
    "Descent.presentDaySignalToNoise": [
        jointly_scales(["V_A", "V_E"], 0),
        scales("V_A", 1),
        scales("V_E", -1),
    ],
    "Descent.presentDayR2": [
        jointly_scales(["V_A", "V_E"], 0),
    ],
    "Descent.presentDayEqualVarianceGaussianAUC": [
        jointly_scales(["V_A", "V_E"], 0),
    ],
    "Descent.realWorldPGSVariance": [
        scales("V_A", 1),
        scales("rhoSq", 1),
        jointly_scales(["V_A", "rhoSq"], 2),
    ],
    "Descent.ldCorrelationDecay": [
        # The decay reads the product lambda·distance, so those two trade off
        # exactly. This still holds after the body's correction.
        invariant_under_reciprocal_scaling(["distance"], ["lambda"]),
        # And this one is PINNED AS A VIOLATION rather than deleted -- see
        # EXPECTED_VIOLATIONS. It held for the superseded body and must not hold
        # for the corrected one.
        invariant_under_reciprocal_scaling(["fstGap"], ["lambda"]),
    ],
    "Descent.alleleFreqMismatchPenalty": [
        # The body was corrected while this table was live -- from the refuted
        # `exp(-|Δp|)` to the genotype-variance ratio `2p_t(1-p_t)/2p_s(1-p_s)`
        # -- and this gate is how that surfaced: the old body was SYMMETRIC in
        # the two panels and the new one is a ratio, so `swap` started failing
        # on six grid points. The symmetry declaration is removed because the
        # quantity genuinely changed, not because it became inconvenient.
        #
        # Allele-swap invariance survives the correction, and that is worth more
        # than it looks: `2p(1-p)` is even about one half in the numerator AND
        # the denominator, so the ratio is invariant for the same reason the old
        # absolute difference was. A relation that holds across a body
        # replacement is evidence the replacement kept the right symmetry.
        invariant_under_allele_swap(["pSource", "pTarget"]),
    ],
    "Descent.targetR2FromNeutralAFBenchmark": [
        jointly_scales(["V_A", "V_E"], 0),
    ],
    "Descent.targetExactCalibratedBrierRisk": [
        jointly_scales(["V_A", "V_E"], 0),
    ],
    "Descent.targetBrierFromNeutralAFBenchmark": [
        jointly_scales(["V_A", "V_E"], 0),
    ],
    "Descent.standardNormalPdf": [
        even_under_negation(["x"]),
    ],
    "Descent.brierRegretPoint": [
        # The Brier regret is the squared forecast deviation, so it is quadratic
        # in the pair and EVEN in it -- a body carrying a stray linear term
        # would still be zero on the diagonal and still monotone away from it.
        jointly_scales(["η", "q"], 2),
        even_under_negation(["η", "q"]),
    ],
    "Descent.brierRegretRatio": [
        jointly_scales(["η", "qSource", "qTarget"], 0),
    ],
    "Descent.expectedSqMeanPGSDiff_pureSplit": [
        scales("V_A", 1),
        symmetric_in("fstS", "fstT"),
        jointly_scales(["fstS", "fstT"], 1),
    ],
    "Descent.expectedSqMeanPGSDiff_IMEquilibrium": [
        scales("V_A", 1),
    ],
    "Descent.covarianceRetention": [
        symmetric_in("freq_corr", "ld_overlap"),
        jointly_scales(["freq_corr", "ld_overlap"], 2),
    ],
    "Descent.alleleFreqCorrelation": [
        # A variance ratio: only the ratio of ancestral variance to F_ST-weighted
        # heterozygosity matters, so both a common rescaling and a reciprocal
        # trade between F_ST and the heterozygosity leave it alone.
        jointly_scales(["varAncestral", "meanHetAncestral"], 0),
        invariant_under_reciprocal_scaling(["fst"], ["meanHetAncestral"]),
    ],
    "Descent.ldOverlapFromSharedLD": [
        scales("shared_ld", 1),
    ],
    "Descent.presentDayPGSVarianceMutationDrift": [
        scales("V_A", 1),
    ],
    "Descent.presentDayR2MutationDrift": [
        jointly_scales(["V_A", "V_E"], 0),
    ],
    "Descent.neutralAFSharedLDBenchmarkRatio": [
        jointly_scales(["shared_ld_source", "shared_ld_target"], 0),
    ],
    "Descent.fstMigrationDriftEquilibrium": [
        invariant_under_reciprocal_scaling(["Ne"], ["m"]),
    ],
    "Descent.sharedLD_from_equilibrium": [
        invariant_under_reciprocal_scaling(["Ne"], ["m"]),
    ],
    "Descent.neutralAFBenchmarkFromRecurrence": [
        invariant_under_reciprocal_scaling(["Ne"], ["m"]),
    ],
    "Descent.asymmetricFst": [
        # Only the SUM of the two directional rates enters, which is the whole
        # content of the name: asymmetric migration gives a symmetric F_ST.
        symmetric_in("m₁₂", "m₂₁"),
        invariant_under_reciprocal_scaling(["Ne"], ["m₁₂", "m₂₁"]),
    ],
    "Descent.effectiveSymmetricMigration": [
        symmetric_in("m₁₂", "m₂₁"),
        jointly_scales(["m₁₂", "m₂₁"], 1),
    ],

    # --- DGP ---------------------------------------------------------------
    "Descent.scaledMutationRate": [
        # `4·Nₑ·μ`. The symmetry is the content: the compound is a product, so
        # the two factors are interchangeable and only their product is read.
        symmetric_in("Ne", "μ"),
        jointly_scales(["Ne", "μ"], 2),
        scales("Ne", 1),
    ],
    "Descent.scaledMigrationRate": [
        symmetric_in("Ne", "m"),
        jointly_scales(["Ne", "m"], 2),
        scales("Ne", 1),
    ],
    "Descent.r2FromMSE": [
        # A variance ratio subtracted from one: the outcome's unit cancels.
        jointly_scales(["mse", "varY"], 0),
    ],
    "Descent.explainedR2FromTransportMoments": [
        scales("scoreOutcomeCov", 2),
        scales("scoreVariance", -1),
        scales("outcomeVariance", -1),
    ],
    "Descent.taggingMismatchScale": [
        symmetric_in("recombRate", "arraySparsity"),
        jointly_scales(["recombRate", "arraySparsity"], 2),
    ],
    "Descent.demographicCovarianceGapLowerBound": [
        scales("kappa", 1),
        jointly_scales(["recombRate", "arraySparsity"], 2),
        jointly_scales(["fstSource", "fstTarget"], 1),
    ],
    "Descent.optimalSlopeLinearNoise": [
        # Signal over signal-plus-noise: every variance in the same unit, so a
        # common rescaling of all three leaves the optimal slope alone.
        jointly_scales(["sigma_g_sq", "base_error", "slope_error"], 0),
    ],
    "Descent.TransportedMetrics.r2FromSignalVariance": [
        jointly_scales(["vSignal", "vNoise"], 0),
    ],
    "Descent.TransportedMetrics.equalVarianceGaussianAUCFromSignalVariance": [
        jointly_scales(["vSignal", "vNoise"], 0),
    ],
    "Descent.TransportedMetrics.calibratedBrierFromVariances": [
        jointly_scales(["vSignal", "vResidual"], 0),
    ],
    "Descent.alleleFreqDivergenceRate": [
        scales("Ne", -1),
    ],
    "Descent.ldBreakageRate": [
        scales("r", 1),
    ],

    # --- MetricSpecificPortability -----------------------------------------
    "Descent.adaptationDifficultyIndex": [
        jointly_scales(["nParams", "infoPerSample"], 0),
        scales("nParams", 1),
        scales("infoPerSample", -1),
    ],
    "Descent.fisherTraceMSELowerBound": [
        scales("nEff", -1),
        jointly_scales(["nParams", "infoPerSample"], 0),
    ],
    "Descent.requiredEffectiveSampleSizeForTraceMSE": [
        scales("targetTraceMSE", -1),
        jointly_scales(["nParams", "infoPerSample"], 0),
    ],
    "Descent.sensitivityPortabilityGap": [
        # An absolute difference: symmetric, homogeneous of degree one, and EVEN
        # under negating the pair. A signed difference would satisfy the first
        # two and fail the third, which is the one that says "gap".
        symmetric_in("sensSource", "sensTarget"),
        jointly_scales(["sensSource", "sensTarget"], 1),
        even_under_negation(["sensSource", "sensTarget"]),
    ],
    "Descent.mixtureCoupling": [
        scales("ρ", 1),
        # `ρ(2π - 1)` is ODD about π = 1/2: complementing the mixing proportion
        # reverses the coupling. That is the relation which fixes the `2π - 1`
        # factor rather than any other odd function of the mixture.
        negated_under_allele_swap(["π"]),
    ],
    "Descent.twoCellL2EstimationPenalty": [
        jointly_scales(["n₁", "n₂"], -1),
    ],
    "Descent.twoCellWorstEstimationPenalty": [
        symmetric_in("n₁", "n₂"),
        jointly_scales(["n₁", "n₂"], -1),
    ],
    "Descent.ppvPortabilityGap": [
        symmetric_in("prevalenceSource", "prevalenceTarget"),
    ],

    # --- RareVariantPortability --------------------------------------------
    "Descent.rareHeritabilityShare": [
        # A share, so scale-free in the variances and in everything together.
        jointly_scales(["rareCount", "rareVariance",
                        "commonCount", "commonVariance"], 0),
        jointly_scales(["rareVariance", "commonVariance"], 0),
    ],
    "Descent.variantGeneticVarianceContribution": [
        scales("β", 2),
        invariant_under_allele_swap(["p"], effect_args=["β"]),
    ],
    "Descent.rareVariantCountRatio": [
        jointly_scales(["sourceCount", "targetCount"], 0),
        scales("sourceCount", 1),
    ],
    "Descent.burdenSquaredSignal": [
        symmetric_in("β₁", "β₂"),
        jointly_scales(["β₁", "β₂"], 2),
        even_under_negation(["β₁", "β₂"]),
    ],
    "Descent.varianceComponentSignal": [
        # DELIBERATELY the same three relations as burdenSquaredSignal above.
        # `(β₁+β₂)²` and `β₁²+β₂²` are both symmetric, both quadratic and both
        # even, differing only by the cross term `2β₁β₂` -- so these relations
        # do NOT separate the burden statistic from the variance-component one.
        # Recording that they cannot is the point: the pair is what a reference
        # evaluation has to distinguish, and no symmetry or homogeneity will.
        symmetric_in("β₁", "β₂"),
        jointly_scales(["β₁", "β₂"], 2),
        even_under_negation(["β₁", "β₂"]),
    ],
    "Descent.portableVariantSignal": [
        scales("β", 2),
        scales("sharing", 1),
        invariant_under_allele_swap(["frequency"], effect_args=["β"]),
    ],
    "Descent.mutationSelectionBalance": [
        # `μ/(hs + μ)` reads only the ratio of mutation to selection.
        jointly_scales(["mu", "s"], 0),
    ],
    "Descent.mutationSelectionDriftParameter": [
        symmetric_in("s", "h"),
        jointly_scales(["Ne", "s", "h"], 3),
        scales("Ne", 1),
    ],
    "Descent.mutationSelectionBalanceRecessive": [
        jointly_scales(["mu", "s"], 0),
    ],
    # --- PGSCalibrationTheory ----------------------------------------------
    "Descent.calibrationInTheLarge": [
        jointly_scales(["mean_observed", "mean_predicted"], 1),
        odd_under_negation(["mean_observed", "mean_predicted"]),
    ],
    "Descent.hosmerLemeshowContrib": [
        scales("n_group", 1),
    ],
    "Descent.prevalenceLogit": [
        # `log(π/(1-π))` is ODD about π = 1/2: complementing the prevalence
        # negates the log-odds. That is what makes it a logit rather than any
        # other monotone map of a probability to the line.
        negated_under_allele_swap(["pi"]),
    ],
    "Descent.prevalenceCITLShift": [
        negated_under_allele_swap(["pi_source", "pi_target"]),
    ],
    "Descent.interceptRecalibrated": [
        symmetric_in("pgs", "new_intercept"),
        jointly_scales(["pgs", "new_intercept"], 1),
        odd_under_negation(["pgs", "new_intercept"]),
    ],
    "Descent.logisticRecalibrated": [
        # Scaling the intercept AND the slope together scales the recalibrated
        # score; scaling either alone does not, because the score itself is held.
        jointly_scales(["a", "b"], 1),
    ],
    "Descent.recalibratedCalibrationSlope": [
        jointly_scales(["slope", "fittedSlope"], 0),
        scales("slope", 1),
        scales("fittedSlope", -1),
    ],
    "Descent.recalibrationTraceMSELowerBound": [
        scales("nParams", 1),
        # Both arguments sit in the DENOMINATOR, so scaling the pair by c
        # divides by c**2, not by c. Declared as -1 on first writing -- the
        # single power belongs to each argument separately -- and caught here.
        jointly_scales(["nEvents", "infoPerEvent"], -2),
    ],
    "Descent.requiredEventsForRecalibration": [
        scales("nParams", 1),
        jointly_scales(["infoPerEvent", "targetTraceMSE"], -2),
    ],
    "Descent.requiredTargetCohortSizeForRecalibration": [
        scales("nParams", 1),
        scales("prevalence", -1),
    ],
    "Descent.nri": [
        # A reclassification index: the four counts and the two denominators are
        # in the same units, so a common rescaling of everything leaves it alone
        # and a rescaling of the numerators alone scales it linearly.
        jointly_scales(["up_events", "down_events", "up_nonevents",
                        "down_nonevents", "n_events", "n_nonevents"], 0),
        jointly_scales(["up_events", "down_events",
                        "up_nonevents", "down_nonevents"], 1),
    ],
    "Descent.screeningBreakEvenPrevalence": [
        # A prevalence, so scale-free in the utilities: only benefit/harm is read.
        jointly_scales(["benefit", "harm"], 0),
    ],

    # --- SelectionArchitecture ---------------------------------------------
    "Descent.equilibriumEffectVariance": [
        scales("v_mutation", 1),
        scales("s", -1),
        jointly_scales(["v_mutation", "s"], 0),
    ],
    "Descent.stabilizingSelectedArchitectureVariance": [
        scales("v_mutation", 1),
        jointly_scales(["v_mutation", "s"], 0),
    ],
    "Descent.effectVarianceRecurrence": [
        jointly_scales(["V", "v_mut"], 1),
    ],
    "Descent.fluctuatingEffectCorrelation": [
        # `exp(-t/τ)` reads only the ratio, so time units cancel.
        jointly_scales(["t", "τ"], 0),
    ],
    "Descent.optimumOUVariance": [
        scales("sigmaTheta", 2),
        scales("tau", 1),
    ],
    "Descent.tauFromObservedEffectCorrelation": [
        scales("t", 1),
    ],
    "Descent.pleiotropicTargetR2": [
        scales("sourceR2", 1),
        # The shared fraction and the turnover enter only as a product, so they
        # are interchangeable -- half the loci turning over completely is the
        # same as all of them turning over half way.
        symmetric_in("sharedFraction", "turnover"),
    ],

    # --- HaplotypeTheory ---------------------------------------------------
    "Descent.averagePhaseInteraction": [
        jointly_scales(["interaction_cis", "interaction_trans"], 1),
        odd_under_negation(["interaction_cis", "interaction_trans"]),
    ],
    "Descent.dosagePhaseMisspecificationError": [
        # A squared misspecification: quadratic in the interactions and EVEN in
        # them, so a body carrying a stray linear term fails here while passing
        # every scaling relation.
        jointly_scales(["interaction_cis", "interaction_trans"], 2),
        even_under_negation(["interaction_cis", "interaction_trans"]),
    ],
    "Descent.haplotypePhasePredictionError": [
        jointly_scales(["pred_cis", "pred_trans",
                        "interaction_cis", "interaction_trans"], 2),
        even_under_negation(["pred_cis", "pred_trans",
                             "interaction_cis", "interaction_trans"]),
    ],
    "Descent.dosageTransportBias": [
        symmetric_in("freq_cis_source", "freq_cis_target"),
        jointly_scales(["interaction_cis", "interaction_trans"], 1),
        even_under_negation(["interaction_cis", "interaction_trans"]),
    ],
    "Descent.haplotypeTransportBias": [
        jointly_scales(["pred_cis", "pred_trans",
                        "interaction_cis", "interaction_trans"], 1),
        even_under_negation(["pred_cis", "pred_trans",
                             "interaction_cis", "interaction_trans"]),
    ],
    "Descent.haplotypeEffectVarianceOLS": [
        scales("σ2", 1),
        scales("n", -1),
        invariant_under_allele_swap(["freq"]),
    ],
    "Descent.phaseAttenuation": [
        # `(1 - 2s)²` is even about s = 1/2, so a switch rate and its complement
        # attenuate identically -- phasing backwards is as good as phasing right.
        invariant_under_allele_swap(["s"]),
    ],
    "Descent.ancestrySpecificEffect": [
        jointly_scales(["beta_pop1", "beta_pop2"], 1),
        odd_under_negation(["beta_pop1", "beta_pop2"]),
    ],
    "Descent.globalAncestryAveragedEffect": [
        jointly_scales(["beta₁", "beta₂"], 1),
        odd_under_negation(["beta₁", "beta₂"]),
    ],
    "Descent.localAncestryMisspecification": [
        jointly_scales(["beta₁", "beta₂"], 2),
        even_under_negation(["beta₁", "beta₂"]),
    ],
    "Descent.expectedTractLength": [
        scales("g", -1),
    ],

    # --- TARGETED: definitions whose verdict is weakest -------------------
    # Selected by verdict rather than by module. Two populations are worth more
    # than the next alphabetical sweep: bodies still marked FALSIFIED, where a
    # relation either survives a correction (evidence the correction kept the
    # right structure) or fails it (evidence it did not); and bodies with NO
    # verdict at all, which nothing in the corpus can contradict today.

    # STILL FALSIFIED. `d / (d + 4·Nₑ·σ²·m²)`.
    "Descent.steppingStoneFstQuadratic": [
        # σ² and m both enter SQUARED, so they are interchangeable. This is a
        # true relation and a diagnostic one: `symbolic` showed the extra power
        # of m is what is wrong with this body, and the symmetry is that error's
        # signature. A stepping-stone F_ST with σ² and m entering at different
        # powers -- which is what the correction must produce -- will FAIL this
        # relation, and that failure is the confirmation that the body moved.
        # When it is corrected, move this entry to EXPECTED_VIOLATIONS rather
        # than deleting it, exactly as was done for ldCorrelationDecay.
        symmetric_in("m", "σ_sq"),
    ],
    # STILL FALSIFIED. Coalescent time in a serial-founder chain.
    "Descent.serialFounderWithinTime": [
        # Every argument is a time or a population size, so scaling all three
        # together is a change of time unit and must scale the answer by exactly
        # that factor. This holds for the current body and must hold for any
        # replacement: a coalescent time that did not rescale would be reporting
        # generations in one place and coalescent units in another. A relation
        # that constrains the REPAIR as well as the current body is the most
        # useful thing to declare on a falsified quantity.
        jointly_scales(["N", "Nanc", "tAnc"], 1),
    ],

    # NO VERDICT AT ALL: the scoring-rule core of Conclusions.lean. Every one of
    # these is invariant under relabelling which outcome counts as the event --
    # `p ↦ 1-p` together with `π ↦ 1-π` -- because a proper scoring rule cannot
    # depend on which of two complementary outcomes you decided to call success.
    #
    # This is the relation that would have caught the `π`-binder extraction bug
    # directly, and on the definition where it originated. With `π` shadowed by
    # the constant, `expectedBrierScore(1-p, 1-π)` no longer equals
    # `expectedBrierScore(p, π)` at any p other than one half, because only one
    # of the two arguments is really being complemented.
    "Descent.brierScore": [
        symmetric_in("p", "y"),
        jointly_scales(["p", "y"], 2),
        even_under_negation(["p", "y"]),
    ],
    "Descent.expectedBrierScore": [
        invariant_under_allele_swap(["p", "π"]),
    ],
    "Descent.bernoulliLogLoss": [
        invariant_under_allele_swap(["p", "q"]),
    ],
    "Descent.bernoulliKLReal": [
        invariant_under_allele_swap(["p", "q"]),
    ],
    "Descent.brierBernoulliRisk": [
        invariant_under_allele_swap(["η", "q"]),
    ],
    "Descent.logBernoulliRisk": [
        invariant_under_allele_swap(["η", "q"]),
    ],

    # NO VERDICT AT ALL: the shrinkage family of BayesianPGSTheory.
    "Descent.gaussianPosteriorShrinkage": [
        # `nh/(nh+1)` reads only the product, so sample size and heritability
        # are interchangeable -- twice the sample at half the heritability
        # shrinks identically.
        symmetric_in("n", "h"),
    ],
    "Descent.jamesSteinMSE": [
        # Both terms are variances in the same unit.
        jointly_scales(["σ_sq", "β_sq"], 1),
    ],
    "Descent.optimalShrinkage": [
        # A weight in [0,1]: scale-free in the two variances.
        jointly_scales(["σ_sq", "β_sq"], 0),
    ],
    "Descent.snpShrinkage": [
        jointly_scales(["σ", "τ"], 0),
    ],
    "Descent.misspecExcessRisk": [
        scales("σ_β_sq", 1),
        # π(1-π) is even about one half, so the excess risk does not care which
        # outcome is called the event.
        invariant_under_allele_swap(["π"]),
    ],
    "Descent.posteriorPredictiveVariance": [
        symmetric_in("residual_var", "estimation_var"),
        jointly_scales(["residual_var", "estimation_var"], 1),
    ],

    # --- TARGETED, no verdict: CirculationDefect ---------------------------
    "Descent.driftGeneratorForm": [
        # `s(x² + y²) + circulationQuadraticForm a x y`, and the second term is
        # identically zero. So the form is INVARIANT UNDER SCALING `a` -- the
        # circulation parameter is invisible to the Dirichlet form at every
        # value, which is the whole content of this module and is stated here
        # as a relation that can fail rather than as prose. A body in which any
        # part of the circulation survived would move when `a` moves.
        scales("a", 0),
        scales("s", 1),
        symmetric_in("x", "y"),
        jointly_scales(["x", "y"], 2),
        even_under_negation(["x", "y"]),
    ],
    "Descent.frontierTime": [
        scales("s", -1),
    ],
    "Descent.apparentMixingTime": [
        jointly_scales(["s", "a"], -1),
        even_under_negation(["a"]),
    ],
    "Descent.circulationDefect": [
        # `a²/(s(s² + a²))`: numerator degree 2 over denominator degree 3, so
        # the joint exponent is -1. Declared as -2 on first writing -- the third
        # time in this table I have composed a joint exponent from the
        # per-argument ones instead of computing the net degree, and the third
        # time the gate caught it on the first run.
        jointly_scales(["s", "a"], -1),
        even_under_negation(["a"]),
    ],
    "Descent.transferTimeInflation": [
        # Reads only the ratio a/s, so the rate unit cancels.
        jointly_scales(["s", "a"], 0),
        even_under_negation(["a"]),
    ],

    # --- TARGETED, no verdict: ClinicalUtilityFairness ---------------------
    "Descent.netReclassificationImprovement": [
        symmetric_in("event_nri", "nonevent_nri"),
        jointly_scales(["event_nri", "nonevent_nri"], 1),
        odd_under_negation(["event_nri", "nonevent_nri"]),
    ],
    "Descent.ppv": [
        # A posterior probability: scale-free in the two rates.
        jointly_scales(["tpr", "fpr"], 0),
    ],
    "Descent.proportionCorrectlyClassified": [
        jointly_scales(["sensitivity", "specificity"], 1),
    ],
    "Descent.populationAttributableFraction": [
        scales("p_high", 1),
    ],

    # --- TARGETED, no verdict: AncestryCalibration -------------------------
    "Descent.ancestryRecalibratedSlope": [
        scales("bSource", 1),
        scales("rho", 1),
        scales("alpha", -1),
    ],
    "Descent.ancestryRecalibratedR2": [
        symmetric_in("r2Source", "rhoSq"),
        jointly_scales(["r2Source", "rhoSq"], 2),
    ],
    "Descent.effectTurnoverR2Loss": [
        scales("r2Source", 1),
    ],
    "Descent.cubicSplineApproximationScale": [
        # The fourth power is the whole claim: a cubic spline's approximation
        # error is O(h⁴), and a body carrying h³ or h⁵ is monotone and positive
        # exactly as this one is.
        scales("h", 4),
        even_under_negation(["h"]),
    ],
    "Descent.splineCalibrationMSE": [
        # bias² + variance: even in the bias alone, which is what says the
        # decomposition squares the bias rather than carrying it signed.
        even_under_negation(["bias"]),
    ],
    "Descent.explainedVarianceFraction": [
        jointly_scales(["varSignal", "varNoise"], 0),
    ],
    "Descent.transferredEstimatorMSE": [
        jointly_scales(["σ_sq", "bias_sq"], 1),
    ],
    "Descent.targetOnlyEstimatorMSE": [
        symmetric_in("σ_sq", "σ_extra_sq"),
        jointly_scales(["σ_sq", "σ_extra_sq"], 1),
        scales("nTarget", -1),
    ],
    "Descent.epistaticVariancePairwise": [
        scales("γ", 2),
        symmetric_in("p₁", "p₂"),
        invariant_under_allele_swap(["p₁", "p₂"]),
    ],

    # --- TARGETED, no verdict: AncestrySpecificArchitecture ----------------
    # Joint exponents below are computed as NUMERATOR DEGREE MINUS DENOMINATOR
    # DEGREE and written down before choosing the constructor. Three times in
    # this table I composed one from the per-argument exponents instead and got
    # it wrong in three different directions; the order of operations is the fix.
    "Descent.allelicHeterogeneityRetainedSignal": [
        # Product of three, degree 3 over 1.
        jointly_scales(["r2_causal", "r2_tag", "sharedFraction"], 3),
        symmetric_in("r2_causal", "r2_tag"),
    ],
    "Descent.populationGeneVariance": [
        symmetric_in("shared", "specific"),
        jointly_scales(["shared", "specific"], 1),
        odd_under_negation(["shared", "specific"]),
    ],
    "Descent.crossPopulationGeneTransferFraction": [
        # A share: numerator degree 1, denominator degree 1, so net 0.
        jointly_scales(["shared", "targetSpecific"], 0),
    ],
    "Descent.portabilityFromArchitecture": [
        scales("rg", 2),
        scales("tagging_ratio", 1),
        jointly_scales(["rg", "tagging_ratio"], 3),
    ],

    # --- TARGETED, no verdict: AssortativeMatingPGS ------------------------
    "Descent.amVarianceStep": [
        # Both variances enter the numerator linearly; r and h2 sit in a factor.
        jointly_scales(["V₀", "V"], 1),
    ],
    "Descent.amEquilibriumVariance": [
        scales("V_A", 1),
    ],
    "Descent.amCorrectedPortability": [
        scales("port_measured", 1),
    ],
    "Descent.ibdFst": [
        # `d / (4Nσ² + d)`. Two independent invariances, and they are different
        # statements: the deme separation trades against the population size,
        # and the population size trades against the dispersal variance because
        # only the product Nσ² is read.
        jointly_scales(["d", "N"], 0),
        invariant_under_reciprocal_scaling(["N"], ["sigma_sq"]),
    ],

    # --- TARGETED, no verdict: DirichletTransfer ---------------------------
    "Descent.dirichletEfficiency": [
        # `1 + τ·energy`: the two enter only as a product, so they trade freely.
        symmetric_in("τ", "energy"),
    ],
    "Descent.driftHorizon": [
        # `(D₂ - D₁)/(2C)`: numerator degree 1, denominator degree 1, net 0.
        jointly_scales(["D₁", "D₂", "C"], 0),
        jointly_scales(["D₁", "D₂"], 1),
        scales("C", -1),
        odd_under_negation(["D₁", "D₂"]),
    ],
    "Descent.stalePremium": [
        scales("V", 1),
        invariant_under_reciprocal_scaling(["lam"], ["τ"]),
    ],
    "Descent.dampedAdjustment": [
        scales("g", 1),
        invariant_under_reciprocal_scaling(["lam"], ["τ"]),
    ],
    "Descent.dampedPremium": [
        scales("V", 1),
        invariant_under_reciprocal_scaling(["lam"], ["τ"]),
    ],
    "Descent.myopiaPrice": [
        scales("V", 1),
        invariant_under_reciprocal_scaling(["lam"], ["τ"]),
    ],
    "Descent.shrinkagePremium": [
        # `α(2ρ - α)V`: both terms in the bracket are degree 2 in the pair.
        scales("V", 1),
        jointly_scales(["α", "ρ"], 2),
    ],

    # --- TARGETED, no verdict: Condensation / ErgodicCovariancePencil ------
    "Descent.criticalDegree": [
        # `log N / c`: degree -1 in c. N sits inside a logarithm and so falls
        # under the log-scaling gap named in this file's header -- the relation
        # it satisfies is f(N^k, c) = k·f(N, c), which no kind here can carry.
        scales("c", -1),
    ],
    "Descent.twoSiteCovarianceEnergy": [
        symmetric_in("x", "y"),
        jointly_scales(["x", "y"], 2),
        even_under_negation(["x", "y"]),
    ],
    "Descent.firstModeConditionalMean": [
        # `mean + r(source - mean)`: degree 1 in the two location arguments,
        # and odd in them, which is what says it is an interpolation between
        # two locations rather than a shift toward one of them.
        jointly_scales(["mean", "source"], 1),
        odd_under_negation(["mean", "source"]),
    ],

    # --- TARGETED, no verdict: DriftRegime ---------------------------------
    "Descent.targetHetOfRetention": [
        symmetric_in("H₀", "r"),
        jointly_scales(["H₀", "r"], 2),
        scales("H₀", 1),
    ],
    "Descent.targetPgsVarOfRetention": [
        symmetric_in("V_A", "r"),
        jointly_scales(["V_A", "r"], 2),
        scales("V_A", 1),
    ],

    # --- TARGETED, no verdict: EpistasisAndNonAdditivity -------------------
    "Descent.fisherAverageEffect": [
        # The same body as BlindnessRegistry.OneLocusArchitecture.averageEffect,
        # and it carries the same relation: relabelling the alleles sends
        # p ↦ 1-p and a ↦ -a together, leaving d alone, and the average effect
        # is ODD under that -- it is the same substitution described from the
        # other end. Proved in Lean there as averageEffect_allele_swap; executed
        # here, on the copy that lives in this module. Two bodies stating one
        # fact is a place they can drift apart, and this is what would notice.
        negated_under_allele_swap(["p"], effect_args=["a"]),
        jointly_scales(["a", "d"], 1),
    ],
    "Descent.pairwiseModel": [
        jointly_scales(["beta1", "beta2", "beta12"], 1),
        odd_under_negation(["beta1", "beta2", "beta12"]),
    ],
    "Descent.epistaticVariance": [
        scales("beta12", 2),
        symmetric_in("p1", "p2"),
        invariant_under_allele_swap(["p1", "p2"]),
    ],

    # --- TARGETED, no verdict: CausalInference -----------------------------
    "Descent.effectShare": [
        # Numerator degree 1 over denominator degree 1: net 0, so the effect's
        # unit cancels and only the share is read.
        jointly_scales(["indirect_effect", "total_effect"], 0),
    ],
    "Descent.costEffectiveness": [
        jointly_scales(["improvement", "cost"], 0),
        scales("improvement", 1),
        scales("cost", -1),
    ],

    "Descent.recessiveMutationSelectionDriftParameter": [
        scales("Ne", 1),
        symmetric_in("mu", "s"),
        # `2·Nₑ·sqrt(μ·s)`: scaling BOTH by c sends the product to c²μs and the
        # root to c·sqrt(μs), so the joint exponent is 1, not 1/2. Declared as
        # 1/2 on first writing -- the half belongs to each argument separately,
        # not to the pair -- and caught here on the first run.
        jointly_scales(["mu", "s"], 1),
    ],
}

# ---------------------------------------------------------------------------
# PINNED EXPECTED VIOLATIONS -- checked in BOTH directions
# ---------------------------------------------------------------------------

EXPECTED_VIOLATIONS = {
    ("Descent.ldCorrelationDecay", "reciprocal_scale/fstGap|lambda"):
        "The superseded body was `exp(-(lambda · fstGap · distance))`, in which "
        "fstGap and distance entered identically and each traded off exactly "
        "against lambda. That linear fstGap dependence was refuted at 4.73 sems "
        "and the body is now `exp(-(lambda · sqrt(fstGap) · distance))`. So the "
        "trade against lambda survives for DISTANCE and must NOT survive for "
        "fstGap: scaling fstGap by c now needs lambda scaled by 1/sqrt(c), not "
        "1/c. Pinned rather than deleted because that asymmetry IS the "
        "correction -- a body in which the two arguments traded off the same "
        "way would be the refuted one, and this entry fires if anyone restores "
        "it. This table's vocabulary has no reciprocal relation with unequal "
        "exponents, which is why the fact is recorded as a pinned violation "
        "rather than as a relation of its own.",
    ("Descent.multiTraitEffectiveSampleSize", "swap/n₁<->n₂"):
        "The body is deliberately NOT symmetric: n₁ is the target trait's "
        "own sample and enters undiscounted, while the second trait's sample is "
        "discounted by the squared genetic correlation and, since the "
        "correction to `n₁ + rg²·n₂`, further by the other trait's effect "
        "scatter `(1-rg²)·priorVariance`. A body symmetric in the "
        "two would be claiming that borrowing strength from a correlated trait "
        "is as good as having the observations, which is the whole error the "
        "definition exists to avoid. Pinned rather than dropped so that a body "
        "which BECAME symmetric would fail here rather than pass silently.",
}

# ---------------------------------------------------------------------------
# DEFINITIONS IN SWEPT MODULES WITH NO APPLICABLE RELATION
# ---------------------------------------------------------------------------

NO_RELATIONS = {
    "Descent.expectedHeterozygosity":
        "θ/(1+θ) is a saturating map of a single already-dimensionless scaled "
        "parameter. Scaling θ changes the answer -- that is its content -- and "
        "there is no second argument to trade against it.",
    "Descent.islandDemeCorrection":
        "d/(d-1) is a pure deme-count correction. d is a cardinality, so there "
        "is no unit to rescale and no second argument to exchange it with.",
    "Descent.ldCorrelationMigrationAnsatz":
        "M²/(1+M)² is a saturating function of the single scaled migration "
        "parameter; the compound is already formed, so nothing is left to hold "
        "fixed against it.",
    "Descent.hetDecayFactor":
        "(1 - 1/(2Nₑ))(1 - θ/(2Nₑ)) has Nₑ appearing in two channels with "
        "different numerators, so no rescaling of Nₑ against θ leaves it fixed. "
        "The absence is the content: drift and mutation do not trade off.",
    "Descent.continentIslandStepSelectionFirst":
        "One generation of a nonlinear selection-migration recursion. Rescaling "
        "s or m moves the fixed point rather than reparametrising the step, and "
        "the two orderings below are precisely NOT interchangeable.",
    "Descent.continentIslandStepMigrationFirst":
        "As above. That this body and the selection-first one are different "
        "functions is the point of the pair; neither has a symmetry of its own.",
    "Descent.selectionMigrationEquilibrium":
        "max 0 ((s - m - m·s)/s) is clipped at zero, so it is not homogeneous "
        "in any argument: the clip destroys every scaling relation on the half "
        "of the domain where it binds, and a relation that holds only off the "
        "clip is not a relation.",
    "Descent.gaussianSourceResidualRisk":
        "exp(-2·I) turns an information into a risk, so no rescaling of I is a "
        "rescaling of the output: the relation it does satisfy is "
        "f(a+b) = f(a)·f(b), a functional equation rather than a homogeneity, "
        "and this table's kinds are all homogeneities and symmetries.",
    "Descent.infoCertifiedBenDavidUpperBound":
        "A sum of an exponential, a square root and a linear term in three "
        "different arguments. Each summand has a different degree, so no common "
        "scaling acts on the whole; the per-argument relations belong to the "
        "three components, which are declared separately above.",
    "Descent.usableScratchTargetR2":
        "max 0 of the sample-limited R², so the clip destroys every scaling "
        "relation on the half of the domain where it binds. A relation that "
        "holds only off the clip is not a relation, which is why the unclipped "
        "sampleLimitedScratchTargetR2 carries the declaration instead.",
    "Descent.centeredSquareVarianceFromMoments":
        "m₄ - m₂² is Var(X²) from RAW moments, and the two arguments scale at "
        "different rates under the only transformation that matters: scaling "
        "the underlying variable by s sends m₂ to s²m₂ and m₄ to s⁴m₄. No "
        "single common factor acts on both, so no scaling relation in this "
        "table's vocabulary can express the one relation it does have.",
    "Descent.binaryOrientationArrowPermeability":
        "A one-argument function of an orientation angle through a variance "
        "that is not homogeneous in it; θ is an angle, so there is no unit to "
        "rescale and no second argument to hold against it.",
    "Descent.threeCycleOrientationArrowPermeability":
        "As the binary case: a fixed response over 1 - θ², with θ an angle "
        "carrying no unit. The constants are pinned by reference-point "
        "theorems in the module rather than by any invariance.",
    # --- PortabilityDrift --------------------------------------------------
    "Descent.fstFromTau":
        "tau/(1+tau) saturates a single already-scaled coalescent time. Scaling "
        "tau changes the answer -- that is its content -- and there is no "
        "second argument to trade against it. Its rescaling invariance lives in "
        "fstFromGenerations, which does take t and Ne separately.",
    "Descent.twoDemeIMFirstStepSame":
        "One step of a two-deme island recursion, affine in ETst with an "
        "M-dependent intercept AND an M-dependent slope. It is affine, not "
        "homogeneous, so no scaling of any argument multiplies the output.",
    "Descent.twoDemeIMFirstStepDiff":
        "1/M + ETss adds a reciprocal rate to a time. The two summands have "
        "opposite degrees in any common rescaling, so no single factor acts on "
        "the sum; that they nonetheless share units is a statement about the "
        "coalescent scaling and not about this body.",
    "Descent.twoDemeIMEquilibriumETss":
        "Constant at 2: two lineages in the same deme coalesce in two "
        "population-size units whatever the migration rate, which is why the "
        "argument is named `_M` and ignored. A constant satisfies every "
        "invariance vacuously, which is exactly why it must not be declared "
        "with one -- the vacuity screen in run.py would fire, and correctly.",
    "Descent.twoDemeIMEquilibriumETst":
        "(2M+1)/M is a ratio of terms of different degree in M, so it is not "
        "homogeneous; and M is already the scaled migration rate, so there is "
        "no unit left to cancel against it.",
    "Descent.twoDemeIMEquilibriumDelta":
        "1/(2M+1) in the single scaled migration parameter, saturating rather "
        "than homogeneous. Same reason as fstFromTau one entry up.",
    "Descent.hetStepWithMutation":
        "Drift and mutation enter through different powers of Ne and mu with an "
        "additive input term, so no rescaling of Ne against mu holds them "
        "fixed. The absence is the content: unlike hetMutationFloor below, the "
        "STEP is not a function of 4·Ne·mu alone -- only its fixed point is.",
    "Descent.brierFromR2":
        "π(1-π)(1-r2) is affine in r2 and quadratic-with-an-intercept in π, so "
        "no argument scales the output. Its content is pinned by reference "
        "evaluations at r2 = 0 and r2 = 1 instead.",
    "Descent.sourceBrierFromR2":
        "The same body as brierFromR2 read at the source population; same "
        "reason.",
    "Descent.equalVarianceGaussianAUCFromSNR":
        "Phi of a square root: a probability, bounded in [0,1], so no scaling "
        "of the signal-to-noise ratio scales it. Monotone but not homogeneous.",
    "Descent.equalVarianceGaussianAUCFromExplainedR2":
        "As above, and additionally clipped by an `if 1 ≤ r2` branch, so any "
        "relation would hold vacuously on the clipped half of the domain and "
        "fail off it. A relation that holds only off a clip is not a relation.",
    "Descent.logLossRegretPoint":
        "A difference of logarithms, so scaling the pair scales neither the "
        "argument of the log nor the answer. The Brier regret one floor up IS "
        "quadratic and IS declared, which is the honest contrast: the two "
        "regrets have genuinely different homogeneity.",
    "Descent.logLossRegretRatio":
        "A ratio of the above; a common rescaling does not cancel because "
        "neither numerator nor denominator is homogeneous to begin with.",
    "Descent.ibdFlowStep":
        "F + (1-F)/(2Ne) - 2·rate·F mixes an input term, a drift term and a "
        "flow term with different degrees in Ne and rate; no common or "
        "reciprocal rescaling fixes it. Its equilibrium does, and that is "
        "fstMigrationDriftEquilibrium.",
    "Descent.covarianceRetentionFactorFromFst":
        "1 - fst is an affine map of a quantity already in [0,1]. Not "
        "homogeneous, and F_ST carries no unit to rescale.",
    "Descent.covarianceDivergenceFromRetention":
        "1 - (1-fst)·shared_ld: affine in shared_ld with an fst-dependent slope "
        "and a constant intercept, so nothing scales it.",
    "Descent.covarianceDivergenceMutationDrift":
        "fst + (1-fst)(1-shared_ld) is affine in each argument separately with "
        "a cross term; the intercept blocks every homogeneity.",
    "Descent.Core.islandDemeCorrection":
        "d/(d-1) is a pure deme-count correction; d is a cardinality, so there "
        "is no unit to rescale and no second argument to exchange with it.",
    "Descent.ibdRecurrenceStep":
        "(1-rate)²·(1/(2Ne) + (1-1/(2Ne))·x) carries Ne in two channels with "
        "different numerators and an additive input, so no rescaling of Ne "
        "against rate leaves it fixed.",
    "Descent.ibdRecurrenceFixedPoint":
        "(1-rate)²/((1-rate)² + 2Ne·rate·(2-rate)) is NOT a function of the "
        "product Ne·rate alone -- the (2-rate) factor breaks it, which is the "
        "exact respect in which the multiplicative recurrence differs from the "
        "diffusion approximation whose fixed point IS 1/(1+4Ne·m). Declaring a "
        "reciprocal-scaling relation here would assert the approximation.",
    "Descent.islandFstMultiplicativeStep":
        "A rename of ibdRecurrenceStep into F_ST language; same reason.",
    "Descent.fstIslandMultiplicativeEquilibrium":
        "A rename of ibdRecurrenceFixedPoint; same reason, and the same "
        "instructive contrast with fstMigrationDriftEquilibrium, which IS "
        "declared with the reciprocal-scaling relation because it IS the "
        "diffusion form.",
    "Descent.sharedLDFromMigration":
        "M/(1+M) saturates the single scaled migration parameter. The compound "
        "is already formed, so nothing is left to hold fixed against it.",
    "Descent.fstMigDriftNext":
        "(1 - 2m - 1/(2Ne))·Fst + 1/(2Ne) is affine in Fst with an additive "
        "input term, so scaling Fst does not scale the output and Ne appears in "
        "both the slope and the intercept.",

    # --- DGP ---------------------------------------------------------------
    "Descent.fstMutationDriftEquilibrium":
        "1/(1+θ) saturates the single already-scaled mutation parameter. θ is "
        "4·Nₑ·μ, so the compound is formed before this body sees it and there "
        "is nothing left to hold fixed against it. The trade between Nₑ and μ "
        "lives in scaledMutationRate, which IS declared with it.",
    "Descent.hetDecayFromScaled":
        "(1 - 1/(2Nₑ))(1 - θ/(2Nₑ)) carries Nₑ in two channels with different "
        "numerators, so no rescaling of Nₑ against θ leaves it fixed. The "
        "absence is the content: drift and mutation do not trade off, which is "
        "exactly what distinguishes this from the equilibrium above.",
    "Descent.fstTransientDecayFromScaled":
        "hetDecayFromScaled times a third channel in bigM, inheriting the same "
        "obstruction and adding one: three rates in three channels, each with "
        "its own numerator over 2Nₑ.",
    "Descent.TransportedMetrics.calibratedBrier":
        "π(1-π)(1-r2) is affine in r2 and quadratic-with-an-intercept in π, so "
        "no argument scales the output. Its content is pinned by reference "
        "evaluations at r2 = 0 and r2 = 1 instead. The VARIANCE form one entry "
        "below is scale-free and IS declared, which is the contrast: the "
        "explained fraction carries no unit, the variances it is built from do.",

    # --- MetricSpecificPortability -----------------------------------------
    "Descent.metricPPV":
        "Bayes' rule on probabilities. Every argument is a probability with no "
        "unit to rescale, and the body is a ratio whose numerator and "
        "denominator share only one of its three terms, so no common factor "
        "acts on it.",
    "Descent.ogpOverlapProfile":
        "x(1-qx)/(1-qx(1-x)) is a rational function whose numerator and "
        "denominator have different degrees in both arguments; no scaling of "
        "either is a scaling of the output, and q and x are not "
        "interchangeable.",
    "Descent.ogpTransitionPolynomial":
        "1 - 3q + q² has three terms of degrees 0, 1 and 2 in the single "
        "argument, so no rescaling of q multiplies it. The roots are what carry "
        "its content and a reference evaluation pins those.",
    "Descent.brierScoreMetric":
        "A rename of brierScore into metric-portability language; the Brier "
        "score is affine in the outcome and quadratic-with-intercept in the "
        "forecast, so nothing scales it.",
    "Descent.ldBandReconstructionShare":
        "2·arctan((1+d)/(1-d) · tan(πκ/2))/π is a bounded share built from a "
        "tangent of an angle; κ is already a fraction of the band and d a "
        "correlation, so neither carries a unit, and the arctangent is not "
        "homogeneous in either.",
    "Descent.ldBandDetectionShare":
        "κ minus the deficit below. The two summands have different structure "
        "in κ -- one linear, one a sine -- so no scaling acts on the sum. The "
        "relation this body DOES satisfy is an exact decomposition, "
        "`detectionShare + pruningDeficit = κ`, which is an identity between "
        "two definitions rather than a transformation of one input, and so "
        "belongs in AGREEMENTS rather than here if it is ever wanted.",
    "Descent.ldPruningDetectionDeficit":
        "2·d·sin(πκ)/(π(1+d²)) is a sine in κ and a rational function in d of "
        "different degrees above and below; neither argument scales it. Note it "
        "is NOT monotone in d -- it peaks at d = 1 -- so even a monotonicity "
        "claim would need a domain.",

    # --- RareVariantPortability --------------------------------------------
    "Descent.rareVariantSharingApproximation":
        "A wrapper around pgsDriftVariance_one_pop, and the relations belong to "
        "that body rather than to this name. Left undeclared here on purpose "
        "rather than duplicating a neighbour's declaration, which would make "
        "two entries that must be kept in step by hand.",
    "Descent.mutationSelectionStepRare":
        "p(1 - hs) + μ(1 - p) is one generation of a recursion: affine in p "
        "with an additive mutation input, so scaling p does not scale the "
        "output. Its FIXED POINT is scale-free in μ and s and is declared as "
        "mutationSelectionBalance.",
    "Descent.mutationSelectionStepRecessive":
        "p - sp² + μ(1-p) mixes degrees one and two in p with an additive "
        "input; same obstruction as the additive step, one order up.",
    "Descent.expectedEffectMultiplier":
        "(p(1-p))^(1+α) has its EXPONENT as an argument, so scaling p changes "
        "the output by a factor depending on α rather than by a fixed power. "
        "No relation in this table's vocabulary can carry a scaling whose "
        "exponent is itself an argument -- which is precisely why α is the "
        "parameter the architecture literature argues about.",

    "Descent.windowVariance":
        "Phi(w/sqrt v) needs w scaled by c and v by c² to hold fixed, which is a "
        "reciprocal trade with UNEQUAL exponents -- the same shape this table "
        "could not express for ldCorrelationDecay's corrected sqrt(fstGap), and "
        "recorded there as a pinned violation because a relation already "
        "existed to pin. Here there is nothing to pin, so it is recorded as an "
        "absence. Note also that Phi is bounded, so no scaling of the output is "
        "available even where the argument has one.",
    "Descent.localPencilTraceContribution":
        "(1 + source² - 2·source·target)/(1 - source²) carries bare `1`s above "
        "and below. They are ANCHORS -- the unit-variance normalisation of the "
        "standardized coordinates -- so no rescaling of either argument acts on "
        "the ratio. A fourth instance of the anchor family in this file.",
    "Descent.lossOfRetention":
        "`1 - r` is a complement, and the `1` is an anchor: retention and loss "
        "partition one, which is a statement about the constant rather than a "
        "scaling of r.",
    "Descent.benchmarkRatio":
        "(1 - fstT)/(1 - fstS) is a ratio of two complements, so both numerator "
        "and denominator carry the anchor and no rescaling of either F_ST acts "
        "on it.",
    "Descent.benchmarkRatioSquared":
        "The square of benchmarkRatio, inheriting the same anchors. The relation "
        "it DOES satisfy is `benchmarkRatioSquared = benchmarkRatio²`, an "
        "identity between two definitions rather than a transformation of one "
        "input -- so it belongs in AGREEMENTS if it is ever wanted, not here. "
        "Worth noting the pair is exactly the kind that an exponent error would "
        "silently swap, and no relation on either alone would catch it.",
    "Descent.eValue":
        "`rr + sqrt(rr(rr-1))` carries a bare `-1` fixing the null relative risk "
        "at one. Anchor again: rescaling rr moves it relative to the null "
        "rather than scaling the E-value.",

    "Descent.sampleInverseInflation":
        "`n/(n - m - 1)` carries a bare `-1` in the denominator, which is an "
        "ANCHOR and not a scale: it counts one fitted degree of freedom, so "
        "rescaling n and m together moves the answer rather than fixing it. "
        "Without that term the body would be homogeneous of degree 0; with it, "
        "nothing. The same shape as calibrationSlopeDeviation, and the same "
        "reason -- see the vocabulary gaps in this file's header.",

    "Descent.circulationQuadraticForm":
        "`x(ay) + y(-(ax))` is IDENTICALLY ZERO -- the quadratic form of an "
        "antisymmetric operator vanishes, which is `circulationQuadraticForm_eq_zero` "
        "and the reason this definition exists. A constant satisfies every "
        "invariance vacuously, so declaring one would be worse than declaring "
        "nothing, and the vacuity screen in run.py would correctly fire. What "
        "the vanishing DOES buy is declared next door instead, on "
        "driftGeneratorForm, as invariance under scaling `a`: the circulation "
        "parameter is invisible to the Dirichlet form. That is the same fact "
        "attached to a body where it can fail.",

    # --- TARGETED, still FALSIFIED, and a second vocabulary gap -------------
    "Descent.maxSafeEpistaticOrder":
        "log N / hweMellinDrift q. The relation this body DOES satisfy is under "
        "N ↦ N^c, which multiplies the answer by c -- a scaling of the "
        "LOGARITHM of an argument, not of the argument. Every kind in this table "
        "transforms arguments multiplicatively or by complement, so none of them "
        "can carry it, and declaring a plain `scales('N', k)` would assert "
        "something false. This is the second vocabulary gap found by targeting "
        "weak verdicts rather than sweeping modules; the first was "
        "reflection-about-an-anchor (see calibrationSlopeDeviation below). Both "
        "are recorded rather than approximated.",

    # --- PGSCalibrationTheory ----------------------------------------------
    "Descent.calibrationSlopeDeviation":
        "|slope - 1| measures distance from a FIXED anchor, and an anchor is "
        "not a scale: rescaling the slope moves it toward or away from one "
        "rather than multiplying the deviation. It is even about slope = 1, "
        "which is a reflection this table's negation kinds cannot express -- "
        "they reflect about zero.",

    # --- SelectionArchitecture ---------------------------------------------
    "Descent.effectCorrelationStabilizing":
        "1 - 1/(2·Ns) is affine in the reciprocal of a single already-compound "
        "argument; the `1` is an anchor, not a scale, and there is no second "
        "argument to trade Ns against.",
    "Descent.fluctuatingSelectedArchitectureVariance":
        "A SUM of the stabilizing equilibrium `v_mut/s` and the OU term "
        "`σ_θ²τ/2`. The two summands are homogeneous of different degrees in "
        "disjoint arguments, so no common factor acts on the sum. Both "
        "components ARE declared separately above, which is the honest split: "
        "the relations belong to the pieces and not to their sum.",
    "Descent.stabilizingNsFromObservedCorrelation":
        "1/(2(1-ρ)) inverts an affine map of a correlation. ρ is bounded and "
        "carries no unit, and the `1` is an anchor.",
    "Descent.sigmaThetaFromObservedSelectedVariance":
        "A square root of a DIFFERENCE of two variances divided by a fitted "
        "timescale. The subtraction blocks homogeneity in the variances -- "
        "scaling both would scale the difference but the timescale is estimated "
        "from a correlation that does not move with them -- and the whole point "
        "of the body is that it inverts a measurement rather than expressing a "
        "law.",
    "Descent.selectionPortabilityTimescale":
        "A wrapper around driftLDCreationRate; the relations belong to that "
        "body rather than to this name. Left undeclared here on purpose rather "
        "than duplicating a neighbour's declaration, which would create two "
        "entries that must be kept in step by hand.",

    "Descent.selectionMigrationEquilibriumMigrationFirst":
        "The same max-0 clip as the selection-first ordering, and the same "
        "consequence: on the half of the domain where migration overwhelms "
        "selection the body is constant at zero, so every scaling relation "
        "holds there vacuously and fails off it. Additionally the extra "
        "(1 - m) in the divisor is exactly what distinguishes this ordering "
        "from the other, so a relation shared by both would be blind to the "
        "one difference the pair exists to express.",
}

# ---------------------------------------------------------------------------
# IN A SWEPT MODULE BUT NOT EXECUTABLE
# ---------------------------------------------------------------------------

NOT_EXTRACTABLE = {
    # The liability-threshold family in PortabilityDrift. Every one of them
    # routes through `Phi`, the standard normal CDF, or through
    # `Function.invFun Phi`, its inverse -- and `extract/api.py` carries `Phi`
    # only as a NUMERIC STAND-IN (an erf form substituted for Mathlib's
    # measure-theoretic `cdf (gaussianReal 0 1)`), while `invFun` is a
    # noncomputable choice function with no numeric form at all. So these six
    # cannot be executed, and a relation declared for them could never run.
    #
    # This is a real coverage hole and it is stated rather than hidden: the
    # liability-scale AUC chain is the corpus's route from an explained R² to a
    # clinical discrimination number, and NOTHING in the empirical tier can
    # evaluate it. The gate's stale-excuse check will report each of these the
    # moment extraction reaches them.
    "Descent.liabilityThreshold":
        "`Function.invFun Phi (1 - K)`: a noncomputable inverse of the normal "
        "CDF. There is no numeric form, so no relation can be evaluated.",
    "Descent.liabilityCaseMean":
        "Routes through liabilityThreshold, so it inherits the inverse-CDF gap.",
    "Descent.liabilityControlMean":
        "Routes through liabilityCaseMean; same inverse-CDF gap.",
    "Descent.liabilityCaseVariance":
        "Routes through liabilityCaseMean and liabilityThreshold; same gap.",
    "Descent.liabilityControlVariance":
        "Routes through liabilityControlMean and liabilityThreshold; same gap.",
    "Descent.liabilityThresholdAUCFromExplainedR2":
        "Composes the whole liability family under `Phi`; same gap. This is the "
        "one a consumer actually calls, which is what makes the hole matter.",
    # PGSCalibrationTheory's two screening-utility wrappers. Both route through
    # a ScreeningDecisionModel structure argument that `extract/api.py` builds no
    # numeric inhabitant for, so no relation can be evaluated for either.
    "Descent.screeningQalyGain":
        "Routes through `screeningUtilityFromRates` applied to a "
        "`qalyScreeningDecisionModel` STRUCTURE, and the extraction has no "
        "numeric inhabitant for it. Not evaluable, so no relation can run.",
    "Descent.decisionCurveNetBenefit":
        "Routes through `screeningUtilityFromCounts` applied to a "
        "`decisionCurveScreeningModel` structure; same extraction gap.",

    "Descent.targetLiabilityAUCFromNeutralAFBenchmark":
        "Composes liabilityThresholdAUCFromExplainedR2 with presentDayR2, so it "
        "inherits the gap from the liability half while the F_ST half is "
        "perfectly executable.",

    # Below: empty of stale excuses. The gate checks this stays honest in both
    # directions -- an
    # entry here whose definition CAN now be executed is reported as a STALE
    # EXCUSE, which is how the four `ploidy` entries that used to live here were
    # retired. An excuse that outlives its cause is indistinguishable from a
    # decision not to look.
}

# ---------------------------------------------------------------------------
# CROSS-BODY AGREEMENTS: two definitions the corpus PROVES equal, executed.
#
# A proved equality in Lean constrains the two bodies as mathematics. It does
# not check that the two TRANSCRIPTIONS every empirical checker consumes still
# agree, and it is exactly the pairs that are proved equal whose divergence
# nobody would think to look for. Each entry names the Lean theorem, so a reader
# can see that this is executing a proof rather than inventing a claim.
# ---------------------------------------------------------------------------

AGREEMENTS = [
    # An optional FIFTH element permutes the right body's arguments onto the
    # left's. Needed because two definitions can be the same function with their
    # arguments in a different order, and comparing those positionally would
    # manufacture a disagreement out of the ORDER and report it as a divergence
    # of the bodies.
    ("Descent.multiTraitEffectiveSampleSize",
     "Descent.multiAncestryEffectiveN",
     "GeneticArchitectureDiscovery.multiTraitEffectiveSampleSize_eq_multiAncestryEffectiveN",
     "Borrowing across TRAITS and borrowing across ANCESTRIES are the same "
     "inverse-variance arithmetic, and the corpus proves it unrestrictedly. The "
     "prior-variance term was derived on the ancestry side -- it is what "
     "reproduces the cells the old body missed by 2.3%, 5.0%, 12% and 31% -- and "
     "BayesianPGSTheory says of the trait-side body, in as many words, that it "
     "'is the SAME formula and inherits this'. The two are the same expression "
     "up to the name and ORDER of their arguments, which is exactly why both "
     "names are kept and why this entry needs the permutation below: they are "
     "MEASURED separately, against different designs, and this is what catches "
     "them drifting apart. One arity change was repaired twice in opposite "
     "directions today and left main with a three-argument call against a "
     "four-argument definition; that is the failure this executes against.",
     (0, 2, 1, 3)),

    # PROVED EQUAL BY NOBODY. These two are pointwise identical and no theorem
    # relates them, which makes them a FORK: two names for one body, free to
    # drift with nothing watching. The F_ST family cost this corpus three
    # separate repairs for exactly that reason. Recorded here so the divergence
    # is caught even though the corpus has not claimed the equality -- and the
    # theorem field says so rather than naming a proof that does not exist.
    ("Descent.brierFromR2", "Descent.sourceBrierFromR2",
     "NO THEOREM RELATES THESE (recorded as a fork, not as a proved equality)",
     "Both are `TransportedMetrics.calibratedBrier π r2` with the same argument "
     "order, in the same module, differing only in whether the R² is called the "
     "source's. Nothing in the corpus states they are equal, so nothing would "
     "notice if one were corrected and the other left behind -- which is the "
     "precise shape of the alleleFreqMismatchPenalty repair earlier today, where "
     "one body was fixed and two callers had to be decoupled by hand. If the "
     "distinction is real, one of them should carry the source-specific content "
     "that justifies the second name; if it is not, one should be deleted.",
     None),

    # THE `oneMinusRatio` FAMILY. `Conventions.oneMinusRatio a b = 1 - a/b` is a
    # NAMED PRIMITIVE with ZERO consumers -- it appears nowhere in the corpus
    # outside its own file -- while at least four definitions independently
    # reimplement it. That is the fork pattern at its clearest: one canonical
    # name nobody calls, and four copies free to drift from it and from each
    # other.
    #
    # Related rather than collapsed, which is the corpus's own doctrine:
    # identical arithmetic is not identical meaning, so each keeps its name and
    # can be measured separately, and these entries are what catch them moving
    # apart. Relating them also gives the primitive the consumers it lacked.
    #
    # None of the four is PROVED equal to the primitive, so the theorem field
    # records the absence rather than naming a proof. A Lean theorem for each
    # would be strictly better and is blocked on an import-graph question:
    # `Conventions` sits DOWNSTREAM (it imports GeneticArchitectureDiscovery,
    # AssortativeMatingPGS and seven more), so the theorems cannot live beside
    # the primitive without pulling those modules into the importers, and
    # cannot live beside each consumer without those importing Conventions.
    # Whoever resolves that should replace these four entries with proofs.
    ("Descent.oneMinusRatio", "Descent.r2FromMSE",
     "NO THEOREM RELATES THESE (recorded as a fork, not as a proved equality)",
     "`1 - mse/varY` IS `oneMinusRatio mse varY`, argument for argument. R² from "
     "mean squared error is the primitive read with an outcome variance as the "
     "denominator, and nothing in the corpus says so.",
     None),
    ("Descent.oneMinusRatio", "Descent.fstFromHetRatio",
     "NO THEOREM RELATES THESE (recorded as a fork, not as a proved equality)",
     "`1 - H/H₀` IS `oneMinusRatio H H₀`. This is the F_ST-from-heterozygosity "
     "form, and the F_ST family is where this corpus has paid most for "
     "unrelated duplicates -- three separate repairs, including a Nei body "
     "living under the name hudsonFst.",
     None),
    ("Descent.oneMinusRatio", "Descent.hudsonFstFromCoalescenceTimes",
     "NO THEOREM RELATES THESE (recorded as a fork, not as a proved equality)",
     "`1 - ETss/ETst` IS `oneMinusRatio ETss ETst`. Hudson's F_ST from "
     "coalescence times is the same primitive again, in the same family as the "
     "entry above and with the same history behind it.",
     None),
    ("Descent.oneMinusRatio", "Descent.pcTargetAxisEfficacy",
     "NO THEOREM RELATES THESE (recorded as a fork, not as a proved equality)",
     "`1 - residual/uncorrected` is `oneMinusRatio` with its two arguments "
     "TRANSPOSED -- the numerator is the second parameter here and the first "
     "there. Exactly the case that would have been reported as a body "
     "divergence before this table supported argument permutations, and a "
     "concrete reason that support is not a convenience.",
     (1, 0)),

    ("Descent.neiGst", "Descent.neiGstFromFrequencies",
     "Conventions.neiGstFromFrequencies_eq_neiGst",
     "The corpus's two spellings of Nei's G_ST: `1 - H_S/H_T` and "
     "`(p₁-p₂)²/(4 p̄(1-p̄))`. This pair could not be executed at all until the "
     "nullary-def extraction fix, and it is the pair whose FLOATING-POINT "
     "behaviour differs by eleven orders of magnitude as p₁ -> p₂ (see "
     "precision/precision_map.py). On the benign grid used here they must agree "
     "to rounding; that they do is what localises the precision finding to the "
     "cancellation rather than to a disagreement between the bodies.",
     None),
]
