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
    "Calibrator/Conventions.lean",
    "Calibrator/PopulationGeneticsFoundations.lean",
    "Calibrator/AncestrySpecificPower.lean",
    "Calibrator/GeneticArchitectureDiscovery.lean",
    "Calibrator/BlindnessRegistry.lean",
    "Calibrator/TransferLearningPGS.lean",
    "Calibrator/Permeability.lean",
    "Calibrator/PortabilityDrift.lean",
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
    "Calibrator.neiGst": [
        invariant_under_allele_swap(["p₁", "p₂"]),
        symmetric_in("p₁", "p₂"),
    ],
    "Calibrator.hweGenotypeVariance": [
        invariant_under_allele_swap(["p"]),
    ],
    "Calibrator.coalescentTimeScale": [
        scales("Ne", 1),
    ],
    "Calibrator.neiContrastSpike": [
        invariant_under_allele_swap(["p₁", "p₂"]),
        symmetric_in("p₁", "p₂"),
    ],
    "Calibrator.meanAlleleFreq": [
        complement_under_allele_swap(["p₁", "p₂"]),
        symmetric_in("p₁", "p₂"),
        jointly_scales(["p₁", "p₂"], 1),
    ],
    "Calibrator.hudsonFst": [
        invariant_under_allele_swap(["p₁", "p₂"]),
        symmetric_in("p₁", "p₂"),
    ],
    "Calibrator.betweenSubgroupVariance": [
        invariant_under_allele_swap(["p₁", "p₂"]),
        symmetric_in("p₁", "p₂"),
        jointly_scales(["p₁", "p₂"], 2),
    ],
    "Calibrator.hudsonBbpSpike": [
        invariant_under_allele_swap(["p₁", "p₂"]),
        symmetric_in("p₁", "p₂"),
    ],
    "Calibrator.convexMix": [
        jointly_scales(["x", "y"], 1),
        odd_under_negation(["x", "y"]),
    ],
    "Calibrator.oneMinusRatio": [
        jointly_scales(["a", "b"], 0),
    ],
    "Calibrator.retainedFraction": [
        scales("total", 1),
    ],

    # --- PopulationGeneticsFoundations ------------------------------------
    "Calibrator.neiFst": [
        # A ratio of heterozygosities: the unit of heterozygosity cancels.
        jointly_scales(["H_T", "H_S"], 0),
    ],
    "Calibrator.neiGstFromFrequencies": [
        invariant_under_allele_swap(["p₁", "p₂"]),
        symmetric_in("p₁", "p₂"),
    ],
    "Calibrator.coalFst": [
        # Time measured in units of Nₑ: the coalescent rescaling relation.
        jointly_scales(["t", "Ne"], 0),
    ],
    "Calibrator.fstFromHetRatio": [
        jointly_scales(["H", "H₀"], 0),
    ],
    "Calibrator.wrightFIT": [
        symmetric_in("f_IS", "f_ST"),
    ],
    "Calibrator.scaledIdentityStep": [
        invariant_under_reciprocal_scaling(["scaledRate"], ["F"]),
    ],
    "Calibrator.expectedNewMutations": [
        scales("θ", 1),
        scales("t", 1),
        jointly_scales(["θ", "t"], 2),
    ],
    "Calibrator.islandFstFiniteDemes": [
        # The process depends on 4·Nₑ·m, not on Nₑ and m separately.
        invariant_under_reciprocal_scaling(["Ne"], ["m"]),
    ],
    "Calibrator.fstMigrationMutationEquilibriumManyDemes": [
        invariant_under_reciprocal_scaling(["Ne"], ["m", "μ"]),
    ],
    "Calibrator.fstIslandEquilibriumFiniteDemes": [
        invariant_under_reciprocal_scaling(["Ne"], ["m", "μ"]),
    ],
    "Calibrator.fstMutationDriftTransient": [
        # The plateau is set by θ alone; the approach is in units of Nₑ.
        jointly_scales(["t", "Ne"], 0),
    ],
    "Calibrator.steppingStoneCharacteristicLength": [
        scales("m", Q(1, 2)),
        scales("σ_sq", Q(1, 2)),
        scales("μ", Q(-1, 2)),
    ],

    # --- AncestrySpecificPower --------------------------------------------
    "Calibrator.genotypeVarianceHWE": [
        invariant_under_allele_swap(["p"]),
    ],
    "Calibrator.hweHeterozygosity": [
        invariant_under_allele_swap(["p"]),
    ],
    "Calibrator.ncp": [
        scales("β", 2),
        scales("n_eff", 1),
    ],
    "Calibrator.portableFraction": [
        jointly_scales(["r2_causal", "r2_total"], 0),
    ],
    "Calibrator.proportionalAllocation": [
        jointly_scales(["pop_size", "total_pop"], 0),
        scales("total_n", 1),
    ],

    # --- GeneticArchitectureDiscovery -------------------------------------
    "Calibrator.discoveryNCP": [
        # Mirrors the Lean theorems discoveryNCP_allele_swap / _scale_effect /
        # _scale_ld / _scale_n.  Proved there, executed here: the Lean statement
        # constrains the body, this constrains the transcription of the body
        # that every other empirical checker consumes.
        invariant_under_allele_swap(["maf_causal"], effect_args=["β"]),
        scales("β", 2),
        scales("ld", 2),
        scales("n", 1),
    ],
    "Calibrator.multiTraitDiscoveryNCP": [
        invariant_under_allele_swap(["maf"], effect_args=["β"]),
        scales("β", 2),
        scales("ld", 2),
    ],
    "Calibrator.multiTraitEffectiveSampleSize": [
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
    "Calibrator.expectedLinearEffectEstimate": [
        odd_under_negation(["β_true", "meanEstimationError"]),
        jointly_scales(["β_true", "meanEstimationError"], 1),
    ],
    "Calibrator.olsEffectEstimationVariance": [
        scales("σ2", 1),
        scales("varX", -1),
        scales("n", -1),
    ],
    "Calibrator.perCausalLocusSignal": [
        jointly_scales(["h2", "k"], 0),
    ],
    "Calibrator.geneticCorrelation": [
        scales("cov_g", 1),
        # cov / sqrt(vg₁·vg₂): scaling BOTH variances by c divides by c, not by
        # sqrt(c) -- the square root is taken of the product, so the two factors
        # of c combine before it. Declared as -1/2 on first writing and caught
        # by this gate, which is the cheapest evidence that it evaluates.
        jointly_scales(["vg₁", "vg₂"], -1),
        symmetric_in("vg₁", "vg₂"),
    ],

    # --- BlindnessRegistry -------------------------------------------------
    "Calibrator.pairwiseCoalescentSurvival": [
        # Survival depends on the compound lam·t, so time units cancel.
        invariant_under_reciprocal_scaling(["lam"], ["t"]),
    ],

    # --- TransferLearningPGS ----------------------------------------------
    "Calibrator.pgsR2": [
        scales("cov_pgs_y", 2),
        scales("var_pgs", -1),
        scales("var_y", -1),
    ],
    "Calibrator.benDavidUpperBound": [
        jointly_scales(["err_source", "divergence", "lambda_star"], 1),
        symmetric_in("err_source", "divergence"),
    ],
    "Calibrator.importanceWeightESS": [
        scales("sum_w", 2),
        scales("sum_w_sq", -1),
    ],
    "Calibrator.pcaSignalLossPenalty": [
        scales("lossWeight", 1),
        jointly_scales(["signalBaseline", "signalRetained"], 1),
    ],
    "Calibrator.pcaBiasReduction": [
        jointly_scales(["ancestryBiasWith", "ancestryBiasWithout"], 1),
        odd_under_negation(["ancestryBiasWith", "ancestryBiasWithout"]),
    ],
    "Calibrator.pcaNetTargetError": [
        jointly_scales(["ancestryBias", "signalBaseline", "signalRetained"], 1),
    ],
    "Calibrator.infoBottleneckObjective": [
        jointly_scales(["I_phi_Y", "I_phi_A"], 1),
        odd_under_negation(["I_phi_Y", "I_phi_A"]),
    ],
    "Calibrator.pinskerAncestryDivergenceCap": [
        scales("I_phi_A", Q(1, 2)),
    ],
    "Calibrator.fineTunedTargetR2": [
        jointly_scales(["r2_source", "divergence_penalty", "adaptation_gain"], 1),
        odd_under_negation(["r2_source", "divergence_penalty",
                            "adaptation_gain"]),
    ],
    "Calibrator.scratchTargetR2": [
        jointly_scales(["oracle_target_r2", "estimation_penalty"], 1),
        odd_under_negation(["oracle_target_r2", "estimation_penalty"]),
    ],
    "Calibrator.deployedTransferTargetR2": [
        jointly_scales(["transported_r2", "adaptation_gain",
                        "estimation_penalty"], 1),
    ],
    "Calibrator.oracleTransportAdaptationGain": [
        jointly_scales(["transported_r2", "oracle_target_r2"], 1),
        odd_under_negation(["transported_r2", "oracle_target_r2"]),
    ],
    "Calibrator.transportPenalty": [
        jointly_scales(["source_r2", "transported_r2"], 1),
        odd_under_negation(["source_r2", "transported_r2"]),
    ],
    "Calibrator.sampleLimitedScratchTargetR2": [
        # noiseVar and nTarget enter only through their ratio.
        jointly_scales(["noiseVar", "nTarget"], 0),
    ],
    "Calibrator.sourceShrinkageMSE": [
        jointly_scales(["noiseVar", "nTarget"], 0),
    ],
    "Calibrator.optimalSourceShrinkageWeight": [
        # A weight, so it is scale-free in the risks; and the sample size enters
        # only through noiseVar/nTarget.
        jointly_scales(["gapSq", "noiseVar"], 0),
        jointly_scales(["noiseVar", "nTarget"], 0),
    ],
    "Calibrator.optimalFineTuningMSE": [
        jointly_scales(["gapSq", "noiseVar"], 1),
        jointly_scales(["noiseVar", "nTarget"], 0),
    ],
    "Calibrator.requiredTargetSamplesForOptimalFineTuningMSE": [
        scales("noiseVar", 1),
        jointly_scales(["gapSq", "tau"], -1),
    ],
    "Calibrator.privateArchitectureTransferCeiling": [
        scales("h2_target", 1),
    ],
    "Calibrator.scratchVsFineTuningCriticalSampleSize": [
        scales("noiseVar", 1),
    ],

    # --- Permeability ------------------------------------------------------
    "Calibrator.scalarPermeability": [
        # A squared LOG-derivative, so the covariance's unit cancels.
        jointly_scales(["covariance", "covarianceDerivative"], 0),
        scales("covarianceDerivative", 2),
        scales("covariance", -2),
    ],
    "Calibrator.momentPermeability": [
        scales("response", 2),
        scales("noiseVariance", -1),
    ],
    "Calibrator.covarianceMomentPermeability": [
        scales("covarianceDerivative", 2),
    ],
    "Calibrator.replicatesForEqualPermeability": [
        scales("sourceReplicates", 1),
        jointly_scales(["sourcePermeability", "targetPermeability"], 0),
    ],
    "Calibrator.twoChannelMomentNoiseDet": [
        jointly_scales(["firstNoise", "secondNoise", "sharedNoise"], 2),
    ],
    "Calibrator.twoChannelConditionalMomentNoise": [
        jointly_scales(["firstNoise", "secondNoise", "sharedNoise"], 1),
    ],
    "Calibrator.twoChannelConditionalMomentResponse": [
        jointly_scales(["firstResponse", "secondResponse"], 1),
        jointly_scales(["firstNoise", "sharedNoise"], 0),
        odd_under_negation(["firstResponse", "secondResponse"]),
    ],
    "Calibrator.twoChannelMomentInnovationInformation": [
        jointly_scales(["firstResponse", "secondResponse"], 2),
    ],
    "Calibrator.informationPerUnitCost": [
        jointly_scales(["information", "cost"], 0),
        scales("information", 1),
        scales("cost", -1),
    ],
    "Calibrator.informationAtBudget": [
        scales("budget", 1),
        jointly_scales(["information", "cost"], 0),
    ],
    "Calibrator.totalGaussianInformation": [
        scales("m", 1),
        jointly_scales(["covariance", "covarianceDerivative"], 0),
    ],
    "Calibrator.totalCovarianceMomentInformation": [
        scales("m", 1),
        scales("covarianceDerivative", 2),
    ],
    "Calibrator.totalBinaryOrientationArrowPermeability": [
        scales("m", 1),
    ],
    "Calibrator.covarianceTangentEstimatorVarianceFromMoments": [
        scales("m", -1),
        scales("covarianceDerivative", -2),
    ],
    "Calibrator.gaussianCovarianceTangentEstimatorVariance": [
        scales("m", -1),
    ],
    "Calibrator.gaussianCovarianceHalfSquaredRisk": [
        scales("m", -1),
    ],
    "Calibrator.quadraticChannel": [
        scales("θ", 2),
    ],
    "Calibrator.covarianceScoreInformationFromMoments": [
        scales("covarianceDerivative", 2),
        scales("covariance", -4),
    ],

    # --- PortabilityDrift --------------------------------------------------
    # The corpus's largest scalar module. Its recurring structure is that
    # quantities depend on COMPOUND parameters -- 4·Nₑ·m, t/Nₑ, a variance ratio
    # -- and the relations below are what pin the compound rather than the
    # factors, which is the one thing a per-argument monotonicity result cannot
    # do.
    "Calibrator.coalescentTau": [
        jointly_scales(["t", "Ne"], 0),
        scales("t", 1),
        scales("Ne", -1),
    ],
    "Calibrator.fstFromGenerations": [
        jointly_scales(["t", "Ne"], 0),
    ],
    "Calibrator.pairwiseFstFromBranches": [
        symmetric_in("fstS", "fstT"),
    ],
    "Calibrator.pairwiseFstFromBranchTaus": [
        symmetric_in("tauS", "tauT"),
    ],
    "Calibrator.hudsonFstFromCoalescenceTimes": [
        # A ratio of coalescence times: the unit of time cancels.
        jointly_scales(["ETss", "ETst"], 0),
    ],
    "Calibrator.hetMutationFloor": [
        # Depends on 4·Nₑ·μ alone.
        invariant_under_reciprocal_scaling(["Ne"], ["mu"]),
    ],
    "Calibrator.pgsVarianceFromHet": [
        symmetric_in("β_sq_sum", "het"),
        jointly_scales(["β_sq_sum", "het"], 2),
        scales("β_sq_sum", 1),
    ],
    "Calibrator.targetHetFromFst": [
        scales("het_source", 1),
    ],
    "Calibrator.presentDayPGSVariance": [
        scales("V_A", 1),
    ],
    "Calibrator.Var_Delta_Mu": [
        scales("V_A", 1),
        scales("fst", 1),
        jointly_scales(["V_A", "fst"], 2),
    ],
    "Calibrator.Expected_Abs_Shift": [
        # A standard deviation, so half a power of the variance.
        scales("V_A", Q(1, 2)),
        symmetric_in("fstS", "fstT"),
    ],
    "Calibrator.presentDaySignalToNoise": [
        jointly_scales(["V_A", "V_E"], 0),
        scales("V_A", 1),
        scales("V_E", -1),
    ],
    "Calibrator.presentDayR2": [
        jointly_scales(["V_A", "V_E"], 0),
    ],
    "Calibrator.presentDayEqualVarianceGaussianAUC": [
        jointly_scales(["V_A", "V_E"], 0),
    ],
    "Calibrator.realWorldPGSVariance": [
        scales("V_A", 1),
        scales("rhoSq", 1),
        jointly_scales(["V_A", "rhoSq"], 2),
    ],
    "Calibrator.ldCorrelationDecay": [
        # The decay reads only the products lambda·distance and lambda·fstGap.
        invariant_under_reciprocal_scaling(["distance"], ["lambda"]),
        invariant_under_reciprocal_scaling(["fstGap"], ["lambda"]),
    ],
    "Calibrator.alleleFreqMismatchPenalty": [
        # An absolute frequency difference: symmetric in the two panels AND
        # invariant under relabelling which allele is reference, since the
        # complement subtracts out.
        symmetric_in("pSource", "pTarget"),
        invariant_under_allele_swap(["pSource", "pTarget"]),
    ],
    "Calibrator.targetR2FromNeutralAFBenchmark": [
        jointly_scales(["V_A", "V_E"], 0),
    ],
    "Calibrator.targetExactCalibratedBrierRisk": [
        jointly_scales(["V_A", "V_E"], 0),
    ],
    "Calibrator.targetBrierFromNeutralAFBenchmark": [
        jointly_scales(["V_A", "V_E"], 0),
    ],
    "Calibrator.standardNormalPdf": [
        even_under_negation(["x"]),
    ],
    "Calibrator.brierRegretPoint": [
        # The Brier regret is the squared forecast deviation, so it is quadratic
        # in the pair and EVEN in it -- a body carrying a stray linear term
        # would still be zero on the diagonal and still monotone away from it.
        jointly_scales(["η", "q"], 2),
        even_under_negation(["η", "q"]),
    ],
    "Calibrator.brierRegretRatio": [
        jointly_scales(["η", "qSource", "qTarget"], 0),
    ],
    "Calibrator.expectedSqMeanPGSDiff_pureSplit": [
        scales("V_A", 1),
        symmetric_in("fstS", "fstT"),
        jointly_scales(["fstS", "fstT"], 1),
    ],
    "Calibrator.expectedSqMeanPGSDiff_IMEquilibrium": [
        scales("V_A", 1),
    ],
    "Calibrator.covarianceRetention": [
        symmetric_in("freq_corr", "ld_overlap"),
        jointly_scales(["freq_corr", "ld_overlap"], 2),
    ],
    "Calibrator.alleleFreqCorrelation": [
        # A variance ratio: only the ratio of ancestral variance to F_ST-weighted
        # heterozygosity matters, so both a common rescaling and a reciprocal
        # trade between F_ST and the heterozygosity leave it alone.
        jointly_scales(["varAncestral", "meanHetAncestral"], 0),
        invariant_under_reciprocal_scaling(["fst"], ["meanHetAncestral"]),
    ],
    "Calibrator.ldOverlapFromSharedLD": [
        scales("shared_ld", 1),
    ],
    "Calibrator.presentDayPGSVarianceMutationDrift": [
        scales("V_A", 1),
    ],
    "Calibrator.presentDayR2MutationDrift": [
        jointly_scales(["V_A", "V_E"], 0),
    ],
    "Calibrator.neutralAFSharedLDBenchmarkRatio": [
        jointly_scales(["shared_ld_source", "shared_ld_target"], 0),
    ],
    "Calibrator.fstMigrationDriftEquilibrium": [
        invariant_under_reciprocal_scaling(["Ne"], ["m"]),
    ],
    "Calibrator.sharedLD_from_equilibrium": [
        invariant_under_reciprocal_scaling(["Ne"], ["m"]),
    ],
    "Calibrator.signalRetentionMigrationDrift": [
        invariant_under_reciprocal_scaling(["Ne"], ["m"]),
    ],
    "Calibrator.retainedSignalVarianceMigrationDrift": [
        scales("V_A", 1),
        invariant_under_reciprocal_scaling(["Ne"], ["m"]),
    ],
    "Calibrator.neutralAFBenchmarkFromRecurrence": [
        invariant_under_reciprocal_scaling(["Ne"], ["m"]),
    ],
    "Calibrator.asymmetricFst": [
        # Only the SUM of the two directional rates enters, which is the whole
        # content of the name: asymmetric migration gives a symmetric F_ST.
        symmetric_in("m₁₂", "m₂₁"),
        invariant_under_reciprocal_scaling(["Ne"], ["m₁₂", "m₂₁"]),
    ],
    "Calibrator.effectiveSymmetricMigration": [
        symmetric_in("m₁₂", "m₂₁"),
        jointly_scales(["m₁₂", "m₂₁"], 1),
    ],
}

# ---------------------------------------------------------------------------
# PINNED EXPECTED VIOLATIONS -- checked in BOTH directions
# ---------------------------------------------------------------------------

EXPECTED_VIOLATIONS = {
    ("Calibrator.multiTraitEffectiveSampleSize", "swap/n₁<->n₂"):
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
    "Calibrator.expectedHeterozygosity":
        "θ/(1+θ) is a saturating map of a single already-dimensionless scaled "
        "parameter. Scaling θ changes the answer -- that is its content -- and "
        "there is no second argument to trade against it.",
    "Calibrator.islandDemeCorrection":
        "d/(d-1) is a pure deme-count correction. d is a cardinality, so there "
        "is no unit to rescale and no second argument to exchange it with.",
    "Calibrator.ldCorrelationMigrationAnsatz":
        "M²/(1+M)² is a saturating function of the single scaled migration "
        "parameter; the compound is already formed, so nothing is left to hold "
        "fixed against it.",
    "Calibrator.hetDecayFactor":
        "(1 - 1/(2Nₑ))(1 - θ/(2Nₑ)) has Nₑ appearing in two channels with "
        "different numerators, so no rescaling of Nₑ against θ leaves it fixed. "
        "The absence is the content: drift and mutation do not trade off.",
    "Calibrator.continentIslandStepSelectionFirst":
        "One generation of a nonlinear selection-migration recursion. Rescaling "
        "s or m moves the fixed point rather than reparametrising the step, and "
        "the two orderings below are precisely NOT interchangeable.",
    "Calibrator.continentIslandStepMigrationFirst":
        "As above. That this body and the selection-first one are different "
        "functions is the point of the pair; neither has a symmetry of its own.",
    "Calibrator.selectionMigrationEquilibrium":
        "max 0 ((s - m - m·s)/s) is clipped at zero, so it is not homogeneous "
        "in any argument: the clip destroys every scaling relation on the half "
        "of the domain where it binds, and a relation that holds only off the "
        "clip is not a relation.",
    "Calibrator.gaussianSourceResidualRisk":
        "exp(-2·I) turns an information into a risk, so no rescaling of I is a "
        "rescaling of the output: the relation it does satisfy is "
        "f(a+b) = f(a)·f(b), a functional equation rather than a homogeneity, "
        "and this table's kinds are all homogeneities and symmetries.",
    "Calibrator.infoCertifiedBenDavidUpperBound":
        "A sum of an exponential, a square root and a linear term in three "
        "different arguments. Each summand has a different degree, so no common "
        "scaling acts on the whole; the per-argument relations belong to the "
        "three components, which are declared separately above.",
    "Calibrator.usableScratchTargetR2":
        "max 0 of the sample-limited R², so the clip destroys every scaling "
        "relation on the half of the domain where it binds. A relation that "
        "holds only off the clip is not a relation, which is why the unclipped "
        "sampleLimitedScratchTargetR2 carries the declaration instead.",
    "Calibrator.centeredSquareVarianceFromMoments":
        "m₄ - m₂² is Var(X²) from RAW moments, and the two arguments scale at "
        "different rates under the only transformation that matters: scaling "
        "the underlying variable by s sends m₂ to s²m₂ and m₄ to s⁴m₄. No "
        "single common factor acts on both, so no scaling relation in this "
        "table's vocabulary can express the one relation it does have.",
    "Calibrator.binaryOrientationArrowPermeability":
        "A one-argument function of an orientation angle through a variance "
        "that is not homogeneous in it; θ is an angle, so there is no unit to "
        "rescale and no second argument to hold against it.",
    "Calibrator.threeCycleOrientationArrowPermeability":
        "As the binary case: a fixed response over 1 - θ², with θ an angle "
        "carrying no unit. The constants are pinned by reference-point "
        "theorems in the module rather than by any invariance.",
    # --- PortabilityDrift --------------------------------------------------
    "Calibrator.fstFromTau":
        "tau/(1+tau) saturates a single already-scaled coalescent time. Scaling "
        "tau changes the answer -- that is its content -- and there is no "
        "second argument to trade against it. Its rescaling invariance lives in "
        "fstFromGenerations, which does take t and Ne separately.",
    "Calibrator.twoDemeIMFirstStepSame":
        "One step of a two-deme island recursion, affine in ETst with an "
        "M-dependent intercept AND an M-dependent slope. It is affine, not "
        "homogeneous, so no scaling of any argument multiplies the output.",
    "Calibrator.twoDemeIMFirstStepDiff":
        "1/M + ETss adds a reciprocal rate to a time. The two summands have "
        "opposite degrees in any common rescaling, so no single factor acts on "
        "the sum; that they nonetheless share units is a statement about the "
        "coalescent scaling and not about this body.",
    "Calibrator.twoDemeIMEquilibriumETss":
        "Constant at 2: two lineages in the same deme coalesce in two "
        "population-size units whatever the migration rate, which is why the "
        "argument is named `_M` and ignored. A constant satisfies every "
        "invariance vacuously, which is exactly why it must not be declared "
        "with one -- the vacuity screen in run.py would fire, and correctly.",
    "Calibrator.twoDemeIMEquilibriumETst":
        "(2M+1)/M is a ratio of terms of different degree in M, so it is not "
        "homogeneous; and M is already the scaled migration rate, so there is "
        "no unit left to cancel against it.",
    "Calibrator.twoDemeIMEquilibriumDelta":
        "1/(2M+1) in the single scaled migration parameter, saturating rather "
        "than homogeneous. Same reason as fstFromTau one entry up.",
    "Calibrator.hetStepWithMutation":
        "Drift and mutation enter through different powers of Ne and mu with an "
        "additive input term, so no rescaling of Ne against mu holds them "
        "fixed. The absence is the content: unlike hetMutationFloor below, the "
        "STEP is not a function of 4·Ne·mu alone -- only its fixed point is.",
    "Calibrator.brierFromR2":
        "π(1-π)(1-r2) is affine in r2 and quadratic-with-an-intercept in π, so "
        "no argument scales the output. Its content is pinned by reference "
        "evaluations at r2 = 0 and r2 = 1 instead.",
    "Calibrator.sourceBrierFromR2":
        "The same body as brierFromR2 read at the source population; same "
        "reason.",
    "Calibrator.equalVarianceGaussianAUCFromSNR":
        "Phi of a square root: a probability, bounded in [0,1], so no scaling "
        "of the signal-to-noise ratio scales it. Monotone but not homogeneous.",
    "Calibrator.equalVarianceGaussianAUCFromExplainedR2":
        "As above, and additionally clipped by an `if 1 ≤ r2` branch, so any "
        "relation would hold vacuously on the clipped half of the domain and "
        "fail off it. A relation that holds only off a clip is not a relation.",
    "Calibrator.logLossRegretPoint":
        "A difference of logarithms, so scaling the pair scales neither the "
        "argument of the log nor the answer. The Brier regret one floor up IS "
        "quadratic and IS declared, which is the honest contrast: the two "
        "regrets have genuinely different homogeneity.",
    "Calibrator.logLossRegretRatio":
        "A ratio of the above; a common rescaling does not cancel because "
        "neither numerator nor denominator is homogeneous to begin with.",
    "Calibrator.ibdFlowStep":
        "F + (1-F)/(2Ne) - 2·rate·F mixes an input term, a drift term and a "
        "flow term with different degrees in Ne and rate; no common or "
        "reciprocal rescaling fixes it. Its equilibrium does, and that is "
        "fstMigrationDriftEquilibrium.",
    "Calibrator.covarianceRetentionFactorFromFst":
        "1 - fst is an affine map of a quantity already in [0,1]. Not "
        "homogeneous, and F_ST carries no unit to rescale.",
    "Calibrator.covarianceDivergenceFromRetention":
        "1 - (1-fst)·shared_ld: affine in shared_ld with an fst-dependent slope "
        "and a constant intercept, so nothing scales it.",
    "Calibrator.covarianceDivergenceMutationDrift":
        "fst + (1-fst)(1-shared_ld) is affine in each argument separately with "
        "a cross term; the intercept blocks every homogeneity.",
    "Calibrator.finiteIslandCorrection":
        "d/(d-1) is a pure deme-count correction; d is a cardinality, so there "
        "is no unit to rescale and no second argument to exchange with it.",
    "Calibrator.ibdRecurrenceStep":
        "(1-rate)²·(1/(2Ne) + (1-1/(2Ne))·x) carries Ne in two channels with "
        "different numerators and an additive input, so no rescaling of Ne "
        "against rate leaves it fixed.",
    "Calibrator.ibdRecurrenceFixedPoint":
        "(1-rate)²/((1-rate)² + 2Ne·rate·(2-rate)) is NOT a function of the "
        "product Ne·rate alone -- the (2-rate) factor breaks it, which is the "
        "exact respect in which the multiplicative recurrence differs from the "
        "diffusion approximation whose fixed point IS 1/(1+4Ne·m). Declaring a "
        "reciprocal-scaling relation here would assert the approximation.",
    "Calibrator.islandFstMultiplicativeStep":
        "A rename of ibdRecurrenceStep into F_ST language; same reason.",
    "Calibrator.fstIslandMultiplicativeEquilibrium":
        "A rename of ibdRecurrenceFixedPoint; same reason, and the same "
        "instructive contrast with fstMigrationDriftEquilibrium, which IS "
        "declared with the reciprocal-scaling relation because it IS the "
        "diffusion form.",
    "Calibrator.sharedLDFromMigration":
        "M/(1+M) saturates the single scaled migration parameter. The compound "
        "is already formed, so nothing is left to hold fixed against it.",
    "Calibrator.fstMigDriftNext":
        "(1 - 2m - 1/(2Ne))·Fst + 1/(2Ne) is affine in Fst with an additive "
        "input term, so scaling Fst does not scale the output and Ne appears in "
        "both the slope and the intercept.",

    "Calibrator.selectionMigrationEquilibriumMigrationFirst":
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
    "Calibrator.liabilityThreshold":
        "`Function.invFun Phi (1 - K)`: a noncomputable inverse of the normal "
        "CDF. There is no numeric form, so no relation can be evaluated.",
    "Calibrator.liabilityCaseMean":
        "Routes through liabilityThreshold, so it inherits the inverse-CDF gap.",
    "Calibrator.liabilityControlMean":
        "Routes through liabilityCaseMean; same inverse-CDF gap.",
    "Calibrator.liabilityCaseVariance":
        "Routes through liabilityCaseMean and liabilityThreshold; same gap.",
    "Calibrator.liabilityControlVariance":
        "Routes through liabilityControlMean and liabilityThreshold; same gap.",
    "Calibrator.liabilityThresholdAUCFromExplainedR2":
        "Composes the whole liability family under `Phi`; same gap. This is the "
        "one a consumer actually calls, which is what makes the hole matter.",
    "Calibrator.targetLiabilityAUCFromNeutralAFBenchmark":
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
    ("Calibrator.neiGst", "Calibrator.neiGstFromFrequencies",
     "Conventions.neiGstFromFrequencies_eq_neiGst",
     "The corpus's two spellings of Nei's G_ST: `1 - H_S/H_T` and "
     "`(p₁-p₂)²/(4 p̄(1-p̄))`. This pair could not be executed at all until the "
     "nullary-def extraction fix, and it is the pair whose FLOATING-POINT "
     "behaviour differs by eleven orders of magnitude as p₁ -> p₂ (see "
     "precision/precision_map.py). On the benign grid used here they must agree "
     "to rounding; that they do is what localises the precision finding to the "
     "cancellation rather than to a disagreement between the bodies."),
]
