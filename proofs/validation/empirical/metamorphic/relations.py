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


# ---------------------------------------------------------------------------
# SWEPT MODULES
# ---------------------------------------------------------------------------

SWEPT_MODULES = (
    "Calibrator/Conventions.lean",
    "Calibrator/PopulationGeneticsFoundations.lean",
    "Calibrator/AncestrySpecificPower.lean",
    "Calibrator/GeneticArchitectureDiscovery.lean",
    "Calibrator/BlindnessRegistry.lean",
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
        jointly_scales(["n₁", "n₂"], 1),
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
}

# ---------------------------------------------------------------------------
# PINNED EXPECTED VIOLATIONS -- checked in BOTH directions
# ---------------------------------------------------------------------------

EXPECTED_VIOLATIONS = {
    ("Calibrator.multiTraitEffectiveSampleSize", "swap/n₁<->n₂"):
        "n₁ + rg²·n₂ is deliberately NOT symmetric: n₁ is the target trait's "
        "own sample and enters undiscounted, while the second trait's sample is "
        "discounted by the squared genetic correlation. A body symmetric in the "
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
    # Empty, and the gate checks that it stays honest in both directions: an
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
