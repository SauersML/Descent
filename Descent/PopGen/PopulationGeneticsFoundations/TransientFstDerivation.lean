/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.PopGen.PopulationGeneticsFoundations.CoalescentTheory
import Descent.PopGen.PopulationGeneticsFoundations.MutationDriftBalance
-- `Portability.hudsonFstFromCoalescenceTimes`, `hetDecayFromScaled` and `r2FromMSE` are
-- named below; the first is Portability's, the others `PopGen.DGP`'s.
import Descent.PopGen.DGP
import Descent.Portability.PortabilityDrift
import Descent.Layer

assert_below Descent.Blindness Descent.Conditionals Descent.Decision

-- LAYER DEBT. This file cannot yet assert it is below `Descent.Spectral`, `Descent.Portability`, `Descent.Program`:
--   Spectral: reaches 2 module(s) -- `Descent.Spectral.CirculationDefect`, `Descent.Spectral.SpectralDegradation`
--   Portability: reaches 10 module(s) -- `Descent.Portability.PortabilityDrift`, `Descent.Portability.PortabilityDrift.ClosedPopulationRegime`, `Descent.Portability.PortabilityDrift.Definitions` and 7 more
--   Program: reaches 1 module(s) -- `Descent.Program.Conclusions`
-- The repair is to move what it reaches for DOWN, not to move this file up.

namespace Descent.PopGen

open MeasureTheory

/-!
# `PopulationGeneticsFoundations.TransientFstDerivation`

Part of the split of `Descent/PopGen/PopulationGeneticsFoundations.lean`, which was 2,740 lines.

The parts are a FAN: each imports the parts that declare the symbols it names, and nothing
else. The split first made them a CHAIN -- each importing the one before, in the order the
original text ran -- which preserved every resolution the single file had and charged every
part a dependency on everything written above it, used or not. Recovering the real order is
the work that chain deferred: each part's identifiers were resolved against its siblings'
declarations, and the imports above are the answer, so what a part rests on is readable
from its header instead of inherited from its position in a file that no longer exists.

Where a cut falls inside a section, the section is reopened and reclosed by name. A section
scopes `variable`s and this file declares none at that level, so the reopening is exact.
-/



/-!
## Derivation of Transient Fst from Heterozygosity Recurrence with Mutation

The discrete-time analogue of `fstMutationDriftTransient` is DERIVED here, not assumed,
from the heterozygosity recurrence that includes both drift and mutation, using only:
1. The recurrence H(t+1) = λ H(t) + c, where λ = (1 - 1/(2N))(1 - θ/(2N))
   and c captures mutation input.
2. The closed-form solution of affine recurrences via geometric series.
3. The equilibrium H* = θ/(1+θ) (already derived above as a fixed point).
4. The definition Fst(t) = 1 - H(t)/H₀.

The key insight: when we approximate (1-μ)² ≈ 1 - 2μ and set θ = 4Nμ,
the per-generation decay factor for heterozygosity becomes
  λ = (1 - 1/(2N)) × (1 - θ/(2N))
and mutation-drift balance yields the transient formula
  Fst(t) = [1/(1+θ)] × (1 - λ^t).
-/

section TransientFstDerivation

/-! ### Heterozygosity recurrence with mutation -/

/-- **Per-generation decay factor under mutation and drift.**
    λ = (1 - 1/(2N)) × (1 - θ/(2N)).
    The first factor is drift (coalescence probability 1/(2N)),
    the second captures the approximate mutation effect:
    two lineages both fail to mutate with probability (1-μ)² ≈ 1 - 2μ = 1 - θ/(2N).

    **This is `Descent.hetDecayFromScaled` applied, not a second copy of its body.
    Do not inline the product `(1 - 1/(2Ne)) * (1 - θ/(2Ne))` here.** Every call site
    unfolds the PAIR `hetDecayFactor hetDecayFromScaled` — including
    `Descent.Program.Conventions` and `Descent.PopGen.DemographicHistory` — and an inlined body
    leaves no `hetDecayFromScaled` in the goal for the second unfold to find. The
    two-name unfold is the contract: inlining breaks five proofs in three files.

    Empirical status: UNTESTED. -/
noncomputable def hetDecayFactor (Ne θ : ℝ) : ℝ :=
  hetDecayFromScaled Ne θ

/-- **Heterozygosity recurrence with mutation (affine recurrence).**
    H(t+1) = λ H(t) + c, where λ = hetDecayFactor and
    c = (1 - λ) H* (since H* is the fixed point, c = (1-λ) H*).
    Rather than tracking c explicitly we parametrise by the equilibrium H*
    and λ, since the affine recurrence H(t+1) = λ H(t) + c has
    fixed point H* = c/(1-λ), i.e. c = (1-λ) H*.

    Empirical status: **VALIDATED**
    (`validation/empirical/simcov/battery_bulk15.py`). Measured against the
    same infinite-alleles trajectories as `hetMutationDriftRecurrence`, with `lam = 1 - 1/(2 Ne) - 2
    mu` and `Hstar = theta/(1 + theta)`, iterated fifteen
    generations from a measured start: worst cell 1.01 sems, 6.5% relative,
    across `theta` of 0.80 and 1.00 and `Ne` of 50, 100 and 200.

    Deliberately NOT compared against the sibling recurrence. The two are the
    same map in different coordinates -- expanding
    `(1 - 1/(2Ne)) H + 2 mu (1 - H)` gives slope `1 - 1/(2Ne) - 2 mu` and
    intercept `2 mu`, and `2 mu / (1/(2Ne) + 2 mu) = theta/(1 + theta)` -- so
    agreement between them is an algebraic identity carrying no empirical weight.
    The battery reports that identity separately and labels it a SELF-TEST. What
    is measured here is the trajectory.

    The `traj` FALSIFIED record, at 44.23 sems, is inherited and not separate.
    `simcov/ledger.json` logs it under regime "lam and Hstar taken from the
    drift-mutation process the affine form abstracts; run forward with no
    re-anchoring" -- and the coefficients it takes are exactly the ones above,
    `lam = 1 - 1/(2 Ne) - 2 mu` and `Hstar = 2 mu / (1/(2 Ne) + 2 mu)`, which are
    the INFINITE-ALLELES coefficients. `battery_traj.py` then runs them against a
    biallelic two-way-mutation oracle. So this row measures the same regime
    mismatch recorded on `hetMutationDriftRecurrence` above, arriving here through
    the coefficients rather than through the body: this affine map is an exact
    reparametrisation and has no mutation model of its own to be wrong about. Feed
    it a biallelic `lam` and `Hstar` and it tracks a biallelic trajectory.

    The engine runs about 1% hot against the known plateau (`H = 0.4489` and
    `0.5044` measured against `theta/(1+theta) = 0.4444` and `0.5000`), which is
    the same systematic `ia_engine.selftest` reports, so it is disclosed rather
    than absorbed: it is a tenth of the gap being resolved here. -/
noncomputable def hetMutationRecurrence (lam Hstar H₀ : ℝ) : ℕ → ℝ
  | 0 => H₀
  | t + 1 => lam * hetMutationRecurrence lam Hstar H₀ t + (1 - lam) * Hstar

/-- **At t = 0, H equals the initial value.** -/
theorem hetMutationRecurrence_zero (lam Hstar H₀ : ℝ) :
    hetMutationRecurrence lam Hstar H₀ 0 = H₀ := by
  rfl

/-- **Closed-form solution of the affine recurrence.**
    H(t) = H* + (H₀ - H*) × λ^t.
    Proof by induction: the base case is trivial, and the step uses
    the fact that the constant term (1-λ)H* absorbs the equilibrium part. -/
theorem hetMutationRecurrence_closed_form (lam Hstar H₀ : ℝ) (t : ℕ) :
    hetMutationRecurrence lam Hstar H₀ t = Hstar + (H₀ - Hstar) * lam ^ t := by
  induction t with
  | zero =>
    simp [hetMutationRecurrence]
  | succ n ih =>
    simp only [hetMutationRecurrence, ih]
    ring

/-! ### Fst from heterozygosity ratio -/

/-- **Transient Fst from heterozygosity ratio.**
    Fst(t) = 1 - H(t)/H₀.

    Regime: closed Wright-Fisher drift, no mutation, no migration, no
    selection. With a mutation floor the ratio does not run to one; see
    `PortabilityDrift.hetMutationFloor`.

    Empirical status: **VALIDATED** (`simcov/battery_bulk21.py`, `group_ab`).
    Two isolated Wright-Fisher demes started at a common frequency, 20000
    replicate pairs, with `H` measured directly as the mean `2p(1-p)` and
    compared against the classical decay `H_t/H₀ = (1 - 1/(2Nₑ))ᵗ` -- a
    prediction derived independently of this body, so what is on trial is
    whether the heterozygosity ratio is the drift `F` and not merely whether
    two transcriptions of one formula agree. Over `Nₑ` = 50, 100, 200 and `t` =
    40, 60, 120, 200 the measured ratio gives 0.18125, 0.18109, 0.25736,
    0.45429 and 0.63124 against the classical 0.18168, 0.18168, 0.25946,
    0.45284 and 0.63304, worst cell 0.98 sems at 0.28% relative, over a
    prediction spanning 71%. `Nₑ` and `t` are moved separately, so the two
    cells that reach `F ≈ 0.18` by different routes both have to hold.

    Caution, recorded because this battery walked into it: `driftVariance` and
    `expectedFreqDiffSq` compared against the SAME simulated trajectories are
    NOT independent measurements of anything. Given only the martingale
    property `E[p_t] = p₀`, `p₀(1-p₀)(1 - H_t/H₀)` reduces identically to
    `Var(p_t)`, so those comparisons return the drift model's own algebra and
    scored MATCH at 0.00 sems in three cells. The heterozygosity decay above is
    the only one of the four that a simulation can refute. -/
noncomputable def fstFromHetRatio (H H₀ : ℝ) : ℝ :=
  Descent.Core.proportionalReduction H H₀

/-- **fstFromHetRatio where its denominator vanishes, named.** The guard `H₀` is zero at `H₀ = 0`.
Lean returns `1` there rather than the value the modelled quantity takes, and no type error
marks the point. Consumers must require `H₀ ≠ 0`. -/
theorem fstFromHetRatio_at_h0_is_junk (H : ℝ) :
    fstFromHetRatio H 0 = 1 := by
  unfold fstFromHetRatio Descent.Core.proportionalReduction
  norm_num

/-- **The proportional-reduction form, written three times in this corpus, related here so
that a change to any one of them fails to compile.**

`fstFromHetRatio H H₀`, `hudsonFstFromCoalescenceTimes ETss ETst` and `DGP.r2FromMSE mse
varY` are all `1 - residual/baseline`.  They are **not one quantity**: the first divides a
heterozygosity by an ancestral heterozygosity, the second an expected within-population
coalescence time by a between-population one, the third a mean squared error by a total
outcome variance.  Nothing lets a value of one be substituted for another.

What they share is the *measure*, and sharing it is not a coincidence — proportional
reduction of a residual against a baseline is one construction, and each of the three is
an instance of it.  That is why this is stated rather than left to the reader: the three
definitions carry no shared symbol, so before this theorem an edit to any one of them
diverged from the other two silently.

A fourth instance, `PCCorrectability.Diagnostic.pcTargetAxisEfficacy`, is deliberately
absent.  `Diagnostic` imports nothing from this corpus outside `PCCorrectability`, and no
module imports both it and any of the three below, so **no file can currently state that
identity at all.** Closing that one needs an import, not a theorem.

The name spells `hudsonFstFromCoalescenceTimes` out in full, and must keep doing so.  A
DIFFERENT definition owns the short name `hudsonFst` — `Program.Conventions.hudsonFst`,
the allele-frequency form `d² / (p₁ + p₂ - 2p₁p₂)` — and this theorem is false of it:
`hudsonFst` is not `1 - a/b`.  An earlier name for this theorem abbreviated to
`_eq_hudsonFst_`, so anyone grepping `hudsonFst` for what is known about it got this
statement back as a hit that asserts an equality the named function does not satisfy.  That
is the exact convention where `neiFst`'s docstring records paying a factor of two to four,
so the abbreviation is not available here. -/
theorem fstFromHetRatio_eq_hudsonFstFromCoalescenceTimes_eq_r2FromMSE (a b : ℝ) :
    fstFromHetRatio a b = Portability.hudsonFstFromCoalescenceTimes a b ∧
      fstFromHetRatio a b = r2FromMSE a b := by
  constructor <;> rfl

/-- **Fst(t) in terms of the closed-form heterozygosity.**
    Starting from H(0) = H₀, we have
    Fst(t) = 1 - [H* + (H₀ - H*) × λ^t] / H₀
           = 1 - H*/H₀ - (1 - H*/H₀) × λ^t
           = (1 - H*/H₀) × (1 - λ^t). -/
theorem fst_from_closed_form_het (lam Hstar H₀ : ℝ) (t : ℕ) (hH₀ : H₀ ≠ 0) :
    fstFromHetRatio (hetMutationRecurrence lam Hstar H₀ t) H₀ =
      (1 - Hstar / H₀) * (1 - lam ^ t) := by
  unfold fstFromHetRatio Descent.Core.proportionalReduction
  rw [hetMutationRecurrence_closed_form]
  field_simp
  ring

/-! ### Connecting to the equilibrium Fst -/

/-- **Fst prefactor when H₀ is normalized to 1.**
    With H₀ = 1 (heterozygosity normalized by maximum), the prefactor is
    1 - H* = 1 - θ/(1+θ) = 1/(1+θ) = Fst_eq.
    This is the correct normalisation: H₀ represents the ancestral
    heterozygosity before the population split, scaled to unit maximum. -/
theorem het_ratio_prefactor_unit_H₀ (θ : ℝ) (hθ : 0 ≤ θ) :
    1 - expectedHeterozygosity θ / 1 = fstMutationDriftEquilibrium θ := by
  rw [div_one]
  exact (fstEquilibrium_eq_one_minus_het θ hθ).symm

/-! ### The main derivation: transient Fst from the recurrence -/

/-- **Discrete transient Fst under mutation and drift.**
    Fst(t) = [1/(1+θ)] × (1 - λ^t) where λ = (1-1/(2N))(1-θ/(2N)).
    This is the closed-form discrete-time formula. The continuous version
    `fstMutationDriftTransient` (using exp) is the large-Ne approximation.

    Empirical status: **VALIDATED**
    (`validation/empirical/simcov/battery_bulk16.py`), on the same
    infinite-alleles trajectories as `fstMutationDriftTransient` and to the same
    precision: worst cell 2.27 sems, 6.5% relative, across `Ne` of 50, 100 and
    200 and five times per set spanning `t/Ne` from 0.25 to 4.

    The two forms were carried together deliberately, since this one replaces
    `exp(-(1+theta) t/(2 Ne))` by `hetDecayFactor^t` and the substitution is
    exact only to O(1/Ne). The design reached down to `Ne = 50`, where the two
    predictions differ by about a percent, and the measurement's own noise is
    six percent. They therefore did NOT separate, and neither is credited with beating the other.
    What is established is the common content: the plateau
    and the rate at which it is approached.

    Separating them needs about a hundredfold increase in replicates at small
    `Ne`, which is worth doing only if something downstream depends on the
    difference; nothing currently does. -/
noncomputable def fstMutationDriftTransientDiscrete (θ Ne : ℝ) (t : ℕ) : ℝ :=
  fstMutationDriftEquilibrium θ * (1 - hetDecayFactor Ne θ ^ t)

/-- Reference evaluation; see `Descent.Core.Ratios` for what these pin and why. -/
theorem fstMutationDriftTransientDiscrete_at_reference_point :
    fstMutationDriftTransientDiscrete 1 1 1 = 3 / 8 := by
  norm_num [fstMutationDriftTransientDiscrete, fstMutationDriftEquilibrium, hetDecayFactor,
    hetDecayFromScaled, Descent.Core.fstFromFlow]


/-- **Derivation of transient Fst from the heterozygosity recurrence.**

    Starting from the affine recurrence H(t+1) = λ H(t) + (1-λ) H*
    with λ = hetDecayFactor Ne θ, H* = θ/(1+θ), and H₀ = 1
    (normalized ancestral heterozygosity):

    Step 1: Closed form gives H(t) = H* + (1 - H*) λ^t.
    Step 2: Fst(t) = 1 - H(t)/1 = 1 - H* - (1-H*) λ^t = (1-H*)(1 - λ^t).
    Step 3: 1 - H* = 1/(1+θ) = Fst_eq.
    Step 4: Fst(t) = Fst_eq × (1 - λ^t).

    This theorem shows that the recurrence-based Fst exactly equals
    `fstMutationDriftTransientDiscrete`. -/
theorem fstTransient_derived_from_recurrence (θ Ne : ℝ) (t : ℕ)
    (hθ : 0 ≤ θ) :
    fstFromHetRatio
      (hetMutationRecurrence (hetDecayFactor Ne θ) (expectedHeterozygosity θ) 1 t) 1 =
    fstMutationDriftTransientDiscrete θ Ne t := by
  rw [fst_from_closed_form_het _ _ _ _ one_ne_zero]
  unfold fstMutationDriftTransientDiscrete
  rw [het_ratio_prefactor_unit_H₀ θ hθ]

/-- **At t = 0, the derived transient Fst is 0.** -/
theorem fstTransientDiscrete_at_zero (θ Ne : ℝ) :
    fstMutationDriftTransientDiscrete θ Ne 0 = 0 := by
  unfold fstMutationDriftTransientDiscrete
  simp

/-- **The derived transient Fst is nonneg for valid parameters.** -/
theorem fstTransientDiscrete_nonneg (θ Ne : ℝ) (t : ℕ)
    (hθ : 0 ≤ θ) (hNe : 2 ≤ Ne) (hθNe : θ ≤ 2 * Ne) :
    0 ≤ fstMutationDriftTransientDiscrete θ Ne t := by
  unfold fstMutationDriftTransientDiscrete
  apply mul_nonneg
  · exact le_of_lt (fstMutationDriftEquilibrium_pos θ hθ)
  · rw [sub_nonneg]
    apply pow_le_one₀
    · unfold hetDecayFactor hetDecayFromScaled
      apply mul_nonneg
      · rw [sub_nonneg, div_le_one (by linarith)]; linarith
      · rw [sub_nonneg, div_le_one (by linarith)]; linarith
    · unfold hetDecayFactor hetDecayFromScaled
      have h1 : 1 - 1 / (2 * Ne) < 1 := by rw [sub_lt_self_iff]; positivity
      have h2 : 1 - θ / (2 * Ne) ≤ 1 := by rw [sub_le_self_iff]; positivity
      nlinarith [mul_le_of_le_one_right
        (show 0 ≤ 1 - 1 / (2 * Ne) by rw [sub_nonneg, div_le_one (by linarith)]; linarith) h2]

/-- **The derived transient Fst is bounded by the equilibrium Fst.** -/
theorem fstTransientDiscrete_le_equilibrium (θ Ne : ℝ) (t : ℕ)
    (hθ : 0 ≤ θ) (hNe : 2 ≤ Ne) (hθNe : θ ≤ 2 * Ne) :
    fstMutationDriftTransientDiscrete θ Ne t ≤ fstMutationDriftEquilibrium θ := by
  unfold fstMutationDriftTransientDiscrete
  have hfeq : 0 < fstMutationDriftEquilibrium θ := fstMutationDriftEquilibrium_pos θ hθ
  calc fstMutationDriftEquilibrium θ * (1 - hetDecayFactor Ne θ ^ t)
      ≤ fstMutationDriftEquilibrium θ * 1 := by
        apply mul_le_mul_of_nonneg_left _ (le_of_lt hfeq)
        have hpow_nonneg : 0 ≤ hetDecayFactor Ne θ ^ t := by
          apply pow_nonneg
          unfold hetDecayFactor hetDecayFromScaled
          apply mul_nonneg
          · rw [sub_nonneg, div_le_one (by linarith)]
            linarith
          · rw [sub_nonneg, div_le_one (by linarith)]
            linarith
        linarith
    _ = fstMutationDriftEquilibrium θ := by ring

/-- **Discrete-to-continuous approximation.**
    For large Ne, (1-1/(2N))(1-θ/(2N)) ≈ 1 - (1+θ)/(2N) ≈ exp(-(1+θ)/(2N)),
    so λ^t ≈ exp(-(1+θ)t/(2N)).
    We state the algebraic identity connecting the two:
    (1-1/(2N))(1-θ/(2N)) = 1 - (1+θ)/(2N) + θ/(4N²). -/
theorem hetDecayFactor_expansion (Ne θ : ℝ) (hNe : Ne ≠ 0) :
    hetDecayFactor Ne θ = 1 - (1 + θ) / (2 * Ne) + θ / (4 * Ne ^ 2) := by
  unfold hetDecayFactor hetDecayFromScaled
  field_simp
  ring

/-- **The θ/(4N²) correction is negligible for large Ne.**
    |hetDecayFactor - (1 - (1+θ)/(2N))| = θ/(4N²), which vanishes as N → ∞. -/
theorem hetDecayFactor_approx_error (Ne θ : ℝ) (hNe : 0 < Ne) (hθ : 0 ≤ θ) :
    |hetDecayFactor Ne θ - (1 - (1 + θ) / (2 * Ne))| = θ / (4 * Ne ^ 2) := by
  rw [hetDecayFactor_expansion Ne θ (ne_of_gt hNe)]
  have : 1 - (1 + θ) / (2 * Ne) + θ / (4 * Ne ^ 2) - (1 - (1 + θ) / (2 * Ne)) =
      θ / (4 * Ne ^ 2) := by ring
  rw [this, abs_of_nonneg]
  positivity

/-- **The discrete formula matches the original `fstMutationDriftTransient` definition
    in the large-Ne limit.**
    Both have the form Fst_eq × (1 - decay^t), differing only in
    whether the decay factor is the exact discrete
    (1-1/(2N))(1-θ/(2N)) or the continuous approximation exp(-(1+θ)/(2N)).
    This theorem states the structural agreement: when the decay base is the same,
    the formulas are identical. -/
theorem fstTransientDiscrete_eq_explicit (θ Ne : ℝ) (t : ℕ) :
    fstMutationDriftTransientDiscrete θ Ne t =
      1 / (1 + θ) * (1 - ((1 - 1 / (2 * Ne)) * (1 - θ / (2 * Ne))) ^ t) := by
  unfold fstMutationDriftTransientDiscrete fstMutationDriftEquilibrium hetDecayFactor Descent.Core.fstFromFlow
    hetDecayFromScaled
  rfl

end TransientFstDerivation

/-- **Hudson's frequency form IS `1 - H_w/H_b`**, which is what puts it in the lattice.

`hudsonFst` is written `(p₁ - p₂)² / (p₁(1-p₂) + p₂(1-p₁))`, and nothing related that shape
to the heterozygosity-ratio reading the rest of the corpus states `F_ST` results in. It is
the same number: with `H_w = p₁(1-p₁) + p₂(1-p₂)` the mean within-subgroup heterozygosity
and `H_b = p₁(1-p₂) + p₂(1-p₁)` the between-subgroup one, `H_b - H_w = (p₁ - p₂)²` exactly,
so the squared frequency difference in the numerator is not a separate convention -- it is
the heterozygosity excess, already reduced.

This is the edge that was missing. `fstFromHetRatio` is `Core.proportionalReduction`, and
`slatkin_hetRatio_eq_coalescenceRatio` carries that to
`hudsonFstFromCoalescenceTimes`, so the chain now runs frequencies to heterozygosities to
coalescence times without leaving the Hudson convention -- which is the claim the corpus's
`τ/(1+τ)` results have been resting on.

    Empirical status: NOT AN EMPIRICAL CLAIM -- an algebraic identity between two
    spellings of one estimator. The measurement that matters is the one in `neiFst`'s
    docstring, where Hudson tracks the split law at 0.03 sems and Nei does not. -/
theorem hudsonFst_eq_fstFromHetRatio (p₁ p₂ : ℝ)
    (h : p₁ * (1 - p₂) + p₂ * (1 - p₁) ≠ 0) :
    Descent.Core.hudsonFst p₁ p₂
      = PopGen.fstFromHetRatio (p₁ * (1 - p₁) + p₂ * (1 - p₂))
          (p₁ * (1 - p₂) + p₂ * (1 - p₁)) := by
  unfold Descent.Core.hudsonFst PopGen.fstFromHetRatio Descent.Core.proportionalReduction
  field_simp
  ring

theorem hetDecayFactor_uses_timeScale (Ne θ : ℝ) :
    PopGen.hetDecayFactor Ne θ
      = (1 - 1 / Descent.Core.coalescentTimeScale Ne) * (1 - θ / Descent.Core.coalescentTimeScale Ne) := by
  unfold PopGen.hetDecayFactor PopGen.hetDecayFromScaled; rw [Descent.Core.coalescentTimeScale_eq]

end Descent.PopGen
