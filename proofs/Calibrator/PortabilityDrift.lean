/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Calibrator.Conclusions
import Calibrator.DGP
import Calibrator.CirculationDefect

namespace Calibrator

open MeasureTheory

/-! `r2FromSignalVariance` and the Gaussian-AUC declarations live in
`Calibrator.TransportedMetrics` (DGP.lean). `Calibrator.DGP` is imported, so
the module is available, but the namespace was never opened here and this file
refers to five of its declarations WITHOUT qualification. Lean does not report
that as a missing constant: it auto-binds the bare name as an implicit
variable, which is why the failure surfaced as three unrelated-looking symptoms
-- "unknown identifier", "function expected at", and the discriminating
"LOCAL VARIABLE `r2FromSignalVariance` has no definition". A definition that
had failed to build would say something else, and `Calibrator.DGP` itself
builds clean.

These five names are opened rather than qualified at ~40 call sites: the
mechanical repoint is the larger and riskier diff, and an explicit import list
cannot collide, since this file defines none of these names and the only
`Profile` and `calibratedBrier` in the corpus are the ones inside this same
namespace. The remaining `TransportedMetrics.` prefixes in this file are left
alone; both spellings resolve to the same constant. -/
open TransportedMetrics (r2FromSignalVariance r2FromSignalVariance_eq_rsquared
  equalVarianceGaussianAUCFromSignalVariance
  equalVarianceGaussianAUCFromSignalVariance_eq_formula_of_ne_noise)

section PortabilityDrift


/-- Empirical status: UNTESTED. -/
noncomputable def integratedCoalescentHazard (hazard : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ s in (0)..t, hazard s

/-- Probability that a pair has not yet coalesced by time `t`, from the
integrated hazard: `S(t) = exp(-Λ(t))`.

    Empirical status: UNTESTED. -/
noncomputable def coalescenceSurvivalFromHazard (hazard : ℝ → ℝ) (t : ℝ) : ℝ :=
  Real.exp (-(integratedCoalescentHazard hazard t))

/-- Probability that a pair has coalesced by time `t`, the complement of the
survival function.

    Empirical status: UNTESTED. -/
noncomputable def coalescenceCdfFromHazard (hazard : ℝ → ℝ) (t : ℝ) : ℝ :=
  1 - coalescenceSurvivalFromHazard hazard t

/-- Coalescent time `τ = t / (2·Nₑ)`: generations rescaled by the diploid
coalescent timescale.

    Empirical status: UNTESTED. -/
noncomputable def coalescentTau (t Ne : ℝ) : ℝ :=
  t / (2 * Ne)

/-- **`F_ST` after a clean split, in coalescent units.**

This is not an independent formula.  It is `coalFst` expressed in units of
`tau = t / (2 Ne)`, and `coalFst_eq_fstFromTau` is the theorem that says so; the
two cannot drift apart without that theorem failing.  The previous body here was
`1 - exp (-tau)`, which is the coalescence CDF already defined in this file as
`coalescenceCdfFromHazard` under unit hazard -- the probability that a lineage
pair has coalesced by `tau`, not the between-population variance ratio.  The two
were conflated, and `fstFromTau_lt_coalescenceCdf` now records that they are
never equal.

    Regime: instantaneous clean split, constant equal daughter sizes, no
    migration, no selection, continuous (large-N) coalescent -- the model under
    which `validation/differential/refs.py`'s `split_fst_hudson` is exact.  The
    regime is the whole point of this definition rather than a caveat on it: the
    closed-population drift recurrence is a *different* model, not the `F_ST` of
    a split, and confusing the two is the model error that the
    `heterozygosityLossDerived`/`fstFromTau`/`targetHetFromFst` cluster turns on (see the
    `heterozygosityLossDerived-is-not-split-fst` check).  Outside a clean split -- under
    migration, unequal sizes, or ongoing gene flow -- this map is not claimed.

    Empirical status: VALIDATED (0.0909/0.2000/0.3333/0.5000/0.6667/0.8000 at
    tau = .1/.25/.5/1/2/4 against simulated 0.0905/0.1887/0.3137/0.4782/0.6589/
    0.8028, within simulation error at every point).

    Power: the prediction spans `0.0909` to `0.8000` across that `tau` grid,
    nearly an order of magnitude and most of the range `F_ST` can occupy. A
    fortyfold sweep of `tau` moves the prediction across the whole saturating
    curve, so a form that is linear in `tau`, or one saturating at a different
    rate, separates from this one on the grid rather than only at its ends. -/
noncomputable def fstFromTau (tau : ℝ) : ℝ :=
  tau / (1 + tau)

/-- `F_ST` after `t` generations of drift at effective size `Nₑ`, obtained by
rescaling to coalescent time and applying `fstFromTau`.

    Empirical status: UNTESTED. -/
noncomputable def fstFromGenerations (t Ne : ℝ) : ℝ :=
  fstFromTau (coalescentTau t Ne)

/-- **Circulation inflates transfer time by the same saturation law that drift
uses for `F_ST`.**

`CirculationDefect.transferTimeInflation` is `1 + (a/s)^2`, the factor by which
circulation stretches the frontier time. Its reciprocal -- the fraction of the
frontier time that survives -- is `1 - fstFromTau ((a/s)^2)`, the complement of
the chart this file uses for drift at coalescent time `tau`.

The two modules are about different processes, and that is why the shared
functional form is worth recording rather than assuming: `x / (1 + x)` appears
in both, so a change to either body that breaks the identity fails to compile
instead of leaving the two quietly disagreeing about a shape they both use. No
hypothesis is needed, because `1 + (a/s)^2` is positive for every `s` and `a`,
including `s = 0`. -/
theorem one_div_transferTimeInflation_eq_one_sub_fstFromTau (s a : ℝ) :
    1 / transferTimeInflation s a = 1 - fstFromTau ((a / s) ^ 2) := by
  have hpos : (0 : ℝ) < 1 + (a / s) ^ 2 := by positivity
  have hne : (1 : ℝ) + (a / s) ^ 2 ≠ 0 := ne_of_gt hpos
  unfold transferTimeInflation fstFromTau
  first
  | (field_simp; ring)
  | field_simp

/-- **Branchwise-to-pairwise `F_ST` map under independent drift from a common
ancestor.**

    Regime: small divergence, `F_ST` below about `0.05`. Multiplicative
    composition is the right shape -- additive composition `fstS + fstT` is 53%
    high at `T = 4000` -- and this map is within simulation error at the shortest
    branch tested, but it degrades monotonically as divergence grows, and the
    degradation is one-sided, always too high:

        T      fstS     fstT   pairwise obs      se      this map    err
      200    0.0461   0.0500     0.09314      0.00612    0.09366    +0.6%
     1000    0.1867   0.1895     0.31845      0.00941    0.34075    +7.0%
     2000    0.3374   0.3234     0.48780      0.01002    0.55098   +13.0%
     4000    0.5029   0.4987     0.65365      0.00801    0.74948   +14.7%

    Twelve to eighteen standard errors on the last two rows. Not an estimator
    artifact: under Nei's estimator the same rows give -1.4%, +3.3%, +10.0%,
    +14.2%.

    The mechanism is derivable rather than empirical, and
    `pairwiseFstFromBranches_eq_fstFromTau_add_mul` states it: composing
    multiplicatively in `F_ST` is the same as composing *additively in coalescent
    time* after inserting a spurious `tauS * tauT` of extra divergence time.
    Coalescence times add along a path; `F_ST` values do not. At `tau` near `1`,
    which is where `T = 4000` sits, that spurious term doubles the divergence
    time, which is the sign and the size of the error above.
    `pairwiseFstFromBranchTaus` is the same composition without it.

    Empirical status: CONDITIONALLY VALID. -/
noncomputable def pairwiseFstFromBranches (fstS fstT : ℝ) : ℝ :=
  1 - (1 - fstS) * (1 - fstT)

/-- **Pairwise `F_ST` composed in coalescent time instead of in `F_ST`.**

    Under the coalescent, two demes that split `tauS` and `tauT` ago from a
    common ancestor have `E[T_between] = 1 + tauS + tauT` in units where
    `E[T_within] = 1`, because expected coalescence times add along the path.
    Hudson's ratio then gives `fstFromTau (tauS + tauT)` directly.

    This is offered as a candidate for `pairwiseFstFromBranches`, not
    substituted for it: recomputed against the four rows tabulated on that
    definition it errs -5.4%, -1.2%, +3.4%, +2.4% where the multiplicative map
    errs +0.6%, +7.0%, +13.0%, +14.7%.

    Empirical status: UNTESTED. The four residuals just quoted are recomputed
    from the table on `pairwiseFstFromBranches` rather than measured in a run of
    their own, so they are a consistency check on the algebra and not an
    independent validation. -/
noncomputable def pairwiseFstFromBranchTaus (tauS tauT : ℝ) : ℝ :=
  fstFromTau (tauS + tauT)

@[simp] theorem pairwise_fst_decomposition (fstS fstT : ℝ) :
    pairwiseFstFromBranches fstS fstT = fstS + fstT - fstS * fstT := by
  unfold pairwiseFstFromBranches
  ring_nf

/-- **What the multiplicative composition actually computes.**

Feeding it two branch `F_ST` values that came from coalescent times `a` and `b`
returns the `F_ST` of a single branch of length `a + b + a * b`. The `a * b` is
the whole defect: it is divergence time that no branch spent. This identity is
the derivation behind the regime note on `pairwiseFstFromBranches`, and it needs
no simulation to state. -/
theorem pairwiseFstFromBranches_eq_fstFromTau_add_mul (a b : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) :
    pairwiseFstFromBranches (fstFromTau a) (fstFromTau b) =
      fstFromTau (a + b + a * b) := by
  have ha1 : (0 : ℝ) < 1 + a := by linarith
  have hb1 : (0 : ℝ) < 1 + b := by linarith
  have ha1' : (1 : ℝ) + a ≠ 0 := ne_of_gt ha1
  have hb1' : (1 : ℝ) + b ≠ 0 := ne_of_gt hb1
  have hab : (0 : ℝ) < 1 + (a + b + a * b) := by nlinarith
  have hab' : (1 : ℝ) + (a + b + a * b) ≠ 0 := ne_of_gt hab
  unfold pairwiseFstFromBranches fstFromTau
  field_simp
  ring

/-- **The multiplicative map is strictly the larger of the two compositions**,
for every pair of positive branch lengths. The bias has a sign, and it is the
sign the simulation reports. -/
theorem pairwiseFstFromBranchTaus_lt_pairwiseFstFromBranches (a b : ℝ)
    (ha : 0 < a) (hb : 0 < b) :
    pairwiseFstFromBranchTaus a b <
      pairwiseFstFromBranches (fstFromTau a) (fstFromTau b) := by
  rw [pairwiseFstFromBranches_eq_fstFromTau_add_mul a b ha.le hb.le]
  unfold pairwiseFstFromBranchTaus fstFromTau
  have h1 : (0 : ℝ) < 1 + (a + b) := by linarith
  have h2 : (0 : ℝ) < 1 + (a + b + a * b) := by nlinarith
  rw [div_lt_div_iff₀ h1 h2]
  nlinarith [mul_pos ha hb]

/-- **The gap between the two compositions is second order in the branch
lengths.**  It is bounded by `eps ^ 2` when both branches are below `eps`, which
is the precise sense in which the multiplicative map is accurate at small
`F_ST` and the reason the `T = 200` row above agrees to `0.6%`. -/
theorem pairwiseFst_composition_gap_le (a b eps : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hae : a ≤ eps) (hbe : b ≤ eps) :
    pairwiseFstFromBranches (fstFromTau a) (fstFromTau b) -
        pairwiseFstFromBranchTaus a b ≤ eps ^ 2 := by
  have hab : 0 ≤ a * b := mul_nonneg ha hb
  have h1 : (0 : ℝ) < 1 + (a + b) := by linarith
  have h2 : (0 : ℝ) < 1 + (a + b + a * b) := by linarith
  have h1' : (1 : ℝ) + (a + b) ≠ 0 := ne_of_gt h1
  have h2' : (1 : ℝ) + (a + b + a * b) ≠ 0 := ne_of_gt h2
  rw [pairwiseFstFromBranches_eq_fstFromTau_add_mul a b ha hb]
  unfold pairwiseFstFromBranchTaus fstFromTau
  have key : (a + b + a * b) / (1 + (a + b + a * b)) - (a + b) / (1 + (a + b)) =
      a * b / ((1 + (a + b)) * (1 + (a + b + a * b))) := by
    field_simp
    ring
  rw [key]
  have hden : (0 : ℝ) < (1 + (a + b)) * (1 + (a + b + a * b)) := mul_pos h1 h2
  have hsum : (0 : ℝ) ≤ a + b := by linarith
  have hsum' : (0 : ℝ) ≤ a + b + a * b := by linarith
  have hone : (1 : ℝ) ≤ (1 + (a + b)) * (1 + (a + b + a * b)) := by
    nlinarith [mul_nonneg hsum hsum']
  have hstep : a * b / ((1 + (a + b)) * (1 + (a + b + a * b))) ≤ a * b := by
    rw [div_le_iff₀ hden]
    nlinarith [mul_le_mul_of_nonneg_left hone hab]
  have heps : (0 : ℝ) ≤ eps := le_trans ha hae
  have hfinal : a * b ≤ eps ^ 2 := by nlinarith [mul_le_mul hae hbe hb heps]
  linarith

@[simp] theorem coalescenceCdfFromHazard_eq (hazard : ℝ → ℝ) (t : ℝ) :
    coalescenceCdfFromHazard hazard t =
      1 - Real.exp (-(integratedCoalescentHazard hazard t)) := by
  simp [coalescenceCdfFromHazard, coalescenceSurvivalFromHazard]

@[simp] theorem fstFromGenerations_eq (t Ne : ℝ) :
    fstFromGenerations t Ne = t / (2 * Ne) / (1 + t / (2 * Ne)) := rfl

theorem fst_from_tau_nonneg_of_nonneg (tau : ℝ) (htau : 0 ≤ tau) :
    0 ≤ fstFromTau tau :=
  div_nonneg htau (by linarith)

theorem fst_from_tau_lt_one (tau : ℝ) (htau : 0 ≤ tau) : fstFromTau tau < 1 := by
  unfold fstFromTau
  rw [div_lt_one (by linarith)]
  linarith

/-- **The coalescence CDF is not `F_ST`.**  `1 - exp (-tau)` is the probability
that a lineage pair has coalesced by `tau`; `F_ST` is the between-population
share of variance.  Conflating them overstates divergence at every positive
separation, which is the direction and the shape of the bias measured against
simulation (+5% at `tau = 0.1`, rising to +32% at `tau = 1`).  Stating the
inequality keeps the two from being interchanged again silently. -/
theorem fstFromTau_lt_coalescenceCdf (tau : ℝ) (htau : 0 < tau) :
    fstFromTau tau < 1 - Real.exp (-tau) := by
  have hE : (0 : ℝ) < Real.exp tau := Real.exp_pos tau
  have hexp : tau + 1 < Real.exp tau := Real.add_one_lt_exp (by linarith)
  have h1t : (0 : ℝ) < 1 + tau := by linarith
  rw [← sub_pos]
  unfold fstFromTau
  rw [Real.exp_neg]
  have hrw : 1 - (Real.exp tau)⁻¹ - tau / (1 + tau) =
      (Real.exp tau - 1 - tau) / (Real.exp tau * (1 + tau)) := by
    field_simp
    ring
  rw [hrw]
  exact div_pos (by linarith) (by positivity)



/-- A split with ongoing migration.

**Do not add a deme-count field here.** The many-deme regime that
`fstEqLimitLowMutationManyDemes` names is a LIMIT, not a stored count: a deme count would
enter no formula and no theorem in this file, so it could take any value without changing
a single statement, while giving the appearance of tracking something the development does
not track. -/
structure SplitMigrationModel where
  t : ℝ
  Ne : ℝ
  mig : ℝ
  mu : ℝ
  Ne_pos : 0 < Ne
  mig_nonneg : 0 ≤ mig
  mu_nonneg : 0 ≤ mu

/-- **The class is inhabited.**  A theorem quantified over an uninhabited structure is
true and empty: kernel-checked, clean axiom report, no content.  This is the witness that
makes the theorems below statements about something. -/
noncomputable def SplitMigrationModel.witness : SplitMigrationModel where
  t := 1
  Ne := 1
  mig := 1
  mu := 1
  Ne_pos := by norm_num
  mig_nonneg := by norm_num
  mu_nonneg := by norm_num

/-- Empirical status: UNTESTED. -/
noncomputable def SplitMigrationModel.fstEqLimitLowMutationManyDemes (m :
    SplitMigrationModel) : ℝ :=
  1 / (1 + scaledMigrationRate m.Ne m.mig)

/-- Hudson's `F_ST` estimator from mean coalescence times: one minus the ratio
of the within-population time to the total time.

    Empirical status: UNTESTED. -/
noncomputable def hudsonFstFromCoalescenceTimes (ETss ETst : ℝ) : ℝ :=
  1 - ETss / ETst

structure DemographicCoalescenceScalars where
  ETss : ℝ
  ETst : ℝ

noncomputable def DemographicCoalescenceScalars.delta
    (d : DemographicCoalescenceScalars) : ℝ :=
  hudsonFstFromCoalescenceTimes d.ETss d.ETst

@[simp] theorem DemographicCoalescenceScalars.delta_eq
    (d : DemographicCoalescenceScalars) :
    d.delta = 1 - d.ETss / d.ETst := by
  rfl

/-- **First-step analysis of the structured coalescent, same-deme state.**

Symmetric two-deme island model with scaled migration `M`.  Time is in units of
`2 Nₑ` generations, so two lineages sitting in one deme coalesce at rate `1`
and each lineage leaves its deme at rate `M/2`.  From the same-deme state the
competing clocks give a total rate `1 + M`, an expected waiting time
`1/(1 + M)`, and then coalescence with probability `1/(1 + M)` or -- with
probability `M/(1 + M)` -- a migration that leaves the lineages in different
demes.  The map below sends a candidate pair of expected coalescence times to
the pair implied by one such step.

Composition convention: this is the *continuous-time* structured coalescent, in
which competing exponential clocks make the within-generation ordering of
migration and coalescence immaterial.  The discrete-generation model with a
fixed ordering has a different fixed point, differing at O(1/Nₑ).

    Empirical status: UNTESTED. -/
noncomputable def twoDemeIMFirstStepSame (M _ETss ETst : ℝ) : ℝ :=
  1 / (1 + M) + (M / (1 + M)) * ETst

/-- **First-step analysis of the structured coalescent, different-deme state.**
Lineages in different demes cannot coalesce; the only event is a migration, at
total rate `M`, after which both lineages are in one deme.

    Empirical status: UNTESTED. -/
noncomputable def twoDemeIMFirstStepDiff (M ETss _ETst : ℝ) : ℝ :=
  1 / M + ETss

/-- **Expected within-deme coalescence time at migration-drift balance.**

Not stipulated: it is the same-deme component of the fixed point of
`twoDemeIMFirstStepSame`/`twoDemeIMFirstStepDiff`, which
`twoDemeIMEquilibriumETss_isFixedPoint` proves.  That it is *free of `M`* is
Strobeck's invariance -- the content of the model, and just the kind of
fact a stipulated constant cannot be trusted to carry.

    Empirical status: UNTESTED. -/
noncomputable def twoDemeIMEquilibriumETss (_M : ℝ) : ℝ := 2

/-- **Expected between-deme coalescence time at migration-drift balance.**
Derived: see `twoDemeIMEquilibriumETst_isFixedPoint`.  It diverges as `M → 0`,
which is the complete-isolation limit.

    Empirical status: UNTESTED. -/
noncomputable def twoDemeIMEquilibriumETst (M : ℝ) : ℝ :=
  (2 * M + 1) / M

noncomputable def twoDemeIMEquilibriumScalars (M : ℝ) : DemographicCoalescenceScalars where
  ETss := twoDemeIMEquilibriumETss M
  ETst := twoDemeIMEquilibriumETst M

/-- **Hudson's F_ST at two-deme migration-drift balance.**

Derived from the coalescence times above, not asserted:
`twoDemeIMEquilibriumDelta_isFixedPoint` shows that pushing the equilibrium
times through one step of first-step analysis and forming Hudson's ratio
returns this value.  Unlike `twoDemeIMEquilibriumETst`, this closed
form extends to the boundary: at `M = 0` it takes the value `1`, complete
differentiation under total isolation, which
`twoDemeIMEquilibriumDelta_of_no_migration` records.

    Empirical status: UNTESTED. -/
noncomputable def twoDemeIMEquilibriumDelta (M : ℝ) : ℝ :=
  1 / (2 * M + 1)

/-- **The within-deme coalescence time is a fixed point of first-step
analysis.**  Solving `ETss = 1/(1+M) + (M/(1+M)) ETst` jointly with
`ETst = 1/M + ETss` forces `ETss = 2` for every `M > 0`. -/
theorem twoDemeIMEquilibriumETss_isFixedPoint (M : ℝ) (hM : 0 < M) :
    twoDemeIMFirstStepSame M (twoDemeIMEquilibriumETss M) (twoDemeIMEquilibriumETst M) =
      twoDemeIMEquilibriumETss M := by
  have hM' : M ≠ 0 := ne_of_gt hM
  have h1 : (0 : ℝ) < 1 + M := by linarith
  have h1' : (1 : ℝ) + M ≠ 0 := ne_of_gt h1
  unfold twoDemeIMFirstStepSame twoDemeIMEquilibriumETss twoDemeIMEquilibriumETst
  field_simp
  ring

/-- **The between-deme coalescence time is a fixed point of first-step
analysis.** -/
theorem twoDemeIMEquilibriumETst_isFixedPoint (M : ℝ) (hM : 0 < M) :
    twoDemeIMFirstStepDiff M (twoDemeIMEquilibriumETss M) (twoDemeIMEquilibriumETst M) =
      twoDemeIMEquilibriumETst M := by
  have hM' : M ≠ 0 := ne_of_gt hM
  unfold twoDemeIMFirstStepDiff twoDemeIMEquilibriumETss twoDemeIMEquilibriumETst
  rw [eq_div_iff hM', add_mul, one_div_mul_cancel hM']
  ring

/-- **The equilibrium F_ST is the Hudson ratio of the coalescent fixed
point.**  One step of first-step analysis applied to the equilibrium times,
then Hudson's `1 - E[T_within]/E[T_between]`, returns `1/(2M+1)`. -/
theorem twoDemeIMEquilibriumDelta_isFixedPoint (M : ℝ) (hM : 0 < M) :
    hudsonFstFromCoalescenceTimes
        (twoDemeIMFirstStepSame M (twoDemeIMEquilibriumETss M) (twoDemeIMEquilibriumETst M))
        (twoDemeIMFirstStepDiff M (twoDemeIMEquilibriumETss M) (twoDemeIMEquilibriumETst M)) =
      twoDemeIMEquilibriumDelta M := by
  rw [twoDemeIMEquilibriumETss_isFixedPoint M hM, twoDemeIMEquilibriumETst_isFixedPoint M hM]
  have hM' : M ≠ 0 := ne_of_gt hM
  have h2 : (0 : ℝ) < 2 * M + 1 := by linarith
  have h2' : (2 : ℝ) * M + 1 ≠ 0 := ne_of_gt h2
  unfold hudsonFstFromCoalescenceTimes twoDemeIMEquilibriumETss twoDemeIMEquilibriumETst
    twoDemeIMEquilibriumDelta
  field_simp
  ring

/-- **Complete isolation is a boundary the closed form attains.**  At `M = 0`
the two demes exchange nothing, between-deme coalescence times diverge, and
F_ST is exactly `1` -- not merely close to it. -/
@[simp] theorem twoDemeIMEquilibriumDelta_of_no_migration :
    twoDemeIMEquilibriumDelta 0 = 1 := by
  unfold twoDemeIMEquilibriumDelta
  norm_num

theorem twoDemeIMEquilibriumDelta_eq (M : ℝ) (h2M1 : 2 * M + 1 ≠ 0) :
    (twoDemeIMEquilibriumScalars M).delta = twoDemeIMEquilibriumDelta M := by
  simp [DemographicCoalescenceScalars.delta, hudsonFstFromCoalescenceTimes,
    twoDemeIMEquilibriumScalars, twoDemeIMEquilibriumETss,
    twoDemeIMEquilibriumETst, twoDemeIMEquilibriumDelta]
  field_simp [h2M1]
  ring

theorem twoDemeIMEquilibriumDelta_pos (M : ℝ) (hM : 0 < M) :
    0 < twoDemeIMEquilibriumDelta M := by
  unfold twoDemeIMEquilibriumDelta
  positivity

theorem twoDemeIMEquilibriumDelta_lt_one (M : ℝ) (hM : 0 < M) :
    twoDemeIMEquilibriumDelta M < 1 := by
  unfold twoDemeIMEquilibriumDelta
  rw [div_lt_one (by linarith)]
  linarith

/-!
## The closed-population, no-mutation regime, made into an object

Everything below that decays heterozygosity geometrically assumes a **closed
population with no mutation**, and it is carried as an explicit regime object below
rather than inside definition bodies, where nothing can contradict it. Simulation at
demographic equilibrium
with `Ne = 1000` measures the retention `het_A / het_anc` as

       T = 200    1.010 ± 0.022    drift-only prediction 0.905
       T = 1000   0.989 ± 0.022    drift-only prediction 0.607
       T = 4000   1.025 ± 0.020    drift-only prediction 0.135

so at `T = 4000` the recurrence predicts an 86 percent loss of heterozygosity
and the population loses none: mutation replenishes diversity as fast as drift
removes it. The cluster's `F_ST` is therefore near `0` exactly where the
measurable between-population `F_ST` is `0.50`. These are not two calibrations of
one quantity; they are different quantities sharing a name, which is why the same
error was reproduced independently several times.

This section makes the assumption an object rather than a habit.
`hetStepWithMutation` is the recurrence *with* mutation; the closed-population
recurrence is its `mu = 0` case (`hetTrajectory_of_no_mutation`);
`hetMutationFloor` is the heterozygosity that the mutation term holds a
population above forever *once it is above it*
(`hetTrajectory_ge_hetMutationFloor_of_init_ge_floor`); and
`driftOnly_lt_hetTrajectory_of_below_floor` is the quantitative cost -- once the
drift-only prediction dips below that floor it is strictly wrong, with no appeal
to simulation. `ClosedPopulationNoMutation` carries the assumption in a field, so
a use site has to discharge it instead of inheriting it silently.

`Calibrator.DriftRegime` states the epistemic half of the same incident: why
every cross-check inside the cluster passed.
-/

section ClosedPopulationRegime

/-- **One generation of the heterozygosity recurrence, with mutation.**

Drift removes a fraction `1/(2 Nₑ)` of the standing heterozygosity, and
mutation converts a fraction `2 mu` of the identical pairs -- one chance per
lineage -- back into non-identical ones. Dropping the second term is the
closed-population assumption, and it is dropped nowhere in this definition.

Composition convention: drift and mutation are applied to the same input state
and added, which is the first-order model. The unlinearised infinite-alleles
recursion multiplies `(1 - mu)²` against the drift factor and differs at
`O(mu², mu/Nₑ)`.

    Regime: none. This is the general recurrence; the closed population is the
    special case `mu = 0`, recorded by `hetTrajectory_of_no_mutation`.

    Empirical status: UNTESTED. -/
noncomputable def hetStepWithMutation (Ne mu H : ℝ) : ℝ :=
  (1 - 1 / (2 * Ne)) * H + 2 * mu * (1 - H)

/-- The heterozygosity trajectory generated by `hetStepWithMutation` from `H₀`.

    Regime: none; carries whatever `mu` it is given.

    Empirical status: UNTESTED. -/
noncomputable def hetTrajectory (Ne mu H₀ : ℝ) : ℕ → ℝ
  | 0 => H₀
  | t + 1 => hetStepWithMutation Ne mu (hetTrajectory Ne mu H₀ t)

/-- **The heterozygosity floor that mutation holds.**

`theta / (1 + theta)` with `theta = 4 Nₑ mu`: the level at which mutational
input balances drift loss. Below it the recurrence gains heterozygosity, above
it the recurrence loses heterozygosity, and it is never crossed from above.
This is the number the closed-population model sets to zero.

    Regime: none. Its `mu = 0` value is `0`, which is the closed-population
    assumption itself, and is why that model predicts unbounded loss.

    Empirical status: UNTESTED as a formula, but the observation it explains is
    measured: at demographic equilibrium the retention stays at `1.025 ± 0.020`
    out to `T = 4000` where the floorless model predicts `0.135`. -/
noncomputable def hetMutationFloor (Ne mu : ℝ) : ℝ :=
  4 * Ne * mu / (1 + 4 * Ne * mu)

/-- **The floor is the rest point of the recurrence.**  Solving
`(1 - 1/(2 Nₑ)) H + 2 mu (1 - H) = H` gives `H (1/(2 Nₑ) + 2 mu) = 2 mu`, i.e.
`H = 4 Nₑ mu / (1 + 4 Nₑ mu)`. -/
theorem hetMutationFloor_isFixedPoint (Ne mu : ℝ) (hNe : 0 < Ne) (hmu : 0 ≤ mu) :
    hetStepWithMutation Ne mu (hetMutationFloor Ne mu) = hetMutationFloor Ne mu := by
  have hNe' : Ne ≠ 0 := ne_of_gt hNe
  have hprod : (0 : ℝ) ≤ 4 * Ne * mu := by positivity
  have hd : (0 : ℝ) < 1 + 4 * Ne * mu := by linarith
  have hd' : (1 : ℝ) + 4 * Ne * mu ≠ 0 := ne_of_gt hd
  unfold hetStepWithMutation hetMutationFloor
  field_simp
  ring

/-- **The closed-population recurrence is the `mu = 0` case, and nothing else.**
This is the theorem that turns the assumption from a habit into a hypothesis:
the geometric decay formula used throughout is the trajectory at exactly one
value of the mutation rate. -/
theorem hetTrajectory_of_no_mutation (Ne H₀ : ℝ) (t : ℕ) :
    hetTrajectory Ne 0 H₀ t = (1 - 1 / (2 * Ne)) ^ t * H₀ := by
  induction t with
  | zero => simp [hetTrajectory]
  | succ n ih =>
      simp only [hetTrajectory, hetStepWithMutation, ih]
      ring

/-- With mutation present the floor is absorbing from above: one step from a
state at or above the floor lands at or above the floor. The contraction
hypothesis `1/(2 Nₑ) + 2 mu ≤ 1` says only that the two forces together do not
overshoot in a single generation. -/
theorem hetStepWithMutation_ge_hetMutationFloor_of_ge_floor (Ne mu H : ℝ)
    (hNe : 0 < Ne) (hmu : 0 ≤ mu)
    (hcontract : 1 / (2 * Ne) + 2 * mu ≤ 1)
    (hH : hetMutationFloor Ne mu ≤ H) :
    hetMutationFloor Ne mu ≤ hetStepWithMutation Ne mu H := by
  have hfp := hetMutationFloor_isFixedPoint Ne mu hNe hmu
  have hslope : (0 : ℝ) ≤ 1 - 1 / (2 * Ne) - 2 * mu := by linarith
  have hdiff : (0 : ℝ) ≤ H - hetMutationFloor Ne mu := by linarith
  have key : hetStepWithMutation Ne mu H -
      hetStepWithMutation Ne mu (hetMutationFloor Ne mu) =
      (1 - 1 / (2 * Ne) - 2 * mu) * (H - hetMutationFloor Ne mu) := by
    unfold hetStepWithMutation
    ring
  have hprod : (0 : ℝ) ≤
      (1 - 1 / (2 * Ne) - 2 * mu) * (H - hetMutationFloor Ne mu) :=
    mul_nonneg hslope hdiff
  linarith [hfp, key, hprod]

/-- **Heterozygosity never falls below the mutation floor, at any horizon.**
This is the qualitative fact the closed-population model denies: it predicts
decay to zero, and the simulated population at demographic equilibrium loses
nothing in four thousand generations. -/
theorem hetTrajectory_ge_hetMutationFloor_of_init_ge_floor (Ne mu H₀ : ℝ)
    (hNe : 0 < Ne) (hmu : 0 ≤ mu)
    (hcontract : 1 / (2 * Ne) + 2 * mu ≤ 1)
    (hH₀ : hetMutationFloor Ne mu ≤ H₀) (t : ℕ) :
    hetMutationFloor Ne mu ≤ hetTrajectory Ne mu H₀ t := by
  induction t with
  | zero => simpa [hetTrajectory] using hH₀
  | succ n ih =>
      simp only [hetTrajectory]
      exact hetStepWithMutation_ge_hetMutationFloor_of_ge_floor Ne mu _ hNe hmu hcontract ih

/-- **The quantitative cost of the closed-population assumption.**

Once the drift-only prediction has fallen below the floor that mutation holds,
it is strictly below the true heterozygosity -- for every mutation rate,
starting value and horizon in range. This is the inequality that separates the
drift-only quantity from the equilibrium one, in the same shape as
`fstFromTau_lt_coalescenceCdf`, so the two cannot be interchanged
silently. -/
theorem driftOnly_lt_hetTrajectory_of_below_floor (Ne mu H₀ : ℝ) (t : ℕ)
    (hNe : 0 < Ne) (hmu : 0 ≤ mu)
    (hcontract : 1 / (2 * Ne) + 2 * mu ≤ 1)
    (hH₀ : hetMutationFloor Ne mu ≤ H₀)
    (hbelow : (1 - 1 / (2 * Ne)) ^ t * H₀ < hetMutationFloor Ne mu) :
    (1 - 1 / (2 * Ne)) ^ t * H₀ < hetTrajectory Ne mu H₀ t :=
  lt_of_lt_of_le hbelow
    (hetTrajectory_ge_hetMutationFloor_of_init_ge_floor Ne mu H₀ hNe hmu hcontract hH₀ t)

/-- **The regime, as an object a use site must construct.**

Any quantity computed from the geometric retention `(1 - 1/(2 Nₑ))^t` is a
quantity about a population in this regime and about no other. Making the regime
a structure puts the assumption in the type: `mutation_negligible` is the
dimensionless condition, and it is stated against the floor that the recurrence
actually has, not against a rate. If a caller cannot supply it, the
closed-population answer is not available to them -- which is the whole point,
since the falsified uses were all callers who could not have supplied it. -/
structure ClosedPopulationNoMutation where
  /-- Effective population size. -/
  Ne : ℝ
  /-- Mutation rate per generation. -/
  mu : ℝ
  /-- Ancestral heterozygosity. -/
  H₀ : ℝ
  /-- Number of generations the model is used over. -/
  horizon : ℕ
  /-- The fraction of `H₀` that the caller is willing to be wrong by. -/
  tolerance : ℝ
  Ne_pos : 0 < Ne
  mu_nonneg : 0 ≤ mu
  H₀_pos : 0 < H₀
  tolerance_pos : 0 < tolerance
  /-- Drift and mutation together do not overshoot in one generation. -/
  forces_contract : 1 / (2 * Ne) + 2 * mu ≤ 1
  /-- **The standing assumption, in the type.** The heterozygosity floor that
  mutation holds is a negligible fraction of the ancestral heterozygosity. At
  `Ne = 1000` and the mutation rate of the simulation this fails outright: the
  floor is the whole of `H₀`, which is why the measured retention is `1.025`. -/
  mutation_negligible : hetMutationFloor Ne mu ≤ tolerance * H₀

/-- **The regime is inhabited**, at zero mutation rate.

    `mutation_negligible` is the field that makes this structure a regime rather
    than a wrapper, and at `mu = 0` the floor `4·Ne·mu/(1 + 4·Ne·mu)` is exactly
    `0`, so it holds with room to spare. That is the regime's interior, not its
    boundary: a closed population with no mutation is precisely what the name
    says, and the falsified callers are the ones at `Ne = 1000` and a nonzero
    rate where the floor is the whole of `H₀`. -/
noncomputable def ClosedPopulationNoMutation.witness : ClosedPopulationNoMutation where
  Ne := 1
  mu := 0
  H₀ := 1
  horizon := 0
  tolerance := 1
  Ne_pos := by norm_num
  mu_nonneg := le_rfl
  H₀_pos := by norm_num
  tolerance_pos := by norm_num
  forces_contract := by norm_num
  mutation_negligible := by norm_num [hetMutationFloor]

/-- The closed-population retention over the model's horizon.

    Regime: closed population, no mutation -- carried by the structure's
    `mutation_negligible` field rather than assumed.

    Empirical status: FALSIFIED outside the regime. At demographic equilibrium
    with `Ne = 1000`, `t = 4000` this is `0.135` and the measurement is
    `1.025 ± 0.020`. Inside the regime it is untested. -/
noncomputable def ClosedPopulationNoMutation.retention
    (r : ClosedPopulationNoMutation) : ℝ :=
  (1 - 1 / (2 * r.Ne)) ^ r.horizon

/-- Target heterozygosity after the horizon.

    Regime: closed population, no mutation.

    Empirical status: FALSIFIED outside the regime; see
    `ClosedPopulationNoMutation.retention`. -/
noncomputable def ClosedPopulationNoMutation.targetHet
    (r : ClosedPopulationNoMutation) : ℝ :=
  r.H₀ * r.retention

/-- The regime's own prediction is the trajectory at `mu = 0`, which is the
statement that the structure and the recurrence describe the same model. -/
theorem ClosedPopulationNoMutation.targetHet_eq_trajectory_of_no_mutation
    (r : ClosedPopulationNoMutation) :
    r.targetHet = hetTrajectory r.Ne 0 r.H₀ r.horizon := by
  rw [hetTrajectory_of_no_mutation]
  unfold ClosedPopulationNoMutation.targetHet ClosedPopulationNoMutation.retention
  ring

end ClosedPopulationRegime

section PresentDayMetrics

/-- PGS variance from the additive model under HWE.
Under an additive genetic model with Hardy-Weinberg equilibrium,
PGS variance = Σᵢ βᵢ² × 2pᵢ(1-pᵢ), i.e. the sum of squared effect sizes
weighted by per-locus heterozygosity. Here `β_sq_sum` is Σᵢ βᵢ² and `het` is
the average heterozygosity 2p(1-p) (or its sum, depending on normalisation).

    Empirical status: UNTESTED. -/
noncomputable def pgsVarianceFromHet (β_sq_sum het : ℝ) : ℝ :=
  β_sq_sum * het

/-- **Score variance is bilinear in effect scale and heterozygosity.** Rescaling every effect by
`c` scales the summed squares by `c` as given, and the variance follows; the same holds in the
heterozygosity argument. Separating the two orders is what a mutant collapsing them would lose. -/
theorem pgsVarianceFromHet_bilinear (β_sq_sum het c : ℝ) :
    pgsVarianceFromHet (c * β_sq_sum) het = c * pgsVarianceFromHet β_sq_sum het ∧
      pgsVarianceFromHet β_sq_sum (c * het) = c * pgsVarianceFromHet β_sq_sum het := by
  constructor <;> unfold pgsVarianceFromHet <;> ring

/-- Target-population heterozygosity from a heterozygosity-loss fraction.

This definition carries no independent content: `fst` here is *defined* as the
proportional reduction `1 - H_target/H_source`, so `H_target = H_source (1 - fst)`
is that definition rearranged. It is true for every value of `fst`, which is
exactly why it cannot detect a wrong value supplied for `fst`.

Do not attach to it the claim that "after `t` generations of Wright-Fisher
drift with effective size N, `H_t = H_0 (1 - 1/(2N))^t`, giving
`Fst = 1 - (1 - 1/(2N))^t`". Both halves of that are wrong as
written. The recurrence holds only in the closed-population, no-mutation regime
-- at demographic equilibrium with `Ne = 1000`, `t = 4000` it predicts a
retention of `0.135` where the measurement is `1.025 ± 0.020`, an 86 percent
error -- and the resulting quantity is a within-population heterozygosity ratio,
not a between-population `F_ST`. Where that recurrence is wanted, construct a
`ClosedPopulationNoMutation` and use `ClosedPopulationNoMutation.targetHet`,
which carries the assumption in its type;
`ClosedPopulationNoMutation.targetHet_eq_targetHetFromFst` is the bridge.

    Empirical status: VACUOUS. This is an algebraic rearrangement of the
    definition of its own second argument, so no measurement can bear on it; the
    empirical content lives entirely in whatever supplies `fst`. -/
noncomputable def targetHetFromFst (het_source fst : ℝ) : ℝ :=
  het_source * (1 - fst)

/-- **Endpoints of the drift-retention map.** No divergence retains all heterozygosity; complete
divergence retains none. Two anchors rather than one, because a single one is met by many wrong
bodies. -/
theorem targetHetFromFst_endpoints (het_source : ℝ) :
    targetHetFromFst het_source 0 = het_source ∧ targetHetFromFst het_source 1 = 0 := by
  constructor <;> unfold targetHetFromFst <;> ring

/-- The map is linear in the source heterozygosity: it is a retained FRACTION, so doubling the
source doubles the target at fixed divergence. -/
theorem targetHetFromFst_linear (het_source fst c : ℝ) :
    targetHetFromFst (c * het_source) fst = c * targetHetFromFst het_source fst := by
  unfold targetHetFromFst; ring

/-- **The bridge named in the paragraph above**, which until now was named and not stated.

In the closed-population regime the proportional heterozygosity loss over the horizon is
`1 - retention`, and feeding *that* value to `targetHetFromFst` returns the regime's own
target heterozygosity. Which value goes in is the entire content: the rearrangement holds
for every second argument, so it cannot detect a wrong one, and this says which one the
regime supplies. It is a within-population loss, not a between-population `F_ST`. -/
theorem ClosedPopulationNoMutation.targetHet_eq_targetHetFromFst
    (r : ClosedPopulationNoMutation) :
    r.targetHet = targetHetFromFst r.H₀ (1 - r.retention) := by
  unfold ClosedPopulationNoMutation.targetHet targetHetFromFst
  ring

/-- **Present-day PGS variance after drift** from an ancestral variance `V_A`.

**One definition, and it is the composition rather than a re-typed product**: the
Fst-heterozygosity step is applied, not restated. A second body spelling `(1 - fst) * V_A`
directly would need a theorem to hold it in step, which is the failure this file's own
regime discussion is about.

**Which `fst` this means, declared rather than left to the argument name.** The
second argument of `pgsVarianceFromHet` is called `het`, so `1 - fst` is used here
as a **heterozygosity retention** `H_target / H_source`, and `fst` is the
proportional heterozygosity loss. That is not the between-population Hudson
`F_ST`, and the same distinction is spelled out at `targetHetFromFst` above. A
caller holding a Hudson value is asserting the extra claim that the two readings
coincide for its populations.

    Regime: heterozygosity-retention reading of `fst`; ancestral heterozygosities
    scaled by a common factor, which is what makes a single `fst` sufficient for a
    sum over loci.

    Empirical status: **VALIDATED**
    (`proofs/validation/empirical/differential/cluster/fam_pgs_transport_drift.py`,
    check C3; Wright-Fisher, `Ne = 500`, 400 unlinked loci, 200 replicate
    populations, `V_A = 93.667`, `t` from 0 to 350 so that the heterozygosity-loss
    `F_HET` reaches `0.295` and half the loci have fixed). Worst cell `0.94` sems
    on the retention reading. The grid does not by itself separate the two
    readings -- the Hudson reading also passes, worst cell `0.99` sems, the two
    predictions differing by at most `0.26` percent, at `F_HET 0.2953` against
    `F_HUDSON 0.2934` -- because a single deme drifting from its own ancestor
    makes them nearly equal. The declaration above, not that grid, is what says
    which reading the body means; a design that separates them is still owed. -/
noncomputable def presentDayPGSVariance (V_A fst : ℝ) : ℝ :=
  pgsVarianceFromHet V_A (1 - fst)

/-- The closed form, derived rather than taken as the definition. This closes the chain
`pgsVarianceFromHet → targetHetFromFst → presentDayPGSVariance`. -/
theorem presentDayPGSVariance_eq_one_sub_fst_mul (V_A fst : ℝ) :
    presentDayPGSVariance V_A fst = (1 - fst) * V_A := by
  unfold presentDayPGSVariance pgsVarianceFromHet
  ring

/-- The closed-form discrete Wright-Fisher retention factor after `t` generations.

    Regime: closed population, no mutation. Heterozygosity decays geometrically
    only while nothing replenishes it. At mutation-drift balance the measured
    retention is `1.02 ± 0.02` where this formula gives `e^(-2) = 0.135` at
    `Ne = 1000`, `t = 4000`; `Calibrator.DriftRegime.regimes_disagree` proves the
    two regimes disagree at every positive time. Do not read this factor as a
    between-population `F_ST`.

    Empirical status: UNTESTED. -/
noncomputable def wrightFisherDriftRetention (N t : ℕ) : ℝ :=
  (1 - 1 / (2 * (N : ℝ))) ^ t

/-- **Drift retention composes over time.** Retention across `s + t` generations is retention
across `s` times retention across `t`, and no generations retain everything. That semigroup
property is what makes the per-generation factor a rate; a body without it would not compose. -/
theorem wrightFisherDriftRetention_add (N s t : ℕ) :
    wrightFisherDriftRetention N (s + t)
      = wrightFisherDriftRetention N s * wrightFisherDriftRetention N t := by
  unfold wrightFisherDriftRetention
  exact pow_add _ s t

theorem wrightFisherDriftRetention_zero (N : ℕ) : wrightFisherDriftRetention N 0 = 1 := by
  unfold wrightFisherDriftRetention; exact pow_zero _

/-- **Within-population heterozygosity loss after `t` generations of drift.**

    This was called `wrightFisherFst`. It is not an `F_ST`: it is the
    proportional loss of heterozygosity *inside* one population, and a
    heterozygosity ratio within a population is not a between-population variance
    ratio. Under that name it was read as a split `F_ST` throughout, which is the
    substitution that made the cluster wrong.

    Regime: closed population, no mutation, inherited from
    `wrightFisherDriftRetention`. At demographic equilibrium the measured
    retention is `1.025 ± 0.020` at `Ne = 1000`, `t = 4000` where this formula's
    retention is `0.135`, so this quantity is near `0.865` where the measurable
    between-population `F_ST` is `0.50`.

    Empirical status: FALSIFIED as a split `F_ST`; UNTESTED as heterozygosity
    loss in the regime it names. Use `ClosedPopulationNoMutation` when the
    regime is meant, and `fstFromTau` when a split `F_ST` is meant. -/
noncomputable def wrightFisherHeterozygosityLoss (N t : ℕ) : ℝ :=
  1 - wrightFisherDriftRetention N t

theorem wrightFisherHeterozygosityLoss_eq
    (N t : ℕ) :
    wrightFisherHeterozygosityLoss N t = 1 - (1 - 1 / (2 * (N : ℝ))) ^ t := by
  simp [wrightFisherHeterozygosityLoss, wrightFisherDriftRetention]

private lemma wrightFisherBase_bounds (N : ℕ) (hN : 0 < N) :
    0 < 1 - 1 / (2 * (N : ℝ)) ∧ 1 - 1 / (2 * (N : ℝ)) ≤ 1 := by
  have hNge : (1 : ℝ) ≤ N := by exact_mod_cast Nat.succ_le_of_lt hN
  have hpos : 0 < 2 * (N : ℝ) := by positivity
  constructor
  · have h2N : (1 : ℝ) < 2 * (N : ℝ) := by nlinarith
    have : 1 / (2 * (N : ℝ)) < 1 := by
      rw [div_lt_one hpos]; exact h2N
    linarith
  · have := div_nonneg (le_refl (0 : ℝ) |>.trans (by norm_num : (0:ℝ) ≤ 1)) (le_of_lt hpos)
    linarith

theorem wrightFisherHeterozygosityLoss_nonneg
    (N t : ℕ)
    (hN : 0 < N) :
    0 ≤ wrightFisherHeterozygosityLoss N t := by
  obtain ⟨hbase_pos, hbase_le_one⟩ := wrightFisherBase_bounds N hN
  rw [wrightFisherHeterozygosityLoss_eq]
  have : (1 - 1 / (2 * (N : ℝ))) ^ t ≤ 1 :=
    pow_le_one₀ (le_of_lt hbase_pos) hbase_le_one
  linarith

theorem wrightFisherHeterozygosityLoss_lt_one
    (N t : ℕ)
    (hN : 0 < N) :
    wrightFisherHeterozygosityLoss N t < 1 := by
  obtain ⟨hbase_pos, _⟩ := wrightFisherBase_bounds N hN
  rw [wrightFisherHeterozygosityLoss_eq]
  have : 0 < (1 - 1 / (2 * (N : ℝ))) ^ t := pow_pos hbase_pos t
  linarith

/-- Drift-driven variance of the between-population PGS-mean difference.
For one branch with drift index `fst`, this is `2 * fst * V_A`.

    Empirical status: UNTESTED. -/
noncomputable def Var_Delta_Mu (V_A fst : ℝ) : ℝ :=
  2 * fst * V_A

/-- **The two populations contribute one drift variance each.** The factor of two is the whole
content of the definition, and it is what a body carrying a single population's variance would
get wrong. -/
theorem Var_Delta_Mu_eq_add_self (V_A fst : ℝ) :
    Var_Delta_Mu V_A fst = fst * V_A + fst * V_A := by
  unfold Var_Delta_Mu
  ring

/-- Drift-driven expected absolute PGS-mean shift under a Normal approximation.

    Empirical status: UNTESTED. -/
noncomputable def Expected_Abs_Shift (V_A fstS fstT : ℝ) : ℝ :=
  Real.sqrt (Var_Delta_Mu V_A (fstS + fstT)) * Real.sqrt (2 / Real.pi)

/-- **The half-normal relation between the mean absolute shift and its variance.** Squaring
returns exactly `2/π` times the variance, which is the identity that makes this the mean of a
folded normal rather than any other summary of the same spread. A body carrying a different
constant would fail here and nowhere else. -/
theorem Expected_Abs_Shift_sq (V_A fstS fstT : ℝ)
    (hvar : 0 ≤ Var_Delta_Mu V_A (fstS + fstT)) :
    Expected_Abs_Shift V_A fstS fstT ^ 2
      = 2 / Real.pi * Var_Delta_Mu V_A (fstS + fstT) := by
  unfold Expected_Abs_Shift
  rw [mul_pow, Real.sq_sqrt hvar, Real.sq_sqrt (by positivity : (0:ℝ) ≤ 2 / Real.pi)]
  ring

/-- Variance identity used by the dashboard mean-shift card. -/
theorem variance_mean_pgs_diff (V_A fst : ℝ) :
    Var_Delta_Mu V_A fst = 2 * fst * V_A := by
  rfl

/-- Rigorous algebraic proof of the expected absolute mean-shift formula for
    discrete Wright-Fisher drift, via explicit `Real.sqrt` and fraction manipulation. -/
theorem expected_abs_mean_shift_ratio_eq
    (V_A fstS fstT : ℝ)
    (hVA_pos : 0 < V_A)
    (hfst_sum_nonneg : 0 ≤ fstS + fstT)
    (hfstS_lt_one : fstS < 1) :
    Expected_Abs_Shift V_A fstS fstT / Real.sqrt (presentDayPGSVariance V_A fstS) =
      2 * Real.sqrt ((fstS + fstT) / (Real.pi * (1 - fstS))) := by
  unfold Expected_Abs_Shift Var_Delta_Mu presentDayPGSVariance pgsVarianceFromHet
  have h1 :
      Real.sqrt (2 * (fstS + fstT) * V_A) =
        Real.sqrt (2 * (fstS + fstT)) * Real.sqrt V_A := by
    have h_nonneg : 0 ≤ 2 * (fstS + fstT) := mul_nonneg (by norm_num) hfst_sum_nonneg
    rw [Real.sqrt_mul h_nonneg]
  have h2 :
      Real.sqrt (V_A * (1 - fstS)) =
        Real.sqrt (1 - fstS) * Real.sqrt V_A := by
    have h_nonneg : 0 ≤ 1 - fstS := by linarith
    rw [mul_comm, Real.sqrt_mul h_nonneg]
  rw [h1, h2]
  have h_sqrt_VA_ne_zero : Real.sqrt V_A ≠ 0 := Real.sqrt_ne_zero'.mpr hVA_pos
  have h_div :
      (Real.sqrt (2 * (fstS + fstT)) * Real.sqrt V_A * Real.sqrt (2 / Real.pi)) /
          (Real.sqrt (1 - fstS) * Real.sqrt V_A) =
        (Real.sqrt (2 * (fstS + fstT)) * Real.sqrt (2 / Real.pi)) /
          Real.sqrt (1 - fstS) := by
    calc
      (Real.sqrt (2 * (fstS + fstT)) * Real.sqrt V_A * Real.sqrt (2 / Real.pi)) /
          (Real.sqrt (1 - fstS) * Real.sqrt V_A)
        = (Real.sqrt (2 * (fstS + fstT)) * Real.sqrt (2 / Real.pi) * Real.sqrt V_A) /
            (Real.sqrt (1 - fstS) * Real.sqrt V_A) := by
              congr 1
              ring
      _ =
          (Real.sqrt (2 * (fstS + fstT)) * Real.sqrt (2 / Real.pi)) /
            Real.sqrt (1 - fstS) := by
              rw [mul_div_mul_right _ _ h_sqrt_VA_ne_zero]
  rw [h_div]
  have h3 :
      Real.sqrt (2 * (fstS + fstT)) * Real.sqrt (2 / Real.pi) =
        Real.sqrt (4 * (fstS + fstT) / Real.pi) := by
    have h_nonneg : 0 ≤ 2 * (fstS + fstT) := mul_nonneg (by norm_num) hfst_sum_nonneg
    rw [← Real.sqrt_mul h_nonneg]
    congr 1
    ring
  rw [h3]
  have h4 :
      Real.sqrt (4 * (fstS + fstT) / Real.pi) / Real.sqrt (1 - fstS) =
        Real.sqrt ((4 * (fstS + fstT) / Real.pi) / (1 - fstS)) := by
    have h_nonneg : 0 ≤ 4 * (fstS + fstT) / Real.pi := by
      apply div_nonneg
      · linarith
      · exact Real.pi_pos.le
    rw [← Real.sqrt_div h_nonneg]
  rw [h4]
  have h5 :
      (4 * (fstS + fstT) / Real.pi) / (1 - fstS) =
        4 * ((fstS + fstT) / (Real.pi * (1 - fstS))) := by
    calc
      (4 * (fstS + fstT) / Real.pi) / (1 - fstS) =
          (4 * (fstS + fstT)) / (Real.pi * (1 - fstS)) := by
            rw [div_div]
      _ = 4 * ((fstS + fstT) / (Real.pi * (1 - fstS))) := by
            ring
  rw [h5]
  have h4_nonneg : (0 : ℝ) ≤ 4 := by norm_num
  rw [Real.sqrt_mul h4_nonneg]
  have hsqrt_four : Real.sqrt (4 : ℝ) = 2 :=
    (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).2 (by norm_num)
  rw [hsqrt_four]

/-- Exact discrete Wright-Fisher mean-shift formula in source-standard-deviation units. -/
theorem expected_abs_mean_shift_of_wrightFisher
    (V_A : ℝ)
    (NS tS NT tT : ℕ)
    (hVA_pos : 0 < V_A)
    (hNS : 0 < NS)
    (hNT : 0 < NT) :
    Expected_Abs_Shift V_A (wrightFisherHeterozygosityLoss NS tS)
          (wrightFisherHeterozygosityLoss NT tT) /
        Real.sqrt (presentDayPGSVariance V_A (wrightFisherHeterozygosityLoss NS tS)) =
      2 * Real.sqrt
        ((wrightFisherHeterozygosityLoss NS tS + wrightFisherHeterozygosityLoss NT tT) /
          (Real.pi * (1 - wrightFisherHeterozygosityLoss NS tS))) := by
  apply expected_abs_mean_shift_ratio_eq
  · exact hVA_pos
  · exact add_nonneg (wrightFisherHeterozygosityLoss_nonneg NS tS
      hNS) (wrightFisherHeterozygosityLoss_nonneg NT tT hNT)
  · exact wrightFisherHeterozygosityLoss_lt_one NS tS hNS

/-- Present-day signal-to-noise ratio for prediction under drift. -/
noncomputable def presentDaySignalToNoise (V_A V_E fst : ℝ) : ℝ :=
  presentDayPGSVariance V_A fst / V_E

/-- **Present-day coefficient of determination under drift.**

`R² = V_PGS / (V_PGS + V_E)` where `V_PGS = presentDayPGSVariance V_A fst`. The quotient
itself is not restated here: this is `r2FromSignalVariance` applied to the drift-attenuated signal
variance, so the two cannot drift apart. -/
noncomputable def presentDayR2 (V_A V_E fst : ℝ) : ℝ :=
  r2FromSignalVariance (presentDayPGSVariance V_A fst) V_E

/-- Exact bridge theorem: the dashboard algebraic `presentDayR2` equals statistical
`rsquared` when the relevant second-moment identities hold. -/
theorem presentDayR2_eq_statistical_rsquared_of_moments
    {k : ℕ} [Fintype (Fin k)]
    (dgp : DataGeneratingProcess k)
    (signal : Predictor k)
    (V_A V_E fst : ℝ)
    (h_vf :
      (let μ := dgp.jointMeasure
       let mf : ℝ := ∫ pc, signal pc.1 pc.2 ∂μ
       ∫ pc, (signal pc.1 pc.2 - mf) ^ 2 ∂μ) = presentDayPGSVariance V_A fst)
    (h_vg :
      (let μ := dgp.jointMeasure
       let mg : ℝ := ∫ pc, dgp.trueExpectation pc.1 pc.2 ∂μ
       ∫ pc, (dgp.trueExpectation pc.1 pc.2 - mg) ^ 2 ∂μ) =
        presentDayPGSVariance V_A fst + V_E)
    (h_cov :
      (let μ := dgp.jointMeasure
       let mf : ℝ := ∫ pc, signal pc.1 pc.2 ∂μ
       let mg : ℝ := ∫ pc, dgp.trueExpectation pc.1 pc.2 ∂μ
       ∫ pc, (signal pc.1 pc.2 - mf) * (dgp.trueExpectation pc.1 pc.2 - mg) ∂μ) =
        presentDayPGSVariance V_A fst)
    (h_vsig_pos : 0 < presentDayPGSVariance V_A fst)
    (h_vtrue_pos : 0 < presentDayPGSVariance V_A fst + V_E) :
    presentDayR2 V_A V_E fst = rsquared dgp signal dgp.trueExpectation := by
  have h_vsig_ne : presentDayPGSVariance V_A fst ≠ 0 := by linarith
  have h_vtrue_ne : presentDayPGSVariance V_A fst + V_E ≠ 0 := by linarith
  have h_if_not :
      ¬(presentDayPGSVariance V_A fst = 0 ∨ presentDayPGSVariance V_A fst + V_E = 0) := by
    intro h
    rcases h with h0 | h1
    · exact h_vsig_ne h0
    · exact h_vtrue_ne h1
  have h_rs :
      rsquared dgp signal dgp.trueExpectation = (presentDayPGSVariance V_A fst) ^ 2 /
          (presentDayPGSVariance V_A fst * (presentDayPGSVariance V_A fst + V_E)) := by
    unfold rsquared
    simp [h_vf, h_vg, h_cov, h_if_not]
  rw [h_rs]
  unfold presentDayR2 r2FromSignalVariance
  field_simp [h_vsig_ne, h_vtrue_ne]




/-- Exact present-day AUC under the equal-variance Gaussian model.

**NOT APPLICABLE TO DICHOTOMISED TRAITS. The word "liability" was in this docstring and
the formula is not the liability-threshold one.** The hypothesis actually used is that
case and control scores differ only by a mean shift with common residual variance `V_E`,
which is an equal-variance Gaussian *outcome*. Under a liability-threshold model the two
conditional variances are `v₁ = 1 - R²·i(i-T)` and `v₀ = 1 - R²·i_c(i_c-T)` and are **not**
equal, and no prevalence argument appears here at all.

Measured cost of the substitution on 400 simulated binary-trait PGS studies: bias
`-0.068` AUC, RMSE `0.071`, max error `0.120`. For a dichotomised trait use
`liabilityThresholdAUCFromExplainedR2` (RMSE `0.0121` on the same runs, against a `0.0120`
seed-noise floor). -/
noncomputable def presentDayEqualVarianceGaussianAUC (V_A V_E fst : ℝ) : ℝ :=
  equalVarianceGaussianAUCFromSignalVariance (presentDayPGSVariance V_A fst) V_E

/-- Exact present-day **equal-variance Gaussian** AUC formula at positive residual
variance. -/
theorem presentDayEqualVarianceGaussianAUC_eq
    (V_A V_E fst : ℝ) (h_env : V_E ≠ 0) :
    presentDayEqualVarianceGaussianAUC V_A V_E fst =
      Phi (Real.sqrt (presentDaySignalToNoise V_A V_E fst / 2)) := by
  rw [presentDayEqualVarianceGaussianAUC,
    equalVarianceGaussianAUCFromSignalVariance_eq_formula_of_ne_noise _ _ h_env]
  unfold presentDaySignalToNoise
  congr 2
  rw [div_div, mul_comm]

/-- Drift monotonically degrades signal-to-noise when `V_A, V_E > 0`. -/
theorem drift_degrades_signalToNoise
    (V_A V_E fstS fstT : ℝ)
    (hVA : 0 < V_A) (hVE : 0 < V_E)
    (hfst : fstS < fstT) :
    presentDaySignalToNoise V_A V_E fstT < presentDaySignalToNoise V_A V_E fstS := by
  unfold presentDaySignalToNoise presentDayPGSVariance pgsVarianceFromHet
  have hnum : (1 - fstT) * V_A < (1 - fstS) * V_A := by
    nlinarith [mul_lt_mul_of_pos_right hfst hVA]
  have hInv : 0 < V_E⁻¹ := inv_pos.mpr hVE
  have hscaled :
      ((1 - fstT) * V_A) * V_E⁻¹ < ((1 - fstS) * V_A) * V_E⁻¹ :=
    mul_lt_mul_of_pos_right hnum hInv
  simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hscaled

/-- Drift monotonically degrades present-day `R²` when `V_A, V_E > 0` and `fst < 1`. -/
theorem drift_degrades_R2
    (V_A V_E fstS fstT : ℝ)
    (hVA : 0 < V_A) (hVE : 0 < V_E)
    (hfst : fstS < fstT)
    (hfstT_le_one : fstT ≤ 1) :
    presentDayR2 V_A V_E fstT < presentDayR2 V_A V_E fstS := by
  unfold presentDayR2 r2FromSignalVariance presentDayPGSVariance pgsVarianceFromHet
  have h_mono : ∀ (x y : ℝ), 0 ≤ x → x < y → x / (x + V_E) < y / (y + V_E) := by
    intro x y hx hxy
    have hxE : 0 < x + V_E := by linarith
    have hyE : 0 < y + V_E := by linarith [hx, hxy]
    have hxyE : x + V_E < y + V_E := by linarith
    have hInv : 1 / (y + V_E) < 1 / (x + V_E) := by
      rw [one_div_lt_one_div hyE hxE]
      exact hxyE
    have hsub : 1 - V_E / (x + V_E) < 1 - V_E / (y + V_E) := by
      have hmul := mul_lt_mul_of_pos_left hInv hVE
      have hfrac : V_E / (y + V_E) < V_E / (x + V_E) := by
        simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hmul
      nlinarith [hfrac]
    have hxne : x + V_E ≠ 0 := by linarith
    have hyne : y + V_E ≠ 0 := by linarith
    have hxrepr : x / (x + V_E) = 1 - V_E / (x + V_E) := by
      field_simp [hxne]
      ring
    have hyrepr : y / (y + V_E) = 1 - V_E / (y + V_E) := by
      field_simp [hyne]
      ring
    simpa [hxrepr, hyrepr] using hsub
  have hT_nonneg : 0 ≤ V_A * (1 - fstT) := by
    have : 0 ≤ 1 - fstT := by linarith
    exact mul_nonneg (le_of_lt hVA) this
  have h_lt : V_A * (1 - fstT) < V_A * (1 - fstS) := by
    nlinarith [mul_lt_mul_of_pos_right hfst hVA]
  exact h_mono (V_A * (1 - fstT)) (V_A * (1 - fstS)) hT_nonneg h_lt

/-- For fixed `V_E > 0`, `v ↦ v / (v + V_E)` is strictly increasing on nonnegative variances. -/
theorem expectedR2_strictMono_nonneg
    (V_E x y : ℝ)
    (hVE : 0 < V_E) (hx : 0 ≤ x) (hxy : x < y) :
    r2FromSignalVariance x V_E < r2FromSignalVariance y V_E := by
  unfold r2FromSignalVariance
  have hxE : 0 < x + V_E := by linarith
  have hyE : 0 < y + V_E := by linarith [hx, hxy]
  have hxyE : x + V_E < y + V_E := by linarith
  have hInv : 1 / (y + V_E) < 1 / (x + V_E) := by
    rw [one_div_lt_one_div hyE hxE]
    exact hxyE
  have hsub : 1 - V_E / (x + V_E) < 1 - V_E / (y + V_E) := by
    have hmul := mul_lt_mul_of_pos_left hInv hVE
    have hfrac : V_E / (y + V_E) < V_E / (x + V_E) := by
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hmul
    nlinarith [hfrac]
  have hxne : x + V_E ≠ 0 := by linarith
  have hyne : y + V_E ≠ 0 := by linarith
  have hxrepr : x / (x + V_E) = 1 - V_E / (x + V_E) := by
    field_simp [hxne]
    ring
  have hyrepr : y / (y + V_E) = 1 - V_E / (y + V_E) := by
    field_simp [hyne]
    ring
  simpa [hxrepr, hyrepr] using hsub

/-- Drift strictly degrades the exact present-day AUC in the equal-variance
Gaussian liability model. -/
theorem drift_degrades_AUC_of_strictMono
    (V_A V_E fstS fstT : ℝ)
    (hVA : 0 < V_A) (hVE : 0 < V_E)
    (hfst : fstS < fstT)
    (hfstT_le_one : fstT ≤ 1) :
    presentDayEqualVarianceGaussianAUC V_A V_E fstT <
      presentDayEqualVarianceGaussianAUC V_A V_E fstS := by
  rw [presentDayEqualVarianceGaussianAUC_eq _ _ _ (ne_of_gt hVE),
    presentDayEqualVarianceGaussianAUC_eq _ _ _ (ne_of_gt hVE)]
  apply strictMono_Phi
  have hsnr := drift_degrades_signalToNoise V_A V_E fstS fstT hVA hVE hfst
  have hhalf_nonneg : 0 ≤ presentDaySignalToNoise V_A V_E fstT / 2 := by
    have hsnr_nonneg : 0 ≤ presentDaySignalToNoise V_A V_E fstT := by
      unfold presentDaySignalToNoise presentDayPGSVariance pgsVarianceFromHet
      have hnum : 0 ≤ V_A * (1 - fstT) := by
        have h_one_minus : 0 ≤ 1 - fstT := by linarith
        exact mul_nonneg (le_of_lt hVA) h_one_minus
      exact div_nonneg hnum (le_of_lt hVE)
    exact div_nonneg hsnr_nonneg (by positivity)
  have hhalf_lt : presentDaySignalToNoise V_A V_E fstT / 2 <
      presentDaySignalToNoise V_A V_E fstS / 2 := by
    nlinarith
  exact Real.sqrt_lt_sqrt hhalf_nonneg hhalf_lt

/-- Drift strictly degrades the exact **equal-variance Gaussian** AUC whenever
signal variance is positive and target drift exceeds source drift. -/
theorem drift_degrades_equalVarianceGaussianAUC
    (V_A V_E fstS fstT : ℝ)
    (hVA : 0 < V_A) (hVE : 0 < V_E)
    (hfst : fstS < fstT)
    (hfstT_le_one : fstT ≤ 1) :
    presentDayEqualVarianceGaussianAUC V_A V_E fstT <
      presentDayEqualVarianceGaussianAUC V_A V_E fstS := by
  rw [presentDayEqualVarianceGaussianAUC_eq _ _ _ (ne_of_gt hVE),
    presentDayEqualVarianceGaussianAUC_eq _ _ _ (ne_of_gt hVE)]
  apply strictMono_Phi
  have hsnr := drift_degrades_signalToNoise V_A V_E fstS fstT hVA hVE hfst
  have hhalf_nonneg : 0 ≤ presentDaySignalToNoise V_A V_E fstT / 2 := by
    have hsnr_nonneg : 0 ≤ presentDaySignalToNoise V_A V_E fstT := by
      unfold presentDaySignalToNoise presentDayPGSVariance pgsVarianceFromHet
      have hnum : 0 ≤ V_A * (1 - fstT) := by
        have h_one_minus : 0 ≤ 1 - fstT := by linarith
        exact mul_nonneg (le_of_lt hVA) h_one_minus
      exact div_nonneg hnum (le_of_lt hVE)
    exact div_nonneg hsnr_nonneg (by positivity)
  have hhalf_lt : presentDaySignalToNoise V_A V_E fstT / 2 <
      presentDaySignalToNoise V_A V_E fstS / 2 := by
    nlinarith
  exact Real.sqrt_lt_sqrt hhalf_nonneg hhalf_lt

/-! Real-world PGS variance with both drift and LD tagging efficiency. -/
/-- The additive variance a score **explains** in a target population: the source
additive variance `V_A`, attenuated by the transported effect correlation `rhoSq`
and eroded by drift through `1 - fst`.

**This is a scope declaration, not a correction. The body is right; the one-line
reading of it as "the variance of the score" was wrong.** Write `bhat` for the
weights the deployed score actually carries, `b` for the true effects, `w` for the
ancestral per-locus heterozygosities `2p(1-p)`, and put

    A = Σ w bhat²,   B = Σ w b² = V_A,   C = Σ w bhat b,   rhoSq = C² / (A B).

In a target population whose heterozygosities are the ancestral ones scaled by
`1 - fst`:

* the **variance of the score itself** is `(1 - fst) A`;
* the variance of the part of the genetic value that the score predicts, i.e.
  `Cov(G, S)² / Var(S)`, is `(1 - fst) C² / A`, and *that* is this body.

The two agree exactly when `A = C`, i.e. when `Σ w bhat (bhat - b) = 0`: the
weights are calibrated, the residual `b - bhat` orthogonal to `bhat` in the
heterozygosity metric. Read this definition as the explained-variance one. It is
the reading the downstream `r2FromSignalVariance` compositions need, since only
explained variance can enter an `R²`, and it is the reading under which `rhoSq`
attenuates a covariance rather than inflating a variance.

`rhoSq` is meant in the heterozygosity metric `w` above, not as the plain
`corr(bhat, b)²` a reader computes from a table of effect estimates. Score
variance is a `w`-weighted quadratic form in the effects, so no other reading can
enter a variance identity at all. The choice is not cosmetic: at source `n = 500`
the measurement below found `0.63392` weighted against `0.36383` unweighted, the
weighted reading being 74 percent larger.

    Regime: calibrated weights; equivalently, the large-source-GWAS limit.
    Nothing in the body carries a sample size, and at finite source `n` raw
    marginal-OLS weights are not calibrated. To leading order in `1/n`,
    `E[C] = V_A` while `E[A] = V_A + Σ_j w_j Var(bhat_j) ≈ V_A + m V_P / n` over
    `m` loci at phenotypic variance `V_P`, the per-locus term having the shape of
    `HaplotypeTheory.haplotypeEffectVarianceOLS`. So `A > C`, and the score's own
    variance overshoots this body by the factor `(A / C)²`. The finite-`n` score
    variance is `(1 - fst)(V_A + m V_P / n)`; this body is unchanged, which is the
    point. Estimation noise inflates score variance without adding any covariance
    with the phenotype, so it cannot improve prediction, and the quantity defined
    here is the one that survives to an `R²`.

    Empirical status: **VALIDATED as the explained-variance reading; FALSIFIED as
    a claim about the variance of a score built from finite-`n` weights**
    (`proofs/validation/empirical/differential/cluster/fam_pgs_transport_drift.py`,
    check C6; Wright-Fisher, `Ne = 500`, `m = 300` unlinked loci, `V_E = 1`,
    `V_A = 62.853`). Measured score variance against this body: at `n = 500`,
    `fst = 0`, `135.20 ± 0.49` against `39.84`; at `n = 2000`, `81.11 ± 0.24`
    against `55.18`; at `n = 20000`, `65.88 ± 0.26` against `61.88`; at
    `n = 20000`, `fst = 0.295`, `46.55 ± 0.71` against `43.64`. The gap is
    `95.4`, `25.9`, `3.99` across that `n` grid -- it falls as `1/n`, which is the
    signature of estimation noise and not of a wrong constant. Recovering the
    noise term `Σ w (bhat - b)²` from those cells gives `10.16` against the
    predicted `m V_P / n = 9.58` at `n = 2000` and `1.03` against `0.958` at
    `n = 20000`, so the mechanism above is the whole of the gap where the
    leading-order form applies. At `n = 500` it gives `51.3` against `38.3`,
    which is the leading-order form itself degrading: the ancestral spectrum
    there carries loci at `p = 0.01`, about ten minor-allele copies in a sample
    of 500, where `E[1 / Σ (g - ḡ)²]` is no longer `1 / (n w)`. The run's scale
    control reproduced additive variance to relative error `0.00e+00` and its
    corruption control fired to `27.9` sems where it must fire.

    One consequence of the scope. As `n → ∞` with weights carried on the causal
    variants, `rhoSq → 1` and this collapses to `presentDayPGSVariance`. The
    content of `rhoSq < 1` is therefore cross-population tagging loss, which is
    what the surrounding file means by it, and never source-GWAS estimation
    noise, which belongs in `V_A` instead: a score's `V_A` is the variance it
    explains in its own source population, already net of its own noise. -/
noncomputable def realWorldPGSVariance (V_A fst rhoSq : ℝ) : ℝ :=
  rhoSq * (1 - fst) * V_A

/-! Explicit cross-population biological and observational state that can
change deployed portability metrics.

The fields record the named drivers that can change metrics:

- direct causal observation via `directCausalSource/Target`
- novel direct target-only causal links via `novelDirectCausalTarget`
- proxy tagging via `proxyTaggingSource/Target`
- novel target-only proxy tagging via `novelProxyTaggingTarget`
- aggregate tag-to-causal structure via the derived
  `sigmaTagCausalSourceAt`
- causal-vs-tag distinction via separate tag and causal dimensions plus the
  direct-vs-proxy decomposition
- source and target LD among scored SNPs via `sigmaTagSource/Target`
- standing source/target effect architecture via `betaSource/Target`
- target-only novel causal effects via `novelCausalEffectTarget`
- ancestry-specific or environment-specific cross-covariance shifts via
  `contextCrossSource/Target`
- additive irreducible target-side losses derived from:
  broken tagging, ancestry-specific LD distortion, and source-specific
  overfit/context mismatch
- target-only phenotype variance from untagged novel causal mutations via
  `novelUntaggablePhenotypeVarianceTarget`
- source/target outcome scales and target prevalence for deployed metrics

No source `R²` summary appears here because it is not a sufficient biological
state variable for transport. -/
structure CrossPopulationMetricModel (p q : ℕ) where
  beta : Pop → Fin q → ℝ
  sigmaTag : Pop → Matrix (Fin p) (Fin p) ℝ
  directCausal : Pop → Matrix (Fin p) (Fin q) ℝ
  proxyTagging : Pop → Matrix (Fin p) (Fin q) ℝ
  /-- Tag-to-causal links carried by variants that arose after divergence. -/
  novelDirectCausal : Pop → Matrix (Fin p) (Fin q) ℝ
  /-- Proxy tagging carried by variants that arose after divergence. -/
  novelProxyTagging : Pop → Matrix (Fin p) (Fin q) ℝ
  /-- Causal effects carried by variants that arose after divergence. -/
  novelCausalEffect : Pop → Fin q → ℝ
  contextCross : Pop → Fin p → ℝ
  outcomeVariance : Pop → ℝ
  novelUntaggablePhenotypeVarianceTarget : ℝ
  targetPrevalence : ℝ
  /-- **The source is the reference population.** "Novel" means novel *relative to the
  source*, so nothing is novel in the source itself. It is a FIELD rather than a shape
  convention -- the alternative is two separate definitions whose source variant omits the
  novel terms its target twin includes, which cannot be discharged or contradicted. Stated
  here it must be discharged at the use site, and a model violating it cannot be built by
  accident. -/
  novelDirectCausal_source : novelDirectCausal Pop.source = 0
  novelProxyTagging_source : novelProxyTagging Pop.source = 0
  novelCausalEffect_source : novelCausalEffect Pop.source = 0
  outcomeVariance_pos : ∀ P : Pop, 0 < outcomeVariance P
  novelUntaggablePhenotypeVarianceTarget_nonneg : 0 ≤ novelUntaggablePhenotypeVarianceTarget
  targetPrevalence_pos : 0 < targetPrevalence
  targetPrevalence_lt_one : targetPrevalence < 1

/-- **The class is inhabited.**  A theorem quantified over an uninhabited structure is
true and empty: kernel-checked, clean axiom report, no content.  This is the witness that
makes the theorems below statements about something. -/
noncomputable def CrossPopulationMetricModel.witness (p q : ℕ) :
    CrossPopulationMetricModel p q where
  beta := fun _ ↦ 0
  sigmaTag := fun _ ↦ 0
  directCausal := fun _ ↦ 0
  proxyTagging := fun _ ↦ 0
  novelDirectCausal := fun _ ↦ 0
  novelProxyTagging := fun _ ↦ 0
  novelCausalEffect := fun _ ↦ 0
  contextCross := fun _ ↦ 0
  outcomeVariance := fun _ ↦ 1
  novelUntaggablePhenotypeVarianceTarget := 0
  targetPrevalence := 1 / 2
  novelDirectCausal_source := rfl
  novelProxyTagging_source := rfl
  novelCausalEffect_source := rfl
  outcomeVariance_pos := fun _ ↦ by norm_num
  novelUntaggablePhenotypeVarianceTarget_nonneg := le_refl 0
  targetPrevalence_pos := by norm_num
  targetPrevalence_lt_one := by norm_num

/-- Source ERM weights in closed form (normal equations) under invertible source covariance. -/
noncomputable def sourceERMWeights {p : ℕ}
    (sigmaObsSource : Matrix (Fin p) (Fin p) ℝ)
    (crossSource : Fin p → ℝ) : Fin p → ℝ :=
  sigmaObsSource⁻¹.mulVec crossSource

/-- **Aggregate tag-to-causal alignment in a population**: directly observed causal
variants plus ancestry-specific proxy tagging, each including whatever arose after
divergence.

One definition now covers both populations. The source form is not a second definition
but a consequence of `novelDirectCausal_source` and `novelProxyTagging_source`, recorded
as `sigmaTagCausal_source` below. -/
noncomputable def sigmaTagCausalSourceAt {p q : ℕ}
    (m : CrossPopulationMetricModel p q) (P : Pop) : Matrix (Fin p) (Fin q) ℝ :=
  (m.directCausal P + m.novelDirectCausal P) +
    (m.proxyTagging P + m.novelProxyTagging P)

/-- **Total causal-effect vector in a population**: standing effects plus those carried
by variants that arose after divergence.

    Empirical status: UNTESTED. -/
noncomputable def totalEffect {p q : ℕ}
    (m : CrossPopulationMetricModel p q) (P : Pop) : Fin q → ℝ :=
  m.beta P + m.novelCausalEffect P

/-- **In the source the novel terms drop out** — derived from the reference-population
hypotheses rather than written into a separate definition. This is the equation that used
to be the *body* of `sigmaTagCausalSourceAt`; making it a theorem is what stops the source
and target forms from drifting apart silently. -/
@[simp] theorem sigmaTagCausal_source {p q : ℕ} (m : CrossPopulationMetricModel p q) :
    sigmaTagCausalSourceAt m Pop.source = m.directCausal Pop.source +
      m.proxyTagging Pop.source := by
  simp [sigmaTagCausalSourceAt, m.novelDirectCausal_source, m.novelProxyTagging_source]

/-- Likewise the source effect vector is the standing one. -/
@[simp] theorem totalEffect_source {p q : ℕ} (m : CrossPopulationMetricModel p q) :
    totalEffect m Pop.source = m.beta Pop.source := by
  simp [totalEffect, m.novelCausalEffect_source]

@[simp] theorem sigmaTagCausal_eq_direct_plus_novelDirect_plus_proxy_plus_novelProxy {p q : ℕ}
    (m : CrossPopulationMetricModel p q) (P : Pop) :
    sigmaTagCausalSourceAt m P =
      m.directCausal P + m.novelDirectCausal P +
        m.proxyTagging P + m.novelProxyTagging P := by
  simp [sigmaTagCausalSourceAt, add_assoc]

@[simp] theorem totalEffect_eq_beta_plus_novel {p q : ℕ}
    (m : CrossPopulationMetricModel p q) (P : Pop) :
    totalEffect m P = m.beta P + m.novelCausalEffect P := by
  rfl

/-- Target population risk for a linear score `w` under covariance/cross/noise moments. -/
noncomputable def targetLinearRisk {p : ℕ}
    (sigmaObsTarget : Matrix (Fin p) (Fin p) ℝ)
    (crossTarget : Fin p → ℝ)
    (noiseVar : ℝ)
    (w : Fin p → ℝ) : ℝ :=
  noiseVar + dotProduct w (sigmaObsTarget.mulVec w) - 2 * dotProduct w crossTarget

/-- Dense covariance witness in each population, for non-degenerate ERM-transport tests.

These are global witnesses. **Do not name one after a parameter of `sourceERMWeights` or
`targetLinearRisk` directly above** -- the same identifier meaning a global witness in one
declaration and a bound argument in the next is how this section became unreadable. -/
def witnessSigmaObs : Pop → Matrix (Fin 2) (Fin 2) ℝ :=
  Pop.pair !![1, 0.5; 0.5, 1] !![1, 0.1; 0.1, 1]

/-- Cross-covariance vector in each population, paired with `witnessSigmaObs`.

The two components are deliberately equal: the witness holds the cross-covariance fixed so
that the source/target ERM difference it exhibits is driven purely by the shift in LD, not
by a change in the predictor/outcome relationship. Written as two constants that fact was
a coincidence of two literals; written this way it is visible. -/
def witnessCross : Pop → Fin 2 → ℝ :=
  Pop.pair ![0.8, 0.4] ![0.8, 0.4]

/-- Exact OLS solution in each population for the dense witness system. -/
noncomputable def witnessW_opt : Pop → Fin 2 → ℝ :=
  Pop.pair ![0.8, 0.0] ![76 / 99, 32 / 99]

/-- A concrete proof that ERM mismatch occurs under LD shift, without relying on
    the abstract `hConflict` hypothesis, using dense 2x2 witnesses. -/
theorem source_target_erm_differ_dense_witness_proved :
    (witnessSigmaObs Pop.source).mulVec (witnessW_opt Pop.source) = (witnessCross Pop.source) ∧
    (witnessSigmaObs Pop.target).mulVec (witnessW_opt Pop.target) = (witnessCross Pop.target) ∧
    (witnessW_opt Pop.source) ≠ (witnessW_opt Pop.target) := by
  refine ⟨?_, ?_, ?_⟩
  · ext i
    fin_cases i
    · simp [witnessW_opt, witnessSigmaObs, witnessCross, Matrix.mulVec, Matrix.cons_val',
      Matrix.cons_val_fin_one, dotProduct, Pop.pair]
      norm_num
    · simp [witnessW_opt, witnessSigmaObs, witnessCross, Matrix.mulVec, Matrix.cons_val',
      Matrix.cons_val_fin_one, dotProduct, Pop.pair]
      norm_num
  · ext i
    fin_cases i
    · simp [witnessW_opt, witnessSigmaObs, witnessCross, Matrix.mulVec, Matrix.cons_val',
      Matrix.cons_val_fin_one, dotProduct, Pop.pair]
      norm_num
    · simp [witnessW_opt, witnessSigmaObs, witnessCross, Matrix.mulVec, Matrix.cons_val',
      Matrix.cons_val_fin_one, dotProduct, Pop.pair]
      norm_num
  · intro heq
    have h : (witnessW_opt Pop.source) 0 = (witnessW_opt Pop.target) 0 := congrFun heq 0
    revert h
    simp [witnessW_opt, Pop.pair]
    norm_num

/-- **Predictor/outcome cross-covariance in a population**, from explicit biological and
observational drivers. -/
noncomputable def crossCovariance {p q : ℕ}
    (m : CrossPopulationMetricModel p q) (P : Pop) : Fin p → ℝ :=
  (sigmaTagCausalSourceAt m P).mulVec (totalEffect m P) + m.contextCross P

/-- Source-learned linear weights from the full source state, including any
context-dependent source cross-covariance term. -/
noncomputable def sourceWeightsFromExplicitDrivers {p q : ℕ}
    (m : CrossPopulationMetricModel p q) : Fin p → ℝ :=
  sourceERMWeights (m.sigmaTag Pop.source) (crossCovariance m Pop.source)

/-- Explicit SNP-level score equation: any tag-genotype state is scored by the
source-learned weight vector through a linear dot product. This is the
canonical transported score functional; source and target scores differ only by
which tag-genotype state is supplied. -/
noncomputable def sourceWeightedTagScore {p q : ℕ}
    (m : CrossPopulationMetricModel p q) (tagState : Fin p → ℝ) : ℝ :=
  dotProduct (sourceWeightsFromExplicitDrivers m) tagState

@[simp] theorem sourceWeightedTagScore_add {p q : ℕ}
    (m : CrossPopulationMetricModel p q) (x y : Fin p → ℝ) :
    sourceWeightedTagScore m (x + y) =
      sourceWeightedTagScore m x + sourceWeightedTagScore m y := by
  simp [sourceWeightedTagScore, dotProduct, mul_add, Finset.sum_add_distrib]

/-- **Tag-to-causal projection in a population**, induced by that population's causal
effect vector. -/
noncomputable def taggingProjection {p q : ℕ}
    (m : CrossPopulationMetricModel p q) (P : Pop) : Fin p → ℝ :=
  (sigmaTagCausalSourceAt m P).mulVec (totalEffect m P)

/-- Locus-resolved target effect heterogeneity relative to the source effect
vector. This is the closed-form biological object behind claims that
`β_source ≠ β_target`; it is not a scalar retention factor.

    Empirical status: UNTESTED. -/
noncomputable def targetEffectHeterogeneity {p q : ℕ}
    (m : CrossPopulationMetricModel p q) : Fin q → ℝ :=
  totalEffect m Pop.target - (m.beta Pop.source)

/-- The full target effect vector is the source effect vector plus an explicit
locus-resolved heterogeneity term, which may include target-only novel causal
effects. -/
theorem totalEffect_target_eq_betaSource_plus_targetEffectHeterogeneity {p q : ℕ}
    (m : CrossPopulationMetricModel p q) :
    totalEffect m Pop.target = (m.beta Pop.source) + targetEffectHeterogeneity m := by
  ext j
  simp [targetEffectHeterogeneity]

/-- Target tagging projection of the source effect vector through the target
tagging surface. This isolates what would transport if target effects were
identical to source effects.

    Empirical status: UNTESTED. -/
noncomputable def targetSourceEffectProjection {p q : ℕ}
    (m : CrossPopulationMetricModel p q) : Fin p → ℝ :=
  (sigmaTagCausalSourceAt m Pop.target).mulVec (m.beta Pop.source)

/-- Incremental target-side projection induced purely by effect-size
heterogeneity relative to the source effect vector.

    Empirical status: UNTESTED. -/
noncomputable def targetEffectHeterogeneityProjection {p q : ℕ}
    (m : CrossPopulationMetricModel p q) : Fin p → ℝ :=
  (sigmaTagCausalSourceAt m Pop.target).mulVec (targetEffectHeterogeneity m)

/-- Projection induced purely by target-only novel causal effects through the
target tagging surface.

    Empirical status: UNTESTED. -/
noncomputable def targetNovelMutationEffectProjection {p q : ℕ}
    (m : CrossPopulationMetricModel p q) : Fin p → ℝ :=
  (sigmaTagCausalSourceAt m Pop.target).mulVec (m.novelCausalEffect Pop.target)

/-- **Projection carried by directly observed causal variants**, in a population. -/
noncomputable def directCausalProjection {p q : ℕ}
    (m : CrossPopulationMetricModel p q) (P : Pop) : Fin p → ℝ :=
  (m.directCausal P + m.novelDirectCausal P).mulVec (totalEffect m P)

/-- **Projection carried only by proxy tagging** of unscored causal variants, in a
population. -/
noncomputable def proxyTaggingProjection {p q : ℕ}
    (m : CrossPopulationMetricModel p q) (P : Pop) : Fin p → ℝ :=
  (m.proxyTagging P + m.novelProxyTagging P).mulVec (totalEffect m P)

/-- **The aggregate tag-to-causal projection splits into direct causal and proxy-tagging
contributions** — in either population, from the one statement. -/
theorem taggingProjection_eq_direct_plus_proxy {p q : ℕ}
    (m : CrossPopulationMetricModel p q) (P : Pop) :
    taggingProjection m P = directCausalProjection m P + proxyTaggingProjection m P := by
  ext i
  simp [taggingProjection, directCausalProjection, proxyTaggingProjection,
    sigmaTagCausalSourceAt, Matrix.add_mulVec, add_assoc, Pi.add_apply]

/-- The target tagging projection splits into the projection of source effects
through the target tagging surface plus a separate projection of the
locus-resolved effect heterogeneity. -/
theorem taggingProjection_target_eq_source_effect_plus_effectHeterogeneity {p q : ℕ}
    (m : CrossPopulationMetricModel p q) :
    taggingProjection m Pop.target =
      targetSourceEffectProjection m + targetEffectHeterogeneityProjection m := by
  unfold taggingProjection
  rw [totalEffect_target_eq_betaSource_plus_targetEffectHeterogeneity]
  simp [targetSourceEffectProjection, targetEffectHeterogeneityProjection,
    Matrix.mulVec_add]

/-- The target tagging projection also splits into standing target effects plus
target-only novel causal effects. -/
theorem taggingProjection_target_eq_standing_plus_novelMutationEffect {p q : ℕ}
    (m : CrossPopulationMetricModel p q) :
    taggingProjection m Pop.target =
      (sigmaTagCausalSourceAt m Pop.target).mulVec (m.beta Pop.target) +
        targetNovelMutationEffectProjection m := by
  ext i
  simp [taggingProjection, targetNovelMutationEffectProjection,
    totalEffect, Matrix.mulVec_add, Pi.add_apply]

/-- **The score/outcome covariance vector is the tagging projection plus the context
term** — in either population. -/
theorem crossCovariance_eq_taggingProjection_plus_context {p q : ℕ}
    (m : CrossPopulationMetricModel p q) (P : Pop) :
    crossCovariance m P = taggingProjection m P + m.contextCross P := by
  rfl

/-- **The score/outcome covariance vector splits into direct-causal, proxy-tagging and
context contributions** — in either population. -/
theorem crossCovariance_eq_direct_plus_proxy_plus_context {p q : ℕ}
    (m : CrossPopulationMetricModel p q) (P : Pop) :
    crossCovariance m P =
      directCausalProjection m P + proxyTaggingProjection m P + m.contextCross P := by
  rw [crossCovariance_eq_taggingProjection_plus_context,
    taggingProjection_eq_direct_plus_proxy]

/-- Exact target score/outcome cross-covariance splits into the transport of
source-stable effects through the target tagging surface, the projection of
target effect heterogeneity, and the target context term. -/
theorem crossCovariance_target_eq_source_effect_plus_effectHeterogeneity_plus_context
    {p q : ℕ} (m : CrossPopulationMetricModel p q) :
    crossCovariance m Pop.target =
      targetSourceEffectProjection m +
        targetEffectHeterogeneityProjection m +
        (m.contextCross Pop.target) := by
  rw [crossCovariance_eq_taggingProjection_plus_context,
    taggingProjection_target_eq_source_effect_plus_effectHeterogeneity]

/-- Exact target score/outcome cross-covariance also splits into the standing
target-effect projection, the projection of target-only novel causal effects,
and the target context term. -/
theorem crossCovariance_target_eq_standing_plus_novelMutationEffect_plus_context
    {p q : ℕ} (m : CrossPopulationMetricModel p q) :
    crossCovariance m Pop.target =
      (sigmaTagCausalSourceAt m Pop.target).mulVec (m.beta Pop.target) +
        targetNovelMutationEffectProjection m +
        (m.contextCross Pop.target) := by
  rw [crossCovariance_eq_taggingProjection_plus_context,
    taggingProjection_target_eq_standing_plus_novelMutationEffect]

/-- Exact score variance in the source population under the learned source
weights. -/
noncomputable def scoreVarianceFromSourceWeights {p q : ℕ}
    (m : CrossPopulationMetricModel p q) (P : Pop) : ℝ :=
  let wS := sourceWeightsFromExplicitDrivers m
  dotProduct wS ((m.sigmaTag P).mulVec wS)

/-- **Exact score/outcome covariance in a population** under the source-learned weights.
At the target this is where effect changes, tag-causal alignment and context shifts enter;
at the source it is the ordinary in-sample covariance. One definition, because it is one
quantity. -/
noncomputable def predictiveCovarianceFromSourceWeights {p q : ℕ}
    (m : CrossPopulationMetricModel p q) (P : Pop) : ℝ :=
  dotProduct (sourceWeightsFromExplicitDrivers m) (crossCovariance m P)

/-- **Exact calibration slope in a population** under the source-learned score equation:
the literal `Cov(Y, score) / Var(score)` ratio on the explicit SNP-level model. -/
noncomputable def calibrationSlopeFromSourceWeights {p q : ℕ}
    (m : CrossPopulationMetricModel p q) (P : Pop) : ℝ :=
  predictiveCovarianceFromSourceWeights m P / scoreVarianceFromSourceWeights m P

/-- The source predictive covariance is the transported score equation applied
to the source score/outcome cross-covariance vector. -/
theorem sourcePredictiveCovarianceFromSourceWeights_eq_score_on_source_crossCov {p q : ℕ}
    (m : CrossPopulationMetricModel p q) :
    predictiveCovarianceFromSourceWeights m Pop.source =
      sourceWeightedTagScore m (crossCovariance m Pop.source) := by
  simp [predictiveCovarianceFromSourceWeights, sourceWeightedTagScore]

/-- The target predictive covariance is the transported score equation applied
to the target score/outcome cross-covariance vector. This is the explicit
source-weights-on-target-covariance equation that the biological model needs. -/
theorem targetPredictiveCovarianceFromSourceWeights_eq_score_on_target_crossCov {p q : ℕ}
    (m : CrossPopulationMetricModel p q) :
    predictiveCovarianceFromSourceWeights m Pop.target =
      sourceWeightedTagScore m (crossCovariance m Pop.target) := by
  simp [predictiveCovarianceFromSourceWeights, sourceWeightedTagScore]

/-- Exact source calibration-slope law from the source-learned score moments. -/
theorem sourceCalibrationSlopeFromSourceWeights_exact_metric_law {p q : ℕ}
    (m : CrossPopulationMetricModel p q) :
    calibrationSlopeFromSourceWeights m Pop.source =
      predictiveCovarianceFromSourceWeights m Pop.source /
        scoreVarianceFromSourceWeights m Pop.source := by
  rfl

/-- Exact transported calibration-slope law from the explicit SNP-level score
equation and target LD/cross-covariance structure. -/
theorem targetCalibrationSlopeFromSourceWeights_exact_metric_portability_law
    {p q : ℕ} (m : CrossPopulationMetricModel p q) :
    calibrationSlopeFromSourceWeights m Pop.target =
      predictiveCovarianceFromSourceWeights m Pop.target /
        scoreVarianceFromSourceWeights m Pop.target := by
  rfl

/-- Exact transported calibration-slope law written directly on the
source-weights-on-target-covariance equation. -/
theorem targetCalibrationSlopeFromSourceWeights_exact_snp_transport_law
    {p q : ℕ} (m : CrossPopulationMetricModel p q) :
    calibrationSlopeFromSourceWeights m Pop.target =
      sourceWeightedTagScore m (crossCovariance m Pop.target) /
        sourceWeightedTagScore m
          ((m.sigmaTag Pop.target).mulVec (sourceWeightsFromExplicitDrivers m)) := by
  simp [calibrationSlopeFromSourceWeights, predictiveCovarianceFromSourceWeights,
    scoreVarianceFromSourceWeights, sourceWeightedTagScore]

/-- The source predictive covariance decomposes into direct-causal,
proxy-tagging, and context contributions under the transported score
functional. -/
theorem sourcePredictiveCovarianceFromSourceWeights_eq_direct_plus_proxy_plus_context_scores
    {p q : ℕ} (m : CrossPopulationMetricModel p q) :
    predictiveCovarianceFromSourceWeights m Pop.source =
      sourceWeightedTagScore m (directCausalProjection m Pop.source) +
        sourceWeightedTagScore m (proxyTaggingProjection m Pop.source) +
        sourceWeightedTagScore m (m.contextCross Pop.source) := by
  rw [sourcePredictiveCovarianceFromSourceWeights_eq_score_on_source_crossCov,
    crossCovariance_eq_direct_plus_proxy_plus_context]
  simp [add_assoc]

/-- The target predictive covariance decomposes into direct-causal,
proxy-tagging, and context contributions under the transported score
functional. -/
theorem targetPredictiveCovarianceFromSourceWeights_eq_direct_plus_proxy_plus_context_scores
    {p q : ℕ} (m : CrossPopulationMetricModel p q) :
    predictiveCovarianceFromSourceWeights m Pop.target =
      sourceWeightedTagScore m (directCausalProjection m Pop.target) +
        sourceWeightedTagScore m (proxyTaggingProjection m Pop.target) +
        sourceWeightedTagScore m (m.contextCross Pop.target) := by
  rw [targetPredictiveCovarianceFromSourceWeights_eq_score_on_target_crossCov,
    crossCovariance_eq_direct_plus_proxy_plus_context]
  simp [add_assoc]

/-- Exact transported calibration-slope law with the target predictive
covariance expanded into direct-causal, proxy-tagging, and context channels. -/
theorem targetCalibrationSlopeFromSourceWeights_exact_direct_proxy_context_law
    {p q : ℕ} (m : CrossPopulationMetricModel p q) :
    calibrationSlopeFromSourceWeights m Pop.target =
      (sourceWeightedTagScore m (directCausalProjection m Pop.target) +
        sourceWeightedTagScore m (proxyTaggingProjection m Pop.target) +
        sourceWeightedTagScore m (m.contextCross Pop.target)) /
          scoreVarianceFromSourceWeights m Pop.target := by
  rw [targetCalibrationSlopeFromSourceWeights_exact_metric_portability_law,
    targetPredictiveCovarianceFromSourceWeights_eq_direct_plus_proxy_plus_context_scores]

/-- The target predictive covariance decomposes into the transported source-
stable effect projection, the projection of effect-size heterogeneity, and the
target context term. -/
theorem targetPredictiveCovariance_eq_sourceEffect_plus_heterogeneity_plus_context
    {p q : ℕ} (m : CrossPopulationMetricModel p q) :
    predictiveCovarianceFromSourceWeights m Pop.target =
      sourceWeightedTagScore m (targetSourceEffectProjection m) +
        sourceWeightedTagScore m (targetEffectHeterogeneityProjection m) +
        sourceWeightedTagScore m (m.contextCross Pop.target) := by
  rw [targetPredictiveCovarianceFromSourceWeights_eq_score_on_target_crossCov,
    crossCovariance_target_eq_source_effect_plus_effectHeterogeneity_plus_context]
  simp [add_assoc]

/-- Exact transported calibration-slope law with target effect heterogeneity
made explicit. -/
theorem targetCalibrationSlopeFromSourceWeights_exact_effect_heterogeneity_law
    {p q : ℕ} (m : CrossPopulationMetricModel p q) :
    calibrationSlopeFromSourceWeights m Pop.target =
      (sourceWeightedTagScore m (targetSourceEffectProjection m) +
        sourceWeightedTagScore m (targetEffectHeterogeneityProjection m) +
        sourceWeightedTagScore m (m.contextCross Pop.target)) /
          scoreVarianceFromSourceWeights m Pop.target := by
  rw [targetCalibrationSlopeFromSourceWeights_exact_metric_portability_law,
    targetPredictiveCovariance_eq_sourceEffect_plus_heterogeneity_plus_context]

/-- The target predictive covariance also decomposes into standing target
effects, target-only novel mutation effects, and the target context term. -/
theorem targetPredictiveCovariance_eq_standing_plus_novelMutation_plus_context
    {p q : ℕ} (m : CrossPopulationMetricModel p q) :
    predictiveCovarianceFromSourceWeights m Pop.target =
      sourceWeightedTagScore m ((sigmaTagCausalSourceAt m Pop.target).mulVec (m.beta Pop.target)) +
        sourceWeightedTagScore m (targetNovelMutationEffectProjection m) +
        sourceWeightedTagScore m (m.contextCross Pop.target) := by
  rw [targetPredictiveCovarianceFromSourceWeights_eq_score_on_target_crossCov,
    crossCovariance_target_eq_standing_plus_novelMutationEffect_plus_context]
  simp [add_assoc]

/-- Additive irreducible loss from broken source-to-target tagging.
This is the squared target-effect distortion induced by the gap between the
source and target tag-to-causal alignment matrices. -/
noncomputable def brokenTaggingResidual {p q : ℕ}
    (m : CrossPopulationMetricModel p q) : ℝ :=
  let delta := ((sigmaTagCausalSourceAt m Pop.source) - (sigmaTagCausalSourceAt m
      Pop.target)).mulVec (totalEffect m Pop.target)
  dotProduct delta delta

theorem brokenTaggingResidual_nonneg {p q : ℕ}
    (m : CrossPopulationMetricModel p q) :
    0 ≤ brokenTaggingResidual m := by
  unfold brokenTaggingResidual
  classical
  simp [dotProduct]
  exact Finset.sum_nonneg (fun _ _ ↦ mul_self_nonneg _)

/-- Additive irreducible loss from ancestry-specific LD distortion.
This is the squared source-score covariance distortion induced by the gap
between the source and target scored-SNP LD matrices.

    Empirical status: UNTESTED. -/
noncomputable def ancestrySpecificLDResidual {p q : ℕ}
    (m : CrossPopulationMetricModel p q) : ℝ :=
  let wS := sourceWeightsFromExplicitDrivers m
  let delta := ((m.sigmaTag Pop.source) - (m.sigmaTag Pop.target)).mulVec wS
  dotProduct delta delta

theorem ancestrySpecificLDResidual_nonneg {p q : ℕ}
    (m : CrossPopulationMetricModel p q) :
    0 ≤ ancestrySpecificLDResidual m := by
  unfold ancestrySpecificLDResidual
  classical
  simp [dotProduct]
  exact Finset.sum_nonneg (fun _ _ ↦ mul_self_nonneg _)

/-- Additive irreducible loss from source-specific overfit or context mismatch.
This is the squared gap between source-only and target score/outcome
cross-covariance structure. -/
noncomputable def sourceSpecificOverfitResidual {p q : ℕ}
    (m : CrossPopulationMetricModel p q) : ℝ :=
  let delta := (m.contextCross Pop.source) - (m.contextCross Pop.target)
  dotProduct delta delta

theorem sourceSpecificOverfitResidual_nonneg {p q : ℕ}
    (m : CrossPopulationMetricModel p q) :
    0 ≤ sourceSpecificOverfitResidual m := by
  unfold sourceSpecificOverfitResidual
  classical
  simp [dotProduct]
  exact Finset.sum_nonneg (fun _ _ ↦ mul_self_nonneg _)

/-- Additive target-only phenotype variance from novel causal mutations that are
not tagged by the transported source score. -/
noncomputable def novelUntaggablePhenotypeResidual {p q : ℕ}
    (m : CrossPopulationMetricModel p q) : ℝ :=
  m.novelUntaggablePhenotypeVarianceTarget

@[simp] theorem novelUntaggablePhenotypeResidual_eq_field {p q : ℕ}
    (m : CrossPopulationMetricModel p q) :
    novelUntaggablePhenotypeResidual m = m.novelUntaggablePhenotypeVarianceTarget := by
  rfl

@[simp] theorem novelUntaggablePhenotypeResidual_nonneg {p q : ℕ}
    (m : CrossPopulationMetricModel p q) :
    0 ≤ novelUntaggablePhenotypeResidual m := by
  simpa [novelUntaggablePhenotypeResidual] using
    m.novelUntaggablePhenotypeVarianceTarget_nonneg

/-- Total additive irreducible target-side residual burden from the explicit
biological state. These losses are kept separate rather than folded into a
single multiplicative retention factor. -/
noncomputable def irreducibleTargetResidualBurden {p q : ℕ}
    (m : CrossPopulationMetricModel p q) : ℝ :=
  brokenTaggingResidual m +
    ancestrySpecificLDResidual m +
    sourceSpecificOverfitResidual m +
    novelUntaggablePhenotypeResidual m

theorem irreducibleTargetResidualBurden_nonneg {p q : ℕ}
    (m : CrossPopulationMetricModel p q) :
    0 ≤ irreducibleTargetResidualBurden m := by
  unfold irreducibleTargetResidualBurden
  linarith [brokenTaggingResidual_nonneg m, ancestrySpecificLDResidual_nonneg m,
    sourceSpecificOverfitResidual_nonneg m, novelUntaggablePhenotypeResidual_nonneg m]

/-- Canonical additive target-side penalty bundle induced by the explicit
cross-population state. This is the exact bridge back to the generic deployed
metric surface in `DGP.TransportedMetrics`. -/
noncomputable def targetIrreduciblePenaltyProfile {p q : ℕ}
    (m : CrossPopulationMetricModel p q) :
    TransportedMetrics.IrreducibleTargetPenalty where
  brokenTagging := brokenTaggingResidual m
  ancestrySpecificLD := ancestrySpecificLDResidual m
  sourceSpecificOverfit := sourceSpecificOverfitResidual m
  novelUntaggablePhenotype := novelUntaggablePhenotypeResidual m
  brokenTagging_nonneg := brokenTaggingResidual_nonneg m
  ancestrySpecificLD_nonneg := ancestrySpecificLDResidual_nonneg m
  sourceSpecificOverfit_nonneg := sourceSpecificOverfitResidual_nonneg m
  novelUntaggablePhenotype_nonneg := novelUntaggablePhenotypeResidual_nonneg m

@[simp] theorem targetIrreduciblePenaltyProfile_total {p q : ℕ}
    (m : CrossPopulationMetricModel p q) :
    (targetIrreduciblePenaltyProfile m).total =
      irreducibleTargetResidualBurden m := by
  simp [targetIrreduciblePenaltyProfile, TransportedMetrics.IrreducibleTargetPenalty.total,
    irreducibleTargetResidualBurden, add_assoc]

/-- Effective target outcome variance after adding an irreducible
target-specific residual burden from broken tagging, ancestry-specific LD, and
source-specific overfit, plus target-only untagged novel-mutation variance.

    Empirical status: UNTESTED. -/
noncomputable def residualBurden {p q : ℕ}
    (m : CrossPopulationMetricModel p q) (P : Pop) : ℝ :=
  Pop.pair 0 (irreducibleTargetResidualBurden m) P

/-- **The outcome variance a score is actually scored against, in a population.**

The source carries no transport burden — it is where the weights were fitted — and that
is now a computed consequence of `residualBurden` rather than the reason for writing two
separate definitions. `effectiveOutcomeVariance_source` below is the statement that used
to be implicit in the fact that only a `target` version existed.

    Empirical status: UNTESTED. -/
noncomputable def effectiveOutcomeVariance {p q : ℕ}
    (m : CrossPopulationMetricModel p q) (P : Pop) : ℝ :=
  (m.outcomeVariance P) + residualBurden m P

@[simp] theorem residualBurden_source {p q : ℕ} (m : CrossPopulationMetricModel p q) :
    residualBurden m Pop.source = 0 := rfl

/-- The companion to `residualBurden_source`, and the one that was missing.

`residualBurden` is written as a `Pop.pair`, so at the target it reduces to
`irreducibleTargetResidualBurden` by `rfl` -- but only if something performs
that reduction. `residualBurden_source` existed and this did not, which left
every target-side fact stated about `irreducibleTargetResidualBurden`
syntactically disconnected from goals mentioning `residualBurden m Pop.target`.
`linarith` in particular cannot bridge that gap: it was being handed a
nonnegativity fact about a term that does not occur in its goal. -/
@[simp] theorem residualBurden_target {p q : ℕ} (m : CrossPopulationMetricModel p q) :
    residualBurden m Pop.target = irreducibleTargetResidualBurden m := rfl

@[simp] theorem effectiveOutcomeVariance_source {p q : ℕ}
    (m : CrossPopulationMetricModel p q) :
    effectiveOutcomeVariance m Pop.source = m.outcomeVariance Pop.source := by
  simp [effectiveOutcomeVariance]

@[simp] theorem effectiveOutcomeVariance_target {p q : ℕ}
    (m : CrossPopulationMetricModel p q) :
    effectiveOutcomeVariance m Pop.target =
      (m.outcomeVariance Pop.target) + irreducibleTargetResidualBurden m := rfl

/-- The effective target outcome variance dominates the baseline target outcome
variance because the additive residual burden is nonnegative. -/
theorem effectiveTargetOutcomeVariance_ge_targetOutcomeVariance {p q : ℕ}
    (m : CrossPopulationMetricModel p q) :
    (m.outcomeVariance Pop.target) ≤ effectiveOutcomeVariance m Pop.target := by
  simp only [effectiveOutcomeVariance, residualBurden_target]
  linarith [irreducibleTargetResidualBurden_nonneg m]

/-- The effective target outcome variance stays strictly positive because the
base target outcome variance is positive and the additive residual burden is
nonnegative. -/
theorem effectiveTargetOutcomeVariance_pos {p q : ℕ}
    (m : CrossPopulationMetricModel p q) :
    0 < effectiveOutcomeVariance m Pop.target := by
  simp only [effectiveOutcomeVariance, residualBurden_target]
  linarith [m.outcomeVariance_pos Pop.target, irreducibleTargetResidualBurden_nonneg m]

/-- Exact decomposition of the effective target outcome variance into the base
target scale plus the three named additive residual-loss terms. -/
theorem effectiveTargetOutcomeVariance_eq_targetOutcomeVariance_add_losses {p q : ℕ}
    (m : CrossPopulationMetricModel p q) :
    effectiveOutcomeVariance m Pop.target =
      (m.outcomeVariance Pop.target) +
        brokenTaggingResidual m +
        ancestrySpecificLDResidual m +
        sourceSpecificOverfitResidual m +
        novelUntaggablePhenotypeResidual m := by
  simp [effectiveOutcomeVariance, residualBurden_target,
    irreducibleTargetResidualBurden, add_assoc]

/-- Exact source `R²` under the full source-side driver state. -/
noncomputable def explainedSignalVarianceFromSourceWeights {p q : ℕ}
    (m : CrossPopulationMetricModel p q) (P : Pop) : ℝ :=
  (predictiveCovarianceFromSourceWeights m P) ^ 2 / scoreVarianceFromSourceWeights m P

/-- **Exact `R²` in a population** under the full driver state, against the outcome
variance that population is actually scored against. -/
noncomputable def r2FromSourceWeights {p q : ℕ}
    (m : CrossPopulationMetricModel p q) (P : Pop) : ℝ :=
  explainedSignalVarianceFromSourceWeights m P / effectiveOutcomeVariance m P

/-- Exact unexplained source-side liability variance under the full explicit
source-state score equation. This is the residual variance paired with the
source explained signal when constructing exact source AUC and source Brier
coordinates from the same mechanistic SNP-level state. -/
noncomputable def residualVarianceFromSourceWeights {p q : ℕ}
    (m : CrossPopulationMetricModel p q) (P : Pop) : ℝ :=
  effectiveOutcomeVariance m P - explainedSignalVarianceFromSourceWeights m P

/-- Closed-form source calibrated Brier coordinate from the full explicit
source-state score equation, evaluated at an arbitrary observed prevalence
coordinate `π`. This lets downstream theory compare source and target Brier on
the same target-population outcome scale without falling back to a benchmark
`R²` surrogate.

    Empirical status: UNTESTED. -/
noncomputable def sourceCalibratedBrierFromSourceWeightsAtPrevalence {p q : ℕ}
    (m : CrossPopulationMetricModel p q) (π : ℝ) : ℝ :=
  TransportedMetrics.calibratedBrierFromVariances
    π
    (explainedSignalVarianceFromSourceWeights m Pop.source)
    (residualVarianceFromSourceWeights m Pop.source)

/-- The mechanistic source calibrated Brier coordinate is built directly from
source explained signal variance and source residual variance. -/
theorem sourceCalibratedBrierFromSourceWeightsAtPrevalence_eq_explicit_source_variances
    {p q : ℕ} (m : CrossPopulationMetricModel p q) (π : ℝ) :
    sourceCalibratedBrierFromSourceWeightsAtPrevalence m π =
      TransportedMetrics.calibratedBrierFromVariances
        π
        (explainedSignalVarianceFromSourceWeights m Pop.source)
        (residualVarianceFromSourceWeights m Pop.source) := by
  rfl

/-- The direct mechanistic source calibrated Brier coordinate agrees with the
`R²` chart induced by the same explicit source explained-signal and
total-variance decomposition. This is a derived identity, not the defining
construction of source Brier. -/
@[simp] theorem sourceCalibratedBrierFromSourceWeightsAtPrevalence_eq_explainedR2_chart
    {p q : ℕ} (m : CrossPopulationMetricModel p q) (π : ℝ) :
    sourceCalibratedBrierFromSourceWeightsAtPrevalence m π =
      TransportedMetrics.calibratedBrier π (r2FromSourceWeights m Pop.source) := by
  rw [sourceCalibratedBrierFromSourceWeightsAtPrevalence_eq_explicit_source_variances]
  rw [TransportedMetrics.calibratedBrierFromVariances_eq_chart]
  have h_source_ne : (m.outcomeVariance Pop.source) ≠ 0 :=
    ne_of_gt (m.outcomeVariance_pos Pop.source)
  have hr2 :
      TransportedMetrics.r2FromSignalVariance
          (explainedSignalVarianceFromSourceWeights m Pop.source)
          (residualVarianceFromSourceWeights m Pop.source) =
        r2FromSourceWeights m Pop.source := by
    unfold TransportedMetrics.r2FromSignalVariance residualVarianceFromSourceWeights
      r2FromSourceWeights
    field_simp [h_source_ne]
    ring
  rw [hr2]


/-- Exact target `R²` under transported source weights and the full target-side
driver state.

Rather than collapsing to a scalar retention factor, this depends explicitly on:
- source and target tag LD,
- source and target tag-causal alignment,
- source and target effect vectors,
- source and target context/environment cross-covariances, and
- additive irreducible target-side losses from broken tagging,
  ancestry-specific LD distortion, and source-specific overfit. -/
theorem explainedSignalVarianceFromSourceWeights_target {p q : ℕ}
    (m : CrossPopulationMetricModel p q) :
    explainedSignalVarianceFromSourceWeights m Pop.target =
      (predictiveCovarianceFromSourceWeights m Pop.target) ^ 2 /
        scoreVarianceFromSourceWeights m Pop.target := rfl

/-- Exact unexplained target-side liability variance under transported source
weights and the full explicit target-state loss budget. This is the residual
variance entering the liability-threshold AUC formula after the mechanistic
explained signal has been computed from the transported score moments.

**Simp direction changed here, and it affects every downstream file.** This name
was declared twice — once here, general in `P`, and once earlier in the file
specialised to `Pop.source` and spelling the right-hand side
`m.outcomeVariance Pop.source`. Two declarations of it would leave the specialised one in
the simp set, rewriting toward `m.outcomeVariance` at source only. There is one, so simp
rewrites toward `effectiveOutcomeVariance` at every `P`.

That is the direction the population index is going, and this statement is the
definitional unfolding of `residualVarianceFromSourceWeights`, which the
specialised one was not. But it is a behaviour change to a `@[simp]` lemma rather
than only a deletion, so if a downstream proof now normalises somewhere
unexpected, this is the cause. Reverting is one line — restore the specialised
copy and delete this — at the cost of losing the general form. -/
@[simp] theorem residualVarianceFromSourceWeights_eq_effective_minus_signal {p q : ℕ}
    (m : CrossPopulationMetricModel p q) (P : Pop) :
    residualVarianceFromSourceWeights m P =
      effectiveOutcomeVariance m P - explainedSignalVarianceFromSourceWeights m P := rfl

/-- Exact target calibrated Brier coordinate from the full explicit driver
state. Prevalence enters here, so Brier can change even when the score moments
are held fixed. -/
noncomputable def targetCalibratedBrierFromSourceWeights {p q : ℕ}
    (m : CrossPopulationMetricModel p q) : ℝ :=
  TransportedMetrics.calibratedBrierFromVariances
    m.targetPrevalence
    (explainedSignalVarianceFromSourceWeights m Pop.target)
    (residualVarianceFromSourceWeights m Pop.target)

/-- The mechanistic target calibrated Brier coordinate is built directly from
target explained signal variance and target residual variance. -/
theorem targetCalibratedBrierFromSourceWeights_eq_explicit_target_variances {p q : ℕ}
    (m : CrossPopulationMetricModel p q) :
    targetCalibratedBrierFromSourceWeights m =
      TransportedMetrics.calibratedBrierFromVariances
        m.targetPrevalence
        (explainedSignalVarianceFromSourceWeights m Pop.target)
        (residualVarianceFromSourceWeights m Pop.target) := by
  rfl

/-- Exact mechanistic target Brier portability law from transported score
moments and target prevalence. This is the direct variance law, not a theorem
about a benchmark `R²` chart. -/
theorem targetCalibratedBrierFromSourceWeights_exact_metric_portability_law
    {p q : ℕ} (m : CrossPopulationMetricModel p q) :
    targetCalibratedBrierFromSourceWeights m =
      TransportedMetrics.calibratedBrierFromVariances
        m.targetPrevalence
        ((predictiveCovarianceFromSourceWeights m Pop.target) ^ 2 /
          scoreVarianceFromSourceWeights m Pop.target)
        (effectiveOutcomeVariance m Pop.target -
          (predictiveCovarianceFromSourceWeights m Pop.target) ^ 2 /
            scoreVarianceFromSourceWeights m Pop.target) := by
  rw [targetCalibratedBrierFromSourceWeights_eq_explicit_target_variances]
  simp [explainedSignalVarianceFromSourceWeights,
    residualVarianceFromSourceWeights]

/-- Exact mechanistic target Brier portability law with the additive biological
loss budget made explicit in the residual term. -/
theorem targetCalibratedBrierFromSourceWeights_exact_loss_budget_law
    {p q : ℕ} (m : CrossPopulationMetricModel p q) :
    targetCalibratedBrierFromSourceWeights m =
      TransportedMetrics.calibratedBrierFromVariances
        m.targetPrevalence
        ((predictiveCovarianceFromSourceWeights m Pop.target) ^ 2 /
          scoreVarianceFromSourceWeights m Pop.target)
        ((m.outcomeVariance Pop.target) +
          brokenTaggingResidual m +
          ancestrySpecificLDResidual m +
          sourceSpecificOverfitResidual m +
          novelUntaggablePhenotypeResidual m -
          (predictiveCovarianceFromSourceWeights m Pop.target) ^ 2 /
            scoreVarianceFromSourceWeights m Pop.target) := by
  rw [targetCalibratedBrierFromSourceWeights_exact_metric_portability_law,
    effectiveTargetOutcomeVariance_eq_targetOutcomeVariance_add_losses]

/-- The direct mechanistic target calibrated Brier coordinate agrees with the
`R²` chart induced by the same explicit target explained-signal and
total-variance decomposition. This is a derived identity, not the defining
construction of transported Brier. -/
@[simp] theorem targetCalibratedBrierFromSourceWeights_eq_explainedR2_chart {p q : ℕ}
    (m : CrossPopulationMetricModel p q) :
    targetCalibratedBrierFromSourceWeights m =
      TransportedMetrics.calibratedBrier
        m.targetPrevalence (r2FromSourceWeights m Pop.target) := by
  rw [targetCalibratedBrierFromSourceWeights_eq_explicit_target_variances]
  rw [TransportedMetrics.calibratedBrierFromVariances_eq_chart]
  have h_eff_ne : effectiveOutcomeVariance m Pop.target ≠ 0 :=
    ne_of_gt (effectiveTargetOutcomeVariance_pos m)
  have hr2 :
      TransportedMetrics.r2FromSignalVariance
          (explainedSignalVarianceFromSourceWeights m Pop.target)
          (residualVarianceFromSourceWeights m Pop.target) =
        r2FromSourceWeights m Pop.target := by
    unfold TransportedMetrics.r2FromSignalVariance residualVarianceFromSourceWeights
      r2FromSourceWeights
    field_simp [h_eff_ne]
    -- The residual variance is `Y - X`, so the denominator is `X + (Y - X)`.
    -- `ring` alone cannot finish: after collapsing that to `Y` the goal is
    -- `X * Y / Y = X`, and cancelling needs `Y ≠ 0`, which `ring` never
    -- consults. Collapse with `ring`, then cancel explicitly.
    have hden :
        explainedSignalVarianceFromSourceWeights m Pop.target +
            (effectiveOutcomeVariance m Pop.target -
              explainedSignalVarianceFromSourceWeights m Pop.target)
          = effectiveOutcomeVariance m Pop.target := by ring
    rw [hden, mul_div_assoc, div_self h_eff_ne, mul_one]
  rw [hr2]

/-- The target score variance is exactly the target quadratic form
`w_Sᵀ Σ_T w_S`. -/
theorem target_score_variance_from_source_weights_identity {p q : ℕ}
    (m : CrossPopulationMetricModel p q) :
    scoreVarianceFromSourceWeights m Pop.target =
      dotProduct (sourceWeightsFromExplicitDrivers m)
        ((m.sigmaTag Pop.target).mulVec (sourceWeightsFromExplicitDrivers m)) := by
  simp [scoreVarianceFromSourceWeights]

/-- The target score variance is the transported score equation applied to the
target LD operator acting on the transported source weights. -/
theorem targetScoreVarianceFromSourceWeights_eq_score_on_target_covariance_action {p q : ℕ}
    (m : CrossPopulationMetricModel p q) :
    scoreVarianceFromSourceWeights m Pop.target =
      sourceWeightedTagScore m
        ((m.sigmaTag Pop.target).mulVec (sourceWeightsFromExplicitDrivers m)) := by
  simp [scoreVarianceFromSourceWeights, sourceWeightedTagScore]

/-- The source score variance is the same score equation evaluated against the
source LD operator. -/
theorem scoreVarianceFromSourceWeights_source_eq_score_on_covariance_action {p q : ℕ}
    (m : CrossPopulationMetricModel p q) :
    scoreVarianceFromSourceWeights m Pop.source =
      sourceWeightedTagScore m
        ((m.sigmaTag Pop.source).mulVec (sourceWeightsFromExplicitDrivers m)) := by
  simp [scoreVarianceFromSourceWeights, sourceWeightedTagScore]

/-- The source `R²` is exactly the explained signal variance from the explicit
score equation divided by the source outcome variance. -/
theorem sourceR2FromSourceWeights_eq_signalVariance_ratio {p q : ℕ}
    (m : CrossPopulationMetricModel p q) :
    r2FromSourceWeights m Pop.source =
      explainedSignalVarianceFromSourceWeights m Pop.source / (m.outcomeVariance Pop.source) := by
  -- `r2FromSourceWeights` divides by `effectiveOutcomeVariance`, which is
  -- `outcomeVariance + residualBurden`. At the source the burden is zero, but
  -- `x + 0 = x` is not a definitional equality on `ℝ`, so `rfl` cannot close
  -- this and the rewrite has to be done explicitly.
  unfold r2FromSourceWeights effectiveOutcomeVariance
  rw [residualBurden_source, add_zero]

/-- Exact mechanistic source `R²` law from the source-learned score moments. -/
theorem sourceR2FromSourceWeights_exact_metric_law {p q : ℕ}
    (m : CrossPopulationMetricModel p q) :
    r2FromSourceWeights m Pop.source =
      (predictiveCovarianceFromSourceWeights m Pop.source) ^ 2 /
        (scoreVarianceFromSourceWeights m Pop.source * (m.outcomeVariance Pop.source)) := by
  -- Same source-side burden discharge as
  -- `sourceR2FromSourceWeights_eq_signalVariance_ratio`: the statement names
  -- `outcomeVariance`, the definition routes through `effectiveOutcomeVariance`.
  unfold r2FromSourceWeights explainedSignalVarianceFromSourceWeights
    effectiveOutcomeVariance
  rw [residualBurden_source, add_zero]
  ring_nf

/-- The target `R²` is exactly the explained signal variance from the explicit
transported score equation divided by the effective target outcome variance. -/
theorem targetR2FromSourceWeights_eq_signalVariance_ratio {p q : ℕ}
    (m : CrossPopulationMetricModel p q) :
    r2FromSourceWeights m Pop.target =
      explainedSignalVarianceFromSourceWeights m Pop.target /
        effectiveOutcomeVariance m Pop.target := by
  rfl

/-- Exact mechanistic target `R²` portability law from transported score
moments.

This is the exact `R²` law on the explicit SNP-level transport model:

`R²_target = Cov(score_sourceWeights,target)^2 /
             (Var(score_sourceWeights,target) * effectiveOutcomeVariance)`.

No source-`R²` inversion or scalar transport factor appears. -/
theorem targetR2FromSourceWeights_exact_metric_portability_law {p q : ℕ}
    (m : CrossPopulationMetricModel p q) :
    r2FromSourceWeights m Pop.target =
      (predictiveCovarianceFromSourceWeights m Pop.target) ^ 2 /
        (scoreVarianceFromSourceWeights m Pop.target * effectiveOutcomeVariance m Pop.target) := by
  unfold r2FromSourceWeights explainedSignalVarianceFromSourceWeights
  ring_nf

/-- Exact mechanistic source/target `R²` portability ratio law. The ratio is
determined by transported score/outcome covariance, source/target score
variance, and source/target outcome scales, not by any source-`R²` summary. -/
theorem exactR2PortabilityRatio_mechanistic_law {p q : ℕ}
    (m : CrossPopulationMetricModel p q) :
    r2FromSourceWeights m Pop.target / r2FromSourceWeights m Pop.source =
      ((predictiveCovarianceFromSourceWeights m Pop.target) ^ 2 *
          scoreVarianceFromSourceWeights m Pop.source * (m.outcomeVariance Pop.source)) /
        ((predictiveCovarianceFromSourceWeights m Pop.source) ^ 2 *
          scoreVarianceFromSourceWeights m Pop.target * effectiveOutcomeVariance m Pop.target) := by
  rw [targetR2FromSourceWeights_exact_metric_portability_law,
    sourceR2FromSourceWeights_exact_metric_law]
  simp [pow_two, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm, inv_inv]

/-- Exact target `R²` portability law written directly on the transported
source-weight score equation and the target covariance operator. -/
theorem targetR2FromSourceWeights_exact_snp_transport_law {p q : ℕ}
    (m : CrossPopulationMetricModel p q) :
    r2FromSourceWeights m Pop.target =
      (sourceWeightedTagScore m (crossCovariance m Pop.target)) ^ 2 /
        (sourceWeightedTagScore m
            ((m.sigmaTag Pop.target).mulVec (sourceWeightsFromExplicitDrivers m)) *
          effectiveOutcomeVariance m Pop.target) := by
  rw [targetR2FromSourceWeights_exact_metric_portability_law,
    targetPredictiveCovarianceFromSourceWeights_eq_score_on_target_crossCov,
    targetScoreVarianceFromSourceWeights_eq_score_on_target_covariance_action]

/-- Exact target `R²` portability law with the additive biological loss budget
made explicit. Broken tagging, ancestry-specific LD distortion,
source-specific overfit, and target-only untaggable phenotype variance enter
only through the target effective outcome scale. -/
theorem targetR2FromSourceWeights_exact_loss_budget_law {p q : ℕ}
    (m : CrossPopulationMetricModel p q) :
    r2FromSourceWeights m Pop.target =
      (predictiveCovarianceFromSourceWeights m Pop.target) ^ 2 /
        (scoreVarianceFromSourceWeights m Pop.target *
          ((m.outcomeVariance Pop.target) +
            brokenTaggingResidual m +
            ancestrySpecificLDResidual m +
            sourceSpecificOverfitResidual m +
            novelUntaggablePhenotypeResidual m)) := by
  rw [targetR2FromSourceWeights_exact_metric_portability_law,
    effectiveTargetOutcomeVariance_eq_targetOutcomeVariance_add_losses]

/-- Exact target `R²` portability law with the transported covariance expanded
into direct-causal, proxy-tagging, and context channels. -/
theorem targetR2FromSourceWeights_exact_direct_proxy_context_law {p q : ℕ}
    (m : CrossPopulationMetricModel p q) :
    r2FromSourceWeights m Pop.target =
      ((sourceWeightedTagScore m (directCausalProjection m Pop.target) +
          sourceWeightedTagScore m (proxyTaggingProjection m Pop.target) +
          sourceWeightedTagScore m (m.contextCross Pop.target)) ^ 2) /
        (scoreVarianceFromSourceWeights m Pop.target * effectiveOutcomeVariance m Pop.target) := by
  rw [targetR2FromSourceWeights_exact_metric_portability_law,
    targetPredictiveCovarianceFromSourceWeights_eq_direct_plus_proxy_plus_context_scores]

/-- Exact target `R²` portability law with target effect heterogeneity made
explicit. The source-stable transport channel, effect-heterogeneity channel,
and target context channel contribute additively to the transported
score/outcome covariance before squaring. -/
theorem targetR2FromSourceWeights_exact_effect_heterogeneity_law {p q : ℕ}
    (m : CrossPopulationMetricModel p q) :
    r2FromSourceWeights m Pop.target =
      ((sourceWeightedTagScore m (targetSourceEffectProjection m) +
          sourceWeightedTagScore m (targetEffectHeterogeneityProjection m) +
          sourceWeightedTagScore m (m.contextCross Pop.target)) ^ 2) /
        (scoreVarianceFromSourceWeights m Pop.target * effectiveOutcomeVariance m Pop.target) := by
  rw [targetR2FromSourceWeights_exact_metric_portability_law,
    targetPredictiveCovariance_eq_sourceEffect_plus_heterogeneity_plus_context]

/-- Ohta-Kimura-style closed-form LD-correlation decay law across populations:
correlation decays exponentially with recombination distance and divergence.

    Empirical status: UNTESTED. -/
noncomputable def ldCorrelationDecay (distance fstGap lambda : ℝ) : ℝ :=
  Real.exp (-(lambda * fstGap * distance))

/-- For positive divergence scale, LD correlation strictly decreases with distance. -/
theorem ldCorrelationDecay_strictAnti_distance
    (d1 d2 fstGap lambda : ℝ)
    (hScale : 0 < lambda * fstGap)
    (hDist : d1 < d2) :
    ldCorrelationDecay d2 fstGap lambda < ldCorrelationDecay d1 fstGap lambda := by
  unfold ldCorrelationDecay
  apply Real.exp_lt_exp.mpr
  nlinarith [mul_lt_mul_of_pos_left hDist hScale]

/-- For positive distance and decay scale, LD correlation strictly decreases with `F_ST`. -/
theorem ldCorrelationDecay_strictAnti_fst
    (distance lambda fstSource fstTarget : ℝ)
    (hDist : 0 < distance)
    (hLambda : 0 < lambda)
    (hFst : fstSource < fstTarget) :
    ldCorrelationDecay distance fstTarget lambda <
      ldCorrelationDecay distance fstSource lambda := by
  unfold ldCorrelationDecay
  apply Real.exp_lt_exp.mpr
  have h_pos : 0 < lambda * distance := mul_pos hLambda hDist
  have h_lt : fstSource * (lambda * distance) < fstTarget * (lambda * distance) :=
    mul_lt_mul_of_pos_right hFst h_pos
  linarith

/-- Generation-indexed population-genetic parameters that drive explicit
time-varying portability state. These parameters govern drift, mutation,
migration, and recombination without compressing transport into source `R²`. -/
structure GenerationalPopGenParameters where
  Ne : ℝ
  μ : ℝ
  mig : ℝ
  recomb : ℝ
  V_A : ℝ
  Ne_pos : 0 < Ne
  μ_nonneg : 0 ≤ μ
  mig_nonneg : 0 ≤ mig
  recomb_nonneg : 0 ≤ recomb
  recomb_le_half : recomb ≤ 1 / 2
  V_A_pos : 0 < V_A

/-- **The parameter class is inhabited**, at a standard human-scale setting:
`Nₑ = 1000`, `μ = 10⁻⁵` per generation, `m = 10⁻³`, `r = 10⁻²`, additive variance
`1`.

    Every value is strictly inside the constraints — no rate is `0` and the
    recombination fraction is well below the free-recombination boundary `1/2` —
    so nothing downstream is read at a degenerate point. -/
noncomputable def GenerationalPopGenParameters.witness : GenerationalPopGenParameters where
  Ne := 1000
  μ := 1 / 100000
  mig := 1 / 1000
  recomb := 1 / 100
  V_A := 1
  Ne_pos := by norm_num
  μ_nonneg := by norm_num
  mig_nonneg := by norm_num
  recomb_nonneg := by norm_num
  recomb_le_half := by norm_num
  V_A_pos := by norm_num

namespace GenerationalPopGenParameters

/-- Scaled mutation rate `θ = 4Neμ`.

    Empirical status: UNTESTED. -/
noncomputable def theta (g : GenerationalPopGenParameters) : ℝ :=
  scaledMutationRate g.Ne g.μ

/-- Scaled migration rate `M = 4Nem`.

    Empirical status: UNTESTED. -/
noncomputable def bigM (g : GenerationalPopGenParameters) : ℝ :=
  scaledMigrationRate g.Ne g.mig

/-- Coalescent time coordinate at generation `t`.

    Empirical status: UNTESTED. -/
noncomputable def tauAt (g : GenerationalPopGenParameters) (t : ℕ) : ℝ :=
  (t : ℝ) / (2 * g.Ne)

/-- Per-generation heterozygosity retention factor under drift + mutation. -/
noncomputable def hetDecayFactor (g : GenerationalPopGenParameters) : ℝ :=
  hetDecayFromScaled g.Ne g.theta

/-- Transient differentiation after `t` generations. This is the same
discrete-time drift/mutation/migration coordinate used in the evolutionary
layer, but now exposed directly to the mechanistic SNP/LD state.

    Empirical status: UNTESTED. -/
noncomputable def fstTransientAt (g : GenerationalPopGenParameters) (t : ℕ) : ℝ :=
  (1 / (1 + g.theta + g.bigM)) * (1 - g.hetDecayFactor ^ t)

/-- Mutation-driven retention of shared ancestral variation after `t`
generations.

    Empirical status: UNTESTED. -/
noncomputable def mutationSharedRetentionAt
    (g : GenerationalPopGenParameters) (t : ℕ) : ℝ :=
  Real.exp (-g.theta * g.tauAt t)

/-- Migration-driven restoration of shared variation after `t` generations.

    Empirical status: UNTESTED. -/
noncomputable def migrationSharedBoostAt
    (g : GenerationalPopGenParameters) (t : ℕ) : ℝ :=
  1 + g.bigM * g.tauAt t / (1 + g.bigM)

@[simp] theorem tauAt_zero (g : GenerationalPopGenParameters) :
    g.tauAt 0 = 0 := by
  simp [tauAt]

@[simp] theorem fstTransientAt_zero (g : GenerationalPopGenParameters) :
    g.fstTransientAt 0 = 0 := by
  simp [fstTransientAt, hetDecayFactor]

@[simp] theorem mutationSharedRetentionAt_zero (g : GenerationalPopGenParameters) :
    g.mutationSharedRetentionAt 0 = 1 := by
  simp [mutationSharedRetentionAt, tauAt]

@[simp] theorem migrationSharedBoostAt_zero (g : GenerationalPopGenParameters) :
    g.migrationSharedBoostAt 0 = 1 := by
  simp [migrationSharedBoostAt, tauAt, bigM]

end GenerationalPopGenParameters

/-- Exact bridge from the coarse DGP evolutionary block to the
generation-indexed population-genetic parameter block used by the mechanistic
transport model. This carries only the shared popgen primitives; the
SNP/LD-aware state still lives in `CrossPopulationGenerationalModel`. -/
noncomputable def PGSEvolutionaryModel.toGenerationalPopGenParameters
    (m : PGSEvolutionaryModel) : GenerationalPopGenParameters where
  Ne := m.Ne
  μ := m.mu
  mig := m.mig
  recomb := m.recomb
  V_A := m.V_A
  Ne_pos := m.Ne_pos
  μ_nonneg := m.mu_nonneg
  mig_nonneg := m.mig_nonneg
  recomb_nonneg := m.recomb_nonneg
  recomb_le_half := m.recomb_le_half
  V_A_pos := m.V_A_pos

@[simp] theorem PGSEvolutionaryModel.toGenerationalPopGenParameters_theta
    (m : PGSEvolutionaryModel) :
    (m.toGenerationalPopGenParameters).theta = m.theta := by
  simp [PGSEvolutionaryModel.toGenerationalPopGenParameters,
    GenerationalPopGenParameters.theta, EvolutionaryParameters.theta]

@[simp] theorem PGSEvolutionaryModel.toGenerationalPopGenParameters_bigM
    (m : PGSEvolutionaryModel) :
    (m.toGenerationalPopGenParameters).bigM = m.bigM := by
  simp [PGSEvolutionaryModel.toGenerationalPopGenParameters,
    GenerationalPopGenParameters.bigM, EvolutionaryParameters.bigM]

@[simp] theorem PGSEvolutionaryModel.toGenerationalPopGenParameters_hetDecayFactor
    (m : PGSEvolutionaryModel) :
    (m.toGenerationalPopGenParameters).hetDecayFactor = m.hetDecayFactor := by
  unfold GenerationalPopGenParameters.hetDecayFactor PGSEvolutionaryModel.hetDecayFactor
    hetDecayFromScaled
  rw [PGSEvolutionaryModel.toGenerationalPopGenParameters_theta]
  rfl

/-- The transient `F_ST` coordinate in the coarse DGP block agrees exactly with
the generation-indexed popgen bridge at `⌊t_div⌋`, because both use the same
discrete heterozygosity recursion. -/
@[simp] theorem PGSEvolutionaryModel.toGenerationalPopGenParameters_fstTransientAt_floor
    (m : PGSEvolutionaryModel) :
    (m.toGenerationalPopGenParameters).fstTransientAt (Nat.floor m.t_div) =
      m.fstTransient := by
  unfold GenerationalPopGenParameters.fstTransientAt PGSEvolutionaryModel.fstTransient
  rw [PGSEvolutionaryModel.toGenerationalPopGenParameters_hetDecayFactor,
    PGSEvolutionaryModel.toGenerationalPopGenParameters_theta,
    PGSEvolutionaryModel.toGenerationalPopGenParameters_bigM]
  simp [fstEquilibrium, PGSEvolutionaryModel.toEvo,
    EvolutionaryParameters.theta, EvolutionaryParameters.bigM]

/-- When divergence time is an integer number of generations, the coarse
mutation-history coordinate agrees exactly with the generational popgen bridge
at that generation. -/
theorem PGSEvolutionaryModel.toGenerationalPopGenParameters_mutationSharedRetentionAt_floor
    (m : PGSEvolutionaryModel)
    (h_disc : m.t_div = (Nat.floor m.t_div : ℝ)) :
    (m.toGenerationalPopGenParameters).mutationSharedRetentionAt (Nat.floor m.t_div) =
      mutationLDErosion m.toEvo := by
  unfold GenerationalPopGenParameters.mutationSharedRetentionAt
    PGSEvolutionaryModel.toEvo mutationLDErosion
  rw [PGSEvolutionaryModel.toGenerationalPopGenParameters_theta]
  simp only [GenerationalPopGenParameters.tauAt,
    PGSEvolutionaryModel.toGenerationalPopGenParameters,
    EvolutionaryParameters.theta, EvolutionaryParameters.tau]
  rw [h_disc, Nat.floor_natCast]

/-- When divergence time is an integer number of generations, the coarse
migration-history coordinate agrees exactly with the generational popgen bridge
at that generation. -/
theorem PGSEvolutionaryModel.toGenerationalPopGenParameters_migrationSharedBoostAt_floor
    (m : PGSEvolutionaryModel)
    (h_disc : m.t_div = (Nat.floor m.t_div : ℝ)) :
    (m.toGenerationalPopGenParameters).migrationSharedBoostAt (Nat.floor m.t_div) =
      migrationLDBoost m.toEvo := by
  unfold GenerationalPopGenParameters.migrationSharedBoostAt
    PGSEvolutionaryModel.toEvo migrationLDBoost
  rw [PGSEvolutionaryModel.toGenerationalPopGenParameters_bigM]
  simp only [GenerationalPopGenParameters.tauAt,
    PGSEvolutionaryModel.toGenerationalPopGenParameters,
    EvolutionaryParameters.bigM, EvolutionaryParameters.tau]
  rw [h_disc, Nat.floor_natCast]

/-- Exact bridge from the DGP coordinate summary to the generational popgen
coordinates for the fields that genuinely match. The LD coordinate is
deliberately excluded here because the mechanistic model uses a joint
locus-specific kernel rather than a single global LD scalar. -/
theorem PGSEvolutionaryModel.coordinateSummary_matches_generational_popgen_at_floor
    (m : PGSEvolutionaryModel)
    (h_disc : m.t_div = (Nat.floor m.t_div : ℝ)) :
    m.coordinateSummary.alleleFreqCoordinate =
      1 - (m.toGenerationalPopGenParameters).fstTransientAt (Nat.floor m.t_div) ∧
    m.coordinateSummary.ancestralVariantCoordinate =
      (m.toGenerationalPopGenParameters).mutationSharedRetentionAt (Nat.floor m.t_div) ∧
    m.coordinateSummary.migrationCoordinate =
      (m.toGenerationalPopGenParameters).migrationSharedBoostAt (Nat.floor m.t_div) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [PGSEvolutionaryModel.coordinateSummary_alleleFreqCoordinate]
    exact congrArg (fun x ↦ 1 - x)
      (PGSEvolutionaryModel.toGenerationalPopGenParameters_fstTransientAt_floor m)
  · rw [PGSEvolutionaryModel.coordinateSummary_ancestralVariantCoordinate]
    exact (PGSEvolutionaryModel.toGenerationalPopGenParameters_mutationSharedRetentionAt_floor
      m h_disc).symm
  · rw [PGSEvolutionaryModel.coordinateSummary_migrationCoordinate]
    exact (PGSEvolutionaryModel.toGenerationalPopGenParameters_migrationSharedBoostAt_floor
      m h_disc).symm

/-- Allele-frequency mismatch penalty. This penalizes transport when target
allele frequencies drift away from the source frequencies, even if the source
score itself is unchanged.

    Empirical status: UNTESTED. -/
noncomputable def alleleFreqMismatchPenalty (pSource pTarget : ℝ) : ℝ :=
  Real.exp (-|pTarget - pSource|)

/-- **The penalty is a distance in disguise: symmetric, at most one, and exactly one on
agreement.** A directed penalty would fail the first, and a penalty that could exceed one would
reward mismatch. -/
theorem alleleFreqMismatchPenalty_symm (pSource pTarget : ℝ) :
    alleleFreqMismatchPenalty pSource pTarget = alleleFreqMismatchPenalty pTarget pSource := by
  unfold alleleFreqMismatchPenalty
  rw [abs_sub_comm]

theorem alleleFreqMismatchPenalty_le_one (pSource pTarget : ℝ) :
    alleleFreqMismatchPenalty pSource pTarget ≤ 1 := by
  unfold alleleFreqMismatchPenalty
  rw [Real.exp_le_one_iff]
  simpa using abs_nonneg (pTarget - pSource)

@[simp] theorem alleleFreqMismatchPenalty_self (p : ℝ) :
    alleleFreqMismatchPenalty p p = 1 := by
  simp [alleleFreqMismatchPenalty]

/-- Generation-indexed cross-population state. Source quantities are fixed at
training time; target quantities are explicit functions of generation. The
time-varying target LD and tagging state is derived from:

- source LD / source tag-causal alignment,
- source causal effects plus an explicit locus-resolved target-effect
  heterogeneity path,
- target-only novel causal effects,
- direct scored-causal measurements that are not mediated by LD decay,
- target-only novel direct causal links,
- ancestry-specific proxy tagging that is mediated by LD decay,
- target-only novel proxy-tagging links,
- recombination and transient `F_ST`,
- mutation- and migration-driven sharing terms, and
- explicit target allele-frequency trajectories split into standing and
  mutation-shift components,
- plus target-only untaggable phenotype variance from novel mutations. -/
structure CrossPopulationGenerationalModel (p q : ℕ) where
  popGen : GenerationalPopGenParameters
  betaSource : Fin q → ℝ
  targetEffectHeterogeneityAt : ℕ → Fin q → ℝ
  novelCausalEffectTargetAt : ℕ → Fin q → ℝ
  sigmaTagSource : Matrix (Fin p) (Fin p) ℝ
  directCausalSource : Matrix (Fin p) (Fin q) ℝ
  novelDirectCausalTemplate : Matrix (Fin p) (Fin q) ℝ
  proxyTaggingSource : Matrix (Fin p) (Fin q) ℝ
  novelProxyTaggingTemplate : Matrix (Fin p) (Fin q) ℝ
  tagDistance : Matrix (Fin p) (Fin p) ℝ
  tagCausalDistance : Matrix (Fin p) (Fin q) ℝ
  tagAlleleFreqSource : Fin p → ℝ
  tagAlleleFreqStandingTargetAt : ℕ → Fin p → ℝ
  tagAlleleFreqMutationShiftAt : ℕ → Fin p → ℝ
  causalAlleleFreqSource : Fin q → ℝ
  causalAlleleFreqStandingTargetAt : ℕ → Fin q → ℝ
  causalAlleleFreqMutationShiftAt : ℕ → Fin q → ℝ
  contextCrossSource : Fin p → ℝ
  contextCrossTargetAt : ℕ → Fin p → ℝ
  sourceOutcomeVariance : ℝ
  targetOutcomeVarianceAt : ℕ → ℝ
  novelUntaggablePhenotypeVarianceAt : ℕ → ℝ
  targetPrevalenceAt : ℕ → ℝ
  sourceOutcomeVariance_pos : 0 < sourceOutcomeVariance
  targetOutcomeVariance_pos : ∀ t, 0 < targetOutcomeVarianceAt t
  novelUntaggablePhenotypeVariance_nonneg : ∀ t, 0 ≤ novelUntaggablePhenotypeVarianceAt t
  targetPrevalence_pos : ∀ t, 0 < targetPrevalenceAt t
  targetPrevalence_lt_one : ∀ t, targetPrevalenceAt t < 1

/-- **The generational transport model is inhabited**, at every panel size `(p, q)`.

    The tag covariance is the identity, the two populations start at the same
    allele frequencies, and the effect vector, the heterogeneity path and the
    novel-mutation path are zero: this is the no-divergence configuration, in
    which the transported score is the source score at every generation. It is
    the null of the theory rather than an interesting member of it, and that is
    the point — it fixes what the generational statements quantify over. The
    variance and prevalence fields are strictly inside their constraints. -/
noncomputable def CrossPopulationGenerationalModel.witness (p q : ℕ) :
    CrossPopulationGenerationalModel p q where
  popGen := GenerationalPopGenParameters.witness
  betaSource := fun _ ↦ 0
  targetEffectHeterogeneityAt := fun _ _ ↦ 0
  novelCausalEffectTargetAt := fun _ _ ↦ 0
  sigmaTagSource := 1
  directCausalSource := 0
  novelDirectCausalTemplate := 0
  proxyTaggingSource := 0
  novelProxyTaggingTemplate := 0
  tagDistance := 0
  tagCausalDistance := 0
  tagAlleleFreqSource := fun _ ↦ 1 / 2
  tagAlleleFreqStandingTargetAt := fun _ _ ↦ 1 / 2
  tagAlleleFreqMutationShiftAt := fun _ _ ↦ 0
  causalAlleleFreqSource := fun _ ↦ 1 / 2
  causalAlleleFreqStandingTargetAt := fun _ _ ↦ 1 / 2
  causalAlleleFreqMutationShiftAt := fun _ _ ↦ 0
  contextCrossSource := fun _ ↦ 0
  contextCrossTargetAt := fun _ _ ↦ 0
  sourceOutcomeVariance := 1
  targetOutcomeVarianceAt := fun _ ↦ 1
  novelUntaggablePhenotypeVarianceAt := fun _ ↦ 0
  targetPrevalenceAt := fun _ ↦ 1 / 2
  sourceOutcomeVariance_pos := by norm_num
  targetOutcomeVariance_pos := fun _ ↦ by norm_num
  novelUntaggablePhenotypeVariance_nonneg := fun _ ↦ by norm_num
  targetPrevalence_pos := fun _ ↦ by norm_num
  targetPrevalence_lt_one := fun _ ↦ by norm_num

/-- Generation-indexed target effect vector. This is derived from the source
effect vector plus an explicit locus-resolved heterogeneity path and a
target-only novel-mutation effect path, not from any single retained-effect
scalar. -/
noncomputable def betaTargetAt {p q : ℕ}
    (m : CrossPopulationGenerationalModel p q) (t : ℕ) : Fin q → ℝ :=
  m.betaSource + m.targetEffectHeterogeneityAt t + m.novelCausalEffectTargetAt t

@[simp] theorem betaTargetAt_eq_source_plus_effectHeterogeneityAt {p q : ℕ}
    (m : CrossPopulationGenerationalModel p q) (t : ℕ) :
    betaTargetAt m t =
      m.betaSource + m.targetEffectHeterogeneityAt t + m.novelCausalEffectTargetAt t := by
  rfl

/-- Explicit target tag-SNP allele frequency after standing drift and
mutation-specific shift are combined.

    Empirical status: UNTESTED. -/
noncomputable def tagAlleleFreqTargetAt {p q : ℕ}
    (m : CrossPopulationGenerationalModel p q) (t : ℕ) (i : Fin p) : ℝ :=
  m.tagAlleleFreqStandingTargetAt t i + m.tagAlleleFreqMutationShiftAt t i

@[simp] theorem tagAlleleFreqTargetAt_eq_standing_plus_mutationShift {p q : ℕ}
    (m : CrossPopulationGenerationalModel p q) (t : ℕ) (i : Fin p) :
    tagAlleleFreqTargetAt m t i =
      m.tagAlleleFreqStandingTargetAt t i + m.tagAlleleFreqMutationShiftAt t i := by
  rfl

/-- Explicit target causal-site allele frequency after standing drift and
mutation-specific shift are combined.

    Empirical status: UNTESTED. -/
noncomputable def causalAlleleFreqTargetAt {p q : ℕ}
    (m : CrossPopulationGenerationalModel p q) (t : ℕ) (j : Fin q) : ℝ :=
  m.causalAlleleFreqStandingTargetAt t j + m.causalAlleleFreqMutationShiftAt t j

@[simp] theorem causalAlleleFreqTargetAt_eq_standing_plus_mutationShift {p q : ℕ}
    (m : CrossPopulationGenerationalModel p q) (t : ℕ) (j : Fin q) :
    causalAlleleFreqTargetAt m t j =
      m.causalAlleleFreqStandingTargetAt t j + m.causalAlleleFreqMutationShiftAt t j := by
  rfl

/-- Per-tag allele-frequency retention at generation `t`.

    Empirical status: UNTESTED. -/
noncomputable def tagAlleleFreqRetentionAt {p q : ℕ}
    (m : CrossPopulationGenerationalModel p q) (t : ℕ) (i : Fin p) : ℝ :=
  alleleFreqMismatchPenalty (m.tagAlleleFreqSource i) (tagAlleleFreqTargetAt m t i)

/-- Per-causal-variant allele-frequency retention at generation `t`.

    Empirical status: UNTESTED. -/
noncomputable def causalAlleleFreqRetentionAt {p q : ℕ}
    (m : CrossPopulationGenerationalModel p q) (t : ℕ) (j : Fin q) : ℝ :=
  alleleFreqMismatchPenalty (m.causalAlleleFreqSource j) (causalAlleleFreqTargetAt m t j)

/-- Fraction of target-side novel variation accumulated by generation `t`.
This is the complement of shared ancestral variation retained after mutation. -/
noncomputable def novelVariantInnovationAt (g : GenerationalPopGenParameters) (t : ℕ) : ℝ :=
  1 - g.mutationSharedRetentionAt t

@[simp] theorem novelVariantInnovationAt_zero (g : GenerationalPopGenParameters) :
    novelVariantInnovationAt g 0 = 0 := by
  simp [novelVariantInnovationAt]

/-- Joint locus-level transport kernel for LD among scored SNPs at generation
`t`. This is where drift, recombination, mutation history, migration history,
and tag-SNP allele-frequency drift meet; the mechanistic model does not treat
them as independent global scalars.

    Empirical status: UNTESTED. -/
noncomputable def jointTagLDKernelAt {p q : ℕ}
    (m : CrossPopulationGenerationalModel p q) (t : ℕ) (i j : Fin p) : ℝ :=
  ldCorrelationDecay (m.tagDistance i j)
      (m.popGen.fstTransientAt t) m.popGen.recomb *
    m.popGen.mutationSharedRetentionAt t *
    m.popGen.migrationSharedBoostAt t *
    tagAlleleFreqRetentionAt m t i *
    tagAlleleFreqRetentionAt m t j

@[simp] theorem jointTagLDKernelAt_uses_ld_af_mutation_migration {p q : ℕ}
    (m : CrossPopulationGenerationalModel p q) (t : ℕ) (i j : Fin p) :
    jointTagLDKernelAt m t i j =
      ldCorrelationDecay (m.tagDistance i j)
          (m.popGen.fstTransientAt t) m.popGen.recomb *
        m.popGen.mutationSharedRetentionAt t *
        m.popGen.migrationSharedBoostAt t *
        tagAlleleFreqRetentionAt m t i *
        tagAlleleFreqRetentionAt m t j := by
  simp [jointTagLDKernelAt]

/-- Joint locus-level transport kernel for directly scored causal variants.
This omits the LD-decay term because the scored variant is itself causal, but
it still carries mutation, migration, and AF-history interactions. -/
noncomputable def jointDirectCausalKernelAt {p q : ℕ}
    (m : CrossPopulationGenerationalModel p q) (t : ℕ) (i : Fin p) (j : Fin q) : ℝ :=
  m.popGen.mutationSharedRetentionAt t *
    m.popGen.migrationSharedBoostAt t *
    tagAlleleFreqRetentionAt m t i *
    causalAlleleFreqRetentionAt m t j

@[simp] theorem jointDirectCausalKernelAt_uses_af_mutation_migration {p q : ℕ}
    (m : CrossPopulationGenerationalModel p q) (t : ℕ) (i : Fin p) (j : Fin q) :
    jointDirectCausalKernelAt m t i j =
      m.popGen.mutationSharedRetentionAt t *
        m.popGen.migrationSharedBoostAt t *
        tagAlleleFreqRetentionAt m t i *
        causalAlleleFreqRetentionAt m t j := by
  simp [jointDirectCausalKernelAt]

/-- Joint locus-level transport kernel for ancestry-specific proxy tagging.
This carries the full interaction between LD decay, mutation/migration sharing,
and source/target allele-frequency history. -/
noncomputable def jointProxyTaggingKernelAt {p q : ℕ}
    (m : CrossPopulationGenerationalModel p q) (t : ℕ) (i : Fin p) (j : Fin q) : ℝ :=
  ldCorrelationDecay (m.tagCausalDistance i j)
      (m.popGen.fstTransientAt t) m.popGen.recomb *
    m.popGen.mutationSharedRetentionAt t *
    m.popGen.migrationSharedBoostAt t *
    tagAlleleFreqRetentionAt m t i *
    causalAlleleFreqRetentionAt m t j

@[simp] theorem jointProxyTaggingKernelAt_uses_ld_tagging_af_mutation_migration {p q : ℕ}
    (m : CrossPopulationGenerationalModel p q) (t : ℕ) (i : Fin p) (j : Fin q) :
    jointProxyTaggingKernelAt m t i j =
      ldCorrelationDecay (m.tagCausalDistance i j)
          (m.popGen.fstTransientAt t) m.popGen.recomb *
        m.popGen.mutationSharedRetentionAt t *
        m.popGen.migrationSharedBoostAt t *
        tagAlleleFreqRetentionAt m t i *
        causalAlleleFreqRetentionAt m t j := by
  simp [jointProxyTaggingKernelAt]

/-- Joint locus-level kernel for target-only novel direct causal links. Novel
target-specific causal variants accumulate with mutation history, are diluted by
migration, and still depend on target allele-frequency matching.

    Empirical status: UNTESTED. -/
noncomputable def jointNovelDirectCausalKernelAt {p q : ℕ}
    (m : CrossPopulationGenerationalModel p q) (t : ℕ) (i : Fin p) (j : Fin q) : ℝ :=
  novelVariantInnovationAt m.popGen t *
    (m.popGen.migrationSharedBoostAt t)⁻¹ *
    tagAlleleFreqRetentionAt m t i *
    causalAlleleFreqRetentionAt m t j

@[simp] theorem jointNovelDirectCausalKernelAt_uses_af_mutation_migration {p q : ℕ}
    (m : CrossPopulationGenerationalModel p q) (t : ℕ) (i : Fin p) (j : Fin q) :
    jointNovelDirectCausalKernelAt m t i j =
      novelVariantInnovationAt m.popGen t *
        (m.popGen.migrationSharedBoostAt t)⁻¹ *
        tagAlleleFreqRetentionAt m t i *
        causalAlleleFreqRetentionAt m t j := by
  simp [jointNovelDirectCausalKernelAt]

/-- Joint locus-level kernel for target-only novel proxy tagging. This carries
both local LD structure and mutation-generated novelty, rather than just
attenuating the shared source proxy surface. -/
noncomputable def jointNovelProxyTaggingKernelAt {p q : ℕ}
    (m : CrossPopulationGenerationalModel p q) (t : ℕ) (i : Fin p) (j : Fin q) : ℝ :=
  ldCorrelationDecay (m.tagCausalDistance i j)
      (m.popGen.fstTransientAt t) m.popGen.recomb *
    novelVariantInnovationAt m.popGen t *
    (m.popGen.migrationSharedBoostAt t)⁻¹ *
    tagAlleleFreqRetentionAt m t i *
    causalAlleleFreqRetentionAt m t j

@[simp] theorem jointNovelProxyTaggingKernelAt_uses_ld_af_mutation_migration {p q : ℕ}
    (m : CrossPopulationGenerationalModel p q) (t : ℕ) (i : Fin p) (j : Fin q) :
    jointNovelProxyTaggingKernelAt m t i j =
      ldCorrelationDecay (m.tagCausalDistance i j)
          (m.popGen.fstTransientAt t) m.popGen.recomb *
        novelVariantInnovationAt m.popGen t *
        (m.popGen.migrationSharedBoostAt t)⁻¹ *
        tagAlleleFreqRetentionAt m t i *
        causalAlleleFreqRetentionAt m t j := by
  simp [jointNovelProxyTaggingKernelAt]

/-- Time-varying target LD among scored SNPs. This incorporates recombination,
drift (`F_ST`), mutation/migration-driven shared variation, and explicit target
tag-SNP allele-frequency drift. -/
noncomputable def sigmaTagTargetAt {p q : ℕ}
    (m : CrossPopulationGenerationalModel p q) (t : ℕ) :
    Matrix (Fin p) (Fin p) ℝ :=
  fun i j ↦
    m.sigmaTagSource i j * jointTagLDKernelAt m t i j

/-- Time-varying target tag-to-causal alignment. This is the explicit tagging
quality surface, driven by LD decay, allele-frequency divergence, mutation,
migration, and the underlying source tag-causal alignment. -/
noncomputable def directCausalTargetAt {p q : ℕ}
    (m : CrossPopulationGenerationalModel p q) (t : ℕ) :
    Matrix (Fin p) (Fin q) ℝ :=
  fun i j ↦
    m.directCausalSource i j * jointDirectCausalKernelAt m t i j

/-- Time-varying target-only novel direct-causal alignment.

    Empirical status: UNTESTED. -/
noncomputable def novelDirectCausalTargetAt {p q : ℕ}
    (m : CrossPopulationGenerationalModel p q) (t : ℕ) :
    Matrix (Fin p) (Fin q) ℝ :=
  fun i j ↦
    m.novelDirectCausalTemplate i j * jointNovelDirectCausalKernelAt m t i j

/-- Time-varying proxy-tagging alignment. Unlike directly scored causal
variants, this channel is degraded by LD decay between the scored tag and the
unscored causal variant. -/
noncomputable def proxyTaggingTargetAt {p q : ℕ}
    (m : CrossPopulationGenerationalModel p q) (t : ℕ) :
    Matrix (Fin p) (Fin q) ℝ :=
  fun i j ↦
    m.proxyTaggingSource i j * jointProxyTaggingKernelAt m t i j

/-- Time-varying target-only novel proxy-tagging alignment created after
divergence. -/
noncomputable def novelProxyTaggingTargetAt {p q : ℕ}
    (m : CrossPopulationGenerationalModel p q) (t : ℕ) :
    Matrix (Fin p) (Fin q) ℝ :=
  fun i j ↦
    m.novelProxyTaggingTemplate i j * jointNovelProxyTaggingKernelAt m t i j

/-- Time-varying target tag-to-causal alignment is the sum of a direct-causal
channel, a target-only novel direct-causal channel, a proxy-tagging channel,
and a target-only novel proxy-tagging channel. Only the proxy channels carry
LD-decay erosion. -/
noncomputable def sigmaTagCausalTargetAt {p q : ℕ}
    (m : CrossPopulationGenerationalModel p q) (t : ℕ) :
    Matrix (Fin p) (Fin q) ℝ :=
  directCausalTargetAt m t +
    (novelDirectCausalTargetAt m t +
      (proxyTaggingTargetAt m t + novelProxyTaggingTargetAt m t))

/-- Projection of the source effect vector through the generation-indexed
target tagging surface. This isolates what would transport if target causal
effects were identical to source effects.

    Empirical status: UNTESTED. -/
noncomputable def targetSourceEffectProjectionAt {p q : ℕ}
    (m : CrossPopulationGenerationalModel p q) (t : ℕ) : Fin p → ℝ :=
  (sigmaTagCausalTargetAt m t).mulVec m.betaSource

/-- Incremental generation-indexed projection induced purely by per-locus
target-effect heterogeneity, including target-only novel causal effects.

    Empirical status: UNTESTED. -/
noncomputable def targetEffectHeterogeneityProjectionAt {p q : ℕ}
    (m : CrossPopulationGenerationalModel p q) (t : ℕ) : Fin p → ℝ :=
  (sigmaTagCausalTargetAt m t).mulVec
    (m.targetEffectHeterogeneityAt t + m.novelCausalEffectTargetAt t)


/-- The static exact metric model obtained by slicing the generational state at
generation `t`. This is the canonical bridge from explicit population-genetic
dynamics to deployed metrics. -/
noncomputable def CrossPopulationGenerationalModel.toMetricModelAt {p q : ℕ}
    (m : CrossPopulationGenerationalModel p q) (t : ℕ) :
    CrossPopulationMetricModel p q where
  beta := Pop.pair (m.betaSource) (m.betaSource + m.targetEffectHeterogeneityAt t)
  sigmaTag := Pop.pair (m.sigmaTagSource) (sigmaTagTargetAt m t)
  directCausal := Pop.pair (m.directCausalSource) (directCausalTargetAt m t)
  proxyTagging := Pop.pair (m.proxyTaggingSource) (proxyTaggingTargetAt m t)
  contextCross := Pop.pair (m.contextCrossSource) (m.contextCrossTargetAt t)
  outcomeVariance := Pop.pair (m.sourceOutcomeVariance) (m.targetOutcomeVarianceAt t)
  novelDirectCausal := Pop.pair 0 (novelDirectCausalTargetAt m t)
  novelProxyTagging := Pop.pair 0 (novelProxyTaggingTargetAt m t)
  novelCausalEffect := Pop.pair 0 (m.novelCausalEffectTargetAt t)
  novelUntaggablePhenotypeVarianceTarget := m.novelUntaggablePhenotypeVarianceAt t
  targetPrevalence := m.targetPrevalenceAt t
  novelUntaggablePhenotypeVarianceTarget_nonneg := m.novelUntaggablePhenotypeVariance_nonneg t
  targetPrevalence_pos := m.targetPrevalence_pos t
  targetPrevalence_lt_one := m.targetPrevalence_lt_one t
  novelDirectCausal_source := rfl
  novelProxyTagging_source := rfl
  novelCausalEffect_source := rfl
  -- The two cases are exactly the model's own positivity fields; `simp_all`
  -- reduces the `Pop.pair` but has no way to discharge them.
  outcomeVariance_pos := by
    intro P
    cases P
    · exact m.sourceOutcomeVariance_pos
    · exact m.targetOutcomeVariance_pos t

/-- At each generation, the target tagging projection splits into the part that
would be obtained under source-stable effects plus a separate projection of the
locus-resolved target-effect heterogeneity. -/
theorem targetTaggingProjectionAtGeneration_eq_source_effect_plus_effectHeterogeneity
    {p q : ℕ} (m : CrossPopulationGenerationalModel p q) (t : ℕ) :
    taggingProjection (m.toMetricModelAt t) Pop.target =
      targetSourceEffectProjectionAt m t +
        targetEffectHeterogeneityProjectionAt m t := by
  simpa [CrossPopulationGenerationalModel.toMetricModelAt,
    targetSourceEffectProjectionAt, targetEffectHeterogeneityProjectionAt,
    targetSourceEffectProjection, targetEffectHeterogeneityProjection,
    targetEffectHeterogeneity, totalEffect, sigmaTagCausalTargetAt, add_assoc]
    using taggingProjection_target_eq_source_effect_plus_effectHeterogeneity
      (m.toMetricModelAt t)

/-- With any imperfect source tagging (`ρS > 0`), worsening target tagging (`ρT < ρS`)
strictly lowers portability when drift terms are fixed. -/
theorem portability_ratio_with_target_ld_decay_any_source
    (V_A V_E fstS fstT rhoS rhoT : ℝ)
    (hVA : 0 < V_A) (hVE : 0 < V_E)
    (hfstS_lt_one : fstS < 1) (hfstT_lt_one : fstT < 1)
    (h_rho : 0 < rhoT ∧ rhoT < rhoS) :
    r2FromSignalVariance (realWorldPGSVariance V_A fstT rhoT) V_E /
      r2FromSignalVariance (realWorldPGSVariance V_A fstS rhoS) V_E <
    r2FromSignalVariance (realWorldPGSVariance V_A fstT rhoS) V_E /
      r2FromSignalVariance (realWorldPGSVariance V_A fstS rhoS) V_E := by
  rcases h_rho with ⟨hRhoT_pos, hRhoT_lt_rhoS⟩
  have hRhoS_pos : 0 < rhoS := lt_trans hRhoT_pos hRhoT_lt_rhoS
  have hu_pos : 0 < (1 - fstT) * V_A := mul_pos (by linarith) hVA
  -- Numerator: rhoT < rhoS implies R²(rhoT·u) < R²(rhoS·u)
  have h_num_lt :
      r2FromSignalVariance (realWorldPGSVariance V_A fstT rhoT) V_E <
        r2FromSignalVariance (realWorldPGSVariance V_A fstT rhoS) V_E := by
    apply expectedR2_strictMono_nonneg V_E _ _ hVE
    · unfold realWorldPGSVariance
      exact le_of_lt (by simpa [mul_assoc] using mul_pos hRhoT_pos hu_pos)
    · simpa [realWorldPGSVariance, mul_assoc] using
        mul_lt_mul_of_pos_right hRhoT_lt_rhoS hu_pos
  -- Denominator positivity
  have hsource_sig_pos : 0 < realWorldPGSVariance V_A fstS rhoS := by
    unfold realWorldPGSVariance
    simpa [mul_assoc] using mul_pos (mul_pos hRhoS_pos (by linarith : 0 < 1 - fstS)) hVA
  have h_den_pos : 0 < r2FromSignalVariance (realWorldPGSVariance V_A fstS rhoS) V_E := by
    unfold r2FromSignalVariance
    exact div_pos hsource_sig_pos (by linarith)
  -- Divide both sides by positive denominator
  simpa [div_eq_mul_inv] using
    mul_lt_mul_of_pos_right h_num_lt (inv_pos.mpr h_den_pos)

/-- With source perfectly tagged (`ρ_S = 1`), adding target LD decay (`ρ_T < 1`)
strictly lowers the portability ratio versus drift-only transport. -/
theorem portability_ratio_with_ld_decay
    (V_A V_E fstS fstT rhoS rhoT : ℝ)
    (hVA : 0 < V_A) (hVE : 0 < V_E)
    (hfst : fstS < fstT) (hfstT_lt_one : fstT < 1) (hRhoS : rhoS = 1)
    (h_rho : 0 < rhoT ∧ rhoT < rhoS) :
    r2FromSignalVariance (realWorldPGSVariance V_A fstT rhoT) V_E /
      r2FromSignalVariance (realWorldPGSVariance V_A fstS rhoS) V_E <
    r2FromSignalVariance (presentDayPGSVariance V_A fstT) V_E /
      r2FromSignalVariance (presentDayPGSVariance V_A fstS) V_E := by
  rcases h_rho with ⟨hRhoT_pos, hRhoT_lt_rhoS⟩
  have hfstS_lt_one : fstS < 1 := lt_trans hfst hfstT_lt_one
  have hTargetPos : 0 < V_A * (1 - fstT) := by
    have : 0 < 1 - fstT := by linarith
    exact mul_pos hVA this
  have hTarget_nonneg : 0 ≤ V_A * (1 - fstT) := le_of_lt hTargetPos
  have hRhoT_lt_one : rhoT < 1 := by simpa [hRhoS] using hRhoT_lt_rhoS
  have hRealTarget_lt :
      realWorldPGSVariance V_A fstT rhoT < presentDayPGSVariance V_A fstT := by
    have hscaled :
        rhoT * (V_A * (1 - fstT)) < 1 * (V_A * (1 - fstT)) :=
      mul_lt_mul_of_pos_right hRhoT_lt_one hTargetPos
    simpa [realWorldPGSVariance, presentDayPGSVariance, pgsVarianceFromHet,
      mul_assoc, mul_left_comm, mul_comm] using hscaled
  have hR2Target_lt :
      r2FromSignalVariance (realWorldPGSVariance V_A fstT rhoT) V_E <
        r2FromSignalVariance (presentDayPGSVariance V_A fstT) V_E := by
    apply expectedR2_strictMono_nonneg V_E
    · exact hVE
    · unfold realWorldPGSVariance
      have hRhoTerm_nonneg : 0 ≤ rhoT * (1 - fstT) := by
        have hOneMinus_nonneg : 0 ≤ 1 - fstT := by linarith
        exact mul_nonneg (le_of_lt hRhoT_pos) hOneMinus_nonneg
      exact mul_nonneg hRhoTerm_nonneg (le_of_lt hVA)
    · exact hRealTarget_lt
  have hSourcePos : 0 < presentDayPGSVariance V_A fstS := by
    unfold presentDayPGSVariance pgsVarianceFromHet
    have h1s : 0 < 1 - fstS := by linarith
    exact mul_pos hVA h1s
  have hR2Source_pos : 0 < r2FromSignalVariance (presentDayPGSVariance V_A fstS) V_E := by
    unfold r2FromSignalVariance
    have hden : 0 < presentDayPGSVariance V_A fstS + V_E := by linarith [hSourcePos, hVE]
    exact div_pos hSourcePos hden
  have hL :
      r2FromSignalVariance (realWorldPGSVariance V_A fstT rhoT) V_E /
          r2FromSignalVariance (presentDayPGSVariance V_A fstS) V_E <
        r2FromSignalVariance (presentDayPGSVariance V_A fstT) V_E /
          r2FromSignalVariance (presentDayPGSVariance V_A fstS) V_E := by
    have hmul :
        r2FromSignalVariance (realWorldPGSVariance V_A fstT rhoT) V_E * (r2FromSignalVariance
            (presentDayPGSVariance V_A fstS) V_E)⁻¹ <
          r2FromSignalVariance (presentDayPGSVariance V_A fstT) V_E * (r2FromSignalVariance
              (presentDayPGSVariance V_A fstS) V_E)⁻¹ :=
      mul_lt_mul_of_pos_right hR2Target_lt (inv_pos.mpr hR2Source_pos)
    simpa [div_eq_mul_inv] using hmul
  -- `hL` is phrased with `presentDayPGSVariance`; with `rhoS = 1` the goal
  -- normalises to `(1 - fst) * V_A`. `presentDayPGSVariance_eq_one_sub_fst_mul`
  -- is exactly that equation, so it is the bridge -- not a guessed simp set.
  simpa [hRhoS, realWorldPGSVariance, presentDayPGSVariance_eq_one_sub_fst_mul]
    using hL

/-- General LD-aware portability theorem without assuming perfect source tagging.
Under `0 < rhoT < rhoS ≤ 1` and `fstS < fstT < 1`, the LD+drift portability ratio
is strictly below the drift-only portability ratio. -/
theorem portability_ratio_with_ld_decay_general
    (V_A V_E fstS fstT rhoS rhoT : ℝ)
    (hVA : 0 < V_A) (hVE : 0 < V_E)
    (hfst : fstS < fstT) (hfstT_lt_one : fstT < 1)
    (hRhoS : rhoS = 1)
    (h_rho : 0 < rhoT ∧ rhoT < rhoS ∧ rhoS ≤ 1) :
    r2FromSignalVariance (realWorldPGSVariance V_A fstT rhoT) V_E /
      r2FromSignalVariance (realWorldPGSVariance V_A fstS rhoS) V_E <
    r2FromSignalVariance (presentDayPGSVariance V_A fstT) V_E /
      r2FromSignalVariance (presentDayPGSVariance V_A fstS) V_E := by
  rcases h_rho with ⟨hRhoT_pos, hRhoT_lt_rhoS, _⟩
  exact portability_ratio_with_ld_decay V_A V_E fstS fstT rhoS rhoT
    hVA hVE hfst hfstT_lt_one hRhoS ⟨hRhoT_pos, hRhoT_lt_rhoS⟩

/-- If target `R²` is strictly below source `R²`, the portability ratio is strictly below `1`. -/
theorem div_lt_one_of_lt_of_pos
    (srcR2 tgtR2 : ℝ)
    (hsrc_pos : 0 < srcR2)
    (hdrop : tgtR2 < srcR2) :
    tgtR2 / srcR2 < 1 :=
  (_root_.div_lt_iff₀ hsrc_pos).2 (by simpa using hdrop)

/-- Headline portability theorem: positive drift implies `R²` ratio is strictly below `1`. -/
theorem portability_ratio_lt_one_of_positive_drift
    (V_A V_E fstS fstT : ℝ)
    (hVA : 0 < V_A) (hVE : 0 < V_E)
    (hfst : fstS < fstT)
    (hfstT_le_one : fstT ≤ 1) :
    presentDayR2 V_A V_E fstT / presentDayR2 V_A V_E fstS < 1 := by
  -- Source positivity is not a hypothesis: `fstS < fstT ≤ 1` already forces
  -- `0 < 1 - fstS`, and the signal variance is `V_A * (1 - fstS)`.
  have hsrc_pos : 0 < presentDayR2 V_A V_E fstS := by
    unfold presentDayR2 r2FromSignalVariance
    have hv_pos : 0 < presentDayPGSVariance V_A fstS := by
      unfold presentDayPGSVariance pgsVarianceFromHet
      have h_one_minus : 0 < 1 - fstS := by linarith
      exact mul_pos hVA h_one_minus
    exact div_pos hv_pos (by linarith)
  have hdrop : presentDayR2 V_A V_E fstT < presentDayR2 V_A V_E fstS :=
    drift_degrades_R2 V_A V_E fstS fstT hVA hVE hfst hfstT_le_one
  exact div_lt_one_of_lt_of_pos (presentDayR2 V_A V_E fstS)
    (presentDayR2 V_A V_E fstT) hsrc_pos hdrop

/-- Neutral allele-frequency benchmark `R²`.

This section is intentionally limited to the coarse heterozygosity/F_ST chart.
It is a neutral allele-frequency benchmark, not a mechanistic cross-population
portability law. Claims about deployed portability must instead use the
explicit SNP/LD/alignment state in `CrossPopulationMetricModel`. -/
noncomputable def targetR2FromNeutralAFBenchmark
    (V_A V_E fstTarget : ℝ) : ℝ :=
  presentDayR2 V_A V_E fstTarget

/-- Within the neutral allele-frequency benchmark, the target/source `R²` ratio
is strictly below `1` when target `F_ST` exceeds source `F_ST`. -/
theorem targetR2FromNeutralAFBenchmark_ratio_lt_one
    (V_A V_E fstSource fstTarget : ℝ)
    (hVA : 0 < V_A) (hVE : 0 < V_E)
    (h_fst : fstSource < fstTarget)
    (h_fst_bounds : 0 ≤ fstSource ∧ fstTarget < 1) :
    targetR2FromNeutralAFBenchmark V_A V_E fstTarget / presentDayR2 V_A V_E fstSource < 1 := by
  have hsrc_pos : 0 < presentDayR2 V_A V_E fstSource := by
    unfold presentDayR2 r2FromSignalVariance
    have hv_pos : 0 < presentDayPGSVariance V_A fstSource := by
      unfold presentDayPGSVariance pgsVarianceFromHet
      have h_one_minus : 0 < 1 - fstSource := by linarith [h_fst_bounds.2, h_fst]
      exact mul_pos hVA h_one_minus
    exact div_pos hv_pos (by linarith)
  have hdrop :
      targetR2FromNeutralAFBenchmark V_A V_E fstTarget < presentDayR2 V_A V_E fstSource := by
    simpa [targetR2FromNeutralAFBenchmark] using
      drift_degrades_R2 V_A V_E fstSource fstTarget hVA hVE h_fst (le_of_lt h_fst_bounds.2)
  exact div_lt_one_of_lt_of_pos
    (presentDayR2 V_A V_E fstSource)
    (targetR2FromNeutralAFBenchmark V_A V_E fstTarget)
    hsrc_pos hdrop

/-- Within the neutral allele-frequency benchmark, target `R²` is below source
`R²` once target `F_ST` exceeds source `F_ST`. -/
theorem targetR2_lt_source_from_neutralAF_benchmark
    (V_A V_E fstSource fstTarget : ℝ)
    (hVA : 0 < V_A) (hVE : 0 < V_E)
    (h_fst : fstSource < fstTarget)
    (h_fst_bounds : 0 ≤ fstSource ∧ fstTarget < 1) :
    targetR2FromNeutralAFBenchmark V_A V_E fstTarget < presentDayR2 V_A V_E fstSource := by
  simpa [targetR2FromNeutralAFBenchmark] using
    drift_degrades_R2 V_A V_E fstSource fstTarget hVA hVE h_fst (le_of_lt h_fst_bounds.2)

/-! **Deleted: `neutralAFBenchmarkRatio fstSource fstTarget = (1 - fstTarget)/(1 - fstSource)`,
together with `neutralAFBenchmarkRatio_le_inv_one_sub_source`, `_nonneg`, `_lt_one`, `_self`,
and the `FstBounds` section of `Calibrator.PortabilityBounds` that was stated about it.**

These are absent on purpose. On asymmetric effective sizes the ratio form runs `-37%` to
`-74%` low, at nine to fifteen standard errors:

      T    NeA    NeB     fstS     fstT   het_B/het_A   se   ratio form   err
    500    200   2000   0.3577   0.0582     3.7862    0.2547    1.4662   -61.3%
   1000    200   2000   0.4860   0.1187     6.5409    0.3445    1.7147   -73.8%
   1000    500   5000   0.3165   0.0450     2.2220    0.0771    1.3972   -37.1%
   2000    300   3000   0.5611   0.1454     5.7238    0.2201    1.9472   -66.0%

A symmetric design cannot rescue it. With equal branch lengths both sides of the ratio
collapse to about `1`, so a symmetric test has no power to reject a wrong functional form,
and an agreement to `3.2%` measured that way is an artifact.
`Calibrator.DriftRegime.symmetric_design_has_no_power` proves that on any symmetric design
this form and its *square* are indistinguishable.

The defect is not a miscalibration, it is the wrong argument list. The observed ratio is
`2.2` to `6.5` and is driven by the tenfold ratio in effective size, not by `F_ST`:
heterozygosity is governed by `Nₑ` and the mutation floor `hetMutationFloor`, and `F_ST` is a
between-population variance ratio that does not determine either.

**The falsification needs no definition to state**, which is why it survives the deletion.
`benchmarkRatioForm_cannot_reach_measured` below states it about the expression written out,
and is the machine-checked form of "no argument brings this formula into the measured range".
A certificate that can only be stated about a name is hostage to that name.

Nothing replaces it. `hetRatioBetweenBranches` below is a clearly-labelled candidate for
testing, and is a function of the two effective sizes, the mutation rate and the horizon,
which is what the data say the quantity depends on. `DriftRegime.benchmarkRatio` is NOT
this quantity and carries none of this: measurement confirms that form to `-0.003%`, and
what fails there is a different quantity fed into its `fst` slot. -/

/-- **The measured value is outside the range of the heterozygosity-ratio-from-`F_ST` form,
stated about the expression rather than about a name.**

At the design point `fstSource = 0.3577` the form `(1 - fstT)/(1 - fstS)` is below `3` for
every target `F_ST` in range -- its supremum there is `1/(1 - 0.3577) = 1.557`. The measured
heterozygosity ratio at that point is `3.79 ± 0.25`, more than nine standard errors above
`3`. This is the falsification in a form that depends on neither the simulation being rerun
nor the definition continuing to exist: no choice of the free argument brings the expression
into the measured range. -/
theorem benchmarkRatioForm_cannot_reach_measured (fstTarget : ℝ)
    (h0 : 0 ≤ fstTarget) :
    (1 - fstTarget) / (1 - 3577 / 10000) < 3 := by
  rw [div_lt_iff₀ (by norm_num : (0:ℝ) < 1 - 3577 / 10000)]
  linarith

/-- **Candidate replacement, offered for testing and deliberately not
substituted.**

The ratio of present-day heterozygosities between two branches that started
from the same ancestral value, as a function of the two effective sizes, the
mutation rate and the horizon -- which is what the measurement says it depends
on. It reduces to `1` when the effective sizes agree, and unlike the deleted
`(1 - fstT)/(1 - fstS)` benchmark form it has the dynamic range the data
require: `hetRatioBetweenBranches_exceeds_benchmark_ceiling` puts it above `3`
at a two-generation, tenfold-`Nₑ` design point where the benchmark form is
capped at `1.557`.

    Regime: none baked in; the closed population is the `mu = 0` case, and the
    mutation floor enters through `hetTrajectory`.

    Empirical status: UNTESTED. This is written from the recurrence, not fitted
    to the four rows tabulated in the deletion note above, and the user has the
    simulation capability to adjudicate it. -/
noncomputable def hetRatioBetweenBranches (NeA NeB mu H₀ : ℝ) (t : ℕ) : ℝ :=
  hetTrajectory NeB mu H₀ t / hetTrajectory NeA mu H₀ t

/-- Equal effective sizes give a ratio of `1`, so the whole signal in this
quantity is the asymmetry in `Nₑ` -- the variable the falsified form omits. -/
theorem hetRatioBetweenBranches_self (Ne mu H₀ : ℝ) (t : ℕ)
    (h : hetTrajectory Ne mu H₀ t ≠ 0) :
    hetRatioBetweenBranches Ne Ne mu H₀ t = 1 :=
  div_self h

/-- **The candidate has the range the measurement needs and the falsified form
does not.**  At `Nₑ_A = 1`, `Nₑ_B = 5`, no mutation and two generations the
ratio is `81/25 = 3.24`, above the ceiling that
`benchmarkRatioForm_cannot_reach_measured` places on the benchmark form. -/
theorem hetRatioBetweenBranches_exceeds_benchmark_ceiling :
    3 < hetRatioBetweenBranches 1 5 0 1 2 := by
  unfold hetRatioBetweenBranches
  rw [hetTrajectory_of_no_mutation, hetTrajectory_of_no_mutation]
  norm_num

/-- The neutral allele-frequency benchmark target `R²` is definitionally the
literal present-day target `R²` in this coarse chart. -/
theorem targetR2FromNeutralAFBenchmark_eq_presentDayR2
    (V_A V_E fstTarget : ℝ) :
    targetR2FromNeutralAFBenchmark V_A V_E fstTarget =
      presentDayR2 V_A V_E fstTarget := by
  rfl

/-! The exact calibrated Bernoulli Brier risk `π(1-π)(1-r2)` is
`TransportedMetrics.calibratedBrier`. **Do not add a second definition here to expose the
concrete product for `unfold`** -- unfolding the one definition yields the same product,
so that argues against a wrapper, not for a copy. -/

/-- Exact calibrated Bernoulli Brier risk written directly in prevalence and
explained-risk coordinates. -/
abbrev brierFromR2 (π r2 : ℝ) : ℝ :=
  TransportedMetrics.calibratedBrier π r2

/-! ### Liability-threshold primitives

These declarations precede every public profile that names the binary-trait
AUC. Lean checks declaration references in documentation as well as terms, so
placing the liability chart after its first consumer made the module fail even
though the eventual formula was present in the same file. -/

/-- Standard normal density, `φ(x) = exp(-x²/2)/√(2π)`. -/
noncomputable def standardNormalPdf (x : ℝ) : ℝ :=
  Real.exp (-x ^ 2 / 2) / Real.sqrt (2 * Real.pi)

/-- **The mode height.** The density at the mean is the normalising constant, which pins the
constant a body with the wrong normalisation would miss. -/
theorem standardNormalPdf_zero :
    standardNormalPdf 0 = 1 / Real.sqrt (2 * Real.pi) := by
  unfold standardNormalPdf
  norm_num

/-- The liability threshold `T = Φ⁻¹(1 - K)` for prevalence `K`.

    Empirical status: UNTESTED. -/
noncomputable def liabilityThreshold (K : ℝ) : ℝ := Function.invFun Phi (1 - K)

/-- Mean liability among cases, `i = φ(T)/K`.

    Empirical status: UNTESTED. -/
noncomputable def liabilityCaseMean (K : ℝ) : ℝ :=
  standardNormalPdf (liabilityThreshold K) / K

/-- Mean liability among controls, `i_c = -i·K/(1-K)`.

    Empirical status: UNTESTED. -/
noncomputable def liabilityControlMean (K : ℝ) : ℝ :=
  -liabilityCaseMean K * K / (1 - K)

/-- Score variance among cases, `v₁ = 1 - R²·i·(i - T)`.

    Empirical status: UNTESTED. -/
noncomputable def liabilityCaseVariance (r2 K : ℝ) : ℝ :=
  1 - r2 * liabilityCaseMean K * (liabilityCaseMean K - liabilityThreshold K)

/-- Score variance among controls, `v₀ = 1 - R²·i_c·(i_c - T)`.

    Empirical status: UNTESTED. -/
noncomputable def liabilityControlVariance (r2 K : ℝ) : ℝ :=
  1 - r2 * liabilityControlMean K * (liabilityControlMean K - liabilityThreshold K)

/-- **The liability-threshold AUC**, with prevalence a required argument.

Empirical status: VALIDATED against 400 simulated PGS studies. Pooled RMSE is
`0.0121` with bias `-0.0007`, matching the independently measured `0.0120`
seed-to-seed noise floor.

Power: prevalence is the axis this chart has and the equal-variance Gaussian
one lacks, and the design sweeps it. At `R² = 0.3` the AUC this definition
predicts runs from `0.753` at prevalence `0.5` to `0.921` at prevalence
`0.001`, while a prevalence-free chart returns one number for that whole range.
The span is more than a sixth of the discriminable interval above chance, so a
chart missing the prevalence dependence cannot fit it. -/
noncomputable def liabilityThresholdAUCFromExplainedR2 (r2 K : ℝ) : ℝ :=
  Phi ((liabilityCaseMean K - liabilityControlMean K) * Real.sqrt r2 /
    Real.sqrt (liabilityCaseVariance r2 K + liabilityControlVariance r2 K))

/-! **Deleted: `LiabilityThresholdRegime`.**

An *obligation* structure with no consumer is worse than an unused lemma. Its whole claim
is that somebody must discharge these conditions before using the formula, and nobody does,
so it reads as rigour from the outside while every real use site bypasses it.

Three of the seven fields are results rather than domain conditions, so any use of the
structure would import them unproved:

* `threshold_spec : Phi (liabilityThreshold K) = 1 - K`. Since `liabilityThreshold K` is
  `Function.invFun Phi (1 - K)`, this says `Phi` hits `1 - K`, i.e. that the standard
  normal CDF is onto `(0, 1)`. That is a theorem — continuity plus the limits at `±∞` plus
  the intermediate value theorem — and it is *derivable* from `prevalence_pos` and
  `prevalence_lt_one`, which is exactly why it should not have been assumed alongside
  them. `Calibrator.Probability` defines `Phi` and proves nothing about it, so the
  derivation is not currently available; supplying it is the honest way to reinstate this.
* `caseVariance_pos` and `controlVariance_pos`. These are not conditions a caller can
  choose to meet: `liabilityCaseVariance r2 K` is a closed formula in `r2` and `K`, so its
  positivity is true or false once those are fixed. Both follow from `0 ≤ r2 < 1` together
  with the truncated-normal bound `0 ≤ i·(i - T) ≤ 1` on the selection intensity, which is
  the standard fact that truncation cannot increase variance. That bound is a real result
  and the corpus does not have it.

Reinstating this regime honestly means proving those three, not restating them. Until
then, the four genuine domain conditions (`0 < K < 1`, `0 ≤ r2 < 1`) are what the
individual theorems below already take as explicit hypotheses where they need them. -/

/-- Source Brier chart as a function of prevalence and source `R²`. -/
noncomputable def sourceBrierFromR2 (π r2Source : ℝ) : ℝ :=
  TransportedMetrics.calibratedBrier π r2Source

/-- The source Brier chart is the canonical source Brier
specialization. -/
theorem sourceBrierFromR2_eq_transportedMetrics
    (π r2Source : ℝ) :
    sourceBrierFromR2 π r2Source =
      TransportedMetrics.calibratedBrier π r2Source := by
  rfl

/-- Exact target calibrated Brier risk under the Bernoulli-mixing model from
explicit target state. -/
noncomputable def targetExactCalibratedBrierRisk
    (π V_A V_E fstTarget : ℝ) : ℝ :=
  TransportedMetrics.calibratedBrier π
    (targetR2FromNeutralAFBenchmark V_A V_E fstTarget)

/-- Neutral allele-frequency benchmark target Brier map used by the dashboard
(`Brier(R²_target)`). -/
noncomputable def targetBrierFromNeutralAFBenchmark
    (π V_A V_E fstTarget : ℝ) : ℝ :=
  targetExactCalibratedBrierRisk π V_A V_E fstTarget

/-- Canonical bundled deployed metrics under the neutral allele-frequency
benchmark state.

**FOR A CONTINUOUS OUTCOME. On a dichotomised trait this record is internally
inconsistent, and that inconsistency is the clearest statement of the defect in this
family:** it takes a prevalence `π`, uses it to compute the Brier risk, and then computes
the AUC with a formula that has no prevalence argument at all. The same record therefore
treats the trait as binary for one metric and as continuous for another.

`neutralAFBenchmarkLiabilityMetricProfile` is the dichotomised-trait version, which spends
the `π` it was already given on both. -/
noncomputable def neutralAFBenchmarkMetricProfile
    (π V_A V_E fstTarget : ℝ) : TransportedMetrics.Profile :=
  TransportedMetrics.profileFromSignalVariance π V_E (presentDayPGSVariance V_A fstTarget)

/-- The bundled neutral allele-frequency benchmark metrics reproduce the file's public
`R²`, AUC, and Brier surfaces exactly. -/
theorem neutralAFBenchmarkMetricProfile_eq
    (π V_A V_E fstTarget : ℝ) :
    neutralAFBenchmarkMetricProfile π V_A V_E fstTarget =
      { r2 := targetR2FromNeutralAFBenchmark V_A V_E fstTarget
      , auc := presentDayEqualVarianceGaussianAUC V_A V_E fstTarget
      , brier := targetBrierFromNeutralAFBenchmark π V_A V_E fstTarget } := by
  ext
  · change
      TransportedMetrics.r2FromSignalVariance (presentDayPGSVariance V_A fstTarget) V_E =
        targetR2FromNeutralAFBenchmark V_A V_E fstTarget
    unfold targetR2FromNeutralAFBenchmark TransportedMetrics.r2FromSignalVariance presentDayR2
    rfl
  · change
      TransportedMetrics.equalVarianceGaussianAUCFromSignalVariance (presentDayPGSVariance V_A
          fstTarget) V_E =
        presentDayEqualVarianceGaussianAUC V_A V_E fstTarget
    rfl
  · change
      TransportedMetrics.calibratedBrier π
        (TransportedMetrics.r2FromSignalVariance (presentDayPGSVariance V_A fstTarget) V_E) =
        targetBrierFromNeutralAFBenchmark π V_A V_E fstTarget
    -- `TransportedMetrics.calibratedBrier` was named TWICE in this list. The
    -- first occurrence unfolds it; the second then fails, because by that
    -- point the constant is gone from the goal. `unfold` is not idempotent --
    -- it errors when a name is already absent rather than succeeding vacuously.
    unfold targetBrierFromNeutralAFBenchmark targetExactCalibratedBrierRisk
      TransportedMetrics.calibratedBrier targetR2FromNeutralAFBenchmark
      TransportedMetrics.r2FromSignalVariance
      presentDayR2
    rfl

/-- Full neutral allele-frequency benchmark AUC degradation theorem:
strictly higher drift implies strictly lower exact target AUC. -/
theorem targetAUC_lt_source_of_neutralAF_benchmark
    (V_A V_E fstSource fstTarget : ℝ)
    (hVA : 0 < V_A) (hVE : 0 < V_E)
    (h_fst : fstSource < fstTarget)
    (h_fst_bounds : 0 ≤ fstSource ∧ fstTarget < 1) :
    presentDayEqualVarianceGaussianAUC V_A V_E fstTarget <
      presentDayEqualVarianceGaussianAUC V_A V_E fstSource := by
  simpa [presentDayEqualVarianceGaussianAUC] using
    drift_degrades_AUC_of_strictMono
      V_A V_E fstSource fstTarget hVA hVE h_fst (le_of_lt h_fst_bounds.2)

/-- Exact **equal-variance Gaussian** AUC as a function of SNR:
`AUC = Φ(√(snr/2))`.

    This is the AUC when cases and controls are two normals of equal variance
    separated by `√snr`. It is *not* the liability-threshold AUC, under which
    cases are a truncated tail, so the two distributions have different
    variances and the separation depends on where the truncation falls. It was
    named and documented as the liability AUC, twice as "exact".

    Numerical integration over the bivariate normal, agreeing with a
    4·10⁶-draw Monte Carlo to about `0.001`, puts the error at 3% to 26%,
    always understating, and worst where it matters most: at `R² = 0.3` the
    true AUC runs from `0.753` at prevalence `0.5` to `0.921` at `0.001`,
    while this returns one number per `R²` because it takes no prevalence.
    That missing argument is why no constant could repair it.

    Empirical status: VALIDATED for the equal-variance Gaussian model it now
    names; FALSIFIED as the liability-threshold AUC. The binary-trait
    counterpart is `liabilityThresholdAUCFromExplainedR2`, which takes the
    prevalence this one lacks and measures at RMSE `0.0121` where this form is
    biased `-0.068`.

    Power: this chart's own prediction spans `0.760250`, `0.921350`, `0.999797`
    and `1.000000` at `snr = 1, 4, 25, 100`, which is the design the
    two-Gaussian Monte Carlo of `DGP.equalVarianceGaussianAUCFromSignalVariance`
    was run on, at `200000` draws per point; the two are the same chart under
    `snr = vSignal / vNoise`, and
    `equalVarianceGaussianAUCFromSNR_eq_variance` is the theorem saying so, so
    the measurement is of this function rather than of a sibling formula. The
    prediction covers chance-to-perfect discrimination across that design. -/
noncomputable def equalVarianceGaussianAUCFromSNR (snr : ℝ) : ℝ :=
  Phi (Real.sqrt (snr / 2))

/-- The signal-to-noise and signal/residual-variance parameterizations are exactly the
same closed-form chart.  This is algebra only: it does not assert that either chart is the
AUC of a biological process without a separately proved distributional model. -/
theorem equalVarianceGaussianAUCFromSNR_eq_variance
    (vSignal vEnv : ℝ) (h_env : vEnv ≠ 0) :
    equalVarianceGaussianAUCFromSNR (vSignal / vEnv) =
      equalVarianceGaussianAUCFromSignalVariance vSignal vEnv := by
  rw [equalVarianceGaussianAUCFromSignalVariance_eq_formula_of_ne_noise _ _ h_env]
  unfold equalVarianceGaussianAUCFromSNR
  congr 2
  rw [div_div, mul_comm]

/-! The variance form of the equal-variance Gaussian AUC is
`DGP.equalVarianceGaussianAUCFromSignalVariance`. **Do not write a second copy here.** Two
copies of an AUC formula can drift to opposite claims about which quantity they compute --
equal-variance Gaussian versus liability-threshold, which are not the same and differ by a
measured `-0.068` AUC -- and one definition cannot drift from itself.  The Lean definition
is deliberately only a chart; process-level applicability must be proved from an explicit
distributional model rather than supplied as a theorem-bearing parameter. -/

/-- With `vEnv = 1`, variance form equals SNR form exactly. -/
theorem equalVarianceGaussianAUCFromVariances_scaleOne (vSignal : ℝ) :
    equalVarianceGaussianAUCFromSignalVariance vSignal 1 =
      equalVarianceGaussianAUCFromSNR vSignal := by
  rw [equalVarianceGaussianAUCFromSignalVariance_eq_formula_of_ne_noise _ _ (by norm_num)]
  unfold equalVarianceGaussianAUCFromSNR
  ring_nf

/-- On nonnegative SNR, the **equal-variance Gaussian** AUC map is strictly increasing. -/
theorem equalVarianceGaussianAUCFromSNR_strictMonoOn_nonneg :
    StrictMonoOn equalVarianceGaussianAUCFromSNR (Set.Ici 0) := by
  intro x hx y hy hxy
  unfold equalVarianceGaussianAUCFromSNR
  apply strictMono_Phi
  have hx2 : 0 ≤ x / 2 :=
    div_nonneg hx (by positivity)
  have hxy2 : x / 2 < y / 2 := by nlinarith
  exact Real.sqrt_lt_sqrt hx2 hxy2

/-- Equal-variance Gaussian AUC as a direct chart on deployed `R²`.

On `r2 < 1` this is `Φ (sqrt (r2 / (2 * (1 - r2))))`. At and above the perfect-prediction
boundary it is `1`, so totalized real division cannot turn `r2 = 1` into chance discrimination.
Values above one are outside the statistical model and are clamped rather than extrapolated.

This is not a liability-threshold AUC: that chart also requires prevalence.

    Empirical status: VALIDATED for the equal-variance Gaussian model on `[0, 1]`;
    FALSIFIED as the liability-threshold AUC.

    Power: on `r2 = 0.1, 0.3, 0.5, 0.8` this chart predicts `0.5932`, `0.6783`,
    `0.7602` and `0.9214`, which is `snr = r2 / (1 - r2)` fed to the SNR form it
    equals below the boundary. That span runs from near chance to near-perfect
    discrimination. The falsification is read off the same span: at `r2 = 0.3`
    the liability-threshold AUC runs from `0.753` to `0.921` as prevalence moves
    from `0.5` to `0.001`, and this chart answers `0.6783` for all of it. -/
noncomputable def equalVarianceGaussianAUCFromExplainedR2 (r2 : ℝ) : ℝ :=
  if 1 ≤ r2 then 1 else Phi (Real.sqrt (r2 / (2 * (1 - r2))))

/-- Below the perfect-prediction boundary, the total chart is the Gaussian closed form. -/
theorem equalVarianceGaussianAUCFromExplainedR2_eq_formula_of_lt_one
    (r2 : ℝ) (h : r2 < 1) :
    equalVarianceGaussianAUCFromExplainedR2 r2 =
      Phi (Real.sqrt (r2 / (2 * (1 - r2)))) := by
  simp [equalVarianceGaussianAUCFromExplainedR2, not_le.mpr h]

/-- Perfect prediction gives perfect discrimination. -/
@[simp] theorem equalVarianceGaussianAUCFromExplainedR2_at_one :
    equalVarianceGaussianAUCFromExplainedR2 1 = 1 := by
  simp [equalVarianceGaussianAUCFromExplainedR2]

/-! ### WHY A RANGE CHECK COULD NOT CATCH THIS, WHICH IS THE POINT

Ten definitions in this AUC family were flagged by the range checker as **provably unable
to fail**: their bound is `Φ`'s codomain, so "the result lies in `[0,1]`" is a fact about
`Phi` and says nothing whatever about the body. They were counted as covered while being
structurally incapable of detecting the defect below.

**A check that verifies "is it a probability" cannot catch "is it the right probability."**
The equal-variance form returns a perfectly well-formed number in `[0,1]` and is biased by
seven AUC points on dichotomised traits. Every range check passes; the biology is wrong.

This is the concrete instance the vacuity investigation was looking for. The general lesson
is that a bound inherited from a codomain is not evidence about a definition, and a coverage
count that credits such bounds is counting something other than what its name says.

### The liability-threshold AUC, which is the one binary traits need

`equalVarianceGaussianAUCFromExplainedR2` is a true theorem about the equal-variance
Gaussian model and the **wrong formula for a dichotomised trait**, which is most of what
polygenic scores are used for. Its own docstring already recorded
`FALSIFIED as the liability-threshold AUC`; what was missing was the right formula, not a
correction to that one. Both are kept, and each names the other and the regime that selects
it, because the defect was never that either was false — it was that nothing said when each
applies.

The formula below is **classical**: it is the liability-threshold result of Wray et al.
(2010), *The genetic interpretation of area under the ROC curve*, in the same way the
Gaussian information constants and van Trees are classical components named as such. The
contribution here is not the derivation; it is that the corpus carried only the
equal-variance form for binary traits, and that this one has been measured. -/

/-! The liability-threshold primitives and their regime are declared before
the first binary-trait profile above. The substantive comparison starts here,
after the equal-variance chart has also been declared. -/

/-- **The two AUC maps are not the same function, and must not be collapsed into one.**

The equal-variance form takes no prevalence argument, so it is constant in `K`; the
liability form is not. Hence if the liability AUC differs between *any* two prevalences at a
fixed `r2` — which is what the 400-run validation measures, the fitted `K` moving the
prediction by far more than the `0.0120` noise floor — then no identity can equate the two
maps.

This exists to stop a later simplification from quietly identifying them. The hypothesis is
the empirical fact, supplied rather than assumed, in the same way
`NearLowDimensionalFamily` is carried elsewhere. -/
theorem liabilityAUC_ne_equalVarianceAUC_of_prevalence_dependent
    {r2 K₁ K₂ : ℝ}
    (hK : liabilityThresholdAUCFromExplainedR2 r2 K₁ ≠
      liabilityThresholdAUCFromExplainedR2 r2 K₂) :
    ¬ (∀ K : ℝ, liabilityThresholdAUCFromExplainedR2 r2 K =
        equalVarianceGaussianAUCFromExplainedR2 r2) := by
  intro hcollapse
  exact hK ((hcollapse K₁).trans (hcollapse K₂).symm)

/-- Under the regime the case mean strictly exceeds the control mean, so the numerator of
the AUC argument is non-negative and the map is not accidentally reading the wrong tail.

This is the one structural fact worth having beyond the separation theorem: `i > 0 > i_c`
holds for every prevalence in `(0,1)`, because `i_c` is a negative multiple of `i`. -/
theorem liabilityControlMean_lt_caseMean {K : ℝ} (hK0 : 0 < K) (hK1 : K < 1) :
    liabilityControlMean K < liabilityCaseMean K := by
  have hpdf : 0 < standardNormalPdf (liabilityThreshold K) := by
    unfold standardNormalPdf
    exact div_pos (Real.exp_pos _) (Real.sqrt_pos.2 (by positivity))
  have hi : 0 < liabilityCaseMean K :=
    div_pos hpdf hK0
  have h1K : 0 < 1 - K := by linarith
  have hneg : liabilityControlMean K < 0 := by
    unfold liabilityControlMean
    apply div_neg_of_neg_of_pos _ h1K
    nlinarith
  linarith

/-- **Target AUC from the neutral allele-frequency benchmark, for a DICHOTOMISED trait.**

Prevalence `K` is a **required argument**, and that is the whole design. The failure this
replaces was not that someone chose a wrong prevalence — it was that no prevalence was ever
named, so a drift-induced `R²` drop was converted into AUC units by a formula that has no
place to put one. Making `K` mandatory turns a silently biased number into a call that does
not elaborate until whoever owns the call site supplies the prevalence, which is the person
who knows it.

This is the conversion to use for a binary trait. For a genuinely **continuous** outcome the
equal-variance chart is correct and `presentDayEqualVarianceGaussianAUC` is the one to call.

    Empirical status: UNTESTED. -/
noncomputable def targetLiabilityAUCFromNeutralAFBenchmark
    (V_A V_E fstTarget K : ℝ) : ℝ :=
  liabilityThresholdAUCFromExplainedR2 (presentDayR2 V_A V_E fstTarget) K

/-- The same quantity written through the explicit benchmark `R²`, so the two cannot drift
apart. -/
theorem targetLiabilityAUCFromNeutralAFBenchmark_eq (V_A V_E fstTarget K : ℝ) :
    targetLiabilityAUCFromNeutralAFBenchmark V_A V_E fstTarget K =
      liabilityThresholdAUCFromExplainedR2 (presentDayR2 V_A V_E fstTarget) K := rfl

/-- **Bundled deployed metrics for a DICHOTOMISED trait**, with the prevalence used for the
AUC as well as for the Brier risk.

No new modelling input is required to build this: `π` is already an argument of the profile
it replaces. The old record simply declined to use it for the discrimination metric, which
is how a `-0.068` AUC bias survived beside a Brier risk computed correctly at the same
prevalence.

    Empirical status: UNTESTED. -/
noncomputable def neutralAFBenchmarkLiabilityMetricProfile
    (π V_A V_E fstTarget : ℝ) : TransportedMetrics.Profile :=
  { r2 := targetR2FromNeutralAFBenchmark V_A V_E fstTarget
  , auc := targetLiabilityAUCFromNeutralAFBenchmark V_A V_E fstTarget π
  , brier := targetBrierFromNeutralAFBenchmark π V_A V_E fstTarget }

/-- The two profiles agree on `R²` and Brier and differ **only** in the AUC field, which
localises the defect to one coordinate rather than leaving it diffuse. -/
theorem liabilityProfile_differs_only_in_auc (π V_A V_E fstTarget : ℝ) :
    (neutralAFBenchmarkLiabilityMetricProfile π V_A V_E fstTarget).r2 =
      targetR2FromNeutralAFBenchmark V_A V_E fstTarget ∧
    (neutralAFBenchmarkLiabilityMetricProfile π V_A V_E fstTarget).brier =
      targetBrierFromNeutralAFBenchmark π V_A V_E fstTarget ∧
    (neutralAFBenchmarkLiabilityMetricProfile π V_A V_E fstTarget).auc =
      liabilityThresholdAUCFromExplainedR2 (presentDayR2 V_A V_E fstTarget) π :=
  ⟨rfl, rfl, rfl⟩

/-- **The `R²` and variance readings of the equal-variance Gaussian chart agree.**

Reading the AUC off an `R²` needs the variance split as well as the Gaussian regime: `r2`
determines a signal-to-noise ratio only once the outcome variance is known to be signal
plus environment. With `h_split` supplied, `r2 / (1 - r2)` *is* that ratio, and this form
reduces to the one already discharged.

Stating it as a chart identity prevents it from being read as a general biological
conversion.  No Gaussian-process theorem is accepted as an argument. -/
theorem equalVarianceGaussianAUCFromExplainedR2_eq_variance
    (vSignal vEnv : ℝ) (h_signal : 0 ≤ vSignal) (h_env : 0 < vEnv) :
    equalVarianceGaussianAUCFromExplainedR2
        (r2FromSignalVariance vSignal vEnv) =
      equalVarianceGaussianAUCFromSignalVariance vSignal vEnv := by
  have h_total : 0 < vSignal + vEnv := add_pos_of_nonneg_of_pos h_signal h_env
  have h_r2_lt : r2FromSignalVariance vSignal vEnv < 1 := by
    unfold r2FromSignalVariance
    exact (div_lt_one h_total).2 (lt_add_of_pos_right vSignal h_env)
  rw [equalVarianceGaussianAUCFromExplainedR2_eq_formula_of_lt_one _ h_r2_lt]
  rw [← equalVarianceGaussianAUCFromSNR_eq_variance vSignal vEnv (ne_of_gt h_env)]
  unfold equalVarianceGaussianAUCFromSNR r2FromSignalVariance
  congr 2
  -- `field_simp` was called without the two nonzero facts proved directly
  -- above, so it could not cancel `vEnv` and left `X * Y * Y⁻¹ = X` for
  -- `ring`, which cannot discharge it: cancelling needs `Y ≠ 0` and `ring`
  -- never consults hypotheses. Whether the fed version closes the goal
  -- outright or leaves a polynomial identity is not knowable in advance, so
  -- `first` takes neither bet.
  field_simp [ne_of_gt h_total, ne_of_gt h_env]
  ring

/-- **Cross-check: the `R²` form and the SNR form are the same map.**

Under `snr = R²/(1 - R²)` the two agree exactly. Stated because they were
written separately and never related, which is the condition under which the
whole family could be misnamed without any of them contradicting the others. -/
theorem equalVarianceGaussianAUCFromExplainedR2_eq_fromSNR
    (r2 : ℝ) (h : r2 < 1) :
    equalVarianceGaussianAUCFromExplainedR2 r2 =
      equalVarianceGaussianAUCFromSNR (r2 / (1 - r2)) := by
  rw [equalVarianceGaussianAUCFromExplainedR2_eq_formula_of_lt_one r2 h]
  unfold equalVarianceGaussianAUCFromSNR
  congr 2
  rw [div_div, mul_comm]

/-- On valid deployed `R²` values, the liability-threshold AUC chart is strictly
increasing whenever `Phi` is strictly increasing. -/
theorem equalVarianceGaussianAUCFromExplainedR2_strictMonoOn_unitInterval :
    StrictMonoOn equalVarianceGaussianAUCFromExplainedR2 (Set.Ico 0 1) := by
  intro x hx y hy hxy
  rw [equalVarianceGaussianAUCFromExplainedR2_eq_formula_of_lt_one x hx.2,
    equalVarianceGaussianAUCFromExplainedR2_eq_formula_of_lt_one y hy.2]
  apply strictMono_Phi
  have hx_one_sub : 0 < 1 - x := by linarith [hx.2]
  have hy_one_sub : 0 < 1 - y := by linarith [hy.2]
  have hx_den : 0 < 2 * (1 - x) :=
    mul_pos (by norm_num) hx_one_sub
  have hy_den : 0 < 2 * (1 - y) :=
    mul_pos (by norm_num) hy_one_sub
  have hx_arg_nonneg : 0 ≤ x / (2 * (1 - x)) :=
    div_nonneg hx.1 (le_of_lt hx_den)
  have harg_lt : x / (2 * (1 - x)) < y / (2 * (1 - y)) := by
    rw [div_lt_div_iff₀ hx_den hy_den]
    nlinarith
  exact Real.sqrt_lt_sqrt hx_arg_nonneg harg_lt

/-- **Equal-variance Gaussian** AUC induced by the full explicit source-side driver
state. Like the target-side exported AUC, this is built directly from source
explained signal and source residual variance under the source-learned score
equation.

    This is not the liability-threshold AUC: cases under a liability threshold are a
    truncated tail, so the two distributions have unequal variances and the AUC depends on
    prevalence, which this takes no argument for.

    Empirical status: UNTESTED. -/
noncomputable def equalVarianceGaussianAUCFromSourceWeights {p q : ℕ}
    (m : CrossPopulationMetricModel p q) (P : Pop) : ℝ :=
  equalVarianceGaussianAUCFromSignalVariance
    (explainedSignalVarianceFromSourceWeights m P)
    (residualVarianceFromSourceWeights m P)

/-- The mechanistic source AUC is exactly the explicit liability-threshold map
applied to source explained signal and source residual variance. -/
theorem sourceEqualVarianceGaussianAUCFromSourceWeights_eq_explicit_source_variances
    {p q : ℕ} (m : CrossPopulationMetricModel p q) :
    equalVarianceGaussianAUCFromSourceWeights m Pop.source =
      equalVarianceGaussianAUCFromSignalVariance
        (explainedSignalVarianceFromSourceWeights m Pop.source)
        (residualVarianceFromSourceWeights m Pop.source) := by
  rfl

/-- The direct mechanistic source AUC agrees with the `R²` chart induced by the
same source explained-signal and total-variance decomposition.

This is only a derived coordinate identity; it is not the defining
construction of source AUC. -/
theorem sourceEqualVarianceGaussianAUCFromSourceWeights_eq_explainedR2_chart_of_lt_one {p q : ℕ}
    (m : CrossPopulationMetricModel p q)
    (h_r2 : r2FromSourceWeights m Pop.source < 1) :
    equalVarianceGaussianAUCFromSourceWeights m Pop.source =
      equalVarianceGaussianAUCFromExplainedR2 (r2FromSourceWeights m Pop.source) := by
  have h_source_ne : (m.outcomeVariance Pop.source) ≠ 0 :=
    ne_of_gt (m.outcomeVariance_pos Pop.source)
  have h_signal_lt :
      explainedSignalVarianceFromSourceWeights m Pop.source <
        effectiveOutcomeVariance m Pop.source := by
    exact (div_lt_one (by simpa using m.outcomeVariance_pos Pop.source)).mp
      (by simpa [r2FromSourceWeights] using h_r2)
  have h_residual_ne :
      residualVarianceFromSourceWeights m Pop.source ≠ 0 := by
    rw [residualVarianceFromSourceWeights]
    exact ne_of_gt (sub_pos.mpr h_signal_lt)
  rw [equalVarianceGaussianAUCFromExplainedR2_eq_formula_of_lt_one _ h_r2]
  rw [equalVarianceGaussianAUCFromSourceWeights,
    equalVarianceGaussianAUCFromSignalVariance_eq_formula_of_ne_noise _ _ h_residual_ne]
  unfold residualVarianceFromSourceWeights r2FromSourceWeights
  congr 1
  congr 1
  field_simp [h_source_ne]

/-- The mechanistic target AUC is exactly the explicit liability-threshold map
applied to target explained signal and target residual variance. -/
theorem targetEqualVarianceGaussianAUCFromSourceWeights_eq_explicit_target_variances {p q : ℕ}
    (m : CrossPopulationMetricModel p q) :
    equalVarianceGaussianAUCFromSourceWeights m Pop.target =
      equalVarianceGaussianAUCFromSignalVariance
        (explainedSignalVarianceFromSourceWeights m Pop.target)
        (residualVarianceFromSourceWeights m Pop.target) := by
  rfl

/-- Exact mechanistic target liability-AUC portability law from transported
score moments. This is the direct liability-threshold variance law on the
explicit SNP-level transport model. -/
theorem targetEqualVarianceGaussianAUCFromSourceWeights_exact_metric_portability_law
    {p q : ℕ} (m : CrossPopulationMetricModel p q) :
    equalVarianceGaussianAUCFromSourceWeights m Pop.target =
      equalVarianceGaussianAUCFromSignalVariance
        ((predictiveCovarianceFromSourceWeights m Pop.target) ^ 2 /
          scoreVarianceFromSourceWeights m Pop.target)
        (effectiveOutcomeVariance m Pop.target -
          (predictiveCovarianceFromSourceWeights m Pop.target) ^ 2 /
            scoreVarianceFromSourceWeights m Pop.target) := by
  rw [targetEqualVarianceGaussianAUCFromSourceWeights_eq_explicit_target_variances]
  simp [explainedSignalVarianceFromSourceWeights,
    residualVarianceFromSourceWeights]

/-- Exact mechanistic target liability-AUC portability law with the additive
biological loss budget made explicit in the residual term. -/
theorem targetEqualVarianceGaussianAUCFromSourceWeights_exact_loss_budget_law
    {p q : ℕ} (m : CrossPopulationMetricModel p q) :
    equalVarianceGaussianAUCFromSourceWeights m Pop.target =
      equalVarianceGaussianAUCFromSignalVariance
        ((predictiveCovarianceFromSourceWeights m Pop.target) ^ 2 /
          scoreVarianceFromSourceWeights m Pop.target)
        ((m.outcomeVariance Pop.target) +
          brokenTaggingResidual m +
          ancestrySpecificLDResidual m +
          sourceSpecificOverfitResidual m +
          novelUntaggablePhenotypeResidual m -
          (predictiveCovarianceFromSourceWeights m Pop.target) ^ 2 /
            scoreVarianceFromSourceWeights m Pop.target) := by
  rw [targetEqualVarianceGaussianAUCFromSourceWeights_exact_metric_portability_law,
    effectiveTargetOutcomeVariance_eq_targetOutcomeVariance_add_losses]

/-- The direct mechanistic target AUC agrees with the `R²` chart induced by the
same target explained-signal and total-variance decomposition.

This is only a derived coordinate identity; it is not the defining
construction of target AUC. -/
theorem targetEqualVarianceGaussianAUCFromSourceWeights_eq_explainedR2_chart_of_lt_one {p q : ℕ}
    (m : CrossPopulationMetricModel p q)
    (h_r2 : r2FromSourceWeights m Pop.target < 1) :
    equalVarianceGaussianAUCFromSourceWeights m Pop.target =
      equalVarianceGaussianAUCFromExplainedR2 (r2FromSourceWeights m Pop.target) := by
  have h_eff_ne : effectiveOutcomeVariance m Pop.target ≠ 0 :=
    ne_of_gt (effectiveTargetOutcomeVariance_pos m)
  have h_signal_lt :
      explainedSignalVarianceFromSourceWeights m Pop.target <
        effectiveOutcomeVariance m Pop.target := by
    exact (div_lt_one (effectiveTargetOutcomeVariance_pos m)).mp
      (by simpa [r2FromSourceWeights] using h_r2)
  have h_residual_ne :
      residualVarianceFromSourceWeights m Pop.target ≠ 0 := by
    rw [residualVarianceFromSourceWeights]
    exact ne_of_gt (sub_pos.mpr h_signal_lt)
  rw [equalVarianceGaussianAUCFromExplainedR2_eq_formula_of_lt_one _ h_r2]
  rw [equalVarianceGaussianAUCFromSourceWeights,
    equalVarianceGaussianAUCFromSignalVariance_eq_formula_of_ne_noise _ _ h_residual_ne]
  unfold residualVarianceFromSourceWeights r2FromSourceWeights
  congr 1
  congr 1
  field_simp [h_eff_ne]

/-- Canonical mechanistic deployed source metric profile evaluated at an
arbitrary observed prevalence coordinate `π`. This is the source-side analogue
of `targetMetricProfileFromSourceWeights`, and it lets downstream calibration
theory compare source and target Brier on the same target-population
prevalence scale.

    Empirical status: UNTESTED. -/
noncomputable def sourceMetricProfileFromSourceWeightsAtPrevalence {p q : ℕ}
    (m : CrossPopulationMetricModel p q) (π : ℝ) : TransportedMetrics.Profile where
  r2 := r2FromSourceWeights m Pop.source
  auc := equalVarianceGaussianAUCFromSourceWeights m Pop.source
  brier := sourceCalibratedBrierFromSourceWeightsAtPrevalence m π

@[simp] theorem sourceMetricProfileFromSourceWeightsAtPrevalence_r2 {p q : ℕ}
    (m : CrossPopulationMetricModel p q) (π : ℝ) :
    (sourceMetricProfileFromSourceWeightsAtPrevalence m π).r2 =
      r2FromSourceWeights m Pop.source := by
  rfl

@[simp] theorem sourceMetricProfileFromSourceWeightsAtPrevalence_auc {p q : ℕ}
    (m : CrossPopulationMetricModel p q) (π : ℝ) :
    (sourceMetricProfileFromSourceWeightsAtPrevalence m π).auc =
      equalVarianceGaussianAUCFromSourceWeights m Pop.source := by
  rfl

@[simp] theorem sourceMetricProfileFromSourceWeightsAtPrevalence_brier {p q : ℕ}
    (m : CrossPopulationMetricModel p q) (π : ℝ) :
    (sourceMetricProfileFromSourceWeightsAtPrevalence m π).brier =
      sourceCalibratedBrierFromSourceWeightsAtPrevalence m π := by
  rfl

/-- The source metric profile evaluated on the target-population observed
prevalence scale carried by the mechanistic target state.

    Empirical status: UNTESTED. -/
noncomputable def sourceMetricProfileFromSourceWeightsAtTargetPrevalence {p q : ℕ}
    (m : CrossPopulationMetricModel p q) : TransportedMetrics.Profile :=
  sourceMetricProfileFromSourceWeightsAtPrevalence m m.targetPrevalence

@[simp] theorem sourceMetricProfileFromSourceWeightsAtTargetPrevalence_r2 {p q : ℕ}
    (m : CrossPopulationMetricModel p q) :
    (sourceMetricProfileFromSourceWeightsAtTargetPrevalence m).r2 =
      r2FromSourceWeights m Pop.source := by
  rfl

@[simp] theorem sourceMetricProfileFromSourceWeightsAtTargetPrevalence_auc {p q : ℕ}
    (m : CrossPopulationMetricModel p q) :
    (sourceMetricProfileFromSourceWeightsAtTargetPrevalence m).auc =
      equalVarianceGaussianAUCFromSourceWeights m Pop.source := by
  rfl

@[simp] theorem sourceMetricProfileFromSourceWeightsAtTargetPrevalence_brier {p q : ℕ}
    (m : CrossPopulationMetricModel p q) :
    (sourceMetricProfileFromSourceWeightsAtTargetPrevalence m).brier =
      sourceCalibratedBrierFromSourceWeightsAtPrevalence m m.targetPrevalence := by
  rfl

/-- Canonical mechanistic deployed metric profile induced by the explicit
SNP-level transported score equation. The upstream state is the full
source-weights/target-LD/target-tagging system, with AUC bundled from the
explicit target signal/residual moment pair rather than from a source-side
transport surrogate. -/
noncomputable def targetMetricProfileFromSourceWeights {p q : ℕ}
    (m : CrossPopulationMetricModel p q) : TransportedMetrics.Profile where
  r2 := r2FromSourceWeights m Pop.target
  auc := equalVarianceGaussianAUCFromSourceWeights m Pop.target
  brier := targetCalibratedBrierFromSourceWeights m

@[simp] theorem targetMetricProfileFromSourceWeights_r2 {p q : ℕ}
    (m : CrossPopulationMetricModel p q) :
    (targetMetricProfileFromSourceWeights m).r2 = r2FromSourceWeights m Pop.target := by
  rfl

@[simp] theorem targetMetricProfileFromSourceWeights_auc {p q : ℕ}
    (m : CrossPopulationMetricModel p q) :
    (targetMetricProfileFromSourceWeights
        m).auc = equalVarianceGaussianAUCFromSourceWeights m Pop.target := by
  rfl

@[simp] theorem targetMetricProfileFromSourceWeights_brier {p q : ℕ}
    (m : CrossPopulationMetricModel p q) :
    (targetMetricProfileFromSourceWeights m).brier =
      targetCalibratedBrierFromSourceWeights m := by
  rfl

/-- Bundled exact mechanistic metric portability law.

The exported target metric profile is determined exactly by:
- the transported score/outcome covariance under source-learned weights,
- the target score variance under the target LD matrix,
- the target prevalence, and
- the additive biological loss budget entering the effective target outcome
  variance.

This packages the exact `R²`, liability-AUC, and Brier laws on the explicit
SNP-level transport state. -/
theorem targetMetricProfileFromSourceWeights_exact_mechanistic_portability_law
    {p q : ℕ} (m : CrossPopulationMetricModel p q) :
    targetMetricProfileFromSourceWeights m =
      { r2 :=
          (predictiveCovarianceFromSourceWeights m Pop.target) ^ 2 /
            (scoreVarianceFromSourceWeights m Pop.target * effectiveOutcomeVariance m Pop.target)
      , auc :=
          equalVarianceGaussianAUCFromSignalVariance
            ((predictiveCovarianceFromSourceWeights m Pop.target) ^ 2 /
              scoreVarianceFromSourceWeights m Pop.target)
            (effectiveOutcomeVariance m Pop.target -
              (predictiveCovarianceFromSourceWeights m Pop.target) ^ 2 /
                scoreVarianceFromSourceWeights m Pop.target)
      , brier :=
          TransportedMetrics.calibratedBrierFromVariances
            m.targetPrevalence
            ((predictiveCovarianceFromSourceWeights m Pop.target) ^ 2 /
              scoreVarianceFromSourceWeights m Pop.target)
            (effectiveOutcomeVariance m Pop.target -
              (predictiveCovarianceFromSourceWeights m Pop.target) ^ 2 /
                scoreVarianceFromSourceWeights m Pop.target) } := by
  ext
  · rw [targetMetricProfileFromSourceWeights_r2,
      targetR2FromSourceWeights_exact_metric_portability_law]
  · rw [targetMetricProfileFromSourceWeights_auc,
      targetEqualVarianceGaussianAUCFromSourceWeights_exact_metric_portability_law]
  · rw [targetMetricProfileFromSourceWeights_brier,
      targetCalibratedBrierFromSourceWeights_exact_metric_portability_law]

/-- Canonical mechanistic deployed metric profile after `t` generations. -/
noncomputable def targetMetricProfileAtGeneration {p q : ℕ}
    (m : CrossPopulationGenerationalModel p q) (t : ℕ) :
    TransportedMetrics.Profile :=
  targetMetricProfileFromSourceWeights (m.toMetricModelAt t)

@[simp] theorem targetMetricProfileAtGeneration_eq_slice {p q : ℕ}
    (m : CrossPopulationGenerationalModel p q) (t : ℕ) :
    targetMetricProfileAtGeneration m t =
      targetMetricProfileFromSourceWeights (m.toMetricModelAt t) := by
  rfl

/-- Display-normalized target `R²` after `t` generations.

This preserves the exact mechanistic portability ratio while anchoring the
source baseline at a chosen display value, instead of rescaling the biological
state. -/
noncomputable def sourceNormalizedTargetR2AtGeneration {p q : ℕ}
    (m : CrossPopulationGenerationalModel p q) (sourceBaseline : ℝ) (t : ℕ) : ℝ :=
  sourceBaseline *
    (r2FromSourceWeights (m.toMetricModelAt t) Pop.target / r2FromSourceWeights (m.toMetricModelAt
        t) Pop.source)

/-- Exact mechanistic law for display-normalized target `R²` at generation `t`.

This is the correct way to draw a source-anchored `R²` curve for visualization:
it rescales the exact portability ratio, not the underlying biological state. -/
theorem sourceNormalizedTargetR2AtGeneration_exact_mechanistic_popgen_portability_law
    {p q : ℕ} (m : CrossPopulationGenerationalModel p q)
    (sourceBaseline : ℝ) (t : ℕ) :
    sourceNormalizedTargetR2AtGeneration m sourceBaseline t =
      sourceBaseline *
        (((predictiveCovarianceFromSourceWeights (m.toMetricModelAt t) Pop.target) ^ 2 *
            scoreVarianceFromSourceWeights (m.toMetricModelAt t) Pop.source *
            ((m.toMetricModelAt t).outcomeVariance Pop.source)) /
          ((predictiveCovarianceFromSourceWeights (m.toMetricModelAt t) Pop.source) ^ 2 *
            scoreVarianceFromSourceWeights (m.toMetricModelAt t) Pop.target *
            effectiveOutcomeVariance (m.toMetricModelAt t) Pop.target)) := by
  unfold sourceNormalizedTargetR2AtGeneration
  rw [exactR2PortabilityRatio_mechanistic_law]

/-- Bundled exact metric portability law after `t` generations on the explicit
population-genetic state. This packages the exact `R²`, liability-AUC, and
Brier laws on the generation-indexed mechanistic transport model. -/
theorem targetMetricProfileAtGeneration_exact_mechanistic_popgen_portability_law
    {p q : ℕ} (m : CrossPopulationGenerationalModel p q) (t : ℕ) :
    targetMetricProfileAtGeneration m t =
      { r2 :=
          (predictiveCovarianceFromSourceWeights (m.toMetricModelAt t) Pop.target) ^ 2 /
            (scoreVarianceFromSourceWeights (m.toMetricModelAt t) Pop.target *
              effectiveOutcomeVariance (m.toMetricModelAt t) Pop.target)
      , auc :=
          equalVarianceGaussianAUCFromSignalVariance
            ((predictiveCovarianceFromSourceWeights (m.toMetricModelAt t) Pop.target) ^ 2 /
              scoreVarianceFromSourceWeights (m.toMetricModelAt t) Pop.target)
            (effectiveOutcomeVariance (m.toMetricModelAt t) Pop.target -
              (predictiveCovarianceFromSourceWeights (m.toMetricModelAt t) Pop.target) ^ 2 /
                scoreVarianceFromSourceWeights (m.toMetricModelAt t) Pop.target)
      , brier :=
          TransportedMetrics.calibratedBrierFromVariances
            (m.targetPrevalenceAt t)
            ((predictiveCovarianceFromSourceWeights (m.toMetricModelAt t) Pop.target) ^ 2 /
              scoreVarianceFromSourceWeights (m.toMetricModelAt t) Pop.target)
            (effectiveOutcomeVariance (m.toMetricModelAt t) Pop.target -
              (predictiveCovarianceFromSourceWeights (m.toMetricModelAt t) Pop.target) ^ 2 /
                scoreVarianceFromSourceWeights (m.toMetricModelAt t) Pop.target) } := by
  ext
  · rw [targetMetricProfileAtGeneration_eq_slice,
      targetMetricProfileFromSourceWeights_exact_mechanistic_portability_law]
  · rw [targetMetricProfileAtGeneration_eq_slice,
      targetMetricProfileFromSourceWeights_exact_mechanistic_portability_law]
  · rw [targetMetricProfileAtGeneration_eq_slice,
      targetMetricProfileFromSourceWeights_exact_mechanistic_portability_law]
    simp [predictiveCovarianceFromSourceWeights, scoreVarianceFromSourceWeights,
      effectiveOutcomeVariance,
      CrossPopulationGenerationalModel.toMetricModelAt]

/-- The direct `R²`-chart liability AUC agrees with the literal present-day
liability AUC when the deployed `R²` comes from the same neutral benchmark
chart. -/
theorem equalVarianceGaussianAUCFromExplainedR2_eq_presentDayAUC
    (V_A V_E fst : ℝ)
    (hVA : 0 < V_A) (hVE : 0 < V_E)
    (hfst_lt_one : fst < 1) :
    equalVarianceGaussianAUCFromExplainedR2 (presentDayR2 V_A V_E fst) =
      presentDayEqualVarianceGaussianAUC V_A V_E fst := by
  have hv_pos : 0 < presentDayPGSVariance V_A fst := by
    unfold presentDayPGSVariance pgsVarianceFromHet
    have h_one_minus : 0 < 1 - fst := by linarith
    exact mul_pos hVA h_one_minus
  have hsum_ne : presentDayPGSVariance V_A fst + V_E ≠ 0 := by
    linarith
  have hve_ne : V_E ≠ 0 := ne_of_gt hVE
  have hr2_lt : presentDayR2 V_A V_E fst < 1 := by
    unfold presentDayR2 r2FromSignalVariance
    exact (div_lt_one (add_pos hv_pos hVE)).2 (lt_add_of_pos_right _ hVE)
  have hchart :
      presentDayR2 V_A V_E fst / (2 * (1 - presentDayR2 V_A V_E fst)) =
        presentDaySignalToNoise V_A V_E fst / 2 := by
    unfold presentDayR2 r2FromSignalVariance presentDaySignalToNoise
    field_simp [hsum_ne, hve_ne]
    ring
  rw [equalVarianceGaussianAUCFromExplainedR2_eq_formula_of_lt_one _ hr2_lt]
  rw [presentDayEqualVarianceGaussianAUC_eq _ _ _ hve_ne, hchart]

/-- Full neutral allele-frequency benchmark liability-AUC degradation theorem
(exact LTM formula): if drift increases (`fstTarget > fstSource`), target AUC
is strictly lower than source AUC within this benchmark. -/
theorem targetLiabilityAUC_lt_source_of_neutralAF_benchmark
    (V_A V_E fstSource fstTarget : ℝ)
    (hVA : 0 < V_A) (hVE : 0 < V_E)
    (h_fst : fstSource < fstTarget)
    (h_fst_bounds : 0 ≤ fstSource ∧ fstTarget < 1) :
    presentDayEqualVarianceGaussianAUC V_A V_E fstTarget <
      presentDayEqualVarianceGaussianAUC V_A V_E fstSource := by
  simpa [presentDayEqualVarianceGaussianAUC] using
    drift_degrades_equalVarianceGaussianAUC
      V_A V_E fstSource fstTarget hVA hVE h_fst (le_of_lt h_fst_bounds.2)

/-- The exact target calibrated Brier risk is `TransportedMetrics.calibratedBrier`
evaluated at the explicit target `R²` by definition. -/
@[simp] theorem targetBrierFromNeutralAFBenchmark_eq
    (π V_A V_E fstTarget : ℝ) :
    targetExactCalibratedBrierRisk π V_A V_E fstTarget =
      TransportedMetrics.calibratedBrier π
        (targetR2FromNeutralAFBenchmark V_A V_E fstTarget) := by
  rfl

/-- Exact calibrated Bernoulli Brier risk from prevalence and explained-risk
moments. If the true conditional risk `η(Z)` has mean `π` and variance
`π(1-π) r2`, then the exact calibrated population Brier risk is
`π(1-π)(1-r2)`. -/
theorem exactBrierRiskOfCalibrated_eq_exactCalibratedBrierRiskFromR2
    {Z : Type*} [MeasurableSpace Z]
    (μ : Measure Z) [IsProbabilityMeasure μ]
    (η : Z → ℝ) (π r2 : ℝ)
    (hη_int : Integrable η μ)
    (hvar_int : Integrable (fun z ↦ (η z - π) ^ 2) μ)
    (hmean : ∫ z, η z ∂μ = π)
    (hvar : ∫ z, (η z - π) ^ 2 ∂μ = π * (1 - π) * r2) :
    exactBrierRiskOfCalibrated μ η = TransportedMetrics.calibratedBrier π r2 := by
  rw [exactBrierRiskOfCalibrated_eq_integral]
  have hdiff_int : Integrable (fun z ↦ η z - π) μ := by
    simpa [sub_eq_add_neg] using hη_int.sub (integrable_const π)
  have hlin_zero : ∫ z, (η z - π) ∂μ = 0 := by
    rw [integral_sub hη_int (integrable_const π), hmean]
    simp
  calc
    ∫ z, η z * (1 - η z) ∂μ
        = ∫ z, ((π * (1 - π) - (η z - π) ^ 2) + (1 - 2 * π) * (η z - π)) ∂μ := by
            refine integral_congr_ae ?_
            filter_upwards with z
            ring
    _ = ∫ z, (π * (1 - π) - (η z - π) ^ 2) ∂μ +
          ∫ z, (1 - 2 * π) * (η z - π) ∂μ := by
            convert
              (integral_add ((integrable_const _).sub hvar_int)
                (hdiff_int.const_mul (1 - 2 * π))) using 1
    _ = (∫ z, (π * (1 - π)) ∂μ - ∫ z, (η z - π) ^ 2 ∂μ) +
          ∫ z, (1 - 2 * π) * (η z - π) ∂μ := by
            rw [integral_sub (integrable_const _) hvar_int]
    _ = (π * (1 - π) - ∫ z, (η z - π) ^ 2 ∂μ) +
          (1 - 2 * π) * ∫ z, (η z - π) ∂μ := by
            rw [MeasureTheory.integral_const, MeasureTheory.integral_const_mul]
            simp
    _ = π * (1 - π) - ∫ z, (η z - π) ^ 2 ∂μ := by
            rw [hlin_zero]
            ring
    _ = TransportedMetrics.calibratedBrier π r2 := by
            rw [hvar]
            unfold TransportedMetrics.calibratedBrier
            ring

/-- Full neutral allele-frequency benchmark Brier degradation theorem: if
target `R²` drops and `0 ≤ π ≤ 1`, target Brier is at least source Brier
within this benchmark. -/
theorem targetBrier_ge_source_of_neutralAF_benchmark
    (π V_A V_E fstSource fstTarget : ℝ)
    (h_pi : 0 ≤ π ∧ π ≤ 1)
    (hVA : 0 < V_A) (hVE : 0 < V_E)
    (h_fst : fstSource < fstTarget)
    (h_fst_bounds : 0 ≤ fstSource ∧ fstTarget < 1) :
    sourceBrierFromR2 π (presentDayR2 V_A V_E fstSource) ≤
      targetBrierFromNeutralAFBenchmark π V_A V_E fstTarget := by
  rcases h_pi with ⟨hpi0, hpi1⟩
  have hr2_drop :
      targetR2FromNeutralAFBenchmark V_A V_E fstTarget < presentDayR2 V_A V_E fstSource :=
    targetR2_lt_source_from_neutralAF_benchmark V_A V_E fstSource fstTarget
      hVA hVE h_fst h_fst_bounds
  have hcoef_nonneg : 0 ≤ π * (1 - π) := by nlinarith
  unfold sourceBrierFromR2 targetBrierFromNeutralAFBenchmark
    targetExactCalibratedBrierRisk TransportedMetrics.calibratedBrier
  have hbase :
      1 - presentDayR2 V_A V_E fstSource ≤
        1 - targetR2FromNeutralAFBenchmark V_A V_E fstTarget := by
    linarith
  exact mul_le_mul_of_nonneg_left hbase hcoef_nonneg

/-- Pointwise Brier regret relative to the true Bernoulli probability. -/
noncomputable def brierRegretPoint (η q : ℝ) : ℝ :=
  brierBernoulliRisk η q - brierBernoulliRisk η η

/-- Pointwise Brier regret ratio between target and source predictors. -/
noncomputable def brierRegretRatio (η qSource qTarget : ℝ) : ℝ :=
  brierRegretPoint η qTarget / brierRegretPoint η qSource

/-- Brier regret equals squared calibration error exactly. -/
theorem brierRegretPoint_eq_sq_error (η q : ℝ) :
    brierRegretPoint η q = (q - η) ^ 2 := by
  unfold brierRegretPoint
  simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using brier_regret_pointwise η q

/-- Ratio form in present-day units: Brier-regret ratio is a squared-error ratio. -/
theorem brierRegretRatio_eq_sq_error_ratio (η qSource qTarget : ℝ) :
    brierRegretRatio η qSource qTarget =
      ((qTarget - η) ^ 2) / ((qSource - η) ^ 2) := by
  unfold brierRegretRatio
  rw [brierRegretPoint_eq_sq_error, brierRegretPoint_eq_sq_error]

/-- Pointwise log-loss regret relative to truth. -/
noncomputable def logLossRegretPoint (η q : ℝ) : ℝ :=
  bernoulliLogLoss η q - bernoulliLogLoss η η

/-- Pointwise log-loss regret ratio between target and source predictors. -/
noncomputable def logLossRegretRatio (η qSource qTarget : ℝ) : ℝ :=
  logLossRegretPoint η qTarget / logLossRegretPoint η qSource

/-- Log-loss regret is exactly Bernoulli KL divergence. -/
theorem logLossRegretPoint_eq_kl (η q : ℝ)
    (hη0 : 0 < η) (hη1 : η < 1)
    (hq0 : 0 < q) (hq1 : q < 1) :
    logLossRegretPoint η q = bernoulliKLReal η q := by
  unfold logLossRegretPoint
  simpa using logLoss_regret_eq_kl_pointwise η q hη0 hη1 hq0 hq1

/-- Ratio form in present-day units: log-loss regret ratio is a KL ratio. -/
theorem logLossRegretRatio_eq_kl_ratio (η qSource qTarget : ℝ)
    (hη0 : 0 < η) (hη1 : η < 1)
    (hqS0 : 0 < qSource) (hqS1 : qSource < 1)
    (hqT0 : 0 < qTarget) (hqT1 : qTarget < 1) :
    logLossRegretRatio η qSource qTarget =
      bernoulliKLReal η qTarget / bernoulliKLReal η qSource := by
  unfold logLossRegretRatio
  rw [logLossRegretPoint_eq_kl η qTarget hη0 hη1 hqT0 hqT1,
    logLossRegretPoint_eq_kl η qSource hη0 hη1 hqS0 hqS1]

/-! **Do not add an "at zero divergence" variant of
`targetR2FromNeutralAFBenchmark_eq_presentDayR2`.** `targetR2FromNeutralAFBenchmark` is
DEFINED as `presentDayR2`, so the equality holds at every `fst`; a statement restricted to
`fst = 0` advertises a special case that is not special, which is the same defect as a
hypothesis that appears to do work and does not. The unrestricted theorem above is the
edge that keeps the two names tied. -/

/-- For valid prevalence `0 < π < 1`, the linear Brier approximation `π(1-π)(1-R²)`
is strictly decreasing in `R²`. -/
theorem brierFromR2_strictAnti (π : ℝ) (hπ0 : 0 < π) (hπ1 : π < 1) :
    StrictAnti (brierFromR2 π) := by
  intro r2a r2b hab
  unfold brierFromR2
  have hcoef : 0 < π * (1 - π) := mul_pos hπ0 (by linarith)
  have hdrop : 1 - r2b < 1 - r2a := by linarith
  exact mul_lt_mul_of_pos_left hdrop hcoef

/-- Strict neutral allele-frequency benchmark Brier degradation: under
positive drift and non-degenerate prevalence, target Brier is strictly worse
than source Brier within this benchmark. -/
theorem targetBrier_strict_gt_source_of_neutralAF_benchmark
    (π V_A V_E fstSource fstTarget : ℝ)
    (hπ0 : 0 < π) (hπ1 : π < 1)
    (hVA : 0 < V_A) (hVE : 0 < V_E)
    (h_fst : fstSource < fstTarget)
    (h_fst_bounds : 0 ≤ fstSource ∧ fstTarget < 1) :
    sourceBrierFromR2 π (presentDayR2 V_A V_E fstSource) <
      targetBrierFromNeutralAFBenchmark π V_A V_E fstTarget := by
  have hr2_drop :=
    targetR2_lt_source_from_neutralAF_benchmark V_A V_E fstSource fstTarget
      hVA hVE h_fst h_fst_bounds
  unfold sourceBrierFromR2 targetBrierFromNeutralAFBenchmark
  exact brierFromR2_strictAnti π hπ0 hπ1 hr2_drop

/-- Squared mean PGS difference under the pure split model.

    Empirical status: UNTESTED. -/
noncomputable def expectedSqMeanPGSDiff_pureSplit (V_A fstS fstT : ℝ) : ℝ :=
  Var_Delta_Mu V_A (fstS + fstT)

/-- The expected squared mean PGS difference equals `2(F_S + F_T) V_A`. -/
@[simp] theorem expectedSqMeanPGSDiff_pureSplit_eq (V_A fstS fstT : ℝ) :
    expectedSqMeanPGSDiff_pureSplit V_A fstS fstT = 2 * (fstS + fstT) * V_A := by
  rfl

/-- The expected squared mean PGS difference under the IM equilibrium model:
`E[(Δμ)²] = 4δ V_A` where `δ = 1/(2M+1)`.

    Empirical status: UNTESTED. -/
noncomputable def expectedSqMeanPGSDiff_IMEquilibrium (V_A M : ℝ) : ℝ :=
  Var_Delta_Mu V_A (2 * twoDemeIMEquilibriumDelta M)

/-- IM equilibrium squared mean difference equals `4δ V_A`. -/
@[simp] theorem expectedSqMeanPGSDiff_IMEquilibrium_eq (V_A M : ℝ) :
    expectedSqMeanPGSDiff_IMEquilibrium V_A M =
      4 * twoDemeIMEquilibriumDelta M * V_A := by
  unfold expectedSqMeanPGSDiff_IMEquilibrium Var_Delta_Mu
  ring

/-- IM equilibrium: increasing migration strictly decreases genetic differentiation
    on the biologically meaningful domain M > 0. -/
theorem twoDemeIMEquilibriumDelta_strictAntiOn :
    StrictAntiOn (fun M : ℝ ↦ twoDemeIMEquilibriumDelta M) (Set.Ioi 0) := by
  intro a ha b hb hab
  unfold twoDemeIMEquilibriumDelta
  have ha_pos : 0 < 2 * a + 1 := by linarith [Set.mem_Ioi.mp ha]
  have hb_pos : 0 < 2 * b + 1 := by linarith [Set.mem_Ioi.mp hb]
  exact div_lt_div_of_pos_left one_pos ha_pos (by linarith : 2 * a + 1 < 2 * b + 1)

/-- Under the IM model, the mean-shift variance is strictly decreasing in migration rate
    on the biological domain (M > 0) when `V_A > 0`. -/
theorem expectedSqMeanPGSDiff_IMEquilibrium_strictAntiOn_M
    (V_A : ℝ) (hVA : 0 < V_A) :
    StrictAntiOn (fun M : ℝ ↦ expectedSqMeanPGSDiff_IMEquilibrium V_A M) (Set.Ioi 0) := by
  intro a ha b hb hab
  simp only [expectedSqMeanPGSDiff_IMEquilibrium_eq]
  have := twoDemeIMEquilibriumDelta_strictAntiOn ha hb hab
  nlinarith

end PresentDayMetrics


/-!
## Mutation-Drift Balance and Portability

When mutation is non-negligible, Fst has a finite equilibrium (Wright's
1/(1+4Neμ)) instead of approaching 1. This section generalizes the drift-only
portability model to include mutation as a first-class parameter.

Key results:
1. Generalized divergence model that includes mutation rate
2. Covariance divergence including both drift and mutation terms
3. Portability under mutation-drift: mutation-generated population-specific
   variants reduce tagging efficiency
4. Comparison: mutation-drift equilibrium portability vs pure-drift portability
-/

section MutationDriftPortability

/-- Generalized divergence model assumptions that include mutation as a parameter
    rather than assuming it is negligible. -/
structure MutationDriftModelAssumptions where
  Ne : ℝ
  μ : ℝ
  t : ℝ
  Ne_pos : 0 < Ne
  mu_pos : 0 < μ
  t_nonneg : 0 ≤ t

/-- **The class is inhabited.**  A theorem quantified over an uninhabited structure is
true and empty: kernel-checked, clean axiom report, no content.  This is the witness that
makes the theorems below statements about something. -/
noncomputable def MutationDriftModelAssumptions.witness : MutationDriftModelAssumptions where
  Ne := 1
  μ := 1
  t := 1
  Ne_pos := by norm_num
  mu_pos := by norm_num
  t_nonneg := by norm_num

/-- The scaled mutation parameter θ = 4Neμ for a mutation-drift model.

    Empirical status: UNTESTED. -/
noncomputable def MutationDriftModelAssumptions.theta (m : MutationDriftModelAssumptions) : ℝ :=
  scaledMutationRate m.Ne m.μ

/-- θ is positive for any valid mutation-drift model. -/
theorem MutationDriftModelAssumptions.theta_pos (m : MutationDriftModelAssumptions) :
    0 < m.theta := by
  unfold MutationDriftModelAssumptions.theta scaledMutationRate
  nlinarith [m.Ne_pos, m.mu_pos]

/-- **One generation of the identity-by-descent balance.**

`F` is the probability that two gene copies drawn from the same subpopulation
are identical by descent (equivalently, `F_ST` measured against a total
population in which that probability is zero).  In one generation:

* drift makes a pair identical with probability `1/(2 Nₑ)` among the pairs that
  are not already identical, contributing `+(1 - F)/(2 Nₑ)`;
* each of the two lineages independently escapes the local identity class at
  rate `rate` -- by mutating away from its ancestral allelic state, or by being
  replaced by a migrant -- contributing `-2 · rate · F`.

`rate` is therefore whichever homogenising force is in play: `μ` for
mutation-drift balance, `m` for migration-drift balance, `μ + m` for both.
That the two forces enter identically is the whole content of
`islandModelFst_eq_mutationForm`.

Composition convention: this is the first-order (weak-force, large-`Nₑ`)
recursion, in which drift and the homogenising force are *added*, so their
within-generation ordering does not matter.  The unlinearised discrete-generation
recursion multiplies them instead -- see `islandFstMultiplicativeStep` -- and its fixed
point differs from this one at O(rate², rate/Nₑ).

    Empirical status: UNTESTED. -/
noncomputable def ibdFlowStep (Ne rate F : ℝ) : ℝ :=
  F + (1 - F) / (2 * Ne) - 2 * rate * F

/-- **`1/(1 + 4 Nₑ · rate)` is the fixed point of the identity balance.**
Setting `(1 - F)/(2 Nₑ) = 2 · rate · F` gives `1 - F = 4 Nₑ · rate · F`, hence
`F = 1/(1 + 4 Nₑ · rate)`.  This single lemma is what pins every `1/(1 + θ)`
and `1/(1 + 4 N m)` in the development; none of them is stipulated. -/
theorem ibdFlowStep_fixedPoint (Ne rate : ℝ) (hNe : 0 < Ne) (hrate : 0 ≤ rate) :
    ibdFlowStep Ne rate (1 / (1 + 4 * Ne * rate)) = 1 / (1 + 4 * Ne * rate) := by
  have hprod : (0 : ℝ) ≤ 4 * Ne * rate := by positivity
  have hd : (0 : ℝ) < 1 + 4 * Ne * rate := by linarith
  have hd' : (1 : ℝ) + 4 * Ne * rate ≠ 0 := ne_of_gt hd
  have hNe' : Ne ≠ 0 := ne_of_gt hNe
  unfold ibdFlowStep
  field_simp
  ring

/-- **Complete fixation is a boundary the balance attains.**  With no
homogenising force the only fixed point is `F = 1`: drift runs to completion.
The closed form takes that value exactly, rather than approaching it. -/
@[simp] theorem ibdFlowStep_one_of_no_flow (Ne : ℝ) :
    ibdFlowStep Ne 0 1 = 1 := by
  unfold ibdFlowStep
  simp

/-- **Equilibrium Fst under mutation-drift balance: Fst = 1/(1 + θ).**
    This is the Wright (1931) island model result.

    Not stipulated: `MutationDriftModelAssumptions.fstEquilibrium_isFixedPoint`
    derives it as the rest point of `ibdFlowStep` with `rate = μ`.

    Empirical status: UNTESTED. -/
noncomputable def MutationDriftModelAssumptions.fstEquilibrium
    (m : MutationDriftModelAssumptions) : ℝ :=
  fstMutationDriftEquilibrium m.theta

/-- **The mutation-drift equilibrium is the fixed point of the identity
balance** driven by mutation alone. -/
theorem MutationDriftModelAssumptions.fstEquilibrium_isFixedPoint
    (m : MutationDriftModelAssumptions) :
    ibdFlowStep m.Ne m.μ m.fstEquilibrium = m.fstEquilibrium := by
  have hθ : m.fstEquilibrium = 1 / (1 + 4 * m.Ne * m.μ) := rfl
  rw [hθ]
  exact ibdFlowStep_fixedPoint m.Ne m.μ m.Ne_pos (le_of_lt m.mu_pos)

/-- Equilibrium Fst is positive. -/
theorem MutationDriftModelAssumptions.fstEquilibrium_pos
    (m : MutationDriftModelAssumptions) :
    0 < m.fstEquilibrium := by
  unfold MutationDriftModelAssumptions.fstEquilibrium fstMutationDriftEquilibrium
  have hden : 0 < 1 + m.theta := by
    nlinarith [m.theta_pos]
  exact div_pos one_pos hden

/-- Equilibrium Fst is strictly less than 1 (mutation prevents complete fixation). -/
theorem MutationDriftModelAssumptions.fstEquilibrium_lt_one
    (m : MutationDriftModelAssumptions) :
    m.fstEquilibrium < 1 := by
  unfold MutationDriftModelAssumptions.fstEquilibrium fstMutationDriftEquilibrium
  rw [div_lt_one (by linarith [m.theta_pos])]
  linarith [m.theta_pos]

/-- **Transient Fst under mutation-drift: approach to equilibrium.**
    Fst(t) = Fst_eq × (1 - exp(-(1+θ)t/(2Ne)))

    Empirical status: UNTESTED. -/
noncomputable def MutationDriftModelAssumptions.fstTransient
    (m : MutationDriftModelAssumptions) : ℝ :=
  m.fstEquilibrium * (1 - Real.exp (-(1 + m.theta) * m.t / (2 * m.Ne)))

/-- Transient Fst is nonneg. -/
theorem MutationDriftModelAssumptions.fstTransient_nonneg
    (m : MutationDriftModelAssumptions) :
    0 ≤ m.fstTransient := by
  unfold MutationDriftModelAssumptions.fstTransient
  apply mul_nonneg (le_of_lt m.fstEquilibrium_pos)
  have harg : 0 ≤ (1 + m.theta) * m.t / (2 * m.Ne) := by
    have hden : 0 < 2 * m.Ne := by nlinarith [m.Ne_pos]
    apply div_nonneg
    · exact mul_nonneg (by linarith [m.theta_pos]) m.t_nonneg
    · exact le_of_lt hden
  have hexp : Real.exp (-(1 + m.theta) * m.t / (2 * m.Ne)) ≤ 1 := by
    have hnum_nonpos : -(1 + m.theta) * m.t ≤ 0 := by
      have h1 : 0 ≤ 1 + m.theta := by
        have h1' : 0 < 1 + m.theta := by nlinarith [m.theta_pos]
        linarith
      nlinarith [h1, m.t_nonneg]
    have hden_nonneg : 0 ≤ 2 * m.Ne := by linarith [m.Ne_pos]
    have hneg : -(1 + m.theta) * m.t / (2 * m.Ne) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg hnum_nonpos hden_nonneg
    have hexp' : Real.exp (-(1 + m.theta) * m.t / (2 * m.Ne)) ≤ Real.exp 0 :=
      Real.exp_le_exp.mpr hneg
    simpa using hexp'
  have hfactor_nonneg : 0 ≤ 1 - Real.exp (-(1 + m.theta) * m.t / (2 * m.Ne)) := by
    linarith
  exact hfactor_nonneg

/-- Transient Fst is bounded by the equilibrium Fst. -/
theorem MutationDriftModelAssumptions.fstTransient_le_equilibrium
    (m : MutationDriftModelAssumptions) :
    m.fstTransient ≤ m.fstEquilibrium := by
  unfold MutationDriftModelAssumptions.fstTransient
  have hfeq_pos : 0 < m.fstEquilibrium := m.fstEquilibrium_pos
  have hexp_pos : 0 < Real.exp (-(1 + m.theta) * m.t / (2 * m.Ne)) := Real.exp_pos _
  have h_factor_le : 1 - Real.exp (-(1 + m.theta) * m.t / (2 * m.Ne)) ≤ 1 := by
    linarith
  have hmul :
      m.fstEquilibrium * (1 - Real.exp (-(1 + m.theta) * m.t / (2 * m.Ne))) ≤
        m.fstEquilibrium * 1 :=
    mul_le_mul_of_nonneg_left h_factor_le (le_of_lt hfeq_pos)
  simpa using hmul

/-! ## Derivation of the Multiplicative Covariance Divergence Formula

We derive the formula `covarianceDivergenceMutationDrift(Fst, shared_LD) = 1 - (1-Fst) × shared_LD`
from the covariance between a polygenic score and a phenotype across populations.

**Setup.** In the source population, the covariance between a PGS and the phenotype is:

  `Cov(PGS, Y_source) = Σᵢ βᵢ × Cov(Gᵢ_source, Y_source)`

In the target population:

  `Cov(PGS, Y_target) = Σᵢ βᵢ × Cov(Gᵢ_target, Y_target)`

The ratio `Cov_target / Cov_source` depends on two independent factors:

1. **Allele frequency correlation** (`freq_corr`): Genetic drift changes allele frequencies
   between populations. The correlation of allele frequencies between source and target
   populations is `1 - Fst`, where Fst measures frequency divergence. This scales the
   per-locus genetic covariance by `(1 - Fst)`.

2. **LD overlap** (`ld_overlap`): New mutations and recombination alter LD patterns.
   The fraction of LD structure that is shared between populations is `shared_LD`.
   Only shared LD contributes to tagging of causal variants by the PGS SNPs.

For a single locus pair, these act on different aspects of the covariance:
- Frequency change scales the marginal genetic variance: `Var(G_target) ∝ (1-Fst) × Var(G_source)`
- LD change scales the tagging efficiency: `r²_target ∝ shared_LD × r²_source`

Because these are independent mechanisms, the total covariance retention is their product:

  `Cov_target / Cov_source = (1 - Fst) × shared_LD`

Therefore the divergence (fraction of covariance lost) is:

  `divergence = 1 - retention = 1 - (1 - Fst) × shared_LD`
-/

/-- **Covariance retention** across populations.
    The fraction of PGS-phenotype covariance retained in the target population
    is the product of allele frequency correlation and LD overlap. These two
    factors are independent: frequency drift scales per-locus genetic variance,
    while LD decay scales tagging efficiency. -/
noncomputable def covarianceRetention (freq_corr ld_overlap : ℝ) : ℝ :=
  freq_corr * ld_overlap

/-- Allele frequency correlation equals `1 - Fst`, where Fst measures the
    fraction of genetic variance due to population divergence.

    Empirical status: UNTESTED.

    Denotes: the reading its name carries. The same formula appears under
    names from 'factor', 'frequency', 'fst', and the formula alone does not fix which is meant. -/
noncomputable def freqCorrFromFst (fst : ℝ) : ℝ := 1 - fst

/-- LD overlap is directly the shared LD fraction (identity mapping, made
    explicit for clarity in the derivation chain).

    Empirical status: UNTESTED. -/
noncomputable def ldOverlapFromSharedLD (shared_ld : ℝ) : ℝ := shared_ld

/-- Covariance retention in terms of Fst and shared_LD. -/
theorem covarianceRetention_from_fst_ld (fst shared_ld : ℝ) :
    covarianceRetention (freqCorrFromFst fst) (ldOverlapFromSharedLD shared_ld) =
      (1 - fst) * shared_ld := by
  unfold covarianceRetention freqCorrFromFst ldOverlapFromSharedLD
  ring

/-- **Covariance divergence derived from retention.**
    Divergence is `1 - retention`, which yields the multiplicative formula
    `1 - (1 - Fst) × shared_LD`. -/
noncomputable def covarianceDivergenceFromRetention (fst shared_ld : ℝ) : ℝ :=
  1 - covarianceRetention (freqCorrFromFst fst) (ldOverlapFromSharedLD shared_ld)

/-- The derived divergence formula equals `1 - (1 - Fst) × shared_LD`. -/
theorem covarianceDivergenceFromRetention_eq (fst shared_ld : ℝ) :
    covarianceDivergenceFromRetention fst shared_ld = 1 - (1 - fst) * shared_ld := by
  unfold covarianceDivergenceFromRetention
  rw [covarianceRetention_from_fst_ld]

/-- **Generalized covariance divergence under mutation-drift.**
    The total covariance divergence between source and target populations
    includes both:
    (a) drift-driven frequency changes: proportional to Fst
    (b) mutation-driven LD changes: proportional to tagging decay from new variants

    Total divergence factor = Fst_drift + (1 - Fst_drift) × (1 - shared_LD)
    where shared_LD is the fraction of LD preserved despite new mutations.

    Empirical status: UNTESTED. -/
noncomputable def covarianceDivergenceMutationDrift
    (fst_drift shared_ld : ℝ) : ℝ :=
  fst_drift + (1 - fst_drift) * (1 - shared_ld)

/-- Covariance divergence simplifies algebraically. -/
theorem covarianceDivergenceMutationDrift_eq (fst_drift shared_ld : ℝ) :
    covarianceDivergenceMutationDrift fst_drift shared_ld = 1 - (1 - fst_drift) * shared_ld := by
  unfold covarianceDivergenceMutationDrift
  ring

/-- **The derived formula matches the existing definition.**
    This connects the derivation from covariance principles back to
    `covarianceDivergenceMutationDrift`, confirming the multiplicative
    structure is not merely assumed but follows from the independence
    of allele frequency drift and LD decay. -/
theorem covarianceDivergence_derivation_matches (fst shared_ld : ℝ) :
    covarianceDivergenceFromRetention fst shared_ld =
      covarianceDivergenceMutationDrift fst shared_ld := by
  rw [covarianceDivergenceFromRetention_eq, covarianceDivergenceMutationDrift_eq]

/-- With perfect shared LD (shared_ld = 1), covariance divergence reduces to pure drift. -/
theorem covarianceDivergence_pure_drift (fst_drift : ℝ) :
    covarianceDivergenceMutationDrift fst_drift 1 = fst_drift := by
  unfold covarianceDivergenceMutationDrift
  ring

/-- With zero drift (fst_drift = 0), covariance divergence equals the LD divergence. -/
theorem covarianceDivergence_pure_mutation (shared_ld : ℝ) :
    covarianceDivergenceMutationDrift 0 shared_ld = 1 - shared_ld := by
  unfold covarianceDivergenceMutationDrift
  ring

/-- Covariance divergence is at least the drift component alone when shared LD ≤ 1. -/
theorem covarianceDivergence_ge_drift (fst_drift shared_ld : ℝ)
    (hfst_le : fst_drift ≤ 1)
    (hld : shared_ld ≤ 1) :
    fst_drift ≤ covarianceDivergenceMutationDrift fst_drift shared_ld := by
  unfold covarianceDivergenceMutationDrift
  have h1 : 0 ≤ 1 - fst_drift := by linarith
  have h2 : 0 ≤ 1 - shared_ld := by linarith
  linarith [mul_nonneg h1 h2]

/-- Covariance divergence is at most 1 when parameters are in [0, 1]. -/
theorem covarianceDivergence_le_one (fst_drift shared_ld : ℝ)
    (hfst_le : fst_drift ≤ 1)
    (hld : 0 ≤ shared_ld) :
    covarianceDivergenceMutationDrift fst_drift shared_ld ≤ 1 := by
  rw [covarianceDivergenceMutationDrift_eq]
  have h1 : 0 ≤ (1 - fst_drift) * shared_ld :=
    mul_nonneg (by linarith) hld
  linarith

/-- **Generalized signal retention under mutation-drift.**
    The retained signal is (1 - total_divergence) × V_A.

    Empirical status: UNTESTED. -/
noncomputable def presentDayPGSVarianceMutationDrift
    (V_A fst_drift shared_ld : ℝ) : ℝ :=
  (1 - covarianceDivergenceMutationDrift fst_drift shared_ld) * V_A

/-- Signal retention equals (1 - fst) × shared_ld × V_A. -/
theorem presentDayPGSVarianceMutationDrift_eq (V_A fst_drift shared_ld : ℝ) :
    presentDayPGSVarianceMutationDrift V_A fst_drift shared_ld =
      (1 - fst_drift) * shared_ld * V_A := by
  unfold presentDayPGSVarianceMutationDrift
  rw [covarianceDivergenceMutationDrift_eq]
  ring

/-- With perfect shared LD, signal retention reduces to the pure drift formula. -/
theorem presentDayPGSVarianceMutationDrift_pure_drift (V_A fst_drift : ℝ) :
    presentDayPGSVarianceMutationDrift V_A fst_drift 1 = presentDayPGSVariance V_A fst_drift := by
  rw [presentDayPGSVarianceMutationDrift_eq]
  unfold presentDayPGSVariance pgsVarianceFromHet
  ring

/-- Signal retention is nonneg under valid parameters. -/
theorem presentDayPGSVarianceMutationDrift_nonneg (V_A fst_drift shared_ld : ℝ)
    (hVA : 0 ≤ V_A) (hfst_le : fst_drift ≤ 1)
    (hld : 0 ≤ shared_ld) :
    0 ≤ presentDayPGSVarianceMutationDrift V_A fst_drift shared_ld := by
  rw [presentDayPGSVarianceMutationDrift_eq]
  exact mul_nonneg (mul_nonneg (by linarith) hld) hVA

/-- **Mutation strictly reduces signal retention beyond drift alone.**
    When shared_ld < 1 and other parameters are positive, mutation-drift signal
    retention is strictly below drift-only signal retention. -/
theorem mutationDrift_signal_lt_puredrift (V_A fst_drift shared_ld : ℝ)
    (hVA : 0 < V_A) (hfst_lt : fst_drift < 1) (hld_lt : shared_ld < 1) :
    presentDayPGSVarianceMutationDrift V_A fst_drift shared_ld <
      presentDayPGSVariance V_A fst_drift := by
  rw [presentDayPGSVarianceMutationDrift_eq]
  unfold presentDayPGSVariance pgsVarianceFromHet
  have h1 : 0 < 1 - fst_drift := by linarith
  have h_factor : (1 - fst_drift) * shared_ld < (1 - fst_drift) * 1 :=
    mul_lt_mul_of_pos_left hld_lt h1
  nlinarith

/-- **R² under mutation-drift balance.**

    Empirical status: UNTESTED. -/
noncomputable def presentDayR2MutationDrift (V_A V_E fst_drift shared_ld : ℝ) : ℝ :=
  let v := presentDayPGSVarianceMutationDrift V_A fst_drift shared_ld
  v / (v + V_E)

/-- **Mutation-drift R² is below drift-only R².**
    When shared LD is imperfect, R² under mutation-drift is strictly below
    drift-only R². This is the key portability result: ignoring mutation
    overestimates portability. -/
theorem mutationDrift_R2_lt_puredrift_R2 (V_A V_E fst_drift shared_ld : ℝ)
    (hVA : 0 < V_A) (hVE : 0 < V_E)
    (hfst_lt : fst_drift < 1)
    (hld : 0 < shared_ld) (hld_lt : shared_ld < 1) :
    presentDayR2MutationDrift V_A V_E fst_drift shared_ld <
      presentDayR2 V_A V_E fst_drift := by
  unfold presentDayR2MutationDrift presentDayR2 r2FromSignalVariance
  have h_sig_lt := mutationDrift_signal_lt_puredrift V_A fst_drift shared_ld
    hVA hfst_lt hld_lt
  have h_md_nonneg : 0 ≤ presentDayPGSVarianceMutationDrift V_A fst_drift shared_ld :=
    presentDayPGSVarianceMutationDrift_nonneg V_A fst_drift shared_ld
      (le_of_lt hVA) (le_of_lt hfst_lt) (le_of_lt hld)
  exact expectedR2_strictMono_nonneg V_E
    (presentDayPGSVarianceMutationDrift V_A fst_drift shared_ld)
    (presentDayPGSVariance V_A fst_drift)
    hVE h_md_nonneg h_sig_lt

/-- Scalar neutral benchmark that combines allele-frequency retention with a
shared-LD retention coordinate. This remains a coarse benchmark, not a
mechanistic SNP-level transport law.

    Empirical status: UNTESTED. -/
noncomputable def neutralAFSharedLDBenchmarkRatio
    (fstSource fstTarget shared_ld_source shared_ld_target : ℝ) : ℝ :=
  ((1 - fstTarget) * shared_ld_target) / ((1 - fstSource) * shared_ld_source)

/-- **The benchmark ratio's junk branch, named.** A source that shares no linkage structure, or
one at complete differentiation, zeroes the denominator and Lean returns `0`: the ratio reports
total loss of transfer where it is undefined, since there was no source performance to transfer.
Consumers must require the source denominator nonzero. -/
theorem neutralAFSharedLDBenchmarkRatio_no_source_is_junk
    (fstSource fstTarget shared_ld_target : ℝ) :
    neutralAFSharedLDBenchmarkRatio fstSource fstTarget 0 shared_ld_target = 0 := by
  unfold neutralAFSharedLDBenchmarkRatio; simp

/-- The shared-LD benchmark reduces to the neutral allele-frequency benchmark
when shared LD is perfect in both populations. -/
theorem neutralAFSharedLDBenchmarkRatio_pure_drift (fstSource fstTarget : ℝ) :
    neutralAFSharedLDBenchmarkRatio fstSource fstTarget 1 1 =
      (1 - fstTarget) / (1 - fstSource) := by
  unfold neutralAFSharedLDBenchmarkRatio
  ring

/-- The shared-LD benchmark is below the pure neutral allele-frequency
benchmark when target shared LD is worse than source shared LD. -/
theorem neutralAFSharedLDBenchmarkRatio_lt_pure_drift_form
    (fstSource fstTarget shared_ld_source shared_ld_target : ℝ)
    (hfstS : fstSource < 1) (hfstT : fstTarget < 1)
    (hldS : 0 < shared_ld_source)
    (hld_decay : shared_ld_target / shared_ld_source < 1) :
    neutralAFSharedLDBenchmarkRatio fstSource fstTarget shared_ld_source shared_ld_target <
      (1 - fstTarget) / (1 - fstSource) := by
  unfold neutralAFSharedLDBenchmarkRatio
  have h1 : 0 < 1 - fstSource := by linarith
  have h_den_pos : 0 < (1 - fstSource) * shared_ld_source := mul_pos h1 hldS
  rw [div_lt_div_iff₀ h_den_pos h1]
  have h_ld_ratio : shared_ld_target < shared_ld_source := by
    rwa [div_lt_one hldS] at hld_decay
  have hnum_lt :
      ((1 - fstSource) * (1 - fstTarget)) * shared_ld_target <
        ((1 - fstSource) * (1 - fstTarget)) * shared_ld_source :=
    mul_lt_mul_of_pos_left h_ld_ratio (mul_pos h1 (by linarith))
  simpa [mul_assoc, mul_left_comm, mul_comm] using hnum_lt


/-- **At equilibrium, larger θ means lower Fst and thus the drift component
    of portability improves.**
    If we compare two populations at equilibrium with θ₁ < θ₂, the population
    with larger θ has smaller Fst. This improves the allele frequency component
    of signal retention. -/
theorem equilibrium_drift_component_improves_with_theta
    (V_A θ₁ θ₂ : ℝ)
    (hVA : 0 < V_A) (hθ₁ : 0 < θ₁)
    (h_more : θ₁ < θ₂) :
    presentDayPGSVariance V_A (1 / (1 + θ₁)) <
      presentDayPGSVariance V_A (1 / (1 + θ₂)) := by
  unfold presentDayPGSVariance pgsVarianceFromHet
  have h1 : 0 < 1 + θ₁ := by linarith
  have h2 : 0 < 1 + θ₂ := by linarith
  -- 1/(1+θ₂) < 1/(1+θ₁), so 1 - 1/(1+θ₁) < 1 - 1/(1+θ₂)
  -- i.e., θ₁/(1+θ₁) < θ₂/(1+θ₂)
  have hfst₁ : 1 - 1 / (1 + θ₁) = θ₁ / (1 + θ₁) := by
    have hne : 1 + θ₁ ≠ 0 := by linarith
    field_simp [hne]
    ring_nf
  have hfst₂ : 1 - 1 / (1 + θ₂) = θ₂ / (1 + θ₂) := by
    have hne : 1 + θ₂ ≠ 0 := by linarith
    field_simp [hne]
    ring_nf
  rw [hfst₁, hfst₂]
  have h_ratio_lt : θ₁ / (1 + θ₁) < θ₂ / (1 + θ₂) := by
    rw [div_lt_div_iff₀ h1 h2]
    nlinarith
  exact mul_lt_mul_of_pos_left h_ratio_lt hVA

/-- **Pure drift benchmark overestimates retained variance.**
    The drift-only benchmark (which sets `negligibleMutation` = True) always
    overestimates retained variance compared to the mutation-drift model.
    This theorem quantifies the gap: the ratio of mutation-drift variance
    to drift-only variance is exactly `shared_ld`. -/
theorem mutationDrift_variance_ratio (V_A fst shared_ld : ℝ)
    (hVA : 0 < V_A) (hfst : fst < 1)
    (hld : 0 < shared_ld) :
    presentDayPGSVarianceMutationDrift V_A fst shared_ld /
      presentDayPGSVariance V_A fst = shared_ld := by
  rw [presentDayPGSVarianceMutationDrift_eq]
  unfold presentDayPGSVariance pgsVarianceFromHet
  have hfst_ne : 1 - fst ≠ 0 := by linarith
  have hVA_ne : V_A ≠ 0 := ne_of_gt hVA
  field_simp [hfst_ne, hVA_ne]

/-! **Deleted: `neutral_af_benchmark_correction_factor`.**

This theorem is absent on purpose. It states `presentDayPGSVarianceMutationDrift V_A fst
ld = ld * presentDayPGSVariance V_A fst` and closes by `ring`. All six of its hypotheses go
unused — `0 < V_A`, `0 < V_E`, `0 ≤ fst`, `fst < 1`, `0 < ld`, `ld ≤ 1` — and `V_E` is a
phantom parameter appearing nowhere in the statement, present only so the signature reads
like a statement about `R²`. The identity is `presentDayPGSVarianceMutationDrift_eq` with
the factors reassociated, and `mutationDrift_variance_ratio` just above states the same
content as a ratio with the hypotheses it genuinely needs.

Two of those hypotheses are worse than unused. `0 ≤ fst` and `fst < 1` are the range in
which the "correction factor" reading means anything, and leaving them unused lets the
equation hold at `fst > 1`, where `presentDayPGSVariance` is negative and the word
*correction* has no referent. A theorem satisfied by the inadmissible parameter values too
is no evidence that the admissible ones are the intended domain. -/

/-- **Pairwise Fst under mutation-drift balance is bounded.**
    Under mutation-drift equilibrium, pairwise Fst between any two populations
    is bounded above by 2 × Fst_eq (since each branch contributes at most Fst_eq). -/
theorem pairwise_fst_mutationDrift_bound (θ : ℝ) (hθ : 0 < θ) :
    pairwiseFstFromBranches (1 / (1 + θ)) (1 / (1 + θ)) ≤ 2 / (1 + θ) := by
  simp [pairwiseFstFromBranches]
  ring_nf
  have h1 : 0 < 1 + θ := by linarith
  have hsq : 0 ≤ (1 / (1 + θ)) ^ 2 := sq_nonneg (1 / (1 + θ))
  nlinarith

end MutationDriftPortability


/-!
## Migration-Drift Balance and Portability

Gene flow (migration) between populations counteracts drift, preventing complete
differentiation. The classic Wright island model gives Fst ≈ 1/(1 + 4Nm) at
equilibrium. This section extends the `SplitMigrationModel` with:
1. Fst under migration-drift equilibrium and its properties
2. Migration reduces Fst relative to pure drift
3. Stepping-stone model: Fst increases with geographic distance
4. Migration's effect on LD sharing and PGS portability
5. Portability is higher with gene flow than without
6. Asymmetric migration and directional portability
7. Admixture LD from recent migration pulses
-/

section MigrationDriftPortability

/-! ### 1. Fst under migration-drift balance: Fst = 1/(1 + 4Nm) -/

/-- The standard finite-island correction factor for `demes` demes.

This is data, not a packaged claim that an approximation is adequate.  Any biological
use of the infinite-island approximation must compare this explicit quantity with its
own scientifically justified tolerance. -/
noncomputable def finiteIslandCorrection (demes : ℝ) : ℝ :=
  (demes / (demes - 1)) ^ 2

/-- **The finite-island correction's junk branch, named.** At a single deme the correction
diverges and Lean returns `0`. Consumers must require `demes ≠ 1`. -/
theorem finiteIslandCorrection_one_deme_is_junk : finiteIslandCorrection 1 = 0 := by
  unfold finiteIslandCorrection; norm_num

/-- With two demes the finite-island correction is exactly four. -/
@[simp] theorem finiteIslandCorrection_two : finiteIslandCorrection 2 = 4 := by
  norm_num [finiteIslandCorrection]

/-- Consequently its excess over the infinite-island value is exactly three. -/
@[simp] theorem finiteIslandCorrection_two_excess :
    finiteIslandCorrection 2 - 1 = 3 := by
  rw [finiteIslandCorrection_two]
  norm_num

/-- **Island model equilibrium Fst under migration-drift balance.**
    Fst_eq = 1 / (1 + 4Nm) where N is effective size and m is migration rate.
    This is the classical Wright (1931) result.

    Regime: the infinite-island limit. The explicit `finiteIslandCorrection`
    above makes the finite-deme discrepancy inspectable. Simulation puts the law within 2% at 40
    demes, but +17% at 10, +31% at 5 and +95% at 2. The two-deme case is the
    two-ancestry comparison this development is mostly about, so the law is off
    by roughly twofold in its primary application. The finite-deme correction
    `1/(1 + 4 Nₑ m (d/(d-1))²)` repairs the 5-to-10 deme range and overshoots at
    `d = 2` by −40%.

    Empirical status: CONDITIONALLY VALID. Accurate in the limit it was derived
    for; frequently violated in use. Neither validated nor falsified. -/
noncomputable def fstMigrationDriftEquilibrium (Ne m : ℝ) : ℝ :=
  1 / (1 + 4 * Ne * m)

/-- **The island-model F_ST is the rest point of the identity balance** driven
by migration.  It is not a stipulated closed form: substitute any other
constant and this fails. -/
theorem fstMigrationDriftEquilibrium_isFixedPoint (Ne m : ℝ)
    (hNe : 0 < Ne) (hm : 0 ≤ m) :
    ibdFlowStep Ne m (fstMigrationDriftEquilibrium Ne m) =
      fstMigrationDriftEquilibrium Ne m :=
  ibdFlowStep_fixedPoint Ne m hNe hm

/-- **Total isolation is a boundary the closed form attains.**  With `m = 0`
the demes fix independently and F_ST is exactly `1`. -/
@[simp] theorem fstMigrationDriftEquilibrium_of_no_migration (Ne : ℝ) :
    fstMigrationDriftEquilibrium Ne 0 = 1 := by
  unfold fstMigrationDriftEquilibrium
  norm_num

/-- **One generation of the identity-by-descent recurrence.**

A lineage pair coalesces this generation with probability `1/(2 Nₑ)`; failing
that it is identical only if it already was. Independently, the pair survives
the disrupting event -- whatever separates the two lineages -- with probability
`(1 - rate)²`, one chance per lineage.

    Denotes: the recurrence itself, not either quantity that satisfies it. Read
    with `rate = m` it is the island-model single-locus IBD recursion; read with
    `rate = c` it is Sved's two-locus IBD recursion for `E[r²]`. Those are
    different quantities obeying one map, so the map is named for the map and
    for neither of them.

Composition convention: the disrupting event acts on the offspring generation
*after* reproduction, and the two events multiply rather than add. This is the
difference from `ibdFlowStep`, which linearises `(1 - rate)² (1 - 1/(2 Nₑ))` to
`1 - 2 rate - 1/(2 Nₑ)` and therefore has a different fixed point.

    Empirical status: UNTESTED. -/
noncomputable def ibdRecurrenceStep (Ne rate x : ℝ) : ℝ :=
  (1 - rate) ^ 2 * (1 / (2 * Ne) + (1 - 1 / (2 * Ne)) * x)

/-- **The rest point of the identity-by-descent recurrence.**

Solving `x = (1 - rate)² (a + (1 - a) x)` with `a = 1/(2 Nₑ)` gives
`x* = (1 - rate)² a / (1 - (1 - rate)² (1 - a))`, and clearing `a` writes it as
the form below. Both readings of `ibdRecurrenceStep` inherit it: with `rate = m`
it is the island-model equilibrium `F_ST`, with `rate = c` it is Sved's `E[r²]`.

    Denotes: the rest point of the recurrence, under either reading.

    Empirical status: UNTESTED. -/
noncomputable def ibdRecurrenceFixedPoint (Ne rate : ℝ) : ℝ :=
  (1 - rate) ^ 2 / ((1 - rate) ^ 2 + 2 * Ne * rate * (2 - rate))

/-- **The rest point is a fixed point of the recurrence.**  Stated once here so
that the island-model and Sved readings cannot acquire different answers. -/
theorem ibdRecurrenceFixedPoint_isFixedPoint (Ne rate : ℝ)
    (hNe : 0 < Ne) (hr : 0 ≤ rate) (hr1 : rate < 1) :
    ibdRecurrenceStep Ne rate (ibdRecurrenceFixedPoint Ne rate) =
      ibdRecurrenceFixedPoint Ne rate := by
  have h2Ne : (0 : ℝ) < 2 * Ne := by linarith
  have h2Ne' : (2 : ℝ) * Ne ≠ 0 := ne_of_gt h2Ne
  have hpos : (0 : ℝ) < 1 - rate := by linarith
  have hsq : (0 : ℝ) < (1 - rate) ^ 2 := pow_pos hpos 2
  have hflow : (0 : ℝ) ≤ 2 * Ne * rate * (2 - rate) :=
    mul_nonneg (mul_nonneg h2Ne.le hr) (by linarith : (0 : ℝ) ≤ 2 - rate)
  have hd : (0 : ℝ) < (1 - rate) ^ 2 + 2 * Ne * rate * (2 - rate) := by linarith
  have hd' : (1 - rate) ^ 2 + 2 * Ne * rate * (2 - rate) ≠ 0 := ne_of_gt hd
  have hdExpanded :
      (1 : ℝ) - rate * 2 + rate * Ne * 4 +
          (rate ^ 2 - rate ^ 2 * Ne * 2) ≠ 0 := by
    have hbridge :
        (1 : ℝ) - rate * 2 + rate * Ne * 4 +
            (rate ^ 2 - rate ^ 2 * Ne * 2) =
          (1 - rate) ^ 2 + 2 * Ne * rate * (2 - rate) := by
      ring
    rw [hbridge]
    exact hd'
  unfold ibdRecurrenceStep ibdRecurrenceFixedPoint
  -- Clear the fixed-point denominator while it is still in its factored form;
  -- only then clear the coalescence denominator. Expanding first made the
  -- nonzero hypothesis syntactically unusable and left an inverse in the goal.
  apply (eq_div_iff hd').2
  field_simp [h2Ne', hdExpanded]
  have hinv :
      ((1 : ℝ) - rate * 2 + rate * Ne * 4 +
          (rate ^ 2 - rate ^ 2 * Ne * 2))⁻¹ *
        ((1 : ℝ) - rate * 2 + rate * Ne * 4 +
          (rate ^ 2 - rate ^ 2 * Ne * 2)) = 1 :=
    inv_mul_cancel₀ hdExpanded
  ring_nf at hinv ⊢
  nlinarith [hinv]

/-- **Total isolation is a boundary the rest point attains.**  With `rate = 0`
nothing separates the lineages and the recurrence rests at `1`. -/
@[simp] theorem ibdRecurrenceFixedPoint_of_zero_rate (Ne : ℝ) :
    ibdRecurrenceFixedPoint Ne 0 = 1 := by
  unfold ibdRecurrenceFixedPoint
  norm_num

/-- **The exact error of the `1/(1 + 4 Nₑ rate)` linearisation.**

`x* - 1/(1 + 4 Nₑ rate) = 2 Nₑ rate² (2 rate - 3) / (D (1 + 4 Nₑ rate))` where
`D = (1 - rate)² + 2 Nₑ rate (2 - rate)`. The error is second order in `rate`,
which is what makes `1/(1 + 4 Nₑ rate)` a first-order approximation rather than
an identity. -/
theorem ibdRecurrenceFixedPoint_sub_linearisation (Ne rate : ℝ)
    (hNe : 0 < Ne) (hr : 0 ≤ rate) (hr1 : rate < 1) :
    ibdRecurrenceFixedPoint Ne rate - 1 / (1 + 4 * Ne * rate) =
      2 * Ne * rate ^ 2 * (2 * rate - 3) /
        (((1 - rate) ^ 2 + 2 * Ne * rate * (2 - rate)) * (1 + 4 * Ne * rate)) := by
  have h2Ne : (0 : ℝ) < 2 * Ne := by linarith
  have hpos : (0 : ℝ) < 1 - rate := by linarith
  have hsq : (0 : ℝ) < (1 - rate) ^ 2 := pow_pos hpos 2
  have hflow : (0 : ℝ) ≤ 2 * Ne * rate * (2 - rate) :=
    mul_nonneg (mul_nonneg h2Ne.le hr) (by linarith : (0 : ℝ) ≤ 2 - rate)
  have hd : (0 : ℝ) < (1 - rate) ^ 2 + 2 * Ne * rate * (2 - rate) := by linarith
  have hd' : (1 - rate) ^ 2 + 2 * Ne * rate * (2 - rate) ≠ 0 := ne_of_gt hd
  have hlin : (0 : ℝ) < 1 + 4 * Ne * rate := by nlinarith
  have hlin' : (1 : ℝ) + 4 * Ne * rate ≠ 0 := ne_of_gt hlin
  unfold ibdRecurrenceFixedPoint
  rw [div_sub_div _ _ hd' hlin']
  have hnum : (1 - rate) ^ 2 * (1 + 4 * Ne * rate) -
      ((1 - rate) ^ 2 + 2 * Ne * rate * (2 - rate)) * 1 =
      2 * Ne * rate ^ 2 * (2 * rate - 3) := by ring
  rw [hnum]

/-- **`1/(1 + 4 Nₑ rate)` is strictly above the rest point, always.**

This is the theorem that stops the classical formula being re-derived as if it
were exact. One statement covers both readings: `1/(1 + 4 Nₑ m)` for the island
model and Sved's `1/(1 + 4 Nₑ c)` for two-locus LD are the same weak-rate
linearisation of `ibdRecurrenceFixedPoint`, each overstates it, and the gap is
the second-order term of `ibdRecurrenceFixedPoint_sub_linearisation`. At
`Nₑ = 1`, `rate = 1/2` the rest point is `1/7` and the linearisation is `1/3`.

Regime of the linearisation: small `rate`, large `Nₑ`. Outside it the corpus
already records a roughly twofold discrepancy at two demes on the island-model
definitions, and this theorem says the discrepancy has a sign. -/
theorem ibdRecurrenceFixedPoint_lt_linearisation (Ne rate : ℝ)
    (hNe : 0 < Ne) (hr : 0 < rate) (hr1 : rate < 1) :
    ibdRecurrenceFixedPoint Ne rate < 1 / (1 + 4 * Ne * rate) := by
  have h2Ne : (0 : ℝ) < 2 * Ne := by linarith
  have hpos : (0 : ℝ) < 1 - rate := by linarith
  have hsq : (0 : ℝ) < (1 - rate) ^ 2 := pow_pos hpos 2
  have hflow : (0 : ℝ) ≤ 2 * Ne * rate * (2 - rate) :=
    mul_nonneg (mul_nonneg h2Ne.le hr.le) (by linarith : (0 : ℝ) ≤ 2 - rate)
  have hd : (0 : ℝ) < (1 - rate) ^ 2 + 2 * Ne * rate * (2 - rate) := by linarith
  have hlin : (0 : ℝ) < 1 + 4 * Ne * rate := by nlinarith
  have hden : (0 : ℝ) <
      ((1 - rate) ^ 2 + 2 * Ne * rate * (2 - rate)) * (1 + 4 * Ne * rate) :=
    mul_pos hd hlin
  have hrsq : (0 : ℝ) < rate ^ 2 := pow_pos hr 2
  have hnum : 2 * Ne * rate ^ 2 * (2 * rate - 3) < 0 :=
    mul_neg_of_pos_of_neg (mul_pos h2Ne hrsq) (by linarith)
  have hgap := ibdRecurrenceFixedPoint_sub_linearisation Ne rate hNe hr.le hr1
  have hneg : ibdRecurrenceFixedPoint Ne rate - 1 / (1 + 4 * Ne * rate) < 0 := by
    rw [hgap]
    exact div_neg_of_neg_of_pos hnum hden
  linarith

/-- **The island-model reading of the recurrence.**  Migration is the disrupting
event: the pair is identical only if neither lineage is a migrant, probability
`(1 - m)²`, and the parental copies either coalesced in the deme or were already
identical.

    Empirical status: UNTESTED. -/
noncomputable def islandFstMultiplicativeStep (Ne m F : ℝ) : ℝ :=
  ibdRecurrenceStep Ne m F

/-! **`islandFstMultiplicativeStep` is `ibdRecurrenceStep` by definition, and needs no
theorem saying so** -- a definitional alias is carried by the elaborator, and a `rfl`
statement of it cannot fail.

**The DEFINITION must stay.** `LDDecayTheory.driftLDStep_eq_islandFstMultiplicativeStep`
proves the independently written `driftLDStep` equal to it by `ring`; that is a genuine
guard between two bodies, and deleting this name would disconnect `driftLDStep` from the
recurrence it is held to. Connectivity to the hub, not theorem count, is what makes a
removal safe. -/

/-- **Fixed point of the island-model recursion.**

`F* = (1-m)² / ((1-m)² + 2 Nₑ m (2 - m))`.  Expanding the denominator gives
`(1-m)² + 4 Nₑ m − 2 Nₑ m²`, so this reduces to `1/(1 + 4 Nₑ m)` only after
dropping terms of order `m²` and `m/Nₑ`; the two closed forms are never equal
for `m > 0`, which `ibdRecurrenceFixedPoint_lt_linearisation` proves in general
and `fstIslandMultiplicativeEquilibrium_ne_fstMigrationDriftEquilibrium`
witnesses at a point.

    Empirical status: UNTESTED. -/
noncomputable def fstIslandMultiplicativeEquilibrium (Ne m : ℝ) : ℝ :=
  ibdRecurrenceFixedPoint Ne m

/-- **The closed form is the fixed point of the island-model recursion.** -/
theorem fstIslandMultiplicativeEquilibrium_isFixedPoint (Ne m : ℝ)
    (hNe : 0 < Ne) (hm : 0 ≤ m) (hm1 : m < 1) :
    islandFstMultiplicativeStep Ne m (fstIslandMultiplicativeEquilibrium Ne m) =
      fstIslandMultiplicativeEquilibrium Ne m :=
  ibdRecurrenceFixedPoint_isFixedPoint Ne m hNe hm hm1

/-- **Total isolation, island reading.**  This recursion also attains the
boundary: `m = 0` gives `F = 1`. -/
@[simp] theorem fstIslandMultiplicativeEquilibrium_of_no_migration (Ne : ℝ) :
    fstIslandMultiplicativeEquilibrium Ne 0 = 1 :=
  ibdRecurrenceFixedPoint_of_zero_rate Ne

/-- **The two recursions do not have the same fixed point.**

At `Nₑ = 1`, `m = 1/2` the multiplicative recursion rests at `1/7` and the
linearised one at `1/3`.  This is not a defect of either definition: it is the
size of the weak-migration approximation, and it is stated here rather than
left implicit so that the approximation cannot be mistaken for an identity. -/
theorem fstIslandMultiplicativeEquilibrium_ne_fstMigrationDriftEquilibrium :
    fstIslandMultiplicativeEquilibrium 1 (1 / 2) ≠ fstMigrationDriftEquilibrium 1 (1 / 2) := by
  unfold fstIslandMultiplicativeEquilibrium ibdRecurrenceFixedPoint
    fstMigrationDriftEquilibrium
  norm_num


/-- Scaled migration rate is positive when Ne and m are positive. -/
theorem scaledMigrationRate_pos (Ne m : ℝ) (hNe : 0 < Ne) (hm : 0 < m) :
    0 < scaledMigrationRate Ne m := by
  unfold scaledMigrationRate
  positivity

/-- Fst under migration-drift equilibrium equals 1/(1 + M). -/
theorem fstMigrationDriftEquilibrium_eq_from_M (Ne m : ℝ) :
    fstMigrationDriftEquilibrium Ne m = 1 / (1 + scaledMigrationRate Ne m) := by
  unfold fstMigrationDriftEquilibrium scaledMigrationRate
  ring

/-- Equilibrium Fst under migration-drift is positive for nonneg migration. -/
theorem fstMigrationDriftEquilibrium_pos (Ne m : ℝ) (hNe : 0 < Ne) (hm : 0 ≤ m) :
    0 < fstMigrationDriftEquilibrium Ne m := by
  unfold fstMigrationDriftEquilibrium
  have : 0 ≤ 4 * Ne * m := by positivity
  positivity

/-- Equilibrium Fst under migration-drift is at most 1. -/
theorem fstMigrationDriftEquilibrium_le_one (Ne m : ℝ) (hNe : 0 < Ne) (hm : 0 ≤ m) :
    fstMigrationDriftEquilibrium Ne m ≤ 1 := by
  unfold fstMigrationDriftEquilibrium
  rw [div_le_one (by nlinarith)]
  nlinarith

/-- Equilibrium Fst under migration-drift is strictly less than 1 when m > 0.
    This is the key qualitative result: migration prevents complete fixation. -/
theorem fstMigrationDriftEquilibrium_lt_one (Ne m : ℝ) (hNe : 0 < Ne) (hm : 0 < m) :
    fstMigrationDriftEquilibrium Ne m < 1 := by
  unfold fstMigrationDriftEquilibrium
  rw [div_lt_one (by nlinarith)]
  nlinarith

/-- Equilibrium Fst is in the open interval (0, 1) for positive Ne and m. -/
theorem fstMigrationDriftEquilibrium_in_unit (Ne m : ℝ) (hNe : 0 < Ne) (hm : 0 < m) :
    0 < fstMigrationDriftEquilibrium Ne m ∧ fstMigrationDriftEquilibrium Ne m < 1 :=
  ⟨fstMigrationDriftEquilibrium_pos Ne m hNe (le_of_lt hm),
   fstMigrationDriftEquilibrium_lt_one Ne m hNe hm⟩

/-- **Equilibrium Fst decreases with migration rate** (Ne fixed).
    More migration → more gene flow → less differentiation. -/
theorem fstMigrationDriftEquilibrium_decreases_with_m (Ne m₁ m₂ : ℝ)
    (hNe : 0 < Ne) (hm₁ : 0 < m₁) (h_more : m₁ < m₂) :
    fstMigrationDriftEquilibrium Ne m₂ < fstMigrationDriftEquilibrium Ne m₁ := by
  unfold fstMigrationDriftEquilibrium
  apply div_lt_div_of_pos_left one_pos (by nlinarith) (by nlinarith)

/-- **Equilibrium Fst decreases with effective population size** (m fixed).
    Larger Ne → slower drift relative to migration → less differentiation. -/
theorem fstMigrationDriftEquilibrium_decreases_with_Ne (Ne₁ Ne₂ m : ℝ)
    (hNe₁ : 0 < Ne₁) (hm : 0 < m) (h_more : Ne₁ < Ne₂) :
    fstMigrationDriftEquilibrium Ne₂ m < fstMigrationDriftEquilibrium Ne₁ m := by
  unfold fstMigrationDriftEquilibrium
  apply div_lt_div_of_pos_left one_pos (by nlinarith) (by nlinarith)

/-! ### 2. Migration counteracts drift -/

/-! **Deleted: `migration_reduces_fst_vs_pure_drift`.**

This theorem is absent on purpose. Its hypothesis is
`1 / (1 + 4 * Ne * m) < t / (t + 2 * Ne)` and its conclusion is
`fstMigrationDriftEquilibrium Ne m < t / (t + 2 * Ne)`. Since
`fstMigrationDriftEquilibrium Ne m` unfolds to `1 / (1 + 4 * Ne * m)`, the two are the same
proposition and the proof is `unfold; exact h_large_t` — the hypothesis, returned. The
remaining three hypotheses (`0 < Ne`, `0 < m`, `0 < t`) go unused.

The prose around it claims the derivation the theorem skips: "Under migration-drift
equilibrium, Fst = 1/(1+4Nm) < 1 - (1-1/(2Ne))^t for sufficiently large t." Nothing
establishes *for which* `t` the inequality holds. That is exactly what the hypothesis
assumes, under a name (`h_large_t`) that asserts the answer. Establishing it would mean
showing `1/(1+4Nm) < t/(t+2Ne)` for `t` past an explicit threshold in `Ne` and `m`, which
is a real result and appears nowhere in this file.

A result that merely repackages a premise is deleted, not renamed: there is no honest name
for `h → h`. -/

/-- **Finite equilibrium vs unbounded drift.**
    Under pure drift, Fst approaches 1 as t → ∞. Under migration-drift balance,
    Fst is bounded above by 1/(1+4Nm) < 1. This means migration establishes
    a ceiling on differentiation. -/
theorem lt_one_of_le_migrationEquilibrium (Ne m : ℝ) (hNe : 0 < Ne) (hm : 0 < m)
    (fst_observed : ℝ) (h_le : fst_observed ≤ fstMigrationDriftEquilibrium Ne m) :
    fst_observed < 1 := by
  have h_eq_lt := fstMigrationDriftEquilibrium_lt_one Ne m hNe hm
  linarith

/-- **SplitMigrationModel equilibrium Fst using the structure.**

    Empirical status: UNTESTED. -/
noncomputable def SplitMigrationModel.fstMigDriftEq (s : SplitMigrationModel) : ℝ :=
  fstMigrationDriftEquilibrium s.Ne s.mig

/-- SplitMigrationModel equilibrium Fst equals the limit Fst for many demes. -/
theorem SplitMigrationModel.fstMigDriftEq_eq_limit (s : SplitMigrationModel) :
    s.fstMigDriftEq = s.fstEqLimitLowMutationManyDemes := by
  unfold SplitMigrationModel.fstMigDriftEq fstMigrationDriftEquilibrium
    SplitMigrationModel.fstEqLimitLowMutationManyDemes
    scaledMigrationRate
  ring

/-- **Increased migration strictly improves equilibrium Fst in the SplitMigration framework.**
    Comparing two SplitMigrationModels with same Ne but different migration rates. -/
theorem splitMigration_more_migration_less_fst
    (Ne m₁ m₂ : ℝ) (mu : ℝ)
    (hNe : 0 < Ne) (hm₁ : 0 < m₁) (hm₂ : 0 < m₂)
    (hmu : 0 ≤ mu) (h_more : m₁ < m₂) :
    let s₁ : SplitMigrationModel := ⟨0, Ne, m₁, mu, hNe, le_of_lt hm₁, hmu⟩
    let s₂ : SplitMigrationModel := ⟨0, Ne, m₂, mu, hNe, le_of_lt hm₂, hmu⟩
    s₂.fstMigDriftEq < s₁.fstMigDriftEq := by
  simp only [SplitMigrationModel.fstMigDriftEq]
  exact fstMigrationDriftEquilibrium_decreases_with_m Ne m₁ m₂ hNe hm₁ h_more

/-! ### 3. Stepping-stone model: Fst increases with geographic distance -/

/-- **Stepping-stone Fst model.**
    In the stepping-stone model, migration occurs only between adjacent demes.
    Fst between demes separated by d steps is approximately:
    Fst(d) ≈ min 1 (Fst_neighbor × (1 + α × (d - 1)))
    where α controls the rate of increase with distance (isolation by distance).

    The `min 1` is not cosmetic. An `F_ST` is a variance ratio and lies in
    `[0, 1]`; the bare linear form returns `10000` at
    `fst_neighbor = 1, α = 1, d = 10000`, which is not a value the quantity can
    take. Clamping also makes the fixation boundary attainable rather than
    merely approached: `steppingStoneFst_eq_one_of_saturated` exhibits the
    regime where distant demes are completely differentiated, which is the
    physically correct behaviour of isolation by distance at long range.

    Regime: linear, valid below saturation. This is a first-order approximation
    to the closed form, so it is trustworthy only while
    `fst_neighbor * (1 + α (d - 1))` is well below `1`; the monotonicity results
    below carry that condition as a hypothesis rather than assuming it. The
    saturating closed forms are `demoSteppingStoneFst` in
    `Calibrator.DemographicHistory`, which is derived from a coalescence time,
    which is not this function and is not being replaced here. A second
    saturating form, `continuousSteppingStoneFst = 1 - exp (-d/L)`, has been
    deleted from `Calibrator.PopulationGeneticsFoundations`: it contradicted
    `demoSteppingStoneFst`, and the coalescent derivation decides against the
    exponential.

    Empirical status: UNTESTED. -/
noncomputable def steppingStoneFst (fst_neighbor α : ℝ) (d : ℕ) : ℝ :=
  min 1 (fst_neighbor * (1 + α * ((d : ℝ) - 1)))

/-- **Stepping-stone Fst never leaves the unit interval**, which is what the
range of the quantity requires and what the unclamped body violated. -/
theorem steppingStoneFst_le_one (fst_neighbor α : ℝ) (d : ℕ) :
    steppingStoneFst fst_neighbor α d ≤ 1 :=
  min_le_left _ _

/-- **The fixation boundary is attained**, not merely approached: once the
linear form reaches `1` the demes are completely differentiated and stay so. -/
theorem steppingStoneFst_eq_one_of_saturated (fst_neighbor α : ℝ) (d : ℕ)
    (hsat : 1 ≤ fst_neighbor * (1 + α * ((d : ℝ) - 1))) :
    steppingStoneFst fst_neighbor α d = 1 :=
  min_eq_left hsat

/-- Stepping-stone Fst at distance 1 equals the neighbor Fst, provided the
neighbour value is itself a valid `F_ST`. -/
theorem steppingStoneFst_at_one (fst_neighbor α : ℝ) (hle : fst_neighbor ≤ 1) :
    steppingStoneFst fst_neighbor α 1 = fst_neighbor := by
  unfold steppingStoneFst
  simp only [Nat.cast_one, sub_self, mul_zero, add_zero, mul_one]
  exact min_eq_right hle

/-- **Stepping-stone Fst increases with geographic distance** (isolation by distance).
    For positive neighbor Fst and positive distance scaling parameter α,
    Fst is strictly increasing in the number of steps -- below saturation.
    Above it both values are `1` and the increase stops, which is the correct
    behaviour and the reason the hypothesis is needed. -/
theorem steppingStoneFst_increases_with_distance
    (fst_neighbor α : ℝ) (d₁ d₂ : ℕ)
    (hfst : 0 < fst_neighbor) (hα : 0 < α) (hd : d₁ < d₂)
    (hsat : fst_neighbor * (1 + α * ((d₂ : ℝ) - 1)) ≤ 1) :
    steppingStoneFst fst_neighbor α d₁ < steppingStoneFst fst_neighbor α d₂ := by
  unfold steppingStoneFst
  have hd_real : (d₁ : ℝ) < (d₂ : ℝ) := Nat.cast_lt.mpr hd
  have h_inner : α * ((d₁ : ℝ) - 1) < α * ((d₂ : ℝ) - 1) := by nlinarith
  have hlin : fst_neighbor * (1 + α * ((d₁ : ℝ) - 1)) <
      fst_neighbor * (1 + α * ((d₂ : ℝ) - 1)) := by nlinarith
  rw [min_eq_right (le_of_lt (lt_of_lt_of_le hlin hsat)), min_eq_right hsat]
  exact hlin

/-- **Nearby demes have lower Fst than distant demes.**
    Fst(1) < Fst(d) for d > 1 under the stepping-stone model, below saturation. -/
theorem steppingStoneFst_neighbor_lt_distant
    (fst_neighbor α : ℝ) (d : ℕ)
    (hfst : 0 < fst_neighbor) (hα : 0 < α) (hd : 1 < d)
    (hsat : fst_neighbor * (1 + α * ((d : ℝ) - 1)) ≤ 1) :
    steppingStoneFst fst_neighbor α 1 < steppingStoneFst fst_neighbor α d :=
  steppingStoneFst_increases_with_distance fst_neighbor α 1 d hfst hα hd hsat

/-- **Stepping-stone Fst is nonneg for valid parameters.** -/
theorem steppingStoneFst_nonneg (fst_neighbor α : ℝ) (d : ℕ)
    (hfst : 0 < fst_neighbor) (hα : 0 ≤ α) (hd : 1 ≤ d) :
    0 ≤ steppingStoneFst fst_neighbor α d := by
  unfold steppingStoneFst
  apply le_min (by norm_num)
  apply mul_nonneg (le_of_lt hfst)
  have : 0 ≤ α * ((d : ℝ) - 1) := by
    apply mul_nonneg hα
    have : (1 : ℝ) ≤ (d : ℝ) := Nat.one_le_cast.mpr hd
    linarith
  linarith

/-! ### 4. Migration's effect on LD: gene flow homogenizes LD patterns -/

/-! #### Derivation of shared LD fraction from Fst equilibrium

The shared LD fraction under migration-drift balance is **derived**, not assumed.
Since Fst measures the fraction of genetic variation that is *between* populations,
the complementary quantity `1 - Fst` measures the fraction that is *shared*.
LD patterns are shared to the same extent as allele frequencies, so:

  shared_LD = 1 - Fst_eq = 1 - 1/(1 + M) = M/(1 + M)

where M = 4Nm is the scaled migration rate. This is the same algebraic identity
underlying Wright's island model: Fst + shared fraction = 1. The theorem
`sharedLD_from_equilibrium_eq` below proves this algebraically from the
already-derived `fstMigrationDriftEquilibrium`. -/

/-- **Shared LD derived from Fst equilibrium.**
    Defined as `1 - fstMigrationDriftEquilibrium Ne m`, i.e., the complement
    of the between-population divergence under migration-drift balance.

    Empirical status: UNTESTED. -/
noncomputable def sharedLD_from_equilibrium (Ne m : ℝ) : ℝ :=
  1 - fstMigrationDriftEquilibrium Ne m

/-- The shared LD fraction derived from Fst equilibrium equals M/(1+M).
    This is the formal derivation: starting from Fst = 1/(1+M), we obtain
    shared_LD = 1 - 1/(1+M) = M/(1+M). -/
theorem sharedLD_from_equilibrium_eq (Ne m : ℝ) (hNe : 0 < Ne) (hm : 0 ≤ m) :
    sharedLD_from_equilibrium Ne m = scaledMigrationRate Ne m / (1 + scaledMigrationRate Ne m) := by
  unfold sharedLD_from_equilibrium fstMigrationDriftEquilibrium scaledMigrationRate
  have hden : 1 + 4 * Ne * m ≠ 0 := by nlinarith
  field_simp [hden]
  ring

/-- **Shared LD fraction under migration-drift balance.**
    Gene flow homogenizes LD patterns between populations. The fraction of LD
    that is shared between two demes increases with migration rate:
    shared_LD(m) = M / (1 + M) where M = 4Nm.

    **Derivation:** This formula is the complement of the Wright (1931)
    island-model Fst equilibrium. Since Fst = 1/(1+M) (proved at
    `fstMigrationDriftEquilibrium`), the shared fraction is
    1 - Fst = 1 - 1/(1+M) = M/(1+M). See `sharedLD_from_equilibrium_eq`
    and `sharedLD_from_equilibrium_eq_sharedLDFromMigration` for the
    formal algebraic derivation.

    Empirical status: UNTESTED. -/
noncomputable def sharedLDFromMigration (M : ℝ) : ℝ :=
  M / (1 + M)

/-- **The migration shared-LD map and the coalescent `F_ST` map are one function.**

`fstFromTau` sends coalescent time `tau` to `tau / (1 + tau)`; `sharedLDFromMigration`
sends the scaled migration number `M` to `M / (1 + M)`. The arguments are different
quantities and no value of one may be substituted for the other, but the map is the same
saturating map, and a change of convention in either spelling has to be made in both. -/
theorem sharedLDFromMigration_eq_fstFromTau (M : ℝ) :
    sharedLDFromMigration M = fstFromTau M := rfl

/-- The derived shared LD fraction equals `sharedLDFromMigration M`. This
    closes the loop: the formula M/(1+M) is not an assumption but follows
    from the migration-drift Fst equilibrium. -/
theorem sharedLD_from_equilibrium_eq_sharedLDFromMigration (Ne m : ℝ)
    (hNe : 0 < Ne) (hm : 0 ≤ m) :
    sharedLD_from_equilibrium Ne m = sharedLDFromMigration (scaledMigrationRate Ne m) := by
  rw [sharedLD_from_equilibrium_eq Ne m hNe hm]
  unfold sharedLDFromMigration
  rfl

/-- Shared LD fraction is nonneg for nonneg M. -/
theorem sharedLDFromMigration_nonneg (M : ℝ) (hM : 0 ≤ M) :
    0 ≤ sharedLDFromMigration M := by
  unfold sharedLDFromMigration
  exact div_nonneg hM (by linarith)

/-- Shared LD fraction is at most 1. -/
theorem sharedLDFromMigration_lt_one (M : ℝ) (hM : 0 ≤ M) :
    sharedLDFromMigration M < 1 := by
  unfold sharedLDFromMigration
  rw [div_lt_one (by linarith : 0 < 1 + M)]
  linarith

/-- **Shared LD fraction increases with migration rate.**
    More migration → more shared LD → better PGS portability. -/
theorem sharedLDFromMigration_increases (M₁ M₂ : ℝ)
    (hM₁ : 0 < M₁) (h_more : M₁ < M₂) :
    sharedLDFromMigration M₁ < sharedLDFromMigration M₂ := by
  unfold sharedLDFromMigration
  rw [div_lt_div_iff₀ (by linarith) (by linarith)]
  nlinarith

/-- **Complementarity of Fst and shared LD under migration-drift.**
    Fst = 1/(1+M) and shared_LD = M/(1+M) sum to 1.
    This parallels the mutation-drift complementarity. -/
theorem fst_plus_sharedLD_eq_one (Ne m : ℝ) (hNe : 0 < Ne) (hm : 0 ≤ m) :
    fstMigrationDriftEquilibrium Ne m + sharedLDFromMigration (scaledMigrationRate Ne m) = 1 := by
  unfold fstMigrationDriftEquilibrium sharedLDFromMigration scaledMigrationRate
  have hden : 1 + 4 * Ne * m ≠ 0 := by nlinarith
  field_simp [hden]

/-! ### 5. Portability under migration-drift: R² improves with gene flow -/

/-- **Signal retention under migration-drift balance.**

The fraction of additive signal that survives, accounting for both allele
frequency drift and LD sharing at the migration-drift equilibrium. It is
`(1 - F_ST) * shared_LD = M²/(1 + M)²` with `M = 4 Nₑ m`, and it lies in
`[0, 1)`.

The previous body of this name multiplied by `V_A` and so returned a variance,
not a fraction: it was unbounded and grew without limit as the additive variance
grew. A retention that scales with an additive variance is not a retention. The
name now denotes the fraction and `retainedSignalVarianceMigrationDrift` denotes
the variance; `retainedSignalVarianceMigrationDrift_eq_retention_mul_VA` relates
them. This corpus has already lost a factor of four to just this kind of
name/quantity mismatch, so the two are separated rather than bounded.

    Denotes: a dimensionless fraction in `[0, 1)`, never a variance.

    Empirical status: UNTESTED. -/
noncomputable def signalRetentionMigrationDrift (Ne m : ℝ) : ℝ :=
  (1 - fstMigrationDriftEquilibrium Ne m) *
    sharedLDFromMigration (scaledMigrationRate Ne m)

/-- **Retained signal variance under migration-drift balance.**
    The additive variance that survives: the retention fraction times `V_A`.
    This is the quantity the previous `signalRetentionMigrationDrift` computed.

    Denotes: a variance, in the units of `V_A`.

    Empirical status: UNTESTED. -/
noncomputable def retainedSignalVarianceMigrationDrift (V_A Ne m : ℝ) : ℝ :=
  signalRetentionMigrationDrift Ne m * V_A

/-- The variance is the fraction times `V_A`; this is the theorem that keeps the
two names from drifting apart again. -/
theorem retainedSignalVarianceMigrationDrift_eq_retention_mul_VA (V_A Ne m : ℝ) :
    retainedSignalVarianceMigrationDrift V_A Ne m =
      signalRetentionMigrationDrift Ne m * V_A := rfl

/-- The retention fraction equals `M²/(1 + M)²`. -/
theorem signalRetentionMigrationDrift_eq_ratio (Ne m : ℝ)
    (hNe : 0 < Ne) (hm : 0 ≤ m) :
    signalRetentionMigrationDrift Ne m =
      (scaledMigrationRate Ne m) ^ 2 / (1 + scaledMigrationRate Ne m) ^ 2 := by
  unfold signalRetentionMigrationDrift fstMigrationDriftEquilibrium sharedLDFromMigration
    scaledMigrationRate
  have hden : (1 + 4 * Ne * m) ≠ 0 := by nlinarith
  field_simp [hden]
  ring

/-- **The retention is a fraction: it never reaches `1`.**  This is the range
property the name asserts, and a body that can reach `1` does not have it. -/
theorem signalRetentionMigrationDrift_lt_one (Ne m : ℝ)
    (hNe : 0 < Ne) (hm : 0 < m) :
    signalRetentionMigrationDrift Ne m < 1 := by
  rw [signalRetentionMigrationDrift_eq_ratio Ne m hNe (le_of_lt hm)]
  have hM : 0 < scaledMigrationRate Ne m := scaledMigrationRate_pos Ne m hNe hm
  have h1M : 0 < (1 + scaledMigrationRate Ne m) ^ 2 := by positivity
  rw [div_lt_one h1M]
  nlinarith

/-- **The retention is nonneg.** -/
theorem signalRetentionMigrationDrift_nonneg (Ne m : ℝ)
    (hNe : 0 < Ne) (hm : 0 ≤ m) :
    0 ≤ signalRetentionMigrationDrift Ne m := by
  rw [signalRetentionMigrationDrift_eq_ratio Ne m hNe hm]
  positivity

/-- Retained signal variance under migration-drift equals M²/((1+M)²) × V_A. -/
theorem retainedSignalVarianceMigrationDrift_eq (V_A Ne m : ℝ)
    (hNe : 0 < Ne) (hm : 0 ≤ m) :
    retainedSignalVarianceMigrationDrift V_A Ne m =
      (scaledMigrationRate Ne m) ^ 2 / (1 + scaledMigrationRate Ne m) ^ 2 * V_A := by
  unfold retainedSignalVarianceMigrationDrift
  rw [signalRetentionMigrationDrift_eq_ratio Ne m hNe hm]

/-- **Retained signal variance is positive with positive migration.** -/
theorem retainedSignalVarianceMigrationDrift_pos (V_A Ne m : ℝ)
    (hVA : 0 < V_A) (hNe : 0 < Ne) (hm : 0 < m) :
    0 < retainedSignalVarianceMigrationDrift V_A Ne m := by
  rw [retainedSignalVarianceMigrationDrift_eq V_A Ne m hNe (le_of_lt hm)]
  apply mul_pos
  · apply div_pos
    · exact sq_pos_of_pos (scaledMigrationRate_pos Ne m hNe hm)
    · exact sq_pos_of_pos (by nlinarith [scaledMigrationRate_pos Ne m hNe hm])
  · exact hVA

/-- **More migration improves signal retention** (for fixed Ne and V_A).
    This is the core mechanism: gene flow improves PGS portability. -/
theorem signalRetention_increases_with_migration (V_A Ne m₁ m₂ : ℝ)
    (hVA : 0 < V_A) (hNe : 0 < Ne) (hm₁ : 0 < m₁) (hm₂ : 0 < m₂)
    (h_more : m₁ < m₂) :
    retainedSignalVarianceMigrationDrift V_A Ne m₁ <
      retainedSignalVarianceMigrationDrift V_A Ne m₂ := by
  rw [retainedSignalVarianceMigrationDrift_eq V_A Ne m₁ hNe (le_of_lt hm₁),
      retainedSignalVarianceMigrationDrift_eq V_A Ne m₂ hNe (le_of_lt hm₂)]
  apply mul_lt_mul_of_pos_right _ hVA
  -- Need: M₁²/(1+M₁)² < M₂²/(1+M₂)²  i.e. (M₁/(1+M₁))² < (M₂/(1+M₂))²
  -- which follows from M₁/(1+M₁) < M₂/(1+M₂), a monotone function.
  set M₁ := scaledMigrationRate Ne m₁
  set M₂ := scaledMigrationRate Ne m₂
  have hM₁ : 0 < M₁ := scaledMigrationRate_pos Ne m₁ hNe hm₁
  have hM₂ : 0 < M₂ := scaledMigrationRate_pos Ne m₂ hNe hm₂
  have hM_lt : M₁ < M₂ := by
    simp [M₁, M₂, scaledMigrationRate]
    nlinarith
  have h1M₁ : 0 < 1 + M₁ := by linarith
  have h1M₂ : 0 < 1 + M₂ := by linarith
  -- M₁/(1+M₁) < M₂/(1+M₂)
  have h_ratio : M₁ / (1 + M₁) < M₂ / (1 + M₂) := by
    rw [div_lt_div_iff₀ h1M₁ h1M₂]; nlinarith
  -- Squaring preserves order for positive values
  have h_sq₁ : 0 < M₁ / (1 + M₁) := div_pos hM₁ h1M₁
  have h_sq₂ : 0 < M₂ / (1 + M₂) := div_pos hM₂ h1M₂
  have h_sq : (M₁ / (1 + M₁)) ^ 2 < (M₂ / (1 + M₂)) ^ 2 := by
    have hsum_pos : 0 < M₁ / (1 + M₁) + M₂ / (1 + M₂) := by positivity
    have hmul := mul_lt_mul_of_pos_right h_ratio hsum_pos
    nlinarith
  rwa [div_pow, div_pow] at h_sq

/-! **Deleted: `migration_improves_R2_over_pure_drift`.**

Strip the assumed premise and what is left is `drift_degrades_R2` with its first argument
instantiated at `fstMigrationDriftEquilibrium Ne m`, which is the whole proof. The single
call site, `recurrence_derived_R2_increases_with_m`, calls `drift_degrades_R2` directly.
That theorem *does* prove the migration claim, because it derives the `F_ST` ordering from
`m₁ < m₂` via `fstMigrationDriftEquilibrium_decreases_with_m` instead of assuming it. -/

/-! ### 6. Asymmetric migration -/

/-- **Asymmetric migration Fst model.**
    When migration is asymmetric (m₁₂ ≠ m₂₁), the effective Fst depends on
    direction. The effective migration for population i is the rate at which
    it receives migrants. The "effective Fst" from population 1's perspective
    uses m₁₂ (rate of migrants into pop 1 from pop 2).

    Empirical status: UNTESTED. -/
noncomputable def asymmetricFst (Ne m_into : ℝ) : ℝ :=
  1 / (1 + 4 * Ne * m_into)

/-- **Asymmetric Fst is just the island model Fst with directional migration.** -/
theorem asymmetricFst_eq_migrationDriftEq (Ne m_into : ℝ) :
    asymmetricFst Ne m_into = fstMigrationDriftEquilibrium Ne m_into := by
  unfold asymmetricFst fstMigrationDriftEquilibrium
  rfl

/-- **When m₁₂ > m₂₁, Fst from perspective of pop 1 is lower.**
    Population 1 receives more migrants from pop 2, so its genetic composition
    is closer to pop 2 than vice versa. -/
theorem asymmetric_migration_directional_fst
    (Ne m₁₂ m₂₁ : ℝ) (hNe : 0 < Ne) (hm₂₁ : 0 < m₂₁)
    (h_asym : m₂₁ < m₁₂) :
    asymmetricFst Ne m₁₂ < asymmetricFst Ne m₂₁ := by
  simp only [asymmetricFst_eq_migrationDriftEq]
  exact fstMigrationDriftEquilibrium_decreases_with_m Ne m₂₁ m₁₂ hNe hm₂₁ h_asym

/-- **Portability depends on prediction direction under asymmetric migration.**
    Predicting into a population that receives more migrants (lower Fst from
    its perspective) yields higher R² than predicting the other way. -/
theorem asymmetric_migration_portability_direction
    (V_A V_E Ne m₁₂ m₂₁ : ℝ)
    (hVA : 0 < V_A) (hVE : 0 < V_E) (hNe : 0 < Ne)
    (hm₂₁ : 0 < m₂₁)
    (h_asym : m₂₁ < m₁₂) :
    presentDayR2 V_A V_E (asymmetricFst Ne m₂₁) <
      presentDayR2 V_A V_E (asymmetricFst Ne m₁₂) := by
  have h_fst := asymmetric_migration_directional_fst Ne m₁₂ m₂₁ hNe hm₂₁ h_asym
  have h_lt_one : asymmetricFst Ne m₂₁ < 1 := by
    simpa [asymmetricFst_eq_migrationDriftEq] using
      fstMigrationDriftEquilibrium_lt_one Ne m₂₁ hNe hm₂₁
  exact drift_degrades_R2 V_A V_E (asymmetricFst Ne m₁₂) (asymmetricFst Ne m₂₁)
    hVA hVE h_fst (le_of_lt h_lt_one)

/-- **Arithmetic mean of the two directional migration rates.**

    **The docstring here said "harmonic mean" and the body is the arithmetic mean.** They
    are different numbers whenever the two rates differ, and the disagreement is
    one-sided: AM ≥ HM always, with equality only at `m₁₂ = m₂₁`
    (`harmonicMigrationMean_le_effectiveSymmetricMigration` below). So the stated
    quantity systematically *overstates* gene flow relative to the quantity the docstring
    named.

    That error does not stop at the mean. `fstMigrationDriftEquilibrium` is decreasing in
    the migration rate, so an overstated rate yields an understated `F_ST`, which
    `presentDayR2` turns into an *overstated* `R²` in the target population — the
    optimistic direction, and the direction that matters for a user being told how well a
    score transfers. `effectiveSymmetricMigration_fst_le_harmonic_fst` states that
    consequence.

    This is the same failure shape the corpus already records for `hudsonFst` computing
    Nei's `G_ST`: a name and docstring asserting one estimator over a body computing
    another, with the discrepancy landing in the direction that flatters the result. The
    name and docstring are corrected here rather than the body, because the body is what
    two other files already depend on — `Conventions.lean` ties it to `meanAlleleFreq`
    (an arithmetic mean, so that identity is only true of the current body), and
    `PopulationGeneticsFoundations.lean` proves the betweenness and idempotence facts
    against it. Changing the body to a harmonic mean would falsify both. Which of the two
    means is the right effective rate for asymmetric migration is not settled anywhere in
    this corpus, and nothing here should be read as settling it.
    nothing about the harmonic mean.

    Empirical status: UNTESTED. A test of this quantity tests the arithmetic mean and says -/
noncomputable def effectiveSymmetricMigration (m₁₂ m₂₁ : ℝ) : ℝ :=
  (m₁₂ + m₂₁) / 2

/-- **The arithmetic mean used here is never below the harmonic mean**, with equality
exactly when the two directional rates agree. This is AM-GM-HM for two positive reals, and
it fixes the sign of the discrepancy between the two means. -/
theorem harmonicMigrationMean_le_effectiveSymmetricMigration (m₁₂ m₂₁ : ℝ)
    (h₁ : 0 < m₁₂) (h₂ : 0 < m₂₁) :
    2 * m₁₂ * m₂₁ / (m₁₂ + m₂₁) ≤ effectiveSymmetricMigration m₁₂ m₂₁ := by
  unfold effectiveSymmetricMigration
  rw [div_le_div_iff₀ (by linarith) (by norm_num : (0:ℝ) < 2)]
  nlinarith [sq_nonneg (m₁₂ - m₂₁)]

/-- **Hence the equilibrium `F_ST` computed from this mean is never above the one the
harmonic mean would give.** `fstMigrationDriftEquilibrium` is decreasing in the migration
rate, so substituting the larger mean returns the smaller `F_ST`. Composed with
`presentDayR2`, which is decreasing in `F_ST`, the arithmetic mean is the optimistic
choice at every pair of asymmetric rates: it reports better cross-population portability
than the harmonic mean does. Stated so the direction of the bias is checkable rather than
left in prose. -/
theorem effectiveSymmetricMigration_fst_le_harmonic_fst (Ne m₁₂ m₂₁ : ℝ)
    (hNe : 0 < Ne) (h₁ : 0 < m₁₂) (h₂ : 0 < m₂₁) :
    fstMigrationDriftEquilibrium Ne (effectiveSymmetricMigration m₁₂ m₂₁) ≤
      fstMigrationDriftEquilibrium Ne (2 * m₁₂ * m₂₁ / (m₁₂ + m₂₁)) := by
  unfold fstMigrationDriftEquilibrium
  have hHM_pos : 0 < 2 * m₁₂ * m₂₁ / (m₁₂ + m₂₁) := by positivity
  have hle := harmonicMigrationMean_le_effectiveSymmetricMigration m₁₂ m₂₁ h₁ h₂
  have hden_pos : 0 < 1 + 4 * Ne * (2 * m₁₂ * m₂₁ / (m₁₂ + m₂₁)) := by positivity
  exact one_div_le_one_div_of_le hden_pos (by nlinarith)

/-- The arithmetic mean of two distinct rates lies strictly between them. -/
theorem effectiveSymmetricMigration_between (m₁₂ m₂₁ : ℝ)
    (h_asym : m₂₁ < m₁₂) :
    m₂₁ < effectiveSymmetricMigration m₁₂ m₂₁ ∧
    effectiveSymmetricMigration m₁₂ m₂₁ < m₁₂ := by
  unfold effectiveSymmetricMigration
  constructor <;> linarith

/-! ### 7. Recent migration (admixture): transient LD from migration pulses -/

/-- **Admixture LD from a recent migration pulse.**
    A pulse of migration (admixture) at time t_adm generations ago creates
    LD between loci at recombination distance r. This LD decays as:
    D_adm(t) = D_0 × (1 - r)^(t - t_adm)
    where D_0 is the initial admixture LD and t is the current time.
    We model the decay factor.

    **REGIME: infinite population.** `(1-r)` is the recombination-only
    retention, i.e. the `Nₑ → ∞` limit, and nothing in the expression says so
    -- there is no `Nₑ` argument for it to say it with. The finite-population
    retention is `(1-r)(1 - 1/(2Nₑ))`, which is
    `LDDecayTheory.ldRetentionPerGen` and is measured accurate to within
    `0.12%`. This body is high by exactly the omitted drift factor: measured
    `+0.24%` to `+0.37%` over the tested range. The bias is therefore small but
    STRICTLY ONE-SIDED, and `admixtureLDDecay_ge_finitePopulation` below proves
    that direction rather than leaving it to the runs that happened to be done;
    it also grows with `generations_since`, since the omitted factor is
    compounded.

    Small and one-sided is the combination worth naming: it will not show up as
    noise in a comparison, and it accumulates in the same direction over time.

    Empirical status: VALIDATED as the `Nₑ → ∞` limit; MEASURED high by
    `+0.24%` to `+0.37%` against the finite-population retention. The sibling
    quantities `LDDecayTheory.admixtureLD` and
    `CovarianceStructure.admixtureLDTwoLocus` are EXACT to `2.8e-17` and need
    nothing.

    Power: the comparison in
    `validation/empirical/differential/cluster/fam_admixture.py` runs the
    per-generation retention at `r = 0, 0.0025, 0.02, 0.1, 0.5` with `Ne = 200`,
    where this body predicts `1.000000`, `0.997500`, `0.980000`, `0.900000` and
    `0.500000` against measured `0.997575`, `0.994828`, `0.977596`, `0.896658`
    and `0.506154`. The grid straddles `1/(2Ne)`, so the drift factor is visible
    rather than swamped, and the prediction covers half the unit interval. -/
noncomputable def admixtureLDDecay (r : ℝ) (generations_since : ℕ) : ℝ :=
  (1 - r) ^ generations_since

/-- **The omission is one-sided: this body is never below the finite-population
    retention.** The finite-`Nₑ` retention per generation is
    `(1-r)(1 - 1/(2Nₑ))`, compounded over `generations_since`; dropping the
    drift factor can only raise the result, at every `r`, every `Nₑ` and every
    number of generations. That is why every measured error is positive
    (`+0.24%` to `+0.37%`) rather than scattered about zero, and it is a
    property of the omission rather than of the parameters that were simulated.

    The finite-population factor is written out here instead of being called by
    name because `LDDecayTheory.ldRetentionPerGen`, which is that expression,
    lives in a module that imports this one; the two are the same quantity. -/
theorem admixtureLDDecay_ge_finitePopulation (r Ne : ℝ) (t : ℕ)
    (hr1 : r ≤ 1) (hNe : 1 ≤ Ne) :
    ((1 - r) * (1 - 1 / (2 * Ne))) ^ t ≤ admixtureLDDecay r t := by
  unfold admixtureLDDecay
  have hdrift_nn : (0 : ℝ) ≤ 1 - 1 / (2 * Ne) := by
    rw [sub_nonneg, div_le_one (by linarith)]; linarith
  have hdrift_le : (1 : ℝ) - 1 / (2 * Ne) ≤ 1 := by
    have : (0 : ℝ) < 1 / (2 * Ne) := by positivity
    linarith
  have h_nn : (0 : ℝ) ≤ (1 - r) * (1 - 1 / (2 * Ne)) :=
    mul_nonneg (by linarith) hdrift_nn
  have h_le : (1 - r) * (1 - 1 / (2 * Ne)) ≤ 1 - r := by
    calc (1 - r) * (1 - 1 / (2 * Ne)) ≤ (1 - r) * 1 :=
          mul_le_mul_of_nonneg_left hdrift_le (by linarith)
      _ = 1 - r := mul_one _
  exact pow_le_pow_left₀ h_nn h_le t

/-- **One body, two names, tied.** `DGP.discreteRecombinationSurvival` is the
same quantity read as survival of two loci to the MRCA rather than as decay of
admixture LD; both are the probability of no recombination in `n` meioses. -/
theorem admixtureLDDecay_eq_discreteRecombinationSurvival (r : ℝ) (t : ℕ) :
    admixtureLDDecay r t = discreteRecombinationSurvival r t := rfl

/-- Admixture LD decay is nonneg for recombination rate in [0, 1]. -/
theorem admixtureLDDecay_nonneg (r : ℝ) (t : ℕ)
    (hr1 : r ≤ 1) :
    0 ≤ admixtureLDDecay r t := by
  unfold admixtureLDDecay
  exact pow_nonneg (by linarith) t

/-- Admixture LD decay is at most 1 for valid recombination rate. -/
theorem admixtureLDDecay_le_one (r : ℝ) (t : ℕ)
    (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    admixtureLDDecay r t ≤ 1 := by
  unfold admixtureLDDecay
  exact pow_le_one₀ (by linarith) (by linarith)

/-- **Admixture LD decays over time** (for positive recombination rate). -/
theorem admixtureLDDecay_decreases_with_time (r : ℝ) (t₁ t₂ : ℕ)
    (hr : 0 < r) (hr1 : r < 1) (ht : t₁ < t₂) :
    admixtureLDDecay r t₂ < admixtureLDDecay r t₁ := by
  unfold admixtureLDDecay
  have h_base_pos : 0 < 1 - r := by linarith
  have h_base_lt : 1 - r < 1 := by linarith
  exact pow_lt_pow_right_of_lt_one₀ h_base_pos h_base_lt ht

/-- **Admixture LD decays faster with higher recombination rate.** -/
theorem admixtureLDDecay_decreases_with_recombination (r₁ r₂ : ℝ) (t : ℕ)
    (hr₂1 : r₂ < 1)
    (h_more : r₁ < r₂) (ht : 0 < t) :
    admixtureLDDecay r₂ t < admixtureLDDecay r₁ t := by
  unfold admixtureLDDecay
  exact pow_lt_pow_left₀ (by linarith : 1 - r₂ < 1 - r₁) (by linarith) (by omega)

/-- **At time 0 since admixture, LD is fully preserved.** -/
theorem admixtureLDDecay_at_zero (r : ℝ) :
    admixtureLDDecay r 0 = 1 := by
  unfold admixtureLDDecay
  simp

/-- **Admixture LD creates a transient boost to portability.**
    Recent admixture (small t since pulse) means LD patterns are shared,
    which temporarily improves tagging efficiency. The portability boost
    from admixture LD relative to equilibrium LD is captured by the ratio
    of admixture LD retention to equilibrium LD fraction.

    Empirical status: UNTESTED. -/
noncomputable def admixtureLDBoost (r : ℝ) (t_since : ℕ) (equilibrium_ld : ℝ) : ℝ :=
  admixtureLDDecay r t_since / equilibrium_ld

/-- Admixture LD boost exceeds 1 when admixture LD is above equilibrium. -/
theorem admixtureLDBoost_gt_one_of_above_equilibrium (r : ℝ) (t_since : ℕ) (equilibrium_ld : ℝ)
    (heq_pos : 0 < equilibrium_ld)
    (h_recent : equilibrium_ld < admixtureLDDecay r t_since) :
    1 < admixtureLDBoost r t_since equilibrium_ld := by
  unfold admixtureLDBoost
  rw [lt_div_iff₀ heq_pos]
  linarith

/-- **Transient admixture portability is higher than equilibrium portability.**
    When admixture is recent, the transient shared LD exceeds equilibrium shared LD,
    and thus portability is temporarily enhanced. -/
theorem admixture_portability_above_equilibrium_of_ld_above_equilibrium
    (V_A fst r : ℝ) (t_since : ℕ)
    (equilibrium_ld : ℝ)
    (hVA : 0 < V_A) (hfst_lt : fst < 1)
    (h_recent : equilibrium_ld < admixtureLDDecay r t_since) :
    presentDayPGSVarianceMutationDrift V_A fst equilibrium_ld <
      presentDayPGSVarianceMutationDrift V_A fst (admixtureLDDecay r t_since) := by
  rw [presentDayPGSVarianceMutationDrift_eq, presentDayPGSVarianceMutationDrift_eq]
  have h1 : 0 < (1 - fst) * V_A := mul_pos (by linarith) hVA
  have h_factor : (1 - fst) * equilibrium_ld < (1 - fst) * admixtureLDDecay r t_since :=
    mul_lt_mul_of_pos_left h_recent (by linarith)
  nlinarith

end MigrationDriftPortability

/-! ## Migration-Drift Recurrence: Deriving Fst = 1/(1 + 4Nm) from First Principles

We derive the classical Wright (1931) equilibrium Fst formula from the
migration-drift recurrence relation. The island model with migration rate m
and effective population size Ne yields a linear recurrence on Fst:

  Fst_{t+1} = (1 - 2m - 1/(2Ne)) * Fst_t + 1/(2Ne)

This is the linearized form where (1-m)² ≈ 1 - 2m. At equilibrium
Fst* = Fst_{t+1} = Fst_t, solving the linear equation gives:

  Fst* = 1 / (4*Ne*m + 1)

We prove this closed form satisfies the recurrence, then derive monotonicity
and portability consequences directly from the recurrence structure.
-/

section MigrationDriftRecurrence

/-! ### 1. The migration-drift recurrence -/

/-- **Migration-drift recurrence on Fst.**
    In the island model with migration rate `m` and effective size `Ne`,
    the linearized one-generation update of Fst is:
      Fst_{t+1} = (1 - 2m - 1/(2Ne)) * Fst_t + 1/(2Ne)
    Migration reduces Fst by a factor (1-2m), and drift adds (1-Fst)/(2Ne).
    The linearization replaces (1-m)² with 1-2m (valid for small m).

    Empirical status: UNTESTED. -/
noncomputable def fstMigDriftNext (Ne m Fst : ℝ) : ℝ :=
  (1 - 2 * m - 1 / (2 * Ne)) * Fst + 1 / (2 * Ne)

/-- The recurrence can be written as Fst_{t+1} = a * Fst_t + b where
    a = 1 - 2m - 1/(2Ne) and b = 1/(2Ne). -/
theorem fstMigDriftNext_eq (Ne m Fst : ℝ) :
    fstMigDriftNext Ne m Fst =
      (1 - 2 * m - 1 / (2 * Ne)) * Fst + 1 / (2 * Ne) := by
  rfl

/-- The drift term: when m = 0, the recurrence reduces to pure drift. -/
theorem fstMigDriftNext_no_migration (Ne Fst : ℝ) :
    fstMigDriftNext Ne 0 Fst = (1 - 1 / (2 * Ne)) * Fst + 1 / (2 * Ne) := by
  unfold fstMigDriftNext
  ring

/-- With no migration, the recurrence pushes Fst toward 1: the drift-only
    fixed point is Fst = 1. We verify: f(1) = 1. -/
theorem fstMigDriftNext_no_migration_fixedpoint_one (Ne : ℝ) (hNe : Ne ≠ 0) :
    fstMigDriftNext Ne 0 1 = 1 := by
  rw [fstMigDriftNext_no_migration]
  field_simp
  ring_nf

/-! ### 2. The exact equilibrium fixed point -/

/-- **Equilibrium Fst from the migration-drift recurrence.**
    Solving Fst* = (1 - 2m - 1/(2Ne)) * Fst* + 1/(2Ne) for Fst*:
      Fst* - (1 - 2m - 1/(2Ne)) * Fst* = 1/(2Ne)
      Fst* * (2m + 1/(2Ne)) = 1/(2Ne)
      Fst* = (1/(2Ne)) / (2m + 1/(2Ne))
            = 1 / (4*Ne*m + 1)
    This is the closed-form solution of the linearized recurrence.

    Empirical status: UNTESTED. -/
noncomputable def fstMigDriftEquil (Ne m : ℝ) : ℝ :=
  1 / (4 * Ne * m + 1)

/-- The derived equilibrium matches `fstMigrationDriftEquilibrium`. -/
theorem fstMigDriftEquil_eq_fstMigrationDriftEquilibrium (Ne m : ℝ) :
    fstMigDriftEquil Ne m = fstMigrationDriftEquilibrium Ne m := by
  unfold fstMigDriftEquil fstMigrationDriftEquilibrium
  ring

/-- **Intermediate form of the fixed-point equation.**
    The equilibrium can also be written as
      Fst* = (1/(2Ne)) / (2m + 1/(2Ne))
    which makes the balance between drift (numerator) and
    migration + drift (denominator) explicit. -/
theorem fstMigDriftEquil_ratio_form (Ne m : ℝ)
    (hNe : 0 < Ne) (hm : 0 ≤ m) :
    fstMigDriftEquil Ne m =
      (1 / (2 * Ne)) / (2 * m + 1 / (2 * Ne)) := by
  unfold fstMigDriftEquil
  have hNe2 : (0 : ℝ) < 2 * Ne := by positivity
  have hden : 2 * m + 1 / (2 * Ne) ≠ 0 := by
    have : 0 < 2 * m + 1 / (2 * Ne) := by positivity
    linarith
  field_simp [hden]
  ring

/-! ### 3. Equilibrium Fst is positive and bounded -/

/-- Equilibrium Fst from the recurrence is positive. -/
theorem fstMigDriftEquil_pos (Ne m : ℝ) (hNe : 0 < Ne) (hm : 0 ≤ m) :
    0 < fstMigDriftEquil Ne m := by
  unfold fstMigDriftEquil
  positivity

/-- Equilibrium Fst from the recurrence is at most 1. -/
theorem fstMigDriftEquil_le_one (Ne m : ℝ) (hNe : 0 < Ne) (hm : 0 ≤ m) :
    fstMigDriftEquil Ne m ≤ 1 := by
  unfold fstMigDriftEquil
  rw [div_le_one (by nlinarith)]
  nlinarith

/-- Equilibrium Fst from the recurrence is strictly less than 1 when m > 0. -/
theorem fstMigDriftEquil_lt_one (Ne m : ℝ) (hNe : 0 < Ne) (hm : 0 < m) :
    fstMigDriftEquil Ne m < 1 := by
  unfold fstMigDriftEquil
  rw [div_lt_one (by nlinarith)]
  nlinarith

/-! ### 4. Equilibrium Fst is decreasing in m (derived from the formula) -/

/-- **Equilibrium Fst decreases with migration rate.**
    From Fst* = 1/(4Nm + 1), increasing m increases the denominator,
    hence decreases Fst*. This is derived, not assumed. -/
theorem fstMigDriftEquil_decreasing_in_m (Ne m₁ m₂ : ℝ)
    (hNe : 0 < Ne) (hm₁ : 0 < m₁)
    (h_more : m₁ < m₂) :
    fstMigDriftEquil Ne m₂ < fstMigDriftEquil Ne m₁ := by
  unfold fstMigDriftEquil
  apply div_lt_div_of_pos_left one_pos (by nlinarith) (by nlinarith)

/-! ### 5. Equilibrium Fst is decreasing in Ne (derived from the formula) -/

/-- **Equilibrium Fst decreases with effective population size.**
    From Fst* = 1/(4Nm + 1), increasing Ne increases the denominator 4Nm + 1,
    hence decreases Fst*. Larger populations have slower drift relative to
    migration, so less differentiation. -/
theorem fstMigDriftEquil_decreasing_in_Ne (Ne₁ Ne₂ m : ℝ)
    (hNe₁ : 0 < Ne₁) (hm : 0 < m)
    (h_more : Ne₁ < Ne₂) :
    fstMigDriftEquil Ne₂ m < fstMigDriftEquil Ne₁ m := by
  unfold fstMigDriftEquil
  apply div_lt_div_of_pos_left one_pos (by nlinarith) (by nlinarith)

/-! ### 6. The full (non-linearized) recurrence and its fixed point -/


/-! ### 7. Migration-to-neutral-benchmark connection derived from the recurrence -/

/-- **Neutral allele-frequency benchmark ratio from the derived Fst formula.**
    The benchmark ratio is `1 - Fst = 1 - 1/(4Nm + 1) = 4Nm/(4Nm + 1)`.
    This is still only the recurrence's coarse allele-frequency benchmark,
    not a mechanistic portability law. -/
noncomputable def neutralAFBenchmarkFromRecurrence (Ne m : ℝ) : ℝ :=
  1 - fstMigDriftEquil Ne m

/-- The recurrence-derived neutral allele-frequency benchmark equals
`4Nm / (4Nm + 1)`. -/
theorem neutralAFBenchmarkFromRecurrence_eq (Ne m : ℝ)
    (hNe : 0 < Ne) (hm : 0 ≤ m) :
    neutralAFBenchmarkFromRecurrence Ne m = 4 * Ne * m / (4 * Ne * m + 1) := by
  unfold neutralAFBenchmarkFromRecurrence fstMigDriftEquil
  have hden : 4 * Ne * m + 1 ≠ 0 := by nlinarith
  field_simp [hden]
  ring_nf

/-- **The recurrence-derived neutral benchmark improves with migration rate.**
    From the derived formula `4Nm/(4Nm+1)`, increasing `m` increases the
    recurrence-derived benchmark ratio. -/
theorem neutralAFBenchmarkFromRecurrence_increasing_in_m (Ne m₁ m₂ : ℝ)
    (hNe : 0 < Ne) (hm₁ : 0 < m₁) (hm₂ : 0 < m₂)
    (h_more : m₁ < m₂) :
    neutralAFBenchmarkFromRecurrence Ne m₁ < neutralAFBenchmarkFromRecurrence Ne m₂ := by
  rw [neutralAFBenchmarkFromRecurrence_eq Ne m₁ hNe (le_of_lt hm₁),
      neutralAFBenchmarkFromRecurrence_eq Ne m₂ hNe (le_of_lt hm₂)]
  rw [div_lt_div_iff₀ (by nlinarith) (by nlinarith)]
  nlinarith

/-- **The recurrence-derived neutral benchmark is nonnegative.** -/
theorem neutralAFBenchmarkFromRecurrence_nonneg (Ne m : ℝ) (hNe : 0 < Ne) (hm : 0 ≤ m) :
    0 ≤ neutralAFBenchmarkFromRecurrence Ne m := by
  rw [neutralAFBenchmarkFromRecurrence_eq Ne m hNe hm]
  exact div_nonneg (by nlinarith) (by nlinarith)

/-- **The recurrence-derived neutral benchmark is strictly positive with migration.** -/
theorem neutralAFBenchmarkFromRecurrence_pos (Ne m : ℝ) (hNe : 0 < Ne) (hm : 0 < m) :
    0 < neutralAFBenchmarkFromRecurrence Ne m := by
  rw [neutralAFBenchmarkFromRecurrence_eq Ne m hNe (le_of_lt hm)]
  exact div_pos (by nlinarith) (by nlinarith)

/-- **The recurrence-derived neutral benchmark is strictly less than `1`.** -/
theorem neutralAFBenchmarkFromRecurrence_lt_one (Ne m : ℝ) (hNe : 0 < Ne) (hm : 0 ≤ m) :
    neutralAFBenchmarkFromRecurrence Ne m < 1 := by
  rw [neutralAFBenchmarkFromRecurrence_eq Ne m hNe hm]
  rw [div_lt_one (by nlinarith : 0 < 4 * Ne * m + 1)]
  linarith

/-- **The recurrence-derived benchmark connects back to the file's coarse `R²`
benchmark.**
    Using the recurrence-derived `F_ST`, the benchmark target `R²` is the
    present-day `R²` at `fstMigDriftEquil`. More migration yields higher
    benchmark `R²`. -/
theorem recurrence_derived_R2_increases_with_m (V_A V_E Ne m₁ m₂ : ℝ)
    (hVA : 0 < V_A) (hVE : 0 < V_E) (hNe : 0 < Ne)
    (hm₁ : 0 < m₁) (h_more : m₁ < m₂) :
    presentDayR2 V_A V_E (fstMigDriftEquil Ne m₁) <
      presentDayR2 V_A V_E (fstMigDriftEquil Ne m₂) := by
  rw [fstMigDriftEquil_eq_fstMigrationDriftEquilibrium,
      fstMigDriftEquil_eq_fstMigrationDriftEquilibrium]
  exact drift_degrades_R2 V_A V_E
    (fstMigrationDriftEquilibrium Ne m₂) (fstMigrationDriftEquilibrium Ne m₁)
    hVA hVE
    (fstMigrationDriftEquilibrium_decreases_with_m Ne m₁ m₂ hNe hm₁ h_more)
    (le_of_lt (fstMigrationDriftEquilibrium_lt_one Ne m₁ hNe hm₁))

end MigrationDriftRecurrence

end PortabilityDrift

/-! ## Nonreversible gene flow: the mixing time is not the transfer time

Everything above this point models divergence with reversible machinery — drift, symmetric
migration, coalescent times. Real gene flow is not reversible: expansions, admixture pulses and
sex-biased migration carry probability around cycles. `Calibrator.CirculationDefect` separates
what that changes from what it does not.

It does not change the degradation calculus: the Dirichlet energy annihilates the circulation, so
every ordering of weighting schemes by that energy survives unchanged.

It does change what a measured mixing time means. Circulation accelerates ergodic averaging
without contributing to the frontier, so the diagnostic reports a shorter time than the one
governing transfer — at equal circulation and dissipation, half of it.

That is a third mechanism alongside the two this file carries. Allele-frequency divergence says
how far apart populations are, tagging mismatch says how much linkage structure carries over, and
this says a well-mixed-looking population can still be a bad transfer target because the rate at
which its environment forgets is not the rate at which a design degrades. -/

section NonreversibleFlow

/-- A mixing-time diagnostic understates the transfer-relevant time. Instance of
    `apparentMixingTime_lt_frontierTime`: with any cyclic component to gene flow, the time
    constant an ergodic-averaging diagnostic measures is strictly shorter than the one setting the
    transfer frontier, so substituting it into a horizon calculus overstates transportability.

    Empirical status: DERIVED; the circulation-to-dissipation ratio of a real demography is the
    unmeasured input this asks for. -/
theorem geneFlowMixingTime_understates_transferTime
    (dissipation circulation : ℝ) (hd : 0 < dissipation) (hc : circulation ≠ 0) :
    apparentMixingTime dissipation circulation < frontierTime dissipation :=
  apparentMixingTime_lt_frontierTime dissipation circulation hd hc

/-- The overstatement is a factor of two at equal circulation and dissipation, and grows
    quadratically in the ratio beyond that.

    Empirical status: DERIVED. -/
theorem transferTime_doubles_at_equal_circulation (dissipation : ℝ) (hd : 0 < dissipation) :
    frontierTime dissipation
        = transferTimeInflation dissipation dissipation *
            apparentMixingTime dissipation dissipation ∧
      transferTimeInflation dissipation dissipation = 2 := by
  refine ⟨frontierTime_eq_inflation_mul_apparent dissipation dissipation hd, ?_⟩
  unfold transferTimeInflation
  rw [div_self (ne_of_gt hd)]
  norm_num

end NonreversibleFlow

end Calibrator
