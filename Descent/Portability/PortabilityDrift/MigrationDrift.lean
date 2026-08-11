/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.PortabilityDrift.MutationDrift
import Descent.PopGen.DriftRecurrences
import Descent.Portability.PortabilityDrift.Definitions

assert_below Descent.Decision Descent.Program

namespace Descent.Portability

open PopGen (effectiveSymmetricMigration
  fstMigrationDriftEquilibrium_strictAnti_product
  fstMigrationDriftEquilibrium_decreases_with_m ibdRecurrenceStep ibdRecurrenceFixedPoint
  islandFstMultiplicativeStep fstIslandMultiplicativeEquilibrium fstMigrationDriftEquilibrium)

open MeasureTheory

open PopGen.TransportedMetrics (r2FromSignalVariance r2FromSignalVariance_eq_rsquared
  equalVarianceGaussianAUCFromSignalVariance
  equalVarianceGaussianAUCFromSignalVariance_eq_formula_of_ne_noise)

/-!
# `PortabilityDrift.MigrationDrift`

Part of the split of `Portability/PortabilityDrift.lean`, which was 9,208 lines and 555
declarations -- the largest file in the corpus by both measures, and large enough that
nothing in it could be read without reading past most of it.

The parts are a FAN, not a chain. The head carries the definitions and every import the
subsystem draws on from outside it; each other part imports the head and whichever siblings
actually declare the names it uses. The split first laid the parts out as a chain, each
importing the one before in the order the original was written, which made every part
transitively downstream of everything written earlier -- so the depth of the corpus was a
function of the length of a file rather than of what depends on what. The order here was
recovered by resolving each name a part references back to the sibling that declares it.

Sections are reopened and reclosed by name where a cut falls inside one: the original
opened `section PortabilityDrift` and closed it 8,000 lines later. A section scopes
`variable`s, and this file declares none at that level, so the reopening is exact.
-/

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

/-- **fstMigrationDriftEquilibrium at `4 * Ne * m = -1`, named.** A negative migration rate is
inadmissible, and at `4 Ne m = -1` the divisor vanishes. Lean returns `0`: no differentiation at
all, the value for free gene flow. Consumers must exclude it by hypothesis. -/
theorem fstMigrationDriftEquilibrium_balancing_negative_migration_is_junk :
    fstMigrationDriftEquilibrium 1 (-(1/4)) = 0 := by
  unfold fstMigrationDriftEquilibrium Descent.Core.fstFromFlow
  norm_num

/-- **No migration leaves complete differentiation.** At `m = 0` the island model fixes
populations entirely, so the equilibrium is one; that is the reference point which fixes the
constant term, and it is what a body with the wrong intercept would miss. It is also the
boundary the closed form attains, which was a second theorem with this statement. -/
@[simp] theorem fstMigrationDriftEquilibrium_no_migration (Ne : ℝ) :
    fstMigrationDriftEquilibrium Ne 0 = 1 := by
  unfold fstMigrationDriftEquilibrium Descent.Core.fstFromFlow
  norm_num

/-- **The island-model F_ST is the rest point of the identity balance** driven
by migration.  It is not a stipulated closed form: substitute any other
constant and this fails. -/
theorem fstMigrationDriftEquilibrium_isFixedPoint (Ne m : ℝ)
    (hNe : 0 < Ne) (hm : 0 ≤ m) :
    PopGen.ibdFlowStep Ne m (fstMigrationDriftEquilibrium Ne m) =
      fstMigrationDriftEquilibrium Ne m :=
  PopGen.ibdFlowStep_fixedPoint Ne m hNe hm

/-- **ibdRecurrenceStep at its junk point, named.** At `Ne = 0` the identity-by-descent input
term is junk-zero and the retained term keeps full weight, so an empty population is reported as
generating no new identity by descent. Iterating the recurrence compounds the error. Consumers
must exclude the argument that makes the guard vanish. -/
theorem ibdRecurrenceStep_empty_population_is_junk (rate x : ℝ) :
    ibdRecurrenceStep 0 rate x = (1 - rate) ^ 2 * x := by
  unfold ibdRecurrenceStep Descent.Core.survivalWeightedMix
  simp

/-- **ibdRecurrenceFixedPoint where its denominator vanishes, named.** The guard `(1 - rate) ^ 2 + 2
* Ne * rate * (2 - rate)` is zero at `Ne = 0`, `rate = 1`. Lean returns `0` there rather than
the value the modelled quantity takes, and no type error marks the point. Consumers must require
`(1 - rate) ^ 2 + 2 * Ne * rate * (2 - rate) ≠ 0`. -/
theorem ibdRecurrenceFixedPoint_at_ne0rate1_is_junk :
    ibdRecurrenceFixedPoint 0 1 = 0 := by
  unfold ibdRecurrenceFixedPoint
  norm_num

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
  unfold ibdRecurrenceStep ibdRecurrenceFixedPoint Descent.Core.survivalWeightedMix
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

/-- Reference evaluation; see `Descent.Core.Ratios` for what these pin and why. -/
theorem islandFstMultiplicativeStep_at_reference_point :
    islandFstMultiplicativeStep 1 (1 / 2) 0 = 1 / 8 := by
  norm_num [islandFstMultiplicativeStep, ibdRecurrenceStep, Descent.Core.survivalWeightedMix]

/-! **`islandFstMultiplicativeStep` is `ibdRecurrenceStep` by definition, and needs no
theorem saying so** -- a definitional alias is carried by the elaborator, and a `rfl`
statement of it cannot fail.

**The DEFINITION must stay.** `LDDecayTheory.driftLDStep_eq_islandFstMultiplicativeStep`
proves the independently written `driftLDStep` equal to it by `ring`; that is a genuine
guard between two bodies, and deleting this name would disconnect `driftLDStep` from the
recurrence it is held to. Connectivity to the hub, not theorem count, is what makes a
removal safe. -/

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
    fstMigrationDriftEquilibrium Descent.Core.fstFromFlow
  norm_num

/-- Scaled migration rate is positive when Ne and m are positive. -/
theorem scaledMigrationRate_pos (Ne m : ℝ) (hNe : 0 < Ne) (hm : 0 < m) :
    0 < Descent.Core.scaledMigrationRate Ne m := by
  unfold Descent.Core.scaledMigrationRate Descent.Core.ploidy
  positivity

/-- Fst under migration-drift equilibrium equals 1/(1 + M). -/
theorem fstMigrationDriftEquilibrium_eq_from_M (Ne m : ℝ) :
    fstMigrationDriftEquilibrium Ne m = 1 / (1 + Descent.Core.scaledMigrationRate Ne m) := by
  unfold fstMigrationDriftEquilibrium Descent.Core.scaledMigrationRate Descent.Core.fstFromFlow
    Descent.Core.ploidy
  ring

/-- Equilibrium Fst under migration-drift is positive for nonneg migration. -/
theorem fstMigrationDriftEquilibrium_pos (Ne m : ℝ) (hNe : 0 < Ne) (hm : 0 ≤ m) :
    0 < fstMigrationDriftEquilibrium Ne m := by
  unfold fstMigrationDriftEquilibrium Descent.Core.fstFromFlow
  have : 0 ≤ 4 * Ne * m := by positivity
  positivity

/-- Equilibrium Fst under migration-drift is at most 1. -/
theorem fstMigrationDriftEquilibrium_le_one (Ne m : ℝ) (hNe : 0 < Ne) (hm : 0 ≤ m) :
    fstMigrationDriftEquilibrium Ne m ≤ 1 := by
  unfold fstMigrationDriftEquilibrium Descent.Core.fstFromFlow
  rw [div_le_one (by nlinarith)]
  nlinarith

/-- Equilibrium Fst under migration-drift is strictly less than 1 when m > 0.
    This is the key qualitative result: migration prevents complete fixation. -/
theorem fstMigrationDriftEquilibrium_lt_one (Ne m : ℝ) (hNe : 0 < Ne) (hm : 0 < m) :
    fstMigrationDriftEquilibrium Ne m < 1 := by
  unfold fstMigrationDriftEquilibrium Descent.Core.fstFromFlow
  rw [div_lt_one (by nlinarith)]
  nlinarith

/-- Equilibrium Fst is in the open interval (0, 1) for positive Ne and m. -/
theorem fstMigrationDriftEquilibrium_in_unit (Ne m : ℝ) (hNe : 0 < Ne) (hm : 0 < m) :
    0 < fstMigrationDriftEquilibrium Ne m ∧ fstMigrationDriftEquilibrium Ne m < 1 :=
  ⟨fstMigrationDriftEquilibrium_pos Ne m hNe (le_of_lt hm),
   fstMigrationDriftEquilibrium_lt_one Ne m hNe hm⟩

/-- **Equilibrium Fst decreases with effective population size** (m fixed).
    Larger Ne → slower drift relative to migration → less differentiation. -/
theorem fstMigrationDriftEquilibrium_decreases_with_Ne (Ne₁ Ne₂ m : ℝ)
    (hNe₁ : 0 < Ne₁) (hm : 0 < m) (h_more : Ne₁ < Ne₂) :
    fstMigrationDriftEquilibrium Ne₂ m < fstMigrationDriftEquilibrium Ne₁ m :=
  fstMigrationDriftEquilibrium_strictAnti_product Ne₁ m Ne₂ m
    (by positivity) (by nlinarith)

/-! ### 2. Migration counteracts drift -/

/-! **Deleted: `migration_reduces_fst_vs_pure_drift`.**

This theorem is absent on purpose. Its hypothesis is
`1 / (1 + 4 * Ne * m) < t / (t + 2 * Ne)` and its conclusion is
`fstMigrationDriftEquilibrium Ne m < t / (t + 2 * Ne)`. Since
`fstMigrationDriftEquilibrium Ne m` unfolds to `1 / (1 + 4 * Ne * m)`, the two are the same
Descent.Core.fstFromFlow
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

    Empirical status: **FALSIFIED** outside the weak-migration limit, inherited
    (`validation/empirical/simcov/battery_pd1.py`). This body forwards
    `s.Ne` and `s.mig` to `fstMigrationDriftEquilibrium`, so it carries that
    definition's verdict without qualification: within 2% at `mig ≤ 0.01`, 182%
    high at `mig = 0.5`, against an explicit 200-deme Wright-Fisher island model
    whose panmictic control reads 0.05 sems from zero. The table is at
    `SplitMigrationModel.fstEqLimitLowMutationManyDemes`, which is the same
    closed form written through `scaledMigrationRate`.

    What the forwarding adds over the parent, and what is therefore NOT covered
    by inheriting: that `Ne` and `mig` are passed in that order. Nothing here
    measures the argument order, because `fstMigrationDriftEquilibrium` is
    symmetric in its two arguments only through the product `4 * Ne * m`, so a
    transposition would return the same number and no simulation can see it.
    `SplitMigrationModel.fstMigDriftEq_mul_denom` is what pins the coefficient.

    argument_source: model. -/
noncomputable def SplitMigrationModel.fstMigDriftEq (s : SplitMigrationModel) : ℝ :=
  fstMigrationDriftEquilibrium s.Ne s.mig

/-- **The equilibrium inverts one plus four Ne m.** The many-deme limit identity below relates
this to another quantity without fixing the coefficient on the scaled migration rate; multiplying
the denominator back does, and any other coefficient would satisfy the limit identity equally. -/
theorem SplitMigrationModel.fstMigDriftEq_mul_denom (s : SplitMigrationModel)
    (h : 1 + 4 * s.Ne * s.mig ≠ 0) :
    s.fstMigDriftEq * (1 + 4 * s.Ne * s.mig) = 1 := by
  unfold SplitMigrationModel.fstMigDriftEq fstMigrationDriftEquilibrium Descent.Core.fstFromFlow
  field_simp

/-- SplitMigrationModel equilibrium Fst equals the limit Fst for many demes. -/
theorem SplitMigrationModel.fstMigDriftEq_eq_limit (s : SplitMigrationModel) :
    s.fstMigDriftEq = s.fstEqLimitLowMutationManyDemes := by
  unfold SplitMigrationModel.fstMigDriftEq fstMigrationDriftEquilibrium Descent.Core.fstFromFlow
    SplitMigrationModel.fstEqLimitLowMutationManyDemes
    Descent.Core.scaledMigrationRate Descent.Core.ploidy
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
    Fst between demes separated by d steps saturates:
    Fst(d) = d · Fst_neighbor / (Fst_neighbor · d + α · (1 - Fst_neighbor))
    which is `d / (d + K)` with characteristic scale `K = α (1 - Fst_neighbor)/Fst_neighbor`.
    `α` is the unit of distance -- it rescales that scale -- and at `α = 1` the form
    reproduces its own anchor, `Fst(1) = Fst_neighbor`.

    **This body was corrected.** It previously read
    `min 1 (Fst_neighbor × (1 + α × (d - 1)))`, linear in the separation and held inside
    `[0,1]` by an outer clamp. That form is FALSIFIED and the saturating one is measured;
    the evidence is below. Two theorems changed with it:
    `steppingStoneFstGeneral_eq_one_of_saturated` is gone, replaced by
    `steppingStoneFstGeneral_lt_one`
    which says the opposite, because a saturating form approaches complete
    differentiation without ever attaining it at finite separation; and
    `steppingStoneFstGeneral_increases_with_distance` no longer needs a below-saturation
    hypothesis, since `d/(d+K)` rises at every separation while the clamped linear form
    stopped rising once it hit the clamp.

    The `min 1` is not cosmetic. An `F_ST` is a variance ratio and lies in
    `[0, 1]`; the bare linear form returns `10000` at
    `fst_neighbor = 1, α = 1, d = 10000`, which is not a value the quantity can
    take. Clamping also makes the fixation boundary attainable rather than
    merely approached: `steppingStoneFstGeneral_eq_one_of_saturated` exhibits the
    regime where distant demes are completely differentiated, which is the
    physically correct behaviour of isolation by distance at long range.

    Regime: all separations. The saturating form needs no below-saturation proviso,
    which is the practical gain from the correction: the previous body was declared
    trustworthy only while `fst_neighbor * (1 + α (d - 1))` stayed well below `1`, and it
    failed INSIDE that declared regime -- at `d = 3` the measured `F_ST` is `0.123`,
    nowhere near saturation, and the linear form is 12% high there. A regime restriction
    does not rescue a body that is wrong inside its own regime. The companion
    saturating closed form is `demoSteppingStoneFst` in
    `Descent.PopGen.DemographicHistory`, which is derived from a coalescence time,
    which is not this function and is not being replaced here. A second
    saturating form, `continuousSteppingStoneFst = 1 - exp (-d/L)`, has been
    deleted from `Descent.PopGen.PopulationGeneticsFoundations`: it contradicted
    `demoSteppingStoneFst`, and the coalescent derivation decides against the
    exponential.

    Empirical status: **MIXED** -- the saturating body above is the MEASURED
    form, better than the linear one it replaced on the same runs and with no
    free parameter (`simcov/battery_bulk17.py`, head-to-head table below); and it
    is APPROXIMATE, since `K` still drifts 15% across the swept separations, so
    the true `d`-dependence is not pinned. The falsification recorded next
    belongs to the SUPERSEDED linear body, not to the one defined above.

    A leading marker describing a body that no longer exists is read as the
    current verdict by every scanner and by any reader who stops at the first
    status line, which is why it is stated here rather than left below.

    The superseded body: **FALSIFIED** in its distance dependence
    (`validation/empirical/simcov/battery_bulk11.py`). That body said
    `F_ST` grows LINEARLY in the separation `d`, capped at one. Measured on a
    20-deme 1D stepping stone, `Ne = 500`, `m = 0.01`, interior demes only so no
    boundary reflection enters, `F_ST` read from coalescence times so no
    estimator convention enters, 26 replicates of 6 Mb:

      d    measured F_ST      linear (alpha from d=2)   saturating d/(d+K)
      1    0.05073±0.00285          --                        --
      2    0.09655±0.00423        fitted                    fitted
      3    0.13472±0.00457    0.14238   (1.7 sems)       K = 19.27
      5    0.18782±0.00399    0.23403  (11.6 sems)       K = 21.62
      8    0.27945±0.00605    0.37151  (15.2 sems)       K = 20.63

    `alpha` is fitted at `d = 2` and used to predict the rest, because a form
    fitted to every point agrees with anything monotone. The linear form then
    overshoots by 33 percent at `d = 8`, which is what a function without
    saturation must do once the separation is large enough.

    The sibling `DemographicHistory.demoSteppingStoneFst`, which saturates,
    describes the SAME runs far better: its `K = d(1-F)/F` should be constant
    and comes out 18.71, 19.27, 21.62, 20.63 -- a 15 percent drift rather than
    33, and no systematic overshoot. That head-to-head on one dataset is the
    evidence here, not a control cell that could only agree with itself.

    Neither form is exact. The residual drift in `K` says the saturating form is
    also approximate at these separations, and pinning the true `d`-dependence
    is not attempted here.

    Power: the measurement spans 0.05073 to 0.27945, a factor of five and a
    half, and the two candidate forms diverge monotonically across it. 
    **The correction, measured head to head**
    (`validation/empirical/simcov/battery_bulk17.py`). Same 20-deme lattice,
    `Ne = 500`, `m = 0.01`, interior demes only, `F_ST` from coalescence times, 22
    replicates of 4 Mb. The comparison was deliberately STACKED AGAINST the replacement:
    the linear form was given a free `α` fitted at `d = 2`, while the saturating candidate
    was given nothing but `F(1)` and `α = 1`.

      d    measured F_ST        linear (free α)        saturating (no free parameter)
      1    0.04887 ± 0.00400     anchor                 anchor
      2    0.09378 ± 0.00379     fitted                 --
      3    0.12319 ± 0.00570    0.13869  (2.72 sems)   0.13357  (1.82 sems)
      5    0.20518 ± 0.00574    0.22850  (4.06 sems)   0.20441  (0.13 sems)
      8    0.27555 ± 0.00845    0.36322 (10.38 sems)   0.29132  (1.87 sems)

    The linear form is FALSIFIED at 10.38 sems and 31.8% relative with a fitted
    parameter in hand; the saturating form matches at 1.87 sems with none. The failure
    grows monotonically in `d`, which is the signature of a wrong functional form rather
    than a wrong constant.

    This reproduces `battery_bulk11.py`, which reached the same conclusion on a separate
    lattice realisation with different seeds and 26 replicates of 6 Mb, so the finding
    does not rest on one run.
-/
noncomputable def steppingStoneFstGeneral (fst_neighbor α : ℝ) (d : ℕ) : ℝ :=
  (d : ℝ) * fst_neighbor / (fst_neighbor * (d : ℝ) + α * (1 - fst_neighbor))

/-- **Stepping-stone `F_ST` at the measured shape coefficient**, `α = 1`.

`steppingStoneFstGeneral` carries `α` because the saturating form admits one; this is the
value the measurement picks, and it is picked with NO free parameter to spend. Every current
caller uses this body: nothing in the corpus supplies an `α ≠ 1`, and a coefficient no caller
varies is a free parameter in the signature and a constant in fact.

    Empirical status: **VALIDATED at `α = 1`, and approximate at depth**
    (`validation/empirical/simcov/battery_bulk17.py`, reproduced on separate seeds and a
    separate lattice realisation by `battery_bulk11.py`). A 20-deme 1D stepping stone,
    `Nₑ = 500`, `m = 0.01`, interior demes only, `F_ST` from coalescence times, 22 replicates
    of 4 Mb. The comparison was stacked AGAINST this body: the rival linear form was given a
    free `α` fitted at `d = 2`, this one was given nothing but `F(1)`.

      d    measured F_ST        linear (free α)        this body (no free parameter)
      3    0.12319 ± 0.00570    0.13869  (2.72 sems)   0.13357  (1.82 sems)
      5    0.20518 ± 0.00574    0.22850  (4.06 sems)   0.20441  (0.13 sems)
      8    0.27555 ± 0.00845    0.36322 (10.38 sems)   0.29132  (1.87 sems)

    The linear form is FALSIFIED at 10.38 sems and 31.8% relative with a fitted parameter in
    hand; this one matches at 1.87 sems with none.

    PINNING `α` IS NOT AN ALL-DISTANCE VALIDATION, and the two claims must not be run
    together. `α = 1` is the right coefficient AND the body is approximate at depth: at
    `d = 9` the chart returns 0.255 against an exact 0.193. So the shape coefficient is
    settled and the `d`-dependence at large separation is not, which is the same residual
    drift in `K = d(1-F)/F` that `battery_bulk11` reports.

    Power: the prediction spans 0.13357 to 0.29132 over `d` = 3, 5, 8, and the
    comparison was stacked AGAINST this body -- the rival linear form was given a
    free `α` fitted at `d = 2` and this one was given nothing but `F(1)`. The
    linear form is FALSIFIED at 10.38 sems and 31.8 percent with that fitted
    parameter in hand where this one matches at 1.87 with none. -/
noncomputable def steppingStoneFst (fst_neighbor : ℝ) (d : ℕ) : ℝ :=
  steppingStoneFstGeneral fst_neighbor 1 d

/-- **The pinned body is the general one at the measured coefficient**, stated so that the
general lemmas apply to it by rewriting rather than by unfolding a definition. -/
theorem steppingStoneFst_eq_general (fst_neighbor : ℝ) (d : ℕ) :
    steppingStoneFst fst_neighbor d = steppingStoneFstGeneral fst_neighbor 1 d := rfl

/-- **Stepping-stone Fst never leaves the unit interval.** The saturating body needs no
clamp to achieve this: the denominator exceeds the numerator by `α (1 - fst_neighbor)`,
which is nonnegative exactly when the neighbour value is itself a valid `F_ST`. The
previous linear body returned `10000` at `fst_neighbor = 1, α = 1, d = 10000` and was
held in range by an outer `min`; the range is now a consequence of the form. -/
theorem steppingStoneFstGeneral_le_one (fst_neighbor α : ℝ) (d : ℕ)
    (hfst : 0 < fst_neighbor) (hle : fst_neighbor ≤ 1) (hα : 0 ≤ α) (hd : 1 ≤ d) :
    steppingStoneFstGeneral fst_neighbor α d ≤ 1 := by
  unfold steppingStoneFstGeneral
  have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hnum : 0 < fst_neighbor * (d : ℝ) := by nlinarith
  have hextra : 0 ≤ α * (1 - fst_neighbor) := mul_nonneg hα (by linarith)
  rw [div_le_one (by linarith)]
  nlinarith

/-- **The fixation boundary is approached and never attained.** This REPLACES
`steppingStoneFstGeneral_eq_one_of_saturated`, which said the opposite, and the replacement is
forced by the measurement rather than chosen for elegance. The linear body reached `1` at
finite separation and the clamp then held it there, so complete differentiation was
attainable at a finite number of steps. A saturating form cannot do that: with `α (1 - fst_neighbor)
> 0` the value is strictly below one at every finite `d` and tends to
one only as `d → ∞`, which is the correct behaviour of isolation by distance -- demes an
arbitrary but finite distance apart still share ancestry. -/
theorem steppingStoneFstGeneral_lt_one (fst_neighbor α : ℝ) (d : ℕ)
    (hfst : 0 < fst_neighbor) (hlt : fst_neighbor < 1) (hα : 0 < α) (hd : 1 ≤ d) :
    steppingStoneFstGeneral fst_neighbor α d < 1 := by
  unfold steppingStoneFstGeneral
  have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hnum : 0 < fst_neighbor * (d : ℝ) := by nlinarith
  have hextra : 0 < α * (1 - fst_neighbor) := mul_pos hα (by linarith)
  rw [div_lt_one (by linarith)]
  nlinarith

/-- **Zero separation, zero differentiation.** A deme compared with itself has `F_ST = 0`,
and the saturating body gives it with no hypotheses at all: the numerator carries the
factor `d` and vanishes, so even the degenerate parameter settings that make the
denominator zero return Lean's `0`, which is the right answer here rather than a junk one.

This is the anchor the range lemmas above cannot supply. `steppingStoneFstGeneral_le_one`,
`steppingStoneFstGeneral_lt_one` and `steppingStoneFstGeneral_nonneg` all require `1 ≤ d`,
which is the
correct hypothesis for them — their proofs need the numerator to be positive — and it
excludes the source deme itself. A composed law that starts at zero distance and walks
outward needs the `d = 0` end, and gets it here. -/
theorem steppingStoneFstGeneral_at_zero (fst_neighbor α : ℝ) :
    steppingStoneFstGeneral fst_neighbor α 0 = 0 := by
  unfold steppingStoneFstGeneral
  norm_num

/-- Stepping-stone Fst at distance 1 equals the neighbor Fst. At `α = 1` the
characteristic scale is `(1 - fst_neighbor)/fst_neighbor` and the form reproduces its own
anchor; `α` rescales that length, so it is the unit of distance rather than a per-step
increment as it was under the linear body. -/
theorem steppingStoneFstGeneral_at_one (fst_neighbor : ℝ) :
    steppingStoneFstGeneral fst_neighbor 1 1 = fst_neighbor := by
  unfold steppingStoneFstGeneral
  have hden : fst_neighbor * ((1 : ℕ) : ℝ) + 1 * (1 - fst_neighbor) = 1 := by
    push_cast; ring
  rw [hden, div_one]
  push_cast; ring

/-- **Stepping-stone Fst increases with geographic distance** (isolation by distance).
    Under the saturating body this needs no below-saturation hypothesis: `d / (d + K)` is
    strictly increasing in `d` for every positive `K`, at every separation. The linear
    body required the caller to certify it had not yet hit the clamp, and above the clamp
    the increase stopped altogether. -/
theorem steppingStoneFstGeneral_increases_with_distance
    (fst_neighbor α : ℝ) (d₁ d₂ : ℕ)
    (hfst : 0 < fst_neighbor) (hlt : fst_neighbor < 1) (hα : 0 < α) (hd : d₁ < d₂) :
    steppingStoneFstGeneral fst_neighbor α d₁ < steppingStoneFstGeneral fst_neighbor α d₂ := by
  unfold steppingStoneFstGeneral
  have hd_real : (d₁ : ℝ) < (d₂ : ℝ) := Nat.cast_lt.mpr hd
  have hd₁ : (0 : ℝ) ≤ (d₁ : ℝ) := Nat.cast_nonneg _
  have hK : 0 < α * (1 - fst_neighbor) := mul_pos hα (by linarith)
  have hd₂ : (0 : ℝ) ≤ (d₂ : ℝ) := Nat.cast_nonneg _
  have hp₁ : 0 ≤ fst_neighbor * (d₁ : ℝ) := mul_nonneg (le_of_lt hfst) hd₁
  have hp₂ : 0 ≤ fst_neighbor * (d₂ : ℝ) := mul_nonneg (le_of_lt hfst) hd₂
  have hden₁ : 0 < fst_neighbor * (d₁ : ℝ) + α * (1 - fst_neighbor) := by linarith
  have hden₂ : 0 < fst_neighbor * (d₂ : ℝ) + α * (1 - fst_neighbor) := by linarith
  rw [div_lt_div_iff₀ hden₁ hden₂]
  nlinarith [mul_pos (mul_pos hfst hK) (sub_pos.mpr hd_real)]

/-- **Nearby demes have lower Fst than distant demes.**
    Fst(1) < Fst(d) for d > 1 under the stepping-stone model, at every separation. -/
theorem steppingStoneFstGeneral_neighbor_lt_distant
    (fst_neighbor α : ℝ) (d : ℕ)
    (hfst : 0 < fst_neighbor) (hlt : fst_neighbor < 1) (hα : 0 < α) (hd : 1 < d) :
    steppingStoneFstGeneral fst_neighbor α 1 < steppingStoneFstGeneral fst_neighbor α d :=
  steppingStoneFstGeneral_increases_with_distance fst_neighbor α 1 d hfst hlt hα hd

/-- **Stepping-stone Fst is nonneg for valid parameters.** -/
theorem steppingStoneFstGeneral_nonneg (fst_neighbor α : ℝ) (d : ℕ)
    (hfst : 0 < fst_neighbor) (hle : fst_neighbor ≤ 1) (hα : 0 ≤ α) (hd : 1 ≤ d) :
    0 ≤ steppingStoneFstGeneral fst_neighbor α d := by
  unfold steppingStoneFstGeneral
  have hd1 : (1 : ℝ) ≤ (d : ℝ) := Nat.one_le_cast.mpr hd
  have hextra : 0 ≤ α * (1 - fst_neighbor) := mul_nonneg hα (by linarith)
  apply div_nonneg (by nlinarith) (by nlinarith)

/-! ### 4. Migration's effect on LD: gene flow homogenizes LD patterns -/

/-! #### Derivation of the shared LD fraction: migration against recombination

This section read, for a long time, that the shared LD fraction is `1 - Fst`:
`Fst` is the fraction of variation held BETWEEN demes, so its complement is the
fraction held in common, and "LD patterns are shared to the same extent as
allele frequencies". The last clause is the false one, and simulation says so at
35 sems (`simcov/battery_bulk34.py`): at `Fst = 0.56` the measured shared
fraction is 0.91 where `1 - Fst` predicts 0.44.

The reason is that `Fst` is a property of ONE site and LD is a property of a
PAIR, and a pair has a parameter a single site does not: the recombination rate
`c` between the two sites. At fixed `Fst` -- one deme pair, one replicate set --
the measured shared fraction runs from 0.97 down to 0.06 as the SNP pairs are
sorted by separation. No function of `Fst` alone, of any shape, can follow that,
which is why `(1 - Fst)²` and `1 - 2·Fst` were rejected too.

The correct derivation is a race between migration and recombination, and it is
the classical one (Ohta 1982; Sved 2009, eqns 5-6 and 9). Let `σ_W` be the
within-deme second moment of the disequilibrium `D` and `σ_B` the between-deme
one. Both decay by `(1-c)²` per generation -- one factor of `(1-c)` for each
deme -- and drift feeds only `σ_W`, since drift in one deme is independent of
drift in the other:

  σ_W' = (1-c)²·[(1-α)·σ_W + α·σ_B] + 1/(2·Nₑ)
  σ_B' = (1-c)²·[β·σ_W + (1-β)·σ_B]

where `β = 2·m·(1-m)` is the chance that two gametes now in different demes sat
in the same deme one generation ago. The second line carries no source term, and
that is the whole content: between demes there is nothing to renew the
association. At stationarity, for small `m` and `c`,

  shared_LD = σ_B / σ_W = (1-c)²·β / (1 - (1-c)²·(1-β)) → 2·m / (2·m + 2·c)
            = m / (m + c)

The coalescent reading is the same race: two lineages in different demes cannot
coalesce at all until migration puts them together, and recombination -- rate
`2·c`, one lineage each -- runs against that migration. `Nₑ` cancels, which is
the sharpest thing about the result: `Nₑ` sets how much LD there is, not how
much of it is shared. `m` is the backward rate between one ORDERED pair of
demes, so the deme count cancels as well, a move to a third deme leaving the two
lineages apart. `sharedLD_from_equilibrium` below is this ratio, and
`sharedLD_from_equilibrium_eq_sharedLDFromMigration` shows it is the same
saturating map as before, read at `m/c` rather than at `4·Nₑ·m`. -/

/-- **Shared LD fraction: migration against recombination.**
    `m / (m + c)`, where `m` is the backward migration rate between one ORDERED
    pair of demes and `c` the recombination rate between the two sites whose
    disequilibrium is being shared. Derived above from the stationary
    disequilibrium moments (Ohta 1982; Sved 2009, eqns 5-6 and 9): between demes
    nothing renews the association, so the shared component is whatever survives
    the race between the migration that reunites two lineages and the
    recombination that separates the two loci.

    NO SHAPE IN `F_ST` ALONE IS ADMISSIBLE HERE, and the argument list is the
    finding. `F_ST` is a property of one site, shared LD of a PAIR, and a pair
    carries a parameter a single site does not. `1 - fstMigrationDriftEquilibrium
    Nₑ m` is FALSIFIED at 35 sems (`simcov/battery_bulk34.py`, 0.91 measured
    against 0.44 predicted at `F_ST = 0.56`), `(1 - F)²` at 56 sems and `1 - 2·F`
    at 78 sems. The reason none of them can survive: at FIXED `F_ST` -- one deme
    pair, one replicate set -- the measured fraction runs from 0.97 to 0.06 as the
    pairs are sorted by separation. `Nₑ` is absent from this body for the same
    reason: it sets how much LD there is, not how much of it is shared.

    Denotes: a fraction of the disequilibrium SECOND MOMENT, `σ_B/σ_W`, not a
    correlation of `r`. The two are different numbers -- normalising by the
    frequency term inflates the fraction by 5 to 25% -- and Sved's `E[r²] = L`
    is the step where that cost is paid.

    Empirical status: **CONDITIONALLY VALID** for `c ≲ m/5`
    (`simcov/battery_sharedld_rec.py`). Measured as `σ_B/σ_W` with every product
    taken between DISJOINT sample halves, so no sampling noise enters either
    the numerator or the denominator; 10 Mb, 12 replicates, `Nₑ` varied
    threefold at fixed `m` on purpose:

      Nₑ     m         c/m     this body   measured           rel
      2000   4.0e-3    0.01    0.9878      0.9726 ± 0.0047    -1.5%
      2000   4.0e-3    0.05    0.9549      0.9504 ± 0.0052    -0.5%
      1000   1.0e-3    0.05    0.9529      0.8897 ± 0.0064    +7.1%
      2000   1.0e-3    0.05    0.9527      0.9159 ± 0.0073    +4.0%
      4000   1.0e-3    0.05    0.9528      0.9364 ± 0.0047    +1.8%
      2000   4.0e-3    0.16    0.8607      0.8826 ± 0.0067    -2.5%
      1000   1.0e-3    0.19    0.8413      0.8399 ± 0.0077    +0.2%
      2000   1.0e-3    0.19    0.8412      0.8623 ± 0.0082    -2.4%
      4000   1.0e-3    0.19    0.8408      0.8687 ± 0.0049    -3.2%
      2000   2.5e-4    0.20    0.8357      0.8183 ± 0.0081    +2.1%
      2000   4.0e-3    0.50    0.6673      0.7128 ± 0.0135    -6.4%
      1000   1.0e-3    0.65    0.6069      0.7198 ± 0.0086   -15.7%
      2000   1.0e-3    0.65    0.6066      0.7028 ± 0.0111   -13.7%
      4000   1.0e-3    0.65    0.6063      0.6859 ± 0.0089   -11.6%
      2000   2.5e-4    0.75    0.5711      0.7197 ± 0.0098   -20.7%

    So: within `c ≲ m/5` the body is right to 3% on ten of eleven cells and to
    7% on the last, under an ascertainment systematic of 12% (the same run with a pooled-frequency
    filter instead of a per-deme one moves the measured ratio
    by that much on average). Past `c ≈ m/2` the body reads LOW and the shortfall
    grows to 21% at `c = 0.75·m` and to 41% out to `c = 80·m`; the shape that
    tracks the measurement there is `2·m/(2·m + c)`, off by at worst 9.7%
    against this body's 20.7%, and it is NOT ADOPTED because nothing derives it
    -- it is this race with the destruction rate halved by hand, and a fitted
    factor of two named as a law is what this corpus refuses.

    What neither shape carries: at `c/m = 0.05` the measured fraction rises
    0.8897, 0.9159, 0.9364 as `Nₑ` goes 1000, 2000, 4000. The stationary ratio is
    `Nₑ`-free, so that trend is a finite-`Nₑ` correction the derivation drops,
    and it bounds how well any `Nₑ`-free body can do at small `c`.

    The `Nₑ` axis is also what kills the competitors outright: `1 - F_ST` (32
    sems, 42%) and `M/(1+M)` (29 sems, 37%) move with `Nₑ` and not with `c`,
    which is exactly backwards, and `1/(1 + 4·Nₑ·c)` -- the within-deme Sved
    shape, which moves with `c` but not with `m` -- fails at 128 sems.

    Control: one panmictic population split four ways, run through the SAME
    estimator, must give 1 at every distance and does, 2.15 sems from it. The
    old correlation estimator returned 0.9945 there, and the 0.55% shortfall was
    attenuation; the split-half denominator removes it, so the control can now
    fail for a reason other than bias.

    argument_source: model, with `c` realized from the separations of the pairs
    actually drawn.

    REBUILT AND RE-RUN, and the numbers above are superseded by these. The
    battery this cites had never been committed: the verdict was real when it
    was produced and no reader could check it, which is the same standing as no
    verdict. `simcov/battery_sharedld_rec.py` is now in the repository, was run against
    the design described above, and its results are committed beside it.
    FALSIFIED at worst 3.4 sems (44% relative) over the c/m range the design reaches,
    with `1 - F_ST`, `M/(1+M)` and the within-deme Sved shape all rejected at 4.9, 4.9
    and 14.4 sems -- and `2m/(2m + c)` MATCHING at 2.3 sems, which is the same picture
    the table above records. The estimator is the split-half second-moment ratio and the
    panmictic control passes at 0.956 against 1.
    -/
noncomputable def sharedLD_from_equilibrium (m c : ℝ) : ℝ :=
  Descent.Core.share m c

/-- **One step of the race the shared fraction is the outcome of.** The derivation above
reads `m/(m + c)` two ways, and this is the second one stated as a map: two lineages in
different demes are shared once migration puts them together, lost once recombination pulls
the two sites apart, and otherwise carry into the next generation unchanged. So a fraction
`m` becomes shared, a fraction `c` is lost, and the remaining `1 - m - c` keeps whatever it
had.

The point of writing it is that `sharedLD_from_equilibrium` is then derived rather than
stipulated: a closed form asserted beside a dynamic can be wrong about it without anything
failing, and the theorem below is what makes that impossible here.

    Empirical status: THIS IS THE MODEL. The map constitutes the migration-recombination
    race rather than asserting anything about a population; what a population does is
    measured on the fraction it fixes, whose status line is on
    `sharedLD_from_equilibrium`. -/
noncomputable def sharedLDStep (m c r : ℝ) : ℝ := m + (1 - m - c) * r

/-- **The shared fraction is the rest point of that step**, and not a stipulation placed
next to it. `m/(m + c)` is exactly the `r` the race leaves unchanged, which is the
competing-risks reading of the derivation above: migration and recombination run against
each other and the shared fraction is migration's share of the total hazard. -/
theorem sharedLD_from_equilibrium_isFixedPoint (m c : ℝ) (h : m + c ≠ 0) :
    sharedLDStep m c (sharedLD_from_equilibrium m c) = sharedLD_from_equilibrium m c := by
  unfold sharedLDStep sharedLD_from_equilibrium Descent.Core.share
  field_simp
  ring

/-- Reference evaluation; see `Descent.Core.Ratios` for what these pin and why. -/
theorem sharedLD_from_equilibrium_at_reference_point :
    sharedLD_from_equilibrium 1 1 = 1 / 2 := by
  norm_num [sharedLD_from_equilibrium,
      Descent.Core.share]

/-- **The two hazards divide one unit between them.**

Migration's share and recombination's share of the same race sum to one: swap the two rates
and you get exactly what the first fraction leaves behind. This is the competing-risks reading
carried to its conclusion — there is one lineage pair, it is either brought together or pulled
apart, and no third outcome is available at equilibrium.

It is also the sharpest of the cheap tests on this body. Every rival the battery above
rejects fails it: `2m / (2m + c)` sums with its swap to more than one wherever the two rates
differ, and `1 - F_ST` and `M / (1 + M)` do not depend on `c` at all, so neither can trade
against recombination's share. -/
theorem sharedLD_from_equilibrium_add_swap (m c : ℝ) (h : m + c ≠ 0) :
    Descent.Core.sum (sharedLD_from_equilibrium m c) (sharedLD_from_equilibrium c m) = 1 := by
  unfold Descent.Core.sum sharedLD_from_equilibrium Descent.Core.share
  rw [add_comm c m, div_add_div_same, div_self h]

/-- **Complete linkage: the shared fraction is 1.** Two sites that never
recombine apart carry the same ancestral association in both demes however far
their frequencies have drifted, and this is the limit the old `1 - F_ST` body
could not reach: it answered `4·Nₑ·m/(1 + 4·Nₑ·m)` here, a number that has
nothing to do with linkage. -/
theorem sharedLD_from_equilibrium_no_recombination (m : ℝ) (hm : m ≠ 0) :
    sharedLD_from_equilibrium m 0 = 1 := by
  unfold sharedLD_from_equilibrium Descent.Core.share
  rw [add_zero, div_self hm]

/-- **No migration, no shared disequilibrium.** With the demes closed, two
lineages in different demes never meet, so nothing renews the association
between them. -/
theorem sharedLD_from_equilibrium_no_migration (c : ℝ) :
    sharedLD_from_equilibrium 0 c = 0 := by
  unfold sharedLD_from_equilibrium Descent.Core.share
  simp

/-- **Both rates zero, named.** With `m = c = 0` the body is `0/0`, reported as
`0` -- complete sharing spelled as no sharing at all, the opposite of the
`c → 0` limit above. Consumers must exclude it by requiring `0 < m + c`. -/
theorem sharedLD_from_equilibrium_both_rates_zero_is_junk :
    sharedLD_from_equilibrium 0 0 = 0 := by
  unfold sharedLD_from_equilibrium Descent.Core.share
  norm_num

/-- **Only the ratio of the two rates is read.** Scaling migration and
recombination together leaves the shared fraction alone: the body is homogeneous
of degree zero, so it is a function of `c/m` and carries no time unit. This is
the invariance the old body did not have and the new one must be tested against
-- a design that scales `m` alone moves it, and one that scales both does not. -/
theorem sharedLD_from_equilibrium_scale_invariant (k m c : ℝ) (hk : k ≠ 0) :
    sharedLD_from_equilibrium (k * m) (k * c) = sharedLD_from_equilibrium m c := by
  unfold sharedLD_from_equilibrium Descent.Core.share
  rw [← mul_add, mul_div_mul_left _ _ hk]

/-- **Tighter linkage shares more.** Strictly decreasing in the recombination
rate at fixed migration -- the direction the measurement confirms across four
orders of magnitude in `c`, and the direction no function of `F_ST` has at all. -/
theorem sharedLD_from_equilibrium_decreasing_in_recombination
    (m c₁ c₂ : ℝ) (hm : 0 < m) (hc₁ : 0 ≤ c₁) (hlt : c₁ < c₂) :
    sharedLD_from_equilibrium m c₂ < sharedLD_from_equilibrium m c₁ := by
  unfold sharedLD_from_equilibrium Descent.Core.share
  have h₁ : 0 < m + c₁ := by linarith
  have h₂ : 0 < m + c₂ := by linarith
  rw [div_lt_div_iff₀ h₂ h₁]
  nlinarith

/-- **More gene flow shares more.** Strictly increasing in the migration rate at
fixed recombination. -/
theorem sharedLD_from_equilibrium_increasing_in_migration
    (m₁ m₂ c : ℝ) (hc : 0 < c) (hm₁ : 0 ≤ m₁) (hlt : m₁ < m₂) :
    sharedLD_from_equilibrium m₁ c < sharedLD_from_equilibrium m₂ c := by
  unfold sharedLD_from_equilibrium Descent.Core.share
  have h₁ : 0 < m₁ + c := by linarith
  have h₂ : 0 < m₂ + c := by linarith
  rw [div_lt_div_iff₀ h₁ h₂]
  nlinarith

/-- **It is a fraction.** Nonnegative for nonnegative rates. -/
theorem sharedLD_from_equilibrium_nonneg (m c : ℝ) (hm : 0 ≤ m) (hc : 0 ≤ c) :
    0 ≤ sharedLD_from_equilibrium m c := by
  unfold sharedLD_from_equilibrium Descent.Core.share
  exact div_nonneg hm (by linarith)

/-- **It is a fraction: below one whenever the loci can recombine apart.** -/
theorem sharedLD_from_equilibrium_lt_one (m c : ℝ) (hm : 0 ≤ m) (hc : 0 < c) :
    sharedLD_from_equilibrium m c < 1 := by
  unfold sharedLD_from_equilibrium Descent.Core.share
  rw [div_lt_one (by linarith)]
  linarith

/-- **Shared LD fraction under migration-drift balance.**
    Gene flow homogenizes LD patterns between populations. The fraction of LD
    that is shared between two demes increases with migration rate:
    shared_LD(m) = M / (1 + M) where M = 4Nm.

    **Derivation:** This formula is the complement of the Wright (1931)
    island-model Fst equilibrium. Since Fst = 1/(1+M) (proved at
    `fstMigrationDriftEquilibrium`), the complement is
    1 - Fst = 1 - 1/(1+M) = M/(1+M).

    THE MAP IS RIGHT AND THE ARGUMENT WAS NOT. `sharedLD_from_equilibrium` is
    now `m/(m + c)`, and `sharedLD_from_equilibrium_eq_sharedLDFromMigration`
    shows that this is the SAME saturating map read at the
    migration-to-recombination ratio `m/c`. So `M/(1+M)` survives as a shape;
    what does not survive is feeding it `M = 4·Nₑ·m` and calling the result a
    shared-LD fraction, which is what the paragraph below rejects.

    Empirical status: **AN IDENTITY, NOT A MEASUREMENT**
    (`validation/empirical/simcov/battery_bulk9.py`). This is the
    algebraic complement of `fstMigrationDriftEquilibrium`, which is separately
    measured, so a battery comparing the two reproduces `M/(1+M) = 1 - 1/(1+M)`
    to machine precision and the harness returns SELF-TEST. The empirical content
    is entirely in the equilibrium it complements -- including that equilibrium's
    recorded deme-count blindness, which this inherits.

    THE NAME IS A SECOND CLAIM, AND IT IS **FALSIFIED**
    (`simcov/battery_bulk34.py`). That `M/(1+M) = 1 - 1/(1+M)` is algebra. That
    the resulting number is the fraction of LD SHARED between demes is not, and
    a simulation reaches it: shared LD read as the cross-deme correlation of
    signed `r` over SNP pairs -- a property of PAIRS of sites, where `F_ST` is a
    property of single sites -- runs 0.9060, 0.9341, 0.9674 and 0.9890 as
    `4·Nₑ·m` goes 0.4, 2, 8, 40, against this body's 0.4394, 0.7921, 0.9290 and
    0.9864. Worst cell 35 sems, low by a factor of two at `F_ST = 0.56`. The
    agreement at `4·Nₑ·m = 40` is the weak-differentiation limit, not the
    general case. See `sharedLD_from_equilibrium` for the full table, the
    rejected variants, the control, and the argument -- the recombination rate
    between the two sites -- whose absence is why no reading of `4·Nₑ·m` could
    have worked.

    So the SELF-TEST verdict is right about what `battery_bulk9.py` compared,
    and wrong as a summary of this body's empirical content: the identity is
    unfalsifiable, the interpretation is not, and the interpretation is what
    downstream consumers use. -/
noncomputable def sharedLDFromMigration (M : ℝ) : ℝ :=
  Descent.Core.saturation M

/-- **sharedLDFromMigration at `M = -1`, named.** A negative scaled migration rate is
inadmissible; the divisor vanishes there and the shared disequilibrium is reported as zero, which
is what complete isolation also gives. Consumers must exclude it by hypothesis. -/
theorem sharedLDFromMigration_negative_unit_migration_is_junk :
    sharedLDFromMigration (-1) = 0 := by
  unfold sharedLDFromMigration Descent.Core.saturation
  norm_num

/-- **The migration shared-LD map and the coalescent `F_ST` map are one MAP, and the
identity is stated at the map rather than at the two quantities.**

`Core.fstFromTau` sends a coalescent time `τ` to `τ/(1 + τ)`; `sharedLDFromMigration`
sends the scaled migration number `M` to `M/(1 + M)`. The arguments are different
quantities and no value of one may be substituted for the other, but the map is the same
saturating map, and a change of convention in either spelling has to be made in both.

Stating that as `sharedLDFromMigration M = Core.fstFromTau M` would say the right thing
in a form that ASSERTS the substitution the paragraph above forbids: both sides would
take the same real. `Core.fstFromTau` takes a `Tau`, so that spelling does not elaborate,
and the shared content is stated where it actually lives -- both are `Core.saturation`. -/
theorem sharedLDFromMigration_eq_saturation (M : ℝ) :
    sharedLDFromMigration M = Descent.Core.saturation M := rfl

/-- **The derived shared LD fraction is the same saturating map, read at `m/c`.**
    `m/(m + c) = (m/c)/(1 + m/c)`, so the shape `M/(1 + M)` survives the repair
    of `sharedLD_from_equilibrium` unchanged; what changed is its ARGUMENT, from
    the scaled migration rate `4·Nₑ·m` to the migration-to-recombination ratio
    `m/c`. The old reading is the one the simulation rejected, and this theorem
    is where the substitution that produced it is now visible: no value of
    `4·Nₑ·m` may be fed to this map as a shared-LD fraction. -/
theorem sharedLD_from_equilibrium_eq_sharedLDFromMigration (m c : ℝ) (hc : 0 < c) :
    sharedLD_from_equilibrium m c = sharedLDFromMigration (m / c) := by
  unfold sharedLD_from_equilibrium sharedLDFromMigration Descent.Core.share Descent.Core.saturation
  have hc' : c ≠ 0 := ne_of_gt hc
  have h1 : 1 + m / c = (m + c) / c := by field_simp; ring
  rw [h1]
  rcases eq_or_ne (m + c) 0 with h | h
  · rw [h]
    simp
  · rw [div_div_div_cancel_right₀]
    -- `div_div_div_cancel_right₀` discharges the equality but leaves its own
    -- side condition, which is `hc'` from three lines up. Left open, this was
    -- the single module that failed to build.
    exact hc'

/-- Shared LD fraction is nonneg for nonneg M. -/
theorem sharedLDFromMigration_nonneg (M : ℝ) (hM : 0 ≤ M) :
    0 ≤ sharedLDFromMigration M := by
  unfold sharedLDFromMigration Descent.Core.saturation
  exact div_nonneg hM (by linarith)

/-- Shared LD fraction is at most 1. -/
theorem sharedLDFromMigration_lt_one (M : ℝ) (hM : 0 ≤ M) :
    sharedLDFromMigration M < 1 := by
  unfold sharedLDFromMigration Descent.Core.saturation
  rw [div_lt_one (by linarith : 0 < 1 + M)]
  linarith

/-- **Shared LD fraction increases with migration rate.**
    More migration → more shared LD → better PGS portability. -/
theorem sharedLDFromMigration_increases (M₁ M₂ : ℝ)
    (hM₁ : 0 < M₁) (h_more : M₁ < M₂) :
    sharedLDFromMigration M₁ < sharedLDFromMigration M₂ := by
  unfold sharedLDFromMigration Descent.Core.saturation
  rw [div_lt_div_iff₀ (by linarith) (by linarith)]
  nlinarith

/-- **Complementarity of Fst and shared LD under migration-drift.**
    Fst = 1/(1+M) and shared_LD = M/(1+M) sum to 1.
    This parallels the mutation-drift complementarity. -/
theorem fst_plus_sharedLD_eq_one (Ne m : ℝ) (hNe : 0 < Ne) (hm : 0 ≤ m) :
    fstMigrationDriftEquilibrium Ne m + sharedLDFromMigration (Descent.Core.scaledMigrationRate Ne
      m) = 1 := by
  unfold fstMigrationDriftEquilibrium sharedLDFromMigration Descent.Core.scaledMigrationRate
    Descent.Core.fstFromFlow Descent.Core.saturation Descent.Core.ploidy
  have hden : 1 + 4 * Ne * m ≠ 0 := by nlinarith
  have hden' : 1 + Ne * m * 4 ≠ 0 := by intro hc; apply hden; linarith
  field_simp
  ring

/-! ### 5. Portability under migration-drift: R² improves with gene flow -/

/-- **Two demes exchanging migrants at two different rates.**

    `1 / (1 + 4 Nₑ (m₁₂ + m₂₁))`: the differentiation between two demes is set by
    the TOTAL rate at which they exchange lineages, and by nothing else. It does
    not depend on the direction, and there is no such thing as "`F_ST` from
    population 1's perspective" -- `F_ST` is a property of the pair.

    **Both the signature and the body have been corrected, and the claim the old
    ones made was excluded by measurement.** The definition read
    `asymmetricFst (Ne m_into) = 1 / (1 + 4 Nₑ m_into)`: one rate, named as the
    rate INTO the focal deme, with two theorems below asserting that the answer
    moves when the direction is swapped. Two things were wrong with it at once.
    It could not say which of the two rates `m_into` was, and at `m₁₂ = m₂₁`,
    where that ambiguity does not arise, it still returned the many-deme limit
    `1/(1 + 4 Nₑ m)` for a system its own name commits to exactly two demes.

    Empirical status: **VALIDATED after correction; the superseded body
    FALSIFIED at up to 80 sems**
    (`validation/empirical/simcov/battery_dis2.py`). Two demes,
    `Ne = 1000`, `F_ST` read as `1 - E[T_within]/E[T_between]` from branch
    lengths so no estimator convention enters, 24 replicates of 4 Mb. Six
    designs: the total rate spans a factor of four, and three of them share a
    total while differing in asymmetry, so a law that depended on more than the
    total would separate:

      m12      m21      larger    smaller   this body   measured
      5.0e-4   5.0e-4   0.33333   0.33333   0.20000     0.22086 ± 0.01028
      1.0e-3   1.0e-3   0.20000   0.20000   0.11111     0.12226 ± 0.00576
      2.0e-3   2.0e-3   0.11111   0.11111   0.05882     0.05748 ± 0.00331
      1.5e-3   5.0e-4   0.14286   0.33333   0.11111     0.10395 ± 0.00570
      1.8e-3   2.0e-4   0.12195   0.55556   0.11111     0.10281 ± 0.00567
      3.5e-3   5.0e-4   0.06667   0.33333   0.05882     0.05717 ± 0.00383

    This body's worst cell is 2.03 sems. The two readings of the old single
    argument are excluded at 16.2 and 79.9 sems, and neither failure is a
    constant: the smaller-rate reading is wrong by a factor of five at the most
    asymmetric design and right to within a factor of two at the least, which is
    what an underspecified signature looks like from the outside.

    Note which rows carry the finding. The three symmetric rows alone would only
    have shown the missing deme-count factor of two. The three rows sharing a
    total of `2.0e-3` while running from mild to strong asymmetry are what
    excludes any direction dependence: they agree with each other to 1.4 sems
    while the two directional readings differ from each other by a factor of
    four and a half across them.

    The positive control is the symmetric cell at `m = 1.0e-3` against the
    two-deme island value `1/(1 + 2 · 4 Nₑ m)`, validated independently in
    `battery_correct.py`, and it passes at 1.93 sems.

    Superseded, and recorded because it was believed: **FALSIFIED**, by the same
    mechanism as
    `PopulationGeneticsFoundations.fstMigrationMutationEquilibriumManyDemes`: the
    deme-count factor is missing (`validation/empirical/simcov/battery_bulk13.py`).
    Two demes with asymmetric migration, `Ne = 1000`, `F_ST` read as
    `1 - E[T_within]/E[T_between]` from coalescence times so no estimator
    convention enters, 26 replicates of 4 Mb:

      m12       m21      larger-rate reading   smaller-rate   measured
      1.0e-3    1.0e-3     0.20000 (14.5σ)     0.20000 (14.5σ)  0.11480±0.00589
      1.5e-3    5.0e-4     0.14286 ( 4.3σ)     0.33333 (34.1σ)  0.11538±0.00640
      1.8e-3    2.0e-4     0.12195 ( 2.4σ)     0.55556 (85.6σ)  0.10918±0.00521

    NEITHER reading of the single `m_into` argument works, and the SYMMETRIC row
    says why. There `m12 = m21`, so there is no ambiguity about which rate to
    use, and the body still misses by 14.5 sems: it returns
    `1/(1 + 4 Ne m) = 0.200` where the two-deme value is
    `1/(1 + 2 · 4 Ne m) = 0.111`. The factor of two is `islandDemeCorrection` at
    `n = 2`, which two independent designs in this branch have now confirmed.

    So this is not an asymmetry problem at all. It is the deme-count blindness
    already recorded on `fstMigrationMutationEquilibriumManyDemes`, in a definition whose
    name commits it to exactly two demes and which therefore cannot plead the
    many-deme limit. Use `fstIslandEquilibriumFiniteDemes` with `nDemes = 2`.

    The positive control is the symmetric cell against the independently
    validated two-deme island value, and it passes at 0.77 sems, so the design
    reproduces a known answer before reporting a new one -- which the forward
    Wright-Fisher attempt at this same pair in `battery_bulk1.py` did not, and
    was correctly voided for.

    Power: the prediction spans 0.05882 to 0.20000 across the design, a factor
    of three and a half. -/
noncomputable def asymmetricFst (Ne m₁₂ m₂₁ : ℝ) : ℝ :=
  1 / (1 + 4 * Ne * (m₁₂ + m₂₁))

/-- **Asymmetric migration enters the island law only through the TOTAL rate.**

The body is `Core.fstFromFlow` applied to `Core.scaledMigrationRate Ne (m₁₂ + m₂₁)`, so two
demes exchanging migrants at different rates are, for `F_ST`, a single deme pair exchanging
at the sum. That is the content: the asymmetry does not survive into the equilibrium, and a
reader who expected a separate law for it gets the reason it is not there.

It also places the `4` where the others are. Written out here it is a fourth inlined ploidy
convention; through `scaledMigrationRate` it is `2 · ploidy · Ne · m` and moves with the
convention. -/
theorem asymmetricFst_eq_fstFromFlow_total (Ne m₁₂ m₂₁ : ℝ) :
    asymmetricFst Ne m₁₂ m₂₁
      = Descent.Core.fstFromFlow (Descent.Core.scaledMigrationRate Ne (m₁₂ + m₂₁)) := by
  unfold asymmetricFst Descent.Core.fstFromFlow Descent.Core.scaledMigrationRate
    Descent.Core.ploidy
  ring_nf

/-- **asymmetricFst at `4 * Ne * (m₁₂ + m₂₁) = -1`, named.** The two-deme twin of
`fstMigrationDriftEquilibrium_balancing_negative_migration_is_junk`, with the same divisor and
the same collapse to no differentiation. Consumers must exclude it by hypothesis. -/
theorem asymmetricFst_balancing_negative_migration_is_junk :
    asymmetricFst 1 (-(1/8)) (-(1/8)) = 0 := by
  unfold asymmetricFst
  norm_num

/-- **Two demes at two rates are one deme pair at the total rate.** The limit form applied to
the SUM of the two rates is the two-deme answer -- which is also why the deme-count factor of
two appears in the symmetric case without being written anywhere: at `m₁₂ = m₂₁ = m` the sum is
`2 m`. -/
theorem asymmetricFst_eq_migrationDriftEq (Ne m₁₂ m₂₁ : ℝ) :
    asymmetricFst Ne m₁₂ m₂₁ = fstMigrationDriftEquilibrium Ne (m₁₂ + m₂₁) := by
  unfold asymmetricFst fstMigrationDriftEquilibrium Descent.Core.fstFromFlow
  rfl

/-- **The two-deme `Fst`'s scale, pinned.** The identity with `migrationDriftEq` constrains the
two definitions jointly: a common wrong factor in both cancels and the identity survives. This
evaluates `asymmetricFst` alone, at the total exchange rate where drift and immigration balance,
and fixes the `4 Ne m` normalisation that the identity leaves free. -/
theorem asymmetricFst_at_balancing_migration :
    asymmetricFst 1 (1 / 8) (1 / 8) = 1 / 2 := by
  unfold asymmetricFst
  norm_num

/-- **There is no direction. Swapping the two rates changes nothing.**

    This replaces `asymmetric_migration_directional_fst`, which asserted the
    opposite -- that when `m₁₂ > m₂₁` the `F_ST` "from population 1's
    perspective" is strictly lower -- and which was excluded by measurement. The
    design that excludes it is in the docstring above: three deme pairs sharing a
    total exchange rate of `2.0e-3` while running from mild to strong asymmetry
    agree with each other to 1.4 sems, where the directional reading requires
    them to span a factor of four and a half.

    A definition that returns different numbers for `(m₁₂, m₂₁)` and
    `(m₂₁, m₁₂)` is making a claim, and it is not enough to note that the claim
    is now absent from the body: stating the symmetry is what stops the
    directional reading being reintroduced by someone who reads the name. -/
theorem asymmetricFst_symm (Ne m₁₂ m₂₁ : ℝ) :
    asymmetricFst Ne m₁₂ m₂₁ = asymmetricFst Ne m₂₁ m₁₂ := by
  unfold asymmetricFst
  ring_nf

/-- **Portability does not depend on the prediction direction under asymmetric migration.**

    The superseded `asymmetric_migration_portability_direction` said it does:
    that predicting into the deme receiving more migrants yields a strictly
    higher `R²`. That was a consequence of the directional `F_ST`, and it goes
    with it. Drift degrades `R²` through `F_ST` alone, and `F_ST` here is a
    property of the pair, so the two directions are worth exactly the same. -/
theorem asymmetric_migration_portability_directionless
    (V_A V_E Ne m₁₂ m₂₁ : ℝ) :
    presentDayR2 V_A V_E (asymmetricFst Ne m₂₁ m₁₂) =
      presentDayR2 V_A V_E (asymmetricFst Ne m₁₂ m₂₁) := by
  rw [asymmetricFst_symm]

/-- **The arithmetic mean used here is never below the harmonic mean**, with equality
exactly when the two directional rates agree. This is AM-GM-HM for two positive reals, and
it fixes the sign of the discrepancy between the two means. -/
theorem harmonicMigrationMean_le_effectiveSymmetricMigration (m₁₂ m₂₁ : ℝ)
    (h₁ : 0 < m₁₂) (h₂ : 0 < m₂₁) :
    2 * m₁₂ * m₂₁ / (m₁₂ + m₂₁) ≤ effectiveSymmetricMigration m₁₂ m₂₁ := by
  unfold effectiveSymmetricMigration Descent.Core.midpoint
  rw [div_le_div_iff₀ (by linarith) (by norm_num : (0:ℝ) < 2)]
  nlinarith [sq_nonneg (m₁₂ - m₂₁)]

/-- **And equality forces the two directional rates to agree**, which is what the
statement above claims and does not prove on its own. Together they are the
equality case of the arithmetic-harmonic mean inequality: symmetrising two
migration rates loses nothing exactly when there was nothing asymmetric to
lose. -/
theorem harmonicMigrationMean_eq_iff_symmetric (m₁₂ m₂₁ : ℝ)
    (h₁ : 0 < m₁₂) (h₂ : 0 < m₂₁)
    (heq : 2 * m₁₂ * m₂₁ / (m₁₂ + m₂₁) = effectiveSymmetricMigration m₁₂ m₂₁) :
    m₁₂ = m₂₁ := by
  have hsum : (0 : ℝ) < m₁₂ + m₂₁ := by linarith
  have hne : m₁₂ + m₂₁ ≠ 0 := ne_of_gt hsum
  unfold effectiveSymmetricMigration Descent.Core.midpoint at heq
  field_simp at heq
  have hsq : (m₁₂ - m₂₁) ^ 2 = 0 := by nlinarith [heq]
  have hzero : m₁₂ - m₂₁ = 0 := sq_eq_zero_iff.mp hsq
  linarith

/-- **Hence the equilibrium `F_ST` computed from this mean is never above the one the
harmonic mean would give.** `fstMigrationDriftEquilibrium` is decreasing in the migration
rate, so substituting the larger mean returns the smaller `F_ST`. Composed with `presentDayR2`,
which is decreasing in `F_ST`, the arithmetic mean is the optimistic
choice at every pair of asymmetric rates: it reports better cross-population portability
than the harmonic mean does. Stated so the direction of the bias is checkable rather than
left in prose. -/
theorem effectiveSymmetricMigration_fst_le_harmonic_fst (Ne m₁₂ m₂₁ : ℝ)
    (hNe : 0 < Ne) (h₁ : 0 < m₁₂) (h₂ : 0 < m₂₁) :
    fstMigrationDriftEquilibrium Ne (effectiveSymmetricMigration m₁₂ m₂₁) ≤
      fstMigrationDriftEquilibrium Ne (2 * m₁₂ * m₂₁ / (m₁₂ + m₂₁)) := by
  unfold fstMigrationDriftEquilibrium Descent.Core.fstFromFlow
  have hHM_pos : 0 < 2 * m₁₂ * m₂₁ / (m₁₂ + m₂₁) := by positivity
  have hle := harmonicMigrationMean_le_effectiveSymmetricMigration m₁₂ m₂₁ h₁ h₂
  have hden_pos : 0 < 1 + 4 * Ne * (2 * m₁₂ * m₂₁ / (m₁₂ + m₂₁)) := by positivity
  exact one_div_le_one_div_of_le hden_pos (by nlinarith)

/-- The arithmetic mean of two distinct rates lies strictly between them. -/
theorem effectiveSymmetricMigration_between (m₁₂ m₂₁ : ℝ)
    (h_asym : m₂₁ < m₁₂) :
    m₂₁ < effectiveSymmetricMigration m₁₂ m₂₁ ∧
    effectiveSymmetricMigration m₁₂ m₂₁ < m₁₂ := by
  unfold effectiveSymmetricMigration Descent.Core.midpoint
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
  Descent.Core.geometricDecay r generations_since

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
  unfold admixtureLDDecay Descent.Core.geometricDecay
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
    admixtureLDDecay r t = PopGen.discreteRecombinationSurvival r t := rfl

/-- Admixture LD decay is nonneg for recombination rate in [0, 1]. -/
theorem admixtureLDDecay_nonneg (r : ℝ) (t : ℕ)
    (hr1 : r ≤ 1) :
    0 ≤ admixtureLDDecay r t := by
  unfold admixtureLDDecay Descent.Core.geometricDecay
  exact pow_nonneg (by linarith) t

/-- Admixture LD decay is at most 1 for valid recombination rate. -/
theorem admixtureLDDecay_le_one (r : ℝ) (t : ℕ)
    (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    admixtureLDDecay r t ≤ 1 := by
  unfold admixtureLDDecay Descent.Core.geometricDecay
  exact pow_le_one₀ (by linarith) (by linarith)

/-- **Admixture LD decays over time** (for positive recombination rate). -/
theorem admixtureLDDecay_decreases_with_time (r : ℝ) (t₁ t₂ : ℕ)
    (hr : 0 < r) (hr1 : r < 1) (ht : t₁ < t₂) :
    admixtureLDDecay r t₂ < admixtureLDDecay r t₁ := by
  unfold admixtureLDDecay Descent.Core.geometricDecay
  have h_base_pos : 0 < 1 - r := by linarith
  have h_base_lt : 1 - r < 1 := by linarith
  exact pow_lt_pow_right_of_lt_one₀ h_base_pos h_base_lt ht

/-- **Admixture LD decays faster with higher recombination rate.** -/
theorem admixtureLDDecay_decreases_with_recombination (r₁ r₂ : ℝ) (t : ℕ)
    (hr₂1 : r₂ < 1)
    (h_more : r₁ < r₂) (ht : 0 < t) :
    admixtureLDDecay r₂ t < admixtureLDDecay r₁ t := by
  unfold admixtureLDDecay Descent.Core.geometricDecay
  exact pow_lt_pow_left₀ (by linarith : 1 - r₂ < 1 - r₁) (by linarith) (by omega)

/-- **At time 0 since admixture, LD is fully preserved.** -/
theorem admixtureLDDecay_at_zero (r : ℝ) :
    admixtureLDDecay r 0 = 1 := by
  unfold admixtureLDDecay Descent.Core.geometricDecay
  simp

/-- **Admixture LD creates a transient boost to portability.**
    Recent admixture (small t since pulse) means LD patterns are shared,
    which temporarily improves tagging efficiency. The portability boost
    from admixture LD relative to equilibrium LD is captured by the ratio
    of admixture LD retention to equilibrium LD fraction.

    Regime: a one-pulse admixture event, read from the pulse forward.
    `equilibrium_ld` is an INPUT and not modelled here, so what a simulation can
    put on trial is the numerator and the fact that the body is a ratio in it --
    not the baseline's value.

    Empirical status: **VALIDATED** (`simcov/battery_bulk20c.py`, `group_d`).
    A 50/50 pulse into a Wright-Fisher population at `Nₑ = 2000`, then
    recombination and drift for 40 generations, over 400 independent
    replicates; the observable is `E[D_t] / E[D_0]` divided by a baseline held
    at 0.25. Across `r` = 0.005, 0.02, 0.05, 0.15 and `t` = 10, 40 the body
    predicts 3.80444, 3.27327, 3.26828, 1.78280, 2.39497, 0.51402, 0.78749 and
    0.00602 against measured 3.83190 ± 0.02512, 3.26726 ± 0.04721, 3.28631 ±
    0.02277, 1.79945 ± 0.03596, 2.41661 ± 0.02143, 0.46521 ± 0.02707, 0.77093 ±
    0.01663 and 0.01927 ± 0.01690, worst cell 1.80 sems.

    Power: the prediction spans the full range from a 3.8-fold boost down to
    essentially none -- three orders of magnitude -- and `r` and `t` are moved
    separately, so the two cells that reach a similar boost by different routes
    both have to hold. Control: the finite-`Nₑ` retention
    `((1-r)(1 - 1/(2Nₑ)))^t`, derived independently of this body, passed on the
    same code path. -/
noncomputable def admixtureLDBoost (r : ℝ) (t_since : ℕ) (equilibrium_ld : ℝ) : ℝ :=
  admixtureLDDecay r t_since / equilibrium_ld

/-- **admixtureLDBoost at zero equilibrium_ld, named.** A zero equilibrium linkage disequilibrium
gives no baseline for the boost to be measured against. Lean returns `0`, reporting no excess
disequilibrium from admixture, in exactly the situation where any disequilibrium at all is
entirely due to admixture. Consumers must require `equilibrium_ld ≠ 0`. -/
theorem admixtureLDBoost_zero_equilibriumld_is_junk (r : ℝ) (t_since : ℕ) :
    admixtureLDBoost r t_since 0 = 0 := by
  unfold admixtureLDBoost
  simp

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

theorem effectiveSymmetricMigration_eq_meanAlleleFreq_map (m₁₂ m₂₁ : ℝ) :
    effectiveSymmetricMigration m₁₂ m₂₁ = Descent.Core.meanAlleleFreq m₁₂ m₂₁ := by
  unfold effectiveSymmetricMigration Descent.Core.meanAlleleFreq Descent.Core.midpoint;
    ring

/-- **The migration-drift equilibrium is the flow map at the scaled MIGRATION rate.**

This used to read `= PopGen.fstMutationDriftEquilibrium (scaledMigrationRate Ne m)`, and it
stopped elaborating the moment `fstMutationDriftEquilibrium` began taking a `Core.Theta`.
The type was right and the statement was wrong: it fed a scaled MIGRATION rate to the
MUTATION-drift law, which is the exact substitution `Core/Scaling.lean` was built after --
`theta_bigM_share_constant` says the two carry the same number at equal rates, so nothing
about the value objected and nothing ever would have.

What is true, and is what this now says, is that both are `Core.fstFromFlow`: one map,
`1/(1 + x)`, applied to two different flows. The shared content is the map. -/
theorem fstMigrationDriftEquilibrium_eq_scaled (Ne m : ℝ) :
    fstMigrationDriftEquilibrium Ne m =
      Descent.Core.fstFromFlow (Descent.Core.scaledMigrationRate Ne m) := by
  unfold fstMigrationDriftEquilibrium Descent.Core.fstFromFlow
  rw [Descent.Core.scaledMigrationRate_eq_ploidy_form]; unfold Descent.Core.ploidy; ring_nf

/-- **And the asymmetric two-deme `F_ST` is the same map at the summed migration rate.**
Restated through `Core.fstFromFlow` for the reason given on
`fstMigrationDriftEquilibrium_eq_scaled` directly above. -/
theorem asymmetricFst_eq_scaled (Ne m₁₂ m₂₁ : ℝ) :
    Portability.asymmetricFst Ne m₁₂ m₂₁
      = Descent.Core.fstFromFlow (Descent.Core.scaledMigrationRate Ne (m₁₂ + m₂₁)) := by
  unfold Portability.asymmetricFst Descent.Core.fstFromFlow
  rw [Descent.Core.scaledMigrationRate_eq_ploidy_form]; unfold Descent.Core.ploidy; ring_nf

/-- **The multiplicative identity recurrence carries the same coalescent scale.** -/
theorem ibdRecurrenceStep_uses_coalescentTimeScale (Ne rate x : ℝ) :
    ibdRecurrenceStep Ne rate x
      = (1 - rate) ^ 2 * (1 / Descent.Core.coalescentTimeScale Ne
          + (1 - 1 / Descent.Core.coalescentTimeScale Ne) * x) := by
  unfold ibdRecurrenceStep Descent.Core.survivalWeightedMix; rw
    [Descent.Core.coalescentTimeScale_eq]

/-- **The rest point of that recurrence carries it too**, in both of its constants: the
`2 Nₑ` is the coalescent time scale and the `2 - rate` is `ploidy - rate`, the two lineages
less the one disrupting event they share. -/
theorem ibdRecurrenceFixedPoint_uses_coalescentTimeScale (Ne rate : ℝ) :
    ibdRecurrenceFixedPoint Ne rate
      = (1 - rate) ^ 2
          / ((1 - rate) ^ 2 + Descent.Core.coalescentTimeScale Ne * rate * (Descent.Core.ploidy -
            rate)) := by
  unfold ibdRecurrenceFixedPoint Descent.Core.ploidy; rw
    [Descent.Core.coalescentTimeScale_eq]

end Descent.Portability
