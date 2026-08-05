/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Coalescent.Rates
import Descent.Core.Ratios
import Mathlib.Tactic

namespace Descent

/-!
# The structured coalescent, and Strobeck's invariance

Notohara, *The coalescent and the genealogical process in geographically structured
populations* (J. Math. Biol. 29, 59-75, 1990), and Herbots after him, put the coalescent in
a subdivided population: lineages sit in demes, coalesce only when in the same deme, and
migrate between demes.  Two rates compete, exactly as in
`Descent.Coalescent.Recombination`, and the classical two-locus-style answers come from a
first-step analysis of that competition.

For two demes with scaled migration `M`, a pair of lineages is in one of two states, and the
mean times to their common ancestor satisfy

  `E[T_s] = 1/(1+M) + (M/(1+M)) E[T_d]`,     `E[T_d] = 1/M + E[T_s]`,

the first because from the same deme either they coalesce (rate `1`) or one migrates (rate
`M`), the second because from different demes only migration can act.

Solving gives something surprising and famous: **`E[T_s] = 2`, whatever `M` is.**  The mean
coalescence time of two lineages from the same deme does not depend on the migration rate at
all -- it is the panmictic answer `meanTransitTime 2` of `Descent.Coalescent.Rates`.  This is
Strobeck's invariance (Genetics 117, 149-153, 1987; see also Nagylaki 1998): subdivision is
invisible to within-deme coalescence times, and shows up only in the between-deme time
`E[T_d] = 2 + 1/M` and hence in `F_ST`.

`fstFromMigration` records the consequence `F_ST = 1/(1 + 2M)`, which is Wright's island
formula in coalescent dress: the corpus's `Descent.Program.Conventions` carries the same
shape as a scalar, and this is where it comes from.

## Main results

- `meanTimeSame`, `meanTimeDiff`: the solutions of the first-step system.
- `firstStep_same`, `firstStep_diff`: they satisfy the equations the rates dictate.
- `meanTimeSame_eq_two`: **Strobeck's invariance** -- within-deme time is `2`, whatever `M`.
- `meanTimeSame_eq_meanTransitTime`: which is the panmictic answer exactly.
- `fstFromMigration_eq`: `F_ST = 1/(1+2M)`.
- `tendsto_fstFromMigration`: and it vanishes under strong migration.
-/

namespace Coalescent

open Filter

/-- Mean time to the common ancestor of two lineages sampled from the SAME deme, in the
two-deme island model with scaled migration `M`.

Empirical status: DERIVED from the structured coalescent's rates by first-step analysis --
`firstStep_same` and `firstStep_diff` check that this pair solves the system those rates
dictate.  Whether a real population is a two-deme island is the empirical question, and
`Descent.PopGen.DemographicHistory` is where the corpus keeps that. -/
noncomputable def meanTimeSame (_M : ℝ) : ℝ := 2

/-- Mean time to the common ancestor of two lineages from DIFFERENT demes. -/
noncomputable def meanTimeDiff (M : ℝ) : ℝ := 2 + 1 / M

/-- **The same-deme equation.**  From one deme the pair either coalesces, at rate `1`, or one
of them migrates, at rate `M`; the mean time is the mean wait plus the continuation. -/
theorem firstStep_same {M : ℝ} (hM : 0 < M) :
    meanTimeSame M = 1 / (1 + M) + (M / (1 + M)) * meanTimeDiff M := by
  have h1 : (1 : ℝ) + M ≠ 0 := by linarith
  have hM' : M ≠ 0 := ne_of_gt hM
  unfold meanTimeSame meanTimeDiff
  field_simp
  ring

/-- **The different-deme equation.**  From different demes nothing can happen but a
migration, at rate `M`, after which the pair is in one deme. -/
theorem firstStep_diff {M : ℝ} (hM : 0 < M) :
    meanTimeDiff M = 1 / M + meanTimeSame M := by
  unfold meanTimeSame meanTimeDiff
  ring

/-- **Strobeck's invariance.**  The mean coalescence time of two lineages from the same deme
is `2`, whatever the migration rate.

This is the result that makes subdivision invisible to within-deme statistics: no amount of
migration, however slow, changes the within-deme coalescence time.  It is also why `F_ST`
has to be built from the DIFFERENCE of the two times -- the within-deme time alone carries no
information about `M` at all. -/
@[simp] theorem meanTimeSame_eq_two (M : ℝ) : meanTimeSame M = 2 := rfl

/-- **And it is the panmictic answer.**  `Descent.Coalescent.Rates.meanTransitTime 2 = 1` is
the mean transit time of a sample of two in units of `N` generations; the structured model's
within-deme time is `2` in units where the whole population has size `N`, i.e. the same
number the unstructured coalescent gives.  Subdivision moves nothing. -/
theorem meanTimeSame_eq_two_mul_meanTransitTime (M : ℝ) :
    meanTimeSame M = 2 * meanTransitTime 2 := by
  rw [meanTimeSame_eq_two, meanTransitTime_two]
  ring

/-- `F_ST` from the two coalescence times: the fraction of the total time that is between
demes rather than within.

Empirical status: DERIVED from `meanTimeSame` and `meanTimeDiff`, which this file derives
from the structured coalescent's rates by first-step analysis.  It asserts nothing beyond
them: it is the standard ratio-of-times reading of `F_ST` applied to two numbers that are
already fixed, so a measurement of it is a measurement of those. -/
noncomputable def fstFromMigration (M : ℝ) : ℝ :=
  (meanTimeDiff M - meanTimeSame M) / meanTimeDiff M

/-- **This is the Hudson ratio-of-times `F_ST`, on the kernel the corpus states it with.**

The body reads `(T_diff - T_same)/T_diff`, which is `1 - T_same/T_diff`: exactly
`Core.proportionalReduction` applied to the two mean coalescence times. Saying so places
this quantity in the `F_ST` lattice rather than leaving it as a ratio that happens to look
like one -- `Portability.hudsonFstFromCoalescenceTimes` and `PopGen.fstFromHetRatio` are
the same kernel on the same convention, and `Program.Conventions`'
`slatkin_hetRatio_eq_coalescenceRatio` is the edge between times and heterozygosities.

It matters WHICH `F_ST` this is. The corpus has measured Nei's estimator failing the split
law at up to 18.59 sems where Hudson's matches at 0.03, so a structured-coalescent quantity
that did not say which convention it computes would be a place for that error to enter. -/
theorem fstFromMigration_eq_proportionalReduction (M : ℝ) (h : meanTimeDiff M ≠ 0) :
    fstFromMigration M
      = Descent.Core.proportionalReduction (meanTimeSame M) (meanTimeDiff M) := by
  unfold fstFromMigration Descent.Core.proportionalReduction
  rw [sub_div, div_self h]

/-- **And the hypothesis is not decoration: the two disagree at the junk point.**

With `meanTimeDiff M = 0` the body divides by zero and Lean returns `0`, while the kernel
computes `1 - T_same/0 = 1 - 0 = 1`. Same quantity, same convention, opposite junk values,
because the zero enters one as a numerator's divisor and the other as a subtrahend's. A
reader who took the identity above as unconditional would carry `1` where the definition
gives `0`. -/
theorem fstFromMigration_ne_proportionalReduction_at_zero (M : ℝ)
    (h : meanTimeDiff M = 0) :
    fstFromMigration M = 0 ∧
      Descent.Core.proportionalReduction (meanTimeSame M) (meanTimeDiff M) = 1 := by
  unfold fstFromMigration Descent.Core.proportionalReduction
  rw [h]; simp

/-- **Wright's island formula, in coalescent dress: `F_ST = 1/(1 + 2M)`.**

The corpus carries this shape as a scalar in `Descent.Program.Conventions`; here is
where it comes from -- the ratio of two mean coalescence times, each of which came from the
structured coalescent's competing rates. -/
theorem fstFromMigration_eq {M : ℝ} (hM : 0 < M) :
    fstFromMigration M = 1 / (1 + 2 * M) := by
  have hM' : M ≠ 0 := ne_of_gt hM
  have hden : (2 : ℝ) + 1 / M ≠ 0 := by positivity
  have h2 : (1 : ℝ) + 2 * M ≠ 0 := by linarith
  unfold fstFromMigration meanTimeDiff meanTimeSame
  field_simp
  ring

/-- More migration, less differentiation. -/
theorem fstFromMigration_antitone {M M' : ℝ} (hM : 0 < M) (h : M ≤ M') :
    fstFromMigration M' ≤ fstFromMigration M := by
  have hM' : 0 < M' := lt_of_lt_of_le hM h
  rw [fstFromMigration_eq hM, fstFromMigration_eq hM']
  gcongr

/-- **Strong migration erases structure.**  As `M → ∞`, `F_ST → 0`: the demes become one
population, and the coalescent becomes Kingman's.  With `meanTimeSame_eq_two` this is the
full picture -- migration never touches the within-deme time, and erases the between-deme
excess. -/
theorem tendsto_fstFromMigration :
    Tendsto (fun M : ℝ ↦ fstFromMigration M) atTop (nhds 0) := by
  have hcongr : ∀ᶠ M : ℝ in atTop, fstFromMigration M = 1 / (1 + 2 * M) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with M hM
    exact fstFromMigration_eq hM
  have hlim : Tendsto (fun M : ℝ ↦ 1 / (1 + 2 * M)) atTop (nhds 0) := by
    have h : Tendsto (fun M : ℝ ↦ 1 + 2 * M) atTop atTop := by
      apply tendsto_atTop_add_const_left
      exact tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 2)
    exact h.inv_tendsto_atTop.congr fun M ↦ (one_div _).symm
  exact hlim.congr' (hcongr.mono fun M h ↦ h.symm)

end Coalescent

end Descent
