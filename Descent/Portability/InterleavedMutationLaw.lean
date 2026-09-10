/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.OrderedMutationCatalogue

assert_below Descent.Decision Descent.Program

/-!
Chronologically interleaved mutations on the contemporaneous branches of one
ancestry interval. Each proposal selects a branch proportionally to its
mutation exposure and performs one JC69 mutation with ordered catalogue
memory. A unit of null-proposal exposure permits the same normalized formula
when every mutation exposure is zero. Null proposals leave all state intact.

The generator below is derived from the individual branch exposures. This
differs from completing all mutations on one branch before moving to another:
the global mutation order determines the allele-discovery catalogue.

Primary implementation reference for new mutation ordering:
https://github.com/tskit-dev/msprime/blob/996f12d83a5231533fbb2f94c4684817709b79b9/lib/mutgen.c
The comparator sorts new mutations by decreasing time. This is an immutable
source reference, not an assertion that the simulation used this version.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.InterleavedMutationLaw

open FiniteReportLaw GenealogyGenotypeLaw OrderedMutationCatalogue ProbabilityTheory
open AncestralEpochLaw
open scoped NNReal

variable {n count : ℕ}

noncomputable def totalExposure (branches : Fin count → Branch n) : ℝ≥0 :=
  ∑ index, (branches index).exposure

noncomputable def proposalParameter (branches : Fin count → Branch n) : ℝ≥0 :=
  1 + totalExposure branches

theorem proposalParameter_pos (branches : Fin count → Branch n) :
    0 < (proposalParameter branches : ℝ) := by
  simp only [proposalParameter, NNReal.coe_add, NNReal.coe_one]
  positivity

theorem proposalParameter_eq (branches : Fin count → Branch n) :
    (proposalParameter branches : ℝ) = 1 + ∑ index, ((branches index).exposure : ℝ) := by
  simp [proposalParameter, totalExposure]

noncomputable def markLaw (branches : Fin count → Branch n) :
    FiniteReportLaw (Option (Fin count)) where
  mass := fun mark ↦ match mark with
    | none => 1 / (proposalParameter branches : ℝ)
    | some index => ((branches index).exposure : ℝ) / (proposalParameter branches : ℝ)
  mass_nonneg := by
    intro mark
    cases mark with
    | none => exact div_nonneg zero_le_one (proposalParameter_pos branches).le
    | some index =>
      exact div_nonneg (branches index).exposure.property
        (proposalParameter_pos branches).le
  mass_sum := by
    rw [Fintype.sum_option, ← Finset.sum_div, ← add_div,
      ← proposalParameter_eq branches, div_self (ne_of_gt (proposalParameter_pos branches))]

noncomputable def markedKernel (branches : Fin count → Branch n) (state : SiteState n) :
    Option (Fin count) → FiniteReportLaw (SiteState n)
  | none => pointMass state
  | some index => mutationKernel (branches index) state

def markWeight (weights : Fin count → ℝ) : Option (Fin count) → ℝ
  | none => 1
  | some index => weights index

theorem mark_expectation (branches : Fin count → Branch n) (weights : Fin count → ℝ) :
    (markLaw branches).expectation (markWeight weights) =
      (1 + ∑ index, ((branches index).exposure : ℝ) * weights index) /
        (proposalParameter branches : ℝ) := by
  unfold expectation markLaw markWeight
  rw [Fintype.sum_option]
  dsimp only
  simp only [mul_one, div_mul_eq_mul_div, ← Finset.sum_div, ← add_div]

noncomputable def markHistoryMass (branches : Fin count → Branch n) (proposals : ℕ)
    (history : Fin proposals → Option (Fin count)) : ℝ :=
  ∏ position, (markLaw branches).mass (history position)

theorem markHistory_normalized (branches : Fin count → Branch n) (proposals : ℕ) :
    (∑ history : Fin proposals → Option (Fin count), markHistoryMass branches proposals history) =
      1 := by
  unfold markHistoryMass
  rw [← Fintype.prod_sum]
  simp only [FiniteReportLaw.mass_sum, Finset.prod_const_one]

theorem markHistory_generating_function (branches : Fin count → Branch n)
    (weights : Fin count → ℝ) (proposals : ℕ) :
    (∑ history : Fin proposals → Option (Fin count),
      markHistoryMass branches proposals history *
        ∏ position, markWeight weights (history position)) =
      ((1 + ∑ index, ((branches index).exposure : ℝ) * weights index) /
        (proposalParameter branches : ℝ)) ^ proposals := by
  unfold markHistoryMass
  simp only [← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun (_ : Fin proposals) (mark : Option (Fin count)) ↦
    (markLaw branches).mass mark * markWeight weights mark)]
  have h := mark_expectation branches weights
  unfold expectation at h
  simp only [h, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- The exact multivariate count generating function factors into the Poisson
generating functions for the individual branch exposures. The chronological
mark sequence above is retained before these counts are marginalized. -/
theorem poisson_mark_generating_function (branches : Fin count → Branch n)
    (weights : Fin count → ℝ) :
    (∑' proposals, poissonPMFReal (proposalParameter branches) proposals *
      ∑ history : Fin proposals → Option (Fin count),
        markHistoryMass branches proposals history *
          ∏ position, markWeight weights (history position)) =
      ∏ index, Real.exp (((branches index).exposure : ℝ) * (weights index - 1)) := by
  simp only [markHistory_generating_function]
  rw [poisson_generating_function, ← Real.exp_sum]
  congr 1
  have hp := ne_of_gt (proposalParameter_pos branches)
  rw [mul_sub, mul_div_cancel₀ _ hp, mul_one, proposalParameter_eq]
  simp only [mul_sub, mul_one, Finset.sum_sub_distrib]
  ring

noncomputable def intervalKernel (branches : Fin count → Branch n) (state : SiteState n) :
    FiniteReportLaw (SiteState n) :=
  (markLaw branches).bind (markedKernel branches state)

theorem intervalKernel_expectation (branches : Fin count → Branch n) (state : SiteState n)
    (readout : SiteState n → ℝ) :
    (intervalKernel branches state).expectation readout =
      (readout state + ∑ index, ((branches index).exposure : ℝ) *
        (mutationKernel (branches index) state).expectation readout) /
          (proposalParameter branches : ℝ) := by
  rw [intervalKernel, expectation_bind]
  unfold expectation markLaw markedKernel
  rw [Fintype.sum_option]
  dsimp only
  have hp : (∑ target, (pointMass state).mass target * readout target) = readout state :=
    expectation_pointMass state readout
  rw [hp]
  simp only [div_mul_eq_mul_div, one_mul, ← Finset.sum_div, ← add_div]

/-- The finite proposal kernel has exactly the sum of all branch mutation
generators. The extra null proposals disappear from this identity. -/
theorem interval_generator (branches : Fin count → Branch n) (state : SiteState n)
    (readout : SiteState n → ℝ) :
    (proposalParameter branches : ℝ) *
        ((intervalKernel branches state).expectation readout - readout state) =
      ∑ index, ((branches index).exposure : ℝ) *
        ((mutationKernel (branches index) state).expectation readout - readout state) := by
  rw [intervalKernel_expectation]
  have hp := ne_of_gt (proposalParameter_pos branches)
  rw [mul_sub, mul_div_cancel₀ _ hp, proposalParameter_eq]
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
  ring

noncomputable def countLaw (branches : Fin count → Branch n) (state : SiteState n)
    (proposals : ℕ) : FiniteReportLaw (SiteState n) :=
  ExactFiniteHistoryLaw.propagate (pointMass state) (fun _ ↦ intervalKernel branches) proposals

private theorem coordinate_summable (branches : Fin count → Branch n)
    (state target : SiteState n) :
    Summable (fun proposals ↦ poissonPMFReal (proposalParameter branches) proposals *
      (countLaw branches state proposals).mass target) := by
  apply (poissonPMFRealSum (proposalParameter branches)).summable.of_nonneg_of_le
  · intro proposals
    exact mul_nonneg poissonPMFReal_nonneg ((countLaw branches state proposals).mass_nonneg target)
  · intro proposals
    have hmass : (countLaw branches state proposals).mass target ≤ 1 := by
      rw [← (countLaw branches state proposals).mass_sum]
      exact Finset.single_le_sum (fun output _ ↦
        (countLaw branches state proposals).mass_nonneg output) (Finset.mem_univ target)
    exact mul_le_of_le_one_right poissonPMFReal_nonneg hmass

/-- Complete finite site-state law for the interval, summing all possible
interleavings and all possible mutation counts. Branch exposure already
includes the interval duration times the per-site mutation rate. -/
noncomputable def intervalLaw (branches : Fin count → Branch n) (state : SiteState n) :
    FiniteReportLaw (SiteState n) where
  mass := fun target ↦ ∑' proposals, poissonPMFReal (proposalParameter branches) proposals *
    (countLaw branches state proposals).mass target
  mass_nonneg := fun target ↦ tsum_nonneg (fun proposals ↦
    mul_nonneg poissonPMFReal_nonneg ((countLaw branches state proposals).mass_nonneg target))
  mass_sum := by
    rw [← Summable.tsum_finsetSum (fun target _ ↦ coordinate_summable branches state target)]
    simp only [← Finset.mul_sum, FiniteReportLaw.mass_sum, mul_one]
    exact (poissonPMFRealSum (proposalParameter branches)).tsum_eq

theorem interval_expectation (branches : Fin count → Branch n) (state : SiteState n)
    (readout : SiteState n → ℝ) :
    (intervalLaw branches state).expectation readout =
      ∑' proposals, poissonPMFReal (proposalParameter branches) proposals *
        (countLaw branches state proposals).expectation readout := by
  unfold expectation intervalLaw
  simp only [← tsum_mul_right]
  rw [← Summable.tsum_finsetSum (fun target _ ↦
    (coordinate_summable branches state target).mul_right (readout target))]
  apply tsum_congr
  intro proposals
  simp only [Finset.mul_sum, mul_assoc]

theorem intervalKernel_unsupported (branches : Fin count → Branch n)
    (state target : SiteState n) (hstate : Covered state) (htarget : ¬ Covered target) :
    (intervalKernel branches state).mass target = 0 := by
  classical
  have hne : target ≠ state := by intro heq; exact htarget (heq ▸ hstate)
  unfold intervalKernel FiniteReportLaw.bind
  dsimp only
  rw [Fintype.sum_option]
  simp [markedKernel, pointMass, hne,
    mutationKernel_unsupported _ state target hstate htarget]

theorem count_unsupported (branches : Fin count → Branch n)
    (state target : SiteState n) (hstate : Covered state) (htarget : ¬ Covered target)
    (proposals : ℕ) : (countLaw branches state proposals).mass target = 0 := by
  classical
  induction proposals generalizing target with
  | zero =>
      have hne : target ≠ state := by intro heq; exact htarget (heq ▸ hstate)
      simp [countLaw, ExactFiniteHistoryLaw.propagate, pointMass, hne]
  | succ proposals ih =>
      change ∑ middle, (countLaw branches state proposals).mass middle *
        (intervalKernel branches middle).mass target = 0
      apply Finset.sum_eq_zero
      intro middle _
      by_cases hm : Covered middle
      · rw [intervalKernel_unsupported branches middle target hm htarget, mul_zero]
      · rw [ih middle hm, zero_mul]

/-- Every positive-mass outcome admits valid catalogue decoding into allele
indices, even after arbitrarily many chronologically interleaved mutations. -/
theorem interval_covered (branches : Fin count → Branch n) (state target : SiteState n)
    (hstate : Covered state) (hpositive : 0 < (intervalLaw branches state).mass target) :
    Covered target := by
  by_contra htarget
  have hzero : (intervalLaw branches state).mass target = 0 := by
    simp [intervalLaw, count_unsupported branches state target hstate htarget]
  rw [hzero] at hpositive
  exact lt_irrefl 0 hpositive

/-- The raw diploid allele-index dosage has a finite conditional expectation
bounded by six. This bound uses the proved support invariant, since arbitrary
unreachable site states need not have every leaf base in their catalogue. -/
theorem interval_rawDosage_bounds (branches : Fin count → Branch n) (state : SiteState n)
    (hstate : Covered state) (first second : Fin n) :
    0 ≤ (intervalLaw branches state).expectation
        (fun output ↦ (rawDosage output first second : ℝ)) ∧
      (intervalLaw branches state).expectation
        (fun output ↦ (rawDosage output first second : ℝ)) ≤ 6 := by
  constructor
  · exact Finset.sum_nonneg (fun output _ ↦
      mul_nonneg ((intervalLaw branches state).mass_nonneg output) (Nat.cast_nonneg _))
  · have hnorm : (∑ output, (intervalLaw branches state).mass output * 6) = 6 := by
      rw [← Finset.sum_mul, FiniteReportLaw.mass_sum, one_mul]
    rw [← hnorm]
    apply Finset.sum_le_sum
    intro output _
    by_cases hcovered : Covered output
    · have hbound : (rawDosage output first second : ℝ) ≤ 6 := by
        exact_mod_cast rawDosage_le_six output hcovered first second
      exact mul_le_mul_of_nonneg_left hbound
        ((intervalLaw branches state).mass_nonneg output)
    · have hzero : (intervalLaw branches state).mass output = 0 := by
        simp [intervalLaw, count_unsupported branches state output hstate hcovered]
      simp [hzero]

theorem zero_exposure_kernel (branches : Fin count → Branch n)
    (hzero : ∀ index, (branches index).exposure = 0) (state : SiteState n) :
    intervalKernel branches state = pointMass state := by
  apply (eq_iff_singleton_expectations_eq _ _).mpr
  intro target
  rw [intervalKernel_expectation, expectation_pointMass]
  simp [hzero, proposalParameter, totalExposure]

theorem zero_exposure_count (branches : Fin count → Branch n)
    (hzero : ∀ index, (branches index).exposure = 0) (state : SiteState n) (proposals : ℕ) :
    countLaw branches state proposals = pointMass state := by
  induction proposals with
  | zero => rfl
  | succ proposals ih =>
      apply (eq_iff_singleton_expectations_eq _ _).mpr
      intro target
      change ((countLaw branches state proposals).bind (intervalKernel branches)).expectation _ = _
      rw [expectation_bind, ih, expectation_pointMass, zero_exposure_kernel branches hzero]

/-- Null uniformization proposals create no mutations when the physical
mutation exposures vanish. The complete law is exactly deterministic. -/
theorem zero_exposure_interval (branches : Fin count → Branch n)
    (hzero : ∀ index, (branches index).exposure = 0) (state : SiteState n) :
    intervalLaw branches state = pointMass state := by
  apply (eq_iff_singleton_expectations_eq _ _).mpr
  intro target
  rw [interval_expectation]
  simp only [zero_exposure_count branches hzero, expectation_pointMass]
  rw [tsum_mul_right, (poissonPMFRealSum (proposalParameter branches)).tsum_eq, one_mul]

def absentReadout (state : SiteState n) : ℝ := if state.2.2 then 0 else 1

theorem kernel_absence (branches : Fin count → Branch n) (state : SiteState n) :
    (intervalKernel branches state).expectation absentReadout =
      1 / (proposalParameter branches : ℝ) * absentReadout state := by
  rw [intervalKernel_expectation]
  have hmutation (index : Fin count) :
      (mutationKernel (branches index) state).expectation absentReadout = 0 := by
    rw [mutationKernel, expectation_pushforward]
    simp [expectation, absentReadout, recordMutation]
  simp [hmutation, div_eq_mul_inv, mul_comm]

private theorem expectation_const_mul (law : FiniteReportLaw (SiteState n))
    (factor : ℝ) (readout : SiteState n → ℝ) :
    law.expectation (fun output ↦ factor * readout output) = factor * law.expectation readout := by
  simp only [expectation, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro output _
  ring

theorem count_absence (branches : Fin count → Branch n) (state : SiteState n)
    (proposals : ℕ) :
    (countLaw branches state proposals).expectation absentReadout =
      (1 / (proposalParameter branches : ℝ)) ^ proposals * absentReadout state := by
  induction proposals with
  | zero => simp [countLaw, ExactFiniteHistoryLaw.propagate, expectation_pointMass]
  | succ proposals ih =>
      change ((countLaw branches state proposals).bind (intervalKernel branches)).expectation _ = _
      rw [expectation_bind]
      simp only [kernel_absence]
      rw [expectation_const_mul, ih, pow_succ]
      ring

/-- Summing every interleaving recovers the exact no-mutation probability for
the combined exposure of all active branches. -/
theorem interval_absence (branches : Fin count → Branch n) (state : SiteState n) :
    (intervalLaw branches state).expectation absentReadout =
      Real.exp (-(totalExposure branches : ℝ)) * absentReadout state := by
  rw [interval_expectation]
  simp only [count_absence, ← mul_assoc]
  rw [tsum_mul_right, poisson_generating_function]
  congr 2
  have hp := ne_of_gt (proposalParameter_pos branches)
  rw [mul_sub, mul_one_div_cancel hp, proposalParameter]
  push_cast
  ring

theorem interval_presence (branches : Fin count → Branch n) (state : SiteState n) :
    (intervalLaw branches state).expectation presentReadout =
      1 - Real.exp (-(totalExposure branches : ℝ)) * (1 - presentReadout state) := by
  have hp (output : SiteState n) : presentReadout output = 1 - absentReadout output := by
    simp only [presentReadout, absentReadout]
    cases output.2.2 <;> norm_num
  have hfun : presentReadout (n := n) = fun output ↦ 1 - absentReadout output := funext hp
  rw [hfun, expectation_complement, interval_absence]
  ring

end Descent.Portability.InterleavedMutationLaw
