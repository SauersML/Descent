/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.FiniteMixtureKernel
import Descent.Portability.ResamplingJetExpansion
import Mathlib.Data.Real.Sqrt
import Mathlib.Algebra.Order.Floor.Semiring

assert_below Descent.Decision Descent.Program

/-!
# The resampling stage as a probability kernel, and the random-stage assembly

This file closes the drift half of NOTE 1 section 2.3 by presenting the single-draw
resampling step as a genuine `FiniteMixtureKernel` and calibrating its chromosome count
against a step size, and it supplies the assembly lemma for the random-stage construction
NOTE 1 offers in place of composing stages.

`resamplingKernel deme N` is the kernel whose four branches are the four haplotypes, weighted
by the drawing deme's own frequencies, each moving the state by `resampleStepAt`.  Its weights
are nonnegative and sum to one, so it is a probability kernel with no side conditions, and
`apply_resamplingKernel` identifies its action with `resampleExpectation`.

`driftChromosomeCount rate step` is the NOTE 1 calibration `ceil ((rate * step) ^ (-1/2))`.
The two facts that matter are proved: `one_div_driftChromosomeCount_le` says `1 / N` is at
most `sqrt (rate * step)`, and `abs_one_div_sq_sub_le` says `1 / N ^ 2` differs from
`rate * step` by at most `2 * sqrt (rate * step) ^ 3`.  Both come from the ceiling bounds
alone.  Consequently `apply_driftStageKernel_expansion`: for any jet carrying a
`ResamplingExpansion`, one drift stage moves the expectation by `step * rate * driftAt` up to
`step * driftStageSlack`, and `driftStageSlack_tendsto` shows that slack vanishes as the step
does.  This is hypothesis (3) of NOTE 1 Theorem 1 for the drift generator, with an explicit
`epsilon`.

`apply_uniformStageMixture` is the generic assembly lemma, stated for an arbitrary carrier.
Given stage kernels each of which expands to first order in its own step size with its own
slack, the uniform mixture run at `card S * step` expands to first order in `step` with
velocity the SUM of the stage velocities and slack the sum of the stage slacks.  This is the
"choose one stage uniformly at random" device of NOTE 1 section 2.3: it delivers the sum of
the generators with no composition lemma.

Scope.  Only the drift stage is instantiated here; migration, recombination and mutation
stages are deterministic and belong to the pulse package, which can feed them into
`apply_uniformStageMixture` through the same interface.  Nothing here forms a semigroup or
takes a limit; Theorem 1's Euler passage is separate.  Multinomial resampling, NOTE 1 (10),
is still not formalized: the single-draw alternative is used throughout.

## Empirical status

None.  The bodies here are algebra and calculus about named maps: a kernel built from the
simplex coordinates, a ceiling, a square root, and bounds relating them.  No measurement can
bear on them.  Whether a population's drift stage is this kernel is asked wherever a composed
prediction meets data, not here.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.RandomStageKernel

open Coalescent SimplexResamplingKernel ResamplingJetExpansion
open Descent.Portability.FiniteMixtureKernel

noncomputable section

/-- A sum over the four haplotypes written out in the corpus order. -/
theorem sum_haplotype (score : TwoLocusHaplotype → ℝ) :
    ∑ observed : TwoLocusHaplotype, score observed =
      score .AB + score .Ab + score .aB + score .ab := by
  have huniv : (Finset.univ : Finset TwoLocusHaplotype) =
      {TwoLocusHaplotype.AB, TwoLocusHaplotype.Ab, TwoLocusHaplotype.aB,
        TwoLocusHaplotype.ab} := by
    ext observed
    cases observed <;> simp
  rw [huniv, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  ring

/-- The single-draw resampling step in one deme, presented as a genuine probability kernel
with four branches: the drawn haplotype is the branch, the drawing weights are that deme's own
frequencies, and the move is `resampleStepAt`. -/
def resamplingKernel {D : ℕ} (deme : Fin D) (N : ℕ) :
    FiniteMixtureKernel TwoLocusHaplotype (Fin D → TwoLocusHaplotypeFrequencies) where
  weight state drawn := haplotypeCoordinate (state deme) drawn
  move drawn state := resampleStepAt state deme N drawn
  weight_nonneg state drawn := haplotypeCoordinate_nonneg (state deme) drawn
  weight_sum state := by
    rw [sum_haplotype]
    simp only [haplotypeCoordinate]
    exact (state deme).total_eq_one

/-- The resampling kernel's action on an observable is exactly `resampleExpectation`. -/
theorem apply_resamplingKernel {D : ℕ} (deme : Fin D) (N : ℕ)
    (state : Fin D → TwoLocusHaplotypeFrequencies)
    (observable : (Fin D → TwoLocusHaplotypeFrequencies) → ℝ) :
    (resamplingKernel deme N).apply observable state =
      resampleExpectation state deme N observable := by
  simp only [FiniteMixtureKernel.apply, resamplingKernel, sum_haplotype,
    resampleExpectation, twoLocusHaplotypeMean, haplotypeCoordinate]

/-- The chromosome count of the drift stage at coalescence rate `rate` and step size `step`:
the NOTE 1 calibration `ceil ((rate * step) ^ (-1/2))`, chosen so that `1 / N ^ 2` is
`rate * step` to within order `(rate * step) ^ (3/2)`. -/
def driftChromosomeCount (rate step : ℝ) : ℕ := ⌈(Real.sqrt (rate * step))⁻¹⌉₊

/-- At positive rate and step the drift stage draws at least one chromosome. -/
theorem one_le_driftChromosomeCount (rate step : ℝ) (hrate : 0 < rate) (hstep : 0 < step) :
    1 ≤ driftChromosomeCount rate step := by
  have hroot : 0 < Real.sqrt (rate * step) := Real.sqrt_pos.mpr (mul_pos hrate hstep)
  exact Nat.ceil_pos.mpr (inv_pos.mpr hroot)

/-- The reciprocal chromosome count is at most `sqrt (rate * step)`, directly from the
ceiling's lower bound. -/
theorem one_div_driftChromosomeCount_le (rate step : ℝ) (hrate : 0 < rate)
    (hstep : 0 < step) :
    1 / (driftChromosomeCount rate step : ℝ) ≤ Real.sqrt (rate * step) := by
  have hroot : 0 < Real.sqrt (rate * step) := Real.sqrt_pos.mpr (mul_pos hrate hstep)
  have hcount := one_le_driftChromosomeCount rate step hrate hstep
  have hreal : (0 : ℝ) < (driftChromosomeCount rate step : ℝ) := by
    exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hcount
  have hceil : (Real.sqrt (rate * step))⁻¹ ≤ (driftChromosomeCount rate step : ℝ) :=
    Nat.le_ceil _
  have hcancel : Real.sqrt (rate * step) * (Real.sqrt (rate * step))⁻¹ = 1 :=
    mul_inv_cancel₀ (ne_of_gt hroot)
  have hproduct := mul_le_mul_of_nonneg_left hceil hroot.le
  have hone : 1 ≤ Real.sqrt (rate * step) * (driftChromosomeCount rate step : ℝ) := by
    linarith
  have hexpand : 1 / (driftChromosomeCount rate step : ℝ) *
      (driftChromosomeCount rate step : ℝ) = 1 := by
    field_simp
  nlinarith [hone, hexpand, hreal, hroot.le]

/-- The square of the reciprocal chromosome count reproduces `rate * step` to within
`2 * sqrt (rate * step) ^ 3`.  Both ceiling bounds are used: the lower one caps `1 / N`, the
upper one keeps `1 / N` from being too small. -/
theorem abs_one_div_sq_sub_le (rate step : ℝ) (hrate : 0 < rate) (hstep : 0 < step) :
    |1 / (driftChromosomeCount rate step : ℝ) ^ 2 - rate * step| ≤
      2 * Real.sqrt (rate * step) ^ 3 := by
  have hroot : 0 < Real.sqrt (rate * step) := Real.sqrt_pos.mpr (mul_pos hrate hstep)
  have hsquare : Real.sqrt (rate * step) ^ 2 = rate * step :=
    Real.sq_sqrt (le_of_lt (mul_pos hrate hstep))
  have hcount := one_le_driftChromosomeCount rate step hrate hstep
  have hreal : (0 : ℝ) < (driftChromosomeCount rate step : ℝ) := by
    exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hcount
  have hexpand : 1 / (driftChromosomeCount rate step : ℝ) *
      (driftChromosomeCount rate step : ℝ) = 1 := by
    field_simp
  have hupper := one_div_driftChromosomeCount_le rate step hrate hstep
  have hnonneg : (0 : ℝ) ≤ 1 / (driftChromosomeCount rate step : ℝ) := by positivity
  have hceilupper : (driftChromosomeCount rate step : ℝ) <
      (Real.sqrt (rate * step))⁻¹ + 1 :=
    Nat.ceil_lt_add_one (le_of_lt (inv_pos.mpr hroot))
  have hcancel : Real.sqrt (rate * step) * (Real.sqrt (rate * step))⁻¹ = 1 :=
    mul_inv_cancel₀ (ne_of_gt hroot)
  have hnear : Real.sqrt (rate * step) * (driftChromosomeCount rate step : ℝ) <
      1 + Real.sqrt (rate * step) := by
    have hscaled := mul_lt_mul_of_pos_left hceilupper hroot
    nlinarith [hscaled, hcancel]
  have hone : 1 ≤ Real.sqrt (rate * step) * (driftChromosomeCount rate step : ℝ) := by
    nlinarith [hupper, hexpand, hreal]
  have hcubic : Real.sqrt (rate * step) ≤
      Real.sqrt (rate * step) ^ 2 * (driftChromosomeCount rate step : ℝ) := by
    nlinarith [hone, hroot.le]
  have hlower : Real.sqrt (rate * step) - 1 / (driftChromosomeCount rate step : ℝ) ≤
      Real.sqrt (rate * step) ^ 2 := by
    nlinarith [hnear, hcubic, hexpand, hreal]
  have hfactor : (Real.sqrt (rate * step) - 1 / (driftChromosomeCount rate step : ℝ)) *
      (Real.sqrt (rate * step) + 1 / (driftChromosomeCount rate step : ℝ)) ≤
      Real.sqrt (rate * step) ^ 2 * (2 * Real.sqrt (rate * step)) :=
    mul_le_mul hlower (by linarith) (by linarith) (by positivity)
  have hsq : 1 / (driftChromosomeCount rate step : ℝ) ^ 2 =
      (1 / (driftChromosomeCount rate step : ℝ)) ^ 2 := by
    ring
  rw [abs_le, hsq]
  constructor
  · nlinarith [hfactor, hsquare]
  · nlinarith [hupper, hnonneg, hsquare, hroot.le]

/-- The drift stage at coalescence rate `rate` and step size `step`: one single-draw
resampling step in the named deme with `driftChromosomeCount rate step` chromosomes. -/
def driftStageKernel {D : ℕ} (deme : Fin D) (rate step : ℝ) :
    FiniteMixtureKernel TwoLocusHaplotype (Fin D → TwoLocusHaplotypeFrequencies) :=
  resamplingKernel deme (driftChromosomeCount rate step)

/-- The explicit slack of one drift stage: the `epsilon` of NOTE 1 (3), equal to
`(remainder + 2 * bound) * rate ^ (3/2) * sqrt step`. -/
def driftStageSlack (rate step bound remainder : ℝ) : ℝ :=
  (remainder + 2 * bound) * (rate * Real.sqrt rate) * Real.sqrt step

/-- The drift-stage slack vanishes with the step size, which is what NOTE 1 (3) requires of
`epsilon`. -/
theorem driftStageSlack_tendsto (rate bound remainder : ℝ) :
    Filter.Tendsto (fun step ↦ driftStageSlack rate step bound remainder)
      (nhds 0) (nhds 0) := by
  have hcontinuous : Continuous
      fun step : ℝ ↦ driftStageSlack rate step bound remainder := by
    simp only [driftStageSlack]
    exact continuous_const.mul Real.continuous_sqrt
  have hzero : driftStageSlack rate 0 bound remainder = 0 := by
    simp [driftStageSlack]
  exact hcontinuous.tendsto' 0 0 hzero

/-- **One drift stage is the coalescence generator plus a vanishing slack.**  For any corpus
jet carrying a `ResamplingExpansion`, the drift stage at rate `rate` and step `step` moves the
expectation of the jet's value by `step * rate * driftAt` up to `step` times a slack that
tends to zero with the step.  This is hypothesis (3) of NOTE 1 Theorem 1 for the drift
generator, with the calibration `N = ceil ((rate * step) ^ (-1/2))`. -/
theorem apply_driftStageKernel_expansion {D : ℕ} {jet : TwoLocusDiffusionJet D}
    (resampling : ResamplingExpansion jet) (rate step : ℝ) (hrate : 0 < rate)
    (hstep : 0 < step) (state : Fin D → TwoLocusHaplotypeFrequencies) (deme : Fin D) :
    |(driftStageKernel deme rate step).apply jet.value state - jet.value state -
        step * (rate * jet.driftAt deme state)| ≤
      step * driftStageSlack rate step resampling.bound resampling.remainder := by
  have hcount := one_le_driftChromosomeCount rate step hrate hstep
  have hreal : (0 : ℝ) < (driftChromosomeCount rate step : ℝ) := by
    exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hcount
  have hbase := resampleExpectation_jet_expansion resampling
    (driftChromosomeCount rate step) hcount state deme
  have hdrift : |jet.driftAt deme state| ≤ resampling.bound := by
    rw [← resampling.second_mean deme state]
    exact twoLocusHaplotypeMean_abs_le (state deme) (resampling.second deme state)
      resampling.bound (fun observed ↦ resampling.second_le deme state observed)
  have hgap := abs_one_div_sq_sub_le rate step hrate hstep
  have hremainder := resampling.remainder_nonneg state deme .AB
  have hupper := one_div_driftChromosomeCount_le rate step hrate hstep
  have hnonneg : (0 : ℝ) ≤ 1 / (driftChromosomeCount rate step : ℝ) := by positivity
  have hcubebound : 1 / (driftChromosomeCount rate step : ℝ) ^ 3 ≤
      Real.sqrt (rate * step) ^ 3 := by
    have hcubeeq : 1 / (driftChromosomeCount rate step : ℝ) ^ 3 =
        (1 / (driftChromosomeCount rate step : ℝ)) ^ 3 := by
      ring
    have hpositive : (0 : ℝ) ≤ Real.sqrt (rate * step) ^ 2 +
        Real.sqrt (rate * step) * (1 / (driftChromosomeCount rate step : ℝ)) +
        (1 / (driftChromosomeCount rate step : ℝ)) ^ 2 := by
      positivity
    have hdifference := mul_nonneg (sub_nonneg.mpr hupper) hpositive
    rw [hcubeeq]
    nlinarith [hdifference]
  have hscaled : resampling.remainder / (driftChromosomeCount rate step : ℝ) ^ 3 ≤
      resampling.remainder * Real.sqrt (rate * step) ^ 3 := by
    have hrewrite : resampling.remainder / (driftChromosomeCount rate step : ℝ) ^ 3 =
        resampling.remainder * (1 / (driftChromosomeCount rate step : ℝ) ^ 3) := by
      ring
    rw [hrewrite]
    exact mul_le_mul_of_nonneg_left hcubebound hremainder
  have hproduct := abs_mul_le_of_abs_le_of_abs_le hgap hdrift
  have hsqrtcube : Real.sqrt (rate * step) ^ 3 =
      rate * Real.sqrt rate * (step * Real.sqrt step) := by
    rw [Real.sqrt_mul hrate.le]
    have hrateroot : Real.sqrt rate ^ 2 = rate := Real.sq_sqrt hrate.le
    have hsteproot : Real.sqrt step ^ 2 = step := Real.sq_sqrt hstep.le
    linear_combination (Real.sqrt rate * Real.sqrt step ^ 3) * hrateroot +
      (Real.sqrt rate * Real.sqrt step * rate) * hsteproot
  have hslackeq : step * driftStageSlack rate step resampling.bound resampling.remainder =
      (resampling.remainder + 2 * resampling.bound) * Real.sqrt (rate * step) ^ 3 := by
    simp only [driftStageSlack]
    rw [hsqrtcube]
    ring
  simp only [driftStageKernel]
  rw [apply_resamplingKernel]
  have hsplit : resampleExpectation state deme (driftChromosomeCount rate step) jet.value -
      jet.value state - step * (rate * jet.driftAt deme state) =
      (resampleExpectation state deme (driftChromosomeCount rate step) jet.value -
          jet.value state -
          1 / (driftChromosomeCount rate step : ℝ) ^ 2 * jet.driftAt deme state) +
        (1 / (driftChromosomeCount rate step : ℝ) ^ 2 - rate * step) *
          jet.driftAt deme state := by
    ring
  rw [hsplit, hslackeq]
  refine le_trans (abs_add_le _ _) ?_
  linarith

/-- **The random-stage assembly.**  If each stage kernel, run at its own step size, moves an
observable by that step size times its velocity up to that step size times its slack, then
choosing one of the `card S` stages uniformly at random and running it at `card S * step`
moves the observable by `step` times the SUM of the velocities, up to `step` times the sum of
the slacks.  No composition lemma is needed: this is the device NOTE 1 section 2.3 offers in
place of composing the stages. -/
theorem apply_uniformStageMixture {B X S : Type*} [Fintype B] [Fintype S]
    (stage : S → ℝ → FiniteMixtureKernel B X) (velocity : S → X → ℝ)
    (slack : S → ℝ → ℝ) (hcard : 0 < Fintype.card S) (observable : X → ℝ) (point : X)
    (step : ℝ) (hstep : 0 < step)
    (stage_expansion : ∀ s : S, ∀ scale : ℝ, 0 < scale → ∀ other : X,
      |(stage s scale).apply observable other - observable other -
        scale * velocity s other| ≤ scale * slack s scale) :
    |(FiniteMixtureKernel.uniformMixture
            (fun s ↦ stage s ((Fintype.card S : ℝ) * step)) hcard).apply
          observable point - observable point - step * ∑ s, velocity s point| ≤
      step * ∑ s, slack s ((Fintype.card S : ℝ) * step) := by
  have hcardpos : (0 : ℝ) < (Fintype.card S : ℝ) := by exact_mod_cast hcard
  have hcardne : (Fintype.card S : ℝ) ≠ 0 := ne_of_gt hcardpos
  have hscale : (0 : ℝ) < (Fintype.card S : ℝ) * step := mul_pos hcardpos hstep
  have hcancel : (Fintype.card S : ℝ) * (Fintype.card S : ℝ)⁻¹ = 1 :=
    mul_inv_cancel₀ hcardne
  have hsumbound : |∑ s : S,
      ((stage s ((Fintype.card S : ℝ) * step)).apply observable point - observable point -
        (Fintype.card S : ℝ) * step * velocity s point)| ≤
      ∑ s : S, (Fintype.card S : ℝ) * step *
        slack s ((Fintype.card S : ℝ) * step) :=
    le_trans (Finset.abs_sum_le_sum_abs _ _)
      (Finset.sum_le_sum (fun s _ ↦ stage_expansion s _ hscale point))
  have hsplit : ∑ s : S,
      ((stage s ((Fintype.card S : ℝ) * step)).apply observable point - observable point -
        (Fintype.card S : ℝ) * step * velocity s point) =
      (Fintype.card S : ℝ) * ((Fintype.card S : ℝ)⁻¹ *
          ∑ s : S, (stage s ((Fintype.card S : ℝ) * step)).apply observable point -
        observable point - step * ∑ s : S, velocity s point) := by
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_const,
      ← Finset.mul_sum, Finset.card_univ, nsmul_eq_mul]
    linear_combination (-(∑ s : S,
      (stage s ((Fintype.card S : ℝ) * step)).apply observable point)) * hcancel
  have hslacksum : ∑ s : S, (Fintype.card S : ℝ) * step *
      slack s ((Fintype.card S : ℝ) * step) =
      (Fintype.card S : ℝ) *
        (step * ∑ s : S, slack s ((Fintype.card S : ℝ) * step)) := by
    rw [← Finset.mul_sum]
    ring
  rw [hsplit, hslacksum, abs_mul, abs_of_pos hcardpos] at hsumbound
  rw [FiniteMixtureKernel.apply_uniformMixture]
  exact le_of_mul_le_mul_left hsumbound hcardpos

end

end Descent.Portability.RandomStageKernel
