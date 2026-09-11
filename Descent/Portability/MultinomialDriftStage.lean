/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.MultinomialMomentExpansion
import Descent.Portability.RandomStageKernel

assert_below Descent.Decision Descent.Program

/-!
# The multinomial drift stage

NOTE1 §2.3 builds the drift half of its microscopic kernel from multinomial resampling: a deme
with coalescence rate `c` draws `N(h) = ⌈1 / (c h)⌉` chromosomes independently from its own
haplotype frequencies and is replaced by their census frequencies. The corpus drift stage
`RandomStageKernel.driftStageKernel` uses the single-draw alternative instead. This module
constructs the multinomial stage as a genuine probability kernel and proves its expansion.

`haplotypeDrawLaw` is the law of one draw, the deme's own haplotype frequencies, and
`censusFrequencies` reads a census of `N ≥ 1` chromosomes as a point of the haplotype simplex.
`multinomialDriftKernel deme hN` is the kernel whose branches are the census vectors of total
`N`, weighted by the corpus multinomial law `FiniteReproductiveKernel.multinomialLaw` of the
drawing deme and moving that deme to the census frequencies. Its weights are multinomial masses,
so it is a probability kernel with no side conditions.

`DegreeFourObservable deme observable` certifies that an observable is, in the resampled deme,
a polynomial of total degree at most four in the four haplotype frequencies, with the other
demes fixing the coefficients, together with uniform bounds on the coefficient mass and on the
second-order operator. Under such a certificate `apply_multinomialDriftKernel_expansion` is
NOTE1 (10) for one stage: a multinomial step moves the observable by `resamplingOperator / N` up
to `coefficientBound / N ^ 2`, read off `MultinomialMomentExpansion.abs_expectation_eval_sub_le`.

`multinomialChromosomeCount rate step` is the calibration `⌈1 / (rate · step)⌉`. Its reciprocal
is at most `rate · step` (`one_div_multinomialChromosomeCount_le`) and at least
`rate · step - (rate · step) ^ 2` (`abs_one_div_multinomialChromosomeCount_sub_le`). Hence
`apply_multinomialDriftStage_expansion`, the replacement theorem for the drift stage: at step
size `step` the stage moves a certified observable by `step · rate · resamplingOperator` up to
`step · rate ^ 2 · step · (coefficientBound + driftBound)`, a slack of order `step` where the
single-draw stage has a slack of order `sqrt step`. `leftFrequencyObservable` is a certified
observable, the left-locus allele frequency of a deme, whose second-order operator vanishes.

What is NOT proved here: certificates for the corpus coordinate jets `H`, `DD`, `Dz`, `pi2` and
`H^R`, that is their polynomial representations in the resampled deme together with the
identification of `resamplingOperator` with `TwoLocusDiffusionJet.driftAt`; and the replacement
of the single-draw stage inside `TwoLocusMicroscopicKernel`, which also needs a branch type that
does not depend on the step size, since the census vectors of total `N(h)` change with `h`.

## Empirical status

None. The bodies here are finite probability: a multinomial law on census vectors, a polynomial
expansion with explicit constants and a ceiling bound. No measurement can bear on the moments of
a named law.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.MultinomialDriftStage

open Coalescent SimplexResamplingKernel RandomStageKernel
open Descent.Portability.FiniteMixtureKernel
open Descent.Portability.FiniteReproductiveKernel
open Descent.Portability.MultinomialMomentExpansion

noncomputable section

/-! ## The stage kernel -/

/-- The law of one chromosome drawn from a deme: its haplotype frequencies. -/
def haplotypeDrawLaw (frequency : TwoLocusHaplotypeFrequencies) :
    FiniteReportLaw TwoLocusHaplotype where
  mass := haplotypeCoordinate frequency
  mass_nonneg := haplotypeCoordinate_nonneg frequency
  mass_sum := by
    rw [sum_haplotype]
    simp only [haplotypeCoordinate]
    exact frequency.total_eq_one

/-- The haplotype frequencies of a census of `N ≥ 1` chromosomes: each count divided by `N`. -/
def censusFrequencies {N : ℕ} (hN : 0 < N) (counts : Counts TwoLocusHaplotype N) :
    TwoLocusHaplotypeFrequencies where
  AB := (counts.val .AB : ℝ) / N
  Ab := (counts.val .Ab : ℝ) / N
  aB := (counts.val .aB : ℝ) / N
  ab := (counts.val .ab : ℝ) / N
  AB_nonneg := by positivity
  Ab_nonneg := by positivity
  aB_nonneg := by positivity
  ab_nonneg := by positivity
  total_eq_one := by
    have hNne : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
    have hcast : ((∑ observed, counts.val observed : ℕ) : ℝ) = N := by
      exact_mod_cast counts_sum counts
    rw [Nat.cast_sum, sum_haplotype] at hcast
    field_simp
    linarith

/-- A haplotype coordinate of the census frequencies is the count divided by `N`. -/
theorem haplotypeCoordinate_censusFrequencies {N : ℕ} (hN : 0 < N)
    (counts : Counts TwoLocusHaplotype N) (observed : TwoLocusHaplotype) :
    haplotypeCoordinate (censusFrequencies hN counts) observed
      = (counts.val observed : ℝ) / N := by
  cases observed <;> rfl

/-- **The multinomial drift stage kernel.** Deme `deme` is replaced by the census frequencies
of `N` independent draws from its own haplotype frequencies, weighted by the multinomial law. -/
def multinomialDriftKernel {D : ℕ} (deme : Fin D) {N : ℕ} (hN : 0 < N) :
    FiniteMixtureKernel (Counts TwoLocusHaplotype N) (Fin D → TwoLocusHaplotypeFrequencies) where
  weight state counts := (multinomialLaw (haplotypeDrawLaw (state deme)) N).mass counts
  move counts state := Function.update state deme (censusFrequencies hN counts)
  weight_nonneg state counts :=
    (multinomialLaw (haplotypeDrawLaw (state deme)) N).mass_nonneg counts
  weight_sum state := (multinomialLaw (haplotypeDrawLaw (state deme)) N).mass_sum

/-! ## The expansion of one stage -/

/-- **A degree-four observable of the resampled deme.** In deme `deme` the observable is the
evaluation, at that deme's haplotype frequencies, of a polynomial of total degree at most four
whose coefficients depend only on the other demes, and the coefficient mass controlling the
remainder of (10) and the second-order operator are uniformly bounded.
Assumes: the five Prop fields. `leftFrequencyObservable` is a concrete inhabitant. -/
structure DegreeFourObservable {D : ℕ} (deme : Fin D)
    (observable : (Fin D → TwoLocusHaplotypeFrequencies) → ℝ) where
  /-- The polynomial in the resampled deme, with coefficients read off the other demes. -/
  polynomial : (Fin D → TwoLocusHaplotypeFrequencies) → MvPolynomial TwoLocusHaplotype ℝ
  /-- The polynomial has total degree at most four. -/
  totalDegree_le : ∀ state, (polynomial state).totalDegree ≤ 4
  /-- The coefficients do not depend on the resampled deme. -/
  polynomial_update : ∀ state frequency,
    polynomial (Function.update state deme frequency) = polynomial state
  /-- The observable is the polynomial evaluated at the resampled deme's frequencies. -/
  observable_eq : ∀ state,
    observable state = MvPolynomial.eval (haplotypeCoordinate (state deme)) (polynomial state)
  /-- A uniform bound on the coefficient mass that controls the remainder. -/
  coefficientBound : ℝ
  /-- The coefficient mass is at most `coefficientBound` at every state. -/
  coefficient_le : ∀ state, ∑ s ∈ (polynomial state).support,
      |(polynomial state).coeff s| * (11 + 4 * totalStirlingWeight ⇑s) ≤ coefficientBound
  /-- A uniform bound on the second-order operator. -/
  driftBound : ℝ
  /-- The second-order operator is at most `driftBound` in absolute value at every state. -/
  drift_le : ∀ state,
    |resamplingOperator (haplotypeCoordinate (state deme)) (polynomial state)| ≤ driftBound

/-- **NOTE1 (10) for one multinomial drift stage.** One step of `multinomialDriftKernel` with
`N ≥ 1` chromosomes moves a certified observable by `resamplingOperator / N`, up to
`coefficientBound / N ^ 2`. -/
theorem apply_multinomialDriftKernel_expansion {D : ℕ} {deme : Fin D}
    {observable : (Fin D → TwoLocusHaplotypeFrequencies) → ℝ}
    (certificate : DegreeFourObservable deme observable) {N : ℕ} (hN : 0 < N)
    (state : Fin D → TwoLocusHaplotypeFrequencies) :
    |(multinomialDriftKernel deme hN).apply observable state - observable state
        - resamplingOperator (haplotypeCoordinate (state deme)) (certificate.polynomial state)
          / N|
      ≤ certificate.coefficientBound / (N : ℝ) ^ 2 := by
  have happly : (multinomialDriftKernel deme hN).apply observable state
      = (multinomialLaw (haplotypeDrawLaw (state deme)) N).expectation
          (fun counts ↦ MvPolynomial.eval (fun a ↦ (counts.val a : ℝ) / N)
            (certificate.polynomial state)) := by
    simp only [FiniteMixtureKernel.apply, multinomialDriftKernel, FiniteReportLaw.expectation]
    refine Finset.sum_congr rfl fun counts _ ↦ ?_
    rw [certificate.observable_eq, Function.update_self, certificate.polynomial_update]
    have hcoordinate : haplotypeCoordinate (censusFrequencies hN counts)
        = fun a ↦ (counts.val a : ℝ) / N :=
      funext fun a ↦ haplotypeCoordinate_censusFrequencies hN counts a
    rw [hcoordinate]
  rw [happly, certificate.observable_eq state]
  refine (abs_expectation_eval_sub_le (haplotypeDrawLaw (state deme)) N hN
    (certificate.polynomial state) (certificate.totalDegree_le state)).trans ?_
  gcongr
  exact certificate.coefficient_le state

/-! ## The step-size calibration -/

/-- The chromosome count of the multinomial drift stage at rate `rate` and step size `step`,
the NOTE1 calibration `⌈1 / (rate · step)⌉`. -/
def multinomialChromosomeCount (rate step : ℝ) : ℕ := ⌈(rate * step)⁻¹⌉₊

/-- At positive rate and step the multinomial stage draws at least one chromosome. -/
theorem one_le_multinomialChromosomeCount (rate step : ℝ) (hrate : 0 < rate)
    (hstep : 0 < step) : 1 ≤ multinomialChromosomeCount rate step :=
  Nat.ceil_pos.mpr (inv_pos.mpr (mul_pos hrate hstep))

/-- The reciprocal chromosome count is at most `rate · step`. -/
theorem one_div_multinomialChromosomeCount_le (rate step : ℝ) (hrate : 0 < rate)
    (hstep : 0 < step) : 1 / (multinomialChromosomeCount rate step : ℝ) ≤ rate * step := by
  have hu : 0 < rate * step := mul_pos hrate hstep
  have hceil : (rate * step)⁻¹ ≤ (multinomialChromosomeCount rate step : ℝ) := Nat.le_ceil _
  have hNpos : (0 : ℝ) < multinomialChromosomeCount rate step :=
    lt_of_lt_of_le (inv_pos.mpr hu) hceil
  rw [div_le_iff₀ hNpos]
  have hscaled := mul_le_mul_of_nonneg_left hceil hu.le
  rwa [mul_inv_cancel₀ hu.ne'] at hscaled

/-- **The rounding of the chromosome count.** The reciprocal chromosome count is `rate · step`
to within `(rate · step) ^ 2`. -/
theorem abs_one_div_multinomialChromosomeCount_sub_le (rate step : ℝ) (hrate : 0 < rate)
    (hstep : 0 < step) :
    |1 / (multinomialChromosomeCount rate step : ℝ) - rate * step| ≤ (rate * step) ^ 2 := by
  have hu : 0 < rate * step := mul_pos hrate hstep
  have hceil' : (multinomialChromosomeCount rate step : ℝ) < (rate * step)⁻¹ + 1 :=
    Nat.ceil_lt_add_one (inv_nonneg.mpr hu.le)
  have hNpos : (0 : ℝ) < multinomialChromosomeCount rate step :=
    lt_of_lt_of_le (inv_pos.mpr hu) (Nat.le_ceil _)
  have hnu : (multinomialChromosomeCount rate step : ℝ) * (rate * step) < 1 + rate * step := by
    have hscaled := mul_lt_mul_of_pos_right hceil' hu
    rwa [add_mul, inv_mul_cancel₀ hu.ne', one_mul] at hscaled
  have hw : 1 / (multinomialChromosomeCount rate step : ℝ)
      * (multinomialChromosomeCount rate step : ℝ) = 1 := by
    field_simp
  have hwpos : 0 < 1 / (multinomialChromosomeCount rate step : ℝ) := by positivity
  have hwle := one_div_multinomialChromosomeCount_le rate step hrate hstep
  have hwnu : 1 / (multinomialChromosomeCount rate step : ℝ)
      * (multinomialChromosomeCount rate step : ℝ) * (rate * step) = rate * step := by
    rw [hw, one_mul]
  have hprod := mul_lt_mul_of_pos_left hnu hwpos
  have hwu : 1 / (multinomialChromosomeCount rate step : ℝ) * (rate * step)
      ≤ rate * step * (rate * step) := mul_le_mul_of_nonneg_right hwle hu.le
  rw [abs_le]
  constructor
  · nlinarith [hprod, hwnu, hwu]
  · nlinarith [hwle, hu]

/-- Combining a first-order expansion in `1 / n` with the rounding of `1 / n` against `u`. -/
theorem abs_sub_mul_le_of_rounding (change drift coefficientBound driftBound u n : ℝ)
    (hn : 0 < n) (hK : 0 ≤ coefficientBound) (hB : |drift| ≤ driftBound) (hwu : 1 / n ≤ u)
    (hround : |1 / n - u| ≤ u ^ 2) (hbase : |change - drift / n| ≤ coefficientBound / n ^ 2) :
    |change - u * drift| ≤ (coefficientBound + driftBound) * u ^ 2 := by
  have hB0 : 0 ≤ driftBound := (abs_nonneg _).trans hB
  have hw0 : 0 ≤ 1 / n := by positivity
  have hw2 : (1 / n) ^ 2 ≤ u ^ 2 := by nlinarith
  have hdiv : drift / n = drift * (1 / n) := by ring
  have hsq : coefficientBound / n ^ 2 = coefficientBound * (1 / n) ^ 2 := by ring
  rw [hdiv, hsq] at hbase
  calc |change - u * drift| = |(change - drift * (1 / n)) + drift * (1 / n - u)| := by
        congr 1
        ring
    _ ≤ |change - drift * (1 / n)| + |drift| * |1 / n - u| := by
        rw [← abs_mul]
        exact abs_add_le _ _
    _ ≤ coefficientBound * (1 / n) ^ 2 + driftBound * u ^ 2 :=
        add_le_add hbase (mul_le_mul hB hround (abs_nonneg _) hB0)
    _ ≤ coefficientBound * u ^ 2 + driftBound * u ^ 2 := by
        nlinarith [mul_le_mul_of_nonneg_left hw2 hK]
    _ = (coefficientBound + driftBound) * u ^ 2 := by ring

/-- **The multinomial drift stage replaces the single-draw stage to first order.** At rate
`rate > 0` and step size `step > 0`, one multinomial step with `multinomialChromosomeCount`
chromosomes moves a certified observable by `step · rate · resamplingOperator`, up to
`step · rate ^ 2 · step · (coefficientBound + driftBound)`. -/
theorem apply_multinomialDriftStage_expansion {D : ℕ} {deme : Fin D}
    {observable : (Fin D → TwoLocusHaplotypeFrequencies) → ℝ}
    (certificate : DegreeFourObservable deme observable) (rate step : ℝ) (hrate : 0 < rate)
    (hstep : 0 < step) (state : Fin D → TwoLocusHaplotypeFrequencies) :
    |(multinomialDriftKernel deme (one_le_multinomialChromosomeCount rate step hrate hstep)).apply
          observable state - observable state
        - step * (rate * resamplingOperator (haplotypeCoordinate (state deme))
            (certificate.polynomial state))|
      ≤ step * (rate ^ 2 * step * (certificate.coefficientBound + certificate.driftBound)) := by
  have hNpos : (0 : ℝ) < multinomialChromosomeCount rate step := by
    exact_mod_cast one_le_multinomialChromosomeCount rate step hrate hstep
  have hbase := apply_multinomialDriftKernel_expansion certificate
    (one_le_multinomialChromosomeCount rate step hrate hstep) state
  have hK : 0 ≤ certificate.coefficientBound :=
    le_trans (Finset.sum_nonneg fun s _ ↦ mul_nonneg (abs_nonneg _)
      (by
        have hweight : 0 ≤ totalStirlingWeight ⇑s :=
          Finset.sum_nonneg fun j _ ↦ stirlingWeight_nonneg _ j
        linarith)) (certificate.coefficient_le state)
  have hkey := abs_sub_mul_le_of_rounding
    ((multinomialDriftKernel deme (one_le_multinomialChromosomeCount rate step hrate hstep)).apply
      observable state - observable state)
    (resamplingOperator (haplotypeCoordinate (state deme)) (certificate.polynomial state))
    certificate.coefficientBound certificate.driftBound (rate * step)
    (multinomialChromosomeCount rate step : ℝ) hNpos hK (certificate.drift_le state)
    (one_div_multinomialChromosomeCount_le rate step hrate hstep)
    (abs_one_div_multinomialChromosomeCount_sub_le rate step hrate hstep) hbase
  calc |(multinomialDriftKernel deme
            (one_le_multinomialChromosomeCount rate step hrate hstep)).apply observable state
          - observable state
        - step * (rate * resamplingOperator (haplotypeCoordinate (state deme))
            (certificate.polynomial state))|
      = |((multinomialDriftKernel deme
            (one_le_multinomialChromosomeCount rate step hrate hstep)).apply observable state
          - observable state)
        - rate * step * resamplingOperator (haplotypeCoordinate (state deme))
            (certificate.polynomial state)| := by
        congr 1
        ring
    _ ≤ (certificate.coefficientBound + certificate.driftBound) * (rate * step) ^ 2 := hkey
    _ = step * (rate ^ 2 * step * (certificate.coefficientBound + certificate.driftBound)) := by
        ring

/-! ## A certified observable -/

/-- The second partial derivatives of a coordinate polynomial vanish. -/
theorem pderiv_pderiv_X {H : Type*} [DecidableEq H] (a c observed : H) :
    MvPolynomial.pderiv a (MvPolynomial.pderiv c (MvPolynomial.X observed : MvPolynomial H ℝ))
      = 0 := by
  rw [MvPolynomial.pderiv_X]
  by_cases hco : c = observed
  · subst hco
    rw [Pi.single_eq_same, MvPolynomial.pderiv_one]
  · rw [Pi.single_eq_of_ne (Ne.symm hco), map_zero]

/-- The second-order operator of (10) vanishes on a coordinate polynomial. -/
theorem resamplingOperator_X {H : Type*} [Fintype H] [DecidableEq H] (x : H → ℝ)
    (observed : H) : resamplingOperator x (MvPolynomial.X observed) = 0 := by
  simp only [resamplingOperator, pderiv_pderiv_X, map_zero, mul_zero, Finset.sum_const_zero]

/-- **A certified observable: the left-locus allele frequency of a deme.** It is the linear
polynomial `X_AB + X_Ab` in the deme's haplotype frequencies, with a constant coefficient mass
and a vanishing second-order operator. -/
def leftFrequencyObservable {D : ℕ} (deme : Fin D) :
    DegreeFourObservable deme (fun state ↦ (state deme).leftFrequency) where
  polynomial _ := MvPolynomial.X .AB + MvPolynomial.X .Ab
  totalDegree_le _ := le_trans (MvPolynomial.totalDegree_add _ _) (by
    rw [MvPolynomial.totalDegree_X, MvPolynomial.totalDegree_X]
    norm_num)
  polynomial_update _ _ := by dsimp only
  observable_eq state := by
    simp [TwoLocusHaplotypeFrequencies.leftFrequency, haplotypeCoordinate]
  coefficientBound := ∑ s ∈ (MvPolynomial.X TwoLocusHaplotype.AB
      + MvPolynomial.X TwoLocusHaplotype.Ab : MvPolynomial TwoLocusHaplotype ℝ).support,
    |(MvPolynomial.X TwoLocusHaplotype.AB + MvPolynomial.X TwoLocusHaplotype.Ab
      : MvPolynomial TwoLocusHaplotype ℝ).coeff s| * (11 + 4 * totalStirlingWeight ⇑s)
  coefficient_le _ := le_rfl
  driftBound := 0
  drift_le _ := by
    rw [resamplingOperator_add, resamplingOperator_X, resamplingOperator_X, add_zero, abs_zero]

end

end Descent.Portability.MultinomialDriftStage
