/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.EndToEndBrierLaw
import Descent.Portability.PortabilityMomentLadder
import Descent.Portability.EndToEndAscertainedWitness
import Descent.Portability.EndToEndSelectionLaw

assert_below Descent.Decision Descent.Program

/-!
# No finite rung fixes the calibration error: two process laws that agree through degree three

`EndToEndBrierLaw` brackets the expected calibration error `E Σ_s |a_s - v_s q_s|` between a
budget-1 and a budget-2 computation and leaves open whether finitely many propagated moments
determine it.  This module settles the first case: the budget-3 moments do not.

The witness.  One deme carries one biallelic locus, and the report sends a haplotype to the single
score group and its allele (`outcomeReport`).  At allele frequency `q` the calibration error at
value `1/2` is `|q - 1/2|` (`caseMass_biallelicState`, `controlMass_biallelicState`,
`calibrationError_biallelicState`): the residual is linear, and the error is its absolute value.
Two constant kernels draw the state from finite laws on the frequency (`biallelicState`,
`firstLaw`, `secondLaw`, `firstKernel`, `secondKernel`; `isMarkovKernel_firstKernel`,
`isMarkovKernel_secondKernel`).  The first puts mass `1/2` on the frequencies `1/4` and `3/4`; the
second puts `1/8, 3/4, 1/8` on `0, 1/2, 1` (`integral_firstLaw`, `integral_secondLaw`).  The
residual `q - 1/2` has the laws `½ δ_{-1/4} + ½ δ_{1/4}` and `⅛ δ_{-1/2} + ¾ δ_0 + ⅛ δ_{1/2}`, with
equal moments of degree at most three and mean absolute values `1/4` and `1/8`.

Agreement through degree three.  At a biallelic state every configuration moment is
`q^i (1 - q)^j`, with `i` carriers of the allele and `j` of the other
(`configurationMoment_frequencyLaw`).  The two laws weight every such product with `i + j ≤ 3`
equally (`frequencyProducts_mixtures_eq`), so their budget-3 moment vectors agree
(`momentVector_mixtures_eq`).  Every frequency polynomial of total degree at most three is the
corpus coefficient vector dotted with that moment vector
(`eval_eq_budgetCoefficients_dotProduct`), so the two process laws agree on all of them
(`polynomialsAgreeAt_three`).

The separation.  The expected calibration errors are `1/4` and `1/8`
(`expectedCalibrationError_firstKernel`, `expectedCalibrationError_secondKernel`), so two Markov
kernels that agree on every frequency polynomial of degree at most three give different expected
calibration error (`polynomialsAgreeAt_three_and_expectedCalibrationError_ne`): no function of the
budget-3 moments determines it
(`not_forall_expectedCalibrationError_eq_of_polynomialsAgreeAt_three`).

Contrast.  The repaired Brier loss is a convergent series of polynomial expectations, so agreement
at every degree fixes it
(`PortabilityMomentLadderBrier.expectedRepairedBrier_eq_of_polynomialsAgreeAt_all`).
The calibration error is an absolute value of a linear residual, not a series of polynomials, and a
finite rung of the moment ladder does not reach it.

Scope.  The witnesses are constant kernels of finite laws on the frequency state, not histories of
epochs.  Budgets above three are not separated here: whether agreement at every finite budget fixes
the expected calibration error is not settled.

## Empirical status

None.  The bodies here are finite sums of point masses, polynomial identities at rational
frequencies and rational arithmetic, so no measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.EndToEndCalibrationErrorNonclosure

open MeasureTheory ProbabilityTheory MvPolynomial Descent.Coalescent PartialHaplotypeCarrier
  PartialHaplotypeDualGenerator NeutralFellerGenerator NeutralMomentSemigroup
  NeutralPolynomialSemigroup ReplicaMetricInstances EndToEndPortabilityLaw EndToEndBrierLaw
  PortabilityMomentLadder EndToEndAscertainedWitness EndToEndSelectionLaw

noncomputable section

/-! ## The biallelic witness -/

/-- The frequency states of one deme at one biallelic locus. -/
abbrev BiallelicState : Type := FrequencyState Unit Unit fun _ : Unit ↦ Bool

/-- The report of the single score group and the allele of the haplotype. -/
def outcomeReport (hap : FullHaplotype Unit fun _ : Unit ↦ Bool) : Unit × Bool :=
  ((), hap ())

/-- The biallelic state at allele frequency `q`. -/
def biallelicState (q : ℝ) (hq : 0 ≤ q ∧ q ≤ 1) : BiallelicState :=
  stateOfLaws (frequencyLaw q hq)

/-- The case mass of the outcome report at frequency `q` is `q`. -/
theorem caseMass_biallelicState (q : ℝ) (hq : 0 ≤ q ∧ q ≤ 1) :
    ((stateLaw (biallelicState q hq) ()).pushforward outcomeReport).mass ((), true) = q := by
  rw [pushforwardMass_eq_expectation, biallelicState, stateLaw_stateOfLaws,
    FiniteReportLaw.expectation, sum_unitHaplotype]
  simp [frequencyLaw, outcomeReport]

/-- The control mass of the outcome report at frequency `q` is `1 - q`. -/
theorem controlMass_biallelicState (q : ℝ) (hq : 0 ≤ q ∧ q ≤ 1) :
    ((stateLaw (biallelicState q hq) ()).pushforward outcomeReport).mass ((), false) = 1 - q := by
  rw [pushforwardMass_eq_expectation, biallelicState, stateLaw_stateOfLaws,
    FiniteReportLaw.expectation, sum_unitHaplotype]
  simp [frequencyLaw, outcomeReport]

/-- **The calibration error at frequency `q`** of the outcome report at value `1/2` is `|q - 1/2|`:
the group mass is one and the residual is `q - 1/2`. -/
theorem calibrationError_biallelicState (q : ℝ) (hq : 0 ≤ q ∧ q ≤ 1) :
    calibrationError ((stateLaw (biallelicState q hq) ()).pushforward outcomeReport)
      (fun _ ↦ 1 / 2) = |q - 1 / 2| := by
  have hgroup : scoreGroupMass ((stateLaw (biallelicState q hq) ()).pushforward outcomeReport) ()
      = 1 := by
    rw [scoreGroupMass, caseMass_biallelicState, controlMass_biallelicState]
    ring
  have hresidual : calibrationResidual
      ((stateLaw (biallelicState q hq) ()).pushforward outcomeReport) (fun _ ↦ 1 / 2) ()
      = q - 1 / 2 := by
    rw [calibrationResidual, caseMass_biallelicState, hgroup]
    ring
  rw [calibrationError, Finset.univ_unique, Finset.sum_singleton]
  show |calibrationResidual ((stateLaw (biallelicState q hq) ()).pushforward outcomeReport)
    (fun _ ↦ 1 / 2) ()| = |q - 1 / 2|
  rw [hresidual]

/-- **Configuration moments at a biallelic state**: `q^i (1 - q)^j` for `i` carriers of the allele
and `j` carriers of the other allele. -/
theorem configurationMoment_frequencyLaw (q : ℝ) (hq : 0 ≤ q ∧ q ≤ 1)
    (ζ : Multiset (PartialType Unit Unit fun _ : Unit ↦ Bool)) :
    configurationMoment (frequencyLaw q hq) ζ
      = q ^ ζ.countP (fun τ ↦ τ.allele () = some true)
        * (1 - q) ^ ζ.countP (fun τ ↦ ¬ τ.allele () = some true) := by
  induction ζ using Multiset.induction_on with
  | empty => simp [configurationMoment]
  | cons τ ζ ih =>
    rw [configurationMoment_cons, marginalFrequency_frequencyLaw, ih]
    by_cases hcarrier : τ.allele () = some true
    · rw [if_pos hcarrier,
        Multiset.countP_cons_of_pos
          (p := fun σ : PartialType Unit Unit (fun _ : Unit ↦ Bool) ↦ σ.allele () = some true) _
          hcarrier,
        Multiset.countP_cons_of_neg
          (p := fun σ : PartialType Unit Unit (fun _ : Unit ↦ Bool) ↦ ¬ σ.allele () = some true)
          _ (not_not.mpr hcarrier)]
      ring
    · rw [if_neg hcarrier,
        Multiset.countP_cons_of_neg
          (p := fun σ : PartialType Unit Unit (fun _ : Unit ↦ Bool) ↦ σ.allele () = some true) _
          hcarrier,
        Multiset.countP_cons_of_pos
          (p := fun σ : PartialType Unit Unit (fun _ : Unit ↦ Bool) ↦ ¬ σ.allele () = some true)
          _ hcarrier]
      ring

/-! ## Two laws of the frequency -/

/-- The state at frequency `1/4`. -/
def quarterState : BiallelicState := biallelicState (1 / 4) ⟨by norm_num, by norm_num⟩

/-- The state at frequency `3/4`. -/
def threeQuarterState : BiallelicState := biallelicState (3 / 4) ⟨by norm_num, by norm_num⟩

/-- The state at frequency `0`. -/
def zeroState : BiallelicState := biallelicState 0 ⟨le_rfl, zero_le_one⟩

/-- The state at frequency `1/2`. -/
def halfState : BiallelicState := biallelicState (1 / 2) ⟨by norm_num, by norm_num⟩

/-- The state at frequency `1`. -/
def oneState : BiallelicState := biallelicState 1 ⟨zero_le_one, le_rfl⟩

/-- The first law: frequency `1/4` or `3/4`, each with probability `1/2`. -/
def firstLaw : Measure BiallelicState :=
  ENNReal.ofReal (1 / 2) • Measure.dirac quarterState
    + ENNReal.ofReal (1 / 2) • Measure.dirac threeQuarterState

/-- The second law: frequency `0`, `1/2` or `1`, with probabilities `1/8`, `3/4`, `1/8`. -/
def secondLaw : Measure BiallelicState :=
  ENNReal.ofReal (1 / 8) • Measure.dirac zeroState
    + ENNReal.ofReal (3 / 4) • Measure.dirac halfState
    + ENNReal.ofReal (1 / 8) • Measure.dirac oneState

/-- A continuous observable integrates against a weighted point mass to the weighted value. -/
theorem integral_smul_dirac (w : ℝ) (hw : 0 ≤ w) (s : BiallelicState) {f : BiallelicState → ℝ}
    (hf : Continuous f) : ∫ y, f y ∂(ENNReal.ofReal w • Measure.dirac s) = w * f s := by
  rw [integral_smul_measure, integral_dirac' _ _ hf.stronglyMeasurable, ENNReal.toReal_ofReal hw,
    smul_eq_mul]

/-- A continuous observable is integrable against a weighted point mass. -/
theorem integrable_smul_dirac (w : ℝ) (s : BiallelicState) {f : BiallelicState → ℝ}
    (hf : Continuous f) : Integrable f (ENNReal.ofReal w • Measure.dirac s) :=
  (integrable_dirac' hf.stronglyMeasurable (by simp)).smul_measure ENNReal.ofReal_ne_top

/-- A continuous observable integrates against the first law to its average at `1/4` and `3/4`. -/
theorem integral_firstLaw {f : BiallelicState → ℝ} (hf : Continuous f) :
    ∫ y, f y ∂firstLaw = 1 / 2 * f quarterState + 1 / 2 * f threeQuarterState := by
  rw [firstLaw,
    integral_add_measure (integrable_smul_dirac _ _ hf) (integrable_smul_dirac _ _ hf),
    integral_smul_dirac (1 / 2) (by norm_num) _ hf, integral_smul_dirac (1 / 2) (by norm_num) _ hf]

/-- A continuous observable integrates against the second law to its weighted values at `0`,
`1/2` and `1`. -/
theorem integral_secondLaw {f : BiallelicState → ℝ} (hf : Continuous f) :
    ∫ y, f y ∂secondLaw
      = 1 / 8 * f zeroState + 3 / 4 * f halfState + 1 / 8 * f oneState := by
  rw [secondLaw, integral_add_measure
      ((integrable_smul_dirac _ _ hf).add_measure (integrable_smul_dirac _ _ hf))
      (integrable_smul_dirac _ _ hf),
    integral_add_measure (integrable_smul_dirac _ _ hf) (integrable_smul_dirac _ _ hf),
    integral_smul_dirac (1 / 8) (by norm_num) zeroState hf,
    integral_smul_dirac (3 / 4) (by norm_num) _ hf,
    integral_smul_dirac (1 / 8) (by norm_num) _ hf]

/-- The first law is a probability measure. -/
theorem firstLaw_isProbabilityMeasure : IsProbabilityMeasure firstLaw := by
  refine ⟨?_⟩
  simp only [firstLaw, Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    (show (0 : ℝ) ≤ 1 / 2 by norm_num)]
  norm_num

/-- The second law is a probability measure. -/
theorem secondLaw_isProbabilityMeasure : IsProbabilityMeasure secondLaw := by
  refine ⟨?_⟩
  simp only [secondLaw, Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add (show (0 : ℝ) ≤ 1 / 8 by norm_num) (show (0 : ℝ) ≤ 3 / 4 by norm_num),
    ← ENNReal.ofReal_add (show (0 : ℝ) ≤ 1 / 8 + 3 / 4 by norm_num)
      (show (0 : ℝ) ≤ 1 / 8 by norm_num)]
  norm_num

/-- The first process law: every state moves to a draw from the first law. -/
def firstKernel : Kernel BiallelicState BiallelicState :=
  Kernel.const _ firstLaw

/-- The second process law: every state moves to a draw from the second law. -/
def secondKernel : Kernel BiallelicState BiallelicState :=
  Kernel.const _ secondLaw

/-- The first process law is a Markov kernel. -/
theorem isMarkovKernel_firstKernel : IsMarkovKernel firstKernel := by
  haveI := firstLaw_isProbabilityMeasure
  unfold firstKernel
  infer_instance

/-- The second process law is a Markov kernel. -/
theorem isMarkovKernel_secondKernel : IsMarkovKernel secondKernel := by
  haveI := secondLaw_isProbabilityMeasure
  unfold secondKernel
  infer_instance

/-! ## Agreement through degree three -/

/-- **The two laws weight every product `q^i (1 - q)^j` with `i + j ≤ 3` equally.** -/
theorem frequencyProducts_mixtures_eq {i j : ℕ} (hij : i + j ≤ 3) :
    1 / 2 * ((1 / 4 : ℝ) ^ i * (1 - 1 / 4) ^ j) + 1 / 2 * ((3 / 4 : ℝ) ^ i * (1 - 3 / 4) ^ j)
      = 1 / 8 * ((0 : ℝ) ^ i * (1 - 0) ^ j) + 3 / 4 * ((1 / 2 : ℝ) ^ i * (1 - 1 / 2) ^ j)
        + 1 / 8 * ((1 : ℝ) ^ i * (1 - 1) ^ j) := by
  have hi : i ≤ 3 := by omega
  have hj : j ≤ 3 := by omega
  interval_cases i <;> interval_cases j <;> first | omega | norm_num

/-- **The budget-3 moment vectors of the two laws agree**: both weight every `q^i (1 - q)^j` with
`i + j ≤ 3` equally. -/
theorem momentVector_mixtures_eq :
    (1 / 2 : ℝ) • momentVector (fun _ ↦ 3) quarterState
        + (1 / 2 : ℝ) • momentVector (fun _ ↦ 3) threeQuarterState
      = (1 / 8 : ℝ) • momentVector (fun _ ↦ 3) zeroState
        + (3 / 4 : ℝ) • momentVector (fun _ ↦ 3) halfState
        + (1 / 8 : ℝ) • momentVector (fun _ ↦ 3) oneState := by
  funext η
  have hcard : Multiset.card η.1 ≤ 3 := by
    simpa using card_le_capacity_total (fun _ : Unit ↦ 3) η.1 η.2
  have hsplit := Multiset.card_eq_countP_add_countP
    (p := fun τ : PartialType Unit Unit (fun _ : Unit ↦ Bool) ↦ τ.allele () = some true) η.1
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, momentVector, quarterState,
    threeQuarterState, zeroState, halfState, oneState, biallelicState, stateOfLaws,
    eval_momentPolynomial, configurationMoment_frequencyLaw]
  exact frequencyProducts_mixtures_eq (by omega)

/-- A frequency polynomial of total degree at most three evaluates at a biallelic state to the
corpus coefficient vector dotted with the budget-3 moment vector. -/
theorem eval_eq_budgetCoefficients_dotProduct
    (p : FrequencyPolynomial Unit Unit fun _ : Unit ↦ Bool) (hp : p.totalDegree ≤ 3)
    (y : BiallelicState) :
    eval y.1 p = budgetCoefficients () (fun _ ↦ 3) p ⬝ᵥ momentVector (fun _ ↦ 3) y :=
  eval_eq_dotProduct () (fun _ ↦ 3) p (withinBudget_of_totalDegree_le () p hp) y

/-- **The two process laws agree on every frequency polynomial of total degree at most three.** -/
theorem polynomialsAgreeAt_three (x₁ x₂ : BiallelicState) :
    PolynomialsAgreeAt 3 firstKernel secondKernel x₁ x₂ := by
  intro p hp
  have hcontinuous : Continuous fun y : BiallelicState ↦ polynomialFunction p y :=
    (polynomialFunction p).continuous
  have hmixture :=
    congrArg (budgetCoefficients () (fun _ ↦ 3) p ⬝ᵥ ·) momentVector_mixtures_eq
  simp only [dotProduct_add, dotProduct_smul, smul_eq_mul] at hmixture
  rw [firstKernel, secondKernel, Kernel.const_apply, Kernel.const_apply,
    integral_firstLaw hcontinuous, integral_secondLaw hcontinuous]
  simp only [polynomialFunction_apply, eval_eq_budgetCoefficients_dotProduct p hp]
  linarith

/-! ## The separation -/

/-- The calibration error of the outcome report is a continuous observable of the state. -/
theorem continuous_outcomeCalibrationError :
    Continuous fun y : BiallelicState ↦
      calibrationError ((stateLaw y ()).pushforward outcomeReport) (fun _ ↦ 1 / 2) := by
  unfold calibrationError
  exact continuous_finset_sum _ fun group _ ↦
    (continuous_calibrationResidual () outcomeReport (fun _ ↦ 1 / 2) group).abs

/-- **The first process law has expected calibration error `1/4`.** -/
theorem expectedCalibrationError_firstKernel (x : BiallelicState) :
    expectedCalibrationError firstKernel x () outcomeReport (fun _ ↦ 1 / 2) = 1 / 4 := by
  rw [expectedCalibrationError, firstKernel, Kernel.const_apply,
    integral_firstLaw continuous_outcomeCalibrationError, quarterState, threeQuarterState,
    calibrationError_biallelicState, calibrationError_biallelicState,
    abs_of_nonpos (show (1 / 4 : ℝ) - 1 / 2 ≤ 0 by norm_num),
    abs_of_nonneg (show (0 : ℝ) ≤ 3 / 4 - 1 / 2 by norm_num)]
  norm_num

/-- **The second process law has expected calibration error `1/8`.** -/
theorem expectedCalibrationError_secondKernel (x : BiallelicState) :
    expectedCalibrationError secondKernel x () outcomeReport (fun _ ↦ 1 / 2) = 1 / 8 := by
  rw [expectedCalibrationError, secondKernel, Kernel.const_apply,
    integral_secondLaw continuous_outcomeCalibrationError, zeroState, halfState, oneState,
    calibrationError_biallelicState, calibrationError_biallelicState,
    calibrationError_biallelicState, abs_of_nonpos (show (0 : ℝ) - 1 / 2 ≤ 0 by norm_num),
    sub_self, abs_zero, abs_of_nonneg (show (0 : ℝ) ≤ 1 - 1 / 2 by norm_num)]
  norm_num

/-- **Degree three does not fix the calibration error.**  The two Markov kernels agree on every
frequency polynomial of total degree at most three, from any initial states, and give expected
calibration errors `1/4` and `1/8`. -/
theorem polynomialsAgreeAt_three_and_expectedCalibrationError_ne (x₁ x₂ : BiallelicState) :
    PolynomialsAgreeAt 3 firstKernel secondKernel x₁ x₂
      ∧ expectedCalibrationError firstKernel x₁ () outcomeReport (fun _ ↦ 1 / 2)
        ≠ expectedCalibrationError secondKernel x₂ () outcomeReport (fun _ ↦ 1 / 2) := by
  refine ⟨polynomialsAgreeAt_three x₁ x₂, ?_⟩
  rw [expectedCalibrationError_firstKernel, expectedCalibrationError_secondKernel]
  norm_num

/-- **No function of the budget-3 moments determines the expected calibration error**: agreement
on every frequency polynomial of degree at most three does not force equal expected calibration
error. -/
theorem not_forall_expectedCalibrationError_eq_of_polynomialsAgreeAt_three :
    ¬ ∀ (κ₁ κ₂ : Kernel BiallelicState BiallelicState) (x₁ x₂ : BiallelicState),
      PolynomialsAgreeAt 3 κ₁ κ₂ x₁ x₂ →
        expectedCalibrationError κ₁ x₁ () outcomeReport (fun _ ↦ 1 / 2)
          = expectedCalibrationError κ₂ x₂ () outcomeReport (fun _ ↦ 1 / 2) := fun h ↦
  (polynomialsAgreeAt_three_and_expectedCalibrationError_ne zeroState zeroState).2
    (h _ _ _ _ (polynomialsAgreeAt_three zeroState zeroState))

end

end Descent.Portability.EndToEndCalibrationErrorNonclosure
