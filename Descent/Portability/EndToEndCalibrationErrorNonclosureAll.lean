/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.EndToEndCalibrationErrorNonclosure
import Descent.Portability.MomentOrderObstruction

assert_below Descent.Decision Descent.Program

/-!
# No finite moment budget fixes the calibration error

`EndToEndCalibrationErrorNonclosure` separates two process laws that agree through degree three.
This module separates two process laws at every degree, which settles the question that
`EndToEndBrierLaw` leaves open: no finite rung of the moment ladder determines the expected
calibration error.

The witness.  Fix `n`.  The alternating binomial weights `(-1)^j C(n+2, j)` of the `(n+2)`-nd
forward difference, split by sign, are the two parity laws `MomentOrderObstruction.parityMass`
of order `n + 2` on the nodes `j = 0, …, n+2` (`MomentOrderObstruction.parityMass_nonneg`,
`MomentOrderObstruction.parityMass_sum`).  Node `j` carries the allele frequency
`q_j = 1/2 + (j - 1) h` with step `h = 1/(2(n+1))`, so every node lies in `[0, 1]`
(`frequencyStep`, `pointFrequency`, `pointFrequency_mem`, `pointState`).  Drawing the state from
either law gives two constant Markov kernels (`parityLaw`, `parityKernel`,
`isProbabilityMeasure_parityLaw`, `isMarkovKernel_parityKernel`).

Agreement through degree `n + 1`.  On any function of the node the two laws differ by
`2^{-(n+1)}` times its alternating binomial sum (`sum_parityMass_sub`).  At a biallelic state
every configuration moment of budget `n + 1` is `q^a (1 - q)^b` with `a + b ≤ n + 1`
(`EndToEndCalibrationErrorNonclosure.configurationMoment_frequencyLaw`), a polynomial of degree at
most `n + 1` in the node (`natDegree_frequencyProduct_le`), so the forward difference annihilates
it (`MomentOrderObstruction.alternating_annihilates`, `sum_parityMass_products_eq`,
`sum_parityMass_momentVector_eq`).  Every frequency polynomial of total degree at most `n + 1` is
a coefficient vector dotted with those moments (`eval_eq_budgetCoefficients_dotProduct_of_le`,
`dotProduct_weightedSum`), so the two kernels agree on all of them
(`polynomialsAgreeAt_parityKernel`).

The separation.  The calibration error at value `1/2` is `|q - 1/2| = |j - 1| h`
(`abs_pointFrequency_sub_half`, `expectedCalibrationError_parityKernel`).  On the nodes
`|j - 1|` is `j - 1` plus `2` at `j = 0`, and the forward difference kills the linear part, so
the alternating binomial sum of `|j - 1|` is `2` (`sum_alternating_abs`).  The two expected
calibration errors differ by `2 h / 2^(n+1)` (`expectedCalibrationError_parityKernel_sub`,
`expectedCalibrationError_parityKernel_ne`).  So for every `n` two Markov kernels agree on every
frequency polynomial of total degree at most `n` and give different expected calibration errors
(`polynomialsAgreeAt_and_expectedCalibrationError_ne`), and agreement at no finite degree forces
equal expected calibration error
(`not_forall_expectedCalibrationError_eq_of_polynomialsAgreeAt`).

Scope.  The witnesses are constant kernels of finite laws on the frequency state of one deme at
one biallelic locus, not histories of epochs.  The claim is non-identification: for every budget
there are two process laws that the budget's moments do not tell apart and that differ in
expected calibration error.  Which pairs of laws a history of epochs can produce is not settled
here.

## Empirical status

None.  The bodies here are finite sums of point masses, binomial identities, polynomial degree
bounds and rational arithmetic, so no measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.EndToEndCalibrationErrorNonclosureAll

open MeasureTheory ProbabilityTheory Descent.Coalescent PartialHaplotypeCarrier
  PartialHaplotypeDualGenerator PartialHaplotypeDualSemigroup NeutralFellerGenerator
  NeutralMomentSemigroup NeutralPolynomialSemigroup ReplicaMetricInstances EndToEndPortabilityLaw
  EndToEndBrierLaw PortabilityMomentLadder EndToEndAscertainedWitness EndToEndSelectionLaw
  EndToEndCalibrationErrorNonclosure MomentOrderObstruction

noncomputable section

/-! ## The nodes -/

/-- The frequency step `1/(2(n+1))` between consecutive nodes. -/
def frequencyStep (n : ℕ) : ℝ := 1 / (2 * ((n : ℝ) + 1))

/-- The frequency step is positive. -/
theorem frequencyStep_pos (n : ℕ) : 0 < frequencyStep n := by
  unfold frequencyStep
  positivity

/-- `n + 1` steps make one half. -/
theorem frequencyStep_mul (n : ℕ) : frequencyStep n * ((n : ℝ) + 1) = 1 / 2 := by
  unfold frequencyStep
  rw [div_mul_eq_mul_div, one_mul, div_eq_iff (by positivity)]
  ring

/-- The allele frequency `1/2 - h + j h` of node `j`. -/
def pointFrequency (n j : ℕ) : ℝ := 1 / 2 - frequencyStep n + j * frequencyStep n

/-- The nodes `j ≤ n + 2` carry frequencies in the unit interval. -/
theorem pointFrequency_mem (n : ℕ) (j : Fin (n + 1 + 2)) :
    0 ≤ pointFrequency n j ∧ pointFrequency n j ≤ 1 := by
  have hstep := frequencyStep_pos n
  have hmul := frequencyStep_mul n
  have hbound : (j : ℕ) ≤ n + 2 := by
    have := j.2
    omega
  have hj : ((j : ℕ) : ℝ) ≤ (n : ℝ) + 2 := by exact_mod_cast hbound
  have hupper : ((j : ℕ) : ℝ) * frequencyStep n ≤ ((n : ℝ) + 2) * frequencyStep n :=
    mul_le_mul_of_nonneg_right hj hstep.le
  have hlower : 0 ≤ ((j : ℕ) : ℝ) * frequencyStep n := mul_nonneg (Nat.cast_nonneg _) hstep.le
  have hhalf : frequencyStep n * 1 ≤ frequencyStep n * ((n : ℝ) + 1) :=
    mul_le_mul_of_nonneg_left (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]) hstep.le
  unfold pointFrequency
  constructor <;> linarith

/-- The biallelic state at node `j`. -/
def pointState (n : ℕ) (j : Fin (n + 1 + 2)) : BiallelicState :=
  biallelicState (pointFrequency n j) (pointFrequency_mem n j)

/-- The residual of node `j` at value `1/2` is `(j - 1) h`. -/
theorem abs_pointFrequency_sub_half (n j : ℕ) :
    |pointFrequency n j - 1 / 2| = |-1 + (j : ℝ)| * frequencyStep n := by
  rw [show pointFrequency n j - 1 / 2 = (-1 + (j : ℝ)) * frequencyStep n by
      unfold pointFrequency; ring,
    abs_mul, abs_of_pos (frequencyStep_pos n)]

/-! ## The two parity laws -/

/-- **The parity gap on the nodes.**  On any function of the node, the two parity laws of order
`k + 1` differ by `2^{-k}` times its alternating binomial sum. -/
theorem sum_parityMass_sub (k : ℕ) (g : ℕ → ℝ) :
    ∑ j : Fin (k + 2), parityMass k false j * g j - ∑ j : Fin (k + 2), parityMass k true j * g j
      = (∑ j ∈ Finset.range (k + 2), (-1 : ℝ) ^ j * ((k + 1).choose j : ℝ) * g j) / 2 ^ k := by
  rw [← Finset.sum_sub_distrib,
    Fin.sum_univ_eq_sum_range
      (fun j ↦ parityMass k false j * g j - parityMass k true j * g j) (k + 2),
    Finset.sum_div]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  have h0 : parityMass k false j = (|alternatingWeight k j| + alternatingWeight k j) / 2 := rfl
  have h1 : parityMass k true j = (|alternatingWeight k j| - alternatingWeight k j) / 2 := rfl
  rw [h0, h1]
  unfold alternatingWeight
  ring

/-- The parity law of sign `s`: node `j` with mass `parityMass (n + 1) s j`. -/
def parityLaw (n : ℕ) (s : Bool) : Measure BiallelicState :=
  ∑ j : Fin (n + 1 + 2), ENNReal.ofReal (parityMass (n + 1) s j) • Measure.dirac (pointState n j)

/-- A continuous observable integrates against a parity law to its weighted node values. -/
theorem integral_parityLaw (n : ℕ) (s : Bool) {f : BiallelicState → ℝ} (hf : Continuous f) :
    ∫ y, f y ∂(parityLaw n s)
      = ∑ j : Fin (n + 1 + 2), parityMass (n + 1) s j * f (pointState n j) := by
  have hintegrable : ∀ j : Fin (n + 1 + 2),
      Integrable f (ENNReal.ofReal (parityMass (n + 1) s j) • Measure.dirac (pointState n j)) :=
    fun j ↦ integrable_smul_dirac _ _ hf
  rw [parityLaw, integral_finset_sum_measure fun j _ ↦ hintegrable j]
  exact Finset.sum_congr rfl fun j _ ↦ integral_smul_dirac _ (parityMass_nonneg _ _ _) _ hf

/-- Each parity law is a probability measure. -/
theorem isProbabilityMeasure_parityLaw (n : ℕ) (s : Bool) :
    IsProbabilityMeasure (parityLaw n s) := by
  refine ⟨?_⟩
  rw [parityLaw, Measure.finset_sum_apply]
  simp only [Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  have hsum : ∑ j : Fin (n + 1 + 2), parityMass (n + 1) s j = 1 := parityMass_sum (n + 1) s
  rw [← ENNReal.ofReal_sum_of_nonneg (s := Finset.univ)
      (f := fun j : Fin (n + 1 + 2) ↦ parityMass (n + 1) s j) fun j _ ↦ parityMass_nonneg _ _ _,
    hsum, ENNReal.ofReal_one]

/-- The parity process law of sign `s`: every state moves to a draw from the parity law. -/
def parityKernel (n : ℕ) (s : Bool) : Kernel BiallelicState BiallelicState :=
  Kernel.const _ (parityLaw n s)

/-- Each parity process law is a Markov kernel. -/
theorem isMarkovKernel_parityKernel (n : ℕ) (s : Bool) : IsMarkovKernel (parityKernel n s) := by
  haveI := isProbabilityMeasure_parityLaw n s
  unfold parityKernel
  infer_instance

/-! ## Agreement through degree `n + 1` -/

/-- The product `X^a (1 - X)^b` has degree at most `a + b`. -/
theorem natDegree_frequencyProduct_le (a b : ℕ) :
    (Polynomial.X ^ a * (1 - Polynomial.X) ^ b : Polynomial ℝ).natDegree ≤ a + b := by
  have hX : (Polynomial.X : Polynomial ℝ).natDegree ≤ 1 := (Polynomial.natDegree_X (R := ℝ)).le
  have hY : (1 - Polynomial.X : Polynomial ℝ).natDegree ≤ 1 :=
    (Polynomial.natDegree_sub_le _ _).trans (max_le (by simp) hX)
  calc (Polynomial.X ^ a * (1 - Polynomial.X) ^ b : Polynomial ℝ).natDegree
      ≤ (Polynomial.X ^ a : Polynomial ℝ).natDegree
        + ((1 - Polynomial.X) ^ b : Polynomial ℝ).natDegree := Polynomial.natDegree_mul_le
    _ ≤ a * 1 + b * 1 :=
        add_le_add (Polynomial.natDegree_pow_le.trans (Nat.mul_le_mul le_rfl hX))
          (Polynomial.natDegree_pow_le.trans (Nat.mul_le_mul le_rfl hY))
    _ = a + b := by ring

/-- **The two parity laws weight every `q^a (1 - q)^b` with `a + b ≤ n + 1` equally.** -/
theorem sum_parityMass_products_eq (n a b : ℕ) (hab : a + b ≤ n + 1) :
    ∑ j : Fin (n + 1 + 2),
        parityMass (n + 1) false j * (pointFrequency n j ^ a * (1 - pointFrequency n j) ^ b)
      = ∑ j : Fin (n + 1 + 2),
        parityMass (n + 1) true j * (pointFrequency n j ^ a * (1 - pointFrequency n j) ^ b) := by
  have hzero := alternating_annihilates (n + 1) (1 / 2 - frequencyStep n) (frequencyStep n)
    (Polynomial.X ^ a * (1 - Polynomial.X) ^ b) ((natDegree_frequencyProduct_le a b).trans hab)
  simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_one,
    Polynomial.eval_X] at hzero
  have hgap := sum_parityMass_sub (n + 1) fun j ↦
    (1 / 2 - frequencyStep n + j * frequencyStep n) ^ a
      * (1 - (1 / 2 - frequencyStep n + j * frequencyStep n)) ^ b
  rw [hzero, zero_div, sub_eq_zero] at hgap
  exact hgap

/-- **The budget-`(n + 1)` moment vectors of the two parity laws agree.** -/
theorem sum_parityMass_momentVector_eq (n : ℕ)
    (η : BudgetConfiguration Unit Unit (fun _ : Unit ↦ Bool) (fun _ ↦ n + 1)) :
    ∑ j : Fin (n + 1 + 2),
        parityMass (n + 1) false j * momentVector (fun _ ↦ n + 1) (pointState n j) η
      = ∑ j : Fin (n + 1 + 2),
        parityMass (n + 1) true j * momentVector (fun _ ↦ n + 1) (pointState n j) η := by
  have hcard : Multiset.card η.1 ≤ n + 1 := by
    simpa using card_le_capacity_total (fun _ : Unit ↦ n + 1) η.1 η.2
  have hsplit := Multiset.card_eq_countP_add_countP
    (p := fun τ : PartialType Unit Unit (fun _ : Unit ↦ Bool) ↦ τ.allele () = some true) η.1
  simp only [momentVector, pointState, biallelicState, stateOfLaws, eval_momentPolynomial,
    configurationMoment_frequencyLaw]
  exact sum_parityMass_products_eq n _ _ (by omega)

/-- A frequency polynomial of total degree at most `m` evaluates at a biallelic state to the
corpus coefficient vector dotted with the budget-`m` moment vector. -/
theorem eval_eq_budgetCoefficients_dotProduct_of_le (m : ℕ)
    (p : FrequencyPolynomial Unit Unit fun _ : Unit ↦ Bool) (hp : p.totalDegree ≤ m)
    (y : BiallelicState) :
    MvPolynomial.eval y.1 p
      = budgetCoefficients () (fun _ ↦ m) p ⬝ᵥ momentVector (fun _ ↦ m) y :=
  eval_eq_dotProduct () (fun _ ↦ m) p (withinBudget_of_totalDegree_le () p hp) y

/-- The dot product with a weighted finite sum of vectors is the weighted sum of dot products. -/
theorem dotProduct_weightedSum {ι κ : Type*} [Fintype κ] (s : Finset ι) (c : κ → ℝ)
    (w : ι → ℝ) (v : ι → κ → ℝ) :
    c ⬝ᵥ ∑ i ∈ s, w i • v i = ∑ i ∈ s, w i * (c ⬝ᵥ v i) := by
  simp only [dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun x _ ↦ by ring

/-- **The two parity process laws agree on every frequency polynomial of total degree at most
`n + 1`.** -/
theorem polynomialsAgreeAt_parityKernel (n : ℕ) (x₁ x₂ : BiallelicState) :
    PolynomialsAgreeAt (n + 1) (parityKernel n false) (parityKernel n true) x₁ x₂ := by
  intro p hp
  have hcontinuous : Continuous fun y : BiallelicState ↦ polynomialFunction p y :=
    (polynomialFunction p).continuous
  have hvector :
      ∑ j : Fin (n + 1 + 2),
          parityMass (n + 1) false j • momentVector (fun _ ↦ n + 1) (pointState n j)
        = ∑ j : Fin (n + 1 + 2),
          parityMass (n + 1) true j • momentVector (fun _ ↦ n + 1) (pointState n j) := by
    funext η
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact sum_parityMass_momentVector_eq n η
  have hdot := congrArg (budgetCoefficients () (fun _ ↦ n + 1) p ⬝ᵥ ·) hvector
  simp only [dotProduct_weightedSum] at hdot
  rw [parityKernel, parityKernel, Kernel.const_apply, Kernel.const_apply,
    integral_parityLaw n false hcontinuous, integral_parityLaw n true hcontinuous]
  simp only [polynomialFunction_apply, eval_eq_budgetCoefficients_dotProduct_of_le (n + 1) p hp]
  linarith

/-! ## The separation -/

/-- The expected calibration error of a parity process law is the weighted residual at `1/2`. -/
theorem expectedCalibrationError_parityKernel (n : ℕ) (s : Bool) (x : BiallelicState) :
    expectedCalibrationError (parityKernel n s) x () outcomeReport (fun _ ↦ 1 / 2)
      = ∑ j : Fin (n + 1 + 2), parityMass (n + 1) s j * |pointFrequency n j - 1 / 2| := by
  rw [expectedCalibrationError, parityKernel, Kernel.const_apply,
    integral_parityLaw n s continuous_outcomeCalibrationError]
  simp only [pointState, calibrationError_biallelicState]

/-- **The alternating binomial sum of `|j - 1|` is `2`.**  On the nodes `|j - 1|` is `j - 1` plus
`2` at `j = 0`, and the forward difference of order `n + 2` kills the linear part. -/
theorem sum_alternating_abs (n : ℕ) :
    ∑ j ∈ Finset.range (n + 1 + 2), (-1 : ℝ) ^ j * ((n + 1 + 1).choose j : ℝ) * |-1 + (j : ℝ)|
      = 2 := by
  have hlinear := alternating_annihilates (n + 1) (-1) 1 Polynomial.X
    ((Polynomial.natDegree_X (R := ℝ)).trans_le (by omega))
  simp only [Polynomial.eval_X, mul_one] at hlinear
  have hpoint : ∀ j ∈ Finset.range (n + 1 + 2),
      (-1 : ℝ) ^ j * ((n + 1 + 1).choose j : ℝ) * |-1 + (j : ℝ)|
        = (-1 : ℝ) ^ j * ((n + 1 + 1).choose j : ℝ) * (-1 + (j : ℝ))
          + if j = 0 then 2 else 0 := by
    intro j _
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · norm_num
    · have h1 : (1 : ℝ) ≤ j := by exact_mod_cast hj
      rw [abs_of_nonneg (show (0 : ℝ) ≤ -1 + (j : ℝ) by linarith),
        if_neg (Nat.pos_iff_ne_zero.mp hj), add_zero]
  rw [Finset.sum_congr rfl hpoint, Finset.sum_add_distrib, hlinear, zero_add]
  simp

/-- **The two parity process laws differ in expected calibration error by `2 h / 2^(n+1)`.** -/
theorem expectedCalibrationError_parityKernel_sub (n : ℕ) (x₁ x₂ : BiallelicState) :
    expectedCalibrationError (parityKernel n false) x₁ () outcomeReport (fun _ ↦ 1 / 2)
      - expectedCalibrationError (parityKernel n true) x₂ () outcomeReport (fun _ ↦ 1 / 2)
      = 2 * frequencyStep n / 2 ^ (n + 1) := by
  rw [expectedCalibrationError_parityKernel, expectedCalibrationError_parityKernel,
    sum_parityMass_sub (n + 1) fun j ↦ |pointFrequency n j - 1 / 2|]
  have hpoint : ∀ j ∈ Finset.range (n + 1 + 2),
      (-1 : ℝ) ^ j * ((n + 1 + 1).choose j : ℝ) * |pointFrequency n j - 1 / 2|
        = (-1 : ℝ) ^ j * ((n + 1 + 1).choose j : ℝ) * |-1 + (j : ℝ)| * frequencyStep n := by
    intro j _
    rw [abs_pointFrequency_sub_half]
    ring
  rw [Finset.sum_congr rfl hpoint, ← Finset.sum_mul, sum_alternating_abs]

/-- **The two parity process laws give different expected calibration errors.** -/
theorem expectedCalibrationError_parityKernel_ne (n : ℕ) (x₁ x₂ : BiallelicState) :
    expectedCalibrationError (parityKernel n false) x₁ () outcomeReport (fun _ ↦ 1 / 2)
      ≠ expectedCalibrationError (parityKernel n true) x₂ () outcomeReport (fun _ ↦ 1 / 2) := by
  intro h
  have hgap := expectedCalibrationError_parityKernel_sub n x₁ x₂
  rw [h, sub_self] at hgap
  have hpos : 0 < 2 * frequencyStep n / 2 ^ (n + 1) :=
    div_pos (mul_pos two_pos (frequencyStep_pos n)) (pow_pos two_pos _)
  linarith

/-- **No finite degree fixes the calibration error.**  For every `n` the two parity process laws
agree on every frequency polynomial of total degree at most `n`, from any initial states, and
give different expected calibration errors. -/
theorem polynomialsAgreeAt_and_expectedCalibrationError_ne (n : ℕ) (x₁ x₂ : BiallelicState) :
    PolynomialsAgreeAt n (parityKernel n false) (parityKernel n true) x₁ x₂
      ∧ expectedCalibrationError (parityKernel n false) x₁ () outcomeReport (fun _ ↦ 1 / 2)
        ≠ expectedCalibrationError (parityKernel n true) x₂ () outcomeReport (fun _ ↦ 1 / 2) :=
  ⟨PolynomialsAgreeAt.mono (Nat.le_succ n) (polynomialsAgreeAt_parityKernel n x₁ x₂),
    expectedCalibrationError_parityKernel_ne n x₁ x₂⟩

/-- **No function of finitely many moments determines the expected calibration error**: at every
degree `n`, agreement on every frequency polynomial of degree at most `n` does not force equal
expected calibration error. -/
theorem not_forall_expectedCalibrationError_eq_of_polynomialsAgreeAt (n : ℕ) :
    ¬ ∀ (κ₁ κ₂ : Kernel BiallelicState BiallelicState) (x₁ x₂ : BiallelicState),
      PolynomialsAgreeAt n κ₁ κ₂ x₁ x₂ →
        expectedCalibrationError κ₁ x₁ () outcomeReport (fun _ ↦ 1 / 2)
          = expectedCalibrationError κ₂ x₂ () outcomeReport (fun _ ↦ 1 / 2) := fun h ↦
  (polynomialsAgreeAt_and_expectedCalibrationError_ne n zeroState zeroState).2
    (h _ _ _ _ (polynomialsAgreeAt_and_expectedCalibrationError_ne n zeroState zeroState).1)

end

end Descent.Portability.EndToEndCalibrationErrorNonclosureAll
