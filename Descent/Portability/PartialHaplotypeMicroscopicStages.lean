/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.PartialHaplotypeLineTaylor
import Descent.Portability.NeutralFellerGenerator
import Descent.Portability.FiniteMixtureKernel

assert_below Descent.Decision Descent.Program

/-!
# Microscopic stages of the neutral multi-deme model on partial-haplotype moments

NOTE1 §4.2a constructs the neutral semigroup from physical microscopic kernels.  This module
builds the two kinds of stage such a kernel is made of, on the multi-deme haplotype-frequency
simplex `NeutralFellerGenerator.FrequencyState`, and proves their first-order expansions against
the neutral generator of `PartialHaplotypeDualGenerator` for every frequency polynomial.

The resampling stage of deme `i` draws a haplotype `g` with probability `x_i[g]` and moves the
deme's frequencies a fraction `ε` toward the point mass at `g` (`resamplingMove`).  The direction
averages to zero and its second moment is the Wright–Fisher covariance, so the stage advances a
polynomial by `(ε² / 2)` times the deme's second-order operator, up to `B ε³`
(`resampling_expansion`).

The drift stage moves the state along the drift field, `x ↦ x + (ε / κ) μ(x)`, where `μ` is the
first-order drift of migration, recombination and mutation and `κ` bounds every rate
(`driftMove`).  The drift splits into a nonnegative inflow and an outflow proportional to the
frequency (`eval_driftPolynomial_eq`), and its deme totals vanish on the simplex
(`sum_driftPolynomial_eq_zero`), so the moved state stays in the simplex.  The stage advances a
polynomial by `ε / κ` times the drift derivative, up to `2 B ε²` (`drift_expansion`).  The
remainder constants are those of `PartialHaplotypeLineTaylor.exists_lineTaylor_bound`.

Scope.  The stages and their expansions only; the mixture kernel, the microscopic approximation of
the dual generator and the realized expectation family are assembled in a separate module.

## Empirical status

None.  The bodies here are algebra and elementary inequalities about polynomials on the simplex,
so no measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.PartialHaplotypeMicroscopicStages

open PartialHaplotypeCarrier PartialHaplotypeDualGenerator PartialHaplotypeLineTaylor
open NeutralFellerGenerator MvPolynomial

variable {Deme Locus : Type*} {Allele : Locus → Type*}
variable [Fintype Deme] [DecidableEq Deme] [Fintype Locus] [DecidableEq Locus]
  [∀ ℓ, Fintype (Allele ℓ)] [∀ ℓ, DecidableEq (Allele ℓ)]

noncomputable section

/-! ## States -/

/-- Every coordinate of a state lies in the unit interval. -/
theorem abs_state_le_one (x : FrequencyState Deme Locus Allele)
    (u : FrequencyVariable Deme Locus Allele) : |x.1 u| ≤ 1 := by
  rw [abs_of_nonneg (x.2.1 u)]
  calc x.1 u = x.1 (u.1, u.2) := rfl
    _ ≤ ∑ hap, x.1 (u.1, hap) :=
        Finset.single_le_sum (fun hap _ ↦ x.2.1 (u.1, hap)) (Finset.mem_univ u.2)
    _ = 1 := x.2.2 u.1

/-- At a state, a marginal frequency lies in the unit interval. -/
theorem eval_assignmentPolynomial_mem_unit (x : FrequencyState Deme Locus Allele) (i : Deme)
    (assignment : ∀ ℓ, Option (Allele ℓ)) :
    0 ≤ eval x.1 (assignmentPolynomial i assignment)
      ∧ eval x.1 (assignmentPolynomial i assignment) ≤ 1 := by
  rw [eval_assignmentPolynomial]
  refine ⟨Finset.sum_nonneg fun hap _ ↦ x.2.1 (i, hap), ?_⟩
  calc ∑ hap ∈ Finset.univ.filter (Satisfies assignment), x.1 (i, hap)
      ≤ ∑ hap, x.1 (i, hap) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          fun hap _ _ ↦ x.2.1 (i, hap)
    _ = 1 := x.2.2 i

/-! ## The resampling stage -/

/-- The resampling direction toward haplotype `g` in deme `i`: the deme's frequencies move
toward the point mass at `g`. -/
def resamplingDirection (i : Deme) (g : FullHaplotype Locus Allele)
    (x : FrequencyVariable Deme Locus Allele → ℝ) : FrequencyVariable Deme Locus Allele → ℝ :=
  fun w ↦ if w.1 = i then (if w.2 = g then 1 else 0) - x w else 0

/-- Resampling directions from a state lie in the box of radius two. -/
theorem abs_resamplingDirection_le (i : Deme) (g : FullHaplotype Locus Allele)
    (x : FrequencyState Deme Locus Allele) (w : FrequencyVariable Deme Locus Allele) :
    |resamplingDirection i g x.1 w| ≤ 2 := by
  have h0 := x.2.1 w
  have h1 := (abs_le.mp (abs_state_le_one x w)).2
  unfold resamplingDirection
  split_ifs <;> · rw [abs_le]; constructor <;> linarith

/-- Pairing a function with a resampling direction centres it at the deme frequencies. -/
theorem sum_mul_resamplingDirection (i : Deme) (g : FullHaplotype Locus Allele)
    (x F : FrequencyVariable Deme Locus Allele → ℝ) :
    ∑ u, F u * resamplingDirection i g x u = F (i, g) - ∑ k, x (i, k) * F (i, k) := by
  rw [Fintype.sum_prod_type, Finset.sum_eq_single i]
  · simp only [resamplingDirection, ↓reduceIte, mul_sub, mul_ite, mul_one, mul_zero,
      Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ]
    congr 1
    exact Finset.sum_congr rfl fun k _ ↦ mul_comm _ _
  · intro d _ hd
    simp [resamplingDirection, hd]
  · intro hnot
    exact absurd (Finset.mem_univ i) hnot

/-- A resampling move keeps the state in the simplex. -/
theorem resamplingMove_mem (i : Deme) (g : FullHaplotype Locus Allele) (ε : ℝ) (hε0 : 0 ≤ ε)
    (hε1 : ε ≤ 1) (x : FrequencyState Deme Locus Allele) :
    x.1 + ε • resamplingDirection i g x.1 ∈ frequencySimplex Deme Locus Allele := by
  refine ⟨fun w ↦ ?_, fun d ↦ ?_⟩
  · have h0 := x.2.1 w
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, resamplingDirection]
    split_ifs <;> nlinarith
  · have hsum : ∑ hap, resamplingDirection i g x.1 (d, hap) = 0 := by
      by_cases hd : d = i
      · rw [hd]
        simp only [resamplingDirection, ↓reduceIte, Finset.sum_sub_distrib, Finset.sum_ite_eq',
          Finset.mem_univ, x.2.2 i, sub_self]
      · simp [resamplingDirection, hd]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib, ← Finset.mul_sum,
      hsum, x.2.2 d, mul_zero, add_zero]

/-- The resampling move toward haplotype `g` in deme `i`, as a state. -/
def resamplingMove (i : Deme) (g : FullHaplotype Locus Allele) (ε : ℝ) (hε0 : 0 ≤ ε)
    (hε1 : ε ≤ 1) (x : FrequencyState Deme Locus Allele) : FrequencyState Deme Locus Allele :=
  ⟨x.1 + ε • resamplingDirection i g x.1, resamplingMove_mem i g ε hε0 hε1 x⟩

/-- The weighted centred quadratic form of a probability vector: centring at the weights turns
`E` into the Wright–Fisher form `Σ_g q_g E_{gg} − Σ_{g,k} q_g q_k E_{gk}`. -/
theorem weighted_centered_quadratic {ι : Type*} [Fintype ι] (q : ι → ℝ) (hq : ∑ g, q g = 1)
    (E : ι → ι → ℝ) :
    ∑ g, q g * ((E g g - ∑ k, q k * E g k) - ∑ m, q m * (E m g - ∑ k, q k * E m k))
      = ∑ g, q g * E g g - ∑ g, ∑ k, q g * q k * E g k := by
  have ha : ∑ g, q g * ∑ k, q k * E g k = ∑ g, ∑ k, q g * q k * E g k :=
    Finset.sum_congr rfl fun g _ ↦ by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ ↦ by ring
  have hb : ∑ g, q g * ∑ m, q m * E m g = ∑ g, ∑ k, q g * q k * E g k := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun m _ ↦ Finset.sum_congr rfl fun g _ ↦ by ring
  have hc : ∑ g, q g * ∑ m, q m * ∑ k, q k * E m k = ∑ g, ∑ k, q g * q k * E g k := by
    rw [← Finset.sum_mul, hq, one_mul]
    exact Finset.sum_congr rfl fun m _ ↦ by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ ↦ by ring
  have hexpand : ∀ g, q g * ((E g g - ∑ k, q k * E g k) - ∑ m, q m * (E m g - ∑ k, q k * E m k))
      = q g * E g g - q g * ∑ k, q k * E g k - q g * ∑ m, q m * E m g
        + q g * ∑ m, q m * ∑ k, q k * E m k := by
    intro g
    simp only [mul_sub, Finset.mul_sum, Finset.sum_sub_distrib]
    ring
  rw [Finset.sum_congr rfl fun g _ ↦ hexpand g]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [ha, hb, hc]
  ring

/-- Averaged over the drawn haplotype, the directional derivative along the resampling
direction vanishes. -/
theorem sum_weight_directionalDerivative (p : FrequencyPolynomial Deme Locus Allele) (i : Deme)
    (x : FrequencyState Deme Locus Allele) :
    ∑ g, x.1 (i, g) * directionalDerivative p x.1 (resamplingDirection i g x.1) = 0 := by
  simp only [directionalDerivative, sum_mul_resamplingDirection, mul_sub,
    Finset.sum_sub_distrib, ← Finset.sum_mul, x.2.2 i, one_mul, sub_self]

/-- Averaged over the drawn haplotype, the second directional derivative along the resampling
direction is the Wright–Fisher second-order operator of the deme. -/
theorem sum_weight_secondDirectionalDerivative (p : FrequencyPolynomial Deme Locus Allele)
    (i : Deme) (x : FrequencyState Deme Locus Allele) :
    ∑ g, x.1 (i, g) * secondDirectionalDerivative p x.1 (resamplingDirection i g x.1)
      = eval x.1 (demeSecondOrder i p) := by
  have hinner : ∀ (g : FullHaplotype Locus Allele) (u : FrequencyVariable Deme Locus Allele),
      ∑ w, eval x.1 (pderiv u (pderiv w p)) * resamplingDirection i g x.1 w
        = eval x.1 (pderiv u (pderiv (i, g) p))
          - ∑ k, x.1 (i, k) * eval x.1 (pderiv u (pderiv (i, k) p)) :=
    fun g u ↦ sum_mul_resamplingDirection i g x.1 fun w ↦ eval x.1 (pderiv u (pderiv w p))
  have hsecond : ∀ g, secondDirectionalDerivative p x.1 (resamplingDirection i g x.1)
      = (eval x.1 (pderiv (i, g) (pderiv (i, g) p))
          - ∑ k, x.1 (i, k) * eval x.1 (pderiv (i, g) (pderiv (i, k) p)))
        - ∑ m, x.1 (i, m) * (eval x.1 (pderiv (i, m) (pderiv (i, g) p))
          - ∑ k, x.1 (i, k) * eval x.1 (pderiv (i, m) (pderiv (i, k) p))) := by
    intro g
    have hrow : secondDirectionalDerivative p x.1 (resamplingDirection i g x.1)
        = ∑ u, (∑ w, eval x.1 (pderiv u (pderiv w p)) * resamplingDirection i g x.1 w)
            * resamplingDirection i g x.1 u := by
      rw [secondDirectionalDerivative]
      refine Finset.sum_congr rfl fun u _ ↦ ?_
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun w _ ↦ by ring
    rw [hrow]
    simp only [hinner g]
    exact sum_mul_resamplingDirection i g x.1 fun u ↦
      eval x.1 (pderiv u (pderiv (i, g) p))
        - ∑ k, x.1 (i, k) * eval x.1 (pderiv u (pderiv (i, k) p))
  simp only [hsecond]
  rw [demeSecondOrder, map_sub, map_sum, map_sum]
  simp only [map_mul, map_sum, eval_X]
  exact weighted_centered_quadratic (fun g ↦ x.1 (i, g)) (x.2.2 i)
    fun g k ↦ eval x.1 (pderiv (i, g) (pderiv (i, k) p))

/-- **The resampling stage expansion.**  Averaged over the drawn haplotype, the resampling move of
deme `i` advances a frequency polynomial by `ε² / 2` times the deme's Wright–Fisher operator, up
to `B ε³`, where `B` bounds the segment remainders of the polynomial. -/
theorem resampling_expansion (i : Deme) (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (p : FrequencyPolynomial Deme Locus Allele) (B : ℝ)
    (hB : ∀ x v : FrequencyVariable Deme Locus Allele → ℝ, (∀ u, |x u| ≤ 1) → (∀ u, |v u| ≤ 2) →
      ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 → |lineRemainder p x v ε| ≤ B * ε ^ 3)
    (x : FrequencyState Deme Locus Allele) :
    |∑ g, x.1 (i, g) * eval (resamplingMove i g ε hε0 hε1 x).1 p - eval x.1 p
        - ε ^ 2 / 2 * eval x.1 (demeSecondOrder i p)| ≤ B * ε ^ 3 := by
  have hweighted : ∀ g, x.1 (i, g) * eval (resamplingMove i g ε hε0 hε1 x).1 p
      = x.1 (i, g) * eval x.1 p
        + ε * (x.1 (i, g) * directionalDerivative p x.1 (resamplingDirection i g x.1))
        + ε ^ 2 / 2
          * (x.1 (i, g) * secondDirectionalDerivative p x.1 (resamplingDirection i g x.1))
        + x.1 (i, g) * lineRemainder p x.1 (resamplingDirection i g x.1) ε := by
    intro g
    show x.1 (i, g) * eval (x.1 + ε • resamplingDirection i g x.1) p = _
    rw [lineRemainder]
    ring
  have hsplit : ∑ g, x.1 (i, g) * eval (resamplingMove i g ε hε0 hε1 x).1 p - eval x.1 p
        - ε ^ 2 / 2 * eval x.1 (demeSecondOrder i p)
      = ∑ g, x.1 (i, g) * lineRemainder p x.1 (resamplingDirection i g x.1) ε := by
    simp only [hweighted, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul, x.2.2 i,
      one_mul, sum_weight_directionalDerivative, mul_zero, add_zero,
      sum_weight_secondDirectionalDerivative]
    ring
  rw [hsplit]
  calc |∑ g, x.1 (i, g) * lineRemainder p x.1 (resamplingDirection i g x.1) ε|
      ≤ ∑ g, |x.1 (i, g) * lineRemainder p x.1 (resamplingDirection i g x.1) ε| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ g, x.1 (i, g) * (B * ε ^ 3) := Finset.sum_le_sum fun g _ ↦ by
        rw [abs_mul, abs_of_nonneg (x.2.1 (i, g))]
        exact mul_le_mul_of_nonneg_left
          (hB x.1 _ (abs_state_le_one x) (abs_resamplingDirection_le i g x) ε hε0 hε1)
          (x.2.1 (i, g))
    _ = B * ε ^ 3 := by rw [← Finset.sum_mul, x.2.2 i, one_mul]

/-! ## The drift stage -/

/-- The inflow into a haplotype frequency: migrants, recombinants and mutants. -/
def driftInflow (rates : NeutralRates Deme Locus Allele)
    (x : FrequencyVariable Deme Locus Allele → ℝ) (u : FrequencyVariable Deme Locus Allele) : ℝ :=
  (∑ j, rates.migration u.1 j * x (j, u.2))
    + (∑ selector : Locus → Bool, rates.recombination selector *
        (eval x (assignmentPolynomial u.1
            (restrictAssignment (fun ℓ ↦ some (u.2 ℓ)) selector))
          * eval x (assignmentPolynomial u.1
            (restrictAssignment (fun ℓ ↦ some (u.2 ℓ)) fun ℓ ↦ !selector ℓ))))
    + ∑ ℓ, ∑ b : Allele ℓ, rates.mutation ℓ b (u.2 ℓ) * x (u.1, Function.update u.2 ℓ b)

/-- The total outflow rate of a haplotype frequency. -/
def driftOutflow (rates : NeutralRates Deme Locus Allele)
    (u : FrequencyVariable Deme Locus Allele) : ℝ :=
  (∑ j, rates.migration u.1 j) + (∑ selector : Locus → Bool, rates.recombination selector)
    + ∑ ℓ, ∑ b : Allele ℓ, rates.mutation ℓ (u.2 ℓ) b

/-- The drift of a haplotype frequency is its inflow minus its outflow rate times the
frequency. -/
theorem eval_driftPolynomial_eq (rates : NeutralRates Deme Locus Allele)
    (x : FrequencyVariable Deme Locus Allele → ℝ) (u : FrequencyVariable Deme Locus Allele) :
    eval x (driftPolynomial rates u) = driftInflow rates x u - driftOutflow rates u * x u := by
  simp only [driftPolynomial, driftInflow, driftOutflow, map_add, map_sum, map_mul, map_sub, eval_C,
    eval_X, mul_sub, Finset.sum_sub_distrib, add_mul, Finset.sum_mul]
  ring

/-- A bound for every rate of the model, at least one. -/
def rateScale (rates : NeutralRates Deme Locus Allele) : ℝ :=
  1 + (∑ i, ∑ j, rates.migration i j) + (∑ selector : Locus → Bool, rates.recombination selector)
    + ∑ ℓ, ∑ a : Allele ℓ, ∑ b : Allele ℓ, rates.mutation ℓ a b

/-- The rate scale is at least one. -/
theorem one_le_rateScale (rates : NeutralRates Deme Locus Allele) : 1 ≤ rateScale rates := by
  have hm : 0 ≤ ∑ i, ∑ j, rates.migration i j :=
    Finset.sum_nonneg fun i _ ↦ Finset.sum_nonneg fun j _ ↦ rates.migration_nonneg i j
  have hr : 0 ≤ ∑ selector : Locus → Bool, rates.recombination selector :=
    Finset.sum_nonneg fun s _ ↦ rates.recombination_nonneg s
  have hu : 0 ≤ ∑ ℓ, ∑ a : Allele ℓ, ∑ b : Allele ℓ, rates.mutation ℓ a b :=
    Finset.sum_nonneg fun ℓ _ ↦ Finset.sum_nonneg fun a _ ↦
      Finset.sum_nonneg fun b _ ↦ rates.mutation_nonneg ℓ a b
  unfold rateScale
  linarith

/-- The outflow rate lies between zero and the rate scale. -/
theorem driftOutflow_mem (rates : NeutralRates Deme Locus Allele)
    (u : FrequencyVariable Deme Locus Allele) :
    0 ≤ driftOutflow rates u ∧ driftOutflow rates u ≤ rateScale rates := by
  have hm : ∑ j, rates.migration u.1 j ≤ ∑ i, ∑ j, rates.migration i j :=
    Finset.single_le_sum (f := fun i ↦ ∑ j, rates.migration i j)
      (fun i _ ↦ Finset.sum_nonneg fun j _ ↦ rates.migration_nonneg i j) (Finset.mem_univ u.1)
  have hu : ∑ ℓ, ∑ b : Allele ℓ, rates.mutation ℓ (u.2 ℓ) b
      ≤ ∑ ℓ, ∑ a : Allele ℓ, ∑ b : Allele ℓ, rates.mutation ℓ a b :=
    Finset.sum_le_sum fun ℓ _ ↦ Finset.single_le_sum (f := fun a ↦ ∑ b, rates.mutation ℓ a b)
      (fun a _ ↦ Finset.sum_nonneg fun b _ ↦ rates.mutation_nonneg ℓ a b) (Finset.mem_univ _)
  have hm0 : 0 ≤ ∑ j, rates.migration u.1 j :=
    Finset.sum_nonneg fun j _ ↦ rates.migration_nonneg _ j
  have hr0 : 0 ≤ ∑ selector : Locus → Bool, rates.recombination selector :=
    Finset.sum_nonneg fun s _ ↦ rates.recombination_nonneg s
  have hu0 : 0 ≤ ∑ ℓ, ∑ b : Allele ℓ, rates.mutation ℓ (u.2 ℓ) b :=
    Finset.sum_nonneg fun ℓ _ ↦ Finset.sum_nonneg fun b _ ↦ rates.mutation_nonneg _ _ _
  unfold driftOutflow rateScale
  constructor <;> linarith

/-- At a state, the inflow lies between zero and the rate scale. -/
theorem driftInflow_mem (rates : NeutralRates Deme Locus Allele)
    (x : FrequencyState Deme Locus Allele) (u : FrequencyVariable Deme Locus Allele) :
    0 ≤ driftInflow rates x.1 u ∧ driftInflow rates x.1 u ≤ rateScale rates := by
  have hmig0 : 0 ≤ ∑ j, rates.migration u.1 j * x.1 (j, u.2) :=
    Finset.sum_nonneg fun j _ ↦ mul_nonneg (rates.migration_nonneg _ j) (x.2.1 _)
  have hmig1 : ∑ j, rates.migration u.1 j * x.1 (j, u.2) ≤ ∑ j, rates.migration u.1 j :=
    Finset.sum_le_sum fun j _ ↦ mul_le_of_le_one_right (rates.migration_nonneg _ j)
      (abs_le.mp (abs_state_le_one x _)).2
  have hrec0 : 0 ≤ ∑ selector : Locus → Bool, rates.recombination selector *
        (eval x.1 (assignmentPolynomial u.1
            (restrictAssignment (fun ℓ ↦ some (u.2 ℓ)) selector))
          * eval x.1 (assignmentPolynomial u.1
            (restrictAssignment (fun ℓ ↦ some (u.2 ℓ)) fun ℓ ↦ !selector ℓ))) :=
    Finset.sum_nonneg fun s _ ↦ mul_nonneg (rates.recombination_nonneg s)
      (mul_nonneg (eval_assignmentPolynomial_mem_unit x _ _).1
        (eval_assignmentPolynomial_mem_unit x _ _).1)
  have hrec1 : ∑ selector : Locus → Bool, rates.recombination selector *
        (eval x.1 (assignmentPolynomial u.1
            (restrictAssignment (fun ℓ ↦ some (u.2 ℓ)) selector))
          * eval x.1 (assignmentPolynomial u.1
            (restrictAssignment (fun ℓ ↦ some (u.2 ℓ)) fun ℓ ↦ !selector ℓ)))
      ≤ ∑ selector : Locus → Bool, rates.recombination selector :=
    Finset.sum_le_sum fun s _ ↦ mul_le_of_le_one_right (rates.recombination_nonneg s)
      (mul_le_one₀ (eval_assignmentPolynomial_mem_unit x _ _).2
        (eval_assignmentPolynomial_mem_unit x _ _).1 (eval_assignmentPolynomial_mem_unit x _ _).2)
  have hmut0 : 0 ≤ ∑ ℓ, ∑ b : Allele ℓ,
      rates.mutation ℓ b (u.2 ℓ) * x.1 (u.1, Function.update u.2 ℓ b) :=
    Finset.sum_nonneg fun ℓ _ ↦ Finset.sum_nonneg fun b _ ↦
      mul_nonneg (rates.mutation_nonneg _ _ _) (x.2.1 _)
  have hmut1 : ∑ ℓ, ∑ b : Allele ℓ,
      rates.mutation ℓ b (u.2 ℓ) * x.1 (u.1, Function.update u.2 ℓ b)
      ≤ ∑ ℓ, ∑ a : Allele ℓ, ∑ b : Allele ℓ, rates.mutation ℓ a b := by
    refine Finset.sum_le_sum fun ℓ _ ↦ ?_
    rw [Finset.sum_comm]
    exact Finset.single_le_sum (f := fun a ↦ ∑ b, rates.mutation ℓ a b)
      (fun a _ ↦ Finset.sum_nonneg fun b _ ↦ rates.mutation_nonneg ℓ a b) (Finset.mem_univ _)
      |>.trans' (Finset.sum_le_sum fun b _ ↦ mul_le_of_le_one_right
        (rates.mutation_nonneg _ _ _) (abs_le.mp (abs_state_le_one x _)).2)
  have hm : ∑ j, rates.migration u.1 j ≤ ∑ i, ∑ j, rates.migration i j :=
    Finset.single_le_sum (f := fun i ↦ ∑ j, rates.migration i j)
      (fun i _ ↦ Finset.sum_nonneg fun j _ ↦ rates.migration_nonneg i j) (Finset.mem_univ u.1)
  unfold driftInflow rateScale
  constructor <;> linarith

/-- On the simplex the drift of every deme total vanishes. -/
theorem sum_driftPolynomial_eq_zero (rates : NeutralRates Deme Locus Allele)
    (x : FrequencyState Deme Locus Allele) (i : Deme) :
    ∑ hap, eval x.1 (driftPolynomial rates (i, hap)) = 0 := by
  have hall : Finset.univ.filter (Satisfies fun ℓ ↦ (none : Option (Allele ℓ)))
      = (Finset.univ : Finset (FullHaplotype Locus Allele)) :=
    Finset.filter_true_of_mem fun _ _ _ ↦ Or.inl rfl
  have htotal : ∀ j, eval x.1 (assignmentPolynomial j fun ℓ ↦ (none : Option (Allele ℓ))) = 1 := by
    intro j
    rw [eval_assignmentPolynomial, hall]
    exact x.2.2 j
  have hmigration := sum_migrationDrift rates x.1 i fun ℓ ↦ (none : Option (Allele ℓ))
  rw [hall] at hmigration
  simp only [htotal, sub_self, mul_zero, Finset.sum_const_zero] at hmigration
  have hmutation : ∀ ℓ, ∑ hap : FullHaplotype Locus Allele, ∑ b : Allele ℓ,
      (rates.mutation ℓ b (hap ℓ) * x.1 (i, Function.update hap ℓ b)
        - rates.mutation ℓ (hap ℓ) b * x.1 (i, hap)) = 0 := by
    intro ℓ
    have h := mutationDrift_unassigned rates x.1 i (fun ℓ ↦ (none : Option (Allele ℓ))) ℓ rfl
    rwa [hall] at h
  have hnone : ∀ selector : Locus → Bool,
      restrictAssignment (fun ℓ ↦ (none : Option (Allele ℓ))) selector = fun ℓ ↦ none := by
    intro selector
    funext ℓ
    simp [restrictAssignment]
  have hrecombination : ∀ selector : Locus → Bool,
      ∑ hap : FullHaplotype Locus Allele, rates.recombination selector *
        (eval x.1 (assignmentPolynomial i
            (restrictAssignment (fun ℓ ↦ some (hap ℓ)) selector))
          * eval x.1 (assignmentPolynomial i
            (restrictAssignment (fun ℓ ↦ some (hap ℓ)) fun ℓ ↦ !selector ℓ))
          - x.1 (i, hap)) = 0 := by
    intro selector
    have h := sum_recombinantProduct x.1 i (fun ℓ ↦ (none : Option (Allele ℓ))) selector
    rw [hall, hnone, hnone, sum_satisfies_none x.1 x.2.2 i] at h
    rw [← Finset.mul_sum, Finset.sum_sub_distrib, x.2.2 i]
    simp only [eval_assignmentPolynomial]
    rw [h, mul_one, sub_self, mul_zero]
  simp only [driftPolynomial, map_add, map_sum, map_mul, map_sub, eval_C, eval_X,
    Finset.sum_add_distrib]
  rw [hmigration, Finset.sum_comm, Finset.sum_congr rfl fun s _ ↦ hrecombination s,
    Finset.sum_const_zero, Finset.sum_comm, Finset.sum_congr rfl fun ℓ _ ↦ hmutation ℓ,
    Finset.sum_const_zero]
  ring

/-- The drift direction: the drift field scaled by the rate scale. -/
def driftDirection (rates : NeutralRates Deme Locus Allele)
    (x : FrequencyVariable Deme Locus Allele → ℝ) : FrequencyVariable Deme Locus Allele → ℝ :=
  fun u ↦ eval x (driftPolynomial rates u) / rateScale rates

/-- Drift directions from a state lie in the box of radius two. -/
theorem abs_driftDirection_le (rates : NeutralRates Deme Locus Allele)
    (x : FrequencyState Deme Locus Allele) (u : FrequencyVariable Deme Locus Allele) :
    |driftDirection rates x.1 u| ≤ 2 := by
  have hscale := one_le_rateScale rates
  have hin := driftInflow_mem rates x u
  have hout := driftOutflow_mem rates u
  have hx0 := x.2.1 u
  have hx1 := (abs_le.mp (abs_state_le_one x u)).2
  have hprod : driftOutflow rates u * x.1 u ≤ rateScale rates :=
    (mul_le_of_le_one_right hout.1 hx1).trans hout.2
  have hprod0 : 0 ≤ driftOutflow rates u * x.1 u := mul_nonneg hout.1 hx0
  rw [driftDirection, eval_driftPolynomial_eq, abs_div, abs_of_pos (by linarith),
    div_le_iff₀ (by linarith), abs_le]
  constructor <;> linarith

/-- A drift move keeps the state in the simplex. -/
theorem driftMove_mem (rates : NeutralRates Deme Locus Allele) (ε : ℝ) (hε0 : 0 ≤ ε)
    (hε1 : ε ≤ 1) (x : FrequencyState Deme Locus Allele) :
    x.1 + ε • driftDirection rates x.1 ∈ frequencySimplex Deme Locus Allele := by
  have hscale := one_le_rateScale rates
  refine ⟨fun u ↦ ?_, fun d ↦ ?_⟩
  · have hin := (driftInflow_mem rates x u).1
    have hout := driftOutflow_mem rates u
    have hx0 := x.2.1 u
    have hfrac : 0 ≤ 1 - ε * driftOutflow rates u / rateScale rates := by
      rw [sub_nonneg, div_le_one (by linarith)]
      nlinarith
    have hkey : x.1 u + ε * driftDirection rates x.1 u
        = x.1 u * (1 - ε * driftOutflow rates u / rateScale rates)
          + ε * driftInflow rates x.1 u / rateScale rates := by
      rw [driftDirection, eval_driftPolynomial_eq]
      field_simp
      ring
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [hkey]
    exact add_nonneg (mul_nonneg hx0 hfrac) (div_nonneg (mul_nonneg hε0 hin) (by linarith))
  · have hsum : ∑ hap, driftDirection rates x.1 (d, hap) = 0 := by
      simp only [driftDirection, ← Finset.sum_div, sum_driftPolynomial_eq_zero rates x d,
        zero_div]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib, ← Finset.mul_sum,
      hsum, x.2.2 d, mul_zero, add_zero]

/-- The drift move as a state. -/
def driftMove (rates : NeutralRates Deme Locus Allele) (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (x : FrequencyState Deme Locus Allele) : FrequencyState Deme Locus Allele :=
  ⟨x.1 + ε • driftDirection rates x.1, driftMove_mem rates ε hε0 hε1 x⟩

/-- **The drift stage expansion.**  The drift move advances a frequency polynomial by
`ε / κ` times its drift derivative, up to `2 B ε²`, where `B` bounds the second directional
derivatives and segment remainders of the polynomial. -/
theorem drift_expansion (rates : NeutralRates Deme Locus Allele) (ε : ℝ) (hε0 : 0 ≤ ε)
    (hε1 : ε ≤ 1) (p : FrequencyPolynomial Deme Locus Allele) (B : ℝ) (hB0 : 0 ≤ B)
    (hB : ∀ x v : FrequencyVariable Deme Locus Allele → ℝ, (∀ u, |x u| ≤ 1) → (∀ u, |v u| ≤ 2) →
      ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 →
        |secondDirectionalDerivative p x v| ≤ B ∧ |lineRemainder p x v ε| ≤ B * ε ^ 3)
    (x : FrequencyState Deme Locus Allele) :
    |eval (driftMove rates ε hε0 hε1 x).1 p - eval x.1 p
        - ε / rateScale rates * eval x.1 (∑ u, driftPolynomial rates u * pderiv u p)|
      ≤ 2 * B * ε ^ 2 := by
  have hscale := one_le_rateScale rates
  obtain ⟨hsecond, hrem⟩ :=
    hB x.1 (driftDirection rates x.1) (abs_state_le_one x) (abs_driftDirection_le rates x) ε hε0
      hε1
  have hdirectional : ε * directionalDerivative p x.1 (driftDirection rates x.1)
      = ε / rateScale rates * eval x.1 (∑ u, driftPolynomial rates u * pderiv u p) := by
    rw [directionalDerivative, map_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun u _ ↦ ?_
    rw [map_mul, driftDirection]
    field_simp
    ring
  have hsplit : eval (driftMove rates ε hε0 hε1 x).1 p - eval x.1 p
        - ε / rateScale rates * eval x.1 (∑ u, driftPolynomial rates u * pderiv u p)
      = ε ^ 2 / 2 * secondDirectionalDerivative p x.1 (driftDirection rates x.1)
        + lineRemainder p x.1 (driftDirection rates x.1) ε := by
    rw [← hdirectional]
    show eval (x.1 + ε • driftDirection rates x.1) p - _ - _ = _
    rw [lineRemainder]
    ring
  rw [hsplit]
  have hε2 : 0 ≤ ε ^ 2 := sq_nonneg ε
  have hε3 : ε ^ 3 ≤ ε ^ 2 := by nlinarith [hε0, hε1]
  calc |ε ^ 2 / 2 * secondDirectionalDerivative p x.1 (driftDirection rates x.1)
        + lineRemainder p x.1 (driftDirection rates x.1) ε|
      ≤ |ε ^ 2 / 2 * secondDirectionalDerivative p x.1 (driftDirection rates x.1)|
        + |lineRemainder p x.1 (driftDirection rates x.1) ε| := abs_add_le _ _
    _ = ε ^ 2 / 2 * |secondDirectionalDerivative p x.1 (driftDirection rates x.1)|
        + |lineRemainder p x.1 (driftDirection rates x.1) ε| := by
      rw [abs_mul, abs_of_nonneg (div_nonneg hε2 zero_le_two)]
    _ ≤ ε ^ 2 / 2 * B + B * ε ^ 3 :=
      add_le_add (mul_le_mul_of_nonneg_left hsecond (div_nonneg hε2 zero_le_two)) hrem
    _ ≤ 2 * B * ε ^ 2 := by nlinarith [mul_le_mul_of_nonneg_left hε3 hB0]

end

end Descent.Portability.PartialHaplotypeMicroscopicStages
