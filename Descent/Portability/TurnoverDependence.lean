/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.TraitPortabilityRange

assert_below Descent.Decision Descent.Program

/-!
# Exact turnover dependence of expected portability

Effect turnover is carried by a sign configuration on the causal loci. Each
configuration defines a complete finite scored-genotype/outcome population
(`turnoverWorld`), whose `R²` is computed from that population by the master
formula of `PortabilityMasterTheorem` rather than postulated. The expected `R²`
over a joint sign law is then the exact quadratic form of TQ Theorem 3.5 in the
cross-locus second-moment matrix, so one-locus retention values alone do not
determine it. TQ Theorem 3.7 exhibits two joint laws, independent signs and one
shared sign, with identical one-locus laws and different expected `R²`, and TQ
Corollary 3.8 gives the exact arbitrary-weight time law together with the sharp
criterion for the direction of change. This module builds on `uniformExp`,
`weightedExp`, `DeploymentPopulation` and `r2` of `PortabilityMasterTheorem`, on
`variance` and `covariance` of `TransportIdentities`, and reuses the sign map of
`TraitPortabilityRange`. Hypotheses are only finiteness of the locus set, the
sign law's own normalisation, and positivity of the genetic variance wherever a
ratio is evaluated.

## Empirical status

None. The bodies here are algebra: a weight vector, an effect vector, a noise
scale and a sign law are inputs, and every definition is a sum, a product or a
ratio of them. What would carry an empirical status is a named quantity claiming
that one of these algebraic expressions is a measured retention or a measured
accuracy; no definition here makes that claim.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.TurnoverDependence

open Foundations

noncomputable section

section Signs

/-- Rademacher value of a Boolean coordinate: the sign map already used by
`TraitPortabilityRange`, reused rather than redefined. -/
def sgn (b : Bool) : ℝ := TraitPortabilityRange.sign b

/-- `sgn true = 1`. -/
@[simp] theorem sgn_true : sgn true = 1 := by
  simp [sgn, TraitPortabilityRange.sign]

/-- `sgn false = -1`. -/
@[simp] theorem sgn_false : sgn false = -1 := by
  simp [sgn, TraitPortabilityRange.sign]

/-- A sign takes only the two values `±1`. -/
theorem sgn_cases (b : Bool) : sgn b = 1 ∨ sgn b = -1 := by
  cases b
  · exact Or.inr sgn_false
  · exact Or.inl sgn_true

/-- Signs square to one. -/
@[simp] theorem sgn_sq (b : Bool) : sgn b ^ 2 = 1 := by
  cases b <;> norm_num

/-- A sum over Boolean configurations of a coordinatewise product factorises into a
product of two-point sums. -/
theorem sum_prod_bool {k : ℕ} (f : Fin k → Bool → ℝ) :
    ∑ z : Fin k → Bool, ∏ i, f i (z i) = ∏ i, (f i true + f i false) := by
  rw [← Fintype.prod_sum]
  exact Finset.prod_congr rfl fun i _ ↦ Fintype.sum_bool (f i)

/-- A product whose factors are `g` at one index and `1` elsewhere. -/
theorem prod_one_index {k : ℕ} (i : Fin k) (g : Fin k → ℝ) :
    ∏ l : Fin k, (if l = i then g l else 1) = g i := by
  rw [Finset.prod_eq_single i (fun l _ hl ↦ if_neg hl)
    (fun h ↦ absurd (Finset.mem_univ i) h), if_pos rfl]

/-- A product whose factors are `g` at two distinct indices and `1` elsewhere. -/
theorem prod_two_indices {k : ℕ} {i j : Fin k} (hij : i ≠ j) (g : Fin k → ℝ) :
    ∏ l : Fin k, (if l = i ∨ l = j then g l else 1) = g i * g j := by
  have h1 : ∏ l ∈ (Finset.univ \ ({i, j} : Finset (Fin k))),
      (if l = i ∨ l = j then g l else 1) = 1 := by
    refine Finset.prod_eq_one fun l hl ↦ ?_
    simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hl
    exact if_neg (by tauto)
  rw [← Finset.prod_sdiff (Finset.subset_univ ({i, j} : Finset (Fin k))), h1, one_mul,
    Finset.prod_pair hij, if_pos (Or.inl rfl), if_pos (Or.inr rfl)]

end Signs

section ProductSignLaw

/-- The product sign law on `k` loci, every coordinate having mean `m`. -/
def bernoulliSign (k : ℕ) (m : ℝ) (z : Fin k → Bool) : ℝ := ∏ i, (1 + m * sgn (z i)) / 2

/-- The product sign law is a nonnegative weight vector for `m` in `[-1,1]`. -/
theorem bernoulliSign_nonneg {k : ℕ} {m : ℝ} (hm : -1 ≤ m) (hm' : m ≤ 1)
    (z : Fin k → Bool) : 0 ≤ bernoulliSign k m z := by
  refine Finset.prod_nonneg fun i _ ↦ ?_
  rcases sgn_cases (z i) with h | h <;> rw [h] <;> linarith

/-- The product sign law has total mass one. -/
theorem sum_bernoulliSign (k : ℕ) (m : ℝ) : ∑ z : Fin k → Bool, bernoulliSign k m z = 1 := by
  unfold bernoulliSign
  rw [sum_prod_bool fun _ b ↦ (1 + m * sgn b) / 2]
  refine (Finset.prod_congr rfl fun i _ ↦ ?_).trans Finset.prod_const_one
  rw [sgn_true, sgn_false]
  ring

/-- Each locus has mean `m` under the product sign law. -/
theorem sum_bernoulliSign_sgn {k : ℕ} (m : ℝ) (i : Fin k) :
    ∑ z : Fin k → Bool, bernoulliSign k m z * sgn (z i) = m := by
  have hrw : ∀ z : Fin k → Bool, bernoulliSign k m z * sgn (z i)
      = ∏ l, ((1 + m * sgn (z l)) / 2 * (if l = i then sgn (z l) else 1)) := by
    intro z
    rw [Finset.prod_mul_distrib, prod_one_index i fun l ↦ sgn (z l)]
    rfl
  rw [Finset.sum_congr rfl fun z _ ↦ hrw z,
    sum_prod_bool fun l b ↦ (1 + m * sgn b) / 2 * (if l = i then sgn b else 1)]
  have hfac : ∀ l : Fin k,
      (1 + m * sgn true) / 2 * (if l = i then sgn true else 1)
        + (1 + m * sgn false) / 2 * (if l = i then sgn false else 1)
      = if l = i then m else 1 := by
    intro l
    by_cases h : l = i
    · rw [if_pos h, if_pos h, if_pos h, sgn_true, sgn_false]
      ring
    · rw [if_neg h, if_neg h, if_neg h, sgn_true, sgn_false]
      ring
  rw [Finset.prod_congr rfl fun l _ ↦ hfac l, prod_one_index i fun _ ↦ m]

/-- Exact second moments of the product sign law: unit diagonal, `m²` off the diagonal. -/
theorem sum_bernoulliSign_sgn_mul {k : ℕ} (m : ℝ) (i j : Fin k) :
    ∑ z : Fin k → Bool, bernoulliSign k m z * (sgn (z i) * sgn (z j))
      = if i = j then 1 else m ^ 2 := by
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl]
    have h1 : ∀ z : Fin k → Bool, bernoulliSign k m z * (sgn (z i) * sgn (z i))
        = bernoulliSign k m z := by
      intro z
      rcases sgn_cases (z i) with h | h <;> rw [h] <;> ring
    rw [Finset.sum_congr rfl fun z _ ↦ h1 z, sum_bernoulliSign]
  · rw [if_neg hij]
    have hrw : ∀ z : Fin k → Bool, bernoulliSign k m z * (sgn (z i) * sgn (z j))
        = ∏ l, ((1 + m * sgn (z l)) / 2 * (if l = i ∨ l = j then sgn (z l) else 1)) := by
      intro z
      rw [Finset.prod_mul_distrib, prod_two_indices hij fun l ↦ sgn (z l)]
      rfl
    rw [Finset.sum_congr rfl fun z _ ↦ hrw z,
      sum_prod_bool fun l b ↦ (1 + m * sgn b) / 2 * (if l = i ∨ l = j then sgn b else 1)]
    have hfac : ∀ l : Fin k,
        (1 + m * sgn true) / 2 * (if l = i ∨ l = j then sgn true else 1)
          + (1 + m * sgn false) / 2 * (if l = i ∨ l = j then sgn false else 1)
        = if l = i ∨ l = j then m else 1 := by
      intro l
      by_cases h : l = i ∨ l = j
      · rw [if_pos h, if_pos h, if_pos h, sgn_true, sgn_false]
        ring
      · rw [if_neg h, if_neg h, if_neg h, sgn_true, sgn_false]
        ring
    rw [Finset.prod_congr rfl fun l _ ↦ hfac l, prod_two_indices hij fun _ ↦ m]
    ring

end ProductSignLaw

section UniformSigns

/-- Expectation of a finite sum of observables. -/
theorem eval_finset_sum {Ω ι : Type*} [DecidableEq ι] (E : ExpFunctional Ω) (s : Finset ι)
    (f : ι → Ω → ℝ) : E (fun ω ↦ ∑ i ∈ s, f i ω) = ∑ i ∈ s, E (f i) := by
  have h : (fun ω ↦ ∑ i ∈ s, f i ω) = Finset.sum s f := by
    funext ω
    simp [Finset.sum_apply]
  rw [h, ExpFunctional.eval_sum]

/-- The uniform law on sign configurations is the product sign law at mean zero. -/
theorem uniformExp_eq_bernoulli {k : ℕ} (f : (Fin k → Bool) → ℝ) :
    uniformExp (Fin k → Bool) f = ∑ z : Fin k → Bool, bernoulliSign k 0 z * f z := by
  rw [uniformExp_apply]
  refine Finset.sum_congr rfl fun z _ ↦ ?_
  congr 1
  have hb : bernoulliSign k 0 z = ((2 : ℝ) ^ k)⁻¹ := by
    unfold bernoulliSign
    simp only [zero_mul, add_zero]
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, div_pow, one_pow,
      inv_eq_one_div]
  have hcard : (Fintype.card (Fin k → Bool) : ℝ) = 2 ^ k := by
    simp
  rw [hb, hcard]

/-- Each coordinate is centred under the uniform sign law. -/
theorem uniform_sgn {k : ℕ} (i : Fin k) :
    uniformExp (Fin k → Bool) (fun z ↦ sgn (z i)) = 0 := by
  rw [uniformExp_eq_bernoulli, sum_bernoulliSign_sgn]

/-- The uniform sign law has identity second-moment matrix. -/
theorem uniform_sgn_mul {k : ℕ} (i j : Fin k) :
    uniformExp (Fin k → Bool) (fun z ↦ sgn (z i) * sgn (z j)) = if i = j then 1 else 0 := by
  rw [uniformExp_eq_bernoulli, sum_bernoulliSign_sgn_mul]
  by_cases h : i = j <;> simp [h]

/-- A linear form in the sign coordinates. -/
def linSign {k : ℕ} (c : Fin k → ℝ) (z : Fin k → Bool) : ℝ := ∑ i, c i * sgn (z i)

/-- A linear sign form is centred under the uniform law. -/
theorem uniform_linSign_mean {k : ℕ} (c : Fin k → ℝ) :
    uniformExp (Fin k → Bool) (linSign c) = 0 := by
  have h := eval_finset_sum (uniformExp (Fin k → Bool)) Finset.univ
    fun (i : Fin k) (z : Fin k → Bool) ↦ c i * sgn (z i)
  unfold linSign
  rw [h]
  refine Finset.sum_eq_zero fun i _ ↦ ?_
  have hs : (fun z : Fin k → Bool ↦ c i * sgn (z i)) = c i • fun z ↦ sgn (z i) := by
    funext z
    simp
  rw [hs, ExpFunctional.smul_eval, uniform_sgn, mul_zero]

/-- Exact bilinear form of two linear sign forms under the uniform law. -/
theorem uniform_linSign_mul {k : ℕ} (c d : Fin k → ℝ) :
    uniformExp (Fin k → Bool) (fun z ↦ linSign c z * linSign d z) = ∑ i, c i * d i := by
  have hexp : (fun z : Fin k → Bool ↦ linSign c z * linSign d z)
      = fun z ↦ ∑ i, ∑ j, c i * d j * (sgn (z i) * sgn (z j)) := by
    funext z
    unfold linSign
    rw [Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ by ring
  rw [hexp, eval_finset_sum (uniformExp (Fin k → Bool)) Finset.univ
    fun (i : Fin k) (z : Fin k → Bool) ↦ ∑ j, c i * d j * (sgn (z i) * sgn (z j))]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [eval_finset_sum (uniformExp (Fin k → Bool)) Finset.univ
    fun (j : Fin k) (z : Fin k → Bool) ↦ c i * d j * (sgn (z i) * sgn (z j))]
  have hterm : ∀ j : Fin k,
      uniformExp (Fin k → Bool) (fun z ↦ c i * d j * (sgn (z i) * sgn (z j)))
        = c i * d j * (if i = j then 1 else 0) := by
    intro j
    have hs : (fun z : Fin k → Bool ↦ c i * d j * (sgn (z i) * sgn (z j)))
        = (c i * d j) • fun z ↦ sgn (z i) * sgn (z j) := by
      funext z
      simp
    rw [hs, ExpFunctional.smul_eval, uniform_sgn_mul]
  rw [Finset.sum_congr rfl fun j _ ↦ hterm j]
  simp

/-- Exact covariance of two linear sign forms under the uniform law. -/
theorem uniform_linSign_covariance {k : ℕ} (c d : Fin k → ℝ) :
    covariance (uniformExp (Fin k → Bool)) (linSign c) (linSign d) = ∑ i, c i * d i := by
  rw [covariance_eq_expect_mul_sub_means, uniform_linSign_mul, uniform_linSign_mean,
    uniform_linSign_mean]
  ring

/-- Exact variance of a linear sign form under the uniform law. -/
theorem uniform_linSign_variance {k : ℕ} (c : Fin k → ℝ) :
    variance (uniformExp (Fin k → Bool)) (linSign c) = ∑ i, c i ^ 2 := by
  have hsq : (fun z : Fin k → Bool ↦ linSign c z ^ 2)
      = fun z ↦ linSign c z * linSign c z := by
    funext z
    ring
  have hz : ((0 : ℝ)) ^ 2 = 0 := by norm_num
  rw [variance_eq_expect_sq_sub_sq_mean, uniform_linSign_mean, hsq, uniform_linSign_mul, hz,
    sub_zero]
  exact Finset.sum_congr rfl fun i _ ↦ (pow_two (c i)).symm

/-- Splitting a `Fin.snoc` bilinear sum into its head block and its last coordinate. -/
theorem sum_snoc_mul {n : ℕ} (c d : Fin n → ℝ) (a e : ℝ) :
    ∑ i : Fin (n + 1), Fin.snoc c a i * Fin.snoc d e i = (∑ i, c i * d i) + a * e := by
  rw [Fin.sum_univ_castSucc]
  simp

/-- Splitting a `Fin.snoc` square sum into its head block and its last coordinate. -/
theorem sum_snoc_sq {n : ℕ} (c : Fin n → ℝ) (a : ℝ) :
    ∑ i : Fin (n + 1), Fin.snoc c a i ^ 2 = (∑ i, c i ^ 2) + a ^ 2 := by
  rw [Fin.sum_univ_castSucc]
  simp

end UniformSigns

section TurnoverWorlds

variable {n : ℕ}

/-- **The finite turnover population.**  `n` independent standardised sign coordinates
carry both the scored and the causal genotype, one further independent sign coordinate
carries noise of standard deviation `sigma`, and the population's causal effect at locus
`i` is `b i * z i` for the effect-sign configuration `z`. -/
def turnoverWorld (b : Fin n → ℝ) (sigma : ℝ) (z : Fin n → ℝ) :
    DeploymentPopulation (Fin (n + 1) → Bool) (Fin n) (Fin n) where
  E := uniformExp (Fin (n + 1) → Bool)
  X := fun g i ↦ sgn (g i.castSucc)
  C := fun g i ↦ sgn (g i.castSucc)
  β := fun i ↦ b i * z i
  h := fun g ↦ sigma * sgn (g (Fin.last n))

/-- The deployed score of the turnover population is a linear sign form. -/
theorem turnoverWorld_score (b : Fin n → ℝ) (sigma : ℝ) (z w : Fin n → ℝ) :
    (turnoverWorld b sigma z).score w = linSign (Fin.snoc w 0) := by
  funext g
  simp only [DeploymentPopulation.score, linScore, dot, Core.innerSum, linSign, turnoverWorld]
  rw [Fin.sum_univ_castSucc]
  simp

/-- The realised phenotype of the turnover population is a linear sign form. -/
theorem turnoverWorld_phenotype (b : Fin n → ℝ) (sigma : ℝ) (z : Fin n → ℝ) :
    (turnoverWorld b sigma z).phenotype = linSign (Fin.snoc (fun i ↦ b i * z i) sigma) := by
  funext g
  simp only [DeploymentPopulation.phenotype, causalSignal, dot, Core.innerSum, linSign,
    turnoverWorld]
  rw [Fin.sum_univ_castSucc]
  simp

/-- **Exact moments of the turnover population**, evaluated from its finite law with no
supplied covariance, heritability or portability premise. -/
theorem turnoverWorld_moments (b : Fin n → ℝ) (sigma : ℝ) (z w : Fin n → ℝ) :
    (turnoverWorld b sigma z).scoreVariance w = ∑ i, w i ^ 2 ∧
      (turnoverWorld b sigma z).predictiveCovariance w = ∑ i, w i * (b i * z i) ∧
      (turnoverWorld b sigma z).outcomeVariance = (∑ i, (b i * z i) ^ 2) + sigma ^ 2 := by
  refine ⟨?_, ?_, ?_⟩
  · have h1 : (turnoverWorld b sigma z).scoreVariance w
        = variance (uniformExp (Fin (n + 1) → Bool)) (linSign (Fin.snoc w 0)) := by
      rw [← turnoverWorld_score b sigma z w]
      rfl
    rw [h1, uniform_linSign_variance, sum_snoc_sq]
    ring
  · have h1 : (turnoverWorld b sigma z).predictiveCovariance w
        = covariance (uniformExp (Fin (n + 1) → Bool)) (linSign (Fin.snoc w 0))
            (linSign (Fin.snoc (fun i ↦ b i * z i) sigma)) := by
      rw [← turnoverWorld_score b sigma z w, ← turnoverWorld_phenotype b sigma z]
      rfl
    rw [h1, uniform_linSign_covariance, sum_snoc_mul]
    ring
  · have h1 : (turnoverWorld b sigma z).outcomeVariance
        = variance (uniformExp (Fin (n + 1) → Bool))
            (linSign (Fin.snoc (fun i ↦ b i * z i) sigma)) := by
      rw [← turnoverWorld_phenotype b sigma z]
      rfl
    rw [h1, uniform_linSign_variance, sum_snoc_sq]

/-- **Exact conditional accuracy at a fixed effect-sign configuration.**  This is the
quantity averaged in TQ (3.8); the outcome variance is `V = H + σ²`. -/
theorem turnoverWorld_r2 (b : Fin n → ℝ) (sigma : ℝ) (z w : Fin n → ℝ)
    (hz : ∀ i, z i = 1 ∨ z i = -1) :
    (turnoverWorld b sigma z).r2 w
      = (∑ i, w i * b i * z i) ^ 2 / ((∑ i, w i ^ 2) * ((∑ i, b i ^ 2) + sigma ^ 2)) := by
  obtain ⟨hv, hc, ho⟩ := turnoverWorld_moments b sigma z w
  have hnum : ∑ i, w i * (b i * z i) = ∑ i, w i * b i * z i :=
    Finset.sum_congr rfl fun i _ ↦ by ring
  have hden : ∑ i, (b i * z i) ^ 2 = ∑ i, b i ^ 2 := by
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rcases hz i with h | h <;> rw [h] <;> ring
  simp only [DeploymentPopulation.r2]
  rw [hv, hc, ho, hnum, hden]

end TurnoverWorlds

section TurnoverDependenceLaw

variable {n : ℕ}

/-- **TQ Theorem 3.5, exact turnover-dependence law.**  For any joint law of the effect
signs the expected within-population squared correlation is the quadratic form

`E[q] = aᵀ M a / (‖w‖² V)`,  `a i = w i * b i`,  `M i j = E[Z i Z j]`,

evaluated from the populations themselves. The one-locus means `E[Z i]` appear nowhere
on the right-hand side, so they do not determine the left-hand side. -/
theorem expected_r2_turnover_law {Ω : Type*} (E : ExpFunctional Ω) (Z : Ω → Fin n → ℝ)
    (hZ : ∀ ω i, Z ω i = 1 ∨ Z ω i = -1) (w b : Fin n → ℝ) (sigma : ℝ) :
    E (fun ω ↦ (turnoverWorld b sigma (Z ω)).r2 w)
      = (∑ i, ∑ j, w i * b i * E (fun ω ↦ Z ω i * Z ω j) * (w j * b j))
          / ((∑ i, w i ^ 2) * ((∑ i, b i ^ 2) + sigma ^ 2)) := by
  have hnum : E (fun ω ↦ ∑ i, ∑ j, w i * b i * (Z ω i * Z ω j) * (w j * b j))
      = ∑ i, ∑ j, w i * b i * E (fun ω ↦ Z ω i * Z ω j) * (w j * b j) := by
    rw [eval_finset_sum E Finset.univ
      fun (i : Fin n) (ω : Ω) ↦ ∑ j, w i * b i * (Z ω i * Z ω j) * (w j * b j)]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [eval_finset_sum E Finset.univ
      fun (j : Fin n) (ω : Ω) ↦ w i * b i * (Z ω i * Z ω j) * (w j * b j)]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    have hs : (fun ω ↦ w i * b i * (Z ω i * Z ω j) * (w j * b j))
        = (w i * b i * (w j * b j)) • fun ω ↦ Z ω i * Z ω j := by
      funext ω
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    rw [hs, ExpFunctional.smul_eval]
    ring
  have hfun : (fun ω ↦ (turnoverWorld b sigma (Z ω)).r2 w)
      = ((∑ i, w i ^ 2) * ((∑ i, b i ^ 2) + sigma ^ 2))⁻¹
        • fun ω ↦ ∑ i, ∑ j, w i * b i * (Z ω i * Z ω j) * (w j * b j) := by
    funext ω
    rw [turnoverWorld_r2 b sigma (Z ω) w (hZ ω)]
    simp only [Pi.smul_apply, smul_eq_mul]
    have hexpand : (∑ i, w i * b i * Z ω i) ^ 2
        = ∑ i, ∑ j, w i * b i * (Z ω i * Z ω j) * (w j * b j) := by
      rw [pow_two, Finset.sum_mul_sum]
      exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ by ring
    rw [hexpand]
    ring
  rw [hfun, ExpFunctional.smul_eval, hnum]
  ring

/-- The quadratic form of TQ (3.8) at a sign law with unit diagonal and constant
off-diagonal second moment `r`. -/
theorem quadratic_form_equicorrelated (a : Fin n → ℝ) (r : ℝ) :
    ∑ i, ∑ j, a i * (if i = j then (1 : ℝ) else r) * a j
      = r * (∑ i, a i) ^ 2 + (1 - r) * ∑ i, a i ^ 2 := by
  have hinner : ∀ i : Fin n, ∑ j, a i * (if i = j then (1 : ℝ) else r) * a j
      = r * a i * ∑ j, a j + (1 - r) * a i ^ 2 := by
    intro i
    have key : ∀ j : Fin n, a i * (if i = j then (1 : ℝ) else r) * a j
        = r * a i * a j + (if i = j then (1 - r) * a i ^ 2 else 0) := by
      intro j
      by_cases h : i = j
      · subst h
        rw [if_pos rfl, if_pos rfl]
        ring
      · rw [if_neg h, if_neg h]
        ring
    rw [Finset.sum_congr rfl fun j _ ↦ key j, Finset.sum_add_distrib,
      Finset.sum_ite_eq_of_mem Finset.univ i (fun _ ↦ (1 - r) * a i ^ 2) (Finset.mem_univ i),
      ← Finset.mul_sum]
  rw [Finset.sum_congr rfl fun i _ ↦ hinner i, Finset.sum_add_distrib]
  have h1 : ∑ i : Fin n, r * a i * ∑ j, a j = r * (∑ i, a i) ^ 2 := by
    rw [Finset.sum_congr rfl fun i _ ↦
      show r * a i * ∑ j, a j = r * (∑ j, a j) * a i from by ring, ← Finset.mul_sum]
    ring
  have h2 : ∑ i : Fin n, (1 - r) * a i ^ 2 = (1 - r) * ∑ i, a i ^ 2 :=
    (Finset.mul_sum Finset.univ (fun i ↦ a i ^ 2) (1 - r)).symm
  rw [h1, h2]

end TurnoverDependenceLaw

section TwoMechanisms

variable {n : ℕ}

/-- **Independent equal-rate turnover.**  The `n` effect signs are independent, each with
mean `m`. -/
def independentTurnover (n : ℕ) (m : ℝ) (hm : -1 ≤ m) (hm' : m ≤ 1) :
    ExpFunctional (Fin n → Bool) :=
  weightedExp (bernoulliSign n m) (bernoulliSign_nonneg hm hm') (sum_bernoulliSign n m)

/-- **Synchronised turnover.**  One shared sign drives every locus, with mean `m`. -/
def synchronizedTurnover (m : ℝ) (hm : -1 ≤ m) (hm' : m ≤ 1) : ExpFunctional Bool :=
  weightedExp (fun c ↦ (1 + m * sgn c) / 2)
    (fun c ↦ by
      show (0 : ℝ) ≤ (1 + m * sgn c) / 2
      rcases sgn_cases c with h | h <;> rw [h] <;> linarith)
    (by rw [Fintype.sum_bool, sgn_true, sgn_false]; ring)

/-- The effect-sign configuration of the independent mechanism. -/
def independentSigns (n : ℕ) (z : Fin n → Bool) (i : Fin n) : ℝ := sgn (z i)

/-- The effect-sign configuration of the synchronised mechanism. -/
def synchronizedSigns (n : ℕ) (c : Bool) (_ : Fin n) : ℝ := sgn c

/-- **The two mechanisms have the same complete one-locus law**: the same marginal mean
and the same unit second moment at every locus. -/
theorem turnover_mechanisms_share_marginals (m : ℝ) (hm : -1 ≤ m) (hm' : m ≤ 1) (i : Fin n) :
    independentTurnover n m hm hm' (fun z ↦ independentSigns n z i) = m ∧
      synchronizedTurnover m hm hm' (fun c ↦ synchronizedSigns n c i) = m ∧
      independentTurnover n m hm hm' (fun z ↦ independentSigns n z i ^ 2) = 1 ∧
      synchronizedTurnover m hm hm' (fun c ↦ synchronizedSigns n c i ^ 2) = 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [independentTurnover, weightedExp_apply]
    exact sum_bernoulliSign_sgn m i
  · rw [synchronizedTurnover, weightedExp_apply, Fintype.sum_bool]
    simp only [synchronizedSigns, sgn_true, sgn_false]
    ring
  · rw [independentTurnover, weightedExp_apply]
    simp only [independentSigns, sgn_sq, mul_one]
    exact sum_bernoulliSign n m
  · rw [synchronizedTurnover, weightedExp_apply, Fintype.sum_bool]
    simp only [synchronizedSigns, sgn_true, sgn_false]
    ring

/-- Cross-locus second moments of the independent mechanism. -/
theorem independent_second_moments (m : ℝ) (hm : -1 ≤ m) (hm' : m ≤ 1) (i j : Fin n) :
    independentTurnover n m hm hm' (fun z ↦ independentSigns n z i * independentSigns n z j)
      = if i = j then 1 else m ^ 2 := by
  rw [independentTurnover, weightedExp_apply]
  exact sum_bernoulliSign_sgn_mul m i j

/-- Cross-locus second moments of the synchronised mechanism: every pair is perfectly
aligned at every marginal mean. -/
theorem synchronized_second_moments (m : ℝ) (hm : -1 ≤ m) (hm' : m ≤ 1) (i j : Fin n) :
    synchronizedTurnover m hm hm' (fun c ↦ synchronizedSigns n c i * synchronizedSigns n c j)
      = 1 := by
  rw [synchronizedTurnover, weightedExp_apply, Fintype.sum_bool]
  simp only [synchronizedSigns, sgn_true, sgn_false]
  ring

/-- The oracle-weight accuracy ceiling `Q₀ = H / (H + σ²)`. -/
def ceiling (H sigma : ℝ) : ℝ := H / (H + sigma ^ 2)

/-- Effect concentration `κ_b = ∑ α_i²` with `α_i = b_i² / H`. -/
def effectConcentration (n : ℕ) (b : Fin n → ℝ) : ℝ := ∑ i, (b i ^ 2 / ∑ j, b j ^ 2) ^ 2

/-- **TQ Theorem 3.7, independent branch (3.10).**  Under independent turnover with oracle
weights, `E q = Q₀ (κ_b + (1 - κ_b) m²)`. -/
theorem independent_turnover_expected_r2 (b : Fin n → ℝ) (sigma m : ℝ) (hm : -1 ≤ m)
    (hm' : m ≤ 1) (hH : 0 < ∑ i, b i ^ 2) :
    independentTurnover n m hm hm'
        (fun z ↦ (turnoverWorld b sigma (independentSigns n z)).r2 b)
      = ceiling (∑ i, b i ^ 2) sigma
          * (effectConcentration n b + (1 - effectConcentration n b) * m ^ 2) := by
  rw [expected_r2_turnover_law (independentTurnover n m hm hm') (independentSigns n)
    (fun z i ↦ sgn_cases (z i)) b b sigma]
  have hstep : ∀ i : Fin n,
      (∑ j, b i * b i * independentTurnover n m hm hm'
          (fun ω ↦ independentSigns n ω i * independentSigns n ω j) * (b j * b j))
        = ∑ j, b i ^ 2 * (if i = j then (1 : ℝ) else m ^ 2) * b j ^ 2 := by
    intro i
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [independent_second_moments m hm hm' i j]
    ring
  have hquad : ∑ i, ∑ j, b i ^ 2 * (if i = j then (1 : ℝ) else m ^ 2) * b j ^ 2
      = m ^ 2 * (∑ i, b i ^ 2) ^ 2 + (1 - m ^ 2) * ∑ i, (b i ^ 2) ^ 2 :=
    quadratic_form_equicorrelated (fun i ↦ b i ^ 2) (m ^ 2)
  have hkappa : effectConcentration n b = (∑ i, (b i ^ 2) ^ 2) / (∑ i, b i ^ 2) ^ 2 := by
    unfold effectConcentration
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun i _ ↦ by rw [div_pow]
  have hHne : (∑ i, b i ^ 2) ≠ 0 := ne_of_gt hH
  have hV : (0 : ℝ) < (∑ i, b i ^ 2) + sigma ^ 2 := by nlinarith [sq_nonneg sigma]
  have hVne : (∑ i, b i ^ 2) + sigma ^ 2 ≠ 0 := ne_of_gt hV
  rw [Finset.sum_congr rfl fun i _ ↦ hstep i, hquad, hkappa, ceiling]
  field_simp
  ring

/-- **TQ Theorem 3.7, synchronised branch (3.11).**  Under synchronised turnover with
oracle weights, `E q = Q₀` at every marginal mean `m`. -/
theorem synchronized_turnover_expected_r2 (b : Fin n → ℝ) (sigma m : ℝ) (hm : -1 ≤ m)
    (hm' : m ≤ 1) (hH : 0 < ∑ i, b i ^ 2) :
    synchronizedTurnover m hm hm'
        (fun c ↦ (turnoverWorld b sigma (synchronizedSigns n c)).r2 b)
      = ceiling (∑ i, b i ^ 2) sigma := by
  rw [expected_r2_turnover_law (synchronizedTurnover m hm hm') (synchronizedSigns n)
    (fun c _ ↦ sgn_cases c) b b sigma]
  have hstep : ∀ i : Fin n,
      (∑ j, b i * b i * synchronizedTurnover m hm hm'
          (fun c ↦ synchronizedSigns n c i * synchronizedSigns n c j) * (b j * b j))
        = ∑ j, b i ^ 2 * (if i = j then (1 : ℝ) else 1) * b j ^ 2 := by
    intro i
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [synchronized_second_moments m hm hm' i j]
    by_cases h : i = j
    · rw [if_pos h]
      ring
    · rw [if_neg h]
      ring
  have hquad : ∑ i, ∑ j, b i ^ 2 * (if i = j then (1 : ℝ) else 1) * b j ^ 2
      = 1 * (∑ i, b i ^ 2) ^ 2 + (1 - 1) * ∑ i, (b i ^ 2) ^ 2 :=
    quadratic_form_equicorrelated (fun i ↦ b i ^ 2) 1
  have hHne : (∑ i, b i ^ 2) ≠ 0 := ne_of_gt hH
  have hV : (0 : ℝ) < (∑ i, b i ^ 2) + sigma ^ 2 := by nlinarith [sq_nonneg sigma]
  have hVne : (∑ i, b i ^ 2) + sigma ^ 2 ≠ 0 := ne_of_gt hV
  rw [Finset.sum_congr rfl fun i _ ↦ hstep i, hquad, ceiling]
  field_simp
  ring

/-- **One-locus retention does not determine expected accuracy.**  Two centred sign laws
with the same one-locus law give `1/2` and `1` on two equal unit effects with noiseless
outcomes. -/
theorem marginals_do_not_determine_expected_r2 :
    independentTurnover 2 0 (by norm_num) (by norm_num)
        (fun z ↦ (turnoverWorld ![1, 1] 0 (independentSigns 2 z)).r2 ![1, 1]) = 1 / 2 ∧
      synchronizedTurnover 0 (by norm_num) (by norm_num)
        (fun c ↦ (turnoverWorld ![1, 1] 0 (synchronizedSigns 2 c)).r2 ![1, 1]) = 1 := by
  have hH : (0 : ℝ) < ∑ i, (![(1 : ℝ), 1] i) ^ 2 := by
    norm_num [Fin.sum_univ_two]
  constructor
  · rw [independent_turnover_expected_r2 ![1, 1] 0 0 (by norm_num) (by norm_num) hH]
    norm_num [ceiling, effectConcentration, Fin.sum_univ_two]
  · rw [synchronized_turnover_expected_r2 ![1, 1] 0 0 (by norm_num) (by norm_num) hH]
    norm_num [ceiling, Fin.sum_univ_two]

end TwoMechanisms

section FlipProcess

/-- The symmetric two-state sign generator: each sign flips at rate `lam`. -/
def flipGenerator (lam : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  fun x y ↦ if x = y then -lam else lam

/-- The transition semigroup of the symmetric two-state sign process. -/
def flipSemigroup (lam t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  fun x y ↦ if x = y then (1 + Real.exp (-(2 * lam * t))) / 2
    else (1 - Real.exp (-(2 * lam * t))) / 2

/-- The signed value carried by a two-state sign coordinate. -/
def signState (x : Fin 2) : ℝ := sgn (decide (x = 0))

/-- The two signed values of the two-state coordinate. -/
theorem signState_values : signState 0 = 1 ∧ signState 1 = -1 := by
  constructor <;> norm_num [signState, sgn, TraitPortabilityRange.sign]

/-- One-locus retention `m(t) = e^{-2λt}`. -/
def retention (lam t : ℝ) : ℝ := Real.exp (-(2 * lam * t))

/-- Retention never drops below `-1`. -/
theorem neg_one_le_retention (lam t : ℝ) : -1 ≤ retention lam t := by
  have h := Real.exp_pos (-(2 * lam * t))
  unfold retention
  linarith

/-- Retention is at most one once `lam * t` is nonnegative. -/
theorem retention_le_one {lam t : ℝ} (h : 0 ≤ lam * t) : retention lam t ≤ 1 := by
  unfold retention
  rw [Real.exp_le_one_iff]
  linarith

/-- The square of retention is the four-fold exponential of TQ (3.10). -/
theorem retention_sq (lam t : ℝ) : retention lam t ^ 2 = Real.exp (-(4 * lam * t)) := by
  unfold retention
  rw [pow_two, ← Real.exp_add]
  ring_nf

/-- The semigroup starts at the identity. -/
theorem flipSemigroup_zero (lam : ℝ) : flipSemigroup lam 0 = 1 := by
  ext x y
  by_cases h : x = y <;> simp [flipSemigroup, Matrix.one_apply, h]

/-- Every row of the semigroup is a probability vector once `lam * t` is nonnegative. -/
theorem flipSemigroup_stochastic {lam t : ℝ} (h : 0 ≤ lam * t) (x : Fin 2) :
    (∀ y, 0 ≤ flipSemigroup lam t x y) ∧ ∑ y, flipSemigroup lam t x y = 1 := by
  have h1 : Real.exp (-(2 * lam * t)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    linarith
  have h0 : 0 < Real.exp (-(2 * lam * t)) := Real.exp_pos _
  constructor
  · intro y
    by_cases hxy : x = y
    · have : flipSemigroup lam t x y = (1 + Real.exp (-(2 * lam * t))) / 2 := by
        simp [flipSemigroup, hxy]
      rw [this]
      linarith
    · have : flipSemigroup lam t x y = (1 - Real.exp (-(2 * lam * t))) / 2 := by
        simp [flipSemigroup, hxy]
      rw [this]
      linarith
  · fin_cases x <;> simp [flipSemigroup, Fin.sum_univ_two] <;> ring

/-- **The forward equation.**  The semigroup solves `P'(t) = P(t) Q` for the symmetric
two-state generator, so it is that chain's transition law and not a fitted curve. -/
theorem flipSemigroup_forward (lam t : ℝ) (x y : Fin 2) :
    HasDerivAt (fun s ↦ flipSemigroup lam s x y)
      ((flipSemigroup lam t * flipGenerator lam) x y) t := by
  have hlin : HasDerivAt (fun s : ℝ ↦ -(2 * lam * s)) (-(2 * lam)) t := by
    simpa using ((hasDerivAt_id t).const_mul (2 * lam)).neg
  have hexp : HasDerivAt (fun s : ℝ ↦ Real.exp (-(2 * lam * s)))
      (Real.exp (-(2 * lam * t)) * -(2 * lam)) t :=
    (Real.hasDerivAt_exp _).comp t hlin
  have hprod : (flipSemigroup lam t * flipGenerator lam) x y
      = if x = y then -(lam * Real.exp (-(2 * lam * t)))
        else lam * Real.exp (-(2 * lam * t)) := by
    rw [Matrix.mul_apply, Fin.sum_univ_two]
    fin_cases x <;> fin_cases y <;> simp [flipSemigroup, flipGenerator] <;> ring
  rw [hprod]
  by_cases hxy : x = y
  · have hfun : (fun s ↦ flipSemigroup lam s x y)
        = fun s ↦ (1 + Real.exp (-(2 * lam * s))) / 2 := by
      funext s
      simp [flipSemigroup, hxy]
    have hval : -(lam * Real.exp (-(2 * lam * t)))
        = Real.exp (-(2 * lam * t)) * -(2 * lam) / 2 := by ring
    rw [hfun, if_pos hxy, hval]
    exact (hexp.const_add 1).div_const 2
  · have hfun : (fun s ↦ flipSemigroup lam s x y)
        = fun s ↦ (1 - Real.exp (-(2 * lam * s))) / 2 := by
      funext s
      simp [flipSemigroup, hxy]
    have hval : lam * Real.exp (-(2 * lam * t))
        = -(Real.exp (-(2 * lam * t)) * -(2 * lam)) / 2 := by ring
    rw [hfun, if_neg hxy, hval]
    exact (hexp.const_sub 1).div_const 2

/-- **TQ Theorem 3.7, retention.**  Started at the `+1` state, the two-state chain has
expected sign `e^{-2λt}` at time `t`. -/
theorem flip_retention (lam t : ℝ) :
    (flipSemigroup lam t).mulVec signState 0 = retention lam t := by
  have h0 : signState 0 = 1 := signState_values.1
  have h1 : signState 1 = -1 := signState_values.2
  have hd : flipSemigroup lam t 0 0 = (1 + Real.exp (-(2 * lam * t))) / 2 := by
    simp [flipSemigroup]
  have ho : flipSemigroup lam t 0 1 = (1 - Real.exp (-(2 * lam * t))) / 2 := by
    simp [flipSemigroup]
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, h0, h1, hd, ho, retention]
  ring

end FlipProcess

section LearningDependentMonotonicity

variable {n : ℕ}

/-- Aligned signal `A_w = ∑ w_i² b_i²`: the part carried by single loci. -/
def alignedSignal (n : ℕ) (w b : Fin n → ℝ) : ℝ := ∑ i, w i ^ 2 * b i ^ 2

/-- Cross signal `B_w = (wᵀb)² - A_w`: the part carried by cross-locus alignment rather
than by single loci. -/
def crossSignal (n : ℕ) (w b : Fin n → ℝ) : ℝ := (∑ i, w i * b i) ^ 2 - alignedSignal n w b

/-- **TQ Corollary 3.8 (3.12) at an arbitrary weight vector.**  Under independent turnover
with one-locus mean `m` the expected accuracy is `(A_w + m² B_w)/(‖w‖² V)`. -/
theorem independent_turnover_general_weights (w b : Fin n → ℝ) (sigma m : ℝ) (hm : -1 ≤ m)
    (hm' : m ≤ 1) :
    independentTurnover n m hm hm'
        (fun z ↦ (turnoverWorld b sigma (independentSigns n z)).r2 w)
      = (alignedSignal n w b + m ^ 2 * crossSignal n w b)
          / ((∑ i, w i ^ 2) * ((∑ i, b i ^ 2) + sigma ^ 2)) := by
  rw [expected_r2_turnover_law (independentTurnover n m hm hm') (independentSigns n)
    (fun z i ↦ sgn_cases (z i)) w b sigma]
  have hstep : ∀ i : Fin n,
      (∑ j, w i * b i * independentTurnover n m hm hm'
          (fun ω ↦ independentSigns n ω i * independentSigns n ω j) * (w j * b j))
        = ∑ j, (w i * b i) * (if i = j then (1 : ℝ) else m ^ 2) * (w j * b j) := by
    intro i
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [independent_second_moments m hm hm' i j]
  have hquad : ∑ i, ∑ j, (w i * b i) * (if i = j then (1 : ℝ) else m ^ 2) * (w j * b j)
      = m ^ 2 * (∑ i, w i * b i) ^ 2 + (1 - m ^ 2) * ∑ i, (w i * b i) ^ 2 :=
    quadratic_form_equicorrelated (fun i ↦ w i * b i) (m ^ 2)
  have hA : ∑ i, (w i * b i) ^ 2 = alignedSignal n w b := by
    unfold alignedSignal
    exact Finset.sum_congr rfl fun i _ ↦ by ring
  rw [Finset.sum_congr rfl fun i _ ↦ hstep i, hquad, hA]
  congr 1
  unfold crossSignal
  ring

/-- Expected accuracy at evolutionary time `t` under independent equal-rate turnover. -/
def independentTurnoverAccuracy (n : ℕ) (w b : Fin n → ℝ) (sigma lam t : ℝ) : ℝ :=
  (alignedSignal n w b + retention lam t ^ 2 * crossSignal n w b)
    / ((∑ i, w i ^ 2) * ((∑ i, b i ^ 2) + sigma ^ 2))

/-- The time law is the expectation of the population `R²` over the turnover law, not a
separate definition. -/
theorem independentTurnoverAccuracy_eq (w b : Fin n → ℝ) (sigma lam t : ℝ)
    (ht : 0 ≤ lam * t) :
    independentTurnover n (retention lam t) (neg_one_le_retention lam t) (retention_le_one ht)
        (fun z ↦ (turnoverWorld b sigma (independentSigns n z)).r2 w)
      = independentTurnoverAccuracy n w b sigma lam t :=
  independent_turnover_general_weights w b sigma (retention lam t)
    (neg_one_le_retention lam t) (retention_le_one ht)

/-- **TQ Corollary 3.8, the exact monotonicity criterion.**  With a positive flip rate,
expected accuracy strictly decreases exactly when `B_w > 0`, is constant exactly when
`B_w = 0`, and strictly increases exactly when `B_w < 0`. -/
theorem turnover_monotonicity_criterion (w b : Fin n → ℝ) (sigma lam s t : ℝ)
    (hlam : 0 < lam) (hst : s < t) (hw : 0 < ∑ i, w i ^ 2)
    (hV : 0 < (∑ i, b i ^ 2) + sigma ^ 2) :
    (independentTurnoverAccuracy n w b sigma lam t
          < independentTurnoverAccuracy n w b sigma lam s ↔ 0 < crossSignal n w b) ∧
      (independentTurnoverAccuracy n w b sigma lam t
          = independentTurnoverAccuracy n w b sigma lam s ↔ crossSignal n w b = 0) ∧
      (independentTurnoverAccuracy n w b sigma lam s
          < independentTurnoverAccuracy n w b sigma lam t ↔ crossSignal n w b < 0) := by
  have hD : 0 < (∑ i, w i ^ 2) * ((∑ i, b i ^ 2) + sigma ^ 2) := mul_pos hw hV
  have hexp : Real.exp (-(4 * lam * t)) < Real.exp (-(4 * lam * s)) := by
    rw [Real.exp_lt_exp]
    nlinarith
  have hdiff : independentTurnoverAccuracy n w b sigma lam t
      - independentTurnoverAccuracy n w b sigma lam s
      = (Real.exp (-(4 * lam * t)) - Real.exp (-(4 * lam * s))) * crossSignal n w b
          / ((∑ i, w i ^ 2) * ((∑ i, b i ^ 2) + sigma ^ 2)) := by
    unfold independentTurnoverAccuracy
    rw [retention_sq, retention_sq, div_sub_div_same]
    congr 1
    ring
  have hneg : Real.exp (-(4 * lam * t)) - Real.exp (-(4 * lam * s)) < 0 := by linarith
  refine ⟨?_, ?_, ?_⟩
  · rw [← sub_neg, hdiff, div_neg_iff]
    constructor
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · linarith
      · nlinarith
    · intro hB
      right
      exact ⟨mul_neg_of_neg_of_pos hneg hB, hD⟩
  · rw [← sub_eq_zero, hdiff, div_eq_zero_iff]
    constructor
    · rintro (h | h)
      · rcases mul_eq_zero.mp h with h' | h'
        · linarith
        · exact h'
      · linarith
    · intro hB
      left
      rw [hB, mul_zero]
  · rw [← sub_pos, hdiff, div_pos_iff]
    constructor
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · nlinarith
      · linarith
    · intro hB
      left
      exact ⟨mul_pos_of_neg_of_neg hneg hB, hD⟩

/-- **The exact time derivative of TQ Corollary 3.8.** -/
theorem independentTurnoverAccuracy_hasDerivAt (w b : Fin n → ℝ) (sigma lam t : ℝ) :
    HasDerivAt (independentTurnoverAccuracy n w b sigma lam)
      (-(4 * lam) * Real.exp (-(4 * lam * t)) * crossSignal n w b
        / ((∑ i, w i ^ 2) * ((∑ i, b i ^ 2) + sigma ^ 2))) t := by
  have hlin : HasDerivAt (fun s : ℝ ↦ -(4 * lam * s)) (-(4 * lam)) t := by
    simpa using ((hasDerivAt_id t).const_mul (4 * lam)).neg
  have hexp : HasDerivAt (fun s : ℝ ↦ Real.exp (-(4 * lam * s)))
      (Real.exp (-(4 * lam * t)) * -(4 * lam)) t :=
    (Real.hasDerivAt_exp _).comp t hlin
  have hfun : independentTurnoverAccuracy n w b sigma lam
      = fun s ↦ (alignedSignal n w b + Real.exp (-(4 * lam * s)) * crossSignal n w b)
          / ((∑ i, w i ^ 2) * ((∑ i, b i ^ 2) + sigma ^ 2)) := by
    funext s
    rw [independentTurnoverAccuracy, retention_sq]
  have hval : -(4 * lam) * Real.exp (-(4 * lam * t)) * crossSignal n w b
        / ((∑ i, w i ^ 2) * ((∑ i, b i ^ 2) + sigma ^ 2))
      = Real.exp (-(4 * lam * t)) * -(4 * lam) * crossSignal n w b
        / ((∑ i, w i ^ 2) * ((∑ i, b i ^ 2) + sigma ^ 2)) := by ring
  rw [hfun, hval]
  exact ((hexp.mul_const (crossSignal n w b)).const_add (alignedSignal n w b)).div_const
    ((∑ i, w i ^ 2) * ((∑ i, b i ^ 2) + sigma ^ 2))

/-- **TQ Corollary 3.8 (3.13).**  For a source-trained weight drawn independently of the
turnover process, the time law is affine in `e^{-4λt}` with coefficient `E[B_ŵ/‖ŵ‖²]`. -/
theorem random_weight_turnover_law {W : Type*} (EW : ExpFunctional W) (wf : W → Fin n → ℝ)
    (b : Fin n → ℝ) (sigma lam t : ℝ) :
    EW (fun u ↦ independentTurnoverAccuracy n (wf u) b sigma lam t)
      = (EW (fun u ↦ alignedSignal n (wf u) b / ∑ i, wf u i ^ 2)
          + Real.exp (-(4 * lam * t))
            * EW (fun u ↦ crossSignal n (wf u) b / ∑ i, wf u i ^ 2))
        / ((∑ i, b i ^ 2) + sigma ^ 2) := by
  have hdecomp : (fun u ↦ independentTurnoverAccuracy n (wf u) b sigma lam t)
      = ((∑ i, b i ^ 2) + sigma ^ 2)⁻¹ •
          ((fun u ↦ alignedSignal n (wf u) b / ∑ i, wf u i ^ 2)
            + Real.exp (-(4 * lam * t)) • fun u ↦ crossSignal n (wf u) b / ∑ i, wf u i ^ 2) := by
    funext u
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    rw [independentTurnoverAccuracy, retention_sq, ← div_div, add_div, mul_div_assoc]
    ring
  rw [hdecomp, ExpFunctional.smul_eval, ExpFunctional.add_eval, ExpFunctional.smul_eval]
  ring

/-- **Turnover can raise accuracy.**  With `b = (1,1)` and the anti-aligned weight
`w = (1,-1)` the cross signal is `-2` while the aligned signal is `2`, so independent
turnover strictly increases expected squared correlation from zero. -/
theorem antialigned_weight_has_negative_cross_signal :
    crossSignal 2 ![1, -1] ![1, 1] = -2 ∧ alignedSignal 2 ![1, -1] ![1, 1] = 2 := by
  constructor <;> norm_num [crossSignal, alignedSignal, Fin.sum_univ_two]

end LearningDependentMonotonicity

end

end Descent.Portability.TurnoverDependence
