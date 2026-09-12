/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.AncestralLocality.LocalityBounds
import Descent.Pangenome.AncestralLocality.LocalityCoupling
import Mathlib.MeasureTheory.Integral.Bochner.Set

assert_below Descent.PopGen Descent.Spectral Descent.Blindness Descent.Conditionals
assert_below Descent.Portability Descent.Decision Descent.Program

/-!
# Corollary 8.1 with the explicit escape bounds

`ANCESTRAL_LOCALITY.md` §9. `LocalityCoupling` proves Corollary 8.1 with the escape probability
as the weight of an escape event, and `LocalityBounds` proves the escape bounds (9.1) and (9.2)
for the marginal laws of the backward circuit. This module joins them, so the total-variation
bound holds with the explicit bound in place of a parameter.

The randomness of the circuit is its tagged state at time `T`, distributed by the marginal law
`μ T`. On each state the circuit evaluated on an input is a finite law on samples, and the
sample law is its `μ T`-average. When the evaluations on two inputs coincide on every state that
has not escaped, the two sample laws are within total variation the probability of escape
(`totalVariation_integralLaw_le`), the measure form of `totalVariation_mixtureLaw_le`. With
`measureReal_escapeSet_le_exp` this is Corollary 8.1 under (9.1),
`d_TV ≤ min {1, n|A| e^{D(1+2a)T} / a^ℓ}` (`totalVariation_integralLaw_le_exp`). At the radius
`a = ℓ/(2DT)`, through `exp_div_pow_eq_of_radius`, it is Corollary 8.1 under (9.2),
`d_TV ≤ min {1, n|A| e^{DT} (2eDT/ℓ)^ℓ}` (`totalVariation_integralLaw_le_radius`).

Scope. Dynkin's formula for the marginal laws and the locality of the evaluations are hypotheses,
as in `LocalityBounds` and `LocalityCoupling`; the duality identity that makes the averaged
evaluation the sample law `S_{n,A,T}(p)` is not constructed.

## Empirical status

None. The bodies here are integrals of bounded functions and a chain of stated bounds: the rates,
the marginal laws and the evaluations are supplied, and no measurement enters any statement.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Pangenome.AncestralLocality

open Finset MeasureTheory

noncomputable section

/-- Spec Corollary 8.1 in measure form. Assumes: a probability law `ν` of the circuit state,
evaluations of the state on two inputs as finite laws on samples, measurable in the state, and an
escape set off which the two evaluations coincide. The two averaged sample laws are within total
variation the probability of escape. -/
theorem totalVariation_integralLaw_le {σ S : Type*} [MeasurableSpace σ] [Fintype S]
    (ν : Measure σ) [IsProbabilityMeasure ν] (evaluationP evaluationQ : σ → S → ℝ)
    (hmeasurableP : ∀ s, Measurable fun x ↦ evaluationP x s)
    (hmeasurableQ : ∀ s, Measurable fun x ↦ evaluationQ x s)
    (hnonnegP : ∀ x s, 0 ≤ evaluationP x s) (hnonnegQ : ∀ x s, 0 ≤ evaluationQ x s)
    (htotalP : ∀ x, ∑ s, evaluationP x s = 1) (htotalQ : ∀ x, ∑ s, evaluationQ x s = 1)
    {escape : Set σ} (hagree : ∀ x ∉ escape, evaluationP x = evaluationQ x) :
    totalVariation (fun s ↦ ∫ x, evaluationP x s ∂ν) (fun s ↦ ∫ x, evaluationQ x s ∂ν) ≤
      ν.real escape := by
  have hintegrable : ∀ evaluation : σ → S → ℝ, (∀ s, Measurable fun x ↦ evaluation x s) →
      (∀ x s, 0 ≤ evaluation x s) → (∀ x, ∑ s, evaluation x s = 1) →
        ∀ s, Integrable (fun x ↦ evaluation x s) ν := by
    intro evaluation hmeasurable hnonneg htotal s
    refine (integrable_const (1 : ℝ)).mono' (hmeasurable s).aestronglyMeasurable
      (ae_of_all _ fun x ↦ ?_)
    show ‖evaluation x s‖ ≤ 1
    rw [Real.norm_of_nonneg (hnonneg x s), ← htotal x]
    exact Finset.single_le_sum (fun t _ ↦ hnonneg x t) (Finset.mem_univ s)
  have hP := hintegrable evaluationP hmeasurableP hnonnegP htotalP
  have hQ := hintegrable evaluationQ hmeasurableQ hnonnegQ htotalQ
  have hbound : ∀ s, |∫ x, evaluationP x s ∂ν - ∫ x, evaluationQ x s ∂ν| ≤
      ∫ x in escape, (evaluationP x s + evaluationQ x s) ∂ν := by
    intro s
    have hvanish : ∀ x, x ∉ escape → evaluationP x s - evaluationQ x s = 0 := fun x hx ↦ by
      rw [hagree x hx, sub_self]
    have hdifference : IntegrableOn (fun x ↦ ‖evaluationP x s - evaluationQ x s‖) escape ν :=
      ((hP s).sub (hQ s)).norm.integrableOn
    have hsum : IntegrableOn (fun x ↦ evaluationP x s + evaluationQ x s) escape ν :=
      ((hP s).add (hQ s)).integrableOn
    rw [← integral_sub (hP s) (hQ s), ← setIntegral_eq_integral_of_forall_compl_eq_zero hvanish,
      ← Real.norm_eq_abs]
    refine (norm_integral_le_integral_norm _).trans
      (setIntegral_mono hdifference hsum fun x ↦ ?_)
    simp only [Real.norm_eq_abs]
    exact abs_le.mpr ⟨by linarith [hnonnegP x s, hnonnegQ x s],
      by linarith [hnonnegP x s, hnonnegQ x s]⟩
  have htotal : ∑ s, ∫ x in escape, (evaluationP x s + evaluationQ x s) ∂ν =
      2 * ν.real escape := by
    have hsumIntegrable : ∀ s ∈ (univ : Finset S),
        Integrable (fun x ↦ evaluationP x s + evaluationQ x s) (ν.restrict escape) :=
      fun s _ ↦ ((hP s).add (hQ s)).integrableOn
    rw [← integral_finset_sum univ hsumIntegrable]
    have hconstant : ∀ x, ∑ s, (evaluationP x s + evaluationQ x s) = 2 := fun x ↦ by
      rw [Finset.sum_add_distrib, htotalP x, htotalQ x]
      norm_num
    simp only [hconstant, setIntegral_const, smul_eq_mul]
    ring
  unfold totalVariation
  rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
  calc ∑ s, |∫ x, evaluationP x s ∂ν - ∫ x, evaluationQ x s ∂ν|
      ≤ ∑ s, ∫ x in escape, (evaluationP x s + evaluationQ x s) ∂ν :=
        Finset.sum_le_sum fun s _ ↦ hbound s
    _ = ν.real escape * 2 := by rw [htotal, mul_comm]

/-- Spec Corollary 8.1 under (9.1). Assumes: the hypotheses of `measureReal_escapeSet_le_exp` for
the marginal laws `μ t` of the circuit started from `n` arguments carrying `A`, and evaluations of
the circuit state on two inputs as finite laws on samples, measurable in the state, which coincide
on every state that has not escaped. At time `T` the two sample laws are within total variation
`min {1, n |A| e^{D(1+2a)T} / a^ℓ}`. -/
theorem totalVariation_integralLaw_le_exp {V S : Type*} [DecidableEq V] [Fintype V] [Fintype S]
    [MeasurableSpace (Multiset (Finset V))] [MeasurableSingletonClass (Multiset (Finset V))]
    {r : V → V → ℝ} {c D T a : ℝ} {n ℓ : ℕ} {A : Finset V}
    (hr : ∀ i j, 0 ≤ r i j) (hD : ∀ i, ∑ j, r i j ≤ D) (hc : 0 ≤ c) (ha : 1 ≤ a) (hT : 0 ≤ T)
    {μ : ℝ → Measure (Multiset (Finset V))} [∀ t, IsProbabilityMeasure (μ t)]
    (hμ0 : μ 0 = Measure.dirac (Multiset.replicate n A))
    (hint : ∀ t ∈ Set.Icc 0 T, Integrable (weightedCount (lightWeight r A ℓ a)) (μ t))
    (hintL : ∀ t ∈ Set.Icc 0 T,
      Integrable (supportGenerator r c (weightedCount (lightWeight r A ℓ a))) (μ t))
    (hcont : ContinuousOn (fun t ↦ ∫ s, weightedCount (lightWeight r A ℓ a) s ∂μ t)
      (Set.Icc 0 T))
    (hdynkin : ∀ t ∈ Set.Ico 0 T,
      HasDerivWithinAt (fun t ↦ ∫ s, weightedCount (lightWeight r A ℓ a) s ∂μ t)
        (∫ s, supportGenerator r c (weightedCount (lightWeight r A ℓ a)) s ∂μ t) (Set.Ici t) t)
    (evaluationP evaluationQ : Multiset (Finset V) → S → ℝ)
    (hmeasurableP : ∀ x, Measurable fun s ↦ evaluationP s x)
    (hmeasurableQ : ∀ x, Measurable fun s ↦ evaluationQ s x)
    (hnonnegP : ∀ s x, 0 ≤ evaluationP s x) (hnonnegQ : ∀ s x, 0 ≤ evaluationQ s x)
    (htotalP : ∀ s, ∑ x, evaluationP s x = 1) (htotalQ : ∀ s, ∑ x, evaluationQ s x = 1)
    (hagree : ∀ s ∉ escapeSet r A ℓ, evaluationP s = evaluationQ s) :
    totalVariation (fun x ↦ ∫ s, evaluationP s x ∂μ T) (fun x ↦ ∫ s, evaluationQ s x ∂μ T) ≤
      min 1 (n * A.card * Real.exp (D * (1 + 2 * a) * T) / a ^ ℓ) :=
  (totalVariation_integralLaw_le (μ T) evaluationP evaluationQ hmeasurableP hmeasurableQ
    hnonnegP hnonnegQ htotalP htotalQ hagree).trans
    (measureReal_escapeSet_le_exp hr hD hc ha hT hμ0 hint hintL hcont hdynkin)

/-- Spec Corollary 8.1 under (9.2). Assumes: `DT > 0`, `ℓ ≥ 2DT`, and the hypotheses of
`totalVariation_integralLaw_le_exp` at the radius `a = ℓ/(2DT)`. At time `T` the two sample laws
are within total variation `min {1, n |A| e^{DT} (2eDT/ℓ)^ℓ}`. -/
theorem totalVariation_integralLaw_le_radius {V S : Type*} [DecidableEq V] [Fintype V] [Fintype S]
    [MeasurableSpace (Multiset (Finset V))] [MeasurableSingletonClass (Multiset (Finset V))]
    {r : V → V → ℝ} {c D T : ℝ} {n ℓ : ℕ} {A : Finset V}
    (hr : ∀ i j, 0 ≤ r i j) (hD : ∀ i, ∑ j, r i j ≤ D) (hc : 0 ≤ c) (hT : 0 ≤ T)
    (hDT : 0 < D * T) (hradius : 2 * D * T ≤ ℓ)
    {μ : ℝ → Measure (Multiset (Finset V))} [∀ t, IsProbabilityMeasure (μ t)]
    (hμ0 : μ 0 = Measure.dirac (Multiset.replicate n A))
    (hint : ∀ t ∈ Set.Icc 0 T,
      Integrable (weightedCount (lightWeight r A ℓ (ℓ / (2 * D * T)))) (μ t))
    (hintL : ∀ t ∈ Set.Icc 0 T,
      Integrable (supportGenerator r c (weightedCount (lightWeight r A ℓ (ℓ / (2 * D * T)))))
        (μ t))
    (hcont : ContinuousOn
      (fun t ↦ ∫ s, weightedCount (lightWeight r A ℓ (ℓ / (2 * D * T))) s ∂μ t) (Set.Icc 0 T))
    (hdynkin : ∀ t ∈ Set.Ico 0 T,
      HasDerivWithinAt (fun t ↦ ∫ s, weightedCount (lightWeight r A ℓ (ℓ / (2 * D * T))) s ∂μ t)
        (∫ s, supportGenerator r c (weightedCount (lightWeight r A ℓ (ℓ / (2 * D * T)))) s ∂μ t)
        (Set.Ici t) t)
    (evaluationP evaluationQ : Multiset (Finset V) → S → ℝ)
    (hmeasurableP : ∀ x, Measurable fun s ↦ evaluationP s x)
    (hmeasurableQ : ∀ x, Measurable fun s ↦ evaluationQ s x)
    (hnonnegP : ∀ s x, 0 ≤ evaluationP s x) (hnonnegQ : ∀ s x, 0 ≤ evaluationQ s x)
    (htotalP : ∀ s, ∑ x, evaluationP s x = 1) (htotalQ : ∀ s, ∑ x, evaluationQ s x = 1)
    (hagree : ∀ s ∉ escapeSet r A ℓ, evaluationP s = evaluationQ s) :
    totalVariation (fun x ↦ ∫ s, evaluationP s x ∂μ T) (fun x ↦ ∫ s, evaluationQ s x ∂μ T) ≤
      min 1 (n * A.card * Real.exp (D * T) * (2 * Real.exp 1 * D * T / ℓ) ^ ℓ) := by
  have ha : 1 ≤ (ℓ : ℝ) / (2 * D * T) := by
    rw [le_div_iff₀ (by linarith)]
    linarith
  have h := totalVariation_integralLaw_le_exp hr hD hc ha hT hμ0 hint hintL hcont hdynkin
    evaluationP evaluationQ hmeasurableP hmeasurableQ hnonnegP hnonnegQ htotalP htotalQ hagree
  rwa [exp_div_pow_eq_of_radius hDT.ne'] at h

end

end Descent.Pangenome.AncestralLocality
