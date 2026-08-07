/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Coalescent.EntranceLaw
import Descent.Coalescent.LaplaceTransform
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Independence.Integration
import Mathlib.Tactic

assert_below Descent.Pangenome Descent.PopGen Descent.Spectral Descent.Blindness
assert_below Descent.Conditionals
assert_below Descent.Portability Descent.Decision Descent.Program

namespace Descent

/-!
# K-G (5.9): the transit time's transform is a product

K-G (5.9) computes the transit time's density from

  `E(e^{-θT}) = ∏_{r≥2} d_r/(d_r + θ)`,

and `Descent.Coalescent.Rates.transitDensityTerm` carries the series that comes out of it.
The identity itself has never been in the corpus.  It needs three things the corpus now has:
`Descent.Coalescent.LaplaceTransform` for the factor, `Descent.Coalescent.EntranceLaw`'s
product measure for the clock, and the independence of that product's coordinates -- which is
`ProbabilityTheory.iIndepFun_infinitePi`, and is the whole content of "the `τ_r` are
independent" in K-C (1.12).

With those, the identity is Fubini for independent factors: the transform of a sum is the
product of the transforms, one factor per level, each `d_r/(d_r+θ)`.

  `E(exp(-θ Σ_{k<m} τ_k)) = ∏_{k<m} γ_k/(γ_k + θ)`.

`kingman_transitTransform` reads it at Kingman's ladder, which is K-G (5.9)'s own product.

## Why this is the shape the converse needs

`EntranceLaw` proves the forward half of Schweinsberg's equivalence -- summable means give an
almost surely finite descent.  The converse runs through exactly this transform: the descent
time is infinite almost surely precisely when the product tends to zero, which for
`θ = 1` is `Σ log(1 + γ_k⁻¹) = ∞`.  The transform is therefore not a detour; it is the
instrument.  What is still missing for the converse is the passage from the finite products
to the infinite one, a monotone-convergence step over a decreasing sequence.

## Main results

- `indep_holdCoords`: the clock's coordinates are independent -- K-C (1.12)'s premise, proved
  of the construction rather than assumed.
- `lintegral_exp_neg_partialSum`: **`E(e^{-θ Σ τ}) = ∏ γ_k/(γ_k+θ)`**.
- `kingman_transitTransform`: the same at `d_r = r(r-1)/2`, K-G (5.9).
-/

namespace Coalescent

open MeasureTheory ProbabilityTheory Finset

/-- **The clock's coordinates are independent.**  K-C (1.12) says the sojourn times `τ_r` are
independent; here that is a property of the construction -- `Measure.infinitePi` -- rather
than a hypothesis, and `ProbabilityTheory.iIndepFun_infinitePi` is the proof. -/
theorem indep_holdCoords {γ : ℕ → ℝ} (hγ : ∀ k, 0 < γ (k + 2)) (θ : ℝ) :
    iIndepFun (fun (k : ℕ) (ω : ℕ → ℝ) ↦ ENNReal.ofReal (Real.exp (-(θ * ω k))))
      (holdProduct γ hγ) := by
  haveI : ∀ k : ℕ, IsProbabilityMeasure (holdMeasure (γ (k + 2))) := fun k ↦
    holdMeasure_isProbabilityMeasure (hγ k)
  exact iIndepFun_infinitePi (X := fun _ (t : ℝ) ↦ ENNReal.ofReal (Real.exp (-(θ * t))))
    (fun _ ↦ ((measurable_const.mul measurable_id).neg.exp).ennreal_ofReal)

/-- **K-G (5.9), at every truncation.**  The transform of a partial sum of sojourns is the
product of the per-level transforms.  Independence turns the integral of a product into a
product of integrals, and `LaplaceTransform.lintegral_exp_neg_holdMeasure` evaluates each. -/
theorem lintegral_exp_neg_partialSum {γ : ℕ → ℝ} (hγ : ∀ k, 0 < γ (k + 2)) {θ : ℝ}
    (hθ : 0 ≤ θ) (m : ℕ) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (-(θ * ∑ k ∈ range m, ω k))) ∂(holdProduct γ hγ)
      = ∏ k ∈ range m, ENNReal.ofReal (γ (k + 2) / (γ (k + 2) + θ)) := by
  haveI : ∀ k : ℕ, IsProbabilityMeasure (holdMeasure (γ (k + 2))) := fun k ↦
    holdMeasure_isProbabilityMeasure (hγ k)
  have hsplit : ∀ ω : ℕ → ℝ, ENNReal.ofReal (Real.exp (-(θ * ∑ k ∈ range m, ω k)))
      = ∏ k ∈ range m, ENNReal.ofReal (Real.exp (-(θ * ω k))) := by
    intro ω
    have hprod : Real.exp (-(θ * ∑ k ∈ range m, ω k))
        = ∏ k ∈ range m, Real.exp (-(θ * ω k)) := by
      rw [← Real.exp_sum]
      congr 1
      rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    rw [hprod, ENNReal.ofReal_prod_of_nonneg]
    intro k _
    positivity
  simp only [hsplit]
  rw [lintegral_prod_eq_prod_lintegral_of_indepFun (range m)
    (fun (k : ℕ) (ω : ℕ → ℝ) ↦ ENNReal.ofReal (Real.exp (-(θ * ω k)))) (indep_holdCoords hγ θ)
    (fun k ↦ ((measurable_const.mul (measurable_pi_apply k)).neg.exp).ennreal_ofReal)]
  refine Finset.prod_congr rfl fun k _ ↦ ?_
  have hco : ∫⁻ ω : ℕ → ℝ, ENNReal.ofReal (Real.exp (-(θ * ω k))) ∂(holdProduct γ hγ)
      = ∫⁻ t, ENNReal.ofReal (Real.exp (-(θ * t))) ∂(holdMeasure (γ (k + 2))) := by
    unfold holdProduct
    exact (measurePreserving_eval_infinitePi
      (fun k : ℕ ↦ holdMeasure (γ (k + 2))) k).lintegral_comp
      (((measurable_const.mul measurable_id).neg.exp).ennreal_ofReal)
  rw [hco, lintegral_exp_neg_holdMeasure (hγ k) hθ]

/-- **K-G (5.9) at Kingman's ladder.**  Each level contributes `d_r/(d_r+θ)`, and the transit
time's transform is their product -- the identity from which K-G reads off the density
`Rates.transitDensityTerm` sums. -/
theorem kingman_transitTransform {θ : ℝ} (hθ : 0 ≤ θ) (m : ℕ) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (-(θ * ∑ k ∈ range m, ω k)))
        ∂(holdProduct deathRate (fun k ↦ deathRate_pos (by omega)))
      = ∏ k ∈ range m, ENNReal.ofReal (deathRate (k + 2) / (deathRate (k + 2) + θ)) :=
  lintegral_exp_neg_partialSum _ hθ m

end Coalescent

end Descent
