/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.BinomialAggregateEnvelope

assert_below Descent.Decision Descent.Program

/-!
# The unrestricted fixed-time envelope and the exact cost of nonanticipation

This module formalizes DC Theorem 5.1 and Corollary 5.2.

Dropping the coadaptation constraint and keeping only the fixed-time coordinate
probabilities, the minimum of every convex aggregate report is the two-point law
`a + Bernoulli(δ)` with `μ = a + δ` the common mean count. The lower bound is Jensen's
inequality in the exact form the grid supplies: the adjacent secant at `a` supports a
grid-convex function at every grid point, which is
`Descent.Portability.ConvexOrderCoupling.right_secant_support`. The bound is attained by
`twoPointExp`, an explicit two-point law, giving DC (5.2)
`min E(2N - n)² = (2μ - n)² + 4δ(1 - δ)`.

Corollary 5.2 is then exact on the manuscript's instance: at `n = 4`, coordinate
probability `3/4` and `ν = 0`, an unrestricted coupling reports mean squared correlation
`1/4` -- exhibited by the uniform law on the four configurations with exactly three
aligned loci, whose coordinate marginals are checked -- while the coadapted minimum from
`Descent.Portability.BinomialAggregateEnvelope.binomial_envelope_lower` is `3/8`. The gap
is exactly `1/8`, and it is positive, so a theorem about coadapted processes is not a
theorem about all couplings of the same marginal path laws.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.NonanticipationCost

open Foundations TurnoverArchitectureMetrics BinomialAggregateEnvelope

noncomputable section

/-! ## The unrestricted fixed-time convex envelope -/

/-- The convex aggregate report `(2N - n)²` of DC (5.2). -/
def squareReport (n : ℕ) (k : ℤ) : ℝ := (2 * (k : ℝ) - (n : ℝ)) ^ 2

/-- The squared aggregate report is grid convex, with constant second difference `8`. -/
theorem squareReport_gridConvex (n : ℕ) :
    ∀ j : ℤ, 1 ≤ j → j + 1 ≤ (n : ℤ) →
      0 ≤ squareReport n (j - 1) - 2 * squareReport n j + squareReport n (j + 1) := by
  intro j _ _
  have h : squareReport n (j - 1) - 2 * squareReport n j + squareReport n (j + 1) = 8 := by
    simp only [squareReport]
    push_cast
    ring
  linarith

/-- **DC Theorem 5.1, lower bound.**  Among all laws of the count with a prescribed mean
`a + δ` inside the grid, every grid-convex report is at least its linear interpolation at
that mean.  Only the mean is constrained, so this covers every coupling of the coordinate
path laws, coadapted or not. -/
theorem fixed_time_convex_lower_bound (n : ℕ) (f : ℤ → ℝ)
    (hf : ∀ j : ℤ, 1 ≤ j → j + 1 ≤ (n : ℤ) → 0 ≤ f (j - 1) - 2 * f j + f (j + 1))
    {Ω : Type*} [Fintype Ω] (w : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω) (hsum : ∑ ω, w ω = 1)
    (N : Ω → ℕ) (hNn : ∀ ω, N ω ≤ n) (a : ℕ) (δ : ℝ) (han : a + 1 ≤ n)
    (hmean : ∑ ω, w ω * ((N ω : ℕ) : ℝ) = (a : ℝ) + δ) :
    (1 - δ) * f ((a : ℕ) : ℤ) + δ * f (((a : ℕ) : ℤ) + 1)
      ≤ ∑ ω, w ω * f ((N ω : ℕ) : ℤ) := by
  have hk0 : (0 : ℤ) ≤ ((a : ℕ) : ℤ) := by positivity
  have hk1n : ((a : ℕ) : ℤ) + 1 ≤ (n : ℤ) := by exact_mod_cast han
  have hsupp : ∀ ω : Ω,
      (f (((a : ℕ) : ℤ) + 1) - f ((a : ℕ) : ℤ)) * (((N ω : ℕ) : ℝ) - ((a : ℕ) : ℝ))
        ≤ f ((N ω : ℕ) : ℤ) - f ((a : ℕ) : ℤ) := by
    intro ω
    have h := ConvexOrderCoupling.right_secant_support n f hf (k := ((a : ℕ) : ℤ))
      (j := ((N ω : ℕ) : ℤ)) hk0 hk1n (by positivity) (by exact_mod_cast hNn ω)
    have hc : ((((N ω : ℕ) : ℤ)) : ℝ) - ((((a : ℕ) : ℤ)) : ℝ)
        = ((N ω : ℕ) : ℝ) - ((a : ℕ) : ℝ) := by push_cast; ring
    rw [hc] at h
    exact h
  have h1 : ∑ ω, w ω * ((f (((a : ℕ) : ℤ) + 1) - f ((a : ℕ) : ℤ))
        * (((N ω : ℕ) : ℝ) - ((a : ℕ) : ℝ)))
      ≤ ∑ ω, w ω * (f ((N ω : ℕ) : ℤ) - f ((a : ℕ) : ℤ)) :=
    Finset.sum_le_sum fun ω _ ↦ mul_le_mul_of_nonneg_left (hsupp ω) (hw ω)
  have hL : ∑ ω, w ω * ((f (((a : ℕ) : ℤ) + 1) - f ((a : ℕ) : ℤ))
        * (((N ω : ℕ) : ℝ) - ((a : ℕ) : ℝ)))
      = (f (((a : ℕ) : ℤ) + 1) - f ((a : ℕ) : ℤ)) * δ := by
    have hpt : ∀ ω : Ω, w ω * ((f (((a : ℕ) : ℤ) + 1) - f ((a : ℕ) : ℤ))
          * (((N ω : ℕ) : ℝ) - ((a : ℕ) : ℝ)))
        = (f (((a : ℕ) : ℤ) + 1) - f ((a : ℕ) : ℤ)) * (w ω * ((N ω : ℕ) : ℝ))
          - ((f (((a : ℕ) : ℤ) + 1) - f ((a : ℕ) : ℤ)) * ((a : ℕ) : ℝ)) * w ω :=
      fun ω ↦ by ring
    rw [Finset.sum_congr rfl fun ω _ ↦ hpt ω, Finset.sum_sub_distrib, ← Finset.mul_sum,
      ← Finset.mul_sum, hmean, hsum]
    ring
  have hR : ∑ ω, w ω * (f ((N ω : ℕ) : ℤ) - f ((a : ℕ) : ℤ))
      = (∑ ω, w ω * f ((N ω : ℕ) : ℤ)) - f ((a : ℕ) : ℤ) := by
    have hpt : ∀ ω : Ω, w ω * (f ((N ω : ℕ) : ℤ) - f ((a : ℕ) : ℤ))
        = w ω * f ((N ω : ℕ) : ℤ) - f ((a : ℕ) : ℤ) * w ω := fun ω ↦ by ring
    rw [Finset.sum_congr rfl fun ω _ ↦ hpt ω, Finset.sum_sub_distrib, ← Finset.mul_sum, hsum]
    ring
  rw [hL, hR] at h1
  linarith

/-! ## The attaining two-point law -/

/-- The attaining law of DC (5.1): the count is `a` with probability `1 - δ` and `a + 1`
with probability `δ`. -/
def twoPointExp (δ : ℝ) (h0 : 0 ≤ δ) (h1 : δ ≤ 1) : ExpFunctional (Fin 2) :=
  weightedExp ![1 - δ, δ]
    (by
      intro i
      fin_cases i
      · show (0 : ℝ) ≤ 1 - δ
        linarith
      · show (0 : ℝ) ≤ δ
        linarith)
    (by
      rw [Fin.sum_univ_two]
      show (1 - δ) + δ = 1
      ring)

/-- The two counts carried by the attaining law. -/
def twoPointCount (a : ℕ) : Fin 2 → ℕ := ![a, a + 1]

/-- The attaining law has the prescribed mean count `a + δ`. -/
theorem twoPoint_mean (a : ℕ) (δ : ℝ) (h0 : 0 ≤ δ) (h1 : δ ≤ 1) :
    twoPointExp δ h0 h1 (fun i ↦ ((twoPointCount a i : ℕ) : ℝ)) = (a : ℝ) + δ := by
  show ∑ i : Fin 2, ![1 - δ, δ] i * ((twoPointCount a i : ℕ) : ℝ) = (a : ℝ) + δ
  rw [Fin.sum_univ_two]
  show (1 - δ) * ((a : ℕ) : ℝ) + δ * (((a + 1 : ℕ)) : ℝ) = (a : ℝ) + δ
  push_cast
  ring

/-- The attaining law reports exactly the interpolated value, for every report. -/
theorem twoPoint_value (a : ℕ) (δ : ℝ) (h0 : 0 ≤ δ) (h1 : δ ≤ 1) (f : ℤ → ℝ) :
    twoPointExp δ h0 h1 (fun i ↦ f ((twoPointCount a i : ℕ) : ℤ))
      = (1 - δ) * f ((a : ℕ) : ℤ) + δ * f (((a : ℕ) : ℤ) + 1) := by
  show ∑ i : Fin 2, ![1 - δ, δ] i * f ((twoPointCount a i : ℕ) : ℤ) = _
  rw [Fin.sum_univ_two]
  show (1 - δ) * f ((a : ℕ) : ℤ) + δ * f (((a + 1 : ℕ)) : ℤ) = _
  push_cast
  ring

/-- **DC (5.2)**: the attaining law's squared aggregate report is
`(2μ - n)² + 4δ(1 - δ)`. -/
theorem twoPoint_squared_value (n a : ℕ) (δ : ℝ) (h0 : 0 ≤ δ) (h1 : δ ≤ 1) :
    twoPointExp δ h0 h1 (fun i ↦ squareReport n ((twoPointCount a i : ℕ) : ℤ))
      = (2 * ((a : ℝ) + δ) - (n : ℝ)) ^ 2 + 4 * δ * (1 - δ) := by
  rw [twoPoint_value a δ h0 h1 (squareReport n)]
  simp only [squareReport]
  push_cast
  ring

/-- **DC Theorem 5.1 and (5.2)**: the exact unrestricted fixed-time minimum of the squared
aggregate report.  The bound holds for every law of the count with the prescribed mean, and
`twoPoint_squared_value` shows it is attained. -/
theorem unrestricted_square_min (n a : ℕ) (δ : ℝ) (han : a + 1 ≤ n)
    {Ω : Type*} [Fintype Ω] (w : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω) (hsum : ∑ ω, w ω = 1)
    (N : Ω → ℕ) (hNn : ∀ ω, N ω ≤ n)
    (hmean : ∑ ω, w ω * ((N ω : ℕ) : ℝ) = (a : ℝ) + δ) :
    (2 * ((a : ℝ) + δ) - (n : ℝ)) ^ 2 + 4 * δ * (1 - δ)
      ≤ ∑ ω, w ω * squareReport n ((N ω : ℕ) : ℤ) := by
  have hbound := fixed_time_convex_lower_bound n (squareReport n) (squareReport_gridConvex n)
    w hw hsum N hNn a δ han hmean
  have hid : (1 - δ) * squareReport n ((a : ℕ) : ℤ) + δ * squareReport n (((a : ℕ) : ℤ) + 1)
      = (2 * ((a : ℝ) + δ) - (n : ℝ)) ^ 2 + 4 * δ * (1 - δ) := by
    simp only [squareReport]
    push_cast
    ring
  linarith

/-! ## The exact positive cost of nonanticipation, DC Corollary 5.2 -/

/-- The four configurations of `n = 4` loci with exactly three aligned. -/
def tripleConfig (j : Fin 4) : Fin 4 → Bool := fun i ↦ decide (i ≠ j)

/-- Each of them has count three. -/
theorem tripleConfig_count (j : Fin 4) :
    ConvexOrderCoupling.occupiedCount (tripleConfig j) = 3 := by
  fin_cases j <;> decide

/-- Exactly three of the four configurations align coordinate `i`. -/
theorem tripleConfig_marginal_card (i : Fin 4) :
    (Finset.univ.filter (fun j : Fin 4 ↦ tripleConfig j i = true)).card = 3 := by
  fin_cases i <;> decide

/-- **The unrestricted construction has the prescribed coordinate marginals.**  Each
coordinate is aligned with probability `3/4`, so this law does couple the specified
one-locus laws; only the joint geometry is unrestricted. -/
theorem tripleConfig_marginal (i : Fin 4) :
    uniformExp (Fin 4) (fun j ↦ if tripleConfig j i = true then (1 : ℝ) else 0) = 3 / 4 := by
  rw [uniformExp_apply, ← Finset.mul_sum, Finset.sum_boole, tripleConfig_marginal_card]
  norm_num

/-- **DC Corollary 5.2, unrestricted minimum.**  The constant-count coupling reports mean
squared correlation `1/4`. -/
theorem unrestricted_min_r2 :
    uniformExp (Fin 4)
        (fun j ↦ countR2 4 0 (ConvexOrderCoupling.occupiedCount (tripleConfig j)))
      = 1 / 4 := by
  have hconst : (fun j : Fin 4 ↦
      countR2 4 0 (ConvexOrderCoupling.occupiedCount (tripleConfig j)))
      = fun _ ↦ countR2 4 0 3 := funext fun j ↦ by rw [tripleConfig_count j]
  rw [hconst, ExpFunctional.eval_const]
  norm_num [countR2]

/-- **DC Corollary 5.2, coadapted minimum.**  The coadapted envelope's lower endpoint at
`n = 4`, `p = 1/2` and `ν = 0` is `3/8`. -/
theorem coadapted_min_r2 :
    binomialExp 2 (1 / 2) (by norm_num) (by norm_num)
        (fun k ↦ countR2 4 0 (2 + (k : ℕ))) = 3 / 8 := by
  have h := binomial_envelope_lower 2 (by norm_num) (1 / 2) 0 (by norm_num) (by norm_num)
    (le_refl 0)
  norm_num at h ⊢
  exact h

/-- **DC (5.3), the exact positive cost of nonanticipation.**  The unrestricted minimum is
strictly below the coadapted minimum, by exactly `1/8`.  Both constructions preserve the
whole one-locus law; only the second respects the full-filtration rate constraint. -/
theorem nonanticipation_gap :
    binomialExp 2 (1 / 2) (by norm_num) (by norm_num)
          (fun k ↦ countR2 4 0 (2 + (k : ℕ)))
        - uniformExp (Fin 4)
          (fun j ↦ countR2 4 0 (ConvexOrderCoupling.occupiedCount (tripleConfig j)))
      = 1 / 8 := by
  rw [coadapted_min_r2, unrestricted_min_r2]
  norm_num

/-- The cost of nonanticipation is strictly positive. -/
theorem nonanticipation_gap_pos :
    uniformExp (Fin 4)
        (fun j ↦ countR2 4 0 (ConvexOrderCoupling.occupiedCount (tripleConfig j)))
      < binomialExp 2 (1 / 2) (by norm_num) (by norm_num)
        (fun k ↦ countR2 4 0 (2 + (k : ℕ))) := by
  rw [coadapted_min_r2, unrestricted_min_r2]
  norm_num

end

end Descent.Portability.NonanticipationCost
