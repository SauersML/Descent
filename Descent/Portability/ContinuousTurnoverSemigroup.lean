/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.BanachEulerExponential
import Descent.Portability.ConvexOrderCoupling
import Mathlib.Analysis.Matrix
import Mathlib.Analysis.Normed.Module.FiniteDimension

assert_below Descent.Decision Descent.Program

/-!
# Towards the continuous-time form of the dynamic convex-order theorem

Two of the three ingredients of the continuous-time form of DC Theorem 3.1 / PL Theorem 5.3
for Markov admissible generators.

`exp_mulVec_le_of_euler` is the limit bridge: matrix evaluation against a fixed vector at a
fixed coordinate is linear, hence continuous in finite dimension, so an inequality between
the Euler approximants of two finite-state generators passes to the semigroups they
generate, via the Euler limit of `Descent.Portability.BanachEulerExponential`.

`nearestDriftMatrix` realizes the nearest-drift generator `L_*` of DC (3.4) / PL (5.8) as a
matrix on the count grid `{0, …, n}`, and `nearestDriftMatrix_mulVec_le` is DC Lemma 3.4 for
Markov generators: among all finite-state generators with nonnegative off-diagonal rates,
rows summing to zero, and the count drift forced by the coordinate-rate constraints,
`L_*` acts most negatively on every grid-convex report.

**Scope.** The semigroup comparison itself is NOT proved here. Closing it needs, in order:
convexity preservation by `1 + τ L_*` transported from
`Descent.Portability.ConvexOrderCoupling.driftStep_gridConvex` through `gridEmbed`; the
iterated comparison `(1 + τ L_*)^m v ≤ (1 + τ L)^m v` (induction, using that `1 + τ L` is
entrywise nonnegative for short steps); and instantiating `exp_mulVec_le_of_euler` at
`τ = t/m` for large `m`. Until those land, the dynamic convex-order theorem in this corpus
is the discrete skeleton `ConvexOrderCoupling.pathExp_nearestDrift_le`, which is proved for
arbitrary history-dependent couplings rather than Markov ones.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.ContinuousTurnoverSemigroup

open scoped Matrix.Norms.Operator

noncomputable section

/-- Evaluating a matrix against a fixed vector at a fixed coordinate is linear. -/
def mulVecEntry (N : ℕ) (v : Fin N → ℝ) (j : Fin N) :
    Matrix (Fin N) (Fin N) ℝ →ₗ[ℝ] ℝ where
  toFun M := M.mulVec v j
  map_add' M M' := by simp [Matrix.add_mulVec]
  map_smul' c M := by simp [Matrix.smul_mulVec_assoc]

/-- **Euler limits transfer a pointwise inequality to the generated semigroups.** -/
theorem exp_mulVec_le_of_euler {N : ℕ} (A B : Matrix (Fin N) (Fin N) ℝ) (v : Fin N → ℝ)
    (j : Fin N)
    (h : ∀ m : ℕ, ((1 + (m : ℝ)⁻¹ • A) ^ m).mulVec v j
      ≤ ((1 + (m : ℝ)⁻¹ • B) ^ m).mulVec v j) :
    (NormedSpace.exp ℝ A).mulVec v j ≤ (NormedSpace.exp ℝ B).mulVec v j := by
  have hcont : Continuous (mulVecEntry N v j) :=
    (mulVecEntry N v j).continuous_of_finiteDimensional
  have hA := (hcont.tendsto (NormedSpace.exp ℝ A)).comp
    (BanachEulerExponential.euler_tends_exp A)
  have hB := (hcont.tendsto (NormedSpace.exp ℝ B)).comp
    (BanachEulerExponential.euler_tends_exp B)
  exact le_of_tendsto_of_tendsto hA hB (Filter.Eventually.of_forall h)


/-! ## The nearest-drift generator as a finite matrix -/

/-- A count vector embedded in `ℤ → ℝ` by clamping outside the grid.  The clamped values
are always multiplied by a vanishing rate, so the choice of extension is immaterial. -/
def gridEmbed (n : ℕ) (v : Fin (n + 1) → ℝ) : ℤ → ℝ :=
  fun k ↦ v ⟨min k.toNat n, by omega⟩

/-- The clamped successor on the count grid. -/
def gridSucc (n : ℕ) (k : Fin (n + 1)) : Fin (n + 1) := ⟨min ((k : ℕ) + 1) n, by omega⟩

/-- The truncated predecessor on the count grid. -/
def gridPred (n : ℕ) (k : Fin (n + 1)) : Fin (n + 1) :=
  ⟨(k : ℕ) - 1, by have := k.isLt; omega⟩

/-- The embedding restores the vector on the grid. -/
theorem gridEmbed_coe (n : ℕ) (v : Fin (n + 1) → ℝ) (k : Fin (n + 1)) :
    gridEmbed n v ((k : ℕ) : ℤ) = v k := by
  have hk := k.isLt
  have h : (⟨min (((k : ℕ) : ℤ)).toNat n, by omega⟩ : Fin (n + 1)) = k := by
    apply Fin.ext
    simp only [Int.toNat_natCast]
    omega
  simp only [gridEmbed]
  rw [h]

/-- The embedding one step up the grid. -/
theorem gridEmbed_succ (n : ℕ) (v : Fin (n + 1) → ℝ) (k : Fin (n + 1)) :
    gridEmbed n v (((k : ℕ) : ℤ) + 1) = v (gridSucc n k) := by
  have hk := k.isLt
  have h : (⟨min ((((k : ℕ) : ℤ) + 1)).toNat n, by omega⟩ : Fin (n + 1)) = gridSucc n k := by
    apply Fin.ext
    simp only [gridSucc]
    omega
  simp only [gridEmbed]
  rw [h]

/-- The embedding one step down the grid. -/
theorem gridEmbed_pred (n : ℕ) (v : Fin (n + 1) → ℝ) (k : Fin (n + 1)) :
    gridEmbed n v (((k : ℕ) : ℤ) - 1) = v (gridPred n k) := by
  have hk := k.isLt
  have h : (⟨min ((((k : ℕ) : ℤ) - 1)).toNat n, by omega⟩ : Fin (n + 1)) = gridPred n k := by
    apply Fin.ext
    simp only [gridPred]
    omega
  simp only [gridEmbed]
  rw [h]

/-- The nearest-drift generator `L_*` of DC (3.4) / PL (5.8) as a matrix on the count grid.
The clamped successor and predecessor are harmless because the outward rate vanishes at
each endpoint. -/
def nearestDriftMatrix (n : ℕ) (α β : ℝ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  Matrix.of fun k j ↦
    ConvexOrderCoupling.upRate n α β ((k : ℕ) : ℤ)
        * ((if j = gridSucc n k then (1 : ℝ) else 0) - (if j = k then (1 : ℝ) else 0))
      + ConvexOrderCoupling.downRate n α β ((k : ℕ) : ℤ)
        * ((if j = gridPred n k then (1 : ℝ) else 0) - (if j = k then (1 : ℝ) else 0))

/-- The matrix acts on count vectors exactly as the nearest-drift generator acts on their
embeddings. -/
theorem nearestDriftMatrix_mulVec (n : ℕ) (α β : ℝ) (v : Fin (n + 1) → ℝ) (k : Fin (n + 1)) :
    (nearestDriftMatrix n α β).mulVec v k
      = ConvexOrderCoupling.nearestDriftGen n α β (gridEmbed n v) ((k : ℕ) : ℤ) := by
  have hsum : ∀ c : Fin (n + 1),
      ∑ j : Fin (n + 1), (if j = c then (1 : ℝ) else 0) * v j = v c := by
    intro c
    simp only [ite_mul, one_mul, zero_mul]
    rw [Finset.sum_ite_eq' Finset.univ c v, if_pos (Finset.mem_univ c)]
  have hpt : ∀ j : Fin (n + 1), nearestDriftMatrix n α β k j * v j
      = ConvexOrderCoupling.upRate n α β ((k : ℕ) : ℤ)
          * ((if j = gridSucc n k then (1 : ℝ) else 0) * v j
            - (if j = k then (1 : ℝ) else 0) * v j)
        + ConvexOrderCoupling.downRate n α β ((k : ℕ) : ℤ)
          * ((if j = gridPred n k then (1 : ℝ) else 0) * v j
            - (if j = k then (1 : ℝ) else 0) * v j) := by
    intro j
    simp only [nearestDriftMatrix, Matrix.of_apply]
    ring
  show ∑ j : Fin (n + 1), nearestDriftMatrix n α β k j * v j = _
  rw [Finset.sum_congr rfl fun j _ ↦ hpt j, Finset.sum_add_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  simp only [hsum]
  simp only [ConvexOrderCoupling.nearestDriftGen, gridEmbed_succ, gridEmbed_pred, gridEmbed_coe]

/-- **DC Lemma 3.4 for Markov generators.**  Among all finite-state generators whose
off-diagonal rates are nonnegative, whose rows sum to zero, and whose count drift is the one
forced by the coordinate-rate constraints DC (3.2) / PL (5.7), the nearest-drift generator
acts most negatively on every grid-convex report.  No structure of the jumps is assumed. -/
theorem nearestDriftMatrix_mulVec_le (n : ℕ) (α β : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (L : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (hoff : ∀ k j, j ≠ k → 0 ≤ L k j)
    (hrow : ∀ k, ∑ j, L k j = 0)
    (hdrift : ∀ k : Fin (n + 1), ∑ j, L k j * (((j : ℕ) : ℝ) - ((k : ℕ) : ℝ))
      = ConvexOrderCoupling.countDrift n α β ((k : ℕ) : ℤ))
    (v : Fin (n + 1) → ℝ)
    (hv : ∀ j : ℤ, 1 ≤ j → j + 1 ≤ (n : ℤ) →
      0 ≤ gridEmbed n v (j - 1) - 2 * gridEmbed n v j + gridEmbed n v (j + 1))
    (k : Fin (n + 1)) :
    (nearestDriftMatrix n α β).mulVec v k ≤ L.mulVec v k := by
  have hk := k.isLt
  have hgen := ConvexOrderCoupling.nearestDrift_generator_le n α β 1 hα hβ (gridEmbed n v) hv
    ((k : ℕ) : ℤ) (by positivity) (by omega)
    (fun j : Fin (n + 1) ↦ if j = k then (0 : ℝ) else L k j)
    (fun j ↦ by
      show (0 : ℝ) ≤ if j = k then (0 : ℝ) else L k j
      by_cases h : j = k
      · simp [h]
      · rw [if_neg h]
        exact hoff k j h)
    (fun j : Fin (n + 1) ↦ ((j : ℕ) : ℤ) - ((k : ℕ) : ℤ))
    (fun j ↦ by
      have := j.isLt
      show (0 : ℤ) ≤ ((k : ℕ) : ℤ) + (((j : ℕ) : ℤ) - ((k : ℕ) : ℤ))
      omega)
    (fun j ↦ by
      have := j.isLt
      show ((k : ℕ) : ℤ) + (((j : ℕ) : ℤ) - ((k : ℕ) : ℤ)) ≤ (n : ℤ)
      omega)
    (by
      have hall : ∀ j : Fin (n + 1),
          (if j = k then (0 : ℝ) else L k j)
              * (((((k : ℕ) : ℤ) + (((j : ℕ) : ℤ) - ((k : ℕ) : ℤ)) : ℤ) : ℝ)
                - (((k : ℕ) : ℤ) : ℝ))
            = L k j * (((j : ℕ) : ℝ) - ((k : ℕ) : ℝ)) := by
        intro j
        by_cases h : j = k
        · rw [if_pos h, h]
          push_cast
          ring
        · rw [if_neg h]
          push_cast
          ring
      rw [Finset.sum_congr rfl fun j _ ↦ hall j, hdrift k]
      ring)
  have hrhs : ∑ j : Fin (n + 1), (if j = k then (0 : ℝ) else L k j)
        * (gridEmbed n v (((k : ℕ) : ℤ) + (((j : ℕ) : ℤ) - ((k : ℕ) : ℤ)))
          - gridEmbed n v ((k : ℕ) : ℤ))
      = L.mulVec v k := by
    have hpt : ∀ j : Fin (n + 1), (if j = k then (0 : ℝ) else L k j)
          * (gridEmbed n v (((k : ℕ) : ℤ) + (((j : ℕ) : ℤ) - ((k : ℕ) : ℤ)))
            - gridEmbed n v ((k : ℕ) : ℤ))
        = L k j * v j - L k j * v k := by
      intro j
      have hidx : ((k : ℕ) : ℤ) + (((j : ℕ) : ℤ) - ((k : ℕ) : ℤ)) = ((j : ℕ) : ℤ) := by ring
      rw [hidx, gridEmbed_coe, gridEmbed_coe]
      by_cases h : j = k
      · rw [if_pos h, h]
        ring
      · rw [if_neg h]
        ring
    rw [Finset.sum_congr rfl fun j _ ↦ hpt j, Finset.sum_sub_distrib, ← Finset.sum_mul, hrow k]
    show (∑ j : Fin (n + 1), L k j * v j) - 0 * v k = ∑ j : Fin (n + 1), L k j * v j
    ring
  rw [nearestDriftMatrix_mulVec, ← hrhs]
  linarith [hgen]

/-! ## The Euler step and its iterates -/

/-- One Euler step acts as the identity plus `τ` times the generator. -/
theorem step_mulVec_eq (n : ℕ) (τ : ℝ) (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (u : Fin (n + 1) → ℝ) (k : Fin (n + 1)) :
    (1 + τ • M).mulVec u k = u k + τ * M.mulVec u k := by
  rw [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec]
  simp

/-- The Euler step of the nearest-drift matrix is the skeleton step of
`Descent.Portability.ConvexOrderCoupling` on the embedded vector. -/
theorem gridEmbed_step (n : ℕ) (α β τ : ℝ) (v : Fin (n + 1) → ℝ) (j : ℤ)
    (hj0 : 0 ≤ j) (hjn : j ≤ (n : ℤ)) :
    gridEmbed n ((1 + τ • nearestDriftMatrix n α β).mulVec v) j
      = ConvexOrderCoupling.driftStep n α β τ (gridEmbed n v) j := by
  obtain ⟨k, hk⟩ : ∃ k : Fin (n + 1), ((k : ℕ) : ℤ) = j :=
    ⟨⟨j.toNat, by omega⟩, by
      show ((j.toNat : ℕ) : ℤ) = j
      omega⟩
  subst hk
  rw [gridEmbed_coe, step_mulVec_eq, nearestDriftMatrix_mulVec,
    ConvexOrderCoupling.driftStep, gridEmbed_coe]

/-- Grid convexity survives one Euler step of the nearest-drift matrix. -/
theorem gridEmbed_step_gridConvex (n : ℕ) (α β τ : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β) (hτ : 0 ≤ τ)
    (hshort : τ * (2 * (n : ℝ) * (α + β)) ≤ 1) (v : Fin (n + 1) → ℝ)
    (hv : ∀ j : ℤ, 1 ≤ j → j + 1 ≤ (n : ℤ) →
      0 ≤ gridEmbed n v (j - 1) - 2 * gridEmbed n v j + gridEmbed n v (j + 1))
    (j : ℤ) (hj1 : 1 ≤ j) (hjn : j + 1 ≤ (n : ℤ)) :
    0 ≤ gridEmbed n ((1 + τ • nearestDriftMatrix n α β).mulVec v) (j - 1)
      - 2 * gridEmbed n ((1 + τ • nearestDriftMatrix n α β).mulVec v) j
      + gridEmbed n ((1 + τ • nearestDriftMatrix n α β).mulVec v) (j + 1) := by
  rw [gridEmbed_step n α β τ v (j - 1) (by omega) (by omega),
    gridEmbed_step n α β τ v j (by omega) (by omega),
    gridEmbed_step n α β τ v (j + 1) (by omega) (by omega)]
  exact ConvexOrderCoupling.driftStep_gridConvex n α β τ hα hβ hτ hshort (gridEmbed n v) hv j
    hj1 hjn

/-- A matrix power acts by iterating the matrix. -/
theorem pow_mulVec_succ {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) (v : Fin N → ℝ) (m : ℕ) :
    (A ^ (m + 1)).mulVec v = A.mulVec ((A ^ m).mulVec v) := by
  rw [pow_succ']
  simp [Matrix.mulVec_mulVec]

/-- Every iterate of the Euler step of the nearest-drift matrix stays grid convex. -/
theorem gridEmbed_pow_gridConvex (n : ℕ) (α β τ : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β) (hτ : 0 ≤ τ)
    (hshort : τ * (2 * (n : ℝ) * (α + β)) ≤ 1) (v : Fin (n + 1) → ℝ)
    (hv : ∀ j : ℤ, 1 ≤ j → j + 1 ≤ (n : ℤ) →
      0 ≤ gridEmbed n v (j - 1) - 2 * gridEmbed n v j + gridEmbed n v (j + 1)) (m : ℕ) :
    ∀ j : ℤ, 1 ≤ j → j + 1 ≤ (n : ℤ) →
      0 ≤ gridEmbed n (((1 + τ • nearestDriftMatrix n α β) ^ m).mulVec v) (j - 1)
        - 2 * gridEmbed n (((1 + τ • nearestDriftMatrix n α β) ^ m).mulVec v) j
        + gridEmbed n (((1 + τ • nearestDriftMatrix n α β) ^ m).mulVec v) (j + 1) := by
  induction m with
  | zero => simpa using hv
  | succ m ih =>
    intro j hj1 hjn
    rw [pow_mulVec_succ]
    exact gridEmbed_step_gridConvex n α β τ hα hβ hτ hshort _ ih j hj1 hjn

/-- A short Euler step of an admissible generator has nonnegative entries, so it is
monotone on vectors. -/
theorem step_mulVec_mono (n : ℕ) (τ : ℝ) (hτ : 0 ≤ τ)
    (L : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (hoff : ∀ k j, j ≠ k → 0 ≤ L k j)
    (hdiag : ∀ k, 0 ≤ 1 + τ * L k k) (u w : Fin (n + 1) → ℝ) (huw : ∀ j, u j ≤ w j)
    (k : Fin (n + 1)) :
    (1 + τ • L).mulVec u k ≤ (1 + τ • L).mulVec w k := by
  have hentry : ∀ j, 0 ≤ (1 + τ • L) k j := by
    intro j
    have h1 : (1 + τ • L) k j = (if k = j then (1 : ℝ) else 0) + τ * L k j := by
      simp [Matrix.one_apply]
    rw [h1]
    by_cases h : k = j
    · rw [if_pos h, ← h]
      exact hdiag k
    · rw [if_neg h, zero_add]
      exact mul_nonneg hτ (hoff k j fun hc ↦ h hc.symm)
  show ∑ j, (1 + τ • L) k j * u j ≤ ∑ j, (1 + τ • L) k j * w j
  exact Finset.sum_le_sum fun j _ ↦ mul_le_mul_of_nonneg_left (huw j) (hentry j)

/-- **The Euler approximants are ordered.**  For a short step, every iterate of the
nearest-drift Euler step is below the corresponding iterate for any admissible generator. -/
theorem euler_iterate_le (n : ℕ) (α β τ : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β) (hτ : 0 ≤ τ)
    (hshort : τ * (2 * (n : ℝ) * (α + β)) ≤ 1)
    (L : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (hoff : ∀ k j, j ≠ k → 0 ≤ L k j)
    (hrow : ∀ k, ∑ j, L k j = 0)
    (hdrift : ∀ k : Fin (n + 1), ∑ j, L k j * (((j : ℕ) : ℝ) - ((k : ℕ) : ℝ))
      = ConvexOrderCoupling.countDrift n α β ((k : ℕ) : ℤ))
    (hdiag : ∀ k, 0 ≤ 1 + τ * L k k) (v : Fin (n + 1) → ℝ)
    (hv : ∀ j : ℤ, 1 ≤ j → j + 1 ≤ (n : ℤ) →
      0 ≤ gridEmbed n v (j - 1) - 2 * gridEmbed n v j + gridEmbed n v (j + 1)) (m : ℕ) :
    ∀ k : Fin (n + 1), ((1 + τ • nearestDriftMatrix n α β) ^ m).mulVec v k
      ≤ ((1 + τ • L) ^ m).mulVec v k := by
  induction m with
  | zero => intro k; simp
  | succ m ih =>
    intro k
    rw [pow_mulVec_succ, pow_mulVec_succ]
    have hstar : (1 + τ • nearestDriftMatrix n α β).mulVec
          (((1 + τ • nearestDriftMatrix n α β) ^ m).mulVec v) k
        ≤ (1 + τ • L).mulVec (((1 + τ • nearestDriftMatrix n α β) ^ m).mulVec v) k := by
      have hgen := nearestDriftMatrix_mulVec_le n α β hα hβ L hoff hrow hdrift
        (((1 + τ • nearestDriftMatrix n α β) ^ m).mulVec v)
        (gridEmbed_pow_gridConvex n α β τ hα hβ hτ hshort v hv m) k
      have hscaled := mul_le_mul_of_nonneg_left hgen hτ
      rw [step_mulVec_eq, step_mulVec_eq]
      linarith
    exact le_trans hstar (step_mulVec_mono n τ hτ L hoff hdiag _ _ ih k)

end

end Descent.Portability.ContinuousTurnoverSemigroup
