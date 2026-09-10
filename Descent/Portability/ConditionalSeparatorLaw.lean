/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.ExactMetricEvaluation
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Exp

assert_below Descent.Decision Descent.Program

/-!
Conditional separator attenuation for a finite joint probability law. A single
conditioning on the complement makes all separator coordinates independent.
Minorization then bounds each conditional phase mean, and only these genuinely
independent conditional means are multiplied. The joint law is constructed and
normalized below; graph factorization into this representation remains explicit.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.ConditionalSeparatorLaw

variable {X Y D : Type*} [Fintype X] [Fintype Y] [Fintype D] [DecidableEq D]

/-- Complex phase mean under an actual finite probability law. -/
noncomputable def phaseMean (p : FiniteReportLaw X) (z : X → ℂ) : ℂ :=
  ∑ x, (p.mass x : ℂ) * z x

/-- A subprobability weighted sum of unit phases has norm at most its total mass. -/
theorem norm_weighted_phase (w : X → ℝ) (hw : ∀ x, 0 ≤ w x)
    (z : X → ℂ) (hz : ∀ x, ‖z x‖ ≤ 1) :
    ‖∑ x, (w x : ℂ) * z x‖ ≤ ∑ x, w x := by
  calc
    _ ≤ ∑ x, ‖(w x : ℂ) * z x‖ := norm_sum_le _ _
    _ ≤ ∑ x, w x := Finset.sum_le_sum (fun x _ ↦ by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw x)]
      exact mul_le_of_le_one_right (hw x) (hz x))

theorem phaseMean_norm_le_one (p : FiniteReportLaw X) (z : X → ℂ)
    (hz : ∀ x, ‖z x‖ ≤ 1) : ‖phaseMean p z‖ ≤ 1 := by
  simpa [phaseMean, p.mass_sum] using norm_weighted_phase p.mass p.mass_nonneg z hz

/-- Minorization yields contraction even at mixing weight zero or one. -/
theorem phaseMean_norm_minorization (p ν : FiniteReportLaw X) (η : ℝ)
    (hη : 0 ≤ η) (hminor : ∀ x, η * ν.mass x ≤ p.mass x)
    (z : X → ℂ) (hz : ∀ x, ‖z x‖ ≤ 1) :
    ‖phaseMean p z‖ ≤ 1 - η * (1 - ‖phaseMean ν z‖) := by
  have hres : ‖∑ x, ((p.mass x - η * ν.mass x : ℝ) : ℂ) * z x‖ ≤ 1 - η := by
    have h := norm_weighted_phase (fun x ↦ p.mass x - η * ν.mass x)
      (fun x ↦ sub_nonneg.mpr (hminor x)) z hz
    simpa [Finset.sum_sub_distrib, ← Finset.mul_sum, p.mass_sum, ν.mass_sum] using h
  have heq : phaseMean p z = (η : ℂ) * phaseMean ν z +
      ∑ x, ((p.mass x - η * ν.mass x : ℝ) : ℂ) * z x := by
    simp only [phaseMean, Finset.mul_sum, ← Finset.sum_add_distrib,
      Complex.ofReal_sub, Complex.ofReal_mul]
    congr 1
    funext x
    ring
  rw [heq]
  calc
    _ ≤ ‖(η : ℂ) * phaseMean ν z‖ +
        ‖∑ x, ((p.mass x - η * ν.mass x : ℝ) : ℂ) * z x‖ := norm_add_le _ _
    _ ≤ η * ‖phaseMean ν z‖ + (1 - η) := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hη]
      exact add_le_add_left hres _
    _ = _ := by ring

/-- Complete joint law: complement first, conditionally independent separator second. -/
noncomputable def separatorLaw (q : FiniteReportLaw Y)
    (k : Y → D → FiniteReportLaw X) : FiniteReportLaw (Y × (D → X)) where
  mass yx := q.mass yx.1 * ∏ i, (k yx.1 i).mass (yx.2 i)
  mass_nonneg yx := mul_nonneg (q.mass_nonneg _) (Finset.prod_nonneg (fun i _ ↦
    (k yx.1 i).mass_nonneg _))
  mass_sum := by
    rw [Fintype.sum_prod_type]
    simp only [← Finset.mul_sum, ← Fintype.prod_sum]
    simp only [FiniteReportLaw.mass_sum, Finset.prod_const_one, mul_one]

/-- The factorization is proved from the complete law, not from marginal bounds. -/
theorem separator_phase_identity (q : FiniteReportLaw Y)
    (k : Y → D → FiniteReportLaw X) (u : Y → ℂ) (z : D → X → ℂ) :
    phaseMean (separatorLaw q k) (fun yx ↦ u yx.1 * ∏ i, z i (yx.2 i)) =
      ∑ y, (q.mass y : ℂ) * u y * ∏ i, phaseMean (k y i) (z i) := by
  unfold phaseMean separatorLaw
  simp only [Fintype.sum_prod_type, Complex.ofReal_mul, Complex.ofReal_prod]
  apply Finset.sum_congr rfl
  intro y _
  dsimp only
  rw [Fintype.prod_sum]
  simp only [Finset.mul_sum, Finset.prod_mul_distrib]
  apply Finset.sum_congr rfl
  intro x _
  ring

/-- Whole-law attenuation, retaining arbitrary dependence through the complement. -/
theorem separator_phase_bound (q : FiniteReportLaw Y)
    (k : Y → D → FiniteReportLaw X) (ν : D → FiniteReportLaw X)
    (η : D → ℝ) (hη : ∀ i, 0 ≤ η i)
    (hminor : ∀ y i x, η i * (ν i).mass x ≤ (k y i).mass x)
    (u : Y → ℂ) (hu : ∀ y, ‖u y‖ ≤ 1)
    (z : D → X → ℂ) (hz : ∀ i x, ‖z i x‖ ≤ 1)
    (hηone : ∀ i, η i ≤ 1) :
    ‖phaseMean (separatorLaw q k) (fun yx ↦ u yx.1 * ∏ i, z i (yx.2 i))‖ ≤
      ∏ i, (1 - η i * (1 - ‖phaseMean (ν i) (z i)‖)) := by
  let a := fun i ↦ 1 - η i * (1 - ‖phaseMean (ν i) (z i)‖)
  have ha : ∀ i, 0 ≤ a i := by
    intro i
    dsimp [a]
    nlinarith [norm_nonneg (phaseMean (ν i) (z i)), hη i, hηone i]
  have hk : ∀ y, ‖∏ i, phaseMean (k y i) (z i)‖ ≤ ∏ i, a i := by
    intro y
    rw [norm_prod]
    exact Finset.prod_le_prod (fun i _ ↦ norm_nonneg _)
      (fun i _ ↦ phaseMean_norm_minorization (k y i) (ν i) (η i) (hη i)
        (hminor y i) (z i) (hz i))
  rw [separator_phase_identity]
  calc
    _ ≤ ∑ y, ‖(q.mass y : ℂ) * u y * ∏ i, phaseMean (k y i) (z i)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ y, q.mass y * ∏ i, a i := by
      apply Finset.sum_le_sum
      intro y _
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (q.mass_nonneg y)]
      exact mul_le_mul (mul_le_of_le_one_right (q.mass_nonneg y) (hu y))
        (hk y) (norm_nonneg _) (q.mass_nonneg y)
    _ = _ := by rw [← Finset.sum_mul, q.mass_sum, one_mul]

/-- The product contraction implies the stated exponential separator bound. -/
theorem separator_phase_exp_bound (q : FiniteReportLaw Y)
    (k : Y → D → FiniteReportLaw X) (ν : D → FiniteReportLaw X)
    (η : D → ℝ) (hη : ∀ i, 0 ≤ η i) (hηone : ∀ i, η i ≤ 1)
    (hminor : ∀ y i x, η i * (ν i).mass x ≤ (k y i).mass x)
    (u : Y → ℂ) (hu : ∀ y, ‖u y‖ ≤ 1)
    (z : D → X → ℂ) (hz : ∀ i x, ‖z i x‖ ≤ 1) :
    ‖phaseMean (separatorLaw q k) (fun yx ↦ u yx.1 * ∏ i, z i (yx.2 i))‖ ≤
      Real.exp (-∑ i, η i * (1 - ‖phaseMean (ν i) (z i)‖)) := by
  apply (separator_phase_bound q k ν η hη hminor u hu z hz hηone).trans
  calc
    _ ≤ ∏ i, Real.exp (-(η i * (1 - ‖phaseMean (ν i) (z i)‖))) := by
      apply Finset.prod_le_prod
      · intro i _
        nlinarith [norm_nonneg (phaseMean (ν i) (z i)), hη i, hηone i]
      · intro i _
        exact Real.one_sub_le_exp_neg _
    _ = _ := by rw [← Real.exp_sum, Finset.sum_neg_distrib]

/-- Normalizing constant for an actual finite Gibbs tilt of a reference law. -/
noncomputable def gibbsNormalizer (ν : FiniteReportLaw X) (U : X → ℝ) : ℝ :=
  ∑ x, ν.mass x * Real.exp (U x)

theorem gibbsNormalizer_pos (ν : FiniteReportLaw X) (U : X → ℝ) :
    0 < gibbsNormalizer ν U := by
  have hex : ∃ x ∈ Finset.univ, 0 < ν.mass x := by
    apply (Finset.sum_pos_iff_of_nonneg (fun x _ ↦ ν.mass_nonneg x)).mp
    rw [ν.mass_sum]
    norm_num
  obtain ⟨x, hx, hpos⟩ := hex
  apply (Finset.sum_pos_iff_of_nonneg
    (fun y _ ↦ mul_nonneg (ν.mass_nonneg y) (Real.exp_pos _).le)).mpr
  exact ⟨x, hx, mul_pos hpos (Real.exp_pos _)⟩

/-- The tilted conditional distribution is normalized, including reference zeros. -/
noncomputable def gibbsLaw (ν : FiniteReportLaw X) (U : X → ℝ) : FiniteReportLaw X where
  mass x := ν.mass x * Real.exp (U x) / gibbsNormalizer ν U
  mass_nonneg x := div_nonneg (mul_nonneg (ν.mass_nonneg x) (Real.exp_pos _).le)
    (gibbsNormalizer_pos ν U).le
  mass_sum := by
    rw [← Finset.sum_div]
    exact div_self (gibbsNormalizer_pos ν U).ne'

/-- Uniform oscillation control proves Gibbs minorization from its actual probabilities. -/
theorem gibbsLaw_minorization (ν : FiniteReportLaw X) (U : X → ℝ) (R : ℝ)
    (hosc : ∀ x y, U y - U x ≤ R) (x : X) :
    Real.exp (-R) * ν.mass x ≤ (gibbsLaw ν U).mass x := by
  have hZ : gibbsNormalizer ν U ≤ Real.exp (R + U x) := by
    calc
      _ ≤ ∑ y, ν.mass y * Real.exp (R + U x) := by
        apply Finset.sum_le_sum
        intro y _
        exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith [hosc x y]))
          (ν.mass_nonneg y)
      _ = _ := by rw [← Finset.sum_mul, ν.mass_sum, one_mul]
  change _ ≤ ν.mass x * Real.exp (U x) / gibbsNormalizer ν U
  apply (le_div_iff₀ (gibbsNormalizer_pos ν U)).mpr
  calc
    _ ≤ (Real.exp (-R) * ν.mass x) * Real.exp (R + U x) :=
      mul_le_mul_of_nonneg_left hZ (mul_nonneg (Real.exp_pos _).le (ν.mass_nonneg x))
    _ = ν.mass x * Real.exp (U x) := by
      rw [mul_assoc, mul_left_comm (Real.exp (-R)), ← Real.exp_add]
      congr 2
      ring

/-- A specified Gibbs family discharges the conditional minorization hypothesis. -/
theorem gibbs_separator_exp_bound (q : FiniteReportLaw Y)
    (ν : D → FiniteReportLaw X) (U : Y → D → X → ℝ) (R : D → ℝ)
    (hR : ∀ i, 0 ≤ R i) (hosc : ∀ y i x x', U y i x' - U y i x ≤ R i)
    (u : Y → ℂ) (hu : ∀ y, ‖u y‖ ≤ 1)
    (z : D → X → ℂ) (hz : ∀ i x, ‖z i x‖ ≤ 1) :
    ‖phaseMean (separatorLaw q (fun y i ↦ gibbsLaw (ν i) (U y i)))
      (fun yx ↦ u yx.1 * ∏ i, z i (yx.2 i))‖ ≤
      Real.exp (-∑ i, Real.exp (-R i) * (1 - ‖phaseMean (ν i) (z i)‖)) := by
  apply separator_phase_exp_bound q (fun y i ↦ gibbsLaw (ν i) (U y i)) ν
    (fun i ↦ Real.exp (-R i)) (fun i ↦ (Real.exp_pos _).le)
    (fun i ↦ Real.exp_le_one_iff.mpr (neg_nonpos.mpr (hR i)))
  · exact fun y i x ↦ gibbsLaw_minorization (ν i) (U y i) (R i) (hosc y i) x
  · exact hu
  · exact hz

end Descent.Portability.ConditionalSeparatorLaw
