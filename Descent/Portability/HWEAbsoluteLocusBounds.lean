/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.HWEAbsoluteLocusLaw

assert_below Descent.Decision Descent.Program

/-!
Near balance, the total square-biased absolute locus factor is a contraction.
Its heterozygote part is bounded by 16 times the maximal displacement times the
squared displacement. This yields a summable error for arbitrary triangular rows.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.HWEAbsoluteLocusBounds

open Foundations HWEAbsoluteLocusLaw

theorem homoMass_pos (h : HardyWeinbergModel)
    (h0 : 0 < h.altFreq) (h1 : h.altFreq < 1) : 0 < homoMass h := by
  exact mul_pos (by norm_num)
    (Real.sqrt_pos.mpr (mul_pos h0 (sub_pos.mpr h1)))

theorem homoMass_square (h : HardyWeinbergModel)
    (h0 : 0 < h.altFreq) (h1 : h.altFreq < 1) :
    homoMass h ^ 2 = 1 - 4 * (h.altFreq - 1 / 2) ^ 2 := by
  rw [homoMass, mul_pow, Real.sq_sqrt (mul_pos h0 (sub_pos.mpr h1)).le]
  ring

theorem heteroMass_mul_homoMass (h : HardyWeinbergModel)
    (h0 : 0 < h.altFreq) (h1 : h.altFreq < 1) :
    heteroMass h * homoMass h = 8 * (h.altFreq - 1 / 2) ^ 2 * |h.altFreq - 1 / 2| := by
  have hs := (Real.sqrt_pos.mpr (mul_pos h0 (sub_pos.mpr h1))).ne'
  unfold heteroMass homoMass
  field_simp
  <;> ring

/-- Concrete bounds derived from the exact locus moments for displacement at most 1/8. -/
theorem near_balance_bounds (h : HardyWeinbergModel)
    (h0 : 0 < h.altFreq) (h1 : h.altFreq < 1)
    (hsmall : |h.altFreq - 1 / 2| ≤ 1 / 8) :
    1 / 2 ≤ homoMass h ∧ homoMass h + heteroMass h ≤ 1 := by
  have hr := homoMass_pos h h0 h1
  have hb := (masses_nonneg h).2
  have hs := homoMass_square h h0 h1
  have he := heteroMass_mul_homoMass h h0 h1
  have hd := sq_nonneg (h.altFreq - 1 / 2)
  have hdmax : (h.altFreq - 1 / 2) ^ 2 ≤ 1 / 64 := by
    nlinarith [sq_abs (h.altFreq - 1 / 2),
      mul_nonneg (abs_nonneg (h.altFreq - 1 / 2))
        (sub_nonneg.mpr hsmall)]
  have hlo : 1 - 3 * (h.altFreq - 1 / 2) ^ 2 ≤ homoMass h := by
    have hh : 0 ≤ (h.altFreq - 1 / 2) ^ 2 *
        (2 - 9 * (h.altFreq - 1 / 2) ^ 2) :=
      mul_nonneg hd (by linarith)
    nlinarith
  have hc : heteroMass h * homoMass h ≤ (h.altFreq - 1 / 2) ^ 2 := by
    rw [he]
    nlinarith [mul_nonneg hd (show 0 ≤ 1 - 8 * |h.altFreq - 1 / 2| by linarith)]
  constructor <;> nlinarith

/-- Uniform row displacement bounds the exceptional locus mass cubically. -/
theorem heteroMass_bound (h : HardyWeinbergModel)
    (h0 : 0 < h.altFreq) (h1 : h.altFreq < 1) (ε : ℝ)
    (hε : |h.altFreq - 1 / 2| ≤ ε) (hsmall : |h.altFreq - 1 / 2| ≤ 1 / 8) :
    heteroMass h ≤ 16 * ε * (h.altFreq - 1 / 2) ^ 2 := by
  have hlo := (near_balance_bounds h h0 h1 hsmall).1
  have hb := (masses_nonneg h).2
  have he := heteroMass_mul_homoMass h h0 h1
  have hd := sq_nonneg (h.altFreq - 1 / 2)
  nlinarith [mul_nonneg hd (sub_nonneg.mpr hε)]

end Descent.Portability.HWEAbsoluteLocusBounds
