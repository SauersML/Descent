/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.CompensatedCharacteristicKernel
import Mathlib.Analysis.SpecificLimits.Basic

assert_below Descent.Decision Descent.Program

/-!
The compensated characteristic kernel vanishes when the absolute amplitude
escapes to infinity. A quantitative inverse-amplitude bound identifies why a
heterozygosity layer can lose variance while disappearing from the weak limit.
This analytic result does not assume or establish escape for a genotype array.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.EscapingCharacteristicKernel

open scoped Topology
open Filter CompensatedCharacteristicKernel

/-- An inverse-amplitude bound derived from the exact compensated exponential identity. -/
theorem kernel_inverse_bound (t y : ℝ) (hy : y ≠ 0) :
    ‖kernel t y‖ ≤ 2 * (|y|⁻¹) ^ 2 + |t| * |y|⁻¹ := by
  have hn : |y| ^ 2 * ‖kernel t y‖ ≤ 2 + |t| * |y| := by
    calc
      _ = ‖(y : ℂ) ^ 2 * kernel t y‖ := by
        simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
      _ = ‖Complex.exp ((t * y : ℝ) * Complex.I) - 1 -
          ((t * y : ℝ) : ℂ) * Complex.I‖ := by rw [quadratic_identity]
      _ ≤ ‖Complex.exp ((t * y : ℝ) * Complex.I) - 1‖ +
          ‖((t * y : ℝ) : ℂ) * Complex.I‖ := norm_sub_le _ _
      _ ≤ (‖Complex.exp ((t * y : ℝ) * Complex.I)‖ + ‖(1 : ℂ)‖) +
          ‖((t * y : ℝ) : ℂ) * Complex.I‖ :=
        add_le_add_right (norm_sub_le _ _) _
      _ = _ := by
        simp only [Complex.norm_exp_ofReal_mul_I, norm_one, norm_mul, Complex.norm_real,
          Real.norm_eq_abs, Complex.norm_I, mul_one]
        norm_num
  have ha : |y| ≠ 0 := abs_ne_zero.mpr hy
  have hp : 0 < |y| ^ 2 := sq_pos_of_ne_zero ha
  apply (mul_le_mul_iff_right₀ hp).mp
  calc
    _ ≤ 2 + |t| * |y| := hn
    _ = _ := by field_simp

/-- Escaping absolute amplitudes make the compensated kernel tend to zero. -/
theorem kernel_tendsto_zero_of_abs_tendsto_atTop {α : Type*} {l : Filter α}
    (y : α → ℝ) (hy : Tendsto (fun a ↦ |y a|) l atTop) (t : ℝ) :
    Tendsto (fun a ↦ kernel t (y a)) l (𝓝 0) := by
  have hi := tendsto_inv_atTop_zero.comp hy
  have hb : Tendsto (fun a ↦ 2 * (|y a|⁻¹) ^ 2 + |t| * |y a|⁻¹) l (𝓝 0) := by
    convert ((hi.pow 2).const_mul 2).add (hi.const_mul |t|) using 1
    norm_num
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall (fun a ↦ norm_nonneg _)) ?_ hb
  filter_upwards [hy.eventually (eventually_gt_atTop (0 : ℝ))] with a ha
  exact kernel_inverse_bound t (y a) (abs_pos.mp ha)

end Descent.Portability.EscapingCharacteristicKernel
