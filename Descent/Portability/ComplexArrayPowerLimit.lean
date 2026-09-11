/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.SmallRealProduct
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.Calculus.DSlope

assert_below Descent.Decision Descent.Program

/-!
For arbitrary diverging natural row sizes, convergence of N times (phi-1)
implies convergence of phi^N to the exponential of that limit. The proof derives
phi tending to one and uses the derivative of log at one, without selecting a
subsequence or assuming a uniform logarithm expansion.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.ComplexArrayPowerLimit

open scoped Topology
open Filter

/-- The logarithmic coordinate has derivative one at the origin. -/
theorem log_derivative : HasDerivAt (fun z : ℂ ↦ Complex.log (1 + z)) 1 0 := by
  simpa using ((hasDerivAt_id (0 : ℂ)).const_add 1).clog (by simp)

/-- An exact slope factorization, valid even when the increment is zero. -/
theorem log_slope_identity (z : ℂ) :
    z * dslope (fun w : ℂ ↦ Complex.log (1 + w)) 0 z = Complex.log (1 + z) := by
  simpa only [sub_zero, smul_eq_mul, add_zero, Complex.log_one] using
    sub_smul_dslope (fun w : ℂ ↦ Complex.log (1 + w)) 0 z

/-- The triangular-array characteristic power limit for any diverging block-count sequence. -/
theorem power_limit (N : ℕ → ℕ) (hN : Tendsto (fun m ↦ (N m : ℝ)) atTop atTop)
    (φ : ℕ → ℂ) (ell : ℂ)
    (hgen : Tendsto (fun m ↦ (N m : ℂ) * (φ m - 1)) atTop (𝓝 ell)) :
    Tendsto (fun m ↦ φ m ^ N m) atTop (𝓝 (Complex.exp ell)) := by
  have hinv : Tendsto (fun m ↦ (N m : ℂ)⁻¹) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Complex.ofReal_inv, Complex.ofReal_natCast,
      Complex.ofReal_zero] using
      (tendsto_inv_atTop_zero.comp hN).ofReal
  have hd : Tendsto (fun m ↦ φ m - 1) atTop (𝓝 0) := by
    have hh := hinv.mul hgen
    rw [zero_mul] at hh
    apply hh.congr'
    filter_upwards [hN.eventually (eventually_gt_atTop (0 : ℝ))] with m hm
    have hn : (N m : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hm)
    exact inv_mul_cancel_left₀ hn _
  have hs : Tendsto (fun m ↦ dslope (fun w : ℂ ↦ Complex.log (1 + w)) 0 (φ m - 1))
      atTop (𝓝 1) := by
    simpa only [dslope_same, log_derivative.deriv] using
      (continuousAt_dslope_same.mpr log_derivative.differentiableAt).tendsto.comp hd
  have hl : Tendsto (fun m ↦ (N m : ℂ) * Complex.log (φ m)) atTop (𝓝 ell) := by
    have hh := hgen.mul hs
    simpa only [mul_assoc, log_slope_identity, add_sub_cancel, mul_one] using hh
  have he := Complex.continuous_exp.continuousAt.tendsto.comp hl
  have hp : Tendsto φ atTop (𝓝 1) := by simpa using hd.add_const 1
  apply he.congr'
  filter_upwards [hp.eventually (isOpen_ne.mem_nhds (by norm_num : (1 : ℂ) ≠ 0))] with m hm
  dsimp only [Function.comp_def]
  rw [Complex.exp_nat_mul, Complex.exp_log hm]

end Descent.Portability.ComplexArrayPowerLimit
