/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.GraphCoalescent.HiddenClockExample
import Descent.Pangenome.GraphCoalescent.ShortTimeConnectionLaw
import Descent.Pangenome.GraphCoalescent.TwoComponentSurvival
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

assert_below Descent.PopGen Descent.Spectral Descent.Blindness Descent.Conditionals
assert_below Descent.Portability Descent.Decision Descent.Program

/-!
# The mean connection time as the integral of the killed survival function

`TwoComponentSurvival` builds the survival function `S_{a,b}(t) = α e^{tQ} 𝟙` of the two-component
load chain from the killed generator `loadGenerator`, and its header leaves the identification of
the mean connection time with the integral of the survival function unformalized. This module
proves that identification for positive loads.

## A Metzler exponential

`exp_smul_apply_nonneg`: if the off-diagonal entries of a matrix `Q` are nonnegative, every entry
of `e^{tQ}` is nonnegative for `t ≥ 0`. The proof shifts `Q` by a multiple of the identity to a
nonnegative matrix `P`, splits `e^{tQ} = e^{tP} e^{-tc}` (`exp_smul_one_apply`), and reads the
nonnegative series of `e^{tP}` (`pow_apply_nonneg`).

## The killed load chain

* Positive loads form a closed class: a nonzero rate never lowers a load to zero
  (`loadGenerator_eq_zero_of_not_pos`, `pow_loadGenerator_eq_zero_of_not_pos`), so the chain from
  positive loads never visits the grid's zero loads (`exp_smul_loadGenerator_eq_zero_of_not_pos`).
  The off-diagonal rates are nonnegative (`loadGenerator_nonneg_of_ne`), so the survival function
  is nonnegative (`gridSurvival_nonneg`).
* **Decay.** The forward equation `S_x' = Σ_z e^{tQ}(x, z) (Q𝟙)(z)`
  (`hasDerivAt_gridSurvival_forward`) kills at rate `ab ≥ 1` at every positive loads, so
  `S_x(t) ≤ e^{-t}` (`gridSurvival_le_exp_neg`):
  the survival function vanishes at infinity (`tendsto_gridSurvival_atTop`) and is integrable on
  `(0, ∞)` (`integrableOn_gridSurvival`).
* **The integrated backward equation.** With `M_y = ∫_0^∞ S_y`, `Σ_y Q(x, y) M_y = -1` at positive
  loads (`sum_loadGenerator_mul_integral`): `M` solves `(-Q) M = 𝟙` on the closed class, the
  phase-type mean `α (-Q)^{-1} 𝟙` in solved form.
* **The first-step mean.** `loadMean a b` is the first-step mean of the load chain: loads `(a, b)`
  are held for a time of rate `C(a,2) + C(b,2) + ab` and then move to `(a - 1, b)` or `(a, b - 1)`
  or connect. By induction on the total load, the integral of the survival function is that mean
  (`integral_gridSurvival_eq_loadMean`, `integral_survival_eq_loadMean`), and the mean solves the
  generator equation (`sum_loadGenerator_mul_loadMean`). The grid does not enter the mean.

## Example (A4)

Loads `(2, 1)`: `loadMean_one_one`, `loadMean_two_one`, so `∫_0^∞ S_{2,1} = 2/3`
(`integral_survival_two_one`). It is the integral of the example's closed-form survival function
`½e^{-3t} + ½e^{-t}` of `HiddenClockExample`
(`integral_survival_two_one_eq_integral_exampleSurvival`), and the three clocks `2/3`, `1` and
`4/3` differ (`three_clocks_differ_survival`, from
`HiddenClockExample.three_clocks_differ`).

Not yet here: the identification of `loadMean` with the labeled first-step mean
`VisibleIntensityClock.meanConnectionTime` at a coalescent state whose report has two components
with those loads.

Scope, as in `TwoComponentSurvival`: the survival function is `α e^{tQ} 𝟙` of the killed generator;
the continuous-time chain is not constructed as a process, and that the integral of its survival
function is the mean of its absorption time is the definition here.

## Empirical status

None. The bodies here are a finite matrix exponential, its improper integral and a finite
recursion in two natural numbers, so no measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Pangenome.GraphCoalescent.KilledSurvivalMean

open Coalescent Finset MeasureTheory Filter Topology
open Descent.Pangenome.GraphCoalescent.TwoComponentSurvival
open Descent.Pangenome.GraphCoalescent.MinimalRefinement
open Descent.Pangenome.GraphCoalescent.ShortTimeConnectionLaw

noncomputable section

/-! ### The exponential of a Metzler matrix -/

/-- The entries of the powers of a nonnegative matrix are nonnegative. -/
theorem pow_apply_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι] {P : Matrix ι ι ℝ}
    (hP : ∀ x y, 0 ≤ P x y) (k : ℕ) (x y : ι) : 0 ≤ (P ^ k) x y := by
  induction k generalizing x with
  | zero =>
    rw [pow_zero, Matrix.one_apply]
    split_ifs <;> norm_num
  | succ k ih =>
    rw [pow_succ', Matrix.mul_apply]
    exact sum_nonneg fun z _ ↦ mul_nonneg (hP x z) (ih z)

/-- The exponential of a scalar matrix: `e^{u I} = e^u I`. -/
theorem exp_smul_one_apply {ι : Type*} [Fintype ι] [DecidableEq ι] (u : ℝ) (x y : ι) :
    NormedSpace.exp ℝ (u • (1 : Matrix ι ι ℝ)) x y = Real.exp u * (1 : Matrix ι ι ℝ) x y := by
  rw [exp_smul_apply]
  simp only [one_pow]
  rw [tsum_mul_right, Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]

/-- **The exponential of a Metzler matrix is nonnegative.** If every off-diagonal entry of `Q` is
nonnegative, every entry of `e^{tQ}` is nonnegative for `t ≥ 0`. -/
theorem exp_smul_apply_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι] {Q : Matrix ι ι ℝ}
    (hoff : ∀ x y, x ≠ y → 0 ≤ Q x y) {t : ℝ} (ht : 0 ≤ t) (x y : ι) :
    0 ≤ NormedSpace.exp ℝ (t • Q) x y := by
  have hP : ∀ z w, 0 ≤ (Q + (∑ u, ∑ v, |Q u v|) • (1 : Matrix ι ι ℝ)) z w := by
    intro z w
    rw [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    by_cases hzw : z = w
    · subst hzw
      rw [if_pos rfl, mul_one]
      have hrow : |Q z z| ≤ ∑ v, |Q z v| :=
        single_le_sum (fun v _ ↦ abs_nonneg (Q z v)) (mem_univ z)
      have htotal : ∑ v, |Q z v| ≤ ∑ u, ∑ v, |Q u v| :=
        single_le_sum (fun u _ ↦ sum_nonneg fun v _ ↦ abs_nonneg (Q u v)) (mem_univ z)
      linarith [neg_abs_le (Q z z)]
    · rw [if_neg hzw, mul_zero, add_zero]
      exact hoff z w hzw
  have hcommute : Commute (t • (Q + (∑ u, ∑ v, |Q u v|) • (1 : Matrix ι ι ℝ)))
      ((-(t * ∑ u, ∑ v, |Q u v|)) • (1 : Matrix ι ι ℝ)) :=
    (Commute.one_right _).smul_right _
  have hsplit : t • Q = t • (Q + (∑ u, ∑ v, |Q u v|) • (1 : Matrix ι ι ℝ)) +
      (-(t * ∑ u, ∑ v, |Q u v|)) • (1 : Matrix ι ι ℝ) := by
    rw [smul_add, smul_smul, neg_smul, add_neg_cancel_right]
  rw [hsplit, Matrix.exp_add_of_commute (𝕂 := ℝ) _ _ hcommute, Matrix.mul_apply]
  refine sum_nonneg fun z _ ↦ mul_nonneg ?_ ?_
  · rw [exp_smul_apply]
    exact tsum_nonneg fun k ↦
      mul_nonneg (div_nonneg (pow_nonneg ht k) (Nat.cast_nonneg _)) (pow_apply_nonneg hP k x z)
  · rw [exp_smul_one_apply, Matrix.one_apply]
    split_ifs <;> positivity

/-! ### The closed class of positive loads -/

/-- **The killed generator never lowers a load to zero.** From loads that are both positive, every
nonzero rate leads to loads that are both positive. -/
theorem loadGenerator_eq_zero_of_not_pos {A B : ℕ} {x y : Fin (A + 1) × Fin (B + 1)}
    (hx : 1 ≤ (x.1 : ℕ) ∧ 1 ≤ (x.2 : ℕ)) (hy : ¬(1 ≤ (y.1 : ℕ) ∧ 1 ≤ (y.2 : ℕ))) :
    loadGenerator A B x y = 0 := by
  have hfirst : (if y = lowerFirst x then (Nat.choose x.1 2 : ℝ) else 0) = 0 := by
    split_ifs with h
    · have h1 : (y.1 : ℕ) = (x.1 : ℕ) - 1 :=
        congrArg (fun z : Fin (A + 1) × Fin (B + 1) ↦ (z.1 : ℕ)) h
      have h2 : (y.2 : ℕ) = (x.2 : ℕ) :=
        congrArg (fun z : Fin (A + 1) × Fin (B + 1) ↦ (z.2 : ℕ)) h
      have hone : (x.1 : ℕ) = 1 := by omega
      rw [hone]
      norm_num [Nat.choose]
    · rfl
  have hsecond : (if y = lowerSecond x then (Nat.choose x.2 2 : ℝ) else 0) = 0 := by
    split_ifs with h
    · have h1 : (y.1 : ℕ) = (x.1 : ℕ) :=
        congrArg (fun z : Fin (A + 1) × Fin (B + 1) ↦ (z.1 : ℕ)) h
      have h2 : (y.2 : ℕ) = (x.2 : ℕ) - 1 :=
        congrArg (fun z : Fin (A + 1) × Fin (B + 1) ↦ (z.2 : ℕ)) h
      have hone : (x.2 : ℕ) = 1 := by omega
      rw [hone]
      norm_num [Nat.choose]
    · rfl
  have hdiag : ¬y = x := fun hyx ↦ hy (hyx ▸ hx)
  simp only [loadGenerator, hfirst, hsecond, if_neg hdiag, sub_zero, add_zero]

/-- The powers of the killed generator keep positive loads positive. -/
theorem pow_loadGenerator_eq_zero_of_not_pos {A B : ℕ} (k : ℕ)
    {x y : Fin (A + 1) × Fin (B + 1)} (hx : 1 ≤ (x.1 : ℕ) ∧ 1 ≤ (x.2 : ℕ))
    (hy : ¬(1 ≤ (y.1 : ℕ) ∧ 1 ≤ (y.2 : ℕ))) :
    (loadGenerator A B ^ k) x y = 0 := by
  induction k generalizing x with
  | zero =>
    have hxy : x ≠ y := fun h ↦ hy (h ▸ hx)
    rw [pow_zero, Matrix.one_apply, if_neg hxy]
  | succ k ih =>
    rw [pow_succ', Matrix.mul_apply]
    refine sum_eq_zero fun z _ ↦ ?_
    by_cases hz : 1 ≤ (z.1 : ℕ) ∧ 1 ≤ (z.2 : ℕ)
    · rw [ih hz, mul_zero]
    · rw [loadGenerator_eq_zero_of_not_pos hx hz, zero_mul]

/-- **The chain started at positive loads stays at positive loads.** -/
theorem exp_smul_loadGenerator_eq_zero_of_not_pos {A B : ℕ} (t : ℝ)
    {x y : Fin (A + 1) × Fin (B + 1)} (hx : 1 ≤ (x.1 : ℕ) ∧ 1 ≤ (x.2 : ℕ))
    (hy : ¬(1 ≤ (y.1 : ℕ) ∧ 1 ≤ (y.2 : ℕ))) :
    NormedSpace.exp ℝ (t • loadGenerator A B) x y = 0 := by
  rw [exp_smul_apply]
  simp only [fun k ↦ pow_loadGenerator_eq_zero_of_not_pos k hx hy, mul_zero, tsum_zero]

/-- The off-diagonal rates of the killed generator are nonnegative. -/
theorem loadGenerator_nonneg_of_ne {A B : ℕ} {x y : Fin (A + 1) × Fin (B + 1)} (hxy : x ≠ y) :
    0 ≤ loadGenerator A B x y := by
  simp only [loadGenerator, if_neg (Ne.symm hxy), sub_zero]
  exact add_nonneg (by split_ifs <;> positivity) (by split_ifs <;> positivity)

/-- The survival function is nonnegative. -/
theorem gridSurvival_nonneg (A B : ℕ) (x : Fin (A + 1) × Fin (B + 1)) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ gridSurvival A B x t :=
  sum_nonneg fun y _ ↦ exp_smul_apply_nonneg (fun _ _ ↦ loadGenerator_nonneg_of_ne) ht x y

/-! ### Decay of the survival function -/

/-- **The forward equation for the survival function**: `d/dt S_x(t) = Σ_z e^{tQ}(x, z) (Q𝟙)(z)`,
the killing at the current loads. -/
theorem hasDerivAt_gridSurvival_forward (A B : ℕ) (x : Fin (A + 1) × Fin (B + 1)) (t : ℝ) :
    HasDerivAt (gridSurvival A B x)
      (∑ z, NormedSpace.exp ℝ (t • loadGenerator A B) x z *
        -(((z.1 : ℕ) : ℝ) * (z.2 : ℕ))) t := by
  let rowSum : Matrix (Fin (A + 1) × Fin (B + 1)) (Fin (A + 1) × Fin (B + 1)) ℝ →ₗ[ℝ] ℝ :=
    { toFun := fun N ↦ ∑ y, N x y
      map_add' := fun N N' ↦ by simp only [Matrix.add_apply, sum_add_distrib]
      map_smul' := fun c N ↦ by
        simp only [Matrix.smul_apply, smul_eq_mul, RingHom.id_apply, mul_sum] }
  have hcont : Continuous rowSum := LinearMap.continuous_of_finiteDimensional rowSum
  have key : HasDerivAt (fun u : ℝ ↦ rowSum (NormedSpace.exp ℝ (u • loadGenerator A B)))
      (rowSum (NormedSpace.exp ℝ (t • loadGenerator A B) * loadGenerator A B)) t := by
    open scoped Matrix.Norms.Operator in
    exact (⟨rowSum, hcont⟩ : Matrix _ _ ℝ →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt (x := t)
      (hasDerivAt_exp_smul_const (𝕂 := ℝ) (loadGenerator A B) t)
  have hvalue : rowSum (NormedSpace.exp ℝ (t • loadGenerator A B) * loadGenerator A B) =
      ∑ z, NormedSpace.exp ℝ (t • loadGenerator A B) x z * -(((z.1 : ℕ) : ℝ) * (z.2 : ℕ)) := by
    show ∑ y, (NormedSpace.exp ℝ (t • loadGenerator A B) * loadGenerator A B) x y = _
    simp only [Matrix.mul_apply]
    rw [sum_comm]
    refine sum_congr rfl fun z _ ↦ ?_
    rw [← mul_sum, sum_loadGenerator]
  rw [hvalue] at key
  exact key

/-- **Positive loads are killed at rate at least one**: the survival function decays at least like
`e^{-t}`. -/
theorem gridSurvival_le_exp_neg {A B : ℕ} {x : Fin (A + 1) × Fin (B + 1)}
    (hx : 1 ≤ (x.1 : ℕ) ∧ 1 ≤ (x.2 : ℕ)) {t : ℝ} (ht : 0 ≤ t) :
    gridSurvival A B x t ≤ Real.exp (-t) := by
  have hderiv : ∀ u, HasDerivAt (fun u ↦ Real.exp u * gridSurvival A B x u)
      (Real.exp u * gridSurvival A B x u + Real.exp u *
        ∑ z, NormedSpace.exp ℝ (u • loadGenerator A B) x z * -(((z.1 : ℕ) : ℝ) * (z.2 : ℕ))) u :=
    fun u ↦ (Real.hasDerivAt_exp u).mul (hasDerivAt_gridSurvival_forward A B x u)
  have hkill : ∀ u, 0 ≤ u →
      ∑ z, NormedSpace.exp ℝ (u • loadGenerator A B) x z * -(((z.1 : ℕ) : ℝ) * (z.2 : ℕ)) ≤
        -gridSurvival A B x u := by
    intro u hu
    rw [gridSurvival, ← sum_neg_distrib]
    refine sum_le_sum fun z _ ↦ ?_
    by_cases hz : 1 ≤ (z.1 : ℕ) ∧ 1 ≤ (z.2 : ℕ)
    · have hprod : (1 : ℝ) ≤ ((z.1 : ℕ) : ℝ) * (z.2 : ℕ) := by
        have hnat := Nat.mul_le_mul hz.1 hz.2
        exact_mod_cast hnat
      have hnonneg := exp_smul_apply_nonneg (fun _ _ ↦ loadGenerator_nonneg_of_ne) hu x z
      nlinarith
    · rw [exp_smul_loadGenerator_eq_zero_of_not_pos u hx hz]
      simp
  have hanti : AntitoneOn (fun u ↦ Real.exp u * gridSurvival A B x u) (Set.Ici 0) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ici 0)
      (fun u _ ↦ (hderiv u).continuousAt.continuousWithinAt)
      (fun u _ ↦ (hderiv u).differentiableAt.differentiableWithinAt) fun u hu ↦ ?_
    rw [interior_Ici] at hu
    rw [(hderiv u).deriv]
    have hbound := hkill u (le_of_lt hu)
    have hexp := Real.exp_pos u
    nlinarith
  have hle := hanti (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr ht) ht
  simp only [Real.exp_zero, gridSurvival_zero, mul_one] at hle
  calc gridSurvival A B x t = Real.exp (-t) * (Real.exp t * gridSurvival A B x t) := by
        rw [← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]
    _ ≤ Real.exp (-t) * 1 := mul_le_mul_of_nonneg_left hle (Real.exp_pos _).le
    _ = Real.exp (-t) := mul_one _

/-- **The survival function vanishes at infinity** from positive loads. -/
theorem tendsto_gridSurvival_atTop {A B : ℕ} {x : Fin (A + 1) × Fin (B + 1)}
    (hx : 1 ≤ (x.1 : ℕ) ∧ 1 ≤ (x.2 : ℕ)) :
    Tendsto (gridSurvival A B x) atTop (𝓝 0) :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    Real.tendsto_exp_neg_atTop_nhds_zero
    (eventually_atTop.mpr ⟨0, fun _ ht ↦ gridSurvival_nonneg A B x ht⟩)
    (eventually_atTop.mpr ⟨0, fun _ ht ↦ gridSurvival_le_exp_neg hx ht⟩)

/-- The survival function is continuous. -/
theorem continuous_gridSurvival (A B : ℕ) (x : Fin (A + 1) × Fin (B + 1)) :
    Continuous (gridSurvival A B x) :=
  continuous_iff_continuousAt.mpr fun t ↦ (hasDerivAt_gridSurvival A B x t).continuousAt

/-- **The survival function is integrable on `(0, ∞)`** from positive loads. -/
theorem integrableOn_gridSurvival {A B : ℕ} {x : Fin (A + 1) × Fin (B + 1)}
    (hx : 1 ≤ (x.1 : ℕ) ∧ 1 ≤ (x.2 : ℕ)) :
    IntegrableOn (gridSurvival A B x) (Set.Ioi 0) := by
  have hexp : IntegrableOn (fun t : ℝ ↦ Real.exp (-t)) (Set.Ioi 0) := by
    simpa using exp_neg_integrableOn_Ioi 0 one_pos
  refine Integrable.mono' hexp (continuous_gridSurvival A B x).aestronglyMeasurable ?_
  refine ae_restrict_of_forall_mem measurableSet_Ioi fun t ht ↦ ?_
  rw [Real.norm_eq_abs, abs_of_nonneg (gridSurvival_nonneg A B x (le_of_lt ht))]
  exact gridSurvival_le_exp_neg hx (le_of_lt ht)

/-! ### The integrated backward equation -/

/-- **The integrated backward equation**: `Σ_y Q(x, y) ∫_0^∞ S_y = -1` at positive loads, the
phase-type mean `(-Q) M = 𝟙` in solved form. -/
theorem sum_loadGenerator_mul_integral {A B : ℕ} {x : Fin (A + 1) × Fin (B + 1)}
    (hx : 1 ≤ (x.1 : ℕ) ∧ 1 ≤ (x.2 : ℕ)) :
    ∑ y, loadGenerator A B x y * ∫ t in Set.Ioi 0, gridSurvival A B y t = -1 := by
  have hftc : ∀ T : ℝ, ∑ y, loadGenerator A B x y * ∫ t in (0 : ℝ)..T, gridSurvival A B y t =
      gridSurvival A B x T - 1 := by
    intro T
    rw [← gridSurvival_zero A B x, ← intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t _ ↦ hasDerivAt_gridSurvival A B x t)
      ((continuous_finset_sum _ fun y _ ↦ continuous_const.mul
        (continuous_gridSurvival A B y)).intervalIntegrable _ _),
      intervalIntegral.integral_finset_sum fun y _ ↦
        ((continuous_const.mul (continuous_gridSurvival A B y)).intervalIntegrable _ _)]
    exact sum_congr rfl fun y _ ↦ (intervalIntegral.integral_const_mul _ _).symm
  have hlimit : Tendsto (fun T : ℝ ↦ ∑ y, loadGenerator A B x y *
      ∫ t in (0 : ℝ)..T, gridSurvival A B y t) atTop
        (𝓝 (∑ y, loadGenerator A B x y * ∫ t in Set.Ioi 0, gridSurvival A B y t)) := by
    refine tendsto_finset_sum _ fun y _ ↦ ?_
    by_cases hy : 1 ≤ (y.1 : ℕ) ∧ 1 ≤ (y.2 : ℕ)
    · exact (intervalIntegral_tendsto_integral_Ioi 0 (integrableOn_gridSurvival hy)
        tendsto_id).const_mul _
    · rw [loadGenerator_eq_zero_of_not_pos hx hy]
      simp only [zero_mul]
      exact tendsto_const_nhds
  have hsurv : Tendsto (fun T : ℝ ↦ gridSurvival A B x T - 1) atTop (𝓝 (0 - 1)) :=
    (tendsto_gridSurvival_atTop hx).sub_const 1
  simp only [← hftc] at hsurv
  rw [zero_sub] at hsurv
  exact tendsto_nhds_unique hlimit hsurv

/-! ### The first-step mean -/

/-- **The first-step mean of the two-component load chain**: loads `(a, b)` are held for a time of
rate `C(a,2) + C(b,2) + ab`, then move to `(a - 1, b)` at rate `C(a,2)`, to `(a, b - 1)` at rate
`C(b,2)`, or connect at rate `ab`. -/
def loadMean (a b : ℕ) : ℝ :=
  (1 + (if h : 2 ≤ a then (a.choose 2 : ℝ) * loadMean (a - 1) b else 0) +
      (if h : 2 ≤ b then (b.choose 2 : ℝ) * loadMean a (b - 1) else 0)) /
    ((a.choose 2 : ℝ) + b.choose 2 + a * b)
termination_by a + b
decreasing_by all_goals first | omega | (simp_wf; omega)

/-- Loads `(1, 1)` connect after mean one. -/
theorem loadMean_one_one : loadMean 1 1 = 1 := by
  rw [loadMean, dif_neg (show ¬(2 ≤ 1) by norm_num)]
  norm_num [Nat.choose]

/-- **Spec (A4)**: loads `(2, 1)` connect after mean `2/3`. -/
theorem loadMean_two_one : loadMean 2 1 = 2 / 3 := by
  rw [loadMean, dif_pos (show 2 ≤ 2 by norm_num), dif_neg (show ¬(2 ≤ 1) by norm_num)]
  norm_num [loadMean_one_one, Nat.choose]

/-- **The integral of the survival function is the first-step mean**, by induction on the total
load. -/
theorem integral_gridSurvival_eq_loadMean_aux {A B : ℕ} (k : ℕ) :
    ∀ x : Fin (A + 1) × Fin (B + 1), (x.1 : ℕ) + (x.2 : ℕ) = k → 1 ≤ (x.1 : ℕ) →
      1 ≤ (x.2 : ℕ) → ∫ t in Set.Ioi 0, gridSurvival A B x t = loadMean x.1 x.2 := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro x hk ha hb
    have hsum := sum_loadGenerator_mul_integral (A := A) (B := B) ⟨ha, hb⟩
    rw [← sum_loadGenerator_mul A B
      (gridExtension A B fun y ↦ ∫ t in Set.Ioi 0, gridSurvival A B y t) x] at hsum
    simp only [gridExtension_apply] at hsum
    have hself : gridExtension A B (fun y ↦ ∫ t in Set.Ioi 0, gridSurvival A B y t) x.1 x.2 =
        ∫ t in Set.Ioi 0, gridSurvival A B x t :=
      gridExtension_apply A B _ x
    have hterm1 : (Nat.choose x.1 2 : ℝ) *
        gridExtension A B (fun y ↦ ∫ t in Set.Ioi 0, gridSurvival A B y t) (x.1 - 1) x.2 =
          if h : 2 ≤ (x.1 : ℕ) then (Nat.choose x.1 2 : ℝ) * loadMean (x.1 - 1) x.2 else 0 := by
      by_cases ha2 : 2 ≤ (x.1 : ℕ)
      · rw [dif_pos ha2]
        have hE : gridExtension A B (fun y ↦ ∫ t in Set.Ioi 0, gridSurvival A B y t)
            (x.1 - 1) x.2 = ∫ t in Set.Ioi 0, gridSurvival A B (lowerFirst x) t :=
          gridExtension_apply A B _ (lowerFirst x)
        have hih : ∫ t in Set.Ioi 0, gridSurvival A B (lowerFirst x) t =
            loadMean (x.1 - 1) x.2 :=
          ih ((x.1 : ℕ) - 1 + x.2) (by omega) (lowerFirst x) rfl
            (show 1 ≤ (x.1 : ℕ) - 1 by omega) hb
        rw [hE, hih]
      · rw [dif_neg ha2, Nat.choose_eq_zero_of_lt (by omega : (x.1 : ℕ) < 2), Nat.cast_zero,
          zero_mul]
    have hterm2 : (Nat.choose x.2 2 : ℝ) *
        gridExtension A B (fun y ↦ ∫ t in Set.Ioi 0, gridSurvival A B y t) x.1 (x.2 - 1) =
          if h : 2 ≤ (x.2 : ℕ) then (Nat.choose x.2 2 : ℝ) * loadMean x.1 (x.2 - 1) else 0 := by
      by_cases hb2 : 2 ≤ (x.2 : ℕ)
      · rw [dif_pos hb2]
        have hE : gridExtension A B (fun y ↦ ∫ t in Set.Ioi 0, gridSurvival A B y t)
            x.1 (x.2 - 1) = ∫ t in Set.Ioi 0, gridSurvival A B (lowerSecond x) t :=
          gridExtension_apply A B _ (lowerSecond x)
        have hih : ∫ t in Set.Ioi 0, gridSurvival A B (lowerSecond x) t =
            loadMean x.1 (x.2 - 1) :=
          ih (x.1 + ((x.2 : ℕ) - 1)) (by omega) (lowerSecond x) rfl ha
            (show 1 ≤ (x.2 : ℕ) - 1 by omega)
        rw [hE, hih]
      · rw [dif_neg hb2, Nat.choose_eq_zero_of_lt (by omega : (x.2 : ℕ) < 2), Nat.cast_zero,
          zero_mul]
    have hq : (0 : ℝ) < (Nat.choose x.1 2 : ℝ) + Nat.choose x.2 2 + (x.1 : ℕ) * (x.2 : ℕ) := by
      have hprod : (1 : ℝ) ≤ ((x.1 : ℕ) : ℝ) * (x.2 : ℕ) := by
        have hnat := Nat.mul_le_mul ha hb
        exact_mod_cast hnat
      positivity
    rw [loadMean, eq_div_iff hq.ne', ← hterm1, ← hterm2]
    simp only [twoComponentGenerator, hself] at hsum
    linarith

/-- **The integral of the survival function is the first-step mean** at every positive loads of
the grid. -/
theorem integral_gridSurvival_eq_loadMean {A B : ℕ} (x : Fin (A + 1) × Fin (B + 1))
    (hx : 1 ≤ (x.1 : ℕ) ∧ 1 ≤ (x.2 : ℕ)) :
    ∫ t in Set.Ioi 0, gridSurvival A B x t = loadMean x.1 x.2 :=
  integral_gridSurvival_eq_loadMean_aux _ x rfl hx.1 hx.2

/-- **The mean connection time of the load chain**: `∫_0^∞ S_{a,b} = loadMean a b` for positive
loads. -/
theorem integral_survival_eq_loadMean (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    ∫ t in Set.Ioi 0, survival a b t = loadMean a b :=
  integral_gridSurvival_eq_loadMean (Fin.last a, Fin.last b) ⟨ha, hb⟩

/-- **The first-step mean solves the generator equation** `(-Q) m = 𝟙` at positive loads. -/
theorem sum_loadGenerator_mul_loadMean {A B : ℕ} {x : Fin (A + 1) × Fin (B + 1)}
    (hx : 1 ≤ (x.1 : ℕ) ∧ 1 ≤ (x.2 : ℕ)) :
    ∑ y, loadGenerator A B x y * loadMean y.1 y.2 = -1 := by
  rw [← sum_loadGenerator_mul_integral hx]
  refine sum_congr rfl fun y _ ↦ ?_
  by_cases hy : 1 ≤ (y.1 : ℕ) ∧ 1 ≤ (y.2 : ℕ)
  · rw [integral_gridSurvival_eq_loadMean y hy]
  · rw [loadGenerator_eq_zero_of_not_pos hx hy, zero_mul, zero_mul]

/-! ### Example (A4) -/

/-- **Spec (A4)**: from loads `(2, 1)` the mean connection time is `2/3`. -/
theorem integral_survival_two_one : ∫ t in Set.Ioi 0, survival 2 1 t = 2 / 3 := by
  rw [integral_survival_eq_loadMean 2 1 (by norm_num) (by norm_num), loadMean_two_one]

/-- The survival function of the load chain from loads `(2, 1)` has the mean of the example's
closed-form survival function `½e^{-3t} + ½e^{-t}`. -/
theorem integral_survival_two_one_eq_integral_exampleSurvival :
    ∫ t in Set.Ioi 0, survival 2 1 t = ∫ t in Set.Ioi 0, exampleSurvival t := by
  rw [integral_survival_two_one, integral_exampleSurvival]

/-- **The three clocks differ**: the connection time from loads `(2, 1)` has mean `2/3`, the graph
coalescent started at `q` has mean `1`, and the labeled root time has mean `4/3`. -/
theorem three_clocks_differ_survival :
    ∫ t in Set.Ioi 0, survival 2 1 t ≠ graphMeanTransitTime exampleInterface ∧
      graphMeanTransitTime exampleInterface ≠ meanTransitTime 3 ∧
      ∫ t in Set.Ioi 0, survival 2 1 t ≠ meanTransitTime 3 := by
  rw [integral_survival_two_one_eq_integral_exampleSurvival]
  exact three_clocks_differ

end

end Descent.Pangenome.GraphCoalescent.KilledSurvivalMean
