/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.FourthMomentDuality

assert_below Descent.Decision Descent.Program

/-!
# The global fourth-moment region: feasibility, value, and no duality gap

This assembles UPT Theorem 3.1 on top of `FourthMomentDuality`, and proves UPT
Theorem 3.2.

* `minFourthMoment` is `V(β, k, m)` of UPT (3.3)/(3.5): the infimum of `E[a²]` over the
  reduced constraint set (3.6). `FourthMomentDuality.twoPointKernel_moments` turns any
  feasible reduced pair into an actual outcome kernel with that fourth moment, so this is
  the same number as the infimum over kernels.
* `feasible_second_moment_bound` is the necessity half of UPT (3.4): orthonormal features
  force `m ≥ β² + ‖k‖²`. `featureMean`/`slackSecond` are the sufficiency half — the
  explicit pair `b = β + kᵀX`, `a = b² + τ` of UPT Step 1, whose two-point kernel is a
  law with exactly the prescribed moments.
* `boundary_mean_square_rigidity` is UPT (3.11) in the form available for an arbitrary
  positive linear functional, and `boundary_pointwise` upgrades it to an identity at every
  point for a finitely supported law with positive weights, where the fourth moment is
  then the singleton `E[(β + kᵀX)⁴]`.
* `minFourthMoment_eq_of_certificate` and `strong_duality_at_certificate` are UPT
  Theorem 3.1(b): at any certified point the dual objective equals the primal minimum, so
  the supremum in (3.8) is attained and there is no gap.
* `constant_magnitude_value` and `constant_magnitude_of_value_eq` are the two halves of
  UPT Theorem 3.2 (3.16), and `support_function_bound` is the support-function inequality
  (3.17) for a point of `√m 𝒵_X`.
* `waterfill_minFourthMoment` is the general solved case behind every closed form in UPT
  §3.5: when the conditional mean `b` is forced, the optimal second moment raises `b²` to
  a common water level `t`, and the multipliers `r = 2t`, `λ₀ + λᵀX = 4(a − t) b` certify
  it whenever that form is affine in the features. Both Corollary 3.3 and Corollary 3.4
  are instances.

The orthonormality hypotheses `E X = 0` and `E[XXᵀ] = I` are UPT (3.1); they are the
coordinate choice the manuscript makes, not an assumption about the answer.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.GlobalFourthMomentRegion

open Foundations IndividualLossMoments FourthMomentDuality

noncomputable section

variable {Ω : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Elementary functional identities -/

omit [Fintype ι] [DecidableEq ι] in
/-- Expansion of a mean squared difference for a positive linear functional. -/
theorem eval_sq_sub (E : ExpFunctional Ω) (f g : Ω → ℝ) :
    E (fun ω ↦ (f ω - g ω) ^ 2)
      = E (fun ω ↦ f ω ^ 2) - 2 * E (fun ω ↦ f ω * g ω) + E (fun ω ↦ g ω ^ 2) := by
  have hsplit : (fun ω ↦ (f ω - g ω) ^ 2)
      = (fun ω ↦ f ω ^ 2) + (-2 : ℝ) • (fun ω ↦ f ω * g ω) + (fun ω ↦ g ω ^ 2) := by
    funext ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [hsplit, E.add_eval, E.add_eval, E.smul_eval]
  ring

omit [Fintype ι] [DecidableEq ι] in
/-- A positive linear functional does not increase absolute value. -/
theorem abs_eval_le (E : ExpFunctional Ω) (f : Ω → ℝ) :
    |E f| ≤ E (fun ω ↦ |f ω|) := by
  have h1 : E f ≤ E (fun ω ↦ |f ω|) := E.eval_mono fun ω ↦ le_abs_self _
  have h2 : E (fun ω ↦ -|f ω|) ≤ E f := E.eval_mono fun ω ↦ neg_abs_le _
  have h3 : E (fun ω ↦ -|f ω|) = -E (fun ω ↦ |f ω|) := E.eval_neg (fun ω ↦ |f ω|)
  rw [h3] at h2
  exact abs_le.mpr ⟨by linarith, h1⟩

omit [DecidableEq ι] in
/-- A scalar factors out of a coordinate inner product. -/
theorem dot_smul_right (lam : ι → ℝ) (c : ℝ) (v : ι → ℝ) :
    dot lam (fun i ↦ c * v i) = c * dot lam v := by
  simp only [dot, Descent.Core.innerSum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ ↦ by ring

/-- The expectation of a feature-linear form is that form applied to the feature means. -/
theorem eval_dot_feature (E : ExpFunctional Ω) (X : Ω → ι → ℝ) (k : ι → ℝ) :
    E (fun ω ↦ dot k (X ω)) = dot k (fun i ↦ E (fun ω ↦ X ω i)) := by
  have hsplit : (fun ω ↦ dot k (X ω))
      = Finset.univ.sum (fun i ↦ (k i) • (fun ω ↦ X ω i)) := by
    funext ω
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, dot, Descent.Core.innerSum]
  rw [hsplit, E.eval_sum]
  simp only [E.smul_eval]
  rfl

/-! ## The value `V(β, k, m)` of the reduced program -/

/-- The set of reduced objective values `E[a²]` over all pairs satisfying the constraints
(3.6) of UPT Theorem 3.1(a). -/
def reducedValues (E : ExpFunctional Ω) (X : Ω → ι → ℝ) (β : ℝ) (k : ι → ℝ) (m : ℝ) :
    Set ℝ :=
  {v : ℝ | ∃ b a : Ω → ℝ, (∀ ω, b ω ^ 2 ≤ a ω) ∧ E b = β ∧
    (∀ i, E (fun ω ↦ X ω i * b ω) = k i) ∧ E a = m ∧ v = E (fun ω ↦ a ω ^ 2)}

/-- `V(β, k, m)` of UPT (3.3): the least residual fourth moment compatible with the
prescribed mean, feature cross-moments, and second moment. -/
def minFourthMoment (E : ExpFunctional Ω) (X : Ω → ι → ℝ) (β : ℝ) (k : ι → ℝ) (m : ℝ) :
    ℝ :=
  sInf (reducedValues E X β k m)

/-- **A certified pair computes `V` (UPT Theorem 3.1(a)).** Pointwise complementarity at a
feasible pair identifies that pair's objective as the minimum. -/
theorem minFourthMoment_eq_of_certificate (E : ExpFunctional Ω) (X : Ω → ι → ℝ)
    (b a : Ω → ℝ) (β : ℝ) (k : ι → ℝ) (m : ℝ) (lam0 : ℝ) (lam : ι → ℝ) (r : ℝ)
    (hab : ∀ ω, b ω ^ 2 ≤ a ω)
    (hb : E b = β) (hk : ∀ i, E (fun ω ↦ X ω i * b ω) = k i) (ha : E a = m)
    (hmax : ∀ ω, ∀ e : ℝ, (lam0 + dot lam (X ω)) * e + r * e ^ 2 - e ^ 4
      ≤ (lam0 + dot lam (X ω)) * b ω + r * a ω - a ω ^ 2) :
    minFourthMoment E X β k m = E (fun ω ↦ a ω ^ 2) := by
  refine IsLeast.csInf_eq ⟨⟨b, a, hab, hb, hk, ha, rfl⟩, ?_⟩
  rintro v ⟨b', a', hab', hb', hk', ha', rfl⟩
  exact certificate_minimizes E X b a β k m lam0 lam r hab hb hk ha hmax b' a' hab'
    hb' hk' ha'

/-- **No duality gap at a certified point (UPT Theorem 3.1(b)).** The supremum in (3.8) is
attained at the certifying multipliers, and its value is exactly `V(β, k, m)`. -/
theorem strong_duality_at_certificate (E : ExpFunctional Ω) (X : Ω → ι → ℝ)
    (b a : Ω → ℝ) (β : ℝ) (k : ι → ℝ) (m : ℝ) (lam0 : ℝ) (lam : ι → ℝ) (r : ℝ)
    (hab : ∀ ω, b ω ^ 2 ≤ a ω)
    (hb : E b = β) (hk : ∀ i, E (fun ω ↦ X ω i * b ω) = k i) (ha : E a = m)
    (hmax : ∀ ω, ∀ e : ℝ, (lam0 + dot lam (X ω)) * e + r * e ^ 2 - e ^ 4
      ≤ (lam0 + dot lam (X ω)) * b ω + r * a ω - a ω ^ 2) :
    minFourthMoment E X β k m = dualObjective E X β k m lam0 lam r := by
  rw [minFourthMoment_eq_of_certificate E X b a β k m lam0 lam r hab hb hk ha hmax,
    dualObjective_eq_of_certificate E X b a β k m lam0 lam r hab hb hk ha hmax]

omit [Fintype ι] [DecidableEq ι] in
/-- **`V ≥ m²` (conditional Jensen).** -/
theorem sq_le_minFourthMoment (E : ExpFunctional Ω) (X : Ω → ι → ℝ) (β : ℝ) (k : ι → ℝ)
    (m : ℝ) (hne : (reducedValues E X β k m).Nonempty) :
    m ^ 2 ≤ minFourthMoment E X β k m := by
  refine le_csInf hne ?_
  rintro v ⟨b, a, hab, hb, hk, ha, rfl⟩
  exact second_moment_sq_le E a m ha

/-! ## Feasibility: UPT (3.4) -/

/-- The forced conditional mean on the deterministic boundary, `β + kᵀX`. -/
def featureMean (β : ℝ) (k : ι → ℝ) (X : Ω → ι → ℝ) : Ω → ℝ :=
  fun ω ↦ β + dot k (X ω)

/-- The conditional second moment of UPT Step 1: the forced mean squared, plus the whole
slack `τ = m − β² − ‖k‖²` spread uniformly. -/
def slackSecond (β : ℝ) (k : ι → ℝ) (X : Ω → ι → ℝ) (m : ℝ) : Ω → ℝ :=
  fun ω ↦ featureMean β k X ω ^ 2 + (m - β ^ 2 - dot k k)

/-- Under UPT (3.1) the forced mean `β + kᵀX` has exactly the prescribed mean and feature
cross-moments, and second moment `β² + ‖k‖²`. -/
theorem featureMean_moments (E : ExpFunctional Ω) (X : Ω → ι → ℝ) (β : ℝ) (k : ι → ℝ)
    (hmean : ∀ i, E (fun ω ↦ X ω i) = 0)
    (horth : ∀ i j, E (fun ω ↦ X ω i * X ω j) = if i = j then 1 else 0) :
    E (featureMean β k X) = β ∧
      (∀ i, E (fun ω ↦ X ω i * featureMean β k X ω) = k i) ∧
      E (fun ω ↦ featureMean β k X ω ^ 2) = β ^ 2 + dot k k := by
  have hm : E (featureMean β k X) = β := by
    have hsplit : featureMean β k X = (fun _ : Ω ↦ β) + fun ω ↦ dot k (X ω) := by
      funext ω
      simp [featureMean]
    rw [hsplit, E.add_eval, E.eval_const, eval_dot_feature E X k]
    simp only [hmean]
    simp [dot, Descent.Core.innerSum]
  have hc : ∀ i, E (fun ω ↦ X ω i * featureMean β k X ω) = k i := by
    intro i
    have hcomm : (fun ω ↦ X ω i * featureMean β k X ω)
        = fun ω ↦ (β + dot k (X ω)) * X ω i := by
      funext ω
      simp [featureMean, mul_comm]
    rw [hcomm, eval_affine_form E X (fun ω ↦ X ω i) β k]
    simp only [hmean, horth, mul_zero, zero_add]
    simp [dot, Descent.Core.innerSum]
  refine ⟨hm, hc, ?_⟩
  have hsq : (fun ω ↦ featureMean β k X ω ^ 2)
      = fun ω ↦ (β + dot k (X ω)) * featureMean β k X ω := by
    funext ω
    simp [featureMean]
    ring
  rw [hsq, eval_affine_form E X (featureMean β k X) β k, hm]
  simp only [hc]
  ring

/-- **Sufficiency in UPT (3.4).** When `m ≥ β² + ‖k‖²` the explicit pair of Step 1 is
feasible for the reduced program. -/
theorem slackPair_feasible (E : ExpFunctional Ω) (X : Ω → ι → ℝ) (β : ℝ) (k : ι → ℝ)
    (m : ℝ) (hmean : ∀ i, E (fun ω ↦ X ω i) = 0)
    (horth : ∀ i j, E (fun ω ↦ X ω i * X ω j) = if i = j then 1 else 0)
    (hfeas : β ^ 2 + dot k k ≤ m) :
    (∀ ω, featureMean β k X ω ^ 2 ≤ slackSecond β k X m ω) ∧
      E (featureMean β k X) = β ∧
      (∀ i, E (fun ω ↦ X ω i * featureMean β k X ω) = k i) ∧
      E (slackSecond β k X m) = m := by
  obtain ⟨hm, hc, hsq⟩ := featureMean_moments E X β k hmean horth
  refine ⟨fun ω ↦ by simp only [slackSecond]; linarith, hm, hc, ?_⟩
  have hsplit : slackSecond β k X m
      = (fun ω ↦ featureMean β k X ω ^ 2) + fun _ : Ω ↦ (m - β ^ 2 - dot k k) := by
    funext ω
    simp [slackSecond]
  rw [hsplit, E.add_eval, E.eval_const, hsq]
  ring

/-- The reduced constraint set is nonempty exactly on the feasible side of (3.4). -/
theorem reducedValues_nonempty (E : ExpFunctional Ω) (X : Ω → ι → ℝ) (β : ℝ) (k : ι → ℝ)
    (m : ℝ) (hmean : ∀ i, E (fun ω ↦ X ω i) = 0)
    (horth : ∀ i j, E (fun ω ↦ X ω i * X ω j) = if i = j then 1 else 0)
    (hfeas : β ^ 2 + dot k k ≤ m) :
    (reducedValues E X β k m).Nonempty := by
  obtain ⟨h1, h2, h3, h4⟩ := slackPair_feasible E X β k m hmean horth hfeas
  exact ⟨_, featureMean β k X, slackSecond β k X m, h1, h2, h3, h4, rfl⟩

/-- **Necessity in UPT (3.4).** With orthonormal features, every feasible reduced pair
forces `m ≥ β² + ‖k‖²`; there is no hypothesis here beyond the constraints themselves. -/
theorem feasible_second_moment_bound (E : ExpFunctional Ω) (X : Ω → ι → ℝ)
    (β : ℝ) (k : ι → ℝ) (m : ℝ) (b a : Ω → ℝ)
    (hmean : ∀ i, E (fun ω ↦ X ω i) = 0)
    (horth : ∀ i j, E (fun ω ↦ X ω i * X ω j) = if i = j then 1 else 0)
    (hab : ∀ ω, b ω ^ 2 ≤ a ω) (hb : E b = β)
    (hk : ∀ i, E (fun ω ↦ X ω i * b ω) = k i) (ha : E a = m) :
    β ^ 2 + dot k k ≤ m := by
  obtain ⟨_, _, hsq⟩ := featureMean_moments (X := X) E β k hmean horth
  have hbg : E (fun ω ↦ b ω * featureMean β k X ω) = β ^ 2 + dot k k := by
    have hcomm : (fun ω ↦ b ω * featureMean β k X ω)
        = fun ω ↦ (β + dot k (X ω)) * b ω := by
      funext ω
      simp [featureMean, mul_comm]
    rw [hcomm, eval_affine_form E X b β k, hb]
    simp only [hk]
    ring
  have hnn : 0 ≤ E (fun ω ↦ (b ω - featureMean β k X ω) ^ 2) :=
    E.nonneg_eval _ fun ω ↦ sq_nonneg _
  rw [eval_sq_sub E b (featureMean β k X), hbg, hsq] at hnn
  have hle : E (fun ω ↦ b ω ^ 2) ≤ m := by
    rw [← ha]
    exact E.eval_mono hab
  linarith

/-! ## The deterministic boundary: UPT (3.11) -/

/-- **Boundary rigidity (UPT (3.11)).** On the equality face `m = β² + ‖k‖²` every
feasible pair has `b = β + kᵀX` and `a = b²` in mean square: the residual is the feature
regression almost surely, in the form available for an arbitrary positive functional. -/
theorem boundary_mean_square_rigidity (E : ExpFunctional Ω) (X : Ω → ι → ℝ)
    (β : ℝ) (k : ι → ℝ) (m : ℝ) (b a : Ω → ℝ)
    (hmean : ∀ i, E (fun ω ↦ X ω i) = 0)
    (horth : ∀ i j, E (fun ω ↦ X ω i * X ω j) = if i = j then 1 else 0)
    (hab : ∀ ω, b ω ^ 2 ≤ a ω) (hb : E b = β)
    (hk : ∀ i, E (fun ω ↦ X ω i * b ω) = k i) (ha : E a = m)
    (hbdry : m = β ^ 2 + dot k k) :
    E (fun ω ↦ (b ω - featureMean β k X ω) ^ 2) = 0 ∧
      E (fun ω ↦ a ω - b ω ^ 2) = 0 := by
  obtain ⟨_, _, hsq⟩ := featureMean_moments (X := X) E β k hmean horth
  have hbg : E (fun ω ↦ b ω * featureMean β k X ω) = β ^ 2 + dot k k := by
    have hcomm : (fun ω ↦ b ω * featureMean β k X ω)
        = fun ω ↦ (β + dot k (X ω)) * b ω := by
      funext ω
      simp [featureMean, mul_comm]
    rw [hcomm, eval_affine_form E X b β k, hb]
    simp only [hk]
    ring
  have hnn : 0 ≤ E (fun ω ↦ (b ω - featureMean β k X ω) ^ 2) :=
    E.nonneg_eval _ fun ω ↦ sq_nonneg _
  have hexp := eval_sq_sub E b (featureMean β k X)
  rw [hbg, hsq] at hexp
  have hle : E (fun ω ↦ b ω ^ 2) ≤ m := by
    rw [← ha]
    exact E.eval_mono hab
  have hbsq : E (fun ω ↦ b ω ^ 2) = m := by linarith [hexp ▸ hnn]
  refine ⟨by rw [hexp, hbsq]; linarith, ?_⟩
  have hsub : E (fun ω ↦ a ω - b ω ^ 2) = E a - E (fun ω ↦ b ω ^ 2) :=
    E.eval_sub a (fun ω ↦ b ω ^ 2)
  rw [hsub, ha, hbsq]
  ring

/-- A finitely supported law with strictly positive weights sees a pointwise identity
behind every vanishing expectation of a nonnegative function. -/
theorem eq_of_weightedExp_eq_zero [Fintype Ω] (p : Ω → ℝ) (hp : ∀ ω, 0 < p ω)
    (hsum : ∑ ω, p ω = 1) (f : Ω → ℝ) (hf : ∀ ω, 0 ≤ f ω)
    (hzero : weightedExp p (fun ω ↦ (hp ω).le) hsum f = 0) (ω : Ω) : f ω = 0 := by
  have hterms : ∀ ω' ∈ Finset.univ, 0 ≤ p ω' * f ω' :=
    fun ω' _ ↦ mul_nonneg (hp ω').le (hf ω')
  have hsum0 : ∑ ω', p ω' * f ω' = 0 := hzero
  have := (Finset.sum_eq_zero_iff_of_nonneg hterms).mp hsum0 ω (Finset.mem_univ ω)
  rcases mul_eq_zero.mp this with h | h
  · exact absurd h (ne_of_gt (hp ω))
  · exact h

/-- **The boundary fourth moment is a singleton.** For a finitely supported law with
positive weights on the face `m = β² + ‖k‖²`, every feasible pair has `a = (β + kᵀX)²`
at every point, so `V(β, k, m) = E[(β + kᵀX)⁴]` and no other value occurs. -/
theorem boundary_pointwise [Fintype Ω] (p : Ω → ℝ) (hp : ∀ ω, 0 < p ω)
    (hsum : ∑ ω, p ω = 1) (X : Ω → ι → ℝ) (β : ℝ) (k : ι → ℝ) (m : ℝ) (b a : Ω → ℝ)
    (hmean : ∀ i, weightedExp p (fun ω ↦ (hp ω).le) hsum (fun ω ↦ X ω i) = 0)
    (horth : ∀ i j, weightedExp p (fun ω ↦ (hp ω).le) hsum (fun ω ↦ X ω i * X ω j)
      = if i = j then 1 else 0)
    (hab : ∀ ω, b ω ^ 2 ≤ a ω)
    (hb : weightedExp p (fun ω ↦ (hp ω).le) hsum b = β)
    (hk : ∀ i, weightedExp p (fun ω ↦ (hp ω).le) hsum (fun ω ↦ X ω i * b ω) = k i)
    (ha : weightedExp p (fun ω ↦ (hp ω).le) hsum a = m)
    (hbdry : m = β ^ 2 + dot k k) :
    ∀ ω, b ω = featureMean β k X ω ∧ a ω = featureMean β k X ω ^ 2 := by
  obtain ⟨h1, h2⟩ := boundary_mean_square_rigidity
    (weightedExp p (fun ω ↦ (hp ω).le) hsum) X β k m b a hmean horth hab hb hk ha hbdry
  intro ω
  have hbg : (b ω - featureMean β k X ω) ^ 2 = 0 :=
    eq_of_weightedExp_eq_zero p hp hsum _ (fun ω' ↦ sq_nonneg _) h1 ω
  have hbeq : b ω = featureMean β k X ω := by
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hbg
    linarith [this]
  have hslack : a ω - b ω ^ 2 = 0 :=
    eq_of_weightedExp_eq_zero p hp hsum _ (fun ω' ↦ by linarith [hab ω']) h2 ω
  exact ⟨hbeq, by rw [← hbeq]; linarith⟩

/-! ## UPT Theorem 3.2: the constant-magnitude residual criterion -/

/-- **Sufficiency in UPT (3.16).** If `(β, k)` lies in `√m 𝒵_X`, witnessed by a
contraction `z`, then the constant-second-moment pair `b = √m z`, `a ≡ m` is feasible,
`V(β, k, m) = m²`, and the dual value at the multipliers `(0, 0, 2m)` is already `m²`: the
supremum in (3.8) is attained and there is no gap on this face. -/
theorem constant_magnitude_value (E : ExpFunctional Ω) (X : Ω → ι → ℝ) (β : ℝ)
    (k : ι → ℝ) (m : ℝ) (hm : 0 ≤ m) (z : Ω → ℝ) (hz : ∀ ω, z ω ^ 2 ≤ 1)
    (hzb : Real.sqrt m * E z = β)
    (hzk : ∀ i, Real.sqrt m * E (fun ω ↦ X ω i * z ω) = k i) :
    minFourthMoment E X β k m = m ^ 2 ∧
      minFourthMoment E X β k m = dualObjective E X β k m 0 (fun _ ↦ 0) (2 * m) := by
  have hsm : Real.sqrt m ^ 2 = m := Real.sq_sqrt hm
  set b : Ω → ℝ := fun ω ↦ Real.sqrt m * z ω with hbdef
  have hab : ∀ ω, b ω ^ 2 ≤ m := by
    intro ω
    have h : b ω ^ 2 = m * z ω ^ 2 := by
      rw [hbdef]
      rw [mul_pow, hsm]
    rw [h]
    nlinarith [hz ω]
  have hb : E b = β := by
    have h : E b = Real.sqrt m * E z := by
      have := E.smul_eval (Real.sqrt m) z
      simpa [hbdef, smul_eq_mul] using this
    rw [h, hzb]
  have hk : ∀ i, E (fun ω ↦ X ω i * b ω) = k i := by
    intro i
    have hfun : (fun ω ↦ X ω i * b ω)
        = Real.sqrt m • (fun ω ↦ X ω i * z ω) := by
      funext ω
      simp [hbdef, smul_eq_mul]
      ring
    rw [hfun, E.smul_eval, hzk i]
  have ha : E (fun _ : Ω ↦ m) = m := E.eval_const m
  have hmax : ∀ ω, ∀ e : ℝ,
      (0 + dot (fun _ : ι ↦ (0 : ℝ)) (X ω)) * e + (2 * m) * e ^ 2 - e ^ 4
        ≤ (0 + dot (fun _ : ι ↦ (0 : ℝ)) (X ω)) * b ω + (2 * m) * m - m ^ 2 := by
    intro ω e
    have hd : dot (fun _ : ι ↦ (0 : ℝ)) (X ω) = 0 := by
      simp [dot, Descent.Core.innerSum]
    rw [hd]
    nlinarith [sq_nonneg (e ^ 2 - m)]
  have hval : minFourthMoment E X β k m = E (fun _ : Ω ↦ m ^ 2) :=
    minFourthMoment_eq_of_certificate E X b (fun _ ↦ m) β k m 0 (fun _ ↦ 0) (2 * m)
      hab hb hk ha hmax
  rw [E.eval_const] at hval
  refine ⟨hval, ?_⟩
  rw [hval, dualObjective_zero_multipliers E X β k m hm]

omit [Fintype ι] [DecidableEq ι] in
/-- **Necessity in UPT (3.16).** For a finitely supported law with positive weights and
`m > 0`, a feasible pair whose objective already equals `m²` forces `a ≡ m`, so the
residual has constant magnitude `√m` and `(β, k)` lies in `√m 𝒵_X`. -/
theorem constant_magnitude_of_value_eq [Fintype Ω] (p : Ω → ℝ) (hp : ∀ ω, 0 < p ω)
    (hsum : ∑ ω, p ω = 1) (X : Ω → ι → ℝ) (β : ℝ) (k : ι → ℝ) (m : ℝ) (hm : 0 < m)
    (b a : Ω → ℝ) (hab : ∀ ω, b ω ^ 2 ≤ a ω)
    (hb : weightedExp p (fun ω ↦ (hp ω).le) hsum b = β)
    (hk : ∀ i, weightedExp p (fun ω ↦ (hp ω).le) hsum (fun ω ↦ X ω i * b ω) = k i)
    (ha : weightedExp p (fun ω ↦ (hp ω).le) hsum a = m)
    (hval : weightedExp p (fun ω ↦ (hp ω).le) hsum (fun ω ↦ a ω ^ 2) = m ^ 2) :
    ∃ z : Ω → ℝ, (∀ ω, z ω ^ 2 ≤ 1) ∧
      Real.sqrt m * weightedExp p (fun ω ↦ (hp ω).le) hsum z = β ∧
      ∀ i, Real.sqrt m * weightedExp p (fun ω ↦ (hp ω).le) hsum (fun ω ↦ X ω i * z ω)
        = k i := by
  set E := weightedExp p (fun ω ↦ (hp ω).le) hsum with hE
  have hsm : Real.sqrt m ^ 2 = m := Real.sq_sqrt hm.le
  have hspos : 0 < Real.sqrt m := Real.sqrt_pos.mpr hm
  have hconst : E (fun ω ↦ (a ω - m) ^ 2) = 0 := by
    have hexp := eval_sq_sub E a (fun _ ↦ m)
    have h1 : E (fun ω ↦ a ω * m) = m ^ 2 := by
      have h : (fun ω ↦ a ω * m) = m • a := by
        funext ω
        simp [smul_eq_mul, mul_comm]
      rw [h, E.smul_eval, ha]
      ring
    rw [hval, h1, E.eval_const] at hexp
    have hm2 : E (fun _ : Ω ↦ m ^ 2) = m ^ 2 := E.eval_const _
    rw [hexp]
    ring
  have hazero : ∀ ω, a ω = m := by
    intro ω
    have h := eq_of_weightedExp_eq_zero p hp hsum _ (fun ω' ↦ sq_nonneg _) hconst ω
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h
    linarith [this]
  refine ⟨fun ω ↦ b ω / Real.sqrt m, fun ω ↦ ?_, ?_, ?_⟩
  · have h := hab ω
    rw [hazero ω] at h
    rw [div_pow, hsm, div_le_one hm]
    exact h
  · have h : E (fun ω ↦ b ω / Real.sqrt m) = (Real.sqrt m)⁻¹ * E b := by
      have hfun : (fun ω ↦ b ω / Real.sqrt m) = (Real.sqrt m)⁻¹ • b := by
        funext ω
        simp [smul_eq_mul, div_eq_inv_mul]
      rw [hfun, E.smul_eval]
    rw [h, hb]
    field_simp
  · intro i
    have hfun : (fun ω ↦ X ω i * (b ω / Real.sqrt m))
        = (Real.sqrt m)⁻¹ • (fun ω ↦ X ω i * b ω) := by
      funext ω
      simp [smul_eq_mul]
      ring
    rw [hfun, E.smul_eval, hk i]
    field_simp

/-- **The support-function inequality (UPT (3.17)).** A point of `√m 𝒵_X` satisfies every
supporting halfspace inequality for that set. -/
theorem support_function_bound (E : ExpFunctional Ω) (X : Ω → ι → ℝ) (β : ℝ) (k : ι → ℝ)
    (m : ℝ) (hm : 0 ≤ m) (z : Ω → ℝ) (hzb : Real.sqrt m * E z = β)
    (hzk : ∀ i, Real.sqrt m * E (fun ω ↦ X ω i * z ω) = k i)
    (hz : ∀ ω, |z ω| ≤ 1) (lam0 : ℝ) (lam : ι → ℝ) :
    |lam0 * β + dot lam k| ≤ Real.sqrt m * E (fun ω ↦ |lam0 + dot lam (X ω)|) := by
  have hsm : 0 ≤ Real.sqrt m := Real.sqrt_nonneg m
  rcases eq_or_lt_of_le hm with hm0 | hmpos
  · have hz0 : Real.sqrt m = 0 := by
      rw [← hm0]
      simp
    have hb0 : β = 0 := by
      rw [← hzb, hz0]
      ring
    have hk0 : ∀ i, k i = 0 := by
      intro i
      rw [← hzk i, hz0]
      ring
    have hdot : dot lam k = 0 := by
      simp [dot, Descent.Core.innerSum, hk0]
    rw [hb0, hdot, hz0]
    simp
  have hspos : 0 < Real.sqrt m := Real.sqrt_pos.mpr hmpos
  have hne : Real.sqrt m ≠ 0 := ne_of_gt hspos
  have hkey : lam0 * β + dot lam k
      = Real.sqrt m * E (fun ω ↦ (lam0 + dot lam (X ω)) * z ω) := by
    rw [eval_affine_form E X z lam0 lam]
    have hk' : (fun i ↦ E (fun ω ↦ X ω i * z ω))
        = fun i ↦ (Real.sqrt m)⁻¹ * k i := by
      funext i
      rw [← hzk i]
      field_simp
    rw [hk', dot_smul_right lam (Real.sqrt m)⁻¹ k, ← hzb]
    field_simp
  rw [hkey, abs_mul, abs_of_nonneg hsm]
  refine mul_le_mul_of_nonneg_left ?_ hsm
  refine le_trans (abs_eval_le E (fun ω ↦ (lam0 + dot lam (X ω)) * z ω)) ?_
  refine E.eval_mono fun ω ↦ ?_
  rw [abs_mul]
  have h1 : |z ω| ≤ 1 := hz ω
  nlinarith [abs_nonneg (lam0 + dot lam (X ω)), abs_nonneg (z ω)]

/-! ## Water filling: the solved case behind the closed forms of UPT §3.5 -/

/-- The water-filling conditional second moment at level `t`: the forced lower bound `b²`
raised to `t` wherever it falls short. -/
def waterfillSecond (b : Ω → ℝ) (t : ℝ) : Ω → ℝ :=
  fun ω ↦ max (b ω ^ 2) t

/-- The dual linear form attached to the water-filling pair, `4(a − t) b`. It vanishes
wherever the level `t` is binding and is proportional to `b` wherever `b²` is. -/
def waterfillForm (b : Ω → ℝ) (t : ℝ) : Ω → ℝ :=
  fun ω ↦ 4 * (waterfillSecond b t ω - t) * b ω

omit [Fintype ι] [DecidableEq ι] in
/-- **Pointwise complementarity of the water-filling pair.** Where `b²` binds, the quartic
of (3.7) exceeds its value at `e = b` by `(b² − e²)² + 2(b² − t)(b − e)²`; where the level
binds, by `(e² − t)²`. Both are nonnegative, so the pair maximizes the pointwise
Lagrangian at the multipliers `r = 2t` and `z = 4(a − t) b`. -/
theorem waterfill_pointwise (b : Ω → ℝ) (t : ℝ) (ω : Ω) (e : ℝ) :
    waterfillForm b t ω * e + 2 * t * e ^ 2 - e ^ 4
      ≤ waterfillForm b t ω * b ω + 2 * t * waterfillSecond b t ω
        - waterfillSecond b t ω ^ 2 := by
  unfold waterfillForm waterfillSecond
  rcases le_total t (b ω ^ 2) with h | h
  · rw [max_eq_left h]
    nlinarith [sq_nonneg (b ω ^ 2 - e ^ 2), sq_nonneg (b ω - e), sub_nonneg.mpr h]
  · rw [max_eq_right h]
    nlinarith [sq_nonneg (e ^ 2 - t)]

/-- **The water-filling pair attains `V` and closes the duality gap.** If the conditional
mean `b` has the prescribed mean and feature cross-moments, the water level `t` makes the
second moment come out at `m`, and the form `4(a − t) b` is affine in the features, then
`V(β, k, m) = E[a²]` and the supremum of (3.8) is attained at `(λ₀, λ, 2t)`. -/
theorem waterfill_minFourthMoment (E : ExpFunctional Ω) (X : Ω → ι → ℝ) (b : Ω → ℝ)
    (t : ℝ) (β : ℝ) (k : ι → ℝ) (m : ℝ) (lam0 : ℝ) (lam : ι → ℝ)
    (haff : ∀ ω, lam0 + dot lam (X ω) = waterfillForm b t ω)
    (hb : E b = β) (hk : ∀ i, E (fun ω ↦ X ω i * b ω) = k i)
    (ha : E (waterfillSecond b t) = m) :
    minFourthMoment E X β k m = E (fun ω ↦ waterfillSecond b t ω ^ 2) ∧
      minFourthMoment E X β k m = dualObjective E X β k m lam0 lam (2 * t) := by
  have hab : ∀ ω, b ω ^ 2 ≤ waterfillSecond b t ω := fun ω ↦ le_max_left _ _
  have hmax : ∀ ω, ∀ e : ℝ, (lam0 + dot lam (X ω)) * e + 2 * t * e ^ 2 - e ^ 4
      ≤ (lam0 + dot lam (X ω)) * b ω + 2 * t * waterfillSecond b t ω
        - waterfillSecond b t ω ^ 2 := by
    intro ω e
    rw [haff ω]
    exact waterfill_pointwise b t ω e
  exact ⟨minFourthMoment_eq_of_certificate E X b (waterfillSecond b t) β k m lam0 lam
      (2 * t) hab hb hk ha hmax,
    strong_duality_at_certificate E X b (waterfillSecond b t) β k m lam0 lam (2 * t)
      hab hb hk ha hmax⟩

end

end Descent.Portability.GlobalFourthMomentRegion
