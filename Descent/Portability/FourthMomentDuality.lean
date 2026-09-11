/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.IndividualLossMoments

assert_below Descent.Decision Descent.Program

/-!
# The global fourth-moment program and its finite-dimensional dual

UPT Theorem 3.1 holds the entire pre-outcome law fixed and prescribes an outcome mean `β`,
a vector of feature cross-moments `k`, and a second moment `m`; it asks for the least
attainable fourth moment `V(β, k, m)`. This module proves the parts that need no
assumption on the shape of the feature law.

* The reduction of an arbitrary outcome kernel to its pair of conditional moments
  `(b, a) = (E[E | W], E[E² | W])`, which always satisfies `b² ≤ a` and always has
  `E[E⁴] ≥ E[a²]` (UPT 3.5-3.6, Step 2); and the converse, the explicit conditional
  two-point law of UPT (3.12) supported on `{±√a(W)}`, whose fourth moment is exactly
  `E[a²]`. Together these say the two infima agree and the minimizing kernel may be taken
  two-point.
* Weak duality for the dual (3.8), whose only ingredient is the scalar quartic maximum
  `Φ(z, r) = sup_e (z e + r e² − e⁴)` of (3.7), proved here to be a genuine supremum.
* A no-gap certificate: a feasible pair together with multipliers at which the pointwise
  quartic is maximized by that pair proves simultaneously that the pair is a minimizer and
  that the dual value equals it. Every closed form in UPT §3.5 is an instance.
* The unconditional bounds `V ≥ m²` (conditional Jensen) and `sup ≥ m²` (the multipliers
  `(0, 0, 2m)`), which already give no gap on the whole `V = m²` face of UPT Theorem 3.2.

Everything is stated for an arbitrary `Foundations.ExpFunctional`; no finiteness and no
orthonormality of the features is used anywhere in this module. It builds on
`Foundations.ExpFunctional`, `Foundations.cauchy_schwarz`, `Foundations.dot` and on
`IndividualLossMoments.mixture`, the outer-law/conditional-kernel pairing used throughout
the portability corpus.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.FourthMomentDuality

open Foundations IndividualLossMoments

noncomputable section

variable {Ω Ψ : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## The scalar quartic maximum `Φ` -/

/-- `Φ(z, r) = sup_e {z e + r e² − e⁴}`, the scalar conjugate of UPT (3.7). -/
def quarticMax (z r : ℝ) : ℝ :=
  sSup {v : ℝ | ∃ e : ℝ, v = z * e + r * e ^ 2 - e ^ 4}

/-- An explicit polynomial majorant for the quartic of (3.7): apply `z e ≤ (z² + e²)/2` and
then `c e² − e⁴ ≤ c²/4`. This is the Young-type bound of UPT Step 4 in a form with no
fractional powers. -/
theorem quartic_le_bound (z r e : ℝ) :
    z * e + r * e ^ 2 - e ^ 4 ≤ z ^ 2 / 2 + (2 * r + 1) ^ 2 / 16 := by
  nlinarith [sq_nonneg (e - z), sq_nonneg (e ^ 2 - (2 * r + 1) / 4)]

/-- The quartic value set is bounded above, so `quarticMax` is a real supremum and not the
junk value of an unbounded `sSup`. -/
theorem quarticMax_bddAbove (z r : ℝ) :
    BddAbove {v : ℝ | ∃ e : ℝ, v = z * e + r * e ^ 2 - e ^ 4} := by
  refine ⟨z ^ 2 / 2 + (2 * r + 1) ^ 2 / 16, ?_⟩
  rintro v ⟨e, rfl⟩
  exact quartic_le_bound z r e

/-- Every evaluation of the quartic is at most `Φ(z, r)`. -/
theorem le_quarticMax (z r e : ℝ) : z * e + r * e ^ 2 - e ^ 4 ≤ quarticMax z r :=
  le_csSup (quarticMax_bddAbove z r) ⟨e, rfl⟩

/-- `Φ(z, r)` is at most any pointwise majorant of the quartic. -/
theorem quarticMax_le {z r c : ℝ} (h : ∀ e : ℝ, z * e + r * e ^ 2 - e ^ 4 ≤ c) :
    quarticMax z r ≤ c := by
  refine csSup_le ⟨0, ⟨0, by norm_num⟩⟩ ?_
  rintro v ⟨e, rfl⟩
  exact h e

/-- `Φ ≥ 0`, because `e = 0` is always a competitor. -/
theorem quarticMax_nonneg (z r : ℝ) : 0 ≤ quarticMax z r := by
  have h := le_quarticMax z r 0
  norm_num at h
  exact h

/-- `Φ(z, r) = z e + r e² − e⁴` exactly when `e` maximizes the quartic. -/
theorem quarticMax_eq_of_max {z r e : ℝ}
    (h : ∀ e' : ℝ, z * e' + r * e' ^ 2 - e' ^ 4 ≤ z * e + r * e ^ 2 - e ^ 4) :
    quarticMax z r = z * e + r * e ^ 2 - e ^ 4 :=
  le_antisymm (quarticMax_le h) (le_quarticMax z r e)

/-- `Φ(0, r) = r²/4` for `r ≥ 0`. This is the value that makes the multipliers
`(λ₀, λ, r) = (0, 0, 2m)` a dual competitor of value exactly `m²`. -/
theorem quarticMax_zero_left {r : ℝ} (hr : 0 ≤ r) : quarticMax 0 r = r ^ 2 / 4 := by
  have hs : Real.sqrt (r / 2) ^ 2 = r / 2 := Real.sq_sqrt (by linarith)
  have h4 : Real.sqrt (r / 2) ^ 4 = (r / 2) ^ 2 := by
    have : Real.sqrt (r / 2) ^ 4 = (Real.sqrt (r / 2) ^ 2) ^ 2 := by ring
    rw [this, hs]
  rw [quarticMax_eq_of_max (e := Real.sqrt (r / 2))
      (fun e' ↦ by nlinarith [sq_nonneg (e' ^ 2 - r / 2), hs, h4]), hs, h4]
  ring

/-- **Pointwise Fenchel inequality.** For any conditional-moment pair with `b² ≤ a`,
`z b + r a − a² ≤ Φ(z, r)`: maximizing `z b` over `|b| ≤ √a` gives `|z| √a`, and the
substitution `e = ±√a` turns the remaining problem into the quartic of (3.7). -/
theorem conjugate_pointwise_bound (z r b a : ℝ) (hab : b ^ 2 ≤ a) :
    z * b + r * a - a ^ 2 ≤ quarticMax z r := by
  have ha : 0 ≤ a := le_trans (sq_nonneg b) hab
  have hs : Real.sqrt a ^ 2 = a := Real.sq_sqrt ha
  have hs4 : Real.sqrt a ^ 4 = a ^ 2 := by
    have : Real.sqrt a ^ 4 = (Real.sqrt a ^ 2) ^ 2 := by ring
    rw [this, hs]
  have habs : |b| ≤ Real.sqrt a := by
    have h1 : Real.sqrt (b ^ 2) ≤ Real.sqrt a := Real.sqrt_le_sqrt hab
    rwa [Real.sqrt_sq_eq_abs] at h1
  rcases le_or_gt 0 z with hz | hz
  · have h := le_quarticMax z r (Real.sqrt a)
    rw [hs, hs4] at h
    have hb : b ≤ Real.sqrt a := le_trans (le_abs_self b) habs
    nlinarith [h]
  · have h := le_quarticMax z r (-Real.sqrt a)
    have hsq : (-Real.sqrt a) ^ 2 = a := by rw [neg_pow]; simpa using hs
    have hsq4 : (-Real.sqrt a) ^ 4 = a ^ 2 := by
      have : (-Real.sqrt a) ^ 4 = ((-Real.sqrt a) ^ 2) ^ 2 := by ring
      rw [this, hsq]
    rw [hsq, hsq4] at h
    have hb : -Real.sqrt a ≤ b := by
      have := neg_abs_le b
      linarith [habs]
    nlinarith [h]

/-! ## The reduced program and its dual -/

/-- The dual objective of UPT (3.8) at multipliers `(λ₀, λ, r)`:
`λ₀ β + λᵀ k + r m − E Φ(λ₀ + λᵀX, r)`. -/
def dualObjective (E : ExpFunctional Ω) (X : Ω → ι → ℝ) (β : ℝ) (k : ι → ℝ) (m : ℝ)
    (lam0 : ℝ) (lam : ι → ℝ) (r : ℝ) : ℝ :=
  lam0 * β + dot lam k + r * m - E (fun ω ↦ quarticMax (lam0 + dot lam (X ω)) r)

/-- Linearity of `E` on the three-term combination the duality proof needs. -/
theorem eval_comb (E : ExpFunctional Ω) (f g h : Ω → ℝ) (c : ℝ) :
    E (fun ω ↦ f ω + c * g ω - h ω) = E f + c * E g - E h := by
  have hsplit : (fun ω ↦ f ω + c * g ω - h ω) = f + c • g - h := by
    funext ω
    simp [smul_eq_mul]
  rw [hsplit, E.eval_sub, E.add_eval, E.smul_eval]

/-- The expectation of the dual linear form `(λ₀ + λᵀX) b` is read off the prescribed
moments of `b`: it is `λ₀ E b + λᵀ E[X b]`. -/
theorem eval_affine_form (E : ExpFunctional Ω) (X : Ω → ι → ℝ) (b : Ω → ℝ)
    (lam0 : ℝ) (lam : ι → ℝ) :
    E (fun ω ↦ (lam0 + dot lam (X ω)) * b ω)
      = lam0 * E b + dot lam (fun i ↦ E (fun ω ↦ X ω i * b ω)) := by
  have hsplit : (fun ω ↦ (lam0 + dot lam (X ω)) * b ω)
      = lam0 • b + Finset.univ.sum (fun i ↦ (lam i) • (fun ω ↦ X ω i * b ω)) := by
    funext ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_apply, dot,
      Descent.Core.innerSum]
    rw [add_mul, Finset.sum_mul]
    refine congrArg _ (Finset.sum_congr rfl fun i _ ↦ by ring)
  rw [hsplit, E.add_eval, E.smul_eval, E.eval_sum]
  simp only [E.smul_eval]
  rfl

/-- **Weak duality for the reduced fourth-moment program (UPT Theorem 3.1(b), `≤`).**
Every feasible conditional-moment pair `(b, a)` dominates every dual competitor. The
hypotheses are exactly the constraints (3.6): `a ≥ b²`, `E b = β`, `E[X b] = k`, `E a = m`.
No orthonormality and no finiteness is used. -/
theorem dualObjective_le (E : ExpFunctional Ω) (X : Ω → ι → ℝ) (b a : Ω → ℝ)
    (β : ℝ) (k : ι → ℝ) (m : ℝ) (lam0 : ℝ) (lam : ι → ℝ) (r : ℝ)
    (hab : ∀ ω, b ω ^ 2 ≤ a ω) (hb : E b = β)
    (hk : ∀ i, E (fun ω ↦ X ω i * b ω) = k i) (ha : E a = m) :
    dualObjective E X β k m lam0 lam r ≤ E (fun ω ↦ a ω ^ 2) := by
  have hlin : E (fun ω ↦ (lam0 + dot lam (X ω)) * b ω) = lam0 * β + dot lam k := by
    rw [eval_affine_form E X b lam0 lam, hb]
    simp only [hk]
  have hmono : E (fun ω ↦ (lam0 + dot lam (X ω)) * b ω + r * a ω - a ω ^ 2)
      ≤ E (fun ω ↦ quarticMax (lam0 + dot lam (X ω)) r) :=
    E.eval_mono fun ω ↦ conjugate_pointwise_bound _ r (b ω) (a ω) (hab ω)
  rw [eval_comb E _ a (fun ω ↦ a ω ^ 2) r, hlin, ha] at hmono
  unfold dualObjective
  linarith

/-- **No-gap certificate (UPT Theorem 3.1(a)+(b) at a certified point).** If a feasible
pair `(b, a)` and multipliers `(λ₀, λ, r)` satisfy pointwise complementarity — the quartic
`e ↦ z e + r e² − e⁴` at `z = λ₀ + λᵀX(ω)` is maximized by the value the pair itself
supplies — then the dual objective at those multipliers equals `E[a²]`. -/
theorem dualObjective_eq_of_certificate (E : ExpFunctional Ω) (X : Ω → ι → ℝ)
    (b a : Ω → ℝ) (β : ℝ) (k : ι → ℝ) (m : ℝ) (lam0 : ℝ) (lam : ι → ℝ) (r : ℝ)
    (hab : ∀ ω, b ω ^ 2 ≤ a ω)
    (hb : E b = β) (hk : ∀ i, E (fun ω ↦ X ω i * b ω) = k i) (ha : E a = m)
    (hmax : ∀ ω, ∀ e : ℝ, (lam0 + dot lam (X ω)) * e + r * e ^ 2 - e ^ 4
      ≤ (lam0 + dot lam (X ω)) * b ω + r * a ω - a ω ^ 2) :
    dualObjective E X β k m lam0 lam r = E (fun ω ↦ a ω ^ 2) := by
  have hphi : (fun ω ↦ quarticMax (lam0 + dot lam (X ω)) r)
      = fun ω ↦ (lam0 + dot lam (X ω)) * b ω + r * a ω - a ω ^ 2 := by
    funext ω
    exact le_antisymm (quarticMax_le (hmax ω))
      (conjugate_pointwise_bound _ r (b ω) (a ω) (hab ω))
  have hlin : E (fun ω ↦ (lam0 + dot lam (X ω)) * b ω) = lam0 * β + dot lam k := by
    rw [eval_affine_form E X b lam0 lam, hb]
    simp only [hk]
  unfold dualObjective
  rw [hphi, eval_comb E _ a (fun ω ↦ a ω ^ 2) r, hlin, ha]
  ring

/-- **A certified pair is a minimizer.** Complementarity at `(b, a)` forces every other
feasible pair to have a fourth-moment value at least as large, so `E[a²] = V(β, k, m)` and
the dual supremum is attained. -/
theorem certificate_minimizes (E : ExpFunctional Ω) (X : Ω → ι → ℝ)
    (b a : Ω → ℝ) (β : ℝ) (k : ι → ℝ) (m : ℝ) (lam0 : ℝ) (lam : ι → ℝ) (r : ℝ)
    (hab : ∀ ω, b ω ^ 2 ≤ a ω)
    (hb : E b = β) (hk : ∀ i, E (fun ω ↦ X ω i * b ω) = k i) (ha : E a = m)
    (hmax : ∀ ω, ∀ e : ℝ, (lam0 + dot lam (X ω)) * e + r * e ^ 2 - e ^ 4
      ≤ (lam0 + dot lam (X ω)) * b ω + r * a ω - a ω ^ 2)
    (b' a' : Ω → ℝ) (hab' : ∀ ω, b' ω ^ 2 ≤ a' ω) (hb' : E b' = β)
    (hk' : ∀ i, E (fun ω ↦ X ω i * b' ω) = k i) (ha' : E a' = m) :
    E (fun ω ↦ a ω ^ 2) ≤ E (fun ω ↦ a' ω ^ 2) := by
  have h1 := dualObjective_eq_of_certificate E X b a β k m lam0 lam r hab hb hk ha hmax
  have h2 := dualObjective_le E X b' a' β k m lam0 lam r hab' hb' hk' ha'
  linarith

/-! ## Unconditional bounds: the `m²` floor and the matching dual competitor -/

/-- Conditional Jensen in functional form: `(E f)² ≤ E[f²]`, from `cauchy_schwarz`. -/
theorem sq_eval_le_eval_sq (E : ExpFunctional Ω) (f : Ω → ℝ) :
    E f ^ 2 ≤ E (fun ω ↦ f ω ^ 2) := by
  have h := E.cauchy_schwarz f (fun _ ↦ 1)
  simpa using h

/-- **`V(β, k, m) ≥ m²`.** Jensen applied to `a` alone: the reduced objective of any
feasible pair is at least the square of the prescribed second moment. -/
theorem second_moment_sq_le (E : ExpFunctional Ω) (a : Ω → ℝ) (m : ℝ) (ha : E a = m) :
    m ^ 2 ≤ E (fun ω ↦ a ω ^ 2) := by
  have h := sq_eval_le_eval_sq E a
  rwa [ha] at h

omit [DecidableEq ι] in
/-- **The dual supremum is always at least `m²`.** The multipliers `(0, 0, 2m)` have dual
value exactly `m²` whenever `m ≥ 0`, since `Φ(0, 2m) = m²`. Combined with
`dualObjective_le` and `second_moment_sq_le` this closes the duality gap on the whole face
where `V = m²` (UPT Theorem 3.2). -/
theorem dualObjective_zero_multipliers (E : ExpFunctional Ω) (X : Ω → ι → ℝ)
    (β : ℝ) (k : ι → ℝ) (m : ℝ) (hm : 0 ≤ m) :
    dualObjective E X β k m 0 (fun _ ↦ 0) (2 * m) = m ^ 2 := by
  have hdot : dot (fun _ : ι ↦ (0 : ℝ)) k = 0 := by
    simp [dot, Descent.Core.innerSum]
  have hdotX : ∀ ω : Ω, dot (fun _ : ι ↦ (0 : ℝ)) (X ω) = 0 := by
    intro ω
    simp [dot, Descent.Core.innerSum]
  have hphi : (fun ω : Ω ↦ quarticMax (0 + dot (fun _ : ι ↦ (0 : ℝ)) (X ω)) (2 * m))
      = fun _ : Ω ↦ m ^ 2 := by
    funext ω
    rw [hdotX ω, add_zero, quarticMax_zero_left (by linarith)]
    ring
  unfold dualObjective
  rw [hdot, hphi, E.eval_const]
  ring

/-! ## From an outcome kernel to its conditional moments -/

/-- The conditional first moment `b(W) = E[E | W]` of an outcome kernel. -/
def condMean (K : Ω → ExpFunctional Ψ) (res : Ω × Ψ → ℝ) (ω : Ω) : ℝ :=
  K ω (fun ψ ↦ res (ω, ψ))

/-- The conditional second moment `a(W) = E[E² | W]` of an outcome kernel. -/
def condSecond (K : Ω → ExpFunctional Ψ) (res : Ω × Ψ → ℝ) (ω : Ω) : ℝ :=
  K ω (fun ψ ↦ res (ω, ψ) ^ 2)

/-- The pair of conditional moments of any kernel is feasible for the reduced program:
`b² ≤ a` pointwise (UPT 3.6). -/
theorem condMean_sq_le_condSecond (K : Ω → ExpFunctional Ψ) (res : Ω × Ψ → ℝ) (ω : Ω) :
    condMean K res ω ^ 2 ≤ condSecond K res ω :=
  sq_eval_le_eval_sq (K ω) _

/-- The kernel's outcome mean is the outer mean of its conditional mean. -/
theorem mixture_mean (E : ExpFunctional Ω) (K : Ω → ExpFunctional Ψ) (res : Ω × Ψ → ℝ) :
    mixture E K res = E (condMean K res) := rfl

/-- The kernel's outcome second moment is the outer mean of its conditional second
moment. -/
theorem mixture_second (E : ExpFunctional Ω) (K : Ω → ExpFunctional Ψ) (res : Ω × Ψ → ℝ) :
    mixture E K (fun z ↦ res z ^ 2) = E (condSecond K res) := rfl

omit [Fintype ι] [DecidableEq ι] in
/-- Each feature cross-moment of the kernel is the outer cross-moment against the
conditional mean: the constraints (3.2) depend on the kernel only through `b`. -/
theorem mixture_cross (E : ExpFunctional Ω) (K : Ω → ExpFunctional Ψ) (res : Ω × Ψ → ℝ)
    (X : Ω → ι → ℝ) (i : ι) :
    mixture E K (fun z ↦ X z.1 i * res z) = E (fun ω ↦ X ω i * condMean K res ω) := by
  show E (fun ω ↦ K ω (fun ψ ↦ X ω i * res (ω, ψ))) = _
  refine congrArg E.eval (funext fun ω ↦ ?_)
  have h := (K ω).smul_eval (X ω i) (fun ψ ↦ res (ω, ψ))
  simpa [smul_eq_mul, condMean] using h

/-- **The reduction of UPT Theorem 3.1 Step 2.** The fourth moment of any outcome kernel is
at least the reduced objective `E[a²]` at its own conditional moments. This is conditional
Jensen applied to `E²`. -/
theorem reduced_objective_le_fourth_moment (E : ExpFunctional Ω) (K : Ω → ExpFunctional Ψ)
    (res : Ω × Ψ → ℝ) :
    E (fun ω ↦ condSecond K res ω ^ 2) ≤ mixture E K (fun z ↦ res z ^ 4) := by
  refine E.eval_mono fun ω ↦ ?_
  have h := sq_eval_le_eval_sq (K ω) (fun ψ ↦ res (ω, ψ) ^ 2)
  have hpow : (fun ψ ↦ (res (ω, ψ) ^ 2) ^ 2) = fun ψ ↦ res (ω, ψ) ^ 4 := by
    funext ψ
    ring
  rwa [hpow] at h

/-! ## The conditional two-point law of UPT (3.12) -/

/-- The weight `P(E = +√a | W) = ½(1 + b/√a)` of UPT (3.12), with the degenerate value ½
where `a = 0` (there `b = 0` as well and the law is the point mass at zero). -/
def twoPointWeight (b a : ℝ) : ℝ :=
  if a ≤ 0 then 1 / 2 else (1 + b / Real.sqrt a) / 2

/-- The two-point probability vector on `Bool`. -/
def twoPointWeights (b a : ℝ) : Bool → ℝ
  | true => twoPointWeight b a
  | false => 1 - twoPointWeight b a

/-- The two-point residual values `±√a` of UPT (3.12). -/
def twoPointResidual (a : ℝ) : Bool → ℝ
  | true => Real.sqrt a
  | false => -Real.sqrt a

/-- The weights of (3.12) are probabilities exactly because `|b| ≤ √a`, i.e. because the
pair is feasible for the reduced program. -/
theorem twoPointWeights_nonneg {b a : ℝ} (hab : b ^ 2 ≤ a) (s : Bool) :
    0 ≤ twoPointWeights b a s := by
  have ha : 0 ≤ a := le_trans (sq_nonneg b) hab
  have hbound : 0 ≤ twoPointWeight b a ∧ twoPointWeight b a ≤ 1 := by
    unfold twoPointWeight
    rcases le_or_gt a 0 with h | h
    · rw [if_pos h]
      norm_num
    · rw [if_neg (not_le.mpr h)]
      have hspos : 0 < Real.sqrt a := Real.sqrt_pos.mpr h
      have hs : Real.sqrt a ^ 2 = a := Real.sq_sqrt ha
      have habs : |b| ≤ Real.sqrt a := by
        have h1 : Real.sqrt (b ^ 2) ≤ Real.sqrt a := Real.sqrt_le_sqrt hab
        rwa [Real.sqrt_sq_eq_abs] at h1
      have h1 : -Real.sqrt a ≤ b := by linarith [neg_abs_le b, habs]
      have h2 : b ≤ Real.sqrt a := by linarith [le_abs_self b, habs]
      constructor
      · have : -1 ≤ b / Real.sqrt a := by
          rw [le_div_iff₀ hspos]
          linarith
        linarith
      · have : b / Real.sqrt a ≤ 1 := by
          rw [div_le_iff₀ hspos]
          linarith
        linarith
  cases s with
  | false => exact by simpa [twoPointWeights] using sub_nonneg.mpr hbound.2
  | true => exact hbound.1

/-- The two-point weights sum to one. -/
theorem twoPointWeights_sum (b a : ℝ) : ∑ s : Bool, twoPointWeights b a s = 1 := by
  rw [Fintype.sum_bool]
  show twoPointWeight b a + (1 - twoPointWeight b a) = 1
  ring

/-- The conditional two-point law of UPT (3.12) at conditional moments `(b, a)`. -/
def twoPointExp (b a : ℝ) (hab : b ^ 2 ≤ a) : ExpFunctional Bool :=
  weightedExp (twoPointWeights b a) (twoPointWeights_nonneg hab) (twoPointWeights_sum b a)

/-- The two-point law of (3.12) has conditional mean `b`, conditional second moment `a`,
and conditional fourth moment exactly `a²`. This is the whole content of Step 2's converse:
the reduced objective `E[a²]` is realized, not merely bounded. -/
theorem twoPointExp_moments (b a : ℝ) (hab : b ^ 2 ≤ a) :
    twoPointExp b a hab (twoPointResidual a) = b ∧
      twoPointExp b a hab (fun s ↦ twoPointResidual a s ^ 2) = a ∧
      twoPointExp b a hab (fun s ↦ twoPointResidual a s ^ 4) = a ^ 2 := by
  have ha : 0 ≤ a := le_trans (sq_nonneg b) hab
  have hs : Real.sqrt a ^ 2 = a := Real.sq_sqrt ha
  have hs4 : Real.sqrt a ^ 4 = a ^ 2 := by
    have h : Real.sqrt a ^ 4 = (Real.sqrt a ^ 2) ^ 2 := by ring
    rw [h, hs]
  have hexp : ∀ f : Bool → ℝ, twoPointExp b a hab f
      = twoPointWeight b a * f true + (1 - twoPointWeight b a) * f false := by
    intro f
    show ∑ s : Bool, twoPointWeights b a s * f s = _
    rw [Fintype.sum_bool]
    rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [hexp]
    show twoPointWeight b a * Real.sqrt a + (1 - twoPointWeight b a) * (-Real.sqrt a) = b
    rcases le_or_gt a 0 with h | h
    · have ha0 : a = 0 := le_antisymm h ha
      have hb0 : b = 0 := by nlinarith [sq_nonneg b]
      rw [ha0, hb0]
      simp
    · have hspos : 0 < Real.sqrt a := Real.sqrt_pos.mpr h
      unfold twoPointWeight
      rw [if_neg (not_le.mpr h)]
      field_simp
      ring
  · rw [hexp]
    show twoPointWeight b a * Real.sqrt a ^ 2
      + (1 - twoPointWeight b a) * (-Real.sqrt a) ^ 2 = a
    rw [hs, neg_pow, hs]
    ring
  · rw [hexp]
    show twoPointWeight b a * Real.sqrt a ^ 4
      + (1 - twoPointWeight b a) * (-Real.sqrt a) ^ 4 = a ^ 2
    have hneg : (-Real.sqrt a) ^ 4 = a ^ 2 := by
      have h : (-Real.sqrt a) ^ 4 = (Real.sqrt a) ^ 4 := by ring
      rw [h, hs4]
    rw [hs4, hneg]
    ring

/-- The outcome kernel of UPT (3.12) attached to a feasible reduced pair: conditionally on
`W`, the outcome is `±√a(W)` with the weights of (3.12). -/
def twoPointKernel (a : Ω → ℝ) : Ω × Bool → ℝ :=
  fun z ↦ twoPointResidual (a z.1) z.2

omit [Fintype ι] [DecidableEq ι] in
/-- **The two-point kernel realizes the prescribed moments and the reduced objective.**
Given a feasible pair `(b, a)`, the kernel supported on `{±√a(W)}` has outcome mean `β`,
feature cross-moments `k`, second moment `m`, and fourth moment exactly `E[a²]`. Together
with `reduced_objective_le_fourth_moment` this is the equality of the two infima in UPT
Theorem 3.1(a), and it exhibits a minimizer supported on two conditional points. -/
theorem twoPointKernel_moments (E : ExpFunctional Ω) (X : Ω → ι → ℝ) (b a : Ω → ℝ)
    (β : ℝ) (k : ι → ℝ) (m : ℝ) (hab : ∀ ω, b ω ^ 2 ≤ a ω) (hb : E b = β)
    (hk : ∀ i, E (fun ω ↦ X ω i * b ω) = k i) (ha : E a = m) :
    mixture E (fun ω ↦ twoPointExp (b ω) (a ω) (hab ω)) (twoPointKernel a) = β ∧
      (∀ i, mixture E (fun ω ↦ twoPointExp (b ω) (a ω) (hab ω))
        (fun z ↦ X z.1 i * twoPointKernel a z) = k i) ∧
      mixture E (fun ω ↦ twoPointExp (b ω) (a ω) (hab ω))
        (fun z ↦ twoPointKernel a z ^ 2) = m ∧
      mixture E (fun ω ↦ twoPointExp (b ω) (a ω) (hab ω))
        (fun z ↦ twoPointKernel a z ^ 4) = E (fun ω ↦ a ω ^ 2) := by
  set K : Ω → ExpFunctional Bool := fun ω ↦ twoPointExp (b ω) (a ω) (hab ω) with hK
  have hmean : condMean K (twoPointKernel a) = b := by
    funext ω
    exact (twoPointExp_moments (b ω) (a ω) (hab ω)).1
  have hsecond : condSecond K (twoPointKernel a) = a := by
    funext ω
    exact (twoPointExp_moments (b ω) (a ω) (hab ω)).2.1
  have hfourth : (fun ω ↦ K ω (fun s ↦ twoPointKernel a (ω, s) ^ 4))
      = fun ω ↦ a ω ^ 2 := by
    funext ω
    exact (twoPointExp_moments (b ω) (a ω) (hab ω)).2.2
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [mixture_mean E K, hmean, hb]
  · intro i
    rw [mixture_cross E K _ X i, hmean]
    exact hk i
  · rw [mixture_second E K, hsecond, ha]
  · show E (fun ω ↦ K ω (fun s ↦ twoPointKernel a (ω, s) ^ 4)) = _
    rw [hfourth]

end

end Descent.Portability.FourthMomentDuality
