/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.GlobalFourthMomentRegion

assert_below Descent.Decision Descent.Program

/-!
# The entire attainable fourth-moment range

UPT Theorem 3.1(c). With strict slack `m > β² + ‖k‖²`, the set of residual fourth moments
compatible with the prescribed mean, feature cross-moments and second moment is exactly
`[V(β, k, m), ∞)`, and every finite value in it is attained by an explicit outcome kernel.

The lower half is `kernel_fourth_moment_ge_min`: the conditional moments of any kernel are
feasible for the reduced program, and conditional Jensen puts the kernel's fourth moment
above their objective, hence above `V`.

The upper half is `attains_every_larger_fourth_moment`, the manuscript's Step 6 made
explicit. `splitExp` forms the convex combination of two outcome laws on the disjoint union
of their spaces; `rangeKernel` combines the minimal two-point kernel of UPT (3.12) at a
given feasible pair with a symmetric three-point spread around the forced regression
`β + kᵀX` whose conditional variance is the whole slack `τ`. Both components satisfy the
constraints, so the combination does; its fourth moment is
`θ E[a²] + (1 − θ)(E[g⁴] + 6τ E[g²] + τ s)`, which is affine in the mixing weight `θ` and
in the spread scale `s`. Solving those two linear equations hits any prescribed
`J ≥ E[a²]` on the nose.

This is what UPT Theorem 3.5 needs in a cell with strict slack, and it is the step that
makes the range in UPT (3.21) exact rather than merely bounded.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.FourthMomentAttainableRange

open Foundations IndividualLossMoments FourthMomentDuality GlobalFourthMomentRegion

noncomputable section

variable {Ω : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Linearity helpers -/

omit [Fintype ι] [DecidableEq ι] in
/-- Two-term linearity of a positive linear functional. -/
theorem eval_lin2 (E : ExpFunctional Ω) (c d : ℝ) (f h : Ω → ℝ) :
    E (fun ω ↦ c * f ω + d * h ω) = c * E f + d * E h := by
  have hsplit : (fun ω ↦ c * f ω + d * h ω) = c • f + d • h := by
    funext ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [hsplit, E.add_eval, E.smul_eval, E.smul_eval]

omit [Fintype ι] [DecidableEq ι] in
/-- Three-term linearity plus a constant. -/
theorem eval_lin3_const (E : ExpFunctional Ω) (c₁ c₂ c₃ c₀ : ℝ) (f₁ f₂ f₃ : Ω → ℝ) :
    E (fun ω ↦ c₁ * f₁ ω + c₂ * f₂ ω + c₃ * f₃ ω + c₀)
      = c₁ * E f₁ + c₂ * E f₂ + c₃ * E f₃ + c₀ := by
  have hsplit : (fun ω ↦ c₁ * f₁ ω + c₂ * f₂ ω + c₃ * f₃ ω + c₀)
      = c₁ • f₁ + c₂ • f₂ + c₃ • f₃ + fun _ : Ω ↦ c₀ := by
    funext ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [hsplit, E.add_eval, E.add_eval, E.add_eval, E.smul_eval, E.smul_eval, E.smul_eval,
    E.eval_const]

/-! ## Convex combinations of outcome laws -/

/-- A mixing weight clamped to `[0, 1]`, so that the combined law below is total. -/
def clamp01 (θ : ℝ) : ℝ := max 0 (min 1 θ)

/-- The clamp is the identity on `[0, 1]`. -/
theorem clamp01_eq {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) : clamp01 θ = θ := by
  unfold clamp01
  rw [min_eq_right h1, max_eq_right h0]

/-- The clamp always lands in `[0, 1]`. -/
theorem clamp01_bounds (θ : ℝ) : 0 ≤ clamp01 θ ∧ clamp01 θ ≤ 1 := by
  refine ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

/-- **The convex combination of two outcome laws**, living on the disjoint union of their
outcome spaces. Every moment constraint is linear in the law, so a combination of two laws
meeting the constraints of UPT (3.2) meets them too. -/
def splitExp {α γ : Type*} (θ : ℝ) (F : ExpFunctional α) (G : ExpFunctional γ) :
    ExpFunctional (α ⊕ γ) where
  eval f := clamp01 θ * F (fun x ↦ f (Sum.inl x))
    + (1 - clamp01 θ) * G (fun y ↦ f (Sum.inr y))
  add_eval f g := by
    show clamp01 θ * F ((fun x ↦ f (Sum.inl x)) + fun x ↦ g (Sum.inl x))
      + (1 - clamp01 θ) * G ((fun y ↦ f (Sum.inr y)) + fun y ↦ g (Sum.inr y)) = _
    rw [F.add_eval, G.add_eval]
    ring
  smul_eval c f := by
    show clamp01 θ * F (c • fun x ↦ f (Sum.inl x))
      + (1 - clamp01 θ) * G (c • fun y ↦ f (Sum.inr y)) = _
    rw [F.smul_eval, G.smul_eval]
    ring
  const_one := by
    show clamp01 θ * F (fun _ ↦ (1 : ℝ)) + (1 - clamp01 θ) * G (fun _ ↦ (1 : ℝ)) = 1
    rw [F.const_one, G.const_one]
    ring
  nonneg_eval f hf := by
    have hb := clamp01_bounds θ
    have h1 : 0 ≤ F (fun x ↦ f (Sum.inl x)) := F.nonneg_eval _ fun x ↦ hf _
    have h2 : 0 ≤ G (fun y ↦ f (Sum.inr y)) := G.nonneg_eval _ fun y ↦ hf _
    have h3 : (0 : ℝ) ≤ 1 - clamp01 θ := by linarith [hb.2]
    have h4 : 0 ≤ clamp01 θ * F (fun x ↦ f (Sum.inl x)) := mul_nonneg hb.1 h1
    have h5 : 0 ≤ (1 - clamp01 θ) * G (fun y ↦ f (Sum.inr y)) := mul_nonneg h3 h2
    show 0 ≤ clamp01 θ * F (fun x ↦ f (Sum.inl x))
      + (1 - clamp01 θ) * G (fun y ↦ f (Sum.inr y))
    linarith

/-- Evaluation of a convex combination at an admissible mixing weight. -/
theorem splitExp_apply {α γ : Type*} {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1)
    (F : ExpFunctional α) (G : ExpFunctional γ) (f : α ⊕ γ → ℝ) :
    splitExp θ F G f
      = θ * F (fun x ↦ f (Sum.inl x)) + (1 - θ) * G (fun y ↦ f (Sum.inr y)) := by
  show clamp01 θ * F (fun x ↦ f (Sum.inl x))
    + (1 - clamp01 θ) * G (fun y ↦ f (Sum.inr y)) = _
  rw [clamp01_eq h0 h1]

/-! ## The symmetric spreading law -/

/-- A spreading weight clamped to `[0, 1/2]`. -/
def spreadWeight (ep : ℝ) : ℝ := max 0 (min (1 / 2) ep)

/-- The spreading weight always lands in `[0, 1/2]`. -/
theorem spreadWeight_bounds (ep : ℝ) : 0 ≤ spreadWeight ep ∧ spreadWeight ep ≤ 1 / 2 := by
  refine ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

/-- The clamp is the identity on `[0, 1/2]`. -/
theorem spreadWeight_eq {ep : ℝ} (h0 : 0 ≤ ep) (h1 : ep ≤ 1 / 2) : spreadWeight ep = ep := by
  unfold spreadWeight
  rw [min_eq_right h1, max_eq_right h0]

/-- The three-point probability vector `(ε, 1 − 2ε, ε)`. -/
def spreadWeights (ep : ℝ) : Fin 3 → ℝ :=
  ![spreadWeight ep, 1 - 2 * spreadWeight ep, spreadWeight ep]

/-- The symmetric three-point spreading law of UPT Step 6. -/
def spreadExp (ep : ℝ) : ExpFunctional (Fin 3) :=
  weightedExp (spreadWeights ep)
    (by
      intro i
      have hb := spreadWeight_bounds ep
      fin_cases i
      · show (0 : ℝ) ≤ spreadWeight ep
        exact hb.1
      · show (0 : ℝ) ≤ 1 - 2 * spreadWeight ep
        linarith [hb.2]
      · show (0 : ℝ) ≤ spreadWeight ep
        exact hb.1)
    (by
      rw [Fin.sum_univ_three]
      show spreadWeight ep + (1 - 2 * spreadWeight ep) + spreadWeight ep = 1
      ring)

/-- The three spreading offsets `−√s`, `0`, `√s`. -/
def spreadOffset (s : ℝ) : Fin 3 → ℝ :=
  ![-Real.sqrt s, 0, Real.sqrt s]

/-- Evaluation of the spreading law at an admissible weight. -/
theorem spreadExp_apply {ep : ℝ} (h0 : 0 ≤ ep) (h1 : ep ≤ 1 / 2) (f : Fin 3 → ℝ) :
    spreadExp ep f = ep * f 0 + (1 - 2 * ep) * f 1 + ep * f 2 := by
  show ∑ i : Fin 3, spreadWeights ep i * f i = _
  rw [Fin.sum_univ_three]
  show spreadWeight ep * f 0 + (1 - 2 * spreadWeight ep) * f 1 + spreadWeight ep * f 2 = _
  rw [spreadWeight_eq h0 h1]

/-- **The spreading law keeps the mean and adds exactly `2εs` to the second moment**, while
its fourth moment grows without bound in the spread scale `s`. -/
theorem spreadExp_moments {ep : ℝ} (h0 : 0 ≤ ep) (h1 : ep ≤ 1 / 2) (s : ℝ) (hs : 0 ≤ s)
    (G : ℝ) :
    spreadExp ep (fun i ↦ G + spreadOffset s i) = G ∧
      spreadExp ep (fun i ↦ (G + spreadOffset s i) ^ 2) = G ^ 2 + 2 * ep * s ∧
      spreadExp ep (fun i ↦ (G + spreadOffset s i) ^ 4)
        = G ^ 4 + 12 * ep * G ^ 2 * s + 2 * ep * s ^ 2 := by
  have hr : Real.sqrt s ^ 2 = s := Real.sq_sqrt hs
  refine ⟨?_, ?_, ?_⟩
  · rw [spreadExp_apply h0 h1]
    show ep * (G + -Real.sqrt s) + (1 - 2 * ep) * (G + 0) + ep * (G + Real.sqrt s) = G
    ring
  · rw [spreadExp_apply h0 h1]
    show ep * (G + -Real.sqrt s) ^ 2 + (1 - 2 * ep) * (G + 0) ^ 2
      + ep * (G + Real.sqrt s) ^ 2 = G ^ 2 + 2 * ep * s
    linear_combination (2 * ep) * hr
  · rw [spreadExp_apply h0 h1]
    show ep * (G + -Real.sqrt s) ^ 4 + (1 - 2 * ep) * (G + 0) ^ 4
      + ep * (G + Real.sqrt s) ^ 4 = G ^ 4 + 12 * ep * G ^ 2 * s + 2 * ep * s ^ 2
    linear_combination (12 * ep * G ^ 2 + 2 * ep * (Real.sqrt s ^ 2 + s)) * hr

/-! ## The mixed outcome kernel and its conditional moments -/

/-- **The outcome kernel of UPT Step 6.** Conditionally on the pre-outcome variable it is
the mixture, with weight `θ`, of the minimal two-point law of UPT (3.12) at the feasible
pair `(b, a)` and the symmetric spread around the forced regression. -/
def rangeKernel (b a : Ω → ℝ) (hab : ∀ ω, b ω ^ 2 ≤ a ω) (θ ep : ℝ) :
    Ω → ExpFunctional (Bool ⊕ Fin 3) :=
  fun ω ↦ splitExp θ (twoPointExp (b ω) (a ω) (hab ω)) (spreadExp ep)

/-- The residual of the mixed kernel: `±√a(W)` on the first component and
`g(W) + offset` on the second. -/
def rangeResidual (a g : Ω → ℝ) (s : ℝ) : Ω × (Bool ⊕ Fin 3) → ℝ :=
  fun z ↦ Sum.elim (fun t ↦ twoPointResidual (a z.1) t)
    (fun i ↦ g z.1 + spreadOffset s i) z.2

/-- **The conditional moments of the mixed kernel.** Each is the convex combination of the
two components' moments, and the fourth moment carries the spread scale `s` linearly. -/
theorem rangeKernel_moments (b a g : Ω → ℝ) (hab : ∀ ω, b ω ^ 2 ≤ a ω) {θ ep : ℝ}
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (h0 : 0 ≤ ep) (h1 : ep ≤ 1 / 2) (s : ℝ) (hs : 0 ≤ s)
    (ω : Ω) :
    condMean (rangeKernel b a hab θ ep) (rangeResidual a g s) ω
        = θ * b ω + (1 - θ) * g ω ∧
      condSecond (rangeKernel b a hab θ ep) (rangeResidual a g s) ω
        = θ * a ω + (1 - θ) * (g ω ^ 2 + 2 * ep * s) ∧
      rangeKernel b a hab θ ep ω (fun ψ ↦ rangeResidual a g s (ω, ψ) ^ 4)
        = θ * a ω ^ 2
          + (1 - θ) * (g ω ^ 4 + 12 * ep * g ω ^ 2 * s + 2 * ep * s ^ 2) := by
  obtain ⟨htp1, htp2, htp4⟩ := twoPointExp_moments (b ω) (a ω) (hab ω)
  obtain ⟨hsp1, hsp2, hsp4⟩ := spreadExp_moments h0 h1 s hs (g ω)
  refine ⟨?_, ?_, ?_⟩
  · show splitExp θ (twoPointExp (b ω) (a ω) (hab ω)) (spreadExp ep)
      (fun ψ ↦ rangeResidual a g s (ω, ψ)) = _
    rw [splitExp_apply hθ0 hθ1]
    show θ * twoPointExp (b ω) (a ω) (hab ω) (twoPointResidual (a ω))
      + (1 - θ) * spreadExp ep (fun i ↦ g ω + spreadOffset s i) = _
    rw [htp1, hsp1]
  · show splitExp θ (twoPointExp (b ω) (a ω) (hab ω)) (spreadExp ep)
      (fun ψ ↦ rangeResidual a g s (ω, ψ) ^ 2) = _
    rw [splitExp_apply hθ0 hθ1]
    show θ * twoPointExp (b ω) (a ω) (hab ω) (fun t ↦ twoPointResidual (a ω) t ^ 2)
      + (1 - θ) * spreadExp ep (fun i ↦ (g ω + spreadOffset s i) ^ 2) = _
    rw [htp2, hsp2]
  · rw [splitExp_apply hθ0 hθ1]
    show θ * twoPointExp (b ω) (a ω) (hab ω) (fun t ↦ twoPointResidual (a ω) t ^ 4)
      + (1 - θ) * spreadExp ep (fun i ↦ (g ω + spreadOffset s i) ^ 4) = _
    rw [htp4, hsp4]

/-! ## The lower half of the range -/

/-- The reduced objective values are bounded below by `m²`. -/
theorem reducedValues_bddBelow (E : ExpFunctional Ω) (X : Ω → ι → ℝ) (β : ℝ) (k : ι → ℝ)
    (m : ℝ) : BddBelow (reducedValues E X β k m) := by
  refine ⟨m ^ 2, ?_⟩
  rintro v ⟨b, a, hab, hb, hk, ha, rfl⟩
  exact second_moment_sq_le E a m ha

/-- **The lower half of UPT (3.10).** The fourth moment of any outcome kernel meeting the
constraints (3.2) is at least `V(β, k, m)`. -/
theorem kernel_fourth_moment_ge_min {Ψ : Type*} (E : ExpFunctional Ω) (X : Ω → ι → ℝ)
    (K : Ω → ExpFunctional Ψ) (res : Ω × Ψ → ℝ) (β : ℝ) (k : ι → ℝ) (m : ℝ)
    (hb : mixture E K res = β)
    (hk : ∀ i, mixture E K (fun z ↦ X z.1 i * res z) = k i)
    (ha : mixture E K (fun z ↦ res z ^ 2) = m) :
    minFourthMoment E X β k m ≤ mixture E K (fun z ↦ res z ^ 4) := by
  have hmem : E (fun ω ↦ condSecond K res ω ^ 2) ∈ reducedValues E X β k m := by
    refine ⟨condMean K res, condSecond K res, fun ω ↦ condMean_sq_le_condSecond K res ω,
      ?_, ?_, ?_, rfl⟩
    · rw [← mixture_mean E K res]
      exact hb
    · intro i
      rw [← mixture_cross E K res X i]
      exact hk i
    · rw [← mixture_second E K res]
      exact ha
  have hle : minFourthMoment E X β k m ≤ E (fun ω ↦ condSecond K res ω ^ 2) :=
    csInf_le (reducedValues_bddBelow E X β k m) hmem
  exact le_trans hle (reduced_objective_le_fourth_moment E K res)

/-! ## The upper half of the range -/

/-- **UPT Theorem 3.1(c): every value above the minimum is attained.** Given a feasible
reduced pair and strict slack `m > β² + ‖k‖²`, every `J` at least that pair's objective is
the exact fourth moment of an explicit outcome kernel satisfying all of (3.2). Applied to a
minimizing pair this says the attainable set contains `[V(β, k, m), ∞)`, which with
`kernel_fourth_moment_ge_min` makes it exactly that interval. -/
theorem attains_every_larger_fourth_moment (E : ExpFunctional Ω) (X : Ω → ι → ℝ)
    (b a : Ω → ℝ) (β : ℝ) (k : ι → ℝ) (m : ℝ)
    (hmean : ∀ i, E (fun ω ↦ X ω i) = 0)
    (horth : ∀ i j, E (fun ω ↦ X ω i * X ω j) = if i = j then 1 else 0)
    (hab : ∀ ω, b ω ^ 2 ≤ a ω) (hb : E b = β)
    (hk : ∀ i, E (fun ω ↦ X ω i * b ω) = k i) (ha : E a = m)
    (hslack : β ^ 2 + dot k k < m) (J : ℝ) (hJ : E (fun ω ↦ a ω ^ 2) ≤ J) :
    ∃ θ ep s : ℝ,
      mixture E (rangeKernel b a hab θ ep)
          (rangeResidual a (featureMean β k X) s) = β ∧
        (∀ i, mixture E (rangeKernel b a hab θ ep)
          (fun z ↦ X z.1 i * rangeResidual a (featureMean β k X) s z) = k i) ∧
        mixture E (rangeKernel b a hab θ ep)
          (fun z ↦ rangeResidual a (featureMean β k X) s z ^ 2) = m ∧
        mixture E (rangeKernel b a hab θ ep)
          (fun z ↦ rangeResidual a (featureMean β k X) s z ^ 4) = J := by
  obtain ⟨hgm, hgc, hgsq⟩ := featureMean_moments E X β k hmean horth
  set g := featureMean β k X with hgdef
  set τ := m - β ^ 2 - dot k k with hτdef
  have hτpos : 0 < τ := by
    rw [hτdef]
    linarith
  set J₀ := E (fun ω ↦ a ω ^ 2) with hJ0def
  set G4 := E (fun ω ↦ g ω ^ 4) with hG4def
  set C₀ := G4 + 6 * τ * (β ^ 2 + dot k k) + τ ^ 2 with hC0def
  set s := τ + (|J - C₀| + 1) / τ with hsdef
  have hextra : 0 < (|J - C₀| + 1) / τ := by positivity
  have hsgt : τ < s := by
    rw [hsdef]
    linarith
  have hspos : 0 < s := lt_trans hτpos hsgt
  set ep := τ / (2 * s) with hepdef
  have hep0 : 0 ≤ ep := by
    rw [hepdef]
    positivity
  have hep1 : ep ≤ 1 / 2 := by
    rw [hepdef, div_le_div_iff₀ (by linarith) (by norm_num)]
    linarith
  have h2eps : 2 * ep * s = τ := by
    rw [hepdef]
    field_simp
  set Fs := G4 + 6 * τ * (β ^ 2 + dot k k) + τ * s with hFsdef
  have hFsval : Fs = C₀ + (|J - C₀| + 1) := by
    rw [hFsdef, hC0def, hsdef]
    field_simp
    ring
  have hFsJ : J + 1 ≤ Fs := by
    rw [hFsval]
    linarith [le_abs_self (J - C₀)]
  have hFsJ0 : J₀ < Fs := by linarith
  set θ := (Fs - J) / (Fs - J₀) with hθdef
  have hdenpos : 0 < Fs - J₀ := by linarith
  have hθ0 : 0 ≤ θ := by
    rw [hθdef]
    apply div_nonneg (by linarith) hdenpos.le
  have hθ1 : θ ≤ 1 := by
    rw [hθdef, div_le_one hdenpos]
    linarith
  refine ⟨θ, ep, s, ?_, ?_, ?_, ?_⟩
  · rw [mixture_mean E (rangeKernel b a hab θ ep)]
    have hfun : condMean (rangeKernel b a hab θ ep) (rangeResidual a g s)
        = fun ω ↦ θ * b ω + (1 - θ) * g ω := by
      funext ω
      exact (rangeKernel_moments b a g hab hθ0 hθ1 hep0 hep1 s hspos.le ω).1
    rw [hfun, eval_lin2 E θ (1 - θ) b g, hb, hgm]
    ring
  · intro i
    rw [mixture_cross E (rangeKernel b a hab θ ep) _ X i]
    have hfun : (fun ω ↦ X ω i * condMean (rangeKernel b a hab θ ep)
        (rangeResidual a g s) ω)
        = fun ω ↦ θ * (X ω i * b ω) + (1 - θ) * (X ω i * g ω) := by
      funext ω
      rw [(rangeKernel_moments b a g hab hθ0 hθ1 hep0 hep1 s hspos.le ω).1]
      ring
    rw [hfun, eval_lin2 E θ (1 - θ) (fun ω ↦ X ω i * b ω) (fun ω ↦ X ω i * g ω), hk i,
      hgc i]
    ring
  · rw [mixture_second E (rangeKernel b a hab θ ep)]
    have hfun : condSecond (rangeKernel b a hab θ ep) (rangeResidual a g s)
        = fun ω ↦ θ * a ω + (1 - θ) * (g ω ^ 2) + 0 * (g ω ^ 2)
          + (1 - θ) * (2 * ep * s) := by
      funext ω
      rw [(rangeKernel_moments b a g hab hθ0 hθ1 hep0 hep1 s hspos.le ω).2.1]
      ring
    rw [hfun, eval_lin3_const E θ (1 - θ) 0 ((1 - θ) * (2 * ep * s)) a
      (fun ω ↦ g ω ^ 2) (fun ω ↦ g ω ^ 2), ha, hgsq, h2eps]
    rw [hτdef]
    ring
  · show E (fun ω ↦ rangeKernel b a hab θ ep ω
      (fun ψ ↦ rangeResidual a g s (ω, ψ) ^ 4)) = J
    have hfun : (fun ω ↦ rangeKernel b a hab θ ep ω
        (fun ψ ↦ rangeResidual a g s (ω, ψ) ^ 4))
        = fun ω ↦ θ * (a ω ^ 2) + (1 - θ) * (g ω ^ 4)
          + ((1 - θ) * (12 * ep * s)) * (g ω ^ 2) + (1 - θ) * (2 * ep * s ^ 2) := by
      funext ω
      rw [(rangeKernel_moments b a g hab hθ0 hθ1 hep0 hep1 s hspos.le ω).2.2]
      ring
    rw [hfun, eval_lin3_const E θ (1 - θ) ((1 - θ) * (12 * ep * s))
      ((1 - θ) * (2 * ep * s ^ 2)) (fun ω ↦ a ω ^ 2) (fun ω ↦ g ω ^ 4)
      (fun ω ↦ g ω ^ 2), hgsq]
    have h12 : 12 * ep * s = 6 * τ := by linarith [h2eps]
    have h2s : 2 * ep * s ^ 2 = τ * s := by
      have : 2 * ep * s ^ 2 = (2 * ep * s) * s := by ring
      rw [this, h2eps]
    rw [h12, h2s, ← hJ0def, ← hG4def]
    have hmix : θ * J₀ + (1 - θ) * Fs = J := by
      rw [hθdef]
      field_simp
      ring
    rw [hFsdef] at hmix
    linarith [hmix]

end

end Descent.Portability.FourthMomentAttainableRange
