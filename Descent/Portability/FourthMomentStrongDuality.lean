/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.GlobalFourthMomentRegion

assert_below Descent.Decision Descent.Program

/-!
# No duality gap for a finitely supported feature law

UPT Theorem 3.1(b) claims the supremum of the dual (3.8) equals the primal minimum
`V(β, k, m)`, and argues it in Step 5 by separating a point from the closed convex epigraph
of the value function. `GlobalFourthMomentRegion` proves weak duality for an arbitrary law
and no gap at any certified point. This module closes the gap unconditionally for a
finitely supported pre-outcome law at any triple strictly inside the feasible region,
`m > β² + ‖k‖²`, which is the manuscript's Slater point.

The construction is the manuscript's, with one change that removes the need to prove the
epigraph closed. `attainableSet` is the set of moment vectors `(E b, E[X b], E a, t)` with
`a ≥ b²` and `t ≥ E[a²]`, convex because the constraint `a ≥ b²` and the objective `E[a²]`
are both convex. A point `(β, k, m, V − ε)` lies outside it. Rather than separating from
the set itself, we separate from its interior, which is open and convex; the interior is
nonempty because the explicit slack pair of UPT Step 1 realizes an entire open region, and
a segment argument carries the resulting inequality back to the whole set. The coefficient
of the objective coordinate is nonzero because the separating functional must distinguish
two points that differ only in that coordinate, so the multipliers can be normalized. The
quartic maximum of (3.7) is attained (`FourthMomentDuality.exists_quartic_argmax`), so
`E Φ` is itself the value of a feasible pair, which converts the separation into the dual
bound.

* `exists_near_optimal_multipliers` is the `ε` form: multipliers whose dual value exceeds
  `V − ε`.
* `dual_sup_eq_minFourthMoment` is UPT (3.8) itself: the supremum over all multipliers
  equals `V(β, k, m)`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.FourthMomentStrongDuality

open Foundations IndividualLossMoments FourthMomentDuality GlobalFourthMomentRegion

noncomputable section

variable {Ω : Type*} [Fintype Ω] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## The attainable moment set -/

/-- The moment vector `(β, k, m, t)` in the coordinates the dual uses. -/
def momentVector (β : ℝ) (k : ι → ℝ) (m t : ℝ) : Option ι ⊕ Bool → ℝ
  | Sum.inl none => β
  | Sum.inl (some i) => k i
  | Sum.inr false => m
  | Sum.inr true => t

/-- The attainable set of UPT Step 5: moment vectors of feasible conditional-moment pairs,
thickened upward in the objective coordinate. -/
def attainableSet (E : ExpFunctional Ω) (X : Ω → ι → ℝ) :
    Set (Option ι ⊕ Bool → ℝ) :=
  {v | ∃ b a : Ω → ℝ, (∀ ω, b ω ^ 2 ≤ a ω) ∧ v (Sum.inl none) = E b ∧
    (∀ i, v (Sum.inl (some i)) = E (fun ω ↦ X ω i * b ω)) ∧ v (Sum.inr false) = E a ∧
    E (fun ω ↦ a ω ^ 2) ≤ v (Sum.inr true)}

omit [Fintype Ω] [Fintype ι] [DecidableEq ι] in
/-- Linearity of an expectation on a convex combination. -/
theorem eval_convex_comb (E : ExpFunctional Ω) (s t : ℝ) (f g : Ω → ℝ) :
    E (fun ω ↦ s * f ω + t * g ω) = s * E f + t * E g := by
  have hsplit : (fun ω ↦ s * f ω + t * g ω) = s • f + t • g := by
    funext ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [hsplit, E.add_eval, E.smul_eval, E.smul_eval]

omit [Fintype Ω] [Fintype ι] [DecidableEq ι] in
/-- **The attainable set is convex.** Mixing two conditional-moment pairs keeps `a ≥ b²`
because the square is convex, and the objective `E[a²]` is convex for the same reason, so
the upward thickening absorbs the deficit. -/
theorem convex_attainableSet (E : ExpFunctional Ω) (X : Ω → ι → ℝ) :
    Convex ℝ (attainableSet E X) := by
  rintro v ⟨b, a, hab, h1, h2, h3, h4⟩ w ⟨b', a', hab', h1', h2', h3', h4'⟩ s t hs ht hst
  refine ⟨fun ω ↦ s * b ω + t * b' ω, fun ω ↦ s * a ω + t * a' ω, ?_, ?_, ?_, ?_, ?_⟩
  · intro ω
    nlinarith [hab ω, hab' ω, mul_nonneg (mul_nonneg hs ht) (sq_nonneg (b ω - b' ω))]
  · show s * v (Sum.inl none) + t * w (Sum.inl none) = _
    rw [h1, h1', eval_convex_comb]
  · intro i
    show s * v (Sum.inl (some i)) + t * w (Sum.inl (some i)) = _
    rw [h2 i, h2' i]
    have hfun : (fun ω ↦ X ω i * (s * b ω + t * b' ω))
        = fun ω ↦ s * (X ω i * b ω) + t * (X ω i * b' ω) := by
      funext ω
      ring
    rw [hfun, eval_convex_comb]
  · show s * v (Sum.inr false) + t * w (Sum.inr false) = _
    rw [h3, h3', eval_convex_comb]
  · show E (fun ω ↦ (s * a ω + t * a' ω) ^ 2)
      ≤ s * v (Sum.inr true) + t * w (Sum.inr true)
    have hmono : E (fun ω ↦ (s * a ω + t * a' ω) ^ 2)
        ≤ E (fun ω ↦ s * a ω ^ 2 + t * a' ω ^ 2) := by
      refine E.eval_mono fun ω ↦ ?_
      nlinarith [mul_nonneg (mul_nonneg hs ht) (sq_nonneg (a ω - a' ω))]
    rw [eval_convex_comb] at hmono
    have hs4 : s * E (fun ω ↦ a ω ^ 2) ≤ s * v (Sum.inr true) :=
      mul_le_mul_of_nonneg_left h4 hs
    have ht4 : t * E (fun ω ↦ a' ω ^ 2) ≤ t * w (Sum.inr true) :=
      mul_le_mul_of_nonneg_left h4' ht
    linarith

omit [Fintype Ω] in
/-- A point of the attainable set bounds `V(β, k, m)` from above. -/
theorem minFourthMoment_le_of_mem (E : ExpFunctional Ω) (X : Ω → ι → ℝ) (β : ℝ)
    (k : ι → ℝ) (m t : ℝ) (hmem : momentVector β k m t ∈ attainableSet E X) :
    minFourthMoment E X β k m ≤ t := by
  obtain ⟨b, a, hab, h1, h2, h3, h4⟩ := hmem
  have hb : E b = β := h1.symm
  have hk : ∀ i, E (fun ω ↦ X ω i * b ω) = k i := fun i ↦ (h2 i).symm
  have ha : E a = m := h3.symm
  refine le_trans (csInf_le ⟨m ^ 2, ?_⟩ ⟨b, a, hab, hb, hk, ha, rfl⟩) h4
  rintro u ⟨b', a', hab', hb', hk', ha', rfl⟩
  exact second_moment_sq_le E a' m ha'

/-! ## The interior is nonempty -/

/-- The objective value of the explicit slack pair of UPT Step 1. -/
def slackValue (E : ExpFunctional Ω) (X : Ω → ι → ℝ) (β : ℝ) (k : ι → ℝ) (m : ℝ) : ℝ :=
  E (fun ω ↦ slackSecond β k X m ω ^ 2)

/-- The open region on which the slack pair already witnesses membership. -/
def slackRegion (E : ExpFunctional Ω) (X : Ω → ι → ℝ) : Set (Option ι ⊕ Bool → ℝ) :=
  {v | v (Sum.inl none) ^ 2 + dot (fun i ↦ v (Sum.inl (some i)))
        (fun i ↦ v (Sum.inl (some i))) < v (Sum.inr false) ∧
    slackValue E X (v (Sum.inl none)) (fun i ↦ v (Sum.inl (some i)))
      (v (Sum.inr false)) < v (Sum.inr true)}

/-- The slack region sits inside the attainable set. -/
theorem slackRegion_subset (E : ExpFunctional Ω) (X : Ω → ι → ℝ)
    (hmean : ∀ i, E (fun ω ↦ X ω i) = 0)
    (horth : ∀ i j, E (fun ω ↦ X ω i * X ω j) = if i = j then 1 else 0) :
    slackRegion E X ⊆ attainableSet E X := by
  rintro v ⟨hfeas, hval⟩
  obtain ⟨hpt, hb, hk, ha⟩ := slackPair_feasible E X (v (Sum.inl none))
    (fun i ↦ v (Sum.inl (some i))) (v (Sum.inr false)) hmean horth (le_of_lt hfeas)
  exact ⟨featureMean (v (Sum.inl none)) (fun i ↦ v (Sum.inl (some i))) X,
    slackSecond (v (Sum.inl none)) (fun i ↦ v (Sum.inl (some i))) X (v (Sum.inr false)),
    hpt, hb.symm, fun i ↦ (hk i).symm, ha.symm, le_of_lt hval⟩

/-- The slack value is a polynomial in the prescribed moments, hence continuous in them. -/
theorem continuous_slackValue (E : ExpFunctional Ω) (p : Ω → ℝ)
    (hE : ∀ f : Ω → ℝ, E f = ∑ ω, p ω * f ω) (X : Ω → ι → ℝ) :
    Continuous fun v : Option ι ⊕ Bool → ℝ ↦
      slackValue E X (v (Sum.inl none)) (fun i ↦ v (Sum.inl (some i)))
        (v (Sum.inr false)) := by
  have hfun : (fun v : Option ι ⊕ Bool → ℝ ↦
      slackValue E X (v (Sum.inl none)) (fun i ↦ v (Sum.inl (some i)))
        (v (Sum.inr false)))
      = fun v ↦ ∑ ω, p ω *
        (((v (Sum.inl none) + ∑ i, v (Sum.inl (some i)) * X ω i) ^ 2
          + (v (Sum.inr false) - v (Sum.inl none) ^ 2
            - ∑ i, v (Sum.inl (some i)) * v (Sum.inl (some i)))) ^ 2) := by
    funext v
    unfold slackValue slackSecond featureMean
    rw [hE]
    simp only [dot, Descent.Core.innerSum]
  rw [hfun]
  fun_prop

/-- The slack region is open. -/
theorem isOpen_slackRegion (E : ExpFunctional Ω) (p : Ω → ℝ)
    (hE : ∀ f : Ω → ℝ, E f = ∑ ω, p ω * f ω) (X : Ω → ι → ℝ) :
    IsOpen (slackRegion E X) := by
  have h1 : IsOpen {v : Option ι ⊕ Bool → ℝ | v (Sum.inl none) ^ 2
      + dot (fun i ↦ v (Sum.inl (some i))) (fun i ↦ v (Sum.inl (some i)))
      < v (Sum.inr false)} := by
    refine isOpen_lt ?_ (continuous_apply _)
    have hfun : (fun v : Option ι ⊕ Bool → ℝ ↦ v (Sum.inl none) ^ 2
        + dot (fun i ↦ v (Sum.inl (some i))) (fun i ↦ v (Sum.inl (some i))))
        = fun v ↦ v (Sum.inl none) ^ 2
          + ∑ i, v (Sum.inl (some i)) * v (Sum.inl (some i)) := by
      funext v
      simp only [dot, Descent.Core.innerSum]
    rw [hfun]
    fun_prop
  have h2 : IsOpen {v : Option ι ⊕ Bool → ℝ |
      slackValue E X (v (Sum.inl none)) (fun i ↦ v (Sum.inl (some i)))
        (v (Sum.inr false)) < v (Sum.inr true)} :=
    isOpen_lt (continuous_slackValue E p hE X) (continuous_apply _)
  exact h1.inter h2

/-! ## Coordinates of a separating functional -/

omit [Fintype Ω] in
/-- The moment vector is the corresponding combination of coordinate spikes. -/
theorem momentVector_decomp (β : ℝ) (k : ι → ℝ) (m t : ℝ) :
    momentVector β k m t
      = β • Pi.single (Sum.inl none) (1 : ℝ)
        + ((∑ i, k i • Pi.single (Sum.inl (some i)) (1 : ℝ))
          + (m • Pi.single (Sum.inr false) (1 : ℝ)
            + t • Pi.single (Sum.inr true) (1 : ℝ))) := by
  funext j
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_apply, Pi.single_apply]
  rcases j with j | c
  · rcases j with _ | i
    · simp [momentVector]
    · simp [momentVector, Finset.sum_ite_eq]
  · cases c
    · simp [momentVector]
    · simp [momentVector]

omit [Fintype Ω] in
/-- **A continuous linear functional in the manuscript's coordinates.** -/
theorem apply_momentVector (f : ((Option ι ⊕ Bool) → ℝ) →L[ℝ] ℝ) (β : ℝ) (k : ι → ℝ)
    (m t : ℝ) :
    f (momentVector β k m t)
      = β * f (Pi.single (Sum.inl none) (1 : ℝ))
        + (∑ i, k i * f (Pi.single (Sum.inl (some i)) (1 : ℝ)))
        + m * f (Pi.single (Sum.inr false) (1 : ℝ))
        + t * f (Pi.single (Sum.inr true) (1 : ℝ)) := by
  rw [momentVector_decomp, map_add, map_add, map_add, map_smul, map_smul, map_smul,
    map_sum]
  simp only [map_smul, smul_eq_mul]
  ring

/-! ## Strong duality -/

/-- **No duality gap, in `ε` form.** For a finitely supported law at a triple strictly
inside the feasible region there are multipliers whose dual value exceeds `V − ε`. -/
theorem exists_near_optimal_multipliers (E : ExpFunctional Ω) (p : Ω → ℝ)
    (hE : ∀ f : Ω → ℝ, E f = ∑ ω, p ω * f ω) (X : Ω → ι → ℝ) (β : ℝ) (k : ι → ℝ) (m : ℝ)
    (hmean : ∀ i, E (fun ω ↦ X ω i) = 0)
    (horth : ∀ i j, E (fun ω ↦ X ω i * X ω j) = if i = j then 1 else 0)
    (hslater : β ^ 2 + dot k k < m) (ε : ℝ) (hε : 0 < ε) :
    ∃ (lam0 : ℝ) (lam : ι → ℝ) (r : ℝ),
      minFourthMoment E X β k m - ε ≤ dualObjective E X β k m lam0 lam r := by
  set A := attainableSet E X with hAdef
  have hA : Convex ℝ A := convex_attainableSet E X
  set V := minFourthMoment E X β k m with hVdef
  set T := slackValue E X β k m + 1 with hTdef
  set y₀ := momentVector β k m (V - ε) with hy₀
  set y₁ := momentVector β k m T with hy₁
  -- the separated point is outside the attainable set
  have hy₀not : y₀ ∉ A := by
    intro hmem
    have := minFourthMoment_le_of_mem E X β k m (V - ε) hmem
    rw [← hVdef] at this
    linarith
  -- the slack region is an open subset of the attainable set containing `y₁`
  have hsub : slackRegion E X ⊆ A := slackRegion_subset E X hmean horth
  have hopen : IsOpen (slackRegion E X) := isOpen_slackRegion E p hE X
  have hy₁mem : y₁ ∈ slackRegion E X := by
    constructor
    · show momentVector β k m T (Sum.inl none) ^ 2
        + dot (fun i ↦ momentVector β k m T (Sum.inl (some i)))
          (fun i ↦ momentVector β k m T (Sum.inl (some i)))
        < momentVector β k m T (Sum.inr false)
      exact hslater
    · show slackValue E X β k m < T
      rw [hTdef]
      linarith
  have hy₁int : y₁ ∈ interior A := by
    have hmono : interior (slackRegion E X) ⊆ interior A := interior_mono hsub
    rw [hopen.interior_eq] at hmono
    exact hmono hy₁mem
  have hy₀notint : y₀ ∉ interior A := fun h ↦ hy₀not (interior_subset h)
  obtain ⟨f, hsep⟩ :=
    geometric_hahn_banach_open_point hA.interior isOpen_interior hy₀notint
  have hy₁lt : f y₁ < f y₀ := hsep y₁ hy₁int
  -- the objective coefficient is nonzero
  set c : ℝ := f (Pi.single (Sum.inr true) (1 : ℝ)) with hc
  have hcoef : ∀ s t : ℝ, f (momentVector β k m t) - f (momentVector β k m s)
      = (t - s) * c := by
    intro s t
    rw [apply_momentVector, apply_momentVector, ← hc]
    ring
  have hcne : c ≠ 0 := by
    intro h0
    have := hcoef (V - ε) T
    rw [h0, mul_zero] at this
    rw [← hy₀, ← hy₁] at this
    linarith
  -- the separation extends from the interior to the whole set
  have hall : ∀ v ∈ A, f v ≤ f y₀ := by
    intro v hv
    by_contra hcon
    push_neg at hcon
    rcases le_or_lt (f v) (f y₁) with hC | hC
    · linarith
    · set s : ℝ := min 1 ((f v - f y₀) / (2 * (f v - f y₁))) with hs
      have hpos : 0 < (f v - f y₀) / (2 * (f v - f y₁)) := by
        apply div_pos (by linarith)
        linarith
      have hs0 : 0 < s := lt_min one_pos hpos
      have hs1 : s ≤ 1 := min_le_left _ _
      have hmem := hA.combo_interior_self_mem_interior hy₁int hv hs0
        (by linarith : (0 : ℝ) ≤ 1 - s) (by ring)
      have hlt := hsep _ hmem
      rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul] at hlt
      have hsC : s * (f v - f y₁) ≤ (f v - f y₀) / 2 := by
        have h1 : s ≤ (f v - f y₀) / (2 * (f v - f y₁)) := min_le_right _ _
        have h2 : (f v - f y₀) / (2 * (f v - f y₁)) * (f v - f y₁)
            = (f v - f y₀) / 2 := by
          field_simp
        calc s * (f v - f y₁)
            ≤ (f v - f y₀) / (2 * (f v - f y₁)) * (f v - f y₁) :=
              mul_le_mul_of_nonneg_right h1 (by linarith)
          _ = (f v - f y₀) / 2 := h2
      linarith
  -- normalize the multipliers
  have hcneg : c < 0 := by
    rcases lt_or_gt_of_ne hcne with h | h
    · exact h
    · exfalso
      have hmemT : ∀ s : ℝ, T ≤ s → momentVector β k m s ∈ A := by
        intro s hs
        refine hsub ⟨?_, ?_⟩
        · show β ^ 2 + dot k k < m
          exact hslater
        · show slackValue E X β k m < s
          rw [hTdef] at hs
          linarith
      have hbig := hall _ (hmemT (T + (f y₀ - f y₁ + 1) / c) (by positivity))
      have := hcoef T (T + (f y₀ - f y₁ + 1) / c)
      rw [← hy₁] at this
      have hfield : (T + (f y₀ - f y₁ + 1) / c - T) * c = f y₀ - f y₁ + 1 := by
        field_simp
      rw [hfield] at this
      linarith
  set lam0 : ℝ := f (Pi.single (Sum.inl none) (1 : ℝ)) / (-c) with hlam0
  set lam : ι → ℝ := fun i ↦ f (Pi.single (Sum.inl (some i)) (1 : ℝ)) / (-c) with hlam
  set r : ℝ := f (Pi.single (Sum.inr false) (1 : ℝ)) / (-c) with hr
  refine ⟨lam0, lam, r, ?_⟩
  -- the separation as an inequality on feasible pairs
  have hpair : ∀ b a : Ω → ℝ, (∀ ω, b ω ^ 2 ≤ a ω) →
      lam0 * E b + dot lam (fun i ↦ E (fun ω ↦ X ω i * b ω)) + r * E a
        - E (fun ω ↦ a ω ^ 2) ≤ lam0 * β + dot lam k + r * m - (V - ε) := by
    intro b a hab
    have hmem : momentVector (E b) (fun i ↦ E (fun ω ↦ X ω i * b ω)) (E a)
        (E (fun ω ↦ a ω ^ 2)) ∈ A := ⟨b, a, hab, rfl, fun i ↦ rfl, rfl, le_rfl⟩
    have hle := hall _ hmem
    rw [apply_momentVector, ← hy₀, hy₀, apply_momentVector] at hle
    have hcpos : 0 < -c := by linarith
    rw [hlam0, hr]
    have hdotlam : ∀ u : ι → ℝ, dot lam u
        = (∑ i, u i * f (Pi.single (Sum.inl (some i)) (1 : ℝ))) / (-c) := by
      intro u
      simp only [dot, Descent.Core.innerSum, hlam]
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun i _ ↦ by ring
    rw [hdotlam, hdotlam]
    rw [div_add_div_same, div_add_div_same, sub_le_iff_le_add, div_add' _ _ _ (ne_of_gt hcpos),
      div_add' _ _ _ (ne_of_gt hcpos), div_le_div_iff_of_pos_right hcpos]
    nlinarith [hle, hcpos]
  -- turn the pointwise quartic maximum into such a pair
  have hchoice : ∀ ω : Ω, ∃ e : ℝ, ∀ e' : ℝ,
      (lam0 + dot lam (X ω)) * e' + r * e' ^ 2 - e' ^ 4
        ≤ (lam0 + dot lam (X ω)) * e + r * e ^ 2 - e ^ 4 :=
    fun ω ↦ exists_quartic_argmax (lam0 + dot lam (X ω)) r
  choose eStar hStar using hchoice
  have hphi : ∀ ω, quarticMax (lam0 + dot lam (X ω)) r
      = (lam0 + dot lam (X ω)) * eStar ω + r * eStar ω ^ 2 - eStar ω ^ 4 :=
    fun ω ↦ quarticMax_eq_of_max (hStar ω)
  have hab : ∀ ω, eStar ω ^ 2 ≤ eStar ω ^ 2 := fun ω ↦ le_rfl
  have hlin := eval_affine_form E X eStar lam0 lam
  have hkey := hpair eStar (fun ω ↦ eStar ω ^ 2) hab
  have hsq : (fun ω ↦ (eStar ω ^ 2) ^ 2) = fun ω ↦ eStar ω ^ 4 := by
    funext ω
    ring
  rw [hsq] at hkey
  have hPhi : E (fun ω ↦ quarticMax (lam0 + dot lam (X ω)) r)
      = E (fun ω ↦ (lam0 + dot lam (X ω)) * eStar ω)
        + r * E (fun ω ↦ eStar ω ^ 2) - E (fun ω ↦ eStar ω ^ 4) := by
    have hfun : (fun ω ↦ quarticMax (lam0 + dot lam (X ω)) r)
        = fun ω ↦ (lam0 + dot lam (X ω)) * eStar ω + r * eStar ω ^ 2 - eStar ω ^ 4 :=
      funext hphi
    rw [hfun, eval_comb E _ (fun ω ↦ eStar ω ^ 2) (fun ω ↦ eStar ω ^ 4) r]
  unfold dualObjective
  rw [hPhi, hlin]
  linarith [hkey]

/-- **UPT (3.8): the dual supremum equals the primal minimum.** -/
theorem dual_sup_eq_minFourthMoment (E : ExpFunctional Ω) (p : Ω → ℝ)
    (hE : ∀ f : Ω → ℝ, E f = ∑ ω, p ω * f ω) (X : Ω → ι → ℝ) (β : ℝ) (k : ι → ℝ) (m : ℝ)
    (hmean : ∀ i, E (fun ω ↦ X ω i) = 0)
    (horth : ∀ i j, E (fun ω ↦ X ω i * X ω j) = if i = j then 1 else 0)
    (hslater : β ^ 2 + dot k k < m) :
    sSup {u : ℝ | ∃ (lam0 : ℝ) (lam : ι → ℝ) (r : ℝ),
        u = dualObjective E X β k m lam0 lam r}
      = minFourthMoment E X β k m := by
  have hne : (reducedValues E X β k m).Nonempty :=
    reducedValues_nonempty E X β k m hmean horth (le_of_lt hslater)
  have hupper : ∀ u ∈ {u : ℝ | ∃ (lam0 : ℝ) (lam : ι → ℝ) (r : ℝ),
      u = dualObjective E X β k m lam0 lam r}, u ≤ minFourthMoment E X β k m := by
    rintro u ⟨lam0, lam, r, rfl⟩
    refine le_csInf hne ?_
    rintro w ⟨b, a, hab, hb, hk, ha, rfl⟩
    exact dualObjective_le E X b a β k m lam0 lam r hab hb hk ha
  have hsetne : {u : ℝ | ∃ (lam0 : ℝ) (lam : ι → ℝ) (r : ℝ),
      u = dualObjective E X β k m lam0 lam r}.Nonempty :=
    ⟨dualObjective E X β k m 0 (fun _ ↦ 0) 0, 0, fun _ ↦ 0, 0, rfl⟩
  refine le_antisymm (csSup_le hsetne hupper) ?_
  by_contra hcon
  push_neg at hcon
  set S := sSup {u : ℝ | ∃ (lam0 : ℝ) (lam : ι → ℝ) (r : ℝ),
    u = dualObjective E X β k m lam0 lam r} with hS
  obtain ⟨lam0, lam, r, hlt⟩ := exists_near_optimal_multipliers E p hE X β k m hmean horth
    hslater (minFourthMoment E X β k m - S) (by linarith)
  have hmem : dualObjective E X β k m lam0 lam r ∈ {u : ℝ | ∃ (lam0 : ℝ) (lam : ι → ℝ)
      (r : ℝ), u = dualObjective E X β k m lam0 lam r} := ⟨lam0, lam, r, rfl⟩
  have hle : dualObjective E X β k m lam0 lam r ≤ S :=
    le_csSup ⟨minFourthMoment E X β k m, hupper⟩ hmem
  linarith

end

end Descent.Portability.FourthMomentStrongDuality
