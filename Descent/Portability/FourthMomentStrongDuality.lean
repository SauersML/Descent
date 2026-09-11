/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.GlobalFourthMomentRegion

assert_below Descent.Decision Descent.Program

/-!
# No duality gap for a finitely supported feature law

UPT Theorem 3.1(b) claims the supremum of the dual (3.8) equals the primal minimum
`V(β, k, m)`, and argues it in Step 5 by separating a point from the closed convex epigraph
of the value function. `GlobalFourthMomentRegion` proves weak duality for an arbitrary law,
and no gap at any certified point. This module closes the gap unconditionally for a
finitely supported pre-outcome law at any triple strictly inside the feasible region,
`m > β² + ‖k‖²`, which is the manuscript's Slater point.

The construction is the manuscript's, with one change that removes the need to prove the
epigraph closed. `attainableSet` is the set of moment vectors `(E b, E[X b], E a, t)` with
`a ≥ b²` and `t ≥ E[a²]`; it is convex because the constraint `a ≥ b²` and the objective
`E[a²]` are both convex, the slack `s t (b − b')²` being exactly what the upward thickening
absorbs. The point `(β, k, m, V − ε)` lies outside it. Rather than separating from the set,
we separate from its interior, which is open and convex; the interior is nonempty because
the explicit slack pair of UPT Step 1 realizes an entire open region, and a segment
argument carries the resulting inequality back to the whole set. The coefficient of the
objective coordinate cannot vanish, because the separating functional must distinguish two
points differing only in that coordinate, and cannot be positive, because the set contains
an upward ray; so rescaling the functional makes that coefficient exactly `−1` and the
separation becomes the dual inequality verbatim. Finally the quartic maximum of (3.7) is
attained (`FourthMomentDuality.exists_quartic_argmax`), so `E Φ` is itself the value of a
feasible pair, which is what turns the separation into a bound on the dual objective.

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

/-- The unit spike at one coordinate of the moment space. -/
def spike (j : Option ι ⊕ Bool) : (Option ι ⊕ Bool) → ℝ := Pi.single j 1

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
/-- The mixing defect of the square: `s x² + t y² − (s x + t y)² = s t (x − y)²`. -/
theorem convex_comb_sq (s t x y : ℝ) (hst : s + t = 1) :
    s * x ^ 2 + t * y ^ 2 - (s * x + t * y) ^ 2 = s * t * (x - y) ^ 2 := by
  have hts : t = 1 - s := by linarith
  rw [hts]
  ring

omit [Fintype Ω] [Fintype ι] [DecidableEq ι] in
/-- **The attainable set is convex.** Mixing two conditional-moment pairs keeps `a ≥ b²`
because the square is convex, and raises `E[a²]` by no more than the mixture of the two
values, which the upward thickening absorbs. -/
theorem convex_attainableSet (E : ExpFunctional Ω) (X : Ω → ι → ℝ) :
    Convex ℝ (attainableSet E X) := by
  rintro v ⟨b, a, hab, h1, h2, h3, h4⟩ w ⟨b', a', hab', h1', h2', h3', h4'⟩ s t hs ht hst
  refine ⟨fun ω ↦ s * b ω + t * b' ω, fun ω ↦ s * a ω + t * a' ω, ?_, ?_, ?_, ?_, ?_⟩
  · intro ω
    have hkey := convex_comb_sq s t (b ω) (b' ω) hst
    have hnn : 0 ≤ s * t * (b ω - b' ω) ^ 2 :=
      mul_nonneg (mul_nonneg hs ht) (sq_nonneg _)
    have hb1 : s * b ω ^ 2 ≤ s * a ω := mul_le_mul_of_nonneg_left (hab ω) hs
    have hb2 : t * b' ω ^ 2 ≤ t * a' ω := mul_le_mul_of_nonneg_left (hab' ω) ht
    linarith
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
      have hkey := convex_comb_sq s t (a ω) (a' ω) hst
      have hnn : 0 ≤ s * t * (a ω - a' ω) ^ 2 :=
        mul_nonneg (mul_nonneg hs ht) (sq_nonneg _)
      linarith
    rw [eval_convex_comb] at hmono
    have hs4 : s * E (fun ω ↦ a ω ^ 2) ≤ s * v (Sum.inr true) :=
      mul_le_mul_of_nonneg_left h4 hs
    have ht4 : t * E (fun ω ↦ a' ω ^ 2) ≤ t * w (Sum.inr true) :=
      mul_le_mul_of_nonneg_left h4' ht
    linarith

omit [Fintype Ω] [Fintype ι] [DecidableEq ι] in
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

omit [Fintype Ω] in
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

omit [DecidableEq ι] in
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

omit [DecidableEq ι] in
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
      = β • spike (Sum.inl none) + ((∑ i, k i • spike (Sum.inl (some i)))
          + (m • spike (Sum.inr false) + t • spike (Sum.inr true))) := by
  funext j
  simp only [spike, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_apply,
    Pi.single_apply]
  rcases j with j | c
  · rcases j with _ | i
    · simp [momentVector]
    · simp [momentVector, Finset.sum_ite_eq]
  · cases c
    · simp [momentVector]
    · simp [momentVector]

omit [Fintype Ω] in
/-- **A continuous linear functional read in the manuscript's coordinates.** -/
theorem apply_momentVector (f : ((Option ι ⊕ Bool) → ℝ) →L[ℝ] ℝ) (β : ℝ) (k : ι → ℝ)
    (m t : ℝ) :
    f (momentVector β k m t)
      = β * f (spike (Sum.inl none)) + (∑ i, k i * f (spike (Sum.inl (some i))))
        + m * f (spike (Sum.inr false)) + t * f (spike (Sum.inr true)) := by
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
  have hA : Convex ℝ (attainableSet E X) := convex_attainableSet E X
  set V := minFourthMoment E X β k m with hVdef
  set T := slackValue E X β k m + 1 with hTdef
  set y₀ := momentVector β k m (V - ε) with hy₀
  set y₁ := momentVector β k m T with hy₁
  have hy₀not : y₀ ∉ attainableSet E X := by
    intro hmem
    have hle := minFourthMoment_le_of_mem E X β k m (V - ε) hmem
    rw [← hVdef] at hle
    linarith
  have hsub : slackRegion E X ⊆ attainableSet E X := slackRegion_subset E X hmean horth
  have hopen : IsOpen (slackRegion E X) := isOpen_slackRegion E p hE X
  have hmemT : ∀ s : ℝ, T ≤ s → momentVector β k m s ∈ attainableSet E X := by
    intro s hs
    refine hsub ⟨?_, ?_⟩
    · show β ^ 2 + dot k k < m
      exact hslater
    · show slackValue E X β k m < s
      rw [hTdef] at hs
      linarith
  have hy₁mem : y₁ ∈ slackRegion E X := by
    refine ⟨?_, ?_⟩
    · show β ^ 2 + dot k k < m
      exact hslater
    · show slackValue E X β k m < T
      rw [hTdef]
      linarith
  have hy₁int : y₁ ∈ interior (attainableSet E X) := by
    have hmono := interior_mono hsub
    rw [hopen.interior_eq] at hmono
    exact hmono hy₁mem
  have hy₀notint : y₀ ∉ interior (attainableSet E X) := fun h ↦ hy₀not (interior_subset h)
  obtain ⟨f, hsep⟩ :=
    geometric_hahn_banach_open_point hA.interior isOpen_interior hy₀notint
  have hy₁lt : f y₁ < f y₀ := hsep y₁ hy₁int
  set c : ℝ := f (spike (Sum.inr true)) with hc
  have hcoef : ∀ s t : ℝ, f (momentVector β k m t) - f (momentVector β k m s)
      = (t - s) * c := by
    intro s t
    rw [apply_momentVector, apply_momentVector, ← hc]
    ring
  have hcne : c ≠ 0 := by
    intro h0
    have hgap := hcoef (V - ε) T
    rw [h0, mul_zero, ← hy₀, ← hy₁] at hgap
    linarith
  have hall : ∀ v ∈ attainableSet E X, f v ≤ f y₀ := by
    intro v hv
    by_contra hcon
    push_neg at hcon
    rcases le_or_gt (f v) (f y₁) with hC | hC
    · linarith
    · have hne1 : f v - f y₁ ≠ 0 := ne_of_gt (by linarith)
      have hpos : 0 < (f v - f y₀) / (2 * (f v - f y₁)) :=
        div_pos (by linarith) (by linarith)
      set s : ℝ := min 1 ((f v - f y₀) / (2 * (f v - f y₁))) with hs
      have hs0 : 0 < s := lt_min one_pos hpos
      have hs1 : s ≤ 1 := min_le_left _ _
      have hmem := hA.combo_interior_self_mem_interior hy₁int hv hs0
        (by linarith : (0 : ℝ) ≤ 1 - s) (by ring)
      have hlt := hsep _ hmem
      rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul] at hlt
      have h2 : (f v - f y₀) / (2 * (f v - f y₁)) * (f v - f y₁) = (f v - f y₀) / 2 := by
        field_simp
      have hsC : s * (f v - f y₁) ≤ (f v - f y₀) / 2 := by
        calc s * (f v - f y₁)
            ≤ (f v - f y₀) / (2 * (f v - f y₁)) * (f v - f y₁) :=
              mul_le_mul_of_nonneg_right (min_le_right _ _) (by linarith)
          _ = (f v - f y₀) / 2 := h2
      linarith
  have hcneg : c < 0 := by
    rcases lt_or_gt_of_ne hcne with h | h
    · exact h
    · exfalso
      have hstep : 0 < (f y₀ - f y₁ + 1) / c := div_pos (by linarith) h
      have hbig := hall _ (hmemT (T + (f y₀ - f y₁ + 1) / c) (by linarith))
      have hgap := hcoef T (T + (f y₀ - f y₁ + 1) / c)
      rw [← hy₁] at hgap
      have hfield : (T + (f y₀ - f y₁ + 1) / c - T) * c = f y₀ - f y₁ + 1 := by
        field_simp
        ring
      rw [hfield] at hgap
      linarith
  set d : ℝ := -c with hd
  have hdpos : 0 < d := by
    rw [hd]
    linarith
  set g : ((Option ι ⊕ Bool) → ℝ) →L[ℝ] ℝ := (1 / d) • f with hg
  have hgapp : ∀ v : (Option ι ⊕ Bool) → ℝ, g v = (1 / d) * f v := by
    intro v
    rw [hg]
    simp
  have hgt : g (spike (Sum.inr true)) = -1 := by
    rw [hgapp, ← hc, hd]
    field_simp
  have hallg : ∀ v ∈ attainableSet E X, g v ≤ g y₀ := by
    intro v hv
    rw [hgapp, hgapp]
    exact mul_le_mul_of_nonneg_left (hall v hv) (by positivity)
  set lam0 : ℝ := g (spike (Sum.inl none)) with hlam0
  set lam : ι → ℝ := fun i ↦ g (spike (Sum.inl (some i))) with hlam
  set r : ℝ := g (spike (Sum.inr false)) with hr
  have hpair : ∀ b a : Ω → ℝ, (∀ ω, b ω ^ 2 ≤ a ω) →
      lam0 * E b + dot lam (fun i ↦ E (fun ω ↦ X ω i * b ω)) + r * E a
        - E (fun ω ↦ a ω ^ 2) ≤ lam0 * β + dot lam k + r * m - (V - ε) := by
    intro b a hab
    have hmem : momentVector (E b) (fun i ↦ E (fun ω ↦ X ω i * b ω)) (E a)
        (E (fun ω ↦ a ω ^ 2)) ∈ attainableSet E X :=
      ⟨b, a, hab, rfl, fun i ↦ rfl, rfl, le_rfl⟩
    have hle := hallg _ hmem
    rw [hy₀, apply_momentVector, apply_momentVector, hgt, ← hlam0, ← hr] at hle
    have hd1 : dot lam (fun i ↦ E (fun ω ↦ X ω i * b ω))
        = ∑ i, E (fun ω ↦ X ω i * b ω) * g (spike (Sum.inl (some i))) := by
      simp only [dot, Descent.Core.innerSum, hlam]
      exact Finset.sum_congr rfl fun i _ ↦ by ring
    have hd2 : dot lam k = ∑ i, k i * g (spike (Sum.inl (some i))) := by
      simp only [dot, Descent.Core.innerSum, hlam]
      exact Finset.sum_congr rfl fun i _ ↦ by ring
    rw [hd1, hd2]
    linarith
  have hchoice : ∀ ω : Ω, ∃ e : ℝ, ∀ e' : ℝ,
      (lam0 + dot lam (X ω)) * e' + r * e' ^ 2 - e' ^ 4
        ≤ (lam0 + dot lam (X ω)) * e + r * e ^ 2 - e ^ 4 :=
    fun ω ↦ exists_quartic_argmax (lam0 + dot lam (X ω)) r
  choose eStar hStar using hchoice
  have hphi : ∀ ω, quarticMax (lam0 + dot lam (X ω)) r
      = (lam0 + dot lam (X ω)) * eStar ω + r * eStar ω ^ 2 - eStar ω ^ 4 :=
    fun ω ↦ quarticMax_eq_of_max (hStar ω)
  have hkey := hpair eStar (fun ω ↦ eStar ω ^ 2) (fun ω ↦ le_rfl)
  have hsq : (fun ω ↦ (eStar ω ^ 2) ^ 2) = fun ω ↦ eStar ω ^ 4 := by
    funext ω
    ring
  rw [hsq] at hkey
  have hlin := eval_affine_form E X eStar lam0 lam
  have hPhi : E (fun ω ↦ quarticMax (lam0 + dot lam (X ω)) r)
      = E (fun ω ↦ (lam0 + dot lam (X ω)) * eStar ω)
        + r * E (fun ω ↦ eStar ω ^ 2) - E (fun ω ↦ eStar ω ^ 4) := by
    have hfun : (fun ω ↦ quarticMax (lam0 + dot lam (X ω)) r)
        = fun ω ↦ (lam0 + dot lam (X ω)) * eStar ω + r * eStar ω ^ 2 - eStar ω ^ 4 :=
      funext hphi
    rw [hfun, eval_comb E _ (fun ω ↦ eStar ω ^ 2) (fun ω ↦ eStar ω ^ 4) r]
  refine ⟨lam0, lam, r, ?_⟩
  unfold dualObjective
  rw [hPhi, hlin]
  linarith

/-- **UPT (3.8): the dual supremum equals the primal minimum.** For a finitely supported
law at a triple strictly inside the feasible region there is no duality gap. -/
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
  obtain ⟨lam0, lam, r, hlt⟩ := exists_near_optimal_multipliers E p hE X β k m hmean horth
    hslater ((minFourthMoment E X β k m
      - sSup {u : ℝ | ∃ (lam0 : ℝ) (lam : ι → ℝ) (r : ℝ),
        u = dualObjective E X β k m lam0 lam r}) / 2) (by linarith)
  have hle : dualObjective E X β k m lam0 lam r
      ≤ sSup {u : ℝ | ∃ (lam0 : ℝ) (lam : ι → ℝ) (r : ℝ),
        u = dualObjective E X β k m lam0 lam r} :=
    le_csSup ⟨minFourthMoment E X β k m, hupper⟩ ⟨lam0, lam, r, rfl⟩
  linarith

end

end Descent.Portability.FourthMomentStrongDuality
