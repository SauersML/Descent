/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.TurnoverDependence
import Mathlib.Analysis.Calculus.Deriv.MeanValue

assert_below Descent.Decision Descent.Program

/-!
# When a portability report can decline for every initial condition

A finite state space carries a transition law and a defined report. UPT Theorem
5.1 is proved in both time scales: the expected report fails to increase in one
step for *every* initial law exactly when `K h' ≤ h` coordinatewise, and, for a
continuous-time generator `Q` with its transition semigroup, the expectation is
nonincreasing on `[0,∞)` for every initial law exactly when `Q h ≤ 0`. The
continuous-time semigroup enters through its defining properties, the initial
condition and the forward equation together with nonnegativity of its entries,
and `TurnoverDependence.flipSemigroup` is an explicit family satisfying all of
them, so those hypotheses are not vacuous. UPT Corollary 5.2 follows in both
time scales: under irreducibility only a constant report can decline from every
initial condition, so a decline observed from one source-selected start cannot
be upgraded to a claim about every start.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.UniversalReportMonotonicity

open Foundations TurnoverDependence

open scoped Matrix

noncomputable section

variable {S : Type*} [Fintype S] [DecidableEq S]

section OneStep

/-- The state law after one transition step. -/
def pushLaw (K : Matrix S S ℝ) (p : S → ℝ) : S → ℝ := fun y ↦ ∑ x, p x * K x y

omit [DecidableEq S] in
/-- Coordinate form of a matrix acting on a report. -/
theorem mulVec_coord (K : Matrix S S ℝ) (g : S → ℝ) (x : S) :
    (K *ᵥ g) x = ∑ y, K x y * g y := rfl

omit [DecidableEq S] in
/-- A stochastic step carries probability vectors to probability vectors. -/
theorem pushLaw_isLaw (K : Matrix S S ℝ) (hKnn : ∀ x y, 0 ≤ K x y)
    (hKrow : ∀ x, ∑ y, K x y = 1) (p : S → ℝ) (hp : ∀ x, 0 ≤ p x) (hsum : ∑ x, p x = 1) :
    (∀ y, 0 ≤ pushLaw K p y) ∧ ∑ y, pushLaw K p y = 1 := by
  constructor
  · intro y
    exact Finset.sum_nonneg fun x _ ↦ mul_nonneg (hp x) (hKnn x y)
  · have h1 : ∀ x : S, ∑ y, p x * K x y = p x := by
      intro x
      rw [← Finset.mul_sum, hKrow x, mul_one]
    show ∑ y, ∑ x, p x * K x y = 1
    rw [Finset.sum_comm, Finset.sum_congr rfl fun x _ ↦ h1 x]
    exact hsum

omit [DecidableEq S] in
/-- Backward form of the one-step report expectation. -/
theorem pushLaw_expectation (K : Matrix S S ℝ) (p g : S → ℝ) :
    ∑ y, pushLaw K p y * g y = ∑ x, p x * (K *ᵥ g) x := by
  have h1 : ∀ y : S, pushLaw K p y * g y = ∑ x, p x * (K x y * g y) := by
    intro y
    show (∑ x, p x * K x y) * g y = _
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun x _ ↦ by ring
  have h2 : ∀ x : S, p x * (K *ᵥ g) x = ∑ y, p x * (K x y * g y) := by
    intro x
    show p x * ∑ y, K x y * g y = _
    rw [Finset.mul_sum]
  rw [Finset.sum_congr rfl fun y _ ↦ h1 y, Finset.sum_congr rfl fun x _ ↦ h2 x]
  exact Finset.sum_comm

/-- **UPT Theorem 5.1 (5.1), discrete time.**  The expected report does not increase in
one step for every initial law exactly when `K h' ≤ h` coordinatewise. -/
theorem universal_one_step_monotone_iff (K : Matrix S S ℝ) (h g : S → ℝ) :
    (∀ p : S → ℝ, (∀ x, 0 ≤ p x) → (∑ x, p x = 1) →
        ∑ y, pushLaw K p y * g y ≤ ∑ x, p x * h x)
      ↔ ∀ x, (K *ᵥ g) x ≤ h x := by
  constructor
  · intro hall x
    have hpt := hall (fun z ↦ if z = x then (1 : ℝ) else 0)
      (fun z ↦ by by_cases hz : z = x <;> simp [hz]) (by simp)
    rw [pushLaw_expectation] at hpt
    simpa using hpt
  · intro hcoord p hp hsum
    rw [pushLaw_expectation]
    exact Finset.sum_le_sum fun x _ ↦ mul_le_mul_of_nonneg_left (hcoord x) (hp x)

end OneStep

section ContinuousTime

/-- **UPT Theorem 5.1 (5.2), continuous time.**  For a transition semigroup solving the
forward equation of the generator `Q`, the expected report is nonincreasing on `[0,∞)` for
every initial law exactly when `Q h ≤ 0`.

Assumes: the family `P` starts at the identity, has nonnegative entries at nonnegative
times, and solves `P'(t) = P(t) Q`. These are the defining properties of the chain's own
transition law, and `flipSemigroup_is_transition_semigroup` exhibits a family with all of
them. -/
theorem universal_generator_monotone_iff (Q : Matrix S S ℝ) (P : ℝ → Matrix S S ℝ)
    (h : S → ℝ) (hP0 : P 0 = 1) (hPnn : ∀ t, 0 ≤ t → ∀ x y, 0 ≤ P t x y)
    (hforward : ∀ t x y, HasDerivAt (fun s ↦ P s x y) ((P t * Q) x y) t) :
    (∀ p : S → ℝ, (∀ x, 0 ≤ p x) → (∑ x, p x = 1) →
        AntitoneOn (fun t ↦ ∑ x, p x * (P t *ᵥ h) x) (Set.Ici 0))
      ↔ ∀ x, (Q *ᵥ h) x ≤ 0 := by
  constructor
  · intro hall x
    have hd : HasDerivAt (fun t ↦ (P t *ᵥ h) x) ((Q *ᵥ h) x) 0 := by
      have hsum : HasDerivAt (fun t ↦ ∑ y, P t x y * h y) (∑ y, (P 0 * Q) x y * h y) 0 :=
        HasDerivAt.fun_sum fun y _ ↦ (hforward 0 x y).mul_const (h y)
      have hval : ∑ y, (P 0 * Q) x y * h y = (Q *ᵥ h) x := by
        rw [hP0, one_mul, mulVec_coord]
      rw [← hval]
      exact hsum
    have hanti : AntitoneOn (fun t ↦ (P t *ᵥ h) x) (Set.Ici 0) := by
      have hall_x := hall (fun z ↦ if z = x then (1 : ℝ) else 0)
        (fun z ↦ by by_cases hz : z = x <;> simp [hz]) (by simp)
      have hfe : (fun t ↦ ∑ z, (if z = x then (1 : ℝ) else 0) * (P t *ᵥ h) z)
          = fun t ↦ (P t *ᵥ h) x := by
        funext t
        simp
      rwa [hfe] at hall_x
    have hslope : Filter.Tendsto (slope (fun t ↦ (P t *ᵥ h) x) 0)
        (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds ((Q *ᵥ h) x)) := hasDerivAt_iff_tendsto_slope.mp hd
    have hsub : nhdsWithin (0 : ℝ) (Set.Ioi 0) ≤ nhdsWithin (0 : ℝ) {(0 : ℝ)}ᶜ :=
      nhdsWithin_mono _ fun t ht ↦ ne_of_gt ht
    refine le_of_tendsto (hslope.mono_left hsub) ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    have htpos : (0 : ℝ) < t := ht
    have hft : (P t *ᵥ h) x ≤ (P 0 *ᵥ h) x :=
      hanti Set.left_mem_Ici (Set.mem_Ici.mpr htpos.le) htpos.le
    have h3 : 0 ≤ ((P 0 *ᵥ h) x - (P t *ᵥ h) x) / (t - 0) :=
      div_nonneg (by linarith) (by linarith)
    rw [slope_def_field]
    have h4 : ((P t *ᵥ h) x - (P 0 *ᵥ h) x) / (t - 0)
        = -(((P 0 *ᵥ h) x - (P t *ᵥ h) x) / (t - 0)) := by ring
    rw [h4]
    linarith
  · intro hQ p hp hsum
    have hgd : ∀ t : ℝ, HasDerivAt (fun s ↦ ∑ x, p x * (P s *ᵥ h) x)
        (∑ x, p x * ((P t * Q) *ᵥ h) x) t := by
      intro t
      refine HasDerivAt.fun_sum fun x _ ↦ ?_
      have h2 : HasDerivAt (fun s ↦ ∑ y, P s x y * h y) (∑ y, (P t * Q) x y * h y) t :=
        HasDerivAt.fun_sum fun y _ ↦ (hforward t x y).mul_const (h y)
      exact h2.const_mul (p x)
    have hdiff : Differentiable ℝ (fun s ↦ ∑ x, p x * (P s *ᵥ h) x) := fun t ↦
      (hgd t).differentiableAt
    refine antitoneOn_of_deriv_nonpos (convex_Ici 0) hdiff.continuous.continuousOn
      hdiff.differentiableOn ?_
    intro t ht
    rw [interior_Ici] at ht
    have htpos : (0 : ℝ) < t := ht
    rw [(hgd t).deriv]
    refine Finset.sum_nonpos fun x _ ↦ ?_
    have hrow : ((P t * Q) *ᵥ h) x = ∑ y, P t x y * (Q *ᵥ h) y := by
      rw [← Matrix.mulVec_mulVec, mulVec_coord]
    have hAle : ((P t * Q) *ᵥ h) x ≤ 0 := by
      rw [hrow]
      refine Finset.sum_nonpos fun y _ ↦ ?_
      have hmul : P t x y * (Q *ᵥ h) y ≤ P t x y * 0 :=
        mul_le_mul_of_nonneg_left (hQ y) (hPnn t htpos.le x y)
      simpa using hmul
    have hmul : p x * ((P t * Q) *ᵥ h) x ≤ p x * 0 :=
      mul_le_mul_of_nonneg_left hAle (hp x)
    simpa using hmul

end ContinuousTime

section Irreducibility

variable [Nonempty S]

omit [DecidableEq S] [Nonempty S] in
/-- **A minimiser's reachable successors are minimisers**, in discrete time. -/
theorem minimizer_successor (K : Matrix S S ℝ) (hKnn : ∀ x y, 0 ≤ K x y)
    (hKrow : ∀ x, ∑ y, K x y = 1) (h : S → ℝ) (hKh : ∀ x, (K *ᵥ h) x ≤ h x)
    (z : S) (hz : ∀ w, h z ≤ h w) (y : S) (hy : 0 < K z y) : h y = h z := by
  have hmv : (K *ᵥ h) z = ∑ w, K z w * h w := mulVec_coord K h z
  have hge : h z ≤ ∑ w, K z w * h w := by
    have h1 : ∑ w, K z w * h z ≤ ∑ w, K z w * h w :=
      Finset.sum_le_sum fun w _ ↦ mul_le_mul_of_nonneg_left (hz w) (hKnn z w)
    rw [← Finset.sum_mul, hKrow z, one_mul] at h1
    exact h1
  have hle : ∑ w, K z w * h w ≤ h z := by
    rw [← hmv]
    exact hKh z
  have hs : ∑ w, K z w * (h w - h z) = (∑ w, K z w * h w) - (∑ w, K z w) * h z := by
    rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun w _ ↦ by ring
  have heq : ∑ w, K z w * (h w - h z) = 0 := by
    rw [hs, hKrow z, one_mul]
    linarith
  have hnn : ∀ w ∈ (Finset.univ : Finset S), 0 ≤ K z w * (h w - h z) := fun w _ ↦
    mul_nonneg (hKnn z w) (by linarith [hz w])
  have hterm := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp heq y (Finset.mem_univ y)
  rcases mul_eq_zero.mp hterm with h3 | h3
  · exact absurd h3 (ne_of_gt hy)
  · linarith

omit [Nonempty S] in
/-- Powers of a nonnegative matrix are nonnegative. -/
theorem pow_nonneg_entries (K : Matrix S S ℝ) (hKnn : ∀ x y, 0 ≤ K x y) (n : ℕ) :
    ∀ x y, 0 ≤ (K ^ n) x y := by
  induction n with
  | zero =>
      intro x y
      rw [pow_zero, Matrix.one_apply]
      by_cases hxy : x = y <;> simp [hxy]
  | succ n ih =>
      intro x y
      rw [pow_succ, Matrix.mul_apply]
      exact Finset.sum_nonneg fun z _ ↦ mul_nonneg (ih x z) (hKnn z y)

/-- **UPT Corollary 5.2, discrete time, core step.**  An irreducible stochastic matrix whose
report does not increase in one step from any state has a constant report. -/
theorem irreducible_forces_constant (K : Matrix S S ℝ) (hKnn : ∀ x y, 0 ≤ K x y)
    (hKrow : ∀ x, ∑ y, K x y = 1) (hirr : ∀ x y, ∃ n : ℕ, 0 < (K ^ n) x y)
    (h : S → ℝ) (hKh : ∀ x, (K *ᵥ h) x ≤ h x) : ∀ x y, h x = h y := by
  obtain ⟨x0, -, hx0⟩ :=
    Finset.exists_min_image (Finset.univ : Finset S) h ⟨Classical.arbitrary S, Finset.mem_univ _⟩
  have hmin : ∀ w, h x0 ≤ h w := fun w ↦ hx0 w (Finset.mem_univ w)
  have hstep : ∀ n : ℕ, ∀ y, 0 < (K ^ n) x0 y → h y = h x0 := by
    intro n
    induction n with
    | zero =>
        intro y hy
        rw [pow_zero, Matrix.one_apply] at hy
        by_cases hxy : x0 = y
        · rw [hxy]
        · rw [if_neg hxy] at hy
          exact absurd hy (by norm_num)
    | succ n ih =>
        intro y hy
        rw [pow_succ, Matrix.mul_apply] at hy
        have hex : ∃ z : S, 0 < (K ^ n) x0 z * K z y := by
          by_contra hcon
          push_neg at hcon
          have : ∑ z, (K ^ n) x0 z * K z y ≤ 0 :=
            Finset.sum_nonpos fun z _ ↦ hcon z
          linarith
        obtain ⟨z, hz⟩ := hex
        have hz1 : 0 < (K ^ n) x0 z := by
          rcases lt_or_eq_of_le (pow_nonneg_entries K hKnn n x0 z) with hlt | heq
          · exact hlt
          · rw [← heq] at hz
            simp at hz
        have hz2 : 0 < K z y := by
          rcases lt_or_eq_of_le (hKnn z y) with hlt | heq
          · exact hlt
          · rw [← heq] at hz
            simp at hz
        have hzmin : ∀ w, h z ≤ h w := by
          intro w
          rw [ih z hz1]
          exact hmin w
        rw [minimizer_successor K hKnn hKrow h hKh z hzmin y hz2, ih z hz1]
  intro x y
  obtain ⟨nx, hnx⟩ := hirr x0 x
  obtain ⟨ny, hny⟩ := hirr x0 y
  rw [hstep nx x hnx, hstep ny y hny]

/-- **UPT Corollary 5.2, discrete time.**  Under irreducibility a nonconstant report cannot
be nonincreasing in expectation from every initial law. -/
theorem recurrent_evolution_obstruction (K : Matrix S S ℝ) (hKnn : ∀ x y, 0 ≤ K x y)
    (hKrow : ∀ x, ∑ y, K x y = 1) (hirr : ∀ x y, ∃ n : ℕ, 0 < (K ^ n) x y)
    (h : S → ℝ) (hnc : ∃ x y, h x ≠ h y) :
    ¬ ∀ p : S → ℝ, (∀ x, 0 ≤ p x) → (∑ x, p x = 1) →
        ∑ y, pushLaw K p y * h y ≤ ∑ x, p x * h x := by
  intro hall
  obtain ⟨x, y, hxy⟩ := hnc
  exact hxy (irreducible_forces_constant K hKnn hKrow hirr h
    ((universal_one_step_monotone_iff K h h).mp hall) x y)

omit [Nonempty S] in
/-- **A minimiser's reachable successors are minimisers**, for a generator. -/
theorem generator_minimizer_successor (Q : Matrix S S ℝ)
    (hQnn : ∀ x y, x ≠ y → 0 ≤ Q x y) (hQrow : ∀ x, ∑ y, Q x y = 0) (h : S → ℝ)
    (hQh : ∀ x, (Q *ᵥ h) x ≤ 0) (z : S) (hz : ∀ w, h z ≤ h w) (y : S) (hy : 0 < Q z y) :
    h y = h z := by
  have hmv : (Q *ᵥ h) z = ∑ w, Q z w * h w := mulVec_coord Q h z
  have hsplit : ∑ w, Q z w * (h w - h z) = (Q *ᵥ h) z := by
    have hs : ∑ w, Q z w * (h w - h z) = (∑ w, Q z w * h w) - (∑ w, Q z w) * h z := by
      rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun w _ ↦ by ring
    rw [hs, hQrow z, zero_mul, sub_zero, hmv]
  have hnn : ∀ w ∈ (Finset.univ : Finset S), 0 ≤ Q z w * (h w - h z) := by
    intro w _
    by_cases hwz : w = z
    · rw [hwz]
      simp
    · exact mul_nonneg (hQnn z w fun hc ↦ hwz hc.symm) (by linarith [hz w])
  have hge : 0 ≤ ∑ w, Q z w * (h w - h z) := Finset.sum_nonneg hnn
  have heq : ∑ w, Q z w * (h w - h z) = 0 := by
    rw [hsplit]
    rw [hsplit] at hge
    linarith [hQh z]
  have hterm := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp heq y (Finset.mem_univ y)
  rcases mul_eq_zero.mp hterm with h3 | h3
  · exact absurd h3 (ne_of_gt hy)
  · linarith

/-- **UPT Corollary 5.2, continuous time, core step.**  An irreducible generator whose
report has nonpositive drift everywhere has a constant report. -/
theorem generator_irreducible_forces_constant (Q : Matrix S S ℝ)
    (hQnn : ∀ x y, x ≠ y → 0 ≤ Q x y) (hQrow : ∀ x, ∑ y, Q x y = 0)
    (hirr : ∀ x y, Relation.ReflTransGen (fun a b ↦ 0 < Q a b) x y) (h : S → ℝ)
    (hQh : ∀ x, (Q *ᵥ h) x ≤ 0) : ∀ x y, h x = h y := by
  obtain ⟨x0, -, hx0⟩ :=
    Finset.exists_min_image (Finset.univ : Finset S) h ⟨Classical.arbitrary S, Finset.mem_univ _⟩
  have hmin : ∀ w, h x0 ≤ h w := fun w ↦ hx0 w (Finset.mem_univ w)
  have hstep : ∀ y, Relation.ReflTransGen (fun a b ↦ 0 < Q a b) x0 y → h y = h x0 := by
    intro y hy
    induction hy with
    | refl => rfl
    | tail _ hbc ih =>
        rename_i b c _
        have hbmin : ∀ w, h b ≤ h w := by
          intro w
          rw [ih]
          exact hmin w
        rw [generator_minimizer_successor Q hQnn hQrow h hQh b hbmin c hbc, ih]
  intro x y
  rw [hstep x (hirr x0 x), hstep y (hirr x0 y)]

end Irreducibility

section FlipWitness

/-- **The two-state flip family satisfies every semigroup hypothesis.**  The hypotheses of
`universal_generator_monotone_iff` are therefore not vacuous. -/
theorem flipSemigroup_is_transition_semigroup (lam : ℝ) (hlam : 0 ≤ lam) :
    flipSemigroup lam 0 = 1 ∧
      (∀ t, 0 ≤ t → ∀ x y, 0 ≤ flipSemigroup lam t x y) ∧
      (∀ t, 0 ≤ t → ∀ x, ∑ y, flipSemigroup lam t x y = 1) ∧
      (∀ t x y, HasDerivAt (fun s ↦ flipSemigroup lam s x y)
        ((flipSemigroup lam t * flipGenerator lam) x y) t) := by
  refine ⟨flipSemigroup_zero lam, ?_, ?_, flipSemigroup_forward lam⟩
  · intro t ht x y
    exact (flipSemigroup_stochastic (mul_nonneg hlam ht) x).1 y
  · intro t ht x
    exact (flipSemigroup_stochastic (mul_nonneg hlam ht) x).2

/-- The symmetric two-state generator is a genuine generator and is irreducible at a
positive flip rate. -/
theorem flipGenerator_is_irreducible_generator (lam : ℝ) (hlam : 0 < lam) :
    (∀ x y : Fin 2, x ≠ y → 0 ≤ flipGenerator lam x y) ∧
      (∀ x : Fin 2, ∑ y, flipGenerator lam x y = 0) ∧
      ∀ x y : Fin 2, Relation.ReflTransGen (fun a b ↦ 0 < flipGenerator lam a b) x y := by
  refine ⟨?_, ?_, ?_⟩
  · intro x y hxy
    show 0 ≤ if x = y then -lam else lam
    rw [if_neg hxy]
    exact hlam.le
  · intro x
    rw [Fin.sum_univ_two]
    fin_cases x <;> simp [flipGenerator]
  · intro x y
    by_cases hxy : x = y
    · rw [hxy]
    · refine Relation.ReflTransGen.single ?_
      show 0 < if x = y then -lam else lam
      rw [if_neg hxy]
      exact hlam

/-- **UPT Corollary 5.2 on the two-state flip chain.**  With a positive flip rate the only
reports whose expectation is nonincreasing from every initial law are the constants. -/
theorem flip_report_monotone_iff (lam : ℝ) (hlam : 0 < lam) (h : Fin 2 → ℝ) :
    (∀ p : Fin 2 → ℝ, (∀ x, 0 ≤ p x) → (∑ x, p x = 1) →
        AntitoneOn (fun t ↦ ∑ x, p x * (flipSemigroup lam t *ᵥ h) x) (Set.Ici 0))
      ↔ h 0 = h 1 := by
  obtain ⟨h0, hnn, -, hfwd⟩ := flipSemigroup_is_transition_semigroup lam hlam.le
  rw [universal_generator_monotone_iff (flipGenerator lam) (flipSemigroup lam) h h0 hnn hfwd]
  have hval : ∀ x : Fin 2, (flipGenerator lam *ᵥ h) x
      = (if x = 0 then lam * (h 1 - h 0) else lam * (h 0 - h 1)) := by
    intro x
    show ∑ y, (if x = y then -lam else lam) * h y = _
    rw [Fin.sum_univ_two]
    fin_cases x <;> simp <;> ring
  constructor
  · intro hall
    have hA := hall 0
    have hB := hall 1
    rw [hval 0, if_pos rfl] at hA
    rw [hval 1, if_neg (by decide : ¬((1 : Fin 2) = 0))] at hB
    have h1 : h 1 - h 0 ≤ 0 := by
      by_contra hc
      push_neg at hc
      nlinarith
    have h2 : h 0 - h 1 ≤ 0 := by
      by_contra hc
      push_neg at hc
      nlinarith
    linarith
  · intro heq x
    rw [hval x, heq]
    by_cases hx : x = 0 <;> simp [hx]

end FlipWitness

end

end Descent.Portability.UniversalReportMonotonicity
