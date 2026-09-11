/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.ObservableClosureLaw
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

assert_below Descent.Decision Descent.Program

/-!
# The terminating minimal invariant report space

Finitely many allowed transition types act on functions of a finite state space. Starting
from the span of the prescribed terminal raw observables, the iteration that adjoins every
transition's image of the current space increases, hence stabilizes, and the stabilized
space is exactly the span of all words of transitions applied to the starting space. It is
invariant, it is contained in every invariant space containing the starting space, and any
proposed linear summary that retains total mass and determines every word observable's
expectation on every initial probability law must contain it.

This is TQ Theorem 7.2 (7.3)-(7.4), the continuation of TQ Theorem 7.1 already formalized as
`ObservableClosureLaw.matrix_autonomy_iff` and applied to the scoring pipeline by
`EvolutionaryMetricClosure.scoring_features_close_iff`. The stabilization count is the
manuscript's: at most `Fintype.card S - Module.finrank ℝ V₀` strict enlargements, stated
without truncated subtraction as `j + finrank V₀ ≤ card S`. The closing minimality claim
reuses `ObservableClosureLaw.zero_sum_probability_difference`, so the two laws exhibited are
genuine probability laws rather than signed rows.

The hypotheses are domain conditions: the transition family is finite data, the starting
space is whatever raw observables were requested, and total mass is retained by the proposed
summary. Nothing assumes a low-dimensional closure exists; the construction can return the
whole space.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.InvariantReportSpace

open ObservableClosureLaw

noncomputable section

variable {S A : Type*} [Fintype S]

/-- One step of the closure iteration (7.3): adjoin the image of the current space under
every allowed transition type. -/
def enlarge (K : A → Matrix S S ℝ) (V : Submodule ℝ (S → ℝ)) : Submodule ℝ (S → ℝ) :=
  V ⊔ ⨆ a : A, V.map (Matrix.mulVecLin (K a))

/-- The iteration (7.3) started from the prescribed terminal raw observables. -/
def closureStep (K : A → Matrix S S ℝ) (V₀ : Submodule ℝ (S → ℝ)) :
    ℕ → Submodule ℝ (S → ℝ)
  | 0 => V₀
  | j + 1 => enlarge K (closureStep K V₀ j)

/-- The composite action of a word of allowed transitions on state functions. -/
def wordMap (K : A → Matrix S S ℝ) : List A → ((S → ℝ) →ₗ[ℝ] (S → ℝ))
  | [] => LinearMap.id
  | a :: rest => (Matrix.mulVecLin (K a)).comp (wordMap K rest)

/-- The span in (7.4): every word of allowed transitions applied to the prescribed raw
observables. -/
def wordSpan (K : A → Matrix S S ℝ) (V₀ : Submodule ℝ (S → ℝ)) : Submodule ℝ (S → ℝ) :=
  ⨆ w : List A, V₀.map (wordMap K w)

/-- The iteration only grows. -/
theorem closureStep_le_succ (K : A → Matrix S S ℝ) (V₀ : Submodule ℝ (S → ℝ)) (j : ℕ) :
    closureStep K V₀ j ≤ closureStep K V₀ (j + 1) := by
  simp only [closureStep, enlarge]
  exact le_sup_left

/-- The iteration is monotone in the number of steps. -/
theorem closureStep_monotone (K : A → Matrix S S ℝ) (V₀ : Submodule ℝ (S → ℝ)) :
    Monotone (closureStep K V₀) :=
  monotone_nat_of_le_succ (closureStep_le_succ K V₀)

/-- The prescribed raw observables sit inside every step. -/
theorem le_closureStep (K : A → Matrix S S ℝ) (V₀ : Submodule ℝ (S → ℝ)) (j : ℕ) :
    V₀ ≤ closureStep K V₀ j :=
  closureStep_monotone K V₀ (Nat.zero_le j)

/-- Once one step fails to enlarge, every later step equals it. -/
theorem closureStep_stable (K : A → Matrix S S ℝ) (V₀ : Submodule ℝ (S → ℝ)) (j : ℕ)
    (hstab : closureStep K V₀ (j + 1) = closureStep K V₀ j) (k : ℕ) :
    closureStep K V₀ (j + k) = closureStep K V₀ j := by
  induction k with
  | zero => rfl
  | succ k ih =>
    show enlarge K (closureStep K V₀ (j + k)) = closureStep K V₀ j
    rw [ih]
    exact hstab

/-- At stabilization the space is invariant under every allowed transition, which is what
makes its features close exactly in the sense of TQ Theorem 7.1. -/
theorem map_le_of_stable (K : A → Matrix S S ℝ) (V₀ : Submodule ℝ (S → ℝ)) (j : ℕ)
    (hstab : closureStep K V₀ (j + 1) = closureStep K V₀ j) (a : A) :
    (closureStep K V₀ j).map (Matrix.mulVecLin (K a)) ≤ closureStep K V₀ j :=
  calc (closureStep K V₀ j).map (Matrix.mulVecLin (K a))
      ≤ enlarge K (closureStep K V₀ j) :=
        le_sup_of_le_right
          (le_iSup (fun b : A ↦ (closureStep K V₀ j).map (Matrix.mulVecLin (K b))) a)
    _ = closureStep K V₀ (j + 1) := rfl
    _ = closureStep K V₀ j := hstab

/-- The empty word is the identity, so the prescribed observables lie in the word span. -/
theorem le_wordSpan (K : A → Matrix S S ℝ) (V₀ : Submodule ℝ (S → ℝ)) :
    V₀ ≤ wordSpan K V₀ := by
  have hid : V₀.map (wordMap K ([] : List A)) = V₀ := by
    simp [wordMap]
  calc V₀ = V₀.map (wordMap K ([] : List A)) := hid.symm
    _ ≤ wordSpan K V₀ := le_iSup (fun w : List A ↦ V₀.map (wordMap K w)) []

/-- The word span is invariant: prefixing a transition to every word stays inside it. -/
theorem wordSpan_map_le (K : A → Matrix S S ℝ) (V₀ : Submodule ℝ (S → ℝ)) (a : A) :
    (wordSpan K V₀).map (Matrix.mulVecLin (K a)) ≤ wordSpan K V₀ := by
  rw [wordSpan, Submodule.map_iSup]
  refine iSup_le fun w ↦ ?_
  have hstep : (V₀.map (wordMap K w)).map (Matrix.mulVecLin (K a)) =
      V₀.map (wordMap K (a :: w)) := by
    rw [wordMap, Submodule.map_comp]
  rw [hstep]
  exact le_iSup (fun v : List A ↦ V₀.map (wordMap K v)) (a :: w)

/-- Every invariant space containing the prescribed observables contains the word span:
this is the minimality half of (7.4). -/
theorem wordSpan_le_of_invariant (K : A → Matrix S S ℝ) (V₀ W : Submodule ℝ (S → ℝ))
    (hstart : V₀ ≤ W) (hinv : ∀ a : A, W.map (Matrix.mulVecLin (K a)) ≤ W) :
    wordSpan K V₀ ≤ W := by
  refine iSup_le fun w ↦ ?_
  induction w with
  | nil => simpa [wordMap] using hstart
  | cons a rest ih =>
    have hstep : V₀.map (wordMap K (a :: rest)) =
        (V₀.map (wordMap K rest)).map (Matrix.mulVecLin (K a)) := by
      rw [wordMap, Submodule.map_comp]
    rw [hstep]
    exact le_trans (Submodule.map_mono ih) (hinv a)

/-- Each step of the iteration is spanned by words, the containment half of (7.4). -/
theorem closureStep_le_wordSpan (K : A → Matrix S S ℝ) (V₀ : Submodule ℝ (S → ℝ)) (j : ℕ) :
    closureStep K V₀ j ≤ wordSpan K V₀ := by
  induction j with
  | zero => exact le_wordSpan K V₀
  | succ j ih =>
    show enlarge K (closureStep K V₀ j) ≤ wordSpan K V₀
    refine sup_le ih (iSup_le fun a ↦ ?_)
    exact le_trans (Submodule.map_mono ih) (wordSpan_map_le K V₀ a)

/-- TQ (7.4): the stabilized space is exactly the span of all words of allowed transitions
applied to the prescribed raw observables. -/
theorem closureStep_eq_wordSpan_of_stable (K : A → Matrix S S ℝ) (V₀ : Submodule ℝ (S → ℝ))
    (j : ℕ) (hstab : closureStep K V₀ (j + 1) = closureStep K V₀ j) :
    closureStep K V₀ j = wordSpan K V₀ :=
  le_antisymm (closureStep_le_wordSpan K V₀ j)
    (wordSpan_le_of_invariant K V₀ _ (le_closureStep K V₀ j) (map_le_of_stable K V₀ j hstab))

/-- Every strict enlargement raises the dimension, so `j` strict steps cost `j` dimensions. -/
theorem finrank_closureStep_ge (K : A → Matrix S S ℝ) (V₀ : Submodule ℝ (S → ℝ)) (j : ℕ)
    (hstrict : ∀ i < j, closureStep K V₀ i ≠ closureStep K V₀ (i + 1)) :
    j + Module.finrank ℝ V₀ ≤ Module.finrank ℝ (closureStep K V₀ j) := by
  induction j with
  | zero => simp [closureStep]
  | succ j ih =>
    have hprev := ih fun i hi ↦ hstrict i (by omega)
    have hlt : closureStep K V₀ j < closureStep K V₀ (j + 1) :=
      lt_of_le_of_ne (closureStep_le_succ K V₀ j) (hstrict j (by omega))
    have hrank := Submodule.finrank_lt_finrank_of_lt hlt
    omega

/-- TQ Theorem 7.2: the iteration stabilizes after at most `card S - finrank V₀` strict
enlargements, stated without truncated subtraction. -/
theorem exists_stable_index (K : A → Matrix S S ℝ) (V₀ : Submodule ℝ (S → ℝ)) :
    ∃ j, j + Module.finrank ℝ V₀ ≤ Fintype.card S ∧
      closureStep K V₀ (j + 1) = closureStep K V₀ j := by
  classical
  have hcard : ∀ j, Module.finrank ℝ (closureStep K V₀ j) ≤ Fintype.card S := by
    intro j
    have hle := Submodule.finrank_le (closureStep K V₀ j)
    rwa [Module.finrank_fintype_fun_eq_card] at hle
  have hexists : ∃ j, closureStep K V₀ (j + 1) = closureStep K V₀ j := by
    by_contra hno
    push_neg at hno
    have hbig := finrank_closureStep_ge K V₀ (Fintype.card S + 1)
      fun i _ ↦ (hno i).symm
    have hsmall := hcard (Fintype.card S + 1)
    omega
  refine ⟨Nat.find hexists, ?_, Nat.find_spec hexists⟩
  have hmin : ∀ i < Nat.find hexists, closureStep K V₀ i ≠ closureStep K V₀ (i + 1) :=
    fun i hi heq ↦ Nat.find_min hexists hi heq.symm
  have hbig := finrank_closureStep_ge K V₀ (Nat.find hexists) hmin
  have hsmall := hcard (Nat.find hexists)
  omega

/-- The minimal invariant space exists as an actual space: it is invariant, contains the
prescribed observables, and is contained in every such invariant space. -/
theorem wordSpan_is_smallest_invariant (K : A → Matrix S S ℝ) (V₀ : Submodule ℝ (S → ℝ)) :
    V₀ ≤ wordSpan K V₀ ∧ (∀ a : A, (wordSpan K V₀).map (Matrix.mulVecLin (K a)) ≤
        wordSpan K V₀) ∧
      ∀ W : Submodule ℝ (S → ℝ), V₀ ≤ W → (∀ a : A, W.map (Matrix.mulVecLin (K a)) ≤ W) →
        wordSpan K V₀ ≤ W :=
  ⟨le_wordSpan K V₀, wordSpan_map_le K V₀, wordSpan_le_of_invariant K V₀⟩

/-- Pairing a signed direction with a state function, written as an expectation difference
of the two probability laws that the direction is a positive multiple of. -/
theorem pairing_eq_expectation_difference (dir : S → ℝ) (first second : FiniteReportLaw S)
    (scale : ℝ) (heq : dir = scale • (first.mass - second.mass)) (g : S → ℝ) :
    ∑ s, dir s * g s = scale * (first.expectation g - second.expectation g) := by
  calc ∑ s, dir s * g s = ∑ s, scale * ((first.mass s - second.mass s) * g s) := by
        subst heq
        exact Finset.sum_congr rfl fun s _ ↦ by
          simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, mul_assoc]
    _ = scale * ∑ s, (first.mass s - second.mass s) * g s := by rw [Finset.mul_sum]
    _ = scale * (first.expectation g - second.expectation g) := by
        simp only [FiniteReportLaw.expectation, sub_mul, Finset.sum_sub_distrib]

/-- TQ Theorem 7.2, closing claim: a proposed summary whose feature span retains total mass
and determines every word observable's expectation for every initial probability law has a
feature span containing the whole minimal invariant space. The two laws exhibited when it
fails are genuine probability laws, not signed rows, which is why a state is supplied
explicitly rather than through an instance. -/
theorem wordSpan_le_of_determines_expectations [DecidableEq S] (witness : S)
    (K : A → Matrix S S ℝ)
    (V₀ W : Submodule ℝ (S → ℝ)) (hmass : (fun _ ↦ (1 : ℝ)) ∈ W)
    (hdet : ∀ first second : FiniteReportLaw S,
      (∀ g ∈ W, first.expectation g = second.expectation g) →
      ∀ h ∈ wordSpan K V₀, first.expectation h = second.expectation h) :
    wordSpan K V₀ ≤ W := by
  classical
  haveI : Nonempty S := ⟨witness⟩
  intro h hh
  by_contra hnot
  obtain ⟨dual, hdualne, hdualW⟩ := W.exists_dual_map_eq_bot_of_notMem hnot inferInstance
  set dir : S → ℝ := fun s ↦ dual fun t ↦ if s = t then (1 : ℝ) else 0 with hdirdef
  have hpair : ∀ x : S → ℝ, ∑ s, dir s * x s = dual x := by
    intro x
    rw [LinearMap.pi_apply_eq_sum_univ dual x]
    exact Finset.sum_congr rfl fun s _ ↦ by rw [smul_eq_mul, hdirdef]; ring
  have hWzero : ∀ g ∈ W, dual g = 0 := by
    intro g hg
    have hmem : dual g ∈ W.map dual := Submodule.mem_map_of_mem hg
    rw [hdualW] at hmem
    simpa using hmem
  have hsum : ∑ s, dir s = 0 := by
    have hone := hWzero _ hmass
    have := hpair fun _ ↦ (1 : ℝ)
    simp only [mul_one] at this
    rw [this, hone]
  obtain ⟨first, second, scale, hscale, heq⟩ := zero_sum_probability_difference dir hsum
  have hequal : ∀ g ∈ W, first.expectation g = second.expectation g := by
    intro g hg
    have hzero : scale * (first.expectation g - second.expectation g) = 0 := by
      rw [← pairing_eq_expectation_difference dir first second scale heq g, hpair g, hWzero g hg]
    have := (mul_eq_zero.1 hzero).resolve_left (ne_of_gt hscale)
    linarith
  have hh' := hdet first second hequal h hh
  have hfinal : dual h = 0 := by
    rw [← hpair h, pairing_eq_expectation_difference dir first second scale heq h, hh']
    ring
  exact hdualne hfinal

end

end Descent.Portability.InvariantReportSpace
