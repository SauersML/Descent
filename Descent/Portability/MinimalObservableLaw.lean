/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.ObservableClosureLaw
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

assert_below Descent.Decision Descent.Program

/-!
The smallest exact linear predictive state is the span of all future observed
functions. Cayley–Hamilton makes this span finite for a fixed finite transition
matrix. A family of transitions instead requires all finite transition words.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
open scoped Matrix

namespace Descent.Portability.MinimalObservableLaw

variable {V I A : Type*} [AddCommGroup V] [Module ℝ V]

/-- Forward invariance of a space of observable functions. -/
def Invariant (evolution : Module.End ℝ V) (space : Submodule ℝ V) : Prop :=
  ∀ observable ∈ space, evolution observable ∈ space

noncomputable def orbitSpan (evolution : Module.End ℝ V) (targets : I → V) :
    Submodule ℝ V :=
  Submodule.span ℝ (Set.range fun index : ℕ × I ↦ (evolution ^ index.1) (targets index.2))

theorem orbit_mem (evolution : Module.End ℝ V) (targets : I → V) (time : ℕ) (index : I) :
    (evolution ^ time) (targets index) ∈ orbitSpan evolution targets :=
  Submodule.subset_span ⟨(time, index), rfl⟩

theorem target_mem (evolution : Module.End ℝ V) (targets : I → V) (index : I) :
    targets index ∈ orbitSpan evolution targets := by
  simpa using orbit_mem evolution targets 0 index

theorem orbitSpan_invariant (evolution : Module.End ℝ V) (targets : I → V) :
    Invariant evolution (orbitSpan evolution targets) := by
  have hle : orbitSpan evolution targets ≤
      (orbitSpan evolution targets).comap evolution := by
    apply Submodule.span_le.mpr
    rintro observable ⟨⟨time, index⟩, rfl⟩
    change evolution ((evolution ^ time) (targets index)) ∈ orbitSpan evolution targets
    simpa only [pow_succ', Module.End.mul_apply] using
      orbit_mem evolution targets (time + 1) index
  exact fun _ hmem ↦ hle hmem

theorem orbitSpan_minimal (evolution : Module.End ℝ V) (targets : I → V)
    (space : Submodule ℝ V) (hinvariant : Invariant evolution space)
    (htargets : ∀ index, targets index ∈ space) : orbitSpan evolution targets ≤ space := by
  apply Submodule.span_le.mpr
  rintro observable ⟨⟨time, index⟩, rfl⟩
  induction time with
  | zero => simpa using htargets index
  | succ time ih => simpa only [pow_succ', Module.End.mul_apply] using hinvariant _ ih

/-- Products are ordered so a new transition acts on the left. -/
noncomputable def wordOperator (evolutions : A → Module.End ℝ V) : List A → Module.End ℝ V
  | [] => 1
  | head :: tail => evolutions head * wordOperator evolutions tail

noncomputable def wordSpan (evolutions : A → Module.End ℝ V) (targets : I → V) :
    Submodule ℝ V :=
  Submodule.span ℝ (Set.range fun index : List A × I ↦
    wordOperator evolutions index.1 (targets index.2))

theorem word_mem (evolutions : A → Module.End ℝ V) (targets : I → V)
    (word : List A) (index : I) :
    wordOperator evolutions word (targets index) ∈ wordSpan evolutions targets :=
  Submodule.subset_span ⟨(word, index), rfl⟩

theorem wordSpan_targets (evolutions : A → Module.End ℝ V) (targets : I → V) (index : I) :
    targets index ∈ wordSpan evolutions targets := by
  simpa [wordOperator] using word_mem evolutions targets [] index

theorem wordSpan_invariant (evolutions : A → Module.End ℝ V) (targets : I → V) (step : A) :
    Invariant (evolutions step) (wordSpan evolutions targets) := by
  have hle : wordSpan evolutions targets ≤
      (wordSpan evolutions targets).comap (evolutions step) := by
    apply Submodule.span_le.mpr
    rintro observable ⟨⟨word, index⟩, rfl⟩
    exact word_mem evolutions targets (step :: word) index
  exact fun _ hmem ↦ hle hmem

theorem wordSpan_minimal (evolutions : A → Module.End ℝ V) (targets : I → V)
    (space : Submodule ℝ V) (hinvariant : ∀ step, Invariant (evolutions step) space)
    (htargets : ∀ index, targets index ∈ space) : wordSpan evolutions targets ≤ space := by
  apply Submodule.span_le.mpr
  rintro observable ⟨⟨word, index⟩, rfl⟩
  induction word with
  | nil => simpa [wordOperator] using htargets index
  | cons step word ih => exact hinvariant step _ ih


/-- Iteratively add every one-step image of the retained observable space. -/
noncomputable def closureStage (evolutions : A → Module.End ℝ V) (targets : I → V) :
    ℕ → Submodule ℝ V
  | 0 => Submodule.span ℝ (Set.range targets)
  | time + 1 => closureStage evolutions targets time ⊔
      ⨆ step, (closureStage evolutions targets time).map (evolutions step)

theorem closureStage_le_succ (evolutions : A → Module.End ℝ V) (targets : I → V) (time : ℕ) :
    closureStage evolutions targets time ≤ closureStage evolutions targets (time + 1) :=
  le_sup_left

theorem closureStage_mono (evolutions : A → Module.End ℝ V) (targets : I → V) :
    Monotone (closureStage evolutions targets) :=
  monotone_nat_of_le_succ (closureStage_le_succ evolutions targets)

theorem closureStage_le_wordSpan (evolutions : A → Module.End ℝ V)
    (targets : I → V) (time : ℕ) :
    closureStage evolutions targets time ≤ wordSpan evolutions targets := by
  induction time with
  | zero =>
      apply Submodule.span_le.mpr
      rintro _ ⟨index, rfl⟩
      exact wordSpan_targets _ _ _
  | succ time ih =>
      apply sup_le ih
      apply iSup_le
      intro step observable hmem
      obtain ⟨earlier, hearlier, rfl⟩ := hmem
      exact wordSpan_invariant evolutions targets step _ (ih hearlier)

theorem stable_stage_eq_wordSpan (evolutions : A → Module.End ℝ V) (targets : I → V)
    (time : ℕ) (hstable : closureStage evolutions targets time =
      closureStage evolutions targets (time + 1)) :
    closureStage evolutions targets time = wordSpan evolutions targets := by
  apply le_antisymm (closureStage_le_wordSpan _ _ _)
  apply wordSpan_minimal
  · intro step observable hmem
    rw [hstable]
    change (evolutions step) observable ∈ closureStage evolutions targets time ⊔
      ⨆ next, (closureStage evolutions targets time).map (evolutions next)
    exact (le_trans (le_iSup (fun next ↦
      (closureStage evolutions targets time).map (evolutions next)) step)
      le_sup_right) ⟨observable, hmem, rfl⟩
  · intro index
    apply closureStage_mono evolutions targets (Nat.zero_le time)
    exact Submodule.subset_span ⟨index, rfl⟩

/-- The iterative construction reaches the minimal common invariant space
after at most `dim V` strict increases, even for an infinite family of operators. -/
theorem closure_stabilizes [FiniteDimensional ℝ V]
    (evolutions : A → Module.End ℝ V) (targets : I → V) :
    ∃ time ≤ Module.finrank ℝ V,
      closureStage evolutions targets time = wordSpan evolutions targets := by
  have hexists : ∃ time ≤ Module.finrank ℝ V,
      closureStage evolutions targets time = closureStage evolutions targets (time + 1) := by
    by_contra hnone
    push_neg at hnone
    have hrank : ∀ time ≤ Module.finrank ℝ V + 1,
        time ≤ Module.finrank ℝ (closureStage evolutions targets time) := by
      intro time
      induction time with
      | zero => intro _; exact Nat.zero_le _
      | succ time ih =>
          intro htime
          have hi := ih (by omega)
          have hstrict : closureStage evolutions targets time <
              closureStage evolutions targets (time + 1) :=
            lt_of_le_of_ne (closureStage_le_succ _ _ _) (hnone time (by omega))
          have hdim := Submodule.finrank_lt_finrank_of_lt hstrict
          omega
    have hlower := hrank (Module.finrank ℝ V + 1) le_rfl
    have hupper := Submodule.finrank_le (closureStage evolutions targets (Module.finrank ℝ V + 1))
    omega
  obtain ⟨time, htime, hstable⟩ := hexists
  exact ⟨time, htime, stable_stage_eq_wordSpan _ _ _ hstable⟩

variable {S : Type*} [Fintype S] [Nonempty S] [DecidableEq S]

/-- A finite state space needs at most its dimension many powers of each target. -/
noncomputable def finiteOrbitSpan (transition : Matrix S S ℝ) (targets : I → S → ℝ) :
    Submodule ℝ (S → ℝ) :=
  Submodule.span ℝ (Set.range fun index : Fin (Fintype.card S) × I ↦
    (transition ^ (index.1 : ℕ)) *ᵥ targets index.2)

/-- Cayley–Hamilton, with explicit coefficients from the remainder polynomial. -/
theorem power_remainder (transition : Matrix S S ℝ) (time : ℕ) :
    transition ^ time = ∑ earlier ∈ Finset.range (Fintype.card S),
      ((Polynomial.X ^ time %ₘ transition.charpoly).coeff earlier) • transition ^ earlier := by
  have hne : transition.charpoly ≠ 1 := by
    intro heq
    have hd := transition.charpoly_natDegree_eq_dim
    rw [heq, Polynomial.natDegree_one] at hd
    exact (Nat.ne_of_gt Fintype.card_pos) hd.symm
  have hdegree := Polynomial.natDegree_modByMonic_lt
    (Polynomial.X ^ time) transition.charpoly_monic hne
  rw [transition.charpoly_natDegree_eq_dim] at hdegree
  rw [transition.pow_eq_aeval_mod_charpoly, Polynomial.aeval_eq_sum_range' hdegree]

theorem orbit_mem_finite (transition : Matrix S S ℝ) (targets : I → S → ℝ)
    (time : ℕ) (index : I) :
    (transition ^ time) *ᵥ targets index ∈ finiteOrbitSpan transition targets := by
  rw [power_remainder, Matrix.sum_mulVec]
  apply Submodule.sum_mem
  intro earlier hearlier
  rw [Matrix.smul_mulVec]
  apply Submodule.smul_mem
  exact Submodule.subset_span ⟨(⟨earlier, Finset.mem_range.mp hearlier⟩, index), rfl⟩

/-- The report's finite Krylov space is exactly the minimal invariant space,
not merely an invariant space containing the targets. -/
theorem finiteOrbitSpan_eq (transition : Matrix S S ℝ) (targets : I → S → ℝ) :
    finiteOrbitSpan transition targets = orbitSpan transition.toLin' targets := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro observable ⟨⟨time, index⟩, rfl⟩
    simpa only [← Matrix.toLin'_pow, Matrix.toLin'_apply] using
      orbit_mem transition.toLin' targets time index
  · apply Submodule.span_le.mpr
    rintro observable ⟨⟨time, index⟩, rfl⟩
    simpa only [← Matrix.toLin'_pow, Matrix.toLin'_apply] using
      orbit_mem_finite transition targets time index

theorem finiteOrbitSpan_invariant (transition : Matrix S S ℝ) (targets : I → S → ℝ) :
    Invariant transition.toLin' (finiteOrbitSpan transition targets) := by
  rw [finiteOrbitSpan_eq]
  exact orbitSpan_invariant _ _

theorem finiteOrbitSpan_minimal (transition : Matrix S S ℝ) (targets : I → S → ℝ)
    (space : Submodule ℝ (S → ℝ)) (hinvariant : Invariant transition.toLin' space)
    (htargets : ∀ index, targets index ∈ space) : finiteOrbitSpan transition targets ≤ space := by
  rw [finiteOrbitSpan_eq]
  exact orbitSpan_minimal _ _ _ hinvariant htargets

end Descent.Portability.MinimalObservableLaw
