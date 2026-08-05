/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Coalescent.Restriction
import Descent.Coalescent.Kernel
import Mathlib.Tactic

namespace Descent

/-!
# Seating the `(n+1)`-th sample: the fibres of restriction

`Descent.Coalescent.Program` lists the Ewens normalisation
`Σ_{ξ ∈ 𝓔ₙ} θ^{|ξ|-1} ∏(λ_a - 1)! = (θ+1)⋯(θ+n-1)` as open, and names what it needs: the
decomposition of `𝓔_{n+1}` over `𝓔ₙ` in which the new element either starts a class or joins
an existing one.  That decomposition is the Chinese restaurant, and it is what this file
builds.

The construction is one map.  Given `ξ` on `{1, …, n}` and a choice `o` -- either a class of
`ξ` to join, or `none` for a new class -- send `x` to `some ⟦x⟧` when `x ≤ n` and to `o`
when `x = n+1`, and take the kernel.  Being a kernel, it is an equivalence relation with no
argument; being this particular kernel, it restricts to `ξ` and seats the new element
exactly where `o` says.

Three theorems make it the fibre decomposition rather than merely a construction:
`restrict_extend` (every extension lies over `ξ`), `extend_injective` (distinct choices give
distinct extensions), and `exists_extend` (every relation on `n+1` elements is an extension
of its own restriction).  Together they say the fibre of restriction over `ξ` is
`Option (Quotient ξ)` -- which is the `θ + n` of the Chinese restaurant recursion, once each
choice is weighted.

What remains for the Ewens normalisation after this file is the weighting: that joining a
class of size `λ` multiplies `∏(λ_a - 1)!` by `λ` while leaving `|ξ|` alone, and that
starting a class multiplies `θ^{|ξ|-1}` by `θ` while leaving the factorials alone.  The
block-count half of that is proved here (`blocks_extend_none`, `blocks_extend_some`); the
class-size half is not.  The gap named in `Program` is therefore narrower after this file,
and it is still a gap.

## Main results

- `extend`: seat the new element, either at a named class or alone.
- `restrict_extend`: the extension lies over `ξ`.  K-G (7.1) applied to the construction.
- `extend_injective`: distinct seatings give distinct relations.
- `exists_extend`: every relation on `n+1` elements arises this way.
- `blocks_extend_none`, `blocks_extend_some`: a new class adds a block; joining one does not.
-/

namespace Coalescent

open scoped Classical

/-- Where the extension sends each element: an existing class for the first `n`, and the
choice `o` for the new one. -/
noncomputable def extendMap {n : ℕ} (ξ : ER n) (o : Option (Quotient ξ)) :
    Fin (n + 1) → Option (Quotient ξ) :=
  fun x => if h : (x : ℕ) < n then some (Quotient.mk ξ ⟨x, h⟩) else o

/-- **Seat the `(n+1)`-th sample.**  `extend ξ (some c)` puts it in class `c`; `extend ξ none`
gives it a class of its own.

Empirical status: NOT AN EMPIRICAL CLAIM.  A construction of relations on `n+1` elements
from relations on `n`. -/
noncomputable def extend {n : ℕ} (ξ : ER n) (o : Option (Quotient ξ)) : ER (n + 1) :=
  Setoid.ker (extendMap ξ o)

theorem extendMap_of_lt {n : ℕ} (ξ : ER n) (o : Option (Quotient ξ)) (x : Fin (n + 1))
    (h : (x : ℕ) < n) : extendMap ξ o x = some (Quotient.mk ξ ⟨x, h⟩) := dif_pos h

theorem extendMap_castLE {n : ℕ} (ξ : ER n) (o : Option (Quotient ξ)) (x : Fin n) :
    extendMap ξ o (Fin.castLE (Nat.le_succ n) x) = some (Quotient.mk ξ x) := by
  have h : ((Fin.castLE (Nat.le_succ n) x : Fin (n + 1)) : ℕ) < n := x.isLt
  rw [extendMap_of_lt ξ o _ h]
  congr 1

theorem extendMap_last {n : ℕ} (ξ : ER n) (o : Option (Quotient ξ)) :
    extendMap ξ o (Fin.last n) = o := by
  refine dif_neg ?_
  simp

/-- Every element other than the new one is below `n`. -/
theorem eq_last_of_not_lt {n : ℕ} {x : Fin (n + 1)} (h : ¬ (x : ℕ) < n) : x = Fin.last n := by
  refine Fin.ext ?_
  have := x.isLt
  simp only [Fin.val_last]
  omega

/-- **The extension lies over `ξ`.**  Discarding the new element returns the relation we
started from, so `extend` really does parametrise the fibre of restriction. -/
theorem restrict_extend {n : ℕ} (ξ : ER n) (o : Option (Quotient ξ)) :
    restrict (Nat.le_succ n) (extend ξ o) = ξ := by
  refine Setoid.ext fun x y => ?_
  constructor
  · intro h
    have h' : extendMap ξ o (Fin.castLE (Nat.le_succ n) x)
        = extendMap ξ o (Fin.castLE (Nat.le_succ n) y) := h
    rw [extendMap_castLE, extendMap_castLE] at h'
    exact Quotient.exact (Option.some_injective _ h')
  · intro h
    show extendMap ξ o (Fin.castLE (Nat.le_succ n) x)
        = extendMap ξ o (Fin.castLE (Nat.le_succ n) y)
    rw [extendMap_castLE, extendMap_castLE, Quotient.sound h]

/-- The new element joins the class it was told to. -/
theorem extend_last_rel {n : ℕ} (ξ : ER n) (c : Quotient ξ) (x : Fin n) :
    (extend ξ (some c)).r (Fin.castLE (Nat.le_succ n) x) (Fin.last n)
      ↔ Quotient.mk ξ x = c := by
  constructor
  · intro h
    have h' : extendMap ξ (some c) (Fin.castLE (Nat.le_succ n) x)
        = extendMap ξ (some c) (Fin.last n) := h
    rw [extendMap_castLE, extendMap_last] at h'
    exact Option.some_injective _ h'
  · intro h
    show extendMap ξ (some c) (Fin.castLE (Nat.le_succ n) x)
        = extendMap ξ (some c) (Fin.last n)
    rw [extendMap_castLE, extendMap_last, h]

/-- A new class is a class of its own: the new element is related to nothing before it. -/
theorem extend_none_last_not_rel {n : ℕ} (ξ : ER n) (x : Fin n) :
    ¬ (extend ξ none).r (Fin.castLE (Nat.le_succ n) x) (Fin.last n) := by
  intro h
  have h' : extendMap ξ none (Fin.castLE (Nat.le_succ n) x)
      = extendMap ξ none (Fin.last n) := h
  rw [extendMap_castLE, extendMap_last] at h'
  exact Option.noConfusion h'

/-- **Distinct seatings give distinct relations.**  Joining different classes relates the new
element to different elements, and starting a new class relates it to none of them. -/
theorem extend_injective {n : ℕ} (ξ : ER n) : Function.Injective (extend ξ) := by
  intro o o' h
  match o, o' with
  | none, none => rfl
  | none, some c =>
      exfalso
      obtain ⟨x, hx⟩ := quotient_mk_surjective ξ c
      have hrel : (extend ξ (some c)).r (Fin.castLE (Nat.le_succ n) x) (Fin.last n) :=
        (extend_last_rel ξ c x).mpr hx
      rw [← h] at hrel
      exact extend_none_last_not_rel ξ x hrel
  | some c, none =>
      exfalso
      obtain ⟨x, hx⟩ := quotient_mk_surjective ξ c
      have hrel : (extend ξ (some c)).r (Fin.castLE (Nat.le_succ n) x) (Fin.last n) :=
        (extend_last_rel ξ c x).mpr hx
      rw [h] at hrel
      exact extend_none_last_not_rel ξ x hrel
  | some c, some c' =>
      obtain ⟨x, hx⟩ := quotient_mk_surjective ξ c
      have hrel : (extend ξ (some c)).r (Fin.castLE (Nat.le_succ n) x) (Fin.last n) :=
        (extend_last_rel ξ c x).mpr hx
      rw [h] at hrel
      have := (extend_last_rel ξ c' x).mp hrel
      rw [hx] at this
      rw [this]

/-- **Every relation on `n+1` elements is an extension of its own restriction.**  With
`restrict_extend` and `extend_injective`, this is the fibre decomposition: restriction over
`ξ` has fibre `Option (Quotient ξ)`, which is the Chinese restaurant's "join a class or start
one". -/
theorem exists_extend {n : ℕ} (ζ : ER (n + 1)) :
    ∃ o : Option (Quotient (restrict (Nat.le_succ n) ζ)),
      ζ = extend (restrict (Nat.le_succ n) ζ) o := by
  classical
  set ξ := restrict (Nat.le_succ n) ζ with hξ
  by_cases hjoin : ∃ x : Fin n, ζ.r (Fin.castLE (Nat.le_succ n) x) (Fin.last n)
  · obtain ⟨x₀, hx₀⟩ := hjoin
    refine ⟨some (Quotient.mk ξ x₀), ?_⟩
    refine Setoid.ext fun u v => ?_
    rcases lt_or_ge (u : ℕ) n with hu | hu
    · rcases lt_or_ge (v : ℕ) n with hv | hv
      · -- both old: the relation is `ξ`, and both maps agree there
        constructor
        · intro huv
          show extendMap ξ _ u = extendMap ξ _ v
          rw [extendMap_of_lt ξ _ u hu, extendMap_of_lt ξ _ v hv]
          have : ξ.r ⟨u, hu⟩ ⟨v, hv⟩ := huv
          rw [Quotient.sound this]
        · intro huv
          have h' : extendMap ξ (some (Quotient.mk ξ x₀)) u
              = extendMap ξ (some (Quotient.mk ξ x₀)) v := huv
          rw [extendMap_of_lt ξ _ u hu, extendMap_of_lt ξ _ v hv] at h'
          exact Quotient.exact (Option.some_injective _ h')
      · -- `v` is the new element
        have hvlast : v = Fin.last n := eq_last_of_not_lt (by omega)
        subst hvlast
        constructor
        · intro huv
          show extendMap ξ _ u = extendMap ξ _ (Fin.last n)
          rw [extendMap_of_lt ξ _ u hu, extendMap_last]
          have hux₀ : ξ.r ⟨u, hu⟩ x₀ :=
            ζ.iseqv.trans huv (ζ.iseqv.symm hx₀)
          rw [Quotient.sound hux₀]
        · intro huv
          have h' : extendMap ξ (some (Quotient.mk ξ x₀)) u
              = extendMap ξ (some (Quotient.mk ξ x₀)) (Fin.last n) := huv
          rw [extendMap_of_lt ξ _ u hu, extendMap_last] at h'
          have hq : Quotient.mk ξ ⟨u, hu⟩ = Quotient.mk ξ x₀ := Option.some_injective _ h'
          have hux₀ : ζ.r (Fin.castLE (Nat.le_succ n) ⟨u, hu⟩)
              (Fin.castLE (Nat.le_succ n) x₀) := Quotient.exact hq
          have huu : (Fin.castLE (Nat.le_succ n) (⟨u, hu⟩ : Fin n)) = u := Fin.ext rfl
          rw [huu] at hux₀
          exact ζ.iseqv.trans hux₀ hx₀
    · -- `u` is the new element; symmetric
      have hulast : u = Fin.last n := eq_last_of_not_lt (by omega)
      subst hulast
      rcases lt_or_ge (v : ℕ) n with hv | hv
      · constructor
        · intro huv
          show extendMap ξ _ (Fin.last n) = extendMap ξ _ v
          rw [extendMap_of_lt ξ _ v hv, extendMap_last]
          have hvx₀ : ξ.r ⟨v, hv⟩ x₀ := ζ.iseqv.trans (ζ.iseqv.symm huv) (ζ.iseqv.symm hx₀)
          rw [Quotient.sound hvx₀]
        · intro huv
          have h' : extendMap ξ (some (Quotient.mk ξ x₀)) (Fin.last n)
              = extendMap ξ (some (Quotient.mk ξ x₀)) v := huv
          rw [extendMap_of_lt ξ _ v hv, extendMap_last] at h'
          have hq : Quotient.mk ξ ⟨v, hv⟩ = Quotient.mk ξ x₀ := (Option.some_injective _ h').symm
          have hvx₀ : ζ.r (Fin.castLE (Nat.le_succ n) ⟨v, hv⟩)
              (Fin.castLE (Nat.le_succ n) x₀) := Quotient.exact hq
          have hvv : (Fin.castLE (Nat.le_succ n) (⟨v, hv⟩ : Fin n)) = v := Fin.ext rfl
          rw [hvv] at hvx₀
          exact ζ.iseqv.symm (ζ.iseqv.trans hvx₀ hx₀)
      · have hvlast : v = Fin.last n := eq_last_of_not_lt (by omega)
        subst hvlast
        exact ⟨fun _ => (extend ξ _).iseqv.refl _, fun _ => ζ.iseqv.refl _⟩
  · push_neg at hjoin
    refine ⟨none, ?_⟩
    refine Setoid.ext fun u v => ?_
    rcases lt_or_ge (u : ℕ) n with hu | hu
    · rcases lt_or_ge (v : ℕ) n with hv | hv
      · constructor
        · intro huv
          show extendMap ξ _ u = extendMap ξ _ v
          rw [extendMap_of_lt ξ _ u hu, extendMap_of_lt ξ _ v hv]
          have : ξ.r ⟨u, hu⟩ ⟨v, hv⟩ := huv
          rw [Quotient.sound this]
        · intro huv
          have h' : extendMap ξ (none : Option (Quotient ξ)) u
              = extendMap ξ none v := huv
          rw [extendMap_of_lt ξ _ u hu, extendMap_of_lt ξ _ v hv] at h'
          exact Quotient.exact (Option.some_injective _ h')
      · have hvlast : v = Fin.last n := eq_last_of_not_lt (by omega)
        subst hvlast
        constructor
        · intro huv
          exfalso
          have huu : (Fin.castLE (Nat.le_succ n) (⟨u, hu⟩ : Fin n)) = u := Fin.ext rfl
          exact hjoin ⟨⟨u, hu⟩, by rw [huu]; exact huv⟩
        · intro huv
          exfalso
          have h' : extendMap ξ (none : Option (Quotient ξ)) u
              = extendMap ξ none (Fin.last n) := huv
          rw [extendMap_of_lt ξ _ u hu, extendMap_last] at h'
          exact Option.noConfusion h'
    · have hulast : u = Fin.last n := eq_last_of_not_lt (by omega)
      subst hulast
      rcases lt_or_ge (v : ℕ) n with hv | hv
      · constructor
        · intro huv
          exfalso
          have hvv : (Fin.castLE (Nat.le_succ n) (⟨v, hv⟩ : Fin n)) = v := Fin.ext rfl
          exact hjoin ⟨⟨v, hv⟩, by rw [hvv]; exact ζ.iseqv.symm huv⟩
        · intro huv
          exfalso
          have h' : extendMap ξ (none : Option (Quotient ξ)) (Fin.last n)
              = extendMap ξ none v := huv
          rw [extendMap_of_lt ξ _ v hv, extendMap_last] at h'
          exact Option.noConfusion h'.symm
      · have hvlast : v = Fin.last n := eq_last_of_not_lt (by omega)
        subst hvlast
        exact ⟨fun _ => (extend ξ _).iseqv.refl _, fun _ => ζ.iseqv.refl _⟩

/-! ### The block count across a seating

Half of the Chinese-restaurant weight is the block count: starting a class raises `|ξ|` by
one and joining a class leaves it alone.  Both come from the image of `extendMap`. -/

/-- Starting a new class adds a block. -/
theorem blocks_extend_none {n : ℕ} (ξ : ER n) : blocks (extend ξ none) = blocks ξ + 1 := by
  classical
  have hrange : Set.range (extendMap ξ none) = Set.univ := by
    ext y
    simp only [Set.mem_univ, iff_true]
    match y with
    | none => exact ⟨Fin.last n, extendMap_last ξ none⟩
    | some c =>
        obtain ⟨x, hx⟩ := quotient_mk_surjective ξ c
        exact ⟨Fin.castLE (Nat.le_succ n) x, by rw [extendMap_castLE, hx]⟩
  unfold blocks extend
  rw [Nat.card_congr (Setoid.quotientKerEquivRange _),
    Nat.card_congr (Equiv.setCongr hrange), Nat.card_congr (Equiv.Set.univ _),
    Nat.card_option]

/-- Joining an existing class does not. -/
theorem blocks_extend_some {n : ℕ} (ξ : ER n) (c : Quotient ξ) :
    blocks (extend ξ (some c)) = blocks ξ := by
  classical
  have hrange : Set.range (extendMap ξ (some c))
      = Set.range (some : Quotient ξ → Option (Quotient ξ)) := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      rcases lt_or_ge (x : ℕ) n with hx | hx
      · exact ⟨Quotient.mk ξ ⟨x, hx⟩, (extendMap_of_lt ξ _ x hx).symm⟩
      · rw [eq_last_of_not_lt (by omega), extendMap_last]
        exact ⟨c, rfl⟩
    · rintro ⟨d, rfl⟩
      obtain ⟨x, hx⟩ := quotient_mk_surjective ξ d
      exact ⟨Fin.castLE (Nat.le_succ n) x, by rw [extendMap_castLE, hx]⟩
  unfold blocks extend
  rw [Nat.card_congr (Setoid.quotientKerEquivRange _), Nat.card_congr (Equiv.setCongr hrange)]
  exact (Nat.card_congr (Equiv.ofInjective _ (Option.some_injective (Quotient ξ)))).symm

end Coalescent

end Descent
