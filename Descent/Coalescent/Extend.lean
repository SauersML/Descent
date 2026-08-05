/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Coalescent.Restriction
import Descent.Coalescent.Kernel
import Mathlib.Data.Finite.Card
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
  match o, o' with | none, none => rfl
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
          have h2 : Quotient.mk ξ (⟨(u : ℕ), hu⟩ : Fin n)
              = Quotient.mk ξ (⟨(v : ℕ), hv⟩ : Fin n) := Option.some_injective _ h'
          have h3ξ : ξ.r (⟨(u : ℕ), hu⟩ : Fin n) (⟨(v : ℕ), hv⟩ : Fin n) := Quotient.exact h2
          have h3 : ζ.r (Fin.castLE (Nat.le_succ n) (⟨(u : ℕ), hu⟩ : Fin n))
              (Fin.castLE (Nat.le_succ n) (⟨(v : ℕ), hv⟩ : Fin n)) := h3ξ
          have hu' : (Fin.castLE (Nat.le_succ n) (⟨(u : ℕ), hu⟩ : Fin n)) = u := Fin.ext rfl
          have hv' : (Fin.castLE (Nat.le_succ n) (⟨(v : ℕ), hv⟩ : Fin n)) = v := Fin.ext rfl
          rwa [hu', hv'] at h3
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
          have huξ : ξ.r (⟨(u : ℕ), hu⟩ : Fin n) x₀ := Quotient.exact hq
          have hux₀ : ζ.r (Fin.castLE (Nat.le_succ n) (⟨(u : ℕ), hu⟩ : Fin n))
              (Fin.castLE (Nat.le_succ n) x₀) := huξ
          have huu : (Fin.castLE (Nat.le_succ n) (⟨(u : ℕ), hu⟩ : Fin n)) = u := Fin.ext rfl
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
          have hvξ : ξ.r (⟨(v : ℕ), hv⟩ : Fin n) x₀ := Quotient.exact hq
          have hvx₀ : ζ.r (Fin.castLE (Nat.le_succ n) (⟨(v : ℕ), hv⟩ : Fin n))
              (Fin.castLE (Nat.le_succ n) x₀) := hvξ
          have hvv : (Fin.castLE (Nat.le_succ n) (⟨(v : ℕ), hv⟩ : Fin n)) = v := Fin.ext rfl
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
          have h2 : Quotient.mk ξ (⟨(u : ℕ), hu⟩ : Fin n)
              = Quotient.mk ξ (⟨(v : ℕ), hv⟩ : Fin n) := Option.some_injective _ h'
          have h3ξ : ξ.r (⟨(u : ℕ), hu⟩ : Fin n) (⟨(v : ℕ), hv⟩ : Fin n) := Quotient.exact h2
          have h3 : ζ.r (Fin.castLE (Nat.le_succ n) (⟨(u : ℕ), hu⟩ : Fin n))
              (Fin.castLE (Nat.le_succ n) (⟨(v : ℕ), hv⟩ : Fin n)) := h3ξ
          have hu' : (Fin.castLE (Nat.le_succ n) (⟨(u : ℕ), hu⟩ : Fin n)) = u := Fin.ext rfl
          have hv' : (Fin.castLE (Nat.le_succ n) (⟨(v : ℕ), hv⟩ : Fin n)) = v := Fin.ext rfl
          rwa [hu', hv'] at h3
      · have hvlast : v = Fin.last n := eq_last_of_not_lt (by omega)
        subst hvlast
        constructor
        · intro huv
          exfalso
          refine hjoin (⟨(u : ℕ), hu⟩ : Fin n) ?_
          have huu : (Fin.castLE (Nat.le_succ n) (⟨(u : ℕ), hu⟩ : Fin n)) = u := Fin.ext rfl
          rw [huu]
          exact huv
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
          refine hjoin (⟨(v : ℕ), hv⟩ : Fin n) ?_
          have hvv : (Fin.castLE (Nat.le_succ n) (⟨(v : ℕ), hv⟩ : Fin n)) = v := Fin.ext rfl
          rw [hvv]
          exact ζ.iseqv.symm huv
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
    match y with | none => exact ⟨Fin.last n, extendMap_last ξ none⟩
    | some c =>
        obtain ⟨x, hx⟩ := quotient_mk_surjective ξ c
        exact ⟨Fin.castLE (Nat.le_succ n) x, by rw [extendMap_castLE, hx]⟩
  unfold blocks extend
  rw [Nat.card_congr (Setoid.quotientKerEquivRange _),
    Nat.card_congr (Equiv.setCongr hrange), Nat.card_congr (Equiv.Set.univ _)]
  simp

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
      · rw [eq_last_of_not_lt (x := x) (by omega), extendMap_last]
        exact ⟨c, rfl⟩
    · rintro ⟨d, rfl⟩
      obtain ⟨x, hx⟩ := quotient_mk_surjective ξ d
      exact ⟨Fin.castLE (Nat.le_succ n) x, by rw [extendMap_castLE, hx]⟩
  unfold blocks extend
  rw [Nat.card_congr (Setoid.quotientKerEquivRange _), Nat.card_congr (Equiv.setCongr hrange)]
  exact (Nat.card_congr (Equiv.ofInjective _ (Option.some_injective (Quotient ξ)))).symm

/-! ### Class sizes across a seating

The other half of the Chinese-restaurant weight.  Kingman's `λ₁, …, λ_k` are the class
sizes, and what the recursion needs is that seating the new element at class `c` raises
`λ_c` by one and leaves every other class alone.  Each statement below is the cardinality of
one fibre of `extendMap`, and the fibres of `extendMap` ARE the classes of the extension --
that is what `Setoid.ker` means. -/

/-- `λ_c`, the size of a class.  Kingman's `λ` in K-C (2.3) and K-G (3.8). -/
noncomputable def classSize {n : ℕ} (ξ : ER n) (c : Quotient ξ) : ℕ :=
  (Finset.univ.filter fun x : Fin n => Quotient.mk ξ x = c).card

/-- **`λ₁ + ⋯ + λ_k = n`.**  The class sizes of a relation on a sample of `n` sum to `n`.
`Descent.Coalescent.JumpChain.absoluteProb_recursion` takes this as a hypothesis on its
multiset of sizes; here it is a theorem about the relation those sizes come from. -/
theorem sum_classSize {n : ℕ} (ξ : ER n) :
    ∑ c : Quotient ξ, classSize ξ c = n := by
  classical
  have h := Finset.card_eq_sum_card_fiberwise
    (f := fun x : Fin n => Quotient.mk ξ x) (s := (Finset.univ : Finset (Fin n)))
    (t := (Finset.univ : Finset (Quotient ξ))) (fun x _ => Finset.mem_univ _)
  rw [Finset.card_univ, Fintype.card_fin] at h
  exact h.symm

/-- Seating at `c` leaves every other class untouched. -/
theorem card_fiber_of_ne {n : ℕ} (ξ : ER n) (c d : Quotient ξ) (hne : d ≠ c) :
    Nat.card {x : Fin (n + 1) // extendMap ξ (some c) x = some d}
      = Nat.card {x : Fin n // Quotient.mk ξ x = d} := by
  classical
  refine (Nat.card_eq_of_bijective
    (fun p : {x : Fin n // Quotient.mk ξ x = d} =>
      (⟨Fin.castLE (Nat.le_succ n) p.1, by rw [extendMap_castLE, p.2]⟩ :
        {x : Fin (n + 1) // extendMap ξ (some c) x = some d})) ?_).symm
  constructor
  · rintro ⟨x, hx⟩ ⟨y, hy⟩ h
    have hval : (x : ℕ) = (y : ℕ) := congrArg (fun q => (q.1 : ℕ)) h
    exact Subtype.ext (Fin.ext hval)
  · rintro ⟨y, hy⟩
    rcases lt_or_ge (y : ℕ) n with hylt | hyge
    · refine ⟨⟨⟨y, hylt⟩, ?_⟩, ?_⟩
      · rw [extendMap_of_lt ξ _ y hylt] at hy
        exact Option.some_injective _ hy
      · exact Subtype.ext (Fin.ext rfl)
    · exfalso
      rw [eq_last_of_not_lt (x := y) (by omega), extendMap_last] at hy
      exact hne (Option.some_injective _ hy).symm

/-- Seating at `c` raises `λ_c` by exactly one. -/
theorem card_fiber_self {n : ℕ} (ξ : ER n) (c : Quotient ξ) :
    Nat.card {x : Fin (n + 1) // extendMap ξ (some c) x = some c}
      = Nat.card {x : Fin n // Quotient.mk ξ x = c} + 1 := by
  classical
  have hbij : Function.Bijective
      (fun p : Option {x : Fin n // Quotient.mk ξ x = c} =>
        (match p with | none => ⟨Fin.last n, by rw [extendMap_last]⟩
          | some q => ⟨Fin.castLE (Nat.le_succ n) q.1, by rw [extendMap_castLE, q.2]⟩ :
            {x : Fin (n + 1) // extendMap ξ (some c) x = some c})) := by
    constructor
    · intro p q h
      match p, q with | none, none => rfl
      | none, some b =>
          exfalso
          have hval : (n : ℕ) = (b.1 : ℕ) := congrArg (fun r => (r.1 : ℕ)) h
          exact absurd b.1.isLt (by omega)
      | some a, none =>
          exfalso
          have hval : (a.1 : ℕ) = (n : ℕ) := congrArg (fun r => (r.1 : ℕ)) h
          exact absurd a.1.isLt (by omega)
      | some a, some b =>
          have hval : (a.1 : ℕ) = (b.1 : ℕ) := congrArg (fun r => (r.1 : ℕ)) h
          exact congrArg some (Subtype.ext (Fin.ext hval))
    · rintro ⟨y, hy⟩
      rcases lt_or_ge (y : ℕ) n with hylt | hyge
      · refine ⟨some ⟨⟨y, hylt⟩, ?_⟩, ?_⟩
        · rw [extendMap_of_lt ξ _ y hylt] at hy
          exact Option.some_injective _ hy
        · exact Subtype.ext (Fin.ext rfl)
      · exact ⟨none, Subtype.ext (Fin.ext (by simp [eq_last_of_not_lt (by omega : ¬ (y : ℕ) < n)]))⟩
  rw [← Nat.card_eq_of_bijective _ hbij]
  simp

/-- Starting a new class leaves every old class untouched. -/
theorem card_fiber_none_old {n : ℕ} (ξ : ER n) (d : Quotient ξ) :
    Nat.card {x : Fin (n + 1) // extendMap ξ none x = some d}
      = Nat.card {x : Fin n // Quotient.mk ξ x = d} := by
  classical
  refine (Nat.card_eq_of_bijective
    (fun p : {x : Fin n // Quotient.mk ξ x = d} =>
      (⟨Fin.castLE (Nat.le_succ n) p.1, by rw [extendMap_castLE, p.2]⟩ :
        {x : Fin (n + 1) // extendMap ξ none x = some d})) ?_).symm
  constructor
  · rintro ⟨x, hx⟩ ⟨y, hy⟩ h
    have hval : (x : ℕ) = (y : ℕ) := congrArg (fun q => (q.1 : ℕ)) h
    exact Subtype.ext (Fin.ext hval)
  · rintro ⟨y, hy⟩
    rcases lt_or_ge (y : ℕ) n with hylt | hyge
    · refine ⟨⟨⟨y, hylt⟩, ?_⟩, ?_⟩
      · rw [extendMap_of_lt ξ _ y hylt] at hy
        exact Option.some_injective _ hy
      · exact Subtype.ext (Fin.ext rfl)
    · exfalso
      rw [eq_last_of_not_lt (x := y) (by omega), extendMap_last] at hy
      exact Option.noConfusion hy

/-- And the class it starts is a singleton -- the `(λ - 1)! = 0! = 1` that leaves the
factorial product unchanged when a new class opens. -/
theorem card_fiber_none_new {n : ℕ} (ξ : ER n) :
    Nat.card {x : Fin (n + 1) // extendMap ξ none x = none} = 1 := by
  classical
  have hbij : Function.Bijective
      (fun _ : Unit => (⟨Fin.last n, by rw [extendMap_last]⟩ :
        {x : Fin (n + 1) // extendMap ξ none x = none})) := by
    constructor
    · rintro ⟨⟩ ⟨⟩ _
      rfl
    · rintro ⟨y, hy⟩
      refine ⟨(), Subtype.ext (Fin.ext ?_)⟩
      rcases lt_or_ge (y : ℕ) n with hylt | hyge
      · exfalso
        rw [extendMap_of_lt ξ _ y hylt] at hy
        exact Option.noConfusion hy
      · simp [eq_last_of_not_lt (by omega : ¬ (y : ℕ) < n)]
  rw [← Nat.card_eq_of_bijective _ hbij]
  simp

end Coalescent

end Descent
