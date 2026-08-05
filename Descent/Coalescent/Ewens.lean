/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Coalescent.Extend
import Mathlib.Tactic

namespace Descent

/-!
# Summing over `𝓔ₙ` one seat at a time

`Descent.Coalescent.Extend` shows the fibre of restriction over `ξ` is `Option (Quotient ξ)`.
This file cashes that in as a summation rule: any sum over `𝓔_{n+1}` is a sum over `𝓔ₙ` of a
sum over seatings.  That is the shape every Chinese-restaurant argument needs, and the Ewens
normalisation is the case where the summand is `θ^{|ξ|-1} ∏(λ_a - 1)!`.

The step that made this awkward, and the reason `Descent.Coalescent.Program` listed it
separately from the fibre theorems, is a dependent-type one: `exists_extend` produces a
seating in `Option (Quotient (ρ ζ))`, indexed by the restriction of `ζ` itself, while the sum
ranges over `Option (Quotient ξ)` for a fixed `ξ`.  Inside the fibre those two are the same
type, but only because `ρ ζ = ξ` -- which is a hypothesis, not a definitional equality.
Substituting it is what `sum_fiber_eq_sum_seatings` does, and it is why that proof exists at
all rather than being a one-line rewrite.

What is still not here, and is still listed as open: the weight identity
`w(extend ξ o) = (if o = none then θ else λ_o) · w(ξ)`.  Its ingredients are all proved --
`blocks_extend_none`, `blocks_extend_some` for the `θ^{|ξ|-1}` factor, and `card_fiber_self`,
`card_fiber_of_ne`, `card_fiber_none_old`, `card_fiber_none_new` for the `∏(λ_a - 1)!`
factor -- but turning class-size facts into a statement about the product over
`Quotient (extend ξ o)` needs a transfer of products along
`Quotient (Setoid.ker f) ≃ range f`, and that is not written.  With it, this file's
`sum_ER_succ` gives the recursion `Σ_{𝓔_{n+1}} w = (θ + n) Σ_{𝓔ₙ} w` immediately.

## Main results

- `subsingleton_ER_one`: there is only one relation on a sample of one.
- `sum_fiber_eq_sum_seatings`: the fibre of restriction over `ξ` sums as `Option (Quotient ξ)`.
- `sum_ER_succ`: any sum over `𝓔_{n+1}` decomposes over `𝓔ₙ` by seating.
-/

namespace Coalescent

open scoped Classical

/-- A sample of one admits exactly one relation, so sums over `𝓔₁` are single terms.  This
is the base of the Chinese-restaurant induction: Kingman's `θ^{k-1}` normalisation makes the
first class free, so the recursion starts at `n = 1`, not at `n = 0`. -/
instance subsingleton_ER_one : Subsingleton (ER 1) :=
  ⟨fun ξ η => Setoid.ext fun x y => by
    have hxy : x = y := Subsingleton.elim x y
    subst hxy
    exact ⟨fun _ => η.iseqv.refl x, fun _ => ξ.iseqv.refl x⟩⟩

theorem sum_ER_one {M : Type*} [AddCommMonoid M] (w : ER 1 → M) :
    ∑ ξ : ER 1, w ξ = w ⊥ := by
  classical
  rw [Finset.sum_congr rfl (fun ξ _ => congrArg w (Subsingleton.elim ξ (⊥ : ER 1)))]
  rw [Finset.sum_const, Finset.card_univ]
  have hcard : Fintype.card (ER 1) = 1 := Fintype.card_eq_one_iff.mpr ⟨⊥, fun ξ => Subsingleton.elim ξ ⊥⟩
  rw [hcard, one_smul]

/-- **The fibre of restriction sums as a sum over seatings.**

The dependent step: `exists_extend` hands back a seating indexed by `Quotient (ρ ζ)`, and the
sum wants one indexed by `Quotient ξ`.  Inside the fibre `ρ ζ = ξ`, so the two agree -- but
by a hypothesis rather than definitionally, and it has to be substituted. -/
theorem sum_fiber_eq_sum_seatings {n : ℕ} (ξ : ER n) (w : ER (n + 1) → ℝ) :
    ∑ o : Option (Quotient ξ), w (extend ξ o)
      = ∑ ζ ∈ Finset.univ.filter (fun ζ : ER (n + 1) =>
          restrict (Nat.le_succ n) ζ = ξ), w ζ := by
  classical
  refine Finset.sum_bij (fun (o : Option (Quotient ξ)) _ => extend ξ o) ?_ ?_ ?_ ?_
  · intro o _
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, restrict_extend ξ o⟩
  · intro o _ o' _ h
    exact extend_injective ξ h
  · intro ζ hζ
    have hres : restrict (Nat.le_succ n) ζ = ξ := (Finset.mem_filter.mp hζ).2
    subst hres
    obtain ⟨o, ho⟩ := exists_extend ζ
    exact ⟨o, Finset.mem_univ _, ho⟩
  · intro o _
    rfl

/-- **Any sum over `𝓔_{n+1}` decomposes over `𝓔ₙ` by seating the new sample.**

This is the summation rule behind every Chinese-restaurant argument.  Applied to the Ewens
weight it gives `Σ_{𝓔_{n+1}} w = (θ + n) Σ_{𝓔ₙ} w` as soon as the weight of a seating is
known, which is the one step `Descent.Coalescent.Program` still lists as open. -/
theorem sum_ER_succ {n : ℕ} (w : ER (n + 1) → ℝ) :
    ∑ ζ : ER (n + 1), w ζ = ∑ ξ : ER n, ∑ o : Option (Quotient ξ), w (extend ξ o) := by
  classical
  have hmaps : ∀ ζ ∈ (Finset.univ : Finset (ER (n + 1))),
      restrict (Nat.le_succ n) ζ ∈ (Finset.univ : Finset (ER n)) :=
    fun ζ _ => Finset.mem_univ _
  have hfib := Finset.sum_fiberwise_of_maps_to hmaps w
  rw [← hfib]
  exact Finset.sum_congr rfl fun ξ _ => (sum_fiber_eq_sum_seatings ξ w).symm

/-- The seatings of a sample into `k` existing classes number `k + 1`: join one of the `k`,
or start a new one.  This is the `θ + n` of the recursion before the weights are attached --
`n` of the seats are elements, one is the new class, and `sum_classSize` is what turns
"one seat per class" into "one seat per element". -/
theorem card_seatings {n : ℕ} (ξ : ER n) :
    Nat.card (Option (Quotient ξ)) = blocks ξ + 1 := by
  rw [Nat.card_option]
  rfl

/-! ### Transferring products from classes to fibres

A class of `Setoid.ker f` IS a fibre of `f`, so a product over classes is a product over the
distinct values of `f`.  That is the transfer `Descent.Coalescent.Program` named as the last
missing piece of the Ewens item, and with it the class-size facts of
`Descent.Coalescent.Extend` become facts about the Ewens weight. -/

/-- The size of the class of `x` is the size of the fibre of `f` over `f x`. -/
theorem classSize_ker {m : ℕ} {β : Type*} [DecidableEq β] (f : Fin m → β) (x : Fin m) :
    classSize (Setoid.ker f) (Quotient.mk _ x)
      = (Finset.univ.filter fun y => f y = f x).card := by
  classical
  unfold classSize
  congr 1
  ext y
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun h => Quotient.exact h, fun h => Quotient.sound h⟩

/-- **A product over classes is a product over the distinct values of the defining map.** -/
theorem prod_quotient_ker {m : ℕ} {β : Type*} [DecidableEq β] (f : Fin m → β) (g : ℕ → ℝ) :
    ∏ d : Quotient (Setoid.ker f), g (classSize (Setoid.ker f) d)
      = ∏ v ∈ Finset.univ.image f, g ((Finset.univ.filter fun y => f y = v).card) := by
  classical
  refine Finset.prod_bij
    (fun (d : Quotient (Setoid.ker f)) _ => Quotient.liftOn d f fun _ _ h => h) ?_ ?_ ?_ ?_
  · intro d _
    induction d using Quotient.inductionOn with
    | _ x => exact Finset.mem_image.mpr ⟨x, Finset.mem_univ x, rfl⟩
  · intro d _ d' _ h
    induction d using Quotient.inductionOn with
    | _ x =>
        induction d' using Quotient.inductionOn with
        | _ y => exact Quotient.sound (show f x = f y from h)
  · intro v hv
    obtain ⟨x, _, hx⟩ := Finset.mem_image.mp hv
    exact ⟨Quotient.mk _ x, Finset.mem_univ _, hx.symm⟩
  · intro d _
    induction d using Quotient.inductionOn with
    | _ x =>
        show g (classSize (Setoid.ker f) (Quotient.mk _ x)) = _
        rw [classSize_ker]

/-- Fibre cardinalities, as `Finset` cards rather than `Nat.card` of subtypes, which is what
the transfer above consumes. -/
theorem card_filter_eq_card {m : ℕ} {β : Type*} [DecidableEq β] (f : Fin m → β) (v : β) :
    (Finset.univ.filter fun y => f y = v).card = Nat.card {x : Fin m // f x = v} := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

/-- Every class is nonempty, so `λ_c ≥ 1` and `(λ_c - 1)!` is what it should be. -/
theorem one_le_classSize {n : ℕ} (ξ : ER n) (c : Quotient ξ) : 1 ≤ classSize ξ c := by
  classical
  obtain ⟨x, hx⟩ := quotient_mk_surjective ξ c
  refine Finset.card_pos.mpr ⟨x, ?_⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ x, hx⟩

/-- The Ewens weight of K-G (3.8), stripped of its normalising denominator. -/
noncomputable def ewensWeight {n : ℕ} (θ : ℝ) (ξ : ER n) : ℝ :=
  θ ^ (blocks ξ - 1) * ∏ c : Quotient ξ, (((classSize ξ c - 1)! : ℕ) : ℝ)

/-! ### The weight of a seating

Everything above combines into one identity: seating the new sample at a class of size `λ`
multiplies the Ewens weight by `λ`, and starting a new class multiplies it by `θ`.  That is
the Chinese restaurant, and it is what makes the normalisation an induction. -/

theorem image_extendMap_none {n : ℕ} (ξ : ER n) :
    Finset.univ.image (extendMap ξ none) = Finset.univ := by
  classical
  ext v
  simp only [Finset.mem_image, Finset.mem_univ, iff_true, and_true]
  match v with
  | none => exact ⟨Fin.last n, extendMap_last ξ none⟩
  | some c =>
      obtain ⟨x, hx⟩ := quotient_mk_surjective ξ c
      exact ⟨Fin.castLE (Nat.le_succ n) x, by rw [extendMap_castLE, hx]⟩

theorem image_extendMap_some {n : ℕ} (ξ : ER n) (c : Quotient ξ) :
    Finset.univ.image (extendMap ξ (some c))
      = Finset.univ.image (some : Quotient ξ → Option (Quotient ξ)) := by
  classical
  ext v
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨x, rfl⟩
    rcases lt_or_ge (x : ℕ) n with hx | hx
    · exact ⟨Quotient.mk ξ ⟨x, hx⟩, (extendMap_of_lt ξ _ x hx).symm⟩
    · rw [eq_last_of_not_lt (by omega), extendMap_last]
      exact ⟨c, rfl⟩
  · rintro ⟨d, rfl⟩
    obtain ⟨x, hx⟩ := quotient_mk_surjective ξ d
    exact ⟨Fin.castLE (Nat.le_succ n) x, by rw [extendMap_castLE, hx]⟩

/-- **Starting a new class multiplies the weight by `θ`.**  The new class is a singleton, so
`(λ - 1)! = 0! = 1` and the factorial product is untouched; only `θ^{|ξ|-1}` moves. -/
theorem ewensWeight_extend_none {n : ℕ} (θ : ℝ) (ξ : ER n) (hb : 1 ≤ blocks ξ) :
    ewensWeight θ (extend ξ none) = θ * ewensWeight θ ξ := by
  classical
  have hprod : ∏ d : Quotient (extend ξ none), (((classSize (extend ξ none) d - 1)! : ℕ) : ℝ)
      = ∏ c : Quotient ξ, (((classSize ξ c - 1)! : ℕ) : ℝ) := by
    rw [show extend ξ none = Setoid.ker (extendMap ξ none) from rfl,
      prod_quotient_ker (extendMap ξ none) (fun k => (((k - 1)! : ℕ) : ℝ)),
      image_extendMap_none]
    rw [Fintype.prod_option]
    have hnone : (Finset.univ.filter fun y => extendMap ξ none y = none).card = 1 := by
      rw [card_filter_eq_card]
      exact card_fiber_none_new ξ
    have hsome : ∀ d : Quotient ξ,
        (Finset.univ.filter fun y => extendMap ξ none y = some d).card = classSize ξ d := by
      intro d
      rw [card_filter_eq_card, card_fiber_none_old ξ d, ← card_filter_eq_card]
      rfl
    rw [hnone]
    simp only [hsome]
    norm_num
  have hblocks : blocks (extend ξ none) = blocks ξ + 1 := blocks_extend_none ξ
  unfold ewensWeight
  rw [hprod, hblocks]
  have hpow : θ ^ (blocks ξ + 1 - 1) = θ * θ ^ (blocks ξ - 1) := by
    have : blocks ξ + 1 - 1 = (blocks ξ - 1) + 1 := by omega
    rw [this, pow_succ]
    ring
  rw [hpow]
  ring

/-- **Joining a class of size `λ` multiplies the weight by `λ`.**  The block count is
unchanged, so `θ^{|ξ|-1}` stands still; the class grows by one, and `λ!/(λ-1)! = λ`. -/
theorem ewensWeight_extend_some {n : ℕ} (θ : ℝ) (ξ : ER n) (c : Quotient ξ) :
    ewensWeight θ (extend ξ (some c)) = (classSize ξ c : ℝ) * ewensWeight θ ξ := by
  classical
  have hfib : ∀ d : Quotient ξ,
      (Finset.univ.filter fun y => extendMap ξ (some c) y = some d).card
        = classSize ξ d + (if d = c then 1 else 0) := by
    intro d
    by_cases hd : d = c
    · subst hd
      rw [card_filter_eq_card, card_fiber_self ξ d, ← card_filter_eq_card]
      simp [classSize]
    · rw [card_filter_eq_card, card_fiber_of_ne ξ c d hd, ← card_filter_eq_card, if_neg hd]
      simp [classSize]
  have hprod : ∏ d : Quotient (extend ξ (some c)),
        (((classSize (extend ξ (some c)) d - 1)! : ℕ) : ℝ)
      = ∏ d : Quotient ξ, ((((classSize ξ d + (if d = c then 1 else 0)) - 1)! : ℕ) : ℝ) := by
    rw [show extend ξ (some c) = Setoid.ker (extendMap ξ (some c)) from rfl,
      prod_quotient_ker (extendMap ξ (some c)) (fun k => (((k - 1)! : ℕ) : ℝ)),
      image_extendMap_some]
    rw [Finset.prod_image (fun a _ b _ h => Option.some_injective _ h)]
    exact Finset.prod_congr rfl fun d _ => by rw [hfib d]
  have hsplit : ∏ d : Quotient ξ, ((((classSize ξ d + (if d = c then 1 else 0)) - 1)! : ℕ) : ℝ)
      = (classSize ξ c : ℝ) * ∏ d : Quotient ξ, (((classSize ξ d - 1)! : ℕ) : ℝ) := by
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ c),
      ← Finset.mul_prod_erase Finset.univ
        (fun d => (((classSize ξ d - 1)! : ℕ) : ℝ)) (Finset.mem_univ c)]
    have hc : ((((classSize ξ c + (if c = c then 1 else 0)) - 1)! : ℕ) : ℝ)
        = (classSize ξ c : ℝ) * (((classSize ξ c - 1)! : ℕ) : ℝ) := by
      rw [if_pos rfl]
      obtain ⟨m, hm⟩ : ∃ m, classSize ξ c = m + 1 := ⟨classSize ξ c - 1, by
        have := one_le_classSize ξ c
        omega⟩
      rw [hm]
      simp only [Nat.add_sub_cancel]
      rw [show m + 1 + 1 - 1 = m + 1 from by omega, Nat.factorial_succ]
      push_cast
      ring
    have herase : ∏ d ∈ Finset.univ.erase c,
          ((((classSize ξ d + (if d = c then 1 else 0)) - 1)! : ℕ) : ℝ)
        = ∏ d ∈ Finset.univ.erase c, (((classSize ξ d - 1)! : ℕ) : ℝ) :=
      Finset.prod_congr rfl fun d hd => by
        rw [if_neg (Finset.ne_of_mem_erase hd)]
        norm_num
    rw [hc, herase]
    ring
  unfold ewensWeight
  rw [hprod, hsplit, blocks_extend_some ξ c]
  ring

/-- **The seatings of one state contribute `θ + n`.**  This is the Chinese-restaurant
recursion: one seat per element, weighted by which class the element is in, plus the new
class weighted `θ`.  `sum_classSize` is what turns the class sum into `n`. -/
theorem sum_seatings_ewensWeight {n : ℕ} (θ : ℝ) (ξ : ER n) (hb : 1 ≤ blocks ξ) :
    ∑ o : Option (Quotient ξ), ewensWeight θ (extend ξ o)
      = (θ + (n : ℝ)) * ewensWeight θ ξ := by
  classical
  rw [Fintype.sum_option, ewensWeight_extend_none θ ξ hb]
  have hsome : ∀ c : Quotient ξ,
      ewensWeight θ (extend ξ (some c)) = (classSize ξ c : ℝ) * ewensWeight θ ξ :=
    ewensWeight_extend_some θ ξ
  simp only [hsome]
  rw [← Finset.sum_mul]
  have hcast : ∑ c : Quotient ξ, ((classSize ξ c : ℕ) : ℝ) = (n : ℝ) := by
    rw [← Nat.cast_sum, sum_classSize]
  rw [hcast]
  ring

/-- On a sample of one there is one class and it has one member. -/
theorem classSize_ER_one (ξ : ER 1) (c : Quotient ξ) : classSize ξ c = 1 := by
  classical
  refine le_antisymm ?_ (one_le_classSize ξ c)
  calc classSize ξ c ≤ (Finset.univ : Finset (Fin 1)).card := Finset.card_filter_le _ _
    _ = 1 := by simp

/-- **The Ewens normalisation, for every `n`.**

`Σ_{ξ ∈ 𝓔ₙ} θ^{|ξ|-1} ∏_a (λ_a - 1)! = (θ+1)(θ+2)⋯(θ+n-1)`.

This is what makes K-G (3.8) a probability distribution, and it is the general-`n` statement
that `Descent.Coalescent.Mutation` could only check at `n = 2` and `n = 3`.  The proof is
Kingman's restaurant, run as an induction on the sample size: `sum_ER_succ` decomposes the
sum by seating, and `sum_seatings_ewensWeight` values each seating at `θ + n`. -/
theorem sum_ewensWeight {n : ℕ} (θ : ℝ) (hn : 1 ≤ n) :
    ∑ ξ : ER n, ewensWeight θ ξ = ∏ i ∈ Finset.Ico 1 n, (θ + (i : ℝ)) := by
  classical
  induction n, hn using Nat.le_induction with
  | base =>
      rw [sum_ER_one]
      have hblocks : blocks (⊥ : ER 1) = 1 := blocks_bot 1
      have hprod : ∏ c : Quotient (⊥ : ER 1), (((classSize (⊥ : ER 1) c - 1)! : ℕ) : ℝ) = 1 := by
        refine Finset.prod_eq_one fun c _ => ?_
        rw [classSize_ER_one]
        norm_num
      unfold ewensWeight
      rw [hblocks, hprod]
      simp
  | succ m hm ih =>
      haveI : NeZero m := ⟨by omega⟩
      rw [sum_ER_succ]
      have hterm : ∀ ξ : ER m,
          ∑ o : Option (Quotient ξ), ewensWeight θ (extend ξ o)
            = (θ + (m : ℝ)) * ewensWeight θ ξ :=
        fun ξ => sum_seatings_ewensWeight θ ξ (blocks_pos ξ)
      simp only [hterm]
      rw [← Finset.mul_sum, ih, Finset.prod_Ico_succ_top hm]
      ring

end Coalescent

end Descent
