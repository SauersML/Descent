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

end Coalescent

end Descent
