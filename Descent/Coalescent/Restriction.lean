/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Coalescent.StateSpace
import Mathlib.Tactic

assert_below Descent.Pangenome Descent.PopGen Descent.Spectral Descent.Blindness Descent.Conditionals Descent.Portability Descent.Decision Descent.Program

namespace Descent

/-!
# Restriction, and the consistency that lets the coalescent exist for all `n` at once

Both of Kingman's 1982 papers turn on one map.  K-G (7.1) and K-C (3.12) define

  `ρ_{mn} ξ = {(i, j) ; 1 ≤ i, j ≤ m, (i, j) ∈ ξ}`,

the restriction of an equivalence relation on `{1, …, n}` to `{1, …, m}`, and K-G (7.2)
records `ρ_{mn}(ρ_n ξ) = ρ_m ξ`.  That identity is the whole reason a single process can
carry `n`-coalescents for every `n`: it is the consistency condition the projective limit
of K-G section 7 needs, and it is what makes "discard the last `n - m` sampled individuals"
a well-defined operation on genealogies.

Restriction is `Setoid.comap` along `Fin.castLE`, so the composition law is definitional --
which is the right outcome.  What is not definitional, and is proved here, is the effect on
block counts: restricting can only merge nothing and lose blocks, never gain them
(`blocks_restrict_le`), and it is the identity on `Δ` and `Θ`.

## Main results

- `restrict_restrict`: K-G (7.2), the consistency identity.
- `restrict_mono`: restriction preserves the coarsening order, so it maps coalescent
  trajectories to coalescent trajectories.
- `restrict_bot`, `restrict_top`: `Δ` and `Θ` restrict to `Δ` and `Θ`.
- `blocks_restrict_le`: restriction never increases the block count.
-/

namespace Coalescent

/-- K-G (7.1): the restriction of a relation on a sample of `n` to the first `m` of them.

Empirical status: NOT AN EMPIRICAL CLAIM.  It is "look at a sub-sample", written down. -/
def restrict {m n : ℕ} (h : m ≤ n) (ξ : ER n) : ER m := Setoid.comap (Fin.castLE h) ξ

theorem restrict_rel {m n : ℕ} (h : m ≤ n) (ξ : ER n) (x y : Fin m) :
    (restrict h ξ).r x y ↔ ξ.r (Fin.castLE h x) (Fin.castLE h y) := Iff.rfl

/-- **K-G (7.2): restriction is consistent.**  Restricting to `m` and then to `l` is
restricting to `l`.  This is the identity the projective limit of K-G section 7 runs on, and
so the reason `n`-coalescents for all `n` can live on one probability space. -/
theorem restrict_restrict {l m n : ℕ} (h1 : l ≤ m) (h2 : m ≤ n) (ξ : ER n) :
    restrict h1 (restrict h2 ξ) = restrict (le_trans h1 h2) ξ :=
  Setoid.ext fun _ _ ↦ Iff.rfl

/-- Restriction preserves coarsening, so it carries a coalescent path to a path. -/
theorem restrict_mono {m n : ℕ} (h : m ≤ n) {ξ η : ER n} (hle : ξ ≤ η) :
    restrict h ξ ≤ restrict h η := by
  intro x y hxy
  exact hle hxy

/-- Restricting the starting state gives the starting state. -/
theorem restrict_bot {m n : ℕ} (h : m ≤ n) : restrict h (Delta n) = Delta m := by
  refine Setoid.ext fun x y ↦ ⟨fun hxy ↦ ?_, fun hxy ↦ ?_⟩
  · have hcast : Fin.castLE h x = Fin.castLE h y := hxy
    exact Fin.ext (by simpa using congrArg Fin.val hcast)
  · show Fin.castLE h x = Fin.castLE h y
    rw [show x = y from hxy]

/-- Restricting the absorbing state gives the absorbing state. -/
theorem restrict_top {m n : ℕ} (h : m ≤ n) : restrict h (Theta n) = Theta m :=
  Setoid.ext fun _ _ ↦ ⟨fun _ ↦ trivial, fun _ ↦ trivial⟩

/-- Restriction never manufactures blocks: a sub-sample has at most as many ancestral
lineages as the sample it came from. -/
theorem blocks_restrict_le {m n : ℕ} (h : m ≤ n) (ξ : ER n) :
    blocks (restrict h ξ) ≤ blocks ξ := by
  classical
  letI : Fintype (Quotient (restrict h ξ)) := Fintype.ofFinite _
  letI : Fintype (Quotient ξ) := Fintype.ofFinite _
  have hinj : Function.Injective
      (Quotient.lift (fun x : Fin m ↦ Quotient.mk ξ (Fin.castLE h x))
        (fun _ _ hab ↦ Quotient.sound hab) : Quotient (restrict h ξ) → Quotient ξ) := by
    intro p q hpq
    induction p using Quotient.inductionOn with
    | _ x =>
        induction q using Quotient.inductionOn with
        | _ y =>
            have h1 : Quotient.mk ξ (Fin.castLE h x) = Quotient.mk ξ (Fin.castLE h y) := hpq
            have h2 : ξ.r (Fin.castLE h x) (Fin.castLE h y) := Quotient.exact h1
            exact Quotient.sound h2
  unfold blocks
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  exact Fintype.card_le_of_injective _ hinj

end Coalescent

end Descent
