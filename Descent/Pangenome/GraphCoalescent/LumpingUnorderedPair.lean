/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.GraphCoalescent.LumpingVisibleRates

assert_below Descent.PopGen Descent.Spectral Descent.Blindness Descent.Conditionals
assert_below Descent.Portability Descent.Decision Descent.Program

/-!
# A strong lumping determines the unordered pair of loads of a two-component report

Theorem B of the hidden-lineage clock says that while a pangenome report has two components, a
predictive Markov refinement of the report must keep the unordered pair of loads `{a, b}`.
`MinimalRefinement.refines_unorderedPair` proves the necessity algebra under the hypothesis that
the statistic determines the first two survival derivatives `S'(0) = -ab` and
`S''(0) = (ab)² + ab(a + b - 2)/2` of the reported connection. This module derives that hypothesis
from strong lumpability in Rosenblatt's form, the form used in `LumpingVisibleRates`: from two
states with the same value, equally many covers lead to every other value.

`card_covers_eq_of_lumping` shows that two states with the same value of a strong lumping have
equally many covers, since with at least two report components the counts agree at every value
(`LumpingVisibleRates.card_covers_value_eq_of_lumping`). A state with `K` true blocks has
`C(K, 2)` covers, so `blocks_eq_of_lumping` concludes that the two states have the same number of
true blocks. With two report components the two loads add up to that number
(`hiddenLoad_add_hiddenLoad`), so the statistic determines `a + b`, and
`LumpingVisibleRates.visibleRate_eq_of_lumping` gives `ab`. Sum and product fix both survival
derivatives (`survivalDerivatives_eq_of_sum_product`), which is
`survivalDerivatives_eq_of_lumping`, and `unorderedPair_eq_of_lumping` concludes with (B2): two
states with the same value carry the same unordered pair of loads.

## Empirical status

None. The bodies here are counts of equivalence classes on a finite set and algebra of the
resulting natural numbers, so no measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Pangenome.GraphCoalescent.LumpingUnorderedPair

open Coalescent Finset LumpingVisibleRates MinimalRefinement
open scoped Classical

attribute [local instance] LumpingVisibleRates.fintypeStates

noncomputable section

variable {n : ℕ}

/-- **A strong lumping counts all covers alike.** While the report has at least two components,
two states with the same value of a strong lumping that determines the report have equally many
covers. Assumes: the statistic determines the report, and it is a strong lumping in Rosenblatt's
form. -/
theorem card_covers_eq_of_lumping {Stat : Type*} (s : Fin n → Fin n) (f : ER n → Stat)
    (hreport : ∀ ξ ξ' : ER n, f ξ = f ξ' → observed s ξ = observed s ξ')
    (hlumping : ∀ ξ ξ' : ER n, f ξ = f ξ' → ∀ v, v ≠ f ξ →
      Nat.card {η : ER n // Covers ξ η ∧ f η = v} = Nat.card {η : ER n // Covers ξ' η ∧ f η = v})
    {ξ ξ' : ER n} (hsame : f ξ = f ξ') (hcomponents : 2 ≤ blocks (observed s ξ)) :
    Nat.card {η : ER n // Covers ξ η} = Nat.card {η : ER n // Covers ξ' η} := by
  have htotal : ∀ ζ : ER n, Nat.card {η : ER n // Covers ζ η} =
      ((univ.filter (Covers ζ)).filter fun _ ↦ () = ()).card := by
    intro ζ
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    congr 1
    exact (filter_true_of_mem fun _ _ ↦ rfl).symm
  rw [htotal ξ, htotal ξ']
  refine card_filter_comp_eq _ _ f (fun _ ↦ ()) () fun v _ ↦ ?_
  exact (natCard_covers_eq ξ fun η ↦ f η = v).symm.trans
    ((card_covers_value_eq_of_lumping s f hreport hlumping hsame hcomponents v).trans
      (natCard_covers_eq ξ' fun η ↦ f η = v))

/-- **A strong lumping determines the number of true lineages.** A state with `K` true blocks has
`C(K, 2)` covers, so while the report has at least two components, two states with the same value
of a strong lumping that determines the report have the same number of true ancestral blocks.
Assumes: the statistic determines the report, and it is a strong lumping in Rosenblatt's form. -/
theorem blocks_eq_of_lumping {Stat : Type*} (s : Fin n → Fin n) (f : ER n → Stat)
    (hreport : ∀ ξ ξ' : ER n, f ξ = f ξ' → observed s ξ = observed s ξ')
    (hlumping : ∀ ξ ξ' : ER n, f ξ = f ξ' → ∀ v, v ≠ f ξ →
      Nat.card {η : ER n // Covers ξ η ∧ f η = v} = Nat.card {η : ER n // Covers ξ' η ∧ f η = v})
    (hn : 0 < n) {ξ ξ' : ER n} (hsame : f ξ = f ξ') (hcomponents : 2 ≤ blocks (observed s ξ)) :
    blocks ξ = blocks ξ' := by
  haveI : NeZero n := ⟨hn.ne'⟩
  have hcovers : (blocks ξ).choose 2 = (blocks ξ').choose 2 := by
    rw [← card_covers ξ, ← card_covers ξ']
    exact card_covers_eq_of_lumping s f hreport hlumping hsame hcomponents
  have hreal : ((blocks ξ).choose 2 : ℝ) = ((blocks ξ').choose 2 : ℝ) := by
    exact_mod_cast hcovers
  rw [Nat.cast_choose_two, Nat.cast_choose_two] at hreal
  have hK : (1 : ℝ) ≤ blocks ξ := by exact_mod_cast (blocks_pos ξ : 1 ≤ blocks ξ)
  have hK' : (1 : ℝ) ≤ blocks ξ' := by exact_mod_cast (blocks_pos ξ' : 1 ≤ blocks ξ')
  have hfactor : ((blocks ξ : ℝ) - blocks ξ') * (blocks ξ + blocks ξ' - 1) = 0 := by
    linear_combination 2 * hreal
  rcases mul_eq_zero.mp hfactor with hzero | hzero
  · exact_mod_cast sub_eq_zero.mp hzero
  · exfalso
    linarith

/-- **Two components hold every true lineage.** While the report has two components, the loads of
the two components add up to the number of true ancestral blocks. -/
theorem hiddenLoad_add_hiddenLoad (s : Fin n → Fin n) (ξ : ER n)
    (hcomponents : blocks (observed s ξ) = 2) {x y : Fin n} (hxy : ¬ (observed s ξ).r x y) :
    hiddenLoad s ξ (Quotient.mk (observed s ξ) x) +
        hiddenLoad s ξ (Quotient.mk (observed s ξ) y) = blocks ξ := by
  have hne : Quotient.mk (observed s ξ) x ≠ Quotient.mk (observed s ξ) y :=
    fun hq ↦ hxy (Quotient.exact hq)
  have huniv : ({Quotient.mk (observed s ξ) x, Quotient.mk (observed s ξ) y} :
      Finset (Quotient (observed s ξ))) = univ := by
    refine eq_univ_of_card _ ?_
    rw [card_pair hne, ← Nat.card_eq_fintype_card]
    exact hcomponents.symm
  rw [← sum_hiddenLoad s ξ, ← huniv, sum_pair hne]

/-- **Sum and product fix both survival derivatives.** Positive loads with the same sum and the same
product have the same first two survival derivatives of the two-component chain. -/
theorem survivalDerivatives_eq_of_sum_product {a b a' b' : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (ha' : 1 ≤ a') (hb' : 1 ≤ b') (hproduct : a * b = a' * b') (hsum : a + b = a' + b') :
    twoComponentGenerator (fun _ _ ↦ 1) a b = twoComponentGenerator (fun _ _ ↦ 1) a' b' ∧
      twoComponentGenerator (twoComponentGenerator fun _ _ ↦ 1) a b =
        twoComponentGenerator (twoComponentGenerator fun _ _ ↦ 1) a' b' := by
  have hproductReal : (a : ℝ) * b = a' * b' := by exact_mod_cast hproduct
  have hsumReal : (a : ℝ) + b = a' + b' := by exact_mod_cast hsum
  refine ⟨?_, ?_⟩
  · rw [twoComponentGenerator_one, twoComponentGenerator_one, hproductReal]
  · rw [(twoComponentGenerator_twice_one a b ha hb).2,
      (twoComponentGenerator_twice_one a' b' ha' hb').2, hproductReal, hsumReal]

/-- **Theorem B with two components, the Rosenblatt step.** A statistic that determines the report
and is a strong lumping in Rosenblatt's form determines the first two survival derivatives of the
reported connection while the report has two components: two states with the same value, with
loads `a, b` and `a', b'` at the components of `x` and `y`, give the same `S'(0)` and `S''(0)`.
Assumes: the statistic determines the report, and it is a strong lumping in Rosenblatt's form. -/
theorem survivalDerivatives_eq_of_lumping {Stat : Type*} (s : Fin n → Fin n) (f : ER n → Stat)
    (hreport : ∀ ξ ξ' : ER n, f ξ = f ξ' → observed s ξ = observed s ξ')
    (hlumping : ∀ ξ ξ' : ER n, f ξ = f ξ' → ∀ v, v ≠ f ξ →
      Nat.card {η : ER n // Covers ξ η ∧ f η = v} = Nat.card {η : ER n // Covers ξ' η ∧ f η = v})
    {ξ ξ' : ER n} (hsame : f ξ = f ξ') (hcomponents : blocks (observed s ξ) = 2) {x y : Fin n}
    (hxy : ¬ (observed s ξ).r x y) :
    twoComponentGenerator (fun _ _ ↦ 1) (hiddenLoad s ξ (Quotient.mk (observed s ξ) x))
        (hiddenLoad s ξ (Quotient.mk (observed s ξ) y)) =
      twoComponentGenerator (fun _ _ ↦ 1) (hiddenLoad s ξ' (Quotient.mk (observed s ξ') x))
        (hiddenLoad s ξ' (Quotient.mk (observed s ξ') y)) ∧
    twoComponentGenerator (twoComponentGenerator fun _ _ ↦ 1)
        (hiddenLoad s ξ (Quotient.mk (observed s ξ) x))
        (hiddenLoad s ξ (Quotient.mk (observed s ξ) y)) =
      twoComponentGenerator (twoComponentGenerator fun _ _ ↦ 1)
        (hiddenLoad s ξ' (Quotient.mk (observed s ξ') x))
        (hiddenLoad s ξ' (Quotient.mk (observed s ξ') y)) := by
  have hreports : observed s ξ = observed s ξ' := hreport ξ ξ' hsame
  have hxy' : ¬ (observed s ξ').r x y := hreports ▸ hxy
  have hcomponents' : blocks (observed s ξ') = 2 := hreports ▸ hcomponents
  refine survivalDerivatives_eq_of_sum_product (hiddenLoad_pos s ξ _) (hiddenLoad_pos s ξ _)
    (hiddenLoad_pos s ξ' _) (hiddenLoad_pos s ξ' _)
    (visibleRate_eq_of_lumping s f hreport hlumping hsame hxy) ?_
  rw [hiddenLoad_add_hiddenLoad s ξ hcomponents hxy,
    hiddenLoad_add_hiddenLoad s ξ' hcomponents' hxy']
  exact blocks_eq_of_lumping s f hreport hlumping (Fin.pos x) hsame hcomponents.ge

/-- **Theorem B with two components, the Rosenblatt step discharged.** A statistic that determines
the report and is a strong lumping in Rosenblatt's form determines the unordered pair of loads
while the report has two components. Assumes: the statistic determines the report, and it is a
strong lumping in Rosenblatt's form. -/
theorem unorderedPair_eq_of_lumping {Stat : Type*} (s : Fin n → Fin n) (f : ER n → Stat)
    (hreport : ∀ ξ ξ' : ER n, f ξ = f ξ' → observed s ξ = observed s ξ')
    (hlumping : ∀ ξ ξ' : ER n, f ξ = f ξ' → ∀ v, v ≠ f ξ →
      Nat.card {η : ER n // Covers ξ η ∧ f η = v} = Nat.card {η : ER n // Covers ξ' η ∧ f η = v})
    {ξ ξ' : ER n} (hsame : f ξ = f ξ') (hcomponents : blocks (observed s ξ) = 2) {x y : Fin n}
    (hxy : ¬ (observed s ξ).r x y) :
    (hiddenLoad s ξ' (Quotient.mk (observed s ξ') x) =
          hiddenLoad s ξ (Quotient.mk (observed s ξ) x) ∧
        hiddenLoad s ξ' (Quotient.mk (observed s ξ') y) =
          hiddenLoad s ξ (Quotient.mk (observed s ξ) y)) ∨
      (hiddenLoad s ξ' (Quotient.mk (observed s ξ') x) =
          hiddenLoad s ξ (Quotient.mk (observed s ξ) y) ∧
        hiddenLoad s ξ' (Quotient.mk (observed s ξ') y) =
          hiddenLoad s ξ (Quotient.mk (observed s ξ) x)) :=
  unorderedPair_of_survivalDerivatives_eq _ _ _ _ (hiddenLoad_pos s ξ _) (hiddenLoad_pos s ξ _)
    (hiddenLoad_pos s ξ' _) (hiddenLoad_pos s ξ' _)
    (survivalDerivatives_eq_of_lumping s f hreport hlumping hsame hcomponents hxy).1
    (survivalDerivatives_eq_of_lumping s f hreport hlumping hsame hcomponents hxy).2

end

end Descent.Pangenome.GraphCoalescent.LumpingUnorderedPair
