/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.FiniteReproductiveKernel
import Descent.Portability.FiniteGeneticTransition
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.Sym.Card

assert_below Descent.Decision Descent.Program

/-!
# Census counts and the zero-weight failure rule of NOTE2 section 2

Two facts NOTE2 section 2 states about its reproductive primitives.

The census count of §2.2. With `K` exchangeable reproductive types and census size `N`, one
unlabelled census has `C(N + K - 1, K - 1)` states. `card_counts` identifies the corpus census
vectors `FiniteReproductiveKernel.Counts H N` with the multisets of size `N` over the types and
counts them as `C(K + N - 1, N)`, and `card_counts_eq_choose_pred` is the note's form for
`K ≥ 1`. The four-cell census of a cohort of size `N` has `C(N + 3, 3)` states
(`card_fourCellCounts`). This count is exact. NOTE1's looser budget bound `C(K + B, B)` is
`PartialHaplotypeCarrier.card_withinBudget_le_choose`.

The selection law (4). Census-weighted selection `ν(g | x) = x_g w(g, x) / Σ_g' x_g' w(g', x)`
with nonnegative fitness is a normalized law when the total reproductive weight is positive
(`censusSelection_mass`). A zero total weight admits no law proportional to the weights
(`no_proportional_law_of_total_eq_zero`), so it needs an explicit extinction or failure rule:
`censusSelection` returns `none` exactly then (`censusSelection_eq_none_iff`). With every
individual counted once and strictly positive fitness it is the corpus
`FiniteGeneticTransition.selectionLaw` (`censusSelection_one_mass`).

## Empirical status

None. The bodies here are counting and algebra on supplied finite inputs, so no measurement can
bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.ReproductiveCensusPrimitives

open FiniteReproductiveKernel

section CensusCount

variable {H : Type*} [Fintype H] [DecidableEq H]

/-- NOTE2 §2.2: the census vectors of size `N` over the reproductive types are the multisets of
size `N` over the types, so there are `C(K + N - 1, N)` of them, `K` the number of types. -/
theorem card_counts (N : ℕ) :
    Fintype.card (Counts H N) = (Fintype.card H + N - 1).choose N := by
  have hequiv : Counts H N ≃ Sym H N :=
    (Equiv.subtypeEquivRight fun counts ↦ by simp [Finset.mem_piAntidiag]).trans
      (Sym.equivNatSumOfFintype H N).symm
  rw [Fintype.card_congr hequiv, Sym.card_sym_eq_choose]

/-- NOTE2 §2.2: with `K ≥ 1` exchangeable reproductive types and census size `N`, one unlabelled
census has `C(N + K - 1, K - 1)` states. -/
theorem card_counts_eq_choose_pred (N : ℕ) (htypes : 0 < Fintype.card H) :
    Fintype.card (Counts H N) = (N + Fintype.card H - 1).choose (Fintype.card H - 1) := by
  rw [card_counts, add_comm (Fintype.card H) N]
  have hle : N ≤ N + Fintype.card H - 1 := by omega
  rw [← Nat.choose_symm hle]
  congr 1
  omega

/-- The four-cell census of a cohort of size `N` has `C(N + 3, 3)` states. -/
theorem card_fourCellCounts (N : ℕ) :
    Fintype.card (Counts (Bool × Bool) N) = (N + 3).choose 3 := by
  have hcard : Fintype.card (Bool × Bool) = 4 := by simp
  have hcount := card_counts_eq_choose_pred (H := Bool × Bool) N Fintype.card_pos
  have hsum : N + Fintype.card (Bool × Bool) - 1 = N + 3 := by rw [hcard]; omega
  rw [hsum, hcard] at hcount
  exact hcount

end CensusCount

section Selection

variable {I : Type*} [Fintype I]

/-- NOTE2 (4): census-weighted selection with nonnegative reproductive fitness and an explicit
failure outcome: the normalized law `x_g w(g) / Σ_g' x_g' w(g')` when the total reproductive
weight is positive, and `none` when it is zero. -/
noncomputable def censusSelection (census : I → ℕ) (fitness : I → ℝ)
    (hfitness : ∀ g, 0 ≤ fitness g) : Option (FiniteReportLaw I) :=
  if htotal : 0 < ∑ g, (census g : ℝ) * fitness g then
    some
      { mass := fun g ↦
          (census g : ℝ) * fitness g / ∑ other, (census other : ℝ) * fitness other
        mass_nonneg := fun g ↦
          div_nonneg (mul_nonneg (Nat.cast_nonneg _) (hfitness g)) htotal.le
        mass_sum := by
          rw [← Finset.sum_div]
          exact div_self htotal.ne' }
  else none

/-- NOTE2 (4): with positive total reproductive weight, census-weighted selection is the
normalized law `x_g w(g) / Σ_g' x_g' w(g')`. -/
theorem censusSelection_mass (census : I → ℕ) (fitness : I → ℝ)
    (hfitness : ∀ g, 0 ≤ fitness g) (htotal : 0 < ∑ g, (census g : ℝ) * fitness g) :
    ∃ law : FiniteReportLaw I, censusSelection census fitness hfitness = some law ∧
      ∀ g, law.mass g =
        (census g : ℝ) * fitness g / ∑ other, (census other : ℝ) * fitness other := by
  unfold censusSelection
  rw [dif_pos htotal]
  exact ⟨_, rfl, fun _ ↦ rfl⟩

/-- NOTE2 (4): a zero total reproductive weight is not a normalized law; no finite law is
proportional to the census weights. -/
theorem no_proportional_law_of_total_eq_zero (census : I → ℕ) (fitness : I → ℝ)
    (htotal : ∑ g, (census g : ℝ) * fitness g = 0) :
    ¬ ∃ (law : FiniteReportLaw I) (scale : ℝ),
      ∀ g, law.mass g = scale * ((census g : ℝ) * fitness g) := by
  rintro ⟨law, scale, hlaw⟩
  have hsum := law.mass_sum
  simp only [hlaw, ← Finset.mul_sum, htotal, mul_zero] at hsum
  exact zero_ne_one hsum

/-- NOTE2 (4): census-weighted selection fails exactly when the total reproductive weight is
zero. -/
theorem censusSelection_eq_none_iff (census : I → ℕ) (fitness : I → ℝ)
    (hfitness : ∀ g, 0 ≤ fitness g) :
    censusSelection census fitness hfitness = none ↔ ∑ g, (census g : ℝ) * fitness g = 0 := by
  have hnonneg : 0 ≤ ∑ g, (census g : ℝ) * fitness g :=
    Finset.sum_nonneg fun g _ ↦ mul_nonneg (Nat.cast_nonneg _) (hfitness g)
  unfold censusSelection
  split_ifs with htotal
  · exact ⟨fun hnone ↦ absurd hnone (by simp), fun hzero ↦ absurd hzero htotal.ne'⟩
  · exact ⟨fun _ ↦ le_antisymm (not_lt.mp htotal) hnonneg, fun _ ↦ rfl⟩

/-- With every individual counted once and strictly positive fitness, census-weighted selection
is the corpus fitness-selection law. -/
theorem censusSelection_one_mass [Nonempty I] (fitness : I → ℝ) (hfit : ∀ g, 0 < fitness g) :
    ∃ law : FiniteReportLaw I,
      censusSelection (fun _ ↦ 1) fitness (fun g ↦ (hfit g).le) = some law ∧
        law.mass = (FiniteGeneticTransition.selectionLaw fitness hfit).mass := by
  have htotal : 0 < ∑ g, ((1 : ℕ) : ℝ) * fitness g := by
    simpa using Finset.sum_pos (fun g _ ↦ hfit g) Finset.univ_nonempty
  obtain ⟨law, hlaw, hmass⟩ :=
    censusSelection_mass (fun _ ↦ 1) fitness (fun g ↦ (hfit g).le) htotal
  refine ⟨law, hlaw, funext fun g ↦ ?_⟩
  rw [hmass, FiniteGeneticTransition.selectionLaw_mass]
  simp

end Selection

end Descent.Portability.ReproductiveCensusPrimitives
