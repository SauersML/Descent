/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.FourCellCohortLaw
import Descent.Portability.EmpiricalCorrelationDefinedness
import Descent.Portability.SmallCohortConditionalMeans

assert_below Descent.Decision Descent.Program

/-!
# The ordered-sample law of a cohort and the count law

NOTE1 section 7 computes permutation-invariant cohort reports from the four-cell count law
(37), and directs order-sensitive algorithms to the ordered-sample law instead. The
ordered-sample law of an independent cohort of size `n` is the corpus independent product
`FourCellCohortLaw.cohortLaw`, and `FourCellCohortLaw.pushforward_cohortCounts` states that its
census pushforward is the corpus multinomial count law. `pushforward_cohortCounts_mass` writes
that pushforward at the four cells of NOTE1 (31) in the `n!/(a! b! c! d!) · Π P^k` form of
(37), through `SmallCohortConditionalMeans.censusWeight`.

This module proves the other half of the instruction: the statistics that factor through the
counts are exactly the permutation-invariant ones. `cellCount_comp_perm` shows that relabelling
the members leaves the census unchanged. `factors_through_cohortCounts_iff` shows that a real
statistic of the ordered sample is a function of the census if and only if it is invariant
under every relabelling of the members; the converse direction reads a census through any
sample realizing it (`exists_sample_of_counts`). `firstScore_not_factors_through_cohortCounts`
is the witness that an order-sensitive statistic is in general not a function of the counts:
the score of the first member of a cohort of two changes when the two members of a sample
with one doubly donor and one doubly recipient member are exchanged, while the census does not.

Not formalised here: any particular order-sensitive algorithm beyond this witness.

## Empirical status

None. The bodies here are algebra: they compare finite functions on ordered samples with their
censuses, so no measurement on any cohort can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.OrderedSampleCohortLaw

open FiniteReproductiveKernel FourCellCohortLaw EmpiricalCorrelationDefinedness
  SmallCohortConditionalMeans

variable {H : Type*} [Fintype H] [DecidableEq H]

/-- Relabelling the members of an ordered cohort sample leaves every cell count unchanged. -/
theorem cellCount_comp_perm {n : ℕ} (sample : Fin n → H) (relabel : Equiv.Perm (Fin n)) :
    cellCount (sample ∘ relabel) = cellCount sample := by
  funext cell
  simp only [cellCount, Finset.card_filter]
  exact Equiv.sum_comp relabel fun member ↦ if sample member = cell then 1 else 0

/-- Relabelling the members of an ordered cohort sample leaves its census unchanged. -/
theorem cohortCounts_comp_perm {n : ℕ} (sample : Fin n → H) (relabel : Equiv.Perm (Fin n)) :
    cohortCounts (sample ∘ relabel) = cohortCounts sample :=
  Subtype.ext (cellCount_comp_perm sample relabel)

/-- Every census of a cohort of size `n` is realized by some ordered sample, because the number
of samples realizing it is a positive multinomial coefficient. -/
theorem exists_sample_of_counts {n : ℕ} (census : Counts H n) :
    ∃ sample : Fin n → H, cohortCounts sample = census := by
  have hcard := card_filter_cellCount census.val (counts_sum census)
  have hpos : 0 < (Finset.univ.filter fun sample : Fin n → H ↦
      cellCount sample = census.val).card := by
    rw [hcard]
    exact Nat.multinomial_pos _ _
  obtain ⟨sample, hsample⟩ := Finset.card_pos.mp hpos
  exact ⟨sample, Subtype.ext (Finset.mem_filter.mp hsample).2⟩

/-- A real statistic of the ordered cohort sample is a function of the census exactly when it
is invariant under every relabelling of the members. -/
theorem factors_through_cohortCounts_iff {n : ℕ} (report : (Fin n → H) → ℝ) :
    (∃ countReport : Counts H n → ℝ,
        ∀ sample, report sample = countReport (cohortCounts sample)) ↔
      ∀ (sample : Fin n → H) (relabel : Equiv.Perm (Fin n)),
        report (sample ∘ relabel) = report sample := by
  constructor
  · rintro ⟨countReport, hfactor⟩ sample relabel
    rw [hfactor, hfactor, cohortCounts_comp_perm]
  · intro hinvariant
    refine ⟨fun census ↦ report (Classical.choose (exists_sample_of_counts census)),
      fun sample ↦ ?_⟩
    exact report_eq_of_cohortCounts report hinvariant _ _
      (Classical.choose_spec (exists_sample_of_counts (cohortCounts sample))).symm

/-- NOTE1 (37) as the census pushforward of the ordered-sample law: at the four cells of NOTE1
(31), the ordered sample of an independent cohort of size `n` pushed forward to its census has
mass `n!/(a! b! c! d!) · P₀₀^a P₀₁^b P₁₀^c P₁₁^d` at the census `(a, b, c, d)`. -/
theorem pushforward_cohortCounts_mass (law : FiniteReportLaw (Bool × Bool)) (n : ℕ)
    (census : Counts (Bool × Bool) n) :
    ((cohortLaw law n).pushforward cohortCounts).mass census = censusWeight law n census.val := by
  rw [pushforward_cohortCounts, multinomialLaw_mass_eq_censusWeight]

/-- An order-sensitive statistic that is not a function of the counts: the score of the first
member of an ordered cohort of two. Exchanging the members of a sample with one doubly donor
and one doubly recipient member leaves the census unchanged and changes the statistic. -/
theorem firstScore_not_factors_through_cohortCounts :
    ¬ ∃ countReport : Counts (Bool × Bool) 2 → ℝ,
      ∀ sample : Fin 2 → Bool × Bool,
        scoreValue (sample 0) = countReport (cohortCounts sample) := by
  intro hfactor
  have hinvariant := (factors_through_cohortCounts_iff
    fun sample : Fin 2 → Bool × Bool ↦ scoreValue (sample 0)).mp hfactor
  have hswap := hinvariant ![(true, true), (false, false)] (Equiv.swap 0 1)
  norm_num [scoreValue] at hswap

end Descent.Portability.OrderedSampleCohortLaw
