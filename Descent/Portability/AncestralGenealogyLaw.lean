/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.AncestralBranchExposure
import Descent.Portability.GenealogyGenotypeLaw

assert_below Descent.Decision Descent.Program

/-!
Compile an actual marked ancestry trace into the ordered locus branches used
by the joint nucleotide kernel. Older intervals precede younger intervals.
Nonempty descendant material, representative membership, and mutation exposure
are constructed from the ancestry rather than supplied as unrelated inputs.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.AncestralGenealogyLaw

open Coalescent.FiniteGenomeAncestry MarkedAncestralLaw AncestralBranchExposure
open GenealogyGenotypeLaw
open scoped NNReal

variable {D L n count : ℕ}

noncomputable def intervalBranchesAux (locus : Fin L) (exposure : ℝ≥0) :
    List (Lineage D L n) → List (Branch n)
  | [] => []
  | lineage :: rest =>
      if h : (locusDescendants lineage.2 locus).Nonempty then
        { descendants := locusDescendants lineage.2 locus
          representative := (locusDescendants lineage.2 locus).min' h
          representative_mem := Finset.min'_mem _ h
          exposure := exposure } :: intervalBranchesAux locus exposure rest
      else intervalBranchesAux locus exposure rest

noncomputable def intervalBranches (state : State D L n) (locus : Fin L) (exposure : ℝ≥0) :
    List (Branch n) := intervalBranchesAux locus exposure state.val.toList

noncomputable def summedExposure (branches : List (Branch n)) (clade : Finset (Fin n)) : ℝ :=
  (branches.map (fun branch ↦ if branch.descendants = clade then (branch.exposure : ℝ) else 0)).sum

theorem summedExposure_append (first second : List (Branch n)) (clade : Finset (Fin n)) :
    summedExposure (first ++ second) clade =
      summedExposure first clade + summedExposure second clade := by
  simp [summedExposure]

private theorem intervalBranchesAux_exposure (lineages : List (Lineage D L n))
    (locus : Fin L) (exposure : ℝ≥0) (clade : Finset (Fin n)) :
    summedExposure (intervalBranchesAux locus exposure lineages) clade =
      (lineages.map (fun lineage ↦
        if locusDescendants lineage.2 locus = clade ∧ clade.Nonempty
        then (exposure : ℝ) else 0)).sum := by
  induction lineages with
  | nil => rfl
  | cons lineage rest ih =>
      simp only [summedExposure] at ih
      by_cases hne : (locusDescendants lineage.2 locus).Nonempty
      · by_cases heq : locusDescendants lineage.2 locus = clade
        · have hc : clade.Nonempty := heq ▸ hne
          simp [intervalBranchesAux, summedExposure, heq, hc, ih]
        · simp [intervalBranchesAux, hne, summedExposure, heq, ih]
      · by_cases heq : locusDescendants lineage.2 locus = clade
        · have hc : ¬ clade.Nonempty := heq ▸ hne
          simp [intervalBranchesAux, summedExposure, heq, hc, ih]
        · simp [intervalBranchesAux, hne, summedExposure, heq, ih]

/-- The branch compiler assigns exactly the mutation exposure carried by the
active descendant clade in this inter-event interval. -/
theorem intervalBranches_exposure (state : State D L n) (locus : Fin L)
    (exposure : ℝ≥0) (clade : Finset (Fin n)) :
    summedExposure (intervalBranches state locus exposure) clade =
      cladeCount locus clade state * (exposure : ℝ) := by
  classical
  rw [intervalBranches, intervalBranchesAux_exposure, Finset.sum_map_toList]
  unfold cladeCount
  rw [Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_mul, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro lineage _
  by_cases h : locusDescendants lineage.2 locus = clade ∧ clade.Nonempty <;> simp [h]

/-- Compile intervals from older to younger. Nonnegative subtraction is exact
on the support of the ordered-time law; no stochastic event is discarded. -/
noncomputable def traceBranches (locus : Fin L) (mutationRate : ℝ≥0) : {count : ℕ} →
    {start : State D L n} → Trace count start → ℝ≥0 → (Fin count → ℝ≥0) → List (Branch n)
  | 0, start, _, duration, _ => intervalBranches start locus (mutationRate * duration)
  | _count + 1, start, ⟨_event, rest⟩, duration, times =>
      traceBranches locus mutationRate rest (duration - times 0)
        (fun i ↦ times i.succ - times 0) ++
          intervalBranches start locus (mutationRate * times 0)

/-- The compiled branch list and the direct piecewise ancestry integral assign
exactly the same exposure to every sampled clade. -/
theorem traceBranches_exposure (locus : Fin L) (mutationRate : ℝ≥0)
    {start : State D L n} (trace : Trace count start) (duration : ℝ≥0)
    (times : Fin count → ℝ≥0) (hmono : Monotone times) (htimes : ∀ i, times i ≤ duration)
    (clade : Finset (Fin n)) :
    summedExposure (traceBranches locus mutationRate trace duration times) clade =
      (mutationRate : ℝ) * cladeExposure trace duration (fun i ↦ (times i : ℝ)) locus clade := by
  induction count generalizing start duration with
  | zero =>
      rw [traceBranches, intervalBranches_exposure]
      simp only [cladeExposure, occupation, NNReal.coe_mul]
      ring
  | succ count ih =>
      rcases trace with ⟨event, rest⟩
      have hm : Monotone (fun i : Fin count ↦ times i.succ - times 0) := by
        intro i j hij
        exact tsub_le_tsub_right (hmono (by simpa using hij)) _
      have ht (i : Fin count) : times i.succ - times 0 ≤ duration - times 0 :=
        tsub_le_tsub_right (htimes i.succ) _
      change summedExposure (traceBranches locus mutationRate rest (duration - times 0)
        (fun i ↦ times i.succ - times 0) ++
        intervalBranches start locus (mutationRate * times 0)) clade = _
      rw [summedExposure_append, ih rest _ _ hm ht, intervalBranches_exposure]
      have heq (i : Fin count) : ((times i.succ - times 0 : ℝ≥0) : ℝ) =
          (times i.succ : ℝ) - (times 0 : ℝ) :=
        NNReal.coe_sub (hmono (Fin.zero_le _))
      simp only [cladeExposure, occupation, NNReal.coe_mul, NNReal.coe_sub (htimes 0), heq]
      ring

end Descent.Portability.AncestralGenealogyLaw
