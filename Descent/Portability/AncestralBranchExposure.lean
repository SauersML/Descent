/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.TimedAncestralLaw
import Descent.Portability.NucleotideMutationLaw

assert_below Descent.Decision Descent.Program

/-!
Branch mutation exposure constructed directly from marked ancestry histories
and their proposal times. Migration, recombination and null events partition
branch time; descendant clades at each locus identify the ancestral branches.
This module handles a finite epoch, including branches crossing its boundaries.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.AncestralBranchExposure

open Coalescent.FiniteGenomeAncestry AncestralEventLaw MarkedAncestralLaw TimedAncestralLaw
open MeasureTheory
open scoped NNReal

variable {D L n count : ℕ}

/-- Integrate a state reward over successive inter-proposal intervals, including
both the initial interval and the final interval before the epoch boundary. -/
noncomputable def occupation (reward : State D L n → ℝ) : {count : ℕ} →
    {start : State D L n} → Trace count start → ℝ → (Fin count → ℝ) → ℝ
  | 0, start, _, duration, _ => duration * reward start
  | _count + 1, start, ⟨_event, rest⟩, duration, times =>
      times 0 * reward start + occupation reward rest (duration - times 0)
        (fun i ↦ times i.succ - times 0)

theorem occupation_continuous (reward : State D L n → ℝ) {start : State D L n}
    (trace : Trace count start) :
    Continuous (fun input : ℝ × (Fin count → ℝ) ↦ occupation reward trace input.1 input.2) := by
  induction count generalizing start with
  | zero => exact continuous_fst.mul continuous_const
  | succ count ih =>
      change Continuous (fun input : ℝ × (Fin (count + 1) → ℝ) ↦
        input.2 0 * reward start + occupation reward trace.2 (input.1 - input.2 0)
          (fun i ↦ input.2 i.succ - input.2 0))
      apply Continuous.add
      · exact ((continuous_apply 0).comp continuous_snd).mul continuous_const
      · apply (ih trace.2).comp (f := fun input : ℝ × (Fin (count + 1) → ℝ) ↦
          (input.1 - input.2 0, fun i ↦ input.2 i.succ - input.2 0))
        apply Continuous.prodMk
        · exact continuous_fst.sub ((continuous_apply 0).comp continuous_snd)
        · apply continuous_pi
          intro i
          exact ((continuous_apply i.succ).comp continuous_snd).sub
            ((continuous_apply 0).comp continuous_snd)

/-- No branch time is lost by introducing proposals, including null proposals. -/
theorem occupation_one {start : State D L n} (trace : Trace count start)
    (duration : ℝ) (times : Fin count → ℝ) :
    occupation (fun _ ↦ 1) trace duration times = duration := by
  induction count generalizing start duration with
  | zero => simp [occupation]
  | succ count ih =>
      change times 0 * 1 + occupation (fun _ ↦ 1) trace.2 (duration - times 0)
        (fun i ↦ times i.succ - times 0) = duration
      rw [ih]
      ring

theorem occupation_bounds (reward : State D L n → ℝ) {start : State D L n}
    (trace : Trace count start) (duration bound : ℝ) (hd : 0 ≤ duration)
    (hreward : ∀ state, 0 ≤ reward state ∧ reward state ≤ bound)
    (times : Fin count → ℝ) (hmono : Monotone times)
    (htimes : ∀ i, times i ∈ Set.Icc 0 duration) :
    0 ≤ occupation reward trace duration times ∧
      occupation reward trace duration times ≤ duration * bound := by
  induction count generalizing start duration with
  | zero => exact ⟨mul_nonneg hd (hreward start).1,
      mul_le_mul_of_nonneg_left (hreward start).2 hd⟩
  | succ count ih =>
      have htailmono : Monotone (fun i : Fin count ↦ times i.succ - times 0) := by
        intro i j hij
        exact sub_le_sub_right (hmono (by simpa using hij)) _
      have htailbounds (i : Fin count) :
          times i.succ - times 0 ∈ Set.Icc 0 (duration - times 0) :=
        ⟨sub_nonneg.mpr (hmono (Fin.zero_le _)), sub_le_sub_right (htimes i.succ).2 _⟩
      have htail := ih trace.2 (duration - times 0) (sub_nonneg.mpr (htimes 0).2)
        _ htailmono htailbounds
      change 0 ≤ times 0 * reward start + _ ∧ times 0 * reward start + _ ≤ duration * bound
      constructor
      · exact add_nonneg (mul_nonneg (htimes 0).1 (hreward start).1) htail.1
      · calc
          times 0 * reward start + _ ≤ times 0 * bound + (duration - times 0) * bound :=
            add_le_add (mul_le_mul_of_nonneg_left (hreward start).2 (htimes 0).1) htail.2
          _ = duration * bound := by ring

noncomputable def locusDescendants (material : Material L n) (locus : Fin L) : Finset (Fin n) :=
  Finset.univ.filter (fun sample ↦ (locus, sample) ∈ material)

/-- Count the active ancestral branches carrying exactly this nonempty clade
at this locus. Disjoint material prevents counting two copies of a sample. -/
noncomputable def cladeCount (locus : Fin L) (clade : Finset (Fin n))
    (state : State D L n) : ℝ := by
  classical
  exact ((state.val.filter (fun lineage ↦
    locusDescendants lineage.2 locus = clade ∧ clade.Nonempty)).card : ℝ)

/-- A nonempty sampled clade cannot belong to two active lineages at once. -/
theorem cladeCount_bounds (locus : Fin L) (clade : Finset (Fin n)) (state : State D L n) :
    0 ≤ cladeCount locus clade state ∧ cladeCount locus clade state ≤ 1 := by
  classical
  constructor
  · unfold cladeCount
    positivity
  · unfold cladeCount
    have hcard : (state.val.filter (fun lineage ↦
        locusDescendants lineage.2 locus = clade ∧ clade.Nonempty)).card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro a ha b hb
      by_contra hab
      have haf := Finset.mem_filter.mp ha
      have hbf := Finset.mem_filter.mp hb
      obtain ⟨sample, hsample⟩ := haf.2.2
      have ha' : sample ∈ locusDescendants a.2 locus := haf.2.1.symm ▸ hsample
      have hb' : sample ∈ locusDescendants b.2 locus := hbf.2.1.symm ▸ hsample
      exact Finset.disjoint_left.mp (state.property.2 haf.1 hbf.1 hab)
        (Finset.mem_filter.mp ha').2 (Finset.mem_filter.mp hb').2
    exact_mod_cast hcard

/-- Total branch length of the specified locus/clade within this epoch. -/
noncomputable def cladeExposure {start : State D L n} (trace : Trace count start)
    (duration : ℝ) (times : Fin count → ℝ) (locus : Fin L) (clade : Finset (Fin n)) : ℝ :=
  occupation (cladeCount locus clade) trace duration times

theorem cladeExposure_bounds {start : State D L n} (trace : Trace count start)
    (duration : ℝ≥0) (times : Fin count → ℝ) (hmono : Monotone times)
    (htimes : ∀ i, times i ∈ Set.Icc 0 (duration : ℝ))
    (locus : Fin L) (clade : Finset (Fin n)) :
    0 ≤ cladeExposure trace duration times locus clade ∧
      cladeExposure trace duration times locus clade ≤ (duration : ℝ) := by
  simpa using occupation_bounds _ trace duration 1 duration.property
    (cladeCount_bounds locus clade) times hmono htimes

/-- The JC69 exponential factor for this clade's exposure. Joint leaf genotype
probabilities still require composing all clade transitions on the genealogy. -/
noncomputable def mutationFactor {start : State D L n} (trace : Trace count start)
    (duration : ℝ≥0) (mutationRate : ℝ≥0) (locus : Fin L) (clade : Finset (Fin n))
    (times : Fin count → ℝ) : ℝ :=
  Real.exp (-4 * (mutationRate : ℝ) * cladeExposure trace duration times locus clade / 3)

theorem mutationFactor_measurable {start : State D L n} (trace : Trace count start)
    (duration mutationRate : ℝ≥0) (locus : Fin L) (clade : Finset (Fin n)) :
    Measurable (mutationFactor trace duration mutationRate locus clade) := by
  have h : Continuous (fun times ↦ cladeExposure trace duration times locus clade) :=
    (occupation_continuous (cladeCount locus clade) trace).comp
      (continuous_const.prodMk continuous_id)
  exact (Real.continuous_exp.comp ((continuous_const.mul h).div_const 3)).measurable

theorem mutationFactor_bounds {start : State D L n} (trace : Trace count start)
    (duration mutationRate : ℝ≥0) (locus : Fin L) (clade : Finset (Fin n)) :
    ∀ᵐ times ∂timeLaw duration count,
      0 ≤ mutationFactor trace duration mutationRate locus clade times ∧
        mutationFactor trace duration mutationRate locus clade times ≤ 1 := by
  filter_upwards [timeLaw_support duration count] with times htimes
  constructor
  · exact (Real.exp_pos _).le
  · apply Real.exp_le_one_iff.mpr
    have h := (cladeExposure_bounds trace duration times htimes.1 htimes.2 locus clade).1
    exact div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg (by norm_num) mutationRate.property) h) (by norm_num)

/-- A rate-and-demography-derived convergent expectation for the branch
mutation factor, with the timed law's explicit Poisson truncation certificate. -/
theorem mutationFactor_summable (rates : Rates D L) (start : State D L n)
    (duration mutationRate : ℝ≥0) (locus : Fin L) (clade : Finset (Fin n)) :
    Summable (fun count ↦ ProbabilityTheory.poissonPMFReal
      (AncestralEpochLaw.poissonParameter (n := n) rates duration) count *
      countExpectation rates start duration count
        (fun trace ↦ mutationFactor trace duration mutationRate locus clade)) :=
  timedExpectation_summable rates start duration _
    (fun _ trace ↦ mutationFactor_measurable trace duration mutationRate locus clade) 1
    (fun _ trace ↦ mutationFactor_bounds trace duration mutationRate locus clade)

end Descent.Portability.AncestralBranchExposure
