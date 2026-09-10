/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.AncestralEpochGenotypeLaw
import Descent.Portability.SourceDesignLaw

assert_below Descent.Decision Descent.Program

/-!
The default serial-founder and square-grid histories from `gen_real_pt.py`,
with explicit rates, epoch boundaries, relocations and source-dependent initial
samples. These instantiate the proved continuous-time ancestry and finite-site
mutation law. They do not identify the finite PRNG implementation with a real
probability measure, or yet encode the simulator's independent chunk loop.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.SimulationDemographyLaw

open Coalescent.FiniteGenomeAncestry AncestralEventLaw AncestralEpochLaw
open AncestralAbsorptionLaw AncestralEpochGenotypeLaw StoppedGenotypeLaw
open FiniteReportLaw SourceDesignLaw SamplingDesignLaw
open scoped NNReal

/-- Both simulators oversample the selected source by 4750 diploid individuals. -/
def cohortSize (demes : ℕ) : ℕ := demes * 250 + 4750

noncomputable def individualIndex {demes : ℕ} (source : Fin demes) :
    ((deme : Fin demes) × Fin (sampleSize source deme)) ≃ Fin (cohortSize demes) :=
  finSigmaFinEquiv.trans (finCongr (sampleSize_total source))

theorem individualIndex_val {demes : ℕ} (source deme : Fin demes)
    (individual : Fin (sampleSize source deme)) :
    (individualIndex source ⟨deme, individual⟩).val =
      (∑ i : Fin deme.val, sampleSize source (Fin.castLE deme.isLt.le i)) + individual.val := by
  exact finSigmaFinEquiv_apply _

/-- Enumerate individuals by deme, then each individual's two chromosomes.
This agrees with taking columns 0::2 and 1::2 in the genotype matrix. -/
noncomputable def chromosomeDeme {demes : ℕ} (source : Fin demes)
    (chromosome : Fin (cohortSize demes * 2)) : Fin (demes + 1) :=
  ((individualIndex source).symm (finProdFinEquiv.symm chromosome).1).1.castSucc

theorem chromosomeDeme_pair {demes : ℕ} (source deme : Fin demes)
    (individual : Fin (sampleSize source deme)) (copy : Fin 2) :
    chromosomeDeme source (finProdFinEquiv (individualIndex source ⟨deme, individual⟩, copy)) =
      deme.castSucc := by
  simp [chromosomeDeme]

theorem chromosomeDeme_not_ancestor {demes : ℕ} (source : Fin demes)
    (chromosome : Fin (cohortSize demes * 2)) :
    chromosomeDeme source chromosome ≠ Fin.last demes := by
  exact ne_of_lt (Fin.castSucc_lt_last _)

noncomputable def initialSamples {demes L : ℕ} (source : Fin demes) (hL : 0 < L) :
    State (demes + 1) L (cohortSize demes * 2) :=
  initialState (chromosomeDeme source) hL (by unfold cohortSize; omega)

theorem initialSamples_complete {demes L : ℕ} (source : Fin demes) (hL : 0 < L) :
    SampleComplete (initialSamples source hL) :=
  sampleComplete_initial (chromosomeDeme source) hL (by unfold cohortSize; omega)

/-- Deme indices below `modern` have size 3000; the final index is ANC of size 10000. -/
def populationSize (modern : ℕ) (deme : Fin (modern + 1)) : ℝ :=
  if deme.val = modern then 10000 else 3000

private theorem populationSize_pos (modern : ℕ) (deme : Fin (modern + 1)) :
    0 < populationSize modern deme := by
  unfold populationSize
  split_ifs <;> norm_num

noncomputable def tailRates (modern L : ℕ) : Rates (modern + 1) L where
  populationSize := populationSize modern
  size_pos := populationSize_pos modern
  migration := fun _ _ ↦ 0
  migration_nonneg := fun _ _ ↦ le_rfl
  recombination := fun _ ↦ 1 / 100000000
  recombination_nonneg := fun _ ↦ by norm_num

theorem tailRates_isolated (modern L : ℕ) (destination : Fin (modern + 1)) :
    (tailRates modern L).migration (Fin.last modern) destination = 0 := rfl

noncomputable def mutationRate : ℝ≥0 := ⟨1 / 80000000, by norm_num⟩

/-- `active` is the number of chain demes whose adjacent migration edges
remain enabled. Removing edge (k-1,k) changes this from k+1 to k at time t. -/
noncomputable def serialRates (L active : ℕ) : Rates 11 L where
  populationSize := populationSize 10
  size_pos := populationSize_pos 10
  migration := fun a b ↦
    if a.val < active ∧ b.val < active ∧ (a.val + 1 = b.val ∨ b.val + 1 = a.val)
      then 1 / 1000 else 0
  migration_nonneg := fun _ _ ↦ by split_ifs <;> norm_num
  recombination := fun _ ↦ 1 / 100000000
  recombination_nonneg := fun _ ↦ by norm_num

theorem serialRates_enabled (L active : ℕ) (a b : Fin 11)
    (ha : a.val < active) (hb : b.val < active)
    (hab : a.val + 1 = b.val ∨ b.val + 1 = a.val) :
    (serialRates L active).migration a b = 1 / 1000 := by
  simp [serialRates, ha, hb, hab]

theorem serialRates_removed (L active : ℕ) (a b : Fin 11) (ha : active ≤ a.val) :
    (serialRates L active).migration a b = 0 ∧
      (serialRates L active).migration b a = 0 := by
  simp [serialRates, not_lt.mpr ha]

/-- A probability-one mass migration at t+1 moves only the named source deme. -/
def serialRelocation (stage : Fin 9) (deme : Fin 11) : Fin 11 :=
  if deme.val = 9 - stage.val then ⟨8 - stage.val, by omega⟩ else deme

theorem serialRelocation_source (stage : Fin 9) :
    serialRelocation stage ⟨9 - stage.val, by omega⟩ = ⟨8 - stage.val, by omega⟩ := by
  simp [serialRelocation]

theorem serialRelocation_other (stage : Fin 9) (deme : Fin 11)
    (h : deme.val ≠ 9 - stage.val) : serialRelocation stage deme = deme := by
  simp [serialRelocation, h]

/-- The last 899-generation wait reaches t_anc=4300. Earlier 399-generation
waits reach the next edge-removal time, 400 generations after the previous one. -/
noncomputable def serialStage (L : ℕ) (stage : Fin 9) : List (Instruction 11 L) :=
  [.epoch (serialRates L (9 - stage.val)) 1,
   .relocate (serialRelocation stage),
   .epoch (serialRates L (9 - stage.val)) (if stage.val = 8 then 899 else 399)]

noncomputable def serialInstructions (L : ℕ) : List (Instruction 11 L) :=
  [.epoch (serialRates L 10) 200] ++ (List.ofFn (serialStage L)).flatten

def serialEventSchedule : List (ℕ × ℕ × ℕ) :=
  List.ofFn (fun stage : Fin 9 ↦
    (200 + stage.val * 400, 201 + stage.val * 400, 9 - stage.val))

theorem serialEventSchedule_exact : serialEventSchedule =
    [(200, 201, 9), (600, 601, 8), (1000, 1001, 7), (1400, 1401, 6),
     (1800, 1801, 5), (2200, 2201, 4), (2600, 2601, 3), (3000, 3001, 2),
     (3400, 3401, 1)] := by decide

def instructionDuration {D L : ℕ} : Instruction D L → ℝ≥0
  | .epoch _ duration => duration
  | .relocate _ => 0

theorem serialInstructions_duration (L : ℕ) :
    ((serialInstructions L).map instructionDuration).sum = 4300 := by
  norm_num [serialInstructions, serialStage, List.ofFn_succ, List.ofFn_zero, instructionDuration]

/-- Manhattan adjacency in the simulator's row-major 6-by-6 deme labels. -/
def gridAdjacent (a b : Fin 37) : Prop :=
  a.val < 36 ∧ b.val < 36 ∧
    ((a.val / 6 - b.val / 6) + (b.val / 6 - a.val / 6) +
      (a.val % 6 - b.val % 6) + (b.val % 6 - a.val % 6) = 1)

instance gridAdjacentDecidable (a b : Fin 37) : Decidable (gridAdjacent a b) := by
  unfold gridAdjacent
  infer_instance

theorem gridAdjacent_eq_manhattan (a b : Fin 6 × Fin 6) :
    gridAdjacent (finProdFinEquiv a).castSucc (finProdFinEquiv b).castSucc ↔
      gridDistance a b = 1 := by
  have har := a.1.isLt
  have hac := a.2.isLt
  have hbr := b.1.isLt
  have hbc := b.2.isLt
  have ha : ((finProdFinEquiv a).castSucc : Fin 37).val = a.2.val + 6 * a.1.val := rfl
  have hb : ((finProdFinEquiv b).castSucc : Fin 37).val = b.2.val + 6 * b.1.val := rfl
  unfold gridAdjacent
  rw [ha, hb]
  unfold gridDistance serialDistance
  omega

noncomputable def gridRates (L : ℕ) : Rates 37 L where
  populationSize := populationSize 36
  size_pos := populationSize_pos 36
  migration := fun a b ↦ if gridAdjacent a b then 3 / 10000 else 0
  migration_nonneg := fun _ _ ↦ by split_ifs <;> norm_num
  recombination := fun _ ↦ 1 / 100000000
  recombination_nonneg := fun _ ↦ by norm_num

theorem gridRates_adjacent (L : ℕ) (a b : Fin 37) (h : gridAdjacent a b) :
    (gridRates L).migration a b = 3 / 10000 := by simp [gridRates, h]

theorem gridRates_nonadjacent (L : ℕ) (a b : Fin 37) (h : ¬ gridAdjacent a b) :
    (gridRates L).migration a b = 0 := by simp [gridRates, h]

noncomputable def gridInstructions (L : ℕ) : List (Instruction 37 L) :=
  [.epoch (gridRates L) 12000]

theorem gridInstructions_duration (L : ℕ) :
    ((gridInstructions L).map instructionDuration).sum = 12000 := by
  simp [gridInstructions, instructionDuration]

/-- Source-conditioned one-chunk law, with the exact 4300-generation serial
history followed by the 10000-individual isolated ancestral tail. -/
noncomputable def serialGenomeLaw (L : ℕ) (hL : 0 < L) (source : Fin 10) :
    FiniteReportLaw (WholeGenome L (cohortSize 10 * 2)) :=
  completeDemographyLaw (serialInstructions L) (tailRates 10 L) (Fin.last 10)
    (tailRates_isolated 10 L) mutationRate (initialSamples source hL)
      (initialSamples_complete source hL)

/-- Source-conditioned one-chunk law, with the grid merge at generation 12000. -/
noncomputable def gridGenomeLaw (L : ℕ) (hL : 0 < L) (source : Fin 36) :
    FiniteReportLaw (WholeGenome L (cohortSize 36 * 2)) :=
  completeDemographyLaw (gridInstructions L) (tailRates 36 L) (Fin.last 36)
    (tailRates_isolated 36 L) mutationRate (initialSamples source hL)
      (initialSamples_complete source hL)

/-- Source choice precedes ancestry and remains in the joint output, so later
distance bins use the same source that determined the initial sample locations. -/
noncomputable def serialSourceGenomeLaw (L : ℕ) (hL : 0 < L) :
    FiniteReportLaw (Fin 10 × WholeGenome L (cohortSize 10 * 2)) :=
  (sourceLaw 10 (by norm_num)).joint (serialGenomeLaw L hL)

noncomputable def gridSourceGenomeLaw (L : ℕ) (hL : 0 < L) :
    FiniteReportLaw (Fin 36 × WholeGenome L (cohortSize 36 * 2)) :=
  (sourceLaw 36 (by norm_num)).joint (gridGenomeLaw L hL)

theorem serialSourceGenome_expectation (L : ℕ) (hL : 0 < L)
    (readout : Fin 10 × WholeGenome L (cohortSize 10 * 2) → ℝ) :
    (serialSourceGenomeLaw L hL).expectation readout =
      (∑ source, (serialGenomeLaw L hL source).expectation
        (fun genome ↦ readout (source, genome))) / 10 := by
  rw [serialSourceGenomeLaw, expectation_joint]
  unfold expectation
  simp_rw [sourceLaw_mass]
  rw [← Finset.mul_sum]
  ring

theorem gridSourceGenome_expectation (L : ℕ) (hL : 0 < L)
    (readout : Fin 36 × WholeGenome L (cohortSize 36 * 2) → ℝ) :
    (gridSourceGenomeLaw L hL).expectation readout =
      (∑ source, (gridGenomeLaw L hL source).expectation
        (fun genome ↦ readout (source, genome))) / 36 := by
  rw [gridSourceGenomeLaw, expectation_joint]
  unfold expectation
  simp_rw [sourceLaw_mass]
  rw [← Finset.mul_sum]
  ring

end Descent.Portability.SimulationDemographyLaw
