/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.ExactFiniteHistoryLaw

assert_below Descent.Decision Descent.Program

namespace Descent.Portability.FiniteDemographicSampling

open scoped Classical

/-!
# A constructed finite demographic transition law

This is a neutral, haploid, biallelic Wright–Fisher model with finitely many demes and
the same positive census size `N` in each deme. For each offspring independently: choose
a parental deme from its migration row, draw an allele uniformly from that deme's parental
copies, then apply two-way mutation. The product law explicitly makes those offspring
draws conditionally independent. Migration and mutation may change at every generation.

The model constructs normalized count transitions from these biological sampling choices;
it does not take the resulting genotype transition kernel as an unexplained input. This
one-locus model does not include linkage, selection, diploid mating, variable census sizes,
phenotypes, or a training algorithm. Arbitrary terminal readouts can be evaluated exactly,
but those omitted mechanisms are not supplied by the generic readout theorem.
-/

variable {Deme : Type*} [Fintype Deme]

/-- Parental counts of the focal allele, including loss and fixation. -/
abbrev Counts (Deme : Type*) (N : ℕ) := Deme → Fin (N + 1)

/-- Demographic and mutation inputs, not an assumed offspring genotype kernel.
Migration rows index destination first, then the sampled parental source deme. -/
structure Step (Deme : Type*) [Fintype Deme] where
  migration : Deme → FiniteReportLaw Deme
  mutationUp : Deme → Set.Icc (0 : ℝ) 1
  mutationDown : Deme → Set.Icc (0 : ℝ) 1

/-- A normalized Bernoulli law retaining both allele outcomes. -/
noncomputable def bernoulli (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    FiniteReportLaw Bool where
  mass := fun allele ↦ if allele then p else 1 - p
  mass_nonneg := by intro allele; cases allele <;> simp <;> linarith
  mass_sum := by simp

/-- The focal-allele frequency read from the actual parental count. -/
noncomputable def parentalFrequency {N : ℕ} (counts : Counts Deme N) (deme : Deme) : ℝ :=
  (counts deme).val / (N : ℝ)

omit [Fintype Deme] in
theorem parentalFrequency_nonneg {N : ℕ} (counts : Counts Deme N) (deme : Deme) :
    0 ≤ parentalFrequency counts deme := by
  unfold parentalFrequency
  positivity

omit [Fintype Deme] in
theorem parentalFrequency_le_one {N : ℕ} (hN : 0 < N)
    (counts : Counts Deme N) (deme : Deme) : parentalFrequency counts deme ≤ 1 := by
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  have hcount : (counts deme).val ≤ N := Nat.lt_succ_iff.mp (counts deme).isLt
  unfold parentalFrequency
  apply (div_le_one hNreal).mpr
  exact_mod_cast hcount

/-- Sampling a uniformly chosen parental gene copy gives this two-outcome law.
The count-to-frequency rule is the uniform within-deme sampling premise. -/
noncomputable def parentalAlleleLaw {N : ℕ} (hN : 0 < N)
    (counts : Counts Deme N) (deme : Deme) : FiniteReportLaw Bool :=
  bernoulli (parentalFrequency counts deme) (parentalFrequency_nonneg counts deme)
    (parentalFrequency_le_one hN counts deme)

/-- First sample a parental deme, then an allele from its actual finite census. -/
noncomputable def inheritedAlleleLaw {N : ℕ} (step : Step Deme) (hN : 0 < N)
    (counts : Counts Deme N) (destination : Deme) : FiniteReportLaw Bool :=
  (step.migration destination).bind (parentalAlleleLaw hN counts)

/-- The post-migration frequency is derived from the sampled parental-deme mixture. -/
theorem inheritedAlleleLaw_true {N : ℕ} (step : Step Deme) (hN : 0 < N)
    (counts : Counts Deme N) (destination : Deme) :
    (inheritedAlleleLaw step hN counts destination).mass true =
      ∑ source, (step.migration destination).mass source * parentalFrequency counts source := by
  simp [inheritedAlleleLaw, FiniteReportLaw.bind, parentalAlleleLaw, bernoulli]

/-- Conditional two-way mutation after parental copying. -/
noncomputable def mutationLaw (step : Step Deme) (destination : Deme) (parent : Bool) :
    FiniteReportLaw Bool :=
  if parent then
    bernoulli (1 - (step.mutationDown destination).val)
      (by linarith [(step.mutationDown destination).property.2])
      (by linarith [(step.mutationDown destination).property.1])
  else bernoulli (step.mutationUp destination).val
    (step.mutationUp destination).property.1 (step.mutationUp destination).property.2

/-- The single offspring law is constructed by composing migration, copying, and mutation. -/
noncomputable def offspringAlleleLaw {N : ℕ} (step : Step Deme) (hN : 0 < N)
    (counts : Counts Deme N) (destination : Deme) : FiniteReportLaw Bool :=
  (inheritedAlleleLaw step hN counts destination).bind (mutationLaw step destination)

/-- Exact post-migration, post-mutation focal-allele probability. -/
noncomputable def offspringFrequency {N : ℕ} (step : Step Deme)
    (counts : Counts Deme N) (destination : Deme) : ℝ :=
  let q := ∑ source,
    (step.migration destination).mass source * parentalFrequency counts source
  (1 - (step.mutationDown destination).val) * q +
    (step.mutationUp destination).val * (1 - q)

/-- Mutation acts on the exact migration mixture, with no diffusion or moment closure. -/
theorem offspringAlleleLaw_true {N : ℕ} (step : Step Deme) (hN : 0 < N)
    (counts : Counts Deme N) (destination : Deme) :
    (offspringAlleleLaw step hN counts destination).mass true =
      offspringFrequency step counts destination := by
  have hsum := (inheritedAlleleLaw step hN counts destination).mass_sum
  simp only [Fintype.sum_bool] at hsum
  have htrue := inheritedAlleleLaw_true step hN counts destination
  have hfalse : (inheritedAlleleLaw step hN counts destination).mass false =
      1 - ∑ source,
        (step.migration destination).mass source * parentalFrequency counts source := by
    linarith
  simp only [offspringAlleleLaw, FiniteReportLaw.bind, Fintype.sum_bool]
  simp [mutationLaw, bernoulli]
  dsimp only [offspringFrequency]
  rw [htrue, hfalse]
  ring

theorem offspringAlleleLaw_false {N : ℕ} (step : Step Deme) (hN : 0 < N)
    (counts : Counts Deme N) (destination : Deme) :
    (offspringAlleleLaw step hN counts destination).mass false =
      1 - offspringFrequency step counts destination := by
  have hsum := (offspringAlleleLaw step hN counts destination).mass_sum
  simp only [Fintype.sum_bool, offspringAlleleLaw_true] at hsum
  linarith

/-- Independent finite draws, normalized by the existing finite product-of-sums identity. -/
noncomputable def independentLaw {Index : Type*} [Fintype Index] [DecidableEq Index]
    (law : Index → FiniteReportLaw Bool) : FiniteReportLaw (Index → Bool) where
  mass := fun configuration ↦ ∏ i, (law i).mass (configuration i)
  mass_nonneg := fun configuration ↦
    Finset.prod_nonneg (fun i _ ↦ (law i).mass_nonneg (configuration i))
  mass_sum := by
    rw [← Fintype.prod_sum]
    simp only [FiniteReportLaw.mass_sum, Finset.prod_const_one]

/-- Labelled offspring gene copies before count aggregation. -/
abbrev Offspring (Deme : Type*) (N : ℕ) := (Deme × Fin N) → Bool

variable [DecidableEq Deme]

/-- Conditional independent reproduction of every gene copy in every destination deme. -/
noncomputable def offspringLaw {N : ℕ} (step : Step Deme) (hN : 0 < N)
    (counts : Counts Deme N) : FiniteReportLaw (Offspring Deme N) :=
  independentLaw (fun copy : Deme × Fin N ↦ offspringAlleleLaw step hN counts copy.1)

/-- Every labelled offspring configuration has this exact product probability. -/
theorem offspringLaw_mass {N : ℕ} (step : Step Deme) (hN : 0 < N)
    (counts : Counts Deme N) (configuration : Offspring Deme N) :
    (offspringLaw step hN counts).mass configuration =
      ∏ copy, if configuration copy then offspringFrequency step counts copy.1
        else 1 - offspringFrequency step counts copy.1 := by
  change (∏ copy, (offspringAlleleLaw step hN counts copy.1).mass (configuration copy)) = _
  apply Finset.prod_congr rfl
  intro copy _
  cases h : configuration copy <;>
    simp [offspringAlleleLaw_true, offspringAlleleLaw_false]

/-- Count focal alleles in each destination, with the census bound proved by counting. -/
noncomputable def countOffspring {N : ℕ} (configuration : Offspring Deme N) :
    Counts Deme N := by
  classical
  exact fun deme ↦ ⟨(Finset.univ.filter fun copy : Fin N ↦ configuration (deme, copy)).card,
    Nat.lt_succ_of_le (by
      simpa using (Finset.card_filter_le
        (s := Finset.univ) (p := fun copy : Fin N ↦ configuration (deme, copy))))⟩

/-- A normalized demographic count transition derived from labelled reproduction. -/
noncomputable def transition {N : ℕ} (step : Step Deme) (hN : 0 < N)
    (counts : Counts Deme N) : FiniteReportLaw (Counts Deme N) :=
  (offspringLaw step hN counts).pushforward countOffspring

/-- Exact count-transition probability, aggregating every labelled offspring realization.
This finite sum includes the combinatorial multiplicities without a binomial approximation. -/
theorem transition_mass {N : ℕ} (step : Step Deme) (hN : 0 < N)
    (counts next : Counts Deme N) :
    (transition step hN counts).mass next =
      ∑ configuration : Offspring Deme N,
        (∏ copy, if configuration copy then offspringFrequency step counts copy.1
          else 1 - offspringFrequency step counts copy.1) *
        (if countOffspring configuration = next then 1 else 0) := by
  classical
  simp only [transition, FiniteReportLaw.pushforward, FiniteReportLaw.bind]
  apply Finset.sum_congr rfl
  intro configuration _
  rw [offspringLaw_mass]
  by_cases h : countOffspring configuration = next
  · simp [FiniteReportLaw.pointMass, h]
  · simp [FiniteReportLaw.pointMass, h, Ne.symm h]

/-- Exact finite-horizon demographic prediction for every real-valued count readout. -/
theorem history_readout_exact {N : ℕ} (hN : 0 < N)
    (initial : FiniteReportLaw (Counts Deme N)) (history : ℕ → Step Deme)
    (generations : ℕ) (metric : Counts Deme N → ℝ) :
    (ExactFiniteHistoryLaw.propagate initial
      (fun time ↦ transition (history time) hN) generations).expectation metric =
      initial.expectation (ExactFiniteHistoryLaw.backwardReadout
        (fun time ↦ transition (history time) hN) generations metric) :=
  ExactFiniteHistoryLaw.expectation_propagate initial _ generations metric

/-- The same demographic prediction is the exact sum over every complete count history. -/
theorem history_path_sum_exact {N : ℕ} (hN : 0 < N)
    (initial : FiniteReportLaw (Counts Deme N)) (history : ℕ → Step Deme)
    (generations : ℕ) (metric : Counts Deme N → ℝ) :
    (∑ path : ExactFiniteHistoryLaw.Path (Counts Deme N) generations,
      ExactFiniteHistoryLaw.pathMass initial
        (fun time ↦ transition (history time) hN) path *
        metric (ExactFiniteHistoryLaw.terminal path)) =
      initial.expectation (ExactFiniteHistoryLaw.backwardReadout
        (fun time ↦ transition (history time) hN) generations metric) := by
  rw [ExactFiniteHistoryLaw.path_sum_eq_expectation, history_readout_exact]

end Descent.Portability.FiniteDemographicSampling
