/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.PartialHaplotypeDualSemigroup

assert_below Descent.Decision Descent.Program

/-!
# Substitution kernels of splits and admixture pulses on partial-haplotype moments

The last paragraph of NOTE1 §4.2 states that splits and admixture pulses have finite
substitution kernels on the partial-haplotype carrier, because they only reassign lineage
parents.  This module formalizes that claim.  A pulse matrix `A` assigns a probability vector
`A i` to every deme `i`: across the pulse a lineage sampled in deme `i` descends from deme `j`
with probability `A i j`.  Forward in time the haplotype law of deme `i` after the pulse is the
mixture `Σ_j A i j · law_j` (`pulsedLaw`).  The split of a daughter deme from a parent deme is
the pulse whose daughter row is the point mass at the parent (`PulseMatrix.split`).

After the pulse the marginal frequency of a partial type is `Σ_j A_{τ.deme, j} x_j[τ]`, so the
configuration moment `H_ξ` is a product of such sums.  Expanding the product over a listing of
the carriers gives the substitution kernel: a choice of parent deme for every carrier, with
probability the product of the chosen weights, relabels the carriers by migration
(`configurationMoment_pulsedLaw`).  The weights are nonnegative and sum to one
(`sum_choiceWeight`), and relabelling preserves every per-locus load (`load_relabelCarriers`).
The kernel therefore acts on the budget-respecting state space of
`Descent.Portability.PartialHaplotypeDualSemigroup` as a stochastic matrix `pulseKernel`, whose
action on configuration moments is the pulse (`pulseKernel_mulVec_configurationMoment`) and which
carries expected moment vectors across the pulse (`pulseKernel_mulVec_expectedMoment`).

Scope.  Interleaving pulses with the epoch exponentials of
`Descent.Portability.PartialHaplotypeDualSemigroup` is a product of matrices; a combined history
theorem is not stated here.

## Empirical status

None.  The bodies here are algebra: finite sums and products of supplied mixture weights and
marginal masses, so no measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.PartialHaplotypePulseKernel

open PartialHaplotypeCarrier PartialHaplotypeDualGenerator PartialHaplotypeDualSemigroup
open SubstochasticGeneratorSemigroup Descent.Foundations

variable {Deme Locus : Type*} {Allele : Locus → Type*}

/-- A pulse matrix: `weight i j` is the probability that a lineage sampled in deme `i` descends
from deme `j` across the pulse, so every row is a probability vector. -/
structure PulseMatrix (Deme : Type*) [Fintype Deme] where
  /-- The parent-deme weights. -/
  weight : Deme → Deme → ℝ
  /-- No weight is negative. -/
  weight_nonneg : ∀ i j, 0 ≤ weight i j
  /-- Every row sums to one. -/
  row_sum : ∀ i, ∑ j, weight i j = 1

/-- The identity pulse: every lineage stays in its own deme.  It inhabits `PulseMatrix`. -/
def PulseMatrix.identity [Fintype Deme] [DecidableEq Deme] : PulseMatrix Deme where
  weight i j := if i = j then 1 else 0
  weight_nonneg i j := by split_ifs <;> norm_num
  row_sum i := by simp

/-- The split of a daughter deme from a parent deme: lineages of the daughter descend from the
parent, and every other deme is unchanged. -/
def PulseMatrix.split [Fintype Deme] [DecidableEq Deme] (daughter parent : Deme) :
    PulseMatrix Deme where
  weight i j := if i = daughter then (if j = parent then 1 else 0) else (if i = j then 1 else 0)
  weight_nonneg i j := by split_ifs <;> norm_num
  row_sum i := by split_ifs <;> simp

variable [Fintype Deme] [DecidableEq Deme] [Fintype Locus] [DecidableEq Locus]
  [∀ ℓ, Fintype (Allele ℓ)] [∀ ℓ, DecidableEq (Allele ℓ)]

noncomputable section

/-- The per-deme haplotype laws after a pulse: deme `i` holds the mixture `Σ_j A i j · law_j`. -/
def pulsedLaw (pulse : PulseMatrix Deme)
    (law : Deme → FiniteReportLaw (FullHaplotype Locus Allele)) :
    Deme → FiniteReportLaw (FullHaplotype Locus Allele) :=
  fun i ↦
    { mass := fun hap ↦ ∑ j, pulse.weight i j * (law j).mass hap
      mass_nonneg := fun hap ↦
        Finset.sum_nonneg fun j _ ↦ mul_nonneg (pulse.weight_nonneg i j) ((law j).mass_nonneg hap)
      mass_sum := by
        rw [Finset.sum_comm]
        simp only [← Finset.mul_sum, FiniteReportLaw.mass_sum, mul_one]
        exact pulse.row_sum i }

/-- After a pulse, the marginal frequency of a partial type is the pulse-weighted average of the
marginal frequencies of its relabellings. -/
theorem marginalFrequency_pulsedLaw (pulse : PulseMatrix Deme)
    (law : Deme → FiniteReportLaw (FullHaplotype Locus Allele))
    (τ : PartialType Deme Locus Allele) :
    marginalFrequency (pulsedLaw pulse law) τ
      = ∑ j, pulse.weight τ.deme j * marginalFrequency law (migrate τ j) := by
  simp only [marginalFrequency, pulsedLaw]
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum]
  rfl

/-- The carriers of a listing relabelled by a choice of parent deme for every position. -/
def relabelCarriers (carriers : List (PartialType Deme Locus Allele))
    (choice : Fin carriers.length → Deme) : Multiset (PartialType Deme Locus Allele) :=
  Finset.univ.val.map fun k ↦ migrate (carriers.get k) (choice k)

/-- The probability of a choice of parent deme for every position of a listing. -/
def choiceWeight (pulse : PulseMatrix Deme) (carriers : List (PartialType Deme Locus Allele))
    (choice : Fin carriers.length → Deme) : ℝ :=
  ∏ k, pulse.weight (carriers.get k).deme (choice k)

/-- A listing, read as a configuration, is the image of its positions. -/
theorem carriers_eq_map_get (carriers : List (PartialType Deme Locus Allele)) :
    (↑carriers : Multiset (PartialType Deme Locus Allele))
      = Finset.univ.val.map carriers.get := by
  rw [Fin.univ_val_map, List.ofFn_get]

/-- Relabelling the demes of the carriers changes no per-locus load. -/
theorem load_relabelCarriers (carriers : List (PartialType Deme Locus Allele))
    (choice : Fin carriers.length → Deme) (ℓ : Locus) :
    load (relabelCarriers carriers choice) ℓ
      = load (↑carriers : Multiset (PartialType Deme Locus Allele)) ℓ := by
  rw [carriers_eq_map_get]
  simp only [load, relabelCarriers, Multiset.countP_map, migrate]

/-- Relabelling a budget-respecting configuration keeps it within the budget. -/
theorem withinBudget_relabelCarriers (capacity : Locus → ℕ)
    (ξ : Multiset (PartialType Deme Locus Allele)) (hξ : WithinBudget capacity ξ)
    (choice : Fin ξ.toList.length → Deme) :
    WithinBudget capacity (relabelCarriers ξ.toList choice) := by
  intro ℓ
  rw [load_relabelCarriers, Multiset.coe_toList]
  exact hξ ℓ

/-- Choice probabilities are nonnegative. -/
theorem choiceWeight_nonneg (pulse : PulseMatrix Deme)
    (carriers : List (PartialType Deme Locus Allele)) (choice : Fin carriers.length → Deme) :
    0 ≤ choiceWeight pulse carriers choice :=
  Finset.prod_nonneg fun k _ ↦ pulse.weight_nonneg _ _

/-- Choice probabilities sum to one. -/
theorem sum_choiceWeight (pulse : PulseMatrix Deme)
    (carriers : List (PartialType Deme Locus Allele)) :
    ∑ choice : Fin carriers.length → Deme, choiceWeight pulse carriers choice = 1 := by
  have h := Finset.prod_univ_sum (fun _ : Fin carriers.length ↦ (Finset.univ : Finset Deme))
    fun k j ↦ pulse.weight (carriers.get k).deme j
  simp only [pulse.row_sum, Finset.prod_const_one, Fintype.piFinset_univ] at h
  exact h.symm

/-- **The substitution kernel of a pulse.**  The configuration moment of the carriers of a
listing after the pulse is the expectation, over the choices of parent demes, of the moment of
the relabelled configuration before the pulse. -/
theorem configurationMoment_pulsedLaw (pulse : PulseMatrix Deme)
    (law : Deme → FiniteReportLaw (FullHaplotype Locus Allele))
    (carriers : List (PartialType Deme Locus Allele)) :
    configurationMoment (pulsedLaw pulse law) ↑carriers
      = ∑ choice : Fin carriers.length → Deme, choiceWeight pulse carriers choice
          * configurationMoment law (relabelCarriers carriers choice) := by
  have hprod : ∀ (lw : Deme → FiniteReportLaw (FullHaplotype Locus Allele))
      (g : Fin carriers.length → PartialType Deme Locus Allele),
      configurationMoment lw (Finset.univ.val.map g) = ∏ k, marginalFrequency lw (g k) := by
    intro lw g
    rw [configurationMoment, Multiset.map_map]
    rfl
  rw [carriers_eq_map_get, hprod]
  simp only [marginalFrequency_pulsedLaw, Finset.prod_univ_sum, Fintype.piFinset_univ,
    choiceWeight, relabelCarriers, hprod, ← Finset.prod_mul_distrib]

/-- The substitution kernel of a pulse on the budget-respecting state space: the probability that
the pulse relabels the carriers of `ξ` into `η`, over the choices of parent demes for a listing of
`ξ`. -/
def pulseKernel (pulse : PulseMatrix Deme) (capacity : Locus → ℕ) :
    Matrix (BudgetConfiguration Deme Locus Allele capacity)
      (BudgetConfiguration Deme Locus Allele capacity) ℝ :=
  fun ξ η ↦ ∑ choice : Fin ξ.1.toList.length → Deme,
    if relabelCarriers ξ.1.toList choice = η.1 then choiceWeight pulse ξ.1.toList choice else 0

/-- The pulse kernel applied to a table of values averages the values of the relabelled
configurations. -/
theorem pulseKernel_mulVec (pulse : PulseMatrix Deme) (capacity : Locus → ℕ)
    (value : Multiset (PartialType Deme Locus Allele) → ℝ)
    (ξ : BudgetConfiguration Deme Locus Allele capacity) :
    (pulseKernel pulse capacity).mulVec (fun η ↦ value η.1) ξ
      = ∑ choice : Fin ξ.1.toList.length → Deme,
          choiceWeight pulse ξ.1.toList choice * value (relabelCarriers ξ.1.toList choice) := by
  simp only [Matrix.mulVec, dotProduct, pulseKernel, Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun choice _ ↦ ?_
  rw [Finset.sum_eq_single
    ⟨relabelCarriers ξ.1.toList choice, withinBudget_relabelCarriers capacity ξ.1 ξ.2 choice⟩]
  · simp
  · intro η _ hne
    exact if_neg fun heq ↦ hne (Subtype.ext heq.symm)
  · intro hnot
    exact absurd (Finset.mem_univ _) hnot

/-- Every row of the pulse kernel sums to one: a pulse loses no mass. -/
theorem pulseKernel_rowSum (pulse : PulseMatrix Deme) (capacity : Locus → ℕ)
    (ξ : BudgetConfiguration Deme Locus Allele capacity) :
    ∑ η, pulseKernel pulse capacity ξ η = 1 := by
  have h := pulseKernel_mulVec pulse capacity (fun _ ↦ 1) ξ
  simp only [Matrix.mulVec, dotProduct, mul_one, sum_choiceWeight] at h
  exact h

/-- The pulse kernel is a stochastic, hence substochastic, matrix. -/
theorem pulseKernel_substochastic (pulse : PulseMatrix Deme) (capacity : Locus → ℕ) :
    SubstochasticMatrix (pulseKernel pulse capacity) where
  entry_nonneg ξ η := Finset.sum_nonneg fun choice _ ↦ by
    split_ifs
    · exact choiceWeight_nonneg pulse _ choice
    · exact le_rfl
  rowSum_le_one ξ := (pulseKernel_rowSum pulse capacity ξ).le

/-- **The pulse acts on configuration moments through its substitution kernel.**  The kernel
applied to the moment vector of per-deme haplotype laws is the moment vector of the pulsed
laws. -/
theorem pulseKernel_mulVec_configurationMoment (pulse : PulseMatrix Deme) (capacity : Locus → ℕ)
    (law : Deme → FiniteReportLaw (FullHaplotype Locus Allele))
    (ξ : BudgetConfiguration Deme Locus Allele capacity) :
    (pulseKernel pulse capacity).mulVec (fun η ↦ configurationMoment law η.1) ξ
      = configurationMoment (pulsedLaw pulse law) ξ.1 := by
  rw [pulseKernel_mulVec, ← configurationMoment_pulsedLaw, Multiset.coe_toList]

/-- **Expected moments across a pulse.**  For any expectation functional over per-deme haplotype
laws, the expected moments of the pulsed laws are the pulse kernel applied to the expected
moments before the pulse. -/
theorem pulseKernel_mulVec_expectedMoment (pulse : PulseMatrix Deme) (capacity : Locus → ℕ)
    (expectation : ExpFunctional (Deme → FiniteReportLaw (FullHaplotype Locus Allele)))
    (ξ : BudgetConfiguration Deme Locus Allele capacity) :
    (expectation fun law ↦ configurationMoment (pulsedLaw pulse law) ξ.1)
      = (pulseKernel pulse capacity).mulVec
          (fun η ↦ expectation fun law ↦ configurationMoment law η.1) ξ := by
  have hpoint : (fun law ↦ configurationMoment (pulsedLaw pulse law) ξ.1)
      = ∑ η, pulseKernel pulse capacity ξ η • fun law ↦ configurationMoment law η.1 := by
    funext law
    rw [← pulseKernel_mulVec_configurationMoment pulse capacity law ξ]
    simp [Matrix.mulVec, dotProduct, Finset.sum_apply]
  rw [hpoint, ExpFunctional.eval_sum]
  simp only [ExpFunctional.smul_eval, Matrix.mulVec, dotProduct]

end

end Descent.Portability.PartialHaplotypePulseKernel
