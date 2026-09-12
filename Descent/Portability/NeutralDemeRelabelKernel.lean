/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.NeutralHistoryKernel

assert_below Descent.Decision Descent.Program

/-!
# Neutral Markov kernels across a change of the deme set

NOTE1 §4.2 lets a history found new demes by splits.  Within a fixed deme set a split is the
pulse whose daughter row is the point mass at the parent
(`PartialHaplotypePulseKernel.PulseMatrix.split`).  When the split changes the deme set itself,
it is a relabelling: a map `parent : Deme' → Deme` names the deme of the old population from
which every deme of the new population is founded, and the new state copies the haplotype
frequencies of the parent (`relabelState`).  A deme that persists
is its own parent; a daughter founded by a split shares the parent of its founding deme.

The move is deterministic and continuous (`continuous_relabelState`), so it is a Markov kernel
(`relabelStateKernel`).  On partial-haplotype moments it substitutes carriers: a carrier sitting in
a new deme becomes the same carrier in the parent deme (`relabelCarrier`), which keeps every
per-locus load (`load_map_relabelCarrier`) and hence the retention budget.  The configuration
moment of the relabelled state is the moment of the relabelled configuration before the split
(`configurationMoment_stateLaw_relabelState`).  The substitution is a deterministic stochastic
matrix from the budget configurations of the new deme set to those of the old one
(`relabelKernel`, `relabelKernel_rowSum`), and it carries expected moments across the split
(`integral_momentPolynomial_relabelStateKernel`).

Expected configuration moments compose by matrix product across kernels between different deme
sets (`integral_momentPolynomial_comp_hetero`).  So a history of constant-rate epochs on one deme
set, a split into another, and constant-rate epochs on the new set has expected configuration
moments `P' R P` applied to the initial moments, with `P` and `P'` the chronological epoch
propagators of `NeutralHistoryKernel` and `R` the substitution matrix of the split
(`integral_momentPolynomial_splitHistoryKernel`).

Scope.  One change of deme set is composed explicitly; longer alternations follow by the same
composition lemma.  Admixture pulses within a deme set are not treated here.

## Empirical status

None.  The bodies here are integrals of polynomials against compositions of Markov kernels, finite
multisets relabelled along a supplied map, and products of matrix exponentials of supplied rates,
so no measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.NeutralDemeRelabelKernel

open MeasureTheory ProbabilityTheory MvPolynomial Descent.Coalescent PartialHaplotypeCarrier
  PartialHaplotypeDualGenerator PartialHaplotypeDualSemigroup NeutralFellerGenerator
  NeutralPolynomialSemigroup PartialHaplotypeMicroscopicApproximation
  NeutralMicroscopicEulerLimit NeutralKernelPanelLikelihood NeutralHistoryKernel
open scoped Matrix NNReal

noncomputable section

section Carriers

variable {Deme Deme' Locus : Type*} {Allele : Locus → Type*}

/-- **A carrier moved to the parent of its deme.**  The same partial allele assignment, sitting in
the deme of the old population from which its deme was founded. -/
def relabelCarrier (parent : Deme' → Deme) (τ : PartialType Deme' Locus Allele) :
    PartialType Deme Locus Allele where
  deme := parent τ.deme
  allele := τ.allele
  retained := τ.retained

/-- Relabelling the demes of the carriers changes no per-locus load. -/
theorem load_map_relabelCarrier (parent : Deme' → Deme)
    (ξ : Multiset (PartialType Deme' Locus Allele)) (ℓ : Locus) :
    load (ξ.map (relabelCarrier parent)) ℓ = load ξ ℓ := by
  induction ξ using Multiset.induction_on with
  | empty => simp [load]
  | cons τ ξ ih =>
    simp only [Multiset.map_cons, load, Multiset.countP_cons] at ih ⊢
    rw [ih]
    rfl

/-- Relabelling a budget-respecting configuration keeps it within the budget. -/
theorem withinBudget_map_relabelCarrier (parent : Deme' → Deme) (capacity : Locus → ℕ)
    (ξ : Multiset (PartialType Deme' Locus Allele)) (hξ : WithinBudget capacity ξ) :
    WithinBudget capacity (ξ.map (relabelCarrier parent)) := by
  intro ℓ
  rw [load_map_relabelCarrier]
  exact hξ ℓ

end Carriers

variable {Deme Deme' Locus : Type*} {Allele : Locus → Type*}
variable [Fintype Deme] [DecidableEq Deme] [Fintype Deme'] [DecidableEq Deme']
  [Fintype Locus] [DecidableEq Locus] [∀ ℓ, Fintype (Allele ℓ)] [∀ ℓ, DecidableEq (Allele ℓ)]

/-! ## The split on frequency states -/

/-- **The frequency state founded by a split.**  Every deme of the new population holds the
haplotype frequencies of its parent deme. -/
def relabelState (parent : Deme' → Deme) (x : FrequencyState Deme Locus Allele) :
    FrequencyState Deme' Locus Allele :=
  ⟨fun c ↦ x.1 (parent c.1, c.2), fun c ↦ x.2.1 (parent c.1, c.2), fun i ↦ x.2.2 (parent i)⟩

/-- The per-deme laws of the founded state are the laws of the parents. -/
theorem stateLaw_relabelState (parent : Deme' → Deme) (x : FrequencyState Deme Locus Allele)
    (i : Deme') : stateLaw (relabelState parent x) i = stateLaw x (parent i) :=
  rfl

/-- A split acts continuously on frequency states. -/
theorem continuous_relabelState (parent : Deme' → Deme) :
    Continuous (relabelState (Locus := Locus) (Allele := Allele) parent) :=
  (continuous_pi fun c ↦
    (continuous_apply (parent c.1, c.2)).comp continuous_subtype_val).subtype_mk
      fun x ↦ (relabelState parent x).2

/-- **The Markov kernel of a split**: the deterministic move to the founded state. -/
def relabelStateKernel (parent : Deme' → Deme) :
    Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme' Locus Allele) :=
  Kernel.deterministic (relabelState parent) (continuous_relabelState parent).measurable

/-- The kernel of a split is a Markov kernel. -/
theorem isMarkovKernel_relabelStateKernel (parent : Deme' → Deme) :
    IsMarkovKernel (relabelStateKernel (Locus := Locus) (Allele := Allele) parent) := by
  rw [relabelStateKernel]
  infer_instance

/-! ## The split on configuration moments -/

/-- After a split, the marginal frequency of a carrier is the marginal frequency of the relabelled
carrier before it. -/
theorem marginalFrequency_stateLaw_relabelState (parent : Deme' → Deme)
    (x : FrequencyState Deme Locus Allele) (τ : PartialType Deme' Locus Allele) :
    marginalFrequency (stateLaw (relabelState parent x)) τ
      = marginalFrequency (stateLaw x) (relabelCarrier parent τ) :=
  rfl

/-- **The substitution of a split.**  The configuration moment of the founded state is the moment
of the relabelled configuration before the split. -/
theorem configurationMoment_stateLaw_relabelState (parent : Deme' → Deme)
    (x : FrequencyState Deme Locus Allele) (ξ : Multiset (PartialType Deme' Locus Allele)) :
    configurationMoment (stateLaw (relabelState parent x)) ξ
      = configurationMoment (stateLaw x) (ξ.map (relabelCarrier parent)) := by
  rw [configurationMoment, configurationMoment, Multiset.map_map]
  congr 1
  exact Multiset.map_congr rfl fun τ _ ↦ marginalFrequency_stateLaw_relabelState parent x τ

/-- The budget moment features of the founded state are the features of the relabelled
configurations before the split. -/
theorem budgetMomentFeature_relabelState (parent : Deme' → Deme) (capacity : Locus → ℕ)
    (x : FrequencyState Deme Locus Allele) (ξ : BudgetConfiguration Deme' Locus Allele capacity) :
    budgetMomentFeature capacity (relabelState parent x) ξ
      = budgetMomentFeature capacity x ⟨ξ.1.map (relabelCarrier parent),
          withinBudget_map_relabelCarrier parent capacity ξ.1 ξ.2⟩ :=
  (eval_momentPolynomial (stateLaw (relabelState parent x)) ξ.1).trans
    ((configurationMoment_stateLaw_relabelState parent x ξ.1).trans
      (eval_momentPolynomial (stateLaw x) (ξ.1.map (relabelCarrier parent))).symm)

/-- **The substitution matrix of a split**: the budget configuration of the new deme set is
relabelled into the budget configuration of the old one with probability one. -/
def relabelKernel (parent : Deme' → Deme) (capacity : Locus → ℕ) :
    Matrix (BudgetConfiguration Deme' Locus Allele capacity)
      (BudgetConfiguration Deme Locus Allele capacity) ℝ :=
  fun ξ η ↦ if ξ.1.map (relabelCarrier parent) = η.1 then 1 else 0

/-- The substitution matrix applied to a table of values reads the value of the relabelled
configuration. -/
theorem relabelKernel_mulVec (parent : Deme' → Deme) (capacity : Locus → ℕ)
    (v : BudgetConfiguration Deme Locus Allele capacity → ℝ)
    (ξ : BudgetConfiguration Deme' Locus Allele capacity) :
    (relabelKernel parent capacity *ᵥ v) ξ
      = v ⟨ξ.1.map (relabelCarrier parent),
          withinBudget_map_relabelCarrier parent capacity ξ.1 ξ.2⟩ := by
  simp only [Matrix.mulVec, dotProduct, relabelKernel, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_eq_single
    ⟨ξ.1.map (relabelCarrier parent), withinBudget_map_relabelCarrier parent capacity ξ.1 ξ.2⟩]
  · simp
  · intro η _ hne
    exact if_neg fun heq ↦ hne (Subtype.ext heq.symm)
  · intro hnot
    exact absurd (Finset.mem_univ _) hnot

/-- Every row of the substitution matrix sums to one: a split loses no mass. -/
theorem relabelKernel_rowSum (parent : Deme' → Deme) (capacity : Locus → ℕ)
    (ξ : BudgetConfiguration Deme' Locus Allele capacity) :
    ∑ η, relabelKernel (Allele := Allele) parent capacity ξ η = 1 := by
  have h := relabelKernel_mulVec (Allele := Allele) parent capacity (fun _ ↦ 1) ξ
  simp only [Matrix.mulVec, dotProduct, mul_one] at h
  exact h

/-- The entries of the substitution matrix are nonnegative. -/
theorem relabelKernel_nonneg (parent : Deme' → Deme) (capacity : Locus → ℕ)
    (ξ : BudgetConfiguration Deme' Locus Allele capacity)
    (η : BudgetConfiguration Deme Locus Allele capacity) :
    0 ≤ relabelKernel parent capacity ξ η := by
  unfold relabelKernel
  split_ifs <;> norm_num

/-- **A split on configuration moments, under the process law.**  The expected configuration
moments after a split are its substitution matrix applied to the moments of the initial state. -/
theorem integral_momentPolynomial_relabelStateKernel (parent : Deme' → Deme)
    (capacity : Locus → ℕ) (x : FrequencyState Deme Locus Allele)
    (ξ : BudgetConfiguration Deme' Locus Allele capacity) :
    ∫ y, polynomialFunction (momentPolynomial ξ.1) y ∂(relabelStateKernel parent x)
      = (relabelKernel parent capacity *ᵥ budgetMomentFeature capacity x) ξ := by
  rw [relabelStateKernel, Kernel.deterministic_apply, integral_dirac' _ _
    (polynomialFunction (momentPolynomial ξ.1)).continuous.stronglyMeasurable,
    relabelKernel_mulVec]
  exact budgetMomentFeature_relabelState parent capacity x ξ

/-! ## Composition across deme sets -/

/-- **Expected configuration moments compose by matrix product across deme sets.**  If the
expected moments under `κ` from the old deme set to the new are `M` applied to the initial moments,
and under `η` from the new deme set to a third are `N` applied to them, then under `η ∘ₖ κ` they
are `N M` applied to the initial moments. -/
theorem integral_momentPolynomial_comp_hetero {Deme'' : Type*} [Fintype Deme'']
    [DecidableEq Deme''] (capacity : Locus → ℕ)
    (κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme' Locus Allele))
    (η : Kernel (FrequencyState Deme' Locus Allele) (FrequencyState Deme'' Locus Allele))
    [IsMarkovKernel κ] [IsMarkovKernel η]
    (M : Matrix (BudgetConfiguration Deme' Locus Allele capacity)
      (BudgetConfiguration Deme Locus Allele capacity) ℝ)
    (N : Matrix (BudgetConfiguration Deme'' Locus Allele capacity)
      (BudgetConfiguration Deme' Locus Allele capacity) ℝ)
    (hκ : ∀ (x : FrequencyState Deme Locus Allele)
      (ξ : BudgetConfiguration Deme' Locus Allele capacity),
      ∫ y, polynomialFunction (momentPolynomial ξ.1) y ∂(κ x)
        = (M *ᵥ budgetMomentFeature capacity x) ξ)
    (hη : ∀ (x : FrequencyState Deme' Locus Allele)
      (ξ : BudgetConfiguration Deme'' Locus Allele capacity),
      ∫ y, polynomialFunction (momentPolynomial ξ.1) y ∂(η x)
        = (N *ᵥ budgetMomentFeature capacity x) ξ)
    (x : FrequencyState Deme Locus Allele)
    (ξ : BudgetConfiguration Deme'' Locus Allele capacity) :
    ∫ y, polynomialFunction (momentPolynomial ξ.1) y ∂((η ∘ₖ κ) x)
      = ((N * M) *ᵥ budgetMomentFeature capacity x) ξ := by
  have hint : ∀ ζ : BudgetConfiguration Deme' Locus Allele capacity,
      Integrable (fun y ↦ polynomialFunction (momentPolynomial ζ.1) y) (κ x) := fun ζ ↦
    (BoundedContinuousFunction.mkOfCompact
      (polynomialFunction (momentPolynomial ζ.1))).integrable _
  have hcomp : Integrable (fun y ↦ polynomialFunction (momentPolynomial ξ.1) y) ((η ∘ₖ κ) x) :=
    (BoundedContinuousFunction.mkOfCompact
      (polynomialFunction (momentPolynomial ξ.1))).integrable _
  rw [Kernel.integral_comp hcomp]
  calc ∫ y, ∫ z, polynomialFunction (momentPolynomial ξ.1) z ∂(η y) ∂(κ x)
      = ∫ y, ∑ ζ, N ξ ζ * polynomialFunction (momentPolynomial ζ.1) y ∂(κ x) := by
        congr 1
        funext y
        rw [hη y ξ]
        simp only [Matrix.mulVec, dotProduct]
        rfl
    _ = ∑ ζ, N ξ ζ * ∫ y, polynomialFunction (momentPolynomial ζ.1) y ∂(κ x) := by
        rw [integral_finset_sum Finset.univ fun ζ _ ↦ (hint ζ).const_mul (N ξ ζ)]
        simp only [integral_const_mul]
    _ = _ := by
        simp only [hκ, ← Matrix.mulVec_mulVec]
        simp only [Matrix.mulVec, dotProduct]

/-- **NOTE1 §4.2 across a split that changes the deme set, under the process law.**  Run the
constant-rate epochs `before` on the old deme set, found the new deme set by the split `parent`,
and run the epochs `after` on the new set.  For every budget, the expected configuration moments
are `P' R P` applied to the moments of the initial state, with `P` and `P'` the chronological
epoch propagators and `R` the substitution matrix of the split. -/
theorem integral_momentPolynomial_splitHistoryKernel (ℓ₀ : Locus)
    (hap₀ : FullHaplotype Locus Allele) (capacity : Locus → ℕ) (parent : Deme' → Deme)
    (before : List (NeutralRates Deme Locus Allele × ℝ≥0))
    (after : List (NeutralRates Deme' Locus Allele × ℝ≥0)) (x : FrequencyState Deme Locus Allele)
    (ξ : BudgetConfiguration Deme' Locus Allele capacity) :
    ∫ y, polynomialFunction (momentPolynomial ξ.1) y
        ∂((neutralHistoryKernel ℓ₀ hap₀ after
          ∘ₖ (relabelStateKernel parent ∘ₖ neutralHistoryKernel ℓ₀ hap₀ before)) x)
      = ((historyPropagator capacity (after.map fun epoch ↦ (epoch.1, (epoch.2 : ℝ)))
          * relabelKernel parent capacity
          * historyPropagator capacity (before.map fun epoch ↦ (epoch.1, (epoch.2 : ℝ))))
          *ᵥ budgetMomentFeature capacity x) ξ := by
  haveI := isMarkovKernel_neutralHistoryKernel ℓ₀ hap₀ before
  haveI := isMarkovKernel_neutralHistoryKernel ℓ₀ hap₀ after
  haveI := isMarkovKernel_relabelStateKernel (Locus := Locus) (Allele := Allele) parent
  rw [Matrix.mul_assoc]
  exact integral_momentPolynomial_comp_hetero capacity _ (neutralHistoryKernel ℓ₀ hap₀ after) _ _
    (fun x' ξ' ↦ integral_momentPolynomial_comp_hetero capacity
      (neutralHistoryKernel ℓ₀ hap₀ before) (relabelStateKernel parent) _ _
      (integral_momentPolynomial_neutralHistoryKernel ℓ₀ hap₀ capacity before)
      (integral_momentPolynomial_relabelStateKernel parent capacity) x' ξ')
    (integral_momentPolynomial_neutralHistoryKernel ℓ₀ hap₀ capacity after) x ξ

end

end Descent.Portability.NeutralDemeRelabelKernel
