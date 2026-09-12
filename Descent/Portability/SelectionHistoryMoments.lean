/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.AncestralLocality.SelectionDecisions
import Descent.Portability.PartialHaplotypePulseKernel

assert_below Descent.Decision Descent.Program

/-!
# Partial-haplotype moments with haploid selection at one locus

`PartialHaplotypeDualGenerator` proves NOTE1 (19) for the neutral diffusion: on configuration
moments the forward generator is a finite jump generator, so along a neutral history the expected
moments of a bounded budget are a matrix exponential of the initial moments. This module adds
selection.

The fitness model. Selection is haploid and acts at one locus `ℓ`: a haplotype `h` of deme `i`
has fitness `s_i(h_ℓ)`, and the fitness may differ between demes (`SelectionModel`). The mean
fitness of deme `i` is the polynomial `s̄_i = Σ_b s_i(b) x_i[ℓ = b]` (`meanFitnessPolynomial`),
which at a frequency point is the corpus mean fitness `AncestralLocality.meanFitness` of the deme
(`eval_meanFitnessPolynomial_eq_meanFitness`). Every haplotype frequency drifts at the classical
rate `x_i[h] (s_i(h_ℓ) - s̄_i)` (`selectiveDrift`, `eval_selectiveDrift`), the drift of
`AncestralLocality.selectionGenerator_eq_drift`, and the selection generator is the derivation
along that vector field (`selectionGenerator`). Without fitness differences it vanishes
(`selectionGenerator_neutral`), and the generator with selection (`selectedGenerator`) is the
neutral generator (`selectedGenerator_neutral`).

The generator on moments. The selection generator is a derivation (`selectionGenerator_mul`), so
on a configuration moment it acts carrier by carrier
(`eval_selectionGenerator_momentPolynomial`). On one carrier it weighs the haplotypes the carrier
counts by their fitness deviation from the deme mean (`eval_selectionGenerator_marginal`). At a
state, fitnesses in `[0, σ]` put the mean fitness in `[0, σ]` too
(`eval_meanFitnessPolynomial_mem`), so a carrier moves by at most `σ` times its frequency
(`abs_eval_selectionGenerator_marginal_le`) and a configuration with `n` carriers by at most
`n σ` times its moment (`abs_eval_selectionGenerator_momentPolynomial_le`).

Scope. Selection is haploid and at one locus; dominance, epistasis and fitness read at several
loci are not covered.

## Empirical status

None. The bodies here are algebra: derivatives of polynomials in supplied frequencies and finite
sums of supplied fitness values, so no measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.SelectionHistoryMoments

open MvPolynomial PartialHaplotypeCarrier PartialHaplotypeDualGenerator
  PartialHaplotypeDualSemigroup SubstochasticGeneratorSemigroup PartialHaplotypePulseKernel
open Descent.Coalescent Descent.Foundations
open scoped Matrix

variable {Deme Locus : Type*} {Allele : Locus → Type*}

/-- **Haploid selection at one locus.** A haplotype of deme `i` carrying allele `b` at the
selected locus has fitness `fitness i b`; demes may differ in fitness, as environments do. -/
structure SelectionModel (Deme Locus : Type*) (Allele : Locus → Type*) where
  /-- The selected locus. -/
  locus : Locus
  /-- The fitness of every allele of the selected locus in every deme. -/
  fitness : Deme → Allele locus → ℝ

/-- The neutral model at a locus: every allele has fitness zero. -/
def SelectionModel.neutral (ℓ : Locus) : SelectionModel Deme Locus Allele where
  locus := ℓ
  fitness _ _ := 0

variable [Fintype Deme] [DecidableEq Deme] [Fintype Locus] [DecidableEq Locus]
  [∀ ℓ, Fintype (Allele ℓ)] [∀ ℓ, DecidableEq (Allele ℓ)]

noncomputable section

/-! ## The selection generator -/

/-- A haplotype satisfies the one-locus carrier of allele `b` exactly when it carries `b`. -/
theorem satisfies_singleLocusType_iff (i : Deme) (ℓ₀ : Locus) (b : Allele ℓ₀)
    (hap : FullHaplotype Locus Allele) :
    Satisfies (singleLocusType i ℓ₀ b).allele hap ↔ hap ℓ₀ = b := by
  constructor
  · intro h
    rcases h ℓ₀ with h0 | h0
    · simp [singleLocusType] at h0
    · simpa [singleLocusType] using h0.symm
  · intro h ℓ
    by_cases hℓ : ℓ = ℓ₀
    · subst hℓ
      exact Or.inr (by simp [singleLocusType, h])
    · exact Or.inl (by simp [singleLocusType, Function.update_of_ne hℓ])

/-- The mean fitness `s̄_i = Σ_b s_i(b) x_i[ℓ = b]` of deme `i`, as a frequency polynomial. -/
def meanFitnessPolynomial (model : SelectionModel Deme Locus Allele) (i : Deme) :
    FrequencyPolynomial Deme Locus Allele :=
  ∑ b, C (model.fitness i b) * marginalPolynomial (singleLocusType i model.locus b)

/-- At a frequency point the mean fitness polynomial of deme `i` is `Σ_h x_i[h] s_i(h_ℓ)`. -/
theorem eval_meanFitnessPolynomial (model : SelectionModel Deme Locus Allele)
    (x : FrequencyVariable Deme Locus Allele → ℝ) (i : Deme) :
    eval x (meanFitnessPolynomial model i)
      = ∑ hap, x (i, hap) * model.fitness i (hap model.locus) := by
  simp only [meanFitnessPolynomial, map_sum, map_mul, eval_C, marginalPolynomial,
    eval_assignmentPolynomial, Finset.mul_sum]
  rw [← Finset.sum_fiberwise Finset.univ (fun hap : FullHaplotype Locus Allele ↦ hap model.locus)
    (fun hap ↦ x (i, hap) * model.fitness i (hap model.locus))]
  refine Finset.sum_congr rfl fun b _ ↦ Finset.sum_congr
    (Finset.filter_congr fun hap _ ↦ satisfies_singleLocusType_iff i model.locus b hap)
    fun hap hhap ↦ ?_
  rw [(Finset.mem_filter.mp hhap).2]
  exact mul_comm _ _

/-- **The mean fitness polynomial is the corpus mean fitness** of the frequencies of the deme. -/
theorem eval_meanFitnessPolynomial_eq_meanFitness (model : SelectionModel Deme Locus Allele)
    (x : FrequencyVariable Deme Locus Allele → ℝ) (i : Deme) :
    eval x (meanFitnessPolynomial model i)
      = Descent.Pangenome.AncestralLocality.meanFitness
          (fun hap : FullHaplotype Locus Allele ↦ model.fitness i (hap model.locus))
          (fun hap ↦ x (i, hap)) :=
  eval_meanFitnessPolynomial model x i

/-- The selective drift `x_i[h] (s_i(h_ℓ) - s̄_i)` of one haplotype frequency. -/
def selectiveDrift (model : SelectionModel Deme Locus Allele)
    (coordinate : FrequencyVariable Deme Locus Allele) : FrequencyPolynomial Deme Locus Allele :=
  X coordinate * (C (model.fitness coordinate.1 (coordinate.2 model.locus))
    - meanFitnessPolynomial model coordinate.1)

/-- At a frequency point the selective drift is the classical drift `p_h (s(h) - s̄(p))` of
`AncestralLocality.selectionGenerator_eq_drift`, read in the deme of the coordinate. -/
theorem eval_selectiveDrift (model : SelectionModel Deme Locus Allele)
    (x : FrequencyVariable Deme Locus Allele → ℝ) (i : Deme) (hap : FullHaplotype Locus Allele) :
    eval x (selectiveDrift model (i, hap))
      = x (i, hap) * (model.fitness i (hap model.locus)
        - Descent.Pangenome.AncestralLocality.meanFitness
          (fun g : FullHaplotype Locus Allele ↦ model.fitness i (g model.locus))
          (fun g ↦ x (i, g))) := by
  rw [← eval_meanFitnessPolynomial_eq_meanFitness]
  simp only [selectiveDrift, map_mul, map_sub, eval_X, eval_C]

/-- **The selection generator**: the derivation of frequency polynomials along the selective
drift of every haplotype frequency. -/
def selectionGenerator (model : SelectionModel Deme Locus Allele)
    (f : FrequencyPolynomial Deme Locus Allele) : FrequencyPolynomial Deme Locus Allele :=
  ∑ coordinate, selectiveDrift model coordinate * pderiv coordinate f

/-- **The forward generator with selection**: the neutral generator of NOTE1 §4.2 plus the
selection generator. -/
def selectedGenerator (rates : NeutralRates Deme Locus Allele)
    (model : SelectionModel Deme Locus Allele) (f : FrequencyPolynomial Deme Locus Allele) :
    FrequencyPolynomial Deme Locus Allele :=
  neutralGenerator rates f + selectionGenerator model f

/-- Without fitness differences the selection generator vanishes. -/
theorem selectionGenerator_neutral (ℓ : Locus) (f : FrequencyPolynomial Deme Locus Allele) :
    selectionGenerator (SelectionModel.neutral ℓ) f = 0 := by
  simp [selectionGenerator, selectiveDrift, meanFitnessPolynomial, SelectionModel.neutral]

/-- **Without fitness differences the generator with selection is the neutral generator.** -/
theorem selectedGenerator_neutral (rates : NeutralRates Deme Locus Allele) (ℓ : Locus)
    (f : FrequencyPolynomial Deme Locus Allele) :
    selectedGenerator rates (SelectionModel.neutral ℓ) f = neutralGenerator rates f := by
  rw [selectedGenerator, selectionGenerator_neutral, add_zero]

/-- The selection generator is a derivation: `S(f h) = f S(h) + h S(f)`. -/
theorem selectionGenerator_mul (model : SelectionModel Deme Locus Allele)
    (f h : FrequencyPolynomial Deme Locus Allele) :
    selectionGenerator model (f * h)
      = f * selectionGenerator model h + h * selectionGenerator model f := by
  unfold selectionGenerator
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun coordinate _ ↦ ?_
  rw [pderiv_mul]
  ring

/-- The selection generator annihilates constants. -/
theorem selectionGenerator_one (model : SelectionModel Deme Locus Allele) :
    selectionGenerator model 1 = 0 := by
  simp [selectionGenerator]

/-- **The selection generator of a marginal frequency** is the sum of the selective drifts of the
haplotypes it counts. -/
theorem selectionGenerator_assignmentPolynomial (model : SelectionModel Deme Locus Allele)
    (i : Deme) (assignment : ∀ ℓ, Option (Allele ℓ)) :
    selectionGenerator model (assignmentPolynomial i assignment)
      = ∑ hap ∈ Finset.univ.filter (Satisfies assignment), selectiveDrift model (i, hap) := by
  unfold selectionGenerator
  rw [Fintype.sum_prod_type, Finset.sum_comm, Finset.sum_filter]
  refine Finset.sum_congr rfl fun hap _ ↦ ?_
  by_cases hsat : Satisfies assignment hap
  · simp [pderiv_assignmentPolynomial, hsat, mul_ite]
  · simp [pderiv_assignmentPolynomial, hsat, mul_ite]

/-- **The selection generator on one carrier**: at every frequency point, the frequencies of the
haplotypes the carrier counts, weighted by their fitness deviation from the deme mean. -/
theorem eval_selectionGenerator_marginal (model : SelectionModel Deme Locus Allele)
    (x : FrequencyVariable Deme Locus Allele → ℝ) (τ : PartialType Deme Locus Allele) :
    eval x (selectionGenerator model (marginalPolynomial τ))
      = ∑ hap ∈ Finset.univ.filter (Satisfies τ.allele), x (τ.deme, hap)
          * (model.fitness τ.deme (hap model.locus)
            - eval x (meanFitnessPolynomial model τ.deme)) := by
  rw [marginalPolynomial, selectionGenerator_assignmentPolynomial, map_sum]
  simp only [selectiveDrift, map_mul, map_sub, eval_X, eval_C]

/-- **The selection generator on a configuration moment** acts carrier by carrier. -/
theorem eval_selectionGenerator_momentPolynomial (model : SelectionModel Deme Locus Allele)
    (x : FrequencyVariable Deme Locus Allele → ℝ) (ξ : Multiset (PartialType Deme Locus Allele)) :
    eval x (selectionGenerator model (momentPolynomial ξ))
      = (ξ.map fun τ ↦ eval x (selectionGenerator model (marginalPolynomial τ))
          * eval x (momentPolynomial (ξ.erase τ))).sum := by
  rw [leibniz_momentPolynomial (selectionGenerator model) (selectionGenerator_mul model)
    (selectionGenerator_one model), map_multiset_sum, Multiset.map_map]
  simp only [Function.comp_def, map_mul]

/-! ## The selection generator at a state -/

/-- **At a state the mean fitness lies in `[0, σ]`** when every fitness does: the frequencies of
the deme are nonnegative and sum to one. -/
theorem eval_meanFitnessPolynomial_mem (model : SelectionModel Deme Locus Allele) {σ : ℝ}
    (hfit : ∀ i b, 0 ≤ model.fitness i b ∧ model.fitness i b ≤ σ)
    {x : FrequencyVariable Deme Locus Allele → ℝ} (hx0 : ∀ c, 0 ≤ x c)
    (hx1 : ∀ i, ∑ hap, x (i, hap) = 1) (i : Deme) :
    0 ≤ eval x (meanFitnessPolynomial model i) ∧ eval x (meanFitnessPolynomial model i) ≤ σ := by
  rw [eval_meanFitnessPolynomial]
  refine ⟨Finset.sum_nonneg fun hap _ ↦ mul_nonneg (hx0 _) (hfit _ _).1, ?_⟩
  calc ∑ hap, x (i, hap) * model.fitness i (hap model.locus) ≤ ∑ hap, x (i, hap) * σ :=
        Finset.sum_le_sum fun hap _ ↦ mul_le_mul_of_nonneg_left (hfit _ _).2 (hx0 _)
    _ = σ := by rw [← Finset.sum_mul, hx1, one_mul]

/-- **A carrier moves by at most `σ` times its frequency** under selection with fitnesses in
`[0, σ]`, at every state. -/
theorem abs_eval_selectionGenerator_marginal_le (model : SelectionModel Deme Locus Allele)
    {σ : ℝ} (hfit : ∀ i b, 0 ≤ model.fitness i b ∧ model.fitness i b ≤ σ)
    {x : FrequencyVariable Deme Locus Allele → ℝ} (hx0 : ∀ c, 0 ≤ x c)
    (hx1 : ∀ i, ∑ hap, x (i, hap) = 1) (τ : PartialType Deme Locus Allele) :
    |eval x (selectionGenerator model (marginalPolynomial τ))|
      ≤ σ * eval x (marginalPolynomial τ) := by
  obtain ⟨hmean0, hmeanσ⟩ := eval_meanFitnessPolynomial_mem model hfit hx0 hx1 τ.deme
  rw [eval_selectionGenerator_marginal, marginalPolynomial, eval_assignmentPolynomial,
    Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun hap _ ↦ ?_)
  have hdev : |model.fitness τ.deme (hap model.locus)
      - eval x (meanFitnessPolynomial model τ.deme)| ≤ σ :=
    abs_sub_le_iff.mpr ⟨by linarith [(hfit τ.deme (hap model.locus)).2],
      by linarith [(hfit τ.deme (hap model.locus)).1]⟩
  rw [abs_mul, abs_of_nonneg (hx0 _)]
  exact (mul_le_mul_of_nonneg_left hdev (hx0 _)).trans_eq (mul_comm _ _)

/-- **A configuration with `n` carriers moves by at most `n σ` times its moment** under selection
with fitnesses in `[0, σ]`, at every state. -/
theorem abs_eval_selectionGenerator_momentPolynomial_le (model : SelectionModel Deme Locus Allele)
    {σ : ℝ} (hfit : ∀ i b, 0 ≤ model.fitness i b ∧ model.fitness i b ≤ σ)
    {x : FrequencyVariable Deme Locus Allele → ℝ} (hx0 : ∀ c, 0 ≤ x c)
    (hx1 : ∀ i, ∑ hap, x (i, hap) = 1) (ξ : Multiset (PartialType Deme Locus Allele)) :
    |eval x (selectionGenerator model (momentPolynomial ξ))|
      ≤ Multiset.card ξ * σ * eval x (momentPolynomial ξ) := by
  have hmarginal : ∀ τ : PartialType Deme Locus Allele, 0 ≤ eval x (marginalPolynomial τ) := by
    intro τ
    rw [marginalPolynomial, eval_assignmentPolynomial]
    exact Finset.sum_nonneg fun hap _ ↦ hx0 _
  have hmoment : ∀ ζ : Multiset (PartialType Deme Locus Allele),
      0 ≤ eval x (momentPolynomial ζ) := by
    intro ζ
    induction ζ using Multiset.induction_on with
    | empty => simp [momentPolynomial]
    | cons τ ζ ih =>
      rw [momentPolynomial_cons, map_mul]
      exact mul_nonneg (hmarginal τ) ih
  rw [eval_selectionGenerator_momentPolynomial]
  refine Multiset.abs_sum_le_sum_abs.trans ?_
  rw [Multiset.map_map]
  refine le_trans (Multiset.sum_map_le_sum_map _ (fun _ ↦ σ * eval x (momentPolynomial ξ))
    fun τ hτ ↦ ?_) (le_of_eq ?_)
  · have hsplit : eval x (momentPolynomial ξ)
        = eval x (marginalPolynomial τ) * eval x (momentPolynomial (ξ.erase τ)) := by
      rw [← map_mul, ← momentPolynomial_cons, Multiset.cons_erase hτ]
    rw [Function.comp_apply, abs_mul, abs_of_nonneg (hmoment _), hsplit, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right
      (abs_eval_selectionGenerator_marginal_le model hfit hx0 hx1 τ) (hmoment _)
  · rw [Multiset.map_const', Multiset.sum_replicate, nsmul_eq_mul, mul_assoc]

end

end Descent.Portability.SelectionHistoryMoments
