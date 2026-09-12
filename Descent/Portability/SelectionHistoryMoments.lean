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

Branching. On one carrier the selection generator is `Σ_b s(b) (x[τ ∧ b] - x[τ] x[ℓ = b])`
(`eval_selectionGenerator_marginal_branching`): at rate `s(b)` the carrier merged with allele `b`
at the selected locus is gained (the cemetery when the carrier retains another allele there), and
the configuration with a new lineage carrying `b` is lost. So on a configuration the selection
generator is a signed sum over `selectionTerms` (`selectionGenerator_configurationMoment`), every
term respects the budget with one more copy at the selected locus (`bumpCapacity`,
`selectionTerms_withinBudget`), and the selection matrix `B_n` from budget `n` to that budget
carries it on moment vectors (`selectionMatrix_mulVec_configurationMoment`,
`expectedSelection_eq_mulVec`). The forward moment equation with selection is
`v_n' = Q_n v_n + B_n v_{n + 1_ℓ}` (`expectedSelectedGenerator_eq`), which closes on no budget.

One epoch. The propagator from the current time to the end of an epoch obeys a product rule
(`hasDerivWithinAt_propagator_mulVec`), so along the forward equation `e^{(d - t)Q} v(t)` moves
only by the propagated selection term. The propagator is substochastic
(`norm_mulVec_le_of_substochastic`) and the expected selection term of a budget of total size
`B = Σ_ℓ n_ℓ` is at most `B σ` (`abs_expectedSelection_le`), so selection moves the expected
moments of an epoch of length `d` from the neutral propagator by at most `B σ d`
(`norm_expectedMomentVector_sub_propagator_le`).

Scope. Selection is haploid and at one locus; dominance, epistasis and fitness read at several
loci are not covered. The forward moment equation with selection is a hypothesis on the
expectation family: the selected diffusion itself is not constructed.

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

/-! ## Selection as branching on configurations -/

/-- **Selection on one carrier as branching.** At every frequency point the selection generator
of `x[τ]` is `Σ_b s(b) (x[τ ∧ b] - x[τ] x[ℓ = b])` in the deme of `τ`, where `x[τ ∧ b]` is the
merged carrier when `τ` is compatible with allele `b` at the selected locus and zero otherwise. -/
theorem eval_selectionGenerator_marginal_branching (model : SelectionModel Deme Locus Allele)
    (x : FrequencyVariable Deme Locus Allele → ℝ) (τ : PartialType Deme Locus Allele) :
    eval x (selectionGenerator model (marginalPolynomial τ))
      = ∑ b, model.fitness τ.deme b
          * ((if Compatible τ (singleLocusType τ.deme model.locus b) then
                eval x (marginalPolynomial (coalesce τ (singleLocusType τ.deme model.locus b)))
              else 0)
            - eval x (marginalPolynomial τ)
              * eval x (marginalPolynomial (singleLocusType τ.deme model.locus b))) := by
  have hfirst : ∑ hap ∈ Finset.univ.filter (Satisfies τ.allele),
        x (τ.deme, hap) * model.fitness τ.deme (hap model.locus)
      = ∑ b, model.fitness τ.deme b
          * (if Compatible τ (singleLocusType τ.deme model.locus b) then
              eval x (marginalPolynomial (coalesce τ (singleLocusType τ.deme model.locus b)))
            else 0) := by
    rw [← Finset.sum_fiberwise (Finset.univ.filter (Satisfies τ.allele))
      (fun hap : FullHaplotype Locus Allele ↦ hap model.locus)]
    refine Finset.sum_congr rfl fun b _ ↦ ?_
    rw [← jointFrequency_eq_coalesce, Finset.mul_sum, Finset.filter_filter]
    refine Finset.sum_congr (Finset.filter_congr fun hap _ ↦ and_congr_right fun _ ↦
      (satisfies_singleLocusType_iff τ.deme model.locus b hap).symm) fun hap hhap ↦ ?_
    rw [(satisfies_singleLocusType_iff τ.deme model.locus b hap).mp
      (Finset.mem_filter.mp hhap).2.2]
    exact mul_comm _ _
  have hmean : eval x (meanFitnessPolynomial model τ.deme)
      = ∑ b, model.fitness τ.deme b
          * eval x (marginalPolynomial (singleLocusType τ.deme model.locus b)) := by
    simp only [meanFitnessPolynomial, map_sum, map_mul, eval_C]
  have hcarrier : ∑ hap ∈ Finset.univ.filter (Satisfies τ.allele), x (τ.deme, hap)
      = eval x (marginalPolynomial τ) := by
    rw [marginalPolynomial, eval_assignmentPolynomial]
  rw [eval_selectionGenerator_marginal]
  simp only [mul_sub, Finset.sum_sub_distrib]
  rw [hfirst, sub_right_inj, ← Finset.sum_mul, hcarrier, hmean, Finset.mul_sum]
  exact Finset.sum_congr rfl fun b _ ↦ by ring

/-- **The selection terms of a configuration.** For every carrier `τ` and every allele `b` at the
selected locus, at rate `s_{τ.deme}(b)`, the configuration in which `τ` is merged with the
one-locus carrier of `b` is gained (the cemetery when `τ` retains another allele there), and the
configuration with a new lineage carrying `b` beside every carrier is lost. -/
def selectionTerms (model : SelectionModel Deme Locus Allele)
    (ξ : Multiset (PartialType Deme Locus Allele)) :
    Multiset (ℝ × Option (Multiset (PartialType Deme Locus Allele))
      × Multiset (PartialType Deme Locus Allele)) :=
  ξ.bind fun τ ↦ Finset.univ.val.map fun b ↦
    (model.fitness τ.deme b,
      if Compatible τ (singleLocusType τ.deme model.locus b) then
        some (coalesce τ (singleLocusType τ.deme model.locus b) ::ₘ ξ.erase τ)
      else none,
      singleLocusType τ.deme model.locus b ::ₘ ξ)

/-- **The moment equation with selection on configurations.** At the frequency point of per-deme
haplotype laws, the selection generator of `H_ξ` is the sum over the selection terms of the rate
times the moment of the gained configuration minus the moment of the lost one, with `H_† = 0`. -/
theorem selectionGenerator_configurationMoment (model : SelectionModel Deme Locus Allele)
    (law : Deme → FiniteReportLaw (FullHaplotype Locus Allele))
    (ξ : Multiset (PartialType Deme Locus Allele)) :
    eval (lawPoint law) (selectionGenerator model (momentPolynomial ξ))
      = ((selectionTerms model ξ).map fun term ↦ term.1
          * (term.2.1.elim 0 (configurationMoment law)
            - configurationMoment law term.2.2)).sum := by
  rw [eval_selectionGenerator_momentPolynomial, selectionTerms, Multiset.map_bind,
    Multiset.sum_bind]
  refine congrArg Multiset.sum (Multiset.map_congr rfl fun τ hτ ↦ ?_)
  have hξ : configurationMoment law ξ
      = marginalFrequency law τ * configurationMoment law (ξ.erase τ) := by
    rw [← configurationMoment_cons, Multiset.cons_erase hτ]
  rw [eval_selectionGenerator_marginal_branching, eval_momentPolynomial, Finset.sum_mul,
    Finset.sum_eq_multiset_sum, Multiset.map_map]
  refine congrArg Multiset.sum (Multiset.map_congr rfl fun b _ ↦ ?_)
  simp only [Function.comp_apply, eval_marginalPolynomial]
  split_ifs <;> simp only [Option.elim, configurationMoment_cons, hξ] <;> ring

/-- The budget with one more copy at the selected locus. -/
def bumpCapacity (model : SelectionModel Deme Locus Allele) (capacity : Locus → ℕ) :
    Locus → ℕ :=
  Function.update capacity model.locus (capacity model.locus + 1)

/-- **Selection raises the budget by one copy at the selected locus.** From a budget-respecting
configuration, every gained and every lost configuration of the selection terms respects the
budget with one more copy at the selected locus. -/
theorem selectionTerms_withinBudget (model : SelectionModel Deme Locus Allele)
    (capacity : Locus → ℕ) (ξ : Multiset (PartialType Deme Locus Allele))
    (hξ : WithinBudget capacity ξ) :
    ∀ term ∈ selectionTerms model ξ,
      (∀ η, term.2.1 = some η → WithinBudget (bumpCapacity model capacity) η)
        ∧ WithinBudget (bumpCapacity model capacity) term.2.2 := by
  intro term hterm
  obtain ⟨τ, hτ, hτterm⟩ := Multiset.mem_bind.mp hterm
  obtain ⟨b, _, rfl⟩ := Multiset.mem_map.mp hτterm
  have hlost : WithinBudget (bumpCapacity model capacity)
      (singleLocusType τ.deme model.locus b ::ₘ ξ) := by
    intro ℓ
    rw [load_cons]
    by_cases hℓ : ℓ = model.locus
    · subst hℓ
      simpa [singleLocusType, bumpCapacity] using Nat.add_le_add_right (hξ model.locus) 1
    · simpa [singleLocusType, bumpCapacity, Function.update_of_ne hℓ] using hξ ℓ
  refine ⟨fun η hη ↦ ?_, hlost⟩
  dsimp only at hη
  split_ifs at hη with hcompat
  · obtain rfl := Option.some.inj hη
    have hbudget : WithinBudget (bumpCapacity model capacity)
        (τ ::ₘ singleLocusType τ.deme model.locus b ::ₘ ξ.erase τ) := by
      rw [Multiset.cons_swap, Multiset.cons_erase hτ]
      exact hlost
    exact withinBudget_coalesce _ τ _ _ hbudget
  · exact absurd hη (by simp)

/-- **The selection matrix**: from the budget-respecting configurations to those with one more
copy at the selected locus, the rates of the gained configurations minus those of the lost ones. -/
def selectionMatrix (model : SelectionModel Deme Locus Allele) (capacity : Locus → ℕ) :
    Matrix (BudgetConfiguration Deme Locus Allele capacity)
      (BudgetConfiguration Deme Locus Allele (bumpCapacity model capacity)) ℝ :=
  fun ξ η ↦ ((selectionTerms model ξ.1).map fun term ↦ term.1
    * ((if term.2.1 = some η.1 then 1 else 0) - if some term.2.2 = some η.1 then 1 else 0)).sum

/-- **The selection matrix acts through the selection terms**, with `w(†) = 0`. -/
theorem selectionMatrix_mulVec (model : SelectionModel Deme Locus Allele) (capacity : Locus → ℕ)
    (value : Multiset (PartialType Deme Locus Allele) → ℝ)
    (ξ : BudgetConfiguration Deme Locus Allele capacity) :
    (selectionMatrix model capacity).mulVec (fun η ↦ value η.1) ξ
      = ((selectionTerms model ξ.1).map fun term ↦
          term.1 * (term.2.1.elim 0 value - value term.2.2)).sum := by
  have hbudget := selectionTerms_withinBudget model capacity ξ.1 ξ.2
  simp only [Matrix.mulVec, dotProduct, selectionMatrix, ← Multiset.sum_map_mul_right]
  rw [Finset.sum_eq_multiset_sum, Multiset.sum_map_sum_map]
  refine congrArg Multiset.sum (Multiset.map_congr rfl fun term hterm ↦ ?_)
  rw [← Finset.sum_eq_multiset_sum]
  have hgain := sum_target_indicator (bumpCapacity model capacity) term.2.1
    (hbudget term hterm).1 value
  have hloss := sum_target_indicator (bumpCapacity model capacity) (some term.2.2)
    (fun η hη ↦ Option.some.inj hη ▸ (hbudget term hterm).2) value
  simp only [mul_sub, sub_mul, Finset.sum_sub_distrib, mul_assoc, ite_mul, one_mul, zero_mul,
    ← Finset.mul_sum, hgain, hloss, Option.elim]

/-- **The selection matrix on moment vectors**: applied to the configuration moments of per-deme
haplotype laws with one more copy at the selected locus, it is the selection generator of the
moment polynomial evaluated at those laws. -/
theorem selectionMatrix_mulVec_configurationMoment (model : SelectionModel Deme Locus Allele)
    (capacity : Locus → ℕ) (law : Deme → FiniteReportLaw (FullHaplotype Locus Allele))
    (ξ : BudgetConfiguration Deme Locus Allele capacity) :
    (selectionMatrix model capacity).mulVec (fun η ↦ configurationMoment law η.1) ξ
      = eval (lawPoint law) (selectionGenerator model (momentPolynomial ξ.1)) := by
  rw [selectionMatrix_mulVec, selectionGenerator_configurationMoment]

/-- The expected selection term of every budget-respecting configuration under an expectation
functional over per-deme haplotype laws. -/
def expectedSelection (model : SelectionModel Deme Locus Allele) (capacity : Locus → ℕ)
    (expectation : ExpFunctional (Deme → FiniteReportLaw (FullHaplotype Locus Allele))) :
    BudgetConfiguration Deme Locus Allele capacity → ℝ :=
  fun ξ ↦ expectation fun law ↦
    eval (lawPoint law) (selectionGenerator model (momentPolynomial ξ.1))

/-- **The expected selection term is the selection matrix on the expected moments** with one more
copy at the selected locus. -/
theorem expectedSelection_eq_mulVec (model : SelectionModel Deme Locus Allele)
    (capacity : Locus → ℕ)
    (expectation : ExpFunctional (Deme → FiniteReportLaw (FullHaplotype Locus Allele))) :
    expectedSelection model capacity expectation
      = (selectionMatrix model capacity).mulVec
          (fun η ↦ expectation fun law ↦ configurationMoment law η.1) := by
  funext ξ
  have hpoint : (fun law ↦ eval (lawPoint law) (selectionGenerator model (momentPolynomial ξ.1)))
      = ∑ η, selectionMatrix model capacity ξ η • fun law ↦ configurationMoment law η.1 := by
    funext law
    rw [← selectionMatrix_mulVec_configurationMoment model capacity law ξ]
    simp [Matrix.mulVec, dotProduct, Finset.sum_apply]
  show (expectation fun law ↦
      eval (lawPoint law) (selectionGenerator model (momentPolynomial ξ.1))) = _
  rw [hpoint, ExpFunctional.eval_sum]
  simp only [ExpFunctional.smul_eval, Matrix.mulVec, dotProduct]

/-- **The forward moment equation with selection, in matrix form.** Under an expectation
functional, the expected generator with selection of a budget-respecting configuration moment is
the neutral dual generator on the expected moments plus the expected selection term. -/
theorem expectedSelectedGenerator_eq (rates : NeutralRates Deme Locus Allele)
    (model : SelectionModel Deme Locus Allele) (capacity : Locus → ℕ)
    (expectationAt : ℝ → ExpFunctional (Deme → FiniteReportLaw (FullHaplotype Locus Allele)))
    (s : ℝ) (ξ : BudgetConfiguration Deme Locus Allele capacity) :
    (expectationAt s fun law ↦
        eval (lawPoint law) (selectedGenerator rates model (momentPolynomial ξ.1)))
      = (dualGenerator rates capacity).mulVec (expectedMomentVector capacity expectationAt s) ξ
        + expectedSelection model capacity (expectationAt s) ξ := by
  have hsplit : (fun law : Deme → FiniteReportLaw (FullHaplotype Locus Allele) ↦
        eval (lawPoint law) (selectedGenerator rates model (momentPolynomial ξ.1)))
      = (fun law ↦ eval (lawPoint law) (neutralGenerator rates (momentPolynomial ξ.1)))
        + fun law ↦ eval (lawPoint law) (selectionGenerator model (momentPolynomial ξ.1)) := by
    funext law
    simp only [selectedGenerator, map_add, Pi.add_apply]
  rw [hsplit, (expectationAt s).add_eval,
    expectedGenerator_eq_mulVec rates capacity expectationAt s ξ]
  rfl

/-! ## One epoch with selection -/

/-- **A substochastic matrix does not raise the sup norm.** -/
theorem norm_mulVec_le_of_substochastic {ι : Type*} [Fintype ι] {P : Matrix ι ι ℝ}
    (hP : SubstochasticMatrix P) (w : ι → ℝ) : ‖P *ᵥ w‖ ≤ ‖w‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg w)).mpr fun row ↦ ?_
  have hentry : ∀ column, |P row column * w column| ≤ P row column * ‖w‖ := fun column ↦ by
    rw [abs_mul, abs_of_nonneg (hP.entry_nonneg row column)]
    exact mul_le_mul_of_nonneg_left
      (by simpa only [Real.norm_eq_abs] using norm_le_pi_norm w column)
      (hP.entry_nonneg row column)
  rw [Real.norm_eq_abs]
  calc |(P *ᵥ w) row| = |∑ column, P row column * w column| := rfl
    _ ≤ ∑ column, P row column * ‖w‖ :=
        (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun column _ ↦ hentry column)
    _ = (∑ column, P row column) * ‖w‖ := by rw [Finset.sum_mul]
    _ ≤ ‖w‖ := mul_le_of_le_one_left (norm_nonneg w) (hP.rowSum_le_one row)

section Propagator

open scoped Matrix.Norms.Operator

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A matrix exponential commutes with its generator. -/
theorem matrixExponential_mul_comm (A : Matrix ι ι ℝ) (t : ℝ) :
    matrixExponential A t * A = A * matrixExponential A t := by
  rw [matrixExponential_eq_normedSpace_exp]
  exact (((Commute.refl A).smul_left t).exp_left ℝ).eq

/-- The columns of the propagator from time `u` to `finish` move with `u` along minus the
generator. -/
theorem hasDerivAt_propagatorColumn (A : Matrix ι ι ℝ) (finish t : ℝ) (η : ι) :
    HasDerivAt (fun u ↦ matrixExponential A (finish - u) *ᵥ fun j ↦ if η = j then 1 else 0)
      ((-1 : ℝ) • (A *ᵥ (matrixExponential A (finish - t) *ᵥ fun j ↦ if η = j then 1 else 0)))
      t :=
  (hasDerivAt_matrixExponential_mulVec A _ (finish - t)).scomp t
    ((hasDerivAt_id t).const_sub finish)

/-- The propagator from time `u` to `finish` applied to a vector, column by column. -/
theorem propagator_mulVec_eq_sum (A : Matrix ι ι ℝ) (finish u : ℝ) (w : ι → ℝ) :
    matrixExponential A (finish - u) *ᵥ w
      = ∑ η, w η • (matrixExponential A (finish - u) *ᵥ fun j ↦ if η = j then 1 else 0) := by
  conv_lhs => rw [pi_eq_sum_univ w]
  rw [Matrix.mulVec_sum]
  simp only [Matrix.mulVec_smul]

/-- **The product rule for the propagator to the end of an epoch.** If a vector has right
derivative `v'`, the propagator from the current time to `finish` applied to it has right
derivative `e^{(finish - t)A} v' - A e^{(finish - t)A} v(t)`. -/
theorem hasDerivWithinAt_propagator_mulVec (A : Matrix ι ι ℝ) (finish : ℝ) {v : ℝ → ι → ℝ}
    {v' : ι → ℝ} {s : Set ℝ} {t : ℝ} (hv : HasDerivWithinAt v v' s t) :
    HasDerivWithinAt (fun u ↦ matrixExponential A (finish - u) *ᵥ v u)
      (matrixExponential A (finish - t) *ᵥ v'
        - A *ᵥ (matrixExponential A (finish - t) *ᵥ v t)) s t := by
  have hsum := HasDerivWithinAt.fun_sum (u := Finset.univ) fun η (_ : η ∈ Finset.univ) ↦
    (hasDerivWithinAt_pi.mp hv η).smul (hasDerivAt_propagatorColumn A finish t η).hasDerivWithinAt
  have hfun : (fun u ↦ matrixExponential A (finish - u) *ᵥ v u)
      = fun u ↦ ∑ η, v u η
          • (matrixExponential A (finish - u) *ᵥ fun j ↦ if η = j then 1 else 0) :=
    funext fun u ↦ propagator_mulVec_eq_sum A finish u (v u)
  rw [hfun, propagator_mulVec_eq_sum A finish t v', propagator_mulVec_eq_sum A finish t (v t),
    Matrix.mulVec_sum]
  refine hsum.congr_deriv ?_
  simp only [Matrix.mulVec_smul, Finset.sum_add_distrib, smul_smul, mul_neg, mul_one, neg_smul,
    Finset.sum_neg_distrib]
  abel

/-- The propagator to the end of an epoch applied to a continuous vector is continuous. -/
theorem continuousOn_propagator_mulVec (A : Matrix ι ι ℝ) (finish : ℝ) {v : ℝ → ι → ℝ}
    {S : Set ℝ} (hv : ContinuousOn v S) :
    ContinuousOn (fun u ↦ matrixExponential A (finish - u) *ᵥ v u) S := by
  rw [show (fun u ↦ matrixExponential A (finish - u) *ᵥ v u)
      = fun u ↦ ∑ η, v u η
          • (matrixExponential A (finish - u) *ᵥ fun j ↦ if η = j then 1 else 0) from
    funext fun u ↦ propagator_mulVec_eq_sum A finish u (v u)]
  exact continuousOn_finset_sum _ fun η _ ↦ (continuousOn_pi.mp hv η).smul
    (continuous_iff_continuousAt.mpr fun u ↦
      (hasDerivAt_propagatorColumn A finish u η).continuousAt).continuousOn

end Propagator

/-- **The expected selection term of a configuration is at most `B σ`** under every expectation
functional over per-deme haplotype laws, for fitnesses in `[0, σ]` and a budget of total size
`B = Σ_ℓ n_ℓ`: a budget-respecting configuration has at most `B` carriers. -/
theorem abs_expectedSelection_le (model : SelectionModel Deme Locus Allele) {σ : ℝ} (hσ : 0 ≤ σ)
    (hfit : ∀ i b, 0 ≤ model.fitness i b ∧ model.fitness i b ≤ σ) (capacity : Locus → ℕ)
    (expectation : ExpFunctional (Deme → FiniteReportLaw (FullHaplotype Locus Allele)))
    (ξ : BudgetConfiguration Deme Locus Allele capacity) :
    |expectedSelection model capacity expectation ξ| ≤ (∑ ℓ, capacity ℓ : ℕ) * σ := by
  have hpoint : ∀ law : Deme → FiniteReportLaw (FullHaplotype Locus Allele),
      |eval (lawPoint law) (selectionGenerator model (momentPolynomial ξ.1))|
        ≤ (∑ ℓ, capacity ℓ : ℕ) * σ := by
    intro law
    have hmoment := abs_eval_selectionGenerator_momentPolynomial_le model hfit
      (x := lawPoint law) (fun c ↦ (law c.1).mass_nonneg c.2) (fun i ↦ (law i).mass_sum) ξ.1
    rw [eval_momentPolynomial] at hmoment
    have hcard : (Multiset.card ξ.1 : ℝ) ≤ (∑ ℓ, capacity ℓ : ℕ) := by
      exact_mod_cast card_le_capacity_total capacity ξ.1 ξ.2
    calc _ ≤ _ := hmoment
      _ ≤ (Multiset.card ξ.1 : ℝ) * σ * 1 :=
          mul_le_mul_of_nonneg_left (configurationMoment_le_one law ξ.1)
            (mul_nonneg (Nat.cast_nonneg _) hσ)
      _ ≤ (∑ ℓ, capacity ℓ : ℕ) * σ := by
          rw [mul_one]
          exact mul_le_mul_of_nonneg_right hcard hσ
  refine abs_le.mpr ⟨?_, ?_⟩
  · have h := expectation.eval_mono fun law ↦ (abs_le.mp (hpoint law)).1
    simpa only [ExpFunctional.eval_const] using h
  · have h := expectation.eval_mono fun law ↦ (abs_le.mp (hpoint law)).2
    simpa only [ExpFunctional.eval_const] using h

/-- **Selection moves the expected moments of one epoch by at most `B σ d`.** Suppose the expected
budget-respecting configuration moments of an expectation family are continuous on
`[start, finish]` and obey the forward moment equation with selection there, for fitnesses in
`[0, σ]`. Then the moments at `finish` differ from the neutral epoch propagator applied to the
moments at `start` by at most `B σ (finish - start)` in sup norm, with `B = Σ_ℓ n_ℓ`. -/
theorem norm_expectedMomentVector_sub_propagator_le (rates : NeutralRates Deme Locus Allele)
    (model : SelectionModel Deme Locus Allele) {σ : ℝ} (hσ : 0 ≤ σ)
    (hfit : ∀ i b, 0 ≤ model.fitness i b ∧ model.fitness i b ≤ σ) (capacity : Locus → ℕ)
    (expectationAt : ℝ → ExpFunctional (Deme → FiniteReportLaw (FullHaplotype Locus Allele)))
    {start finish : ℝ} (hduration : start ≤ finish)
    (hcont : ContinuousOn (expectedMomentVector capacity expectationAt) (Set.Icc start finish))
    (hforward : ∀ ξ : BudgetConfiguration Deme Locus Allele capacity,
      ∀ t ∈ Set.Ico start finish,
        HasDerivWithinAt (fun s ↦ expectedMomentVector capacity expectationAt s ξ)
          (expectationAt t fun law ↦
            eval (lawPoint law) (selectedGenerator rates model (momentPolynomial ξ.1)))
          (Set.Ici t) t) :
    ‖expectedMomentVector capacity expectationAt finish
        - matrixExponential (dualGenerator rates capacity) (finish - start)
          *ᵥ expectedMomentVector capacity expectationAt start‖
      ≤ (∑ ℓ, capacity ℓ : ℕ) * σ * (finish - start) := by
  have hψ : ∀ t ∈ Set.Ico start finish, HasDerivWithinAt
      (fun u ↦ matrixExponential (dualGenerator rates capacity) (finish - u)
        *ᵥ expectedMomentVector capacity expectationAt u)
      (matrixExponential (dualGenerator rates capacity) (finish - t)
        *ᵥ expectedSelection model capacity (expectationAt t)) (Set.Ici t) t := by
    intro t ht
    have hv : HasDerivWithinAt (expectedMomentVector capacity expectationAt)
        (dualGenerator rates capacity *ᵥ expectedMomentVector capacity expectationAt t
          + expectedSelection model capacity (expectationAt t)) (Set.Ici t) t :=
      hasDerivWithinAt_pi.mpr fun ξ ↦ (hforward ξ t ht).congr_deriv
        (expectedSelectedGenerator_eq rates model capacity expectationAt t ξ)
    refine (hasDerivWithinAt_propagator_mulVec _ finish hv).congr_deriv ?_
    rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, matrixExponential_mul_comm]
    abel
  have hbound : ∀ t ∈ Set.Ico start finish,
      ‖matrixExponential (dualGenerator rates capacity) (finish - t)
        *ᵥ expectedSelection model capacity (expectationAt t)‖ ≤ (∑ ℓ, capacity ℓ : ℕ) * σ := by
    intro t ht
    refine (norm_mulVec_le_of_substochastic
      (dualPropagator_substochastic rates capacity _ (sub_nonneg.mpr ht.2.le)) _).trans ?_
    refine (pi_norm_le_iff_of_nonneg (mul_nonneg (Nat.cast_nonneg _) hσ)).mpr fun ξ ↦ ?_
    rw [Real.norm_eq_abs]
    exact abs_expectedSelection_le model hσ hfit capacity (expectationAt t) ξ
  have h := norm_image_sub_le_of_norm_deriv_right_le_segment
    (continuousOn_propagator_mulVec _ finish hcont) hψ hbound finish ⟨hduration, le_rfl⟩
  simpa only [sub_self, matrixExponential_zero, Matrix.one_mulVec] using h

end

end Descent.Portability.SelectionHistoryMoments
