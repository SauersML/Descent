/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.SelectionMomentUniqueness
import Descent.Portability.SelectionHistoryFirstOrder

assert_below Descent.Decision Descent.Program

/-!
# Diploid viability selection with dominance along a history

Every selection module of the corpus is haploid: a haplotype carries a fitness of its own
(`SelectionHistoryMoments.SelectionModel`, `PolygenicSelectionHistory.additiveFitness`). This module
carries diploid viability selection at one locus, with arbitrary dominance, along histories of
epochs, splits and pulses.

The model. Deme `i` has a symmetric genotype fitness table `w_i(a, a')` at the selected locus
(`DiploidSelectionModel`, `DiploidSelectionModel.neutral`). The marginal fitness of allele `a` is
`ŵ_i(a) = Σ_{a'} w_i(a, a') x_i[ℓ = a']`, the mean fitness of its partner allele
(`partnerModel`, `marginalFitnessPolynomial`, `eval_marginalFitnessPolynomial`), and the mean
fitness is `w̄_i = Σ_a ŵ_i(a) x_i[ℓ = a]` (`diploidMeanFitnessPolynomial`). A haplotype frequency
drifts at `x_i[h] (ŵ_i(h_ℓ) - w̄_i)` (`diploidDrift`), and the diploid selection generator is the
derivation along that vector field (`diploidSelectionGenerator`, `diploidSelectedGenerator`).
Without fitness differences it vanishes (`diploidSelectionGenerator_neutral`).

Frozen marginal fitnesses. At every frequency point the diploid drift is the haploid drift of the
model whose allele `a` has fitness `ŵ_i(a)` read at that point (`frozenHaploidModel`,
`eval_diploidDrift`), so the diploid generator is the haploid generator of that model there
(`eval_diploidSelectionGenerator`). Genotype fitnesses in `[0, σ]` put the frozen fitnesses in
`[0, σ]` at a state (`frozenHaploidModel_fitness_mem`), so a configuration with `n` carriers moves
by at most `n σ` times its moment (`abs_eval_diploidSelectionGenerator_momentPolynomial_le`).

Two copies. On one carrier the diploid generator is
`Σ_{b, b'} w(b, b') (x[τ ∧ b] x[ℓ = b'] - x[τ] x[ℓ = b] x[ℓ = b'])`
(`eval_diploidSelectionGenerator_marginal_branching`). The gained configuration merges the carrier
with allele `b` and adds a lineage carrying `b'`; the lost one adds two lineages. The drift is
quadratic in the frequencies, so the forcing reads the budget with two more copies at the selected
locus, where haploid selection reads one.

The haploid case. With `w_i(a, a') = s_i(a) + s_i(a')` (`haploidDiploidModel`) the marginal fitness
is `s_i(a) + s̄_i` and the mean fitness `2 s̄_i` at a state, so the diploid drift and generator are
the haploid ones (`sum_eval_singleLocusType_eq_one`, `eval_diploidDrift_haploidDiploidModel`,
`eval_diploidSelectionGenerator_haploidDiploidModel`).

Zero order. The expected diploid selection term of a budget of total size `B` is at most `B σ`
(`abs_expectedDiploidSelection_le`), and the expected generator with diploid selection is the
neutral dual generator on the moments plus that term (`expectedDiploidSelectedGenerator_eq`). So an
epoch of length `d` moves the moments by at most `B σ d` from the neutral propagator
(`norm_expectedMomentVector_sub_propagator_le_diploid`). Along a history selected with diploid
fitness (`DiploidSelectedOnHistory`, `diploidSelectedOnHistory_nil`) the moments end within `B σ T`
of the neutral chronological propagation (`norm_diploidHistory_sub_propagator_le`). Where the target
denominator and the source numerator are at least `δ > 0` under the selected family and at the
neutral end moments, portability of expected accuracies moves by at most
`4 ‖a‖₁ ‖b‖₁ ‖c‖₁ ‖d‖₁ / δ⁴ · 4 |L| σ T` from the portability of the neutral end moments
(`abs_diploidPortability_sub_neutral_le`).

Scope. Selection is diploid viability selection at one locus, with one fitness table for the whole
history; epistasis and fitness read at several loci are not covered. The forward moment equation
with diploid selection is a hypothesis on the families. This is allowed only because the haploid
laws `EndToEndSelectionLaw.norm_selectedHistory_sub_propagator_le` and
`PolygenicSelectionHistory.norm_additiveHistory_sub_propagator_le` take the same hypothesis; the
selected diffusion is not constructed. The selection matrix to the budget with two more copies is
not written out, and no first-order law is stated.

## Empirical status

None. The bodies here are algebra and norm inequalities: derivatives of polynomials in supplied
frequencies, finite sums of supplied fitness tables and bounds along matrix exponentials, so no
measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.DiploidSelectionHistory

open MvPolynomial Descent.Coalescent Descent.Foundations PartialHaplotypeCarrier
  PartialHaplotypeDualGenerator PartialHaplotypeDualSemigroup SubstochasticGeneratorSemigroup
  PartialHaplotypePulseKernel NeutralPulseHistoryKernel ReplicaMetricInstances
  EndToEndPortabilityLaw SelectionHistoryMoments EndToEndSelectionLaw
open scoped Matrix NNReal

variable {Deme Locus : Type*} {Allele : Locus → Type*}

/-- **Diploid viability selection at one locus.** An individual of deme `i` whose two haplotypes
carry alleles `a` and `a'` at the selected locus has fitness `fitness i a a'`; the table is
symmetric because a genotype is unordered, and it may differ between demes. -/
structure DiploidSelectionModel (Deme Locus : Type*) (Allele : Locus → Type*) where
  /-- The selected locus. -/
  locus : Locus
  /-- The fitness of every genotype at the selected locus in every deme. -/
  fitness : Deme → Allele locus → Allele locus → ℝ
  /-- A genotype is unordered. -/
  fitness_symm : ∀ i a a', fitness i a a' = fitness i a' a

/-- The neutral table at a locus: every genotype has fitness zero. -/
def DiploidSelectionModel.neutral (ℓ : Locus) : DiploidSelectionModel Deme Locus Allele where
  locus := ℓ
  fitness _ _ _ := 0
  fitness_symm _ _ _ := rfl

/-- The haploid model that reads the partner of a fixed allele `a`: a haplotype carrying `a'` at
the selected locus has fitness `w_i(a, a')`. -/
abbrev partnerModel (model : DiploidSelectionModel Deme Locus Allele) (a : Allele model.locus) :
    SelectionModel Deme Locus Allele where
  locus := model.locus
  fitness i a' := model.fitness i a a'

/-- **Haploid fitness as a genotype table**: the genotype `a a'` has fitness `s_i(a) + s_i(a')`. -/
abbrev haploidDiploidModel (model : SelectionModel Deme Locus Allele) :
    DiploidSelectionModel Deme Locus Allele where
  locus := model.locus
  fitness i a a' := model.fitness i a + model.fitness i a'
  fitness_symm _ _ _ := add_comm _ _

variable [Fintype Deme] [DecidableEq Deme] [Fintype Locus] [DecidableEq Locus]
  [∀ ℓ, Fintype (Allele ℓ)] [∀ ℓ, DecidableEq (Allele ℓ)]

noncomputable section

/-! ## The diploid selection generator -/

/-- The marginal fitness `ŵ_i(a) = Σ_{a'} w_i(a, a') x_i[ℓ = a']` of allele `a` in deme `i`: the
mean fitness of its partner allele. -/
def marginalFitnessPolynomial (model : DiploidSelectionModel Deme Locus Allele) (i : Deme)
    (a : Allele model.locus) : FrequencyPolynomial Deme Locus Allele :=
  meanFitnessPolynomial (partnerModel model a) i

/-- At a frequency point the marginal fitness of `a` is `Σ_h x_i[h] w_i(a, h_ℓ)`. -/
theorem eval_marginalFitnessPolynomial (model : DiploidSelectionModel Deme Locus Allele)
    (x : FrequencyVariable Deme Locus Allele → ℝ) (i : Deme) (a : Allele model.locus) :
    eval x (marginalFitnessPolynomial model i a)
      = ∑ hap, x (i, hap) * model.fitness i a (hap model.locus) :=
  eval_meanFitnessPolynomial (partnerModel model a) x i

/-- The mean fitness `w̄_i = Σ_a ŵ_i(a) x_i[ℓ = a]` of deme `i`, as a frequency polynomial. -/
def diploidMeanFitnessPolynomial (model : DiploidSelectionModel Deme Locus Allele) (i : Deme) :
    FrequencyPolynomial Deme Locus Allele :=
  ∑ a, marginalFitnessPolynomial model i a * marginalPolynomial (singleLocusType i model.locus a)

/-- The diploid selective drift `x_i[h] (ŵ_i(h_ℓ) - w̄_i)` of one haplotype frequency. -/
def diploidDrift (model : DiploidSelectionModel Deme Locus Allele)
    (coordinate : FrequencyVariable Deme Locus Allele) : FrequencyPolynomial Deme Locus Allele :=
  X coordinate * (marginalFitnessPolynomial model coordinate.1 (coordinate.2 model.locus)
    - diploidMeanFitnessPolynomial model coordinate.1)

/-- **The diploid selection generator**: the derivation of frequency polynomials along the diploid
selective drift of every haplotype frequency. -/
def diploidSelectionGenerator (model : DiploidSelectionModel Deme Locus Allele)
    (f : FrequencyPolynomial Deme Locus Allele) : FrequencyPolynomial Deme Locus Allele :=
  ∑ coordinate, diploidDrift model coordinate * pderiv coordinate f

/-- **The forward generator with diploid selection**: the neutral generator plus the diploid
selection generator. -/
def diploidSelectedGenerator (rates : NeutralRates Deme Locus Allele)
    (model : DiploidSelectionModel Deme Locus Allele) (f : FrequencyPolynomial Deme Locus Allele) :
    FrequencyPolynomial Deme Locus Allele :=
  neutralGenerator rates f + diploidSelectionGenerator model f

/-- Without fitness differences the diploid selection generator vanishes. -/
theorem diploidSelectionGenerator_neutral (ℓ : Locus) (f : FrequencyPolynomial Deme Locus Allele) :
    diploidSelectionGenerator (DiploidSelectionModel.neutral ℓ) f = 0 := by
  simp [diploidSelectionGenerator, diploidDrift, diploidMeanFitnessPolynomial,
    marginalFitnessPolynomial, meanFitnessPolynomial, partnerModel, DiploidSelectionModel.neutral]

/-! ## Frozen marginal fitnesses -/

/-- **The haploid model of frozen marginal fitnesses**: allele `a` of deme `i` has fitness `ŵ_i(a)`
read at the frequency point `x`. -/
abbrev frozenHaploidModel (model : DiploidSelectionModel Deme Locus Allele)
    (x : FrequencyVariable Deme Locus Allele → ℝ) : SelectionModel Deme Locus Allele where
  locus := model.locus
  fitness i a := eval x (marginalFitnessPolynomial model i a)

/-- **At a frequency point the diploid drift is the haploid drift of the frozen model.** -/
theorem eval_diploidDrift (model : DiploidSelectionModel Deme Locus Allele)
    (x : FrequencyVariable Deme Locus Allele → ℝ)
    (coordinate : FrequencyVariable Deme Locus Allele) :
    eval x (diploidDrift model coordinate)
      = eval x (selectiveDrift (frozenHaploidModel model x) coordinate) := by
  simp only [diploidDrift, selectiveDrift, diploidMeanFitnessPolynomial, meanFitnessPolynomial,
    frozenHaploidModel, map_mul, map_sub, map_sum, eval_X, eval_C]

/-- **At a frequency point the diploid generator is the haploid generator of the frozen model.** -/
theorem eval_diploidSelectionGenerator (model : DiploidSelectionModel Deme Locus Allele)
    (x : FrequencyVariable Deme Locus Allele → ℝ) (f : FrequencyPolynomial Deme Locus Allele) :
    eval x (diploidSelectionGenerator model f)
      = eval x (selectionGenerator (frozenHaploidModel model x) f) := by
  simp only [diploidSelectionGenerator, selectionGenerator, map_sum, map_mul, eval_diploidDrift]

/-- **At a state the frozen fitnesses lie in `[0, σ]`** when every genotype fitness does: each is
an average of genotype fitnesses over the partner allele. -/
theorem frozenHaploidModel_fitness_mem (model : DiploidSelectionModel Deme Locus Allele) {σ : ℝ}
    (hfit : ∀ i a a', 0 ≤ model.fitness i a a' ∧ model.fitness i a a' ≤ σ)
    {x : FrequencyVariable Deme Locus Allele → ℝ} (hx0 : ∀ c, 0 ≤ x c)
    (hx1 : ∀ i, ∑ hap, x (i, hap) = 1) (i : Deme) (a : Allele model.locus) :
    0 ≤ (frozenHaploidModel model x).fitness i a ∧ (frozenHaploidModel model x).fitness i a ≤ σ :=
  eval_meanFitnessPolynomial_mem (partnerModel model a) (fun j b ↦ hfit j a b) hx0 hx1 i

/-- **A configuration with `n` carriers moves by at most `n σ` times its moment** under diploid
selection with genotype fitnesses in `[0, σ]`, at every state. -/
theorem abs_eval_diploidSelectionGenerator_momentPolynomial_le
    (model : DiploidSelectionModel Deme Locus Allele) {σ : ℝ}
    (hfit : ∀ i a a', 0 ≤ model.fitness i a a' ∧ model.fitness i a a' ≤ σ)
    {x : FrequencyVariable Deme Locus Allele → ℝ} (hx0 : ∀ c, 0 ≤ x c)
    (hx1 : ∀ i, ∑ hap, x (i, hap) = 1) (ξ : Multiset (PartialType Deme Locus Allele)) :
    |eval x (diploidSelectionGenerator model (momentPolynomial ξ))|
      ≤ Multiset.card ξ * σ * eval x (momentPolynomial ξ) := by
  rw [eval_diploidSelectionGenerator]
  exact abs_eval_selectionGenerator_momentPolynomial_le (frozenHaploidModel model x)
    (frozenHaploidModel_fitness_mem model hfit hx0 hx1) hx0 hx1 ξ

/-- **Diploid selection on one carrier raises the budget by two copies.** At every frequency point
the diploid generator of `x[τ]` is
`Σ_{b, b'} w(b, b') (x[τ ∧ b] x[ℓ = b'] - x[τ] x[ℓ = b] x[ℓ = b'])` in the deme of `τ`,
with `x[τ ∧ b] = 0` when `τ` retains another allele at the selected locus. -/
theorem eval_diploidSelectionGenerator_marginal_branching
    (model : DiploidSelectionModel Deme Locus Allele)
    (x : FrequencyVariable Deme Locus Allele → ℝ) (τ : PartialType Deme Locus Allele) :
    eval x (diploidSelectionGenerator model (marginalPolynomial τ))
      = ∑ b, ∑ b', model.fitness τ.deme b b'
          * ((if Compatible τ (singleLocusType τ.deme model.locus b) then
                eval x (marginalPolynomial (coalesce τ (singleLocusType τ.deme model.locus b)))
                  * eval x (marginalPolynomial (singleLocusType τ.deme model.locus b'))
              else 0)
            - eval x (marginalPolynomial τ)
              * eval x (marginalPolynomial (singleLocusType τ.deme model.locus b))
              * eval x (marginalPolynomial (singleLocusType τ.deme model.locus b'))) := by
  rw [eval_diploidSelectionGenerator, eval_selectionGenerator_marginal_branching]
  simp only [frozenHaploidModel, marginalFitnessPolynomial, meanFitnessPolynomial, partnerModel,
    map_sum, map_mul, eval_C, Finset.sum_mul]
  refine Finset.sum_congr rfl fun b _ ↦ Finset.sum_congr rfl fun b' _ ↦ ?_
  split_ifs <;> ring

/-! ## The haploid case -/

/-- At a state the one-locus carriers of the alleles at a locus have frequencies summing to one. -/
theorem sum_eval_singleLocusType_eq_one {x : FrequencyVariable Deme Locus Allele → ℝ}
    (hx1 : ∀ i, ∑ hap, x (i, hap) = 1) (ℓ₀ : Locus) (i : Deme) :
    ∑ b : Allele ℓ₀, eval x (marginalPolynomial (singleLocusType i ℓ₀ b)) = 1 := by
  have h := eval_meanFitnessPolynomial
    ({ locus := ℓ₀, fitness := fun _ _ ↦ 1 } : SelectionModel Deme Locus Allele) x i
  simp only [meanFitnessPolynomial, map_sum, map_mul, eval_C, one_mul, mul_one] at h
  exact h.trans (hx1 i)

/-- **Additive genotype fitness gives the haploid drift.** For `w_i(a, a') = s_i(a) + s_i(a')`, at a
state the diploid drift of every haplotype frequency is the haploid drift of `s`. -/
theorem eval_diploidDrift_haploidDiploidModel (model : SelectionModel Deme Locus Allele)
    {x : FrequencyVariable Deme Locus Allele → ℝ} (hx1 : ∀ i, ∑ hap, x (i, hap) = 1)
    (coordinate : FrequencyVariable Deme Locus Allele) :
    eval x (diploidDrift (haploidDiploidModel model) coordinate)
      = eval x (selectiveDrift model coordinate) := by
  have hone := sum_eval_singleLocusType_eq_one hx1 model.locus coordinate.1
  have hmean : eval x (meanFitnessPolynomial model coordinate.1)
      = ∑ b, model.fitness coordinate.1 b
          * eval x (marginalPolynomial (singleLocusType coordinate.1 model.locus b)) := by
    simp only [meanFitnessPolynomial, map_sum, map_mul, eval_C]
  have hmarginal : ∀ a,
      eval x (marginalFitnessPolynomial (haploidDiploidModel model) coordinate.1 a)
        = model.fitness coordinate.1 a + eval x (meanFitnessPolynomial model coordinate.1) := by
    intro a
    rw [hmean]
    simp only [marginalFitnessPolynomial, meanFitnessPolynomial, partnerModel, haploidDiploidModel,
      map_sum, map_mul, eval_C, add_mul, Finset.sum_add_distrib, ← Finset.mul_sum, hone, mul_one]
  simp only [diploidDrift, diploidMeanFitnessPolynomial, selectiveDrift, map_mul, map_sub, map_sum,
    eval_X, eval_C, hmarginal, add_mul, Finset.sum_add_distrib, ← Finset.mul_sum, hone, mul_one,
    ← hmean]
  ring

/-- **Additive genotype fitness gives the haploid generator**: at a state the diploid generator of
the table `s_i(a) + s_i(a')` is the haploid selection generator of `s`. -/
theorem eval_diploidSelectionGenerator_haploidDiploidModel
    (model : SelectionModel Deme Locus Allele) {x : FrequencyVariable Deme Locus Allele → ℝ}
    (hx1 : ∀ i, ∑ hap, x (i, hap) = 1)
    (f : FrequencyPolynomial Deme Locus Allele) :
    eval x (diploidSelectionGenerator (haploidDiploidModel model) f)
      = eval x (selectionGenerator model f) := by
  simp only [diploidSelectionGenerator, selectionGenerator, map_sum, map_mul,
    eval_diploidDrift_haploidDiploidModel model hx1]

/-! ## Zero order along a history -/

/-- The expected diploid selection term of every budget-respecting configuration under an
expectation functional over per-deme haplotype laws. -/
def expectedDiploidSelection (model : DiploidSelectionModel Deme Locus Allele)
    (capacity : Locus → ℕ)
    (expectation : ExpFunctional (Deme → FiniteReportLaw (FullHaplotype Locus Allele))) :
    BudgetConfiguration Deme Locus Allele capacity → ℝ :=
  fun ξ ↦ expectation fun law ↦
    eval (lawPoint law) (diploidSelectionGenerator model (momentPolynomial ξ.1))

/-- **The expected diploid selection term is at most `B σ`** for genotype fitnesses in `[0, σ]` and
a budget of total size `B = Σ_ℓ n_ℓ`. -/
theorem abs_expectedDiploidSelection_le (model : DiploidSelectionModel Deme Locus Allele) {σ : ℝ}
    (hσ : 0 ≤ σ) (hfit : ∀ i a a', 0 ≤ model.fitness i a a' ∧ model.fitness i a a' ≤ σ)
    (capacity : Locus → ℕ)
    (expectation : ExpFunctional (Deme → FiniteReportLaw (FullHaplotype Locus Allele)))
    (ξ : BudgetConfiguration Deme Locus Allele capacity) :
    |expectedDiploidSelection model capacity expectation ξ| ≤ (∑ ℓ, capacity ℓ : ℕ) * σ := by
  have hpoint : ∀ law : Deme → FiniteReportLaw (FullHaplotype Locus Allele),
      |eval (lawPoint law) (diploidSelectionGenerator model (momentPolynomial ξ.1))|
        ≤ (∑ ℓ, capacity ℓ : ℕ) * σ := by
    intro law
    have hmoment := abs_eval_diploidSelectionGenerator_momentPolynomial_le model hfit
      (x := lawPoint law) (fun c ↦ (law c.1).mass_nonneg c.2) (fun i ↦ (law i).mass_sum) ξ.1
    rw [eval_momentPolynomial] at hmoment
    have hcard : (Multiset.card ξ.1 : ℝ) ≤ (∑ ℓ, capacity ℓ : ℕ) := by
      exact_mod_cast card_le_capacity_total capacity ξ.1 ξ.2
    exact hmoment.trans ((mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcard hσ)
      (PartialHaplotypeCarrier.configurationMoment_nonneg law ξ.1)).trans
        (mul_le_of_le_one_right (mul_nonneg (Nat.cast_nonneg _) hσ)
          (configurationMoment_le_one law ξ.1)))
  exact abs_le.mpr ⟨by simpa only [ExpFunctional.eval_const] using
      expectation.eval_mono fun law ↦ (abs_le.mp (hpoint law)).1,
    by simpa only [ExpFunctional.eval_const] using
      expectation.eval_mono fun law ↦ (abs_le.mp (hpoint law)).2⟩

/-- **The forward moment equation with diploid selection.** Under an expectation functional, the
expected generator with diploid selection of a budget-respecting configuration moment is the
neutral dual generator on the expected moments plus the expected diploid selection term. -/
theorem expectedDiploidSelectedGenerator_eq (rates : NeutralRates Deme Locus Allele)
    (model : DiploidSelectionModel Deme Locus Allele) (capacity : Locus → ℕ)
    (expectationAt : ℝ → ExpFunctional (Deme → FiniteReportLaw (FullHaplotype Locus Allele)))
    (s : ℝ) (ξ : BudgetConfiguration Deme Locus Allele capacity) :
    (expectationAt s fun law ↦
        eval (lawPoint law) (diploidSelectedGenerator rates model (momentPolynomial ξ.1)))
      = (dualGenerator rates capacity *ᵥ expectedMomentVector capacity expectationAt s) ξ
        + expectedDiploidSelection model capacity (expectationAt s) ξ := by
  have h := (expectationAt s).add_eval
    (fun law ↦ eval (lawPoint law) (neutralGenerator rates (momentPolynomial ξ.1)))
    (fun law ↦ eval (lawPoint law) (diploidSelectionGenerator model (momentPolynomial ξ.1)))
  rw [expectedGenerator_eq_mulVec rates capacity expectationAt s ξ] at h
  simp only [diploidSelectedGenerator, map_add]
  exact h

/-- **Diploid selection moves the moments of one epoch by at most `B σ d`.** Suppose the expected
budget-respecting configuration moments of an expectation family are continuous on `[0, d]` and
obey the forward moment equation with diploid selection there, with genotype fitnesses in
`[0, σ]`. Then the moments at `d` differ from the neutral epoch propagator applied to the initial
moments by at most `B σ d` in sup norm, with `B = Σ_ℓ n_ℓ`. -/
theorem norm_expectedMomentVector_sub_propagator_le_diploid
    (rates : NeutralRates Deme Locus Allele) (model : DiploidSelectionModel Deme Locus Allele)
    {σ : ℝ} (hσ : 0 ≤ σ) (hfit : ∀ i a a', 0 ≤ model.fitness i a a' ∧ model.fitness i a a' ≤ σ)
    (capacity : Locus → ℕ)
    (expectationAt : ℝ → ExpFunctional (Deme → FiniteReportLaw (FullHaplotype Locus Allele)))
    {d : ℝ} (hd : 0 ≤ d)
    (hcont : ContinuousOn (expectedMomentVector capacity expectationAt) (Set.Icc 0 d))
    (hforward : ∀ ξ : BudgetConfiguration Deme Locus Allele capacity, ∀ t ∈ Set.Ico 0 d,
      HasDerivWithinAt (fun s ↦ expectedMomentVector capacity expectationAt s ξ)
        (expectationAt t fun law ↦
          eval (lawPoint law) (diploidSelectedGenerator rates model (momentPolynomial ξ.1)))
        (Set.Ici t) t) :
    ‖expectedMomentVector capacity expectationAt d
        - matrixExponential (dualGenerator rates capacity) d
          *ᵥ expectedMomentVector capacity expectationAt 0‖
      ≤ (∑ ℓ, capacity ℓ : ℕ) * σ * d := by
  have hexp : ∀ t, HasDerivAt
      (fun u ↦ matrixExponential (dualGenerator rates capacity) u
        *ᵥ expectedMomentVector capacity expectationAt 0)
      (dualGenerator rates capacity *ᵥ (matrixExponential (dualGenerator rates capacity) t
        *ᵥ expectedMomentVector capacity expectationAt 0)) t := fun t ↦
    StationaryHaplotypeRealization.hasDerivAt_matrixExponential_mulVec _ _ t
  have hderiv : ∀ t ∈ Set.Ico 0 d, HasDerivWithinAt
      (fun u ↦ expectedMomentVector capacity expectationAt u
        - matrixExponential (dualGenerator rates capacity) u
          *ᵥ expectedMomentVector capacity expectationAt 0)
      (dualGenerator rates capacity *ᵥ (expectedMomentVector capacity expectationAt t
          - matrixExponential (dualGenerator rates capacity) t
            *ᵥ expectedMomentVector capacity expectationAt 0)
        + expectedDiploidSelection model capacity (expectationAt t)) (Set.Ici t) t := by
    intro t ht
    have hv : HasDerivWithinAt (expectedMomentVector capacity expectationAt)
        (dualGenerator rates capacity *ᵥ expectedMomentVector capacity expectationAt t
          + expectedDiploidSelection model capacity (expectationAt t)) (Set.Ici t) t :=
      hasDerivWithinAt_pi.mpr fun ξ ↦ (hforward ξ t ht).congr_deriv
        (expectedDiploidSelectedGenerator_eq rates model capacity expectationAt t ξ)
    refine (hv.sub (hexp t).hasDerivWithinAt).congr_deriv ?_
    rw [Matrix.mulVec_sub]
    abel
  have hbound : ∀ t ∈ Set.Ico 0 d,
      ‖expectedDiploidSelection model capacity (expectationAt t)‖ ≤ (∑ ℓ, capacity ℓ : ℕ) * σ :=
    fun t _ ↦ (pi_norm_le_iff_of_nonneg (mul_nonneg (Nat.cast_nonneg _) hσ)).mpr fun ξ ↦ by
      rw [Real.norm_eq_abs]
      exact abs_expectedDiploidSelection_le model hσ hfit capacity (expectationAt t) ξ
  have hG : ∀ y, HasDerivAt (fun u ↦ (∑ ℓ, capacity ℓ : ℕ) * σ * u)
      ((∑ ℓ, capacity ℓ : ℕ) * σ) y := fun y ↦
    ((hasDerivAt_id y).const_mul ((∑ ℓ, capacity ℓ : ℕ) * σ)).congr_deriv (mul_one _)
  exact SelectionMomentUniqueness.norm_le_of_zeroStart
    (killingGenerator_dualGenerator rates capacity) hd
    (hcont.sub (continuous_iff_continuousAt.mpr fun t ↦ (hexp t).continuousAt).continuousOn)
    hderiv (by simp only [matrixExponential_zero, Matrix.one_mulVec, sub_self]) (by simp) hG
    hbound

/-- **Diploid selection along a history of epochs, splits and pulses.** `family k` is the
expectation family over per-deme haplotype laws during the `k`-th event, on its own clock. During
an epoch its expected budget-respecting configuration moments are continuous on `[0, d]` and obey
the forward moment equation with diploid selection at the epoch's neutral rates, and the next
family starts from the moments at `d`. Across a split or a pulse the next family starts from the
pulsed moments.

Assumes: the families are the moment tables of a process with diploid selection run through the
events in chronological order. -/
def DiploidSelectedOnHistory (model : DiploidSelectionModel Deme Locus Allele)
    (capacity : Locus → ℕ)
    (family : ℕ → ℝ → ExpFunctional (Deme → FiniteReportLaw (FullHaplotype Locus Allele))) :
    List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme) → ℕ → Prop
  | [], _ => True
  | Sum.inl epoch :: rest, k =>
      (ContinuousOn (expectedMomentVector capacity (family k)) (Set.Icc 0 (epoch.2 : ℝ))
        ∧ (∀ ξ : BudgetConfiguration Deme Locus Allele capacity, ∀ t ∈ Set.Ico 0 (epoch.2 : ℝ),
          HasDerivWithinAt (fun s ↦ expectedMomentVector capacity (family k) s ξ)
            (family k t fun law ↦
              eval (lawPoint law) (diploidSelectedGenerator epoch.1 model (momentPolynomial ξ.1)))
            (Set.Ici t) t)
        ∧ expectedMomentVector capacity (family (k + 1)) 0
          = expectedMomentVector capacity (family k) epoch.2)
      ∧ DiploidSelectedOnHistory model capacity family rest (k + 1)
  | Sum.inr pulse :: rest, k =>
      (∀ ξ : BudgetConfiguration Deme Locus Allele capacity,
        expectedMomentVector capacity (family (k + 1)) 0 ξ
          = family k 0 fun law ↦ configurationMoment (pulsedLaw pulse law) ξ.1)
      ∧ DiploidSelectedOnHistory model capacity family rest (k + 1)

/-- The empty history carries no obligation, so `DiploidSelectedOnHistory` is inhabited. -/
theorem diploidSelectedOnHistory_nil (model : DiploidSelectionModel Deme Locus Allele)
    (capacity : Locus → ℕ)
    (family : ℕ → ℝ → ExpFunctional (Deme → FiniteReportLaw (FullHaplotype Locus Allele)))
    (k : ℕ) : DiploidSelectedOnHistory model capacity family [] k :=
  trivial

/-- **Diploid selection moves the moments of a whole history by at most `B σ T`.** Along a history
of epochs, splits and pulses with total epoch duration `T`, families selected with genotype
fitnesses in `[0, σ]` end with expected budget-respecting configuration moments within `B σ T` in
sup norm of the neutral chronological propagator applied to their initial moments, with
`B = Σ_ℓ n_ℓ`.

Assumes: `DiploidSelectedOnHistory model capacity family events k`. -/
theorem norm_diploidHistory_sub_propagator_le (model : DiploidSelectionModel Deme Locus Allele)
    {σ : ℝ} (hσ : 0 ≤ σ) (hfit : ∀ i a a', 0 ≤ model.fitness i a a' ∧ model.fitness i a a' ≤ σ)
    (capacity : Locus → ℕ)
    (family : ℕ → ℝ → ExpFunctional (Deme → FiniteReportLaw (FullHaplotype Locus Allele))) :
    ∀ (events : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme)) (k : ℕ),
      DiploidSelectedOnHistory model capacity family events k →
      ‖expectedMomentVector capacity (family (k + events.length)) 0
          - historyEventPropagator capacity events *ᵥ expectedMomentVector capacity (family k) 0‖
        ≤ (∑ ℓ, capacity ℓ : ℕ) * σ * epochDuration events
  | [], k, _ => by
    simp [historyEventPropagator, epochDuration]
  | Sum.inl epoch :: rest, k, hhistory => by
    obtain ⟨⟨hcont, hforward, hnext⟩, hrest⟩ := hhistory
    have hepoch := norm_expectedMomentVector_sub_propagator_le_diploid epoch.1 model hσ hfit
      capacity (family k) (NNReal.coe_nonneg epoch.2) hcont hforward
    rw [← hnext] at hepoch
    have hlength : k + (Sum.inl epoch :: rest).length = k + 1 + rest.length := by
      rw [List.length_cons]
      omega
    rw [hlength, historyEventPropagator, eventPropagator, ← Matrix.mulVec_mulVec]
    exact (norm_sub_mulVec_le (historyEventPropagator_substochastic capacity rest)
      (norm_diploidHistory_sub_propagator_le model hσ hfit capacity family rest (k + 1) hrest)
      hepoch).trans_eq (by simp only [epochDuration]; ring)
  | Sum.inr pulse :: rest, k, hhistory => by
    obtain ⟨hnext, hrest⟩ := hhistory
    have hmoments : expectedMomentVector capacity (family (k + 1)) 0
        = pulseKernel pulse capacity *ᵥ expectedMomentVector capacity (family k) 0 := by
      funext ξ
      rw [hnext ξ, pulseKernel_mulVec_expectedMoment]
      rfl
    have hlength : k + (Sum.inr pulse :: rest).length = k + 1 + rest.length := by
      rw [List.length_cons]
      omega
    have h := norm_diploidHistory_sub_propagator_le model hσ hfit capacity family rest (k + 1)
      hrest
    rw [hmoments, ← hlength, Matrix.mulVec_mulVec] at h
    simpa only [historyEventPropagator, eventPropagator, epochDuration] using h

/-- **Portability under diploid selection, with an explicit error bar.** Along a history selected
with genotype fitnesses in `[0, σ]` and total epoch duration `T`, where the expected target
denominator and source numerator are at least `δ > 0` under the selected family and at the neutral
end moments, the portability of expected accuracies differs from the portability of the neutral end
moments by at most `4 ‖a‖₁ ‖b‖₁ ‖c‖₁ ‖d‖₁ / δ⁴ · 4 |L| σ T`, with `a, b, c, d` the coefficient
vectors of the target numerator, source denominator, target denominator and source numerator.

Assumes: `DiploidSelectedOnHistory model (fun _ ↦ 4) family events 0`. -/
theorem abs_diploidPortability_sub_neutral_le (ℓ₀ : Locus)
    (model : DiploidSelectionModel Deme Locus Allele) {σ : ℝ} (hσ : 0 ≤ σ)
    (hfit : ∀ i a a', 0 ≤ model.fitness i a a' ∧ model.fitness i a a' ≤ σ)
    (family : ℕ → ℝ → ExpFunctional (Deme → FiniteReportLaw (FullHaplotype Locus Allele)))
    (events : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme))
    (hhistory : DiploidSelectedOnHistory model (fun _ ↦ 4) family events 0)
    (source target : Deme) (score outcome : FullHaplotype Locus Allele → ℝ) {δ : ℝ}
    (hδ : 0 < δ)
    (htarget : δ ≤ family events.length 0 fun law ↦
      correlationDenominator (law target) score outcome)
    (hsource : δ ≤ family events.length 0 fun law ↦
      correlationNumerator (law source) score outcome)
    (htarget₀ : δ ≤ budgetCoefficients ℓ₀ (fun _ ↦ 4) (denominatorPolynomial target score outcome)
      ⬝ᵥ (historyEventPropagator (fun _ ↦ 4) events
        *ᵥ expectedMomentVector (fun _ ↦ 4) (family 0) 0))
    (hsource₀ : δ ≤ budgetCoefficients ℓ₀ (fun _ ↦ 4) (numeratorPolynomial source score outcome)
      ⬝ᵥ (historyEventPropagator (fun _ ↦ 4) events
        *ᵥ expectedMomentVector (fun _ ↦ 4) (family 0) 0)) :
    |selectedPortability family events.length source target score outcome
        - momentPortability ℓ₀ source target score outcome
          (historyEventPropagator (fun _ ↦ 4) events
            *ᵥ expectedMomentVector (fun _ ↦ 4) (family 0) 0)|
      ≤ 4 * (∑ i, |budgetCoefficients ℓ₀ (fun _ ↦ 4) (numeratorPolynomial target score outcome) i|)
          * (∑ i, |budgetCoefficients ℓ₀ (fun _ ↦ 4)
              (denominatorPolynomial source score outcome) i|)
          * (∑ i, |budgetCoefficients ℓ₀ (fun _ ↦ 4)
              (denominatorPolynomial target score outcome) i|)
          * (∑ i, |budgetCoefficients ℓ₀ (fun _ ↦ 4) (numeratorPolynomial source score outcome) i|)
          / δ ^ 4 * (4 * Fintype.card Locus * σ * epochDuration events) := by
  have hmoments := norm_diploidHistory_sub_propagator_le model hσ hfit (fun _ ↦ 4) family events
    0 hhistory
  rw [zero_add, sum_four_capacity] at hmoments
  rw [expectation_correlationDenominator ℓ₀] at htarget
  rw [expectation_correlationNumerator ℓ₀] at hsource
  have hbox : ∀ v : BudgetConfiguration Deme Locus Allele (fun _ ↦ 4) → ℝ, ‖v‖ ≤ 1 →
      ∀ η, |v η| ≤ 1 :=
    fun v hv η ↦ by simpa only [Real.norm_eq_abs] using (norm_le_pi_norm v η).trans hv
  have hcross := PortabilityMetricCompilation.abs_crossRatio_sub_le
    (fun w : {w : BudgetConfiguration Deme Locus Allele (fun _ ↦ 4) → ℝ // ∀ i, |w i| ≤ 1} ↦
      w.1) hδ (fun w i ↦ w.2 i)
    (budgetCoefficients ℓ₀ (fun _ ↦ 4) (numeratorPolynomial target score outcome))
    (budgetCoefficients ℓ₀ (fun _ ↦ 4) (denominatorPolynomial source score outcome))
    (budgetCoefficients ℓ₀ (fun _ ↦ 4) (denominatorPolynomial target score outcome))
    (budgetCoefficients ℓ₀ (fun _ ↦ 4) (numeratorPolynomial source score outcome))
    (RealizationBody.mem_realizationBody_of_range _ ⟨_, hbox _
      (SelectionHistoryFirstOrder.norm_expectedMomentVector_le_one (fun _ ↦ 4)
        (family events.length) 0)⟩)
    (RealizationBody.mem_realizationBody_of_range _ ⟨_, hbox _
      ((norm_mulVec_le_of_substochastic
        (historyEventPropagator_substochastic (fun _ ↦ 4) events) _).trans
          (SelectionHistoryFirstOrder.norm_expectedMomentVector_le_one (fun _ ↦ 4) (family 0)
            0))⟩)
    htarget hsource htarget₀ hsource₀
  rw [selectedPortability_eq_momentPortability ℓ₀]
  refine hcross.trans ?_
  rw [one_pow, mul_one]
  exact mul_le_mul_of_nonneg_left hmoments (by positivity)

end

end Descent.Portability.DiploidSelectionHistory
