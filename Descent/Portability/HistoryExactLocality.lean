/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.EndToEndPortabilityLaw
import Descent.Portability.PortabilityExactLocality

assert_below Descent.Decision Descent.Program

/-!
# Exact locality of neutral portability along whole histories

`Descent.Portability.PortabilityExactLocality` shows that under one epoch of NOTE1's neutral model
the expected moments over a set of loci `A` read only the model on `A`. This module extends that to
a whole history of epochs, splits and admixture pulses
(`Descent.Portability.NeutralPulseHistoryKernel.historyEventKernel`), and to the end-to-end
portability of a score (`Descent.Portability.EndToEndPortabilityLaw.expectedPortability`).

## Matrices that act locally

`RowsLocal A P` says the rows of a moment matrix at configurations over `A` vanish off them, and
`RowsAgreeOn A P P'` says two moment matrices agree on those rows. Both are closed under products,
when the left factor acts locally (`RowsLocal.mul`, `RowsAgreeOn.mul`), and vectors equal over `A`
stay equal over `A` (`mulVec_eq_of_rowsAgreeOn`).

The row of an epoch propagator at a configuration over `A` is read through the block of
configurations over `A` (`matrixExponential_apply_eq_local`), by the block intertwining
`localRestriction_mul_matrixExponential`. So an epoch propagator acts locally
(`rowsLocal_matrixExponential`), and two propagators whose generators agree on the rows over `A`
agree on the rows over `A` (`rowsAgreeOn_matrixExponential`). A pulse only relabels demes, so its
substitution kernel acts locally (`rowsLocal_pulseKernel`).

## Histories

Two events agree on `A` (`EventAgreeOn`) when they are epochs of the same duration whose rate tables
agree on `A` (`RatesAgreeOn`: equal coalescence and migration rates, equal mutation rates at the
loci of `A`, and the same total rate for every crossover pattern on `A`), or pulses whose
substitution kernels agree on the rows over `A`. Every history acts locally
(`rowsLocal_historyEventPropagator`). Histories that agree on `A` event by event have chronological
moment matrices that agree on the rows over `A` (`rowsAgreeOn_historyEventPropagator`).

**The history theorem** (`integral_momentPolynomial_historyEventKernel_eq_of_agreeOn`). For two
histories that agree on `A` event by event, started at states with equal configuration moments over
`A`, the expected configuration moments at the end of the history agree at every configuration over
`A`, under the process law.

## End-to-end portability

A function of full haplotypes that reads only the alleles at `A` (`ReadsLoci`) has an expectation
polynomial in the span of the one-carrier moments over `A` (`expectation_mem_localMomentSpan`), by
grouping haplotypes by their alleles at `A` (`localType`). The correlation numerator and denominator
of a score and outcome that read only `A` therefore lie in the span of the moments of at most four
carriers over `A` (`numeratorPolynomial_mem_localMomentSpan`,
`denominatorPolynomial_mem_localMomentSpan`), whose integrals agree for the two histories
(`integral_eq_of_mem_localMomentSpan`).

**The portability theorem** (`expectedPortability_eq_of_agreeOn`). For a score and an outcome that
read only a nonempty set of loci `A`, two histories that agree on `A` event by event, from states
with equal budget-4 moments over `A`, have equal expected portability between every source and
target.

Significance. Under neutrality the end-to-end portability of a polygenic score depends on the
demographic history and the initial state only through the history restricted to the score's loci
and the initial linkage disequilibrium among those loci. Recombination hotspots, mutation rates and
allele frequencies at other loci cannot move it, at any epoch, split or pulse.

Scope. Pulses are compared through their substitution kernels on the rows over `A`; identical
pulses agree. Histories given as continuous rate paths
(`Descent.Portability.NeutralRateHistoryKernel`) and the joint form of NOTE2 (27) at budget 8 are
not covered here. The model is NOTE1's neutral model; selection is not covered.

## Empirical status

None. The bodies here are finite sums of supplied rates and mixture weights, matrix exponentials of
supplied rate tables, and integrals of polynomials against Markov kernels, so no measurement can
bear on them.
-/

namespace Descent.Portability.HistoryExactLocality

open MeasureTheory ProbabilityTheory MvPolynomial Descent.Coalescent PartialHaplotypeCarrier
  PartialHaplotypeDualGenerator PartialHaplotypeDualSemigroup NeutralFellerGenerator
  NeutralPolynomialSemigroup PartialHaplotypeMicroscopicApproximation PartialHaplotypePulseKernel
  NeutralPulseHistoryKernel NeutralRateHistoryRealization NeutralRateHistoryKernel
  ReplicaMetricInstances EndToEndPortabilityLaw PortabilityExactLocality Finset
open scoped Matrix NNReal Pointwise

variable {Deme Locus : Type*} {Allele : Locus → Type*}
variable [Fintype Deme] [DecidableEq Deme] [Fintype Locus] [DecidableEq Locus]
  [∀ ℓ, Fintype (Allele ℓ)] [∀ ℓ, DecidableEq (Allele ℓ)]

noncomputable section

/-! ### Matrices that act locally -/

/-- **A moment matrix acts locally on `A`**: its rows at configurations over `A` vanish off
them. -/
def RowsLocal (A : Finset Locus) {capacity : Locus → ℕ}
    (P : Matrix (BudgetConfiguration Deme Locus Allele capacity)
      (BudgetConfiguration Deme Locus Allele capacity) ℝ) : Prop :=
  ∀ ξ η : BudgetConfiguration Deme Locus Allele capacity, LociWithin A ξ.1 → ¬LociWithin A η.1 →
    P ξ η = 0

/-- **Two moment matrices agree on the rows over `A`.** -/
def RowsAgreeOn (A : Finset Locus) {capacity : Locus → ℕ}
    (P P' : Matrix (BudgetConfiguration Deme Locus Allele capacity)
      (BudgetConfiguration Deme Locus Allele capacity) ℝ) : Prop :=
  ∀ ξ η : BudgetConfiguration Deme Locus Allele capacity, LociWithin A ξ.1 → P ξ η = P' ξ η

/-- The identity acts locally. -/
theorem rowsLocal_one (A : Finset Locus) (capacity : Locus → ℕ) :
    RowsLocal A (1 : Matrix (BudgetConfiguration Deme Locus Allele capacity)
      (BudgetConfiguration Deme Locus Allele capacity) ℝ) := by
  intro ξ η hξ hη
  rw [Matrix.one_apply, if_neg fun (h : ξ = η) ↦ hη (h ▸ hξ)]

/-- Every moment matrix agrees with itself on the rows over `A`. -/
theorem rowsAgreeOn_refl (A : Finset Locus) {capacity : Locus → ℕ}
    (P : Matrix (BudgetConfiguration Deme Locus Allele capacity)
      (BudgetConfiguration Deme Locus Allele capacity) ℝ) : RowsAgreeOn A P P :=
  fun _ _ _ ↦ rfl

/-- A product of moment matrices that act locally acts locally. -/
theorem RowsLocal.mul {A : Finset Locus} {capacity : Locus → ℕ}
    {P R : Matrix (BudgetConfiguration Deme Locus Allele capacity)
      (BudgetConfiguration Deme Locus Allele capacity) ℝ}
    (hP : RowsLocal A P) (hR : RowsLocal A R) : RowsLocal A (P * R) := by
  intro ξ η hξ hη
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun ζ _ ↦ ?_
  by_cases hζ : LociWithin A ζ.1
  · rw [hR ζ η hζ hη, mul_zero]
  · rw [hP ξ ζ hξ hζ, zero_mul]

/-- **Products that agree on the rows over `A` agree on the rows over `A`**, when the left factor
acts locally. -/
theorem RowsAgreeOn.mul {A : Finset Locus} {capacity : Locus → ℕ}
    {P P' R R' : Matrix (BudgetConfiguration Deme Locus Allele capacity)
      (BudgetConfiguration Deme Locus Allele capacity) ℝ}
    (hP : RowsAgreeOn A P P') (hlocal : RowsLocal A P) (hR : RowsAgreeOn A R R') :
    RowsAgreeOn A (P * R) (P' * R') := by
  intro ξ η hξ
  rw [Matrix.mul_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun ζ _ ↦ ?_
  by_cases hζ : LociWithin A ζ.1
  · rw [hP ξ ζ hξ, hR ζ η hζ]
  · rw [← hP ξ ζ hξ, hlocal ξ ζ hξ hζ, zero_mul, zero_mul]

/-- **Vectors equal over `A` stay equal over `A`** under moment matrices that act locally and agree
on the rows over `A`. -/
theorem mulVec_eq_of_rowsAgreeOn {A : Finset Locus} {capacity : Locus → ℕ}
    {P P' : Matrix (BudgetConfiguration Deme Locus Allele capacity)
      (BudgetConfiguration Deme Locus Allele capacity) ℝ}
    (hlocal : RowsLocal A P) (hagree : RowsAgreeOn A P P')
    {v v' : BudgetConfiguration Deme Locus Allele capacity → ℝ}
    (hv : ∀ ξ : BudgetConfiguration Deme Locus Allele capacity, LociWithin A ξ.1 → v ξ = v' ξ)
    {ξ : BudgetConfiguration Deme Locus Allele capacity} (hξ : LociWithin A ξ.1) :
    (P *ᵥ v) ξ = (P' *ᵥ v') ξ := by
  simp only [Matrix.mulVec, dotProduct]
  refine Finset.sum_congr rfl fun ζ _ ↦ ?_
  by_cases hζ : LociWithin A ζ.1
  · rw [hagree ξ ζ hξ, hv ζ hζ]
  · rw [← hagree ξ ζ hξ, hlocal ξ ζ hξ hζ, zero_mul, zero_mul]

/-! ### The events of a history -/

/-- The row of an epoch propagator at a configuration over `A` is read through the block of
configurations over `A`. -/
theorem matrixExponential_apply_eq_local (rates : NeutralRates Deme Locus Allele)
    (capacity : Locus → ℕ) (A : Finset Locus) (t : ℝ)
    {ξ : BudgetConfiguration Deme Locus Allele capacity} (hξ : LociWithin A ξ.1)
    (η : BudgetConfiguration Deme Locus Allele capacity) :
    matrixExponential (dualGenerator rates capacity) t ξ η =
      ∑ s : LocalConfiguration Deme Locus Allele capacity A,
        matrixExponential (localGenerator rates capacity A) t ⟨ξ, hξ⟩ s *
          localRestriction capacity A s η := by
  have h := congrFun (congrFun
    (localRestriction_mul_matrixExponential rates capacity A t) ⟨ξ, hξ⟩) η
  rw [Matrix.mul_apply, Matrix.mul_apply] at h
  have hleft : ∑ ζ, localRestriction capacity A ⟨ξ, hξ⟩ ζ *
      matrixExponential (dualGenerator rates capacity) t ζ η =
        matrixExponential (dualGenerator rates capacity) t ξ η := by
    simp [localRestriction]
  exact hleft.symm.trans h

/-- **An epoch propagator acts locally.** -/
theorem rowsLocal_matrixExponential (rates : NeutralRates Deme Locus Allele)
    (capacity : Locus → ℕ) (A : Finset Locus) (t : ℝ) :
    RowsLocal A (matrixExponential (dualGenerator rates capacity) t) := by
  intro ξ η hξ hη
  rw [matrixExponential_apply_eq_local rates capacity A t hξ η]
  exact Finset.sum_eq_zero fun s' _ ↦ by
    simp only [localRestriction]
    rw [if_neg fun (heq : η = s'.1) ↦ hη (heq ▸ s'.2), mul_zero]

/-- **Epoch propagators whose generators agree on the rows over `A` agree on the rows over
`A`.** -/
theorem rowsAgreeOn_matrixExponential {rates rates' : NeutralRates Deme Locus Allele}
    {capacity : Locus → ℕ} {A : Finset Locus}
    (hrow : ∀ ξ η : BudgetConfiguration Deme Locus Allele capacity, LociWithin A ξ.1 →
      dualGenerator rates capacity ξ η = dualGenerator rates' capacity ξ η) (t : ℝ) :
    RowsAgreeOn A (matrixExponential (dualGenerator rates capacity) t)
      (matrixExponential (dualGenerator rates' capacity) t) := by
  have hgen : localGenerator rates capacity A = localGenerator rates' capacity A := by
    ext s s'
    exact hrow s.1 s'.1 s.2
  intro ξ η hξ
  rw [matrixExponential_apply_eq_local rates capacity A t hξ η,
    matrixExponential_apply_eq_local rates' capacity A t hξ η, hgen]

/-- A pulse relabels demes only, so it relabels a configuration over `A` into one over `A`. -/
theorem lociWithin_relabelCarriers {A : Finset Locus}
    {ξ : Multiset (PartialType Deme Locus Allele)} (hξ : LociWithin A ξ)
    (choice : Fin ξ.toList.length → Deme) : LociWithin A (relabelCarriers ξ.toList choice) := by
  intro τ hτ
  obtain ⟨k, _, rfl⟩ := Multiset.mem_map.mp hτ
  exact hξ _ (Multiset.mem_toList.mp (List.get_mem _ k))

/-- **A pulse acts locally.** -/
theorem rowsLocal_pulseKernel (pulse : PulseMatrix Deme) (capacity : Locus → ℕ)
    (A : Finset Locus) : RowsLocal A (pulseKernel (Allele := Allele) pulse capacity) := by
  intro ξ η hξ hη
  simp only [pulseKernel]
  exact Finset.sum_eq_zero fun choice _ ↦
    if_neg fun (heq : relabelCarriers ξ.1.toList choice = η.1) ↦
      hη (heq ▸ lociWithin_relabelCarriers hξ choice)

/-- **Two neutral rate tables agree on `A`**: equal coalescence and migration rates, equal mutation
rates at the loci of `A`, and the same total rate for every crossover pattern on `A`. -/
structure RatesAgreeOn (A : Finset Locus) (rates rates' : NeutralRates Deme Locus Allele) :
    Prop where
  /-- The coalescence rates are equal. -/
  coalescence : rates.coalescence = rates'.coalescence
  /-- The migration rates are equal. -/
  migration : rates.migration = rates'.migration
  /-- The mutation rates agree at the loci of `A`. -/
  mutation : ∀ ℓ ∈ A, rates.mutation ℓ = rates'.mutation ℓ
  /-- Every crossover pattern on `A` has the same total rate. -/
  recombination : ∀ key : ↥A → Bool,
    ∑ s ∈ univ.filter fun s ↦ selectorOn A s = key, rates.recombination s =
      ∑ s ∈ univ.filter fun s ↦ selectorOn A s = key, rates'.recombination s

/-- A rate table agrees with itself on `A`. -/
theorem RatesAgreeOn.refl (A : Finset Locus) (rates : NeutralRates Deme Locus Allele) :
    RatesAgreeOn A rates rates :=
  ⟨rfl, rfl, fun _ _ ↦ rfl, fun _ ↦ rfl⟩

/-- **Two events of a history agree on `A`**: epochs of the same duration whose rate tables agree
on `A`, or pulses whose substitution kernels agree on the rows over `A`. -/
def EventAgreeOn (A : Finset Locus) (capacity : Locus → ℕ) :
    (NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme →
      (NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme → Prop
  | Sum.inl epoch, Sum.inl epoch' => epoch.2 = epoch'.2 ∧ RatesAgreeOn A epoch.1 epoch'.1
  | Sum.inr pulse, Sum.inr pulse' =>
      RowsAgreeOn A (pulseKernel (Allele := Allele) pulse capacity) (pulseKernel pulse' capacity)
  | _, _ => False

/-- Every event agrees with itself on `A`. -/
theorem eventAgreeOn_refl (A : Finset Locus) (capacity : Locus → ℕ) :
    ∀ event : (NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme,
      EventAgreeOn A capacity event event
  | Sum.inl epoch => ⟨rfl, RatesAgreeOn.refl A epoch.1⟩
  | Sum.inr pulse => rowsAgreeOn_refl A (pulseKernel (Allele := Allele) pulse capacity)

/-- **The moment matrix of every event acts locally.** -/
theorem rowsLocal_eventPropagator (capacity : Locus → ℕ) (A : Finset Locus) :
    ∀ event : (NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme,
      RowsLocal A (eventPropagator capacity event)
  | Sum.inl epoch => rowsLocal_matrixExponential epoch.1 capacity A epoch.2
  | Sum.inr pulse => rowsLocal_pulseKernel pulse capacity A

/-- **Events that agree on `A` have moment matrices that agree on the rows over `A`.** -/
theorem rowsAgreeOn_eventPropagator (capacity : Locus → ℕ) (A : Finset Locus) :
    ∀ event event' : (NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme,
      EventAgreeOn A capacity event event' →
        RowsAgreeOn A (eventPropagator capacity event) (eventPropagator capacity event')
  | Sum.inl epoch, Sum.inl epoch', h => by
    obtain ⟨hduration, hrates⟩ := h
    show RowsAgreeOn A (matrixExponential (dualGenerator epoch.1 capacity) epoch.2)
      (matrixExponential (dualGenerator epoch'.1 capacity) epoch'.2)
    rw [hduration]
    exact rowsAgreeOn_matrixExponential (fun ξ η hξ ↦ dualGenerator_eq_of_agreeOn
      hrates.coalescence hrates.migration hrates.mutation hrates.recombination capacity ξ η hξ) _
  | Sum.inr _, Sum.inr _, h => h
  | Sum.inl _, Sum.inr _, h => False.elim h
  | Sum.inr _, Sum.inl _, h => False.elim h

/-! ### Histories -/

/-- **The chronological moment matrix of every history acts locally.** -/
theorem rowsLocal_historyEventPropagator (capacity : Locus → ℕ) (A : Finset Locus) :
    ∀ events : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme),
      RowsLocal A (historyEventPropagator capacity events)
  | [] => rowsLocal_one A capacity
  | event :: rest =>
    (rowsLocal_historyEventPropagator capacity A rest).mul
      (rowsLocal_eventPropagator capacity A event)

/-- **Histories that agree on `A` event by event have chronological moment matrices that agree on
the rows over `A`.** -/
theorem rowsAgreeOn_historyEventPropagator (capacity : Locus → ℕ) (A : Finset Locus)
    {first second : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme)}
    (h : List.Forall₂ (EventAgreeOn A capacity) first second) :
    RowsAgreeOn A (historyEventPropagator capacity first)
      (historyEventPropagator capacity second) := by
  induction h with
  | nil => exact rowsAgreeOn_refl A _
  | cons hevent _ ih =>
    exact ih.mul (rowsLocal_historyEventPropagator capacity A _)
      (rowsAgreeOn_eventPropagator capacity A _ _ hevent)

/-- **Histories that agree on `A` carry vectors equal over `A` to vectors equal over `A`.**

Assumes: the histories agree on `A` event by event (`h`), and the vectors agree over `A` (`hv`). -/
theorem historyEventPropagator_mulVec_eq_of_agreeOn (capacity : Locus → ℕ) (A : Finset Locus)
    {first second : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme)}
    (h : List.Forall₂ (EventAgreeOn A capacity) first second)
    {v v' : BudgetConfiguration Deme Locus Allele capacity → ℝ}
    (hv : ∀ ξ : BudgetConfiguration Deme Locus Allele capacity, LociWithin A ξ.1 → v ξ = v' ξ)
    {ξ : BudgetConfiguration Deme Locus Allele capacity} (hξ : LociWithin A ξ.1) :
    (historyEventPropagator capacity first *ᵥ v) ξ =
      (historyEventPropagator capacity second *ᵥ v') ξ :=
  mulVec_eq_of_rowsAgreeOn (rowsLocal_historyEventPropagator capacity A first)
    (rowsAgreeOn_historyEventPropagator capacity A h) hv hξ

/-- **Exact locality along a whole history.** For two histories of epochs, splits and pulses that
agree on `A` event by event, started at states with equal configuration moments over `A`, the
expected configuration moments at the end of the history agree at every configuration over `A`.

Assumes: the histories agree on `A` event by event (`h`), and the initial states have equal
configuration moments over `A` (`hx`). -/
theorem integral_momentPolynomial_historyEventKernel_eq_of_agreeOn (ℓ₀ : Locus)
    (hap₀ : FullHaplotype Locus Allele) (capacity : Locus → ℕ) (A : Finset Locus)
    {first second : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme)}
    (h : List.Forall₂ (EventAgreeOn A capacity) first second)
    {x₁ x₂ : FrequencyState Deme Locus Allele}
    (hx : ∀ ξ : BudgetConfiguration Deme Locus Allele capacity, LociWithin A ξ.1 →
      budgetMomentFeature capacity x₁ ξ = budgetMomentFeature capacity x₂ ξ)
    {ξ : BudgetConfiguration Deme Locus Allele capacity} (hξ : LociWithin A ξ.1) :
    ∫ y, polynomialFunction (momentPolynomial ξ.1) y ∂(historyEventKernel ℓ₀ hap₀ first x₁) =
      ∫ y, polynomialFunction (momentPolynomial ξ.1) y ∂(historyEventKernel ℓ₀ hap₀ second x₂) := by
  rw [integral_momentPolynomial_historyEventKernel ℓ₀ hap₀ capacity first x₁ ξ,
    integral_momentPolynomial_historyEventKernel ℓ₀ hap₀ capacity second x₂ ξ]
  exact historyEventPropagator_mulVec_eq_of_agreeOn capacity A h hx hξ

/-! ### Polynomials that read only the loci of `A` -/

/-- **A function of full haplotypes reads only the alleles at `A`.** -/
def ReadsLoci (A : Finset Locus) (f : FullHaplotype Locus Allele → ℝ) : Prop :=
  ∀ h h' : FullHaplotype Locus Allele, (∀ ℓ ∈ A, h ℓ = h' ℓ) → f h = f h'

/-- A constant reads no alleles. -/
theorem readsLoci_const (A : Finset Locus) (c : ℝ) :
    ReadsLoci A fun _ : FullHaplotype Locus Allele ↦ c :=
  fun _ _ _ ↦ rfl

/-- A function of the allele at one locus of `A` reads only the alleles at `A`. -/
theorem readsLoci_eval {A : Finset Locus} {ℓ₀ : Locus} (hℓ₀ : ℓ₀ ∈ A) (g : Allele ℓ₀ → ℝ) :
    ReadsLoci A fun hap : FullHaplotype Locus Allele ↦ g (hap ℓ₀) :=
  fun _ _ hh ↦ congrArg g (hh ℓ₀ hℓ₀)

/-- The polynomials spanned by the configuration moments of at most `k` carriers over `A`. -/
def localMomentSpan (A : Finset Locus) (k : ℕ) :
    Submodule ℝ (FrequencyPolynomial Deme Locus Allele) :=
  Submodule.span ℝ {p | ∃ ξ : Multiset (PartialType Deme Locus Allele),
    LociWithin A ξ ∧ Multiset.card ξ ≤ k ∧ momentPolynomial ξ = p}

/-- The moment of a configuration of at most `k` carriers over `A` lies in the local span. -/
theorem momentPolynomial_mem_localMomentSpan {A : Finset Locus} {k : ℕ}
    {ξ : Multiset (PartialType Deme Locus Allele)} (hξ : LociWithin A ξ)
    (hcard : Multiset.card ξ ≤ k) : momentPolynomial ξ ∈ localMomentSpan A k := by
  rw [localMomentSpan]
  exact Submodule.mem_span_of_mem ⟨ξ, hξ, hcard, rfl⟩

/-- The moment of a sum of configurations is the product of their moments. -/
theorem momentPolynomial_add (ξ ζ : Multiset (PartialType Deme Locus Allele)) :
    momentPolynomial (ξ + ζ) = momentPolynomial ξ * momentPolynomial ζ := by
  simp only [momentPolynomial, Multiset.map_add, Multiset.prod_add]

/-- The local moment spans grow with the number of carriers. -/
theorem localMomentSpan_mono {A : Finset Locus} {j k : ℕ} (hjk : j ≤ k) :
    localMomentSpan (Deme := Deme) (Allele := Allele) A j ≤ localMomentSpan A k :=
  Submodule.span_mono fun _ ⟨ξ, hξ, hcard, hp⟩ ↦ ⟨ξ, hξ, hcard.trans hjk, hp⟩

/-- **Products of local moment polynomials are local.** -/
theorem mul_mem_localMomentSpan {A : Finset Locus} {j k : ℕ}
    {p q : FrequencyPolynomial Deme Locus Allele} (hp : p ∈ localMomentSpan A j)
    (hq : q ∈ localMomentSpan A k) : p * q ∈ localMomentSpan A (j + k) := by
  have h := Submodule.mul_mem_mul hp hq
  rw [localMomentSpan, localMomentSpan, Submodule.span_mul_span] at h
  rw [localMomentSpan]
  refine Submodule.span_mono ?_ h
  rintro _ ⟨_, ⟨ξ, hξ, hcard, rfl⟩, _, ⟨ζ, hζ, hcard', rfl⟩, rfl⟩
  exact ⟨ξ + ζ, lociWithin_add.mpr ⟨hξ, hζ⟩, by rw [Multiset.card_add]; omega,
    momentPolynomial_add ξ ζ⟩

/-- The carrier that records the alleles of a full haplotype at the loci of `A`, in one deme. -/
def localType (deme : Deme) {A : Finset Locus} (hA : A.Nonempty)
    (h : FullHaplotype Locus Allele) : PartialType Deme Locus Allele where
  deme := deme
  allele := fun ℓ ↦ if ℓ ∈ A then some (h ℓ) else none
  retained := by
    obtain ⟨ℓ, hℓ⟩ := hA
    exact ⟨ℓ, by simp [hℓ]⟩

/-- The carrier of a haplotype at `A` retains only loci of `A`. -/
theorem lociWithin_localType (deme : Deme) {A : Finset Locus} (hA : A.Nonempty)
    (h : FullHaplotype Locus Allele) : LociWithin A {localType deme hA h} := by
  intro τ hτ ℓ hℓ
  rw [Multiset.mem_singleton] at hτ
  subst hτ
  by_contra hnot
  simp [localType, hnot] at hℓ

/-- A haplotype satisfies the carrier of another haplotype at `A` when the two agree at `A`. -/
theorem satisfies_localType_iff (deme : Deme) {A : Finset Locus} (hA : A.Nonempty)
    (h h' : FullHaplotype Locus Allele) :
    Satisfies (localType deme hA h).allele h' ↔ ∀ ℓ ∈ A, h' ℓ = h ℓ := by
  constructor
  · intro hs ℓ hℓ
    rcases hs ℓ with hnone | hsome
    · simp [localType, hℓ] at hnone
    · have hval : some (h ℓ) = some (h' ℓ) := by
        simpa only [localType, if_pos hℓ] using hsome
      exact (Option.some.inj hval).symm
  · intro hagree ℓ
    by_cases hℓ : ℓ ∈ A
    · right
      simp only [localType, if_pos hℓ, hagree ℓ hℓ]
    · left
      simp only [localType, if_neg hℓ]

/-- **The expectation of a function of the alleles at `A` is a local moment polynomial**: grouped
by their alleles at `A`, the haplotype frequencies sum to one-carrier marginal frequencies over
`A`. -/
theorem expectation_mem_localMomentSpan (deme : Deme) {A : Finset Locus} (hA : A.Nonempty)
    {f : FullHaplotype Locus Allele → ℝ} (hf : ReadsLoci A f) :
    rename (fun hap ↦ (deme, hap)) (expectationPolynomial f) ∈ localMomentSpan A 1 := by
  classical
  simp only [expectationPolynomial, map_sum, map_mul, rename_C, rename_X]
  rw [← Finset.sum_fiberwise_of_maps_to
    (fun hap _ ↦ Finset.mem_image_of_mem (localType deme hA) (Finset.mem_univ hap))]
  refine (localMomentSpan A 1).sum_mem fun t ht ↦ ?_
  obtain ⟨h₀, _, rfl⟩ := Finset.mem_image.mp ht
  have hfiber : ∀ hap, localType deme hA hap = localType deme hA h₀ ↔
      ∀ ℓ ∈ A, hap ℓ = h₀ ℓ := by
    intro hap
    constructor
    · intro heq ℓ hℓ
      have hallele := congrFun (congrArg PartialType.allele heq) ℓ
      have hval : some (hap ℓ) = some (h₀ ℓ) := by
        simpa only [localType, if_pos hℓ] using hallele
      exact Option.some.inj hval
    · intro hagree
      refine PartialType.eq_of_fields rfl (funext fun ℓ ↦ ?_)
      by_cases hℓ : ℓ ∈ A
      · simp only [localType, if_pos hℓ, hagree ℓ hℓ]
      · simp only [localType, if_neg hℓ]
  have hvalue : ∀ hap ∈ Finset.univ.filter
      fun hap ↦ localType deme hA hap = localType deme hA h₀,
      (C (f hap) * X (deme, hap) : FrequencyPolynomial Deme Locus Allele) =
        C (f h₀) * X (deme, hap) := by
    intro hap hhap
    rw [hf hap h₀ ((hfiber hap).mp (Finset.mem_filter.mp hhap).2)]
  have hmarginal : ∑ hap ∈ Finset.univ.filter
      fun hap ↦ localType deme hA hap = localType deme hA h₀,
        (X (deme, hap) : FrequencyPolynomial Deme Locus Allele) =
      momentPolynomial {localType deme hA h₀} := by
    rw [momentPolynomial_singleton, marginalPolynomial, assignmentPolynomial]
    refine Finset.sum_congr (Finset.filter_congr fun hap _ ↦ ?_) fun _ _ ↦ rfl
    rw [hfiber, satisfies_localType_iff]
  rw [Finset.sum_congr rfl hvalue, ← Finset.mul_sum, hmarginal, MvPolynomial.C_mul']
  exact (localMomentSpan A 1).smul_mem (f h₀)
    (momentPolynomial_mem_localMomentSpan (lociWithin_localType deme hA h₀) (by simp))

/-- The covariance polynomial of two functions of the alleles at `A` is local, of two carriers. -/
theorem covariance_mem_localMomentSpan (deme : Deme) {A : Finset Locus} (hA : A.Nonempty)
    {f g : FullHaplotype Locus Allele → ℝ} (hf : ReadsLoci A f) (hg : ReadsLoci A g) :
    rename (fun hap ↦ (deme, hap)) (covariancePolynomial f g) ∈ localMomentSpan A 2 := by
  have hfg : ReadsLoci A fun hap ↦ f hap * g hap := fun h h' hh ↦ by
    show f h * g h = f h' * g h'
    rw [hf h h' hh, hg h h' hh]
  rw [covariancePolynomial, map_sub, map_mul]
  exact (localMomentSpan A 2).sub_mem
    (localMomentSpan_mono (by norm_num) (expectation_mem_localMomentSpan deme hA hfg))
    (mul_mem_localMomentSpan (expectation_mem_localMomentSpan deme hA hf)
      (expectation_mem_localMomentSpan deme hA hg))

/-- **The correlation numerator of a score and outcome that read only `A` is local**, of at most
four carriers over `A`. -/
theorem numeratorPolynomial_mem_localMomentSpan (deme : Deme) {A : Finset Locus}
    (hA : A.Nonempty) {score outcome : FullHaplotype Locus Allele → ℝ}
    (hS : ReadsLoci A score) (hY : ReadsLoci A outcome) :
    numeratorPolynomial deme score outcome ∈ localMomentSpan A 4 := by
  have hcov := covariance_mem_localMomentSpan deme hA hS hY
  rw [numeratorPolynomial, demePolynomial, correlationNumeratorPolynomial, map_mul, rename_C,
    map_pow, pow_two, MvPolynomial.C_mul']
  exact (localMomentSpan A 4).smul_mem 16 (mul_mem_localMomentSpan hcov hcov)

/-- **The correlation denominator of a score and outcome that read only `A` is local**, of at most
four carriers over `A`. -/
theorem denominatorPolynomial_mem_localMomentSpan (deme : Deme) {A : Finset Locus}
    (hA : A.Nonempty) {score outcome : FullHaplotype Locus Allele → ℝ}
    (hS : ReadsLoci A score) (hY : ReadsLoci A outcome) :
    denominatorPolynomial deme score outcome ∈ localMomentSpan A 4 := by
  rw [denominatorPolynomial, demePolynomial, correlationDenominatorPolynomial, map_mul, rename_C,
    map_mul, MvPolynomial.C_mul']
  exact (localMomentSpan A 4).smul_mem 16
    (mul_mem_localMomentSpan (covariance_mem_localMomentSpan deme hA hS hS)
      (covariance_mem_localMomentSpan deme hA hY hY))

/-- **Measures with equal local moments integrate local polynomials equally.**

Assumes: the two finite measures integrate the moments of at most `k` carriers over `A` equally
(`hmoment`). -/
theorem integral_eq_of_mem_localMomentSpan {A : Finset Locus} {k : ℕ}
    (μ₁ μ₂ : Measure (FrequencyState Deme Locus Allele)) [IsFiniteMeasure μ₁]
    [IsFiniteMeasure μ₂]
    (hmoment : ∀ ξ : Multiset (PartialType Deme Locus Allele), LociWithin A ξ →
      Multiset.card ξ ≤ k →
        ∫ y, polynomialFunction (momentPolynomial ξ) y ∂μ₁ =
          ∫ y, polynomialFunction (momentPolynomial ξ) y ∂μ₂)
    {p : FrequencyPolynomial Deme Locus Allele} (hp : p ∈ localMomentSpan A k) :
    ∫ y, polynomialFunction p y ∂μ₁ = ∫ y, polynomialFunction p y ∂μ₂ := by
  have hint : ∀ (μ : Measure (FrequencyState Deme Locus Allele)) [IsFiniteMeasure μ]
      (q : FrequencyPolynomial Deme Locus Allele), Integrable (fun y ↦ eval y.1 q) μ := by
    intro μ _ q
    exact (BoundedContinuousFunction.mkOfCompact (polynomialFunction q)).integrable μ
  rw [localMomentSpan] at hp
  induction hp using Submodule.span_induction with
  | mem q hq =>
    obtain ⟨ξ, hξ, hcard, rfl⟩ := hq
    exact hmoment ξ hξ hcard
  | zero => simp only [polynomialFunction_apply, map_zero, integral_zero]
  | add q r _ _ hq hr =>
    simp only [polynomialFunction_apply, map_add] at hq hr ⊢
    rw [integral_add (hint μ₁ q) (hint μ₁ r), integral_add (hint μ₂ q) (hint μ₂ r), hq, hr]
  | smul c q _ hq =>
    simp only [polynomialFunction_apply, smul_eq_C_mul, map_mul, eval_C, integral_const_mul]
      at hq ⊢
    rw [hq]

/-- **End-to-end portability sees only the loci of the score.** For a score and an outcome that
read only a nonempty set of loci `A`, two histories of epochs, splits and pulses that agree on `A`
event by event, from states with equal budget-4 configuration moments over `A`, have equal expected
portability between every source and target.

Assumes: `A` is nonempty (`hA`), the histories agree on `A` event by event (`h`), the initial
budget-4 moments over `A` agree (`hx`), and the score and outcome read only `A` (`hS`, `hY`). -/
theorem expectedPortability_eq_of_agreeOn (ℓ₀ : Locus) (hap₀ : FullHaplotype Locus Allele)
    {A : Finset Locus} (hA : A.Nonempty)
    {first second : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme)}
    (h : List.Forall₂ (EventAgreeOn A (fun _ ↦ 4)) first second)
    {x₁ x₂ : FrequencyState Deme Locus Allele}
    (hx : ∀ ξ : BudgetConfiguration Deme Locus Allele (fun _ ↦ 4), LociWithin A ξ.1 →
      budgetMomentFeature (fun _ ↦ 4) x₁ ξ = budgetMomentFeature (fun _ ↦ 4) x₂ ξ)
    (source target : Deme) {score outcome : FullHaplotype Locus Allele → ℝ}
    (hS : ReadsLoci A score) (hY : ReadsLoci A outcome) :
    expectedPortability (historyEventKernel ℓ₀ hap₀ first) x₁ source target score outcome =
      expectedPortability (historyEventKernel ℓ₀ hap₀ second) x₂ source target score outcome := by
  haveI := isMarkovKernel_historyEventKernel ℓ₀ hap₀ first
  haveI := isMarkovKernel_historyEventKernel ℓ₀ hap₀ second
  have hmoment : ∀ ξ : Multiset (PartialType Deme Locus Allele), LociWithin A ξ →
      Multiset.card ξ ≤ 4 →
        ∫ y, polynomialFunction (momentPolynomial ξ) y ∂(historyEventKernel ℓ₀ hap₀ first x₁) =
          ∫ y, polynomialFunction (momentPolynomial ξ) y
            ∂(historyEventKernel ℓ₀ hap₀ second x₂) := by
    intro ξ hξ hcard
    have hbudget : WithinBudget (fun _ ↦ 4) ξ := fun _ ↦ (Multiset.countP_le_card ξ).trans hcard
    exact integral_momentPolynomial_historyEventKernel_eq_of_agreeOn ℓ₀ hap₀ (fun _ ↦ 4) A h hx
      (ξ := ⟨ξ, hbudget⟩) hξ
  have hpoly : ∀ p ∈ localMomentSpan A 4,
      ∫ y, polynomialFunction p y ∂(historyEventKernel ℓ₀ hap₀ first x₁) =
        ∫ y, polynomialFunction p y ∂(historyEventKernel ℓ₀ hap₀ second x₂) :=
    fun p hp ↦ integral_eq_of_mem_localMomentSpan _ _ hmoment hp
  simp only [expectedPortability, ← polynomialFunction_numeratorPolynomial,
    ← polynomialFunction_denominatorPolynomial]
  rw [hpoly _ (numeratorPolynomial_mem_localMomentSpan target hA hS hY),
    hpoly _ (denominatorPolynomial_mem_localMomentSpan source hA hS hY),
    hpoly _ (denominatorPolynomial_mem_localMomentSpan target hA hS hY),
    hpoly _ (numeratorPolynomial_mem_localMomentSpan source hA hS hY)]

end

end Descent.Portability.HistoryExactLocality
