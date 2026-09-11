/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.FellerMarkovKernel
import Descent.Portability.PartialHaplotypeDualSemigroup
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Topology.Algebra.MvPolynomial

assert_below Descent.Decision Descent.Program

/-!
# The neutral Feller semigroup has the neutral diffusion generator

This module connects the operator construction of NOTE1 §4.2a (`PolynomialFellerExtension`,
`FellerKernelRepresentation`, `FellerMarkovKernel`) with the generator identity (19) and the
dual likelihood representation (20) (`PartialHaplotypeDualGenerator`,
`PartialHaplotypeDualSemigroup`).

The state space. `frequencySimplex Deme Locus Allele` is the set of multi-deme haplotype
frequency vectors that are nonnegative and sum to one in every deme, and `FrequencyState` is
its subtype. It is compact (`isCompact_frequencySimplex`), so it carries the Feller
construction, and every state is the frequency point of per-deme haplotype laws
(`lawPoint_stateLaw`). `polynomialFunction p` reads a frequency polynomial as a continuous
observable; these observables form the subalgebra `polynomialAlgebra`, which separates states
(`polynomialAlgebra_separatesPoints`) and is therefore dense (`dense_polynomialSubspace`).

The generator identification. On states, the neutral generator applied to a budget-respecting
configuration moment is the dual generator applied to the vector of configuration moments
(`polynomialFunction_neutralGenerator_momentPolynomial`, NOTE1 (19) in matrix form). Take any
family of Markov kernels on the state space whose configuration moments evolve by the dual
semigroup, `∫ H_ξ dK_t(x, ·) = (e^{tQ} H(x))_ξ` as in NOTE1 (20). Then its generator on
configuration moments is the neutral diffusion generator,
`d/dt ∫ H_ξ dK_t(x, ·) = ∫ (neutralGenerator H_ξ) dK_t(x, ·)` at every time, state and
configuration, with a right derivative at time zero
(`hasDerivWithinAt_integral_momentPolynomial`). The proof differentiates the matrix exponential
and moves the finite dual sum through the integral. `exists_markovKernel_neutralGenerator`
assembles NOTE1 §4.2a in this form: from a positive, constant-preserving semigroup of linear
operators on polynomial observables whose action on configuration moments is the dual
semigroup, `FellerMarkovKernel` constructs Markov kernels that represent it, compose by
`K_{s+t} = K_t ∘ₖ K_s`, and have the neutral generator on configuration moments.

Scope. The polynomial semigroup is a hypothesis: its positivity, and its existence as a linear
operator on functions agreeing with `e^{tQ}` on configuration moments, are not constructed here.
The note derives positivity from the microscopic physical kernels through the Euler limit of
`markov_of_euler_tendstoUniformly`; those kernels are formalized for the two-locus low-order
moments (`TwoLocusMicroscopicApproximation`), not for arbitrary partial-haplotype
configurations. The converse direction, that the forward moment equation forces the dual
representation, is `PartialHaplotypeDualSemigroup.expectedMomentVector_eq_matrixExponential`
for expectation functionals over finitely supported laws. The generator is identified on
configuration moments; that they span all polynomial observables is not proved here.

## Empirical status

None. The bodies here are analysis: derivatives of a matrix exponential and integrals of
polynomial observables against kernels built from a supplied operator, so no measurement on
any population could bear on one.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.NeutralFellerGenerator

open MeasureTheory Filter Topology ProbabilityTheory MvPolynomial
open scoped NNReal
open Descent.Coalescent PartialHaplotypeCarrier PartialHaplotypeDualGenerator
  PartialHaplotypeDualSemigroup PolynomialFellerExtension FellerMarkovKernel

noncomputable section

/-- The state space of the neutral diffusion: multi-deme haplotype frequency vectors that are
nonnegative and sum to one in every deme. -/
def frequencySimplex (Deme Locus : Type*) (Allele : Locus → Type*) [Fintype Locus]
    [DecidableEq Locus] [∀ ℓ, Fintype (Allele ℓ)] :
    Set (FrequencyVariable Deme Locus Allele → ℝ) :=
  {x | (∀ c, 0 ≤ x c) ∧ ∀ i, ∑ hap, x (i, hap) = 1}

/-- The state space of the neutral diffusion as a type. -/
abbrev FrequencyState (Deme Locus : Type*) (Allele : Locus → Type*) [Fintype Locus]
    [DecidableEq Locus] [∀ ℓ, Fintype (Allele ℓ)] :=
  ↥(frequencySimplex Deme Locus Allele)

section Topology

variable {Deme Locus : Type*} {Allele : Locus → Type*} [Fintype Locus] [DecidableEq Locus]
  [∀ ℓ, Fintype (Allele ℓ)]

/-- The state space is compact: it is a closed subset of the unit cube. -/
theorem isCompact_frequencySimplex : IsCompact (frequencySimplex Deme Locus Allele) := by
  have hclosed : IsClosed (frequencySimplex Deme Locus Allele) := by
    have hset : frequencySimplex Deme Locus Allele
        = (⋂ c, {x : FrequencyVariable Deme Locus Allele → ℝ | 0 ≤ x c})
          ∩ ⋂ i, {x : FrequencyVariable Deme Locus Allele → ℝ | ∑ hap, x (i, hap) = 1} := by
      ext x
      simp only [frequencySimplex, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
    rw [hset]
    exact (isClosed_iInter fun c ↦ isClosed_le continuous_const (continuous_apply c)).inter
      (isClosed_iInter fun i ↦ isClosed_eq
        (continuous_finset_sum _ fun hap _ ↦ continuous_apply (i, hap)) continuous_const)
  refine (isCompact_univ_pi fun _ ↦ isCompact_Icc (a := (0 : ℝ)) (b := 1)).of_isClosed_subset
    hclosed fun x hx ↦ Set.mem_univ_pi.mpr fun c ↦ ⟨hx.1 c, ?_⟩
  calc x c = x (c.1, c.2) := rfl
    _ ≤ ∑ hap, x (c.1, hap) :=
        Finset.single_le_sum (fun hap _ ↦ hx.1 (c.1, hap)) (Finset.mem_univ c.2)
    _ = 1 := hx.2 c.1

/-- The state space of the neutral diffusion is a compact space. -/
instance compactSpace_frequencyState : CompactSpace (FrequencyState Deme Locus Allele) :=
  isCompact_iff_compactSpace.mp isCompact_frequencySimplex

end Topology

variable {Deme Locus : Type*} {Allele : Locus → Type*}
variable [Fintype Deme] [DecidableEq Deme] [Fintype Locus] [DecidableEq Locus]
  [∀ ℓ, Fintype (Allele ℓ)] [∀ ℓ, DecidableEq (Allele ℓ)]

/-- The per-deme haplotype laws of a state: the haplotype frequencies of each deme. -/
def stateLaw (x : FrequencyState Deme Locus Allele) (i : Deme) :
    FiniteReportLaw (FullHaplotype Locus Allele) where
  mass hap := x.1 (i, hap)
  mass_nonneg hap := x.2.1 (i, hap)
  mass_sum := x.2.2 i

/-- Every state is the frequency point of its per-deme haplotype laws. -/
theorem lawPoint_stateLaw (x : FrequencyState Deme Locus Allele) :
    lawPoint (stateLaw x) = x.1 :=
  rfl

/-- A frequency polynomial read as a continuous observable of the state. -/
def polynomialFunction (p : FrequencyPolynomial Deme Locus Allele) :
    C(FrequencyState Deme Locus Allele, ℝ) where
  toFun x := eval x.1 p
  continuous_toFun := (MvPolynomial.continuous_eval p).comp continuous_subtype_val

/-- A polynomial observable evaluates its polynomial at the frequency vector of the state. -/
theorem polynomialFunction_apply (p : FrequencyPolynomial Deme Locus Allele)
    (x : FrequencyState Deme Locus Allele) : polynomialFunction p x = eval x.1 p :=
  rfl

/-- The polynomial observables of the state form a subalgebra of the continuous observables. -/
def polynomialAlgebra : Subalgebra ℝ C(FrequencyState Deme Locus Allele, ℝ) where
  carrier := Set.range polynomialFunction
  mul_mem' := by
    rintro _ _ ⟨p, rfl⟩ ⟨q, rfl⟩
    exact ⟨p * q, ContinuousMap.ext fun x ↦ by simp [polynomialFunction_apply]⟩
  add_mem' := by
    rintro _ _ ⟨p, rfl⟩ ⟨q, rfl⟩
    exact ⟨p + q, ContinuousMap.ext fun x ↦ by simp [polynomialFunction_apply]⟩
  algebraMap_mem' r := ⟨C r, ContinuousMap.ext fun x ↦ by simp [polynomialFunction_apply]⟩

/-- The polynomial observables as a subspace of the continuous observables. -/
abbrev PolynomialSubspace (Deme Locus : Type*) (Allele : Locus → Type*) [Fintype Deme]
    [DecidableEq Deme] [Fintype Locus] [DecidableEq Locus] [∀ ℓ, Fintype (Allele ℓ)]
    [∀ ℓ, DecidableEq (Allele ℓ)] : Submodule ℝ C(FrequencyState Deme Locus Allele, ℝ) :=
  Subalgebra.toSubmodule polynomialAlgebra

/-- Every polynomial observable lies in the polynomial subspace. -/
theorem polynomialFunction_mem (p : FrequencyPolynomial Deme Locus Allele) :
    polynomialFunction p ∈ PolynomialSubspace Deme Locus Allele :=
  Set.mem_range_self p

/-- The constant observable one is polynomial. -/
theorem one_mem_polynomialSubspace :
    (1 : C(FrequencyState Deme Locus Allele, ℝ)) ∈ PolynomialSubspace Deme Locus Allele :=
  Subalgebra.one_mem _

/-- The polynomial observables separate states: two distinct states differ in some haplotype
frequency, and that frequency is a coordinate polynomial. -/
theorem polynomialAlgebra_separatesPoints :
    (polynomialAlgebra (Deme := Deme) (Locus := Locus) (Allele := Allele)).SeparatesPoints := by
  intro x y hxy
  have hex : ∃ c, x.1 c ≠ y.1 c := by
    by_contra hc
    push_neg at hc
    exact hxy (Subtype.ext (funext hc))
  obtain ⟨c, hc⟩ := hex
  refine ⟨_, ⟨polynomialFunction (X c), Set.mem_range_self (X c), rfl⟩, ?_⟩
  simpa only [polynomialFunction_apply, eval_X] using hc

/-- The polynomial observables are dense in the continuous observables, by Stone–Weierstrass. -/
theorem dense_polynomialSubspace :
    Dense (PolynomialSubspace Deme Locus Allele : Set C(FrequencyState Deme Locus Allele, ℝ)) :=
  dense_toSubmodule_of_separatesPoints _ polynomialAlgebra_separatesPoints

/-- **NOTE1 (19) on states, in matrix form.** The neutral generator applied to a
budget-respecting configuration moment is the dual generator applied to the vector of
configuration moments of the state. -/
theorem polynomialFunction_neutralGenerator_momentPolynomial
    (rates : NeutralRates Deme Locus Allele) (capacity : Locus → ℕ)
    (ξ : BudgetConfiguration Deme Locus Allele capacity) (x : FrequencyState Deme Locus Allele) :
    polynomialFunction (neutralGenerator rates (momentPolynomial ξ.1)) x
      = (dualGenerator rates capacity).mulVec
          (fun η ↦ polynomialFunction (momentPolynomial η.1) x) ξ := by
  have h := dualGenerator_mulVec_configurationMoment rates capacity (stateLaw x) ξ
  simp only [← eval_momentPolynomial, lawPoint_stateLaw] at h
  exact h.symm

/-- **The generator of the neutral Feller semigroup on configuration moments.** For Markov
kernels on the state space whose configuration moments evolve by the dual semigroup,
`∫ H_ξ dK_t(x, ·) = (e^{tQ} H(x))_ξ` as in NOTE1 (20), the time derivative of the expected
configuration moment is the expected neutral generator of the moment polynomial (NOTE1 (19)):
`d/dt ∫ H_ξ dK_t(x, ·) = ∫ (neutralGenerator H_ξ) dK_t(x, ·)`, a right derivative at time
zero. -/
theorem hasDerivWithinAt_integral_momentPolynomial (rates : NeutralRates Deme Locus Allele)
    (capacity : Locus → ℕ)
    (K : ℝ≥0 → Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele))
    [∀ t, IsMarkovKernel (K t)]
    (hmoment : ∀ (t : ℝ≥0) (x : FrequencyState Deme Locus Allele)
      (ξ : BudgetConfiguration Deme Locus Allele capacity),
      ∫ y, polynomialFunction (momentPolynomial ξ.1) y ∂(K t x)
        = (matrixExponential (dualGenerator rates capacity) t).mulVec
            (fun η ↦ polynomialFunction (momentPolynomial η.1) x) ξ)
    (t : ℝ≥0) (x : FrequencyState Deme Locus Allele)
    (ξ : BudgetConfiguration Deme Locus Allele capacity) :
    HasDerivWithinAt
      (fun s : ℝ ↦ ∫ y, polynomialFunction (momentPolynomial ξ.1) y ∂(K s.toNNReal x))
      (∫ y, polynomialFunction (neutralGenerator rates (momentPolynomial ξ.1)) y ∂(K t x))
      (Set.Ici 0) t := by
  have hint : ∀ η : BudgetConfiguration Deme Locus Allele capacity,
      Integrable (polynomialFunction (momentPolynomial η.1)) (K t x) := fun η ↦
    (BoundedContinuousFunction.mkOfCompact (polynomialFunction (momentPolynomial η.1))).integrable
      _
  have hgen :
      ∫ y, polynomialFunction (neutralGenerator rates (momentPolynomial ξ.1)) y ∂(K t x)
        = (dualGenerator rates capacity).mulVec
            ((matrixExponential (dualGenerator rates capacity) t).mulVec
              (fun η ↦ polynomialFunction (momentPolynomial η.1) x)) ξ := by
    calc ∫ y, polynomialFunction (neutralGenerator rates (momentPolynomial ξ.1)) y ∂(K t x)
        = ∫ y, ∑ η, dualGenerator rates capacity ξ η
            * polynomialFunction (momentPolynomial η.1) y ∂(K t x) := by
          congr 1
          funext y
          exact polynomialFunction_neutralGenerator_momentPolynomial rates capacity ξ y
      _ = ∑ η, dualGenerator rates capacity ξ η
            * ∫ y, polynomialFunction (momentPolynomial η.1) y ∂(K t x) := by
          rw [integral_finset_sum Finset.univ
            fun η _ ↦ (hint η).const_mul (dualGenerator rates capacity ξ η)]
          simp only [integral_const_mul]
      _ = _ := by
          simp only [hmoment, Matrix.mulVec, dotProduct]
  have hderiv := hasDerivAt_pi.mp
    (StationaryHaplotypeRealization.hasDerivAt_matrixExponential_mulVec
      (dualGenerator rates capacity) (fun η ↦ polynomialFunction (momentPolynomial η.1) x) t) ξ
  rw [hgen]
  refine hderiv.hasDerivWithinAt.congr (fun s hs ↦ ?_) ?_
  · rw [hmoment, Real.coe_toNNReal s hs]
  · rw [hmoment, Real.coe_toNNReal _ (NNReal.coe_nonneg t)]

/-- **NOTE1 §4.2a with the generator identified.** A positive, constant-preserving semigroup
of linear operators on the polynomial observables whose action on budget-respecting
configuration moments is the dual semigroup `e^{tQ}` of NOTE1 (20) is integration against
Markov kernels that compose by `K_{s+t} = K_t ∘ₖ K_s` and whose generator on configuration
moments is the neutral diffusion generator of NOTE1 (19). -/
theorem exists_markovKernel_neutralGenerator (rates : NeutralRates Deme Locus Allele)
    (capacity : Locus → ℕ)
    (T : ℝ≥0 → PolynomialSubspace Deme Locus Allele →ₗ[ℝ] PolynomialSubspace Deme Locus Allele)
    (hT1 : ∀ t, (T t ⟨1, one_mem_polynomialSubspace⟩ : C(FrequencyState Deme Locus Allele, ℝ))
      = 1)
    (hpos : ∀ t (f : PolynomialSubspace Deme Locus Allele),
      0 ≤ (f : C(FrequencyState Deme Locus Allele, ℝ))
        → 0 ≤ (T t f : C(FrequencyState Deme Locus Allele, ℝ)))
    (hsemi : ∀ s t, T (s + t) = T s ∘ₗ T t)
    (hdual : ∀ (t : ℝ≥0) (ξ : BudgetConfiguration Deme Locus Allele capacity)
      (x : FrequencyState Deme Locus Allele),
      (T t ⟨polynomialFunction (momentPolynomial ξ.1), polynomialFunction_mem _⟩ :
          C(FrequencyState Deme Locus Allele, ℝ)) x
        = (matrixExponential (dualGenerator rates capacity) t).mulVec
            (fun η ↦ polynomialFunction (momentPolynomial η.1) x) ξ) :
    ∃ K : ℝ≥0 → Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele),
      (∀ t, IsMarkovKernel (K t)) ∧
      (∀ t x (f : PolynomialSubspace Deme Locus Allele),
        ∫ y, (f : C(FrequencyState Deme Locus Allele, ℝ)) y ∂(K t x)
          = (T t f : C(FrequencyState Deme Locus Allele, ℝ)) x) ∧
      (∀ s t, K (s + t) = K t ∘ₖ K s) ∧
      ∀ t x (ξ : BudgetConfiguration Deme Locus Allele capacity),
        HasDerivWithinAt
          (fun s : ℝ ↦ ∫ y, polynomialFunction (momentPolynomial ξ.1) y ∂(K s.toNNReal x))
          (∫ y, polynomialFunction (neutralGenerator rates (momentPolynomial ξ.1)) y ∂(K t x))
          (Set.Ici 0) t := by
  obtain ⟨K, hK, hrep, hsg⟩ := exists_markovKernel_semigroup _ dense_polynomialSubspace
    one_mem_polynomialSubspace T hT1 hpos hsemi
  haveI : ∀ t, IsMarkovKernel (K t) := hK
  exact ⟨K, hK, hrep, hsg, fun t x ξ ↦ hasDerivWithinAt_integral_momentPolynomial rates capacity
    K (fun t x ξ ↦ (hrep t x _).trans (hdual t ξ x)) t x ξ⟩

end

end Descent.Portability.NeutralFellerGenerator
