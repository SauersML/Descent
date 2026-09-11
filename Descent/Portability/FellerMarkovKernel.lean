/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.FellerKernelRepresentation
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.Probability.Kernel.Composition.IntegralCompProd

assert_below Descent.Decision Descent.Program

/-!
# Feller kernels on metrizable compact spaces are Markov kernels

`FellerKernelRepresentation` writes each positive, constant-preserving operator `S` of
`C(X, ℝ)` as integration against the Riesz measures `kernelMeasure S hS x`, continuous in `x`
for the weak topology, but leaves the family as a bare map into measures. This module shows
that when `X` is pseudo-metrizable (the allele-frequency simplex is) the family is a genuine
`ProbabilityTheory.Kernel` satisfying `IsMarkovKernel`, and that a semigroup of operators gives
the Markov semigroup law `K_{s+t} = K_t ∘ₖ K_s`. This is the probability kernel `K_t(x, dy)` of
NOTE1 §4.2a in the standard measurable sense.

The measurability step. For a closed set `F`, `HasOuterApproxClosed` supplies bounded
continuous approximants `apprSeq n` of the indicator of `F`. The kernel integrals of those
approximants are `ENNReal.ofReal` of the continuous functions `S (apprSeq n)`, hence measurable
in the state, and they converge to the mass `K(x, F)` (`measurable_kernelMeasure_of_isClosed`).
Closed sets form a π-system generating the Borel σ-algebra, so `x ↦ K(x, ·)` is measurable for
the Giry σ-algebra (`Measurable.measure_of_isPiSystem_of_isProbabilityMeasure`), and
`markovKernel S hS hS1` is a Markov kernel (`markovKernel_apply`,
`isMarkovKernel_markovKernel`) that integrates continuous observables to `S g x`
(`integral_markovKernel`). For a semigroup of operators `markovKernel_add` proves
`K_{s+t} = K_t ∘ₖ K_s` from Chapman–Kolmogorov (`integral_kernelMeasure_add`) and the uniqueness
of finite Borel measures with equal integrals of bounded continuous functions.
`exists_markovKernel_semigroup` packages NOTE1 §4.2a in this form for a positive,
constant-preserving semigroup on a dense subspace containing the constants.

Scope. Pseudo-metrizability is assumed throughout; for a compact Hausdorff space that is not
pseudo-metrizable neither the measurability argument nor the uniqueness step is formalized.

## Empirical status

None. The bodies here are measure theory: every statement is about measurability or equality
of measures determined by an operator on continuous functions, so no measurement on any
population could bear on one.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.FellerMarkovKernel

open MeasureTheory Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open PolynomialFellerExtension FellerKernelRepresentation

noncomputable section

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
  [TopologicalSpace.PseudoMetrizableSpace X] [MeasurableSpace X] [BorelSpace X]

/-- The kernel mass of a closed set depends measurably on the state: it is the limit of the
integrals of the continuous approximants `apprSeq n` of its indicator, each of which is
`ENNReal.ofReal` of the continuous function `S (apprSeq n)`. -/
theorem measurable_kernelMeasure_of_isClosed (S : C(X, ℝ) →L[ℝ] C(X, ℝ))
    (hS : ∀ g, 0 ≤ g → 0 ≤ S g) (hS1 : S 1 = 1) {F : Set X} (hF : IsClosed F) :
    Measurable fun x ↦ kernelMeasure S hS x F := by
  haveI : ∀ x, IsProbabilityMeasure (kernelMeasure S hS x) := fun x ↦
    isProbabilityMeasure_kernelMeasure S hS hS1 x
  have hmeas : ∀ n,
      Measurable fun x ↦ ∫⁻ y, (hF.apprSeq n y : ℝ≥0∞) ∂(kernelMeasure S hS x) := by
    intro n
    let g : C(X, ℝ) :=
      ⟨fun y ↦ (hF.apprSeq n y : ℝ), NNReal.continuous_coe.comp (hF.apprSeq n).continuous⟩
    have key : (fun x ↦ ∫⁻ y, (hF.apprSeq n y : ℝ≥0∞) ∂(kernelMeasure S hS x))
        = fun x ↦ ENNReal.ofReal (S g x) := by
      funext x
      have hfin := BoundedContinuousFunction.lintegral_lt_top_of_nnreal (kernelMeasure S hS x)
        (hF.apprSeq n)
      rw [← ENNReal.ofReal_toReal hfin.ne,
        BoundedContinuousFunction.toReal_lintegral_coe_eq_integral]
      exact congrArg ENNReal.ofReal (integral_kernelMeasure S hS x g)
    rw [key]
    exact (S g).continuous.measurable.ennreal_ofReal
  exact measurable_of_tendsto_metrizable hmeas
    (tendsto_pi_nhds.mpr fun x ↦ HasOuterApproxClosed.tendsto_lintegral_apprSeq hF _)

/-- The Riesz kernels of a positive operator fixing the constants, as a genuine kernel: the
state map is measurable for the Giry σ-algebra, because closed sets are a π-system generating
the Borel σ-algebra and every closed-set mass is measurable. -/
def markovKernel (S : C(X, ℝ) →L[ℝ] C(X, ℝ)) (hS : ∀ g, 0 ≤ g → 0 ≤ S g) (hS1 : S 1 = 1) :
    Kernel X X where
  toFun := kernelMeasure S hS
  measurable' := by
    haveI : ∀ x, IsProbabilityMeasure (kernelMeasure S hS x) := fun x ↦
      isProbabilityMeasure_kernelMeasure S hS hS1 x
    exact Measurable.measure_of_isPiSystem_of_isProbabilityMeasure
      (BorelSpace.measurable_eq.trans borel_eq_generateFrom_isClosed) isPiSystem_isClosed
      fun F hF ↦ measurable_kernelMeasure_of_isClosed S hS hS1 hF

/-- At every state the Markov kernel is the Riesz measure of the evaluation functional. -/
theorem markovKernel_apply (S : C(X, ℝ) →L[ℝ] C(X, ℝ)) (hS : ∀ g, 0 ≤ g → 0 ≤ S g)
    (hS1 : S 1 = 1) (x : X) : markovKernel S hS hS1 x = kernelMeasure S hS x :=
  rfl

/-- The kernel of a positive operator fixing the constants is a Markov kernel. -/
theorem isMarkovKernel_markovKernel (S : C(X, ℝ) →L[ℝ] C(X, ℝ)) (hS : ∀ g, 0 ≤ g → 0 ≤ S g)
    (hS1 : S 1 = 1) : IsMarkovKernel (markovKernel S hS hS1) :=
  ⟨fun x ↦ isProbabilityMeasure_kernelMeasure S hS hS1 x⟩

/-- Integrating a continuous observable against the Markov kernel at `x` returns `S g x`. -/
theorem integral_markovKernel (S : C(X, ℝ) →L[ℝ] C(X, ℝ)) (hS : ∀ g, 0 ≤ g → 0 ≤ S g)
    (hS1 : S 1 = 1) (x : X) (g : C(X, ℝ)) : ∫ y, g y ∂(markovKernel S hS hS1 x) = S g x :=
  integral_kernelMeasure S hS x g

/-- The Markov semigroup law: the kernels of a semigroup of positive constant-preserving
operators compose, `K_{s+t} = K_t ∘ₖ K_s` (first `K_s`, then `K_t`). Both sides are finite
Borel measures at every state with equal integrals of bounded continuous functions, by
Chapman–Kolmogorov. -/
theorem markovKernel_add (S : ℝ≥0 → C(X, ℝ) →L[ℝ] C(X, ℝ)) (hS : ∀ t g, 0 ≤ g → 0 ≤ S t g)
    (hS1 : ∀ t, S t 1 = 1) (hsemi : ∀ s t, S (s + t) = (S s).comp (S t)) (s t : ℝ≥0) :
    markovKernel (S (s + t)) (hS (s + t)) (hS1 (s + t))
      = markovKernel (S t) (hS t) (hS1 t) ∘ₖ markovKernel (S s) (hS s) (hS1 s) := by
  haveI := isMarkovKernel_markovKernel (S s) (hS s) (hS1 s)
  haveI := isMarkovKernel_markovKernel (S t) (hS t) (hS1 t)
  haveI := isMarkovKernel_markovKernel (S (s + t)) (hS (s + t)) (hS1 (s + t))
  refine DFunLike.ext _ _ fun x ↦ ext_of_forall_integral_eq_of_IsFiniteMeasure fun f ↦ ?_
  rw [Kernel.integral_comp (f.integrable
    ((markovKernel (S t) (hS t) (hS1 t) ∘ₖ markovKernel (S s) (hS s) (hS1 s)) x))]
  exact integral_kernelMeasure_add S hS hsemi s t x f.toContinuousMap

/-- NOTE1 §4.2a, Markov kernel form, on a pseudo-metrizable compact space. A positive,
constant-preserving semigroup of linear operators on a dense subspace of `C(X, ℝ)` containing
the constants is integration against a semigroup of Markov kernels, `K_{s+t} = K_t ∘ₖ K_s`. -/
theorem exists_markovKernel_semigroup (V : Submodule ℝ C(X, ℝ))
    (hV : Dense (V : Set C(X, ℝ))) (h1 : (1 : C(X, ℝ)) ∈ V) (T : ℝ≥0 → V →ₗ[ℝ] V)
    (hT1 : ∀ t, (T t ⟨1, h1⟩ : C(X, ℝ)) = 1)
    (hpos : ∀ t (f : V), 0 ≤ (f : C(X, ℝ)) → 0 ≤ (T t f : C(X, ℝ)))
    (hsemi : ∀ s t, T (s + t) = T s ∘ₗ T t) :
    ∃ K : ℝ≥0 → Kernel X X, (∀ t, IsMarkovKernel (K t)) ∧
      (∀ t x (f : V), ∫ y, (f : C(X, ℝ)) y ∂(K t x) = (T t f : C(X, ℝ)) x) ∧
      ∀ s t, K (s + t) = K t ∘ₖ K s := by
  have hT : ∀ t (f : V), ‖(T t f : C(X, ℝ))‖ ≤ ‖(f : C(X, ℝ))‖ := fun t ↦
    norm_le_of_nonneg_of_map_unit V.subtype (V.subtype ∘ₗ T t) ⟨1, h1⟩ rfl (hT1 t) (hpos t)
  have hS : ∀ t g, 0 ≤ g → 0 ≤ denseExtension V hV (T t) (hT t) g := fun t ↦
    denseExtension_nonneg V hV (T t) (hT t) h1 (hT1 t)
  have hS1 : ∀ t, denseExtension V hV (T t) (hT t) 1 = 1 := fun t ↦
    denseExtension_one V hV (T t) (hT t) h1 (hT1 t)
  refine ⟨fun t ↦ markovKernel (denseExtension V hV (T t) (hT t)) (hS t) (hS1 t),
    fun t ↦ isMarkovKernel_markovKernel _ _ _,
    fun t x f ↦ integral_kernelMeasure_denseExtension V hV h1 (T t) (hT t) (hT1 t) x f,
    fun s t ↦ markovKernel_add (fun t ↦ denseExtension V hV (T t) (hT t)) hS hS1
      (denseExtension_add V hV T hT hsemi) s t⟩

end

end Descent.Portability.FellerMarkovKernel
