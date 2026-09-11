/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.PolynomialFellerExtension
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

assert_below Descent.Decision Descent.Program

/-!
# Feller semigroups on compact spaces integrate against probability kernels

This module proves the representation half of NOTE1 §4.2a: the extended operators of
`PolynomialFellerExtension` are integration against probability kernels `K_t(x, dy)`. For a
positive operator `S` of `C(X, ℝ)` and a state `x`, the functional `g ↦ S g x` is positive and
linear; on a compact space every continuous function has compact support, so the
Riesz–Markov–Kakutani theorem at this Mathlib pin (`RealRMK.rieszMeasure`,
`RealRMK.integral_rieszMeasure`) yields a Borel measure `kernelMeasure S hS x` with
`∫ g d(kernelMeasure S hS x) = S g x` for every continuous `g` (`integral_kernelMeasure`).

What is proved. The kernel is a probability measure when `S` fixes the constant one
(`isProbabilityMeasure_kernelMeasure`, packaged as `kernelProbability`). It is the unique
finite Borel measure representing `g ↦ S g x` when `X` is pseudo-metrizable, which covers the
simplex of haplotype frequencies (`kernelMeasure_eq_of_integral_eq`). It depends continuously
on the state in the topology of weak convergence of probability measures
(`continuous_kernelProbability`), which is the Feller property. A semigroup of positive
operators gives kernels obeying the Chapman–Kolmogorov identity
`∫ g dK_{s+t}(x, ·) = ∫ (∫ g dK_t(y, ·)) K_s(x, dy)` (`integral_kernelMeasure_add`). On the
dense subspace, integration against the kernel of `denseExtension` returns the original
operator (`integral_kernelMeasure_denseExtension`). The theorem
`exists_probabilityKernel_semigroup` assembles NOTE1 §4.2a: a positive, constant-preserving
semigroup on a dense subspace of `C(X, ℝ)` containing the constants is integration against
continuous probability kernels obeying Chapman–Kolmogorov.

Scope. Uniqueness of the representing measure on a compact Hausdorff space that is not
pseudo-metrizable is not formalized (it holds among regular measures). The kernels are not
packaged as a `ProbabilityTheory.Kernel`: measurability of `x ↦ K_t(x, B)` for every Borel
set `B` needs a monotone-class passage from continuous tests to Borel sets that is not done
here; only continuity of `x ↦ K_t(x, ·)` into the weak topology is proved. Measurable
time-dependent rate histories (NOTE1 §2.4) are not treated.

## Empirical status

None. The bodies here are measure theory: every statement relates an operator on continuous
functions to integrals against measures that the operator itself determines, so no
measurement on any population could bear on one.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.FellerKernelRepresentation

open MeasureTheory Filter Topology
open scoped NNReal CompactlySupported
open PolynomialFellerExtension

noncomputable section

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [MeasurableSpace X]
  [BorelSpace X]

/-- Evaluation at the state `x` after a positive operator `S`, as a positive linear functional
on compactly supported continuous functions. -/
def evalFunctional (S : C(X, ℝ) →L[ℝ] C(X, ℝ)) (hS : ∀ g, 0 ≤ g → 0 ≤ S g) (x : X) :
    C_c(X, ℝ) →ₚ[ℝ] ℝ :=
  PositiveLinearMap.mk₀
    { toFun := fun f ↦ S f.toContinuousMap x
      map_add' := fun f g ↦ by
        change S (f.toContinuousMap + g.toContinuousMap) x
          = S f.toContinuousMap x + S g.toContinuousMap x
        rw [map_add, ContinuousMap.add_apply]
      map_smul' := fun c f ↦ by
        change S (c • f.toContinuousMap) x = c • S f.toContinuousMap x
        rw [map_smul, ContinuousMap.smul_apply] }
    fun f hf ↦ ContinuousMap.le_def.mp
      (hS f.toContinuousMap (ContinuousMap.le_def.mpr fun y ↦
        CompactlySupportedContinuousMap.le_def.mp hf y)) x

/-- The kernel of a positive operator at a state: the Riesz–Markov–Kakutani measure of the
evaluation functional `g ↦ S g x`. -/
def kernelMeasure (S : C(X, ℝ) →L[ℝ] C(X, ℝ)) (hS : ∀ g, 0 ≤ g → 0 ≤ S g) (x : X) :
    Measure X :=
  RealRMK.rieszMeasure (evalFunctional S hS x)

/-- Integrating a continuous observable against the kernel at `x` returns the operator's
value at `x`: the representation `S g x = ∫ g(y) K(x, dy)` of NOTE1 §4.2a. -/
theorem integral_kernelMeasure (S : C(X, ℝ) →L[ℝ] C(X, ℝ)) (hS : ∀ g, 0 ≤ g → 0 ≤ S g)
    (x : X) (g : C(X, ℝ)) : ∫ y, g y ∂(kernelMeasure S hS x) = S g x :=
  RealRMK.integral_rieszMeasure (evalFunctional S hS x)
    (CompactlySupportedContinuousMap.ContinuousMap.liftCompactlySupported g)

/-- A positive operator fixing the constant one has probability kernels: the mass of the
kernel at every state is `S 1 x = 1`. -/
theorem isProbabilityMeasure_kernelMeasure (S : C(X, ℝ) →L[ℝ] C(X, ℝ))
    (hS : ∀ g, 0 ≤ g → 0 ≤ S g) (hS1 : S 1 = 1) (x : X) :
    IsProbabilityMeasure (kernelMeasure S hS x) := by
  have h := integral_kernelMeasure S hS x 1
  simp only [hS1, ContinuousMap.one_apply, integral_const, smul_eq_mul, mul_one] at h
  exact ⟨(ENNReal.toReal_eq_one_iff _).mp h⟩

/-- The kernel at a state as a probability measure, for an operator fixing the constants. -/
def kernelProbability (S : C(X, ℝ) →L[ℝ] C(X, ℝ)) (hS : ∀ g, 0 ≤ g → 0 ≤ S g)
    (hS1 : S 1 = 1) (x : X) : ProbabilityMeasure X :=
  ⟨kernelMeasure S hS x, isProbabilityMeasure_kernelMeasure S hS hS1 x⟩

/-- The Feller property: the kernel depends continuously on the state in the topology of weak
convergence of probability measures, because every test integral is the continuous function
`S g`. -/
theorem continuous_kernelProbability (S : C(X, ℝ) →L[ℝ] C(X, ℝ)) (hS : ∀ g, 0 ≤ g → 0 ≤ S g)
    (hS1 : S 1 = 1) : Continuous (kernelProbability S hS hS1) := by
  refine continuous_iff_continuousAt.mpr fun x ↦
    ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr fun f ↦ ?_
  have hf : ∀ x', ∫ y, f y ∂(kernelProbability S hS hS1 x' : Measure X)
      = S f.toContinuousMap x' := fun x' ↦ integral_kernelMeasure S hS x' f.toContinuousMap
  rw [hf]
  exact Tendsto.congr (fun x' ↦ (hf x').symm) (S f.toContinuousMap).continuous.continuousAt

/-- On a pseudo-metrizable compact space the kernel is the only finite Borel measure that
represents the functional `g ↦ S g x`. -/
theorem kernelMeasure_eq_of_integral_eq [TopologicalSpace.PseudoMetrizableSpace X]
    (S : C(X, ℝ) →L[ℝ] C(X, ℝ)) (hS : ∀ g, 0 ≤ g → 0 ≤ S g) (hS1 : S 1 = 1) (x : X)
    (μ : Measure X) [IsFiniteMeasure μ] (hμ : ∀ g : C(X, ℝ), ∫ y, g y ∂μ = S g x) :
    μ = kernelMeasure S hS x := by
  haveI := isProbabilityMeasure_kernelMeasure S hS hS1 x
  exact ext_of_forall_integral_eq_of_IsFiniteMeasure fun f ↦
    (hμ f.toContinuousMap).trans (integral_kernelMeasure S hS x f.toContinuousMap).symm

/-- The Chapman–Kolmogorov identity: the kernels of a semigroup of positive operators compose,
`∫ g dK_{s+t}(x, ·) = ∫ (∫ g dK_t(y, ·)) K_s(x, dy)`. -/
theorem integral_kernelMeasure_add (S : ℝ≥0 → C(X, ℝ) →L[ℝ] C(X, ℝ))
    (hS : ∀ t g, 0 ≤ g → 0 ≤ S t g) (hsemi : ∀ s t, S (s + t) = (S s).comp (S t))
    (s t : ℝ≥0) (x : X) (g : C(X, ℝ)) :
    ∫ y, g y ∂(kernelMeasure (S (s + t)) (hS (s + t)) x)
      = ∫ y, (∫ z, g z ∂(kernelMeasure (S t) (hS t) y)) ∂(kernelMeasure (S s) (hS s) x) := by
  calc ∫ y, g y ∂(kernelMeasure (S (s + t)) (hS (s + t)) x) = S s (S t g) x :=
        (integral_kernelMeasure _ _ x g).trans
          (congrArg (fun L : C(X, ℝ) →L[ℝ] C(X, ℝ) ↦ L g x) (hsemi s t))
    _ = ∫ y, S t g y ∂(kernelMeasure (S s) (hS s) x) :=
        (integral_kernelMeasure _ _ x (S t g)).symm
    _ = ∫ y, (∫ z, g z ∂(kernelMeasure (S t) (hS t) y)) ∂(kernelMeasure (S s) (hS s) x) := by
        congr 1
        funext y
        exact (integral_kernelMeasure _ _ y g).symm

/-- On the dense subspace, integration against the kernel of `denseExtension` returns the
original operator. -/
theorem integral_kernelMeasure_denseExtension (V : Submodule ℝ C(X, ℝ))
    (hV : Dense (V : Set C(X, ℝ))) (h1 : (1 : C(X, ℝ)) ∈ V) (T : V →ₗ[ℝ] V)
    (hT : ∀ f : V, ‖(T f : C(X, ℝ))‖ ≤ ‖(f : C(X, ℝ))‖) (hT1 : (T ⟨1, h1⟩ : C(X, ℝ)) = 1)
    (x : X) (f : V) :
    ∫ y, (f : C(X, ℝ)) y
        ∂(kernelMeasure (denseExtension V hV T hT) (denseExtension_nonneg V hV T hT h1 hT1) x)
      = (T f : C(X, ℝ)) x := by
  rw [integral_kernelMeasure, denseExtension_coe]

/-- NOTE1 §4.2a, representation form. A positive, constant-preserving semigroup of linear
operators on a dense subspace of `C(X, ℝ)` containing the constants is integration against a
family of probability kernels that depend continuously on the state and obey the
Chapman–Kolmogorov identity. -/
theorem exists_probabilityKernel_semigroup (V : Submodule ℝ C(X, ℝ))
    (hV : Dense (V : Set C(X, ℝ))) (h1 : (1 : C(X, ℝ)) ∈ V) (T : ℝ≥0 → V →ₗ[ℝ] V)
    (hT1 : ∀ t, (T t ⟨1, h1⟩ : C(X, ℝ)) = 1)
    (hpos : ∀ t (f : V), 0 ≤ (f : C(X, ℝ)) → 0 ≤ (T t f : C(X, ℝ)))
    (hsemi : ∀ s t, T (s + t) = T s ∘ₗ T t) :
    ∃ K : ℝ≥0 → X → ProbabilityMeasure X,
      (∀ t x (f : V), ∫ y, (f : C(X, ℝ)) y ∂(K t x : Measure X) = (T t f : C(X, ℝ)) x) ∧
      (∀ s t x (g : C(X, ℝ)), ∫ y, g y ∂(K (s + t) x : Measure X)
        = ∫ y, (∫ z, g z ∂(K t y : Measure X)) ∂(K s x : Measure X)) ∧
      ∀ t, Continuous (K t) := by
  have hT : ∀ t (f : V), ‖(T t f : C(X, ℝ))‖ ≤ ‖(f : C(X, ℝ))‖ := fun t ↦
    norm_le_of_nonneg_of_map_unit V.subtype (V.subtype ∘ₗ T t) ⟨1, h1⟩ rfl (hT1 t) (hpos t)
  have hS : ∀ t g, 0 ≤ g → 0 ≤ denseExtension V hV (T t) (hT t) g := fun t ↦
    denseExtension_nonneg V hV (T t) (hT t) h1 (hT1 t)
  have hS1 : ∀ t, denseExtension V hV (T t) (hT t) 1 = 1 := fun t ↦
    denseExtension_one V hV (T t) (hT t) h1 (hT1 t)
  refine ⟨fun t ↦ kernelProbability (denseExtension V hV (T t) (hT t)) (hS t) (hS1 t),
    fun t x f ↦ integral_kernelMeasure_denseExtension V hV h1 (T t) (hT t) (hT1 t) x f,
    fun s t x g ↦ integral_kernelMeasure_add (fun t ↦ denseExtension V hV (T t) (hT t)) hS
      (denseExtension_add V hV T hT hsemi) s t x g,
    fun t ↦ continuous_kernelProbability (denseExtension V hV (T t) (hT t)) (hS t) (hS1 t)⟩

end

end Descent.Portability.FellerKernelRepresentation
