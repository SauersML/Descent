/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.KernelRealizationPreservation
import Mathlib.Analysis.Convex.Integral
import Mathlib.MeasureTheory.Integral.Bochner.Basic

assert_below Descent.Decision Descent.Program

/-!
# NOTE1 Theorem 1 for general probability kernels

NOTE1 Theorem 1 asks for genuine probability kernels `K_h` on the state space `X`, with
`sup_x ‖K_h φ(x) - φ(x) - h A φ(x)‖ ≤ h ε(h)` and `ε(h) → 0` (hypothesis (3)), and concludes
that `e^{tA}` carries the realization body `conv φ(X)` into itself (4). The corpus form
`FiniteMixtureKernel.MicroscopicApproximation` admits only kernels with finitely many
deterministic branches. This module removes that restriction.

`MeasureKernelApproximation φ A` is hypothesis (3) for kernels given as arbitrary probability
measures: at each step size `h` and state `x` the next-state law `kernel h x` is a probability
measure on `X`, the feature map is integrable under it, and `K_h φ(x)` is the Bochner integral
`∫ φ d(kernel h x)`, with the expansion stated in the supremum norm exactly as in (3). No
measurability of the kernel in the state is required, so the class contains every Markov kernel
of Mathlib and more.

`exp_mulVec_mem_realizationBody_of_measureKernel` is (4) for such kernels whenever the body is
closed. The step map starts from a finitely supported law realizing a point of the body and
replaces each atom by the next-state law of that atom. Its feature vector is the law's average
of the kernel integrals, and each integral lies in the body by Jensen's inequality for closed
convex sets (`Convex.integral_mem`), so the average does too; this is the one point where the
limit needs the closedness of the body. The first-order estimate passes through the average by
`KernelRealizationPreservation.abs_law_average_le`, and the telescoping limit is
`EulerInvariantSet.exp_mulVec_mem_of_euler_approx`.
`propagator_mulVec_mem_realizationBody_of_measureKernel` is the corpus epoch with no closedness
hypothesis.

The finite-branch class is the special case. `mixtureMeasure K x` places each branch weight of
a finite mixture kernel as a point mass at the moved state; it is a probability measure
(`mixtureMeasure_isProbabilityMeasure`), every observable is integrable under it, and
integrating a feature coordinate against it is the kernel's own averaging action
(`integral_mixtureMeasure_apply`), the tie between the two notions.
`ofMicroscopicApproximation` turns a finite-branch approximation into a measure-kernel one with
the same remainder, and `realizationBody_invariant_of_finiteMixture` recovers the finite-branch
invariance on a bare state type from the general theorem by equipping it with the discrete
sigma-algebra. `diracBoolApproximation` inhabits the structure.

Scope. The kernels are probability measures, not sub-probability measures; the approximation
is uniform in the state, as in (3); the time-varying case of NOTE1 §2.4 is not treated here.

## Empirical status

None. The bodies here are measure theory and convexity: integrals of a feature map against
probability measures, convex combinations and a limit of Euler products, so no measurement can
bear on whether a convex set is mapped into itself.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.MeasureKernelRealization

open MeasureTheory
open Descent.Portability.FiniteMixtureKernel Descent.Portability.RealizationBody
  Descent.Portability.KernelRealizationPreservation Descent.Coalescent

noncomputable section

/-- Hypothesis (3) of NOTE1 Theorem 1 for arbitrary probability kernels, bundled as data.
`kernel h x` is the law of the next state from `x` at step size `h`, a probability measure under
which the feature map is integrable; `error` is a remainder bound vanishing as the step size
decreases to zero; and `expansion` is (3) in the supremum norm, with `K_h φ(x)` the integral of
the feature map against the next-state law. Assumes: nothing beyond the listed fields;
`diracBoolApproximation` is a witness. -/
structure MeasureKernelApproximation {ι X : Type*} [Fintype ι] [MeasurableSpace X]
    (φ : X → ι → ℝ) (A : Matrix ι ι ℝ) where
  /-- The next-state law at step size `h` from each state. -/
  kernel : ℝ → X → Measure X
  /-- Every next-state law is a probability measure. -/
  kernel_isProbabilityMeasure : ∀ h x, IsProbabilityMeasure (kernel h x)
  /-- The feature map is integrable under every next-state law. -/
  integrable : ∀ h x, Integrable φ (kernel h x)
  /-- The uniform remainder bound at step size `h`. -/
  error : ℝ → ℝ
  /-- The remainder bound is nonnegative. -/
  error_nonneg : ∀ h, 0 ≤ error h
  /-- The remainder bound vanishes as the step size decreases to zero from above. -/
  error_tendsto : Filter.Tendsto error (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)
  /-- NOTE1 (3): one step advances the feature vector by `h A φ`, uniformly in the state, up
  to `h · error h` in the supremum norm. -/
  expansion : ∀ h, 0 < h → ∀ x,
    ‖(∫ y, φ y ∂(kernel h x)) - φ x - h • A.mulVec (φ x)‖ ≤ h * error h

/-- **NOTE1 Theorem 1 for general probability kernels.** If the feature map admits a
microscopic approximation of `A` by probability kernels and its realization body is closed,
then the semigroup generated by `A` carries the body into itself at every nonnegative time.
Assumes: the body is closed; the approximation is supplied as data. -/
theorem exp_mulVec_mem_realizationBody_of_measureKernel {ι X : Type*} [Fintype ι]
    [DecidableEq ι] [MeasurableSpace X] (φ : X → ι → ℝ) (A : Matrix ι ι ℝ)
    (approx : MeasureKernelApproximation φ A) (hclosed : IsClosed (realizationBody φ))
    (t : ℝ) (ht : 0 ≤ t) (v : ι → ℝ) (hv : v ∈ realizationBody φ) :
    (matrixExponential A t).mulVec v ∈ realizationBody φ := by
  classical
  have hkernelMem : ∀ h x, (∫ y, φ y ∂(approx.kernel h x)) ∈ realizationBody φ := by
    intro h x
    haveI := approx.kernel_isProbabilityMeasure h x
    exact (convex_realizationBody φ).integral_mem hclosed
      (ae_of_all _ fun y ↦ mem_realizationBody_of_range φ y) (approx.integrable h x)
  have hrealize : ∀ h : ℝ, ∀ u : ι → ℝ, ∃ w : ι → ℝ,
      0 < h → u ∈ realizationBody φ →
        w ∈ realizationBody φ ∧ ‖w - (u + h • A.mulVec u)‖ ≤ h * approx.error h := by
    intro h u
    by_cases hcase : 0 < h ∧ u ∈ realizationBody φ
    · obtain ⟨hh, hu⟩ := hcase
      obtain ⟨Ω, hΩ, p, point, hp, hsum, hfeat⟩ := (mem_realizationBody_iff φ u).mp hu
      have hnn : 0 ≤ h * approx.error h := mul_nonneg hh.le (approx.error_nonneg h)
      refine ⟨∑ ω, p ω • ∫ y, φ y ∂(approx.kernel h (point ω)), fun _ _ ↦ ⟨?_, ?_⟩⟩
      · exact (convex_realizationBody φ).sum_mem (fun ω _ ↦ hp ω) hsum
          fun ω _ ↦ hkernelMem h (point ω)
      · rw [pi_norm_le_iff_of_nonneg hnn]
        intro i
        have hui : u i = ∑ ω, p ω * φ (point ω) i := by
          rw [← hfeat, featureVector_apply]
        have hAi : (A.mulVec u) i = ∑ ω, p ω * (A.mulVec (φ (point ω))) i := by
          rw [← hfeat, mulVec_featureVector]
        have hcoordinate : ∑ ω, p ω * ((∫ y, φ y ∂(approx.kernel h (point ω))) i
              - φ (point ω) i - h * (A.mulVec (φ (point ω))) i)
            = (∑ ω, p ω • ∫ y, φ y ∂(approx.kernel h (point ω)) - (u + h • A.mulVec u)) i := by
          simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_apply,
            hui, hAi, Finset.mul_sum]
          rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
          exact Finset.sum_congr rfl fun ω _ ↦ by ring
        rw [Real.norm_eq_abs, ← hcoordinate]
        refine abs_law_average_le p hp hsum _ (h * approx.error h) fun ω ↦ ?_
        have hpoint := (pi_norm_le_iff_of_nonneg hnn).mp (approx.expansion h hh (point ω)) i
        simpa only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Real.norm_eq_abs] using hpoint
    · exact ⟨u, fun hh hu ↦ absurd ⟨hh, hu⟩ hcase⟩
  choose stepMap hstepMap using hrealize
  exact EulerInvariantSet.exp_mulVec_mem_of_euler_approx (realizationBody φ) hclosed A stepMap
    (fun h hh u hu ↦ (hstepMap h u hh hu).1) approx.error approx.error_tendsto
    (fun h hh u hu ↦ (hstepMap h u hh hu).2) t ht v hv

/-- **NOTE1 Theorem 1 for a corpus epoch, general probability kernels.** An epoch whose
generator admits a microscopic approximation by probability kernels on any sigma-algebra of the
multi-deme haplotype states propagates every haplotype-realizable low-order state to a
haplotype-realizable one, with no closedness hypothesis. -/
theorem propagator_mulVec_mem_realizationBody_of_measureKernel {D : ℕ}
    [MeasurableSpace (Fin D → TwoLocusHaplotypeFrequencies)] (epoch : LowOrderLDEpoch D)
    (approx : MeasureKernelApproximation (lowOrderLDFeature D) epoch.generator)
    (v : AffineLowOrderLDCoordinate D → ℝ) (hv : v ∈ realizationBody (lowOrderLDFeature D)) :
    epoch.propagator.mulVec v ∈ realizationBody (lowOrderLDFeature D) := by
  rw [LowOrderLDEpoch.propagator]
  exact exp_mulVec_mem_realizationBody_of_measureKernel (lowOrderLDFeature D) epoch.generator
    approx (isClosed_realizationBody_lowOrderLDFeature D) epoch.duration epoch.duration_nonneg v
    hv

section FiniteMixture

variable {B X : Type*} [Fintype B] [MeasurableSpace X]

/-- The next-state law of a finite mixture kernel at a state: each branch weight placed as a
point mass at the state that branch moves to. -/
def mixtureMeasure (K : FiniteMixtureKernel B X) (x : X) : Measure X :=
  ∑ b, ENNReal.ofReal (K.weight x b) • Measure.dirac (K.move b x)

/-- The next-state law of a finite mixture kernel is a probability measure, because the branch
weights are nonnegative and sum to one. -/
theorem mixtureMeasure_isProbabilityMeasure (K : FiniteMixtureKernel B X) (x : X) :
    IsProbabilityMeasure (mixtureMeasure K x) := by
  refine ⟨?_⟩
  rw [mixtureMeasure, Measure.finset_sum_apply]
  simp only [Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg fun b _ ↦ K.weight_nonneg x b, K.weight_sum,
    ENNReal.ofReal_one]

/-- Every observable is integrable under a weighted point mass on a space with measurable
singletons. -/
theorem integrable_smul_dirac [MeasurableSingletonClass X] {E : Type*} [NormedAddCommGroup E]
    (c : ℝ) (a : X) (f : X → E) : Integrable f (ENNReal.ofReal c • Measure.dirac a) :=
  ((integrable_const (f a)).congr (ae_eq_dirac f).symm).smul_measure ENNReal.ofReal_ne_top

/-- Integrating an observable against the next-state law of a finite mixture kernel averages
its values at the moved states with the branch weights. -/
theorem integral_mixtureMeasure [MeasurableSingletonClass X] {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (K : FiniteMixtureKernel B X) (x : X) (f : X → E) :
    ∫ y, f y ∂(mixtureMeasure K x) = ∑ b, K.weight x b • f (K.move b x) := by
  rw [mixtureMeasure, integral_finset_sum_measure fun b _ ↦ integrable_smul_dirac _ _ f]
  refine Finset.sum_congr rfl fun b _ ↦ ?_
  rw [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal (K.weight_nonneg x b)]

/-- **The tie between the two kernel notions.** Integrating a feature coordinate against the
next-state law of a finite mixture kernel is the kernel's own averaging action
`FiniteMixtureKernel.apply`. -/
theorem integral_mixtureMeasure_apply [MeasurableSingletonClass X] {ι : Type*} [Fintype ι]
    (K : FiniteMixtureKernel B X) (x : X) (φ : X → ι → ℝ) (i : ι) :
    (∫ y, φ y ∂(mixtureMeasure K x)) i = K.apply (fun y ↦ φ y i) x := by
  rw [integral_mixtureMeasure, FiniteMixtureKernel.apply, Finset.sum_apply]
  rfl

/-- A microscopic approximation by finite mixture kernels is a microscopic approximation by
probability kernels: the next-state laws are the mixture measures and the remainder is
unchanged. -/
def ofMicroscopicApproximation [MeasurableSingletonClass X] {ι : Type*} [Fintype ι]
    {φ : X → ι → ℝ} {A : Matrix ι ι ℝ} (approx : MicroscopicApproximation (B := B) φ A) :
    MeasureKernelApproximation φ A where
  kernel h x := mixtureMeasure (approx.kernel h) x
  kernel_isProbabilityMeasure h x := mixtureMeasure_isProbabilityMeasure _ _
  integrable h x := integrable_finset_sum_measure.mpr fun b _ ↦ integrable_smul_dirac _ _ φ
  error := approx.error
  error_nonneg := approx.error_nonneg
  error_tendsto := approx.error_tendsto
  expansion h hh x := by
    have hnn : 0 ≤ h * approx.error h := mul_nonneg hh.le (approx.error_nonneg h)
    rw [pi_norm_le_iff_of_nonneg hnn]
    intro i
    have hcoordinate := integral_mixtureMeasure_apply (approx.kernel h) x φ i
    simpa only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Real.norm_eq_abs, hcoordinate] using
      approx.expansion h hh x i

/-- **The finite-branch Theorem 1 as the special case.** On a bare state type, a microscopic
approximation by finite mixture kernels makes every semigroup time map carry a closed
realization body into itself. The proof equips the states with the discrete sigma-algebra and
applies the general theorem to `ofMicroscopicApproximation`. -/
theorem realizationBody_invariant_of_finiteMixture {ι B X : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype B] (φ : X → ι → ℝ) (A : Matrix ι ι ℝ)
    (approx : MicroscopicApproximation (B := B) φ A) (hclosed : IsClosed (realizationBody φ)) :
    ∀ t, 0 ≤ t → ∀ v ∈ realizationBody φ,
      (matrixExponential A t).mulVec v ∈ realizationBody φ := by
  letI : MeasurableSpace X := ⊤
  haveI : MeasurableSingletonClass X := ⟨fun _ ↦ MeasurableSpace.measurableSet_top⟩
  intro t ht v hv
  exact exp_mulVec_mem_realizationBody_of_measureKernel φ A (ofMicroscopicApproximation approx)
    hclosed t ht v hv

end FiniteMixture

/-- The in-corpus inhabitant of `MeasureKernelApproximation`: on the two-point space, the
identity kernel as point masses approximates the zero generator with zero remainder. -/
def diracBoolApproximation :
    MeasureKernelApproximation (fun (_ : Bool) (_ : Unit) ↦ (1 : ℝ)) (0 : Matrix Unit Unit ℝ) :=
  ofMicroscopicApproximation (trivialApproximation _)

end

end Descent.Portability.MeasureKernelRealization
