/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.MultinomialJetCertificate
import Descent.Portability.Pi2GeneratorBridges
import Descent.Portability.EnlargedBodyClosedness

assert_below Descent.Decision Descent.Program

/-!
# The microscopic approximation with multinomial resampling

NOTE1 section 2.3 resamples a deme by drawing `N(h) = ⌈1/(c h)⌉` chromosomes from its haplotype
frequencies, and NOTE1 equation (10) is the expansion of that draw. The stage-choosing
approximation of `TwoLocusMicroscopicKernel` uses the single-draw stage instead, because the
corpus `MicroscopicApproximation` fixes one branch type for every step size, while the census of
`N(h)` chromosomes is a branch type that grows as the step shrinks. This module lifts that
restriction and assembles the approximation the note describes.

`StepIndexedApproximation φ A` is hypothesis (3) of NOTE1 Theorem 1 with a branch type
`Branch h` that may depend on the step size `h`, and a kernel required only at positive `h`.
`StepIndexedApproximation.ofApproximation` turns every corpus `MicroscopicApproximation` into
one. `exp_mulVec_mem_realizationBody_of_stepIndexed` is NOTE1 Theorem 1 for it. The proof builds
the step map of `EulerInvariantSet` one step size at a time, so no branch type common to all step
sizes is ever needed. Its one-step content is `pushforwardFeature_mem_realizationBody` and
`pushforwardFeature_sub_euler_le`: pushing a finitely supported law through one kernel keeps its
feature vector in the body and moves it by the Euler step up to the expansion bound.

The stage kernels differ in branch type as well: a census of `⌈1/(c_i τ)⌉` chromosomes for the
drift stage in deme `i`, and a haplotype label for each pulse. `reindexKernel` places a kernel's
branches inside a larger finite type, with zero weight outside the image, and
`uniformSigmaMixture` chooses a stage uniformly and runs it on the sigma type of all stage
branches. `apply_uniformSigmaMixture_expansion` is the random-stage assembly of
`RandomStageKernel` for this mixture.

`multinomialStageKernel` is the stage list of `PulseStageKernel` with each drift stage replaced
by `MultinomialDriftStage.multinomialDriftKernel` at the note's chromosome count.
`apply_multinomialStageKernel_expansion` expands each stage on every enlarged coordinate: the
drift stages through `MultinomialJetCertificate.apply_multinomialDriftStage_enlarged`, which is
equation (10) for those coordinates, and the pulse stages through the corpus pulse certificates.
The drift slack `c_i² τ (107 M + B)` is of order `τ`; the single-draw stage's is of order `√τ`.
`multinomialMicroscopicApproximation rates deme` is the resulting `StepIndexedApproximation` of
`enlargedLowOrderLDGenerator rates`, with the stage velocities identified with the generator by
`Pi2GeneratorBridges.stage_generator_enlarged`.

NOTE1 Theorem 2 follows with the note's resampling.
`multinomialPropagator_mulVec_mem_realizationBody` carries the enlarged body into itself, and
`multinomialEpoch_preserves_locusExchangeable_realization` is one epoch at any nonnegative rates.

What is NOT proved here: the list induction over histories, which needs only the epoch theorem
and is carried out for the single-draw approximation in `TwoLocusMicroscopicApproximation`; and
the deme count zero, where the stage set is empty and nothing is resampled.

## Empirical status

None. The bodies here are algebra and one limit: finite averages of polynomial coordinates
against probability weights, bounds between them, and a matrix exponential carrying a closed
convex hull into itself. No measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.MultinomialMicroscopicApproximation

open Coalescent
open Descent.Portability.FiniteMixtureKernel
open Descent.Portability.FiniteReproductiveKernel
open Descent.Portability.RealizationBody
open Descent.Portability.PulseStageKernel
open Descent.Portability.EnlargedLowOrderLDGenerator
open Descent.Portability.TwoLocusMicroscopicKernel
open Descent.Portability.MultinomialDriftStage
open Descent.Portability.MultinomialJetCertificate

noncomputable section

/-! ## Approximations whose branch type depends on the step size -/

/-- Hypothesis (3) of NOTE1 Theorem 1 with a branch type that may depend on the step size.
At every positive step size `h`, `kernel h` is a genuine probability kernel whose finitely many
branches have type `Branch h`; `error` is a remainder bound vanishing with the step size, and
`expansion` is the uniform first-order expansion `K_h φ = φ + h A φ + O(h · error h)`.
Assumes: nothing beyond the listed fields; `trivialStepIndexedApproximation` is a witness. -/
structure StepIndexedApproximation {ι X : Type*} [Fintype ι] (φ : X → ι → ℝ)
    (A : Matrix ι ι ℝ) where
  /-- The branch type of the kernel run at step size `h`. -/
  Branch : ℝ → Type
  /-- Every branch type is finite. -/
  branchFintype : ∀ h, Fintype (Branch h)
  /-- The probability kernel run at a positive step size `h`. -/
  kernel : ∀ h, 0 < h → FiniteMixtureKernel (Branch h) X
  /-- The remainder bound at step size `h`, uniform in the state. -/
  error : ℝ → ℝ
  /-- No remainder bound is negative. -/
  error_nonneg : ∀ h, 0 ≤ error h
  /-- The remainder bound tends to zero along positive step sizes. -/
  error_tendsto : Filter.Tendsto error (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)
  /-- At every positive step size the kernel moves each feature coordinate by `h A φ`, up to
  `h · error h` at every state. -/
  expansion : ∀ h (hh : 0 < h) x i,
    |(kernel h hh).apply (fun y ↦ φ y i) x - φ x i - h * (A.mulVec (φ x)) i| ≤ h * error h

/-- The branch type at each step size is finite. -/
instance StepIndexedApproximation.instFintypeBranch {ι X : Type*} [Fintype ι]
    {φ : X → ι → ℝ} {A : Matrix ι ι ℝ} (approx : StepIndexedApproximation φ A) (h : ℝ) :
    Fintype (approx.Branch h) :=
  approx.branchFintype h

/-- Every corpus microscopic approximation, whose branch type is fixed, is a step-indexed one. -/
def StepIndexedApproximation.ofApproximation {ι X : Type*} [Fintype ι] {B : Type} [Fintype B]
    {φ : X → ι → ℝ} {A : Matrix ι ι ℝ} (approx : MicroscopicApproximation (B := B) φ A) :
    StepIndexedApproximation φ A where
  Branch _ := B
  branchFintype _ := inferInstance
  kernel h _ := approx.kernel h
  error := approx.error
  error_nonneg := approx.error_nonneg
  error_tendsto := approx.error_tendsto
  expansion := approx.expansion

/-- The in-corpus inhabitant of `StepIndexedApproximation`: the kernel that does nothing, with
one branch at every step size, approximates the zero generator with no remainder. -/
def trivialStepIndexedApproximation {ι X : Type*} [Fintype ι] (φ : X → ι → ℝ) :
    StepIndexedApproximation φ (0 : Matrix ι ι ℝ) :=
  StepIndexedApproximation.ofApproximation (trivialApproximation φ)

/-! ## NOTE1 Theorem 1 for step-indexed approximations -/

/-- The feature vector of a finitely supported law after one kernel step. -/
def pushforwardFeature {Ω B X ι : Type*} [Fintype Ω] [Fintype B] (K : FiniteMixtureKernel B X)
    (p : Ω → ℝ) (point : Ω → X) (φ : X → ι → ℝ) : ι → ℝ :=
  featureVector (K.pushforwardMass p point) (K.pushforwardPoint point) φ

/-- One kernel step keeps the feature vector of a probability law inside the realization body. -/
theorem pushforwardFeature_mem_realizationBody {Ω B X ι : Type*} [Fintype Ω] [Fintype B]
    (K : FiniteMixtureKernel B X) (p : Ω → ℝ) (hp : ∀ ω, 0 ≤ p ω) (hsum : ∑ ω, p ω = 1)
    (point : Ω → X) (φ : X → ι → ℝ) :
    pushforwardFeature K p point φ ∈ realizationBody φ :=
  featureVector_mem_convexHull _ (K.pushforwardMass_nonneg p hp point)
    (K.pushforwardMass_sum p hsum point) _ φ

/-- **One kernel step is an Euler step up to the expansion bound.** If the kernel moves every
feature coordinate by `h A φ` up to `bound` at every state, then it moves the feature vector of
any probability law by `h A` applied to that vector, up to `bound` in the sup norm. -/
theorem pushforwardFeature_sub_euler_le {Ω B X ι : Type*} [Fintype Ω] [Fintype B] [Fintype ι]
    (K : FiniteMixtureKernel B X) (p : Ω → ℝ) (hp : ∀ ω, 0 ≤ p ω) (hsum : ∑ ω, p ω = 1)
    (point : Ω → X) (φ : X → ι → ℝ) (A : Matrix ι ι ℝ) (h bound : ℝ) (hbound : 0 ≤ bound)
    (hK : ∀ x i, |K.apply (fun y ↦ φ y i) x - φ x i - h * (A.mulVec (φ x)) i| ≤ bound) :
    ‖pushforwardFeature K p point φ -
        (featureVector p point φ + h • A.mulVec (featureVector p point φ))‖ ≤ bound := by
  refine (pi_norm_le_iff_of_nonneg hbound).mpr fun i ↦ ?_
  have hcoordinate : (pushforwardFeature K p point φ -
        (featureVector p point φ + h • A.mulVec (featureVector p point φ))) i =
      ∑ ω, p ω * (K.apply (fun y ↦ φ y i) (point ω) - φ (point ω) i -
        h * (A.mulVec (φ (point ω))) i) := by
    simp only [pushforwardFeature, K.featureVector_pushforward p point φ, Pi.sub_apply,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_apply, featureVector_apply,
      KernelRealizationPreservation.mulVec_featureVector, Finset.mul_sum,
      ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun ω _ ↦ by ring
  rw [Real.norm_eq_abs, hcoordinate]
  exact KernelRealizationPreservation.abs_law_average_le p hp hsum _ bound
    fun ω ↦ hK (point ω) i

/-- **NOTE1 Theorem 1 with a step-dependent branch type.** If the feature map admits a
step-indexed microscopic approximation of `A` and its realization body is closed, then the
semigroup generated by `A` carries the body into itself at every nonnegative time.
Assumes: the body is closed; the approximation is supplied as data. -/
theorem exp_mulVec_mem_realizationBody_of_stepIndexed {ι X : Type*} [Fintype ι]
    [DecidableEq ι] (φ : X → ι → ℝ) (A : Matrix ι ι ℝ) (approx : StepIndexedApproximation φ A)
    (hclosed : IsClosed (realizationBody φ)) (t : ℝ) (ht : 0 ≤ t) (v : ι → ℝ)
    (hv : v ∈ realizationBody φ) :
    (matrixExponential A t).mulVec v ∈ realizationBody φ := by
  classical
  have hstep : ∀ (h : ℝ) (u : ι → ℝ), ∃ w : ι → ℝ, 0 < h → u ∈ realizationBody φ →
      w ∈ realizationBody φ ∧ ‖w - (u + h • A.mulVec u)‖ ≤ h * approx.error h := by
    intro h u
    by_cases hcase : 0 < h ∧ u ∈ realizationBody φ
    · obtain ⟨Ω, hΩ, p, point, hp, hsum, hfeature⟩ := (mem_realizationBody_iff φ u).mp hcase.2
      refine ⟨pushforwardFeature (approx.kernel h hcase.1) p point φ, fun _ _ ↦
        ⟨pushforwardFeature_mem_realizationBody _ p hp hsum point φ, ?_⟩⟩
      rw [← hfeature]
      exact pushforwardFeature_sub_euler_le _ p hp hsum point φ A h _
        (mul_nonneg hcase.1.le (approx.error_nonneg h)) (approx.expansion h hcase.1)
    · exact ⟨u, fun hpositive hmember ↦ absurd ⟨hpositive, hmember⟩ hcase⟩
  choose step hstepspec using hstep
  exact EulerInvariantSet.exp_mulVec_mem_of_euler_approx (realizationBody φ) hclosed A step
    (fun h hh u hu ↦ (hstepspec h u hh hu).1) approx.error approx.error_tendsto
    (fun h hh u hu ↦ (hstepspec h u hh hu).2) t ht v hv

/-! ## Mixtures of stages with different branch types -/

/-- A kernel whose branches are placed inside a larger finite type along an injection: branches
outside the image carry zero weight and leave the state unchanged. -/
def reindexKernel {B C X : Type*} [Fintype B] [Fintype C] (K : FiniteMixtureKernel B X)
    (embedding : B → C) (hembedding : Function.Injective embedding) :
    FiniteMixtureKernel C X where
  weight x := Function.extend embedding (K.weight x) 0
  move := Function.extend embedding K.move fun _ ↦ id
  weight_nonneg x c := by
    by_cases hc : ∃ b, embedding b = c
    · obtain ⟨b, rfl⟩ := hc
      rw [hembedding.extend_apply]
      exact K.weight_nonneg x b
    · rw [Function.extend_apply' _ _ _ hc]
      exact le_refl 0
  weight_sum x := by
    rw [← K.weight_sum x]
    exact (Fintype.sum_of_injective embedding hembedding (K.weight x) _
      (fun c hc ↦ Function.extend_apply' _ _ _ hc)
      (fun b ↦ (hembedding.extend_apply _ _ b).symm)).symm

/-- Reindexing the branches does not change the kernel action. -/
theorem apply_reindexKernel {B C X : Type*} [Fintype B] [Fintype C] (K : FiniteMixtureKernel B X)
    (embedding : B → C) (hembedding : Function.Injective embedding) (f : X → ℝ) (x : X) :
    (reindexKernel K embedding hembedding).apply f x = K.apply f x := by
  simp only [FiniteMixtureKernel.apply]
  refine (Fintype.sum_of_injective embedding hembedding _ _ (fun c hc ↦ ?_) (fun b ↦ ?_)).symm
  · show Function.extend embedding (K.weight x) 0 c *
        f (Function.extend embedding K.move (fun _ ↦ id) c x) = 0
    rw [Function.extend_apply' _ _ _ hc, Pi.zero_apply, zero_mul]
  · show K.weight x b * f (K.move b x) = Function.extend embedding (K.weight x) 0 (embedding b) *
        f (Function.extend embedding K.move (fun _ ↦ id) (embedding b) x)
    rw [hembedding.extend_apply, hembedding.extend_apply]

/-- The kernel that picks one of `Fintype.card S` stage kernels uniformly at random and runs it,
when each stage has its own branch type. The branches are the pairs of a stage label and a
branch of any stage, and a stage's kernel sees only its own branches. -/
def uniformSigmaMixture {S X : Type*} [Fintype S] {Branch : S → Type*} [∀ s, Fintype (Branch s)]
    (K : ∀ s, FiniteMixtureKernel (Branch s) X) (hS : 0 < Fintype.card S) :
    FiniteMixtureKernel (S × Σ s, Branch s) X :=
  FiniteMixtureKernel.uniformMixture
    (fun s ↦ reindexKernel (K s) (Sigma.mk s) sigma_mk_injective) hS

/-- **The random-stage assembly with stage-dependent branch types.** If each stage kernel moves
an observable by `card S * step` times its velocity up to `card S * step` times its slack, then
the uniform mixture moves it by `step` times the summed velocities up to `step` times the summed
slacks. -/
theorem apply_uniformSigmaMixture_expansion {S X : Type*} [Fintype S] {Branch : S → Type*}
    [∀ s, Fintype (Branch s)] (K : ∀ s, FiniteMixtureKernel (Branch s) X)
    (velocity : S → X → ℝ) (slack : S → ℝ) (hS : 0 < Fintype.card S) (observable : X → ℝ)
    (point : X) (step : ℝ)
    (stage_expansion : ∀ s, |(K s).apply observable point - observable point -
        (Fintype.card S : ℝ) * step * velocity s point| ≤ (Fintype.card S : ℝ) * step * slack s) :
    |(uniformSigmaMixture K hS).apply observable point - observable point -
        step * ∑ s, velocity s point| ≤ step * ∑ s, slack s := by
  refine RandomStageKernel.apply_uniformStageMixture
    (fun s ↦ reindexKernel (K s) (Sigma.mk s) sigma_mk_injective) velocity slack hS observable
    point step fun s ↦ ?_
  simp only [apply_reindexKernel]
  exact stage_expansion s

/-! ## The stages with multinomial resampling -/

/-- The branch type of each stage at parameter `tau`: the census of the note's chromosome count
for resampling, and one haplotype label for each deterministic pulse. -/
def multinomialStageBranch {D : ℕ} (rates : ManyDemeLDRates D) (tau : ℝ) : Stage D → Type
  | .drift deme =>
      Counts TwoLocusHaplotype (multinomialChromosomeCount (rates.coalescence deme) tau)
  | .migration _ _ => TwoLocusHaplotype
  | .recombination _ => TwoLocusHaplotype
  | .mutationLeft _ => TwoLocusHaplotype
  | .mutationRight _ => TwoLocusHaplotype

/-- Every stage branch type is finite. -/
instance multinomialStageBranchFintype {D : ℕ} (rates : ManyDemeLDRates D) (tau : ℝ) :
    (stage : Stage D) → Fintype (multinomialStageBranch rates tau stage)
  | .drift deme => inferInstanceAs
      (Fintype (Counts TwoLocusHaplotype (multinomialChromosomeCount (rates.coalescence deme) tau)))
  | .migration _ _ => inferInstanceAs (Fintype TwoLocusHaplotype)
  | .recombination _ => inferInstanceAs (Fintype TwoLocusHaplotype)
  | .mutationLeft _ => inferInstanceAs (Fintype TwoLocusHaplotype)
  | .mutationRight _ => inferInstanceAs (Fintype TwoLocusHaplotype)

/-- The kernel of each stage at a positive parameter `tau`: the multinomial resampling kernel of
NOTE1 section 2.3 with `⌈1/(c_i tau)⌉` chromosomes for drift in deme `i`, and the corpus pulse
kernel for each of the four deterministic stages. -/
def multinomialStageKernel {D : ℕ} (rates : ManyDemeLDRates D) (tau : ℝ) (htau : 0 < tau) :
    (stage : Stage D) →
      FiniteMixtureKernel (multinomialStageBranch rates tau stage) (DemeHaplotypeState D)
  | .drift deme => multinomialDriftKernel deme
      (one_le_multinomialChromosomeCount (rates.coalescence deme) tau (rates.coalescence_pos deme)
        htau)
  | .migration source recipient => stageKernel rates (.migration source recipient) tau
  | .recombination deme => stageKernel rates (.recombination deme) tau
  | .mutationLeft deme => stageKernel rates (.mutationLeft deme) tau
  | .mutationRight deme => stageKernel rates (.mutationRight deme) tau

/-- The slack of each stage on one enlarged coordinate: the multinomial drift slack, of order
`tau`, for resampling, and the corpus pulse slack for each deterministic stage. -/
def multinomialStageSlack {D : ℕ} (rates : ManyDemeLDRates D)
    (coordinate : AffineEnlargedCoordinate D) : Stage D → ℝ → ℝ
  | .drift deme => fun tau ↦ rates.coalescence deme ^ 2 * tau *
      (107 * (JetPolynomialCertificate.enlarged coordinate).massBound +
        (enlargedStageExpansion coordinate).drift.bound)
  | stage => stageSlack rates (enlargedStageExpansion coordinate) stage

/-- The drift slack is read off the polynomial certificate's coefficient mass and the corpus
resampling certificate's drift bound. -/
theorem multinomialStageSlack_drift {D : ℕ} (rates : ManyDemeLDRates D)
    (coordinate : AffineEnlargedCoordinate D) (deme : Fin D) (tau : ℝ) :
    multinomialStageSlack rates coordinate (.drift deme) tau =
      rates.coalescence deme ^ 2 * tau *
        (107 * (JetPolynomialCertificate.enlarged coordinate).massBound +
          (enlargedStageExpansion coordinate).drift.bound) :=
  rfl

/-- Every stage slack is nonnegative at a nonnegative parameter. -/
theorem multinomialStageSlack_nonneg {D : ℕ} (rates : ManyDemeLDRates D)
    (coordinate : AffineEnlargedCoordinate D) (stage : Stage D) (tau : ℝ) (htau : 0 ≤ tau) :
    0 ≤ multinomialStageSlack rates coordinate stage tau := by
  cases stage with
  | drift deme =>
      have hmass : 0 ≤ (JetPolynomialCertificate.enlarged coordinate).massBound :=
        (coefficientMass_nonneg _).trans
          ((JetPolynomialCertificate.enlarged coordinate).mass_le deme
            fun _ ↦ TwoLocusHaplotypeFrequencies.maximalCoupling)
      have hbound := (enlargedStageExpansion coordinate).drift.bound_nonneg
      rw [multinomialStageSlack_drift]
      exact mul_nonneg (mul_nonneg (sq_nonneg _) htau)
        (add_nonneg (mul_nonneg (by norm_num) hmass) hbound)
  | migration source recipient =>
      exact stageSlack_nonneg rates (enlargedStageExpansion coordinate)
        (.migration source recipient) tau htau
  | recombination deme =>
      exact stageSlack_nonneg rates (enlargedStageExpansion coordinate) (.recombination deme)
        tau htau
  | mutationLeft deme =>
      exact stageSlack_nonneg rates (enlargedStageExpansion coordinate) (.mutationLeft deme)
        tau htau
  | mutationRight deme =>
      exact stageSlack_nonneg rates (enlargedStageExpansion coordinate) (.mutationRight deme)
        tau htau

/-- Every stage slack vanishes with the parameter. -/
theorem multinomialStageSlack_tendsto {D : ℕ} (rates : ManyDemeLDRates D)
    (coordinate : AffineEnlargedCoordinate D) (stage : Stage D) :
    Filter.Tendsto (multinomialStageSlack rates coordinate stage) (nhds 0) (nhds 0) := by
  cases stage with
  | drift deme =>
      have hcontinuous : Continuous (multinomialStageSlack rates coordinate (.drift deme)) := by
        simp only [multinomialStageSlack]
        fun_prop
      exact hcontinuous.tendsto' 0 0 (by simp [multinomialStageSlack])
  | migration source recipient =>
      exact stageSlack_tendsto rates (enlargedStageExpansion coordinate)
        (.migration source recipient)
  | recombination deme =>
      exact stageSlack_tendsto rates (enlargedStageExpansion coordinate) (.recombination deme)
  | mutationLeft deme =>
      exact stageSlack_tendsto rates (enlargedStageExpansion coordinate) (.mutationLeft deme)
  | mutationRight deme =>
      exact stageSlack_tendsto rates (enlargedStageExpansion coordinate) (.mutationRight deme)

/-- **Every stage expands to first order on every enlarged coordinate.** The drift stage is
equation (10) for the coordinate's polynomial certificate at the note's chromosome count, and
each pulse stage is the corpus pulse expansion. -/
theorem apply_multinomialStageKernel_expansion {D : ℕ} (rates : ManyDemeLDRates D)
    (coordinate : AffineEnlargedCoordinate D) (stage : Stage D) (tau : ℝ) (htau : 0 < tau)
    (state : DemeHaplotypeState D) :
    |(multinomialStageKernel rates tau htau stage).apply (enlargedCoordinateJet coordinate).value
          state - (enlargedCoordinateJet coordinate).value state -
        tau * stageDrift rates (enlargedStageExpansion coordinate) stage state| ≤
      tau * multinomialStageSlack rates coordinate stage tau := by
  cases stage with
  | drift deme =>
      exact apply_multinomialDriftStage_enlarged coordinate deme (rates.coalescence deme) tau
        (rates.coalescence_pos deme) htau state
  | migration source recipient =>
      exact apply_stageKernel_expansion rates (enlargedStageExpansion coordinate)
        (.migration source recipient) tau htau state
  | recombination deme =>
      exact apply_stageKernel_expansion rates (enlargedStageExpansion coordinate)
        (.recombination deme) tau htau state
  | mutationLeft deme =>
      exact apply_stageKernel_expansion rates (enlargedStageExpansion coordinate)
        (.mutationLeft deme) tau htau state
  | mutationRight deme =>
      exact apply_stageKernel_expansion rates (enlargedStageExpansion coordinate)
        (.mutationRight deme) tau htau state

/-! ## The assembled step -/

/-- The branch type of one microscopic step at step size `step`: a stage label, then a branch of
any stage run at `card (Stage D) * step`. -/
abbrev multinomialMicroscopicBranch {D : ℕ} (rates : ManyDemeLDRates D) (step : ℝ) : Type :=
  Stage D × Σ stage : Stage D, multinomialStageBranch rates (Fintype.card (Stage D) * step) stage

/-- The stage count is positive as a real number whenever there is a deme. -/
theorem card_stage_real_pos {D : ℕ} (deme : Fin D) : (0 : ℝ) < Fintype.card (Stage D) :=
  Nat.cast_pos.mpr (card_stage_pos deme)

/-- One microscopic step with multinomial resampling: choose one stage uniformly at random and
run it at the stage count times the step size. -/
def multinomialMicroscopicKernel {D : ℕ} (rates : ManyDemeLDRates D) (deme : Fin D) (step : ℝ)
    (hstep : 0 < step) :
    FiniteMixtureKernel (multinomialMicroscopicBranch rates step) (DemeHaplotypeState D) :=
  uniformSigmaMixture
    (multinomialStageKernel rates (Fintype.card (Stage D) * step)
      (mul_pos (card_stage_real_pos deme) hstep))
    (card_stage_pos deme)

/-- **One multinomial microscopic step advances every enlarged coordinate by the summed stage
drift**, up to `step` times the summed stage slacks. -/
theorem multinomialMicroscopicKernel_expansion {D : ℕ} (rates : ManyDemeLDRates D)
    (deme : Fin D) (step : ℝ) (hstep : 0 < step) (state : DemeHaplotypeState D)
    (coordinate : AffineEnlargedCoordinate D) :
    |(multinomialMicroscopicKernel rates deme step hstep).apply
          (enlargedCoordinateJet coordinate).value state -
        (enlargedCoordinateJet coordinate).value state -
        step * ∑ stage : Stage D,
          stageDrift rates (enlargedStageExpansion coordinate) stage state| ≤
      step * ∑ stage : Stage D,
        multinomialStageSlack rates coordinate stage (Fintype.card (Stage D) * step) :=
  apply_uniformSigmaMixture_expansion _
    (fun stage ↦ stageDrift rates (enlargedStageExpansion coordinate) stage)
    (fun stage ↦ multinomialStageSlack rates coordinate stage (Fintype.card (Stage D) * step))
    (card_stage_pos deme) _ state step fun stage ↦
      apply_multinomialStageKernel_expansion rates coordinate stage _
        (mul_pos (card_stage_real_pos deme) hstep) state

/-- The total slack of one multinomial microscopic step over every enlarged coordinate and every
stage, made nonnegative by the absolute value. -/
def multinomialMicroscopicError {D : ℕ} (rates : ManyDemeLDRates D) (step : ℝ) : ℝ :=
  |∑ other : AffineEnlargedCoordinate D, ∑ index : Stage D,
    multinomialStageSlack rates other index (Fintype.card (Stage D) * step)|

/-- The assembled error vanishes as the step size decreases to zero. -/
theorem multinomialMicroscopicError_tendsto {D : ℕ} (rates : ManyDemeLDRates D) :
    Filter.Tendsto (multinomialMicroscopicError rates) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  have hscale : Filter.Tendsto (fun step : ℝ ↦ (Fintype.card (Stage D) : ℝ) * step)
      (nhds 0) (nhds 0) :=
    (continuous_mul_left (Fintype.card (Stage D) : ℝ)).tendsto' 0 0 (mul_zero _)
  have hsum : Filter.Tendsto (fun step ↦ ∑ other : AffineEnlargedCoordinate D,
      ∑ index : Stage D, multinomialStageSlack rates other index
        (Fintype.card (Stage D) * step)) (nhds 0)
      (nhds (∑ _other : AffineEnlargedCoordinate D, ∑ _index : Stage D, (0 : ℝ))) :=
    tendsto_finset_sum _ fun other _ ↦ tendsto_finset_sum _ fun index _ ↦
      (multinomialStageSlack_tendsto rates other index).comp hscale
  simp only [Finset.sum_const_zero] at hsum
  have habs := hsum.abs
  rw [abs_zero] at habs
  exact habs.mono_left nhdsWithin_le_nhds

/-- **The multinomial microscopic approximation of the enlarged generator.** NOTE1 section 2.3
with the note's resampling: every stage is a genuine probability kernel at every positive step
size, the drift stages draw `⌈1/(c_i τ)⌉` chromosomes, the expansion is uniform in the state and
the coordinate, and the error vanishes with the step. The deme is data because it is what makes
the stage set nonempty. -/
def multinomialMicroscopicApproximation {D : ℕ} (rates : ManyDemeLDRates D) (deme : Fin D) :
    StepIndexedApproximation (enlargedLowOrderLDFeature (D := D))
      (enlargedLowOrderLDGenerator rates) where
  Branch := multinomialMicroscopicBranch rates
  branchFintype _ := inferInstance
  kernel := multinomialMicroscopicKernel rates deme
  error := multinomialMicroscopicError rates
  error_nonneg _ := abs_nonneg _
  error_tendsto := multinomialMicroscopicError_tendsto rates
  expansion step hstep state coordinate := by
    have hbound := multinomialMicroscopicKernel_expansion rates deme step hstep state coordinate
    rw [Pi2GeneratorBridges.stage_generator_enlarged rates state coordinate,
      enlargedFeature_eq_jet_value coordinate, ← enlargedCoordinateJet_value coordinate state]
    refine hbound.trans (mul_le_mul_of_nonneg_left ?_ hstep.le)
    refine le_trans (Finset.single_le_sum
      (f := fun other : AffineEnlargedCoordinate D ↦ ∑ index : Stage D,
        multinomialStageSlack rates other index (Fintype.card (Stage D) * step))
      (fun other _ ↦ Finset.sum_nonneg fun index _ ↦
        multinomialStageSlack_nonneg rates other index _
          (mul_pos (card_stage_real_pos deme) hstep).le)
      (Finset.mem_univ coordinate)) (le_abs_self _)

/-! ## NOTE1 Theorem 2 with multinomial resampling -/

/-- **NOTE1 Theorem 2, first sentence, through multinomial resampling.** For every rate law with
at least one deme and every nonnegative duration, the exact propagator of the enlarged moment
system carries the enlarged realization body into itself, as the limit of the multinomial
microscopic steps. -/
theorem multinomialPropagator_mulVec_mem_realizationBody {D : ℕ} (rates : ManyDemeLDRates D)
    (deme : Fin D) (duration : ℝ) (hduration : 0 ≤ duration)
    (vector : AffineEnlargedCoordinate D → ℝ)
    (hvector : vector ∈ realizationBody (enlargedLowOrderLDFeature (D := D))) :
    (matrixExponential (enlargedLowOrderLDGenerator rates) duration).mulVec vector ∈
      realizationBody (enlargedLowOrderLDFeature (D := D)) :=
  exp_mulVec_mem_realizationBody_of_stepIndexed _ _
    (multinomialMicroscopicApproximation rates deme)
    (EnlargedBodyClosedness.isClosed_enlargedRealizationBody D) duration hduration vector hvector

/-- **NOTE1 Theorem 2 for one epoch, through multinomial resampling.** For every rate law with at
least one deme and every nonnegative duration, the epoch propagator maps a locus-exchangeably
realizable stored state to a locus-exchangeably realizable one. -/
theorem multinomialEpoch_preserves_locusExchangeable_realization {D : ℕ}
    (rates : ManyDemeLDRates D) (deme : Fin D) (duration : ℝ) (hduration : 0 ≤ duration)
    {state : AffineLowOrderLDCoordinate D → ℝ}
    (realization : LocusExchangeableLowOrderLDHaplotypeRealization state) :
    Nonempty (LocusExchangeableLowOrderLDHaplotypeRealization
      ((rates.epoch duration hduration).propagator.mulVec state)) := by
  apply TwoLocusRealizabilityPreservation.nonempty_locusExchangeableRealization_of_embed_mem
  change embedLowOrderLDState
      ((matrixExponential (augmentedLowOrderLDGenerator rates) duration).mulVec state) ∈ _
  rw [← enlargedPropagator_mulVec_embed]
  exact multinomialPropagator_mulVec_mem_realizationBody rates deme duration hduration _
    (EnlargedBodyClosedness.embed_mem_enlargedRealizationBody_of_realization realization)

end

end Descent.Portability.MultinomialMicroscopicApproximation
