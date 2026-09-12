/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.TwoLocusStageComposition
import Descent.Portability.MultinomialJetCertificate
import Descent.Portability.AffineCaratheodoryCount

assert_below Descent.Decision Descent.Program

/-!
# The composed microscopic step with multinomial resampling

NOTE1 section 2.3 builds one microscopic step by composing physical stages: simultaneous
migration, recombination, allele flips at both loci, and in each deme multinomial resampling
of `N(h) = ⌈1/(c_i h)⌉` chromosomes.  `TwoLocusStageComposition` composes these stages with
the corpus's single-draw resampling stage in place of the last.  This module runs the
multinomial stage of `MultinomialDriftStage` instead, and proves that the literal composition
gives a `MicroscopicApproximation` of `enlargedLowOrderLDGenerator`, with nothing assumed.

The branch type.  A census of `N(h)` chromosomes is a branch type that changes with `h`, while
the other stages branch over haplotypes, so the stages of one step have different branch types
(`multinomialPhysicalBranch`).  `multinomialComposite rates h` composes them with
`StageCompositionKernel.composeDependentStages`, and its branch type depends on `h`.  The
corpus `MicroscopicApproximation` fixes one branch type for every step size, so the composite
is padded to one.  From every state the feature vector of one step lies in the realization
body, and the enlarged feature family has the constant coordinate `none`, so Carathéodory's
count (`AffineCaratheodoryCount.exists_law_card_of_constant_coordinate`) realizes that vector
by a law on `Fintype.card ι` atoms (`exists_paddedLaw`).  `paddedKernel` is the kernel whose
branches are those atoms with those weights.  It is a genuine probability kernel on the state
space, and it moves every feature coordinate exactly as the original kernel does
(`paddedKernel_apply_feature`).  It does not keep the original action on observables outside
the feature family; the fields of `MicroscopicApproximation` read a kernel only through its
action on the features.  `paddedComposedApproximation` packages any composed step whose stage
branch types change with the step size, given a matrix expansion for every stage, as such a
padded approximation.

The approximation.  `multinomialPhysicalKernel_expansion` is the per-stage estimate.  The
resampling stages go through `MultinomialJetCertificate.apply_multinomialDriftStage_enlarged`,
equation (10) for the enlarged coordinates at the note's chromosome count, with a slack of
order `h`.  Every other stage is the stage of `TwoLocusStageComposition`.  The resampling
velocity is the corpus drift, so each stage acts through the same matrix
`TwoLocusStageComposition.physicalGenerator` (`multinomialPhysicalKernel_mulVec_expansion`).
`multinomialCompositionApproximation` is the resulting approximation.  At step `h > 0` its
kernel is the padded composite, which moves every enlarged coordinate exactly as the composite
does (`multinomialCompositionKernel_apply_feature`), and its error is
`StageCompositionKernel.compositeSlack`.

Scope.  The stages run in the fixed enumeration `TwoLocusStageComposition.stageOrder`; the
first-order law does not depend on the order, and no order is taken from the note.  At step
sizes `h ≤ 0` the kernel is the padded kernel that does not move, which the approximation does
not constrain.  Rate laws have strictly positive coalescence.  The error bound is crude and
explicit; no rate of convergence beyond "vanishes with `h`" is claimed.

## Empirical status

None.  The bodies here are algebra: finite averages of polynomial coordinates against
probability weights, a convex hull with a count of its atoms, and bounds between them.  No
measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.MultinomialStageComposition

open Coalescent
open Descent.Portability.FiniteMixtureKernel
open Descent.Portability.FiniteReproductiveKernel
open Descent.Portability.AffineCaratheodoryCount
open Descent.Portability.PulseJetExpansion
open Descent.Portability.PulseStageKernel
open Descent.Portability.EnlargedLowOrderLDGenerator
open Descent.Portability.TwoLocusMicroscopicKernel
open Descent.Portability.StageCompositionKernel
open Descent.Portability.TwoLocusStageComposition
open Descent.Portability.MultinomialDriftStage
open Descent.Portability.MultinomialJetCertificate

noncomputable section

/-! ## Padding a kernel to a fixed number of atoms -/

/-- **One kernel step is realized on `Fintype.card ι` atoms.**  If one feature coordinate is
identically one, the feature vector of one step of any kernel from any state is the feature
vector of a probability law on `Fintype.card ι` atoms. -/
theorem exists_paddedLaw {ι B X : Type*} [Fintype ι] [Fintype B] (feature : X → ι → ℝ)
    (constant : ι) (hconstant : ∀ x, feature x constant = 1) (kernel : FiniteMixtureKernel B X)
    (x : X) :
    ∃ p : Fin (Fintype.card ι) → ℝ, ∃ point : Fin (Fintype.card ι) → X,
      (∀ k, 0 ≤ p k) ∧ ∑ k, p k = 1 ∧
        featureVector p point feature = fun i ↦ kernel.apply (fun y ↦ feature y i) x := by
  classical
  refine exists_law_card_of_constant_coordinate feature constant hconstant _ ?_
  have hmember := featureVector_mem_convexHull (kernel.weight x) (kernel.weight_nonneg x)
    (kernel.weight_sum x) (fun branch ↦ kernel.move branch x) feature
  have hvector : featureVector (kernel.weight x) (fun branch ↦ kernel.move branch x) feature =
      fun i ↦ kernel.apply (fun y ↦ feature y i) x := by
    funext i
    simp only [featureVector_apply, FiniteMixtureKernel.apply]
  rw [hvector] at hmember
  exact hmember

/-- **A kernel padded to `Fintype.card ι` atoms.**  At every state the branches are the atoms of
a law realizing the kernel's one-step feature vector, with that law's weights. -/
def paddedKernel {ι B X : Type*} [Fintype ι] [Fintype B] (feature : X → ι → ℝ) (constant : ι)
    (hconstant : ∀ x, feature x constant = 1) (kernel : FiniteMixtureKernel B X) :
    FiniteMixtureKernel (Fin (Fintype.card ι)) X where
  weight x := Classical.choose (exists_paddedLaw feature constant hconstant kernel x)
  move k x := Classical.choose
    (Classical.choose_spec (exists_paddedLaw feature constant hconstant kernel x)) k
  weight_nonneg x := (Classical.choose_spec
    (Classical.choose_spec (exists_paddedLaw feature constant hconstant kernel x))).1
  weight_sum x := (Classical.choose_spec
    (Classical.choose_spec (exists_paddedLaw feature constant hconstant kernel x))).2.1

/-- **The padded kernel moves every feature coordinate as the original kernel does.** -/
theorem paddedKernel_apply_feature {ι B X : Type*} [Fintype ι] [Fintype B]
    (feature : X → ι → ℝ) (constant : ι) (hconstant : ∀ x, feature x constant = 1)
    (kernel : FiniteMixtureKernel B X) (x : X) (i : ι) :
    (paddedKernel feature constant hconstant kernel).apply (fun y ↦ feature y i) x =
      kernel.apply (fun y ↦ feature y i) x := by
  have hlaw := (Classical.choose_spec
    (Classical.choose_spec (exists_paddedLaw feature constant hconstant kernel x))).2.2
  have hcoordinate := congrFun hlaw i
  rw [featureVector_apply] at hcoordinate
  exact hcoordinate

/-! ## A padded composed approximation -/

/-- The kernel of a padded composed approximation at step `step`: at a positive step the
composition of the stages at that step, padded to `Fintype.card ι` atoms, and otherwise the
padded kernel that does not move. -/
def paddedComposedKernel {ι X : Type*} [Fintype ι] (feature : X → ι → ℝ) (constant : ι)
    (hconstant : ∀ x, feature x constant = 1) (stageCount : ℕ)
    (Branch : ℝ → Fin stageCount → Type) [∀ step k, Fintype (Branch step k)]
    (stages : ∀ step : ℝ, 0 < step → (k : Fin stageCount) → FiniteMixtureKernel (Branch step k) X)
    (step : ℝ) : FiniteMixtureKernel (Fin (Fintype.card ι)) X :=
  if hstep : 0 < step then
    paddedKernel feature constant hconstant
      (composeDependentStages stageCount (Branch step) (stages step hstep))
  else
    paddedKernel feature constant hconstant (FiniteMixtureKernel.deterministic id)

/-- **At a positive step the padded composed kernel moves every feature coordinate exactly as
the composition of the stages does.** -/
theorem paddedComposedKernel_apply_feature {ι X : Type*} [Fintype ι] (feature : X → ι → ℝ)
    (constant : ι) (hconstant : ∀ x, feature x constant = 1) (stageCount : ℕ)
    (Branch : ℝ → Fin stageCount → Type) [∀ step k, Fintype (Branch step k)]
    (stages : ∀ step : ℝ, 0 < step → (k : Fin stageCount) → FiniteMixtureKernel (Branch step k) X)
    {step : ℝ} (hstep : 0 < step) (x : X) (i : ι) :
    (paddedComposedKernel feature constant hconstant stageCount Branch stages step).apply
        (fun y ↦ feature y i) x =
      (composeDependentStages stageCount (Branch step) (stages step hstep)).apply
        (fun y ↦ feature y i) x := by
  rw [paddedComposedKernel, dif_pos hstep]
  exact paddedKernel_apply_feature feature constant hconstant _ x i

/-- **A composed step with step-dependent branch types, padded, is a microscopic
approximation.**  Stages indexed by `Fin stageCount`, whose branch types may change with the
step size, each advancing the features by `step` times its own matrix up to `step` times a
slack that vanishes with the step size, give a `MicroscopicApproximation` with branch type
`Fin (Fintype.card ι)` of any target generator that agrees with the summed stage matrices on
every feature vector, whenever one feature coordinate is identically one.  At a positive step
the kernel moves the features as the composed stages do (`paddedComposedKernel_apply_feature`),
and the error is the absolute value of `compositeSlack`. -/
def paddedComposedApproximation {ι X : Type*} [Fintype ι] (feature : X → ι → ℝ) (constant : ι)
    (hconstant : ∀ x, feature x constant = 1) (bound : ℝ) (hboundNonneg : 0 ≤ bound)
    (hbound : ∀ x i, |feature x i| ≤ bound) (stageCount : ℕ)
    (Branch : ℝ → Fin stageCount → Type) [∀ step k, Fintype (Branch step k)]
    (stages : ∀ step : ℝ, 0 < step → (k : Fin stageCount) → FiniteMixtureKernel (Branch step k) X)
    (generator : Fin stageCount → Matrix ι ι ℝ) (rowBound : ℝ) (hrowNonneg : 0 ≤ rowBound)
    (hrow : ∀ k i, ∑ d, |generator k i d| ≤ rowBound) (slack : Fin stageCount → ℝ → ℝ)
    (hslackNonneg : ∀ k step, 0 ≤ slack k step)
    (hslackTendsto : ∀ k, Filter.Tendsto (slack k) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0))
    (hstages : ∀ (step : ℝ) (hstep : 0 < step) k x i,
      |(stages step hstep k).apply (fun y ↦ feature y i) x - feature x i -
        step * (generator k).mulVec (feature x) i| ≤ step * slack k step)
    (target : Matrix ι ι ℝ)
    (htarget : ∀ x i, (∑ k, generator k).mulVec (feature x) i = target.mulVec (feature x) i) :
    MicroscopicApproximation (B := Fin (Fintype.card ι)) feature target where
  kernel := paddedComposedKernel feature constant hconstant stageCount Branch stages
  error step := |compositeSlack stageCount rowBound bound step (∑ k, slack k step)|
  error_nonneg _ := abs_nonneg _
  error_tendsto := by
    have hsum : Filter.Tendsto (fun step ↦ ∑ k, slack k step) (nhdsWithin 0 (Set.Ioi 0))
        (nhds 0) := by
      simpa using tendsto_finset_sum Finset.univ fun k _ ↦ hslackTendsto k
    exact abs_compositeSlack_tendsto stageCount rowBound bound
      (fun step ↦ ∑ k, slack k step) hsum
  expansion step hstep x i := by
    rw [paddedComposedKernel_apply_feature feature constant hconstant stageCount Branch stages
      hstep x i]
    have hbase := composeDependentStages_expansion feature bound hboundNonneg hbound rowBound
      hrowNonneg step hstep.le stageCount (Branch step) (stages step hstep) generator
      (fun k ↦ slack k step) hrow (fun k ↦ hslackNonneg k step) (hstages step hstep) x i
    rw [htarget x i] at hbase
    exact hbase.trans (mul_le_mul_of_nonneg_left (le_abs_self _) hstep.le)

/-! ## The physical stages with multinomial resampling -/

/-- The branch type of each physical stage at step `step`: a census of
`multinomialChromosomeCount c_i step` chromosomes for resampling in deme `i`, and a haplotype
label for every other stage. -/
def multinomialPhysicalBranch {D : ℕ} (rates : ManyDemeLDRates D) (step : ℝ) :
    PhysicalStage D → Type
  | .drift deme =>
      Counts TwoLocusHaplotype (multinomialChromosomeCount (rates.coalescence deme) step)
  | .migration => TwoLocusHaplotype
  | .recombination _ => TwoLocusHaplotype
  | .mutation _ => TwoLocusHaplotype

/-- Every physical stage branch type is finite. -/
instance multinomialPhysicalBranchFintype {D : ℕ} (rates : ManyDemeLDRates D) (step : ℝ) :
    (stage : PhysicalStage D) → Fintype (multinomialPhysicalBranch rates step stage)
  | .drift deme => inferInstanceAs (Fintype
      (Counts TwoLocusHaplotype (multinomialChromosomeCount (rates.coalescence deme) step)))
  | .migration => inferInstanceAs (Fintype TwoLocusHaplotype)
  | .recombination _ => inferInstanceAs (Fintype TwoLocusHaplotype)
  | .mutation _ => inferInstanceAs (Fintype TwoLocusHaplotype)

/-- The kernel of each physical stage at a positive step `step`: the multinomial resampling
kernel of NOTE1 section 2.3 with `⌈1/(c_i step)⌉` chromosomes in deme `i`, and the kernel of
`TwoLocusStageComposition` for every other stage. -/
def multinomialPhysicalKernel {D : ℕ} (rates : ManyDemeLDRates D) (step : ℝ) (hstep : 0 < step) :
    (stage : PhysicalStage D) →
      FiniteMixtureKernel (multinomialPhysicalBranch rates step stage) (DemeHaplotypeState D)
  | .drift deme => multinomialDriftKernel deme (one_le_multinomialChromosomeCount
      (rates.coalescence deme) step (rates.coalescence_pos deme) hstep)
  | .migration => physicalStageKernel rates .migration step
  | .recombination deme => physicalStageKernel rates (.recombination deme) step
  | .mutation deme => physicalStageKernel rates (.mutation deme) step

/-- The slack of each physical stage on one enlarged coordinate: the multinomial resampling
slack `c_i² h (107 M + B)`, of order `h`, and the slack of `TwoLocusStageComposition` for every
other stage. -/
def multinomialPhysicalSlack {D : ℕ} (rates : ManyDemeLDRates D)
    (coordinate : AffineEnlargedCoordinate D) : PhysicalStage D → ℝ → ℝ
  | .drift deme => fun step ↦ rates.coalescence deme ^ 2 * step *
      (107 * (JetPolynomialCertificate.enlarged coordinate).massBound +
        (enlargedStageExpansion coordinate).drift.bound)
  | .migration => physicalStageSlack rates coordinate .migration
  | .recombination deme => physicalStageSlack rates coordinate (.recombination deme)
  | .mutation deme => physicalStageSlack rates coordinate (.mutation deme)

/-- **Every physical stage with multinomial resampling expands to first order.**  One stage at
step `step` advances every enlarged coordinate by `step` times its rate-weighted velocity, up to
`step` times its slack.  The resampling velocity is the corpus drift at the coalescence rate. -/
theorem multinomialPhysicalKernel_expansion {D : ℕ} (rates : ManyDemeLDRates D) (step : ℝ)
    (hstep : 0 < step) (stage : PhysicalStage D) (coordinate : AffineEnlargedCoordinate D)
    (state : DemeHaplotypeState D) :
    |(multinomialPhysicalKernel rates step hstep stage).apply
          (fun y ↦ enlargedLowOrderLDFeature y coordinate) state -
        enlargedLowOrderLDFeature state coordinate -
        step * physicalStageDrift rates coordinate stage state| ≤
      step * multinomialPhysicalSlack rates coordinate stage step := by
  cases stage with
  | drift deme =>
      rw [enlargedFeature_eq_jet_value coordinate, ← enlargedCoordinateJet_value coordinate state]
      exact apply_multinomialDriftStage_enlarged coordinate deme (rates.coalescence deme) step
        (rates.coalescence_pos deme) hstep state
  | migration => exact physicalStageKernel_expansion rates .migration coordinate step hstep state
  | recombination deme =>
      exact physicalStageKernel_expansion rates (.recombination deme) coordinate step hstep state
  | mutation deme =>
      exact physicalStageKernel_expansion rates (.mutation deme) coordinate step hstep state

/-- Every physical stage slack vanishes with the step size. -/
theorem multinomialPhysicalSlack_tendsto {D : ℕ} (rates : ManyDemeLDRates D)
    (coordinate : AffineEnlargedCoordinate D) (stage : PhysicalStage D) :
    Filter.Tendsto (multinomialPhysicalSlack rates coordinate stage) (nhds 0) (nhds 0) := by
  cases stage with
  | drift deme =>
      have hcontinuous : Continuous fun step : ℝ ↦ rates.coalescence deme ^ 2 * step *
          (107 * (JetPolynomialCertificate.enlarged coordinate).massBound +
            (enlargedStageExpansion coordinate).drift.bound) := by
        fun_prop
      exact hcontinuous.tendsto' 0 0 (by simp)
  | migration => exact physicalStageSlack_tendsto rates coordinate .migration
  | recombination deme => exact physicalStageSlack_tendsto rates coordinate (.recombination deme)
  | mutation deme => exact physicalStageSlack_tendsto rates coordinate (.mutation deme)

/-- The slack of one physical stage with multinomial resampling over all enlarged
coordinates. -/
def multinomialCompositionStageSlack {D : ℕ} (rates : ManyDemeLDRates D)
    (stage : PhysicalStage D) (step : ℝ) : ℝ :=
  ∑ coordinate : AffineEnlargedCoordinate D,
    |multinomialPhysicalSlack rates coordinate stage step|

/-- The slack of each physical stage over all enlarged coordinates vanishes with the step
size. -/
theorem multinomialCompositionStageSlack_tendsto {D : ℕ} (rates : ManyDemeLDRates D)
    (stage : PhysicalStage D) :
    Filter.Tendsto (multinomialCompositionStageSlack rates stage) (nhdsWithin 0 (Set.Ioi 0))
      (nhds 0) :=
  sum_abs_slack_tendsto
    (fun coordinate step ↦ multinomialPhysicalSlack rates coordinate stage step)
    fun coordinate ↦ multinomialPhysicalSlack_tendsto rates coordinate stage

/-- **Each physical stage with multinomial resampling acts on the features through its own
matrix.**  One stage advances every enlarged coordinate by `step` times the stage matrix
`physicalGenerator` applied to the feature vector, up to `step` times its slack over all
coordinates. -/
theorem multinomialPhysicalKernel_mulVec_expansion {D : ℕ} (rates : ManyDemeLDRates D)
    (step : ℝ) (hstep : 0 < step) (stage : PhysicalStage D) (state : DemeHaplotypeState D)
    (coordinate : AffineEnlargedCoordinate D) :
    |(multinomialPhysicalKernel rates step hstep stage).apply
          (fun y ↦ enlargedLowOrderLDFeature y coordinate) state -
        enlargedLowOrderLDFeature state coordinate -
        step * (physicalGenerator rates stage).mulVec (enlargedLowOrderLDFeature state)
          coordinate| ≤
      step * multinomialCompositionStageSlack rates stage step := by
  have hbase := multinomialPhysicalKernel_expansion rates step hstep stage coordinate state
  rw [physicalStageDrift_eq_mulVec] at hbase
  refine hbase.trans (mul_le_mul_of_nonneg_left ?_ hstep.le)
  exact (le_abs_self _).trans (Finset.single_le_sum
    (f := fun other ↦ |multinomialPhysicalSlack rates other stage step|)
    (fun other _ ↦ abs_nonneg _) (Finset.mem_univ coordinate))

/-! ## The composed step and the approximation -/

/-- **The composed step with multinomial resampling.**  At a positive step `step`, every physical
stage of NOTE1 section 2.3, each at its own rate and with resampling drawing the note's
chromosome count, run in the fixed enumeration `stageOrder`.  A branch records a branch of every
stage, so the branch type changes with the step size. -/
def multinomialComposite {D : ℕ} (rates : ManyDemeLDRates D) (step : ℝ) (hstep : 0 < step) :
    FiniteMixtureKernel ((k : Fin (Fintype.card (PhysicalStage D))) →
      multinomialPhysicalBranch rates step ((stageOrder D).symm k)) (DemeHaplotypeState D) :=
  composeDependentStages (Fintype.card (PhysicalStage D))
    (fun k ↦ multinomialPhysicalBranch rates step ((stageOrder D).symm k))
    fun k ↦ multinomialPhysicalKernel rates step hstep ((stageOrder D).symm k)

/-- **NOTE1 equation (11) for the composed step with multinomial resampling, with nothing
assumed.**  The step that runs every physical stage of NOTE1 section 2.3 in a fixed order at
step `h`, with resampling drawing `⌈1/(c_i h)⌉` chromosomes in deme `i`, advances every enlarged
coordinate by `h · enlargedLowOrderLDGenerator rates` applied to the feature vector, uniformly
in the state, with an explicit error that vanishes with `h`.  The kernel is that step padded to
a fixed number of atoms, which moves the features exactly as the step does
(`multinomialCompositionKernel_apply_feature`). -/
def multinomialCompositionApproximation {D : ℕ} (rates : ManyDemeLDRates D) :
    MicroscopicApproximation (B := Fin (Fintype.card (AffineEnlargedCoordinate D)))
      (enlargedLowOrderLDFeature (D := D)) (enlargedLowOrderLDGenerator rates) :=
  paddedComposedApproximation (enlargedLowOrderLDFeature (D := D)) none (fun _ ↦ rfl)
    (compositionFeatureBound D) (compositionFeatureBound_nonneg D) abs_enlargedFeature_le
    (Fintype.card (PhysicalStage D))
    (fun step k ↦ multinomialPhysicalBranch rates step ((stageOrder D).symm k))
    (fun step hstep k ↦ multinomialPhysicalKernel rates step hstep ((stageOrder D).symm k))
    (fun k ↦ physicalGenerator rates ((stageOrder D).symm k)) (compositionRowBound rates)
    (Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦
      Finset.sum_nonneg fun _ _ ↦ abs_nonneg _)
    (fun k row ↦ physicalGenerator_row_le rates ((stageOrder D).symm k) row)
    (fun k step ↦ multinomialCompositionStageSlack rates ((stageOrder D).symm k) step)
    (fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ abs_nonneg _)
    (fun k ↦ multinomialCompositionStageSlack_tendsto rates ((stageOrder D).symm k))
    (fun step hstep k point other ↦ multinomialPhysicalKernel_mulVec_expansion rates step hstep
      ((stageOrder D).symm k) point other)
    (enlargedLowOrderLDGenerator rates)
    (fun state coordinate ↦ sum_physicalGenerator_mulVec rates state coordinate)

/-- **The approximation's kernel moves the features exactly as the literal composed step.**  At
every positive step, every enlarged coordinate is moved by the kernel as by the composition of
the physical stages with multinomial resampling. -/
theorem multinomialCompositionKernel_apply_feature {D : ℕ} (rates : ManyDemeLDRates D)
    {step : ℝ} (hstep : 0 < step) (state : DemeHaplotypeState D)
    (coordinate : AffineEnlargedCoordinate D) :
    ((multinomialCompositionApproximation rates).kernel step).apply
        (fun y ↦ enlargedLowOrderLDFeature y coordinate) state =
      (multinomialComposite rates step hstep).apply
        (fun y ↦ enlargedLowOrderLDFeature y coordinate) state :=
  paddedComposedKernel_apply_feature (enlargedLowOrderLDFeature (D := D)) none (fun _ ↦ rfl)
    (Fintype.card (PhysicalStage D))
    (fun step k ↦ multinomialPhysicalBranch rates step ((stageOrder D).symm k))
    (fun step hstep k ↦ multinomialPhysicalKernel rates step hstep ((stageOrder D).symm k))
    hstep state coordinate

end

end Descent.Portability.MultinomialStageComposition
