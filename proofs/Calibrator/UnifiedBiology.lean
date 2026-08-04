/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Calibrator.DeclaredInteractionClass
import Calibrator.ContinuumCalibration
import Calibrator.CorrectionWidths
import Calibrator.DescentGeometry
import Calibrator.DirichletTransfer
import Calibrator.ErgodicCovariancePencil
import Calibrator.EnsembleChannel
import Calibrator.HorizonCurve
import Calibrator.LandscapeSuperposition
import Calibrator.PencilEnvironment
import Calibrator.FunctionalDescent
import Calibrator.SpectralUniversalityFailure

namespace Calibrator

/-!
# Unified biology: state, geometry, value, and observation

This module gives the operator program a biological dictionary without conflating four
mathematically different layers.

* A finite state `x` is a population, ancestry, environment, age, or other biological
  context, and `transition x y` is its transport law.
* `Σ(x)` is observable genotype geometry.  Its generalized eigenvalues are handled by
  `Calibrator.ErgodicCovariancePencil`.
* `θ(x)` is context-specific biological value.  The cost of adapting a readout to it is
  handled by `Calibrator.DirichletTransfer`.
* A probe exposes the parameter only modulo a declared nuisance class.  Identification is
  governed by `Calibrator.DeclaredInteractionClass`, independently of the transport and
  pencil calculations.

The separation matters.  Averaging a target-only score after a stationary transition cannot
measure temporal portability: stationarity removes the transition exactly.  A genuinely
temporal quantity must couple source and target, for example by evaluating a source-chosen
readout at the target or by taking an autocorrelation.  The first section proves this repair
and gives a two-state witness where every target-only average agrees while cross-state
performance changes from perfect to zero.

The final theorem packages eight independent obstructions that a unified biological model
must keep visible: stationarity blindness, loss of joint dependence under marginal summaries,
rank-two value/allocation conflict even in a common eigenbasis, failure of freeness for
operators sharing a local genomic geometry, and four failures of *descent* — of a criterion to
be a function of the label it is reported against.  The descent layer comes from
`Calibrator.DescentGeometry`: a cross-state criterion is not a function of the target context,
reportability along each margin does not compose to the pair, dropping a stratum destroys
reportability both finer labels have, and — although every functional descends along posterior
ancestry — the ancestry-weighted average of component values is not the descended report.

## Epistemic boundary

This file does not promote the analytic claims in the motivating program to Lean theorems.
In particular, Donsker--Varadhan regularity, infinite-volume density of states, a Thouless
formula, Minami/Poisson statistics, and hard-edge random-operator limits require hypotheses
and proofs absent from this corpus.  The formal content here is finite and exact; those
claims remain research interfaces rather than axioms disguised as results.
-/

open scoped BigOperators

/-! ## Cohort landscape superposition

Independent cohort objectives add as landscapes, while their covariance kernels add with
squared row weights.  The exact level-resolved calculus therefore gives only a persistence
theorem: a common forbidden overlap at every admissible pair of cohort levels remains
forbidden after pooling.  It does not prove dissolution.  The explicit spherical calculation
below records the complementary biological mechanism: genetic structure shared by cohorts
survives mixing, whereas cohort-specific higher-order structure is diluted.
-/

section CohortLandscapeSuperposition

variable {Cohort Genotype Overlap : Type*}

/-- A level-resolved forbidden overlap in at least one cohort remains forbidden for the pooled
cohort objective.  In biological language, pooling cannot create a pair of high-fitness
genotypes unless every cohort admits that overlap at the component levels realized by the
pair. -/
theorem pooledCohort_forbiddenOverlap_of_levelResolved_cover
    (active : Finset Cohort) (weight : Cohort → ℝ) (fitness : Cohort → Genotype → ℝ)
    (overlap : Genotype → Genotype → Overlap) (target : ℝ)
    (hweight : ∀ cohort ∈ active, 0 ≤ weight cohort) (q : Overlap)
    (hcover : ∀ leftLevel rightLevel,
      AdmissibleLevels active weight target leftLevel →
        AdmissibleLevels active weight target rightLevel →
          ∃ cohort ∈ active,
            q ∉ ComponentAchievableOverlaps fitness overlap leftLevel rightLevel cohort) :
    q ∉ SuperposedAchievableOverlaps active weight fitness overlap target :=
  forbiddenOverlap_of_levelResolved_cover active weight fitness overlap target hweight q hcover

end CohortLandscapeSuperposition

/-! ## Population overlap geometry under ancestry-environment mixing -/

/-- The active sparse-LD correlation after pooling two environments with correlations `rho`
and `-rho`.  This is the biological name for the exact landscape parameter. -/
noncomputable def ancestryMixtureCorrelation (rho positiveEnvironmentMass : ℝ) : ℝ :=
  mixedEnvironmentCorrelation rho positiveEnvironmentMass

/-- A balanced ancestry-environment mixture cancels the active correlation exactly. -/
@[simp] theorem ancestryMixtureCorrelation_balanced (rho : ℝ) :
    ancestryMixtureCorrelation rho (1 / 2) = 0 := by
  exact mixedEnvironmentCorrelation_half rho

/-- **Two individually gapped LD environments can pool to an ungapped population profile.**

At active correlation `4/5`, both signs lie beyond the golden threshold and have a negative
population gap certificate.  Equal environment mass cancels the active correlation, leaving
certificate one.  This is a population-landscape statement only: it does not infer a
polynomial-time algorithm from absence of the gap. -/
theorem ancestryMixture_pure_gapped_balanced_ungapped :
    populationGapCertificate (4 / 5) < 0 ∧
      populationGapCertificate (-(4 / 5)) < 0 ∧
      populationGapCertificate (ancestryMixtureCorrelation (4 / 5) (1 / 2)) = 1 := by
  have hthreshold : goldenCorrelationThreshold < (4 / 5 : ℝ) := by
    have hgold := goldenCorrelationThreshold_sq_add_self
    have hpositive := goldenCorrelationThreshold_mem_Ioo.1
    nlinarith
  have habsPositive : |(4 / 5 : ℝ)| = 4 / 5 := by norm_num
  have habsNegative : |(-(4 / 5) : ℝ)| = 4 / 5 := by norm_num
  have hpositive := populationGapCertificate_neg_of_golden_lt_abs
    (4 / 5) (by norm_num) (by rw [habsPositive]; exact hthreshold)
  have hnegative := populationGapCertificate_neg_of_golden_lt_abs
    (-(4 / 5)) (by norm_num) (by rw [habsNegative]; exact hthreshold)
  refine ⟨hpositive, hnegative, ?_⟩
  simp [ancestryMixtureCorrelation, mixedEnvironmentCorrelation, populationGapCertificate]

section StationarityRepair

variable {State : Type*} [Fintype State]

/-- Mean performance of a target-only biological score under the one-point state law. -/
noncomputable def onePointPerformance (weight : State → ℝ) (score : State → ℝ) : ℝ :=
  ∑ y, weight y * score y

/-- Mean performance obtained by transporting to `y` and then evaluating a score that sees
only `y`.  Under stationarity this is exactly `onePointPerformance`; it contains no temporal
information. -/
noncomputable def targetOnlyTransportPerformance
    (weight : State → ℝ) (transition : State → State → ℝ) (score : State → ℝ) : ℝ :=
  ∑ x, weight x * ∑ y, transition x y * score y

/-- A source-target performance.  Unlike `targetOnlyTransportPerformance`, the quality can
depend on the source decision and the target state simultaneously. -/
noncomputable def crossStatePerformance
    (weight : State → ℝ) (transition : State → State → ℝ)
    (quality : State → State → ℝ) : ℝ :=
  ∑ x, weight x * ∑ y, transition x y * quality x y

/-- **Stationarity repair.**  A target-only average after a stationary transition is the
one-point average, exactly.  Thus a lag parameter in this expression is syntactic but not
identified by the value. -/
theorem targetOnlyTransportPerformance_eq_onePoint
    (weight : State → ℝ) (transition : State → State → ℝ) (score : State → ℝ)
    (hstationary : ∀ y, ∑ x, weight x * transition x y = weight y) :
    targetOnlyTransportPerformance weight transition score =
      onePointPerformance weight score := by
  unfold targetOnlyTransportPerformance onePointPerformance
  calc
    ∑ x, weight x * ∑ y, transition x y * score y =
        ∑ x, ∑ y, weight x * (transition x y * score y) := by
          apply Finset.sum_congr rfl
          intro x _
          rw [Finset.mul_sum]
    _ = ∑ y, ∑ x, weight x * (transition x y * score y) := Finset.sum_comm
    _ = ∑ y, (∑ x, weight x * transition x y) * score y := by
          apply Finset.sum_congr rfl
          intro y _
          simp_rw [← mul_assoc]
          rw [← Finset.sum_mul]
    _ = ∑ y, weight y * score y := by
          apply Finset.sum_congr rfl
          intro y _
          rw [hstationary y]

end StationarityRepair

/-! ## An exact two-state biological witness -/

abbrev BinaryBiologicalState := Fin 2

/-- Uniform invariant law on two biological contexts. -/
noncomputable def binaryStateWeight (_ : BinaryBiologicalState) : ℝ := 1 / 2

/-- The biological context law is the canonical balanced calibration weight. -/
@[simp] theorem binaryStateWeight_eq_balancedBinaryWeight (x : BinaryBiologicalState) :
    binaryStateWeight x = balancedBinaryWeight x := by
  rfl

/-- A transition that preserves the context. -/
noncomputable def persistentTransition
    (x y : BinaryBiologicalState) : ℝ := if x = y then 1 else 0

/-- A transition that swaps the two contexts. -/
noncomputable def switchingTransition
    (x y : BinaryBiologicalState) : ℝ := if x = y then 0 else 1

/-- A target-only annotation distinguishing state `1`. -/
noncomputable def targetAnnotation (y : BinaryBiologicalState) : ℝ :=
  if y = 1 then 1 else 0

/-- Quality of a source-adapted readout: one exactly when source and target contexts match. -/
noncomputable def contextMatchQuality
    (x y : BinaryBiologicalState) : ℝ := if x = y then 1 else 0

/-- **The two-context biological witness runs on the horizon-curve kernels.**

`HorizonCurve.stayKernel` is the Kronecker delta on two states, and so are the transition
that preserves the biological context and the readout quality of a design used in the
context it was built for — `HorizonCurve.agreement` is that same delta read as an
efficiency. Four readings, one matrix: the biological witness is not a second two-state
example but the horizon example under biological names, and a change to either file's
delta contradicts this. -/
theorem persistentTransition_contextMatchQuality_agreement_eq_stayKernel
    (x y : BinaryBiologicalState) :
    persistentTransition x y = stayKernel x y ∧
      contextMatchQuality x y = stayKernel x y ∧
        agreement x y = stayKernel x y :=
  ⟨rfl, rfl, rfl⟩

/-- **Complete context switching is the horizon curve's swap kernel**, the off-diagonal
counterpart of the identification above. -/
theorem switchingTransition_eq_swapKernel (x y : BinaryBiologicalState) :
    switchingTransition x y = swapKernel x y := rfl

theorem binaryStateWeight_stationary_persistent (y : BinaryBiologicalState) :
    ∑ x, binaryStateWeight x * persistentTransition x y = binaryStateWeight y := by
  fin_cases y <;>
    norm_num [binaryStateWeight, persistentTransition, Fin.sum_univ_two]

theorem binaryStateWeight_stationary_switching (y : BinaryBiologicalState) :
    ∑ x, binaryStateWeight x * switchingTransition x y = binaryStateWeight y := by
  fin_cases y <;>
    norm_num [binaryStateWeight, switchingTransition, Fin.sum_univ_two]

/-- Target-only performance is identical under persistence and complete switching. -/
theorem targetOnlyPerformance_blind_to_binary_dynamics :
    targetOnlyTransportPerformance binaryStateWeight persistentTransition targetAnnotation =
      targetOnlyTransportPerformance binaryStateWeight switchingTransition targetAnnotation := by
  rw [targetOnlyTransportPerformance_eq_onePoint _ _ _
      binaryStateWeight_stationary_persistent]
  rw [targetOnlyTransportPerformance_eq_onePoint _ _ _
      binaryStateWeight_stationary_switching]

/-- Cross-state performance detects the dynamics: a source-adapted readout is perfect when
the context persists. -/
theorem crossStatePerformance_persistent_eq_one :
    crossStatePerformance binaryStateWeight persistentTransition contextMatchQuality = 1 := by
  norm_num [crossStatePerformance, binaryStateWeight, persistentTransition,
    contextMatchQuality, Fin.sum_univ_two]

/-- The same readout has zero value when the context always switches. -/
theorem crossStatePerformance_switching_eq_zero :
    crossStatePerformance binaryStateWeight switchingTransition contextMatchQuality = 0 := by
  norm_num [crossStatePerformance, binaryStateWeight, switchingTransition,
    contextMatchQuality, Fin.sum_univ_two]

/-! ## The stationarity repair is a descent failure

The repair above says a target-only average cannot see the dynamics.  `Calibrator.DescentGeometry`
says what kind of statement that is: the target context is a *label*, the two dynamics are two
*populations* on source-target pairs, and a criterion is reportable by target context exactly
when it descends along that label.  The target-only annotation descends; the source-adapted
quality does not.  So the quantity a cross-state criterion measures is a function of the pair
(target context, population), not of the target context — which is why no relabelling of the
target average recovers it. -/

/-- A source-target pair of biological contexts. -/
abbrev TransportPair := BinaryBiologicalState × BinaryBiologicalState

/-- The joint law of source and target contexts under a transition. -/
noncomputable def jointTransportLaw
    (transition : BinaryBiologicalState → BinaryBiologicalState → ℝ) (g : TransportPair) : ℝ :=
  binaryStateWeight g.1 * transition g.1 g.2

/-- The two-population family: the context persists, or the context switches. -/
noncomputable def binaryTransportFamily (persists : Bool) : TransportPair → ℝ :=
  jointTransportLaw (if persists then persistentTransition else switchingTransition)

/-- Both members of the persistence/switching family are genuine nonnegative finite laws. -/
theorem binaryTransportFamily_nonneg (persists : Bool) (g : TransportPair) :
    0 ≤ binaryTransportFamily persists g := by
  rcases g with ⟨x, y⟩
  cases persists <;> fin_cases x <;> fin_cases y <;>
    norm_num [binaryTransportFamily, jointTransportLaw, binaryStateWeight,
      persistentTransition, switchingTransition]

/-- Target-only performance is the mean of a target-measurable kernel under the joint law. -/
theorem targetOnlyTransportPerformance_eq_conditionalSectionMean
    (transition : BinaryBiologicalState → BinaryBiologicalState → ℝ)
    (score : BinaryBiologicalState → ℝ) :
    targetOnlyTransportPerformance binaryStateWeight transition score =
      conditionalSectionMean (fun g : TransportPair ↦ score g.2)
        (jointTransportLaw transition) := by
  rw [targetOnlyTransportPerformance, conditionalSectionMean, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ ↦ ?_
  rw [jointTransportLaw]
  ring

/-- Cross-state performance is the mean of a kernel that reads both coordinates. -/
theorem crossStatePerformance_eq_conditionalSectionMean
    (transition : BinaryBiologicalState → BinaryBiologicalState → ℝ)
    (quality : BinaryBiologicalState → BinaryBiologicalState → ℝ) :
    crossStatePerformance binaryStateWeight transition quality =
      conditionalSectionMean (fun g : TransportPair ↦ quality g.1 g.2)
        (jointTransportLaw transition) := by
  rw [crossStatePerformance, conditionalSectionMean, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ ↦ ?_
  rw [jointTransportLaw]
  ring

/-- Both dynamics put half the mass on each target context. -/
theorem labelMass_binaryTransportFamily (persists : Bool) (y : BinaryBiologicalState) :
    labelMass (fun g : TransportPair ↦ g.2) (binaryTransportFamily persists) y = 1 / 2 := by
  cases persists <;> fin_cases y <;>
    norm_num [labelMass, binaryTransportFamily, jointTransportLaw, binaryStateWeight,
      persistentTransition, switchingTransition, Fintype.sum_prod_type, Fin.sum_univ_two]

/-- Every fiber of either transport family carries mass, so the fiber conditional is
defined at every state.

Both diameter theorems below open by establishing this for `true` and for `false`, and both
did it by rewriting `labelMass_binaryTransportFamily` and calling `norm_num`, twice each.
Stated once, the four copies become four applications. -/
theorem labelMass_binaryTransportFamily_ne_zero (persists : Bool)
    (y : BinaryBiologicalState) :
    labelMass (fun g : TransportPair ↦ g.2) (binaryTransportFamily persists) y ≠ 0 := by
  rw [labelMass_binaryTransportFamily]
  norm_num

/-- A target-only annotation descends along the target context: it is reportable there. -/
theorem descends_targetAnnotation_along_targetState :
    DescendsAlong (fun g : TransportPair ↦ g.2) binaryTransportFamily
      (conditionalSectionMean (fun g : TransportPair ↦ targetAnnotation g.2)) :=
  descendsAlong_sectionMean_of_labelFunction _ binaryTransportFamily targetAnnotation

/-- Under persistence, the source-adapted readout is perfect on every target fiber. -/
theorem contextMatchQuality_value_persistent (y : BinaryBiologicalState) :
    conditionalSectionMean (fun g : TransportPair ↦ contextMatchQuality g.1 g.2)
      (fiberConditional (fun g : TransportPair ↦ g.2) (binaryTransportFamily true) y) = 1 := by
  rw [conditionalSectionMean_fiberConditional, labelMass_binaryTransportFamily]
  fin_cases y <;>
    norm_num [binaryTransportFamily, jointTransportLaw, binaryStateWeight, persistentTransition,
      contextMatchQuality, Fintype.sum_prod_type, Fin.sum_univ_two]

/-- Under complete switching, the same readout is worthless on the same fiber. -/
theorem contextMatchQuality_value_switching (y : BinaryBiologicalState) :
    conditionalSectionMean (fun g : TransportPair ↦ contextMatchQuality g.1 g.2)
      (fiberConditional (fun g : TransportPair ↦ g.2) (binaryTransportFamily false) y) = 0 := by
  rw [conditionalSectionMean_fiberConditional, labelMass_binaryTransportFamily]
  fin_cases y <;>
    norm_num [binaryTransportFamily, jointTransportLaw, binaryStateWeight, switchingTransition,
      contextMatchQuality, Fintype.sum_prod_type, Fin.sum_univ_two]

/-- **The cross-state criterion does not descend along the target context.**  No function of the
target context reproduces it across the two dynamics, so a temporal criterion is a function of
the pair (context, population).  The target-only annotation of the previous theorem does descend:
descent, not sensitivity, is what separates the two quantities. -/
theorem not_descends_contextMatchQuality_along_targetState :
  ¬ DescendsAlong (fun g : TransportPair ↦ g.2) binaryTransportFamily
      (conditionalSectionMean (fun g : TransportPair ↦ contextMatchQuality g.1 g.2)) := by
  rintro ⟨value, hvalue⟩
  have hpersist := hvalue true 0 (by
    change labelMass (fun g : TransportPair ↦ g.2) (binaryTransportFamily true) 0 ≠ 0
    rw [labelMass_binaryTransportFamily]
    norm_num)
  have hswitch := hvalue false 0 (by
    change labelMass (fun g : TransportPair ↦ g.2) (binaryTransportFamily false) 0 ≠ 0
    rw [labelMass_binaryTransportFamily]
    norm_num)
  change conditionalSectionMean (fun g : TransportPair ↦ contextMatchQuality g.1 g.2)
      (fiberConditional (fun g : TransportPair ↦ g.2) (binaryTransportFamily true) 0) = value 0
    at hpersist
  change conditionalSectionMean (fun g : TransportPair ↦ contextMatchQuality g.1 g.2)
      (fiberConditional (fun g : TransportPair ↦ g.2) (binaryTransportFamily false) 0) = value 0
    at hswitch
  rw [contextMatchQuality_value_persistent 0] at hpersist
  rw [contextMatchQuality_value_switching 0] at hswitch
  rw [← hpersist] at hswitch
  norm_num at hswitch

/-- The largest change in source-adapted context-match quality across supported biological
dynamics at one target state.

Empirical status: NOT AN EMPIRICAL CLAIM -- this is an exact finite section oscillation. -/
noncomputable def contextMatchSectionOscillation (y : BinaryBiologicalState) : ℝ :=
  finiteSectionOscillation
    (fun persists y ↦
      labelMass (fun g : TransportPair ↦ g.2) (binaryTransportFamily persists) y ≠ 0)
    (fun persists y ↦
      fiberConditional (fun g : TransportPair ↦ g.2) (binaryTransportFamily persists) y)
    (conditionalSectionMean (fun g : TransportPair ↦ contextMatchQuality g.1 g.2))
    (fun a b : ℝ ↦ |a - b|) y

/-- The total-variation diameter of supported dynamics on one biological target-state fiber.

Empirical status: NOT AN EMPIRICAL CLAIM -- this is an exact finite section diameter. -/
noncomputable def contextMatchTotalVariationDiameter (y : BinaryBiologicalState) : ℝ :=
  finiteSectionDiameter
    (fun persists y ↦
      labelMass (fun g : TransportPair ↦ g.2) (binaryTransportFamily persists) y ≠ 0)
    (fun persists y ↦
      fiberConditional (fun g : TransportPair ↦ g.2) (binaryTransportFamily persists) y)
    totalVariationGap y

/-- **Sharp range-sensitive portability bound for the two-dynamics family.**  Across persistence
and switching, the largest observable change in source-adapted quality on a target-state fiber is
bounded by half the `ℓ¹` total-variation diameter.  The factor `1/2` uses both facts that the fiber
conditionals are probability laws and that quality lies in `[0,1]`; the cruder sup-norm argument
loses this factor.  The maximum is over the whole finite family, not a pointwise restatement. -/
theorem contextMatch_sectionOscillation_le_half_totalVariationDiameter
    (y : BinaryBiologicalState) :
    contextMatchSectionOscillation y ≤ contextMatchTotalVariationDiameter y / 2 := by
  unfold contextMatchSectionOscillation contextMatchTotalVariationDiameter
  apply finiteSectionOscillation_le_modulus_diameter
      (omega := fun t ↦ t / 2) (x := y)
  · exact totalVariationGap_nonneg
  · intro s t hst
    linarith
  · norm_num
  · intro persists switches hpersist hswitch
    have hquality : ∀ g : TransportPair,
        0 ≤ contextMatchQuality g.1 g.2 ∧ contextMatchQuality g.1 g.2 ≤ 1 := by
      rintro ⟨x, z⟩
      fin_cases x <;> fin_cases z <;> norm_num [contextMatchQuality]
    have hbound := abs_sectionMean_sub_le_half_range
      (fun g : TransportPair ↦ contextMatchQuality g.1 g.2)
      (fiberConditional (fun g : TransportPair ↦ g.2) (binaryTransportFamily persists) y)
      (fiberConditional (fun g : TransportPair ↦ g.2) (binaryTransportFamily switches) y)
      0 1 hquality
      (sum_fiberConditional (fun g : TransportPair ↦ g.2)
        (binaryTransportFamily persists) y hpersist)
      (sum_fiberConditional (fun g : TransportPair ↦ g.2)
        (binaryTransportFamily switches) y hswitch)
    simpa [div_eq_mul_inv, mul_comm] using hbound

/-- The two biological conditionals are opposite point masses on every target fiber, so their
`ℓ¹` total-variation diameter is exactly two. -/
theorem contextMatch_totalVariationDiameter_eq_two (y : BinaryBiologicalState) :
    contextMatchTotalVariationDiameter y = 2 := by
  unfold contextMatchTotalVariationDiameter
  apply le_antisymm
  · apply finiteSectionDiameter_le_of_pairwise
      (supported := fun persists y ↦
        labelMass (fun g : TransportPair ↦ g.2) (binaryTransportFamily persists) y ≠ 0)
      (conditionalSection := fun persists y ↦
        fiberConditional (fun g : TransportPair ↦ g.2) (binaryTransportFamily persists) y)
      (rho := totalVariationGap) (x := y) (C := 2) (by norm_num)
    intro persists switches hpersist hswitch
    apply totalVariationGap_le_two_of_probabilityMasses
    · intro g
      exact fiberConditional_nonneg (fun g : TransportPair ↦ g.2)
        (binaryTransportFamily persists) y (binaryTransportFamily_nonneg persists) hpersist g
    · intro g
      exact fiberConditional_nonneg (fun g : TransportPair ↦ g.2)
        (binaryTransportFamily switches) y (binaryTransportFamily_nonneg switches) hswitch g
    · exact sum_fiberConditional (fun g : TransportPair ↦ g.2)
        (binaryTransportFamily persists) y hpersist
    · exact sum_fiberConditional (fun g : TransportPair ↦ g.2)
        (binaryTransportFamily switches) y hswitch
  · have hpersist := labelMass_binaryTransportFamily_ne_zero true y
    have hswitch := labelMass_binaryTransportFamily_ne_zero false y
    have hlower := sectionPairDistance_le_finiteSectionDiameter
      (fun persists y ↦
        labelMass (fun g : TransportPair ↦ g.2) (binaryTransportFamily persists) y ≠ 0)
      (fun persists y ↦
        fiberConditional (fun g : TransportPair ↦ g.2) (binaryTransportFamily persists) y)
      totalVariationGap y true false hpersist hswitch
    have hgap :
        totalVariationGap
          (fiberConditional (fun g : TransportPair ↦ g.2) (binaryTransportFamily true) y)
          (fiberConditional (fun g : TransportPair ↦ g.2) (binaryTransportFamily false) y) = 2 := by
      fin_cases y <;>
        norm_num [totalVariationGap, fiberConditional, labelMass, binaryTransportFamily,
          jointTransportLaw, binaryStateWeight, persistentTransition, switchingTransition,
          Fintype.sum_prod_type, Fin.sum_univ_two]
    rwa [hgap] at hlower

/-- **The quantitative obstruction is attained.**  On every target state the source-adapted
readout changes from one under persistence to zero under switching, so the section oscillation is
exactly one.  Together with `contextMatch_totalVariationDiameter_eq_two`, this proves equality in
the sharp range-sensitive bound above rather than merely exhibiting non-descent. -/
theorem contextMatch_sectionOscillation_eq_one (y : BinaryBiologicalState) :
    contextMatchSectionOscillation y = 1 := by
  unfold contextMatchSectionOscillation
  apply le_antisymm
  · calc
      finiteSectionOscillation
          (fun persists y ↦
            labelMass (fun g : TransportPair ↦ g.2) (binaryTransportFamily persists) y ≠ 0)
          (fun persists y ↦
            fiberConditional (fun g : TransportPair ↦ g.2) (binaryTransportFamily persists) y)
          (conditionalSectionMean (fun g : TransportPair ↦ contextMatchQuality g.1 g.2))
          (fun a b : ℝ ↦ |a - b|) y ≤
          finiteSectionDiameter
            (fun persists y ↦
              labelMass (fun g : TransportPair ↦ g.2) (binaryTransportFamily persists) y ≠ 0)
            (fun persists y ↦
              fiberConditional (fun g : TransportPair ↦ g.2) (binaryTransportFamily persists) y)
            totalVariationGap y / 2 :=
        contextMatch_sectionOscillation_le_half_totalVariationDiameter y
      _ = 1 := by
        change contextMatchTotalVariationDiameter y / 2 = 1
        rw [contextMatch_totalVariationDiameter_eq_two]
        norm_num
  · have hpersist := labelMass_binaryTransportFamily_ne_zero true y
    have hswitch := labelMass_binaryTransportFamily_ne_zero false y
    have hlower := sectionPairValueDistance_le_finiteSectionOscillation
      (fun persists y ↦
        labelMass (fun g : TransportPair ↦ g.2) (binaryTransportFamily persists) y ≠ 0)
      (fun persists y ↦
        fiberConditional (fun g : TransportPair ↦ g.2) (binaryTransportFamily persists) y)
      (conditionalSectionMean (fun g : TransportPair ↦ contextMatchQuality g.1 g.2))
      (fun a b : ℝ ↦ |a - b|) y true false hpersist hswitch
    rw [contextMatchQuality_value_persistent y, contextMatchQuality_value_switching y] at hlower
    norm_num at hlower ⊢
    exact hlower

/-! ## Continuum-calibration core, instantiated in biology -/

/-- With no information favoring persistence over switching after observing the target context,
the posterior on the two biological dynamics is uniform. -/
noncomputable def binaryDynamicsPosterior
    (_ : BinaryBiologicalState) (_ : Bool) : ℝ := 1 / 2

/-- The uninformative dynamics posterior is the canonical balanced calibration weight. -/
@[simp] theorem binaryDynamicsPosterior_eq_balancedBinaryWeight
    (y : BinaryBiologicalState) (persists : Bool) :
    binaryDynamicsPosterior y persists = balancedBinaryWeight persists := by
  rfl

/-- Conditional source-adapted quality for one dynamics and one target context, constructed from
the same fiber conditional used by the descent theorem above. -/
noncomputable def binaryConditionalContextMatch
    (persists : Bool) (y : BinaryBiologicalState) : ℝ :=
  conditionalSectionMean (fun g : TransportPair ↦ contextMatchQuality g.1 g.2)
    (fiberConditional (fun g : TransportPair ↦ g.2) (binaryTransportFamily persists) y)

/-- The constructed conditional-quality field is one for persistence and zero for switching. -/
@[simp] theorem binaryConditionalContextMatch_eq_indicator
    (persists : Bool) (y : BinaryBiologicalState) :
    binaryConditionalContextMatch persists y = if persists then 1 else 0 := by
  cases persists
  · simp [binaryConditionalContextMatch, contextMatchQuality_value_switching]
  · simp [binaryConditionalContextMatch, contextMatchQuality_value_persistent]

/-- The binary dynamics posterior is normalized on every biological target context. -/
theorem binaryDynamicsPosterior_sum_eq_one (y : BinaryBiologicalState) :
    ∑ persists, binaryDynamicsPosterior y persists = 1 := by
  norm_num [binaryDynamicsPosterior]

/-- Pooling persistence and switching makes the source-adapted quality look exactly one-half on
every target context.  This is the posterior-mean predictor of the calibration core. -/
theorem posteriorMean_binaryConditionalContextMatch_eq_half (y : BinaryBiologicalState) :
    posteriorMean binaryDynamicsPosterior binaryConditionalContextMatch y = 1 / 2 := by
  norm_num [posteriorMean, binaryDynamicsPosterior]

/-- **Biological drift defect.**  Persistence has conditional quality one and switching has
quality zero, while the pooled posterior mean is one-half.  Averaging across the two target
contexts leaves an irreducible squared index-wise calibration defect of exactly `1/4`. -/
theorem binaryContextMatch_calibrationDriftDefectSq_eq_quarter :
    calibrationDriftDefectSq binaryStateWeight binaryDynamicsPosterior
      binaryConditionalContextMatch = 1 / 4 := by
  have hposterior : binaryDynamicsPosterior =
      twoIndexPosterior (fun _ : BinaryBiologicalState ↦ 1 / 2) := by
    funext y persists
    cases persists <;> norm_num [binaryDynamicsPosterior, twoIndexPosterior]
  have hconditional : binaryConditionalContextMatch =
      twoIndexConditional (fun _ : BinaryBiologicalState ↦ 1)
        (fun _ : BinaryBiologicalState ↦ 0) := by
    funext persists y
    rw [binaryConditionalContextMatch_eq_indicator]
    cases persists <;> norm_num [twoIndexConditional]
  rw [hposterior, hconditional, twoIndex_calibrationDriftDefectSq_eq]
  norm_num [binaryStateWeight, Fin.sum_univ_two]

/-- **The biological defect is pairwise disagreement.**  The quarter-unit portability loss is
exactly half the expected squared quality difference between two independent posterior draws of
the biological dynamics, averaged over target contexts.  Thus the binary persistence/switching
calculation is a concrete face of the arbitrary finite-population pairwise drift law rather than
an isolated two-state formula. -/
theorem binaryContextMatch_pairwiseCalibrationDriftEnergy_eq_quarter :
    pairwiseCalibrationDriftEnergy binaryStateWeight binaryDynamicsPosterior
      binaryConditionalContextMatch = 1 / 4 := by
  rw [← calibrationDriftDefectSq_eq_pairwiseCalibrationDriftEnergy
    binaryStateWeight binaryDynamicsPosterior binaryConditionalContextMatch
    binaryDynamicsPosterior_sum_eq_one]
  exact binaryContextMatch_calibrationDriftDefectSq_eq_quarter

/-- At each target context, the same pairwise disagreement price is already `1/4`; averaging over
contexts does not create the obstruction, it only preserves a pointwise ancestry/dynamics defect. -/
theorem binaryContextMatch_posteriorPairwiseDriftEnergy_eq_quarter
    (y : BinaryBiologicalState) :
    posteriorPairwiseDriftEnergy binaryDynamicsPosterior
      binaryConditionalContextMatch y = 1 / 4 := by
  rw [posteriorPairwiseDriftEnergy_eq_posteriorDriftEnergy
    binaryDynamicsPosterior binaryConditionalContextMatch y
    (binaryDynamicsPosterior_sum_eq_one y)]
  norm_num [posteriorDrift, posteriorMean_binaryConditionalContextMatch_eq_half,
    binaryDynamicsPosterior]

/-- A sealed support boundary: the deployed population contains only persistent dynamics and
assigns zero posterior mass to switching dynamics.  The conditional field is unchanged; only its
represented support changes. -/
noncomputable def persistentOnlyDynamicsPosterior
    (_ : BinaryBiologicalState) (persists : Bool) : ℝ := binarySecondAnnotation persists

/-- The support-sealed biological posterior remains normalized. -/
theorem persistentOnlyDynamicsPosterior_sum_eq_one (y : BinaryBiologicalState) :
    ∑ persists, persistentOnlyDynamicsPosterior y persists = 1 := by
  norm_num [persistentOnlyDynamicsPosterior, binarySecondAnnotation]

/-- Its posterior masses are nonnegative. -/
theorem persistentOnlyDynamicsPosterior_nonnegative
    (y : BinaryBiologicalState) (persists : Bool) :
    0 ≤ persistentOnlyDynamicsPosterior y persists := by
  cases persists <;> norm_num [persistentOnlyDynamicsPosterior, binarySecondAnnotation]

/-- **Biological sealing law at zero support.**  Persistence and switching still have conditional
qualities one and zero, but after switching receives zero posterior mass the calibration defect is
exactly zero.  This is not conditional invariance; it is categorical blindness created by the
support wall, and it is certified by the general support-aware theorem. -/
theorem persistentOnly_contextMatch_calibrationDriftDefectSq_eq_zero :
    calibrationDriftDefectSq binaryStateWeight persistentOnlyDynamicsPosterior
      binaryConditionalContextMatch = 0 := by
  apply (calibrationDriftDefectSq_eq_zero_iff_on_support
    binaryStateWeight persistentOnlyDynamicsPosterior binaryConditionalContextMatch
    (fun y ↦ by norm_num [binaryStateWeight])
    persistentOnlyDynamicsPosterior_sum_eq_one
    persistentOnlyDynamicsPosterior_nonnegative).mpr
  intro y _ s t hs ht
  cases s
  · norm_num [persistentOnlyDynamicsPosterior, binarySecondAnnotation] at hs
  · cases t
    · norm_num [persistentOnlyDynamicsPosterior, binarySecondAnnotation] at ht
    · rfl

/-! ## Finite correction cannot recover a pooled biological contrast -/

/-- Pool the two biological dynamics into one unlabeled observation.  The sum is intentionally
unnormalized: its kernel, not its scale, is the information boundary. -/
noncomputable def dynamicsPoolingObservation : (Bool → ℝ) →ₗ[ℝ] ℝ where
  toFun β := β false + β true
  map_add' β γ := by simp; ring
  map_smul' c β := by simp; ring

/-- The persistence-versus-switching contrast erased by pooling. -/
noncomputable def dynamicsContrast : Bool → ℝ := fun persists ↦ if persists then 1 else -1

/-- Pooling annihilates the biological dynamics contrast exactly. -/
theorem dynamicsContrast_mem_pooling_kernel :
    dynamicsContrast ∈ LinearMap.ker dynamicsPoolingObservation := by
  rw [LinearMap.mem_ker]
  norm_num [dynamicsPoolingObservation, dynamicsContrast]

/-- **Uniform finite-order correction barrier in biology.**  Every correction assembled from any
nonempty finite dictionary of post-processors acts through the pooled observation, hence erases the
persistence/switching contrast.  Increasing the dictionary order cannot restore information that
pooling removed. -/
theorem every_uniform_pooled_correction_erases_dynamicsContrast
    (k : ℕ) (C : (Bool → ℝ) →ₗ[ℝ] (Bool → ℝ))
    (hC : C ∈ UniformCorrectionFamily dynamicsPoolingObservation k) :
    C dynamicsContrast = 0 := by
  apply factorsThrough_apply_eq_zero_of_mem_ker dynamicsPoolingObservation C
  · exact uniformCorrectionFamily_subset_factorsThrough dynamicsPoolingObservation k hC
  · exact dynamicsContrast_mem_pooling_kernel

/-- Adaptive coefficients do not rescue the contrast either: every vector they can synthesize from
the pooled contrast is zero. -/
theorem adaptive_pooled_correctionSet_dynamicsContrast_eq_zero
    (k : ℕ) (T : Fin k → ℝ →ₗ[ℝ] (Bool → ℝ)) :
    adaptiveCorrectionSet dynamicsPoolingObservation T dynamicsContrast = {0} :=
  adaptiveCorrectionSet_of_mem_ker dynamicsPoolingObservation T dynamicsContrast
    dynamicsContrast_mem_pooling_kernel

/-- The pooled correction residual is the entire contrast, not merely a positive lower bound. -/
theorem uniform_pooled_correction_residual_eq_dynamicsContrast
    (k : ℕ) (C : (Bool → ℝ) →ₗ[ℝ] (Bool → ℝ))
    (hC : C ∈ UniformCorrectionFamily dynamicsPoolingObservation k) :
    dynamicsContrast - C dynamicsContrast = dynamicsContrast := by
  rw [every_uniform_pooled_correction_erases_dynamicsContrast k C hC]
  exact sub_zero _

/-- The correction-theory contrast is exactly twice the calibration drift field of the biological
context-match example.  This equality wires the two obstruction theories to the same biological
direction rather than merely placing their theorems in one file. -/
theorem dynamicsContrast_eq_two_mul_contextMatchDrift
    (persists : Bool) (y : BinaryBiologicalState) :
    dynamicsContrast persists =
      2 * posteriorDrift binaryDynamicsPosterior binaryConditionalContextMatch persists y := by
  cases persists <;>
    norm_num [dynamicsContrast, posteriorDrift,
      posteriorMean_binaryConditionalContextMatch_eq_half]

/-- Broadcast one pooled scalar equally back to the two biological dynamics.  The factor `1/2`
undoes the unnormalized sum in `dynamicsPoolingObservation`. -/
noncomputable def dynamicsBroadcast : ℝ →ₗ[ℝ] (Bool → ℝ) where
  toFun z := fun _ ↦ z / 2
  map_add' z w := by funext persists; dsimp; ring
  map_smul' c z := by funext persists; dsimp; ring

/-- The shared biological mode, invariant between persistence and switching. -/
noncomputable def dynamicsCommonMode (persists : Bool) : ℝ :=
  binaryFirstAnnotation persists + binarySecondAnnotation persists

/-- Pooling followed by broadcasting recovers the common mode exactly. -/
theorem dynamicsBroadcast_pooling_commonMode :
    dynamicsBroadcast (dynamicsPoolingObservation dynamicsCommonMode) =
      dynamicsCommonMode := by
  funext persists
  cases persists <;>
    norm_num [dynamicsBroadcast, dynamicsPoolingObservation, dynamicsCommonMode,
      binaryFirstAnnotation, binarySecondAnnotation]

/-- The common mode is a nonzero eigen-direction of the pooled correction. -/
theorem dynamicsCommonMode_mem_nonzeroCorrectionEigencone :
    dynamicsCommonMode ∈
      NonzeroCorrectionEigencone dynamicsPoolingObservation dynamicsBroadcast := by
  exact ⟨1, one_ne_zero, by
    simpa using dynamicsBroadcast_pooling_commonMode⟩

/-- **Thin-class phase change in biology.**  The same one-term adaptive dictionary that cannot
produce any part of `dynamicsContrast` recovers `dynamicsCommonMode` exactly.  Adaptivity is thus
not generically weak or strong: it is exact on the observable eigencone and absolutely blind on
the pooled kernel. -/
theorem dynamicsCommonMode_mem_adaptive_pooled_correctionSet :
    dynamicsCommonMode ∈ adaptiveCorrectionSet dynamicsPoolingObservation
      (fun _ : Fin 1 ↦ dynamicsBroadcast) dynamicsCommonMode :=
  mem_adaptiveCorrectionSet_singleton_of_mem_nonzeroEigencone
    dynamicsPoolingObservation dynamicsBroadcast dynamicsCommonMode
    dynamicsCommonMode_mem_nonzeroCorrectionEigencone

/-- The biological conditional-quality field decomposes into one half common mode plus one half
contrast.  Pooling retains the former and erases the latter. -/
theorem binaryConditionalContextMatch_eq_half_common_add_contrast
    (persists : Bool) (y : BinaryBiologicalState) :
    binaryConditionalContextMatch persists y =
      (1 / 2) * dynamicsCommonMode persists + (1 / 2) * dynamicsContrast persists := by
  cases persists <;>
    norm_num [binaryConditionalContextMatch_eq_indicator, dynamicsCommonMode, dynamicsContrast,
      binaryFirstAnnotation, binarySecondAnnotation]

/-- **The calibration price is one quarter of squared section oscillation.**  This identifies the
`L²` posterior-field obstruction with the sharp functional-descent geometry in the same biological
model, rather than merely evaluating the two theories on unrelated witnesses. -/
theorem binaryContextMatch_calibrationDriftDefectSq_eq_quarter_oscillationSq
    (y : BinaryBiologicalState) :
    calibrationDriftDefectSq binaryStateWeight binaryDynamicsPosterior
      binaryConditionalContextMatch =
        (1 / 4) * contextMatchSectionOscillation y ^ 2 := by
  rw [binaryContextMatch_calibrationDriftDefectSq_eq_quarter,
    contextMatch_sectionOscillation_eq_one]
  norm_num

/-- **Equivalent total-variation price.**  Since the two biological fibers are maximally
separated in total variation, the same obstruction is one sixteenth of the squared fiber
diameter. -/
theorem binaryContextMatch_calibrationDriftDefectSq_eq_sixteenth_tvDiameterSq
    (y : BinaryBiologicalState) :
    calibrationDriftDefectSq binaryStateWeight binaryDynamicsPosterior
      binaryConditionalContextMatch =
        (1 / 16) * contextMatchTotalVariationDiameter y ^ 2 := by
  rw [binaryContextMatch_calibrationDriftDefectSq_eq_quarter,
    contextMatch_totalVariationDiameter_eq_two]
  norm_num

/-- The pooled predictor is perfectly aggregate-calibrated in the persistence/switching model. -/
theorem binaryContextMatch_aggregateCalibrationEnergy_eq_zero :
    aggregateCalibrationEnergy binaryStateWeight binaryDynamicsPosterior
      binaryConditionalContextMatch
      (posteriorMean binaryDynamicsPosterior binaryConditionalContextMatch) = 0 :=
  aggregateCalibrationEnergy_posteriorMean _ _ _

/-- **No aggregate/index-wise trade-off in the biological model.**  The same pooled predictor
that has zero aggregate error has index-wise energy exactly `1/4`, the drift defect.  This is the
finite biological realization of the continuum program's central Pythagorean obstruction. -/
theorem binaryContextMatch_indexWiseCalibrationEnergy_eq_quarter :
    indexWiseCalibrationEnergy binaryStateWeight binaryDynamicsPosterior
      binaryConditionalContextMatch
      (posteriorMean binaryDynamicsPosterior binaryConditionalContextMatch) = 1 / 4 := by
  rw [indexWiseCalibrationEnergy_posteriorMean_eq_driftDefectSq
    binaryStateWeight binaryDynamicsPosterior binaryConditionalContextMatch
    binaryDynamicsPosterior_sum_eq_one]
  exact binaryContextMatch_calibrationDriftDefectSq_eq_quarter

/-! ## The adaptation time and the transport time are one time -/

/-- **A single-rate integrated autocorrelation time is the inverse-dissipation frontier
time.**

`DirichletTransfer.autocorrTime` is `Σ wᵢ / λᵢ`, the time the value signal stays informative;
`CirculationDefect.frontierTime` is `1 / s`, the time scale a transfer frontier runs on. At
one mode of unit weight they are the same number, and that is what puts the two layers of
this dictionary on one clock: the cost of adapting a readout to `θ(x)` is measured in the
units the transport frontier is measured in.

The link matters because `CirculationDefect` proves that a mixing diagnostic *understates*
`frontierTime` whenever the demography circulates, by the factor `1 + (a/s)²`. Through this
identity that understatement is an understatement of the adaptation time too, rather than a
fact about a separate quantity that happens to be written the same way. -/
theorem autocorrTime_singleton_eq_frontierTime {ι : Type*} (i : ι) (lam : ι → ℝ) :
    autocorrTime {i} (fun _ ↦ (1 : ℝ)) lam = frontierTime (lam i) := by
  unfold autocorrTime frontierTime
  simp

/-! ## Geometry and effect recovery are separate gates -/

/-- The observable covariance geometry and the biological effect field require different
conditions.  Invertibility transfers generalized eigenvalues to the precision pencil, while
effect identification is exactly transversality against the declared nuisance class.  The
conjunction prevents either condition from being silently used as a substitute for the
other. -/
theorem geometry_and_effect_recovery_gates
    {n Context Probe Param : Type*} [Fintype n] [DecidableEq n]
    (A B : Matrix n n ℝ) (lambda : ℝ)
    (hA : IsUnit A.det) (hB : IsUnit B.det)
    (M : ObservationModel Context Probe Param) :
    ((B - lambda • A).det = 0 ↔ (A⁻¹ - lambda • B⁻¹).det = 0) ∧
      (Identifiable M ↔
        ∀ theta theta' h h', h ∈ M.nuisance → h' ∈ M.nuisance →
          actionGap M theta theta' = (fun x p ↦ h' x p - h x p) → theta = theta') := by
  exact ⟨covariancePencil_det_zero_iff_precisionPencil_det_zero A B lambda hA hB,
    identifiable_iff_transversal M⟩

/-! ## The unified obstruction bundle -/

/-- Twenty logically distinct failures and boundaries that a biological transport theory must
not collapse into one scalar "portability" parameter.  The final six fields make continuum
calibration and finite correction part of the core theorem rather than adjacent examples. -/
structure UnifiedBiologyObstructions : Prop where
  /-- Stationary target averaging cannot distinguish persistence from switching. -/
  targetOnlyBlind :
    targetOnlyTransportPerformance binaryStateWeight persistentTransition targetAnnotation =
      targetOnlyTransportPerformance binaryStateWeight switchingTransition targetAnnotation
  /-- A source-target criterion does distinguish them. -/
  crossStateSeparates :
    crossStatePerformance binaryStateWeight persistentTransition contextMatchQuality ≠
      crossStatePerformance binaryStateWeight switchingTransition contextMatchQuality
  /-- Coordinate marginals do not determine the joint biological field law. -/
  marginalsLoseDependence :
    (∀ omega : Bool, coupledBinarySource omega 0 = coupledBinarySource omega 1) ∧
      (∀ omega : Bool, coordinatewiseMarginalPreserver omega 0 ≠
        coordinatewiseMarginalPreserver omega 1)
  /-- At rank two, value allocation can conflict maximally even in a common eigenbasis. -/
  commutingAllocationConflict : (2 : ℝ) < 3 ∧ (3 : ℝ) / 10 < 2 / 1
  /-- Shared local genomic geometry leaves a positive mixed fourth path moment. -/
  sharedGeometryNotFree :
    0 < 2 * (1 : ℝ) * 1 + 4 * (0 : ℝ) ^ 2 * 0 ^ 2
  /-- Equal LD eigenvalues do not determine the third-order orientation invariant in the locus
  basis where the effect-size prior factorizes. -/
  isospectralLDLosesOrientation :
    Isospectral2 (localizedCovarianceBlock (3 / 2))
        (rotatedCovarianceBlock (3 / 2)) ∧
      blockEntryCubeMean (localizedCovarianceBlock (3 / 2)) ≠
        blockEntryCubeMean (rotatedCovarianceBlock (3 / 2))
  /-- Under the centered sparse architecture, that missing LD orientation changes the cubic
  low-SNR information coefficient by exactly `11 / 24`. -/
  skewedLDChangesLowSNRCoefficient :
    ∀ aspect m1 m2 m3 : ℝ,
      lowSNRThirdCoefficient aspect 2 2 m1 m2 m3
          (blockEntryCubeMean (rotatedCovarianceBlock (3 / 2))) -
        lowSNRThirdCoefficient aspect 2 2 m1 m2 m3
          (blockEntryCubeMean (localizedCovarianceBlock (3 / 2))) = 11 / 24
  /-- Coding-symmetric sparse architectures still lose LD orientation: the third-order term
  vanishes, but the exactly isospectral blocks differ in their fourth-cumulant invariant. -/
  symmetricSparseLDLosesOrientation :
    Isospectral2 (localizedCovarianceBlock (3 / 2))
        (rotatedCovarianceBlock (3 / 2)) ∧
      blockEntryFourthMean (localizedCovarianceBlock (3 / 2)) ≠
        blockEntryFourthMean (rotatedCovarianceBlock (3 / 2))
  /-- For a coding-symmetric Rademacher architecture, the missing LD orientation changes the
  fourth-order low-SNR information coefficient by exactly `49 / 96`. -/
  symmetricLDChangesLowSNRCoefficient :
    ∀ c m1 m2 m3 m4 : ℝ,
      lowSNRFourthCoefficient c 1 (-2) m1 m2 m3 m4 rotatedUniformFourthInvariant -
          lowSNRFourthCoefficient c 1 (-2) m1 m2 m3 m4 localizedUniformFourthInvariant =
        49 / 96
  /-- Both signs of a strong sparse-LD direction have a population gap, while a balanced
  environment mixture cancels it. -/
  environmentMixtureClosesPopulationGap :
    populationGapCertificate (4 / 5) < 0 ∧
      populationGapCertificate (-(4 / 5)) < 0 ∧
      populationGapCertificate (ancestryMixtureCorrelation (4 / 5) (1 / 2)) = 1
  /-- A cross-state criterion is not a function of the target context: it fails to descend along
  the label the target-only annotation descends along. -/
  crossStateDoesNotDescend :
    ¬ DescendsAlong (fun g : TransportPair ↦ g.2) binaryTransportFamily
      (conditionalSectionMean (fun g : TransportPair ↦ contextMatchQuality g.1 g.2))
  /-- Reportability along each margin separately does not give reportability along the pair, so a
  stability check run one covariate at a time certifies nothing jointly. -/
  marginalDescentDoesNotCompose :
    DescendsAlong (fun g : TwoLociTrait ↦ g.1) admissibleInteractionTraitLaw
        (conditionalSectionMean traitIndicator) ∧
      DescendsAlong (fun g : TwoLociTrait ↦ g.2.1) admissibleInteractionTraitLaw
        (conditionalSectionMean traitIndicator) ∧
      ¬ DescendsAlong (fun g : TwoLociTrait ↦ (g.1, g.2.1)) admissibleInteractionTraitLaw
        (conditionalSectionMean traitIndicator)
  /-- Dropping a stratum destroys reportability that both finer labels have: there is no coarsest
  honest reporting label. -/
  crudeReportingLosesDescent :
    DescendsAlong (fun g : ExposureStratum ↦ g.1) admissibleConfoundedExposureLaw
        (conditionalSectionMean exposureIndicator) ∧
      DescendsAlong (fun g : ExposureStratum ↦ g.2) admissibleConfoundedExposureLaw
        (conditionalSectionMean exposureIndicator) ∧
      ¬ DescendsAlong trivialLabel admissibleConfoundedExposureLaw
        (conditionalSectionMean exposureIndicator)
  /-- Every functional descends along posterior ancestry, and the ancestry-weighted average of
  component values is still off by a full unit of trait: descent and the affine-in-ancestry
  ansatz are different claims. -/
  ancestryWeightedAnsatzFails : exampleComponentResidual = -1
  /-- Pooling is aggregate-calibrated but leaves the positive index-wise drift defect. -/
  conditionalDriftSurvivesPooling :
    calibrationDriftDefectSq binaryStateWeight binaryDynamicsPosterior
      binaryConditionalContextMatch = 1 / 4
  /-- Removing a dynamics from posterior support seals the defect without making the two
  conditional fields equal. -/
  zeroSupportSealsConditionalDrift :
    calibrationDriftDefectSq binaryStateWeight persistentOnlyDynamicsPosterior
      binaryConditionalContextMatch = 0
  /-- Every finite uniform correction through the pooled observation erases the biological
  contrast, independently of dictionary order. -/
  uniformCorrectionCannotRecoverContrast :
    ∀ (k : ℕ) (C : (Bool → ℝ) →ₗ[ℝ] (Bool → ℝ)),
      C ∈ UniformCorrectionFamily dynamicsPoolingObservation k → C dynamicsContrast = 0
  /-- Target-dependent coefficients cannot recover a direction already annihilated by the
  observation. -/
  adaptiveCorrectionCannotRecoverContrast :
    ∀ (k : ℕ) (T : Fin k → ℝ →ₗ[ℝ] (Bool → ℝ)),
      adaptiveCorrectionSet dynamicsPoolingObservation T dynamicsContrast = {0}
  /-- The same one-term adaptive dictionary is exact on the observable common mode, exposing the
  thin-class phase change rather than a blanket failure of adaptivity. -/
  observableModeIsAdaptivelyExact :
    dynamicsCommonMode ∈ adaptiveCorrectionSet dynamicsPoolingObservation
      (fun _ : Fin 1 ↦ dynamicsBroadcast) dynamicsCommonMode
  /-- The correction-null contrast and the calibration drift are the same biological direction,
  with the normalization made explicit. -/
  correctionContrastIsCalibrationDrift :
    ∀ persists y, dynamicsContrast persists =
      2 * posteriorDrift binaryDynamicsPosterior binaryConditionalContextMatch persists y

/-- **Unified finite obstruction theorem.**  Dynamics, dependence, value allocation, and
local operator geometry each carry information invisible to a tempting scalar reduction.
The witnesses coexist; none is a fallback explanation for another. -/
theorem unifiedBiology_obstructions : UnifiedBiologyObstructions := by
  refine
    { targetOnlyBlind := targetOnlyPerformance_blind_to_binary_dynamics
      crossStateSeparates := ?_
      marginalsLoseDependence := coordinateMarginalsDoNotDetermineJointLaw
      commutingAllocationConflict := commutingConflict_myopic_ne_transport
      sharedGeometryNotFree := tridiagonalABAB_pathExpression_pos 0 0 1 1 (by norm_num)
        (by norm_num)
      isospectralLDLosesOrientation :=
        ⟨localizedCovarianceBlock_isospectral_rotatedCovarianceBlock (3 / 2), by
          intro heq
          have hzero :
              blockEntryCubeMean (localizedCovarianceBlock (3 / 2)) -
                  blockEntryCubeMean (rotatedCovarianceBlock (3 / 2)) = 0 := by
            rw [heq, sub_self]
          rw [midpoint_blockEntryCubeMean_separation] at hzero
          norm_num at hzero⟩
      skewedLDChangesLowSNRCoefficient :=
        sparsePrior_lowSNRThirdCoefficient_rotated_sub_localized
      symmetricSparseLDLosesOrientation :=
        ⟨localizedCovarianceBlock_isospectral_rotatedCovarianceBlock (3 / 2),
          midpoint_blockEntryFourthMean_ne⟩
      symmetricLDChangesLowSNRCoefficient :=
        rademacher_fullLowSNRFourthCoefficient_rotated_sub_localized
      environmentMixtureClosesPopulationGap :=
        ancestryMixture_pure_gapped_balanced_ungapped
      crossStateDoesNotDescend := not_descends_contextMatchQuality_along_targetState
      marginalDescentDoesNotCompose := admissible_interaction_join_obstruction
      crudeReportingLosesDescent := admissible_confounding_meet_obstruction
      ancestryWeightedAnsatzFails := exampleComponentResidual_eq_neg_one
      conditionalDriftSurvivesPooling := binaryContextMatch_calibrationDriftDefectSq_eq_quarter
      zeroSupportSealsConditionalDrift :=
        persistentOnly_contextMatch_calibrationDriftDefectSq_eq_zero
      uniformCorrectionCannotRecoverContrast :=
        every_uniform_pooled_correction_erases_dynamicsContrast
      adaptiveCorrectionCannotRecoverContrast :=
        adaptive_pooled_correctionSet_dynamicsContrast_eq_zero
      observableModeIsAdaptivelyExact :=
        dynamicsCommonMode_mem_adaptive_pooled_correctionSet
      correctionContrastIsCalibrationDrift := dynamicsContrast_eq_two_mul_contextMatchDrift }
  rw [crossStatePerformance_persistent_eq_one, crossStatePerformance_switching_eq_zero]
  norm_num

/-! ## Conditional descent is the portability gate before prediction

The same score bin or ancestry summary can support different conditional phenotype laws in
different cohorts.  `FunctionalDescent` separates two biologically distinct failures:
interaction can disappear in either margin and reappear after refinement, while confounding can
be controlled by either informative variable and reappear after marginalization.  Thus the
choice of retained covariate is part of the portability theorem, not preprocessing notation. -/

/-- **The conditional-descent boundary is present in the biological core.**  Both finite
probability-law witnesses retain their complete order-theoretic statements.  Moreover, each
failure is already pairwise: the exact finite gluing theorem rules out a hidden global-selection
explanation.  Biologically, two cohorts disagree on a charged conditional section; the failure is
effect modification or confounding, not an off-support choice of conditional version. -/
theorem conditionalDescent_biological_boundary :
    ((DescendsAlong (fun g : TwoLociTrait ↦ g.1) admissibleInteractionTraitLaw
          (conditionalSectionMean traitIndicator) ∧
        DescendsAlong (fun g : TwoLociTrait ↦ g.2.1) admissibleInteractionTraitLaw
          (conditionalSectionMean traitIndicator) ∧
        ¬ DescendsAlong (fun g : TwoLociTrait ↦ (g.1, g.2.1))
          admissibleInteractionTraitLaw (conditionalSectionMean traitIndicator)) ∧
      ¬ PairwiseConsistent (fun g : TwoLociTrait ↦ (g.1, g.2.1))
        admissibleInteractionTraitLaw (conditionalSectionMean traitIndicator)) ∧
    ((DescendsAlong (fun g : ExposureStratum ↦ g.1) admissibleConfoundedExposureLaw
          (conditionalSectionMean exposureIndicator) ∧
        DescendsAlong (fun g : ExposureStratum ↦ g.2) admissibleConfoundedExposureLaw
          (conditionalSectionMean exposureIndicator) ∧
        ¬ DescendsAlong trivialLabel admissibleConfoundedExposureLaw
          (conditionalSectionMean exposureIndicator)) ∧
      ¬ PairwiseConsistent trivialLabel admissibleConfoundedExposureLaw
        (conditionalSectionMean exposureIndicator)) := by
  refine ⟨⟨admissible_interaction_join_obstruction, ?_⟩,
    ⟨admissible_confounding_meet_obstruction, ?_⟩⟩
  · intro hpair
    exact admissible_interaction_join_obstruction.2.2
      ((descendsAlong_iff_pairwiseConsistent_of_nonempty _ _ _).mpr hpair)
  · intro hpair
    exact admissible_confounding_meet_obstruction.2.2
      ((descendsAlong_iff_pairwiseConsistent_of_nonempty _ _ _).mpr hpair)

end Calibrator
