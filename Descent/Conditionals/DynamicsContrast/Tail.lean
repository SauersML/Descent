/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Conditionals.DynamicsContrast.StationarityRepair

namespace Descent.Conditionals

open Blindness.MarkedBreakout
open Blindness.XiFromMarks
open Blindness.TrafficInvariantSeparation
open scoped Matrix Topology
open scoped BigOperators

/-!
# `DynamicsContrast.Tail`

Part of the split of `Descent/Conditionals/DynamicsContrast.lean`, which was 3,590 lines.

The parts are a CHAIN: each imports the one before, in the order the original was written.
That is the conservative choice, deliberately. A monolith's declarations depend on each
other in whatever order they happen to appear, and cutting it into modules that import only
what they use means discovering that order first -- worth doing, and not what this does.
The chain preserves every resolution the single file had, so the split cannot change what
any proof sees.

Where a cut falls inside a section, the section is reopened and reclosed by name. A section
scopes `variable`s and this file declares none at that level, so the reopening is exact.
-/


/-! ## An exact two-state biological witness -/


/-- Uniform invariant law on two biological contexts. -/
noncomputable def binaryStateWeight (_ : Descent.BinaryState) : ℝ := 1 / 2

/-- Reference evaluation: the two states are equally weighted. -/
@[simp] theorem binaryStateWeight_at_reference_point (x : Descent.BinaryState) :
    binaryStateWeight x = 1 / 2 := rfl


/-- The biological context law is the canonical balanced calibration weight. -/
@[simp] theorem binaryStateWeight_eq_balancedBinaryWeight (x : Descent.BinaryState) :
    binaryStateWeight x = Portability.balancedBinaryWeight x := by
  rfl

/-- A transition that swaps the two contexts. -/
noncomputable def switchingTransition
    (x y : Descent.BinaryState) : ℝ :=
  Descent.Core.antiKronecker x y

/-- Reference evaluations: the switching kernel is the exchange matrix. -/
theorem switchingTransition_at_reference_point :
    switchingTransition 0 0 = 0 ∧ switchingTransition 0 1 = 1 := by
  constructor <;> norm_num [switchingTransition]


/-- A target-only annotation distinguishing state `1`. -/
noncomputable def targetAnnotation (y : Descent.BinaryState) : ℝ :=
  Descent.Core.kronecker y 1

/-- Reference evaluations: the annotation is the indicator of the distinguished state. -/
theorem targetAnnotation_at_reference_point :
    targetAnnotation 1 = 1 ∧ targetAnnotation 0 = 0 := by
  constructor <;> norm_num [targetAnnotation,
      Descent.Core.kronecker]


/-- Quality of a source-adapted readout: one exactly when source and target contexts match,
and equally the transition that preserves the context -- one function, two readings.

It was written twice, as `contextMatchQuality` and again here, on the argument that one
was a transition and the other a readout quality. Both bodies were `Core.kronecker x y`,
both reference evaluations were `0 0 = 1 ∧ 0 1 = 0` proved the same way, and this docstring
cited a bridging theorem, `contextMatchQuality_eq_contextMatchQuality`, that was never
declared anywhere in the corpus. A distinction with no theorem behind it and no difference
in the body is a comment, so it is a comment now. -/
noncomputable def contextMatchQuality
    (x y : Descent.BinaryState) : ℝ :=
  Descent.Core.kronecker x y

/-- Reference evaluations: quality one on a match, zero on a mismatch. -/
theorem contextMatchQuality_at_reference_point :
    contextMatchQuality 0 0 = 1 ∧ contextMatchQuality 0 1 = 0 := by
  constructor <;> norm_num [contextMatchQuality]


/-- **The two-context biological witness runs on the horizon-curve kernels.**

`HorizonCurve.stayKernel` is the Kronecker delta on two states, and so are the transition
that preserves the biological context and the readout quality of a design used in the
context it was built for — `HorizonCurve.agreement` is that same delta read as an
efficiency. Four readings, one matrix: the biological witness is not a second two-state
example but the horizon example under biological names, and a change to either file's
delta contradicts this. -/
theorem contextMatchQuality_agreement_eq_stayKernel
    (x y : Descent.BinaryState) :
    contextMatchQuality x y = Portability.stayKernel x y ∧
      Portability.agreement x y = Portability.stayKernel x y :=
  ⟨rfl, rfl⟩

/-- **Complete context switching is the horizon curve's swap kernel**, the off-diagonal
counterpart of the identification above. -/
theorem switchingTransition_eq_swapKernel (x y : Descent.BinaryState) :
    switchingTransition x y = Portability.swapKernel x y := rfl

theorem binaryStateWeight_stationary_persistent (y : Descent.BinaryState) :
    ∑ x, binaryStateWeight x * contextMatchQuality x y = binaryStateWeight y := by
  fin_cases y <;>
    norm_num [binaryStateWeight, contextMatchQuality, Fin.sum_univ_two]

theorem binaryStateWeight_stationary_switching (y : Descent.BinaryState) :
    ∑ x, binaryStateWeight x * switchingTransition x y = binaryStateWeight y := by
  fin_cases y <;>
    norm_num [binaryStateWeight, switchingTransition, Fin.sum_univ_two]

/-- Target-only performance is identical under persistence and complete switching. -/
theorem targetOnlyPerformance_blind_to_binary_dynamics :
    targetOnlyTransportPerformance binaryStateWeight contextMatchQuality targetAnnotation =
      targetOnlyTransportPerformance binaryStateWeight switchingTransition targetAnnotation := by
  rw [targetOnlyTransportPerformance_eq_onePoint _ _ _
      binaryStateWeight_stationary_persistent]
  rw [targetOnlyTransportPerformance_eq_onePoint _ _ _
      binaryStateWeight_stationary_switching]

/-- Cross-state performance detects the dynamics: a source-adapted readout is perfect when
the context persists. -/
theorem crossStatePerformance_persistent_eq_one :
    crossStatePerformance binaryStateWeight contextMatchQuality contextMatchQuality = 1 := by
  norm_num [crossStatePerformance, binaryStateWeight, contextMatchQuality,
    contextMatchQuality, Fin.sum_univ_two]

/-- The same readout has zero value when the context always switches. -/
theorem crossStatePerformance_switching_eq_zero :
    crossStatePerformance binaryStateWeight switchingTransition contextMatchQuality = 0 := by
  norm_num [crossStatePerformance, binaryStateWeight, switchingTransition,
    contextMatchQuality, Fin.sum_univ_two]

/-! ## The stationarity repair is a descent failure

The repair above says a target-only average cannot see the dynamics.  `Descent.Conditionals.DescentGeometry`
says what kind of statement that is: the target context is a *label*, the two dynamics are two
*populations* on source-target pairs, and a criterion is reportable by target context exactly
when it descends along that label.  The target-only annotation descends; the source-adapted
quality does not.  So the quantity a cross-state criterion measures is a function of the pair
(target context, population), not of the target context — which is why no relabelling of the
target average recovers it. -/

/-- A source-target pair of biological contexts. -/
abbrev TransportPair := Descent.BinaryState × Descent.BinaryState

/-- The joint law of source and target contexts under a transition. -/
noncomputable def jointTransportLaw
    (transition : Descent.BinaryState → Descent.BinaryState → ℝ) (g : TransportPair) : ℝ :=
  binaryStateWeight g.1 * transition g.1 g.2

/-- Reference evaluation: half the mass of the persistent kernel sits on each diagonal pair. -/
theorem jointTransportLaw_at_reference_point :
    jointTransportLaw contextMatchQuality (0, 0) = 1 / 2 := by
  norm_num [jointTransportLaw, contextMatchQuality, binaryStateWeight]


/-- The two-population family: the context persists, or the context switches. -/
noncomputable def binaryTransportFamily (persists : Bool) : TransportPair → ℝ :=
  jointTransportLaw (if persists then contextMatchQuality else switchingTransition)

/-- Both members of the persistence/switching family are genuine nonnegative finite laws. -/
theorem binaryTransportFamily_nonneg (persists : Bool) (g : TransportPair) :
    0 ≤ binaryTransportFamily persists g := by
  rcases g with ⟨x, y⟩
  cases persists <;> fin_cases x <;> fin_cases y <;>
    norm_num [binaryTransportFamily, jointTransportLaw, binaryStateWeight,
      contextMatchQuality, switchingTransition]

/-- Target-only performance is the mean of a target-measurable kernel under the joint law. -/
theorem targetOnlyTransportPerformance_eq_conditionalSectionMean
    (transition : Descent.BinaryState → Descent.BinaryState → ℝ)
    (score : Descent.BinaryState → ℝ) :
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
    (transition : Descent.BinaryState → Descent.BinaryState → ℝ)
    (quality : Descent.BinaryState → Descent.BinaryState → ℝ) :
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
theorem labelMass_binaryTransportFamily (persists : Bool) (y : Descent.BinaryState) :
    labelMass (fun g : TransportPair ↦ g.2) (binaryTransportFamily persists) y = 1 / 2 := by
  cases persists <;> fin_cases y <;>
    norm_num [labelMass, binaryTransportFamily, jointTransportLaw, binaryStateWeight,
      contextMatchQuality, switchingTransition, Fintype.sum_prod_type, Fin.sum_univ_two]

/-- Every fiber of either transport family carries mass, so the fiber conditional is
defined at every state.

Both diameter theorems below open by establishing this for `true` and for `false`, and both
did it by rewriting `labelMass_binaryTransportFamily` and calling `norm_num`, twice each.
Stated once, the four copies become four applications. -/
theorem labelMass_binaryTransportFamily_ne_zero (persists : Bool)
    (y : Descent.BinaryState) :
    labelMass (fun g : TransportPair ↦ g.2) (binaryTransportFamily persists) y ≠ 0 := by
  rw [labelMass_binaryTransportFamily]
  norm_num

/-- A target-only annotation descends along the target context: it is reportable there. -/
theorem descends_targetAnnotation_along_targetState :
    DescendsAlong (fun g : TransportPair ↦ g.2) binaryTransportFamily
      (conditionalSectionMean (fun g : TransportPair ↦ targetAnnotation g.2)) :=
  descendsAlong_sectionMean_of_labelFunction _ binaryTransportFamily targetAnnotation

/-- Under persistence, the source-adapted readout is perfect on every target fiber. -/
theorem contextMatchQuality_value_persistent (y : Descent.BinaryState) :
    conditionalSectionMean (fun g : TransportPair ↦ contextMatchQuality g.1 g.2)
      (fiberConditional (fun g : TransportPair ↦ g.2) (binaryTransportFamily true) y) = 1 := by
  rw [conditionalSectionMean_fiberConditional, labelMass_binaryTransportFamily]
  fin_cases y <;>
    norm_num [binaryTransportFamily, jointTransportLaw, binaryStateWeight, contextMatchQuality,
      contextMatchQuality, Fintype.sum_prod_type, Fin.sum_univ_two]

/-- Under complete switching, the same readout is worthless on the same fiber. -/
theorem contextMatchQuality_value_switching (y : Descent.BinaryState) :
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
noncomputable def contextMatchSectionOscillation (y : Descent.BinaryState) : ℝ :=
  finiteSectionOscillation
    (fun persists y ↦
      labelMass (fun g : TransportPair ↦ g.2) (binaryTransportFamily persists) y ≠ 0)
    (fun persists y ↦
      fiberConditional (fun g : TransportPair ↦ g.2) (binaryTransportFamily persists) y)
    (conditionalSectionMean (fun g : TransportPair ↦ contextMatchQuality g.1 g.2))
    (fun a b : ℝ ↦ |a - b|) y

/-- The total-variation diameter of supported dynamics on one biological target-state fiber.

Empirical status: NOT AN EMPIRICAL CLAIM -- this is an exact finite section diameter. -/
noncomputable def contextMatchTotalVariationDiameter (y : Descent.BinaryState) : ℝ :=
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
    (y : Descent.BinaryState) :
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
theorem contextMatch_totalVariationDiameter_eq_two (y : Descent.BinaryState) :
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
          jointTransportLaw, binaryStateWeight, contextMatchQuality, switchingTransition,
          Fintype.sum_prod_type, Fin.sum_univ_two]
    rwa [hgap] at hlower

/-- **The quantitative obstruction is attained.**  On every target state the source-adapted
readout changes from one under persistence to zero under switching, so the section oscillation is
exactly one.  Together with `contextMatch_totalVariationDiameter_eq_two`, this proves equality in
the sharp range-sensitive bound above rather than merely exhibiting non-descent. -/
theorem contextMatch_sectionOscillation_eq_one (y : Descent.BinaryState) :
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
    (_ : Descent.BinaryState) (_ : Bool) : ℝ := 1 / 2

/-- The uninformative dynamics posterior is the canonical balanced calibration weight. -/
@[simp] theorem binaryDynamicsPosterior_eq_balancedBinaryWeight
    (y : Descent.BinaryState) (persists : Bool) :
    binaryDynamicsPosterior y persists = Portability.balancedBinaryWeight persists := by
  rfl

/-- Conditional source-adapted quality for one dynamics and one target context, constructed from
the same fiber conditional used by the descent theorem above. -/
noncomputable def binaryConditionalContextMatch
    (persists : Bool) (y : Descent.BinaryState) : ℝ :=
  conditionalSectionMean (fun g : TransportPair ↦ contextMatchQuality g.1 g.2)
    (fiberConditional (fun g : TransportPair ↦ g.2) (binaryTransportFamily persists) y)

/-- The constructed conditional-quality field is one for persistence and zero for switching. -/
@[simp] theorem binaryConditionalContextMatch_eq_indicator
    (persists : Bool) (y : Descent.BinaryState) :
    binaryConditionalContextMatch persists y = if persists then 1 else 0 := by
  cases persists
  · simp [binaryConditionalContextMatch, contextMatchQuality_value_switching]
  · simp [binaryConditionalContextMatch, contextMatchQuality_value_persistent]

/-- The binary dynamics posterior is normalized on every biological target context. -/
theorem binaryDynamicsPosterior_sum_eq_one (y : Descent.BinaryState) :
    ∑ persists, binaryDynamicsPosterior y persists = 1 := by
  norm_num [binaryDynamicsPosterior]

/-- Pooling persistence and switching makes the source-adapted quality look exactly one-half on
every target context.  This is the posterior-mean predictor of the calibration core. -/
theorem posteriorMean_binaryConditionalContextMatch_eq_half (y : Descent.BinaryState) :
    Portability.posteriorMean binaryDynamicsPosterior binaryConditionalContextMatch y = 1 / 2 := by
  norm_num [Portability.posteriorMean, binaryDynamicsPosterior]

/-- **Biological drift defect.**  Persistence has conditional quality one and switching has
quality zero, while the pooled posterior mean is one-half.  Averaging across the two target
contexts leaves an irreducible squared index-wise calibration defect of exactly `1/4`. -/
theorem binaryContextMatch_calibrationDriftDefectSq_eq_quarter :
    Portability.calibrationDriftDefectSq binaryStateWeight binaryDynamicsPosterior
      binaryConditionalContextMatch = 1 / 4 := by
  have hposterior : binaryDynamicsPosterior =
      Portability.twoIndexPosterior (fun _ : Descent.BinaryState ↦ 1 / 2) := by
    funext y persists
    cases persists <;> norm_num [binaryDynamicsPosterior, Portability.twoIndexPosterior]
  have hconditional : binaryConditionalContextMatch =
      Portability.twoIndexConditional (fun _ : Descent.BinaryState ↦ 1)
        (fun _ : Descent.BinaryState ↦ 0) := by
    funext persists y
    rw [binaryConditionalContextMatch_eq_indicator]
    cases persists <;> norm_num [Portability.twoIndexConditional]
  rw [hposterior, hconditional, Portability.twoIndex_calibrationDriftDefectSq_eq]
  norm_num [binaryStateWeight, Fin.sum_univ_two]

/-- **The biological defect is pairwise disagreement.**  The quarter-unit portability loss is
exactly half the expected squared quality difference between two independent posterior draws of
the biological dynamics, averaged over target contexts.  Thus the binary persistence/switching
calculation is a concrete face of the arbitrary finite-population pairwise drift law rather than
an isolated two-state formula. -/
theorem binaryContextMatch_pairwiseCalibrationDriftEnergy_eq_quarter :
    Portability.pairwiseCalibrationDriftEnergy binaryStateWeight binaryDynamicsPosterior
      binaryConditionalContextMatch = 1 / 4 := by
  rw [← Portability.calibrationDriftDefectSq_eq_pairwiseCalibrationDriftEnergy
    binaryStateWeight binaryDynamicsPosterior binaryConditionalContextMatch
    binaryDynamicsPosterior_sum_eq_one]
  exact binaryContextMatch_calibrationDriftDefectSq_eq_quarter

/-- At each target context, the same pairwise disagreement price is already `1/4`; averaging over
contexts does not create the obstruction, it only preserves a pointwise ancestry/dynamics defect. -/
theorem binaryContextMatch_posteriorPairwiseDriftEnergy_eq_quarter
    (y : Descent.BinaryState) :
    Portability.posteriorPairwiseDriftEnergy binaryDynamicsPosterior
      binaryConditionalContextMatch y = 1 / 4 := by
  rw [Portability.posteriorPairwiseDriftEnergy_eq_posteriorDriftEnergy
    binaryDynamicsPosterior binaryConditionalContextMatch y
    (binaryDynamicsPosterior_sum_eq_one y)]
  norm_num [Portability.posteriorDrift, posteriorMean_binaryConditionalContextMatch_eq_half,
    binaryDynamicsPosterior]

/-- A sealed support boundary: the deployed population contains only persistent dynamics and
assigns zero posterior mass to switching dynamics.  The conditional field is unchanged; only its
represented support changes. -/
noncomputable def persistentOnlyDynamicsPosterior
    (_ : Descent.BinaryState) (persists : Bool) : ℝ := Spectral.binarySecondAnnotation persists

/-- The support-sealed biological posterior remains normalized. -/
theorem persistentOnlyDynamicsPosterior_sum_eq_one (y : Descent.BinaryState) :
    ∑ persists, persistentOnlyDynamicsPosterior y persists = 1 := by
  norm_num [persistentOnlyDynamicsPosterior, Spectral.binarySecondAnnotation]

/-- Its posterior masses are nonnegative. -/
theorem persistentOnlyDynamicsPosterior_nonnegative
    (y : Descent.BinaryState) (persists : Bool) :
    0 ≤ persistentOnlyDynamicsPosterior y persists := by
  cases persists <;> norm_num [persistentOnlyDynamicsPosterior, Spectral.binarySecondAnnotation]

/-- **Biological sealing law at zero support.**  Persistence and switching still have conditional
qualities one and zero, but after switching receives zero posterior mass the calibration defect is
exactly zero.  This is not conditional invariance; it is categorical blindness created by the
support wall, and it is certified by the general support-aware theorem. -/
theorem persistentOnly_contextMatch_calibrationDriftDefectSq_eq_zero :
    Portability.calibrationDriftDefectSq binaryStateWeight persistentOnlyDynamicsPosterior
      binaryConditionalContextMatch = 0 := by
  apply (Portability.calibrationDriftDefectSq_eq_zero_iff_on_support
    binaryStateWeight persistentOnlyDynamicsPosterior binaryConditionalContextMatch
    (fun y ↦ by norm_num [binaryStateWeight])
    persistentOnlyDynamicsPosterior_sum_eq_one
    persistentOnlyDynamicsPosterior_nonnegative).mpr
  intro y _ s t hs ht
  cases s
  · norm_num [persistentOnlyDynamicsPosterior, Spectral.binarySecondAnnotation] at hs
  · cases t
    · norm_num [persistentOnlyDynamicsPosterior, Spectral.binarySecondAnnotation] at ht
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
    (hC : C ∈ Portability.UniformCorrectionFamily dynamicsPoolingObservation k) :
    C dynamicsContrast = 0 := by
  apply Portability.factorsThrough_apply_eq_zero_of_mem_ker dynamicsPoolingObservation C
  · exact Portability.uniformCorrectionFamily_subset_factorsThrough dynamicsPoolingObservation k hC
  · exact dynamicsContrast_mem_pooling_kernel

/-- Adaptive coefficients do not rescue the contrast either: every vector they can synthesize from
the pooled contrast is zero. -/
theorem adaptive_pooled_correctionSet_dynamicsContrast_eq_zero
    (k : ℕ) (T : Fin k → ℝ →ₗ[ℝ] (Bool → ℝ)) :
    Portability.adaptiveCorrectionSet dynamicsPoolingObservation T dynamicsContrast = {0} :=
  Portability.adaptiveCorrectionSet_of_mem_ker dynamicsPoolingObservation T dynamicsContrast
    dynamicsContrast_mem_pooling_kernel

/-- The pooled correction residual is the entire contrast, not merely a positive lower bound. -/
theorem uniform_pooled_correction_residual_eq_dynamicsContrast
    (k : ℕ) (C : (Bool → ℝ) →ₗ[ℝ] (Bool → ℝ))
    (hC : C ∈ Portability.UniformCorrectionFamily dynamicsPoolingObservation k) :
    dynamicsContrast - C dynamicsContrast = dynamicsContrast := by
  rw [every_uniform_pooled_correction_erases_dynamicsContrast k C hC]
  exact sub_zero _

/-- The correction-theory contrast is exactly twice the calibration drift field of the biological
context-match example.  This equality wires the two obstruction theories to the same biological
direction rather than merely placing their theorems in one file. -/
theorem dynamicsContrast_eq_two_mul_contextMatchDrift
    (persists : Bool) (y : Descent.BinaryState) :
    dynamicsContrast persists =
      2 * Portability.posteriorDrift binaryDynamicsPosterior binaryConditionalContextMatch persists y := by
  cases persists <;>
    norm_num [dynamicsContrast, Portability.posteriorDrift,
      posteriorMean_binaryConditionalContextMatch_eq_half]

/-- Broadcast one pooled scalar equally back to the two biological dynamics.  The factor `1/2`
undoes the unnormalized sum in `dynamicsPoolingObservation`. -/
noncomputable def dynamicsBroadcast : ℝ →ₗ[ℝ] (Bool → ℝ) where
  toFun z := fun _ ↦ z / 2
  map_add' z w := by funext persists; dsimp; ring
  map_smul' c z := by funext persists; dsimp; ring

/-- The shared biological mode, invariant between persistence and switching. -/
noncomputable def dynamicsCommonMode (persists : Bool) : ℝ :=
  Spectral.binaryFirstAnnotation persists + Spectral.binarySecondAnnotation persists

/-- Reference evaluation; see `Descent.Core.Ratios` for what these pin and why. -/
theorem dynamicsCommonMode_at_reference_point :
    dynamicsCommonMode true = 1 ∧ dynamicsCommonMode false = 1 := by
  constructor <;> norm_num [dynamicsCommonMode, Spectral.binaryFirstAnnotation, Spectral.binarySecondAnnotation]


/-- Pooling followed by broadcasting recovers the common mode exactly. -/
theorem dynamicsBroadcast_pooling_commonMode :
    dynamicsBroadcast (dynamicsPoolingObservation dynamicsCommonMode) =
      dynamicsCommonMode := by
  funext persists
  cases persists <;>
    norm_num [dynamicsBroadcast, dynamicsPoolingObservation, dynamicsCommonMode,
      Spectral.binaryFirstAnnotation, Spectral.binarySecondAnnotation]

/-- The common mode is a nonzero eigen-direction of the pooled correction. -/
theorem dynamicsCommonMode_mem_nonzeroCorrectionEigencone :
    dynamicsCommonMode ∈
      Portability.NonzeroCorrectionEigencone dynamicsPoolingObservation dynamicsBroadcast := by
  exact ⟨1, one_ne_zero, by
    simpa using dynamicsBroadcast_pooling_commonMode⟩

/-- **Thin-class phase change in biology.**  The same one-term adaptive dictionary that cannot
produce any part of `dynamicsContrast` recovers `dynamicsCommonMode` exactly.  Adaptivity is thus
not generically weak or strong: it is exact on the observable eigencone and absolutely blind on
the pooled kernel. -/
theorem dynamicsCommonMode_mem_adaptive_pooled_correctionSet :
    dynamicsCommonMode ∈ Portability.adaptiveCorrectionSet dynamicsPoolingObservation
      (fun _ : Fin 1 ↦ dynamicsBroadcast) dynamicsCommonMode :=
  Portability.mem_adaptiveCorrectionSet_singleton_of_mem_nonzeroEigencone
    dynamicsPoolingObservation dynamicsBroadcast dynamicsCommonMode
    dynamicsCommonMode_mem_nonzeroCorrectionEigencone

/-- The biological conditional-quality field decomposes into one half common mode plus one half
contrast.  Pooling retains the former and erases the latter. -/
theorem binaryConditionalContextMatch_eq_half_common_add_contrast
    (persists : Bool) (y : Descent.BinaryState) :
    binaryConditionalContextMatch persists y =
      (1 / 2) * dynamicsCommonMode persists + (1 / 2) * dynamicsContrast persists := by
  cases persists <;>
    norm_num [binaryConditionalContextMatch_eq_indicator, dynamicsCommonMode, dynamicsContrast,
      Spectral.binaryFirstAnnotation, Spectral.binarySecondAnnotation]

/-- **The calibration price is one quarter of squared section oscillation.**  This identifies the
`L²` posterior-field obstruction with the sharp functional-descent geometry in the same biological
model, rather than merely evaluating the two theories on unrelated witnesses. -/
theorem binaryContextMatch_calibrationDriftDefectSq_eq_quarter_oscillationSq
    (y : Descent.BinaryState) :
    Portability.calibrationDriftDefectSq binaryStateWeight binaryDynamicsPosterior
      binaryConditionalContextMatch =
        (1 / 4) * contextMatchSectionOscillation y ^ 2 := by
  rw [binaryContextMatch_calibrationDriftDefectSq_eq_quarter,
    contextMatch_sectionOscillation_eq_one]
  norm_num

/-- **Equivalent total-variation price.**  Since the two biological fibers are maximally
separated in total variation, the same obstruction is one sixteenth of the squared fiber
diameter. -/
theorem binaryContextMatch_calibrationDriftDefectSq_eq_sixteenth_tvDiameterSq
    (y : Descent.BinaryState) :
    Portability.calibrationDriftDefectSq binaryStateWeight binaryDynamicsPosterior
      binaryConditionalContextMatch =
        (1 / 16) * contextMatchTotalVariationDiameter y ^ 2 := by
  rw [binaryContextMatch_calibrationDriftDefectSq_eq_quarter,
    contextMatch_totalVariationDiameter_eq_two]
  norm_num

/-- The pooled predictor is perfectly aggregate-calibrated in the persistence/switching model. -/
theorem binaryContextMatch_aggregateCalibrationEnergy_eq_zero :
    Portability.aggregateCalibrationEnergy binaryStateWeight binaryDynamicsPosterior
      binaryConditionalContextMatch
      (Portability.posteriorMean binaryDynamicsPosterior binaryConditionalContextMatch) = 0 :=
  Portability.aggregateCalibrationEnergy_posteriorMean _ _ _

/-- **No aggregate/index-wise trade-off in the biological model.**  The same pooled predictor
that has zero aggregate error has index-wise energy exactly `1/4`, the drift defect.  This is the
finite biological realization of the continuum program's central Pythagorean obstruction. -/
theorem binaryContextMatch_indexWiseCalibrationEnergy_eq_quarter :
    Portability.indexWiseCalibrationEnergy binaryStateWeight binaryDynamicsPosterior
      binaryConditionalContextMatch
      (Portability.posteriorMean binaryDynamicsPosterior binaryConditionalContextMatch) = 1 / 4 := by
  rw [Portability.indexWiseCalibrationEnergy_posteriorMean_eq_driftDefectSq
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
    Spectral.autocorrTime {i} (fun _ ↦ (1 : ℝ)) lam = Spectral.frontierTime (lam i) := by
  unfold Spectral.autocorrTime Spectral.frontierTime
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
  exact ⟨Spectral.covariancePencil_det_zero_iff_precisionPencil_det_zero A B lambda hA hB,
    identifiable_iff_transversal M⟩

/-! ## The obstruction bundle -/

/-- Twenty-four logically distinct failures and boundaries that a biological transport theory must
not collapse into one scalar "portability" parameter.  The final six fields make continuum
calibration and finite correction part of the core theorem rather than adjacent examples. -/
structure DynamicsObstructions : Prop where
  /-- Stationary target averaging cannot distinguish persistence from switching. -/
  targetOnlyBlind :
    targetOnlyTransportPerformance binaryStateWeight contextMatchQuality targetAnnotation =
      targetOnlyTransportPerformance binaryStateWeight switchingTransition targetAnnotation
  /-- A source-target criterion does distinguish them. -/
  crossStateSeparates :
    crossStatePerformance binaryStateWeight contextMatchQuality contextMatchQuality ≠
      crossStatePerformance binaryStateWeight switchingTransition contextMatchQuality
  /-- Coordinate marginals do not determine the joint biological field law. -/
  marginalsLoseDependence :
    (∀ omega : Bool, Spectral.coupledBinarySource omega 0 = Spectral.coupledBinarySource omega 1) ∧
      (∀ omega : Bool, Spectral.coordinatewiseMarginalPreserver omega 0 ≠
        Spectral.coordinatewiseMarginalPreserver omega 1)
  /-- At rank two, value allocation can conflict maximally even in a common eigenbasis. -/
  commutingAllocationConflict : (2 : ℝ) < 3 ∧ (3 : ℝ) / 10 < 2 / 1
  /-- Shared local genomic geometry leaves a positive mixed fourth path moment. -/
  sharedGeometryNotFree :
    0 < 2 * (1 : ℝ) * 1 + 4 * (0 : ℝ) ^ 2 * 0 ^ 2
  /-- Equal LD eigenvalues do not determine the third-order orientation invariant in the locus
  basis where the effect-size prior factorizes. -/
  isospectralLDLosesOrientation :
    Blindness.Isospectral2 (Blindness.localizedCovarianceBlock (3 / 2))
        (Blindness.rotatedCovarianceBlock (3 / 2)) ∧
      Blindness.blockEntryCubeMean (Blindness.localizedCovarianceBlock (3 / 2)) ≠
        Blindness.blockEntryCubeMean (Blindness.rotatedCovarianceBlock (3 / 2))
  /-- Under the centered sparse architecture, that missing LD orientation changes the cubic
  low-SNR information coefficient by exactly `11 / 24`. -/
  skewedLDChangesLowSNRCoefficient :
    ∀ aspect m1 m2 m3 : ℝ,
      Blindness.lowSNRThirdCoefficient aspect 2 2 m1 m2 m3
          (Blindness.blockEntryCubeMean (Blindness.rotatedCovarianceBlock (3 / 2))) -
        Blindness.lowSNRThirdCoefficient aspect 2 2 m1 m2 m3
          (Blindness.blockEntryCubeMean (Blindness.localizedCovarianceBlock (3 / 2))) = 11 / 24
  /-- Coding-symmetric sparse architectures still lose LD orientation: the third-order term
  vanishes, but the exactly isospectral blocks differ in their fourth-cumulant invariant. -/
  symmetricSparseLDLosesOrientation :
    Blindness.Isospectral2 (Blindness.localizedCovarianceBlock (3 / 2))
        (Blindness.rotatedCovarianceBlock (3 / 2)) ∧
      Blindness.blockEntryFourthMean (Blindness.localizedCovarianceBlock (3 / 2)) ≠
        Blindness.blockEntryFourthMean (Blindness.rotatedCovarianceBlock (3 / 2))
  /-- For a coding-symmetric Rademacher architecture, the missing LD orientation changes the
  fourth-order low-SNR information coefficient by exactly `49 / 96`. -/
  symmetricLDChangesLowSNRCoefficient :
    ∀ c m1 m2 m3 m4 : ℝ,
      Blindness.lowSNRFourthCoefficient c 1 (-2) m1 m2 m3 m4 Blindness.rotatedUniformFourthInvariant -
          Blindness.lowSNRFourthCoefficient c 1 (-2) m1 m2 m3 m4 Blindness.localizedUniformFourthInvariant =
        49 / 96
  /-- Both signs of a strong sparse-LD direction have a population gap, while a balanced
  environment mixture cancels it. -/
  environmentMixtureClosesPopulationGap :
    Blindness.populationGapCertificate (4 / 5) < 0 ∧
      Blindness.populationGapCertificate (-(4 / 5)) < 0 ∧
      Blindness.populationGapCertificate (ancestryMixtureCorrelation (4 / 5) (1 / 2)) = 1
  /-- Equal-sign active LD cannot be diluted by mixing; the explicit closure theorem is a
  sign-cancellation result. -/
  sameSignEnvironmentPoolingDoesNotMoveGapParameter :
    ∀ rho mix : ℝ, Blindness.pooledEnvironmentCorrelation rho rho mix = rho
  /-- Five demographic epochs already reduce root-sample spectrum estimation to a
  `sampleSize⁻¹ᐟ¹⁴` history-reconstruction exponent. -/
  fiveEpochDemographyIsSeverelyIllConditioned :
    PopGen.fixedEpochSampleRateExponent 5 = 1 / 14
  /-- Kingman's complete rate ladder has the convergent reciprocal sum behind the all-sample
  Müntz obstruction, and every finite spectrum has an explicit rank null direction. -/
  kingmanSpectrumHasIdentifiabilityBoundary :
    Summable (fun k : ℕ ↦
      1 / Coalescent.deathRate (k + 2)) ∧
      ∀ n : ℕ, ∀ observation : (Fin (n + 1) → ℝ) →ₗ[ℝ] (Fin n → ℝ),
        ∃ direction : Fin (n + 1) → ℝ,
          direction ≠ 0 ∧ observation direction = 0
  /-- Normalized pairwise genealogy is speed-blind, while the three-lineage merger rate exactly
  recovers the speed-bias parameter. -/
  speedConditionedGenealogyNeedsThreeLineages :
    ∀ β : ℝ, Blindness.speedTiltBetaMergerRate β 2 2 = 1 ∧
      Blindness.speedBiasParameterFromTripleRate (Blindness.speedTiltBetaMergerRate β 3 3) = β
  /-- The universal branching-front object is a marked successful-family measure: its weighted
  fraction projection gives every unconditioned merger rate, while zero tilt recovers that
  projection exactly. -/
  markedSuccessfulFamilyMeasureDeterminesGenealogy :
    ∀ (ν : MeasureTheory.Measure Blindness.MarkedBreakout.SuccessfulFamilyMark) (b k : ℕ),
      2 ≤ k →
        Blindness.MarkedBreakout.speedTiltedGenealogyMeasure 0 ν = Blindness.MarkedBreakout.genealogyMeasure ν ∧
          Blindness.MarkedBreakout.markedEventMergerRate ν b k = Blindness.MarkedBreakout.markedLambdaMergerRate ν b k
  /-- General successful events are complete mass partitions.  Their collision-weighted marked
  measure is the `Ξ` genealogy law, and collision integrability controls every fixed sample. -/
  markedMassPartitionMeasureDeterminesXi :
    ∀ (n : ℕ) (ν : MeasureTheory.Measure Blindness.XiFromMarks.MarkedMassPartition),
      Blindness.XiFromMarks.HasFiniteCollisionIntensity ν →
        Blindness.XiFromMarks.speedTiltedXiMeasure 0 ν = Blindness.XiFromMarks.xiMeasure ν ∧
          Blindness.XiFromMarks.samplePartitionChangeRateBound n ν < ⊤
  /-- A complete front trajectory cannot identify whether a sweep has one origin or two: the
  collision rate changes and only the two-origin mechanism admits a simultaneous pair-pair
  merger. -/
  frontTrajectoryDoesNotDetermineXi :
    ∀ x : ℝ, x ≠ 0 →
      Blindness.XiFromMarks.paintboxWeight ![x] ≠ Blindness.XiFromMarks.paintboxWeight ![x / 2, x / 2] ∧
        Blindness.XiFromMarks.disjointPairMergeProbability ![x] = 0 ∧
          0 < Blindness.XiFromMarks.disjointPairMergeProbability ![x / 2, x / 2]
  /-- Rank-one two-colour response gives the pioneer fraction and logarithmic amplitude repair
  exactly; the remaining hard-selection obstruction is the uniform probabilistic estimate. -/
  twoColourPioneerResponseIsExact :
    ∀ conversion gamma w : ℝ, conversion ≠ 0 → gamma ≠ 0 → -1 < w →
      conversion * w / (conversion * 1 + conversion * w) = Blindness.XiFromMarks.pioneerWeightFraction w ∧
        Real.exp (-(gamma * Blindness.XiFromMarks.pioneerWeightDisplacement gamma w)) * (1 + w) = 1
  /-- The critical log-mgf transform has unit additive mass and zero centered derivative mass. -/
  branchingRandomWalkBoundaryTransformIsCritical :
    ∀ logMgf logMgfDerivative criticalParameter criticalSpeed : ℝ,
      criticalParameter * criticalSpeed - logMgf = Real.log 2 →
      criticalSpeed = logMgfDerivative →
        Blindness.XiFromMarks.boundaryTiltMass logMgf criticalParameter criticalSpeed = 1 ∧
          Blindness.XiFromMarks.boundaryTiltCenteredFirstMoment
            logMgf logMgfDerivative criticalParameter criticalSpeed = 0
  /-- Selected derivative flux gives the one-breakout scale and a quadratic two-breakout bound. -/
  selectedDerivativeFluxControlsBreakouts :
    ∀ (Pioneer : Type) [Fintype Pioneer] [DecidableEq Pioneer]
      (tailConstant threshold blockScale fluxConstant : ℝ)
      (weight : Pioneer → ℝ),
      0 ≤ tailConstant → 0 < threshold →
      (∀ pioneer, 0 ≤ weight pioneer) →
      Blindness.XiFromMarks.selectedPioneerFlux weight = blockScale * fluxConstant →
        (∑ pioneer,
            paretoExceedanceMass tailConstant threshold (weight pioneer)) =
            blockScale * (tailConstant * fluxConstant / threshold) ∧
          Blindness.XiFromMarks.distinctPairExceedanceMass
              (fun pioneer ↦ paretoExceedanceMass
                tailConstant threshold (weight pioneer)) ≤
            (blockScale * (tailConstant * fluxConstant / threshold)) ^ 2
  /-- A full-tree flux law transfers exactly when the flux discarded by selection vanishes. -/
  selectedPioneerFluxFollowsFromNegligiblePruning :
    ∀ (fullTreeFlux selectedFlux prunedFlux : ℕ → ℝ) (fluxConstant : ℝ),
      Blindness.XiFromMarks.IsSelectedFluxDecomposition fullTreeFlux selectedFlux prunedFlux →
      Filter.Tendsto fullTreeFlux Filter.atTop (nhds fluxConstant) →
      Filter.Tendsto prunedFlux Filter.atTop (nhds 0) →
        Filter.Tendsto selectedFlux Filter.atTop (nhds fluxConstant)
  /-- One pioneer gives one atom pathwise; `w/(1+w)` additionally consumes common-profile
  relaxation, and the amplitude-front response is real-valued even on lattice BRWs. -/
  uniquePioneerCommonProfileDeterminesMarkedResponse :
    ∀ conversion gamma w backgroundCount pioneerCount : ℝ,
      conversion ≠ 0 → backgroundCount + pioneerCount ≠ 0 →
      Blindness.XiFromMarks.HasCommonProfileRelaxation conversion 1 w backgroundCount pioneerCount →
        (Blindness.XiFromMarks.totalFamilyFraction ![Blindness.XiFromMarks.pioneerWeightFraction w] = Blindness.XiFromMarks.pioneerWeightFraction w ∧
          Blindness.XiFromMarks.paintboxWeight ![Blindness.XiFromMarks.pioneerWeightFraction w] = Blindness.XiFromMarks.pioneerWeightFraction w ^ 2 ∧
            Blindness.XiFromMarks.disjointPairMergeProbability ![Blindness.XiFromMarks.pioneerWeightFraction w] = 0) ∧
          pioneerCount / (backgroundCount + pioneerCount) = Blindness.XiFromMarks.pioneerWeightFraction w ∧
            Blindness.XiFromMarks.amplitudeFront gamma (1 + w) - Blindness.XiFromMarks.amplitudeFront gamma 1 =
              Blindness.XiFromMarks.pioneerWeightDisplacement gamma w
  /-- Linear pulled clocks and superlinear stable clocks lie on opposite sides of reciprocal
  summability; using this as an identifiability theorem still requires the transform-system
  reduction. -/
  selectedGenealogyHasMuntzRateDichotomy :
    ∀ coefficient alpha : ℝ, 0 < coefficient → 1 < alpha →
      (¬Summable fun n : ℕ ↦
          1 / Blindness.criticallyPulledLinearRateLadder coefficient n) ∧
        Summable (fun n : ℕ ↦ 1 / Blindness.stablePowerRateLadder alpha n) ∧
          Summable (fun n : ℕ ↦ 1 / Blindness.stablePowerRateLadder 2 n)
  /-- The complete uniform procedure-risk signature is sufficient and is
  coarser than every other sufficient genomic design invariant. -/
  genomicAlgorithmicRiskSignatureIsCoarsest :
    ∀ (Algorithm Design Model Loss : Type)
      (risk : Algorithm → Design → Model → Loss → ℝ),
      Blindness.TrafficInvariantSeparation.RiskSignaturesFactorThrough risk (Blindness.TrafficInvariantSeparation.algorithmicRiskSignature risk) ∧
        ∀ (Invariant : Type) (invariant : Design → Invariant),
          Blindness.TrafficInvariantSeparation.RiskSignaturesFactorThrough risk invariant →
            ∀ left right, invariant left = invariant right →
              Blindness.TrafficInvariantSeparation.algorithmicRiskSignature risk left =
                Blindness.TrafficInvariantSeparation.algorithmicRiskSignature risk right
  /-- Positive-even graph-local degrees and handshaking force the full finite
  genomic rank-one traffic correction to vanish. -/
  genomicRankOneTrafficExpansionFollowsFromHandshake :
    ∀ (Term : Type) [Fintype Term]
      (coefficient : Term → ℝ) (hasOddDegree : Term → Bool)
      (vertices edges : Term → ℕ)
      (degree : ∀ term, Fin (vertices term) → ℕ),
      (∀ term, hasOddDegree term = false →
        ∀ vertex, 0 < degree term vertex) →
      (∀ term, hasOddDegree term = false →
        ∀ vertex, Even (degree term vertex)) →
      (∀ term, hasOddDegree term = false →
        ∑ vertex, degree term vertex = 2 * edges term) →
        Filter.Tendsto
          (fun population : ℕ ↦
            Blindness.TrafficInvariantSeparation.finiteRankOneTrafficCorrection coefficient hasOddDegree vertices edges
              (population + 1))
          Filter.atTop (nhds 0)
  /-- The same concrete balanced matrices simultaneously certify PSD order,
  traffic invisibility, the finite Hamiltonian, ground-state equality, and
  supercritical pressure separation. -/
  positiveLDBalancedRankOneCovarianceHasFullWitness :
    ∀ (Term : Type) [Fintype Term]
      (coefficient : Term → ℝ) (hasOddDegree : Term → Bool)
      (vertices edges : Term → ℕ),
      (∀ term, hasOddDegree term = false → vertices term ≤ edges term) →
      ∀ baseline spikeStrength temperature : ℝ,
        0 ≤ baseline → 0 < spikeStrength →
        1 < temperature * spikeStrength →
          Blindness.TrafficInvariantSeparation.ConcreteBalancedPSDPressureWitness coefficient hasOddDegree vertices edges
            baseline spikeStrength temperature
  /-- A mesoscopic LD block vanishes from every fixed traffic coordinate but has unit normalized
  energy after a logarithmic number of power iterations. -/
  rareLDSubspaceEvadesFixedTrafficAtLogRuntime :
    Blindness.TrafficInvariantSeparation.FixedTrafficLogRuntimeSeparation
  /-- Even degree one can resolve a vanishing mesoscopic LD mass when its
  coefficient grows at the reciprocal traffic resolution. -/
  rareLDSubspaceEvadesLimitingTrafficAtDegreeOne :
    ∀ baseline : ℝ,
      Filter.Tendsto
          (fun iteration ↦ diagonalTrafficCorrection baseline 1 iteration)
          Filter.atTop (nhds 0) ∧
        ∀ iteration,
          Blindness.TrafficInvariantSeparation.amplifiedDegreeOneTrafficDifference baseline iteration = 2
  /-- The genuine finite diagonal iteration realizes the same separation with ambient dimension `16^k`, exceptional rank `4^k`, fixed-time decay, and
  unit logarithmic-time normalized output. -/
  rareLDSubspaceConcreteGFOMEvadesFixedTrafficAtLogRuntime :
    Blindness.TrafficInvariantSeparation.ConcreteGFOMLogRuntimeSeparation
  /-- A positive rank-one LD outlier is invisible to every limiting bulk
  spectral observable but changes the spectral maximum and trace-one PSD SDP
  optimum at every finite size. -/
  genomicBulkSpectralLawDoesNotDetermineExtremalSpectrumOrSDP :
    ∀ baseline spikeStrength : ℝ, 0 < spikeStrength →
      Blindness.TrafficInvariantSeparation.BulkSpectralLawExtremalSDPSeparation baseline spikeStrength
  /-- Every finite contracted rank-one LD traffic expansion vanishes, while
  the associated variational pressure is positive above `tλ = 1`. -/
  positiveLDSpikeFixedTrafficInvisibleVariationalPressureVisible :
    ∀ (Term : Type) [Fintype Term]
      (coefficient : Term → ℝ) (hasOddDegree : Term → Bool)
      (vertices edges : Term → ℕ),
      (∀ term, hasOddDegree term = false → vertices term ≤ edges term) →
      ∀ tlam : ℝ, 1 < tlam →
        Filter.Tendsto
            (fun population : ℕ ↦
              Blindness.TrafficInvariantSeparation.finiteRankOneTrafficCorrection coefficient hasOddDegree vertices edges
                (population + 1))
            Filter.atTop (nhds 0) ∧
          0 < Blindness.TrafficInvariantSeparation.cwVariationalPressureGap tlam
  /-- Every fixed genomic traffic coordinate misses the positive LD spike, but
  its genuine finite Rademacher pressure has a positive uniform lower bound
  throughout the exact supercritical regime, with no LDP premise. -/
  positiveLDSpikeFixedTrafficInvisibleFinitePressureVisible :
    ∀ (Term : Type) [Fintype Term]
      (coefficient : Term → ℝ) (hasOddDegree : Term → Bool)
      (vertices edges : Term → ℕ),
      (∀ term, hasOddDegree term = false → vertices term ≤ edges term) →
      ∀ tlam : ℝ, 1 < tlam →
        Blindness.TrafficInvariantSeparation.RankOneSpikeInvisibleWithFinitePressure
          coefficient hasOddDegree vertices edges tlam
  /-- Every interior magnetisation objective lower-bounds genuine finite
  genomic pressure at each nonempty population. -/
  genomicFiniteCWPressureDominatesVariationalObjective :
    ∀ (population : ℕ) (tlam m : ℝ),
      0 < population → 0 ≤ tlam → |m| < 1 →
        Blindness.TrafficInvariantSeparation.cwObjective tlam m ≤ Blindness.TrafficInvariantSeparation.finiteCWPressureGap population tlam
  /-- Every finite genotype-count type has mass at most one at and below the
  critical LD coupling. -/
  genomicFiniteCWTypeMassLeOneOfSubcritical :
    ∀ (population upSpins : ℕ) (tlam : ℝ),
      tlam ≤ 1 → upSpins ∈ Finset.range (population + 1) →
        Blindness.TrafficInvariantSeparation.finiteCWTypeMass population tlam upSpins ≤ 1
  /-- For nonnegative coupling, the actual finite genomic pressure converges
  to baseline exactly at and below the Curie--Weiss threshold. -/
  genomicFiniteCWPressureHasExactCriticalPoint :
    ∀ tlam : ℝ, 0 ≤ tlam →
      (Filter.Tendsto
          (fun population : ℕ ↦ Blindness.TrafficInvariantSeparation.finiteCWPressureGap (population + 1) tlam)
          Filter.atTop (nhds 0) ↔
        tlam ≤ 1)
  /-- The actual finite genomic pressure converges to its full variational LD
  value for all nonnegative couplings. -/
  genomicFiniteCWPressureConvergesToVariational :
    ∀ tlam : ℝ, 0 ≤ tlam →
      Filter.Tendsto
        (fun population : ℕ ↦ Blindness.TrafficInvariantSeparation.finiteCWPressureGap (population + 1) tlam)
        Filter.atTop (nhds (Blindness.TrafficInvariantSeparation.cwVariationalPressureGap tlam))
  /-- The full finite genomic pressure limit is uniform over all nonnegative
  LD couplings. -/
  genomicFiniteCWPressureConvergesUniformlyOnNonnegative :
    TendstoUniformlyOn
      (fun population : ℕ ↦ fun tlam : ℝ ↦
        Blindness.TrafficInvariantSeparation.finiteCWPressureGap (population + 1) tlam)
      Blindness.TrafficInvariantSeparation.cwVariationalPressureGap Filter.atTop (Set.Ici 0)
  /-- Every nonempty finite genomic population has globally half-Lipschitz
  pressure in effective coupling. -/
  genomicFiniteCWPressureIsHalfLipschitz :
    ∀ population : ℕ, 0 < population →
      LipschitzWith (⟨1 / 2, by norm_num⟩ : NNReal)
        (Blindness.TrafficInvariantSeparation.finiteCWPressureGap population)
  /-- Every nonempty finite genomic population has pressure monotone in
  effective LD coupling. -/
  genomicFiniteCWPressureIsMonotone :
    ∀ population : ℕ, 0 < population →
      Monotone (Blindness.TrafficInvariantSeparation.finiteCWPressureGap population)
  /-- At every nonempty population, the genuine rank-one-spiked genomic
  pressure strictly exceeds the unspiked baseline throughout `tλ > 1`. -/
  positiveLDSpikeFinitePressureExceedsBaseline :
    ∀ (baseline : ℝ) (population : ℕ)
      (temperature spikeStrength : ℝ),
      0 < population → 1 < temperature * spikeStrength →
        Blindness.TrafficInvariantSeparation.finiteBaselineRademacherPressure baseline temperature <
          Blindness.TrafficInvariantSeparation.finiteRankOneRademacherPressure
            baseline population temperature spikeStrength
  /-- The genuine spiked-minus-baseline genomic pressure has exact critical
  effective coupling one. -/
  positiveLDSpikePressureDifferenceHasExactCriticalPoint :
    ∀ baseline temperature spikeStrength : ℝ,
      0 ≤ temperature * spikeStrength →
        Blindness.TrafficInvariantSeparation.FiniteRankOnePressureCriticalStatement baseline temperature spikeStrength
  /-- The complete finite LD-spiked pressure converges to baseline plus its
  variational pressure correction. -/
  positiveLDSpikePressureConvergesToVariational :
    ∀ baseline temperature spikeStrength : ℝ,
      0 ≤ temperature * spikeStrength →
        Blindness.TrafficInvariantSeparation.FiniteRankOnePressureVariationalLimitStatement
          baseline temperature spikeStrength
  /-- At fixed nonnegative temperature, finite LD-spiked pressure converges
  uniformly over all nonnegative spike strengths. -/
  positiveLDSpikePressureConvergesUniformlyOnNonnegativeStrength :
    ∀ baseline temperature : ℝ, 0 ≤ temperature →
      Blindness.TrafficInvariantSeparation.FiniteRankOnePressureUniformLimitStatement baseline temperature
  /-- One positive LD spike simultaneously defeats fixed traffic sufficiency
  and the lower-ground-state characterization. -/
  positiveLDSpikeRefutesTrafficAndGroundStateDichotomies :
    ∀ (Term Genotype : Type) [Fintype Term]
      (coefficient : Term → ℝ) (hasOddDegree : Term → Bool)
      (vertices edges : Term → ℕ),
      (∀ term, hasOddDegree term = false → vertices term ≤ edges term) →
      ∀ (alignment : Genotype → ℝ) (orthogonal aligned : Genotype)
        (baseline spikeStrength population temperature : ℝ),
        0 < spikeStrength → population ≠ 0 →
        alignment orthogonal = 0 → alignment aligned = population →
        1 < temperature * spikeStrength →
          Blindness.TrafficInvariantSeparation.RankOneSpikeRefutesBothDichotomies coefficient hasOddDegree vertices edges
            alignment orthogonal aligned baseline spikeStrength population temperature
  /-- Positive-cone order and the lower genetic ground state do not determine exponential
  pressure: an orthogonal state preserves the minimum while an aligned state separates. -/
  positiveLDSpikeGroundStateDoesNotFixPressure :
    ∀ baseline spikeStrength population tlam : ℝ, 0 ≤ spikeStrength →
      2 * Real.log 2 < tlam →
        ((∀ state : Bool, baseline ≤
            Blindness.TrafficInvariantSeparation.rankOneEnergyDensity baseline spikeStrength population
              (if state = true then population else 0)) ∧
          Blindness.TrafficInvariantSeparation.rankOneEnergyDensity baseline spikeStrength population
            (if false = true then population else 0) = baseline) ∧
          0 < Blindness.TrafficInvariantSeparation.cwObjective tlam 1
  /-- The positive-temperature LD-spike pressure separates at exactly `tλ = 1`. -/
  ldOverlapPressureHasExactCriticalPoint :
    ∀ tlam : ℝ,
      (tlam ≤ 1 → ∀ m : ℝ, |m| ≤ 1 → Blindness.TrafficInvariantSeparation.cwObjective tlam m ≤ 0) ∧
        (1 < tlam → ∃ m : ℝ, |m| < 1 ∧ 0 < Blindness.TrafficInvariantSeparation.cwObjective tlam m)
  /-- The actual supremal variational pressure gap vanishes exactly at and
  below the Curie--Weiss threshold. -/
  ldVariationalPressureGapHasExactCriticalPoint :
    ∀ tlam : ℝ, Blindness.TrafficInvariantSeparation.cwVariationalPressureGap tlam = 0 ↔ tlam ≤ 1
  /-- The genomic LD pressure profile is globally half-Lipschitz, continuous,
  monotone, and convex in effective coupling. -/
  ldVariationalPressureGapHasGlobalRegularity :
    LipschitzWith (⟨1 / 2, by norm_num⟩ : NNReal) Blindness.TrafficInvariantSeparation.cwVariationalPressureGap ∧
      Continuous Blindness.TrafficInvariantSeparation.cwVariationalPressureGap ∧
        Monotone Blindness.TrafficInvariantSeparation.cwVariationalPressureGap ∧
          ConvexOn ℝ Set.univ Blindness.TrafficInvariantSeparation.cwVariationalPressureGap
  /-- The sharp scalar-to-random-design ledger subtracts the sum of two
  independently certified comparison errors. -/
  matchedBayesRandomDesignAsymmetricReduction :
    ∀ scalarLeft scalarRight randomLeft randomRight leftError rightError delta : ℝ,
      |randomLeft - scalarLeft| ≤ leftError →
      |randomRight - scalarRight| ≤ rightError →
      scalarRight - scalarLeft = delta →
        delta - (leftError + rightError) ≤ randomRight - randomLeft
  /-- Scalar matched-channel separation transfers to random design with exactly two comparison
  errors and no hidden constant. -/
  matchedBayesRandomDesignReduction :
    ∀ scalarLeft scalarRight randomLeft randomRight epsilon delta : ℝ,
      |randomLeft - scalarLeft| ≤ epsilon →
      |randomRight - scalarRight| ≤ epsilon →
      scalarRight - scalarLeft = delta →
        delta - 2 * epsilon ≤ randomRight - randomLeft
  /-- Independent vanishing comparison bounds on the two designs suffice for
  eventual transfer of every positive scalar gap. -/
  matchedBayesRandomDesignEventuallySeparatesWithAsymmetricErrors :
    ∀ (Index : Type) (regime : Filter Index)
      (scalarLeft scalarRight delta : ℝ)
      (randomLeft randomRight leftError rightError : Index → ℝ),
      (∀ index, |randomLeft index - scalarLeft| ≤ leftError index) →
      (∀ index, |randomRight index - scalarRight| ≤ rightError index) →
      scalarRight - scalarLeft = delta → 0 < delta →
      Filter.Tendsto leftError regime (nhds 0) →
      Filter.Tendsto rightError regime (nhds 0) →
        ∀ᶠ index in regime, randomLeft index < randomRight index
  /-- Every positive scalar matched-channel gap eventually transfers along a
  regime whose random-design comparison error vanishes. -/
  matchedBayesRandomDesignEventuallySeparates :
    ∀ (Index : Type) (regime : Filter Index)
      (scalarLeft scalarRight delta : ℝ)
      (randomLeft randomRight comparisonError : Index → ℝ),
      (∀ index, |randomLeft index - scalarLeft| ≤ comparisonError index) →
      (∀ index, |randomRight index - scalarRight| ≤ comparisonError index) →
      scalarRight - scalarLeft = delta → 0 < delta →
      Filter.Tendsto comparisonError regime (nhds 0) →
        ∀ᶠ index in regime, randomLeft index < randomRight index
  /-- The explicit `constant / sqrt aspectRatio` comparison rate transfers a
  scalar gap once it is below half the gap. -/
  matchedBayesRandomDesignSeparatesAtLargeAspect :
    ∀ scalarLeft scalarRight randomLeft randomRight aspectRatio constant delta : ℝ,
      |randomLeft - scalarLeft| ≤ constant / Real.sqrt aspectRatio →
      |randomRight - scalarRight| ≤ constant / Real.sqrt aspectRatio →
      scalarRight - scalarLeft = delta →
      2 * (constant / Real.sqrt aspectRatio) < delta →
        randomLeft < randomRight
  /-- Every fixed positive scalar gap eventually transfers when aspect ratio
  tends to infinity at the inverse-square-root comparison rate. -/
  matchedBayesRandomDesignEventuallySeparatesAtDivergingAspect :
    ∀ (Index : Type) (regime : Filter Index)
      (scalarLeft scalarRight delta constant : ℝ)
      (aspectRatio randomLeft randomRight : Index → ℝ),
      (∀ index,
        |randomLeft index - scalarLeft| ≤ constant / Real.sqrt (aspectRatio index)) →
      (∀ index,
        |randomRight index - scalarRight| ≤ constant / Real.sqrt (aspectRatio index)) →
      scalarRight - scalarLeft = delta → 0 < delta →
      Filter.Tendsto aspectRatio regime Filter.atTop →
        ∀ᶠ index in regime, randomLeft index < randomRight index
  /-- Diverging aspect and vanishing reciprocal Wishart ratio are the same
  one-sided limit, with identical pointwise comparison-error formulas. -/
  matchedBayesAspectWishartRatioBridge :
    ∀ (Index : Type) (regime : Filter Index)
      (aspectRatio : Index → ℝ) (constant : ℝ),
      (Filter.Tendsto aspectRatio regime Filter.atTop ↔
        Filter.Tendsto (fun index ↦ (aspectRatio index)⁻¹) regime (𝓝[>] 0)) ∧
      (∀ index, constant / Real.sqrt (aspectRatio index) =
        constant * Real.sqrt ((aspectRatio index)⁻¹))
  /-- A genomic comparison error at Wishart scale vanishes with the adjusted
  dimension/sample ratio. -/
  matchedBayesWishartInformationErrorVanishes :
    ∀ (Index : Type) (regime : Filter Index)
      (informationError adjustedRatio : Index → ℝ) (constant : ℝ),
      Filter.Tendsto adjustedRatio regime (nhds 0) →
      (∀ index,
        |informationError index| ≤ constant * Real.sqrt (adjustedRatio index)) →
        Filter.Tendsto informationError regime (nhds 0)
  /-- The two genomic designs may use distinct Wishart constants and ratios;
  independent vanishing transfers the scalar gap. -/
  matchedBayesRandomDesignEventuallySeparatesAtAsymmetricWishartRatios :
    ∀ (Index : Type) (regime : Filter Index)
      (scalarLeft scalarRight delta leftConstant rightConstant : ℝ)
      (leftRatio rightRatio randomLeft randomRight : Index → ℝ),
      (∀ index, |randomLeft index - scalarLeft| ≤
        leftConstant * Real.sqrt (leftRatio index)) →
      (∀ index, |randomRight index - scalarRight| ≤
        rightConstant * Real.sqrt (rightRatio index)) →
      scalarRight - scalarLeft = delta → 0 < delta →
      Filter.Tendsto leftRatio regime (nhds 0) →
      Filter.Tendsto rightRatio regime (nhds 0) →
        ∀ᶠ index in regime, randomLeft index < randomRight index
  /-- Every fixed positive scalar genomic gap transfers at the Wishart rate
  when `(p+1)/n` tends to zero. -/
  matchedBayesRandomDesignEventuallySeparatesAtWishartRatio :
    ∀ (Index : Type) (regime : Filter Index)
      (scalarLeft scalarRight delta constant : ℝ)
      (adjustedRatio randomLeft randomRight : Index → ℝ),
      (∀ index,
        |randomLeft index - scalarLeft| ≤
          constant * Real.sqrt (adjustedRatio index)) →
      (∀ index,
        |randomRight index - scalarRight| ≤
          constant * Real.sqrt (adjustedRatio index)) →
      scalarRight - scalarLeft = delta → 0 < delta →
      Filter.Tendsto adjustedRatio regime (nhds 0) →
        ∀ᶠ index in regime, randomLeft index < randomRight index
  /-- Finite singular-value support, rank, and operator bounds derive the
  normalized genomic nuclear-distance inequality. -/
  matchedBayesSingularSpectrumHasNormalizedNuclearBound :
    ∀ (Coordinate : Type) [Fintype Coordinate] [DecidableEq Coordinate]
      (spectrum : Blindness.TrafficInvariantSeparation.FiniteLowRankSingularSpectrum Coordinate),
      0 < Fintype.card Coordinate →
        spectrum.normalizedNuclearDistance ≤
          spectrum.operatorBound * spectrum.rankFraction
  /-- A concrete bounded rank-one genomic covariance perturbation has
  vanishing certified matched-information effect. -/
  matchedBayesCertifiedRankOnePerturbationIsAsymptoticallyInvisible :
    ∀ (certificate : ℕ → Blindness.TrafficInvariantSeparation.MatchedInformationPathCertificate)
      (varianceBound spikeStrength : ℝ) (hspike : 0 ≤ spikeStrength),
      (∀ population, (certificate population).variance ≤ varianceBound) →
      (∀ population,
        (certificate population).nuclearDistance =
          Blindness.TrafficInvariantSeparation.FiniteLowRankSingularSpectrum.normalizedNuclearDistance
            (Blindness.TrafficInvariantSeparation.finiteRankOneSingularSpectrum population spikeStrength hspike)) →
        Filter.Tendsto
          (fun population ↦ (certificate population).informationPath 1 -
            (certificate population).informationPath 0)
          Filter.atTop (nhds 0)
  /-- Matrix I--MMSE plus posterior-covariance trace control yields the matched
  genomic nuclear Lipschitz estimate. -/
  matchedBayesInformationPathHasNuclearBound :
    ∀ certificate : Blindness.TrafficInvariantSeparation.MatchedInformationPathCertificate,
      |certificate.informationPath 1 - certificate.informationPath 0| ≤
        certificate.variance / 2 * certificate.nuclearDistance
  /-- The I--MMSE, nuclear/Frobenius, and Wishart ledgers imply the exact
  normalized matched-information comparison rate. -/
  matchedBayesHasWishartFrobeniusComparisonRate :
    ∀ dimension sampleSize signal variance operatorBound informationError
      nuclearError frobeniusError : ℝ,
      0 < dimension → 0 < sampleSize → 0 ≤ signal → 0 ≤ variance →
      |informationError| ≤ signal * variance / (2 * dimension) * nuclearError →
      nuclearError ≤ Real.sqrt dimension * frobeniusError →
      frobeniusError ≤ operatorBound *
        Real.sqrt (dimension * ((dimension + 1) / sampleSize)) →
        |informationError| ≤ signal * variance * operatorBound / 2 *
          Real.sqrt ((dimension + 1) / sampleSize)
  /-- The exact Wishart moment identity and trace bounds imply the complete
  normalized matched-information comparison rate. -/
  matchedBayesHasWishartMomentIdentityComparisonRate :
    ∀ dimension sampleSize signal variance operatorBound covarianceTrace
      covarianceTraceSq frobeniusSecondMoment frobeniusError nuclearError
      informationError : ℝ,
      0 < dimension → 0 < sampleSize → 0 ≤ signal → 0 ≤ variance →
      0 ≤ operatorBound →
      |covarianceTrace| ≤ dimension * operatorBound →
      covarianceTraceSq ≤ dimension * operatorBound ^ 2 →
      frobeniusSecondMoment =
        (covarianceTrace ^ 2 + covarianceTraceSq) / sampleSize →
      frobeniusError ≤ Real.sqrt frobeniusSecondMoment →
      nuclearError ≤ Real.sqrt dimension * frobeniusError →
      |informationError| ≤ signal * variance / (2 * dimension) * nuclearError →
        |informationError| ≤ signal * variance * operatorBound / 2 *
          Real.sqrt ((dimension + 1) / sampleSize)
  /-- A certified matched-information family with uniformly bounded prior
  variance and vanishing rank fraction has vanishing information gap. -/
  matchedBayesCertifiedSublinearRankIsInvisibleUnderVarianceBound :
    ∀ (Index : Type) (regime : Filter Index)
      (certificate : Index → Blindness.TrafficInvariantSeparation.MatchedInformationPathCertificate)
      (varianceBound operatorBound : ℝ) (rankFraction : Index → ℝ),
      (∀ index, (certificate index).variance ≤ varianceBound) →
      Filter.Tendsto rankFraction regime (nhds 0) →
      (∀ index,
        (certificate index).nuclearDistance ≤ operatorBound * rankFraction index) →
        Blindness.TrafficInvariantSeparation.MatchedInformationPathGapTendsToZero regime certificate
  /-- Exact common variance is a special case of the uniform-bound result. -/
  matchedBayesCertifiedSublinearRankIsInvisible :
    ∀ (Index : Type) (regime : Filter Index)
      (certificate : Index → Blindness.TrafficInvariantSeparation.MatchedInformationPathCertificate)
      (operatorBound : ℝ) (rankFraction : Index → ℝ),
      (∃ variance : ℝ, ∀ index, (certificate index).variance = variance) →
      Filter.Tendsto rankFraction regime (nhds 0) →
      (∀ index,
        (certificate index).nuclearDistance ≤ operatorBound * rankFraction index) →
        Blindness.TrafficInvariantSeparation.MatchedInformationPathGapTendsToZero regime certificate
  /-- Under the nuclear estimate, a vanishing-rank-fraction genomic covariance
  perturbation has vanishing matched information-density effect. -/
  matchedBayesSublinearRankPerturbationsAreInvisible :
    ∀ (densityGap rankFraction : ℕ → ℝ) (constant : ℝ),
      Filter.Tendsto rankFraction Filter.atTop (nhds 0) →
      (∀ index, |densityGap index| ≤ constant * rankFraction index) →
        Filter.Tendsto densityGap Filter.atTop (nhds 0)
  /-- A positive finite matched-density gap forces a quantitatively extensive
  genomic covariance-rank fraction. -/
  matchedBayesPositiveGapForcesExtensiveRank :
    ∀ densityGap constant rankFraction delta : ℝ,
      0 < constant → 0 < delta → delta ≤ |densityGap| →
      |densityGap| ≤ constant * rankFraction →
        0 < rankFraction ∧ delta / constant ≤ rankFraction
  /-- A certified finite I--MMSE path gap forces the explicit extensive-rank
  lower bound without assuming the final nuclear information estimate. -/
  matchedBayesCertifiedPositiveGapForcesExtensiveRank :
    ∀ (certificate : Blindness.TrafficInvariantSeparation.MatchedInformationPathCertificate)
      (varianceBound operatorBound rankFraction delta : ℝ),
      certificate.variance ≤ varianceBound →
      0 < varianceBound → 0 < operatorBound → 0 < delta →
      delta ≤ |certificate.informationPath 1 - certificate.informationPath 0| →
      certificate.nuclearDistance ≤ operatorBound * rankFraction →
        0 < rankFraction ∧
          delta / (varianceBound * operatorBound / 2) ≤ rankFraction
  /-- Persistent certified I--MMSE path separation forces the exact eventual
  rank lower bound and excludes vanishing rank fraction. -/
  matchedBayesCertifiedPersistentGapRequiresExtensiveRank :
    ∀ (Index : Type) (regime : Filter Index) [regime.NeBot]
      (certificate : Index → Blindness.TrafficInvariantSeparation.MatchedInformationPathCertificate)
      (varianceBound operatorBound delta : ℝ) (rankFraction : Index → ℝ),
      0 < varianceBound → 0 < operatorBound → 0 < delta →
      (∀ index, (certificate index).variance ≤ varianceBound) →
      (∀ index,
        (certificate index).nuclearDistance ≤ operatorBound * rankFraction index) →
      (∀ᶠ index in regime, delta ≤
        |(certificate index).informationPath 1 -
          (certificate index).informationPath 0|) →
        (∀ᶠ index in regime,
          delta / (varianceBound * operatorBound / 2) ≤ rankFraction index) ∧
          ¬ Filter.Tendsto rankFraction regime (nhds 0)
  /-- A persistent matched-density gap forces an eventual positive rank
  fraction and rules out sublinear-rank perturbations. -/
  matchedBayesPersistentGapRequiresExtensiveRank :
    ∀ (Index : Type) (regime : Filter Index) [regime.NeBot]
      (densityGap rankFraction : Index → ℝ) (constant delta : ℝ),
      0 < constant → 0 < delta →
      (∀ᶠ index in regime, delta ≤ |densityGap index|) →
      (∀ index, |densityGap index| ≤ constant * rankFraction index) →
        (∀ᶠ index in regime, delta / constant ≤ rankFraction index) ∧
          ¬ Filter.Tendsto rankFraction regime (nhds 0)
  /-- Every degree-limited genomic risk that factors through a common truncated traffic profile
  inherits the complete Bayes-risk gap on one shared design. -/
  degreeLimitedGenomicRiskHasFullGapHardness :
    ∀ (Algorithm : Type) (D : ℕ) (risk : Algorithm → Blindness.TrafficInvariantSeparation.TruncatedTrafficRisk D)
      (left right : Fin (D + 1) → ℝ), left = right →
      ∀ bayesLeft bayesRight : ℝ,
        (∀ algorithm, bayesRight ≤ (risk algorithm).evaluate right) →
          ∀ algorithm,
            bayesRight - bayesLeft ≤ (risk algorithm).evaluate left - bayesLeft
  /-- Stable low-degree passage is quantitative: traffic resolution is
  multiplied by the coefficient `ℓ¹` mass. -/
  stableDegreeLimitedGenomicRiskHasQuantitativeTrafficBound :
    ∀ (D : ℕ) (risk : Blindness.TrafficInvariantSeparation.TruncatedTrafficRisk D)
      (left right : Fin (D + 1) → ℝ) (epsilon : ℝ),
      (∀ graph, |left graph - right graph| ≤ epsilon) →
        |risk.evaluate left - risk.evaluate right| ≤
          (∑ graph, |risk.coefficient graph|) * epsilon
  /-- Uniform coefficient mass makes quantitative fixed-depth traffic
  convergence sufficient for stable polynomial convergence. -/
  stableDegreeLimitedGenomicRiskConvergesOfBoundedCoefficientMass :
    ∀ (D : ℕ) (risk : ℕ → Blindness.TrafficInvariantSeparation.TruncatedTrafficRisk D)
      (left right : ℕ → Fin (D + 1) → ℝ)
      (discrepancy coefficientBound : ℝ),
      (∀ index graph,
        |left index graph - right index graph| ≤
          discrepancy * (1 / 2 : ℝ) ^ index) →
      (∀ index,
        (∑ graph, |(risk index).coefficient graph|) ≤ coefficientBound) →
      0 ≤ discrepancy →
        Filter.Tendsto
          (fun index ↦ (risk index).evaluate (left index) -
            (risk index).evaluate (right index))
          Filter.atTop (nhds 0)
  /-- In the uniqueness regime, a certified common finite-traffic expansion
  with a geometric tail determines the limiting matched pressure. -/
  highTemperatureGenomicTrafficDeterminesCertifiedPressure :
    ∀ (leftLimit rightLimit C q : ℝ) (commonTruncation : ℕ → ℝ),
      0 ≤ q → q < 1 →
      (∀ depth,
        |leftLimit - commonTruncation depth| ≤
          C * q ^ (depth + 1) / (1 - q)) →
      (∀ depth,
        |rightLimit - commonTruncation depth| ≤
          C * q ^ (depth + 1) / (1 - q)) →
        leftLimit = rightLimit
  /-- The diagonal genomic traffic hierarchy is strictly increasing at every
  finite edge depth, witnessed by probability laws on `[1,2]`. -/
  genomicLDTrafficHierarchyIsStrictAtEveryDegree :
    ∀ D : ℕ,
      ∃ left right : Fin (D + 2) → ℝ,
        Blindness.TrafficInvariantSeparation.IsMomentMatchedProbabilityPair D left right ∧
          Blindness.TrafficInvariantSeparation.SeparatesAtNextDiagonalTraffic D left right
  /-- A single probability pair defeats every truncated graph-polynomial risk
  at each finite depth while differing at the next LD traffic coordinate. -/
  genomicLDTrafficHasCommonBlindPairAtEveryDegree :
    ∀ D : ℕ,
      ∃ left right : Fin (D + 2) → ℝ,
        Blindness.TrafficInvariantSeparation.IsBlindPairForEveryTruncatedTrafficRisk D left right
  /-- Permutation invariance itself, rather than an assumed orbit-constancy
  premise, yields exact finite graph-sum factorization. -/
  permutationInvariantGenomicPolynomialFactorsThroughLDGraphs :
    ∀ (Slot Locus Graph : Type) [Fintype Slot] [DecidableEq Slot]
      [Fintype Locus] [Fintype Graph] [DecidableEq Graph]
      (shape : (Slot → Locus) → Graph)
      (coefficient value : (Slot → Locus) → ℝ),
      (∀ left right, shape left = shape right → Blindness.TrafficInvariantSeparation.SameEqualityPattern left right) →
      (∀ (permutation : Equiv.Perm Locus) monomial,
        coefficient (permutation ∘ monomial) = coefficient monomial) →
        (∑ monomial, coefficient monomial * value monomial) =
          ∑ graph, Blindness.TrafficInvariantSeparation.graphShapeCoefficient shape coefficient graph *
            ∑ monomial, if shape monomial = graph then value monomial else 0
  /-- Canonical unrooted factorization through the quotient by endpoint
  equality pattern requires no caller-supplied graph encoding. -/
  permutationInvariantGenomicPolynomialFactorsThroughCanonicalLDGraphs :
    ∀ (Slot Locus : Type) [Fintype Slot] [DecidableEq Slot] [Fintype Locus]
      (coefficient value : (Slot → Locus) → ℝ),
      (∀ (permutation : Equiv.Perm Locus) monomial,
        coefficient (permutation ∘ monomial) = coefficient monomial) →
        Blindness.TrafficInvariantSeparation.CanonicalTrafficFactorizationStatement coefficient value
  /-- Canonical rooted factorization uses `none` as the output locus and
  `some slot` as matrix-entry endpoint slots. -/
  permutationEquivariantGenomicPolynomialFactorsThroughRootedLDGraphs :
    ∀ (Slot Locus : Type) [Fintype Slot] [DecidableEq Slot] [Fintype Locus]
      (coefficient value : (Option Slot → Locus) → ℝ),
      (∀ (permutation : Equiv.Perm Locus) monomial,
        coefficient (permutation ∘ monomial) = coefficient monomial) →
        Blindness.TrafficInvariantSeparation.RootedCanonicalTrafficFactorizationStatement coefficient value
  /-- The homogeneous decomposition proves exact traffic factorization for
  every scalar genomic polynomial of total degree at most `D`. -/
  degreeLimitedGenomicPolynomialFactorsThroughCanonicalLDGraphs :
    ∀ (D : ℕ) (Locus : Type) [Fintype Locus]
      (coefficient value : (degree : Fin (D + 1)) →
        ((Fin (degree : ℕ) × Bool → Locus) → ℝ)),
      (∀ degree (permutation : Equiv.Perm Locus) monomial,
        coefficient degree (permutation ∘ monomial) = coefficient degree monomial) →
        Blindness.TrafficInvariantSeparation.DegreeAtMostTrafficFactorizationStatement coefficient value
  /-- The rooted homogeneous decomposition gives the corresponding exact
  degree-`D` statement for equivariant vector-polynomial coordinates. -/
  degreeLimitedGenomicEquivariantPolynomialFactorsThroughRootedLDGraphs :
    ∀ (D : ℕ) (Locus : Type) [Fintype Locus]
      (coefficient value : (degree : Fin (D + 1)) →
        ((Option (Fin (degree : ℕ) × Bool) → Locus) → ℝ)),
      (∀ degree (permutation : Equiv.Perm Locus) monomial,
        coefficient degree (permutation ∘ monomial) = coefficient degree monomial) →
        Blindness.TrafficInvariantSeparation.DegreeAtMostRootedTrafficFactorizationStatement coefficient value
  /-- Equality of canonical profiles implies exact equality of every invariant
  scalar polynomial of degree at most `D`. -/
  degreeLimitedGenomicPolynomialIsDeterminedByCanonicalLDProfile :
    ∀ (D : ℕ) (Locus : Type) [Fintype Locus]
      (coefficient leftValue rightValue : (degree : Fin (D + 1)) →
        ((Fin (degree : ℕ) × Bool → Locus) → ℝ)),
      (∀ degree (permutation : Equiv.Perm Locus) monomial,
        coefficient degree (permutation ∘ monomial) = coefficient degree monomial) →
      Blindness.TrafficInvariantSeparation.degreeAtMostCanonicalTrafficProfile leftValue =
        Blindness.TrafficInvariantSeparation.degreeAtMostCanonicalTrafficProfile rightValue →
        (∑ degree : Fin (D + 1),
          ∑ monomial, coefficient degree monomial * leftValue degree monomial) =
          ∑ degree : Fin (D + 1),
            ∑ monomial, coefficient degree monomial * rightValue degree monomial
  /-- Equality of rooted profiles determines every equivariant polynomial
  coordinate of degree at most `D`. -/
  degreeLimitedGenomicEquivariantPolynomialIsDeterminedByRootedLDProfile :
    ∀ (D : ℕ) (Locus : Type) [Fintype Locus]
      (coefficient leftValue rightValue : (degree : Fin (D + 1)) →
        ((Option (Fin (degree : ℕ) × Bool) → Locus) → ℝ)),
      (∀ degree (permutation : Equiv.Perm Locus) monomial,
        coefficient degree (permutation ∘ monomial) = coefficient degree monomial) →
      Blindness.TrafficInvariantSeparation.degreeAtMostRootedCanonicalTrafficProfile leftValue =
        Blindness.TrafficInvariantSeparation.degreeAtMostRootedCanonicalTrafficProfile rightValue →
        (∑ degree : Fin (D + 1),
          ∑ monomial, coefficient degree monomial * leftValue degree monomial) =
          ∑ degree : Fin (D + 1),
            ∑ monomial, coefficient degree monomial * rightValue degree monomial
  /-- Direct invariant separation transfers the complete Bayes gap to every
  uniform invariant degree-limited genomic polynomial procedure. -/
  degreeLimitedGenomicPolynomialHasDirectFullGapHardness :
    ∀ (Algorithm : Type) (D : ℕ) (Locus : Type) [Fintype Locus]
      (coefficient : Algorithm → (degree : Fin (D + 1)) →
        ((Fin (degree : ℕ) × Bool → Locus) → ℝ))
      (leftValue rightValue : (degree : Fin (D + 1)) →
        ((Fin (degree : ℕ) × Bool → Locus) → ℝ)),
      (∀ algorithm degree (permutation : Equiv.Perm Locus) monomial,
        coefficient algorithm degree (permutation ∘ monomial) =
          coefficient algorithm degree monomial) →
      Blindness.TrafficInvariantSeparation.degreeAtMostCanonicalTrafficProfile leftValue =
        Blindness.TrafficInvariantSeparation.degreeAtMostCanonicalTrafficProfile rightValue →
      ∀ bayesLeft bayesRight : ℝ,
        (∀ algorithm,
          bayesRight ≤ ∑ degree : Fin (D + 1),
            ∑ monomial,
              coefficient algorithm degree monomial * rightValue degree monomial) →
        ∀ algorithm,
          bayesRight - bayesLeft ≤
            (∑ degree : Fin (D + 1),
              ∑ monomial,
                coefficient algorithm degree monomial * leftValue degree monomial) -
              bayesLeft
  /-- A finite tilt net controls the complete Lipschitz genomic pressure
  profile with explicit error `2Kρ + ε`. -/
  genomicPressureProfilesHaveQuantitativeTiltNetControl :
    ∀ (Parameter : Type) [PseudoMetricSpace Parameter]
      (K : NNReal) (left right : Parameter → ℝ),
      LipschitzWith K left → LipschitzWith K right →
      ∀ (net : Set Parameter) (radius coordinateError : ℝ),
        (∀ parameter, ∃ representative ∈ net,
          dist parameter representative ≤ radius) →
        (∀ representative ∈ net,
          dist (left representative) (right representative) ≤ coordinateError) →
          ∀ parameter,
            dist (left parameter) (right parameter) ≤
              2 * (K : ℝ) * radius + coordinateError
  /-- Agreement on a dense rational tilt family determines the full uniformly
  Lipschitz genomic pressure profile. -/
  genomicDenseTiltCoordinatesDeterminePressureProfile :
    ∀ (Parameter : Type) [PseudoMetricSpace Parameter]
      (K : NNReal) (left right : Parameter → ℝ),
      LipschitzWith K left → LipschitzWith K right →
      ∀ parameters : Set Parameter, Dense parameters →
        Set.EqOn left right parameters → left = right
  /-- Pointwise convergence on a dense rational tilt family extends to every
  tilt for a uniformly Lipschitz genomic pressure sequence and limit. -/
  genomicDenseTiltConvergenceExtendsGlobally :
    ∀ (Parameter : Type) [PseudoMetricSpace Parameter]
      (K : NNReal) (profiles : ℕ → Parameter → ℝ) (limit : Parameter → ℝ),
      (∀ index, LipschitzWith K (profiles index)) →
      LipschitzWith K limit →
      ∀ parameters : Set Parameter, Dense parameters →
        (∀ parameter ∈ parameters,
          Filter.Tendsto (fun index ↦ profiles index parameter)
            Filter.atTop (nhds (limit parameter))) →
          ∀ parameter,
            Filter.Tendsto (fun index ↦ profiles index parameter)
              Filter.atTop (nhds (limit parameter))
  /-- On compact tilt domains, the same dense-family hypotheses yield uniform
  convergence of the complete genomic pressure profile. -/
  genomicDenseTiltConvergenceIsUniformOnCompactDomains :
    ∀ (Parameter : Type) [PseudoMetricSpace Parameter] [CompactSpace Parameter]
      (K : NNReal) (profiles : ℕ → Parameter → ℝ) (limit : Parameter → ℝ),
      (∀ index, LipschitzWith K (profiles index)) →
      LipschitzWith K limit →
      ∀ parameters : Set Parameter, Dense parameters →
        (∀ parameter ∈ parameters,
          Filter.Tendsto (fun index ↦ profiles index parameter)
            Filter.atTop (nhds (limit parameter))) →
          TendstoUniformly profiles limit Filter.atTop
  /-- Uniformly bounded, common-Lipschitz genomic pressure functions form a
  compact family on every compact tilt domain. -/
  genomicBoundedLipschitzPressureProfilesAreCompact :
    ∀ (Parameter : Type) [PseudoMetricSpace Parameter] [CompactSpace Parameter]
      (K : NNReal) (bound : ℝ),
      IsCompact (boundedLipschitzPressureFamily
        (Parameter := Parameter) K bound)
  /-- Every bounded equi-Lipschitz genomic pressure sequence has a uniformly
  convergent subsequence whose limit remains bounded and equi-Lipschitz. -/
  genomicBoundedLipschitzPressureProfilesHaveCompactSubsequences :
    ∀ (Parameter : Type) [PseudoMetricSpace Parameter] [CompactSpace Parameter]
      (K : NNReal) (bound : ℝ)
      (profiles : ℕ → BoundedContinuousFunction Parameter ℝ),
      (∀ index, profiles index ∈ boundedLipschitzPressureFamily K bound) →
        ∃ limit ∈ boundedLipschitzPressureFamily (Parameter := Parameter) K bound,
          ∃ subsequence : ℕ → ℕ,
            StrictMono subsequence ∧
              Filter.Tendsto (profiles ∘ subsequence) Filter.atTop (nhds limit)
  /-- Every uniformly bounded countable exponential/LD profile has one common
  coordinatewise-convergent subsequence. -/
  genomicExponentialProfileIsSequentiallyCompact :
    ∀ (bound : ℝ) (profiles : ℕ → Blindness.TrafficInvariantSeparation.BoundedExponentialProfile bound),
      ∃ limit : Blindness.TrafficInvariantSeparation.BoundedExponentialProfile bound, ∃ subsequence : ℕ → ℕ,
        StrictMono subsequence ∧
          ∀ coordinate : ℕ,
            Filter.Tendsto (fun n ↦ profiles (subsequence n) coordinate)
              Filter.atTop (nhds (limit coordinate))
  /-- The explicit weighted exponential-profile formula satisfies the metric
  laws on bounded genomic pressure profiles. -/
  genomicExponentialProfileDistanceSatisfiesMetricLaws :
    ∀ (bound : ℝ) (left middle right : Blindness.TrafficInvariantSeparation.BoundedExponentialProfile bound),
      0 ≤ exponentialProfileDistance left right ∧
        exponentialProfileDistance left right = exponentialProfileDistance right left ∧
        exponentialProfileDistance left right ≤
        exponentialProfileDistance left middle + exponentialProfileDistance middle right ∧
        (exponentialProfileDistance left right = 0 ↔ left = right)
  /-- The explicit genomic right-profile carrier has the installed weighted
  metric and is compact in its standard topology. -/
  genomicExponentialProfilePointIsCompactMetricSpace :
    ∀ bound : ℝ,
      IsCompact (Set.univ : Set (Blindness.TrafficInvariantSeparation.ExponentialProfilePoint bound))
  /-- Metric convergence of bundled genomic profiles is coordinatewise
  convergence of every enumerated pressure. -/
  genomicExponentialProfilePointConvergenceIsCoordinatewise :
    ∀ (bound : ℝ) (profiles : ℕ → Blindness.TrafficInvariantSeparation.ExponentialProfilePoint bound)
      (limit : Blindness.TrafficInvariantSeparation.ExponentialProfilePoint bound),
      Filter.Tendsto profiles Filter.atTop (nhds limit) ↔
        ∀ coordinate : ℕ,
          Filter.Tendsto (fun n ↦ profiles n coordinate)
            Filter.atTop (nhds (limit coordinate))
  /-- Convergence in the explicit genomic right-profile distance is equivalent
  to convergence of every enumerated pressure coordinate. -/
  genomicExponentialProfileDistanceCharacterizesConvergence :
    ∀ (bound : ℝ) (profiles : ℕ → Blindness.TrafficInvariantSeparation.BoundedExponentialProfile bound)
      (limit : Blindness.TrafficInvariantSeparation.BoundedExponentialProfile bound),
      Filter.Tendsto (fun n ↦ exponentialProfileDistance (profiles n) limit)
          Filter.atTop (nhds 0) ↔
        ∀ coordinate : ℕ,
          Filter.Tendsto (fun n ↦ profiles n coordinate)
            Filter.atTop (nhds (limit coordinate))
  /-- A finite prefix of genomic pressure coordinates controls the complete
  right-profile distance by the exact remaining geometric tail. -/
  genomicExponentialProfileHasFiniteCoordinateApproximation :
    ∀ (bound : ℝ) (left right : Blindness.TrafficInvariantSeparation.BoundedExponentialProfile bound)
      (prefixLength : ℕ),
      (∀ coordinate < prefixLength, left coordinate = right coordinate) →
        exponentialProfileDistance left right ≤ 2 ∧
          exponentialProfileDistance left right ≤
            2 * (1 / 2 : ℝ) ^ prefixLength
  /-- Every bounded sequence has a subsequence converging in the explicit
  weighted exponential-profile distance. -/
  genomicExponentialProfileIsCompactInExplicitDistance :
    ∀ (bound : ℝ) (profiles : ℕ → Blindness.TrafficInvariantSeparation.BoundedExponentialProfile bound),
      ∃ limit : Blindness.TrafficInvariantSeparation.BoundedExponentialProfile bound, ∃ subsequence : ℕ → ℕ,
        StrictMono subsequence ∧
          Filter.Tendsto
            (fun n ↦ exponentialProfileDistance (profiles (subsequence n)) limit)
            Filter.atTop (nhds 0)
  /-- Equal unconditioned Bolthausen--Sznitman genealogy does not determine the conditioned
  family: the logarithmic and linear response marks already separate at three lineages. -/
  speedConditionedGenealogyRetainsResponseMark :
    Blindness.MarkedBreakout.linearDisplacementTripleRate 1 ≠ Blindness.speedTiltBetaMergerRate 1 3 3
  /-- The cubic genealogical clock belongs to pioneer susceptibility, not coalescent theory. -/
  pioneerSusceptibilitySetsClock :
    ∀ width : ℝ, Blindness.MarkedBreakout.genealogicalTimescale width 3 = width ^ 3
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
    Portability.calibrationDriftDefectSq binaryStateWeight binaryDynamicsPosterior
      binaryConditionalContextMatch = 1 / 4
  /-- Removing a dynamics from posterior support seals the defect without making the two
  conditional fields equal. -/
  zeroSupportSealsConditionalDrift :
    Portability.calibrationDriftDefectSq binaryStateWeight persistentOnlyDynamicsPosterior
      binaryConditionalContextMatch = 0
  /-- Every finite uniform correction through the pooled observation erases the biological
  contrast, independently of dictionary order. -/
  uniformCorrectionCannotRecoverContrast :
    ∀ (k : ℕ) (C : (Bool → ℝ) →ₗ[ℝ] (Bool → ℝ)),
      C ∈ Portability.UniformCorrectionFamily dynamicsPoolingObservation k → C dynamicsContrast = 0
  /-- Target-dependent coefficients cannot recover a direction already annihilated by the
  observation. -/
  adaptiveCorrectionCannotRecoverContrast :
    ∀ (k : ℕ) (T : Fin k → ℝ →ₗ[ℝ] (Bool → ℝ)),
      Portability.adaptiveCorrectionSet dynamicsPoolingObservation T dynamicsContrast = {0}
  /-- The same one-term adaptive dictionary is exact on the observable common mode, exposing the
  thin-class phase change rather than a blanket failure of adaptivity. -/
  observableModeIsAdaptivelyExact :
    dynamicsCommonMode ∈ Portability.adaptiveCorrectionSet dynamicsPoolingObservation
      (fun _ : Fin 1 ↦ dynamicsBroadcast) dynamicsCommonMode
  /-- The correction-null contrast and the calibration drift are the same biological direction,
  with the normalization made explicit. -/
  correctionContrastIsCalibrationDrift :
    ∀ persists y, dynamicsContrast persists =
      2 * Portability.posteriorDrift binaryDynamicsPosterior binaryConditionalContextMatch persists y

/-- **The finite obstruction theorem.**  Dynamics, dependence, value allocation, and
local operator geometry each carry information invisible to a tempting scalar reduction.
The witnesses coexist; none is a fallback explanation for another. -/
theorem dynamicsContrast_obstructions : DynamicsObstructions := by
  refine
    { targetOnlyBlind := targetOnlyPerformance_blind_to_binary_dynamics
      crossStateSeparates := ?_
      marginalsLoseDependence := Spectral.coordinateMarginalsDoNotDetermineJointLaw
      commutingAllocationConflict := Spectral.commutingConflict_myopic_ne_transport
      sharedGeometryNotFree := Spectral.tridiagonalABAB_pathExpression_pos 0 0 1 1 (by norm_num)
        (by norm_num)
      isospectralLDLosesOrientation :=
        ⟨Blindness.localizedCovarianceBlock_isospectral_rotatedCovarianceBlock (3 / 2), by
          intro heq
          have hzero :
              Blindness.blockEntryCubeMean (Blindness.localizedCovarianceBlock (3 / 2)) -
                  Blindness.blockEntryCubeMean (Blindness.rotatedCovarianceBlock (3 / 2)) = 0 := by
            rw [heq, sub_self]
          rw [Blindness.midpoint_blockEntryCubeMean_separation] at hzero
          norm_num at hzero⟩
      skewedLDChangesLowSNRCoefficient :=
        Blindness.sparsePrior_lowSNRThirdCoefficient_rotated_sub_localized
      symmetricSparseLDLosesOrientation :=
        ⟨Blindness.localizedCovarianceBlock_isospectral_rotatedCovarianceBlock (3 / 2),
          Blindness.midpoint_blockEntryFourthMean_ne⟩
      symmetricLDChangesLowSNRCoefficient :=
        Blindness.rademacher_fullLowSNRFourthCoefficient_rotated_sub_localized
      environmentMixtureClosesPopulationGap :=
        ancestryMixture_pure_gapped_balanced_ungapped
      sameSignEnvironmentPoolingDoesNotMoveGapParameter :=
        sameSignAncestryPooling_preservesActiveCorrelation
      fiveEpochDemographyIsSeverelyIllConditioned :=
        fiveEpochDemography_sampleRateExponent
      kingmanSpectrumHasIdentifiabilityBoundary :=
        kingmanSpectrum_identifiabilityBoundary
      speedConditionedGenealogyNeedsThreeLineages :=
        speedConditionedGenealogy_pairBlind_tripleRecovers
      markedSuccessfulFamilyMeasureDeterminesGenealogy :=
        markedSuccessfulFamilyMeasure_determinesGenealogy
      markedMassPartitionMeasureDeterminesXi :=
        markedMassPartitionMeasure_determinesXi
      frontTrajectoryDoesNotDetermineXi :=
        sweepTrajectory_does_not_determine_genealogy
      twoColourPioneerResponseIsExact :=
        twoColourPioneerResponse_exact
      branchingRandomWalkBoundaryTransformIsCritical :=
        branchingRandomWalkBoundaryTransform_isCritical
      selectedDerivativeFluxControlsBreakouts :=
        fun _Pioneer _ _ tailConstant threshold blockScale fluxConstant weight htail
          hthreshold hweight hflux ↦
            selectedDerivativeFlux_controlsBreakouts
              tailConstant threshold blockScale fluxConstant weight
              htail hthreshold hweight hflux
      selectedPioneerFluxFollowsFromNegligiblePruning :=
        selectedPioneerFlux_follows_from_fullTreeFlux_and_negligiblePruning
      uniquePioneerCommonProfileDeterminesMarkedResponse :=
        uniquePioneer_commonProfile_markedResponse
      selectedGenealogyHasMuntzRateDichotomy :=
        selectedGenealogy_muntzRateDichotomy
      genomicAlgorithmicRiskSignatureIsCoarsest :=
        fun _Algorithm _Design _Model _Loss risk ↦
          genomicAlgorithmicRiskSignature_isCoarsestSufficientInvariant risk
      genomicRankOneTrafficExpansionFollowsFromHandshake :=
        fun _Term _ coefficient hasOddDegree vertices edges degree hpositive heven hhandshake ↦
          genomicRankOneTrafficCorrection_vanishes_of_positiveEvenDegreeData
            coefficient hasOddDegree vertices edges degree hpositive heven hhandshake
      positiveLDBalancedRankOneCovarianceHasFullWitness :=
        fun _Term _ coefficient hasOddDegree vertices edges hconnected baseline
          spikeStrength temperature hbaseline hspike hcritical ↦
            positiveLDBalancedRankOneCovariance_fullWitness coefficient hasOddDegree
              vertices edges hconnected baseline spikeStrength temperature hbaseline
              hspike hcritical
      rareLDSubspaceEvadesFixedTrafficAtLogRuntime :=
        rareLDSubspace_fixedTrafficInvisible_logRuntimeVisible
      rareLDSubspaceEvadesLimitingTrafficAtDegreeOne :=
        rareLDSubspace_limitingTrafficInsufficientForDegreeOne
      rareLDSubspaceConcreteGFOMEvadesFixedTrafficAtLogRuntime :=
        Blindness.TrafficInvariantSeparation.concreteGFOM_fixedTrafficInvisible_logRuntimeVisible
      genomicBulkSpectralLawDoesNotDetermineExtremalSpectrumOrSDP :=
        genomicBulkSpectralLaw_invisible_extremalSpectrumAndSDP_visible
      positiveLDSpikeFixedTrafficInvisibleVariationalPressureVisible :=
        fun _Term _ coefficient hasOddDegree vertices edges hconnected tlam hcritical ↦
          positiveLDSpike_fixedTrafficInvisible_variationalPressureVisible
            coefficient hasOddDegree vertices edges hconnected tlam hcritical
      positiveLDSpikeFixedTrafficInvisibleFinitePressureVisible :=
        fun _Term _ coefficient hasOddDegree vertices edges hconnected tlam hcritical ↦
          positiveLDSpike_fixedTrafficInvisible_finitePressureVisible
            coefficient hasOddDegree vertices edges hconnected tlam hcritical
      genomicFiniteCWPressureDominatesVariationalObjective :=
        genomicFiniteCWPressure_dominatesVariationalObjective
      genomicFiniteCWTypeMassLeOneOfSubcritical :=
        genomicFiniteCWTypeMass_le_one_of_subcritical
      genomicFiniteCWPressureHasExactCriticalPoint :=
        genomicFiniteCWPressure_exactCriticalPoint
      genomicFiniteCWPressureConvergesToVariational :=
        genomicFiniteCWPressure_convergesToVariational
      genomicFiniteCWPressureConvergesUniformlyOnNonnegative :=
        genomicFiniteCWPressure_convergesUniformlyOnNonnegative
      genomicFiniteCWPressureIsHalfLipschitz :=
        genomicFiniteCWPressure_isHalfLipschitz
      genomicFiniteCWPressureIsMonotone :=
        genomicFiniteCWPressure_isMonotone
      positiveLDSpikeFinitePressureExceedsBaseline :=
        positiveLDSpike_finitePressureExceedsBaseline
      positiveLDSpikePressureDifferenceHasExactCriticalPoint :=
        positiveLDSpike_pressureDifference_exactCriticalPoint
      positiveLDSpikePressureConvergesToVariational :=
        positiveLDSpike_pressure_convergesToVariational
      positiveLDSpikePressureConvergesUniformlyOnNonnegativeStrength :=
        positiveLDSpike_pressure_convergesUniformlyOnNonnegativeStrength
      positiveLDSpikeRefutesTrafficAndGroundStateDichotomies :=
        fun _Term _Genotype _ coefficient hasOddDegree vertices edges hconnected alignment
          orthogonal aligned baseline spikeStrength population temperature hspike hpopulation
          horthogonal haligned hcritical ↦
            positiveLDSpike_refutesTrafficAndGroundStateDichotomies
              coefficient hasOddDegree vertices edges hconnected alignment orthogonal aligned
              baseline spikeStrength population temperature hspike hpopulation horthogonal
              haligned hcritical
      positiveLDSpikeGroundStateDoesNotFixPressure :=
        positiveLDSpike_groundStateDoesNotFixPressure
      ldOverlapPressureHasExactCriticalPoint :=
        ldOverlapPressure_exactCriticalPoint
      ldVariationalPressureGapHasExactCriticalPoint :=
        ldVariationalPressureGap_exactCriticalPoint
      ldVariationalPressureGapHasGlobalRegularity :=
        ldVariationalPressureGap_globalRegularity
      matchedBayesRandomDesignAsymmetricReduction :=
        matchedBayes_randomDesignGap_fromScalarGap_asymmetric
      matchedBayesRandomDesignReduction :=
        matchedBayes_randomDesignGap_from_scalarGap
      matchedBayesRandomDesignEventuallySeparatesWithAsymmetricErrors :=
        fun _Index regime scalarLeft scalarRight delta randomLeft randomRight
          leftError rightError hleft hright hgap hpositive hleftVanishing
          hrightVanishing ↦
            matchedBayes_randomDesignEventuallySeparates_fromAsymmetricErrors
              regime scalarLeft scalarRight delta randomLeft randomRight leftError
              rightError hleft hright hgap hpositive hleftVanishing hrightVanishing
      matchedBayesRandomDesignEventuallySeparates :=
        fun _Index regime scalarLeft scalarRight delta randomLeft randomRight
          comparisonError hleft hright hgap hpositive herrorVanishing ↦
            matchedBayes_randomDesignEventuallySeparates_fromScalarGap
              regime scalarLeft scalarRight delta randomLeft randomRight
              comparisonError hleft hright hgap hpositive herrorVanishing
      matchedBayesRandomDesignSeparatesAtLargeAspect :=
        matchedBayes_randomDesignSeparates_ofLargeAspect
      matchedBayesRandomDesignEventuallySeparatesAtDivergingAspect :=
        fun _Index regime scalarLeft scalarRight delta constant aspectRatio
          randomLeft randomRight hleft hright hgap hpositive haspectRatio ↦
            matchedBayes_randomDesignEventuallySeparates_ofAspectAtTop regime
              scalarLeft scalarRight delta constant aspectRatio randomLeft randomRight
              hleft hright hgap hpositive haspectRatio
      matchedBayesAspectWishartRatioBridge :=
        fun _Index regime aspectRatio constant ↦
          matchedBayes_aspectWishartRatioBridge regime aspectRatio constant
      matchedBayesWishartInformationErrorVanishes :=
        fun _Index regime informationError adjustedRatio constant hratio herror ↦
          matchedBayes_wishartInformationErrorVanishes regime informationError
            adjustedRatio constant hratio herror
      matchedBayesRandomDesignEventuallySeparatesAtAsymmetricWishartRatios :=
        fun _Index regime scalarLeft scalarRight delta leftConstant rightConstant
          leftRatio rightRatio randomLeft randomRight hleft hright hgap hpositive
          hleftRatio hrightRatio ↦
            matchedBayes_randomDesignEventuallySeparates_ofAsymmetricWishartRatios
              regime scalarLeft scalarRight delta leftConstant rightConstant leftRatio
              rightRatio randomLeft randomRight hleft hright hgap hpositive hleftRatio
              hrightRatio
      matchedBayesRandomDesignEventuallySeparatesAtWishartRatio :=
        fun _Index regime scalarLeft scalarRight delta constant adjustedRatio
          randomLeft randomRight hleft hright hgap hpositive hratio ↦
            matchedBayes_randomDesignEventuallySeparates_ofWishartRatio regime
              scalarLeft scalarRight delta constant adjustedRatio randomLeft randomRight
              hleft hright hgap hpositive hratio
      matchedBayesSingularSpectrumHasNormalizedNuclearBound :=
        fun _Coordinate _ _ spectrum hdimension ↦
          spectrum.normalizedNuclearDistance_le_operatorBound_mul_rankFraction hdimension
      matchedBayesCertifiedRankOnePerturbationIsAsymptoticallyInvisible :=
        matchedBayes_certifiedRankOnePerturbation_isAsymptoticallyInvisible
      matchedBayesInformationPathHasNuclearBound :=
        matchedBayes_informationPath_nuclearBound
      matchedBayesHasWishartFrobeniusComparisonRate :=
        matchedBayes_wishartFrobeniusComparisonRate
      matchedBayesHasWishartMomentIdentityComparisonRate :=
        matchedBayes_wishartMomentIdentityComparisonRate
      matchedBayesCertifiedSublinearRankIsInvisibleUnderVarianceBound :=
        fun _Index regime certificate varianceBound operatorBound rankFraction
          hvarianceBound hrankVanishing hnuclearRank ↦
            matchedBayes_certifiedSublinearRank_isInvisible_ofVarianceBound
              regime certificate varianceBound operatorBound rankFraction
              hvarianceBound hrankVanishing hnuclearRank
      matchedBayesCertifiedSublinearRankIsInvisible :=
        fun _Index regime certificate operatorBound rankFraction hvariance
          hrankVanishing hnuclearRank ↦
            matchedBayes_certifiedSublinearRank_isInvisible regime certificate
              operatorBound rankFraction hvariance hrankVanishing hnuclearRank
      matchedBayesSublinearRankPerturbationsAreInvisible :=
        matchedBayes_sublinearRankPerturbation_isAsymptoticallyInvisible
      matchedBayesPositiveGapForcesExtensiveRank :=
        matchedBayes_positiveGap_forcesExtensiveRank
      matchedBayesCertifiedPositiveGapForcesExtensiveRank :=
        matchedBayes_certifiedPositiveGap_forcesExtensiveRank
      matchedBayesCertifiedPersistentGapRequiresExtensiveRank :=
        fun _Index regime _hregime certificate varianceBound operatorBound delta rankFraction
          hvariancePositive hoperator hdelta hvarianceBound hnuclearRank hgap ↦
            matchedBayes_certifiedPersistentGap_requiresExtensiveRank regime
              certificate varianceBound operatorBound delta rankFraction hvariancePositive
              hoperator hdelta hvarianceBound hnuclearRank hgap
      matchedBayesPersistentGapRequiresExtensiveRank :=
        fun _Index regime _hregime densityGap rankFraction constant delta hconstant hdelta
          hgap hnuclear ↦
            matchedBayes_persistentGap_requiresExtensiveRank regime densityGap
              rankFraction constant delta hconstant hdelta hgap hnuclear
      degreeLimitedGenomicRiskHasFullGapHardness :=
        fun _Algorithm _D risk left right htraffic bayesLeft bayesRight hoptimal algorithm ↦
          degreeLimitedGenomicRisk_fullGapHardness risk left right htraffic bayesLeft bayesRight
            hoptimal algorithm
      stableDegreeLimitedGenomicRiskHasQuantitativeTrafficBound :=
        fun _D risk left right epsilon hcoordinate ↦
          stableDegreeLimitedGenomicRisk_quantitativeTrafficBound
            risk left right epsilon hcoordinate
      stableDegreeLimitedGenomicRiskConvergesOfBoundedCoefficientMass :=
        fun _D risk left right discrepancy coefficientBound hdiscrepancy
          hcoefficient hdiscrepancyNonneg ↦
            stableDegreeLimitedGenomicRisk_convergesOfBoundedCoefficientMass
              risk left right discrepancy coefficientBound hdiscrepancy
              hcoefficient hdiscrepancyNonneg
      highTemperatureGenomicTrafficDeterminesCertifiedPressure :=
        highTemperatureTrafficLimitsAgree_ofGeometricCertificate
      genomicLDTrafficHierarchyIsStrictAtEveryDegree :=
        genomicLDTrafficHierarchy_strictAtEveryDegree
      genomicLDTrafficHasCommonBlindPairAtEveryDegree :=
        genomicLDTrafficBlindPair_existsAtEveryDegree
      permutationInvariantGenomicPolynomialFactorsThroughLDGraphs :=
        fun _Slot _Locus _Graph _ _ _ _ _ shape coefficient value hshape hinvariant ↦
          permutationInvariantGenomicPolynomial_factorsThroughLDGraphs
            shape coefficient value hshape hinvariant
      permutationInvariantGenomicPolynomialFactorsThroughCanonicalLDGraphs :=
        fun _Slot _Locus _ _ _ coefficient value hinvariant ↦
          permutationInvariantGenomicPolynomial_factorsThroughCanonicalLDGraphs
            coefficient value hinvariant
      permutationEquivariantGenomicPolynomialFactorsThroughRootedLDGraphs :=
        fun _Slot _Locus _ _ _ coefficient value hinvariant ↦
          permutationEquivariantGenomicPolynomial_factorsThroughRootedLDGraphs
            coefficient value hinvariant
      degreeLimitedGenomicPolynomialFactorsThroughCanonicalLDGraphs :=
        fun _D _Locus _ coefficient value hinvariant ↦
          degreeLimitedGenomicPolynomial_factorsThroughCanonicalLDGraphs
            coefficient value hinvariant
      degreeLimitedGenomicEquivariantPolynomialFactorsThroughRootedLDGraphs :=
        fun _D _Locus _ coefficient value hinvariant ↦
          degreeLimitedGenomicEquivariantPolynomial_factorsThroughRootedLDGraphs
            coefficient value hinvariant
      degreeLimitedGenomicPolynomialIsDeterminedByCanonicalLDProfile :=
        fun _D _Locus _ coefficient leftValue rightValue hinvariant htraffic ↦
          degreeLimitedGenomicPolynomial_eq_ofCanonicalLDProfileEq
            coefficient leftValue rightValue hinvariant htraffic
      degreeLimitedGenomicEquivariantPolynomialIsDeterminedByRootedLDProfile :=
        fun _D _Locus _ coefficient leftValue rightValue hinvariant htraffic ↦
          degreeLimitedGenomicEquivariantPolynomial_eq_ofRootedLDProfileEq
            coefficient leftValue rightValue hinvariant htraffic
      degreeLimitedGenomicPolynomialHasDirectFullGapHardness :=
        fun _Algorithm _D _Locus _ coefficient leftValue rightValue hinvariant
          htraffic bayesLeft bayesRight hoptimalRight algorithm ↦
            degreeLimitedGenomicPolynomial_fullGapHardness_fromCanonicalLDProfile
              coefficient leftValue rightValue hinvariant htraffic bayesLeft bayesRight
              hoptimalRight algorithm
      genomicPressureProfilesHaveQuantitativeTiltNetControl :=
        fun _Parameter _ K left right hleft hright net radius coordinateError hnet hagrees ↦
          genomicPressureProfiles_dist_le_of_tiltNet
            K left right hleft hright net radius coordinateError hnet hagrees
      genomicDenseTiltCoordinatesDeterminePressureProfile :=
        fun _Parameter _ K left right hleft hright parameters hdense hagrees ↦
          genomicPressureProfiles_eq_of_eqOn_denseTilts
            K left right hleft hright parameters hdense hagrees
      genomicDenseTiltConvergenceExtendsGlobally :=
        fun _Parameter _ K profiles limit hprofiles hlimit parameters hdense hconverges ↦
          Blindness.TrafficInvariantSeparation.lipschitzPressureProfiles_tendsto_of_tendstoOn_dense
            K profiles limit hprofiles hlimit parameters hdense hconverges
      genomicDenseTiltConvergenceIsUniformOnCompactDomains :=
        fun _Parameter _ _ K profiles limit hprofiles hlimit parameters hdense hconverges ↦
          Blindness.TrafficInvariantSeparation.lipschitzPressureProfiles_tendstoUniformly_of_tendstoOn_dense
            K profiles limit hprofiles hlimit parameters hdense hconverges
      genomicBoundedLipschitzPressureProfilesAreCompact :=
        fun _Parameter _ _ K bound ↦
          genomicBoundedLipschitzPressureFamily_isCompact K bound
      genomicBoundedLipschitzPressureProfilesHaveCompactSubsequences :=
        fun _Parameter _ _ K bound profiles hprofiles ↦
          genomicBoundedLipschitzPressureFamily_hasUniformlyConvergentSubsequence
            K bound profiles hprofiles
      genomicExponentialProfileIsSequentiallyCompact :=
        genomicExponentialProfile_hasCommonCoordinatewiseSubsequence
      genomicExponentialProfileDistanceSatisfiesMetricLaws :=
        fun _bound left middle right ↦
          genomicExponentialProfileDistance_metricLaws left middle right
      genomicExponentialProfilePointIsCompactMetricSpace :=
        genomicExponentialProfilePoint_isCompactMetricSpace
      genomicExponentialProfilePointConvergenceIsCoordinatewise :=
        fun _bound _profiles _limit ↦
          genomicExponentialProfilePoint_converges_iff_coordinatewise
      genomicExponentialProfileDistanceCharacterizesConvergence :=
        fun _bound _profiles _limit ↦
          genomicExponentialProfileDistance_converges_iff_coordinatewise
      genomicExponentialProfileHasFiniteCoordinateApproximation :=
        fun _bound left right prefixLength hprefix ↦
          genomicExponentialProfileDistance_finitePrefixControl
            left right prefixLength hprefix
      genomicExponentialProfileIsCompactInExplicitDistance :=
        genomicExponentialProfile_compactInExplicitDistance
      speedConditionedGenealogyRetainsResponseMark :=
        speedConditionedGenealogy_chart_not_universal
      pioneerSusceptibilitySetsClock :=
        pioneerSusceptibility_setsGenealogicalClock
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


end Descent.Conditionals
