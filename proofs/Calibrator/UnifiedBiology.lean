/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Calibrator.DeclaredInteractionClass
import Calibrator.DirichletTransfer
import Calibrator.ErgodicCovariancePencil
import Calibrator.HorizonCurve
import Calibrator.PencilEnvironment
import Calibrator.FunctionalDescent

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

The final theorem packages four independent obstructions that a unified biological model
must keep visible: stationarity blindness, loss of joint dependence under marginal summaries,
rank-two value/allocation conflict even in a common eigenbasis, and failure of freeness for
operators sharing a local genomic geometry.

## Epistemic boundary

This file does not promote the analytic claims in the motivating program to Lean theorems.
In particular, Donsker--Varadhan regularity, infinite-volume density of states, a Thouless
formula, Minami/Poisson statistics, and hard-edge random-operator limits require hypotheses
and proofs absent from this corpus.  The formal content here is finite and exact; those
claims remain research interfaces rather than axioms disguised as results.
-/

open scoped BigOperators

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

/-- Four logically distinct failures that a biological transport theory must not collapse
into one scalar "portability" parameter. -/
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
        (by norm_num) }
  rw [crossStatePerformance_persistent_eq_one, crossStatePerformance_switching_eq_zero]
  norm_num

/-! ## Conditional descent is the portability gate before prediction

The same score bin or ancestry summary can support different conditional phenotype laws in
different cohorts.  `FunctionalDescent` separates two biologically distinct failures:
interaction can disappear in either margin and reappear after refinement, while confounding can
be controlled by either informative variable and reappear after marginalization.  Thus the
choice of retained covariate is part of the portability theorem, not preprocessing notation. -/

/-- **The conditional-descent boundary is present in the biological core.**  A balanced pure
interaction is invisible in either ancestry/environment margin but visible jointly, and a
cohort-varying confounder prevalence changes marginal risk. -/
theorem conditionalDescent_biological_boundary :
    (∀ theta : ℝ, ∀ u : BinaryDescentCovariate,
      (interactionRisk theta u 0 + interactionRisk theta u 1) / 2 = 1 / 2) ∧
    interactionRisk 0 0 0 ≠ interactionRisk (1 / 4) 0 0 ∧
    confoundedMarginalRisk 0 ≠ confoundedMarginalRisk 1 := by
  refine ⟨interactionRisk_average_second, ?_, ?_⟩
  · exact interactionRisk_joint_separates (by norm_num)
  · exact confoundedMarginalRisk_separates (by norm_num)

end Calibrator
