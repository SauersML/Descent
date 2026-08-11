/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Core.Ratios
import Mathlib.Tactic

assert_below Descent.Meta Descent.Foundations Descent.Coalescent Descent.Pangenome Descent.PopGen
assert_below Descent.Spectral Descent.Blindness Descent.Conditionals Descent.Portability
assert_below Descent.Decision Descent.Program

namespace Descent.Core

/-!
# Core identification and sharp-fiber laws

This file contains the logic shared by observational impossibility results and by positive
partial-identification results.  It asserts nothing about a biological model.  A subsystem
supplies an observation, an exact target law, and—when finite approximation is claimed—sharp
attained endpoint laws.  Core then says exactly what those data imply.

The separation is load-bearing.  `SharpFiberEnvelope` is not evidence that a particular
pipeline has a nontrivial fiber, and it is not a license to invent endpoint values.  Its fields
require both global bounds and compatible completions attaining them.  Constructing those
fields for a scientific model is the scientific theorem.
-/

/-! ## Exact identification -/

/-- The observation identifies the target when equal observations force equal targets. -/
def IdentifiedBy {Parameter Data Target : Type*}
    (observe : Parameter → Data) (target : Parameter → Target) : Prop :=
  ∀ first second : Parameter, observe first = observe second → target first = target second

/-- A target explicitly computed from the observation is identified by it. -/
theorem identifiedBy_of_factors {Parameter Data Target : Type*}
    (observe : Parameter → Data) (readout : Data → Target) :
    IdentifiedBy observe (fun parameter ↦ readout (observe parameter)) :=
  fun _first _second hobserve ↦ congrArg readout hobserve

/-- Identification is exactly the existence of a readout on the range of the observation.
The base parameter supplies an arbitrary value off that range, where no claim is made. -/
theorem IdentifiedBy.exists_readout {Parameter Data Target : Type*}
    {observe : Parameter → Data} {target : Parameter → Target} (base : Parameter)
    (hidentified : IdentifiedBy observe target) :
    ∃ readout : Data → Target, ∀ parameter : Parameter,
      target parameter = readout (observe parameter) := by
  classical
  refine ⟨fun data ↦ if hdata : ∃ parameter : Parameter, observe parameter = data then
    target hdata.choose else target base, ?_⟩
  intro parameter
  have hdata : ∃ preimage : Parameter, observe preimage = observe parameter := ⟨parameter, rfl⟩
  show target parameter =
    if hexists : ∃ preimage : Parameter, observe preimage = observe parameter then
      target hexists.choose else target base
  rw [dif_pos hdata]
  exact hidentified parameter hdata.choose hdata.choose_spec.symm

/-! ## Completion laws -/

/-- An exact coordinate family depending on a visible input and a completion.  The value type
is generic so a partial scientific output can use `Option ℝ` without encoding undefined as a
number.  Whether a simulator's internal random objects belong in `Completion` or must first be
integrated out is part of the subsystem semantics, not something this structure decides. -/
structure CompletionLaw (Input Completion Coordinate Value : Type*) where
  value : Input → Completion → Coordinate → Value

/-- A single visible-input readout that is exact at every completion and coordinate. -/
def HasExactReadout {Input Completion Coordinate Value : Type*}
    (law : CompletionLaw Input Completion Coordinate Value) : Prop :=
  ∃ readout : Input → Coordinate → Value,
    ∀ input completion coordinate,
      law.value input completion coordinate = readout input coordinate

/-- The completion law has an exact readout exactly when the visible projection identifies
its complete coordinate family. -/
theorem hasExactReadout_iff_identifiedBy
    {Input Completion Coordinate Value : Type*}
    (law : CompletionLaw Input Completion Coordinate Value)
    (baseInput : Input) (baseCompletion : Completion) :
    HasExactReadout law ↔
      IdentifiedBy
        (fun completed : Input × Completion ↦ completed.1)
        (fun completed ↦ law.value completed.1 completed.2) := by
  constructor
  · rintro ⟨readout, hreadout⟩ first second hvisible
    have hvis : first.1 = second.1 := hvisible
    funext coordinate
    show law.value first.1 first.2 coordinate = law.value second.1 second.2 coordinate
    rw [hreadout first.1 first.2 coordinate, hreadout second.1 second.2 coordinate, hvis]
  · intro hidentified
    obtain ⟨readout, hreadout⟩ :=
      hidentified.exists_readout (baseInput, baseCompletion)
    exact ⟨readout, fun input completion coordinate ↦
      congrFun (hreadout (input, completion)) coordinate⟩

/-- A coordinate is exactly identified when its value is constant across every completion at
each visible input. -/
def CompletionLaw.CoordinateIdentified
    {Input Completion Coordinate Value : Type*}
    (law : CompletionLaw Input Completion Coordinate Value) (coordinate : Coordinate) : Prop :=
  ∀ input first second,
    law.value input first coordinate = law.value input second coordinate

/-! ## Sharp partial identification -/

/-- A sharp coordinatewise completion fiber.  `lower` and `upper` depend only on the visible
input, bound every completion, and are both attained by compatible completions. -/
structure SharpFiberEnvelope {Input Completion Coordinate : Type*}
    (law : CompletionLaw Input Completion Coordinate ℝ) where
  lower : Input → Coordinate → ℝ
  upper : Input → Coordinate → ℝ
  lower_le : ∀ input completion coordinate,
    lower input coordinate ≤ law.value input completion coordinate
  le_upper : ∀ input completion coordinate,
    law.value input completion coordinate ≤ upper input coordinate
  lowerWitness : Input → Coordinate → Completion
  upperWitness : Input → Coordinate → Completion
  lower_attained : ∀ input coordinate,
    law.value input (lowerWitness input coordinate) coordinate = lower input coordinate
  upper_attained : ∀ input coordinate,
    law.value input (upperWitness input coordinate) coordinate = upper input coordinate

/-- The center of the sharp completion fiber. -/
noncomputable def SharpFiberEnvelope.midpointLaw
    {Input Completion Coordinate : Type*}
    {law : CompletionLaw Input Completion Coordinate ℝ}
    (envelope : SharpFiberEnvelope law) : Input → Coordinate → ℝ :=
  fun input coordinate ↦
    midpoint (envelope.lower input coordinate) (envelope.upper input coordinate)

/-- Half the sharp fiber width. -/
noncomputable def SharpFiberEnvelope.halfWidth
    {Input Completion Coordinate : Type*}
    {law : CompletionLaw Input Completion Coordinate ℝ}
    (envelope : SharpFiberEnvelope law) (input : Input) (coordinate : Coordinate) : ℝ :=
  (envelope.upper input coordinate - envelope.lower input coordinate) / 2

/-- The midpoint misses every compatible exact value by at most half the sharp fiber width. -/
theorem SharpFiberEnvelope.midpoint_error_le_halfWidth
    {Input Completion Coordinate : Type*}
    {law : CompletionLaw Input Completion Coordinate ℝ}
    (envelope : SharpFiberEnvelope law)
    (input : Input) (completion : Completion) (coordinate : Coordinate) :
    |law.value input completion coordinate - envelope.midpointLaw input coordinate| ≤
      envelope.halfWidth input coordinate := by
  have hlower := envelope.lower_le input completion coordinate
  have hupper := envelope.le_upper input completion coordinate
  rw [abs_le]
  constructor <;>
    simp only [SharpFiberEnvelope.midpointLaw, SharpFiberEnvelope.halfWidth, midpoint] <;>
    linarith

/-- No competing visible-input law has smaller worst-case error on the two attained endpoints.
Together with `midpoint_error_le_halfWidth`, this is coordinatewise minimax optimality. -/
theorem SharpFiberEnvelope.halfWidth_le_worstEndpointError
    {Input Completion Coordinate : Type*}
    {law : CompletionLaw Input Completion Coordinate ℝ}
    (envelope : SharpFiberEnvelope law) (candidate : Input → Coordinate → ℝ)
    (input : Input) (coordinate : Coordinate) :
    envelope.halfWidth input coordinate ≤
      max
        |law.value input (envelope.lowerWitness input coordinate) coordinate -
          candidate input coordinate|
        |law.value input (envelope.upperWitness input coordinate) coordinate -
          candidate input coordinate| := by
  rw [envelope.lower_attained input coordinate, envelope.upper_attained input coordinate]
  have horder : envelope.lower input coordinate ≤ envelope.upper input coordinate :=
    le_trans
      (envelope.lower_le input (envelope.lowerWitness input coordinate) coordinate)
      (envelope.le_upper input (envelope.lowerWitness input coordinate) coordinate)
  by_cases hcandidate : candidate input coordinate ≤ envelope.midpointLaw input coordinate
  · have hnonneg : 0 ≤ envelope.upper input coordinate - candidate input coordinate := by
      simp only [SharpFiberEnvelope.midpointLaw, midpoint] at hcandidate
      linarith
    have hhalf : envelope.halfWidth input coordinate ≤
        envelope.upper input coordinate - candidate input coordinate := by
      simp only [SharpFiberEnvelope.midpointLaw, midpoint] at hcandidate
      simp only [SharpFiberEnvelope.halfWidth]
      linarith
    rw [abs_of_nonneg hnonneg]
    exact le_trans hhalf (le_max_right _ _)
  · have hcandidate' : envelope.midpointLaw input coordinate < candidate input coordinate :=
      lt_of_not_ge hcandidate
    have hnonpos : envelope.lower input coordinate - candidate input coordinate ≤ 0 := by
      simp only [SharpFiberEnvelope.midpointLaw, midpoint] at hcandidate'
      linarith
    have hhalf : envelope.halfWidth input coordinate ≤
        -(envelope.lower input coordinate - candidate input coordinate) := by
      simp only [SharpFiberEnvelope.midpointLaw, midpoint] at hcandidate'
      simp only [SharpFiberEnvelope.halfWidth]
      linarith
    rw [abs_of_nonpos hnonpos]
    exact le_trans hhalf (le_max_left _ _)

/-- A coordinate is identified exactly when both sharp endpoints agree at every input. -/
theorem SharpFiberEnvelope.coordinateIdentified_iff_endpoints_eq
    {Input Completion Coordinate : Type*}
    {law : CompletionLaw Input Completion Coordinate ℝ}
    (envelope : SharpFiberEnvelope law) (coordinate : Coordinate) :
    law.CoordinateIdentified coordinate ↔
      ∀ input, envelope.lower input coordinate = envelope.upper input coordinate := by
  constructor
  · intro hidentified input
    calc
      envelope.lower input coordinate =
          law.value input (envelope.lowerWitness input coordinate) coordinate :=
        (envelope.lower_attained input coordinate).symm
      _ = law.value input (envelope.upperWitness input coordinate) coordinate :=
        hidentified input _ _
      _ = envelope.upper input coordinate := envelope.upper_attained input coordinate
  · intro hendpoints input first second
    have hfirstLower := envelope.lower_le input first coordinate
    have hfirstUpper := envelope.le_upper input first coordinate
    have hsecondLower := envelope.lower_le input second coordinate
    have hsecondUpper := envelope.le_upper input second coordinate
    rw [hendpoints input] at hfirstLower hsecondLower
    linarith

/-- On an identified coordinate, the midpoint is exact even if other coordinates are not. -/
theorem SharpFiberEnvelope.midpoint_exact_of_coordinateIdentified
    {Input Completion Coordinate : Type*}
    {law : CompletionLaw Input Completion Coordinate ℝ}
    (envelope : SharpFiberEnvelope law) (coordinate : Coordinate)
    (hidentified : law.CoordinateIdentified coordinate)
    (input : Input) (completion : Completion) :
    law.value input completion coordinate = envelope.midpointLaw input coordinate := by
  have hendpoints :=
    (envelope.coordinateIdentified_iff_endpoints_eq coordinate).mp hidentified input
  have hlower := envelope.lower_le input completion coordinate
  have hupper := envelope.le_upper input completion coordinate
  simp only [SharpFiberEnvelope.midpointLaw, midpoint]
  rw [← hendpoints]
  linarith

/-- A complete exact readout exists precisely when every sharp completion fiber is a point. -/
theorem SharpFiberEnvelope.hasExactReadout_iff_all_endpoints_eq
    {Input Completion Coordinate : Type*}
    {law : CompletionLaw Input Completion Coordinate ℝ}
    (envelope : SharpFiberEnvelope law) :
    HasExactReadout law ↔
      ∀ input coordinate, envelope.lower input coordinate = envelope.upper input coordinate := by
  constructor
  · rintro ⟨readout, hreadout⟩ input coordinate
    calc
      envelope.lower input coordinate =
          law.value input (envelope.lowerWitness input coordinate) coordinate :=
        (envelope.lower_attained input coordinate).symm
      _ = readout input coordinate := hreadout _ _ _
      _ = law.value input (envelope.upperWitness input coordinate) coordinate :=
        (hreadout _ _ _).symm
      _ = envelope.upper input coordinate := envelope.upper_attained input coordinate
  · intro hendpoints
    refine ⟨envelope.midpointLaw, ?_⟩
    intro input completion coordinate
    have hendpoint := hendpoints input coordinate
    have hlower := envelope.lower_le input completion coordinate
    have hupper := envelope.le_upper input completion coordinate
    simp only [SharpFiberEnvelope.midpointLaw, midpoint]
    rw [← hendpoint]
    linarith

/-- One genuinely positive-width sharp fiber rules out an exact visible-input readout. -/
theorem SharpFiberEnvelope.no_exactReadout_of_lt
    {Input Completion Coordinate : Type*}
    {law : CompletionLaw Input Completion Coordinate ℝ}
    (envelope : SharpFiberEnvelope law) (input : Input) (coordinate : Coordinate)
    (hwidth : envelope.lower input coordinate < envelope.upper input coordinate) :
    ¬ HasExactReadout law := by
  intro hexact
  have heq := envelope.hasExactReadout_iff_all_endpoints_eq.mp hexact input coordinate
  exact (ne_of_lt hwidth) heq

end Descent.Core
