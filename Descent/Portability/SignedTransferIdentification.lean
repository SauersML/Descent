/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.AncestralMutationResolvent
import Descent.Portability.StoppedGenotypeRenewal

assert_below Descent.Decision Descent.Program

/-!
Identification of signed finite genome rows by their physical ancestry and
mutation balance equations. Only admissible rows and the completed root
boundary are used; no normalized law is invented at other material states.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.SignedTransferIdentification

open Coalescent.FiniteGenomeAncestry AncestralEventLaw AncestralAbsorptionLaw
open AncestralMutationTransfer AncestralMutationLimit AncestralMutationResolvent
open FiniteReportLaw
open scoped NNReal

variable {D L n : ℕ}

abbrev Rows (D L n : ℕ) := State D L n → Genome L n → ℝ

noncomputable def arrayTransfer (rates : Rates D L) (mutationRate : Fin L → ℝ≥0)
    (rows : Rows D L n) (state : State D L n) (target : Genome L n) : ℝ :=
  ∑ mark : Mark state, (markLaw rates mutationRate state).mass mark *
    postcomposeArray mark (rows (scanNext state mark)) target

/-- Physical-event balance is exactly the finite joint transfer equation,
also for signed rows that have no probability normalization assumption. -/
theorem arrayTransfer_generator (rates : Rates D L) (mutationRate : Fin L → ℝ≥0)
    (rows : Rows D L n) (state : State D L n) (target : Genome L n) :
    intensity (n := n) rates mutationRate *
        (arrayTransfer rates mutationRate rows state target - rows state target) =
      (∑ event : Channel state, eventRate rates state event *
        (rows (nextState state event) target - rows state target)) +
      ∑ event : MutationChannel state, (mutationRate event.val.2 : ℝ) *
        ((∑ input, rows state input * (mutationKernel event input).mass target) -
          rows state target) := by
  unfold arrayTransfer markLaw scanNext postcomposeArray
  rw [Fintype.sum_option, Fintype.sum_sum_type]
  simp only [div_mul_eq_mul_div, ← Finset.sum_div, mul_sub, Finset.sum_sub_distrib,
    ← Finset.sum_mul]
  unfold totalIntensity totalRate mutationIntensity
  have hi := ne_of_gt (intensity_pos (n := n) rates mutationRate)
  field_simp
  ring

noncomputable def rowCoordinates (deme : Fin D) (rows : Rows D L n) : Coordinates D L n deme :=
  fun state ↦ rows state.val

private theorem row_boundary_extension (deme : Fin D) (rows : Rows D L n)
    (hboundary : rows emptyState = rootGenomeLaw.mass)
    (state : State D L n) (hs : SampleComplete state) (hsupported : SupportedAt deme state) :
    extend deme (rowCoordinates deme rows) state + rootBoundary state = rows state := by
  classical
  by_cases hempty : state.val = ∅
  · have heq : state = emptyState := Subtype.ext hempty
    subst state
    rw [extend_empty, hboundary]
    ext output
    simp [rootBoundary, emptyState]
  · have hinterior : Interior deme state := ⟨hs, hsupported, hempty⟩
    ext output
    simp [extend, hinterior, rootBoundary, hempty, rowCoordinates]

private theorem positive_next_admissible (rates : Rates D L) (mutationRate : Fin L → ℝ≥0)
    (deme : Fin D) (hisolated : ∀ destination, rates.migration deme destination = 0)
    (state : InteriorState D L n deme) (mark : Mark state.val)
    (hpos : 0 < (markLaw rates mutationRate state.val).mass mark) :
    SampleComplete (scanNext state.val mark) ∧ SupportedAt deme (scanNext state.val mark) := by
  rcases mark with _ | (event | event)
  · exact ⟨state.property.1, state.property.2.1⟩
  · have hrate : 0 < eventRate rates state.val event := by
      change 0 < eventRate rates state.val event / intensity (n := n) rates mutationRate at hpos
      exact (div_pos_iff_of_pos_right (intensity_pos rates mutationRate)).mp hpos
    exact ⟨sampleComplete_proposal state.val state.property.1 (some event),
      supportedAt_proposal rates deme hisolated state.val state.property.2.1 (some event)
        (div_pos hrate (dominatingRate_pos rates))⟩
  · exact ⟨state.property.1, state.property.2.1⟩

/-- Any admissible fixed family solves the same finite inhomogeneous system. -/
theorem rowCoordinates_equation (rates : Rates D L) (mutationRate : Fin L → ℝ≥0)
    (deme : Fin D) (hisolated : ∀ destination, rates.migration deme destination = 0)
    (rows : Rows D L n) (hboundary : rows emptyState = rootGenomeLaw.mass)
    (hfixed : ∀ state, Interior deme state → ∀ output,
      arrayTransfer rates mutationRate rows state output = rows state output) :
    residualOperator rates mutationRate deme (rowCoordinates deme rows) =
      forcing rates mutationRate deme := by
  classical
  have heq (state : InteriorState D L n deme) (output : Genome L n) :
      transientOperator rates mutationRate deme (rowCoordinates deme rows) state output +
        forcing rates mutationRate deme state output = rows state.val output := by
    have halgebra : transientOperator rates mutationRate deme (rowCoordinates deme rows)
          state output + forcing rates mutationRate deme state output =
        ∑ mark : Mark state.val, (markLaw rates mutationRate state.val).mass mark *
          postcomposeArray mark
            (extend deme (rowCoordinates deme rows) (scanNext state.val mark) +
              rootBoundary (scanNext state.val mark)) output := by
      simp only [transientOperator, LinearMap.coe_mk, AddHom.coe_mk, forcing,
        postcomposeArray_add, Pi.add_apply, mul_add, Finset.sum_add_distrib]
    rw [halgebra, ← hfixed state.val state.property output]
    unfold arrayTransfer
    apply Finset.sum_congr rfl
    intro mark _
    by_cases hpos : 0 < (markLaw rates mutationRate state.val).mass mark
    · have hn := positive_next_admissible rates mutationRate deme hisolated state mark hpos
      rw [row_boundary_extension deme rows hboundary _ hn.1 hn.2]
    · have hz := le_antisymm (le_of_not_gt hpos)
        ((markLaw rates mutationRate state.val).mass_nonneg mark)
      rw [hz, zero_mul, zero_mul]
  ext state output
  have h := heq state output
  change rows state.val output -
    transientOperator rates mutationRate deme (rowCoordinates deme rows) state output = _
  linarith

/-- The signed balance equations and the root boundary identify the exact
constructed joint law, without any hypotheses on rows outside the support. -/
theorem balance_identifies_limit (rates : Rates D L) (mutationRate : Fin L → ℝ≥0)
    (deme : Fin D) (hisolated : ∀ destination, rates.migration deme destination = 0)
    (rows : Rows D L n) (hboundary : rows emptyState = rootGenomeLaw.mass)
    (hbalance : ∀ state, Interior deme state → ∀ target,
      (∑ event : Channel state, eventRate rates state event *
        (rows (nextState state event) target - rows state target)) +
      (∑ event : MutationChannel state, (mutationRate event.val.2 : ℝ) *
        ((∑ input, rows state input * (mutationKernel event input).mass target) -
          rows state target)) = 0)
    (state : State D L n) (hs : SampleComplete state) (hsupported : SupportedAt deme state) :
    rows state = (limitLaw rates mutationRate deme state hs hsupported hisolated).mass := by
  classical
  have hfixed : ∀ state, Interior deme state → ∀ output,
      arrayTransfer rates mutationRate rows state output = rows state output := by
    intro state hstate output
    have h := arrayTransfer_generator rates mutationRate rows state output
    rw [hbalance state hstate output] at h
    exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_left
      (ne_of_gt (intensity_pos rates mutationRate)))
  have heq : rowCoordinates deme rows = solutionCoordinates rates mutationRate deme hisolated := by
    apply residual_injective rates mutationRate deme hisolated
    rw [rowCoordinates_equation rates mutationRate deme hisolated rows hboundary hfixed,
      solution_equation]
  by_cases hempty : state.val = ∅
  · have he : state = emptyState := Subtype.ext hempty
    subst state
    rw [hboundary, limitLaw_boundary]
  · exact congrArg (fun values : Coordinates D L n deme ↦ values ⟨state, hs, hsupported, hempty⟩)
      heq

open StoppedGenotypeLaw StoppedGenotypeRenewal FiniteProductExponential

/-- A pointwise channel enumeration identity also identifies the generator's
right action on every real genome row. -/
theorem mutation_generator_row (state : State D L n) (rate : ℝ≥0)
    (hgenerator : ∀ source target, genomeGenerator state rate source target =
      ∑ event : MutationChannel state, (rate : ℝ) *
        ((mutationKernel event source).mass target - (pointMass source).mass target))
    (row : Genome L n → ℝ) (target : Genome L n) :
    (∑ source, row source * genomeGenerator state rate source target) =
      ∑ event : MutationChannel state, (rate : ℝ) *
        ((∑ source, row source * (mutationKernel event source).mass target) - row target) := by
  classical
  simp_rw [hgenerator]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro event _
  simp [mul_sub, Finset.sum_sub_distrib, pointMass, mul_left_comm,
    Finset.mul_sum, mul_comm]

/-- Once the finite branch/channel enumeration is proved, the independently
constructed timed stopped law equals the unique combined-event transfer law. -/
theorem stoppedGenome_eq_limit_of_generator (rates : Rates D L) (rate : ℝ≥0)
    (hgenerator : ∀ state : State D L n, ∀ source target,
      genomeGenerator state rate source target =
        ∑ event : MutationChannel state, (rate : ℝ) *
          ((mutationKernel event source).mass target - (pointMass source).mass target))
    (deme : Fin D) (hisolated : ∀ destination, rates.migration deme destination = 0)
    (state : State D L n) (hs : SampleComplete state) (hsupported : SupportedAt deme state) :
    stoppedGenomeLaw rates deme state hs hsupported hisolated rate =
      limitLaw rates (fun _ ↦ rate) deme state hs hsupported hisolated := by
  have hboundary : (fun output : Genome L n ↦ stoppedMass rates emptyState rate output) =
      rootGenomeLaw.mass := funext (stoppedMass_boundary rates rate)
  have hbalance (state : State D L n) (hstate : Interior deme state) (target : Genome L n) :
      (∑ event : Channel state, eventRate rates state event *
        (stoppedMass rates (nextState state event) rate target -
          stoppedMass rates state rate target)) +
      (∑ event : MutationChannel state, (rate : ℝ) *
        ((∑ input, stoppedMass rates state rate input * (mutationKernel event input).mass target) -
          stoppedMass rates state rate target)) = 0 := by
    rw [← mutation_generator_row state rate (hgenerator state)
      (stoppedMass rates state rate) target]
    exact stoppedMass_event_balance rates state rate hstate.2.2 target
  have hid := balance_identifies_limit rates (fun _ ↦ rate) deme hisolated
    (fun state output ↦ stoppedMass rates state rate output) hboundary hbalance state hs hsupported
  apply FiniteReportLaw.ext
  intro output
  exact congrFun hid output

end Descent.Portability.SignedTransferIdentification
