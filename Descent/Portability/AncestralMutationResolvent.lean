/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.AncestralMutationLimit
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

assert_below Descent.Decision Descent.Program

/-!
Finite linear equations for the exact genome/catalogue law. Interior indices
are sampled, supported, unfinished ancestry states and finite genome reports.
The homogeneous operator has zero completed-ancestry boundary. Absorption
eliminates signed homogeneous solutions, proving that the resolvent exists.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.AncestralMutationResolvent

open Coalescent.FiniteGenomeAncestry AncestralEventLaw AncestralAbsorptionLaw
open AncestralMutationTransfer AncestralMutationLimit FiniteReportLaw
open scoped NNReal

variable {D L n : ℕ}

def Interior (deme : Fin D) (s : State D L n) : Prop :=
  SampleComplete s ∧ SupportedAt deme s ∧ s.val ≠ ∅

abbrev InteriorState (D L n : ℕ) (deme : Fin D) := {s : State D L n // Interior deme s}

noncomputable instance interiorFintype (deme : Fin D) : Fintype (InteriorState D L n deme) :=
  Fintype.ofFinite _

abbrev Coordinates (D L n : ℕ) (deme : Fin D) := InteriorState D L n deme → Genome L n → ℝ

/-- Homogeneous Dirichlet extension: the completed-state row is zero. -/
noncomputable def extend (deme : Fin D) (values : Coordinates D L n deme)
    (s : State D L n) : Genome L n → ℝ := by
  classical
  exact if hs : Interior deme s then values ⟨s, hs⟩ else fun _ ↦ 0

theorem extend_interior (deme : Fin D) (values : Coordinates D L n deme)
    (s : InteriorState D L n deme) : extend deme values s.val = values s := by
  simp [extend, s.property]

theorem extend_empty (deme : Fin D) (values : Coordinates D L n deme) :
    extend deme values emptyState = 0 := by
  ext genome
  simp [extend, Interior, emptyState]

theorem extend_add (deme : Fin D) (first second : Coordinates D L n deme)
    (s : State D L n) : extend deme (first + second) s =
      extend deme first s + extend deme second s := by
  classical
  unfold extend
  split
  · rfl
  · ext genome
    simp

theorem extend_smul (deme : Fin D) (factor : ℝ) (values : Coordinates D L n deme)
    (s : State D L n) : extend deme (factor • values) s = factor • extend deme values s := by
  classical
  unfold extend
  split
  · rfl
  · ext genome
    simp

/-- Right action of one chronological mutation on an arbitrary signed row. -/
noncomputable def postcomposeArray {s : State D L n} (mark : Mark s)
    (values : Genome L n → ℝ) (output : Genome L n) : ℝ :=
  match mark with
  | none => values output
  | some (.inl _) => values output
  | some (.inr event) => ∑ input, values input * (mutationKernel event input).mass output

theorem postcomposeArray_add {s : State D L n} (mark : Mark s)
    (first second : Genome L n → ℝ) :
    postcomposeArray mark (first + second) =
      postcomposeArray mark first + postcomposeArray mark second := by
  rcases mark with _ | (event | event)
  · rfl
  · rfl
  · ext output
    simp [postcomposeArray, add_mul, Finset.sum_add_distrib]

theorem postcomposeArray_smul {s : State D L n} (mark : Mark s)
    (factor : ℝ) (values : Genome L n → ℝ) :
    postcomposeArray mark (factor • values) = factor • postcomposeArray mark values := by
  rcases mark with _ | (event | event)
  · rfl
  · rfl
  · ext output
    simp [postcomposeArray, Finset.mul_sum, mul_assoc]

/-- Every coefficient is explicitly a demographic proposal probability or a
JC69 catalogue-kernel entry. This acts on signed finite coordinate arrays. -/
noncomputable def transientOperator (rates : Rates D L) (mutationRate : Fin L → ℝ≥0)
    (deme : Fin D) : Coordinates D L n deme →ₗ[ℝ] Coordinates D L n deme where
  toFun := fun values state output ↦ ∑ mark : Mark state.val,
    (markLaw rates mutationRate state.val).mass mark *
      postcomposeArray mark (extend deme values (scanNext state.val mark)) output
  map_add' := by
    intro first second
    ext state output
    simp only [extend_add, postcomposeArray_add, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' := by
    intro factor values
    ext state output
    simp only [extend_smul, postcomposeArray_smul, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro mark _
    simp only [RingHom.id_apply]
    ring

noncomputable def rowNorm (values : Genome L n → ℝ) : ℝ := ∑ output, |values output|

theorem rowNorm_nonneg (values : Genome L n → ℝ) : 0 ≤ rowNorm values :=
  Finset.sum_nonneg (fun _ _ ↦ abs_nonneg _)

theorem rowNorm_postcompose {s : State D L n} (mark : Mark s) (values : Genome L n → ℝ) :
    rowNorm (postcomposeArray mark values) ≤ rowNorm values := by
  rcases mark with _ | (event | event)
  · exact le_rfl
  · exact le_rfl
  · calc
      rowNorm (postcomposeArray (some (.inr event)) values) ≤
          ∑ output, ∑ input, |values input| * (mutationKernel event input).mass output := by
        apply Finset.sum_le_sum
        intro output _
        exact (Finset.abs_sum_le_sum_abs _ _).trans_eq (by
          apply Finset.sum_congr rfl
          intro input _
          rw [abs_mul, abs_of_nonneg ((mutationKernel event input).mass_nonneg output)])
      _ = rowNorm values := by
        rw [Finset.sum_comm]
        simp only [← Finset.mul_sum, FiniteReportLaw.mass_sum, mul_one, rowNorm]

theorem rowNorm_transient_le (rates : Rates D L) (mutationRate : Fin L → ℝ≥0)
    (deme : Fin D) (values : Coordinates D L n deme) (s : InteriorState D L n deme) :
    rowNorm (transientOperator rates mutationRate deme values s) ≤
      (markLaw rates mutationRate s.val).expectation
        (fun mark ↦ rowNorm (extend deme values (scanNext s.val mark))) := by
  calc
    rowNorm (transientOperator rates mutationRate deme values s) ≤
        ∑ output, ∑ mark : Mark s.val, (markLaw rates mutationRate s.val).mass mark *
          |postcomposeArray mark (extend deme values (scanNext s.val mark)) output| := by
      apply Finset.sum_le_sum
      intro output _
      exact (Finset.abs_sum_le_sum_abs _ _).trans_eq (by
        apply Finset.sum_congr rfl
        intro mark _
        rw [abs_mul, abs_of_nonneg ((markLaw rates mutationRate s.val).mass_nonneg mark)])
    _ = (markLaw rates mutationRate s.val).expectation
        (fun mark ↦ rowNorm (postcomposeArray mark
          (extend deme values (scanNext s.val mark)))) := by
      rw [Finset.sum_comm]
      simp only [expectation, rowNorm, Finset.mul_sum]
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro mark _
      exact mul_le_mul_of_nonneg_left (rowNorm_postcompose mark _)
        ((markLaw rates mutationRate s.val).mass_nonneg mark)


private theorem history_reward_succ (rates : Rates D L) (mutationRate : Fin L → ℝ≥0)
    (count : ℕ) (s : State D L n) (reward : State D L n → ℝ) :
    (historyLaw rates mutationRate (count + 1) s).expectation
        (fun history ↦ reward (terminal history)) =
      (markLaw rates mutationRate s).expectation (fun mark ↦
        (historyLaw rates mutationRate count (scanNext s mark)).expectation
          (fun history ↦ reward (terminal history))) := by
  unfold expectation historyLaw
  change (∑ history : (mark : Mark s) × History count (scanNext s mark),
    ((markLaw rates mutationRate s).mass history.1 *
      historyMass rates mutationRate (scanNext s history.1) history.2) *
        reward (terminal (count := count + 1) history)) = _
  rw [Fintype.sum_sigma]
  simp only [terminal, Finset.mul_sum, mul_assoc]

private theorem subharmonic_iterate (rates : Rates D L) (mutationRate : Fin L → ℝ≥0)
    (reward : State D L n → ℝ)
    (hsub : ∀ s, reward s ≤ (markLaw rates mutationRate s).expectation
      (fun mark ↦ reward (scanNext s mark))) (count : ℕ) (s : State D L n) :
    reward s ≤ (historyLaw rates mutationRate count s).expectation
      (fun history ↦ reward (terminal history)) := by
  induction count generalizing s with
  | zero => simp [historyLaw, expectation, History, historyMass, terminal]
  | succ count ih =>
      rw [history_reward_succ]
      apply (hsub s).trans
      apply Finset.sum_le_sum
      intro mark _
      exact mul_le_mul_of_nonneg_left (ih (scanNext s mark))
        ((markLaw rates mutationRate s).mass_nonneg mark)

/-- Absorption eliminates every nonnegative subharmonic reward with zero root
boundary. This supplies injectivity for signed finite coordinate arrays. -/
theorem subharmonic_zero (rates : Rates D L) (mutationRate : Fin L → ℝ≥0)
    (deme : Fin D) (hisolated : ∀ destination, rates.migration deme destination = 0)
    (reward : State D L n → ℝ) (hnonneg : ∀ s, 0 ≤ reward s) (hroot : reward emptyState = 0)
    (hsub : ∀ s, reward s ≤ (markLaw rates mutationRate s).expectation
      (fun mark ↦ reward (scanNext s mark)))
    (s : State D L n) (hs : SampleComplete s) (hsupported : SupportedAt deme s) : reward s = 0 := by
  classical
  let bound := ∑ state : State D L n, reward state
  have hbound (state : State D L n) : reward state ≤ bound :=
    Finset.single_le_sum (fun state _ ↦ hnonneg state) (Finset.mem_univ state)
  have hpoint (state : State D L n) : reward state ≤ bound * unfinished state := by
    by_cases hcomplete : state.val = ∅
    · have heq : state = emptyState := Subtype.ext hcomplete
      subst state
      rw [hroot]
      simp [unfinished, emptyState]
    · simpa [unfinished, hcomplete] using hbound state
  have hcount (count : ℕ) : reward s ≤ bound *
      AncestralMutationAbsorption.survival rates mutationRate count s := by
    apply (subharmonic_iterate rates mutationRate reward hsub count s).trans
    unfold AncestralMutationAbsorption.survival expectation
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro history _
    have h := mul_le_mul_of_nonneg_left (hpoint (terminal history))
      (historyMass_nonneg rates mutationRate s history)
    change historyMass rates mutationRate s history * reward (terminal history) ≤
      bound * (historyMass rates mutationRate s history * unfinished (terminal history))
    nlinarith
  have hzero := ge_of_tendsto
    ((AncestralMutationAbsorption.survival_tendsto_zero rates mutationRate deme s hs hsupported
      hisolated).const_mul bound) (Filter.Eventually.of_forall hcount)
  exact le_antisymm (by simpa using hzero) (hnonneg s)

/-- A signed homogeneous solution is zero. No positivity or row-normalization
of the putative solution is assumed. -/
theorem transient_no_fixed (rates : Rates D L) (mutationRate : Fin L → ℝ≥0)
    (deme : Fin D) (hisolated : ∀ destination, rates.migration deme destination = 0)
    (values : Coordinates D L n deme) (hfixed : transientOperator rates mutationRate deme values =
      values) : values = 0 := by
  classical
  let reward := fun state : State D L n ↦ rowNorm (extend deme values state)
  have hnonneg : ∀ state, 0 ≤ reward state := fun state ↦ rowNorm_nonneg _
  have hroot : reward emptyState = 0 := by simp [reward, extend_empty, rowNorm]
  have hsub (state : State D L n) : reward state ≤
      (markLaw rates mutationRate state).expectation (fun mark ↦ reward (scanNext state mark)) := by
    by_cases hstate : Interior deme state
    · have h := rowNorm_transient_le rates mutationRate deme values ⟨state, hstate⟩
      rw [hfixed] at h
      simpa only [reward, extend_interior deme values ⟨state, hstate⟩] using h
    · have hz : reward state = 0 := by simp [reward, extend, hstate, rowNorm]
      rw [hz]
      exact Finset.sum_nonneg (fun mark _ ↦
        mul_nonneg ((markLaw rates mutationRate state).mass_nonneg mark) (hnonneg _))
  ext state output
  have hz := subharmonic_zero rates mutationRate deme hisolated reward hnonneg hroot hsub
    state.val state.property.1 state.property.2.1
  have hcoord := Finset.single_le_sum (fun genome (_ : genome ∈ Finset.univ) ↦
    abs_nonneg (values state genome)) (Finset.mem_univ output)
  have hnorm : rowNorm (values state) = 0 := by simpa only [reward, extend_interior] using hz
  change |values state output| ≤ rowNorm (values state) at hcoord
  rw [hnorm] at hcoord
  exact abs_eq_zero.mp (le_antisymm hcoord (abs_nonneg _))

noncomputable def residualOperator (rates : Rates D L) (mutationRate : Fin L → ℝ≥0)
    (deme : Fin D) : Coordinates D L n deme →ₗ[ℝ] Coordinates D L n deme :=
  LinearMap.id - transientOperator rates mutationRate deme

theorem residual_injective (rates : Rates D L) (mutationRate : Fin L → ℝ≥0)
    (deme : Fin D) (hisolated : ∀ destination, rates.migration deme destination = 0) :
    Function.Injective (residualOperator (n := n) rates mutationRate deme) := by
  intro first second heq
  have hz : residualOperator rates mutationRate deme (first - second) = 0 := by
    rw [map_sub, heq, sub_self]
  have hfixed : transientOperator rates mutationRate deme (first - second) = first - second := by
    change (first - second) - transientOperator rates mutationRate deme (first - second) = 0 at hz
    exact (sub_eq_zero.mp hz).symm
  exact sub_eq_zero.mp (transient_no_fixed rates mutationRate deme hisolated _ hfixed)

/-- The inverse of `I-Q` exists on the finite signed interior coordinate space.
This inverse is derived from demographic absorption, not assumed invertible. -/
noncomputable def resolvent (rates : Rates D L) (mutationRate : Fin L → ℝ≥0)
    (deme : Fin D) (hisolated : ∀ destination, rates.migration deme destination = 0) :
    Coordinates D L n deme ≃ₗ[ℝ] Coordinates D L n deme :=
  (LinearEquiv.ofBijective (residualOperator rates mutationRate deme)
    ⟨residual_injective rates mutationRate deme hisolated,
      LinearMap.surjective_of_injective
        (residual_injective rates mutationRate deme hisolated)⟩).symm

theorem resolvent_solve (rates : Rates D L) (mutationRate : Fin L → ℝ≥0)
    (deme : Fin D) (hisolated : ∀ destination, rates.migration deme destination = 0)
    (forcing : Coordinates D L n deme) :
    residualOperator rates mutationRate deme (resolvent rates mutationRate deme hisolated forcing) =
      forcing :=
  (LinearEquiv.ofBijective (residualOperator rates mutationRate deme)
    ⟨residual_injective rates mutationRate deme hisolated,
      LinearMap.surjective_of_injective
        (residual_injective rates mutationRate deme hisolated)⟩).apply_symm_apply forcing

theorem resolvent_unique (rates : Rates D L) (mutationRate : Fin L → ℝ≥0)
    (deme : Fin D) (hisolated : ∀ destination, rates.migration deme destination = 0)
    (forcing values : Coordinates D L n deme)
    (hequation : residualOperator rates mutationRate deme values = forcing) :
    values = resolvent rates mutationRate deme hisolated forcing := by
  apply residual_injective rates mutationRate deme hisolated
  rw [hequation, resolvent_solve]


/-- The known completed-ancestry boundary vector, separated from the unknown
interior coordinates in the finite linear system. -/
noncomputable def rootBoundary (s : State D L n) : Genome L n → ℝ := by
  classical
  exact fun output ↦ if s.val = ∅ then rootGenomeLaw.mass output else 0

noncomputable def forcing (rates : Rates D L) (mutationRate : Fin L → ℝ≥0)
    (deme : Fin D) : Coordinates D L n deme := fun state output ↦
  ∑ mark : Mark state.val, (markLaw rates mutationRate state.val).mass mark *
    postcomposeArray mark (rootBoundary (scanNext state.val mark)) output

noncomputable def solutionCoordinates (rates : Rates D L) (mutationRate : Fin L → ℝ≥0)
    (deme : Fin D) (hisolated : ∀ destination, rates.migration deme destination = 0) :
    Coordinates D L n deme := fun state ↦
  (limitLaw rates mutationRate deme state.val state.property.1 state.property.2.1 hisolated).mass

private theorem solution_boundary_row (rates : Rates D L) (mutationRate : Fin L → ℝ≥0)
    (deme : Fin D) (hisolated : ∀ destination, rates.migration deme destination = 0)
    (s : State D L n) (hs : SampleComplete s) (hsupported : SupportedAt deme s) :
    extend deme (solutionCoordinates rates mutationRate deme hisolated) s + rootBoundary s =
      (limitLaw rates mutationRate deme s hs hsupported hisolated).mass := by
  classical
  by_cases hempty : s.val = ∅
  · have heq : s = emptyState := Subtype.ext hempty
    subst s
    rw [extend_empty, limitLaw_boundary]
    ext output
    simp [rootBoundary, emptyState]
  · have hinterior : Interior deme s := ⟨hs, hsupported, hempty⟩
    ext output
    simp [extend, hinterior, rootBoundary, hempty, solutionCoordinates]

private theorem positiveMark_sum (rates : Rates D L) (mutationRate : Fin L → ℝ≥0)
    (s : State D L n) (values : Mark s → ℝ) :
    (∑ mark : PositiveMark rates mutationRate s,
      (markLaw rates mutationRate s).mass mark.val * values mark.val) =
        ∑ mark : Mark s, (markLaw rates mutationRate s).mass mark * values mark := by
  classical
  have hzero : (∑ mark : {mark : Mark s // ¬ 0 < (markLaw rates mutationRate s).mass mark},
      (markLaw rates mutationRate s).mass mark.val * values mark.val) = 0 := by
    apply Finset.sum_eq_zero
    intro mark _
    have hmass := le_antisymm (le_of_not_gt mark.property)
      ((markLaw rates mutationRate s).mass_nonneg mark.val)
    rw [hmass, zero_mul]
  have h := Fintype.sum_subtype_add_sum_subtype
    (fun mark : Mark s ↦ 0 < (markLaw rates mutationRate s).mass mark)
    (fun mark ↦ (markLaw rates mutationRate s).mass mark * values mark)
  rw [hzero, add_zero] at h
  convert h using 1
  congr 1
  ext mark
  simp

private theorem next_admissible (rates : Rates D L) (mutationRate : Fin L → ℝ≥0)
    (deme : Fin D) (hisolated : ∀ destination, rates.migration deme destination = 0)
    (s : InteriorState D L n deme) (mark : PositiveMark rates mutationRate s.val) :
    SampleComplete (scanNext s.val mark.val) ∧ SupportedAt deme (scanNext s.val mark.val) := by
  rcases mark with ⟨mark, hpos⟩
  rcases mark with _ | (event | event)
  · exact ⟨s.property.1, s.property.2.1⟩
  · have hrate : 0 < eventRate rates s.val event := by
      change 0 < eventRate rates s.val event / intensity (n := n) rates mutationRate at hpos
      exact (div_pos_iff_of_pos_right (intensity_pos rates mutationRate)).mp hpos
    exact ⟨sampleComplete_proposal s.val s.property.1 (some event),
      supportedAt_proposal rates deme hisolated s.val s.property.2.1 (some event)
        (div_pos hrate (dominatingRate_pos rates))⟩
  · exact ⟨s.property.1, s.property.2.1⟩

private theorem postcomposeArray_law {s : State D L n} (mark : Mark s)
    (law : FiniteReportLaw (Genome L n)) :
    postcomposeArray mark law.mass = (postcomposeMark mark law).mass := by
  rcases mark with _ | (event | event) <;> rfl

/-- The constructed exact genome law solves the explicit finite inhomogeneous
linear system, with all boundary probabilities supplied by the root genome law. -/
theorem solution_equation (rates : Rates D L) (mutationRate : Fin L → ℝ≥0)
    (deme : Fin D) (hisolated : ∀ destination, rates.migration deme destination = 0) :
    residualOperator (n := n) rates mutationRate deme
        (solutionCoordinates rates mutationRate deme hisolated) =
      forcing rates mutationRate deme := by
  classical
  let solution : Coordinates D L n deme := solutionCoordinates rates mutationRate deme hisolated
  have hfixed (state : InteriorState D L n deme) (output : Genome L n) :
      solution state output = transientOperator rates mutationRate deme solution state output +
        forcing rates mutationRate deme state output := by
    have halgebra : transientOperator rates mutationRate deme solution state output +
        forcing rates mutationRate deme state output =
          ∑ mark : Mark state.val, (markLaw rates mutationRate state.val).mass mark *
            postcomposeArray mark (extend deme solution (scanNext state.val mark) +
              rootBoundary (scanNext state.val mark)) output := by
      simp only [transientOperator, LinearMap.coe_mk, AddHom.coe_mk, forcing,
        postcomposeArray_add, Pi.add_apply, mul_add, Finset.sum_add_distrib]
    rw [halgebra, ← positiveMark_sum]
    change (limitLaw rates mutationRate deme state.val state.property.1 state.property.2.1
      hisolated).mass output = _
    rw [limitLaw_fixed]
    change (∑ mark : PositiveMark rates mutationRate state.val,
      (markLaw rates mutationRate state.val).mass mark.val *
        (limitMarkLaw rates mutationRate deme state.val state.property.1 state.property.2.1
          hisolated mark).mass output) = _
    apply Finset.sum_congr rfl
    intro mark _
    have hnext := next_admissible rates mutationRate deme hisolated state mark
    have hrow := solution_boundary_row rates mutationRate deme hisolated
      (scanNext state.val mark.val) hnext.1 hnext.2
    unfold limitMarkLaw
    rw [← postcomposeArray_law]
    change (markLaw rates mutationRate state.val).mass mark.val *
      postcomposeArray mark.val (limitLaw rates mutationRate deme (scanNext state.val mark.val)
        hnext.1 hnext.2 hisolated).mass output = _
    rw [← hrow]
  ext state output
  have h := hfixed state output
  change solution state output - transientOperator rates mutationRate deme solution state output = _
  linarith

/-- Exact finite resolvent law. The inverse exists because the actual ancestral
process absorbs; coefficients come from demographic and mutation rates. -/
theorem solution_eq_resolvent (rates : Rates D L) (mutationRate : Fin L → ℝ≥0)
    (deme : Fin D) (hisolated : ∀ destination, rates.migration deme destination = 0) :
    solutionCoordinates (n := n) rates mutationRate deme hisolated =
      resolvent rates mutationRate deme hisolated (forcing rates mutationRate deme) :=
  resolvent_unique rates mutationRate deme hisolated _ _
    (solution_equation rates mutationRate deme hisolated)

/-- Every finite whole-genome report expectation is an explicit readout of
`(I-Q)⁻¹ b`, with invertibility and identification both proved. -/
theorem expectation_resolvent (rates : Rates D L) (mutationRate : Fin L → ℝ≥0)
    (deme : Fin D) (hisolated : ∀ destination, rates.migration deme destination = 0)
    (state : InteriorState D L n deme) (readout : Genome L n → ℝ) :
    (limitLaw rates mutationRate deme state.val state.property.1 state.property.2.1
      hisolated).expectation readout =
      ∑ genome, (resolvent rates mutationRate deme hisolated
        (forcing rates mutationRate deme) state genome) * readout genome := by
  change (∑ genome, solutionCoordinates rates mutationRate deme hisolated state genome *
    readout genome) = _
  rw [solution_eq_resolvent]

end Descent.Portability.AncestralMutationResolvent
