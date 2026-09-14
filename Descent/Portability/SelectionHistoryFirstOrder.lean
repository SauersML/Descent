/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.SelectionMomentExpansion
import Descent.Portability.EndToEndSensitivityMetrics

assert_below Descent.Decision Descent.Program

/-!
# The first-order effect of selection on moments and portability along a history

`SelectionMomentExpansion` gives the first-order selection correction of one epoch, with a
remainder of order `σ² d²`, and `EndToEndSelectionLaw` bounds the zero-order deviation of the
moments along a history of epochs, splits and pulses by `B σ T`. This module composes the two: the
first-order correction of a whole history, its linearity in the fitness table, and the
first-order correction of portability.

The correction of a history. `historyCorrection` sums over the epochs of a history the neutral
propagator of the rest of the history applied to the epoch's first-order correction
(`SelectionMomentExpansion.selectionCorrection`) at the neutral moments of the larger budget
entering the epoch; splits and pulses carry those moments forward and contribute nothing. It is
linear in the initial moments of the larger budget (`historyCorrection_sub`) and costs at most
`2 B S T` in sup norm (`norm_historyCorrection_le`), from the cost `2 B S d` of one epoch
(`norm_selectionCorrection_le`).

The first-order law. One stage of a history combines three errors: the remainder of the rest of
the history, the one-epoch remainder `B S B' σ d²`, and the zero-order error `B' σ d` of the
larger-budget moments entering the rest, carried by the correction of the rest at cost `2 B S T`
(`norm_sub_firstOrder_step_le`). Since `T² = Σ d² + 2 Σ_{j<k} d_j d_k`, these add to exactly
`B S B' σ T²`: along a history with total epoch duration `T` the selected moments equal the neutral
chronological propagator applied to the initial moments plus the correction of the history, up to
`B S B' σ T²` in sup norm (`norm_selectedHistory_sub_firstOrder_le`).

Scope. The forward moment equation with selection is a hypothesis on the families, at the budget
and at the budget with one more copy at the selected locus, as in `SelectionHistoryMoments` and
`EndToEndSelectionLaw`; the selected diffusion is not constructed. Selection is haploid at one
locus, with one fitness table for the whole history.

## Empirical status

None. The bodies here are norm inequalities for matrix products, integrals of matrix exponentials
and rational functions of supplied values, so no measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.SelectionHistoryFirstOrder

open MvPolynomial Descent.Coalescent Descent.Foundations PartialHaplotypeCarrier
  PartialHaplotypeDualGenerator PartialHaplotypeDualSemigroup SubstochasticGeneratorSemigroup
  PartialHaplotypePulseKernel NeutralPulseHistoryKernel EndToEndPortabilityLaw
  SelectionHistoryMoments EndToEndSelectionLaw SelectionMomentExpansion EndToEndSensitivityMetrics
open scoped Matrix NNReal

noncomputable section

/-! ## One stage of the expansion -/

/-- **One stage of the first-order expansion.** Let `P` be substochastic and `H` linear with cost
at most `L`. If `V` is within `a` of `P v + H x`, `v` is within `b` of `u + c` and `x` is within
`e` of `w`, then `V` is within `a + b + L e` of `P u + (P c + H w)`. -/
theorem norm_sub_firstOrder_step_le {ι κ : Type*} [Fintype ι] [Fintype κ] {P : Matrix ι ι ℝ}
    (hP : SubstochasticMatrix P) (H : (κ → ℝ) → ι → ℝ) (hH : ∀ x y, H (x - y) = H x - H y)
    {L : ℝ} (hL : ∀ x, ‖H x‖ ≤ L * ‖x‖) (hL0 : 0 ≤ L) {V v u c : ι → ℝ} {x w : κ → ℝ}
    {a b e : ℝ} (hrest : ‖V - P *ᵥ v - H x‖ ≤ a) (hstage : ‖v - u - c‖ ≤ b)
    (hlarger : ‖x - w‖ ≤ e) :
    ‖V - P *ᵥ u - (P *ᵥ c + H w)‖ ≤ a + b + L * e := by
  have hsplit : V - P *ᵥ u - (P *ᵥ c + H w)
      = (V - P *ᵥ v - H x) + P *ᵥ (v - u - c) + H (x - w) := by
    rw [hH, Matrix.mulVec_sub, Matrix.mulVec_sub]
    abel
  rw [hsplit]
  refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans
    (add_le_add hrest ((norm_mulVec_le_of_substochastic hP _).trans hstage))) ?_)
  exact (hL _).trans (mul_le_mul_of_nonneg_left hlarger hL0)

variable {Deme Locus : Type*} {Allele : Locus → Type*}
variable [Fintype Deme] [DecidableEq Deme] [Fintype Locus] [DecidableEq Locus]
  [∀ ℓ, Fintype (Allele ℓ)] [∀ ℓ, DecidableEq (Allele ℓ)]

/-! ## The first-order correction of one epoch -/

/-- The integrand of the first-order correction of one epoch is continuous in time. -/
theorem continuous_correctionIntegrand (rates : NeutralRates Deme Locus Allele)
    (model : SelectionModel Deme Locus Allele) (capacity : Locus → ℕ)
    (w : BudgetConfiguration Deme Locus Allele (bumpCapacity model capacity) → ℝ) (d : ℝ) :
    Continuous fun t ↦ matrixExponential (dualGenerator rates capacity) (d - t)
      *ᵥ (selectionMatrix model capacity
        *ᵥ (matrixExponential (dualGenerator rates (bumpCapacity model capacity)) t *ᵥ w)) := by
  have hexp : Continuous fun t ↦
      matrixExponential (dualGenerator rates (bumpCapacity model capacity)) t *ᵥ w :=
    continuous_iff_continuousAt.mpr fun t ↦
      (StationaryHaplotypeRealization.hasDerivAt_matrixExponential_mulVec
        (dualGenerator rates (bumpCapacity model capacity)) w t).continuousAt
  have hinner : Continuous fun t ↦ selectionMatrix model capacity
      *ᵥ (matrixExponential (dualGenerator rates (bumpCapacity model capacity)) t *ᵥ w) :=
    continuous_const.matrix_mulVec hexp
  exact continuousOn_univ.mp (continuousOn_propagator_mulVec _ d hinner.continuousOn)

/-- The first-order correction of one epoch is linear in the initial moments of the larger
budget. -/
theorem selectionCorrection_sub (rates : NeutralRates Deme Locus Allele)
    (model : SelectionModel Deme Locus Allele) (capacity : Locus → ℕ)
    (x y : BudgetConfiguration Deme Locus Allele (bumpCapacity model capacity) → ℝ) (d : ℝ) :
    selectionCorrection rates model capacity (x - y) d
      = selectionCorrection rates model capacity x d
        - selectionCorrection rates model capacity y d := by
  simp only [selectionCorrection, Matrix.mulVec_sub]
  exact intervalIntegral.integral_sub
    ((continuous_correctionIntegrand rates model capacity x d).intervalIntegrable _ _)
    ((continuous_correctionIntegrand rates model capacity y d).intervalIntegrable _ _)

/-- **The first-order correction of an epoch costs at most `2 B S d`** in sup norm, for fitness
masses `Σ_b |s_i(b)| ≤ S` and a budget of total size `B = Σ_ℓ n_ℓ`. -/
theorem norm_selectionCorrection_le (rates : NeutralRates Deme Locus Allele)
    (model : SelectionModel Deme Locus Allele) {S : ℝ} (hS0 : 0 ≤ S)
    (hS : ∀ i, ∑ b, |model.fitness i b| ≤ S) (capacity : Locus → ℕ)
    (w : BudgetConfiguration Deme Locus Allele (bumpCapacity model capacity) → ℝ) {d : ℝ}
    (hd : 0 ≤ d) :
    ‖selectionCorrection rates model capacity w d‖
      ≤ 2 * (∑ ℓ, capacity ℓ : ℕ) * S * d * ‖w‖ := by
  have hpoint : ∀ t ∈ Set.uIoc 0 d,
      ‖matrixExponential (dualGenerator rates capacity) (d - t)
        *ᵥ (selectionMatrix model capacity
          *ᵥ (matrixExponential (dualGenerator rates (bumpCapacity model capacity)) t *ᵥ w))‖
        ≤ 2 * (∑ ℓ, capacity ℓ : ℕ) * S * ‖w‖ := by
    intro t ht
    rw [Set.uIoc_of_le hd] at ht
    have hlate := dualPropagator_substochastic rates capacity (d - t) (sub_nonneg.mpr ht.2)
    have hearly := dualPropagator_substochastic rates (bumpCapacity model capacity) t ht.1.le
    calc _ ≤ ‖selectionMatrix model capacity
          *ᵥ (matrixExponential (dualGenerator rates (bumpCapacity model capacity)) t *ᵥ w)‖ :=
          norm_mulVec_le_of_substochastic hlate _
      _ ≤ 2 * (∑ ℓ, capacity ℓ : ℕ) * S
          * ‖matrixExponential (dualGenerator rates (bumpCapacity model capacity)) t *ᵥ w‖ :=
          norm_selectionMatrix_mulVec_le model hS0 hS capacity _
      _ ≤ 2 * (∑ ℓ, capacity ℓ : ℕ) * S * ‖w‖ :=
          mul_le_mul_of_nonneg_left (norm_mulVec_le_of_substochastic hearly w) (by positivity)
  have h := intervalIntegral.norm_integral_le_of_norm_le_const hpoint
  rw [sub_zero, abs_of_nonneg hd] at h
  rw [selectionCorrection]
  exact h.trans_eq (by ring)

/-! ## The first-order correction of a history -/

/-- **The first-order selection correction of a history.** Every epoch contributes the neutral
propagator of the rest of the history applied to its first-order correction at the neutral
moments of the larger budget entering it. Splits and pulses contribute nothing and carry those
moments forward. -/
def historyCorrection (model : SelectionModel Deme Locus Allele) (capacity : Locus → ℕ) :
    List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme) →
      (BudgetConfiguration Deme Locus Allele (bumpCapacity model capacity) → ℝ) →
        BudgetConfiguration Deme Locus Allele capacity → ℝ
  | [], _ => 0
  | Sum.inl epoch :: rest, w =>
      historyEventPropagator capacity rest
          *ᵥ selectionCorrection epoch.1 model capacity w epoch.2
        + historyCorrection model capacity rest
          (matrixExponential (dualGenerator epoch.1 (bumpCapacity model capacity)) epoch.2 *ᵥ w)
  | Sum.inr pulse :: rest, w =>
      historyCorrection model capacity rest (pulseKernel pulse (bumpCapacity model capacity) *ᵥ w)

/-- The first-order correction of a history is linear in the initial moments of the larger
budget. -/
theorem historyCorrection_sub (model : SelectionModel Deme Locus Allele) (capacity : Locus → ℕ) :
    ∀ (events : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme))
      (x y : BudgetConfiguration Deme Locus Allele (bumpCapacity model capacity) → ℝ),
      historyCorrection model capacity events (x - y)
        = historyCorrection model capacity events x - historyCorrection model capacity events y
  | [], _, _ => by simp only [historyCorrection, sub_zero]
  | Sum.inl epoch :: rest, x, y => by
    simp only [historyCorrection, selectionCorrection_sub, Matrix.mulVec_sub,
      historyCorrection_sub model capacity rest]
    abel
  | Sum.inr pulse :: rest, x, y => by
    simp only [historyCorrection, Matrix.mulVec_sub]
    exact historyCorrection_sub model capacity rest _ _

/-- **The first-order correction of a history costs at most `2 B S T`** in sup norm, with `T` the
total epoch duration of the history. -/
theorem norm_historyCorrection_le (model : SelectionModel Deme Locus Allele) {S : ℝ}
    (hS0 : 0 ≤ S) (hS : ∀ i, ∑ b, |model.fitness i b| ≤ S) (capacity : Locus → ℕ) :
    ∀ (events : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme))
      (w : BudgetConfiguration Deme Locus Allele (bumpCapacity model capacity) → ℝ),
      ‖historyCorrection model capacity events w‖
        ≤ 2 * (∑ ℓ, capacity ℓ : ℕ) * S * epochDuration events * ‖w‖
  | [], w => by simp [historyCorrection, epochDuration]
  | Sum.inl epoch :: rest, w => by
    have hstage := (norm_mulVec_le_of_substochastic
      (historyEventPropagator_substochastic capacity rest) _).trans
        (norm_selectionCorrection_le epoch.1 model hS0 hS capacity w (NNReal.coe_nonneg epoch.2))
    have hnext := norm_mulVec_le_of_substochastic
      (dualPropagator_substochastic epoch.1 (bumpCapacity model capacity) epoch.2
        (NNReal.coe_nonneg _)) w
    have hrest := (norm_historyCorrection_le model hS0 hS capacity rest
      (matrixExponential (dualGenerator epoch.1 (bumpCapacity model capacity)) epoch.2 *ᵥ w)).trans
        (mul_le_mul_of_nonneg_left hnext (mul_nonneg (by positivity) (epochDuration_nonneg rest)))
    rw [historyCorrection, epochDuration]
    exact ((norm_add_le _ _).trans (add_le_add hstage hrest)).trans_eq (by ring)
  | Sum.inr pulse :: rest, w => by
    have hnext := norm_mulVec_le_of_substochastic
      (pulseKernel_substochastic (Allele := Allele) pulse (bumpCapacity model capacity)) w
    rw [historyCorrection, epochDuration]
    exact (norm_historyCorrection_le model hS0 hS capacity rest _).trans
      (mul_le_mul_of_nonneg_left hnext (mul_nonneg (by positivity) (epochDuration_nonneg rest)))

/-! ## The first-order law along a history -/

/-- **The first-order selection law of a history.** Along a history of epochs, splits and pulses
with total epoch duration `T`, selected families with fitnesses in `[0, σ]` and fitness masses
`Σ_b |s_i(b)| ≤ S`, obeying the forward moment equation with selection at the budget and at the
budget with one more copy at the selected locus, end with moments equal to the neutral
chronological propagator applied to their initial moments plus the first-order correction of the
history, up to `B S B' σ T²` in sup norm, with `B = Σ_ℓ n_ℓ` and `B' = B + 1`.

Assumes: `SelectedOnHistory model capacity family events k` and
`SelectedOnHistory model (bumpCapacity model capacity) family events k`. -/
theorem norm_selectedHistory_sub_firstOrder_le (model : SelectionModel Deme Locus Allele)
    {σ S : ℝ} (hσ : 0 ≤ σ) (hS0 : 0 ≤ S)
    (hfit : ∀ i b, 0 ≤ model.fitness i b ∧ model.fitness i b ≤ σ)
    (hS : ∀ i, ∑ b, |model.fitness i b| ≤ S) (capacity : Locus → ℕ)
    (family : ℕ → ℝ → ExpFunctional (Deme → FiniteReportLaw (FullHaplotype Locus Allele))) :
    ∀ (events : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme)) (k : ℕ),
      SelectedOnHistory model capacity family events k →
      SelectedOnHistory model (bumpCapacity model capacity) family events k →
      ‖expectedMomentVector capacity (family (k + events.length)) 0
          - historyEventPropagator capacity events *ᵥ expectedMomentVector capacity (family k) 0
          - historyCorrection model capacity events
            (expectedMomentVector (bumpCapacity model capacity) (family k) 0)‖
        ≤ (∑ ℓ, capacity ℓ : ℕ) * S * ((∑ ℓ, capacity ℓ : ℕ) + 1) * σ
          * epochDuration events ^ 2
  | [], k, _, _ => by
    simp [historyEventPropagator, historyCorrection, epochDuration]
  | Sum.inl epoch :: rest, k, hhistory, hhistory' => by
    obtain ⟨⟨hcont, hforward, hnext⟩, hrest⟩ := hhistory
    obtain ⟨⟨hcont', hforward', hnext'⟩, hrest'⟩ := hhistory'
    have hstage := norm_expectedMomentVector_sub_firstOrder_le epoch.1 model hσ hS0 hfit hS
      capacity (family k) (NNReal.coe_nonneg epoch.2) hcont hcont' hforward hforward'
    rw [← hnext] at hstage
    have hlarger := norm_expectedMomentVector_sub_propagator_le epoch.1 model hσ hfit
      (bumpCapacity model capacity) (family k) (NNReal.coe_nonneg epoch.2) hcont' hforward'
    rw [sub_zero, ← hnext', sum_bumpCapacity, Nat.cast_add, Nat.cast_one] at hlarger
    have hstep := norm_sub_firstOrder_step_le (historyEventPropagator_substochastic capacity rest)
      (historyCorrection model capacity rest) (historyCorrection_sub model capacity rest)
      (norm_historyCorrection_le model hS0 hS capacity rest)
      (mul_nonneg (by positivity) (epochDuration_nonneg rest))
      (norm_selectedHistory_sub_firstOrder_le model hσ hS0 hfit hS capacity family rest (k + 1)
        hrest hrest') hstage hlarger
    have hlength : k + (Sum.inl epoch :: rest).length = k + 1 + rest.length := by
      rw [List.length_cons]
      omega
    rw [hlength, historyEventPropagator, eventPropagator, ← Matrix.mulVec_mulVec,
      historyCorrection, epochDuration]
    exact hstep.trans_eq (by ring)
  | Sum.inr pulse :: rest, k, hhistory, hhistory' => by
    obtain ⟨hnext, hrest⟩ := hhistory
    obtain ⟨hnext', hrest'⟩ := hhistory'
    have hpulse : ∀ capacity' : Locus → ℕ,
        (∀ ξ : BudgetConfiguration Deme Locus Allele capacity',
          expectedMomentVector capacity' (family (k + 1)) 0 ξ
            = family k 0 fun law ↦ configurationMoment (pulsedLaw pulse law) ξ.1) →
        expectedMomentVector capacity' (family (k + 1)) 0
          = pulseKernel pulse capacity' *ᵥ expectedMomentVector capacity' (family k) 0 := by
      intro capacity' hmoments
      funext ξ
      rw [hmoments ξ, pulseKernel_mulVec_expectedMoment]
      rfl
    have h := norm_selectedHistory_sub_firstOrder_le model hσ hS0 hfit hS capacity family rest
      (k + 1) hrest hrest'
    rw [hpulse capacity hnext, hpulse (bumpCapacity model capacity) hnext'] at h
    have hlength : k + (Sum.inr pulse :: rest).length = k + 1 + rest.length := by
      rw [List.length_cons]
      omega
    rw [hlength, historyEventPropagator, eventPropagator, ← Matrix.mulVec_mulVec,
      historyCorrection, epochDuration]
    exact h

/-! ## Linearity in the fitness table -/

/-- The selection model at the same locus with every fitness multiplied by `σ`. -/
def scaledModel (σ : ℝ) (model : SelectionModel Deme Locus Allele) :
    SelectionModel Deme Locus Allele where
  locus := model.locus
  fitness i b := σ * model.fitness i b

/-- Scaling the fitness table scales the rate of every selection term and keeps its gained and
lost configurations. -/
theorem selectionTerms_scaledModel (σ : ℝ) (model : SelectionModel Deme Locus Allele)
    (ξ : Multiset (PartialType Deme Locus Allele)) :
    selectionTerms (scaledModel σ model) ξ
      = (selectionTerms model ξ).map fun term ↦ (σ * term.1, term.2) := by
  rw [selectionTerms, selectionTerms, Multiset.map_bind]
  simp only [Multiset.map_map]
  rfl

/-- **The selection matrix is linear in the fitness table**: scaling every fitness by `σ` scales
every entry by `σ`. -/
theorem selectionMatrix_scaledModel (σ : ℝ) (model : SelectionModel Deme Locus Allele)
    (capacity : Locus → ℕ) (ξ : BudgetConfiguration Deme Locus Allele capacity)
    (η : BudgetConfiguration Deme Locus Allele (bumpCapacity (scaledModel σ model) capacity)) :
    selectionMatrix (scaledModel σ model) capacity ξ η
      = σ * selectionMatrix model capacity ξ η := by
  simp only [selectionMatrix]
  rw [selectionTerms_scaledModel, Multiset.map_map, ← Multiset.sum_map_mul_left]
  refine congrArg Multiset.sum (Multiset.map_congr rfl fun term _ ↦ ?_)
  simp only [Function.comp_apply]
  ring

/-- **The first-order correction of an epoch is linear in the fitness table.** -/
theorem selectionCorrection_scaledModel (rates : NeutralRates Deme Locus Allele) (σ : ℝ)
    (model : SelectionModel Deme Locus Allele) (capacity : Locus → ℕ)
    (w : BudgetConfiguration Deme Locus Allele (bumpCapacity model capacity) → ℝ) (d : ℝ) :
    selectionCorrection rates (scaledModel σ model) capacity w d
      = σ • selectionCorrection rates model capacity w d := by
  have hmatrix : ∀ x : BudgetConfiguration Deme Locus Allele (bumpCapacity model capacity) → ℝ,
      selectionMatrix (scaledModel σ model) capacity *ᵥ x
        = σ • (selectionMatrix model capacity *ᵥ x) := by
    intro x
    funext ξ
    show ∑ η, selectionMatrix (scaledModel σ model) capacity ξ η * x η
      = σ * ∑ η, selectionMatrix model capacity ξ η * x η
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun η _ ↦ by rw [selectionMatrix_scaledModel, mul_assoc]
  rw [selectionCorrection, selectionCorrection, ← intervalIntegral.integral_smul]
  congr 1
  funext t
  show matrixExponential (dualGenerator rates capacity) (d - t)
      *ᵥ (selectionMatrix (scaledModel σ model) capacity
        *ᵥ (matrixExponential (dualGenerator rates (bumpCapacity model capacity)) t *ᵥ w))
    = σ • (matrixExponential (dualGenerator rates capacity) (d - t)
      *ᵥ (selectionMatrix model capacity
        *ᵥ (matrixExponential (dualGenerator rates (bumpCapacity model capacity)) t *ᵥ w)))
  rw [hmatrix, Matrix.mulVec_smul]

/-- **The first-order correction of a history is linear in the fitness table.** -/
theorem historyCorrection_scaledModel (σ : ℝ) (model : SelectionModel Deme Locus Allele)
    (capacity : Locus → ℕ) :
    ∀ (events : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme))
      (w : BudgetConfiguration Deme Locus Allele (bumpCapacity model capacity) → ℝ),
      historyCorrection (scaledModel σ model) capacity events w
        = σ • historyCorrection model capacity events w
  | [], _ => by simp only [historyCorrection, smul_zero]
  | Sum.inl epoch :: rest, w => by
    have hrest := historyCorrection_scaledModel σ model capacity rest
      (matrixExponential (dualGenerator epoch.1 (bumpCapacity model capacity)) epoch.2 *ᵥ w)
    have hstage := selectionCorrection_scaledModel epoch.1 σ model capacity w epoch.2
    show historyEventPropagator capacity rest
          *ᵥ selectionCorrection epoch.1 (scaledModel σ model) capacity w epoch.2
        + historyCorrection (scaledModel σ model) capacity rest
          (matrixExponential (dualGenerator epoch.1 (bumpCapacity model capacity)) epoch.2 *ᵥ w)
      = σ • (historyEventPropagator capacity rest
          *ᵥ selectionCorrection epoch.1 model capacity w epoch.2
        + historyCorrection model capacity rest
          (matrixExponential (dualGenerator epoch.1 (bumpCapacity model capacity)) epoch.2 *ᵥ w))
    rw [hstage, hrest, Matrix.mulVec_smul, smul_add]
  | Sum.inr pulse :: rest, w => by
    show historyCorrection (scaledModel σ model) capacity rest
        (pulseKernel pulse (bumpCapacity model capacity) *ᵥ w)
      = σ • historyCorrection model capacity rest
        (pulseKernel pulse (bumpCapacity model capacity) *ᵥ w)
    exact historyCorrection_scaledModel σ model capacity rest _

/-- **Selection strength to first order along a history.** For the fitness table `σ s`, with `s`
in `[0, 1]` and masses `Σ_b |s_i(b)| ≤ S`, the selected moments at the end of a history equal the
neutral chronological propagator applied to the initial moments plus `σ` times the correction of
the history of `s`, up to `B S B' σ² T²` in sup norm.

Assumes: `SelectedOnHistory (scaledModel σ model) capacity family events 0` and
`SelectedOnHistory (scaledModel σ model) (bumpCapacity model capacity) family events 0`. -/
theorem norm_scaledHistory_sub_firstOrder_le (model : SelectionModel Deme Locus Allele)
    {σ S : ℝ} (hσ : 0 ≤ σ) (hS0 : 0 ≤ S)
    (hfit : ∀ i b, 0 ≤ model.fitness i b ∧ model.fitness i b ≤ 1)
    (hS : ∀ i, ∑ b, |model.fitness i b| ≤ S) (capacity : Locus → ℕ)
    (family : ℕ → ℝ → ExpFunctional (Deme → FiniteReportLaw (FullHaplotype Locus Allele)))
    (events : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme))
    (hhistory : SelectedOnHistory (scaledModel σ model) capacity family events 0)
    (hhistory' : SelectedOnHistory (scaledModel σ model) (bumpCapacity model capacity) family
      events 0) :
    ‖expectedMomentVector capacity (family events.length) 0
        - historyEventPropagator capacity events *ᵥ expectedMomentVector capacity (family 0) 0
        - σ • historyCorrection model capacity events
          (expectedMomentVector (bumpCapacity model capacity) (family 0) 0)‖
      ≤ (∑ ℓ, capacity ℓ : ℕ) * S * ((∑ ℓ, capacity ℓ : ℕ) + 1) * σ ^ 2
        * epochDuration events ^ 2 := by
  have hfit' : ∀ i b, 0 ≤ (scaledModel σ model).fitness i b
      ∧ (scaledModel σ model).fitness i b ≤ σ := fun i b ↦
    ⟨mul_nonneg hσ (hfit i b).1, mul_le_of_le_one_right hσ (hfit i b).2⟩
  have hS' : ∀ i, ∑ b, |(scaledModel σ model).fitness i b| ≤ σ * S := by
    intro i
    show ∑ b, |σ * model.fitness i b| ≤ σ * S
    simp only [abs_mul, abs_of_nonneg hσ, ← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (hS i) hσ
  have h := norm_selectedHistory_sub_firstOrder_le (scaledModel σ model) hσ (mul_nonneg hσ hS0)
    hfit' hS' capacity family events 0 hhistory hhistory'
  have hscale := historyCorrection_scaledModel σ model capacity events
    (expectedMomentVector (bumpCapacity model capacity) (family 0) 0)
  calc ‖expectedMomentVector capacity (family events.length) 0
        - historyEventPropagator capacity events *ᵥ expectedMomentVector capacity (family 0) 0
        - σ • historyCorrection model capacity events
          (expectedMomentVector (bumpCapacity model capacity) (family 0) 0)‖
      = ‖expectedMomentVector capacity (family (0 + events.length)) 0
        - historyEventPropagator capacity events *ᵥ expectedMomentVector capacity (family 0) 0
        - historyCorrection (scaledModel σ model) capacity events
          (expectedMomentVector (bumpCapacity model capacity) (family 0) 0)‖ := by
        rw [hscale, zero_add]
    _ ≤ _ := h
    _ = _ := by ring

end

end Descent.Portability.SelectionHistoryFirstOrder
