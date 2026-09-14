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

Linearity in the fitness table. Scaling every fitness by `σ` scales the selection terms
(`selectionTerms_scaledModel`), the selection matrix (`selectionMatrix_scaledModel`) and so the
correction of an epoch and of a history (`selectionCorrection_scaledModel`,
`historyCorrection_scaledModel`) by `σ`. For the fitness table `σ s`, with `s` in `[0, 1]` and
masses at most `S`, the selected moments are the neutral propagator on the initial moments plus
`σ` times the correction of `s`, up to `B S B' σ² T²` (`norm_scaledHistory_sub_firstOrder_le`). A
quadratic remainder gives a right derivative (`hasDerivWithinAt_of_norm_sub_le_sq`), so the
correction of the history is the derivative of the selected moments in the selection strength at
zero (`hasDerivWithinAt_selectedHistory_firstOrder`).

Portability. The portability of expected accuracies is the cross ratio `N_t D_s / (D_t N_s)` of
four dot products with the moments. With `N = A B` and `M = C D`, the exact identity
`N/M - N₀/M₀ - σ P₁ = ((N - N₀ - σ N₁) M₀ - N₀ (M - M₀ - σ M₁)) / (M M₀) - σ P₁ (M - M₀) / M`
(`crossRatio_sub_firstOrder_eq`), with `P₁` the quotient-rule derivative
`EndToEndSensitivityMetrics.crossRatioDerivative`, puts every term at second order
(`abs_mul_sub_firstOrder_le`, `abs_crossRatio_sub_firstOrder_le`). The factors read the moments
through their coefficient vectors (`dotProduct_firstOrder_bounds`), expected moments lie in the
unit box (`norm_expectedMomentVector_le_one`), the zero-order error is `B σ T`
(`EndToEndSelectionLaw.norm_selectedHistory_sub_propagator_le`) and the correction costs `2 B S T`.
So where the target denominator and the source numerator are at least `δ > 0`, the selected
portability is `P(m₀) + σ P₁`, with `P₁ = portabilityFirstOrder` at the neutral moments `m₀` in the
direction of the correction, up to the explicit `crossRatioRemainder`, of order `σ² T²`
(`abs_selectedPortability_sub_firstOrder_le`); and `P₁` is the right derivative of the selected
portability in `σ` at zero (`hasDerivWithinAt_selectedPortability_firstOrder`). With positive
neutral accuracy components, `P₁ > 0` exactly when the relative first-order change
`N_t₁/N_t - D_t₁/D_t` of the target accuracy exceeds that of the source accuracy
(`crossRatioDerivative_pos_iff_of_pos`, `portabilityFirstOrder_pos_iff`).

Significance. `SelectionMomentExpansion` stops at one epoch and `EndToEndSelectionLaw` at zero
order. Here the first-order effect of weak selection on the moments and on portability, along any
history of epochs, splits and pulses, is a linear functional of the fitness table built from
neutral propagators and matrix-exponential integrals of the selection matrix, with an explicit
remainder, and selection raises portability to first order exactly when it raises the target
accuracy relatively more than the source accuracy.

Scope. The forward moment equation with selection is a hypothesis on the families, at the budget
and at the budget with one more copy at the selected locus, as in `SelectionHistoryMoments` and
`EndToEndSelectionLaw`; the selected diffusion is not constructed. Selection is haploid at one
locus, with one fitness table for the whole history; the derivative and portability statements
scale a table in `[0, 1]`. The portability remainder carries the coefficient masses of the metric
polynomials and needs the lower bound `δ` under the selected families and at the neutral moments.
The expected squared correlation `E[N/D]` itself is not expanded.

## Empirical status

None. The bodies here are norm inequalities for matrix products, integrals of matrix exponentials
and rational functions of supplied values, so no measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.SelectionHistoryFirstOrder

open MvPolynomial Descent.Coalescent Descent.Foundations PartialHaplotypeCarrier
  PartialHaplotypeDualGenerator PartialHaplotypeDualSemigroup SubstochasticGeneratorSemigroup
  PartialHaplotypePulseKernel NeutralPulseHistoryKernel ReplicaMetricInstances
  EndToEndPortabilityLaw SelectionHistoryMoments EndToEndSelectionLaw SelectionMomentExpansion
  EndToEndSensitivityMetrics
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

/-! ## The first-order term as a derivative -/

/-- **A quadratic remainder gives the right derivative at zero.** If
`‖f σ - x₀ - σ • f₁‖ ≤ C σ²` for every `σ ≥ 0`, then `f` has right derivative `f₁` at zero. -/
theorem hasDerivWithinAt_of_norm_sub_le_sq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} {x₀ f₁ : E} {C : ℝ}
    (hbound : ∀ σ, 0 ≤ σ → ‖f σ - x₀ - σ • f₁‖ ≤ C * σ ^ 2) :
    HasDerivWithinAt f f₁ (Set.Ici 0) 0 := by
  have h0 : f 0 = x₀ := by
    have h := hbound 0 le_rfl
    rw [zero_smul, sub_zero, zero_pow two_ne_zero, mul_zero] at h
    exact sub_eq_zero.mp (norm_le_zero_iff.mp h)
  have hbig : Asymptotics.IsBigO (nhdsWithin 0 (Set.Ici 0))
      (fun σ : ℝ ↦ f σ - f 0 - (σ - 0) • f₁) fun σ ↦ σ ^ 2 := by
    refine Asymptotics.IsBigO.of_bound C ?_
    filter_upwards [self_mem_nhdsWithin] with σ hσ
    rw [h0, sub_zero, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg σ)]
    exact hbound σ hσ
  have hsmall : Asymptotics.IsLittleO (nhds (0 : ℝ)) (fun σ : ℝ ↦ σ ^ 2) fun σ ↦ σ :=
    Asymptotics.isLittleO_pow_id (by norm_num)
  rw [hasDerivWithinAt_iff_isLittleO]
  simpa only [sub_zero] using hbig.trans_isLittleO (hsmall.mono nhdsWithin_le_nhds)

/-- **The correction of the history is the derivative in selection strength.** Let `family σ` be
selected along a history for the fitness table `σ s` at every `σ ≥ 0`, with `s` in `[0, 1]` and
masses `Σ_b |s_i(b)| ≤ S`, starting from the same moments `v₀` and `w₀` at both budgets. Then the
moments at the end of the history have right derivative in `σ` at zero equal to the first-order
correction of the history of `s` at `w₀`.

Assumes: `SelectedOnHistory (scaledModel σ model) capacity (family σ) events 0` and
`SelectedOnHistory (scaledModel σ model) (bumpCapacity model capacity) (family σ) events 0` for
every `σ ≥ 0`. -/
theorem hasDerivWithinAt_selectedHistory_firstOrder (model : SelectionModel Deme Locus Allele)
    {S : ℝ} (hS0 : 0 ≤ S) (hfit : ∀ i b, 0 ≤ model.fitness i b ∧ model.fitness i b ≤ 1)
    (hS : ∀ i, ∑ b, |model.fitness i b| ≤ S) (capacity : Locus → ℕ)
    (family : ℝ → ℕ → ℝ → ExpFunctional (Deme → FiniteReportLaw (FullHaplotype Locus Allele)))
    (events : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme))
    (hhistory : ∀ σ, 0 ≤ σ →
      SelectedOnHistory (scaledModel σ model) capacity (family σ) events 0)
    (hhistory' : ∀ σ, 0 ≤ σ →
      SelectedOnHistory (scaledModel σ model) (bumpCapacity model capacity) (family σ) events 0)
    (v₀ : BudgetConfiguration Deme Locus Allele capacity → ℝ)
    (w₀ : BudgetConfiguration Deme Locus Allele (bumpCapacity model capacity) → ℝ)
    (hinitial : ∀ σ, 0 ≤ σ → expectedMomentVector capacity (family σ 0) 0 = v₀)
    (hinitial' : ∀ σ, 0 ≤ σ →
      expectedMomentVector (bumpCapacity model capacity) (family σ 0) 0 = w₀) :
    HasDerivWithinAt (fun σ ↦ expectedMomentVector capacity (family σ events.length) 0)
      (historyCorrection model capacity events w₀) (Set.Ici 0) 0 := by
  refine hasDerivWithinAt_of_norm_sub_le_sq (x₀ := historyEventPropagator capacity events *ᵥ v₀)
    (C := (∑ ℓ, capacity ℓ : ℕ) * S * ((∑ ℓ, capacity ℓ : ℕ) + 1) * epochDuration events ^ 2)
    fun σ hσ ↦ ?_
  have h := norm_scaledHistory_sub_firstOrder_le model hσ hS0 hfit hS capacity (family σ) events
    (hhistory σ hσ) (hhistory' σ hσ)
  rw [hinitial σ hσ, hinitial' σ hσ] at h
  exact h.trans_eq (by ring)

/-! ## The cross ratio to first order -/

/-- `|a b| ≤ x y` from `|a| ≤ x` and `|b| ≤ y`. -/
theorem abs_product_le {a b x y : ℝ} (ha : |a| ≤ x) (hb : |b| ≤ y) : |a * b| ≤ x * y := by
  rw [abs_mul]
  exact mul_le_mul ha hb (abs_nonneg _) ((abs_nonneg _).trans ha)

/-- **A product to first order.** If `A` and `B` have first-order changes `σ A₁` and `σ B₁` with
remainders at most `α e₂` and `β e₂`, `σ A₁` is at most `α e₁`, `B` moves by at most `β e₀`, and
`|A₀| ≤ α`, `|B| ≤ β`, then `A B` has first-order change `σ (A₁ B₀ + A₀ B₁)` with remainder at
most `α β (2 e₂ + e₀ e₁)`. -/
theorem abs_mul_sub_firstOrder_le {A B A₀ B₀ A₁ B₁ σ α β e₀ e₁ e₂ : ℝ} (hB : |B| ≤ β)
    (hA₀ : |A₀| ≤ α) (hΔB : |B - B₀| ≤ β * e₀) (hA₁ : |σ * A₁| ≤ α * e₁)
    (hρA : |A - A₀ - σ * A₁| ≤ α * e₂) (hρB : |B - B₀ - σ * B₁| ≤ β * e₂) :
    |A * B - A₀ * B₀ - σ * (A₁ * B₀ + A₀ * B₁)| ≤ α * β * (2 * e₂ + e₀ * e₁) := by
  have hsplit : A * B - A₀ * B₀ - σ * (A₁ * B₀ + A₀ * B₁)
      = (A - A₀ - σ * A₁) * B + σ * A₁ * (B - B₀) + A₀ * (B - B₀ - σ * B₁) := by ring
  rw [hsplit]
  calc _ ≤ |(A - A₀ - σ * A₁) * B + σ * A₁ * (B - B₀)| + |A₀ * (B - B₀ - σ * B₁)| :=
        abs_add_le _ _
    _ ≤ |(A - A₀ - σ * A₁) * B| + |σ * A₁ * (B - B₀)| + |A₀ * (B - B₀ - σ * B₁)| :=
        add_le_add_right (abs_add_le _ _) _
    _ ≤ α * e₂ * β + α * e₁ * (β * e₀) + α * (β * e₂) :=
        add_le_add (add_le_add (abs_product_le hρA hB) (abs_product_le hA₁ hΔB))
          (abs_product_le hA₀ hρB)
    _ = α * β * (2 * e₂ + e₀ * e₁) := by ring

/-- **The cross ratio to first order, exactly.** With `N = A B`, `M = C D` and `P₁` the
cross-ratio derivative at `(A₀, B₀, C₀, D₀)` in the direction `(A₁, B₁, C₁, D₁)`,
`N/M - N₀/M₀ - σ P₁ = ((N - N₀ - σ N₁) M₀ - N₀ (M - M₀ - σ M₁)) / (M M₀) - σ P₁ (M - M₀) / M`,
where `N₁ = A₁ B₀ + A₀ B₁` and `M₁ = C₁ D₀ + C₀ D₁`. -/
theorem crossRatio_sub_firstOrder_eq {A B C D A₀ B₀ C₀ D₀ A₁ B₁ C₁ D₁ σ : ℝ} (hC : C ≠ 0)
    (hD : D ≠ 0) (hC₀ : C₀ ≠ 0) (hD₀ : D₀ ≠ 0) :
    A * B / (C * D) - A₀ * B₀ / (C₀ * D₀) - σ * crossRatioDerivative A₀ B₀ C₀ D₀ A₁ B₁ C₁ D₁
      = ((A * B - A₀ * B₀ - σ * (A₁ * B₀ + A₀ * B₁)) * (C₀ * D₀)
          - A₀ * B₀ * (C * D - C₀ * D₀ - σ * (C₁ * D₀ + C₀ * D₁))) / (C * D * (C₀ * D₀))
        - σ * crossRatioDerivative A₀ B₀ C₀ D₀ A₁ B₁ C₁ D₁ * (C * D - C₀ * D₀) / (C * D) := by
  rw [crossRatioDerivative]
  field_simp
  ring

/-- **The cross ratio to first order, with a remainder.** Let the factors `X ∈ {A, B, C, D}` of a
cross ratio have masses `x ∈ {α, β, γ, κ}`: the neutral values and the selected `B` and `D` are at
most their masses, the selected changes of `B, C, D` at most `x e₀`, the first-order changes
`σ X₁` at most `x e₁`, and the remainders `X - X₀ - σ X₁` at most `x e₂`. Where
`C, D, C₀, D₀ ≥ δ > 0`, the cross ratio has first-order change `σ P₁`, with `P₁` the cross-ratio
derivative, and remainder at most
`2 α β γ κ (2 e₂ + e₀ e₁) / δ⁴ + 8 α β γ² κ² e₀ e₁ / δ⁶`. -/
theorem abs_crossRatio_sub_firstOrder_le
    {A B C D A₀ B₀ C₀ D₀ A₁ B₁ C₁ D₁ σ α β γ κ e₀ e₁ e₂ δ : ℝ} (hδ : 0 < δ) (hC : δ ≤ C)
    (hD : δ ≤ D) (hC₀ : δ ≤ C₀) (hD₀ : δ ≤ D₀) (hB : |B| ≤ β) (hDκ : |D| ≤ κ)
    (hA₀ : |A₀| ≤ α) (hB₀ : |B₀| ≤ β) (hC₀γ : |C₀| ≤ γ) (hD₀κ : |D₀| ≤ κ)
    (hΔB : |B - B₀| ≤ β * e₀) (hΔC : |C - C₀| ≤ γ * e₀) (hΔD : |D - D₀| ≤ κ * e₀)
    (hA₁ : |σ * A₁| ≤ α * e₁) (hB₁ : |σ * B₁| ≤ β * e₁) (hC₁ : |σ * C₁| ≤ γ * e₁)
    (hD₁ : |σ * D₁| ≤ κ * e₁) (hρA : |A - A₀ - σ * A₁| ≤ α * e₂)
    (hρB : |B - B₀ - σ * B₁| ≤ β * e₂) (hρC : |C - C₀ - σ * C₁| ≤ γ * e₂)
    (hρD : |D - D₀ - σ * D₁| ≤ κ * e₂) :
    |A * B / (C * D) - A₀ * B₀ / (C₀ * D₀) - σ * crossRatioDerivative A₀ B₀ C₀ D₀ A₁ B₁ C₁ D₁|
      ≤ 2 * α * β * γ * κ * (2 * e₂ + e₀ * e₁) / δ ^ 4
        + 8 * α * β * γ ^ 2 * κ ^ 2 * (e₀ * e₁) / δ ^ 6 := by
  have hCpos := hδ.trans_le hC
  have hDpos := hδ.trans_le hD
  have hC₀pos := hδ.trans_le hC₀
  have hD₀pos := hδ.trans_le hD₀
  have hMpos : 0 < C * D := mul_pos hCpos hDpos
  have hM₀pos : 0 < C₀ * D₀ := mul_pos hC₀pos hD₀pos
  have hM : δ ^ 2 ≤ C * D := (sq δ).trans_le (mul_le_mul hC hD hδ.le hCpos.le)
  have hM₀ : δ ^ 2 ≤ C₀ * D₀ := (sq δ).trans_le (mul_le_mul hC₀ hD₀ hδ.le hC₀pos.le)
  have hsquare : δ ^ 4 ≤ (C₀ * D₀) ^ 2 := by
    calc δ ^ 4 = δ ^ 2 * δ ^ 2 := by ring
      _ ≤ (C₀ * D₀) * (C₀ * D₀) := mul_le_mul hM₀ hM₀ (by positivity) hM₀pos.le
      _ = (C₀ * D₀) ^ 2 := by ring
  have hden : δ ^ 4 ≤ C * D * (C₀ * D₀) := by
    calc δ ^ 4 = δ ^ 2 * δ ^ 2 := by ring
      _ ≤ C * D * (C₀ * D₀) := mul_le_mul hM hM₀ (by positivity) hMpos.le
  have hΔM : |C * D - C₀ * D₀| ≤ 2 * γ * κ * e₀ := by
    have hsplit : C * D - C₀ * D₀ = (C - C₀) * D + C₀ * (D - D₀) := by ring
    rw [hsplit]
    calc _ ≤ |(C - C₀) * D| + |C₀ * (D - D₀)| := abs_add_le _ _
      _ ≤ γ * e₀ * κ + γ * (κ * e₀) :=
          add_le_add (abs_product_le hΔC hDκ) (abs_product_le hC₀γ hΔD)
      _ = 2 * γ * κ * e₀ := by ring
  have hP₁ : |σ * crossRatioDerivative A₀ B₀ C₀ D₀ A₁ B₁ C₁ D₁|
      ≤ 4 * α * β * γ * κ * e₁ / δ ^ 4 := by
    have hform : σ * crossRatioDerivative A₀ B₀ C₀ D₀ A₁ B₁ C₁ D₁
        = ((σ * A₁ * B₀ + A₀ * (σ * B₁)) * (C₀ * D₀)
          - A₀ * B₀ * (σ * C₁ * D₀ + C₀ * (σ * D₁))) / (C₀ * D₀) ^ 2 := by
      rw [crossRatioDerivative]
      ring
    have hN₁ : |σ * A₁ * B₀ + A₀ * (σ * B₁)| ≤ α * e₁ * β + α * (β * e₁) :=
      (abs_add_le _ _).trans (add_le_add (abs_product_le hA₁ hB₀) (abs_product_le hA₀ hB₁))
    have hM₁ : |σ * C₁ * D₀ + C₀ * (σ * D₁)| ≤ γ * e₁ * κ + γ * (κ * e₁) :=
      (abs_add_le _ _).trans (add_le_add (abs_product_le hC₁ hD₀κ) (abs_product_le hC₀γ hD₁))
    have hnum : |(σ * A₁ * B₀ + A₀ * (σ * B₁)) * (C₀ * D₀)
        - A₀ * B₀ * (σ * C₁ * D₀ + C₀ * (σ * D₁))| ≤ 4 * α * β * γ * κ * e₁ := by
      calc _ ≤ |(σ * A₁ * B₀ + A₀ * (σ * B₁)) * (C₀ * D₀)|
            + |A₀ * B₀ * (σ * C₁ * D₀ + C₀ * (σ * D₁))| := abs_sub _ _
        _ ≤ (α * e₁ * β + α * (β * e₁)) * (γ * κ) + α * β * (γ * e₁ * κ + γ * (κ * e₁)) :=
            add_le_add (abs_product_le hN₁ (abs_product_le hC₀γ hD₀κ))
              (abs_product_le (abs_product_le hA₀ hB₀) hM₁)
        _ = 4 * α * β * γ * κ * e₁ := by ring
    rw [hform, abs_div, abs_of_pos (pow_pos hM₀pos 2),
      div_le_div_iff₀ (pow_pos hM₀pos 2) (pow_pos hδ 4)]
    exact mul_le_mul hnum hsquare (by positivity) ((abs_nonneg _).trans hnum)
  have hT1 : |((A * B - A₀ * B₀ - σ * (A₁ * B₀ + A₀ * B₁)) * (C₀ * D₀)
        - A₀ * B₀ * (C * D - C₀ * D₀ - σ * (C₁ * D₀ + C₀ * D₁))) / (C * D * (C₀ * D₀))|
      ≤ 2 * α * β * γ * κ * (2 * e₂ + e₀ * e₁) / δ ^ 4 := by
    have hnum : |(A * B - A₀ * B₀ - σ * (A₁ * B₀ + A₀ * B₁)) * (C₀ * D₀)
        - A₀ * B₀ * (C * D - C₀ * D₀ - σ * (C₁ * D₀ + C₀ * D₁))|
        ≤ 2 * α * β * γ * κ * (2 * e₂ + e₀ * e₁) := by
      calc _ ≤ |(A * B - A₀ * B₀ - σ * (A₁ * B₀ + A₀ * B₁)) * (C₀ * D₀)|
            + |A₀ * B₀ * (C * D - C₀ * D₀ - σ * (C₁ * D₀ + C₀ * D₁))| := abs_sub _ _
        _ ≤ α * β * (2 * e₂ + e₀ * e₁) * (γ * κ) + α * β * (γ * κ * (2 * e₂ + e₀ * e₁)) :=
            add_le_add
              (abs_product_le (abs_mul_sub_firstOrder_le hB hA₀ hΔB hA₁ hρA hρB)
                (abs_product_le hC₀γ hD₀κ))
              (abs_product_le (abs_product_le hA₀ hB₀)
                (abs_mul_sub_firstOrder_le hDκ hC₀γ hΔD hC₁ hρC hρD))
        _ = 2 * α * β * γ * κ * (2 * e₂ + e₀ * e₁) := by ring
    rw [abs_div, abs_of_pos (mul_pos hMpos hM₀pos),
      div_le_div_iff₀ (mul_pos hMpos hM₀pos) (pow_pos hδ 4)]
    exact mul_le_mul hnum hden (by positivity) ((abs_nonneg _).trans hnum)
  have hT2 : |σ * crossRatioDerivative A₀ B₀ C₀ D₀ A₁ B₁ C₁ D₁ * (C * D - C₀ * D₀) / (C * D)|
      ≤ 8 * α * β * γ ^ 2 * κ ^ 2 * (e₀ * e₁) / δ ^ 6 := by
    have hprod := abs_product_le hP₁ hΔM
    rw [abs_div, abs_of_pos hMpos]
    calc _ ≤ 4 * α * β * γ * κ * e₁ / δ ^ 4 * (2 * γ * κ * e₀) / δ ^ 2 := by
          rw [div_le_div_iff₀ hMpos (pow_pos hδ 2)]
          exact mul_le_mul hprod hM (by positivity) ((abs_nonneg _).trans hprod)
      _ = 8 * α * β * γ ^ 2 * κ ^ 2 * (e₀ * e₁) / δ ^ 6 := by ring
  rw [crossRatio_sub_firstOrder_eq hCpos.ne' hDpos.ne' hC₀pos.ne' hD₀pos.ne']
  exact (abs_sub _ _).trans (add_le_add hT1 hT2)

/-- **The sign criterion in relative changes.** For positive factors, a cross ratio `a b / (c d)`
increases to first order exactly when the relative first-order change of `a / c` exceeds that of
`d / b`. -/
theorem crossRatioDerivative_pos_iff_of_pos {a b c d : ℝ} (a' b' c' d' : ℝ) (ha : 0 < a)
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    0 < crossRatioDerivative a b c d a' b' c' d' ↔ d' / d - b' / b < a' / a - c' / c := by
  rw [crossRatioDerivative_eq_mul a' b' c' d' ha.ne' hb.ne' hc.ne' hd.ne',
    mul_pos_iff_of_pos_left (by positivity)]
  constructor <;> intro h <;> linarith

/-! ## Portability to first order -/

/-- A dot product is at most the coefficient mass times the sup norm of the vector. -/
theorem abs_dotProduct_le_mass_mul_norm {ι : Type*} [Fintype ι] (c v : ι → ℝ) :
    |c ⬝ᵥ v| ≤ (∑ i, |c i|) * ‖v‖ := by
  simpa only [dotProduct_zero, sub_zero] using
    PortabilityMetricCompilation.abs_dotProduct_sub_le c v 0

/-- **One factor to first order.** For a coefficient vector `c` and moment vectors with
`‖V‖, ‖m₀‖ ≤ 1`, `‖V - m₀‖ ≤ e₀`, `‖σ • m₁‖ ≤ e₁` and `‖V - m₀ - σ • m₁‖ ≤ e₂`, the dot products
with `c` are bounded by the mass `‖c‖₁` in the form `abs_crossRatio_sub_firstOrder_le` reads. -/
theorem dotProduct_firstOrder_bounds {ι : Type*} [Fintype ι] (c : ι → ℝ) {V m₀ m₁ : ι → ℝ}
    {σ e₀ e₁ e₂ : ℝ} (hV : ‖V‖ ≤ 1) (hm₀ : ‖m₀‖ ≤ 1) (h₀ : ‖V - m₀‖ ≤ e₀)
    (h₁ : ‖σ • m₁‖ ≤ e₁) (h₂ : ‖V - m₀ - σ • m₁‖ ≤ e₂) :
    |c ⬝ᵥ V| ≤ ∑ i, |c i| ∧ |c ⬝ᵥ m₀| ≤ ∑ i, |c i|
      ∧ |c ⬝ᵥ V - c ⬝ᵥ m₀| ≤ (∑ i, |c i|) * e₀ ∧ |σ * (c ⬝ᵥ m₁)| ≤ (∑ i, |c i|) * e₁
      ∧ |c ⬝ᵥ V - c ⬝ᵥ m₀ - σ * (c ⬝ᵥ m₁)| ≤ (∑ i, |c i|) * e₂ := by
  have hmass : 0 ≤ ∑ i, |c i| := Finset.sum_nonneg fun i _ ↦ abs_nonneg (c i)
  have hbound : ∀ (v : ι → ℝ) (e : ℝ), ‖v‖ ≤ e → |c ⬝ᵥ v| ≤ (∑ i, |c i|) * e := fun v _ hv ↦
    (abs_dotProduct_le_mass_mul_norm c v).trans (mul_le_mul_of_nonneg_left hv hmass)
  have hsmul : σ * (c ⬝ᵥ m₁) = c ⬝ᵥ (σ • m₁) := by rw [dotProduct_smul, smul_eq_mul]
  refine ⟨(hbound V 1 hV).trans_eq (mul_one _), (hbound m₀ 1 hm₀).trans_eq (mul_one _), ?_, ?_,
    ?_⟩
  · rw [← dotProduct_sub]
    exact hbound _ _ h₀
  · rw [hsmul]
    exact hbound _ _ h₁
  · rw [hsmul, ← dotProduct_sub, ← dotProduct_sub]
    exact hbound _ _ h₂

/-- Every expected configuration moment lies in `[0, 1]`, so an expected moment vector has sup norm
at most one. -/
theorem norm_expectedMomentVector_le_one (capacity : Locus → ℕ)
    (expectationAt : ℝ → ExpFunctional (Deme → FiniteReportLaw (FullHaplotype Locus Allele)))
    (s : ℝ) : ‖expectedMomentVector capacity expectationAt s‖ ≤ 1 := by
  refine (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun ξ ↦ ?_
  have hlow : 0 ≤ expectedMomentVector capacity expectationAt s ξ :=
    (expectationAt s).nonneg_eval _ fun law ↦
      PartialHaplotypeCarrier.configurationMoment_nonneg law ξ.1
  have hhigh : expectedMomentVector capacity expectationAt s ξ ≤ 1 :=
    ((expectationAt s).eval_mono fun law ↦ configurationMoment_le_one law ξ.1).trans_eq
      ((expectationAt s).eval_const 1)
  rw [Real.norm_eq_abs, abs_of_nonneg hlow]
  exact hhigh

/-- The coefficient mass `‖c‖₁` of a frequency polynomial over the budget-4 configurations. -/
def coefficientMass (ℓ₀ : Locus) (p : FrequencyPolynomial Deme Locus Allele) : ℝ :=
  ∑ i, |budgetCoefficients ℓ₀ (fun _ ↦ 4) p i|

/-- The remainder of the cross ratio to first order,
`2 α β γ κ (2 e₂ + e₀ e₁) / δ⁴ + 8 α β γ² κ² e₀ e₁ / δ⁶`. -/
def crossRatioRemainder (α β γ κ e₀ e₁ e₂ δ : ℝ) : ℝ :=
  2 * α * β * γ * κ * (2 * e₂ + e₀ * e₁) / δ ^ 4
    + 8 * α * β * γ ^ 2 * κ ^ 2 * (e₀ * e₁) / δ ^ 6

/-- **The first-order portability correction**: the cross-ratio derivative of the target
numerator and source denominator over the target denominator and source numerator, at budget-4
moments `m₀` in the direction `m₁`. -/
def portabilityFirstOrder (ℓ₀ : Locus) (source target : Deme)
    (score outcome : FullHaplotype Locus Allele → ℝ)
    (m₀ m₁ : BudgetConfiguration Deme Locus Allele (fun _ ↦ 4) → ℝ) : ℝ :=
  crossRatioDerivative
    (budgetCoefficients ℓ₀ (fun _ ↦ 4) (numeratorPolynomial target score outcome) ⬝ᵥ m₀)
    (budgetCoefficients ℓ₀ (fun _ ↦ 4) (denominatorPolynomial source score outcome) ⬝ᵥ m₀)
    (budgetCoefficients ℓ₀ (fun _ ↦ 4) (denominatorPolynomial target score outcome) ⬝ᵥ m₀)
    (budgetCoefficients ℓ₀ (fun _ ↦ 4) (numeratorPolynomial source score outcome) ⬝ᵥ m₀)
    (budgetCoefficients ℓ₀ (fun _ ↦ 4) (numeratorPolynomial target score outcome) ⬝ᵥ m₁)
    (budgetCoefficients ℓ₀ (fun _ ↦ 4) (denominatorPolynomial source score outcome) ⬝ᵥ m₁)
    (budgetCoefficients ℓ₀ (fun _ ↦ 4) (denominatorPolynomial target score outcome) ⬝ᵥ m₁)
    (budgetCoefficients ℓ₀ (fun _ ↦ 4) (numeratorPolynomial source score outcome) ⬝ᵥ m₁)

/-- **Selection raises portability to first order exactly when the target gains more.** Where the
target and source accuracy components are positive at `m₀`, the first-order portability correction
is positive exactly when the relative first-order change `N_t₁/N_t - D_t₁/D_t` of the target
accuracy exceeds the relative first-order change `N_s₁/N_s - D_s₁/D_s` of the source accuracy. -/
theorem portabilityFirstOrder_pos_iff (ℓ₀ : Locus) (source target : Deme)
    (score outcome : FullHaplotype Locus Allele → ℝ)
    (m₀ m₁ : BudgetConfiguration Deme Locus Allele (fun _ ↦ 4) → ℝ)
    (hNt : 0 < budgetCoefficients ℓ₀ (fun _ ↦ 4) (numeratorPolynomial target score outcome) ⬝ᵥ m₀)
    (hDs : 0 < budgetCoefficients ℓ₀ (fun _ ↦ 4) (denominatorPolynomial source score outcome)
      ⬝ᵥ m₀)
    (hDt : 0 < budgetCoefficients ℓ₀ (fun _ ↦ 4) (denominatorPolynomial target score outcome)
      ⬝ᵥ m₀)
    (hNs : 0 < budgetCoefficients ℓ₀ (fun _ ↦ 4) (numeratorPolynomial source score outcome)
      ⬝ᵥ m₀) :
    0 < portabilityFirstOrder ℓ₀ source target score outcome m₀ m₁
      ↔ budgetCoefficients ℓ₀ (fun _ ↦ 4) (numeratorPolynomial source score outcome) ⬝ᵥ m₁
            / budgetCoefficients ℓ₀ (fun _ ↦ 4) (numeratorPolynomial source score outcome) ⬝ᵥ m₀
          - budgetCoefficients ℓ₀ (fun _ ↦ 4) (denominatorPolynomial source score outcome) ⬝ᵥ m₁
            / budgetCoefficients ℓ₀ (fun _ ↦ 4) (denominatorPolynomial source score outcome)
              ⬝ᵥ m₀
        < budgetCoefficients ℓ₀ (fun _ ↦ 4) (numeratorPolynomial target score outcome) ⬝ᵥ m₁
            / budgetCoefficients ℓ₀ (fun _ ↦ 4) (numeratorPolynomial target score outcome) ⬝ᵥ m₀
          - budgetCoefficients ℓ₀ (fun _ ↦ 4) (denominatorPolynomial target score outcome) ⬝ᵥ m₁
            / budgetCoefficients ℓ₀ (fun _ ↦ 4) (denominatorPolynomial target score outcome)
              ⬝ᵥ m₀ :=
  crossRatioDerivative_pos_iff_of_pos _ _ _ _ hNt hDs hDt hNs

/-- **Portability to first order in selection along a history.** For the fitness table `σ s`,
with `s` in `[0, 1]` and masses `Σ_b |s_i(b)| ≤ S`, let `m₀` be the neutral chronological
propagator applied to the initial budget-4 moments and `m₁` the first-order correction of the
history of `s` at the initial moments of the larger budget. Where the target denominator and the
source numerator are at least `δ > 0` under the selected family and at `m₀`, the portability of
expected accuracies of the selected history is `P(m₀) + σ P₁`, with `P₁ = portabilityFirstOrder`,
up to `crossRatioRemainder α β γ κ e₀ e₁ e₂ δ`. Here `α, β, γ, κ` are the coefficient masses of the
target numerator, source denominator, target denominator and source numerator,
`e₀ = B σ T`, `e₁ = 2 B S T σ`, `e₂ = B S (B + 1) σ² T²` and `B = 4 |L|`, so the remainder is of
order `σ² T²`.

Assumes: `SelectedOnHistory (scaledModel σ model) (fun _ ↦ 4) family events 0` and
`SelectedOnHistory (scaledModel σ model) (bumpCapacity model (fun _ ↦ 4)) family events 0`. -/
theorem abs_selectedPortability_sub_firstOrder_le (ℓ₀ : Locus)
    (model : SelectionModel Deme Locus Allele) {σ S δ : ℝ} (hσ : 0 ≤ σ) (hS0 : 0 ≤ S)
    (hfit : ∀ i b, 0 ≤ model.fitness i b ∧ model.fitness i b ≤ 1)
    (hS : ∀ i, ∑ b, |model.fitness i b| ≤ S)
    (family : ℕ → ℝ → ExpFunctional (Deme → FiniteReportLaw (FullHaplotype Locus Allele)))
    (events : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme))
    (hhistory : SelectedOnHistory (scaledModel σ model) (fun _ ↦ 4) family events 0)
    (hhistory' : SelectedOnHistory (scaledModel σ model) (bumpCapacity model (fun _ ↦ 4))
      family events 0)
    (source target : Deme) (score outcome : FullHaplotype Locus Allele → ℝ) (hδ : 0 < δ)
    (htarget : δ ≤ family events.length 0 fun law ↦
      correlationDenominator (law target) score outcome)
    (hsource : δ ≤ family events.length 0 fun law ↦
      correlationNumerator (law source) score outcome)
    (htarget₀ : δ ≤ budgetCoefficients ℓ₀ (fun _ ↦ 4) (denominatorPolynomial target score outcome)
      ⬝ᵥ (historyEventPropagator (fun _ ↦ 4) events
        *ᵥ expectedMomentVector (fun _ ↦ 4) (family 0) 0))
    (hsource₀ : δ ≤ budgetCoefficients ℓ₀ (fun _ ↦ 4) (numeratorPolynomial source score outcome)
      ⬝ᵥ (historyEventPropagator (fun _ ↦ 4) events
        *ᵥ expectedMomentVector (fun _ ↦ 4) (family 0) 0)) :
    |selectedPortability family events.length source target score outcome
        - momentPortability ℓ₀ source target score outcome
          (historyEventPropagator (fun _ ↦ 4) events
            *ᵥ expectedMomentVector (fun _ ↦ 4) (family 0) 0)
        - σ * portabilityFirstOrder ℓ₀ source target score outcome
          (historyEventPropagator (fun _ ↦ 4) events
            *ᵥ expectedMomentVector (fun _ ↦ 4) (family 0) 0)
          (historyCorrection model (fun _ ↦ 4) events
            (expectedMomentVector (bumpCapacity model (fun _ ↦ 4)) (family 0) 0))|
      ≤ crossRatioRemainder (coefficientMass ℓ₀ (numeratorPolynomial target score outcome))
          (coefficientMass ℓ₀ (denominatorPolynomial source score outcome))
          (coefficientMass ℓ₀ (denominatorPolynomial target score outcome))
          (coefficientMass ℓ₀ (numeratorPolynomial source score outcome))
          (4 * Fintype.card Locus * σ * epochDuration events)
          (2 * (4 * Fintype.card Locus) * S * epochDuration events * σ)
          (4 * Fintype.card Locus * S * (4 * Fintype.card Locus + 1) * σ ^ 2
            * epochDuration events ^ 2) δ := by
  have hfit' : ∀ i b, 0 ≤ (scaledModel σ model).fitness i b
      ∧ (scaledModel σ model).fitness i b ≤ σ := fun i b ↦
    ⟨mul_nonneg hσ (hfit i b).1, mul_le_of_le_one_right hσ (hfit i b).2⟩
  have hV := norm_expectedMomentVector_le_one (fun _ ↦ 4) (family events.length) 0
  have hm₀ := (norm_mulVec_le_of_substochastic
    (historyEventPropagator_substochastic (fun _ ↦ 4) events)
      (expectedMomentVector (fun _ ↦ 4) (family 0) 0)).trans
        (norm_expectedMomentVector_le_one (fun _ ↦ 4) (family 0) 0)
  have h₀ := norm_selectedHistory_sub_propagator_le (scaledModel σ model) hσ hfit' (fun _ ↦ 4)
    family events 0 hhistory
  rw [zero_add, sum_four_capacity] at h₀
  have h₁ : ‖σ • historyCorrection model (fun _ ↦ 4) events
      (expectedMomentVector (bumpCapacity model (fun _ ↦ 4)) (family 0) 0)‖
      ≤ 2 * (4 * Fintype.card Locus) * S * epochDuration events * σ := by
    have h := norm_historyCorrection_le model hS0 hS (fun _ ↦ 4) events
      (expectedMomentVector (bumpCapacity model (fun _ ↦ 4)) (family 0) 0)
    rw [sum_four_capacity] at h
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hσ]
    exact (mul_comm σ _).trans_le (mul_le_mul_of_nonneg_right (h.trans (mul_le_of_le_one_right
      (mul_nonneg (by positivity) (epochDuration_nonneg events))
      (norm_expectedMomentVector_le_one _ (family 0) 0))) hσ)
  have h₂ := norm_scaledHistory_sub_firstOrder_le model hσ hS0 hfit hS (fun _ ↦ 4) family events
    hhistory hhistory'
  rw [sum_four_capacity] at h₂
  have hC : δ ≤ budgetCoefficients ℓ₀ (fun _ ↦ 4) (denominatorPolynomial target score outcome)
      ⬝ᵥ expectedMomentVector (fun _ ↦ 4) (family events.length) 0 := by
    rw [expectation_correlationDenominator ℓ₀] at htarget
    exact htarget
  have hD : δ ≤ budgetCoefficients ℓ₀ (fun _ ↦ 4) (numeratorPolynomial source score outcome)
      ⬝ᵥ expectedMomentVector (fun _ ↦ 4) (family events.length) 0 := by
    rw [expectation_correlationNumerator ℓ₀] at hsource
    exact hsource
  obtain ⟨-, hA₀, -, hA₁, hρA⟩ := dotProduct_firstOrder_bounds
    (budgetCoefficients ℓ₀ (fun _ ↦ 4) (numeratorPolynomial target score outcome))
    hV hm₀ h₀ h₁ h₂
  obtain ⟨hB, hB₀, hΔB, hB₁, hρB⟩ := dotProduct_firstOrder_bounds
    (budgetCoefficients ℓ₀ (fun _ ↦ 4) (denominatorPolynomial source score outcome))
    hV hm₀ h₀ h₁ h₂
  obtain ⟨-, hC₀, hΔC, hC₁, hρC⟩ := dotProduct_firstOrder_bounds
    (budgetCoefficients ℓ₀ (fun _ ↦ 4) (denominatorPolynomial target score outcome))
    hV hm₀ h₀ h₁ h₂
  obtain ⟨hDκ, hD₀, hΔD, hD₁, hρD⟩ := dotProduct_firstOrder_bounds
    (budgetCoefficients ℓ₀ (fun _ ↦ 4) (numeratorPolynomial source score outcome))
    hV hm₀ h₀ h₁ h₂
  rw [selectedPortability_eq_momentPortability ℓ₀]
  exact abs_crossRatio_sub_firstOrder_le hδ hC hD htarget₀ hsource₀ hB hDκ hA₀ hB₀ hC₀ hD₀ hΔB
    hΔC hΔD hA₁ hB₁ hC₁ hD₁ hρA hρB hρC hρD

/-- **The first-order portability correction is the derivative in selection strength.** Let
`family σ` be selected along a history for the fitness table `σ s` at every `σ ≥ 0`, with `s` in
`[0, 1]`, starting from the same moments `v₀` and `w₀` at both budgets, with target denominator
and source numerator at least `δ > 0` under every `family σ` and at the neutral moments `m₀`. Then
the portability of expected accuracies of the selected history has right derivative in `σ` at
zero equal to `portabilityFirstOrder` at `m₀` in the direction of the correction of the history.

Assumes: `SelectedOnHistory (scaledModel σ model) (fun _ ↦ 4) (family σ) events 0` and
`SelectedOnHistory (scaledModel σ model) (bumpCapacity model (fun _ ↦ 4)) (family σ) events 0`
for every `σ ≥ 0`. -/
theorem hasDerivWithinAt_selectedPortability_firstOrder (ℓ₀ : Locus)
    (model : SelectionModel Deme Locus Allele) {S δ : ℝ} (hS0 : 0 ≤ S)
    (hfit : ∀ i b, 0 ≤ model.fitness i b ∧ model.fitness i b ≤ 1)
    (hS : ∀ i, ∑ b, |model.fitness i b| ≤ S)
    (family : ℝ → ℕ → ℝ → ExpFunctional (Deme → FiniteReportLaw (FullHaplotype Locus Allele)))
    (events : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme))
    (hhistory : ∀ σ, 0 ≤ σ →
      SelectedOnHistory (scaledModel σ model) (fun _ ↦ 4) (family σ) events 0)
    (hhistory' : ∀ σ, 0 ≤ σ → SelectedOnHistory (scaledModel σ model)
      (bumpCapacity model (fun _ ↦ 4)) (family σ) events 0)
    (v₀ : BudgetConfiguration Deme Locus Allele (fun _ ↦ 4) → ℝ)
    (w₀ : BudgetConfiguration Deme Locus Allele (bumpCapacity model (fun _ ↦ 4)) → ℝ)
    (hinitial : ∀ σ, 0 ≤ σ → expectedMomentVector (fun _ ↦ 4) (family σ 0) 0 = v₀)
    (hinitial' : ∀ σ, 0 ≤ σ →
      expectedMomentVector (bumpCapacity model (fun _ ↦ 4)) (family σ 0) 0 = w₀)
    (source target : Deme) (score outcome : FullHaplotype Locus Allele → ℝ) (hδ : 0 < δ)
    (htarget : ∀ σ, 0 ≤ σ → δ ≤ family σ events.length 0 fun law ↦
      correlationDenominator (law target) score outcome)
    (hsource : ∀ σ, 0 ≤ σ → δ ≤ family σ events.length 0 fun law ↦
      correlationNumerator (law source) score outcome)
    (htarget₀ : δ ≤ budgetCoefficients ℓ₀ (fun _ ↦ 4) (denominatorPolynomial target score outcome)
      ⬝ᵥ (historyEventPropagator (fun _ ↦ 4) events *ᵥ v₀))
    (hsource₀ : δ ≤ budgetCoefficients ℓ₀ (fun _ ↦ 4) (numeratorPolynomial source score outcome)
      ⬝ᵥ (historyEventPropagator (fun _ ↦ 4) events *ᵥ v₀)) :
    HasDerivWithinAt
      (fun σ ↦ selectedPortability (family σ) events.length source target score outcome)
      (portabilityFirstOrder ℓ₀ source target score outcome
        (historyEventPropagator (fun _ ↦ 4) events *ᵥ v₀)
        (historyCorrection model (fun _ ↦ 4) events w₀)) (Set.Ici 0) 0 := by
  refine hasDerivWithinAt_of_norm_sub_le_sq
    (x₀ := momentPortability ℓ₀ source target score outcome
      (historyEventPropagator (fun _ ↦ 4) events *ᵥ v₀))
    (C := crossRatioRemainder (coefficientMass ℓ₀ (numeratorPolynomial target score outcome))
      (coefficientMass ℓ₀ (denominatorPolynomial source score outcome))
      (coefficientMass ℓ₀ (denominatorPolynomial target score outcome))
      (coefficientMass ℓ₀ (numeratorPolynomial source score outcome))
      (4 * Fintype.card Locus * epochDuration events)
      (2 * (4 * Fintype.card Locus) * S * epochDuration events)
      (4 * Fintype.card Locus * S * (4 * Fintype.card Locus + 1) * epochDuration events ^ 2) δ)
    fun σ hσ ↦ ?_
  have h := abs_selectedPortability_sub_firstOrder_le ℓ₀ model hσ hS0 hfit hS (family σ) events
    (hhistory σ hσ) (hhistory' σ hσ) source target score outcome hδ (htarget σ hσ)
    (hsource σ hσ) (by rw [hinitial σ hσ]; exact htarget₀) (by rw [hinitial σ hσ]; exact hsource₀)
  rw [hinitial σ hσ, hinitial' σ hσ] at h
  rw [Real.norm_eq_abs, smul_eq_mul]
  refine h.trans_eq ?_
  simp only [crossRatioRemainder]
  ring

end

end Descent.Portability.SelectionHistoryFirstOrder
