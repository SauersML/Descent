/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.SelectionMetricsFirstOrder
import Descent.Portability.SelectionMomentUniqueness

assert_below Descent.Decision Descent.Program

/-!
# Polygenic selection along a history

Every selection module of the corpus reads fitness at one locus
(`SelectionHistoryMoments.SelectionModel`), but the fitness a polygenic trait imposes is spread
over many loci. This module carries haploid additive selection, `s_i(h) = Σ_ℓ s_{i,ℓ}(h_ℓ)` with
one bounded table per locus, along histories of epochs, splits and pulses.

The generator. The additive drift of a haplotype frequency is `x_i[h] (s_i(h) - s̄_i)`, with `s̄_i`
the corpus mean fitness of the additive fitness (`eval_additiveDrift`), and the additive selection
generator is the derivation along it (`additiveSelectionGenerator`). Drift and generator are linear
in the fitness table: the drift is the sum of the one-locus drifts (`additiveDrift_eq_sum`), and the
generator is the sum of the one-locus generators `SelectionHistoryMoments.selectionGenerator` of
the per-locus models (`locusModel`, `additiveSelectionGenerator_eq_sum`). So the forward moment
equation with additive selection is `v_n' = Q_n v_n + Σ_ℓ B_{n,ℓ} v_{n + 1_ℓ}`, with one selection
matrix per locus (`expectedAdditiveSelectedGenerator_eq`).

Zero order. A vector started from the neutral propagation moves only by its forcing
(`SelectionMomentUniqueness.norm_le_of_zeroStart`), and the forcing of locus `ℓ` costs `B σ_ℓ`
(`SelectionHistoryMoments.abs_expectedSelection_le`). So one epoch moves the moments by at most
`B (Σ_ℓ σ_ℓ) d` (`norm_expectedMomentVector_sub_propagator_le_additive`). Along a history selected
with additive fitness (`AdditiveSelectedOnHistory`) the moments end within `B (Σ_ℓ σ_ℓ) T` of the
neutral chronological propagation (`norm_additiveHistory_sub_propagator_le`).

First order. Duhamel's formula with one forcing per locus (`norm_duhamel_firstOrder_sum_le`) gives
one epoch as the neutral propagator plus the sum of the one-locus corrections
`SelectionMomentExpansion.selectionCorrection`, within `B (B + 1) (Σ_ℓ S_ℓ) (Σ_ℓ σ_ℓ) d²`
(`norm_expectedMomentVector_sub_firstOrder_le_additive`). A stage of a history with one linear
correction per locus (`norm_sub_firstOrder_sum_step_le`) composes these: along a history the
selected moments are the neutral propagation plus the sum over loci of the one-locus history
corrections `SelectionHistoryFirstOrder.historyCorrection` (`additiveHistoryCorrection`), within
`B (B + 1) (Σ_ℓ S_ℓ) (Σ_ℓ σ_ℓ) T²` (`norm_additiveHistory_sub_firstOrder_le`). For tables bounded by
`σ` with masses at most `|A| σ`, this remainder is of order `σ² T²`.

Portability. The cross-ratio derivative is linear in its direction (`crossRatioDerivative_add`,
`crossRatioDerivative_sum`), so the first-order portability correction of the additive direction
is the sum of the per-locus first-order terms (`portabilityFirstOrder_sum`,
`portabilityFirstOrder_additiveHistoryCorrection`). Where the target denominator and the source
numerator are at least `δ > 0`, the portability of expected accuracies of the selected history is
its neutral value plus that sum, up to the explicit
`SelectionHistoryFirstOrder.crossRatioRemainder`, quadratic in the fitness scale
(`abs_additivePortability_sub_firstOrder_le`). Selection raises portability to first order exactly
when the target's relative first-order change exceeds the source's
(`additivePortabilityFirstOrder_pos_iff`), and in particular whenever every locus raises it
(`additivePortabilityFirstOrder_pos_of_forall`).

Scope. Selection is haploid and additive across loci; dominance and epistasis are not covered. The
forward moment equation with additive selection is a hypothesis on the families, at the budget and
at every budget with one more copy at one locus; the selected diffusion is not constructed.

## Empirical status

None. The bodies here are norm inequalities along matrix exponentials, finite sums of supplied
fitness tables and rational functions of dot products, so no measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.PolygenicSelectionHistory

open MvPolynomial Descent.Coalescent Descent.Foundations PartialHaplotypeCarrier
  PartialHaplotypeDualGenerator PartialHaplotypeDualSemigroup SubstochasticGeneratorSemigroup
  PartialHaplotypePulseKernel NeutralPulseHistoryKernel ReplicaMetricInstances
  EndToEndPortabilityLaw SelectionHistoryMoments EndToEndSelectionLaw SelectionMomentExpansion
  EndToEndSensitivityMetrics SelectionHistoryFirstOrder SelectionMomentUniqueness
  SelectionMetricsFirstOrder
open Descent.Pangenome.AncestralLocality.DecisionDysonDual (hasDerivAt_integral_from_zero
  continuous_integral_from_zero)
open scoped Matrix NNReal

noncomputable section

/-! ## Sums of forcings and of linear corrections -/

/-- **One stage of the first-order expansion with one linear correction per locus.** Let `P` be
substochastic and each `H_j` linear with cost at most `L_j`. If `V` is within `a` of
`P v + Σ_j H_j x_j`, `v` is within `b` of `u + c` and each `x_j` is within `e_j` of `w_j`, then `V`
is within `a + b + Σ_j L_j e_j` of `P u + (P c + Σ_j H_j w_j)`. -/
theorem norm_sub_firstOrder_sum_step_le {ι K : Type*} [Fintype ι] [Fintype K] {κ : K → Type*}
    [∀ j, Fintype (κ j)] {P : Matrix ι ι ℝ} (hP : SubstochasticMatrix P)
    (H : ∀ j, (κ j → ℝ) → ι → ℝ) (hH : ∀ j x y, H j (x - y) = H j x - H j y) {L : K → ℝ}
    (hL : ∀ j x, ‖H j x‖ ≤ L j * ‖x‖) (hL0 : ∀ j, 0 ≤ L j) {V v u c : ι → ℝ}
    {x w : ∀ j, κ j → ℝ} {a b : ℝ} {e : K → ℝ} (hrest : ‖V - P *ᵥ v - ∑ j, H j (x j)‖ ≤ a)
    (hstage : ‖v - u - c‖ ≤ b) (hlarger : ∀ j, ‖x j - w j‖ ≤ e j) :
    ‖V - P *ᵥ u - (P *ᵥ c + ∑ j, H j (w j))‖ ≤ a + b + ∑ j, L j * e j := by
  have hsplit : V - P *ᵥ u - (P *ᵥ c + ∑ j, H j (w j))
      = (V - P *ᵥ v - ∑ j, H j (x j)) + P *ᵥ (v - u - c) + ∑ j, H j (x j - w j) := by
    simp only [hH, Finset.sum_sub_distrib, Matrix.mulVec_sub]
    abel
  rw [hsplit]
  refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans
    (add_le_add hrest ((norm_mulVec_le_of_substochastic hP _).trans hstage))) ?_)
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ ↦
    (hL j _).trans (mul_le_mul_of_nonneg_left (hlarger j) (hL0 j)))

/-- **Duhamel's formula to first order with one forcing per locus.** Let `Q` be a killing
generator, and let `v` move on `[0, d]` with right derivative `Q v + Σ_j B_j w_j(t)`, where each
`B_j` costs at most `β_j` in sup norm and `w_j(t)` stays within `c_j t` of `e^{tQ'_j} w_j(0)`. Then
`‖v(d) - e^{dQ} v(0) - Σ_j ∫_0^d e^{(d-t)Q} B_j e^{tQ'_j} w_j(0) dt‖ ≤ (Σ_j β_j c_j) d² / 2`. -/
theorem norm_duhamel_firstOrder_sum_le {ι K : Type*} [Fintype ι] [DecidableEq ι] [Fintype K]
    {κ : K → Type*} [∀ j, Fintype (κ j)] [∀ j, DecidableEq (κ j)] {Q : Matrix ι ι ℝ}
    (hQ : KillingGenerator Q) (Q' : ∀ j, Matrix (κ j) (κ j) ℝ) (B : ∀ j, Matrix ι (κ j) ℝ)
    {β c : K → ℝ} (hβ : ∀ j, 0 ≤ β j) (hB : ∀ j x, ‖B j *ᵥ x‖ ≤ β j * ‖x‖)
    {v : ℝ → ι → ℝ} {w : ∀ j, ℝ → κ j → ℝ} {d : ℝ} (hd : 0 ≤ d)
    (hv : ContinuousOn v (Set.Icc 0 d))
    (hderiv : ∀ t ∈ Set.Ico 0 d,
      HasDerivWithinAt v (Q *ᵥ v t + ∑ j, B j *ᵥ w j t) (Set.Ici t) t)
    (hw : ∀ j, ∀ t ∈ Set.Ico 0 d, ‖w j t - matrixExponential (Q' j) t *ᵥ w j 0‖ ≤ c j * t) :
    ‖v d - matrixExponential Q d *ᵥ v 0
        - ∑ j, ∫ t in (0 : ℝ)..d, matrixExponential Q (d - t)
          *ᵥ (B j *ᵥ (matrixExponential (Q' j) t *ᵥ w j 0))‖
      ≤ (∑ j, β j * c j) * (d * d) / 2 := by
  have hcont : ∀ j, Continuous fun t ↦ matrixExponential Q (d - t)
      *ᵥ (B j *ᵥ (matrixExponential (Q' j) t *ᵥ w j 0)) := by
    intro j
    have hexp : Continuous fun t ↦ matrixExponential (Q' j) t *ᵥ w j 0 :=
      continuous_iff_continuousAt.mpr fun t ↦
        (StationaryHaplotypeRealization.hasDerivAt_matrixExponential_mulVec (Q' j) (w j 0)
          t).continuousAt
    have hinner : Continuous fun t ↦ B j *ᵥ (matrixExponential (Q' j) t *ᵥ w j 0) :=
      continuous_const.matrix_mulVec hexp
    exact continuousOn_univ.mp (continuousOn_propagator_mulVec Q d hinner.continuousOn)
  have hψ : ∀ t ∈ Set.Ico 0 d, HasDerivWithinAt
      (fun u ↦ matrixExponential Q (d - u) *ᵥ v u
        - ∑ j, (∫ s in (0 : ℝ)..u, matrixExponential Q (d - s)
          *ᵥ (B j *ᵥ (matrixExponential (Q' j) s *ᵥ w j 0)))
        - matrixExponential Q d *ᵥ v 0)
      (∑ j, matrixExponential Q (d - t)
        *ᵥ (B j *ᵥ (w j t - matrixExponential (Q' j) t *ᵥ w j 0)))
      (Set.Ici t) t := by
    intro t ht
    have hprod := hasDerivWithinAt_propagator_mulVec Q d (hderiv t ht)
    have hint := HasDerivWithinAt.fun_sum (u := Finset.univ) fun j (_ : j ∈ Finset.univ) ↦
      (hasDerivAt_integral_from_zero (hcont j) t).hasDerivWithinAt (s := Set.Ici t)
    have hcomm : matrixExponential Q (d - t) *ᵥ (Q *ᵥ v t)
        = Q *ᵥ (matrixExponential Q (d - t) *ᵥ v t) := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, matrixExponential_mul_comm]
    refine ((hprod.sub hint).sub (hasDerivWithinAt_const t (Set.Ici t)
      (matrixExponential Q d *ᵥ v 0))).congr_deriv ?_
    rw [Matrix.mulVec_add, hcomm, Matrix.mulVec_sum]
    simp only [Matrix.mulVec_sub, Finset.sum_sub_distrib]
    abel
  have hbound : ∀ t ∈ Set.Ico 0 d,
      ‖∑ j, matrixExponential Q (d - t)
        *ᵥ (B j *ᵥ (w j t - matrixExponential (Q' j) t *ᵥ w j 0))‖
        ≤ (∑ j, β j * c j) * t := by
    intro t ht
    have hpropagator := matrixExponential_substochastic Q hQ (d - t) (sub_nonneg.mpr ht.2.le)
    rw [Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ ↦ ?_)
    refine (norm_mulVec_le_of_substochastic hpropagator _).trans ((hB j _).trans ?_)
    exact (mul_le_mul_of_nonneg_left (hw j t ht) (hβ j)).trans_eq (by ring)
  have hboundary : ∀ x, HasDerivAt (fun u ↦ (∑ j, β j * c j) * (u * u) / 2)
      ((∑ j, β j * c j) * x) x := fun x ↦
    ((((hasDerivAt_id x).mul (hasDerivAt_id x)).const_mul (∑ j, β j * c j)).div_const
      2).congr_deriv (by simp only [id_eq]; ring)
  have hmain := image_norm_le_of_norm_deriv_right_le_deriv_boundary
    (((continuousOn_propagator_mulVec Q d hv).sub
      (continuous_finset_sum _ fun j _ ↦ continuous_integral_from_zero (hcont j)).continuousOn).sub
      continuousOn_const) hψ (by simp) hboundary hbound (Set.right_mem_Icc.mpr hd)
  have heq : v d - matrixExponential Q d *ᵥ v 0
      - ∑ j, ∫ t in (0 : ℝ)..d, matrixExponential Q (d - t)
        *ᵥ (B j *ᵥ (matrixExponential (Q' j) t *ᵥ w j 0))
      = matrixExponential Q (d - d) *ᵥ v d
        - ∑ j, (∫ s in (0 : ℝ)..d, matrixExponential Q (d - s)
          *ᵥ (B j *ᵥ (matrixExponential (Q' j) s *ᵥ w j 0)))
        - matrixExponential Q d *ᵥ v 0 := by
    rw [sub_self, matrixExponential_zero, Matrix.one_mulVec]
    abel
  rw [heq]
  exact hmain

/-- **The cross-ratio derivative is additive in its direction.** -/
theorem crossRatioDerivative_add (a b c d a₁ b₁ c₁ d₁ a₂ b₂ c₂ d₂ : ℝ) :
    crossRatioDerivative a b c d (a₁ + a₂) (b₁ + b₂) (c₁ + c₂) (d₁ + d₂)
      = crossRatioDerivative a b c d a₁ b₁ c₁ d₁ + crossRatioDerivative a b c d a₂ b₂ c₂ d₂ := by
  simp only [crossRatioDerivative]
  ring

/-- **The cross-ratio derivative of a sum of directions is the sum of the derivatives.** -/
theorem crossRatioDerivative_sum {K : Type*} [DecidableEq K] (s : Finset K) (a b c d : ℝ)
    (a' b' c' d' : K → ℝ) :
    crossRatioDerivative a b c d (∑ j ∈ s, a' j) (∑ j ∈ s, b' j) (∑ j ∈ s, c' j)
        (∑ j ∈ s, d' j)
      = ∑ j ∈ s, crossRatioDerivative a b c d (a' j) (b' j) (c' j) (d' j) := by
  induction s using Finset.induction_on with
  | empty => simp [crossRatioDerivative]
  | @insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj, Finset.sum_insert hj, Finset.sum_insert hj,
      Finset.sum_insert hj, crossRatioDerivative_add, ih]

variable {Deme Locus : Type*} {Allele : Locus → Type*}
variable [Fintype Deme] [DecidableEq Deme] [Fintype Locus] [DecidableEq Locus]
  [∀ ℓ, Fintype (Allele ℓ)] [∀ ℓ, DecidableEq (Allele ℓ)]

/-! ## Additive fitness and its generator -/

/-- The one-locus selection model of locus `ℓ` in an additive fitness table. -/
def locusModel (table : ∀ ℓ, Deme → Allele ℓ → ℝ) (ℓ : Locus) :
    SelectionModel Deme Locus Allele where
  locus := ℓ
  fitness := table ℓ

/-- **Additive haploid fitness**: a haplotype of deme `i` has fitness `Σ_ℓ s_{i,ℓ}(h_ℓ)`. -/
def additiveFitness (table : ∀ ℓ, Deme → Allele ℓ → ℝ) (i : Deme)
    (hap : FullHaplotype Locus Allele) : ℝ :=
  ∑ ℓ, table ℓ i (hap ℓ)

/-- The additive selective drift `x_i[h] (s_i(h) - s̄_i)` of one haplotype frequency, with `s̄_i`
the sum of the per-locus mean fitness polynomials. -/
def additiveDrift (table : ∀ ℓ, Deme → Allele ℓ → ℝ)
    (coordinate : FrequencyVariable Deme Locus Allele) : FrequencyPolynomial Deme Locus Allele :=
  X coordinate * (C (additiveFitness table coordinate.1 coordinate.2)
    - ∑ ℓ, meanFitnessPolynomial (locusModel table ℓ) coordinate.1)

/-- **At a frequency point the additive drift is the classical drift of the additive fitness**,
`x_i[h] (s_i(h) - s̄_i)` with `s̄_i` the corpus mean fitness `AncestralLocality.meanFitness` of the
additive fitness in the deme. -/
theorem eval_additiveDrift (table : ∀ ℓ, Deme → Allele ℓ → ℝ)
    (x : FrequencyVariable Deme Locus Allele → ℝ) (i : Deme) (hap : FullHaplotype Locus Allele) :
    eval x (additiveDrift table (i, hap))
      = x (i, hap) * (additiveFitness table i hap
        - Descent.Pangenome.AncestralLocality.meanFitness (additiveFitness table i)
          (fun g ↦ x (i, g))) := by
  have hmean : ∑ ℓ, eval x (meanFitnessPolynomial (locusModel table ℓ) i)
      = Descent.Pangenome.AncestralLocality.meanFitness (additiveFitness table i)
          (fun g ↦ x (i, g)) := by
    simp only [eval_meanFitnessPolynomial, locusModel, additiveFitness,
      Descent.Pangenome.AncestralLocality.meanFitness, Finset.mul_sum]
    exact Finset.sum_comm
  simp only [additiveDrift, map_mul, map_sub, map_sum, eval_X, eval_C, hmean]

/-- **The additive selection generator**: the derivation of frequency polynomials along the
additive selective drift of every haplotype frequency. -/
def additiveSelectionGenerator (table : ∀ ℓ, Deme → Allele ℓ → ℝ)
    (f : FrequencyPolynomial Deme Locus Allele) : FrequencyPolynomial Deme Locus Allele :=
  ∑ coordinate, additiveDrift table coordinate * pderiv coordinate f

/-- **The additive drift is the sum of the one-locus drifts**: the drift is linear in the fitness
table. -/
theorem additiveDrift_eq_sum (table : ∀ ℓ, Deme → Allele ℓ → ℝ)
    (coordinate : FrequencyVariable Deme Locus Allele) :
    additiveDrift table coordinate = ∑ ℓ, selectiveDrift (locusModel table ℓ) coordinate := by
  simp only [additiveDrift, selectiveDrift, additiveFitness, locusModel, map_sum,
    ← Finset.sum_sub_distrib, Finset.mul_sum]

/-- **The additive selection generator is the sum of the one-locus generators.** -/
theorem additiveSelectionGenerator_eq_sum (table : ∀ ℓ, Deme → Allele ℓ → ℝ)
    (f : FrequencyPolynomial Deme Locus Allele) :
    additiveSelectionGenerator table f = ∑ ℓ, selectionGenerator (locusModel table ℓ) f := by
  simp only [additiveSelectionGenerator, selectionGenerator, additiveDrift_eq_sum, Finset.sum_mul]
  exact Finset.sum_comm

/-- **The forward generator with additive selection**: the neutral generator plus the additive
selection generator. -/
def additiveSelectedGenerator (rates : NeutralRates Deme Locus Allele)
    (table : ∀ ℓ, Deme → Allele ℓ → ℝ) (f : FrequencyPolynomial Deme Locus Allele) :
    FrequencyPolynomial Deme Locus Allele :=
  neutralGenerator rates f + additiveSelectionGenerator table f

/-- **The forward moment equation with additive selection, in matrix form.** Under an expectation
functional, the expected generator with additive selection of a budget-respecting configuration
moment is the neutral dual generator on the expected moments plus, for every locus, its selection
matrix on the expected moments of the budget with one more copy at that locus. -/
theorem expectedAdditiveSelectedGenerator_eq (rates : NeutralRates Deme Locus Allele)
    (table : ∀ ℓ, Deme → Allele ℓ → ℝ) (capacity : Locus → ℕ)
    (expectationAt : ℝ → ExpFunctional (Deme → FiniteReportLaw (FullHaplotype Locus Allele)))
    (s : ℝ) (ξ : BudgetConfiguration Deme Locus Allele capacity) :
    (expectationAt s fun law ↦
        eval (lawPoint law) (additiveSelectedGenerator rates table (momentPolynomial ξ.1)))
      = (dualGenerator rates capacity *ᵥ expectedMomentVector capacity expectationAt s
        + ∑ ℓ, selectionMatrix (locusModel table ℓ) capacity
          *ᵥ expectedMomentVector (bumpCapacity (locusModel table ℓ) capacity)
            expectationAt s) ξ := by
  have hsplit : (fun law : Deme → FiniteReportLaw (FullHaplotype Locus Allele) ↦
        eval (lawPoint law) (additiveSelectedGenerator rates table (momentPolynomial ξ.1)))
      = (fun law ↦ eval (lawPoint law) (neutralGenerator rates (momentPolynomial ξ.1)))
        + ∑ ℓ, fun law ↦
          eval (lawPoint law) (selectionGenerator (locusModel table ℓ) (momentPolynomial ξ.1)) := by
    funext law
    simp only [additiveSelectedGenerator, additiveSelectionGenerator_eq_sum, map_add, map_sum,
      Pi.add_apply, Finset.sum_apply]
  rw [hsplit, (expectationAt s).add_eval, ExpFunctional.eval_sum,
    expectedGenerator_eq_mulVec rates capacity expectationAt s ξ, Pi.add_apply, Finset.sum_apply]
  congr 1
  exact Finset.sum_congr rfl fun ℓ _ ↦
    congrFun (expectedSelection_eq_mulVec (locusModel table ℓ) capacity (expectationAt s)) ξ

/-! ## Zero order -/

/-- **Additive selection moves the moments of one epoch by at most `B (Σ_ℓ σ_ℓ) d`.** Suppose the
expected budget-respecting configuration moments of an expectation family are continuous on
`[0, d]` and obey the forward moment equation with additive selection there, with the table of
locus `ℓ` in `[0, σ_ℓ]`. Then the moments at `d` differ from the neutral epoch propagator applied
to the initial moments by at most `B (Σ_ℓ σ_ℓ) d` in sup norm, with `B = Σ_ℓ n_ℓ`. -/
theorem norm_expectedMomentVector_sub_propagator_le_additive
    (rates : NeutralRates Deme Locus Allele) (table : ∀ ℓ, Deme → Allele ℓ → ℝ)
    {σ : Locus → ℝ} (hσ : ∀ ℓ, 0 ≤ σ ℓ) (hfit : ∀ ℓ i b, 0 ≤ table ℓ i b ∧ table ℓ i b ≤ σ ℓ)
    (capacity : Locus → ℕ)
    (expectationAt : ℝ → ExpFunctional (Deme → FiniteReportLaw (FullHaplotype Locus Allele)))
    {d : ℝ} (hd : 0 ≤ d)
    (hcont : ContinuousOn (expectedMomentVector capacity expectationAt) (Set.Icc 0 d))
    (hforward : ∀ ξ : BudgetConfiguration Deme Locus Allele capacity, ∀ t ∈ Set.Ico 0 d,
      HasDerivWithinAt (fun s ↦ expectedMomentVector capacity expectationAt s ξ)
        (expectationAt t fun law ↦
          eval (lawPoint law) (additiveSelectedGenerator rates table (momentPolynomial ξ.1)))
        (Set.Ici t) t) :
    ‖expectedMomentVector capacity expectationAt d
        - matrixExponential (dualGenerator rates capacity) d
          *ᵥ expectedMomentVector capacity expectationAt 0‖
      ≤ (∑ ℓ, capacity ℓ : ℕ) * (∑ ℓ, σ ℓ) * d := by
  have hexp : ∀ t, HasDerivAt
      (fun u ↦ matrixExponential (dualGenerator rates capacity) u
        *ᵥ expectedMomentVector capacity expectationAt 0)
      (dualGenerator rates capacity *ᵥ (matrixExponential (dualGenerator rates capacity) t
        *ᵥ expectedMomentVector capacity expectationAt 0)) t := fun t ↦
    StationaryHaplotypeRealization.hasDerivAt_matrixExponential_mulVec _ _ t
  have hderiv : ∀ t ∈ Set.Ico 0 d, HasDerivWithinAt
      (fun u ↦ expectedMomentVector capacity expectationAt u
        - matrixExponential (dualGenerator rates capacity) u
          *ᵥ expectedMomentVector capacity expectationAt 0)
      (dualGenerator rates capacity *ᵥ (expectedMomentVector capacity expectationAt t
          - matrixExponential (dualGenerator rates capacity) t
            *ᵥ expectedMomentVector capacity expectationAt 0)
        + ∑ ℓ, selectionMatrix (locusModel table ℓ) capacity
          *ᵥ expectedMomentVector (bumpCapacity (locusModel table ℓ) capacity) expectationAt t)
      (Set.Ici t) t := by
    intro t ht
    have hv : HasDerivWithinAt (expectedMomentVector capacity expectationAt)
        (dualGenerator rates capacity *ᵥ expectedMomentVector capacity expectationAt t
          + ∑ ℓ, selectionMatrix (locusModel table ℓ) capacity
            *ᵥ expectedMomentVector (bumpCapacity (locusModel table ℓ) capacity) expectationAt t)
        (Set.Ici t) t :=
      hasDerivWithinAt_pi.mpr fun ξ ↦ (hforward ξ t ht).congr_deriv
        (expectedAdditiveSelectedGenerator_eq rates table capacity expectationAt t ξ)
    refine (hv.sub (hexp t).hasDerivWithinAt).congr_deriv ?_
    rw [Matrix.mulVec_sub]
    abel
  have hbound : ∀ t ∈ Set.Ico 0 d, ‖∑ ℓ, selectionMatrix (locusModel table ℓ) capacity
      *ᵥ expectedMomentVector (bumpCapacity (locusModel table ℓ) capacity) expectationAt t‖
        ≤ (∑ ℓ, capacity ℓ : ℕ) * ∑ ℓ, σ ℓ := by
    intro t _
    rw [Finset.mul_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun ℓ _ ↦ ?_)
    have hselection : selectionMatrix (locusModel table ℓ) capacity
        *ᵥ expectedMomentVector (bumpCapacity (locusModel table ℓ) capacity) expectationAt t
        = expectedSelection (locusModel table ℓ) capacity (expectationAt t) :=
      (expectedSelection_eq_mulVec _ _ _).symm
    rw [hselection]
    refine (pi_norm_le_iff_of_nonneg (mul_nonneg (Nat.cast_nonneg _) (hσ ℓ))).mpr fun ξ ↦ ?_
    rw [Real.norm_eq_abs]
    exact abs_expectedSelection_le (locusModel table ℓ) (hσ ℓ) (hfit ℓ) capacity
      (expectationAt t) ξ
  have hG : ∀ x, HasDerivAt (fun u ↦ (∑ ℓ, capacity ℓ : ℕ) * (∑ ℓ, σ ℓ) * u)
      ((∑ ℓ, capacity ℓ : ℕ) * ∑ ℓ, σ ℓ) x := fun x ↦
    ((hasDerivAt_id x).const_mul ((∑ ℓ, capacity ℓ : ℕ) * ∑ ℓ, σ ℓ)).congr_deriv (mul_one _)
  exact norm_le_of_zeroStart (killingGenerator_dualGenerator rates capacity) hd
    (hcont.sub (continuous_iff_continuousAt.mpr fun t ↦ (hexp t).continuousAt).continuousOn)
    hderiv (by simp only [matrixExponential_zero, Matrix.one_mulVec, sub_self]) (by simp) hG
    hbound

/-- **Additive selection along a history of epochs, splits and pulses.** `family k` is the
expectation family over per-deme haplotype laws during the `k`-th event, on its own clock. During
an epoch its expected budget-respecting configuration moments are continuous on `[0, d]` and obey
the forward moment equation with additive selection at the epoch's neutral rates, and the next
family starts from the moments at `d`. Across a split or a pulse the next family starts from the
pulsed moments.

Assumes: the families are the moment tables of a process with additive selection run through the
events in chronological order. -/
def AdditiveSelectedOnHistory (table : ∀ ℓ, Deme → Allele ℓ → ℝ) (capacity : Locus → ℕ)
    (family : ℕ → ℝ → ExpFunctional (Deme → FiniteReportLaw (FullHaplotype Locus Allele))) :
    List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme) → ℕ → Prop
  | [], _ => True
  | Sum.inl epoch :: rest, k =>
      (ContinuousOn (expectedMomentVector capacity (family k)) (Set.Icc 0 (epoch.2 : ℝ))
        ∧ (∀ ξ : BudgetConfiguration Deme Locus Allele capacity, ∀ t ∈ Set.Ico 0 (epoch.2 : ℝ),
          HasDerivWithinAt (fun s ↦ expectedMomentVector capacity (family k) s ξ)
            (family k t fun law ↦
              eval (lawPoint law) (additiveSelectedGenerator epoch.1 table (momentPolynomial ξ.1)))
            (Set.Ici t) t)
        ∧ expectedMomentVector capacity (family (k + 1)) 0
          = expectedMomentVector capacity (family k) epoch.2)
      ∧ AdditiveSelectedOnHistory table capacity family rest (k + 1)
  | Sum.inr pulse :: rest, k =>
      (∀ ξ : BudgetConfiguration Deme Locus Allele capacity,
        expectedMomentVector capacity (family (k + 1)) 0 ξ
          = family k 0 fun law ↦ configurationMoment (pulsedLaw pulse law) ξ.1)
      ∧ AdditiveSelectedOnHistory table capacity family rest (k + 1)

/-- The empty history carries no obligation, so `AdditiveSelectedOnHistory` is inhabited. -/
theorem additiveSelectedOnHistory_nil (table : ∀ ℓ, Deme → Allele ℓ → ℝ) (capacity : Locus → ℕ)
    (family : ℕ → ℝ → ExpFunctional (Deme → FiniteReportLaw (FullHaplotype Locus Allele)))
    (k : ℕ) : AdditiveSelectedOnHistory table capacity family [] k :=
  trivial

/-- **Additive selection moves the moments of a whole history by at most `B (Σ_ℓ σ_ℓ) T`.** Along
a history of epochs, splits and pulses with total epoch duration `T`, families selected with
additive fitness, the table of locus `ℓ` in `[0, σ_ℓ]`, end with expected budget-respecting
configuration moments within `B (Σ_ℓ σ_ℓ) T` in sup norm of the neutral chronological propagator
applied to their initial moments, with `B = Σ_ℓ n_ℓ`.

Assumes: `AdditiveSelectedOnHistory table capacity family events k`. -/
theorem norm_additiveHistory_sub_propagator_le (table : ∀ ℓ, Deme → Allele ℓ → ℝ)
    {σ : Locus → ℝ} (hσ : ∀ ℓ, 0 ≤ σ ℓ) (hfit : ∀ ℓ i b, 0 ≤ table ℓ i b ∧ table ℓ i b ≤ σ ℓ)
    (capacity : Locus → ℕ)
    (family : ℕ → ℝ → ExpFunctional (Deme → FiniteReportLaw (FullHaplotype Locus Allele))) :
    ∀ (events : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme)) (k : ℕ),
      AdditiveSelectedOnHistory table capacity family events k →
      ‖expectedMomentVector capacity (family (k + events.length)) 0
          - historyEventPropagator capacity events *ᵥ expectedMomentVector capacity (family k) 0‖
        ≤ (∑ ℓ, capacity ℓ : ℕ) * (∑ ℓ, σ ℓ) * epochDuration events
  | [], k, _ => by
    simp [historyEventPropagator, epochDuration]
  | Sum.inl epoch :: rest, k, hhistory => by
    obtain ⟨⟨hcont, hforward, hnext⟩, hrest⟩ := hhistory
    have hepoch := norm_expectedMomentVector_sub_propagator_le_additive epoch.1 table hσ hfit
      capacity (family k) (NNReal.coe_nonneg epoch.2) hcont hforward
    rw [← hnext] at hepoch
    have hlength : k + (Sum.inl epoch :: rest).length = k + 1 + rest.length := by
      rw [List.length_cons]
      omega
    rw [hlength, historyEventPropagator, eventPropagator, ← Matrix.mulVec_mulVec]
    exact (norm_sub_mulVec_le (historyEventPropagator_substochastic capacity rest)
      (norm_additiveHistory_sub_propagator_le table hσ hfit capacity family rest (k + 1) hrest)
      hepoch).trans_eq (by simp only [epochDuration]; ring)
  | Sum.inr pulse :: rest, k, hhistory => by
    obtain ⟨hnext, hrest⟩ := hhistory
    have hmoments : expectedMomentVector capacity (family (k + 1)) 0
        = pulseKernel pulse capacity *ᵥ expectedMomentVector capacity (family k) 0 := by
      funext ξ
      rw [hnext ξ, pulseKernel_mulVec_expectedMoment]
      rfl
    have hlength : k + (Sum.inr pulse :: rest).length = k + 1 + rest.length := by
      rw [List.length_cons]
      omega
    have h := norm_additiveHistory_sub_propagator_le table hσ hfit capacity family rest (k + 1)
      hrest
    rw [hmoments, ← hlength, Matrix.mulVec_mulVec] at h
    simpa only [historyEventPropagator, eventPropagator, epochDuration] using h

/-! ## First order -/

/-- **The moments of an epoch to first order in additive selection.** Suppose the expected moments
of the budget and of every budget with one more copy at one locus are continuous on `[0, d]` and
obey the forward moment equation with additive selection there, with the table of locus `ℓ` in
`[0, σ_ℓ]` and masses `Σ_b |s_{i,ℓ}(b)| ≤ S_ℓ`. Then the moments at `d` are the neutral propagator
applied to the initial moments plus the sum over loci of the one-locus first-order corrections,
up to `B (B + 1) (Σ_ℓ S_ℓ) (Σ_ℓ σ_ℓ) d²` in sup norm, with `B = Σ_ℓ n_ℓ`. -/
theorem norm_expectedMomentVector_sub_firstOrder_le_additive
    (rates : NeutralRates Deme Locus Allele) (table : ∀ ℓ, Deme → Allele ℓ → ℝ)
    {σ S : Locus → ℝ} (hσ : ∀ ℓ, 0 ≤ σ ℓ) (hS0 : ∀ ℓ, 0 ≤ S ℓ)
    (hfit : ∀ ℓ i b, 0 ≤ table ℓ i b ∧ table ℓ i b ≤ σ ℓ)
    (hS : ∀ ℓ i, ∑ b, |table ℓ i b| ≤ S ℓ) (capacity : Locus → ℕ)
    (expectationAt : ℝ → ExpFunctional (Deme → FiniteReportLaw (FullHaplotype Locus Allele)))
    {d : ℝ} (hd : 0 ≤ d)
    (hcont : ContinuousOn (expectedMomentVector capacity expectationAt) (Set.Icc 0 d))
    (hcont' : ∀ ℓ, ContinuousOn
      (expectedMomentVector (bumpCapacity (locusModel table ℓ) capacity) expectationAt)
      (Set.Icc 0 d))
    (hforward : ∀ ξ : BudgetConfiguration Deme Locus Allele capacity, ∀ t ∈ Set.Ico 0 d,
      HasDerivWithinAt (fun s ↦ expectedMomentVector capacity expectationAt s ξ)
        (expectationAt t fun law ↦
          eval (lawPoint law) (additiveSelectedGenerator rates table (momentPolynomial ξ.1)))
        (Set.Ici t) t)
    (hforward' : ∀ ℓ, ∀ ξ : BudgetConfiguration Deme Locus Allele
        (bumpCapacity (locusModel table ℓ) capacity), ∀ t ∈ Set.Ico 0 d,
      HasDerivWithinAt (fun s ↦
          expectedMomentVector (bumpCapacity (locusModel table ℓ) capacity) expectationAt s ξ)
        (expectationAt t fun law ↦
          eval (lawPoint law) (additiveSelectedGenerator rates table (momentPolynomial ξ.1)))
        (Set.Ici t) t) :
    ‖expectedMomentVector capacity expectationAt d
        - matrixExponential (dualGenerator rates capacity) d
          *ᵥ expectedMomentVector capacity expectationAt 0
        - ∑ ℓ, selectionCorrection rates (locusModel table ℓ) capacity
          (expectedMomentVector (bumpCapacity (locusModel table ℓ) capacity) expectationAt 0) d‖
      ≤ (∑ ℓ, capacity ℓ : ℕ) * ((∑ ℓ, capacity ℓ : ℕ) + 1) * (∑ ℓ, S ℓ) * (∑ ℓ, σ ℓ)
        * d ^ 2 := by
  have hderiv : ∀ t ∈ Set.Ico 0 d, HasDerivWithinAt (expectedMomentVector capacity expectationAt)
      (dualGenerator rates capacity *ᵥ expectedMomentVector capacity expectationAt t
        + ∑ ℓ, selectionMatrix (locusModel table ℓ) capacity
          *ᵥ expectedMomentVector (bumpCapacity (locusModel table ℓ) capacity) expectationAt t)
      (Set.Ici t) t := fun t ht ↦
    hasDerivWithinAt_pi.mpr fun ξ ↦ (hforward ξ t ht).congr_deriv
      (expectedAdditiveSelectedGenerator_eq rates table capacity expectationAt t ξ)
  have hw : ∀ j, ∀ t ∈ Set.Ico 0 d,
      ‖expectedMomentVector (bumpCapacity (locusModel table j) capacity) expectationAt t
          - matrixExponential (dualGenerator rates (bumpCapacity (locusModel table j) capacity)) t
            *ᵥ expectedMomentVector (bumpCapacity (locusModel table j) capacity) expectationAt 0‖
        ≤ ((∑ ℓ, capacity ℓ : ℕ) + 1) * (∑ ℓ, σ ℓ) * t := by
    intro j t ht
    have h := norm_expectedMomentVector_sub_propagator_le_additive rates table hσ hfit
      (bumpCapacity (locusModel table j) capacity) expectationAt ht.1
      ((hcont' j).mono (Set.Icc_subset_Icc_right ht.2.le))
      (fun ξ s hs ↦ hforward' j ξ s ⟨hs.1, hs.2.trans ht.2⟩)
    rwa [sum_bumpCapacity, Nat.cast_add, Nat.cast_one] at h
  have h := norm_duhamel_firstOrder_sum_le (killingGenerator_dualGenerator rates capacity)
    (fun j ↦ dualGenerator rates (bumpCapacity (locusModel table j) capacity))
    (fun j ↦ selectionMatrix (locusModel table j) capacity)
    (β := fun j ↦ 2 * (∑ ℓ, capacity ℓ : ℕ) * S j)
    (c := fun _ ↦ ((∑ ℓ, capacity ℓ : ℕ) + 1) * ∑ ℓ, σ ℓ)
    (w := fun j t ↦ expectedMomentVector (bumpCapacity (locusModel table j) capacity)
      expectationAt t)
    (fun j ↦ mul_nonneg (mul_nonneg zero_le_two (Nat.cast_nonneg _)) (hS0 j))
    (fun j ↦ norm_selectionMatrix_mulVec_le (locusModel table j) (hS0 j) (hS j) capacity)
    hd hcont hderiv hw
  refine h.trans_eq ?_
  simp only [← Finset.sum_mul, ← Finset.mul_sum]
  ring

/-- Across a split or a pulse, the moments of the next family are the pulse kernel applied to the
moments of the current one. -/
theorem expectedMomentVector_pulse (pulse : PulseMatrix Deme) (capacity : Locus → ℕ)
    (current next : ℝ → ExpFunctional (Deme → FiniteReportLaw (FullHaplotype Locus Allele)))
    (hnext : ∀ ξ : BudgetConfiguration Deme Locus Allele capacity,
      expectedMomentVector capacity next 0 ξ
        = current 0 fun law ↦ configurationMoment (pulsedLaw pulse law) ξ.1) :
    expectedMomentVector capacity next 0
      = pulseKernel pulse capacity *ᵥ expectedMomentVector capacity current 0 :=
  funext fun ξ ↦ (hnext ξ).trans (pulseKernel_mulVec_expectedMoment pulse capacity (current 0) ξ)

/-- **The first-order correction of a history under additive selection**: the sum over loci of the
one-locus history corrections, at the moments of the budgets with one more copy at each locus. -/
def additiveHistoryCorrection (table : ∀ ℓ, Deme → Allele ℓ → ℝ) (capacity : Locus → ℕ)
    (events : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme))
    (w : ∀ ℓ, BudgetConfiguration Deme Locus Allele (bumpCapacity (locusModel table ℓ) capacity)
      → ℝ) :
    BudgetConfiguration Deme Locus Allele capacity → ℝ :=
  ∑ ℓ, historyCorrection (locusModel table ℓ) capacity events (w ℓ)

/-- **The first-order law of a history under additive selection.** Along a history of epochs,
splits and pulses with total epoch duration `T`, families selected with additive fitness, the table
of locus `ℓ` in `[0, σ_ℓ]` with masses at most `S_ℓ`, obeying the forward moment equation at the
budget and at every budget with one more copy at one locus, end with moments equal to the neutral
chronological propagation of their initial moments plus the sum over loci of the one-locus history
corrections, up to `B (B + 1) (Σ_ℓ S_ℓ) (Σ_ℓ σ_ℓ) T²` in sup norm, with `B = Σ_ℓ n_ℓ`.

Assumes: `AdditiveSelectedOnHistory table capacity family events k` and, for every locus `ℓ`,
`AdditiveSelectedOnHistory table (bumpCapacity (locusModel table ℓ) capacity) family events k`. -/
theorem norm_additiveHistory_sub_firstOrder_le (table : ∀ ℓ, Deme → Allele ℓ → ℝ)
    {σ S : Locus → ℝ} (hσ : ∀ ℓ, 0 ≤ σ ℓ) (hS0 : ∀ ℓ, 0 ≤ S ℓ)
    (hfit : ∀ ℓ i b, 0 ≤ table ℓ i b ∧ table ℓ i b ≤ σ ℓ)
    (hS : ∀ ℓ i, ∑ b, |table ℓ i b| ≤ S ℓ) (capacity : Locus → ℕ)
    (family : ℕ → ℝ → ExpFunctional (Deme → FiniteReportLaw (FullHaplotype Locus Allele))) :
    ∀ (events : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme)) (k : ℕ),
      AdditiveSelectedOnHistory table capacity family events k →
      (∀ ℓ, AdditiveSelectedOnHistory table (bumpCapacity (locusModel table ℓ) capacity) family
        events k) →
      ‖expectedMomentVector capacity (family (k + events.length)) 0
          - historyEventPropagator capacity events *ᵥ expectedMomentVector capacity (family k) 0
          - additiveHistoryCorrection table capacity events (fun ℓ ↦
            expectedMomentVector (bumpCapacity (locusModel table ℓ) capacity) (family k) 0)‖
        ≤ (∑ ℓ, capacity ℓ : ℕ) * ((∑ ℓ, capacity ℓ : ℕ) + 1) * (∑ ℓ, S ℓ) * (∑ ℓ, σ ℓ)
          * epochDuration events ^ 2
  | [], k, _, _ => by
    simp [historyEventPropagator, additiveHistoryCorrection, historyCorrection, epochDuration]
  | Sum.inl epoch :: rest, k, hhistory, hhistory' => by
    obtain ⟨⟨hcont, hforward, hnext⟩, hrest⟩ := hhistory
    have hstage := norm_expectedMomentVector_sub_firstOrder_le_additive epoch.1 table hσ hS0 hfit
      hS capacity (family k) (NNReal.coe_nonneg epoch.2) hcont (fun ℓ ↦ (hhistory' ℓ).1.1)
      hforward (fun ℓ ↦ (hhistory' ℓ).1.2.1)
    rw [← hnext] at hstage
    have hlarger : ∀ j,
        ‖expectedMomentVector (bumpCapacity (locusModel table j) capacity) (family (k + 1)) 0
          - matrixExponential (dualGenerator epoch.1 (bumpCapacity (locusModel table j) capacity))
              epoch.2
            *ᵥ expectedMomentVector (bumpCapacity (locusModel table j) capacity) (family k) 0‖
        ≤ ((∑ ℓ, capacity ℓ : ℕ) + 1) * (∑ ℓ, σ ℓ) * epoch.2 := by
      intro j
      have h := norm_expectedMomentVector_sub_propagator_le_additive epoch.1 table hσ hfit
        (bumpCapacity (locusModel table j) capacity) (family k) (NNReal.coe_nonneg epoch.2)
        (hhistory' j).1.1 (hhistory' j).1.2.1
      rwa [← (hhistory' j).1.2.2, sum_bumpCapacity, Nat.cast_add, Nat.cast_one] at h
    have hstep := norm_sub_firstOrder_sum_step_le
      (historyEventPropagator_substochastic capacity rest)
      (fun j ↦ historyCorrection (locusModel table j) capacity rest)
      (fun j ↦ historyCorrection_sub (locusModel table j) capacity rest)
      (fun j ↦ norm_historyCorrection_le (locusModel table j) (hS0 j) (hS j) capacity rest)
      (fun j ↦ mul_nonneg (mul_nonneg (mul_nonneg zero_le_two (Nat.cast_nonneg _)) (hS0 j))
        (epochDuration_nonneg rest))
      (norm_additiveHistory_sub_firstOrder_le table hσ hS0 hfit hS capacity family rest (k + 1)
        hrest fun j ↦ (hhistory' j).2)
      hstage hlarger
    have hlength : k + (Sum.inl epoch :: rest).length = k + 1 + rest.length := by
      rw [List.length_cons]
      omega
    rw [hlength, historyEventPropagator, eventPropagator, ← Matrix.mulVec_mulVec, epochDuration]
    simp only [additiveHistoryCorrection, historyCorrection, Finset.sum_add_distrib,
      ← Matrix.mulVec_sum]
    refine hstep.trans_eq ?_
    simp only [← Finset.sum_mul, ← Finset.mul_sum]
    ring
  | Sum.inr pulse :: rest, k, hhistory, hhistory' => by
    obtain ⟨hnext, hrest⟩ := hhistory
    have h := norm_additiveHistory_sub_firstOrder_le table hσ hS0 hfit hS capacity family rest
      (k + 1) hrest fun j ↦ (hhistory' j).2
    have hpulse := fun j ↦ expectedMomentVector_pulse pulse
      (bumpCapacity (locusModel table j) capacity) (family k) (family (k + 1)) (hhistory' j).1
    rw [expectedMomentVector_pulse pulse capacity (family k) (family (k + 1)) hnext] at h
    simp only [additiveHistoryCorrection, hpulse] at h
    have hlength : k + (Sum.inr pulse :: rest).length = k + 1 + rest.length := by
      rw [List.length_cons]
      omega
    rw [hlength, historyEventPropagator, eventPropagator, ← Matrix.mulVec_mulVec, epochDuration]
    simpa only [additiveHistoryCorrection, historyCorrection] using h

end

end Descent.Portability.PolygenicSelectionHistory
