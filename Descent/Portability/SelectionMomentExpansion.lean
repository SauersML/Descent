/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.EndToEndSelectionLaw
import Descent.Pangenome.AncestralLocality.DecisionDysonDual

assert_below Descent.Decision Descent.Program

/-!
# The first-order selection correction of the partial-haplotype moment law

`SelectionHistoryMoments` bounds how far selection moves the expected moments of one epoch from the
neutral propagator, `‖v(d) - e^{dQ} v(0)‖ ≤ B σ d`, and `EndToEndSelectionLaw` shows that no finite
table of moments closes under selection. This module gives the next term: the exact first-order
correction, with a remainder of order `σ² d²`.

The selection matrix in sup norm. The selection matrix from budget `n` to budget `n + 1_ℓ` acts
through the selection terms, each gained and each lost configuration read once
(`sum_map_abs_rate_selectionTerms`). So for fitness masses `Σ_b |s_i(b)| ≤ S` it costs at most
`2 B S` in sup norm, with `B = Σ_ℓ n_ℓ` (`norm_selectionMatrix_mulVec_le`). This bound holds on
every vector, not only on expected moments, where
`SelectionHistoryMoments.abs_expectedSelection_le` gives `B σ`.

Duhamel to first order. For a killing generator `Q`, a vector moving with `v' = Q v + B w(t)` and a
second vector `w` within `c t` of `e^{tQ'} w(0)`, the difference
`e^{(d-t)Q} v(t) - ∫_0^t e^{(d-s)Q} B e^{sQ'} w(0) ds` moves with
`e^{(d-t)Q} B (w(t) - e^{tQ'} w(0))`, at most `β c t` when `B` costs at most `β`. So
`‖v(d) - e^{dQ} v(0) - ∫_0^d e^{(d-t)Q} B e^{tQ'} w(0) dt‖ ≤ β c d² / 2`
(`norm_duhamel_firstOrder_le`).

The first-order correction. `selectionCorrection` is `∫_0^d e^{(d-t)Q} B e^{tQ'} w(0) dt`, with `Q`
and `Q'` the neutral dual generators of the budget and of the budget with one more copy at the
selected locus, `B` the selection matrix between them, and `w(0)` the initial moments of the larger
budget. Along the forward moment equation with selection at both budgets, the epoch bound of
`SelectionHistoryMoments` at the larger budget supplies `c = B' σ` with `B' = B + 1`
(`sum_bumpCapacity`). So the moments of an epoch are the neutral propagator plus the correction up
to `B S B' σ d²` (`norm_expectedMomentVector_sub_firstOrder_le`). The correction is the selection
matrix, linear in the fitness table, between two neutral propagators, so it is the term of first
order in `σ`. A polynomial whose monomials fit the budget follows with its coefficient mass
(`abs_expectedPolynomial_sub_firstOrder_le`), including the correlation numerators and
denominators of `EndToEndPortabilityLaw`.

Scope. One epoch: composing the first-order terms along a history of epochs and pulses is not
stated. The forward moment equation with selection is a hypothesis at both budgets.

## Empirical status

None. The bodies here are integrals of matrix exponentials of supplied rate tables and norm
inequalities, so no measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.SelectionMomentExpansion

open MvPolynomial PartialHaplotypeCarrier PartialHaplotypeDualGenerator
  PartialHaplotypeDualSemigroup SubstochasticGeneratorSemigroup NeutralPolynomialSemigroup
  EndToEndPortabilityLaw PortabilityMetricCompilation SelectionHistoryMoments
  EndToEndSelectionLaw
open Descent.Coalescent Descent.Foundations
open Descent.Pangenome.AncestralLocality.DecisionDysonDual (hasDerivAt_integral_from_zero
  continuous_integral_from_zero)
open scoped Matrix

variable {Deme Locus : Type*} {Allele : Locus → Type*}
variable [Fintype Deme] [DecidableEq Deme] [Fintype Locus] [DecidableEq Locus]
  [∀ ℓ, Fintype (Allele ℓ)] [∀ ℓ, DecidableEq (Allele ℓ)]

noncomputable section

/-! ## The selection matrix in sup norm -/

/-- The budget with one more copy at the selected locus has total size one more. -/
theorem sum_bumpCapacity (model : SelectionModel Deme Locus Allele) (capacity : Locus → ℕ) :
    ∑ ℓ, bumpCapacity model capacity ℓ = ∑ ℓ, capacity ℓ + 1 := by
  have hpoint : ∀ ℓ, bumpCapacity model capacity ℓ
      = capacity ℓ + if ℓ = model.locus then 1 else 0 := by
    intro ℓ
    by_cases hℓ : ℓ = model.locus
    · subst hℓ
      simp [bumpCapacity]
    · simp [bumpCapacity, Function.update_of_ne hℓ, hℓ]
  simp [hpoint, Finset.sum_add_distrib]

/-- **The selection terms carry the fitness mass of every carrier**: summing `|rate| c` over the
selection terms of a configuration gives `Σ_{τ ∈ ξ} (Σ_b |s_{τ.deme}(b)|) c`. -/
theorem sum_map_abs_rate_selectionTerms (model : SelectionModel Deme Locus Allele)
    (ξ : Multiset (PartialType Deme Locus Allele)) (c : ℝ) :
    ((selectionTerms model ξ).map fun term ↦ |term.1| * c).sum
      = (ξ.map fun τ ↦ (∑ b, |model.fitness τ.deme b|) * c).sum := by
  rw [selectionTerms, Multiset.map_bind, Multiset.sum_bind]
  refine congrArg Multiset.sum (Multiset.map_congr rfl fun τ _ ↦ ?_)
  simp only [Multiset.map_map, Function.comp_def, Finset.sum_mul, Finset.sum_eq_multiset_sum]

/-- **The selection matrix costs at most `2 B S` in sup norm**, for fitness masses
`Σ_b |s_i(b)| ≤ S` and a budget of total size `B = Σ_ℓ n_ℓ`. -/
theorem norm_selectionMatrix_mulVec_le (model : SelectionModel Deme Locus Allele) {S : ℝ}
    (hS0 : 0 ≤ S) (hS : ∀ i, ∑ b, |model.fitness i b| ≤ S) (capacity : Locus → ℕ)
    (w : BudgetConfiguration Deme Locus Allele (bumpCapacity model capacity) → ℝ) :
    ‖selectionMatrix model capacity *ᵥ w‖ ≤ 2 * (∑ ℓ, capacity ℓ : ℕ) * S * ‖w‖ := by
  have hw : (fun η : BudgetConfiguration Deme Locus Allele (bumpCapacity model capacity) ↦
      extendByZero w η.1) = w := funext fun η ↦ by simp only [extendByZero, dif_pos η.2]
  have hvalue : ∀ ζ, |extendByZero w ζ| ≤ ‖w‖ := by
    intro ζ
    unfold extendByZero
    split_ifs with h
    · simpa only [Real.norm_eq_abs] using norm_le_pi_norm w ⟨ζ, h⟩
    · simpa using norm_nonneg w
  have hterm : ∀ term ∈ selectionTerms model ξ.1,
      |term.1 * (term.2.1.elim 0 (extendByZero w) - extendByZero w term.2.2)|
        ≤ |term.1| * (2 * ‖w‖) := by
    intro term _
    have helim : |term.2.1.elim 0 (extendByZero w)| ≤ ‖w‖ := by
      rcases term.2.1 with _ | ζ
      · simpa using norm_nonneg w
      · exact hvalue ζ
    have hlost := abs_le.mp (hvalue term.2.2)
    have hgain := abs_le.mp helim
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (abs_le.mpr ⟨by linarith, by linarith⟩) (abs_nonneg _)
  refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun ξ ↦ ?_
  rw [Real.norm_eq_abs]
  conv_lhs => rw [← hw, selectionMatrix_mulVec]
  calc |((selectionTerms model ξ.1).map fun term ↦
        term.1 * (term.2.1.elim 0 (extendByZero w) - extendByZero w term.2.2)).sum|
      ≤ ((selectionTerms model ξ.1).map fun term ↦ |term.1| * (2 * ‖w‖)).sum := by
        refine Multiset.abs_sum_le_sum_abs.trans ?_
        rw [Multiset.map_map]
        exact Multiset.sum_map_le_sum_map _ _ fun term hmem ↦ hterm term hmem
    _ = (ξ.1.map fun τ ↦ (∑ b, |model.fitness τ.deme b|) * (2 * ‖w‖)).sum :=
        sum_map_abs_rate_selectionTerms model ξ.1 _
    _ ≤ (ξ.1.map fun _ ↦ S * (2 * ‖w‖)).sum :=
        Multiset.sum_map_le_sum_map _ _ fun τ _ ↦
          mul_le_mul_of_nonneg_right (hS τ.deme) (by positivity)
    _ = Multiset.card ξ.1 * (S * (2 * ‖w‖)) := by
        rw [Multiset.map_const', Multiset.sum_replicate, nsmul_eq_mul]
    _ ≤ (∑ ℓ, capacity ℓ : ℕ) * (S * (2 * ‖w‖)) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast card_le_capacity_total capacity ξ.1 ξ.2)
          (by positivity)
    _ = 2 * (∑ ℓ, capacity ℓ : ℕ) * S * ‖w‖ := by ring

/-! ## Duhamel to first order -/

/-- **Duhamel's formula to first order.** Let `Q` be a killing generator, `B` cost at most `β` in
sup norm, and a vector `v` move on `[0, d]` with right derivative `Q v + B w(t)`, where `w(t)` stays
within `c t` of `e^{tQ'} w(0)`. Then
`‖v(d) - e^{dQ} v(0) - ∫_0^d e^{(d-t)Q} B e^{tQ'} w(0) dt‖ ≤ β c d² / 2`. -/
theorem norm_duhamel_firstOrder_le {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] {Q : Matrix ι ι ℝ} (hQ : KillingGenerator Q) (Q' : Matrix κ κ ℝ)
    (B : Matrix ι κ ℝ) {β c : ℝ} (hβ : 0 ≤ β) (hB : ∀ x, ‖B *ᵥ x‖ ≤ β * ‖x‖)
    {v : ℝ → ι → ℝ} {w : ℝ → κ → ℝ} {d : ℝ} (hd : 0 ≤ d) (hv : ContinuousOn v (Set.Icc 0 d))
    (hderiv : ∀ t ∈ Set.Ico 0 d, HasDerivWithinAt v (Q *ᵥ v t + B *ᵥ w t) (Set.Ici t) t)
    (hw : ∀ t ∈ Set.Ico 0 d, ‖w t - matrixExponential Q' t *ᵥ w 0‖ ≤ c * t) :
    ‖v d - matrixExponential Q d *ᵥ v 0
        - ∫ t in (0 : ℝ)..d, matrixExponential Q (d - t)
          *ᵥ (B *ᵥ (matrixExponential Q' t *ᵥ w 0))‖ ≤ β * c * (d * d) / 2 := by
  have hcontg : Continuous fun t ↦ matrixExponential Q (d - t)
      *ᵥ (B *ᵥ (matrixExponential Q' t *ᵥ w 0)) := by
    have hinner : Continuous fun t ↦ B *ᵥ (matrixExponential Q' t *ᵥ w 0) :=
      continuous_const.matrix_mulVec (continuous_iff_continuousAt.mpr fun t ↦
        (StationaryHaplotypeRealization.hasDerivAt_matrixExponential_mulVec Q' (w 0)
          t).continuousAt)
    exact continuousOn_univ.mp (continuousOn_propagator_mulVec Q d hinner.continuousOn)
  have hderivψ : ∀ t ∈ Set.Ico 0 d, HasDerivWithinAt
      (fun u ↦ matrixExponential Q (d - u) *ᵥ v u
        - (∫ s in (0 : ℝ)..u, matrixExponential Q (d - s)
          *ᵥ (B *ᵥ (matrixExponential Q' s *ᵥ w 0)))
        - matrixExponential Q d *ᵥ v 0)
      (matrixExponential Q (d - t) *ᵥ (B *ᵥ (w t - matrixExponential Q' t *ᵥ w 0)))
      (Set.Ici t) t := by
    intro t ht
    have hprod := hasDerivWithinAt_propagator_mulVec Q d (hderiv t ht)
    have hint := (hasDerivAt_integral_from_zero hcontg t).hasDerivWithinAt (s := Set.Ici t)
    have hcomm : matrixExponential Q (d - t) *ᵥ (Q *ᵥ v t)
        = Q *ᵥ (matrixExponential Q (d - t) *ᵥ v t) := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, matrixExponential_mul_comm]
    refine ((hprod.sub hint).sub (hasDerivWithinAt_const t (Set.Ici t)
      (matrixExponential Q d *ᵥ v 0))).congr_deriv ?_
    rw [Matrix.mulVec_add, hcomm, Matrix.mulVec_sub, Matrix.mulVec_sub]
    abel
  have hbound : ∀ t ∈ Set.Ico 0 d,
      ‖matrixExponential Q (d - t) *ᵥ (B *ᵥ (w t - matrixExponential Q' t *ᵥ w 0))‖
        ≤ β * c * t := by
    intro t ht
    refine (norm_mulVec_le_of_substochastic
      (matrixExponential_substochastic Q hQ (d - t) (sub_nonneg.mpr ht.2.le)) _).trans ?_
    exact (hB _).trans ((mul_le_mul_of_nonneg_left (hw t ht) hβ).trans_eq (by ring))
  have hboundary : ∀ x, HasDerivAt (fun u ↦ β * c * (u * u) / 2) (β * c * x) x := fun x ↦
    ((((hasDerivAt_id x).mul (hasDerivAt_id x)).const_mul (β * c)).div_const 2).congr_deriv
      (by simp only [id_eq]; ring)
  have hmain := image_norm_le_of_norm_deriv_right_le_deriv_boundary
    (((continuousOn_propagator_mulVec Q d hv).sub
      (continuous_integral_from_zero hcontg).continuousOn).sub continuousOn_const)
    hderivψ (by simp) hboundary hbound (Set.right_mem_Icc.mpr hd)
  have heq : v d - matrixExponential Q d *ᵥ v 0
      - ∫ t in (0 : ℝ)..d, matrixExponential Q (d - t) *ᵥ (B *ᵥ (matrixExponential Q' t *ᵥ w 0))
      = matrixExponential Q (d - d) *ᵥ v d
        - (∫ s in (0 : ℝ)..d, matrixExponential Q (d - s)
          *ᵥ (B *ᵥ (matrixExponential Q' s *ᵥ w 0)))
        - matrixExponential Q d *ᵥ v 0 := by
    rw [sub_self, matrixExponential_zero, Matrix.one_mulVec]
    abel
  rw [heq]
  exact hmain

/-! ## The first-order correction of one epoch -/

/-- **The first-order selection correction of one epoch** of length `d`:
`∫_0^d e^{(d-t)Q} B e^{tQ'} w dt`, with `Q` and `Q'` the neutral dual generators of the budget and
of the budget with one more copy at the selected locus, `B` the selection matrix between them and
`w` initial moments of the larger budget. -/
def selectionCorrection (rates : NeutralRates Deme Locus Allele)
    (model : SelectionModel Deme Locus Allele) (capacity : Locus → ℕ)
    (initial : BudgetConfiguration Deme Locus Allele (bumpCapacity model capacity) → ℝ)
    (d : ℝ) : BudgetConfiguration Deme Locus Allele capacity → ℝ :=
  ∫ t in (0 : ℝ)..d, matrixExponential (dualGenerator rates capacity) (d - t)
    *ᵥ (selectionMatrix model capacity
      *ᵥ (matrixExponential (dualGenerator rates (bumpCapacity model capacity)) t *ᵥ initial))

/-- **The moments of an epoch to first order in selection.** Suppose the expected moments of the
budget and of the budget with one more copy at the selected locus are continuous on `[0, d]` and
obey the forward moment equation with selection there, for fitnesses in `[0, σ]` with masses
`Σ_b |s_i(b)| ≤ S`. Then the moments at `d` are the neutral propagator applied to the initial
moments plus the first-order correction, up to `B S B' σ d²` in sup norm, with `B = Σ_ℓ n_ℓ` and
`B' = B + 1`. -/
theorem norm_expectedMomentVector_sub_firstOrder_le (rates : NeutralRates Deme Locus Allele)
    (model : SelectionModel Deme Locus Allele) {σ S : ℝ} (hσ : 0 ≤ σ) (hS0 : 0 ≤ S)
    (hfit : ∀ i b, 0 ≤ model.fitness i b ∧ model.fitness i b ≤ σ)
    (hS : ∀ i, ∑ b, |model.fitness i b| ≤ S) (capacity : Locus → ℕ)
    (expectationAt : ℝ → ExpFunctional (Deme → FiniteReportLaw (FullHaplotype Locus Allele)))
    {d : ℝ} (hd : 0 ≤ d)
    (hcont : ContinuousOn (expectedMomentVector capacity expectationAt) (Set.Icc 0 d))
    (hcont' : ContinuousOn (expectedMomentVector (bumpCapacity model capacity) expectationAt)
      (Set.Icc 0 d))
    (hforward : ∀ ξ : BudgetConfiguration Deme Locus Allele capacity, ∀ t ∈ Set.Ico 0 d,
      HasDerivWithinAt (fun s ↦ expectedMomentVector capacity expectationAt s ξ)
        (expectationAt t fun law ↦
          eval (lawPoint law) (selectedGenerator rates model (momentPolynomial ξ.1)))
        (Set.Ici t) t)
    (hforward' : ∀ ξ : BudgetConfiguration Deme Locus Allele (bumpCapacity model capacity),
      ∀ t ∈ Set.Ico 0 d,
        HasDerivWithinAt
          (fun s ↦ expectedMomentVector (bumpCapacity model capacity) expectationAt s ξ)
          (expectationAt t fun law ↦
            eval (lawPoint law) (selectedGenerator rates model (momentPolynomial ξ.1)))
          (Set.Ici t) t) :
    ‖expectedMomentVector capacity expectationAt d
        - matrixExponential (dualGenerator rates capacity) d
          *ᵥ expectedMomentVector capacity expectationAt 0
        - selectionCorrection rates model capacity
          (expectedMomentVector (bumpCapacity model capacity) expectationAt 0) d‖
      ≤ (∑ ℓ, capacity ℓ : ℕ) * S * ((∑ ℓ, capacity ℓ : ℕ) + 1) * σ * d ^ 2 := by
  have hderiv : ∀ t ∈ Set.Ico 0 d,
      HasDerivWithinAt (expectedMomentVector capacity expectationAt)
        (dualGenerator rates capacity *ᵥ expectedMomentVector capacity expectationAt t
          + selectionMatrix model capacity
            *ᵥ expectedMomentVector (bumpCapacity model capacity) expectationAt t)
        (Set.Ici t) t := by
    intro t ht
    have h := hasDerivWithinAt_pi.mpr fun ξ ↦ (hforward ξ t ht).congr_deriv
      (expectedSelectedGenerator_eq rates model capacity expectationAt t ξ)
    rwa [expectedSelection_eq_mulVec] at h
  have hw : ∀ t ∈ Set.Ico 0 d,
      ‖expectedMomentVector (bumpCapacity model capacity) expectationAt t
          - matrixExponential (dualGenerator rates (bumpCapacity model capacity)) t
            *ᵥ expectedMomentVector (bumpCapacity model capacity) expectationAt 0‖
        ≤ ((∑ ℓ, capacity ℓ : ℕ) + 1) * σ * t := by
    intro t ht
    have h := norm_expectedMomentVector_sub_propagator_le rates model hσ hfit
      (bumpCapacity model capacity) expectationAt ht.1
      (hcont'.mono (Set.Icc_subset_Icc_right ht.2.le))
      (fun ξ s hs ↦ hforward' ξ s ⟨hs.1, hs.2.trans ht.2⟩)
    rw [sum_bumpCapacity] at h
    push_cast at h
    simpa only [sub_zero] using h
  have h := norm_duhamel_firstOrder_le (killingGenerator_dualGenerator rates capacity)
    (dualGenerator rates (bumpCapacity model capacity)) (selectionMatrix model capacity)
    (by positivity) (norm_selectionMatrix_mulVec_le model hS0 hS capacity) hd hcont hderiv hw
  rw [selectionCorrection]
  exact h.trans_eq (by ring)

/-- **An expected polynomial to first order in selection.** Under the hypotheses of
`norm_expectedMomentVector_sub_firstOrder_le`, a polynomial whose monomials fit the budget has
expectation at `d` equal to its coefficient vector on the neutrally propagated moments plus its
coefficient vector on the first-order correction, up to `‖c‖₁ B S B' σ d²`. -/
theorem abs_expectedPolynomial_sub_firstOrder_le (ℓ₀ : Locus)
    (rates : NeutralRates Deme Locus Allele)
    (model : SelectionModel Deme Locus Allele) {σ S : ℝ} (hσ : 0 ≤ σ) (hS0 : 0 ≤ S)
    (hfit : ∀ i b, 0 ≤ model.fitness i b ∧ model.fitness i b ≤ σ)
    (hS : ∀ i, ∑ b, |model.fitness i b| ≤ S) (capacity : Locus → ℕ)
    (expectationAt : ℝ → ExpFunctional (Deme → FiniteReportLaw (FullHaplotype Locus Allele)))
    {d : ℝ} (hd : 0 ≤ d)
    (hcont : ContinuousOn (expectedMomentVector capacity expectationAt) (Set.Icc 0 d))
    (hcont' : ContinuousOn (expectedMomentVector (bumpCapacity model capacity) expectationAt)
      (Set.Icc 0 d))
    (hforward : ∀ ξ : BudgetConfiguration Deme Locus Allele capacity, ∀ t ∈ Set.Ico 0 d,
      HasDerivWithinAt (fun s ↦ expectedMomentVector capacity expectationAt s ξ)
        (expectationAt t fun law ↦
          eval (lawPoint law) (selectedGenerator rates model (momentPolynomial ξ.1)))
        (Set.Ici t) t)
    (hforward' : ∀ ξ : BudgetConfiguration Deme Locus Allele (bumpCapacity model capacity),
      ∀ t ∈ Set.Ico 0 d,
        HasDerivWithinAt
          (fun s ↦ expectedMomentVector (bumpCapacity model capacity) expectationAt s ξ)
          (expectationAt t fun law ↦
            eval (lawPoint law) (selectedGenerator rates model (momentPolynomial ξ.1)))
          (Set.Ici t) t)
    (p : FrequencyPolynomial Deme Locus Allele)
    (hp : ∀ β ∈ p.support, WithinBudget capacity (monomialConfiguration ℓ₀ β)) :
    |(expectationAt d fun law ↦ eval (lawPoint law) p)
        - budgetCoefficients ℓ₀ capacity p
          ⬝ᵥ (matrixExponential (dualGenerator rates capacity) d
            *ᵥ expectedMomentVector capacity expectationAt 0)
        - budgetCoefficients ℓ₀ capacity p
          ⬝ᵥ selectionCorrection rates model capacity
            (expectedMomentVector (bumpCapacity model capacity) expectationAt 0) d|
      ≤ (∑ i, |budgetCoefficients ℓ₀ capacity p i|)
        * ((∑ ℓ, capacity ℓ : ℕ) * S * ((∑ ℓ, capacity ℓ : ℕ) + 1) * σ * d ^ 2) := by
  have hmain := norm_expectedMomentVector_sub_firstOrder_le rates model hσ hS0 hfit hS capacity
    expectationAt hd hcont hcont' hforward hforward'
  rw [expectation_polynomial_eq_dotProduct ℓ₀ capacity p hp, ← dotProduct_sub, ← dotProduct_sub]
  refine (abs_dotProduct_le _ _ fun i ↦ ?_).trans
    (mul_le_mul_of_nonneg_left hmain (Finset.sum_nonneg fun i _ ↦ abs_nonneg _))
  simpa only [Real.norm_eq_abs] using norm_le_pi_norm
    (expectedMomentVector capacity expectationAt d
      - matrixExponential (dualGenerator rates capacity) d
        *ᵥ expectedMomentVector capacity expectationAt 0
      - selectionCorrection rates model capacity
        (expectedMomentVector (bumpCapacity model capacity) expectationAt 0) d) i

end

end Descent.Portability.SelectionMomentExpansion
