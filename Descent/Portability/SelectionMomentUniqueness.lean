/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.SelectionMomentExpansion

assert_below Descent.Decision Descent.Program

/-!
# Selected moment families are determined by their initial moments

`SelectionHistoryMoments` writes the forward moment equation with selection as
`v_n' = Q_n v_n + B_n v_{n + 1_ℓ}`. The budget-`n` moments move with the neutral dual generator and
with the selection matrix acting on the budget that has one more copy at the selected locus. The
system closes on no budget (`EndToEndSelectionLaw.not_exists_budgetFour_selectionClosure`), so the
uniqueness of its solutions is not the uniqueness of a finite linear differential equation. This
module proves it for bounded families.

Moment families. A family is a table `m t ξ` of values on all configurations at every time. It
obeys the moment equation with selection when, for every budget, its restriction
(`restrictBudget`) is continuous on `[0, ∞)` and has right derivative `Q_n v_n + B_n v_{n + 1_ℓ}`
at every `t ≥ 0`. The expected configuration moments of an expectation family are its restriction
(`expectedMomentVector_eq_restrictBudget`).

The argument. The difference of two families obeys the same linear equation, starts at zero and is
at most `2` in absolute value.
- From a zero start, a vector moving with `u' = Q u + g(t)` along a killing generator `Q` stays
  below every `G` with `G(0) ≥ 0` whose derivative dominates `‖g‖` (`norm_le_of_zeroStart`).
- The selection matrix costs at most `2 B S`
  (`SelectionMomentExpansion.norm_selectionMatrix_mulVec_le`), and the larger budget has size
  `B + 1` (`SelectionMomentExpansion.sum_bumpCapacity`).
- By induction on the number `j` of selection steps, `‖d_n(t)‖ ≤ 2 C(B + j, j) (2 S t)^j` at every
  budget (`norm_restrictBudget_difference_le`). The binomial step is
  `B C(B + 1 + j, j) ≤ C(B + 1 + j, j + 1) (j + 1)` (`cast_mul_choose_le`).
- These are the terms of a convergent series while `2 S t < 1`, so the difference vanishes there
  (`difference_eq_zero_of_lt`). Shifting time extends this to every `t ≥ 0` (`difference_eq_zero`).
So two bounded families obeying the moment equation with selection that agree at time zero agree at
every time (`moments_eq_of_selectedMomentEquation`). In particular, two selected expectation
families with equal initial moments have equal moments at every time
(`expectedMoments_eq_of_selectedForward`).

Relation to the corpus. `AncestralLocality.moments_eq_of_branchingEquation` proves the same
conclusion for one panmictic window. There the moment functionals act on observations of sampled
genomes, and every pair coalesces at a common rate. The neutral part of the configuration dual of
several demes carries migration, recombination and deme-dependent coalescence, so that theorem does
not apply. The proof here runs the same Duhamel iteration, with the finite dual generators in place
of the coalescence gain.

Scope. The families are bounded by one and continuous on `[0, ∞)`, and the forward moment equation
is assumed at every budget. Existence of a selected family is not proved here.

## Empirical status

None. The bodies here are norm inequalities along matrix exponentials and binomial series, so no
measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.SelectionMomentUniqueness

open MvPolynomial PartialHaplotypeCarrier PartialHaplotypeDualGenerator
  PartialHaplotypeDualSemigroup SubstochasticGeneratorSemigroup NeutralPolynomialSemigroup
  SelectionHistoryMoments SelectionMomentExpansion
open Descent.Coalescent Descent.Foundations Filter Topology
open scoped Matrix

variable {Deme Locus : Type*} {Allele : Locus → Type*}
variable [Fintype Deme] [DecidableEq Deme] [Fintype Locus] [DecidableEq Locus]
  [∀ ℓ, Fintype (Allele ℓ)] [∀ ℓ, DecidableEq (Allele ℓ)]

noncomputable section

/-! ## A zero start along a killing generator -/

/-- **A vector started at zero stays below its forcing.** If `u(0) = 0` and `u` moves on `[0, t]`
with right derivative `Q u + g` for a killing generator `Q`, then `‖u(t)‖ ≤ G(t)` for every `G`
with `G(0) ≥ 0` whose derivative dominates `‖g‖`. -/
theorem norm_le_of_zeroStart {ι : Type*} [Fintype ι] [DecidableEq ι] {Q : Matrix ι ι ℝ}
    (hQ : KillingGenerator Q) {u g : ℝ → ι → ℝ} {G G' : ℝ → ℝ} {t : ℝ} (ht : 0 ≤ t)
    (hu : ContinuousOn u (Set.Icc 0 t))
    (hderiv : ∀ s ∈ Set.Ico 0 t, HasDerivWithinAt u (Q *ᵥ u s + g s) (Set.Ici s) s)
    (hu0 : u 0 = 0) (hG0 : 0 ≤ G 0) (hG : ∀ x, HasDerivAt G (G' x) x)
    (hg : ∀ s ∈ Set.Ico 0 t, ‖g s‖ ≤ G' s) : ‖u t‖ ≤ G t := by
  have hψ : ∀ s ∈ Set.Ico 0 t, HasDerivWithinAt (fun r ↦ matrixExponential Q (t - r) *ᵥ u r)
      (matrixExponential Q (t - s) *ᵥ g s) (Set.Ici s) s := by
    intro s hs
    refine (hasDerivWithinAt_propagator_mulVec Q t (hderiv s hs)).congr_deriv ?_
    rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, matrixExponential_mul_comm]
    abel
  have h := image_norm_le_of_norm_deriv_right_le_deriv_boundary
    (continuousOn_propagator_mulVec Q t hu) hψ (by simpa [hu0] using hG0) hG
    (fun s hs ↦ (norm_mulVec_le_of_substochastic
      (matrixExponential_substochastic Q hQ (t - s) (sub_nonneg.mpr hs.2.le)) _).trans (hg s hs))
    (Set.right_mem_Icc.mpr ht)
  simpa only [sub_self, matrixExponential_zero, Matrix.one_mulVec] using h

/-! ## Moment families -/

/-- The values of a table over configurations, read on the configurations of a budget. -/
def restrictBudget (capacity : Locus → ℕ) (value : Multiset (PartialType Deme Locus Allele) → ℝ) :
    BudgetConfiguration Deme Locus Allele capacity → ℝ :=
  fun η ↦ value η.1

/-- The expected moment vector of a budget is the restriction of the expected configuration
moments. -/
theorem expectedMomentVector_eq_restrictBudget (capacity : Locus → ℕ)
    (expectationAt : ℝ → ExpFunctional (Deme → FiniteReportLaw (FullHaplotype Locus Allele)))
    (s : ℝ) :
    expectedMomentVector capacity expectationAt s
      = restrictBudget capacity fun ξ ↦ expectationAt s fun law ↦ configurationMoment law ξ :=
  rfl

/-- Restriction to a budget commutes with differences. -/
theorem restrictBudget_sub (capacity : Locus → ℕ)
    (value value' : Multiset (PartialType Deme Locus Allele) → ℝ) :
    restrictBudget capacity (fun ξ ↦ value ξ - value' ξ)
      = restrictBudget capacity value - restrictBudget capacity value' :=
  rfl

/-- **The binomial step of the iteration**: `B C(B + 1 + j, j) ≤ C(B + 1 + j, j + 1) (j + 1)`. -/
theorem cast_mul_choose_le (K j : ℕ) :
    (K : ℝ) * ((K + 1 + j).choose j : ℝ)
      ≤ ((K + 1 + j).choose (j + 1) : ℝ) * ((j + 1 : ℕ) : ℝ) := by
  have h := Nat.choose_succ_right_eq (K + 1 + j) j
  rw [show K + 1 + j - j = K + 1 by omega] at h
  have hcast : ((K + 1 + j).choose (j + 1) : ℝ) * ((j + 1 : ℕ) : ℝ)
      = ((K + 1 + j).choose j : ℝ) * ((K + 1 : ℕ) : ℝ) := by
    exact_mod_cast h
  rw [hcast]
  have hC := Nat.cast_nonneg (α := ℝ) ((K + 1 + j).choose j)
  push_cast
  nlinarith

section Difference

variable (rates : NeutralRates Deme Locus Allele) (model : SelectionModel Deme Locus Allele)
  {S : ℝ} (hS0 : 0 ≤ S) (hS : ∀ i, ∑ b, |model.fitness i b| ≤ S)
  (d : ℝ → Multiset (PartialType Deme Locus Allele) → ℝ)
  (hd : ∀ (capacity : Locus → ℕ), ∀ s ∈ Set.Ici (0 : ℝ),
    HasDerivWithinAt (fun r ↦ restrictBudget capacity (d r))
      (dualGenerator rates capacity *ᵥ restrictBudget capacity (d s)
        + selectionMatrix model capacity *ᵥ restrictBudget (bumpCapacity model capacity) (d s))
      (Set.Ici s) s)
  (hcont : ∀ capacity : Locus → ℕ,
    ContinuousOn (fun r ↦ restrictBudget capacity (d r)) (Set.Ici 0))
  (hbound : ∀ s ∈ Set.Ici (0 : ℝ), ∀ ξ, |d s ξ| ≤ 2)

include hS0 hS hd hcont hbound in
/-- **Every selection step costs a factor `2 S t`.** A family obeying the moment equation with
selection, at most `2` in absolute value and zero at time zero, has
`‖d_n(t)‖ ≤ 2 C(B + j, j) (2 S t)^j` at every budget of total size `B`, every `t ≥ 0` and every
number `j` of steps. -/
theorem norm_restrictBudget_difference_le (hzero : ∀ ξ, d 0 ξ = 0) (j : ℕ) :
    ∀ (capacity : Locus → ℕ) {t : ℝ}, 0 ≤ t →
      ‖restrictBudget capacity (d t)‖
        ≤ 2 * ((∑ ℓ, capacity ℓ + j).choose j : ℝ) * (2 * S * t) ^ j := by
  induction j with
  | zero =>
    intro capacity t ht
    simp only [Nat.choose_zero_right, Nat.cast_one, pow_zero, mul_one]
    exact (pi_norm_le_iff_of_nonneg zero_le_two).mpr fun ξ ↦ by
      rw [Real.norm_eq_abs]
      exact hbound t ht ξ.1
  | succ j ih =>
    intro capacity t ht
    have hbump := sum_bumpCapacity model capacity
    have hmain := norm_le_of_zeroStart (killingGenerator_dualGenerator rates capacity) ht
      ((hcont capacity).mono Set.Icc_subset_Ici_self) (fun s hs ↦ hd capacity s hs.1)
      (funext fun ξ ↦ hzero ξ.1)
      (G := fun x ↦ 2 * ((∑ ℓ, capacity ℓ + 1 + j).choose (j + 1) : ℝ) * (2 * S) ^ (j + 1)
        * x ^ (j + 1))
      (G' := fun x ↦ 2 * ((∑ ℓ, capacity ℓ + 1 + j).choose (j + 1) : ℝ) * (2 * S) ^ (j + 1)
        * (((j + 1 : ℕ) : ℝ) * x ^ j))
      (by simp)
      (fun x ↦ by
        simpa using (hasDerivAt_pow (j + 1) x).const_mul
          (2 * ((∑ ℓ, capacity ℓ + 1 + j).choose (j + 1) : ℝ) * (2 * S) ^ (j + 1)))
      (fun s hs ↦ by
        have hih := ih (bumpCapacity model capacity) hs.1
        rw [hbump] at hih
        calc ‖selectionMatrix model capacity
              *ᵥ restrictBudget (bumpCapacity model capacity) (d s)‖
            ≤ 2 * (∑ ℓ, capacity ℓ : ℕ) * S
              * ‖restrictBudget (bumpCapacity model capacity) (d s)‖ :=
              norm_selectionMatrix_mulVec_le model hS0 hS capacity _
          _ ≤ 2 * (∑ ℓ, capacity ℓ : ℕ) * S
              * (2 * ((∑ ℓ, capacity ℓ + 1 + j).choose j : ℝ) * (2 * S * s) ^ j) :=
              mul_le_mul_of_nonneg_left hih (by positivity)
          _ = 4 * S * (2 * S) ^ j * s ^ j
              * ((∑ ℓ, capacity ℓ : ℕ) * ((∑ ℓ, capacity ℓ + 1 + j).choose j : ℝ)) := by
              ring
          _ ≤ 4 * S * (2 * S) ^ j * s ^ j
              * (((∑ ℓ, capacity ℓ + 1 + j).choose (j + 1) : ℝ) * ((j + 1 : ℕ) : ℝ)) :=
              mul_le_mul_of_nonneg_left (cast_mul_choose_le _ j)
                (mul_nonneg (by positivity) (pow_nonneg hs.1 j))
          _ = 2 * ((∑ ℓ, capacity ℓ + 1 + j).choose (j + 1) : ℝ) * (2 * S) ^ (j + 1)
              * (((j + 1 : ℕ) : ℝ) * s ^ j) := by
              ring)
    rw [show ∑ ℓ, capacity ℓ + (j + 1) = ∑ ℓ, capacity ℓ + 1 + j by omega, mul_pow]
    exact hmain.trans_eq (by ring)

include hS0 hS hd hcont hbound in
/-- **A family starting at zero stays at zero while `2 S t < 1`.** -/
theorem difference_eq_zero_of_lt (hzero : ∀ ξ, d 0 ξ = 0) {t : ℝ} (ht : 0 ≤ t)
    (hSt : 2 * S * t < 1) (capacity : Locus → ℕ) : restrictBudget capacity (d t) = 0 := by
  have hr : ‖2 * S * t‖ < 1 := by
    rwa [Real.norm_of_nonneg (by positivity)]
  have hsum := summable_choose_mul_geometric_of_norm_lt_one (∑ ℓ, capacity ℓ) hr
  have htends : Tendsto (fun j : ℕ ↦
      2 * ((∑ ℓ, capacity ℓ + j).choose j : ℝ) * (2 * S * t) ^ j) atTop (𝓝 0) := by
    have h := hsum.tendsto_cofinite_zero
    rw [Nat.cofinite_eq_atTop] at h
    have h2 := h.const_mul 2
    rw [mul_zero] at h2
    refine h2.congr fun j ↦ ?_
    rw [add_comm j, Nat.choose_symm_add]
    ring
  have hle : ‖restrictBudget capacity (d t)‖ ≤ 0 := ge_of_tendsto' htends fun j ↦
    norm_restrictBudget_difference_le rates model hS0 hS d hd hcont hbound hzero j capacity ht
  exact norm_le_zero_iff.mp hle

include hS0 hS hd hcont hbound in
/-- **A family starting at zero stays at zero**, at every `t ≥ 0`: the short-time statement,
applied after shifting time in steps of `1 / (2 S + 1)`. -/
theorem difference_eq_zero (hzero : ∀ ξ, d 0 ξ = 0) {t : ℝ} (ht : 0 ≤ t)
    (capacity : Locus → ℕ) : restrictBudget capacity (d t) = 0 := by
  have hτ0 : 0 < 1 / (2 * S + 1) := one_div_pos.mpr (by linarith)
  have hSτ : 2 * S * (1 / (2 * S + 1)) < 1 := by
    rw [mul_one_div, div_lt_one (by linarith)]
    linarith
  have hentry : ∀ r : ℝ, (∀ capacity : Locus → ℕ, restrictBudget capacity (d r) = 0) →
      ∀ ξ, d r ξ = 0 := fun r h ξ ↦
    congrFun (h (cardinalityBudget ξ)) ⟨ξ, withinBudget_cardinalityBudget ξ⟩
  have hstep : ∀ k : ℕ, ∀ r : ℝ, 0 ≤ r → r ≤ k * (1 / (2 * S + 1)) →
      ∀ capacity : Locus → ℕ, restrictBudget capacity (d r) = 0 := by
    intro k
    induction k with
    | zero =>
      intro r hr0 hr capacity
      have hr' : r = 0 := le_antisymm (by simpa using hr) hr0
      subst hr'
      exact funext fun ξ ↦ hzero ξ.1
    | succ k ih =>
      intro r hr0 hr capacity
      by_cases hrk : r ≤ k * (1 / (2 * S + 1))
      · exact ih r hr0 hrk capacity
      · push_neg at hrk
        have hk0 : 0 ≤ (k : ℝ) * (1 / (2 * S + 1)) := mul_nonneg (Nat.cast_nonneg k) hτ0.le
        have hshift := difference_eq_zero_of_lt rates model hS0 hS
          (fun v ↦ d (k * (1 / (2 * S + 1)) + v))
          (fun capacity' v hv ↦ by
            have hadd : HasDerivWithinAt (fun w : ℝ ↦ (k : ℝ) * (1 / (2 * S + 1)) + w) 1
                (Set.Ici v) v :=
              ((hasDerivAt_id (x := v)).const_add _).hasDerivWithinAt
            have h := HasDerivWithinAt.scomp (hg := hd capacity' _ (add_nonneg hk0 hv))
              (hh := hadd) (hst := fun w hw ↦ by
                simp only [Set.mem_Ici] at hw ⊢
                linarith)
            simpa using h)
          (fun capacity' ↦ (hcont capacity').comp' (Continuous.continuousOn (by fun_prop))
            fun v hv ↦ by
              simp only [Set.mem_Ici] at hv ⊢
              linarith)
          (fun v hv ξ ↦ hbound _ (add_nonneg hk0 hv) ξ)
          (fun ξ ↦ by simpa using hentry _ (ih _ hk0 le_rfl) ξ)
          (sub_nonneg.mpr hrk.le)
          (by
            push_cast at hr
            calc 2 * S * (r - k * (1 / (2 * S + 1))) ≤ 2 * S * (1 / (2 * S + 1)) :=
                  mul_le_mul_of_nonneg_left (by linarith) (by linarith)
              _ < 1 := hSτ)
          capacity
        simpa using hshift
  obtain ⟨k, hk⟩ := exists_nat_ge (t / (1 / (2 * S + 1)))
  exact hstep k t ht (by rwa [div_le_iff₀ hτ0] at hk) capacity

end Difference

/-- **Bounded selected moment families are determined by their initial moments.** Two tables of
configuration values, each at most one in absolute value, continuous on `[0, ∞)` at every budget
and obeying the moment equation with selection there for fitness masses `Σ_b |s_i(b)| ≤ S`, that
agree at time zero agree at every time `t ≥ 0`. -/
theorem moments_eq_of_selectedMomentEquation (rates : NeutralRates Deme Locus Allele)
    (model : SelectionModel Deme Locus Allele) {S : ℝ} (hS0 : 0 ≤ S)
    (hS : ∀ i, ∑ b, |model.fitness i b| ≤ S)
    (m m' : ℝ → Multiset (PartialType Deme Locus Allele) → ℝ)
    (hm : ∀ (capacity : Locus → ℕ), ∀ s ∈ Set.Ici (0 : ℝ),
      HasDerivWithinAt (fun r ↦ restrictBudget capacity (m r))
        (dualGenerator rates capacity *ᵥ restrictBudget capacity (m s)
          + selectionMatrix model capacity *ᵥ restrictBudget (bumpCapacity model capacity) (m s))
        (Set.Ici s) s)
    (hm' : ∀ (capacity : Locus → ℕ), ∀ s ∈ Set.Ici (0 : ℝ),
      HasDerivWithinAt (fun r ↦ restrictBudget capacity (m' r))
        (dualGenerator rates capacity *ᵥ restrictBudget capacity (m' s)
          + selectionMatrix model capacity *ᵥ restrictBudget (bumpCapacity model capacity) (m' s))
        (Set.Ici s) s)
    (hcont : ∀ capacity : Locus → ℕ,
      ContinuousOn (fun r ↦ restrictBudget capacity (m r)) (Set.Ici 0))
    (hcont' : ∀ capacity : Locus → ℕ,
      ContinuousOn (fun r ↦ restrictBudget capacity (m' r)) (Set.Ici 0))
    (hbound : ∀ s ∈ Set.Ici (0 : ℝ), ∀ ξ, |m s ξ| ≤ 1)
    (hbound' : ∀ s ∈ Set.Ici (0 : ℝ), ∀ ξ, |m' s ξ| ≤ 1)
    (h0 : ∀ ξ, m 0 ξ = m' 0 ξ) {t : ℝ} (ht : 0 ≤ t) (ξ : Multiset (PartialType Deme Locus Allele)) :
    m t ξ = m' t ξ := by
  have hdiff := difference_eq_zero rates model hS0 hS (fun r ζ ↦ m r ζ - m' r ζ)
    (fun capacity s hs ↦ by
      rw [show (fun r ↦ restrictBudget capacity fun ζ ↦ m r ζ - m' r ζ)
          = fun r ↦ restrictBudget capacity (m r) - restrictBudget capacity (m' r) from
        funext fun r ↦ restrictBudget_sub capacity (m r) (m' r), restrictBudget_sub,
        restrictBudget_sub]
      refine ((hm capacity s hs).sub (hm' capacity s hs)).congr_deriv ?_
      rw [Matrix.mulVec_sub, Matrix.mulVec_sub]
      abel)
    (fun capacity ↦ by
      rw [show (fun r ↦ restrictBudget capacity fun ζ ↦ m r ζ - m' r ζ)
          = fun r ↦ restrictBudget capacity (m r) - restrictBudget capacity (m' r) from
        funext fun r ↦ restrictBudget_sub capacity (m r) (m' r)]
      exact (hcont capacity).sub (hcont' capacity))
    (fun s hs ζ ↦ by
      have h1 := abs_le.mp (hbound s hs ζ)
      have h2 := abs_le.mp (hbound' s hs ζ)
      exact abs_le.mpr ⟨by linarith [h1.1, h2.2], by linarith [h1.2, h2.1]⟩)
    (fun ζ ↦ sub_eq_zero.mpr (h0 ζ)) ht (cardinalityBudget ξ)
  exact sub_eq_zero.mp (congrFun hdiff ⟨ξ, withinBudget_cardinalityBudget ξ⟩)

/-- **Selected expectation families with equal initial moments have equal moments.** Two
expectation families over per-deme laws, with expected moments continuous on `[0, ∞)` at every
budget and obeying the forward moment equation with selection there, for fitness masses
`Σ_b |s_i(b)| ≤ S`, that agree on every configuration moment at time zero agree on every
configuration moment at every time `t ≥ 0`. -/
theorem expectedMoments_eq_of_selectedForward (rates : NeutralRates Deme Locus Allele)
    (model : SelectionModel Deme Locus Allele) {S : ℝ} (hS0 : 0 ≤ S)
    (hS : ∀ i, ∑ b, |model.fitness i b| ≤ S)
    (first second :
      ℝ → ExpFunctional (Deme → FiniteReportLaw (FullHaplotype Locus Allele)))
    (hfirst : ∀ (capacity : Locus → ℕ) (ξ : BudgetConfiguration Deme Locus Allele capacity),
      ∀ t ∈ Set.Ici (0 : ℝ),
        HasDerivWithinAt (fun s ↦ expectedMomentVector capacity first s ξ)
          (first t fun law ↦
            eval (lawPoint law) (selectedGenerator rates model (momentPolynomial ξ.1)))
          (Set.Ici t) t)
    (hsecond : ∀ (capacity : Locus → ℕ) (ξ : BudgetConfiguration Deme Locus Allele capacity),
      ∀ t ∈ Set.Ici (0 : ℝ),
        HasDerivWithinAt (fun s ↦ expectedMomentVector capacity second s ξ)
          (second t fun law ↦
            eval (lawPoint law) (selectedGenerator rates model (momentPolynomial ξ.1)))
          (Set.Ici t) t)
    (hcont : ∀ capacity : Locus → ℕ,
      ContinuousOn (expectedMomentVector capacity first) (Set.Ici 0))
    (hcont' : ∀ capacity : Locus → ℕ,
      ContinuousOn (expectedMomentVector capacity second) (Set.Ici 0))
    (h0 : ∀ ξ : Multiset (PartialType Deme Locus Allele),
      (first 0 fun law ↦ configurationMoment law ξ)
        = second 0 fun law ↦ configurationMoment law ξ)
    {t : ℝ} (ht : 0 ≤ t) (ξ : Multiset (PartialType Deme Locus Allele)) :
    (first t fun law ↦ configurationMoment law ξ)
      = second t fun law ↦ configurationMoment law ξ := by
  have hderiv : ∀ (expectationAt :
        ℝ → ExpFunctional (Deme → FiniteReportLaw (FullHaplotype Locus Allele))),
      (∀ (capacity : Locus → ℕ) (ξ : BudgetConfiguration Deme Locus Allele capacity),
        ∀ t ∈ Set.Ici (0 : ℝ),
          HasDerivWithinAt (fun s ↦ expectedMomentVector capacity expectationAt s ξ)
            (expectationAt t fun law ↦
              eval (lawPoint law) (selectedGenerator rates model (momentPolynomial ξ.1)))
            (Set.Ici t) t) →
      ∀ (capacity : Locus → ℕ), ∀ s ∈ Set.Ici (0 : ℝ),
        HasDerivWithinAt
          (fun r ↦ restrictBudget capacity fun ζ ↦ expectationAt r fun law ↦
            configurationMoment law ζ)
          (dualGenerator rates capacity
              *ᵥ restrictBudget capacity (fun ζ ↦ expectationAt s fun law ↦
                configurationMoment law ζ)
            + selectionMatrix model capacity
              *ᵥ restrictBudget (bumpCapacity model capacity) (fun ζ ↦ expectationAt s fun law ↦
                configurationMoment law ζ))
          (Set.Ici s) s := by
    intro expectationAt hforward capacity s hs
    have h := hasDerivWithinAt_pi.mpr fun ξ ↦ (hforward capacity ξ s hs).congr_deriv
      (expectedSelectedGenerator_eq rates model capacity expectationAt s ξ)
    rwa [expectedSelection_eq_mulVec] at h
  have hbox : ∀ (expectationAt :
        ℝ → ExpFunctional (Deme → FiniteReportLaw (FullHaplotype Locus Allele))),
      ∀ s ∈ Set.Ici (0 : ℝ), ∀ ζ : Multiset (PartialType Deme Locus Allele),
        |expectationAt s fun law ↦ configurationMoment law ζ| ≤ 1 := by
    intro expectationAt s _ ζ
    have hlow := (expectationAt s).eval_mono (f := fun _ ↦ (0 : ℝ))
      (g := fun law ↦ configurationMoment law ζ) fun law ↦
        PartialHaplotypeCarrier.configurationMoment_nonneg law ζ
    have hhigh := (expectationAt s).eval_mono (f := fun law ↦ configurationMoment law ζ)
      (g := fun _ ↦ (1 : ℝ)) fun law ↦ configurationMoment_le_one law ζ
    simp only [ExpFunctional.eval_const] at hlow hhigh
    exact abs_le.mpr ⟨by linarith, hhigh⟩
  exact moments_eq_of_selectedMomentEquation rates model hS0 hS
    (fun r ζ ↦ first r fun law ↦ configurationMoment law ζ)
    (fun r ζ ↦ second r fun law ↦ configurationMoment law ζ)
    (hderiv first hfirst) (hderiv second hsecond) hcont hcont' (hbox first) (hbox second) h0 ht ξ

end

end Descent.Portability.SelectionMomentUniqueness
