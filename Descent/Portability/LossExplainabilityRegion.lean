/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.HorizonCurve
import Descent.Portability.SymmetricScoreFourthMoment

assert_below Descent.Decision Descent.Program

/-!
# The sharp global loss-explainability region

UPT Theorem 3.5. Across finitely many distance cells with fixed pre-outcome laws,
orthonormal features and prescribed moments `(β_d, k_d, m_d)`, the squared loss `L = E²`
has between-cell variance fixed at `B = Σ π_d (m_d − m̄)²`, while its total variance is
`Σ π_d E[E⁴ | d] − m̄²` and so moves only through the cell fourth moments. Theorem 3.1
bounds each of those below by `V_d` and attains the bound, which pins the fraction
`η_D = B / Var(L)` to the interval `(0, η_max]` with `η_max = B / (J₀ − m̄²)`,
`J₀ = Σ π_d V_d`.

* `between_eq_second_moment_gap` and `between_le_total` give the manuscript's remark that
  the denominator is at least `B`, hence `η_max ≤ 1`.
* `fraction_le_max` is the upper half of (3.21): raising any cell fourth moment above its
  minimum only lowers the fraction.
* `fraction_pos` is the lower half: the fraction is never zero, so `0` is an infimum and
  not a value.
* `fraction_attains` realizes every value of `(0, η_max]` by moving a single cell's fourth
  moment, which UPT Theorem 3.1(c) permits in any cell with strict slack.
* `boundary_fraction_forced` is the degenerate case: with every cell on its deterministic
  boundary the fourth moments are forced and the range is the singleton `{η_max}`.
* `between_eq_variance`, `total_eq_variance` and `sharp_region_for_law` identify the two
  arithmetic quantities above with the actual `Foundations.variance` of the squared loss
  under a multi-cell law built from `IndividualLossMoments.mixture`, so the region is a
  statement about laws and not only about numbers.
* `sparse_example_cell_values` and `sparse_example_max_fraction` are the manuscript's exact
  example: two equally weighted cells carrying the sparse score with `p = 1/2`, `β = 0`,
  `k = 1` and `m₁ = 1`, `m₂ = 2` give `V₁ = 2`, `V₂ = 4` from
  `SymmetricScoreFourthMoment.sparse_symmetric_value`, hence `η_max = 1/3`. The two cells
  are equally weighted, so the cell law is `HorizonCurve.uniformTwo` rather than a second
  copy of it.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.LossExplainabilityRegion

open Foundations IndividualLossMoments FourthMomentDuality GlobalFourthMomentRegion
open SymmetricScoreFourthMoment

noncomputable section

variable {D : Type*} [Fintype D] [DecidableEq D]

/-! ## The two variances of the squared loss -/

/-- The between-cell variance of the squared loss: the numerator of `η_D`, fixed by the
prescribed cell second moments alone. -/
def betweenLossVariance (π m : D → ℝ) : ℝ :=
  ∑ d, π d * (m d - ∑ e, π e * m e) ^ 2

/-- The total variance of the squared loss, given the cell fourth moments `F`. -/
def totalLossVariance (π m F : D → ℝ) : ℝ :=
  (∑ d, π d * F d) - (∑ d, π d * m d) ^ 2

/-- The fraction of squared-loss variance explained by the cell label, `η_D`. -/
def lossExplainedFraction (π m F : D → ℝ) : ℝ :=
  betweenLossVariance π m / totalLossVariance π m F

omit [DecidableEq D] in
/-- The between-cell variance is the gap between the mean of squared cell means and the
square of their mean. -/
theorem between_eq_second_moment_gap (π m : D → ℝ) (hsum : ∑ d, π d = 1) :
    betweenLossVariance π m = (∑ d, π d * m d ^ 2) - (∑ d, π d * m d) ^ 2 := by
  unfold betweenLossVariance
  have h : ∀ d : D, π d * (m d - ∑ e, π e * m e) ^ 2
      = π d * m d ^ 2 - 2 * (∑ e, π e * m e) * (π d * m d)
        + (∑ e, π e * m e) ^ 2 * π d := by
    intro d
    ring
  rw [Finset.sum_congr rfl (fun d _ ↦ h d), Finset.sum_add_distrib,
    Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hsum]
  ring

omit [DecidableEq D] in
/-- **The denominator is at least the numerator (UPT §3.6).** Since every cell fourth
moment is at least the square of its second moment, the total loss variance dominates the
between-cell variance, so `η_max ≤ 1`. -/
theorem between_le_total (π m F : D → ℝ) (hsum : ∑ d, π d = 1) (hπ : ∀ d, 0 ≤ π d)
    (hF : ∀ d, m d ^ 2 ≤ F d) :
    betweenLossVariance π m ≤ totalLossVariance π m F := by
  rw [between_eq_second_moment_gap π m hsum]
  unfold totalLossVariance
  have hle : ∑ d, π d * m d ^ 2 ≤ ∑ d, π d * F d :=
    Finset.sum_le_sum fun d _ ↦ mul_le_mul_of_nonneg_left (hF d) (hπ d)
  linarith

/-! ## The exact attainable range of `η_D` -/

omit [DecidableEq D] in
/-- **The upper half of UPT (3.21).** Raising any cell fourth moment above its minimum
`V_d` can only decrease the explained fraction, so `η_max` computed from the minima is the
largest attainable value. -/
theorem fraction_le_max (π m V F : D → ℝ) (hsum : ∑ d, π d = 1) (hπ : ∀ d, 0 ≤ π d)
    (hV : ∀ d, m d ^ 2 ≤ V d) (hF : ∀ d, V d ≤ F d)
    (hB : 0 < betweenLossVariance π m) :
    lossExplainedFraction π m F ≤ lossExplainedFraction π m V := by
  have hVtot : betweenLossVariance π m ≤ totalLossVariance π m V :=
    between_le_total π m V hsum hπ hV
  have hmono : totalLossVariance π m V ≤ totalLossVariance π m F := by
    unfold totalLossVariance
    have hle : ∑ d, π d * V d ≤ ∑ d, π d * F d :=
      Finset.sum_le_sum fun d _ ↦ mul_le_mul_of_nonneg_left (hF d) (hπ d)
    linarith
  unfold lossExplainedFraction
  exact div_le_div_of_nonneg_left hB.le (by linarith) hmono

omit [DecidableEq D] in
/-- **The lower half of UPT (3.21).** With a positive between-cell variance the explained
fraction is positive for every admissible family of cell fourth moments, so zero is an
infimum that is never attained. -/
theorem fraction_pos (π m F : D → ℝ) (hsum : ∑ d, π d = 1) (hπ : ∀ d, 0 ≤ π d)
    (hF : ∀ d, m d ^ 2 ≤ F d) (hB : 0 < betweenLossVariance π m) :
    0 < lossExplainedFraction π m F := by
  have hVtot : betweenLossVariance π m ≤ totalLossVariance π m F :=
    between_le_total π m F hsum hπ hF
  exact div_pos hB (by linarith)

/-- The cell fourth moments that move one cell off its minimum by a prescribed amount. -/
def raisedFourthMoments (V : D → ℝ) (d₀ : D) (c : ℝ) : D → ℝ :=
  fun d ↦ V d + (if d = d₀ then c else 0)

/-- Raising one cell shifts the weighted total by exactly that cell's weight times the
increment. -/
theorem raised_sum (π V : D → ℝ) (d₀ : D) (c : ℝ) :
    ∑ d, π d * raisedFourthMoments V d₀ c d = (∑ d, π d * V d) + π d₀ * c := by
  unfold raisedFourthMoments
  have h : ∀ d : D, π d * (V d + (if d = d₀ then c else 0))
      = π d * V d + (if d = d₀ then π d * c else 0) := by
    intro d
    by_cases hd : d = d₀
    · rw [if_pos hd, if_pos hd]
      ring
    · rw [if_neg hd, if_neg hd]
      ring
  rw [Finset.sum_congr rfl (fun d _ ↦ h d), Finset.sum_add_distrib,
    Finset.sum_ite_eq' Finset.univ d₀ (fun d ↦ π d * c), if_pos (Finset.mem_univ d₀)]

/-- **Every value of `(0, η_max]` occurs (UPT (3.21)).** Given a target fraction at most
the maximum, moving a single cell's fourth moment up from its minimum by an explicit
amount realizes exactly that fraction. UPT Theorem 3.1(c) supplies a kernel with the
raised fourth moment in any cell with strict slack. -/
theorem fraction_attains (π m V : D → ℝ) (d₀ : D) (hsum : ∑ d, π d = 1)
    (hπ : ∀ d, 0 ≤ π d) (hπ0 : 0 < π d₀) (hV : ∀ d, m d ^ 2 ≤ V d)
    (hB : 0 < betweenLossVariance π m) (η : ℝ) (hη0 : 0 < η)
    (hηmax : η ≤ lossExplainedFraction π m V) :
    ∃ c : ℝ, 0 ≤ c ∧
      lossExplainedFraction π m (raisedFourthMoments V d₀ c) = η ∧
      ∀ d, V d ≤ raisedFourthMoments V d₀ c d := by
  have hVtot : betweenLossVariance π m ≤ totalLossVariance π m V :=
    between_le_total π m V hsum hπ hV
  have hden : 0 < totalLossVariance π m V := lt_of_lt_of_le hB hVtot
  set B := betweenLossVariance π m with hBdef
  set T := totalLossVariance π m V with hTdef
  have hηle : η * T ≤ B := by
    have h := hηmax
    unfold lossExplainedFraction at h
    rw [← hBdef, ← hTdef] at h
    rw [← le_div_iff₀ hden]
    exact h
  refine ⟨(B / η - T) / π d₀, ?_, ?_, ?_⟩
  · apply div_nonneg _ hπ0.le
    rw [sub_nonneg, le_div_iff₀ hη0]
    linarith [hηle]
  · have hsum' : ∑ d, π d * raisedFourthMoments V d₀ ((B / η - T) / π d₀) d
        = (∑ d, π d * V d) + (B / η - T) := by
      rw [raised_sum π V d₀ ((B / η - T) / π d₀)]
      field_simp
    unfold lossExplainedFraction totalLossVariance
    rw [hsum']
    have hT : (∑ d, π d * V d) - (∑ d, π d * m d) ^ 2 = T := rfl
    have hrewrite : (∑ d, π d * V d) + (B / η - T) - (∑ d, π d * m d) ^ 2 = B / η := by
      linarith [hT]
    rw [← hBdef, hrewrite]
    field_simp
  · intro d
    unfold raisedFourthMoments
    by_cases hd : d = d₀
    · rw [if_pos hd]
      have hc : 0 ≤ (B / η - T) / π d₀ := by
        apply div_nonneg _ hπ0.le
        rw [sub_nonneg, le_div_iff₀ hη0]
        linarith [hηle]
      linarith
    · rw [if_neg hd]
      linarith

omit [DecidableEq D] in
/-- **The deterministic-boundary case of UPT Theorem 3.5.** If every cell fourth moment is
forced to its minimum then the fraction is the single value `η_max`. -/
theorem boundary_fraction_forced (π m V F : D → ℝ) (hforced : ∀ d, F d = V d) :
    lossExplainedFraction π m F = lossExplainedFraction π m V := by
  have h : F = V := funext hforced
  rw [h]

/-! ## The manuscript's exact example -/

/-- **The two cell minima of the UPT example.** Two cells carrying the sparse score with
`p = 1/2`, `β = 0` and `k = 1`, at second moments `1` and `2`, have least fourth moments
`2` and `4` by `SymmetricScoreFourthMoment.sparse_symmetric_value`. -/
theorem sparse_example_cell_values :
    minFourthMoment (sparseLaw (1 / 2) (by norm_num) (by norm_num)) (sparseScore (1 / 2))
        0 (fun _ ↦ 1) 1 = 2 ∧
      minFourthMoment (sparseLaw (1 / 2) (by norm_num) (by norm_num)) (sparseScore (1 / 2))
        0 (fun _ ↦ 1) 2 = 4 := by
  constructor
  · rw [(sparse_symmetric_value 1 1 (1 / 2) (by norm_num) (by norm_num) (by norm_num)).1]
    norm_num
  · rw [(sparse_symmetric_value 1 2 (1 / 2) (by norm_num) (by norm_num) (by norm_num)).1]
    norm_num

/-- The two prescribed cell second moments of the UPT example. -/
def exampleSecond : Fin 2 → ℝ
  | 0 => 1
  | 1 => 2

/-- The two cell minima of the UPT example. -/
def exampleMinima : Fin 2 → ℝ
  | 0 => 2
  | 1 => 4

/-- **The exact maximal explained fraction of the UPT example is `1/3`.** With
`B = 1/4` and `J₀ − m̄² = 3 − 9/4 = 3/4`, the sharp ceiling is `1/3`, and it is a ceiling
over every phenotype coupling preserving the score law and the stated moments. -/
theorem sparse_example_max_fraction :
    betweenLossVariance uniformTwo exampleSecond = 1 / 4 ∧
      totalLossVariance uniformTwo exampleSecond exampleMinima = 3 / 4 ∧
      lossExplainedFraction uniformTwo exampleSecond exampleMinima = 1 / 3 := by
  have hB : betweenLossVariance uniformTwo exampleSecond = 1 / 4 := by
    unfold betweenLossVariance
    rw [Fin.sum_univ_two, Fin.sum_univ_two]
    norm_num [uniformTwo, exampleSecond]
  have hT : totalLossVariance uniformTwo exampleSecond exampleMinima = 3 / 4 := by
    unfold totalLossVariance
    rw [Fin.sum_univ_two, Fin.sum_univ_two]
    norm_num [uniformTwo, exampleSecond, exampleMinima]
  refine ⟨hB, hT, ?_⟩
  unfold lossExplainedFraction
  rw [hB, hT]
  norm_num

/-! ## The region as a statement about actual laws -/

omit [DecidableEq D] in
/-- The between-cell variance is the variance of the cell-conditional squared loss. -/
theorem between_eq_variance (π m : D → ℝ) (hπ : ∀ d, 0 ≤ π d) (hsum : ∑ d, π d = 1) :
    variance (weightedExp π hπ hsum) m = betweenLossVariance π m := rfl

omit [DecidableEq D] in
/-- **The total loss variance of a multi-cell law is the arithmetic quantity above.** The
outer law is the cell distribution and each cell carries its own residual law; the second
and fourth conditional moments are all that enter. -/
theorem total_eq_variance {Ψ : Type*} (π : D → ℝ) (hπ : ∀ d, 0 ≤ π d)
    (hsum : ∑ d, π d = 1) (K : D → ExpFunctional Ψ) (res : D × Ψ → ℝ) (m F : D → ℝ)
    (hm : ∀ d, K d (fun ψ ↦ res (d, ψ) ^ 2) = m d)
    (hF : ∀ d, K d (fun ψ ↦ res (d, ψ) ^ 4) = F d) :
    variance (mixture (weightedExp π hπ hsum) K) (fun z ↦ res z ^ 2)
      = totalLossVariance π m F := by
  have hfun : (fun d ↦ K d (fun ψ ↦ res (d, ψ) ^ 4)
      - K d (fun ψ ↦ res (d, ψ) ^ 2) ^ 2) = fun d ↦ F d - m d ^ 2 := by
    funext d
    rw [hm d, hF d]
  have hfun2 : (fun d ↦ K d (fun ψ ↦ res (d, ψ) ^ 2)) = m := funext hm
  rw [squared_loss_total, hfun, hfun2, variance_eq_expect_sq_sub_sq_mean]
  unfold totalLossVariance
  show (∑ d, π d * (F d - m d ^ 2))
    + ((∑ d, π d * m d ^ 2) - (∑ d, π d * m d) ^ 2)
    = (∑ d, π d * F d) - (∑ d, π d * m d) ^ 2
  have hsplit : ∑ d, π d * (F d - m d ^ 2)
      = (∑ d, π d * F d) - ∑ d, π d * m d ^ 2 := by
    rw [eq_sub_iff_add_eq, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun d _ ↦ by ring
  rw [hsplit]
  ring

omit [DecidableEq D] in
/-- **UPT Theorem 3.5 for an actual law.** For a multi-cell residual law whose cell fourth
moments respect the per-cell minima of UPT Theorem 3.1, the fraction of squared-loss
variance explained by the cell label is positive and at most `η_max`. Both bounds are
sharp: `FourthMomentAttainableRange.attains_every_larger_fourth_moment` moves one cell's
fourth moment to realize any prescribed value of `(0, η_max]`. -/
theorem sharp_region_for_law {Ψ : Type*} (π : D → ℝ) (hπ : ∀ d, 0 ≤ π d)
    (hsum : ∑ d, π d = 1) (K : D → ExpFunctional Ψ) (res : D × Ψ → ℝ) (m F V : D → ℝ)
    (hm : ∀ d, K d (fun ψ ↦ res (d, ψ) ^ 2) = m d)
    (hF : ∀ d, K d (fun ψ ↦ res (d, ψ) ^ 4) = F d)
    (hV : ∀ d, m d ^ 2 ≤ V d) (hVF : ∀ d, V d ≤ F d)
    (hB : 0 < betweenLossVariance π m) :
    0 < variance (weightedExp π hπ hsum) (fun d ↦ K d (fun ψ ↦ res (d, ψ) ^ 2))
        / variance (mixture (weightedExp π hπ hsum) K) (fun z ↦ res z ^ 2) ∧
      variance (weightedExp π hπ hsum) (fun d ↦ K d (fun ψ ↦ res (d, ψ) ^ 2))
        / variance (mixture (weightedExp π hπ hsum) K) (fun z ↦ res z ^ 2)
        ≤ lossExplainedFraction π m V := by
  have hfun2 : (fun d ↦ K d (fun ψ ↦ res (d, ψ) ^ 2)) = m := funext hm
  have hbet : variance (weightedExp π hπ hsum) (fun d ↦ K d (fun ψ ↦ res (d, ψ) ^ 2))
      = betweenLossVariance π m := by
    rw [hfun2]
    exact between_eq_variance π m hπ hsum
  have htot : variance (mixture (weightedExp π hπ hsum) K) (fun z ↦ res z ^ 2)
      = totalLossVariance π m F :=
    total_eq_variance π hπ hsum K res m F hm hF
  rw [hbet, htot]
  have hFm : ∀ d, m d ^ 2 ≤ F d := fun d ↦ le_trans (hV d) (hVF d)
  exact ⟨fraction_pos π m F hsum hπ hFm hB, fraction_le_max π m V F hsum hπ hV hVF hB⟩

end

end Descent.Portability.LossExplainabilityRegion
