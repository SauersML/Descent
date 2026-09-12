/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.GraphCoalescent.HiddenLumpability
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

assert_below Descent.PopGen Descent.Spectral Descent.Blindness Descent.Conditionals
assert_below Descent.Portability Descent.Decision Descent.Program

/-!
# The three clocks of the three-haplotype example

The spec is `PANGENOME_HIDDEN_CLOCK.md` §3, example (A4), as a continuous-time statement.
Haplotypes `0` and `1` share a graph state and `2` is alone. The reported graph connects when
the visible merger happens, and before that the hidden-load chain has two transient states,
loads `(2, 1)` and loads `(1, 1)`. Its killed generator is `exampleGenerator = [[-3, 1], [0, -1]]`,
and its entries are the counted rates of `Descent.Pangenome.GraphCoalescent.HiddenLumpability`: the
total rate `3` of the singletons, the invisible rate `1`, and the visible rate `1` after the
invisible merger (`exampleGenerator_eq_rates`).

The survival function of the reported connection time, started at loads `(2, 1)`, is
`S(t) = α e^{tQ} 𝟙` with `α = (1, 0)` (`exampleSurvival`), the matrix exponential being Mathlib's
`NormedSpace.exp` on `2 × 2` real matrices. Diagonalizing `t Q` by its eigenvectors gives the
exponential in closed form (`exp_smul_exampleGenerator`) and hence
`S(t) = e^{-3t}/2 + e^{-t}/2` (`exampleSurvival_eq`). Its integral over `(0, ∞)` is `2/3`
(`integral_exampleSurvival`), which equals the phase-type mean `α (-Q)⁻¹ 𝟙`
(`integral_exampleSurvival_eq_phaseType`) and the first-step mean of the counted rates
(`integral_exampleSurvival_eq_mean_connection_time`).

The three clocks differ (`three_clocks_differ`). Started at the graph's floor `q`, the graph
coalescent has `w = 2` lineages and one cover (`example_graphKer_rate`), so its clock is `Exp(1)`
with mean `1`, the corpus `graphMeanTransitTime` (`example_graphMeanTransitTime`). The labeled
three-lineage coalescent reaches its most recent common ancestor after mean
`1/3 + 1 = 4/3`, the corpus `Coalescent.meanTransitTime 3`
(`example_labeled_meanTransitTime`). The reported connection time has mean `2/3`.

Scope. The identification of the mean of the absorption time with the integral of its survival
function (the layer-cake formula for a nonnegative random variable) and the construction of the
continuous-time chain as a stochastic process are not formalized: the survival function is
defined as `α e^{tQ} 𝟙` of the killed generator, and the mean connection time is its integral.

## Empirical status

None. The bodies here are a matrix exponential, an improper integral and counts of covers of a
three-element partition lattice, so no measurement can bear on them.
-/

namespace Descent.Pangenome.GraphCoalescent

open Coalescent MeasureTheory

noncomputable section

/-! ### The killed generator -/

/-- The killed generator of example (A4) on the transient hidden states, loads `(2, 1)` and loads
`(1, 1)`. -/
def exampleGenerator : Matrix (Fin 2) (Fin 2) ℝ :=
  !![-3, 1; 0, -1]

/-- **The generator's entries are the counted rates**: the total rate of the singletons, the
invisible rate into loads `(1, 1)`, and the visible rate after the invisible merger. -/
theorem exampleGenerator_eq_rates :
    exampleGenerator =
      !![-(Nat.card {η : ER 3 // Covers ⊥ η} : ℝ),
        (Nat.card (invisibleCovers exampleInterface ⊥
          (Quotient.mk (observed exampleInterface ⊥) 0)) : ℝ);
        0, -(Nat.card (visibleCovers exampleInterface
          (merge ⊥ (Quotient.mk ⊥ 0) (Quotient.mk ⊥ 1))
          (Quotient.mk (observed exampleInterface (merge ⊥ (Quotient.mk ⊥ 0) (Quotient.mk ⊥ 1)))
            0)
          (Quotient.mk (observed exampleInterface (merge ⊥ (Quotient.mk ⊥ 0) (Quotient.mk ⊥ 1)))
            2)) : ℝ)] := by
  rw [example_total_rate, example_invisible_rate, example_visible_rate_after]
  norm_num [exampleGenerator]

/-! ### The matrix exponential in closed form -/

/-- The exponential of a real vector acts coordinatewise. -/
theorem exp_apply_fin_two (v : Fin 2 → ℝ) (i : Fin 2) :
    NormedSpace.exp ℝ v i = Real.exp (v i) := by
  let evaluation : (Fin 2 → ℝ) →+* ℝ :=
    { toFun := fun w ↦ w i
      map_one' := rfl
      map_mul' := fun _ _ ↦ rfl
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }
  have h := NormedSpace.map_exp (𝕂 := ℝ) evaluation (by exact continuous_apply i) v
  rw [Real.exp_eq_exp_ℝ]
  exact h

/-- The eigenvectors of the example's generator, for the eigenvalues `-3` and `-1`. -/
def exampleEigenvectors : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1, 1; 0, 2]

/-- The inverse of the eigenvector matrix. -/
theorem exampleEigenvectors_inv : exampleEigenvectors⁻¹ = !![1, -1 / 2; 0, 1 / 2] :=
  Matrix.inv_eq_right_inv (by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [exampleEigenvectors, Matrix.mul_apply, Fin.sum_univ_two])

/-- The eigenvector matrix is invertible. -/
theorem isUnit_exampleEigenvectors : IsUnit exampleEigenvectors := by
  rw [Matrix.isUnit_iff_isUnit_det, exampleEigenvectors, Matrix.det_fin_two_of]
  exact isUnit_iff_ne_zero.mpr (by norm_num)

/-- `t Q`, written out. -/
theorem smul_exampleGenerator (t : ℝ) : t • exampleGenerator = !![-3 * t, t; 0, -t] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [exampleGenerator] <;> ring

/-- A diagonal matrix with two entries, written out. -/
theorem diagonal_fin_two (a b : ℝ) : Matrix.diagonal ![a, b] = !![a, 0; 0, b] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- `t Q` is diagonalized by its eigenvectors. -/
theorem smul_exampleGenerator_eq_conj (t : ℝ) :
    t • exampleGenerator =
      exampleEigenvectors * Matrix.diagonal ![-3 * t, -t] * exampleEigenvectors⁻¹ := by
  rw [exampleEigenvectors_inv, diagonal_fin_two, smul_exampleGenerator, exampleEigenvectors,
    Matrix.mul_fin_two, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> ring

/-- **The matrix exponential of the killed generator**:
`e^{tQ} = [[e^{-3t}, (e^{-t} - e^{-3t})/2], [0, e^{-t}]]`. -/
theorem exp_smul_exampleGenerator (t : ℝ) :
    NormedSpace.exp ℝ (t • exampleGenerator) =
      !![Real.exp (-3 * t), (Real.exp (-t) - Real.exp (-3 * t)) / 2; 0, Real.exp (-t)] := by
  have hexp : NormedSpace.exp ℝ (![-3 * t, -t] : Fin 2 → ℝ) =
      ![Real.exp (-3 * t), Real.exp (-t)] := by
    funext i
    fin_cases i <;> simp [Real.exp_eq_exp_ℝ]
  rw [smul_exampleGenerator_eq_conj, Matrix.exp_conj ℝ _ _ isUnit_exampleEigenvectors,
    Matrix.exp_diagonal ℝ, hexp, diagonal_fin_two, exampleEigenvectors_inv, exampleEigenvectors,
    Matrix.mul_fin_two, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> ring

/-! ### The survival function and its integral -/

/-- **The survival function of example (A4)**: `S(t) = α e^{tQ} 𝟙` with `α = (1, 0)`, the
probability that the report has not connected by time `t` from loads `(2, 1)`. -/
def exampleSurvival (t : ℝ) : ℝ :=
  ∑ j, NormedSpace.exp ℝ (t • exampleGenerator) 0 j

/-- **Spec (A4)**: `S(t) = e^{-3t}/2 + e^{-t}/2`. -/
theorem exampleSurvival_eq (t : ℝ) :
    exampleSurvival t = Real.exp (-3 * t) / 2 + Real.exp (-t) / 2 := by
  rw [exampleSurvival, exp_smul_exampleGenerator, Fin.sum_univ_two]
  simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

/-- **Spec (A4), the mean connection time**: `∫₀^∞ S(t) dt = 2/3`. -/
theorem integral_exampleSurvival : ∫ t in Set.Ioi 0, exampleSurvival t = 2 / 3 := by
  have hint3 : IntegrableOn (fun t : ℝ ↦ Real.exp (-3 * t)) (Set.Ioi 0) :=
    integrableOn_exp_mul_Ioi (by norm_num) 0
  have hint1 : IntegrableOn (fun t : ℝ ↦ Real.exp (-t)) (Set.Ioi 0) := by
    simpa using integrableOn_exp_mul_Ioi (a := -1) (by norm_num) 0
  simp only [exampleSurvival_eq]
  rw [integral_add (hint3.div_const 2) (hint1.div_const 2), integral_div, integral_div,
    integral_exp_mul_Ioi (a := -3) (by norm_num) 0, integral_exp_neg_Ioi_zero]
  norm_num

/-- The inverse of the negated killed generator. -/
theorem neg_exampleGenerator_inv : (-exampleGenerator)⁻¹ = !![1 / 3, 1 / 3; 0, 1] :=
  Matrix.inv_eq_right_inv (by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [exampleGenerator, Matrix.mul_apply, Fin.sum_univ_two])

/-- **The phase-type mean**: the integral of the survival function is `α (-Q)⁻¹ 𝟙`. -/
theorem integral_exampleSurvival_eq_phaseType :
    ∫ t in Set.Ioi 0, exampleSurvival t = ∑ j, (-exampleGenerator)⁻¹ 0 j := by
  rw [integral_exampleSurvival, neg_exampleGenerator_inv, Fin.sum_univ_two]
  norm_num

/-- **The continuous-time mean is the first-step mean of the counted rates** of
`example_mean_connection_time`. -/
theorem integral_exampleSurvival_eq_mean_connection_time :
    ∫ t in Set.Ioi 0, exampleSurvival t =
      (1 : ℝ) / (Nat.card (invisibleCovers exampleInterface ⊥
          (Quotient.mk (observed exampleInterface ⊥) 0)) +
        Nat.card (visibleCovers exampleInterface ⊥ (Quotient.mk (observed exampleInterface ⊥) 0)
          (Quotient.mk (observed exampleInterface ⊥) 2))) +
      (Nat.card (invisibleCovers exampleInterface ⊥
          (Quotient.mk (observed exampleInterface ⊥) 0)) : ℝ) /
        (Nat.card (invisibleCovers exampleInterface ⊥
            (Quotient.mk (observed exampleInterface ⊥) 0)) +
          Nat.card (visibleCovers exampleInterface ⊥
            (Quotient.mk (observed exampleInterface ⊥) 0)
            (Quotient.mk (observed exampleInterface ⊥) 2))) *
        (1 / Nat.card (visibleCovers exampleInterface
          (merge ⊥ (Quotient.mk ⊥ 0) (Quotient.mk ⊥ 1))
          (Quotient.mk (observed exampleInterface (merge ⊥ (Quotient.mk ⊥ 0) (Quotient.mk ⊥ 1)))
            0)
          (Quotient.mk (observed exampleInterface (merge ⊥ (Quotient.mk ⊥ 0) (Quotient.mk ⊥ 1)))
            2))) := by
  rw [integral_exampleSurvival, example_mean_connection_time]

/-! ### The other two clocks -/

/-- The interface of the example occupies two graph states. -/
theorem exampleInterface_width : Linkage.width exampleInterface = 2 := by
  decide

/-- Started at the graph's floor the coalescent has one cover: two lineages, one merger. -/
theorem example_graphKer_rate :
    Nat.card {η : ER 3 // Covers (graphKer exampleInterface) η} = 1 := by
  rw [card_covers, blocks_graphKer, exampleInterface_width]
  rfl

/-- **Started at `q` the clock is `Exp(1)` with mean `1`**: the corpus graph coalescent on its
`w = 2` lineages. -/
theorem example_graphMeanTransitTime : graphMeanTransitTime exampleInterface = 1 := by
  rw [graphMeanTransitTime, exampleInterface_width, meanTransitTime_two]

/-- **The labeled coalescent of three haplotypes reaches its root after mean `4/3 = 1/3 + 1`.** -/
theorem example_labeled_meanTransitTime : meanTransitTime 3 = 4 / 3 := by
  rw [meanTransitTime_eq_two_sub (by norm_num)]
  norm_num

/-- **The three clocks differ**: the reported connection time from the singletons has mean
`2/3`, the graph coalescent started at `q` has mean `1`, and the labeled root time has mean
`4/3`. -/
theorem three_clocks_differ :
    ∫ t in Set.Ioi 0, exampleSurvival t ≠ graphMeanTransitTime exampleInterface ∧
      graphMeanTransitTime exampleInterface ≠ meanTransitTime 3 ∧
      ∫ t in Set.Ioi 0, exampleSurvival t ≠ meanTransitTime 3 := by
  rw [integral_exampleSurvival, example_graphMeanTransitTime, example_labeled_meanTransitTime]
  norm_num

end

end Descent.Pangenome.GraphCoalescent
