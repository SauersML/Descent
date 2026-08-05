/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.TransferLearningPGS.PGSPortabilityDerivation

namespace Descent.Portability

open MeasureTheory Finset

/-!
# `TransferLearningPGS.ImportanceWeighting`

Part of the split of `Descent/Portability/TransferLearningPGS.lean`, which was 3,558 lines.

The parts are a CHAIN: each imports the one before, in the order the original was written.
That is the conservative choice, deliberately. A monolith's declarations depend on each
other in whatever order they happen to appear, and cutting it into modules that import only
what they use means discovering that order first -- worth doing, and not what this does.
The chain preserves every resolution the single file had, so the split cannot change what
any proof sees.

Where a cut falls inside a section, the section is reopened and reclosed by name. A section
scopes `variable`s and this file declares none at that level, so the reopening is exact.
-/



/-!
## Importance Weighting for PGS

Importance weighting (IW) adjusts for the distribution shift
between source and target populations by reweighting individuals.
-/

section ImportanceWeighting

/-- **IW effective sample size.**
    n_eff = (Σ wᵢ)² / (Σ wᵢ²) ≤ n.
    The effective sample size decreases with the divergence
    between source and target (larger weights). -/
noncomputable def importanceWeightESS (sum_w sum_w_sq : ℝ) : ℝ :=
  Descent.Core.scaledSquare sum_w sum_w_sq

/-- **importanceWeightESS at zero sum_w_sq, named.** With zero total squared weight there are no
samples and the effective sample size is undefined. Lean returns `0`, which is the correct-looking
answer for the wrong reason and hides the empty-sample case inside the degenerate-weights case.
Consumers must require `sum_w_sq ≠ 0`. -/
theorem importanceWeightESS_zero_sumwsq_is_junk (sum_w : ℝ) :
    importanceWeightESS sum_w 0 = 0 := by
  unfold importanceWeightESS Descent.Core.scaledSquare
  simp

/-- **The effective size recovers the squared total weight.** -/
theorem importanceWeightESS_mul_sumSq (sum_w sum_w_sq : ℝ) (h : sum_w_sq ≠ 0) :
    importanceWeightESS sum_w sum_w_sq * sum_w_sq = sum_w ^ 2 := by
  unfold importanceWeightESS Descent.Core.scaledSquare
  field_simp

/-- **IW ESS ≤ n, from an actual weight vector, with Cauchy-Schwarz proved.**

    `iw_ess_le_n` used to state this for free scalars `sum_w` and `sum_w_sq` and take
    `sum_w ^ 2 ≤ n * sum_w_sq` as a hypothesis. That hypothesis is Cauchy-Schwarz, which
    is the only mathematical content the bound has; assuming it left the theorem as
    `div_le_iff₀`, and left `n`, `sum_w` and `sum_w_sq` as three unrelated reals with no
    stated connection to any set of weights. In particular nothing forced `sum_w` to be
    the sum of the same weights whose squares make `sum_w_sq`, so the scalar form was
    satisfied by triples that correspond to no weight vector at all.

    Stated over `w : Fin n → ℝ` the hypothesis is discharged from Mathlib
    (`sq_sum_le_card_mul_sum_sq`, the `f = g` case of Chebyshev's sum inequality) and `n`
    is the actual sample size rather than a free variable. -/
theorem importanceWeightESS_le_card {n : ℕ} (w : Fin n → ℝ)
    (h_sq_pos : 0 < ∑ i, w i ^ 2) :
    importanceWeightESS (∑ i, w i) (∑ i, w i ^ 2) ≤ (n : ℝ) := by
  unfold importanceWeightESS Descent.Core.scaledSquare
  rw [div_le_iff₀ h_sq_pos]
  simpa using (sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin n))) (f := w))

/-- **The ESS is nonnegative**, since it is a square over a positive sum. -/
theorem importanceWeightESS_nonneg {n : ℕ} (w : Fin n → ℝ)
    (h_sq_pos : 0 < ∑ i, w i ^ 2) :
    0 ≤ importanceWeightESS (∑ i, w i) (∑ i, w i ^ 2) := by
  unfold importanceWeightESS Descent.Core.scaledSquare
  positivity

/-- **Equal weights attain the bound**: the ESS of a constant weight vector is exactly
    `n`, so the inequality above is sharp and not merely an envelope. Requires `c ≠ 0`,
    since all-zero weights leave the ESS a `0/0`. -/
theorem importanceWeightESS_of_const {n : ℕ} (c : ℝ) (hc : c ≠ 0) (hn : 0 < n) :
    importanceWeightESS (∑ _i : Fin n, c) (∑ _i : Fin n, c ^ 2) = (n : ℝ) := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  unfold importanceWeightESS Descent.Core.scaledSquare
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [mul_pow]
  field_simp

/-! **Deleted: `iw_ess_decreases_with_divergence` and
`iw_positive_weight_variance_reduces_ess`.**

These theorems are absent on purpose. They attach to a second formula for one quantity,
and it is the formula that does not exist. `importanceWeightESS` — the definition this
section is built around, and the one `validation/popgen_defs/transfer_battery.py`
exercises — is `(Σw)²/Σw²`. Both named theorems are about `n / (1 + v)`. That expression is
defined nowhere in this corpus and is proved equal to nothing that is. The identification
`(Σw)²/Σw² = n/(1 + Var(w))` needs the weights normalized to mean one, and no such
normalization is stated or assumed, so a result named for the effective sample size
establishes nothing about it.

Stripped of the naming, `iw_ess_decreases_with_divergence` is `div_lt_div_of_pos_left` and
`iw_positive_weight_variance_reduces_ess` is `div_lt_iff₀` — Mathlib in domain costume,
neither used anywhere. Divergence and `F_ST` appear in neither statement, and the chain
from ancestry divergence to weight variance lives only in prose ("as Fst increases, the
importance weights become more variable"), formalized nowhere.

`importanceWeightESS_le_card` above stands in their place, about the definition that
exists and that the validation battery tests. A genuine monotonicity result — that more
variable weights give a smaller ESS — is a real and provable statement over `w`, and is
the thing to add here if it is wanted. Until then it stays unasserted. -/

/-- **Doubly robust estimation combines IW with model adaptation.**
    DR estimator: if either the weighting model or the outcome model is
    asymptotically correct, and the other nuisance component remains
    uniformly bounded, the target-population estimator is consistent. -/
def AsymptoticallyZero (err : ℕ → ℝ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, |err n| < ε

/-- An estimator sequence converges to the target parameter in absolute error. -/
def AsymptoticallyConsistent (est : ℕ → ℝ) (truth : ℝ) : Prop :=
  AsymptoticallyZero (fun n ↦ est n - truth)

/-- If an error term is bounded by a product and one factor converges to zero
    while the other is uniformly bounded, then the error also converges to zero. -/
theorem asymptoticallyZero_of_abs_le_mul
    (h f g : ℕ → ℝ)
    (h_bound : ∀ n, |h n| ≤ |f n| * |g n|)
    (hg_bounded : ∃ C ≥ 0, ∀ n, |g n| ≤ C)
    (hf_zero : AsymptoticallyZero f) :
    AsymptoticallyZero h := by
  intro ε hε
  rcases hg_bounded with ⟨C, hC_nn, hgC⟩
  have hC1_pos : 0 < C + 1 := by linarith
  have h_scaled_pos : 0 < ε / (C + 1) := by positivity
  rcases hf_zero (ε / (C + 1)) h_scaled_pos with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn
  have hf_small : |f n| < ε / (C + 1) := hN n hn
  have hg_le : |g n| ≤ C := hgC n
  have h_mul_le : |f n| * |g n| ≤ |f n| * C :=
    mul_le_mul_of_nonneg_left hg_le (abs_nonneg _)
  have h_mul_le' : |f n| * C ≤ (ε / (C + 1)) * C :=
    mul_le_mul_of_nonneg_right hf_small.le hC_nn
  have hC_lt : C < C + 1 := by linarith
  have h_scaled_lt : (ε / (C + 1)) * C < (ε / (C + 1)) * (C + 1) :=
    mul_lt_mul_of_pos_left hC_lt h_scaled_pos
  have h_cancel : (ε / (C + 1)) * (C + 1) = ε := by
    field_simp [ne_of_gt hC1_pos]
  calc
    |h n| ≤ |f n| * |g n| := h_bound n
    _ ≤ |f n| * C := h_mul_le
    _ ≤ (ε / (C + 1)) * C := h_mul_le'
    _ < (ε / (C + 1)) * (C + 1) := h_scaled_lt
    _ = ε := h_cancel

/-- **Doubly robust consistency.**
    Let `est_dr n` estimate a target parameter `θ`. If the DR estimation error is
    bounded by the product of the residual weighting bias and residual outcome-model
    bias, then consistency follows whenever either nuisance component converges to
    zero and the other stays uniformly bounded. -/
theorem doubly_robust_consistency
    (θ : ℝ)
    (est_dr bias_iw_only bias_model_only : ℕ → ℝ)
    (h_dr_error_bound :
      ∀ n, |est_dr n - θ| ≤ |bias_iw_only n| * |bias_model_only n|)
    (h_iw_bounded : ∃ C ≥ 0, ∀ n, |bias_iw_only n| ≤ C)
    (h_model_bounded : ∃ C ≥ 0, ∀ n, |bias_model_only n| ≤ C)
    (h_either :
      AsymptoticallyZero bias_iw_only ∨ AsymptoticallyZero bias_model_only) :
    AsymptoticallyConsistent est_dr θ := by
  unfold AsymptoticallyConsistent
  rcases h_either with h_iw_zero | h_model_zero
  · exact asymptoticallyZero_of_abs_le_mul
      (fun n ↦ est_dr n - θ) bias_iw_only bias_model_only
      h_dr_error_bound h_model_bounded h_iw_zero
  · exact asymptoticallyZero_of_abs_le_mul
      (fun n ↦ est_dr n - θ) bias_model_only bias_iw_only
      (by
        intro n
        have h := h_dr_error_bound n
        simpa [mul_comm] using h)
      h_iw_bounded h_model_zero

end ImportanceWeighting

end Descent.Portability
