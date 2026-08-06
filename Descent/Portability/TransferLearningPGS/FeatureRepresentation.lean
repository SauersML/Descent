/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.TransferLearningPGS.PGSPortabilityDerivation
import Descent.Layer

assert_below Descent.Decision Descent.Program

namespace Descent.Portability

open MeasureTheory Finset

/-!
# `TransferLearningPGS.FeatureRepresentation`

Part of the split of `Descent/Portability/TransferLearningPGS.lean`, which was 3,558 lines.

The parts are a FAN: each imports the parts that declare the symbols it names, and nothing
else. The split first made them a CHAIN -- each importing the one before, in the order the
original text ran -- which preserved every resolution the single file had and charged every
part a dependency on everything written above it, used or not. Recovering the real order is
the work that chain deferred: each part's identifiers were resolved against its siblings'
declarations, and the imports above are the answer, so what a part rests on is readable
from its header instead of inherited from its position in a file that no longer exists.

Where a cut falls inside a section, the section is reopened and reclosed by name. A section
scopes `variable`s and this file declares none at that level, so the reopening is exact.
-/



/-!
## Feature Representation Learning

Learning genotype representations that are invariant to ancestry
while preserving trait-relevant information.
-/

section FeatureRepresentation

/-- **PCA projection as a simple representation.**
    Projecting genotypes onto top PCs separates ancestry from
    trait-relevant variation. Removing top PCs reduces ancestry
    signal but may also remove trait signal.
    Net target error is modeled as ancestry-induced bias plus a weighted
    penalty for discarded trait signal. -/
def pcaSignalLossPenalty
    (signalBaseline signalRetained lossWeight : ℝ) : ℝ :=
  lossWeight * (signalBaseline - signalRetained)

/-- **The signal-loss penalty's orientation and scale, pinned.** This definition carries no
result of its own. Two units of weight on two units of lost signal is a penalty of four: the
weight multiplies the loss rather than the retained signal, and the difference runs baseline
minus retained so that losing signal costs rather than pays. -/
theorem pcaSignalLossPenalty_reference :
    pcaSignalLossPenalty 3 1 2 = 4 := by
  unfold pcaSignalLossPenalty
  norm_num

/-- Reduction in ancestry-induced target bias achieved by removing ancestry PCs. -/
noncomputable def pcaBiasReduction
    (ancestryBiasWith ancestryBiasWithout : ℝ) : ℝ :=
  Descent.Core.difference ancestryBiasWith ancestryBiasWithout

/-- **The bias-reduction sign convention, pinned.** This definition carries no result of its own,
and the whole content of the definition is which way the subtraction runs. A reduction is
positive when correcting for principal components leaves LESS ancestry bias than not correcting;
the reversed body reports successful correction as damage. -/
theorem pcaBiasReduction_positive_when_correction_helps :
    pcaBiasReduction 3 1 = 2 := by
  unfold pcaBiasReduction Descent.Core.difference
  norm_num

/-- Linearized target error after PCA adjustment: ancestry bias plus a
    weighted trait-signal loss penalty. -/
def pcaNetTargetError
    (ancestryBias signalBaseline signalRetained lossWeight : ℝ) : ℝ :=
  ancestryBias + pcaSignalLossPenalty signalBaseline signalRetained lossWeight

/-- Reference evaluation; see `Descent.Core.Ratios` for what these pin and why. -/
theorem pcaNetTargetError_at_reference_point :
    pcaNetTargetError 1 1 1 1 = 1 := by
  norm_num [pcaNetTargetError, pcaSignalLossPenalty]



/-- Exact error difference induced by removing ancestry PCs. -/
theorem pca_target_error_difference
    (ancestry_bias_with ancestry_bias_without signal_with signal_without lossWeight : ℝ) :
    pcaNetTargetError ancestry_bias_without signal_with signal_without lossWeight -
        pcaNetTargetError ancestry_bias_with signal_with signal_with lossWeight =
      pcaSignalLossPenalty signal_with signal_without lossWeight -
        pcaBiasReduction ancestry_bias_with ancestry_bias_without := by
  unfold pcaNetTargetError pcaSignalLossPenalty pcaBiasReduction Descent.Core.difference
  ring

/-- **PCA removal improves target error iff bias reduction exceeds weighted signal loss.**
    This is the exact total-error criterion: PC removal helps iff the
    ancestry-bias reduction is larger than the weighted trait-signal loss,
    is neutral iff they are equal, and hurts iff the loss term is larger. -/
theorem pca_tradeoff
    (ancestry_bias_with ancestry_bias_without signal_with signal_without lossWeight : ℝ) :
    (pcaNetTargetError ancestry_bias_without signal_with signal_without lossWeight <
        pcaNetTargetError ancestry_bias_with signal_with signal_with lossWeight ↔
      pcaSignalLossPenalty signal_with signal_without lossWeight <
        pcaBiasReduction ancestry_bias_with ancestry_bias_without) ∧
    (pcaNetTargetError ancestry_bias_without signal_with signal_without lossWeight ≤
        pcaNetTargetError ancestry_bias_with signal_with signal_with lossWeight ↔
      pcaSignalLossPenalty signal_with signal_without lossWeight ≤
        pcaBiasReduction ancestry_bias_with ancestry_bias_without) ∧
    (pcaNetTargetError ancestry_bias_with signal_with signal_with lossWeight <
        pcaNetTargetError ancestry_bias_without signal_with signal_without lossWeight ↔
      pcaBiasReduction ancestry_bias_with ancestry_bias_without <
        pcaSignalLossPenalty signal_with signal_without lossWeight) ∧
    (pcaNetTargetError ancestry_bias_without signal_with signal_without lossWeight =
        pcaNetTargetError ancestry_bias_with signal_with signal_with lossWeight ↔
      pcaSignalLossPenalty signal_with signal_without lossWeight =
        pcaBiasReduction ancestry_bias_with ancestry_bias_without) := by
  -- All four comparisons are the one difference identity read four ways.  Written out,
  -- each carried its own copy of the same two-step rearrangement.
  have hdiff := pca_target_error_difference
    ancestry_bias_with ancestry_bias_without signal_with signal_without lossWeight
  refine ⟨?_, ?_, ?_, ?_⟩ <;> constructor <;> intro h <;> linarith

/-- When the ancestry-bias reduction and signal loss are both positive,
    the total-error tradeoff is controlled by a single loss-weight threshold. -/
theorem pca_tradeoff_threshold_on_lossWeight
    (ancestry_bias_with ancestry_bias_without signal_with signal_without lossWeight : ℝ)
    (h_signal_gap : signal_without < signal_with) :
    (pcaNetTargetError ancestry_bias_without signal_with signal_without lossWeight <
        pcaNetTargetError ancestry_bias_with signal_with signal_with lossWeight ↔
      lossWeight <
        pcaBiasReduction ancestry_bias_with ancestry_bias_without /
          (signal_with - signal_without)) ∧
    (pcaNetTargetError ancestry_bias_without signal_with signal_without lossWeight =
        pcaNetTargetError ancestry_bias_with signal_with signal_with lossWeight ↔
      lossWeight =
        pcaBiasReduction ancestry_bias_with ancestry_bias_without /
          (signal_with - signal_without)) := by
  have hgap_pos : 0 < signal_with - signal_without := sub_pos.mpr h_signal_gap
  have hgap_ne : signal_with - signal_without ≠ 0 := ne_of_gt hgap_pos
  rcases pca_tradeoff ancestry_bias_with ancestry_bias_without
      signal_with signal_without lossWeight with ⟨hImprove, _, _, hNeutral⟩
  refine ⟨?_, ?_⟩
  · constructor <;> intro h
    · have hpenalty := hImprove.mp h
      unfold pcaSignalLossPenalty at hpenalty
      by_contra hnot
      have hge :
          pcaBiasReduction ancestry_bias_with ancestry_bias_without /
              (signal_with - signal_without) ≤ lossWeight := by
        linarith
      have hmul :
          (pcaBiasReduction ancestry_bias_with ancestry_bias_without /
              (signal_with - signal_without)) * (signal_with - signal_without) ≤
            lossWeight * (signal_with - signal_without) :=
        mul_le_mul_of_nonneg_right hge hgap_pos.le
      have hdiv :
          (pcaBiasReduction ancestry_bias_with ancestry_bias_without /
              (signal_with - signal_without)) * (signal_with - signal_without) =
            pcaBiasReduction ancestry_bias_with ancestry_bias_without := by
        field_simp [hgap_ne]
      rw [hdiv] at hmul
      linarith
    · have hpenalty :
          lossWeight * (signal_with - signal_without) <
            pcaBiasReduction ancestry_bias_with ancestry_bias_without := by
        have hmul :
            lossWeight * (signal_with - signal_without) <
              (pcaBiasReduction ancestry_bias_with ancestry_bias_without /
                  (signal_with - signal_without)) * (signal_with - signal_without) :=
          mul_lt_mul_of_pos_right h hgap_pos
        have hdiv :
            (pcaBiasReduction ancestry_bias_with ancestry_bias_without /
                (signal_with - signal_without)) * (signal_with - signal_without) =
              pcaBiasReduction ancestry_bias_with ancestry_bias_without := by
          field_simp [hgap_ne]
        rw [hdiv] at hmul
        exact hmul
      exact hImprove.mpr (by
        unfold pcaSignalLossPenalty
        simpa [sub_eq_add_neg, mul_comm, mul_left_comm, mul_assoc] using hpenalty)
  · constructor <;> intro h
    · have hpenalty := hNeutral.mp h
      unfold pcaSignalLossPenalty at hpenalty
      exact (eq_div_iff hgap_ne).2 (by
        simpa [sub_eq_add_neg, mul_comm, mul_left_comm, mul_assoc] using hpenalty)
    · have hpenalty :
          lossWeight * (signal_with - signal_without) =
            pcaBiasReduction ancestry_bias_with ancestry_bias_without :=
        (eq_div_iff hgap_ne).1 h
      exact hNeutral.mpr (by
        unfold pcaSignalLossPenalty
        simpa [sub_eq_add_neg, mul_comm, mul_left_comm, mul_assoc] using hpenalty)

/-- **A local PC-removal minimum beats the adjacent choices.**
    This theorem does not prove existence of a globally optimal number of
    removed PCs. It records the exact local-optimality consequence available
    from two neighboring error comparisons. -/
theorem local_pc_removal_minimum_beats_adjacent_choices
    (err_k err_k_plus_1 err_k_minus_1 : ℝ)
    (h_local_min_right : err_k ≤ err_k_plus_1)
    (h_local_min_left : err_k ≤ err_k_minus_1) :
    err_k ≤ min err_k_plus_1 err_k_minus_1 :=
  le_min h_local_min_right h_local_min_left

/-- Information-bottleneck objective `I(φ(X); Y) - λ I(φ(X); A)`. -/
def infoBottleneckObjective (I_phi_Y I_phi_A lam : ℝ) : ℝ :=
  I_phi_Y - lam * I_phi_A

/-- **The information-bottleneck trade-off, pinned.** This definition carries no result of its
own. The ancestry term is subtracted and weighted, so a Lagrange multiplier of two on equal
outcome and ancestry information gives an objective of minus one: past `lam = 1` the objective
prefers discarding predictive information to buying ancestry invariance. -/
theorem infoBottleneckObjective_reference :
    infoBottleneckObjective 1 1 2 = -1 := by
  unfold infoBottleneckObjective
  norm_num

/-- Closed-form normalized Gaussian source residual risk from mutual information.
    For a jointly Gaussian source trait `Y` and representation `φ(X)` with `Var(Y)=1`, the residual
    variance fraction is under this model `exp(-2 I(φ(X);Y))`.

    Empirical status: UNTESTED. -/
noncomputable def gaussianSourceResidualRisk (I_phi_Y : ℝ) : ℝ :=
  Real.exp (-2 * I_phi_Y)

/-- **The Gaussian residual risk's rate, pinned.** `gaussianSourceResidualRisk_strictAnti` says
the risk decreases in the retained information, which is true of EVERY decreasing function and
so fixes no exponent. Half a nat of information about the outcome cuts the residual risk by
exactly one e-fold, which is what fixes the factor two in the exponent. -/
theorem gaussianSourceResidualRisk_half_nat :
    gaussianSourceResidualRisk (1 / 2) = Real.exp (-1) := by
  unfold gaussianSourceResidualRisk
  norm_num

/-- Pinsker-certified ancestry-divergence cap from mutual information.
    This is the standard `√(2 I)` envelope obtained by combining binary-domain
    total-variation control with Pinsker's inequality.

    Empirical status: **VALIDATED as an upper bound, and measured to be
    LOOSE BY EXACTLY A FACTOR OF TWO**
    (`validation/empirical/simcov/battery_bulk10.py`,
    `test_pinsker_tightness`). Over 200000 random distribution pairs, recording
    how closely each candidate cap is approached by the realised total
    variation:

      cap                        max attained fraction
      sqrt(KL / 2)                      1.0000
      sqrt(2 * KL)   (this body)        0.5000

    Pinsker's inequality is `TV <= sqrt(KL / 2)`, and that bound is TIGHT: the
    measurement approaches it to four decimal places. This definition's
    `sqrt(2 * I)` is a valid bound -- nothing violates it -- but it is never
    approached more closely than half, because it is twice the tight one.

    A bound that cannot be attained is weaker than its name suggests. Anything
    downstream that treats this as the Pinsker cap is carrying a factor of two
    of slack, which matters wherever the cap is compared against a measured
    divergence rather than used only for a qualitative argument.

    Power: the two candidate caps differ by exactly a factor of two everywhere,
    and the design separates them at 25 sems. -/
noncomputable def pinskerAncestryDivergenceCap (I_phi_A : ℝ) : ℝ :=
  Real.sqrt (2 * I_phi_A)

/-- **pinskerAncestryDivergenceCap at a negative mutual information, named.** Mutual information
cannot be negative, but a plug-in estimate of it can be. `Real.sqrt` is junk-zero on the negative
radicand, so the cap is reported as zero: the tightest possible bound, certifying that no
ancestry information leaks, produced by an estimate that was invalid. Consumers must exclude it
by hypothesis. -/
theorem pinskerAncestryDivergenceCap_negative_information_is_junk :
    pinskerAncestryDivergenceCap (-1) = 0 := by
  unfold pinskerAncestryDivergenceCap
  rw [show (2 : ℝ) * (-1) = -2 by ring]
  exact Real.sqrt_eq_zero_of_nonpos (by norm_num)

/-- **The Pinsker cap's constant, pinned.** `pinskerAncestryDivergenceCap_mono` fixes the
direction and holds for `sqrt (c * I)` at every positive `c`. Half a nat of ancestry information
caps the total-variation divergence at one, which is what fixes `c = 2` -- and, incidentally,
marks where the cap stops saying anything, since total variation never exceeds one. -/
theorem pinskerAncestryDivergenceCap_half_nat :
    pinskerAncestryDivergenceCap (1 / 2) = 1 := by
  unfold pinskerAncestryDivergenceCap
  norm_num

/-- Information-certified Ben-David upper envelope built from:
    - exact Gaussian source residual risk,
    - a Pinsker ancestry-divergence cap,
    - the irreducible `λ*` term. -/
noncomputable def infoCertifiedBenDavidUpperBound
    (I_phi_Y I_phi_A lambda_star : ℝ) : ℝ :=
  gaussianSourceResidualRisk I_phi_Y +
    pinskerAncestryDivergenceCap I_phi_A + lambda_star

/-- Reference evaluation; see `Descent.Core.Ratios` for what these pin and why. -/
theorem infoCertifiedBenDavidUpperBound_at_reference_point :
    infoCertifiedBenDavidUpperBound 0 0 0 = 1 := by
  norm_num [infoCertifiedBenDavidUpperBound, gaussianSourceResidualRisk,
    pinskerAncestryDivergenceCap]



/-- More label information strictly lowers the exact Gaussian source residual term. -/
theorem gaussianSourceResidualRisk_strictAnti
    (I₁ I₂ : ℝ)
    (hI : I₁ < I₂) :
    gaussianSourceResidualRisk I₂ < gaussianSourceResidualRisk I₁ := by
  unfold gaussianSourceResidualRisk
  exact Real.exp_lt_exp.mpr (by linarith)

/-- Less ancestry information weakly lowers the Pinsker divergence cap. -/
theorem pinskerAncestryDivergenceCap_mono
    (I₁ I₂ : ℝ)
    (hI₂ : I₁ ≤ I₂) :
    pinskerAncestryDivergenceCap I₁ ≤ pinskerAncestryDivergenceCap I₂ := by
  unfold pinskerAncestryDivergenceCap
  apply Real.sqrt_le_sqrt
  nlinarith

/-- Dominating a representation by increasing trait information and not
    increasing ancestry leakage tightens the information-certified transfer
    envelope. -/
theorem more_label_info_less_ancestry_info_tightens_ben_david_bound
    (I_phi_Y_standard I_phi_Y_new I_phi_A_standard I_phi_A_new : ℝ)
    (lambda_standard lambda_new : ℝ)
    (h_IY : I_phi_Y_standard < I_phi_Y_new)
    (h_IA_standard : I_phi_A_new ≤ I_phi_A_standard)
    (h_lambda : lambda_new ≤ lambda_standard) :
    infoCertifiedBenDavidUpperBound I_phi_Y_new I_phi_A_new lambda_new <
      infoCertifiedBenDavidUpperBound I_phi_Y_standard I_phi_A_standard lambda_standard := by
  have h_source :
      gaussianSourceResidualRisk I_phi_Y_new <
        gaussianSourceResidualRisk I_phi_Y_standard :=
    gaussianSourceResidualRisk_strictAnti I_phi_Y_standard I_phi_Y_new h_IY
  have h_div :
      pinskerAncestryDivergenceCap I_phi_A_new ≤
        pinskerAncestryDivergenceCap I_phi_A_standard :=
    pinskerAncestryDivergenceCap_mono
      I_phi_A_new I_phi_A_standard h_IA_standard
  unfold infoCertifiedBenDavidUpperBound
  linarith

/-- An exact information certificate upper-bounds the Ben-David functional —
    but only for the source error and divergence the certificate actually
    dominates, which is why the name carries the condition. -/
theorem benDavidUpperBound_le_infoCertifiedBenDavidUpperBound_of_dominated_components
    (err_source divergence lambda_star I_phi_Y I_phi_A : ℝ)
    (h_source : err_source ≤ gaussianSourceResidualRisk I_phi_Y)
    (h_div : divergence ≤ pinskerAncestryDivergenceCap I_phi_A) :
    benDavidUpperBound err_source divergence lambda_star ≤
      infoCertifiedBenDavidUpperBound I_phi_Y I_phi_A lambda_star := by
  unfold benDavidUpperBound infoCertifiedBenDavidUpperBound Descent.Core.sum3
  linarith

/-- **Improving the information-bottleneck objective tightens the transfer bound.**
    This is now an exact information-certified statement rather than an affine
    calibration assumption. If ancestry leakage is held fixed, then a strict
    gain in the bottleneck objective means strictly larger trait information.
    Under the exact Gaussian residual-risk formula and the Pinsker ancestry
    envelope, that strictly tightens the information-certified Ben-David
    upper bound. -/
theorem higher_info_bottleneck_objective_tightens_ben_david_bound
    (I_phi_Y_standard I_phi_Y_new I_phi_A : ℝ)
    (lambda_standard lambda_new lam : ℝ)
    (h_lambda : lambda_new ≤ lambda_standard)
    (h_obj :
      infoBottleneckObjective I_phi_Y_new I_phi_A lam >
        infoBottleneckObjective I_phi_Y_standard I_phi_A lam) :
    infoCertifiedBenDavidUpperBound I_phi_Y_new I_phi_A lambda_new <
      infoCertifiedBenDavidUpperBound I_phi_Y_standard I_phi_A lambda_standard := by
  have h_IY : I_phi_Y_standard < I_phi_Y_new := by
    unfold infoBottleneckObjective at h_obj
    linarith
  exact more_label_info_less_ancestry_info_tightens_ben_david_bound
    I_phi_Y_standard I_phi_Y_new I_phi_A I_phi_A
    lambda_standard lambda_new h_IY (le_rfl) h_lambda

end FeatureRepresentation

end Descent.Portability
