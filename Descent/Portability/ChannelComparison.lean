/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.MetricOrderingClassification
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Topology.Order.Compact

assert_below Descent.Decision Descent.Program

/-!
# Finite information channels: garbling, composition, and decision dominance

Channels are row-stochastic matrices on finite state and signal spaces, and a
decision rule is itself such a matrix from signals to actions. Composition
`chanCompose` is matrix multiplication, so garbling a channel and randomising a
decision are the same operation, and `decisionRisk` evaluates any prior and loss
against the induced state-to-action matrix. This file proves the easy half of
TQ Theorem 4.9 / UPT Theorem 6.5 (a garbling is never an improvement) and the
compactness step the converse needs: a closest garbling of `B` inside the set of
channels reachable from `A` exists. The tie to the corpus is
`confusion_channel_risk_eq_decisionLoss`, which evaluates `decisionRisk` on the
channel of a `Foundations.ConfusionMatrix` and recovers
`ThresholdPolicyTransport.decisionLoss`. Hypotheses are the domain conditions of
the manuscript: row-stochasticity, a probability prior, and a nonempty state
space (needed for the uniform prior used in the converse).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.ChannelComparison

open Foundations

noncomputable section

variable {Θ X Y Z : Type*} [Fintype Θ] [Fintype X] [Fintype Y] [Fintype Z]

/-- Composition of a channel with a garbling (equivalently with a randomised
decision rule): the `(θ, y)` entry is `∑ x, A θ x * G x y`. -/
def chanCompose (A : Θ → X → ℝ) (G : X → Y → ℝ) : Θ → Y → ℝ :=
  fun θ y ↦ ∑ x, A θ x * G x y

omit [Fintype Θ] [Fintype Z] in
/-- Channel composition is associative, so garbling then deciding equals
deciding with the composed rule. -/
theorem chanCompose_assoc (A : Θ → X → ℝ) (G : X → Y → ℝ) (H : Y → Z → ℝ) :
    chanCompose (chanCompose A G) H = chanCompose A (chanCompose G H) := by
  funext θ z
  simp only [chanCompose, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

omit [Fintype Θ] [Fintype Y] in
/-- Composing nonnegative matrices gives a nonnegative matrix. -/
theorem chanCompose_nonneg {A : Θ → X → ℝ} {G : X → Y → ℝ}
    (hA : ∀ θ x, 0 ≤ A θ x) (hG : ∀ x y, 0 ≤ G x y) (θ : Θ) (y : Y) :
    0 ≤ chanCompose A G θ y :=
  Finset.sum_nonneg fun x _ ↦ mul_nonneg (hA θ x) (hG x y)

omit [Fintype Θ] in
/-- Composing row-stochastic matrices gives row-stochastic rows. -/
theorem chanCompose_row_sum {A : Θ → X → ℝ} {G : X → Y → ℝ}
    (hA : ∀ θ, ∑ x, A θ x = 1) (hG : ∀ x, ∑ y, G x y = 1) (θ : Θ) :
    ∑ y, chanCompose A G θ y = 1 := by
  simp only [chanCompose]
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum, hG, mul_one, hA]

/-- Expected loss of the state-to-action matrix `M` under a prior and a loss. -/
def decisionRisk (prior : Θ → ℝ) (M : Θ → Z → ℝ) (loss : Θ → Z → ℝ) : ℝ :=
  ∑ θ, prior θ * ∑ z, M θ z * loss θ z

/-- **TQ Theorem 4.9 / UPT Theorem 6.5, easy direction.** If `B` is a garbling
of `A` then every decision rule after `B` is reproduced exactly by a decision
rule after `A`: garbling `G` first and then deciding. The conclusion is an
equality of expected losses, so it holds for every prior and every loss without
any sign or boundedness condition on the loss. -/
theorem garbling_no_worse (A : Θ → X → ℝ) (B : Θ → Y → ℝ) (G : X → Y → ℝ)
    (hG0 : ∀ x y, 0 ≤ G x y) (hG1 : ∀ x, ∑ y, G x y = 1) (hB : B = chanCompose A G)
    (prior : Θ → ℝ) (loss : Θ → Z → ℝ) (dB : Y → Z → ℝ)
    (hd0 : ∀ y z, 0 ≤ dB y z) (hd1 : ∀ y, ∑ z, dB y z = 1) :
    ∃ dA : X → Z → ℝ, (∀ x z, 0 ≤ dA x z) ∧ (∀ x, ∑ z, dA x z = 1) ∧
      decisionRisk prior (chanCompose A dA) loss =
        decisionRisk prior (chanCompose B dB) loss := by
  refine ⟨chanCompose G dB, chanCompose_nonneg hG0 hd0, chanCompose_row_sum hG1 hd1, ?_⟩
  rw [← chanCompose_assoc, ← hB]

/-- The channel of a confusion table: row `true` is the case-conditional law of
the binary report and row `false` the control-conditional law. -/
def confusionChannel (c : ConfusionMatrix) : Bool → Bool → ℝ :=
  fun θ y ↦ if θ then (if y then c.tp / c.prevalence else c.fn / c.prevalence)
    else (if y then c.fp / (1 - c.prevalence) else c.tn / (1 - c.prevalence))

/-- The deterministic rule "report the observed signal". -/
def identityRule : Bool → Bool → ℝ := fun y z ↦ if y = z then 1 else 0

/-- The confusion channel is row-stochastic at a nondegenerate prevalence. -/
theorem confusionChannel_row_sum (c : ConfusionMatrix) (h0 : 0 < c.prevalence)
    (h1 : c.prevalence < 1) (θ : Bool) : ∑ y, confusionChannel c θ y = 1 := by
  have hp : c.prevalence ≠ 0 := ne_of_gt h0
  have hq : (1 : ℝ) - c.prevalence ≠ 0 := ne_of_gt (sub_pos.mpr h1)
  have hpre : c.tp + c.fn = c.prevalence := rfl
  have hneg : c.fp + c.tn = 1 - c.prevalence := (ConfusionMatrix.one_sub_prevalence c).symm
  cases θ <;>
    simp only [confusionChannel, Fintype.sum_bool, Bool.false_eq_true, if_false, if_true] <;>
    field_simp <;> linarith

/-- The confusion channel entries are nonnegative at a nondegenerate prevalence. -/
theorem confusionChannel_nonneg (c : ConfusionMatrix) (h0 : 0 < c.prevalence)
    (h1 : c.prevalence < 1) (θ y : Bool) : 0 ≤ confusionChannel c θ y := by
  have hq : (0 : ℝ) < 1 - c.prevalence := sub_pos.mpr h1
  cases θ <;> cases y <;>
    simp only [confusionChannel, Bool.false_eq_true, if_false, if_true] <;>
    first
      | exact div_nonneg c.tp_nonneg h0.le
      | exact div_nonneg c.fn_nonneg h0.le
      | exact div_nonneg c.fp_nonneg hq.le
      | exact div_nonneg c.tn_nonneg hq.le

/-- **The corpus tie.** Reading the confusion table as a channel, taking the
prevalence prior and the cost pair `(1, lambda)` for a false negative and a
false positive, the `decisionRisk` of the identity decision rule is exactly
`ThresholdPolicyTransport.decisionLoss`. Thus the abstract channel risk here and
the confusion-cell cost used elsewhere in the corpus are the same number. -/
theorem confusion_channel_risk_eq_decisionLoss (c : ConfusionMatrix) (lambda : ℝ)
    (h0 : 0 < c.prevalence) (h1 : c.prevalence < 1) :
    decisionRisk (fun θ ↦ if θ then c.prevalence else 1 - c.prevalence)
        (chanCompose (confusionChannel c) identityRule)
        (fun θ z ↦ if θ then (if z then 0 else 1) else (if z then lambda else 0)) =
      ThresholdPolicyTransport.decisionLoss c lambda := by
  have hp : c.prevalence ≠ 0 := ne_of_gt h0
  have hq : (1 : ℝ) - c.prevalence ≠ 0 := ne_of_gt (sub_pos.mpr h1)
  have hrule : ∀ θ z : Bool, chanCompose (confusionChannel c) identityRule θ z =
      confusionChannel c θ z := by
    intro θ z
    simp [chanCompose, identityRule, mul_ite]
  simp only [decisionRisk, hrule, confusionChannel,
    ThresholdPolicyTransport.decisionLoss, Fintype.sum_bool, Bool.false_eq_true,
    if_false, if_true]
  field_simp
  try ring

/-- **The compactness step of the converse.** The channels reachable from `A` by
a garbling form the continuous image of a product of standard simplices, hence a
compact set, so the squared distance from `B` to that set is attained. No
convexity is used here; the minimiser is what the variational argument needs. -/
theorem exists_closest_garbling [Nonempty Y] (A : Θ → X → ℝ) (B : Θ → Y → ℝ) :
    ∃ G : X → Y → ℝ, (∀ x y, 0 ≤ G x y) ∧ (∀ x, ∑ y, G x y = 1) ∧
      ∀ G' : X → Y → ℝ, (∀ x y, 0 ≤ G' x y) → (∀ x, ∑ y, G' x y = 1) →
        ∑ θ, ∑ y, (B θ y - chanCompose A G θ y) ^ 2 ≤
          ∑ θ, ∑ y, (B θ y - chanCompose A G' θ y) ^ 2 := by
  classical
  have hcompact : IsCompact (Set.univ.pi (fun _ : X ↦ stdSimplex ℝ Y)) :=
    isCompact_univ_pi fun _ ↦ isCompact_stdSimplex Y
  have hne : (Set.univ.pi (fun _ : X ↦ stdSimplex ℝ Y)).Nonempty := by
    refine ⟨fun _ y ↦ if y = Classical.arbitrary Y then 1 else 0, Set.mem_univ_pi.mpr ?_⟩
    intro x
    refine ⟨fun y ↦ ?_, by simp⟩
    by_cases hy : y = Classical.arbitrary Y <;> simp [hy]
  have hcont : Continuous (fun G : X → Y → ℝ ↦
      ∑ θ, ∑ y, (B θ y - chanCompose A G θ y) ^ 2) := by
    simp only [chanCompose]
    refine continuous_finset_sum _ fun θ _ ↦ continuous_finset_sum _ fun y _ ↦ ?_
    refine Continuous.pow (Continuous.sub continuous_const ?_) 2
    exact continuous_finset_sum _ fun x _ ↦
      continuous_const.mul ((continuous_apply y).comp (continuous_apply x))
  obtain ⟨G, hGmem, hGmin⟩ := hcompact.exists_isMinOn hne hcont.continuousOn
  have hG := Set.mem_univ_pi.mp hGmem
  refine ⟨G, fun x y ↦ (hG x).1 y, fun x ↦ (hG x).2, ?_⟩
  intro G' hG'0 hG'1
  exact hGmin (Set.mem_univ_pi.mpr fun x ↦ ⟨fun y ↦ hG'0 x y, hG'1 x⟩)

end

end Descent.Portability.ChannelComparison
