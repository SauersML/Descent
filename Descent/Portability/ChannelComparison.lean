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
against the induced state-to-action matrix. `garbling_iff_decision_dominance`
proves both directions of TQ Theorem 4.9 / UPT Theorem 6.5: `B` is a garbling of
`A` exactly when `A` is never worse in any finite decision problem. The converse
is the manuscript's nearest-point argument, made unconditional here by
`exists_closest_garbling` (compactness of a product of standard simplices),
`closest_garbling_variational` (the segment between garblings is a garbling), and
the explicit separating decision problem built from the residual. The tie to the
corpus is
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

/-- A quadratic in `t` that is nonnegative throughout `[0, 1]` and has a
nonnegative leading coefficient has a nonpositive linear coefficient. This is the
one-variable fact behind the variational inequality at a nearest point. -/
theorem linear_coefficient_nonpos_of_nonneg_on_unit {b c : ℝ} (hc : 0 ≤ c)
    (h : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → 0 ≤ -(2 * t * b) + t ^ 2 * c) : b ≤ 0 := by
  by_contra hb
  push_neg at hb
  rcases eq_or_lt_of_le hc with heq | hlt
  · have h1 := h 1 zero_le_one le_rfl
    rw [← heq] at h1
    nlinarith
  · have ht0 : 0 < min 1 (b / c) := lt_min one_pos (div_pos hb hlt)
    have ht1 : min 1 (b / c) ≤ 1 := min_le_left _ _
    have htd : min 1 (b / c) * c ≤ b := (le_div_iff₀ hlt).mp (min_le_right _ _)
    have hk := h _ ht0.le ht1
    nlinarith [mul_le_mul_of_nonneg_left htd ht0.le]

omit [Fintype Θ] [Fintype Y] in
/-- A finite sum of an affine combination splits into that combination of sums. -/
theorem sum_affine_split {ι : Type*} [Fintype ι] (u v w : ι → ℝ) (a b : ℝ) :
    (∑ i, u i) - a * (∑ i, v i) + b * ∑ i, w i = ∑ i, (u i - a * v i + b * w i) := by
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]

/-- Two-index finite sums add termwise. -/
theorem sum_pair_add (u v : Θ → Y → ℝ) :
    ∑ θ, ∑ y, (u θ y + v θ y) = (∑ θ, ∑ y, u θ y) + ∑ θ, ∑ y, v θ y := by
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun θ _ ↦ Finset.sum_add_distrib

/-- Two-index finite sums subtract termwise. -/
theorem sum_pair_sub (u v : Θ → Y → ℝ) :
    ∑ θ, ∑ y, (u θ y - v θ y) = (∑ θ, ∑ y, u θ y) - ∑ θ, ∑ y, v θ y := by
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun θ _ ↦ Finset.sum_sub_distrib _ _

omit [Fintype Θ] [Fintype Y] in
/-- The composed channel moves affinely along a segment between two garblings. -/
theorem chanCompose_segment (A : Θ → X → ℝ) (G G' : X → Y → ℝ) (t : ℝ) (θ : Θ)
    (y : Y) :
    chanCompose A (fun x y ↦ G x y + t * (G' x y - G x y)) θ y =
      chanCompose A G θ y + t * (chanCompose A G' θ y - chanCompose A G θ y) := by
  have e1 : ∀ x, A θ x * (G x y + t * (G' x y - G x y)) =
      A θ x * G x y + (t * (A θ x * G' x y) - t * (A θ x * G x y)) := fun x ↦ by ring
  simp only [chanCompose]
  rw [Finset.sum_congr rfl fun x _ ↦ e1 x, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum]
  ring

/-- **The variational inequality at the closest garbling.** The segment between
two garblings is a garbling, so along it the squared distance to `B` is a
quadratic in the segment parameter which is minimised at the endpoint `G`. Hence
the residual `B - A G` has nonpositive inner product with every direction from
`A G` towards another reachable channel. -/
theorem closest_garbling_variational (A : Θ → X → ℝ) (B : Θ → Y → ℝ)
    (G : X → Y → ℝ)
    (hmin : ∀ G' : X → Y → ℝ, (∀ x y, 0 ≤ G' x y) → (∀ x, ∑ y, G' x y = 1) →
      ∑ θ, ∑ y, (B θ y - chanCompose A G θ y) ^ 2 ≤
        ∑ θ, ∑ y, (B θ y - chanCompose A G' θ y) ^ 2)
    (hG0 : ∀ x y, 0 ≤ G x y) (hG1 : ∀ x, ∑ y, G x y = 1)
    (G' : X → Y → ℝ) (hG'0 : ∀ x y, 0 ≤ G' x y) (hG'1 : ∀ x, ∑ y, G' x y = 1) :
    ∑ θ, ∑ y, (B θ y - chanCompose A G θ y) *
      (chanCompose A G' θ y - chanCompose A G θ y) ≤ 0 := by
  refine linear_coefficient_nonpos_of_nonneg_on_unit
    (c := ∑ θ, ∑ y, (chanCompose A G' θ y - chanCompose A G θ y) ^ 2)
    (Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ sq_nonneg _) ?_
  intro t ht0 ht1
  have h1t : (0 : ℝ) ≤ 1 - t := by linarith
  have hGt0 : ∀ x y, 0 ≤ G x y + t * (G' x y - G x y) := by
    intro x y
    have key : G x y + t * (G' x y - G x y) = (1 - t) * G x y + t * G' x y := by ring
    rw [key]
    exact add_nonneg (mul_nonneg h1t (hG0 x y)) (mul_nonneg ht0 (hG'0 x y))
  have hGt1 : ∀ x, ∑ y, (G x y + t * (G' x y - G x y)) = 1 := by
    intro x
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib, hG1 x, hG'1 x]
    ring
  have hm := hmin (fun x y ↦ G x y + t * (G' x y - G x y)) hGt0 hGt1
  have per : ∀ θ, ∑ y, (B θ y -
      chanCompose A (fun x y ↦ G x y + t * (G' x y - G x y)) θ y) ^ 2 =
      (∑ y, (B θ y - chanCompose A G θ y) ^ 2) -
        2 * t * (∑ y, (B θ y - chanCompose A G θ y) *
          (chanCompose A G' θ y - chanCompose A G θ y)) +
        t ^ 2 * ∑ y, (chanCompose A G' θ y - chanCompose A G θ y) ^ 2 := by
    intro θ
    rw [sum_affine_split]
    refine Finset.sum_congr rfl fun y _ ↦ ?_
    rw [chanCompose_segment]
    ring
  have hrw : ∑ θ, ∑ y, (B θ y -
      chanCompose A (fun x y ↦ G x y + t * (G' x y - G x y)) θ y) ^ 2 =
      (∑ θ, ∑ y, (B θ y - chanCompose A G θ y) ^ 2) -
        2 * t * (∑ θ, ∑ y, (B θ y - chanCompose A G θ y) *
          (chanCompose A G' θ y - chanCompose A G θ y)) +
        t ^ 2 * ∑ θ, ∑ y, (chanCompose A G' θ y - chanCompose A G θ y) ^ 2 :=
    (Finset.sum_congr rfl fun θ _ ↦ per θ).trans (sum_affine_split _ _ _ _ _).symm
  rw [hrw] at hm
  linarith

/-- Under the uniform prior and a loss which is the negated residual read
through a relabelling of the signal set as the action set, the expected loss is
minus the inner product of the state-to-action matrix with that residual. -/
theorem uniform_risk_relabel [Nonempty Θ] {m : ℕ} (e : Y ≃ Fin m) (K : Θ → Y → ℝ)
    (M : Θ → Fin m → ℝ) :
    decisionRisk (fun _ : Θ ↦ (Fintype.card Θ : ℝ)⁻¹) M
        (fun θ i ↦ -(Fintype.card Θ : ℝ) * K θ (e.symm i)) =
      -∑ θ, ∑ y, M θ (e y) * K θ y := by
  have hcard : (Fintype.card Θ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have per : ∀ θ : Θ, (Fintype.card Θ : ℝ)⁻¹ *
      ∑ i, M θ i * (-(Fintype.card Θ : ℝ) * K θ (e.symm i)) =
      -∑ y, M θ (e y) * K θ y := by
    intro θ
    have h1 : ∑ i, M θ i * (-(Fintype.card Θ : ℝ) * K θ (e.symm i)) =
        ∑ y, M θ (e y) * (-(Fintype.card Θ : ℝ) * K θ y) := by
      rw [← Equiv.sum_comp e (fun i ↦ M θ i * (-(Fintype.card Θ : ℝ) * K θ (e.symm i)))]
      exact Finset.sum_congr rfl fun y _ ↦ by rw [Equiv.symm_apply_apply]
    have h2 : ∑ y, M θ (e y) * (-(Fintype.card Θ : ℝ) * K θ y) =
        -(Fintype.card Θ : ℝ) * ∑ y, M θ (e y) * K θ y := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun y _ ↦ by ring
    have h3 : (Fintype.card Θ : ℝ)⁻¹ *
        (-(Fintype.card Θ : ℝ) * ∑ y, M θ (e y) * K θ y) =
        -(((Fintype.card Θ : ℝ)⁻¹ * (Fintype.card Θ : ℝ)) *
          ∑ y, M θ (e y) * K θ y) := by
      ring
    rw [h1, h2, h3, inv_mul_cancel₀ hcard, one_mul]
  simp only [decisionRisk]
  rw [Finset.sum_congr rfl fun θ _ ↦ per θ, Finset.sum_neg_distrib]

/-- **TQ Theorem 4.9 / UPT Theorem 6.5, both directions.** `B` is a garbling of
`A` exactly when, for every finite decision problem and every prior, some
decision rule after `A` has expected loss no larger than the given decision rule
after `B`. The forward direction composes the garbling with the rule. The
converse takes the nearest reachable channel `A G` to `B`, and if the residual
`H = B - A G` is nonzero it is itself a separating direction: with the uniform
prior, action set the signal set of `B`, and loss `-|Θ| H`, the identity rule
after `B` beats every rule after `A` strictly, contradicting the hypothesis. The
only domain conditions used are that `B`'s rows sum to one and that the state
space is nonempty, which is what the uniform prior needs; row-stochasticity of
`A` is not needed for the equivalence. -/
theorem garbling_iff_decision_dominance [Nonempty Θ] (A : Θ → X → ℝ) (B : Θ → Y → ℝ)
    (hB1 : ∀ θ, ∑ y, B θ y = 1) :
    (∃ G : X → Y → ℝ, (∀ x y, 0 ≤ G x y) ∧ (∀ x, ∑ y, G x y = 1) ∧
        B = chanCompose A G) ↔
      ∀ (m : ℕ) (prior : Θ → ℝ) (loss : Θ → Fin m → ℝ) (dB : Y → Fin m → ℝ),
        (∀ θ, 0 ≤ prior θ) → (∑ θ, prior θ = 1) → (∀ y z, 0 ≤ dB y z) →
        (∀ y, ∑ z, dB y z = 1) →
        ∃ dA : X → Fin m → ℝ, (∀ x z, 0 ≤ dA x z) ∧ (∀ x, ∑ z, dA x z = 1) ∧
          decisionRisk prior (chanCompose A dA) loss ≤
            decisionRisk prior (chanCompose B dB) loss := by
  constructor
  · rintro ⟨G, hG0, hG1, hB⟩ m prior loss dB _ _ hd0 hd1
    obtain ⟨dA, h1, h2, h3⟩ := garbling_no_worse A B G hG0 hG1 hB prior loss dB hd0 hd1
    exact ⟨dA, h1, h2, le_of_eq h3⟩
  · intro hdom
    have hY : Nonempty Y := by
      by_contra hYc
      rw [not_nonempty_iff] at hYc
      have h := hB1 (Classical.arbitrary Θ)
      rw [Finset.univ_eq_empty, Finset.sum_empty] at h
      exact zero_ne_one h
    obtain ⟨G, hG0, hG1, hmin⟩ := exists_closest_garbling A B
    refine ⟨G, hG0, hG1, ?_⟩
    by_contra hne
    obtain ⟨θ₀, hθ₀⟩ := Function.ne_iff.mp hne
    obtain ⟨y₀, hy₀⟩ := Function.ne_iff.mp hθ₀
    have hHpos : 0 < ∑ θ, ∑ y, (B θ y - chanCompose A G θ y) ^ 2 := by
      have h3 : 0 < (B θ₀ y₀ - chanCompose A G θ₀ y₀) ^ 2 :=
        lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 (sub_ne_zero.mpr hy₀)))
      have h1 : (B θ₀ y₀ - chanCompose A G θ₀ y₀) ^ 2 ≤
          ∑ y, (B θ₀ y - chanCompose A G θ₀ y) ^ 2 :=
        Finset.single_le_sum (f := fun y ↦ (B θ₀ y - chanCompose A G θ₀ y) ^ 2)
          (fun y _ ↦ sq_nonneg _) (Finset.mem_univ y₀)
      have h2 : (∑ y, (B θ₀ y - chanCompose A G θ₀ y) ^ 2) ≤
          ∑ θ, ∑ y, (B θ y - chanCompose A G θ y) ^ 2 :=
        Finset.single_le_sum (f := fun θ ↦ ∑ y, (B θ y - chanCompose A G θ y) ^ 2)
          (fun θ _ ↦ Finset.sum_nonneg fun y _ ↦ sq_nonneg _) (Finset.mem_univ θ₀)
      linarith
    obtain ⟨m, e⟩ : Σ m : ℕ, Y ≃ Fin m := ⟨_, Fintype.equivFin Y⟩
    have hcard : (Fintype.card Θ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    have hprior1 : ∑ _θ : Θ, (Fintype.card Θ : ℝ)⁻¹ = 1 := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_inv_cancel₀ hcard]
    obtain ⟨dA, hdA0, hdA1, hle⟩ := hdom m (fun _ ↦ (Fintype.card Θ : ℝ)⁻¹)
      (fun θ i ↦ -(Fintype.card Θ : ℝ) *
        (B θ (e.symm i) - chanCompose A G θ (e.symm i)))
      (fun y i ↦ if i = e y then 1 else 0) (fun _ ↦ by positivity) hprior1
      (fun y i ↦ by by_cases h : i = e y <;> simp [h]) (fun y ↦ by simp)
    have hBd : ∀ θ y, chanCompose B (fun y' i ↦ if i = e y' then 1 else 0) θ (e y) =
        B θ y := by
      intro θ y
      show (∑ y', B θ y' * (if e y = e y' then 1 else 0)) = B θ y
      refine (Finset.sum_eq_single y ?_ ?_).trans ?_
      · intro y' _ hy'
        have hcond : ¬(e y = e y') := fun hc ↦ hy' (e.injective hc).symm
        simp [hcond]
      · intro hy'
        simp at hy'
      · simp
    have hriskA := uniform_risk_relabel e
      (fun θ y ↦ B θ y - chanCompose A G θ y) (chanCompose A dA)
    have hriskB := uniform_risk_relabel e
      (fun θ y ↦ B θ y - chanCompose A G θ y)
      (chanCompose B (fun y' i ↦ if i = e y' then 1 else 0))
    have e1 : ∑ θ, ∑ y, chanCompose A dA θ (e y) * (B θ y - chanCompose A G θ y) =
        ∑ θ, ∑ y, chanCompose A (fun x y' ↦ dA x (e y')) θ y *
          (B θ y - chanCompose A G θ y) := rfl
    have e2 : ∑ θ, ∑ y, chanCompose B (fun y' i ↦ if i = e y' then 1 else 0) θ (e y) *
          (B θ y - chanCompose A G θ y) =
        ∑ θ, ∑ y, B θ y * (B θ y - chanCompose A G θ y) :=
      Finset.sum_congr rfl fun θ _ ↦ Finset.sum_congr rfl fun y _ ↦ by rw [hBd θ y]
    rw [hriskA, hriskB, e1, e2] at hle
    have hvar := closest_garbling_variational A B G hmin hG0 hG1
      (fun x y' ↦ dA x (e y')) (fun x y' ↦ hdA0 x (e y'))
      (fun x ↦ (Equiv.sum_comp e (dA x)).trans (hdA1 x))
    have hsplit : ∑ θ, ∑ y, (B θ y - chanCompose A G θ y) *
          (chanCompose A (fun x y' ↦ dA x (e y')) θ y - chanCompose A G θ y) =
        (∑ θ, ∑ y, chanCompose A (fun x y' ↦ dA x (e y')) θ y *
            (B θ y - chanCompose A G θ y)) -
          ∑ θ, ∑ y, chanCompose A G θ y * (B θ y - chanCompose A G θ y) := by
      rw [← sum_pair_sub]
      exact Finset.sum_congr rfl fun θ _ ↦ Finset.sum_congr rfl fun y _ ↦ by ring
    have hBsplit : ∑ θ, ∑ y, B θ y * (B θ y - chanCompose A G θ y) =
        (∑ θ, ∑ y, chanCompose A G θ y * (B θ y - chanCompose A G θ y)) +
          ∑ θ, ∑ y, (B θ y - chanCompose A G θ y) ^ 2 := by
      rw [← sum_pair_add]
      exact Finset.sum_congr rfl fun θ _ ↦ Finset.sum_congr rfl fun y _ ↦ by ring
    linarith

end

end Descent.Portability.ChannelComparison
