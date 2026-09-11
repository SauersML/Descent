/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.TurnoverDependence

assert_below Descent.Decision Descent.Program

/-!
# The sharp synchrony envelope at fixed one-locus turnover

With oracle weights and equal squared effects the population accuracy of
`TurnoverDependence.turnoverWorld` is exactly `Q₀ U²`, where `U` is the mean
effect sign. TQ Theorem 3.6 is proved here in both directions: the closed-form
lower bound `Q₀[m² + (m-u_k)(u_{k+1}-m)]` and the upper bound `Q₀` hold for every
joint sign law whose one-locus means are all `m`, and an explicit one-parameter
family of joint laws with those same one-locus means attains every value of the
interval, the two endpoints included. The lower-endpoint law mixes the cyclic
shifts of two threshold patterns; the upper-endpoint law is the fully
synchronised two-point law. The bound side assumes only that the signs are
genuine `±1` values with the prescribed marginal means; it does not assume the
joint law is a product, exchangeable, or Markov.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.SynchronyEnvelope

open Foundations TurnoverDependence

noncomputable section

section Grid

/-- The count grid `u_k = -1 + 2k/n` on which the mean effect sign lives. -/
def gridPoint (n k : ℕ) : ℝ := -1 + 2 * k / n

/-- The mean effect sign `U = (1/n) ∑ Z_i`. -/
def meanSign (n : ℕ) (z : Fin n → ℝ) : ℝ := (∑ i, z i) / n

/-- **Equal squared effects with oracle weights give `q = Q₀ U²`.** -/
theorem equal_effect_r2 {n : ℕ} (hn : 0 < n) (H sigma : ℝ) (hH : 0 < H) (b : Fin n → ℝ)
    (hb : ∀ i, b i ^ 2 = H / n) (z : Fin n → ℝ) (hz : ∀ i, z i = 1 ∨ z i = -1) :
    (turnoverWorld b sigma z).r2 b = ceiling H sigma * meanSign n z ^ 2 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hnne : (n : ℝ) ≠ 0 := ne_of_gt hnR
  have hV : (0 : ℝ) < H + sigma ^ 2 := by nlinarith [sq_nonneg sigma]
  have hVne : H + sigma ^ 2 ≠ 0 := ne_of_gt hV
  have hHne : H ≠ 0 := ne_of_gt hH
  have hsum : ∑ i, b i ^ 2 = H := by
    rw [Finset.sum_congr rfl fun i _ ↦ hb i, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    field_simp
  have hcov : ∑ i, b i * b i * z i = H / n * ∑ i, z i := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [← hb i]
    ring
  rw [turnoverWorld_r2 b sigma z b hz, hsum, hcov, ceiling, meanSign]
  field_simp

/-- Every `±1` configuration has a sign sum on the count grid. -/
theorem sum_signs_grid {n : ℕ} (z : Fin n → ℝ) (hz : ∀ i, z i = 1 ∨ z i = -1) :
    ∃ c : ℕ, c ≤ n ∧ ∑ i, z i = 2 * (c : ℝ) - n := by
  classical
  refine ⟨(Finset.univ.filter fun i ↦ z i = 1).card, ?_, ?_⟩
  · have h := Finset.card_filter_le (Finset.univ : Finset (Fin n)) fun i ↦ z i = 1
    simpa using h
  · have hrw : ∀ i : Fin n, z i = 2 * (if z i = 1 then (1 : ℝ) else 0) - 1 := by
      intro i
      rcases hz i with h | h
      · rw [h, if_pos rfl]
        norm_num
      · rw [h, if_neg (by norm_num)]
        norm_num
    rw [Finset.sum_congr rfl fun i _ ↦ hrw i, Finset.sum_sub_distrib, ← Finset.mul_sum,
      Finset.sum_boole, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      mul_one]

/-- **The grid gap is nonnegative.**  No grid point lies strictly between two adjacent
grid points, so `(U-u_k)(U-u_{k+1}) ≥ 0` pointwise. -/
theorem grid_gap_nonneg {n : ℕ} (hn : 0 < n) (c k : ℕ) :
    0 ≤ (gridPoint n c - gridPoint n k) * (gridPoint n c - gridPoint n (k + 1)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hnne : (n : ℝ) ≠ 0 := ne_of_gt hnR
  have hfac : (gridPoint n c - gridPoint n k) * (gridPoint n c - gridPoint n (k + 1))
      = 4 * (((c : ℝ) - k) * ((c : ℝ) - k - 1)) / ((n : ℝ) * n) := by
    unfold gridPoint
    push_cast
    field_simp
    ring
  have hnum : 0 ≤ ((c : ℝ) - k) * ((c : ℝ) - k - 1) := by
    rcases le_or_lt c k with h | h
    · have h1 : (c : ℝ) ≤ k := by exact_mod_cast h
      nlinarith
    · have h1 : (k : ℝ) + 1 ≤ c := by exact_mod_cast h
      nlinarith
  rw [hfac]
  apply div_nonneg
  · linarith
  · positivity

/-- The mean effect sign of a `±1` configuration is a grid point. -/
theorem meanSign_eq_gridPoint {n : ℕ} (hn : 0 < n) (z : Fin n → ℝ)
    (hz : ∀ i, z i = 1 ∨ z i = -1) : ∃ c : ℕ, c ≤ n ∧ meanSign n z = gridPoint n c := by
  obtain ⟨c, hc, hsum⟩ := sum_signs_grid z hz
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hnne : (n : ℝ) ≠ 0 := ne_of_gt hnR
  refine ⟨c, hc, ?_⟩
  rw [meanSign, hsum, gridPoint]
  field_simp
  ring

/-- The mean effect sign has the common one-locus mean as its own mean. -/
theorem meanSign_mean {Ω : Type*} (E : ExpFunctional Ω) {n : ℕ} (hn : 0 < n)
    (Z : Ω → Fin n → ℝ) (m : ℝ) (hm : ∀ i, E (fun ω ↦ Z ω i) = m) :
    E (fun ω ↦ meanSign n (Z ω)) = m := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hnne : (n : ℝ) ≠ 0 := ne_of_gt hnR
  have hs : (fun ω ↦ meanSign n (Z ω)) = ((n : ℝ)⁻¹) • fun ω ↦ ∑ i, Z ω i := by
    funext ω
    simp only [Pi.smul_apply, smul_eq_mul, meanSign]
    ring
  rw [hs, ExpFunctional.smul_eval,
    eval_finset_sum E Finset.univ fun (i : Fin n) (ω : Ω) ↦ Z ω i,
    Finset.sum_congr rfl fun i _ ↦ hm i, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  field_simp

/-- The second moment of the mean effect sign is at least the grid-corrected square. -/
theorem meanSign_sq_lower {Ω : Type*} (E : ExpFunctional Ω) {n : ℕ} (hn : 0 < n)
    (Z : Ω → Fin n → ℝ) (hZ : ∀ ω i, Z ω i = 1 ∨ Z ω i = -1) (m : ℝ)
    (hm : ∀ i, E (fun ω ↦ Z ω i) = m) (k : ℕ) :
    m ^ 2 + (m - gridPoint n k) * (gridPoint n (k + 1) - m)
      ≤ E (fun ω ↦ meanSign n (Z ω) ^ 2) := by
  have hdecomp : (fun ω ↦ (meanSign n (Z ω) - gridPoint n k)
        * (meanSign n (Z ω) - gridPoint n (k + 1)))
      = ((fun ω ↦ meanSign n (Z ω) ^ 2)
          - ((gridPoint n k + gridPoint n (k + 1)) • fun ω ↦ meanSign n (Z ω)))
        + fun _ ↦ gridPoint n k * gridPoint n (k + 1) := by
    funext ω
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hnn : 0 ≤ E (fun ω ↦ (meanSign n (Z ω) - gridPoint n k)
      * (meanSign n (Z ω) - gridPoint n (k + 1))) := by
    refine E.nonneg_eval _ fun ω ↦ ?_
    obtain ⟨c, _, hc⟩ := meanSign_eq_gridPoint hn (Z ω) (hZ ω)
    rw [hc]
    exact grid_gap_nonneg hn c k
  rw [hdecomp, ExpFunctional.add_eval, ExpFunctional.eval_sub, ExpFunctional.smul_eval,
    ExpFunctional.eval_const, meanSign_mean E hn Z m hm] at hnn
  nlinarith [hnn]

/-- The second moment of the mean effect sign never exceeds one. -/
theorem meanSign_sq_upper {Ω : Type*} (E : ExpFunctional Ω) {n : ℕ} (hn : 0 < n)
    (Z : Ω → Fin n → ℝ) (hZ : ∀ ω i, Z ω i = 1 ∨ Z ω i = -1) :
    E (fun ω ↦ meanSign n (Z ω) ^ 2) ≤ 1 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hpt : ∀ ω, meanSign n (Z ω) ^ 2 ≤ (1 : ℝ) := by
    intro ω
    obtain ⟨c, hc, hgp⟩ := meanSign_eq_gridPoint hn (Z ω) (hZ ω)
    have hcR : (c : ℝ) ≤ n := by exact_mod_cast hc
    have hc0 : (0 : ℝ) ≤ c := Nat.cast_nonneg c
    have h1 : meanSign n (Z ω) ≤ 1 := by
      rw [hgp, gridPoint]
      have hdiv : 2 * (c : ℝ) / n ≤ 2 := by
        rw [div_le_iff₀ hnR]
        nlinarith
      linarith
    have h2 : -1 ≤ meanSign n (Z ω) := by
      rw [hgp, gridPoint]
      have hpos : 0 ≤ 2 * (c : ℝ) / n := by positivity
      linarith
    nlinarith
  have hmono := E.eval_mono hpt
  rwa [ExpFunctional.eval_const] at hmono

/-- **TQ Theorem 3.6, the envelope.**  At equal squared effects, oracle weights, and one
common one-locus mean `m` bracketed by adjacent grid points, expected accuracy lies in
`[Q₀(m² + (m-u_k)(u_{k+1}-m)), Q₀]`. The joint law is arbitrary. -/
theorem synchrony_envelope {Ω : Type*} (E : ExpFunctional Ω) {n : ℕ} (hn : 0 < n)
    (Z : Ω → Fin n → ℝ) (hZ : ∀ ω i, Z ω i = 1 ∨ Z ω i = -1) (m : ℝ)
    (hm : ∀ i, E (fun ω ↦ Z ω i) = m) (k : ℕ) (H sigma : ℝ) (hH : 0 < H)
    (b : Fin n → ℝ) (hb : ∀ i, b i ^ 2 = H / n) :
    ceiling H sigma * (m ^ 2 + (m - gridPoint n k) * (gridPoint n (k + 1) - m))
        ≤ E (fun ω ↦ (turnoverWorld b sigma (Z ω)).r2 b) ∧
      E (fun ω ↦ (turnoverWorld b sigma (Z ω)).r2 b) ≤ ceiling H sigma := by
  have hV : (0 : ℝ) < H + sigma ^ 2 := by nlinarith [sq_nonneg sigma]
  have hQ : 0 < ceiling H sigma := div_pos hH hV
  have hfun : (fun ω ↦ (turnoverWorld b sigma (Z ω)).r2 b)
      = (ceiling H sigma) • fun ω ↦ meanSign n (Z ω) ^ 2 := by
    funext ω
    simp only [Pi.smul_apply, smul_eq_mul]
    exact equal_effect_r2 hn H sigma hH b hb (Z ω) (hZ ω)
  rw [hfun, ExpFunctional.smul_eval]
  constructor
  · exact mul_le_mul_of_nonneg_left (meanSign_sq_lower E hn Z hZ m hm k) hQ.le
  · have h := mul_le_mul_of_nonneg_left (meanSign_sq_upper E hn Z hZ) hQ.le
    linarith

end Grid

section Attainment

/-- Positivity of a successor, at the syntactic form the envelope statements use. -/
theorem succ_pos' (N : ℕ) : 0 < N + 1 := Nat.succ_pos N

/-- Cyclic threshold pattern: locus `i` is positive exactly when `i - s` is one of the
first `c` positions of the cyclic order. -/
def shiftSigns (N c : ℕ) (s i : Fin (N + 1)) : ℝ := sgn (decide ((i - s).val < c))

/-- A threshold sum over the whole index range. -/
theorem sum_threshold_signs (M c : ℕ) (hc : c ≤ M) :
    ∑ r : Fin M, sgn (decide (r.val < c)) = 2 * (c : ℝ) - M := by
  have h1 : ∀ j ∈ Finset.Ico 0 c, sgn (decide (j < c)) = (1 : ℝ) := by
    intro j hj
    rw [Finset.mem_Ico] at hj
    simp [hj.2]
  have h2 : ∀ j ∈ Finset.Ico c M, sgn (decide (j < c)) = (-1 : ℝ) := by
    intro j hj
    rw [Finset.mem_Ico] at hj
    have hnot : ¬ (j < c) := not_lt.mpr hj.1
    simp [hnot]
  rw [Fin.sum_univ_eq_sum_range (fun j ↦ sgn (decide (j < c))) M, Finset.range_eq_Ico,
    ← Finset.sum_Ico_consecutive (fun j ↦ sgn (decide (j < c))) (Nat.zero_le c) hc,
    Finset.sum_congr rfl h1, Finset.sum_congr rfl h2, Finset.sum_const, Finset.sum_const,
    Nat.card_Ico, Nat.card_Ico, nsmul_eq_mul, nsmul_eq_mul, Nat.cast_sub hc, Nat.sub_zero]
  ring

/-- Each shifted threshold pattern has exactly `c` positive loci. -/
theorem sum_shiftSigns_over_loci (N c : ℕ) (hc : c ≤ N + 1) (s : Fin (N + 1)) :
    ∑ i, shiftSigns N c s i = 2 * (c : ℝ) - (N + 1) := by
  have hrw : ∀ i : Fin (N + 1), shiftSigns N c s i
      = (fun r : Fin (N + 1) ↦ sgn (decide (r.val < c))) ((Equiv.subRight s) i) := fun _ ↦ rfl
  rw [Finset.sum_congr rfl fun i _ ↦ hrw i,
    Equiv.sum_comp (Equiv.subRight s) fun r : Fin (N + 1) ↦ sgn (decide (r.val < c)),
    sum_threshold_signs (N + 1) c hc]
  push_cast
  ring

/-- Each locus is positive in exactly `c` of the `N+1` shifts. -/
theorem sum_shiftSigns_over_shifts (N c : ℕ) (hc : c ≤ N + 1) (i : Fin (N + 1)) :
    ∑ s, shiftSigns N c s i = 2 * (c : ℝ) - (N + 1) := by
  have hrw : ∀ s : Fin (N + 1), shiftSigns N c s i
      = (fun r : Fin (N + 1) ↦ sgn (decide (r.val < c))) ((Equiv.subLeft i) s) := fun _ ↦ rfl
  rw [Finset.sum_congr rfl fun s _ ↦ hrw s,
    Equiv.sum_comp (Equiv.subLeft i) fun r : Fin (N + 1) ↦ sgn (decide (r.val < c)),
    sum_threshold_signs (N + 1) c hc]
  push_cast
  ring

/-- The mean effect sign of a shifted threshold pattern is exactly its grid point. -/
theorem meanSign_shiftSigns (N c : ℕ) (hc : c ≤ N + 1) (s : Fin (N + 1)) :
    meanSign (N + 1) (shiftSigns N c s) = gridPoint (N + 1) c := by
  have hne : ((N : ℝ) + 1) ≠ 0 := by positivity
  rw [meanSign, sum_shiftSigns_over_loci N c hc s, gridPoint]
  push_cast
  field_simp
  ring

/-- The mixing weight `λ = (u_{k+1} - m)/(u_{k+1} - u_k)` of the lower-endpoint law. -/
def lowerWeight (n k : ℕ) (m : ℝ) : ℝ := (gridPoint n (k + 1) - m) * n / 2

/-- The mixing weight is nonnegative below the upper bracketing grid point. -/
theorem lowerWeight_nonneg (n k : ℕ) (m : ℝ) (hk2 : m ≤ gridPoint n (k + 1)) :
    0 ≤ lowerWeight n k m := by
  unfold lowerWeight
  have h1 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have h2 : (0 : ℝ) ≤ gridPoint n (k + 1) - m := by linarith
  positivity

/-- The mixing weight is at most one above the lower bracketing grid point. -/
theorem lowerWeight_le_one {n : ℕ} (hn : 0 < n) (k : ℕ) (m : ℝ)
    (hk1 : gridPoint n k ≤ m) : lowerWeight n k m ≤ 1 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hgap : gridPoint n (k + 1) - gridPoint n k = 2 / n := by
    unfold gridPoint
    push_cast
    field_simp
    ring
  have h : gridPoint n (k + 1) - m ≤ 2 / n := by linarith
  unfold lowerWeight
  rw [div_le_one (by norm_num : (0 : ℝ) < 2)]
  calc (gridPoint n (k + 1) - m) * n ≤ 2 / n * n := by
        exact mul_le_mul_of_nonneg_right h hnR.le
    _ = 2 := by field_simp

/-- The mixture reproduces the prescribed mean exactly. -/
theorem lowerWeight_mix {n : ℕ} (hn : 0 < n) (k : ℕ) (m : ℝ) :
    lowerWeight n k m * gridPoint n k + (1 - lowerWeight n k m) * gridPoint n (k + 1) = m := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hnne : (n : ℝ) ≠ 0 := ne_of_gt hnR
  unfold lowerWeight gridPoint
  push_cast
  field_simp
  ring

/-- **The envelope family of joint sign laws.**  Weight `theta` goes to the mixture of two
adjacent threshold levels, `1 - theta` to the fully synchronised two-point law. -/
def envelopeWeight (N k : ℕ) (m theta : ℝ) : (Fin (N + 1) × Bool) ⊕ Bool → ℝ :=
  Sum.elim
    (fun sb ↦ theta
      * (if sb.2 then 1 - lowerWeight (N + 1) k m else lowerWeight (N + 1) k m) / (N + 1))
    (fun c ↦ (1 - theta) * ((1 + m * sgn c) / 2))

/-- The effect-sign field of the envelope family. -/
def envelopeSigns (N k : ℕ) : (Fin (N + 1) × Bool) ⊕ Bool → Fin (N + 1) → ℝ :=
  Sum.elim (fun sb i ↦ shiftSigns N (if sb.2 then k + 1 else k) sb.1 i) fun c _ ↦ sgn c

/-- The envelope family carries genuine `±1` effect signs. -/
theorem envelopeSigns_cases (N k : ℕ) (x : (Fin (N + 1) × Bool) ⊕ Bool) (i : Fin (N + 1)) :
    envelopeSigns N k x i = 1 ∨ envelopeSigns N k x i = -1 := by
  cases x with
  | inl sb => exact sgn_cases _
  | inr c => exact sgn_cases c

/-- The envelope weights are nonnegative. -/
theorem envelopeWeight_nonneg (N k : ℕ) {m theta : ℝ} (hm : -1 ≤ m) (hm' : m ≤ 1)
    (hl0 : 0 ≤ lowerWeight (N + 1) k m) (hl1 : lowerWeight (N + 1) k m ≤ 1)
    (ht0 : 0 ≤ theta) (ht1 : theta ≤ 1) :
    ∀ x, 0 ≤ envelopeWeight N k m theta x := by
  intro x
  have hN : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  cases x with
  | inl sb =>
      show 0 ≤ theta * (if sb.2 then 1 - lowerWeight (N + 1) k m
        else lowerWeight (N + 1) k m) / (N + 1)
      have hbr : 0 ≤ (if sb.2 then 1 - lowerWeight (N + 1) k m
          else lowerWeight (N + 1) k m) := by
        by_cases hb : sb.2 = true
        · rw [if_pos hb]
          linarith
        · rw [if_neg hb]
          exact hl0
      have : 0 ≤ theta * (if sb.2 then 1 - lowerWeight (N + 1) k m
          else lowerWeight (N + 1) k m) := mul_nonneg ht0 hbr
      positivity
  | inr c =>
      show 0 ≤ (1 - theta) * ((1 + m * sgn c) / 2)
      have h2 : 0 ≤ (1 + m * sgn c) / 2 := by
        rcases sgn_cases c with h | h <;> rw [h] <;> linarith
      exact mul_nonneg (by linarith) h2

/-- The envelope weights are a probability vector. -/
theorem sum_envelopeWeight (N k : ℕ) (m theta : ℝ) :
    ∑ x, envelopeWeight N k m theta x = 1 := by
  have hNne : ((N : ℝ) + 1) ≠ 0 := by positivity
  rw [Fintype.sum_sum_type]
  have hleft : ∑ sb : Fin (N + 1) × Bool, envelopeWeight N k m theta (Sum.inl sb) = theta := by
    rw [Fintype.sum_prod_type]
    have hin : ∀ s : Fin (N + 1),
        ∑ c : Bool, envelopeWeight N k m theta (Sum.inl (s, c)) = theta / (N + 1) := by
      intro s
      rw [Fintype.sum_bool]
      show theta * (1 - lowerWeight (N + 1) k m) / (N + 1)
        + theta * lowerWeight (N + 1) k m / (N + 1) = theta / (N + 1)
      field_simp
      ring
    rw [Finset.sum_congr rfl fun s _ ↦ hin s, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    push_cast
    field_simp
  have hright : ∑ c : Bool, envelopeWeight N k m theta (Sum.inr c) = 1 - theta := by
    rw [Fintype.sum_bool]
    show (1 - theta) * ((1 + m * sgn true) / 2) + (1 - theta) * ((1 + m * sgn false) / 2)
      = 1 - theta
    rw [sgn_true, sgn_false]
    ring
  rw [hleft, hright]
  ring

/-- **The envelope law.**  A single one-parameter family of joint sign laws on a finite
space, with `theta` mixing the two-level threshold law and the synchronised law. -/
def envelopeLaw (N k : ℕ) (m theta : ℝ) (hm : -1 ≤ m) (hm' : m ≤ 1)
    (hk1 : gridPoint (N + 1) k ≤ m) (hk2 : m ≤ gridPoint (N + 1) (k + 1))
    (ht0 : 0 ≤ theta) (ht1 : theta ≤ 1) : ExpFunctional ((Fin (N + 1) × Bool) ⊕ Bool) :=
  weightedExp (envelopeWeight N k m theta)
    (envelopeWeight_nonneg N k hm hm' (lowerWeight_nonneg (N + 1) k m hk2)
      (lowerWeight_le_one (succ_pos' N) k m hk1) ht0 ht1)
    (sum_envelopeWeight N k m theta)

/-- **Every member of the family has the prescribed one-locus mean at every locus.** -/
theorem envelopeLaw_marginal (N k : ℕ) (hk : k + 1 ≤ N + 1) (m theta : ℝ) (hm : -1 ≤ m)
    (hm' : m ≤ 1) (hk1 : gridPoint (N + 1) k ≤ m) (hk2 : m ≤ gridPoint (N + 1) (k + 1))
    (ht0 : 0 ≤ theta) (ht1 : theta ≤ 1) (i : Fin (N + 1)) :
    envelopeLaw N k m theta hm hm' hk1 hk2 ht0 ht1 (fun x ↦ envelopeSigns N k x i) = m := by
  have hNne : ((N : ℝ) + 1) ≠ 0 := by positivity
  have hkle : k ≤ N + 1 := le_trans (Nat.le_succ k) hk
  rw [envelopeLaw, weightedExp_apply, Fintype.sum_sum_type]
  have hleft : ∑ sb : Fin (N + 1) × Bool,
      envelopeWeight N k m theta (Sum.inl sb) * envelopeSigns N k (Sum.inl sb) i
      = theta * (lowerWeight (N + 1) k m * gridPoint (N + 1) k
          + (1 - lowerWeight (N + 1) k m) * gridPoint (N + 1) (k + 1)) := by
    rw [Fintype.sum_prod_type]
    have hin : ∀ s : Fin (N + 1),
        ∑ c : Bool, envelopeWeight N k m theta (Sum.inl (s, c))
            * envelopeSigns N k (Sum.inl (s, c)) i
          = theta * ((1 - lowerWeight (N + 1) k m) * shiftSigns N (k + 1) s i
              + lowerWeight (N + 1) k m * shiftSigns N k s i) / (N + 1) := by
      intro s
      rw [Fintype.sum_bool]
      show theta * (1 - lowerWeight (N + 1) k m) / (N + 1) * shiftSigns N (k + 1) s i
        + theta * lowerWeight (N + 1) k m / (N + 1) * shiftSigns N k s i = _
      field_simp
    rw [Finset.sum_congr rfl fun s _ ↦ hin s]
    rw [← Finset.sum_div, ← Finset.mul_sum]
    have hsplit : ∑ s : Fin (N + 1), ((1 - lowerWeight (N + 1) k m) * shiftSigns N (k + 1) s i
        + lowerWeight (N + 1) k m * shiftSigns N k s i)
        = (1 - lowerWeight (N + 1) k m) * (2 * ((k : ℝ) + 1) - (N + 1))
          + lowerWeight (N + 1) k m * (2 * (k : ℝ) - (N + 1)) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
        sum_shiftSigns_over_shifts N (k + 1) hk i, sum_shiftSigns_over_shifts N k hkle i]
      push_cast
      ring
    rw [hsplit]
    unfold gridPoint
    push_cast
    field_simp
    ring
  have hright : ∑ c : Bool,
      envelopeWeight N k m theta (Sum.inr c) * envelopeSigns N k (Sum.inr c) i
      = (1 - theta) * m := by
    rw [Fintype.sum_bool]
    show (1 - theta) * ((1 + m * sgn true) / 2) * sgn true
      + (1 - theta) * ((1 + m * sgn false) / 2) * sgn false = (1 - theta) * m
    rw [sgn_true, sgn_false]
    ring
  rw [hleft, hright, lowerWeight_mix (succ_pos' N) k m]
  ring

/-- **Exact expected accuracy of the family.**  It is affine in `theta`, equal to the
lower endpoint of TQ (3.9) at `theta = 1` and to the ceiling `Q₀` at `theta = 0`. -/
theorem envelopeLaw_expected_r2 (N k : ℕ) (hk : k + 1 ≤ N + 1) (m theta : ℝ) (hm : -1 ≤ m)
    (hm' : m ≤ 1) (hk1 : gridPoint (N + 1) k ≤ m) (hk2 : m ≤ gridPoint (N + 1) (k + 1))
    (ht0 : 0 ≤ theta) (ht1 : theta ≤ 1) (H sigma : ℝ) (hH : 0 < H) (b : Fin (N + 1) → ℝ)
    (hb : ∀ i, b i ^ 2 = H / ((N + 1 : ℕ) : ℝ)) :
    envelopeLaw N k m theta hm hm' hk1 hk2 ht0 ht1
        (fun x ↦ (turnoverWorld b sigma (envelopeSigns N k x)).r2 b)
      = ceiling H sigma * (theta * (m ^ 2 + (m - gridPoint (N + 1) k)
          * (gridPoint (N + 1) (k + 1) - m)) + (1 - theta)) := by
  have hNne : ((N : ℝ) + 1) ≠ 0 := by positivity
  have hkle : k ≤ N + 1 := le_trans (Nat.le_succ k) hk
  have hpt : ∀ x, envelopeWeight N k m theta x
        * (turnoverWorld b sigma (envelopeSigns N k x)).r2 b
      = ceiling H sigma * (envelopeWeight N k m theta x
          * meanSign (N + 1) (envelopeSigns N k x) ^ 2) := by
    intro x
    rw [equal_effect_r2 (succ_pos' N) H sigma hH b hb (envelopeSigns N k x)
      (envelopeSigns_cases N k x)]
    ring
  rw [envelopeLaw, weightedExp_apply, Finset.sum_congr rfl fun x _ ↦ hpt x, ← Finset.mul_sum]
  congr 1
  rw [Fintype.sum_sum_type]
  have hleft : ∑ sb : Fin (N + 1) × Bool, envelopeWeight N k m theta (Sum.inl sb)
      * meanSign (N + 1) (envelopeSigns N k (Sum.inl sb)) ^ 2
      = theta * (lowerWeight (N + 1) k m * gridPoint (N + 1) k ^ 2
          + (1 - lowerWeight (N + 1) k m) * gridPoint (N + 1) (k + 1) ^ 2) := by
    rw [Fintype.sum_prod_type]
    have hin : ∀ s : Fin (N + 1),
        ∑ c : Bool, envelopeWeight N k m theta (Sum.inl (s, c))
            * meanSign (N + 1) (envelopeSigns N k (Sum.inl (s, c))) ^ 2
          = theta * ((1 - lowerWeight (N + 1) k m) * gridPoint (N + 1) (k + 1) ^ 2
              + lowerWeight (N + 1) k m * gridPoint (N + 1) k ^ 2) / (N + 1) := by
      intro s
      rw [Fintype.sum_bool]
      show theta * (1 - lowerWeight (N + 1) k m) / (N + 1)
          * meanSign (N + 1) (shiftSigns N (k + 1) s) ^ 2
        + theta * lowerWeight (N + 1) k m / (N + 1)
          * meanSign (N + 1) (shiftSigns N k s) ^ 2 = _
      rw [meanSign_shiftSigns N (k + 1) hk s, meanSign_shiftSigns N k hkle s]
      field_simp
    rw [Finset.sum_congr rfl fun s _ ↦ hin s, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    push_cast
    field_simp
  have hright : ∑ c : Bool, envelopeWeight N k m theta (Sum.inr c)
      * meanSign (N + 1) (envelopeSigns N k (Sum.inr c)) ^ 2 = 1 - theta := by
    have hms : ∀ c : Bool, meanSign (N + 1) (envelopeSigns N k (Sum.inr c)) ^ 2 = 1 := by
      intro c
      have : meanSign (N + 1) (fun _ : Fin (N + 1) ↦ sgn c) = sgn c := by
        rw [meanSign, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        field_simp
      show meanSign (N + 1) (fun _ ↦ sgn c) ^ 2 = 1
      rw [this, sgn_sq]
    rw [Fintype.sum_bool, hms true, hms false]
    show (1 - theta) * ((1 + m * sgn true) / 2) * 1
      + (1 - theta) * ((1 + m * sgn false) / 2) * 1 = 1 - theta
    rw [sgn_true, sgn_false]
    ring
  rw [hleft, hright]
  have hmix := lowerWeight_mix (succ_pos' N) k m
  have hkey : lowerWeight (N + 1) k m * gridPoint (N + 1) k ^ 2
      + (1 - lowerWeight (N + 1) k m) * gridPoint (N + 1) (k + 1) ^ 2
      = m ^ 2 + (m - gridPoint (N + 1) k) * (gridPoint (N + 1) (k + 1) - m) := by
    linear_combination (gridPoint (N + 1) k + gridPoint (N + 1) (k + 1)) * hmix
  rw [hkey]

/-- **TQ Theorem 3.6, attainment.**  Every value of the envelope interval is attained by a
joint sign law with the prescribed one-locus mean at every locus, the two endpoints
included. -/
theorem envelope_value_attained (N k : ℕ) (hk : k + 1 ≤ N + 1) (m : ℝ) (hm : -1 ≤ m)
    (hm' : m ≤ 1) (hk1 : gridPoint (N + 1) k ≤ m) (hk2 : m ≤ gridPoint (N + 1) (k + 1))
    (H sigma : ℝ) (hH : 0 < H) (b : Fin (N + 1) → ℝ)
    (hb : ∀ i, b i ^ 2 = H / ((N + 1 : ℕ) : ℝ)) (y : ℝ)
    (hy1 : ceiling H sigma * (m ^ 2 + (m - gridPoint (N + 1) k)
        * (gridPoint (N + 1) (k + 1) - m)) ≤ y)
    (hy2 : y ≤ ceiling H sigma) :
    ∃ (theta : ℝ) (ht0 : 0 ≤ theta) (ht1 : theta ≤ 1),
      (∀ i, envelopeLaw N k m theta hm hm' hk1 hk2 ht0 ht1
          (fun x ↦ envelopeSigns N k x i) = m) ∧
      envelopeLaw N k m theta hm hm' hk1 hk2 ht0 ht1
        (fun x ↦ (turnoverWorld b sigma (envelopeSigns N k x)).r2 b) = y := by
  set Q := ceiling H sigma with hQdef
  set L := m ^ 2 + (m - gridPoint (N + 1) k) * (gridPoint (N + 1) (k + 1) - m) with hLdef
  by_cases hdeg : Q * L = Q
  · refine ⟨0, le_refl 0, by norm_num, ?_, ?_⟩
    · intro i
      exact envelopeLaw_marginal N k hk m 0 hm hm' hk1 hk2 (le_refl 0) (by norm_num) i
    · rw [envelopeLaw_expected_r2 N k hk m 0 hm hm' hk1 hk2 (le_refl 0) (by norm_num) H sigma
        hH b hb]
      rw [← hQdef, ← hLdef]
      rw [hdeg] at hy1
      linarith
  · have hlt : Q * L < Q := lt_of_le_of_ne (le_trans hy1 hy2) hdeg
    have hden : 0 < Q - Q * L := by linarith
    have hdenne : Q - Q * L ≠ 0 := ne_of_gt hden
    refine ⟨(Q - y) / (Q - Q * L), div_nonneg (by linarith) hden.le, ?_, ?_, ?_⟩
    · rw [div_le_one hden]
      linarith
    · intro i
      exact envelopeLaw_marginal N k hk m _ hm hm' hk1 hk2 _ _ i
    · rw [envelopeLaw_expected_r2 N k hk m _ hm hm' hk1 hk2 _ _ H sigma hH b hb,
        ← hQdef, ← hLdef]
      have hstep : (Q - y) / (Q - Q * L) * (Q - Q * L) = Q - y := by
        field_simp
      have hexpand : Q * ((Q - y) / (Q - Q * L) * L + (1 - (Q - y) / (Q - Q * L)))
          = Q - (Q - y) / (Q - Q * L) * (Q - Q * L) := by ring
      rw [hexpand, hstep]
      ring

end Attainment

section Bracketing

/-- A grid point lies below a value exactly when its count clears the scaled threshold. -/
theorem gridPoint_le_iff {n : ℕ} (hn : 0 < n) (c : ℕ) (m : ℝ) :
    gridPoint n c ≤ m ↔ 2 * (c : ℝ) ≤ (m + 1) * n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  rw [gridPoint]
  constructor
  · intro h
    have h1 : 2 * (c : ℝ) / n ≤ m + 1 := by linarith
    exact (div_le_iff₀ hnR).mp h1
  · intro h
    have h1 : 2 * (c : ℝ) / n ≤ m + 1 := (div_le_iff₀ hnR).mpr h
    linarith

/-- A value lies below a grid point exactly when the scaled threshold clears its count. -/
theorem le_gridPoint_iff {n : ℕ} (hn : 0 < n) (c : ℕ) (m : ℝ) :
    m ≤ gridPoint n c ↔ (m + 1) * n ≤ 2 * (c : ℝ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  rw [gridPoint]
  constructor
  · intro h
    have h1 : m + 1 ≤ 2 * (c : ℝ) / n := by linarith
    exact (le_div_iff₀ hnR).mp h1
  · intro h
    have h1 : m + 1 ≤ 2 * (c : ℝ) / n := (le_div_iff₀ hnR).mpr h
    linarith

/-- **Every admissible one-locus mean is bracketed by an adjacent pair of grid points**
with the upper index still inside the grid, so the envelope hypotheses are never vacuous. -/
theorem exists_grid_bracket {n : ℕ} (hn : 0 < n) (m : ℝ) (hm : -1 ≤ m) (hm' : m ≤ 1) :
    ∃ k : ℕ, k + 1 ≤ n ∧ gridPoint n k ≤ m ∧ m ≤ gridPoint n (k + 1) := by
  obtain ⟨j, rfl⟩ : ∃ j : ℕ, n = j + 1 := ⟨n - 1, by omega⟩
  have hnR : (0 : ℝ) < ((j + 1 : ℕ) : ℝ) := by exact_mod_cast hn
  have hj0 : (0 : ℝ) ≤ (j : ℕ) := Nat.cast_nonneg j
  set t : ℝ := (m + 1) * ((j + 1 : ℕ) : ℝ) / 2 with hT
  have ht0 : 0 ≤ t := by
    rw [hT]
    have h1 : 0 ≤ m + 1 := by linarith
    positivity
  have htn : t ≤ ((j + 1 : ℕ) : ℝ) := by
    rw [hT, div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
    nlinarith
  by_cases hcase : ⌊t⌋₊ + 1 ≤ j + 1
  · refine ⟨⌊t⌋₊, hcase, ?_, ?_⟩
    · rw [gridPoint_le_iff hn]
      have hfl : (⌊t⌋₊ : ℝ) ≤ t := Nat.floor_le ht0
      rw [hT, le_div_iff₀ (by norm_num : (0 : ℝ) < 2)] at hfl
      linarith
    · rw [le_gridPoint_iff hn]
      have hfl : t < (⌊t⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one t
      rw [hT, div_lt_iff₀ (by norm_num : (0 : ℝ) < 2)] at hfl
      push_cast
      linarith
  · have hge : j + 1 ≤ ⌊t⌋₊ := by omega
    have hfloorle : ⌊t⌋₊ ≤ j + 1 := by
      have h1 : ⌊t⌋₊ ≤ ⌊((j + 1 : ℕ) : ℝ)⌋₊ := Nat.floor_le_floor htn
      simpa using h1
    have heq : ⌊t⌋₊ = j + 1 := le_antisymm hfloorle hge
    refine ⟨j, le_refl _, ?_, ?_⟩
    · rw [gridPoint_le_iff hn]
      have hfl : ((j + 1 : ℕ) : ℝ) ≤ t := by
        have h1 := Nat.floor_le ht0
        rwa [heq] at h1
      rw [hT, le_div_iff₀ (by norm_num : (0 : ℝ) < 2)] at hfl
      push_cast at hfl ⊢
      linarith
    · rw [le_gridPoint_iff hn]
      push_cast
      nlinarith

end Bracketing

end

end Descent.Portability.SynchronyEnvelope
