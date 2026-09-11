/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.GlobalFourthMomentRegion

assert_below Descent.Decision Descent.Program

/-!
# Two exact fourth-moment minima: symmetric and sparse symmetric scores

UPT Corollaries 3.3 and 3.4, with closed-form values, explicit attaining laws, and
attained dual multipliers. Both are instances of
`GlobalFourthMomentRegion.waterfill_minFourthMoment`: the conditional second moment is the
forced lower bound `b²` raised to a common water level, and the induced dual form
`4(a − t) b` happens to be affine in the score.

* `symmetric_two_point_value` is Corollary 3.3 (3.18): for the fair sign `X = ±1`,
  `V(β, k, m) = m² + ((|β| + |k|)² − m)₊²` whenever `m ≥ β² + k²`.
* `sparse_symmetric_value` is Corollary 3.4 (3.19): for `P(X = ±p^{-1/2}) = p/2`,
  `P(X = 0) = 1 − p`, with `β = 0` and `m ≥ k²`,
  `V(0, k, m) = m² + (k² − p m)₊² / (p(1 − p))`.

Each also reports the dual value at explicit multipliers, so the supremum of UPT (3.8) is
attained in both cases and the closed forms are simultaneously primal and dual optima.
The two laws have the same score variance and different sharp minima, which is the point
the manuscript draws from them.

`waterfill_pair` is the shared arithmetic core: the two-point water-filling identity that
turns the constraint `E a = m` into the closed form. It is stated for real numbers and
used for both corollaries, in the two-point case directly and in the sparse case through
the pair `(k²/p, 0)` of forced lower bounds.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.SymmetricScoreFourthMoment

open Foundations IndividualLossMoments FourthMomentDuality GlobalFourthMomentRegion

attribute [local simp] Matrix.cons_val_two Matrix.head_cons Matrix.tail_cons

noncomputable section

/-! ## Two-point water filling as arithmetic -/

/-- Two-point water filling in the ordered case `v ≤ u`: raising both lower bounds to the
level `min m (2m − u)` gives average exactly `m` and mean square `m² + ((u − m)₊)²`. -/
theorem waterfill_pair_ordered (u v m : ℝ) (hle : v ≤ u) (h : u + v ≤ 2 * m) :
    max u (min m (2 * m - u)) + max v (min m (2 * m - u)) = 2 * m
      ∧ max u (min m (2 * m - u)) ^ 2 + max v (min m (2 * m - u)) ^ 2
        = 2 * m ^ 2 + 2 * max (u - m) 0 ^ 2 := by
  rcases le_total u m with hum | hum
  · have ht : min m (2 * m - u) = m := min_eq_left (by linarith)
    have h1 : max u (min m (2 * m - u)) = m := by
      rw [ht]
      exact max_eq_right hum
    have h2 : max v (min m (2 * m - u)) = m := by
      rw [ht]
      exact max_eq_right (by linarith)
    have h3 : max (u - m) 0 = 0 := max_eq_right (by linarith)
    rw [h1, h2, h3]
    constructor <;> ring
  · have ht : min m (2 * m - u) = 2 * m - u := min_eq_right (by linarith)
    have h1 : max u (min m (2 * m - u)) = u := by
      rw [ht]
      exact max_eq_left (by linarith)
    have h2 : max v (min m (2 * m - u)) = 2 * m - u := by
      rw [ht]
      exact max_eq_right (by linarith)
    have h3 : max (u - m) 0 = u - m := max_eq_left (by linarith)
    rw [h1, h2, h3]
    constructor <;> ring

/-- Two-point water filling at the level `min m (2m − max u v)`: the average of the raised
bounds is `m` and their mean square is `m² + ((max u v − m)₊)²`. -/
theorem waterfill_pair (u v m : ℝ) (h : u + v ≤ 2 * m) :
    max u (min m (2 * m - max u v)) + max v (min m (2 * m - max u v)) = 2 * m
      ∧ max u (min m (2 * m - max u v)) ^ 2 + max v (min m (2 * m - max u v)) ^ 2
        = 2 * m ^ 2 + 2 * max (max u v - m) 0 ^ 2 := by
  rcases le_total v u with hle | hle
  · rw [max_eq_left hle]
    exact waterfill_pair_ordered u v m hle h
  · rw [max_eq_right hle]
    obtain ⟨h1, h2⟩ := waterfill_pair_ordered v u m hle (by linarith)
    exact ⟨by linarith, by linarith⟩

/-- The larger of the two forced squared means of a fair-sign score is `(|β| + |k|)²`. -/
theorem max_sq_add_sub (β κ : ℝ) :
    max ((β + κ) ^ 2) ((β - κ) ^ 2) = (|β| + |κ|) ^ 2 := by
  have hexp : (|β| + |κ|) ^ 2 = |β| ^ 2 + 2 * (|β| * |κ|) + |κ| ^ 2 := by ring
  rcases le_total ((β - κ) ^ 2) ((β + κ) ^ 2) with h | h
  · rw [max_eq_left h]
    have hnn : (0 : ℝ) ≤ β * κ := by nlinarith
    have hprod : |β| * |κ| = β * κ := by
      rw [← abs_mul, abs_of_nonneg hnn]
    rw [hexp, sq_abs, sq_abs, hprod]
    ring
  · rw [max_eq_right h]
    have hnp : β * κ ≤ 0 := by nlinarith
    have hprod : |β| * |κ| = -(β * κ) := by
      rw [← abs_mul, abs_of_nonpos hnp]
    rw [hexp, sq_abs, sq_abs, hprod]
    ring

/-! ## UPT Corollary 3.3: the symmetric two-point score -/

/-- The fair-sign score of UPT Corollary 3.3, as a one-coordinate feature vector. -/
def signScore : Bool → Fin 1 → ℝ :=
  fun ω _ ↦ if ω then 1 else -1

/-- Expectation against the fair sign is the average of the two values. -/
theorem uniformExp_bool (f : Bool → ℝ) : uniformExp Bool f = (f true + f false) / 2 := by
  rw [uniformExp_apply, Fintype.sum_bool, Fintype.card_bool]
  push_cast
  ring

/-- The fair sign is centered and standardized: UPT (3.1) for `p = 1`. -/
theorem signScore_orthonormal :
    (∀ i, uniformExp Bool (fun ω ↦ signScore ω i) = 0) ∧
      (∀ i j, uniformExp Bool (fun ω ↦ signScore ω i * signScore ω j)
        = if i = j then 1 else 0) := by
  constructor
  · intro i
    rw [uniformExp_bool]
    simp [signScore]
  · intro i j
    have hij : i = j := Subsingleton.elim i j
    rw [uniformExp_bool, if_pos hij]
    simp [signScore]

/-- Any function of the fair sign is an affine form in it; this is its intercept. -/
def boolIntercept (w : Bool → ℝ) : ℝ := (w true + w false) / 2

/-- Any function of the fair sign is an affine form in it; this is its slope. -/
def boolSlope (w : Bool → ℝ) : Fin 1 → ℝ := fun _ ↦ (w true - w false) / 2

/-- The intercept and slope reconstruct the function: a two-point score makes every dual
form affine, so the water-filling certificate always applies. -/
theorem bool_affine (w : Bool → ℝ) (ω : Bool) :
    boolIntercept w + dot (boolSlope w) (signScore ω) = w ω := by
  have hdot : dot (boolSlope w) (signScore ω) = boolSlope w 0 * signScore ω 0 := by
    simp [dot, Descent.Core.innerSum]
  rw [hdot]
  cases ω with
  | false =>
      show boolIntercept w + (w true - w false) / 2 * (-1 : ℝ) = w false
      unfold boolIntercept
      ring
  | true =>
      show boolIntercept w + (w true - w false) / 2 * (1 : ℝ) = w true
      unfold boolIntercept
      ring

/-- The water level of UPT Corollary 3.3: the common second moment the two cells are
raised to, `min m (2m − (|β| + |k|)²)`. -/
def symmetricLevel (β κ m : ℝ) : ℝ := min m (2 * m - (|β| + |κ|) ^ 2)

/-- The forced conditional mean of a fair-sign score, `β + k X`. -/
def symmetricMean (β κ : ℝ) : Bool → ℝ :=
  featureMean β (fun _ ↦ κ) signScore

/-- The two cells of the fair-sign score carry conditional means `β + k` and `β − k`. -/
theorem symmetricMean_values (β κ : ℝ) :
    symmetricMean β κ true = β + κ ∧ symmetricMean β κ false = β - κ := by
  have hdot : ∀ ω : Bool, dot (fun _ : Fin 1 ↦ κ) (signScore ω) = κ * signScore ω 0 := by
    intro ω
    simp [dot, Descent.Core.innerSum]
  constructor
  · show β + dot (fun _ : Fin 1 ↦ κ) (signScore true) = β + κ
    rw [hdot]
    simp [signScore]
  · show β + dot (fun _ : Fin 1 ↦ κ) (signScore false) = β - κ
    rw [hdot]
    simp [signScore]
    ring

/-- **UPT Corollary 3.3 (symmetric two-point score).** With `X = ±1` equiprobable and
`m ≥ β² + k²`, the least residual fourth moment is exactly
`m² + ((|β| + |k|)² − m)₊²`; it is attained by the water-filling pair, and the supremum of
the dual (3.8) is attained at the explicit multipliers built from that pair. -/
theorem symmetric_two_point_value (β κ m : ℝ) (hfeas : β ^ 2 + κ ^ 2 ≤ m) :
    minFourthMoment (uniformExp Bool) signScore β (fun _ ↦ κ) m
        = m ^ 2 + max ((|β| + |κ|) ^ 2 - m) 0 ^ 2 ∧
      minFourthMoment (uniformExp Bool) signScore β (fun _ ↦ κ) m
        = dualObjective (uniformExp Bool) signScore β (fun _ ↦ κ) m
            (boolIntercept (waterfillForm (symmetricMean β κ) (symmetricLevel β κ m)))
            (boolSlope (waterfillForm (symmetricMean β κ) (symmetricLevel β κ m)))
            (2 * symmetricLevel β κ m) := by
  obtain ⟨hplus, hminus⟩ := symmetricMean_values β κ
  obtain ⟨hmean, horth⟩ := signScore_orthonormal
  obtain ⟨hbmean, hbcross, _⟩ :=
    featureMean_moments (uniformExp Bool) signScore β (fun _ : Fin 1 ↦ κ) hmean horth
  have hmax : max (symmetricMean β κ true ^ 2) (symmetricMean β κ false ^ 2)
      = (|β| + |κ|) ^ 2 := by
    rw [hplus, hminus]
    exact max_sq_add_sub β κ
  have hlevel : symmetricLevel β κ m
      = min m (2 * m - max (symmetricMean β κ true ^ 2) (symmetricMean β κ false ^ 2)) := by
    rw [hmax]
    rfl
  have hsum : symmetricMean β κ true ^ 2 + symmetricMean β κ false ^ 2 ≤ 2 * m := by
    rw [hplus, hminus]
    nlinarith
  obtain ⟨hone, htwo⟩ := waterfill_pair (symmetricMean β κ true ^ 2)
    (symmetricMean β κ false ^ 2) m hsum
  have ha : uniformExp Bool (waterfillSecond (symmetricMean β κ) (symmetricLevel β κ m))
      = m := by
    rw [uniformExp_bool]
    show (max (symmetricMean β κ true ^ 2) (symmetricLevel β κ m)
      + max (symmetricMean β κ false ^ 2) (symmetricLevel β κ m)) / 2 = m
    rw [hlevel, hone]
    ring
  have hval : uniformExp Bool
      (fun ω ↦ waterfillSecond (symmetricMean β κ) (symmetricLevel β κ m) ω ^ 2)
      = m ^ 2 + max ((|β| + |κ|) ^ 2 - m) 0 ^ 2 := by
    rw [uniformExp_bool]
    show (max (symmetricMean β κ true ^ 2) (symmetricLevel β κ m) ^ 2
      + max (symmetricMean β κ false ^ 2) (symmetricLevel β κ m) ^ 2) / 2 = _
    rw [hlevel, htwo, hmax]
    ring
  obtain ⟨hprimal, hdual⟩ := waterfill_minFourthMoment (uniformExp Bool) signScore
    (symmetricMean β κ) (symmetricLevel β κ m) β (fun _ ↦ κ) m
    (boolIntercept (waterfillForm (symmetricMean β κ) (symmetricLevel β κ m)))
    (boolSlope (waterfillForm (symmetricMean β κ) (symmetricLevel β κ m)))
    (fun ω ↦ bool_affine _ ω) hbmean hbcross ha
  exact ⟨by rw [hprimal, hval], hdual⟩

/-! ## UPT Corollary 3.4: the sparse symmetric score -/

/-- The sparse score law of UPT Corollary 3.4: mass `p/2` on each of `±p^{-1/2}` and
`1 − p` on `0`. -/
def sparseWeights (p : ℝ) : Fin 3 → ℝ := ![p / 2, p / 2, 1 - p]

/-- The sparse symmetric score values `±p^{-1/2}` and `0`, as a one-coordinate feature. -/
def sparseScore (p : ℝ) : Fin 3 → Fin 1 → ℝ :=
  fun i _ ↦ ![1 / Real.sqrt p, -(1 / Real.sqrt p), 0] i

/-- The sparse score law of UPT Corollary 3.4. -/
def sparseLaw (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) : ExpFunctional (Fin 3) :=
  weightedExp (sparseWeights p)
    (by
      intro i
      fin_cases i <;> simp [sparseWeights] <;> linarith)
    (by
      show ∑ i : Fin 3, sparseWeights p i = 1
      rw [Fin.sum_univ_three]
      simp [sparseWeights])

/-- Expectation against the sparse score law. -/
theorem sparseLaw_apply (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (f : Fin 3 → ℝ) :
    sparseLaw p hp0 hp1 f = p / 2 * f 0 + p / 2 * f 1 + (1 - p) * f 2 := by
  show ∑ i : Fin 3, sparseWeights p i * f i = _
  rw [Fin.sum_univ_three]
  simp [sparseWeights]

/-- The sparse score is centered and standardized: UPT (3.1) for this law. -/
theorem sparseScore_orthonormal (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    (∀ i, sparseLaw p hp0 hp1 (fun ω ↦ sparseScore p ω i) = 0) ∧
      (∀ i j, sparseLaw p hp0 hp1 (fun ω ↦ sparseScore p ω i * sparseScore p ω j)
        = if i = j then 1 else 0) := by
  have hs : Real.sqrt p ^ 2 = p := Real.sq_sqrt hp0.le
  have hspos : 0 < Real.sqrt p := Real.sqrt_pos.mpr hp0
  have hne : Real.sqrt p ≠ 0 := ne_of_gt hspos
  constructor
  · intro i
    rw [sparseLaw_apply]
    simp [sparseScore]
  · intro i j
    have hij : i = j := Subsingleton.elim i j
    rw [sparseLaw_apply, if_pos hij]
    simp only [sparseScore, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons]
    field_simp
    nlinarith [hs]

/-- The water level of UPT Corollary 3.4, `min m ((m − k²)/(1 − p))`. -/
def sparseLevel (κ m p : ℝ) : ℝ := min m ((m - κ ^ 2) / (1 - p))

/-- The forced conditional mean of the sparse symmetric score, `k X`. -/
def sparseMean (κ p : ℝ) : Fin 3 → ℝ :=
  featureMean 0 (fun _ ↦ κ) (sparseScore p)

/-- The three cells of the sparse score carry conditional means `±k p^{-1/2}` and `0`. -/
theorem sparseMean_values (κ p : ℝ) :
    sparseMean κ p 0 = κ * (1 / Real.sqrt p) ∧
      sparseMean κ p 1 = -(κ * (1 / Real.sqrt p)) ∧ sparseMean κ p 2 = 0 := by
  have hdot : ∀ i : Fin 3,
      dot (fun _ : Fin 1 ↦ κ) (sparseScore p i) = κ * sparseScore p i 0 := by
    intro i
    simp [dot, Descent.Core.innerSum]
  refine ⟨?_, ?_, ?_⟩
  · show (0 : ℝ) + dot (fun _ : Fin 1 ↦ κ) (sparseScore p 0) = _
    rw [hdot]
    simp [sparseScore]
  · show (0 : ℝ) + dot (fun _ : Fin 1 ↦ κ) (sparseScore p 1) = _
    rw [hdot]
    simp [sparseScore]
  · show (0 : ℝ) + dot (fun _ : Fin 1 ↦ κ) (sparseScore p 2) = _
    rw [hdot]
    simp [sparseScore]

/-- **UPT Corollary 3.4 (sparse symmetric score).** With `P(X = ±p^{-1/2}) = p/2`,
`P(X = 0) = 1 − p`, `β = 0` and `m ≥ k²`, the least residual fourth moment is exactly
`m² + (k² − p m)₊² / (p(1 − p))`, attained by the water-filling pair, with the dual
supremum of (3.8) attained at the explicit multipliers. -/
theorem sparse_symmetric_value (κ m p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (hfeas : κ ^ 2 ≤ m) :
    minFourthMoment (sparseLaw p hp0 hp1) (sparseScore p) 0 (fun _ ↦ κ) m
        = m ^ 2 + max (κ ^ 2 - p * m) 0 ^ 2 / (p * (1 - p)) ∧
      minFourthMoment (sparseLaw p hp0 hp1) (sparseScore p) 0 (fun _ ↦ κ) m
        = dualObjective (sparseLaw p hp0 hp1) (sparseScore p) 0 (fun _ ↦ κ) m 0
            (fun _ ↦ 4 * (max (κ ^ 2 / p) (sparseLevel κ m p) - sparseLevel κ m p) * κ)
            (2 * sparseLevel κ m p) := by
  have hs : Real.sqrt p ^ 2 = p := Real.sq_sqrt hp0.le
  have hspos : 0 < Real.sqrt p := Real.sqrt_pos.mpr hp0
  have hne : Real.sqrt p ≠ 0 := ne_of_gt hspos
  have hpne : p ≠ 0 := ne_of_gt hp0
  have hqpos : (0 : ℝ) < 1 - p := by linarith
  have hqne : (1 : ℝ) - p ≠ 0 := ne_of_gt hqpos
  obtain ⟨hz, ho, hzero⟩ := sparseMean_values κ p
  obtain ⟨hmean, horth⟩ := sparseScore_orthonormal p hp0 hp1
  obtain ⟨hbmean, hbcross, _⟩ :=
    featureMean_moments (sparseLaw p hp0 hp1) (sparseScore p) 0 (fun _ : Fin 1 ↦ κ)
      hmean horth
  have hsq : sparseMean κ p 0 ^ 2 = κ ^ 2 / p ∧ sparseMean κ p 1 ^ 2 = κ ^ 2 / p := by
    constructor
    · rw [hz]
      field_simp
      nlinarith [hs]
    · rw [ho]
      field_simp
      nlinarith [hs]
  have hmnn : 0 ≤ m := le_trans (sq_nonneg κ) hfeas
  have hlevel_nonneg : 0 ≤ sparseLevel κ m p := by
    refine le_min hmnn ?_
    apply div_nonneg (by linarith) (by linarith)
  -- the two regimes of the water level
  have hcases : (κ ^ 2 ≤ p * m ∧ sparseLevel κ m p = m) ∨
      (p * m ≤ κ ^ 2 ∧ sparseLevel κ m p = (m - κ ^ 2) / (1 - p)) := by
    rcases le_total (κ ^ 2) (p * m) with h | h
    · left
      refine ⟨h, min_eq_left ?_⟩
      rw [le_div_iff₀ (by linarith)]
      nlinarith
    · right
      refine ⟨h, min_eq_right ?_⟩
      rw [div_le_iff₀ (by linarith)]
      nlinarith
  have hlow : max (κ ^ 2 / p) (sparseLevel κ m p) * p
      + max (0 : ℝ) (sparseLevel κ m p) * (1 - p) = m ∧
      max (κ ^ 2 / p) (sparseLevel κ m p) ^ 2 * p
        + max (0 : ℝ) (sparseLevel κ m p) ^ 2 * (1 - p)
        = m ^ 2 + max (κ ^ 2 - p * m) 0 ^ 2 / (p * (1 - p)) := by
    rcases hcases with ⟨hk, ht⟩ | ⟨hk, ht⟩
    · have h1 : max (κ ^ 2 / p) (sparseLevel κ m p) = m := by
        rw [ht]
        refine max_eq_right ?_
        rw [div_le_iff₀ hp0]
        nlinarith
      have h2 : max (0 : ℝ) (sparseLevel κ m p) = m := by
        rw [ht]
        exact max_eq_right hmnn
      have h3 : max (κ ^ 2 - p * m) 0 = 0 := max_eq_right (by linarith)
      rw [h1, h2, h3]
      refine ⟨by ring, ?_⟩
      rw [show (0 : ℝ) ^ 2 / (p * (1 - p)) = 0 from by norm_num]
      ring
    · have h1 : max (κ ^ 2 / p) (sparseLevel κ m p) = κ ^ 2 / p := by
        rw [ht]
        refine max_eq_left ?_
        rw [div_le_div_iff₀ (by linarith) hp0]
        nlinarith
      have h2 : max (0 : ℝ) (sparseLevel κ m p) = (m - κ ^ 2) / (1 - p) := by
        rw [ht]
        refine max_eq_right ?_
        apply div_nonneg (by linarith) (by linarith)
      have h3 : max (κ ^ 2 - p * m) 0 = κ ^ 2 - p * m := max_eq_left (by linarith)
      have e1 : κ ^ 2 / p * p = κ ^ 2 := by field_simp
      have e2 : (m - κ ^ 2) / (1 - p) * (1 - p) = m - κ ^ 2 := by field_simp
      rw [h1, h2, h3]
      refine ⟨by rw [e1, e2]; ring, ?_⟩
      field_simp
      ring
  have ha : sparseLaw p hp0 hp1 (waterfillSecond (sparseMean κ p) (sparseLevel κ m p))
      = m := by
    rw [sparseLaw_apply]
    show p / 2 * max (sparseMean κ p 0 ^ 2) (sparseLevel κ m p)
      + p / 2 * max (sparseMean κ p 1 ^ 2) (sparseLevel κ m p)
      + (1 - p) * max (sparseMean κ p 2 ^ 2) (sparseLevel κ m p) = m
    rw [hsq.1, hsq.2, hzero, show (0 : ℝ) ^ 2 = 0 from by norm_num]
    linear_combination hlow.1
  have hval : sparseLaw p hp0 hp1
      (fun ω ↦ waterfillSecond (sparseMean κ p) (sparseLevel κ m p) ω ^ 2)
      = m ^ 2 + max (κ ^ 2 - p * m) 0 ^ 2 / (p * (1 - p)) := by
    rw [sparseLaw_apply]
    show p / 2 * max (sparseMean κ p 0 ^ 2) (sparseLevel κ m p) ^ 2
      + p / 2 * max (sparseMean κ p 1 ^ 2) (sparseLevel κ m p) ^ 2
      + (1 - p) * max (sparseMean κ p 2 ^ 2) (sparseLevel κ m p) ^ 2 = _
    rw [hsq.1, hsq.2, hzero, show (0 : ℝ) ^ 2 = 0 from by norm_num]
    linear_combination hlow.2
  have hbi : ∀ i : Fin 3, sparseMean κ p i = κ * sparseScore p i 0 := by
    intro i
    show (0 : ℝ) + dot (fun _ : Fin 1 ↦ κ) (sparseScore p i) = κ * sparseScore p i 0
    simp [dot, Descent.Core.innerSum]
  have hx : ∀ i : Fin 3, sparseScore p i 0 = 0 ∨ sparseScore p i 0 ^ 2 = 1 / p := by
    intro i
    fin_cases i <;> simp [sparseScore, hs]
  have haff : ∀ i : Fin 3,
      (0 : ℝ) + dot (fun _ : Fin 1 ↦
          4 * (max (κ ^ 2 / p) (sparseLevel κ m p) - sparseLevel κ m p) * κ)
          (sparseScore p i)
        = waterfillForm (sparseMean κ p) (sparseLevel κ m p) i := by
    intro i
    have hdot : dot (fun _ : Fin 1 ↦
        4 * (max (κ ^ 2 / p) (sparseLevel κ m p) - sparseLevel κ m p) * κ)
        (sparseScore p i)
        = 4 * (max (κ ^ 2 / p) (sparseLevel κ m p) - sparseLevel κ m p) * κ
          * sparseScore p i 0 := by
      simp [dot, Descent.Core.innerSum]
    show (0 : ℝ) + dot (fun _ : Fin 1 ↦
        4 * (max (κ ^ 2 / p) (sparseLevel κ m p) - sparseLevel κ m p) * κ)
        (sparseScore p i)
      = 4 * (max (sparseMean κ p i ^ 2) (sparseLevel κ m p) - sparseLevel κ m p)
        * sparseMean κ p i
    rw [hdot, hbi i]
    rcases hx i with h0 | h1
    · rw [h0]
      ring
    · have hsq2 : (κ * sparseScore p i 0) ^ 2 = κ ^ 2 / p := by
        rw [mul_pow, h1]
        ring
      rw [hsq2]
      ring
  obtain ⟨hprimal, hdual⟩ := waterfill_minFourthMoment (sparseLaw p hp0 hp1)
    (sparseScore p) (sparseMean κ p) (sparseLevel κ m p) 0 (fun _ ↦ κ) m 0
    (fun _ ↦ 4 * (max (κ ^ 2 / p) (sparseLevel κ m p) - sparseLevel κ m p) * κ)
    haff hbmean hbcross ha
  exact ⟨by rw [hprimal, hval], hdual⟩

end

end Descent.Portability.SymmetricScoreFourthMoment
