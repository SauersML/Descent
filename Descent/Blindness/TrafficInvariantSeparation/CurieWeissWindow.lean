/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Blindness.TrafficInvariantSeparation.RankOneInvisibility

namespace Descent.Blindness
namespace TrafficInvariantSeparation

open scoped Matrix Topology

/-!
# `TrafficInvariantSeparation.CurieWeissWindow`

Part of the split of `Descent/Blindness/TrafficInvariantSeparation.lean`, which was 6,618 lines.

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


section CurieWeissWindow

/-- The Curie-Weiss rate function for a balanced Rademacher magnetisation.

    Empirical status: NOT AN EMPIRICAL CLAIM. This is the Cramer rate function of
    a fair coin, fixed by that description alone; no measurement bears on it. -/
noncomputable def cwRate (m : ℝ) : ℝ :=
  (1 + m) / 2 * Real.log (1 + m) + (1 - m) / 2 * Real.log (1 - m)

/-- The endpoint rate is `log 2`; the vanishing factor multiplies `log 0` and contributes zero. -/
@[simp] theorem cwRate_one : cwRate 1 = Real.log 2 := by
  unfold cwRate
  norm_num

/-- The negative endpoint has the same Bernoulli rate as the positive
endpoint. -/
@[simp] theorem cwRate_neg_one : cwRate (-1) = Real.log 2 := by
  unfold cwRate
  norm_num

/-- The quantity whose supremum over `m` is the overlap-pressure gap.

    Empirical status: NOT AN EMPIRICAL CLAIM. -/
noncomputable def cwObjective (tlam m : ℝ) : ℝ :=
  tlam / 2 * m ^ 2 - cwRate m

/-- Pinsker gap for the balanced Bernoulli pair. -/
noncomputable def cwPinskerGap (m : ℝ) : ℝ :=
  cwRate m - m ^ 2 / 2

/-- Reference evaluation; see `Descent.Core.Ratios` for what these pin and why. -/
theorem cwPinskerGap_at_reference_point :
    cwPinskerGap 1 = Real.log 2 - 1 / 2 := by
  unfold cwPinskerGap
  rw [cwRate_one]
  norm_num


/-- Derivative of the Pinsker gap on the open magnetisation interval. -/
noncomputable def cwPinskerGapDerivative (m : ℝ) : ℝ :=
  (Real.log (1 + m) - Real.log (1 - m)) / 2 - m

/-- Reference evaluation; see `Descent.Core.Ratios` for what these pin and why. -/
theorem cwPinskerGapDerivative_at_reference_point :
    cwPinskerGapDerivative (1 / 2) = Real.log 3 / 2 - 1 / 2 := by
  have h : Real.log (1 + 1 / 2) - Real.log (1 - 1 / 2) = Real.log 3 := by
    rw [show (1 : ℝ) + 1 / 2 = 3 / 2 by norm_num,
      show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num,
      Real.log_div (by norm_num) (by norm_num),
      Real.log_div (by norm_num) (by norm_num), Real.log_one]
    ring
  unfold cwPinskerGapDerivative
  rw [h]


/-- Exact derivative of the Bernoulli Pinsker gap away from the two endpoints. -/
theorem hasDerivAt_cwPinskerGap {m : ℝ} (hm : |m| < 1) :
    HasDerivAt cwPinskerGap (cwPinskerGapDerivative m) m := by
  have hplus : 1 + m ≠ 0 := by
    rw [abs_lt] at hm
    linarith
  have hminus : 1 - m ≠ 0 := by
    rw [abs_lt] at hm
    linarith
  have hplusBase : HasDerivAt (fun x : ℝ ↦ 1 + x) 1 m := by
    simpa using (hasDerivAt_const m 1).add (hasDerivAt_id m)
  have hminusBase : HasDerivAt (fun x : ℝ ↦ 1 - x) (-1) m := by
    simpa using (hasDerivAt_const m 1).sub (hasDerivAt_id m)
  have hplusTerm : HasDerivAt
      (fun x : ℝ ↦ (1 + x) / 2 * Real.log (1 + x))
      (Real.log (1 + m) / 2 + 1 / 2) m := by
    convert (hplusBase.div_const 2).mul (hplusBase.log hplus) using 1
    all_goals field_simp
  have hminusTerm : HasDerivAt
      (fun x : ℝ ↦ (1 - x) / 2 * Real.log (1 - x))
      (-Real.log (1 - m) / 2 - 1 / 2) m := by
    convert (hminusBase.div_const 2).mul (hminusBase.log hminus) using 1
    all_goals field_simp
    all_goals ring
  have hrate : HasDerivAt cwRate
      ((Real.log (1 + m) - Real.log (1 - m)) / 2) m := by
    unfold cwRate
    convert hplusTerm.add hminusTerm using 1
    all_goals ring
  have hquadratic : HasDerivAt (fun x : ℝ ↦ x ^ 2 / 2) m m := by
    convert ((hasDerivAt_id m).pow 2).div_const 2 using 1
    all_goals norm_num
  unfold cwPinskerGap cwPinskerGapDerivative
  convert hrate.sub hquadratic using 1

/-- On the nonnegative half interval, the Pinsker-gap derivative is nonnegative.  The analytic
input is Mathlib's elementary bound `2x/(x+2) ≤ log(1+x)`. -/
theorem cwPinskerGapDerivative_nonneg {m : ℝ} (hm0 : 0 ≤ m) (hm1 : m < 1) :
    0 ≤ cwPinskerGapDerivative m := by
  have hden : 1 - m ≠ 0 := by linarith
  have hx : 0 ≤ 2 * m / (1 - m) := div_nonneg (by positivity) (by linarith)
  have hlog := Real.le_log_one_add_of_nonneg hx
  have harg : 1 + 2 * m / (1 - m) = (1 + m) / (1 - m) := by
    field_simp
    ring
  have hlhs : 2 * (2 * m / (1 - m)) / (2 * m / (1 - m) + 2) = 2 * m := by
    field_simp
    ring
  rw [harg, hlhs, Real.log_div (by linarith : 1 + m ≠ 0) hden] at hlog
  unfold cwPinskerGapDerivative
  linarith

/-- The Bernoulli Pinsker gap is even. -/
theorem cwPinskerGap_neg (m : ℝ) : cwPinskerGap (-m) = cwPinskerGap m := by
  unfold cwPinskerGap cwRate
  simp only [sub_neg_eq_add, neg_sq]
  ring_nf

/-- Pinsker's inequality on the nonnegative open half interval. -/
theorem cwPinskerGap_nonneg_of_nonneg_of_lt_one
    {m : ℝ} (hm0 : 0 ≤ m) (hm1 : m < 1) : 0 ≤ cwPinskerGap m := by
  have hcontinuous : ContinuousOn cwPinskerGap (Set.Ico (0 : ℝ) 1) := by
    intro x hx
    have habs : |x| < 1 := (abs_lt).2 ⟨by linarith [hx.1], hx.2⟩
    exact (hasDerivAt_cwPinskerGap habs).continuousAt.continuousWithinAt
  have hdifferentiable : DifferentiableOn ℝ cwPinskerGap (interior (Set.Ico (0 : ℝ) 1)) := by
    intro x hx
    rw [interior_Ico] at hx
    have habs : |x| < 1 := (abs_lt).2 ⟨by linarith [hx.1], hx.2⟩
    exact (hasDerivAt_cwPinskerGap habs).differentiableAt.differentiableWithinAt
  have hmonotone : MonotoneOn cwPinskerGap (Set.Ico (0 : ℝ) 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ico (0 : ℝ) 1) hcontinuous hdifferentiable
    intro x hx
    rw [interior_Ico] at hx
    have habs : |x| < 1 := (abs_lt).2 ⟨by linarith [hx.1], hx.2⟩
    rw [(hasDerivAt_cwPinskerGap habs).deriv]
    exact cwPinskerGapDerivative_nonneg hx.1.le hx.2
  have hzero : cwPinskerGap 0 = 0 := by simp [cwPinskerGap, cwRate]
  rw [← hzero]
  exact hmonotone (by norm_num) ⟨hm0, hm1⟩ hm0

/-- The endpoint Pinsker gap is positive. -/
theorem cwPinskerGap_one_pos : 0 < cwPinskerGap 1 := by
  rw [cwPinskerGap, cwRate_one]
  have hlog : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  norm_num at hlog ⊢
  linarith

/-- **Bernoulli Pinsker inequality in the magnetisation coordinate.** -/
theorem cw_rate_lower_bound (m : ℝ) (hm : |m| ≤ 1) :
    m ^ 2 / 2 ≤ cwRate m := by
  have hgap : 0 ≤ cwPinskerGap m := by
    by_cases hinterior : |m| < 1
    · by_cases hm0 : 0 ≤ m
      · exact cwPinskerGap_nonneg_of_nonneg_of_lt_one hm0 ((abs_lt.mp hinterior).2)
      · rw [← cwPinskerGap_neg m]
        apply cwPinskerGap_nonneg_of_nonneg_of_lt_one
        · linarith
        · linarith [(abs_lt.mp hinterior).1]
    · have habs : |m| = 1 := le_antisymm hm (not_lt.mp hinterior)
      have hsq : m * m = 1 * 1 := by
        rw [← abs_eq_iff_mul_self_eq]
        simpa using habs
      rcases mul_self_eq_mul_self_iff.mp hsq with hm1 | hm1
      · rw [hm1]
        exact cwPinskerGap_one_pos.le
      · rw [hm1, cwPinskerGap_neg]
        exact cwPinskerGap_one_pos.le
  unfold cwPinskerGap at hgap
  linarith

/-- Elementary upper bound on the Rademacher rate near the origin.  Unlike a Taylor expansion,
it is global on the nonnegative open interval and follows only from `log x ≤ x - 1`. -/
theorem cw_rate_upper_bound {m : ℝ} (hm0 : 0 ≤ m) (hm1 : m < 1) :
    cwRate m ≤ m ^ 2 * (1 + m) / (2 * (1 - m)) := by
  have hplus : 0 < 1 + m := by linarith
  have hminus : 0 < 1 - m := by linarith
  have hsq : 0 < 1 - m ^ 2 := by nlinarith
  have hproduct : 1 - m ^ 2 = (1 + m) * (1 - m) := by ring
  have hlogProduct :
      Real.log (1 - m ^ 2) = Real.log (1 + m) + Real.log (1 - m) := by
    rw [hproduct, Real.log_mul (ne_of_gt hplus) (ne_of_gt hminus)]
  have hlogRatio :
      Real.log ((1 + m) / (1 - m)) = Real.log (1 + m) - Real.log (1 - m) := by
    rw [Real.log_div (ne_of_gt hplus) (ne_of_gt hminus)]
  have hproductBound : Real.log (1 - m ^ 2) ≤ -(m ^ 2) := by
    have := Real.log_le_sub_one_of_pos hsq
    linarith
  have hratioBound : Real.log ((1 + m) / (1 - m)) ≤ 2 * m / (1 - m) := by
    have hratioPos : 0 < (1 + m) / (1 - m) := div_pos hplus hminus
    have := Real.log_le_sub_one_of_pos hratioPos
    have hratio : (1 + m) / (1 - m) - 1 = 2 * m / (1 - m) := by
      field_simp
      ring
    rwa [hratio] at this
  have hproductScaled :
      Real.log (1 - m ^ 2) / 2 ≤ -(m ^ 2) / 2 := by linarith
  have hratioScaled :
      m / 2 * Real.log ((1 + m) / (1 - m)) ≤
        m / 2 * (2 * m / (1 - m)) :=
    mul_le_mul_of_nonneg_left hratioBound (by positivity)
  calc
    cwRate m = Real.log (1 - m ^ 2) / 2 +
        m / 2 * Real.log ((1 + m) / (1 - m)) := by
      unfold cwRate
      rw [hlogProduct, hlogRatio]
      ring
    _ ≤ -(m ^ 2) / 2 + m / 2 * (2 * m / (1 - m)) := by linarith
    _ = m ^ 2 * (1 + m) / (2 * (1 - m)) := by
      field_simp
      ring

/-- **Below the critical point the pressure gap vanishes identically.**

    At `tlam ≤ 1` the objective is non-positive at every admissible `m`, so its
    supremum is `0` and the two designs have EQUAL pressure -- not equal to
    leading order, equal. The critical point is therefore exactly `t = λ⁻¹`.

    The analytic input is `cw_rate_lower_bound`, Pinsker's inequality for a Bernoulli pair
    against the fair coin, proved above from Mathlib's logarithm bound and the mean-value theorem.

    Empirical status: NOT AN EMPIRICAL CLAIM. -/
theorem curieWeiss_subcritical
    (tlam : ℝ) (htl1 : tlam ≤ 1) (m : ℝ) (hm : |m| ≤ 1) :
    cwObjective tlam m ≤ 0 := by
  have hsq : (0 : ℝ) ≤ m ^ 2 := sq_nonneg m
  have h1 : tlam / 2 * m ^ 2 ≤ m ^ 2 / 2 := by nlinarith
  have h2 : m ^ 2 / 2 ≤ cwRate m := cw_rate_lower_bound m hm
  unfold cwObjective
  linarith

/-- **At zero magnetisation the objective is zero**, so the supremum below the
    critical point is attained and equals `0` rather than merely being bounded
    by it. Without this the previous theorem would leave open that the gap is
    negative, which a pressure difference of this form cannot be. -/
@[simp] theorem cwObjective_at_zero (tlam : ℝ) : cwObjective tlam 0 = 0 := by
  unfold cwObjective cwRate
  norm_num

/-- **The rate function vanishes at zero**, the normalisation the previous two
    results rely on. -/
@[simp] theorem cwRate_zero : cwRate 0 = 0 := by
  unfold cwRate; norm_num

/-- At full magnetisation the variational pressure objective is `tλ/2 - log 2`. -/
theorem cwObjective_at_one (tlam : ℝ) :
    cwObjective tlam 1 = tlam / 2 - Real.log 2 := by
  simp [cwObjective]

/-- The two fully aligned endpoints have the same Curie--Weiss objective. -/
theorem cwObjective_at_neg_one (tlam : ℝ) :
    cwObjective tlam (-1) = tlam / 2 - Real.log 2 := by
  simp [cwObjective]

/-- **A completely elementary positive-temperature separation.**  Whenever
`2 log 2 < tλ`, the single fully aligned state already makes the overlap-pressure variational
objective positive.  This weaker-than-sharp window is sufficient to refute positive-cone traffic
sufficiency without importing the local series proof of the exact threshold. -/
theorem curieWeiss_supercritical_witness (tlam : ℝ) (hlarge : 2 * Real.log 2 < tlam) :
    0 < cwObjective tlam 1 := by
  rw [cwObjective_at_one]
  linarith

/-- The sharp `tλ > 1` implication reduces exactly to the local strict upper bound on the
Rademacher rate function.  This theorem keeps the remaining analytic input visible: it does not
smuggle the desired phase transition into a structure field. -/
theorem curieWeiss_supercritical_of_local_rate_upper_bound
    (tlam m : ℝ) (hrate : cwRate m < tlam / 2 * m ^ 2) :
    0 < cwObjective tlam m := by
  unfold cwObjective
  linarith

/-- **Above the critical point the variational pressure is strictly positive.**  The explicit
trial magnetisation lies below `(tλ-1)/(tλ+1)`; the global logarithm bound above then beats its
quadratic energy.  No power-series or unformalized Varadhan step is used here. -/
theorem curieWeiss_supercritical (tlam : ℝ) (hcritical : 1 < tlam) :
    ∃ m : ℝ, |m| < 1 ∧ 0 < cwObjective tlam m := by
  let m : ℝ := (tlam - 1) / (2 * (tlam + 1))
  have hden : 0 < 2 * (tlam + 1) := by linarith
  have hm0 : 0 < m := by
    dsimp [m]
    exact div_pos (by linarith) hden
  have hm1 : m < 1 := by
    dsimp [m]
    rw [div_lt_one hden]
    linarith
  have hratio : (1 + m) / (1 - m) < tlam := by
    have hmden : 0 < 1 - m := by linarith
    rw [div_lt_iff₀ hmden]
    have htden : tlam + 1 ≠ 0 := by linarith
    have hmIdentity : (1 + tlam) * m = (tlam - 1) / 2 := by
      dsimp [m]
      field_simp
      ring
    nlinarith [hmIdentity]
  have hrate := cw_rate_upper_bound hm0.le hm1
  have hstrict : cwRate m < tlam / 2 * m ^ 2 := by
    calc
      cwRate m ≤ m ^ 2 * (1 + m) / (2 * (1 - m)) := hrate
      _ = m ^ 2 / 2 * ((1 + m) / (1 - m)) := by
        field_simp
      _ < m ^ 2 / 2 * tlam := by
        exact mul_lt_mul_of_pos_left hratio (by positivity)
      _ = tlam / 2 * m ^ 2 := by ring
  refine ⟨m, (abs_lt).2 ⟨by linarith, hm1⟩, ?_⟩
  exact curieWeiss_supercritical_of_local_rate_upper_bound tlam m hstrict

/-- The exact Curie–Weiss critical dichotomy for the variational pressure coordinate. -/
theorem curieWeiss_critical_dichotomy (tlam : ℝ) :
    (tlam ≤ 1 → ∀ m : ℝ, |m| ≤ 1 → cwObjective tlam m ≤ 0) ∧
      (1 < tlam → ∃ m : ℝ, |m| < 1 ∧ 0 < cwObjective tlam m) :=
  ⟨fun hcritical m hm ↦ curieWeiss_subcritical tlam hcritical m hm,
    curieWeiss_supercritical tlam⟩

/-- Values attained by the Curie--Weiss variational objective on the admissible
magnetisation interval. -/
noncomputable def cwPressureValueSet (tlam : ℝ) : Set ℝ :=
  cwObjective tlam '' Set.Icc (-1) 1

/-- The actual variational pressure gap, rather than only its pointwise
objective. -/
noncomputable def cwVariationalPressureGap (tlam : ℝ) : ℝ :=
  sSup (cwPressureValueSet tlam)

/-- Zero magnetisation makes the pressure-value set nonempty. -/
theorem cwPressureValueSet_nonempty (tlam : ℝ) :
    (cwPressureValueSet tlam).Nonempty := by
  refine ⟨0, 0, ?_, ?_⟩
  · constructor <;> norm_num
  · exact cwObjective_at_zero tlam

/-- The admissible pressure values are bounded above.  Pinsker's inequality
already supplies a uniform bound, so compactness or endpoint continuity is not
needed merely to define the supremum. -/
theorem cwPressureValueSet_bddAbove (tlam : ℝ) :
    BddAbove (cwPressureValueSet tlam) := by
  refine ⟨|tlam| / 2, ?_⟩
  intro value hvalue
  rcases hvalue with ⟨m, hm, rfl⟩
  have habs : |m| ≤ 1 := (abs_le).2 hm
  have hrate : m ^ 2 / 2 ≤ cwRate m := cw_rate_lower_bound m habs
  have hrate0 : 0 ≤ cwRate m := le_trans (by positivity) hrate
  have hsq0 : 0 ≤ m ^ 2 := sq_nonneg m
  have hsq1 : m ^ 2 ≤ 1 := by
    have hproduct : 0 ≤ (1 - m) * (1 + m) :=
      mul_nonneg (by linarith [hm.2]) (by linarith [hm.1])
    nlinarith
  calc
    cwObjective tlam m ≤ tlam / 2 * m ^ 2 := by
      unfold cwObjective
      linarith
    _ ≤ |tlam| / 2 * m ^ 2 := by
      exact mul_le_mul_of_nonneg_right (by linarith [le_abs_self tlam]) hsq0
    _ ≤ |tlam| / 2 := by
      nlinarith [abs_nonneg tlam]

/-- The variational pressure gap is always nonnegative because zero
magnetisation is admissible. -/
theorem cwVariationalPressureGap_nonneg (tlam : ℝ) :
    0 ≤ cwVariationalPressureGap tlam := by
  unfold cwVariationalPressureGap
  apply le_csSup (cwPressureValueSet_bddAbove tlam)
  exact ⟨0, by norm_num, cwObjective_at_zero tlam⟩

/-- Every admissible objective value lies below the variational pressure
supremum by construction. -/
theorem cwObjective_le_variationalPressureGap
    (tlam m : ℝ) (hm : |m| ≤ 1) :
    cwObjective tlam m ≤ cwVariationalPressureGap tlam := by
  unfold cwVariationalPressureGap
  apply le_csSup (cwPressureValueSet_bddAbove tlam)
  exact ⟨m, (abs_le).1 hm, rfl⟩

/-- Changing coupling changes each admissible Curie--Weiss objective by at
most half the coupling displacement. -/
theorem cwObjective_le_add_half_abs_coupling
    (left right m : ℝ) (hm : |m| ≤ 1) :
    cwObjective left m ≤ cwObjective right m + |left - right| / 2 := by
  have hsqNonnegative : 0 ≤ m ^ 2 := sq_nonneg m
  have hsqUpper : m ^ 2 ≤ 1 := by
    rw [abs_le] at hm
    nlinarith
  have hcoupling : (left - right) / 2 ≤ |left - right| / 2 := by
    linarith [le_abs_self (left - right)]
  have habsHalf : 0 ≤ |left - right| / 2 :=
    div_nonneg (abs_nonneg _) (by norm_num)
  calc
    cwObjective left m =
        cwObjective right m + (left - right) / 2 * m ^ 2 := by
      unfold cwObjective
      ring
    _ ≤ cwObjective right m + |left - right| / 2 * m ^ 2 := by
      exact add_le_add_left
        (mul_le_mul_of_nonneg_right hcoupling hsqNonnegative) _
    _ ≤ cwObjective right m + |left - right| / 2 := by
      simpa using add_le_add_left
        (mul_le_mul_of_nonneg_left hsqUpper habsHalf) (cwObjective right m)

/-- The variational pressure inherits the same one-sided coupling comparison
after taking the supremum over magnetisations. -/
theorem cwVariationalPressureGap_le_add_half_abs_coupling
    (left right : ℝ) :
    cwVariationalPressureGap left ≤
      cwVariationalPressureGap right + |left - right| / 2 := by
  unfold cwVariationalPressureGap
  apply csSup_le (cwPressureValueSet_nonempty left)
  intro value hvalue
  rcases hvalue with ⟨m, hm, rfl⟩
  have habs : |m| ≤ 1 := (abs_le).2 hm
  exact (cwObjective_le_add_half_abs_coupling left right m habs).trans
    (add_le_add_right (cwObjective_le_variationalPressureGap right m habs) _)

/-- Sharp global modulus of continuity of the variational pressure. -/
theorem cwVariationalPressureGap_abs_sub_le_half_abs
    (left right : ℝ) :
    |cwVariationalPressureGap left - cwVariationalPressureGap right| ≤
      |left - right| / 2 := by
  rw [abs_le]
  constructor
  · have hreverse :=
      cwVariationalPressureGap_le_add_half_abs_coupling right left
    rw [abs_sub_comm] at hreverse
    linarith
  · have hforward :=
      cwVariationalPressureGap_le_add_half_abs_coupling left right
    linarith

/-- The variational pressure is globally `1/2`-Lipschitz in coupling. -/
theorem cwVariationalPressureGap_lipschitzWith :
    LipschitzWith (⟨1 / 2, by norm_num⟩ : NNReal) cwVariationalPressureGap := by
  apply LipschitzWith.of_dist_le_mul
  intro left right
  rw [Real.dist_eq, Real.dist_eq]
  simpa [abs_sub_comm, mul_comm] using
    cwVariationalPressureGap_abs_sub_le_half_abs left right

/-- In particular the variational pressure profile is continuous globally. -/
theorem continuous_cwVariationalPressureGap :
    Continuous cwVariationalPressureGap :=
  cwVariationalPressureGap_lipschitzWith.continuous

/-- Increasing the positive quadratic coupling cannot decrease any objective
value. -/
theorem cwObjective_mono_coupling {left right : ℝ} (hle : left ≤ right)
    (m : ℝ) :
    cwObjective left m ≤ cwObjective right m := by
  unfold cwObjective
  nlinarith [sq_nonneg m]

/-- The variational pressure is monotone in coupling. -/
theorem monotone_cwVariationalPressureGap :
    Monotone cwVariationalPressureGap := by
  intro left right hle
  unfold cwVariationalPressureGap
  apply csSup_le (cwPressureValueSet_nonempty left)
  intro value hvalue
  rcases hvalue with ⟨m, hm, rfl⟩
  exact (cwObjective_mono_coupling hle m).trans
    (cwObjective_le_variationalPressureGap right m ((abs_le).2 hm))

/-- Each fixed-magnetisation objective is affine in the coupling parameter. -/
theorem cwObjective_affine_coupling
    (left right weightLeft weightRight m : ℝ)
    (hweights : weightLeft + weightRight = 1) :
    cwObjective (weightLeft * left + weightRight * right) m =
      weightLeft * cwObjective left m +
        weightRight * cwObjective right m := by
  unfold cwObjective
  have hrightWeight : weightRight = 1 - weightLeft := by linarith
  rw [hrightWeight]
  ring

/-- The variational pressure satisfies the two-point Jensen inequality because
it is the supremum of affine coupling objectives. -/
theorem cwVariationalPressureGap_convexCombination
    (left right weightLeft weightRight : ℝ)
    (hleft : 0 ≤ weightLeft) (hright : 0 ≤ weightRight)
    (hweights : weightLeft + weightRight = 1) :
    cwVariationalPressureGap (weightLeft * left + weightRight * right) ≤
      weightLeft * cwVariationalPressureGap left +
        weightRight * cwVariationalPressureGap right := by
  unfold cwVariationalPressureGap
  apply csSup_le (cwPressureValueSet_nonempty
    (weightLeft * left + weightRight * right))
  intro value hvalue
  rcases hvalue with ⟨m, hm, rfl⟩
  have habs : |m| ≤ 1 := (abs_le).2 hm
  rw [cwObjective_affine_coupling left right weightLeft weightRight m hweights]
  exact add_le_add
    (mul_le_mul_of_nonneg_left
      (cwObjective_le_variationalPressureGap left m habs) hleft)
    (mul_le_mul_of_nonneg_left
      (cwObjective_le_variationalPressureGap right m habs) hright)

/-- The complete variational pressure profile is convex on the real coupling
line. -/
theorem convexOn_cwVariationalPressureGap :
    ConvexOn ℝ Set.univ cwVariationalPressureGap := by
  constructor
  · exact convex_univ
  · intro left _hleft right _hright weightLeft weightRight
      hweightLeft hweightRight hweights
    simpa only [smul_eq_mul] using
      cwVariationalPressureGap_convexCombination left right weightLeft weightRight
        hweightLeft hweightRight hweights

/-- Below and at the critical point, the supremum is exactly zero. -/
theorem cwVariationalPressureGap_eq_zero_of_subcritical
    (tlam : ℝ) (hcritical : tlam ≤ 1) :
    cwVariationalPressureGap tlam = 0 := by
  apply le_antisymm
  · unfold cwVariationalPressureGap
    apply csSup_le (cwPressureValueSet_nonempty tlam)
    intro value hvalue
    rcases hvalue with ⟨m, hm, rfl⟩
    exact curieWeiss_subcritical tlam hcritical m ((abs_le).2 hm)
  · exact cwVariationalPressureGap_nonneg tlam

/-- Above the critical point, an interior witness lies below the supremum and
makes the pressure gap strictly positive. -/
theorem cwVariationalPressureGap_pos_of_supercritical
    (tlam : ℝ) (hcritical : 1 < tlam) :
    0 < cwVariationalPressureGap tlam := by
  obtain ⟨m, hm, hpositive⟩ := curieWeiss_supercritical tlam hcritical
  have hmember : cwObjective tlam m ∈ cwPressureValueSet tlam :=
    ⟨m, (abs_le).1 hm.le, rfl⟩
  have hle : cwObjective tlam m ≤ cwVariationalPressureGap tlam := by
    exact le_csSup (cwPressureValueSet_bddAbove tlam) hmember
  exact hpositive.trans_le hle

/-- **Exact critical point for the supremal pressure itself.** -/
theorem cwVariationalPressureGap_eq_zero_iff (tlam : ℝ) :
    cwVariationalPressureGap tlam = 0 ↔ tlam ≤ 1 := by
  constructor
  · intro hzero
    by_contra hnot
    have hpositive := cwVariationalPressureGap_pos_of_supercritical tlam (lt_of_not_ge hnot)
    linarith
  · exact cwVariationalPressureGap_eq_zero_of_subcritical tlam

/-! ### A genuine finite-volume pressure counterexample

The development below identifies the genuine finite-volume limit directly.
A biased-binomial trial law gives the Gibbs lower bound, while the matching
product-law factorisation bounds every type above by the exponential
variational pressure.  Since there are only `population + 1` types, the two
bounds differ by at most `log (population + 1) / population`.  The aligned-state
estimate is retained as a simpler explicit certificate.
-/

/-- Magnetisation of the type with `upSpins` positive spins in a population of
size `population`. -/
noncomputable def finiteCWMagnetization
    (population upSpins : ℕ) : ℝ :=
  2 * (upSpins : ℝ) - population

/-- Magnetisation density of one finite Rademacher type. -/
noncomputable def finiteCWEmpiricalMagnetization
    (population upSpins : ℕ) : ℝ :=
  finiteCWMagnetization population upSpins / population

/-- Positive-spin probability in the biased Rademacher trial law associated
with magnetisation `m`. -/
noncomputable def cwPositiveTrialWeight (m : ℝ) : ℝ :=
  (1 + m) / 2

/-- Negative-spin probability in the same trial law. -/
noncomputable def cwNegativeTrialWeight (m : ℝ) : ℝ :=
  (1 - m) / 2

/-- For a nonempty population, rescaling the empirical magnetisation recovers
the unnormalized magnetisation exactly. -/
theorem finiteCWEmpiricalMagnetization_scale
    (population upSpins : ℕ) (hpopulation : 0 < population) :
    (population : ℝ) * finiteCWEmpiricalMagnetization population upSpins =
      finiteCWMagnetization population upSpins := by
  unfold finiteCWEmpiricalMagnetization
  rw [← mul_div_assoc]
  exact mul_div_cancel_left₀ _ (by exact_mod_cast hpopulation.ne')

/-- For an interior type, the empirical magnetisation lies strictly inside
`(-1,1)`. -/
theorem finiteCWEmpiricalMagnetization_abs_lt_one
    (population upSpins : ℕ)
    (hpositive : 0 < upSpins) (hinterior : upSpins < population) :
    |finiteCWEmpiricalMagnetization population upSpins| < 1 := by
  have hpopulation : (0 : ℝ) < population := by
    exact_mod_cast hpositive.trans_le hinterior.le
  have hupPositive : (0 : ℝ) < upSpins := by exact_mod_cast hpositive
  have hupInterior : (upSpins : ℝ) < population := by exact_mod_cast hinterior
  rw [abs_lt]
  constructor
  · unfold finiteCWEmpiricalMagnetization finiteCWMagnetization
    apply (lt_div_iff₀ hpopulation).mpr
    linarith
  · unfold finiteCWEmpiricalMagnetization finiteCWMagnetization
    apply (div_lt_iff₀ hpopulation).mpr
    linarith

/-- Every admissible finite magnetisation has magnitude at most the population
size, hence squared energy at most `population²`. -/
theorem finiteCWMagnetization_sq_le_population_sq
    (population upSpins : ℕ)
    (hupSpins : upSpins ∈ Finset.range (population + 1)) :
    finiteCWMagnetization population upSpins ^ 2 ≤ (population : ℝ) ^ 2 := by
  have hle : upSpins ≤ population :=
    Nat.le_of_lt_succ (Finset.mem_range.mp hupSpins)
  have hupNonnegative : (0 : ℝ) ≤ upSpins := by positivity
  have hupUpper : (upSpins : ℝ) ≤ population := by exact_mod_cast hle
  unfold finiteCWMagnetization
  nlinarith

/-- The positive-spin parameter induced by the empirical magnetisation is the
observed positive-spin fraction. -/
theorem cwPositiveTrialWeight_empirical
    (population upSpins : ℕ) (hpopulation : 0 < population) :
    cwPositiveTrialWeight
        (finiteCWEmpiricalMagnetization population upSpins) =
      (upSpins : ℝ) / population := by
  unfold cwPositiveTrialWeight finiteCWEmpiricalMagnetization finiteCWMagnetization
  have hpopulationReal : (population : ℝ) ≠ 0 := by
    exact_mod_cast hpopulation.ne'
  field_simp
  ring

/-- The complementary trial parameter is the observed negative-spin fraction. -/
theorem cwNegativeTrialWeight_empirical
    (population upSpins : ℕ) (hpopulation : 0 < population)
    (hle : upSpins ≤ population) :
    cwNegativeTrialWeight
        (finiteCWEmpiricalMagnetization population upSpins) =
      (population - upSpins : ℕ) / (population : ℝ) := by
  unfold cwNegativeTrialWeight finiteCWEmpiricalMagnetization finiteCWMagnetization
  have hpopulationReal : (population : ℝ) ≠ 0 := by
    exact_mod_cast hpopulation.ne'
  rw [Nat.cast_sub hle]
  field_simp
  ring

/-- Binomial type weight under a trial product law with positive-spin weight
`q` and negative-spin weight `r`. -/
noncomputable def biasedBinomialTypeWeight
    (population : ℕ) (q r : ℝ) (upSpins : ℕ) : ℝ :=
  (Nat.choose population upSpins : ℝ) *
    q ^ upSpins * r ^ (population - upSpins)

/-- If the two trial weights add to one, the binomial type weights form a
probability law exactly. -/
theorem biasedBinomialTypeWeight_sum
    (population : ℕ) (q r : ℝ) (hqr : q + r = 1) :
    (∑ upSpins ∈ Finset.range (population + 1),
      biasedBinomialTypeWeight population q r upSpins) = 1 := by
  calc
    (∑ upSpins ∈ Finset.range (population + 1),
        biasedBinomialTypeWeight population q r upSpins) =
        (q + r) ^ population := by
      rw [add_pow]
      apply Finset.sum_congr rfl
      intro upSpins _hupSpins
      simp only [biasedBinomialTypeWeight]
      ring
    _ = 1 := by rw [hqr, one_pow]

/-- The exact first moment of the biased binomial type law.  This is proved
from Pascal splitting rather than imported as a probabilistic fact. -/
theorem biasedBinomialTypeWeight_firstMoment
    (population : ℕ) (q r : ℝ) (hqr : q + r = 1) :
    (∑ upSpins ∈ Finset.range (population + 1),
      biasedBinomialTypeWeight population q r upSpins * upSpins) =
        population * q := by
  induction population with
  | zero => simp [biasedBinomialTypeWeight]
  | succ population ih =>
      have hsplit := Finset.sum_choose_succ_mul (R := ℝ)
        (fun upSpins downSpins ↦
          q ^ upSpins * r ^ downSpins * (upSpins : ℝ)) population
      have hsplit' :
          (∑ upSpins ∈ Finset.range (population + 2),
              biasedBinomialTypeWeight (population + 1) q r upSpins * upSpins) =
            (∑ upSpins ∈ Finset.range (population + 1),
              (Nat.choose population upSpins : ℝ) *
                (q ^ upSpins * r ^ (population + 1 - upSpins) * upSpins)) +
            ∑ upSpins ∈ Finset.range (population + 1),
              (Nat.choose population upSpins : ℝ) *
                (q ^ (upSpins + 1) * r ^ (population - upSpins) * (upSpins + 1)) := by
        simpa only [biasedBinomialTypeWeight, Nat.cast_add, Nat.cast_one,
          Nat.succ_eq_add_one, mul_assoc] using hsplit
      rw [hsplit']
      have hfirst :
          (∑ upSpins ∈ Finset.range (population + 1),
            (Nat.choose population upSpins : ℝ) *
              (q ^ upSpins * r ^ (population + 1 - upSpins) * upSpins)) =
            r * ∑ upSpins ∈ Finset.range (population + 1),
              biasedBinomialTypeWeight population q r upSpins * upSpins := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro upSpins hupSpins
        have hle : upSpins ≤ population :=
          Nat.le_of_lt_succ (Finset.mem_range.mp hupSpins)
        rw [Nat.succ_sub hle, pow_succ]
        simp only [biasedBinomialTypeWeight]
        ring
      have hsecond :
          (∑ upSpins ∈ Finset.range (population + 1),
            (Nat.choose population upSpins : ℝ) *
              (q ^ (upSpins + 1) * r ^ (population - upSpins) * (upSpins + 1))) =
            q * (∑ upSpins ∈ Finset.range (population + 1),
              biasedBinomialTypeWeight population q r upSpins * upSpins) +
            q * (∑ upSpins ∈ Finset.range (population + 1),
              biasedBinomialTypeWeight population q r upSpins) := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro upSpins _hupSpins
        simp only [biasedBinomialTypeWeight, pow_succ]
        ring
      rw [hfirst, hsecond, ih,
        biasedBinomialTypeWeight_sum population q r hqr]
      push_cast
      have hr : r = 1 - q := by linarith
      rw [hr]
      ring

/-- **Finite Gibbs variational inequality.**  For any strictly positive trial
probability weights and strictly positive masses, the log of the total mass is
at least the trial expectation of the log likelihood ratio.  This is the exact
finite change-of-measure inequality needed below; no asymptotic principle is
used. -/
theorem finiteLogSum_ge_weightedLogRatio
    {Index : Type*} (indices : Finset Index)
    (weight mass : Index → ℝ)
    (hindices : indices.Nonempty)
    (hweight : ∀ index ∈ indices, 0 < weight index)
    (hmass : ∀ index ∈ indices, 0 < mass index)
    (hweightSum : ∑ index ∈ indices, weight index = 1) :
    (∑ index ∈ indices,
        weight index * Real.log (mass index / weight index)) ≤
      Real.log (∑ index ∈ indices, mass index) := by
  have hjensen :
      Real.exp (∑ index ∈ indices,
        weight index * Real.log (mass index / weight index)) ≤
        ∑ index ∈ indices,
          weight index * Real.exp (Real.log (mass index / weight index)) := by
    simpa only [smul_eq_mul] using
      (convexOn_exp.map_sum_le
        (t := indices) (w := weight)
        (p := fun index ↦ Real.log (mass index / weight index))
        (fun index hindex ↦ (hweight index hindex).le)
        hweightSum
        (fun index _hindex ↦ Set.mem_univ
          (Real.log (mass index / weight index))))
  have harithmetic :
      (∑ index ∈ indices,
        weight index *
          Real.exp (Real.log (mass index / weight index))) =
        ∑ index ∈ indices, mass index := by
    apply Finset.sum_congr rfl
    intro index hindex
    rw [Real.exp_log (div_pos (hmass index hindex) (hweight index hindex))]
    rw [← mul_div_assoc]
    exact mul_div_cancel_left₀ (mass index) (hweight index hindex).ne'
  rw [harithmetic] at hjensen
  have hmassSum : 0 < ∑ index ∈ indices, mass index :=
    Finset.sum_pos (fun index hindex ↦ hmass index hindex) hindices
  have hlogged := Real.log_le_log (Real.exp_pos _) hjensen
  simpa using hlogged

/-- The exact Curie--Weiss/Rademacher partition function after dividing by the
`2^population` configurations.  Grouping configurations by their number of
positive spins produces the binomial coefficient in the sum. -/
noncomputable def finiteCWPartition
    (population : ℕ) (tlam : ℝ) : ℝ :=
  ((2 : ℝ) ^ population)⁻¹ *
    ∑ upSpins ∈ Finset.range (population + 1),
      (Nat.choose population upSpins : ℝ) *
        Real.exp
          (tlam / (2 * (population : ℝ)) *
            finiteCWMagnetization population upSpins ^ 2)

/-- Normalized finite-volume pressure difference from the unspiked baseline. -/
noncomputable def finiteCWPressureGap
    (population : ℕ) (tlam : ℝ) : ℝ :=
  Real.log (finiteCWPartition population tlam) / population

@[simp] theorem cwTrialWeights_sum (m : ℝ) :
    cwPositiveTrialWeight m + cwNegativeTrialWeight m = 1 := by
  simp [cwPositiveTrialWeight, cwNegativeTrialWeight]
  ring

theorem cwPositiveTrialWeight_pos {m : ℝ} (hm : |m| < 1) :
    0 < cwPositiveTrialWeight m := by
  rw [abs_lt] at hm
  unfold cwPositiveTrialWeight
  linarith

theorem cwNegativeTrialWeight_pos {m : ℝ} (hm : |m| < 1) :
    0 < cwNegativeTrialWeight m := by
  rw [abs_lt] at hm
  unfold cwNegativeTrialWeight
  linarith

/-- Contribution of one magnetisation type to the normalized finite
Curie--Weiss partition function. -/
noncomputable def finiteCWTypeMass
    (population : ℕ) (tlam : ℝ) (upSpins : ℕ) : ℝ :=
  ((2 : ℝ) ^ population)⁻¹ *
    (Nat.choose population upSpins : ℝ) *
      Real.exp
        (tlam / (2 * (population : ℝ)) *
          finiteCWMagnetization population upSpins ^ 2)

/-- The partition function is exactly the sum of its positive type masses. -/
theorem finiteCWTypeMass_sum (population : ℕ) (tlam : ℝ) :
    (∑ upSpins ∈ Finset.range (population + 1),
      finiteCWTypeMass population tlam upSpins) =
        finiteCWPartition population tlam := by
  rw [finiteCWPartition, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro upSpins _hupSpins
  simp only [finiteCWTypeMass]
  ring

/-- Every admissible magnetisation type has strictly positive trial weight. -/
theorem biasedBinomialTypeWeight_pos
    (population upSpins : ℕ) (m : ℝ)
    (hm : |m| < 1) (hupSpins : upSpins ∈ Finset.range (population + 1)) :
    0 < biasedBinomialTypeWeight population
      (cwPositiveTrialWeight m) (cwNegativeTrialWeight m) upSpins := by
  have hle : upSpins ≤ population :=
    Nat.le_of_lt_succ (Finset.mem_range.mp hupSpins)
  exact mul_pos
    (mul_pos
      (by exact_mod_cast Nat.choose_pos hle)
      (pow_pos (cwPositiveTrialWeight_pos hm) _))
    (pow_pos (cwNegativeTrialWeight_pos hm) _)

/-- Every admissible type also has strictly positive partition mass. -/
theorem finiteCWTypeMass_pos
    (population upSpins : ℕ) (tlam : ℝ)
    (hupSpins : upSpins ∈ Finset.range (population + 1)) :
    0 < finiteCWTypeMass population tlam upSpins := by
  have hle : upSpins ≤ population :=
    Nat.le_of_lt_succ (Finset.mem_range.mp hupSpins)
  unfold finiteCWTypeMass
  exact mul_pos
    (mul_pos (by positivity) (by exact_mod_cast Nat.choose_pos hle))
    (Real.exp_pos _)

/-- **The tilted binomial weights, summed and first-moment, in one specialisation.**

Both spin means below open by instantiating the general binomial identities at the
Curie--Weiss trial weights, and each carried its own copy of that step. -/
theorem cwBinomialTypeWeight_sum_and_firstMoment (population : ℕ) (m : ℝ) :
    (∑ upSpins ∈ Finset.range (population + 1),
        biasedBinomialTypeWeight population (cwPositiveTrialWeight m)
          (cwNegativeTrialWeight m) upSpins) = 1 ∧
      (∑ upSpins ∈ Finset.range (population + 1),
        biasedBinomialTypeWeight population (cwPositiveTrialWeight m)
          (cwNegativeTrialWeight m) upSpins * upSpins) =
        population * cwPositiveTrialWeight m :=
  ⟨biasedBinomialTypeWeight_sum population _ _ (cwTrialWeights_sum m),
    biasedBinomialTypeWeight_firstMoment population _ _ (cwTrialWeights_sum m)⟩

/-- Under the biased binomial trial law, expected magnetisation is exactly
`population * m`. -/
theorem biasedBinomialTypeWeight_magnetizationMean
    (population : ℕ) (m : ℝ) :
    (∑ upSpins ∈ Finset.range (population + 1),
      biasedBinomialTypeWeight population
          (cwPositiveTrialWeight m) (cwNegativeTrialWeight m) upSpins *
        finiteCWMagnetization population upSpins) =
      population * m := by
  let q := cwPositiveTrialWeight m
  let r := cwNegativeTrialWeight m
  obtain ⟨hsum, hfirst⟩ := cwBinomialTypeWeight_sum_and_firstMoment population m
  calc
    (∑ upSpins ∈ Finset.range (population + 1),
      biasedBinomialTypeWeight population q r upSpins *
        finiteCWMagnetization population upSpins) =
        2 * (∑ upSpins ∈ Finset.range (population + 1),
          biasedBinomialTypeWeight population q r upSpins * upSpins) -
        population * (∑ upSpins ∈ Finset.range (population + 1),
          biasedBinomialTypeWeight population q r upSpins) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro upSpins _hupSpins
      simp only [finiteCWMagnetization]
      ring
    _ = 2 * (population * q) - population := by rw [hfirst, hsum]; ring
    _ = population * m := by
      dsimp [q, cwPositiveTrialWeight]
      ring

/-- The expected number of negative spins is the complementary binomial
mean. -/
theorem biasedBinomialTypeWeight_downSpinMean
    (population : ℕ) (m : ℝ) :
    (∑ upSpins ∈ Finset.range (population + 1),
      biasedBinomialTypeWeight population
          (cwPositiveTrialWeight m) (cwNegativeTrialWeight m) upSpins *
        (population - upSpins)) =
      population * cwNegativeTrialWeight m := by
  let q := cwPositiveTrialWeight m
  let r := cwNegativeTrialWeight m
  obtain ⟨hsum, hfirst⟩ := cwBinomialTypeWeight_sum_and_firstMoment population m
  calc
    (∑ upSpins ∈ Finset.range (population + 1),
      biasedBinomialTypeWeight population q r upSpins *
        (population - upSpins)) =
        population * (∑ upSpins ∈ Finset.range (population + 1),
          biasedBinomialTypeWeight population q r upSpins) -
        ∑ upSpins ∈ Finset.range (population + 1),
          biasedBinomialTypeWeight population q r upSpins * upSpins := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro upSpins _hupSpins
      ring
    _ = population - population * q := by rw [hsum, hfirst]; ring
    _ = population * r := by
      have hr : r = 1 - q := by
        dsimp [q, r]
        rw [← cwTrialWeights_sum m]
        ring
      rw [hr]
      ring

/-- Jensen's inequality for the square gives the exact lower bound on the
trial second moment needed by the Curie--Weiss energy. -/
theorem biasedBinomialTypeWeight_magnetizationSecondMoment
    (population : ℕ) (m : ℝ) (hm : |m| < 1) :
    ((population : ℝ) * m) ^ 2 ≤
      ∑ upSpins ∈ Finset.range (population + 1),
        biasedBinomialTypeWeight population
            (cwPositiveTrialWeight m) (cwNegativeTrialWeight m) upSpins *
          finiteCWMagnetization population upSpins ^ 2 := by
  let weight := fun upSpins ↦ biasedBinomialTypeWeight population
    (cwPositiveTrialWeight m) (cwNegativeTrialWeight m) upSpins
  have hweightNonnegative : ∀ upSpins ∈ Finset.range (population + 1),
      0 ≤ weight upSpins := fun upSpins hupSpins ↦
    (biasedBinomialTypeWeight_pos population upSpins m hm hupSpins).le
  have hweightSum :
      (∑ upSpins ∈ Finset.range (population + 1), weight upSpins) = 1 :=
    biasedBinomialTypeWeight_sum population
      (cwPositiveTrialWeight m) (cwNegativeTrialWeight m) (cwTrialWeights_sum m)
  have hjensen := Real.pow_arith_mean_le_arith_mean_pow_of_even
    (Finset.range (population + 1)) weight
    (finiteCWMagnetization population) hweightNonnegative hweightSum (by decide : Even 2)
  rw [show (∑ upSpins ∈ Finset.range (population + 1),
      weight upSpins * finiteCWMagnetization population upSpins) =
        population * m by
      exact biasedBinomialTypeWeight_magnetizationMean population m] at hjensen
  exact hjensen

/-- The entropy cost of the biased Bernoulli trial law is exactly the
Curie--Weiss rate function used in the variational objective. -/
theorem cwTrialEntropy_eq_rate {m : ℝ} (hm : |m| < 1) :
    Real.log 2 +
        cwPositiveTrialWeight m * Real.log (cwPositiveTrialWeight m) +
        cwNegativeTrialWeight m * Real.log (cwNegativeTrialWeight m) =
      cwRate m := by
  have hplus : 0 < 1 + m := by
    rw [abs_lt] at hm
    linarith
  have hminus : 0 < 1 - m := by
    rw [abs_lt] at hm
    linarith
  have htwo : (2 : ℝ) ≠ 0 := by norm_num
  rw [show Real.log (cwPositiveTrialWeight m) =
      Real.log (1 + m) - Real.log 2 by
        rw [cwPositiveTrialWeight, Real.log_div hplus.ne' htwo],
    show Real.log (cwNegativeTrialWeight m) =
      Real.log (1 - m) - Real.log 2 by
        rw [cwNegativeTrialWeight, Real.log_div hminus.ne' htwo]]
  unfold cwRate cwPositiveTrialWeight cwNegativeTrialWeight
  ring

/-- Exact pointwise log likelihood ratio between one Curie--Weiss type mass
and the corresponding biased-binomial trial mass.  The binomial coefficient
cancels, leaving energy minus the product-law entropy cost. -/
theorem finiteCWTypeMass_logRatio
    (population upSpins : ℕ) (tlam m : ℝ)
    (hm : |m| < 1) (hupSpins : upSpins ∈ Finset.range (population + 1)) :
    Real.log
        (finiteCWTypeMass population tlam upSpins /
          biasedBinomialTypeWeight population
            (cwPositiveTrialWeight m) (cwNegativeTrialWeight m) upSpins) =
      tlam / (2 * (population : ℝ)) *
          finiteCWMagnetization population upSpins ^ 2 -
        population * Real.log 2 -
        upSpins * Real.log (cwPositiveTrialWeight m) -
        (population - upSpins) * Real.log (cwNegativeTrialWeight m) := by
  have hle : upSpins ≤ population :=
    Nat.le_of_lt_succ (Finset.mem_range.mp hupSpins)
  have hchooseNat : 0 < Nat.choose population upSpins := Nat.choose_pos hle
  have hchoose : (Nat.choose population upSpins : ℝ) ≠ 0 := by
    exact_mod_cast hchooseNat.ne'
  have hq : cwPositiveTrialWeight m ≠ 0 := (cwPositiveTrialWeight_pos hm).ne'
  have hr : cwNegativeTrialWeight m ≠ 0 := (cwNegativeTrialWeight_pos hm).ne'
  have hpowTwo : (2 : ℝ) ^ population ≠ 0 := pow_ne_zero _ (by norm_num)
  rw [Real.log_div
      (finiteCWTypeMass_pos population upSpins tlam hupSpins).ne'
      (biasedBinomialTypeWeight_pos population upSpins m hm hupSpins).ne']
  unfold finiteCWTypeMass biasedBinomialTypeWeight
  rw [Real.log_mul (mul_ne_zero (inv_ne_zero hpowTwo) hchoose)
        (Real.exp_ne_zero _),
    Real.log_mul (inv_ne_zero hpowTwo) hchoose,
    Real.log_inv, Real.log_pow, Real.log_exp,
    Real.log_mul (mul_ne_zero hchoose (pow_ne_zero _ hq))
      (pow_ne_zero _ hr),
    Real.log_mul hchoose (pow_ne_zero _ hq),
    Real.log_pow, Real.log_pow]
  rw [Nat.cast_sub hle]
  ring

/-- At the empirical magnetisation of an interior type, its exact log
likelihood ratio against the matching product law is the population-scaled
Curie--Weiss objective. -/
theorem finiteCWTypeMass_matched_logRatio_eq_objective
    (population upSpins : ℕ) (tlam : ℝ)
    (hpositive : 0 < upSpins) (hinterior : upSpins < population) :
    Real.log
        (finiteCWTypeMass population tlam upSpins /
          biasedBinomialTypeWeight population
            (cwPositiveTrialWeight
              (finiteCWEmpiricalMagnetization population upSpins))
            (cwNegativeTrialWeight
              (finiteCWEmpiricalMagnetization population upSpins)) upSpins) =
      (population : ℝ) *
        cwObjective tlam
          (finiteCWEmpiricalMagnetization population upSpins) := by
  let m := finiteCWEmpiricalMagnetization population upSpins
  let q := cwPositiveTrialWeight m
  let r := cwNegativeTrialWeight m
  have hpopulation : 0 < population := hpositive.trans_le hinterior.le
  have hle : upSpins ≤ population := hinterior.le
  have hm : |m| < 1 :=
    finiteCWEmpiricalMagnetization_abs_lt_one population upSpins
      hpositive hinterior
  have hupSpins : upSpins ∈ Finset.range (population + 1) := by
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le hle)
  have hscale : (population : ℝ) * m =
      finiteCWMagnetization population upSpins :=
    finiteCWEmpiricalMagnetization_scale population upSpins hpopulation
  have hqScale : (population : ℝ) * q = upSpins := by
    dsimp [q, m]
    rw [cwPositiveTrialWeight_empirical population upSpins hpopulation]
    field_simp
  have hrScale : (population : ℝ) * r = population - upSpins := by
    dsimp [r, m]
    rw [cwNegativeTrialWeight_empirical population upSpins hpopulation hle]
    rw [Nat.cast_sub hle]
    field_simp
  rw [finiteCWTypeMass_logRatio population upSpins tlam m hm hupSpins]
  rw [← hqScale]
  unfold cwObjective
  rw [← cwTrialEntropy_eq_rate hm]
  have hpopulationReal : (population : ℝ) ≠ 0 := by
    exact_mod_cast hpopulation.ne'
  rw [← hscale]
  dsimp [m, q, r, cwPositiveTrialWeight, cwNegativeTrialWeight]
  field_simp
  ring

/-- The matched biased-binomial type weight is a genuine probability mass and
therefore is at most one. -/
theorem biasedBinomialTypeWeight_le_one
    (population upSpins : ℕ) (q r : ℝ)
    (hq : 0 ≤ q) (hr : 0 ≤ r) (hqr : q + r = 1)
    (hupSpins : upSpins ∈ Finset.range (population + 1)) :
    biasedBinomialTypeWeight population q r upSpins ≤ 1 := by
  have hnonnegative : ∀ index ∈ Finset.range (population + 1),
      0 ≤ biasedBinomialTypeWeight population q r index := by
    intro index _hindex
    unfold biasedBinomialTypeWeight
    positivity
  have hsingle := Finset.single_le_sum hnonnegative hupSpins
  rw [biasedBinomialTypeWeight_sum population q r hqr] at hsingle
  exact hsingle

/-- Exponentiating the matched log-ratio identity gives an exact factorisation
of every interior Curie--Weiss type mass into a product-law probability and an
exponential variational reward. -/
theorem finiteCWTypeMass_eq_matchedWeight_mul_expObjective
    (population upSpins : ℕ) (tlam : ℝ)
    (hpositive : 0 < upSpins) (hinterior : upSpins < population) :
    finiteCWTypeMass population tlam upSpins =
      biasedBinomialTypeWeight population
          (cwPositiveTrialWeight
            (finiteCWEmpiricalMagnetization population upSpins))
          (cwNegativeTrialWeight
            (finiteCWEmpiricalMagnetization population upSpins)) upSpins *
        Real.exp ((population : ℝ) *
          cwObjective tlam
            (finiteCWEmpiricalMagnetization population upSpins)) := by
  let m := finiteCWEmpiricalMagnetization population upSpins
  let weight := biasedBinomialTypeWeight population
    (cwPositiveTrialWeight m) (cwNegativeTrialWeight m) upSpins
  have hle : upSpins ≤ population := hinterior.le
  have hupSpins : upSpins ∈ Finset.range (population + 1) := by
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le hle)
  have hm : |m| < 1 :=
    finiteCWEmpiricalMagnetization_abs_lt_one population upSpins
      hpositive hinterior
  have hweight : 0 < weight :=
    biasedBinomialTypeWeight_pos population upSpins m hm hupSpins
  have hmass : 0 < finiteCWTypeMass population tlam upSpins :=
    finiteCWTypeMass_pos population upSpins tlam hupSpins
  have hlog := finiteCWTypeMass_matched_logRatio_eq_objective
    population upSpins tlam hpositive hinterior
  have hexp := congrArg Real.exp hlog
  have hratio : finiteCWTypeMass population tlam upSpins / weight =
      Real.exp ((population : ℝ) * cwObjective tlam m) := by
    simpa [weight, m, Real.exp_log (div_pos hmass hweight)] using hexp
  have hmassEq : finiteCWTypeMass population tlam upSpins =
      Real.exp ((population : ℝ) * cwObjective tlam m) * weight :=
    (div_eq_iff hweight.ne').mp hratio
  simpa [weight, m, mul_comm] using hmassEq

/-- Every interior magnetisation type has mass at most one throughout the
complete subcritical and critical regime. -/
theorem finiteCWTypeMass_interior_le_one_of_subcritical
    (population upSpins : ℕ) (tlam : ℝ)
    (hcritical : tlam ≤ 1)
    (hpositive : 0 < upSpins) (hinterior : upSpins < population) :
    finiteCWTypeMass population tlam upSpins ≤ 1 := by
  let m := finiteCWEmpiricalMagnetization population upSpins
  let q := cwPositiveTrialWeight m
  let r := cwNegativeTrialWeight m
  let weight := biasedBinomialTypeWeight population q r upSpins
  have hpopulation : 0 < population := hpositive.trans_le hinterior.le
  have hm : |m| < 1 :=
    finiteCWEmpiricalMagnetization_abs_lt_one population upSpins
      hpositive hinterior
  have hupSpins : upSpins ∈ Finset.range (population + 1) := by
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le hinterior.le)
  have hweightNonnegative : 0 ≤ weight :=
    (biasedBinomialTypeWeight_pos population upSpins m hm hupSpins).le
  have hweightUpper : weight ≤ 1 :=
    biasedBinomialTypeWeight_le_one population upSpins q r
      (cwPositiveTrialWeight_pos hm).le (cwNegativeTrialWeight_pos hm).le
      (cwTrialWeights_sum m) hupSpins
  have hobjective : cwObjective tlam m ≤ 0 :=
    curieWeiss_subcritical tlam hcritical m hm.le
  have hpopulationNonnegative : (0 : ℝ) ≤ population := by positivity
  have hscaled : (population : ℝ) * cwObjective tlam m ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hpopulationNonnegative hobjective
  have hexpUpper : Real.exp ((population : ℝ) * cwObjective tlam m) ≤ 1 := by
    simpa using (Real.exp_le_one_iff.mpr hscaled)
  rw [finiteCWTypeMass_eq_matchedWeight_mul_expObjective population upSpins
    tlam hpositive hinterior]
  exact (mul_le_mul hweightUpper hexpUpper (Real.exp_pos _).le (by norm_num)).trans_eq
    (one_mul 1)

/-- The fully aligned type mass is exactly the exponential of the endpoint
variational objective times the population. -/
theorem finiteCWTypeMass_aligned_eq_exp_objective
    (population : ℕ) (tlam : ℝ) (hpopulation : 0 < population) :
    finiteCWTypeMass population tlam population =
      Real.exp ((population : ℝ) * cwObjective tlam 1) := by
  have hpopulationReal : (population : ℝ) ≠ 0 := by
    exact_mod_cast hpopulation.ne'
  have htwoPow : (2 : ℝ) ^ population =
      Real.exp ((population : ℝ) * Real.log 2) := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  calc
    finiteCWTypeMass population tlam population =
        ((2 : ℝ) ^ population)⁻¹ *
          Real.exp (tlam * population / 2) := by
      unfold finiteCWTypeMass
      simp [finiteCWMagnetization]
      field_simp
      ring
    _ = Real.exp (-((population : ℝ) * Real.log 2)) *
          Real.exp (tlam * population / 2) := by
      rw [htwoPow, Real.exp_neg]
    _ = Real.exp ((population : ℝ) *
          (tlam / 2 - Real.log 2)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ = Real.exp ((population : ℝ) * cwObjective tlam 1) := by
      rw [cwObjective_at_one]

/-- The fully anti-aligned type has the same exact endpoint mass. -/
theorem finiteCWTypeMass_zero_eq_exp_objective
    (population : ℕ) (tlam : ℝ) (hpopulation : 0 < population) :
    finiteCWTypeMass population tlam 0 =
      Real.exp ((population : ℝ) * cwObjective tlam (-1)) := by
  have hpopulationReal : (population : ℝ) ≠ 0 := by
    exact_mod_cast hpopulation.ne'
  have htwoPow : (2 : ℝ) ^ population =
      Real.exp ((population : ℝ) * Real.log 2) := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  calc
    finiteCWTypeMass population tlam 0 =
        ((2 : ℝ) ^ population)⁻¹ *
          Real.exp (tlam * population / 2) := by
      unfold finiteCWTypeMass finiteCWMagnetization
      simp
      field_simp
    _ = Real.exp (-((population : ℝ) * Real.log 2)) *
          Real.exp (tlam * population / 2) := by
      rw [htwoPow, Real.exp_neg]
    _ = Real.exp ((population : ℝ) *
          (tlam / 2 - Real.log 2)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ = Real.exp ((population : ℝ) * cwObjective tlam (-1)) := by
      unfold cwObjective
      rw [cwRate_neg_one]
      ring_nf

/-- Endpoint types also have mass at most one at and below the critical
coupling. -/
theorem finiteCWTypeMass_endpoint_le_one_of_subcritical
    (population : ℕ) (tlam : ℝ) (hpopulation : 0 < population)
    (hcritical : tlam ≤ 1) :
    finiteCWTypeMass population tlam 0 ≤ 1 ∧
      finiteCWTypeMass population tlam population ≤ 1 := by
  have hpopulationNonnegative : (0 : ℝ) ≤ population := by positivity
  have hnegativeObjective : cwObjective tlam (-1) ≤ 0 :=
    curieWeiss_subcritical tlam hcritical (-1) (by norm_num)
  have hpositiveObjective : cwObjective tlam 1 ≤ 0 :=
    curieWeiss_subcritical tlam hcritical 1 (by norm_num)
  constructor
  · rw [finiteCWTypeMass_zero_eq_exp_objective population tlam hpopulation]
    apply Real.exp_le_one_iff.mpr
    exact mul_nonpos_of_nonneg_of_nonpos hpopulationNonnegative hnegativeObjective
  · rw [finiteCWTypeMass_aligned_eq_exp_objective population tlam hpopulation]
    apply Real.exp_le_one_iff.mpr
    exact mul_nonpos_of_nonneg_of_nonpos hpopulationNonnegative hpositiveObjective

/-- The unique zero-population type has unit mass. -/
theorem finiteCWTypeMass_eq_one_of_population_eq_zero
    (population upSpins : ℕ) (tlam : ℝ)
    (hupSpins : upSpins ∈ Finset.range (population + 1))
    (hpopulation : population = 0) :
    finiteCWTypeMass population tlam upSpins = 1 := by
  have hupZero : upSpins = 0 := Nat.eq_zero_of_le_zero
    (hpopulation ▸ Nat.le_of_lt_succ (Finset.mem_range.mp hupSpins))
  subst population
  subst upSpins
  simp [finiteCWTypeMass, finiteCWMagnetization]

/-- Every admissible type mass is at most one throughout the complete
subcritical/critical window. -/
theorem finiteCWTypeMass_le_one_of_subcritical
    (population upSpins : ℕ) (tlam : ℝ) (hcritical : tlam ≤ 1)
    (hupSpins : upSpins ∈ Finset.range (population + 1)) :
    finiteCWTypeMass population tlam upSpins ≤ 1 := by
  have hle : upSpins ≤ population :=
    Nat.le_of_lt_succ (Finset.mem_range.mp hupSpins)
  by_cases hpopulation : population = 0
  · exact (finiteCWTypeMass_eq_one_of_population_eq_zero
      population upSpins tlam hupSpins hpopulation).le
  · have hpopulationPositive : 0 < population := Nat.pos_of_ne_zero hpopulation
    by_cases hupZero : upSpins = 0
    · subst upSpins
      exact (finiteCWTypeMass_endpoint_le_one_of_subcritical population tlam
        hpopulationPositive hcritical).1
    · by_cases hupAligned : upSpins = population
      · subst upSpins
        exact (finiteCWTypeMass_endpoint_le_one_of_subcritical population tlam
          hpopulationPositive hcritical).2
      · exact finiteCWTypeMass_interior_le_one_of_subcritical population upSpins
          tlam hcritical (Nat.pos_of_ne_zero hupZero)
          (lt_of_le_of_ne hle hupAligned)

/-- Every finite magnetisation type is bounded by the exponential of the
population-scaled variational pressure.  For interior types this follows from
the exact matched-product factorisation and the fact that a probability mass
is at most one; the two endpoint identities close the boundary cases. -/
theorem finiteCWTypeMass_le_exp_variationalPressure
    (population upSpins : ℕ) (tlam : ℝ)
    (hupSpins : upSpins ∈ Finset.range (population + 1)) :
    finiteCWTypeMass population tlam upSpins ≤
      Real.exp ((population : ℝ) * cwVariationalPressureGap tlam) := by
  have hle : upSpins ≤ population :=
    Nat.le_of_lt_succ (Finset.mem_range.mp hupSpins)
  by_cases hpopulation : population = 0
  · rw [finiteCWTypeMass_eq_one_of_population_eq_zero
      population upSpins tlam hupSpins hpopulation, hpopulation]
    simp
  · have hpopulationPositive : 0 < population := Nat.pos_of_ne_zero hpopulation
    have hpopulationNonnegative : (0 : ℝ) ≤ population := by positivity
    by_cases hupZero : upSpins = 0
    · subst upSpins
      rw [finiteCWTypeMass_zero_eq_exp_objective population tlam
        hpopulationPositive]
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_left
        (cwObjective_le_variationalPressureGap tlam (-1) (by norm_num))
        hpopulationNonnegative
    · by_cases hupAligned : upSpins = population
      · subst upSpins
        rw [finiteCWTypeMass_aligned_eq_exp_objective population tlam
          hpopulationPositive]
        apply Real.exp_le_exp.mpr
        exact mul_le_mul_of_nonneg_left
          (cwObjective_le_variationalPressureGap tlam 1 (by norm_num))
          hpopulationNonnegative
      · have hpositive : 0 < upSpins := Nat.pos_of_ne_zero hupZero
        have hinterior : upSpins < population :=
          lt_of_le_of_ne hle hupAligned
        let m := finiteCWEmpiricalMagnetization population upSpins
        let q := cwPositiveTrialWeight m
        let r := cwNegativeTrialWeight m
        let weight := biasedBinomialTypeWeight population q r upSpins
        have hm : |m| < 1 :=
          finiteCWEmpiricalMagnetization_abs_lt_one population upSpins
            hpositive hinterior
        have hweightUpper : weight ≤ 1 :=
          biasedBinomialTypeWeight_le_one population upSpins q r
            (cwPositiveTrialWeight_pos hm).le
            (cwNegativeTrialWeight_pos hm).le
            (cwTrialWeights_sum m) hupSpins
        have hobjective : cwObjective tlam m ≤
            cwVariationalPressureGap tlam :=
          cwObjective_le_variationalPressureGap tlam m hm.le
        have hscaled : (population : ℝ) * cwObjective tlam m ≤
            (population : ℝ) * cwVariationalPressureGap tlam :=
          mul_le_mul_of_nonneg_left hobjective hpopulationNonnegative
        have hexpUpper : Real.exp ((population : ℝ) * cwObjective tlam m) ≤
            Real.exp ((population : ℝ) * cwVariationalPressureGap tlam) :=
          Real.exp_le_exp.mpr hscaled
        rw [finiteCWTypeMass_eq_matchedWeight_mul_expObjective population
          upSpins tlam hpositive hinterior]
        exact (mul_le_mul hweightUpper hexpUpper (Real.exp_pos _).le
          (by norm_num)).trans_eq (one_mul _)

/-- Summing the termwise bound shows that the finite partition function has
at most the number of magnetisation types, namely `population + 1`. -/
theorem finiteCWPartition_le_typeCount_of_subcritical
    (population : ℕ) (tlam : ℝ) (hcritical : tlam ≤ 1) :
    finiteCWPartition population tlam ≤ population + 1 := by
  rw [← finiteCWTypeMass_sum]
  calc
    (∑ upSpins ∈ Finset.range (population + 1),
        finiteCWTypeMass population tlam upSpins) ≤
        ∑ _upSpins ∈ Finset.range (population + 1), (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro upSpins hupSpins
      exact finiteCWTypeMass_le_one_of_subcritical population upSpins tlam
        hcritical hupSpins
    _ = population + 1 := by simp

/-- The whole finite partition function is at most the number of
magnetisation types times the exponential variational pressure. -/
theorem finiteCWPartition_le_typeCount_mul_expVariational
    (population : ℕ) (tlam : ℝ) :
    finiteCWPartition population tlam ≤
      (population + 1 : ℕ) *
        Real.exp ((population : ℝ) * cwVariationalPressureGap tlam) := by
  rw [← finiteCWTypeMass_sum]
  calc
    (∑ upSpins ∈ Finset.range (population + 1),
        finiteCWTypeMass population tlam upSpins) ≤
        ∑ _upSpins ∈ Finset.range (population + 1),
          Real.exp ((population : ℝ) * cwVariationalPressureGap tlam) := by
      apply Finset.sum_le_sum
      intro upSpins hupSpins
      exact finiteCWTypeMass_le_exp_variationalPressure population upSpins
        tlam hupSpins
    _ = (population + 1 : ℕ) *
        Real.exp ((population : ℝ) * cwVariationalPressureGap tlam) := by
      simp

/-- At every positive population, the finite pressure exceeds the
variational pressure by at most the normalized logarithm of the number of
types. -/
theorem finiteCWPressureGap_le_variational_add_typeCount
    (population : ℕ) (tlam : ℝ) (hpopulation : 0 < population) :
    finiteCWPressureGap population tlam ≤
      cwVariationalPressureGap tlam +
        Real.log ((population : ℝ) + 1) / (population : ℝ) := by
  have hpopulationReal : (0 : ℝ) < population := by exact_mod_cast hpopulation
  have htypeCountPositive : (0 : ℝ) < population + 1 := by positivity
  have hpartitionPositive : 0 < finiteCWPartition population tlam := by
    rw [← finiteCWTypeMass_sum]
    exact Finset.sum_pos
      (fun upSpins hupSpins ↦
        finiteCWTypeMass_pos population upSpins tlam hupSpins)
      ⟨0, by simp⟩
  have hpartitionUpper : finiteCWPartition population tlam ≤
      ((population : ℝ) + 1) *
        Real.exp ((population : ℝ) * cwVariationalPressureGap tlam) := by
    simpa [Nat.cast_add] using
      finiteCWPartition_le_typeCount_mul_expVariational population tlam
  have hlogUpper : Real.log (finiteCWPartition population tlam) ≤
      Real.log (((population : ℝ) + 1) *
        Real.exp ((population : ℝ) * cwVariationalPressureGap tlam)) :=
    Real.log_le_log hpartitionPositive hpartitionUpper
  rw [finiteCWPressureGap]
  apply (div_le_iff₀ hpopulationReal).mpr
  calc
    Real.log (finiteCWPartition population tlam) ≤
        Real.log (((population : ℝ) + 1) *
          Real.exp ((population : ℝ) * cwVariationalPressureGap tlam)) :=
      hlogUpper
    _ = Real.log ((population : ℝ) + 1) +
        (population : ℝ) * cwVariationalPressureGap tlam := by
      rw [Real.log_mul htypeCountPositive.ne' (Real.exp_ne_zero _), Real.log_exp]
    _ = (cwVariationalPressureGap tlam +
        Real.log ((population : ℝ) + 1) / population) * population := by
      field_simp
      ring

/-- Nonnegative coupling can only increase the normalized Rademacher
partition function above its exactly normalized zero-coupling value. -/
theorem finiteCWPartition_one_le_of_nonnegative
    (population : ℕ) (tlam : ℝ) (htlam : 0 ≤ tlam) :
    1 ≤ finiteCWPartition population tlam := by
  have hzeroPartition : finiteCWPartition population 0 = 1 := by
    have hsum :
        (∑ upSpins ∈ Finset.range (population + 1),
          (Nat.choose population upSpins : ℝ)) = (2 : ℝ) ^ population := by
      exact_mod_cast Nat.sum_range_choose population
    simp [finiteCWPartition, hsum]
  rw [← hzeroPartition]
  unfold finiteCWPartition
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Finset.sum_le_sum
  intro upSpins _hupSpins
  have henergy : 0 ≤ tlam / (2 * (population : ℝ)) *
      finiteCWMagnetization population upSpins ^ 2 := by
    positivity
  have hexp : 1 ≤ Real.exp
      (tlam / (2 * (population : ℝ)) *
        finiteCWMagnetization population upSpins ^ 2) :=
    Real.one_le_exp henergy
  simp only [zero_div, zero_mul, Real.exp_zero, mul_one]
  have hchoose : 0 ≤ (Nat.choose population upSpins : ℝ) := Nat.cast_nonneg _
  simpa using mul_le_mul_of_nonneg_left hexp hchoose

/-- The genuine finite-volume pressure is squeezed between zero and the log
number of magnetisation types throughout the subcritical/critical regime. -/
theorem finiteCWPressureGap_subcritical_bounds
    (population : ℕ) (tlam : ℝ) (hpopulation : 0 < population)
    (htlam : 0 ≤ tlam) (hcritical : tlam ≤ 1) :
    0 ≤ finiteCWPressureGap population tlam ∧
      finiteCWPressureGap population tlam ≤
        Real.log (population + 1) / population := by
  have hpopulationReal : (0 : ℝ) < population := by exact_mod_cast hpopulation
  have hpartitionLower :=
    finiteCWPartition_one_le_of_nonnegative population tlam htlam
  have hpartitionUpper :=
    finiteCWPartition_le_typeCount_of_subcritical population tlam hcritical
  have hpartitionPositive : 0 < finiteCWPartition population tlam :=
    lt_of_lt_of_le zero_lt_one hpartitionLower
  constructor
  · unfold finiteCWPressureGap
    exact div_nonneg (Real.log_nonneg hpartitionLower) hpopulationReal.le
  · unfold finiteCWPressureGap
    exact div_le_div_of_nonneg_right
      (Real.log_le_log hpartitionPositive hpartitionUpper) hpopulationReal.le

/-- The normalized logarithm of the number of Curie--Weiss types vanishes.
The proof factors the shifted ratio into `log x / x` and a shift ratio tending
to one. -/
theorem finiteCWTypeCount_log_div_tendsto_zero :
    Filter.Tendsto
      (fun population : ℕ ↦
        Real.log (((population + 2 : ℕ) : ℝ)) /
          ((population + 1 : ℕ) : ℝ))
      Filter.atTop (nhds 0) := by
  have hshiftTwo : Filter.Tendsto
      (fun population : ℕ ↦ ((population + 2 : ℕ) : ℝ))
      Filter.atTop Filter.atTop := by
    convert (tendsto_natCast_atTop_atTop (R := ℝ)).comp
      (Filter.tendsto_add_atTop_nat 2) using 1
  have hshiftOne : Filter.Tendsto
      (fun population : ℕ ↦ ((population + 1 : ℕ) : ℝ))
      Filter.atTop Filter.atTop := by
    convert (tendsto_natCast_atTop_atTop (R := ℝ)).comp
      (Filter.tendsto_add_atTop_nat 1) using 1
  have hlogDivReal : Filter.Tendsto
      (fun x : ℝ ↦ Real.log x / x) Filter.atTop (nhds 0) := by
    simpa only [id_eq] using
      Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have hlogDivShift : Filter.Tendsto
      (fun population : ℕ ↦
        Real.log (((population + 2 : ℕ) : ℝ)) /
          ((population + 2 : ℕ) : ℝ))
      Filter.atTop (nhds 0) :=
    hlogDivReal.comp hshiftTwo
  have hinvShiftOne : Filter.Tendsto
      (fun population : ℕ ↦ (((population + 1 : ℕ) : ℝ))⁻¹)
      Filter.atTop (nhds 0) :=
    hshiftOne.inv_tendsto_atTop
  have hshiftRatio : Filter.Tendsto
      (fun population : ℕ ↦
        ((population + 2 : ℕ) : ℝ) /
          ((population + 1 : ℕ) : ℝ))
      Filter.atTop (nhds 1) := by
    have hone : Filter.Tendsto (fun _population : ℕ ↦ (1 : ℝ))
        Filter.atTop (nhds 1) := tendsto_const_nhds
    have hadd := hone.add hinvShiftOne
    convert hadd using 1
    · funext population
      have hdenominator : (((population + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
      push_cast
      field_simp
      ring
    · norm_num
  have hproduct := hlogDivShift.mul hshiftRatio
  convert hproduct using 1
  · funext population
    have hpositiveOne : (0 : ℝ) < population + 1 := by positivity
    have hpositiveTwo : (0 : ℝ) < population + 2 := by positivity
    field_simp
  · norm_num

/-- **Exact finite-pressure subcritical limit.**  At every nonnegative
coupling at or below the Curie--Weiss threshold, the genuine normalized
finite-volume pressure converges to zero. -/
theorem finiteCWPressureGap_tendsto_zero_of_subcritical
    (tlam : ℝ) (htlam : 0 ≤ tlam) (hcritical : tlam ≤ 1) :
    Filter.Tendsto
      (fun population : ℕ ↦ finiteCWPressureGap (population + 1) tlam)
      Filter.atTop (nhds 0) := by
  have hnonnegative : ∀ population : ℕ,
      0 ≤ finiteCWPressureGap (population + 1) tlam := by
    intro population
    exact (finiteCWPressureGap_subcritical_bounds (population + 1) tlam
      (Nat.succ_pos population) htlam hcritical).1
  have hupper : ∀ population : ℕ,
      finiteCWPressureGap (population + 1) tlam ≤
        Real.log (((population + 2 : ℕ) : ℝ)) /
          ((population + 1 : ℕ) : ℝ) := by
    intro population
    have hbound := (finiteCWPressureGap_subcritical_bounds (population + 1) tlam
      (Nat.succ_pos population) htlam hcritical).2
    convert hbound using 1
    all_goals norm_num [Nat.cast_add]
    all_goals ring
  exact squeeze_zero hnonnegative hupper finiteCWTypeCount_log_div_tendsto_zero

/-- **Finite-volume Curie--Weiss variational lower bound.**  Every interior
magnetisation supplies its variational objective as a lower bound for the
genuine normalized finite Rademacher pressure.  The proof is an exact biased
binomial change of measure plus Jensen; it uses neither Stirling asymptotics
nor an LDP. -/
theorem finiteCWPressureGap_ge_cwObjective
    (population : ℕ) (tlam m : ℝ)
    (hpopulation : 0 < population) (htlam : 0 ≤ tlam) (hm : |m| < 1) :
    cwObjective tlam m ≤ finiteCWPressureGap population tlam := by
  let indices := Finset.range (population + 1)
  let q := cwPositiveTrialWeight m
  let r := cwNegativeTrialWeight m
  let weight := fun upSpins ↦ biasedBinomialTypeWeight population q r upSpins
  let mass := finiteCWTypeMass population tlam
  let magnetization := finiteCWMagnetization population
  let energyScale := tlam / (2 * (population : ℝ))
  have hindices : indices.Nonempty := ⟨0, by simp [indices]⟩
  have hweightPositive : ∀ upSpins ∈ indices, 0 < weight upSpins := by
    intro upSpins hupSpins
    exact biasedBinomialTypeWeight_pos population upSpins m hm hupSpins
  have hmassPositive : ∀ upSpins ∈ indices, 0 < mass upSpins := by
    intro upSpins hupSpins
    exact finiteCWTypeMass_pos population upSpins tlam hupSpins
  have hweightSum : (∑ upSpins ∈ indices, weight upSpins) = 1 :=
    biasedBinomialTypeWeight_sum population q r (cwTrialWeights_sum m)
  have hfirstMoment :
      (∑ upSpins ∈ indices, weight upSpins * upSpins) = population * q :=
    biasedBinomialTypeWeight_firstMoment population q r (cwTrialWeights_sum m)
  have hdownMoment :
      (∑ upSpins ∈ indices, weight upSpins * (population - upSpins)) =
        population * r :=
    biasedBinomialTypeWeight_downSpinMean population m
  have hsecondMoment :
      ((population : ℝ) * m) ^ 2 ≤
        ∑ upSpins ∈ indices, weight upSpins * magnetization upSpins ^ 2 :=
    biasedBinomialTypeWeight_magnetizationSecondMoment population m hm
  have hvariational :
      (∑ upSpins ∈ indices,
          weight upSpins * Real.log (mass upSpins / weight upSpins)) ≤
        Real.log (finiteCWPartition population tlam) := by
    have h := finiteLogSum_ge_weightedLogRatio indices weight mass hindices
      hweightPositive hmassPositive hweightSum
    rw [show (∑ upSpins ∈ indices, mass upSpins) =
        finiteCWPartition population tlam by
      exact finiteCWTypeMass_sum population tlam] at h
    exact h
  have henergy :
      (∑ upSpins ∈ indices,
        weight upSpins * (energyScale * magnetization upSpins ^ 2)) =
        energyScale *
          ∑ upSpins ∈ indices, weight upSpins * magnetization upSpins ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro upSpins _hupSpins
    ring
  have hbaselineEntropy :
      (∑ upSpins ∈ indices,
        weight upSpins * (population * Real.log 2)) =
        population * Real.log 2 := by
    rw [← Finset.sum_mul, hweightSum]
    ring
  have hpositiveEntropy :
      (∑ upSpins ∈ indices,
        weight upSpins * (upSpins * Real.log q)) =
        (population * q) * Real.log q := by
    calc
      (∑ upSpins ∈ indices,
        weight upSpins * (upSpins * Real.log q)) =
          (∑ upSpins ∈ indices, weight upSpins * upSpins) * Real.log q := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro upSpins _hupSpins
        ring
      _ = _ := by rw [hfirstMoment]
  have hnegativeEntropy :
      (∑ upSpins ∈ indices,
        weight upSpins * ((population - upSpins) * Real.log r)) =
        (population * r) * Real.log r := by
    calc
      (∑ upSpins ∈ indices,
        weight upSpins * ((population - upSpins) * Real.log r)) =
          (∑ upSpins ∈ indices,
            weight upSpins * (population - upSpins)) * Real.log r := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro upSpins _hupSpins
        ring
      _ = _ := by rw [hdownMoment]
  have hweightedIdentity :
      (∑ upSpins ∈ indices,
          weight upSpins * Real.log (mass upSpins / weight upSpins)) =
        energyScale *
            ∑ upSpins ∈ indices, weight upSpins * magnetization upSpins ^ 2 -
          population * Real.log 2 -
          (population * q) * Real.log q -
          (population * r) * Real.log r := by
    calc
      (∑ upSpins ∈ indices,
          weight upSpins * Real.log (mass upSpins / weight upSpins)) =
          ∑ upSpins ∈ indices,
            weight upSpins *
              (energyScale * magnetization upSpins ^ 2 -
                population * Real.log 2 -
                upSpins * Real.log q -
                (population - upSpins) * Real.log r) := by
        apply Finset.sum_congr rfl
        intro upSpins hupSpins
        rw [finiteCWTypeMass_logRatio population upSpins tlam m hm hupSpins]
      _ =
          (∑ upSpins ∈ indices,
            weight upSpins * (energyScale * magnetization upSpins ^ 2)) -
          (∑ upSpins ∈ indices,
            weight upSpins * (population * Real.log 2)) -
          (∑ upSpins ∈ indices,
            weight upSpins * (upSpins * Real.log q)) -
          ∑ upSpins ∈ indices,
            weight upSpins * ((population - upSpins) * Real.log r) := by
        repeat' rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro upSpins _hupSpins
        ring
      _ = _ := by
        rw [henergy, hbaselineEntropy, hpositiveEntropy, hnegativeEntropy]
  have hpopulationReal : (0 : ℝ) < population := by exact_mod_cast hpopulation
  have henergyScaleNonnegative : 0 ≤ energyScale := by
    dsimp [energyScale]
    positivity
  have htrialLower :
      (population : ℝ) * cwObjective tlam m ≤
        ∑ upSpins ∈ indices,
          weight upSpins * Real.log (mass upSpins / weight upSpins) := by
    rw [hweightedIdentity]
    have henergyLower :=
      mul_le_mul_of_nonneg_left hsecondMoment henergyScaleNonnegative
    calc
      (population : ℝ) * cwObjective tlam m =
          energyScale * (((population : ℝ) * m) ^ 2) -
            population * Real.log 2 -
            (population * q) * Real.log q -
            (population * r) * Real.log r := by
        unfold cwObjective
        dsimp [q, r]
        rw [← cwTrialEntropy_eq_rate hm]
        dsimp [energyScale]
        field_simp [hpopulationReal.ne']
        ring
      _ ≤ energyScale *
            ∑ upSpins ∈ indices,
              weight upSpins * magnetization upSpins ^ 2 -
            population * Real.log 2 -
            (population * q) * Real.log q -
            (population * r) * Real.log r := by linarith
  rw [finiteCWPressureGap]
  apply (le_div_iff₀ hpopulationReal).mpr
  exact (by simpa [mul_comm] using htrialLower.trans hvariational)

/-- The genuine finite pressure is strictly positive at every nonzero
population throughout the complete supercritical regime `1 < tlam`. -/
theorem finiteCWPressureGap_pos_of_supercritical
    (population : ℕ) (tlam : ℝ)
    (hpopulation : 0 < population) (hcritical : 1 < tlam) :
    0 < finiteCWPressureGap population tlam := by
  obtain ⟨m, hm, hobjective⟩ := curieWeiss_supercritical tlam hcritical
  exact hobjective.trans_le
    (finiteCWPressureGap_ge_cwObjective population tlam m hpopulation
      (le_trans (by norm_num) hcritical.le) hm)

/-- One interior variational witness gives a positive population-uniform lower
bound on the genuine finite pressure at every supercritical coupling. -/
theorem finiteCWPressureGap_supercritical_uniformWitness
    (tlam : ℝ) (hcritical : 1 < tlam) :
    ∃ m : ℝ, |m| < 1 ∧ 0 < cwObjective tlam m ∧
      ∀ population : ℕ, 0 < population →
        cwObjective tlam m ≤ finiteCWPressureGap population tlam := by
  obtain ⟨m, hm, hobjective⟩ := curieWeiss_supercritical tlam hcritical
  exact ⟨m, hm, hobjective, fun population hpopulation ↦
    finiteCWPressureGap_ge_cwObjective population tlam m hpopulation
      (le_trans (by norm_num) hcritical.le) hm⟩

/-- Hence the actual finite pressure gap cannot converge to zero anywhere in
the full supercritical regime. -/
theorem finiteCWPressureGap_not_tendsto_zero_of_supercritical
    (tlam : ℝ) (hcritical : 1 < tlam) :
    ¬ Filter.Tendsto
      (fun population : ℕ ↦ finiteCWPressureGap (population + 1) tlam)
      Filter.atTop (nhds 0) := by
  obtain ⟨m, hm, hobjective, hlower⟩ :=
    finiteCWPressureGap_supercritical_uniformWitness tlam hcritical
  intro hzero
  have hbelow : ∀ᶠ population in Filter.atTop,
      finiteCWPressureGap (population + 1) tlam < cwObjective tlam m :=
    hzero.eventually_lt_const hobjective
  obtain ⟨population, hpopulation⟩ := Filter.eventually_atTop.mp hbelow
  have hlt := hpopulation population le_rfl
  exact (not_lt_of_ge (hlower (population + 1) (Nat.succ_pos population))) hlt

/-- **Exact phase boundary for the actual finite-volume pressure sequence.**
For nonnegative coupling, convergence of the normalized pressure gap to zero
is equivalent to lying at or below the Curie--Weiss threshold.  The reverse
direction uses the population-uniform interior witness, not an unproved
thermodynamic-limit identification. -/
theorem finiteCWPressureGap_tendsto_zero_iff
    (tlam : ℝ) (htlam : 0 ≤ tlam) :
    Filter.Tendsto
        (fun population : ℕ ↦ finiteCWPressureGap (population + 1) tlam)
        Filter.atTop (nhds 0) ↔
      tlam ≤ 1 := by
  constructor
  · intro hzero
    by_contra hcritical
    exact finiteCWPressureGap_not_tendsto_zero_of_supercritical tlam
      (lt_of_not_ge hcritical) hzero
  · intro hcritical
    exact finiteCWPressureGap_tendsto_zero_of_subcritical tlam htlam hcritical

/-- At zero coupling the binomially grouped partition function is normalized
to one.  This also verifies that the `2^population` denominator is the genuine
uniform Rademacher normalization. -/
@[simp] theorem finiteCWPartition_zero (population : ℕ) :
    finiteCWPartition population 0 = 1 := by
  have hsum :
      (∑ upSpins ∈ Finset.range (population + 1),
        (Nat.choose population upSpins : ℝ)) = (2 : ℝ) ^ population := by
    exact_mod_cast Nat.sum_range_choose population
  simp [finiteCWPartition, hsum]

/-- Consequently the finite-volume pressure gap vanishes at zero coupling. -/
@[simp] theorem finiteCWPressureGap_zero (population : ℕ) :
    finiteCWPressureGap population 0 = 0 := by
  simp [finiteCWPressureGap]

/-- The fully aligned type has magnetisation exactly the population size. -/
@[simp] theorem finiteCWMagnetization_aligned (population : ℕ) :
    finiteCWMagnetization population population = population := by
  simp [finiteCWMagnetization]
  ring

/-- One fully aligned Rademacher state supplies an explicit lower bound on the
whole finite partition function. -/
theorem finiteCWPartition_aligned_lower_bound
    (population : ℕ) (tlam : ℝ) (hpopulation : 0 < population) :
    ((2 : ℝ) ^ population)⁻¹ *
        Real.exp (tlam * population / 2) ≤
      finiteCWPartition population tlam := by
  have htermNonnegative : ∀ upSpins ∈ Finset.range (population + 1),
      0 ≤ (Nat.choose population upSpins : ℝ) *
        Real.exp
          (tlam / (2 * (population : ℝ)) *
            finiteCWMagnetization population upSpins ^ 2) := by
    intro upSpins _hupSpins
    positivity
  have halignedMem : population ∈ Finset.range (population + 1) := by
    simp
  have halignedTerm :
      (Nat.choose population population : ℝ) *
          Real.exp
            (tlam / (2 * (population : ℝ)) *
              finiteCWMagnetization population population ^ 2) ≤
        ∑ upSpins ∈ Finset.range (population + 1),
          (Nat.choose population upSpins : ℝ) *
            Real.exp
              (tlam / (2 * (population : ℝ)) *
                finiteCWMagnetization population upSpins ^ 2) :=
    Finset.single_le_sum htermNonnegative halignedMem
  have hpopulationReal : (population : ℝ) ≠ 0 := by
    exact_mod_cast hpopulation.ne'
  have hnormalizedTerm :
      (Nat.choose population population : ℝ) *
          Real.exp
            (tlam / (2 * (population : ℝ)) *
              finiteCWMagnetization population population ^ 2) =
        Real.exp (tlam * population / 2) := by
    simp [finiteCWMagnetization]
    field_simp
    ring
  rw [finiteCWPartition, ← hnormalizedTerm]
  exact mul_le_mul_of_nonneg_left halignedTerm (by positivity)

/-- The finite Rademacher partition function is strictly positive at every
population size and coupling, so its logarithm never uses the nonpositive junk
branch of `Real.log`. -/
theorem finiteCWPartition_pos (population : ℕ) (tlam : ℝ) :
    0 < finiteCWPartition population tlam := by
  by_cases hzero : population = 0
  · subst population
    simp [finiteCWPartition]
  · have hpopulation : 0 < population := Nat.pos_of_ne_zero hzero
    exact (show
        0 < ((2 : ℝ) ^ population)⁻¹ *
          Real.exp (tlam * population / 2) by positivity).trans_le
      (finiteCWPartition_aligned_lower_bound population tlam hpopulation)

/-- Typewise coupling comparison: changing coupling from `right` to `left`
costs at most the maximal energy factor `exp (population * |left-right| / 2)`. -/
theorem finiteCWTypeMass_le_exp_half_abs_mul_typeMass
    (population upSpins : ℕ) (left right : ℝ)
    (hpopulation : 0 < population)
    (hupSpins : upSpins ∈ Finset.range (population + 1)) :
    finiteCWTypeMass population left upSpins ≤
      Real.exp (|left - right| * population / 2) *
        finiteCWTypeMass population right upSpins := by
  let magnetization := finiteCWMagnetization population upSpins
  have hpopulationReal : (0 : ℝ) < population := by exact_mod_cast hpopulation
  have hmagnetization : magnetization ^ 2 ≤ (population : ℝ) ^ 2 :=
    finiteCWMagnetization_sq_le_population_sq population upSpins hupSpins
  have hdiff : left - right ≤ |left - right| := le_abs_self _
  have hscale : 0 ≤ magnetization ^ 2 / (2 * (population : ℝ)) := by
    positivity
  have hfirst : (left - right) *
      (magnetization ^ 2 / (2 * (population : ℝ))) ≤
      |left - right| *
        (magnetization ^ 2 / (2 * (population : ℝ))) :=
    mul_le_mul_of_nonneg_right hdiff hscale
  have hsecond : |left - right| / (2 * (population : ℝ)) *
      magnetization ^ 2 ≤ |left - right| * population / 2 := by
    have hmul := mul_le_mul_of_nonneg_left hmagnetization
      (show 0 ≤ |left - right| / (2 * (population : ℝ)) by positivity)
    calc
      |left - right| / (2 * (population : ℝ)) * magnetization ^ 2 ≤
          |left - right| / (2 * (population : ℝ)) *
            (population : ℝ) ^ 2 := hmul
      _ = |left - right| * population / 2 := by
        field_simp
  have henergy : left / (2 * (population : ℝ)) * magnetization ^ 2 ≤
      |left - right| * population / 2 +
        right / (2 * (population : ℝ)) * magnetization ^ 2 := by
    calc
      left / (2 * (population : ℝ)) * magnetization ^ 2 =
          right / (2 * (population : ℝ)) * magnetization ^ 2 +
            (left - right) *
              (magnetization ^ 2 / (2 * (population : ℝ))) := by ring
      _ ≤ right / (2 * (population : ℝ)) * magnetization ^ 2 +
            |left - right| *
              (magnetization ^ 2 / (2 * (population : ℝ))) :=
        add_le_add_left hfirst _
      _ ≤ right / (2 * (population : ℝ)) * magnetization ^ 2 +
            |left - right| * population / 2 :=
        add_le_add_left (by
          calc
            |left - right| *
                (magnetization ^ 2 / (2 * (population : ℝ))) =
                |left - right| / (2 * (population : ℝ)) *
                  magnetization ^ 2 := by ring
            _ ≤ |left - right| * population / 2 := hsecond) _
      _ = _ := by ring
  have hexponential : Real.exp
      (left / (2 * (population : ℝ)) * magnetization ^ 2) ≤
      Real.exp (|left - right| * population / 2) *
        Real.exp (right / (2 * (population : ℝ)) * magnetization ^ 2) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr henergy
  unfold finiteCWTypeMass
  dsimp [magnetization] at hexponential ⊢
  calc
    ((2 : ℝ) ^ population)⁻¹ * (Nat.choose population upSpins : ℝ) *
        Real.exp (left / (2 * (population : ℝ)) *
          finiteCWMagnetization population upSpins ^ 2) ≤
      ((2 : ℝ) ^ population)⁻¹ * (Nat.choose population upSpins : ℝ) *
        (Real.exp (|left - right| * population / 2) *
          Real.exp (right / (2 * (population : ℝ)) *
            finiteCWMagnetization population upSpins ^ 2)) :=
      mul_le_mul_of_nonneg_left hexponential (by positivity)
    _ = Real.exp (|left - right| * population / 2) *
        (((2 : ℝ) ^ population)⁻¹ * (Nat.choose population upSpins : ℝ) *
          Real.exp (right / (2 * (population : ℝ)) *
            finiteCWMagnetization population upSpins ^ 2)) := by ring

/-- Each finite type mass is monotone in coupling because its squared
magnetisation energy is nonnegative. -/
theorem finiteCWTypeMass_mono_coupling
    (population upSpins : ℕ) {left right : ℝ}
    (hpopulation : 0 < population) (hle : left ≤ right) :
    finiteCWTypeMass population left upSpins ≤
      finiteCWTypeMass population right upSpins := by
  have hpopulationReal : (0 : ℝ) < population := by exact_mod_cast hpopulation
  unfold finiteCWTypeMass
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_right hle (by positivity)) (sq_nonneg _)

/-- Summing the typewise comparison gives the corresponding exact partition
function comparison. -/
theorem finiteCWPartition_le_exp_half_abs_mul_partition
    (population : ℕ) (left right : ℝ) (hpopulation : 0 < population) :
    finiteCWPartition population left ≤
      Real.exp (|left - right| * population / 2) *
        finiteCWPartition population right := by
  rw [← finiteCWTypeMass_sum, ← finiteCWTypeMass_sum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro upSpins hupSpins
  exact finiteCWTypeMass_le_exp_half_abs_mul_typeMass
    population upSpins left right hpopulation hupSpins

/-- The finite partition function is monotone in coupling. -/
theorem finiteCWPartition_mono_coupling
    (population : ℕ) {left right : ℝ}
    (hpopulation : 0 < population) (hle : left ≤ right) :
    finiteCWPartition population left ≤ finiteCWPartition population right := by
  rw [← finiteCWTypeMass_sum, ← finiteCWTypeMass_sum]
  apply Finset.sum_le_sum
  intro upSpins _hupSpins
  exact finiteCWTypeMass_mono_coupling population upSpins hpopulation hle

/-- One-sided finite pressure comparison in coupling. -/
theorem finiteCWPressureGap_sub_le_half_abs
    (population : ℕ) (left right : ℝ) (hpopulation : 0 < population) :
    finiteCWPressureGap population left - finiteCWPressureGap population right ≤
      |left - right| / 2 := by
  have hpartition := finiteCWPartition_le_exp_half_abs_mul_partition
    population left right hpopulation
  have hlog := Real.log_le_log (finiteCWPartition_pos population left)
    hpartition
  rw [Real.log_mul (Real.exp_ne_zero _)
      (finiteCWPartition_pos population right).ne', Real.log_exp] at hlog
  have hpopulationReal : (0 : ℝ) < population := by exact_mod_cast hpopulation
  rw [finiteCWPressureGap, finiteCWPressureGap]
  calc
    Real.log (finiteCWPartition population left) / population -
        Real.log (finiteCWPartition population right) / population =
      (Real.log (finiteCWPartition population left) -
        Real.log (finiteCWPartition population right)) / population := by ring
    _ ≤ (|left - right| * population / 2) / population :=
      div_le_div_of_nonneg_right (by linarith) hpopulationReal.le
    _ = |left - right| / 2 := by
      field_simp

/-- **Exact finite-volume regularity.**  At every positive population, the
normalized Curie--Weiss pressure is globally `1/2`-Lipschitz in coupling. -/
theorem finiteCWPressureGap_abs_sub_le_half_abs
    (population : ℕ) (left right : ℝ) (hpopulation : 0 < population) :
    |finiteCWPressureGap population left - finiteCWPressureGap population right| ≤
      |left - right| / 2 := by
  rw [abs_le]
  constructor
  · have hreverse := finiteCWPressureGap_sub_le_half_abs
      population right left hpopulation
    rw [abs_sub_comm] at hreverse
    linarith
  · exact finiteCWPressureGap_sub_le_half_abs population left right hpopulation

/-- Bundled finite-volume half-Lipschitz regularity. -/
theorem finiteCWPressureGap_lipschitzWith
    (population : ℕ) (hpopulation : 0 < population) :
    LipschitzWith (⟨1 / 2, by norm_num⟩ : NNReal)
      (finiteCWPressureGap population) := by
  apply LipschitzWith.of_dist_le_mul
  intro left right
  rw [Real.dist_eq, Real.dist_eq]
  simpa [abs_sub_comm, mul_comm] using
    finiteCWPressureGap_abs_sub_le_half_abs population left right hpopulation

/-- Every positive finite-volume pressure is monotone in coupling. -/
theorem monotone_finiteCWPressureGap
    (population : ℕ) (hpopulation : 0 < population) :
    Monotone (finiteCWPressureGap population) := by
  intro left right hle
  have hpartition := finiteCWPartition_mono_coupling population hpopulation hle
  have hlog := Real.log_le_log (finiteCWPartition_pos population left) hpartition
  unfold finiteCWPressureGap
  exact div_le_div_of_nonneg_right hlog (by positivity)

/-- The aligned-state contribution gives a finite-volume lower bound with no
large-deviation or Varadhan premise. -/
theorem finiteCWPressureGap_ge_aligned
    (population : ℕ) (tlam : ℝ) (hpopulation : 0 < population) :
    tlam / 2 - Real.log 2 ≤ finiteCWPressureGap population tlam := by
  have hbasePositive :
      0 < ((2 : ℝ) ^ population)⁻¹ * Real.exp (tlam * population / 2) := by
    positivity
  have hpartitionBound :=
    finiteCWPartition_aligned_lower_bound population tlam hpopulation
  have hlogBound :
      Real.log (((2 : ℝ) ^ population)⁻¹ *
          Real.exp (tlam * population / 2)) ≤
        Real.log (finiteCWPartition population tlam) :=
    Real.log_le_log hbasePositive hpartitionBound
  have hpopulationReal : (0 : ℝ) < population := by
    exact_mod_cast hpopulation
  rw [finiteCWPressureGap]
  apply (le_div_iff₀ hpopulationReal).mpr
  calc
    (tlam / 2 - Real.log 2) * population =
        tlam * population / 2 - population * Real.log 2 := by ring
    _ = Real.log (((2 : ℝ) ^ population)⁻¹ *
        Real.exp (tlam * population / 2)) := by
      rw [Real.log_mul (by positivity) (Real.exp_ne_zero _),
        Real.log_inv, Real.log_pow, Real.log_exp]
      ring
    _ ≤ Real.log (finiteCWPartition population tlam) := hlogBound

/-- The genuine finite pressure dominates the complete variational supremum
at every positive population and nonnegative coupling.  Interior objective
values use the finite Gibbs inequality; both endpoints use the exact aligned
state contribution. -/
theorem cwVariationalPressureGap_le_finiteCWPressureGap
    (population : ℕ) (tlam : ℝ)
    (hpopulation : 0 < population) (htlam : 0 ≤ tlam) :
    cwVariationalPressureGap tlam ≤ finiteCWPressureGap population tlam := by
  unfold cwVariationalPressureGap
  apply csSup_le (cwPressureValueSet_nonempty tlam)
  intro value hvalue
  rcases hvalue with ⟨m, hm, rfl⟩
  by_cases hnegative : m = -1
  · subst m
    simpa [cwObjective_at_neg_one] using
      finiteCWPressureGap_ge_aligned population tlam hpopulation
  · by_cases hpositive : m = 1
    · subst m
      simpa [cwObjective_at_one] using
        finiteCWPressureGap_ge_aligned population tlam hpopulation
    · have hstrictLower : -1 < m :=
        lt_of_le_of_ne hm.1 (Ne.symm hnegative)
      have hstrictUpper : m < 1 :=
        lt_of_le_of_ne hm.2 hpositive
      exact finiteCWPressureGap_ge_cwObjective population tlam m hpopulation
        htlam ((abs_lt).2 ⟨hstrictLower, hstrictUpper⟩)

/-- The complete finite-to-variational squeeze: the only discrepancy is at
most the logarithm of the number of magnetisation types divided by population. -/
theorem finiteCWPressureGap_variational_bounds
    (population : ℕ) (tlam : ℝ)
    (hpopulation : 0 < population) (htlam : 0 ≤ tlam) :
    cwVariationalPressureGap tlam ≤ finiteCWPressureGap population tlam ∧
      finiteCWPressureGap population tlam ≤
        cwVariationalPressureGap tlam +
          Real.log (population + 1) / population :=
  ⟨cwVariationalPressureGap_le_finiteCWPressureGap population tlam
      hpopulation htlam,
    finiteCWPressureGap_le_variational_add_typeCount population tlam hpopulation⟩

/-- The finite pressure approximation has an explicit coupling-independent
absolute error. -/
theorem finiteCWPressureGap_abs_sub_variational_le_typeCount
    (population : ℕ) (tlam : ℝ)
    (hpopulation : 0 < population) (htlam : 0 ≤ tlam) :
    |finiteCWPressureGap population tlam - cwVariationalPressureGap tlam| ≤
      Real.log (population + 1) / population := by
  obtain ⟨hlower, hupper⟩ :=
    finiteCWPressureGap_variational_bounds population tlam hpopulation htlam
  rw [abs_of_nonneg (sub_nonneg.mpr hlower)]
  linarith

/-- **Full thermodynamic-limit identification.**  For every nonnegative
coupling, the genuine finite Rademacher pressure converges to the supremal
Curie--Weiss variational pressure.  The proof is a finite type-count squeeze;
no LDP, Stirling formula, or Varadhan lemma is assumed. -/
theorem finiteCWPressureGap_tendsto_variationalPressure
    (tlam : ℝ) (htlam : 0 ≤ tlam) :
    Filter.Tendsto
      (fun population : ℕ ↦ finiteCWPressureGap (population + 1) tlam)
      Filter.atTop (nhds (cwVariationalPressureGap tlam)) := by
  have herrorNonnegative : ∀ population : ℕ,
      0 ≤ finiteCWPressureGap (population + 1) tlam -
        cwVariationalPressureGap tlam := by
    intro population
    exact sub_nonneg.mpr
      (cwVariationalPressureGap_le_finiteCWPressureGap (population + 1) tlam
        (Nat.succ_pos population) htlam)
  have herrorUpper : ∀ population : ℕ,
      finiteCWPressureGap (population + 1) tlam -
          cwVariationalPressureGap tlam ≤
        Real.log (((population + 2 : ℕ) : ℝ)) /
          ((population + 1 : ℕ) : ℝ) := by
    intro population
    have hupper := finiteCWPressureGap_le_variational_add_typeCount
      (population + 1) tlam (Nat.succ_pos population)
    have hraw : finiteCWPressureGap (population + 1) tlam -
        cwVariationalPressureGap tlam ≤
          Real.log (((population + 1 : ℕ) : ℝ) + 1) /
            ((population + 1 : ℕ) : ℝ) :=
      sub_le_iff_le_add.mpr (by simpa [add_comm] using hupper)
    convert hraw using 1
    all_goals norm_num [Nat.cast_add]
    all_goals ring
  have herror : Filter.Tendsto
      (fun population : ℕ ↦ finiteCWPressureGap (population + 1) tlam -
        cwVariationalPressureGap tlam)
      Filter.atTop (nhds 0) :=
    squeeze_zero herrorNonnegative herrorUpper
      finiteCWTypeCount_log_div_tendsto_zero
  have hconstant : Filter.Tendsto
      (fun _population : ℕ ↦ cwVariationalPressureGap tlam)
      Filter.atTop (nhds (cwVariationalPressureGap tlam)) :=
    tendsto_const_nhds
  convert hconstant.add herror using 1 <;> simp [add_comm]

/-- **Uniform thermodynamic-limit identification on the whole positive
cone.**  Because the type-count error is independent of coupling, finite
Curie--Weiss pressure converges uniformly to the variational pressure on the
entire half-line `[0,∞)`, not merely on compact coupling windows. -/
theorem finiteCWPressureGap_tendstoUniformlyOn_nonnegative :
    TendstoUniformlyOn
      (fun population : ℕ ↦ fun tlam : ℝ ↦
        finiteCWPressureGap (population + 1) tlam)
      cwVariationalPressureGap Filter.atTop (Set.Ici 0) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro epsilon hepsilon
  have hsmall : ∀ᶠ population : ℕ in Filter.atTop,
      Real.log (((population + 2 : ℕ) : ℝ)) /
          ((population + 1 : ℕ) : ℝ) < epsilon :=
    finiteCWTypeCount_log_div_tendsto_zero.eventually_lt_const hepsilon
  filter_upwards [hsmall] with population hpopulationSmall
  intro tlam htlam
  have herror := finiteCWPressureGap_abs_sub_variational_le_typeCount
    (population + 1) tlam (Nat.succ_pos population) htlam
  rw [Real.dist_eq, abs_sub_comm]
  exact herror.trans_lt (by
    convert hpopulationSmall using 1
    all_goals norm_num [Nat.cast_add]
    all_goals ring)

/-- **Actual positive finite-volume pressure separation.**  Above the explicit
aligned-state threshold, every positive population size already has strictly
positive normalized Rademacher pressure.  No limiting interchange, LDP, or
analyticity assumption occurs in the statement. -/
theorem finiteCWPressureGap_pos_of_aligned
    (population : ℕ) (tlam : ℝ) (hpopulation : 0 < population)
    (hlarge : 2 * Real.log 2 < tlam) :
    0 < finiteCWPressureGap population tlam := by
  have hthreshold : 0 < tlam / 2 - Real.log 2 := by linarith
  exact hthreshold.trans_le
    (finiteCWPressureGap_ge_aligned population tlam hpopulation)

/-- The aligned-state lower bound is uniform in population, so above its
threshold the genuine finite pressure gap cannot disappear in the
thermodynamic limit. -/
theorem finiteCWPressureGap_not_tendsto_zero_of_aligned
    (tlam : ℝ) (hlarge : 2 * Real.log 2 < tlam) :
    ¬ Filter.Tendsto
      (fun population : ℕ ↦ finiteCWPressureGap (population + 1) tlam)
      Filter.atTop (nhds 0) := by
  intro hzero
  have hthreshold : 0 < tlam / 2 - Real.log 2 := by linarith
  have hbelow : ∀ᶠ population in Filter.atTop,
      finiteCWPressureGap (population + 1) tlam <
        tlam / 2 - Real.log 2 :=
    hzero.eventually_lt_const hthreshold
  obtain ⟨population, hpopulation⟩ := Filter.eventually_atTop.mp hbelow
  have hlt := hpopulation population le_rfl
  have hle := finiteCWPressureGap_ge_aligned
    (population + 1) tlam (Nat.succ_pos population)
  exact (not_lt_of_ge hle) hlt

/-- The unspiked `aI` contribution to the normalized one-replica quadratic
Rademacher pressure. -/
noncomputable def finiteBaselineRademacherPressure
    (baseline temperature : ℝ) : ℝ :=
  temperature * baseline / 2

/-- The normalized pressure of `aI + λ uuᵀ` for the balanced-sign rank-one
direction.  The Curie--Weiss coupling is exactly `temperature * spikeStrength`;
the baseline and spike contributions therefore separate additively. -/
noncomputable def finiteRankOneRademacherPressure
    (baseline : ℝ) (population : ℕ)
    (temperature spikeStrength : ℝ) : ℝ :=
  finiteBaselineRademacherPressure baseline temperature +
    finiteCWPressureGap population (temperature * spikeStrength)

/-- The difference between the spiked and unspiked finite pressures is exactly
the normalized Curie--Weiss pressure gap, not merely bounded by it. -/
theorem finiteRankOneRademacherPressure_sub_baseline
    (baseline : ℝ) (population : ℕ)
    (temperature spikeStrength : ℝ) :
    finiteRankOneRademacherPressure baseline population temperature spikeStrength -
        finiteBaselineRademacherPressure baseline temperature =
      finiteCWPressureGap population (temperature * spikeStrength) := by
  simp [finiteRankOneRademacherPressure]

/-- Throughout the exact supercritical regime, the genuine spiked finite
pressure is strictly larger than the unspiked pressure for every nonempty
population. -/
theorem finiteRankOneRademacherPressure_gt_baseline
    (baseline : ℝ) (population : ℕ)
    (temperature spikeStrength : ℝ) (hpopulation : 0 < population)
    (hcritical : 1 < temperature * spikeStrength) :
    finiteBaselineRademacherPressure baseline temperature <
      finiteRankOneRademacherPressure
        baseline population temperature spikeStrength := by
  rw [finiteRankOneRademacherPressure]
  exact lt_add_of_pos_right _
    (finiteCWPressureGap_pos_of_supercritical
      population (temperature * spikeStrength) hpopulation hcritical)

/-- The exact-criticality statement for the finite rank-one pressure sequence. -/
def FiniteRankOnePressureCriticalStatement
    (baseline temperature spikeStrength : ℝ) : Prop :=
  Filter.Tendsto
      (fun population : ℕ ↦
        finiteRankOneRademacherPressure baseline (population + 1)
            temperature spikeStrength -
          finiteBaselineRademacherPressure baseline temperature)
      Filter.atTop (nhds 0) ↔
    temperature * spikeStrength ≤ 1

/-- The variational-limit statement for the complete finite rank-one pressure. -/
def FiniteRankOnePressureVariationalLimitStatement
    (baseline temperature spikeStrength : ℝ) : Prop :=
  Filter.Tendsto
    (fun population : ℕ ↦
      finiteRankOneRademacherPressure baseline (population + 1)
        temperature spikeStrength)
    Filter.atTop
    (nhds (finiteBaselineRademacherPressure baseline temperature +
      cwVariationalPressureGap (temperature * spikeStrength)))

/-- The uniform nonnegative-spike convergence statement. -/
def FiniteRankOnePressureUniformLimitStatement
    (baseline temperature : ℝ) : Prop :=
  TendstoUniformlyOn
    (fun population : ℕ ↦ fun spikeStrength : ℝ ↦
      finiteRankOneRademacherPressure baseline (population + 1)
        temperature spikeStrength)
    (fun spikeStrength ↦
      finiteBaselineRademacherPressure baseline temperature +
        cwVariationalPressureGap (temperature * spikeStrength))
    Filter.atTop (Set.Ici 0)

/-- For nonnegative effective coupling, the genuine finite rank-one pressure
difference converges to zero exactly at and below the Curie--Weiss threshold. -/
theorem finiteRankOneRademacherPressure_difference_tendsto_zero_iff
    (baseline temperature spikeStrength : ℝ)
    (hcoupling : 0 ≤ temperature * spikeStrength) :
    FiniteRankOnePressureCriticalStatement baseline temperature spikeStrength := by
  unfold FiniteRankOnePressureCriticalStatement
  simpa only [finiteRankOneRademacherPressure_sub_baseline] using
    finiteCWPressureGap_tendsto_zero_iff
      (temperature * spikeStrength) hcoupling

/-- The complete finite rank-one pressure converges to the baseline plus the
Curie--Weiss variational pressure at every nonnegative effective coupling. -/
theorem finiteRankOneRademacherPressure_tendsto_variational
    (baseline temperature spikeStrength : ℝ)
    (hcoupling : 0 ≤ temperature * spikeStrength) :
    FiniteRankOnePressureVariationalLimitStatement
      baseline temperature spikeStrength := by
  have hbaseline : Filter.Tendsto
      (fun _population : ℕ ↦
        finiteBaselineRademacherPressure baseline temperature)
      Filter.atTop
      (nhds (finiteBaselineRademacherPressure baseline temperature)) :=
    tendsto_const_nhds
  have hgap := finiteCWPressureGap_tendsto_variationalPressure
    (temperature * spikeStrength) hcoupling
  simpa only [finiteRankOneRademacherPressure] using hbaseline.add hgap

/-- The same thermodynamic limit holds along the even dimensions `2(p+1)`
used by the concrete balanced covariance matrices. -/
theorem balancedRankOneCovariancePressure_tendsto_variational
    (baseline temperature spikeStrength : ℝ)
    (hcoupling : 0 ≤ temperature * spikeStrength) :
    Filter.Tendsto
      (fun population : ℕ ↦
        finiteRankOneRademacherPressure baseline (2 * (population + 1))
          temperature spikeStrength)
      Filter.atTop
      (nhds (finiteBaselineRademacherPressure baseline temperature +
        cwVariationalPressureGap (temperature * spikeStrength))) := by
  have hevenIndex : Filter.Tendsto (fun population : ℕ ↦ 2 * population + 1)
      Filter.atTop Filter.atTop := by
    rw [Filter.tendsto_atTop]
    intro threshold
    filter_upwards [Filter.eventually_ge_atTop threshold] with population hpopulation
    omega
  have hpressure := (finiteRankOneRademacherPressure_tendsto_variational
    baseline temperature spikeStrength hcoupling).comp hevenIndex
  simpa only [Function.comp_apply] using hpressure

/-- The complete concrete positive-cone counterexample, packaged so that its
matrix, traffic, ground-state, and thermodynamic statements cannot silently
refer to different witnesses. -/
structure ConcreteBalancedPSDPressureWitness
    {Term : Type*} [Fintype Term]
    (coefficient : Term → ℝ) (hasOddDegree : Term → Bool)
    (vertices edges : Term → ℕ)
    (baseline spikeStrength temperature : ℝ) : Prop where
  covariancePSD : ∀ population : ℕ,
    (balancedRankOneCovariance baseline spikeStrength (population + 1)).PosSemidef
  trafficInvisible :
    Filter.Tendsto
      (fun population : ℕ ↦
        finiteRankOneTrafficCorrection coefficient hasOddDegree vertices edges
          (population + 1))
      Filter.atTop (nhds 0)
  finiteHamiltonian : ∀ population : ℕ,
    ∀ vector : BalancedRankOneCoordinate (population + 1) → ℝ,
      (∀ coordinate, vector coordinate ^ 2 = 1) →
        temperature / 2 *
            (finiteMatrixQuadraticForm
                (balancedRankOneCovariance baseline spikeStrength (population + 1))
                vector - baseline * (2 * (population + 1) : ℕ)) =
          (temperature * spikeStrength) /
              (2 * ((2 * (population + 1) : ℕ) : ℝ)) *
            (balancedRankOneSign (population + 1) ⬝ᵥ vector) ^ 2
  lowerGroundStateUnchanged : ∀ population : ℕ,
    (∀ vector : BalancedRankOneCoordinate (population + 1) → ℝ,
      (∀ coordinate, vector coordinate ^ 2 = 1) →
        baseline * (2 * (population + 1) : ℕ) ≤
          finiteMatrixQuadraticForm
            (balancedRankOneCovariance baseline spikeStrength (population + 1))
            vector) ∧
      finiteMatrixQuadraticForm
          (balancedRankOneCovariance baseline spikeStrength (population + 1))
          (balancedRankOneOrthogonalSpin (population + 1)) =
        baseline * (2 * (population + 1) : ℕ) ∧
      baseline * (2 * (population + 1) : ℕ) <
        finiteMatrixQuadraticForm
          (balancedRankOneCovariance baseline spikeStrength (population + 1))
          (balancedRankOneSign (population + 1))
  pressureConverges :
    Filter.Tendsto
      (fun population : ℕ ↦
        finiteRankOneRademacherPressure baseline (2 * (population + 1))
          temperature spikeStrength)
      Filter.atTop
      (nhds (finiteBaselineRademacherPressure baseline temperature +
        cwVariationalPressureGap (temperature * spikeStrength)))
  pressureStrictlyPositive :
    0 < cwVariationalPressureGap (temperature * spikeStrength)

/-- **One actual balanced PSD covariance sequence refutes both proposed
dichotomies.**  Under `a ≥ 0`, `λ > 0`, and `tλ > 1`, the same matrices
`aI + λP` satisfy every field of `ConcreteBalancedPSDPressureWitness`. -/
theorem concreteBalancedPSDPressureWitness
    {Term : Type*} [Fintype Term]
    (coefficient : Term → ℝ) (hasOddDegree : Term → Bool)
    (vertices edges : Term → ℕ)
    (hconnected : ∀ term, hasOddDegree term = false → vertices term ≤ edges term)
    (baseline spikeStrength temperature : ℝ)
    (hbaseline : 0 ≤ baseline) (hspike : 0 < spikeStrength)
    (hcritical : 1 < temperature * spikeStrength) :
    ConcreteBalancedPSDPressureWitness coefficient hasOddDegree vertices edges
      baseline spikeStrength temperature := by
  have hcoupling : 0 ≤ temperature * spikeStrength := by linarith
  exact
    { covariancePSD := fun population ↦
        balancedRankOneCovariance_posSemidef baseline spikeStrength (population + 1)
          hbaseline hspike.le
      trafficInvisible :=
        finiteRankOneTrafficCorrection_tendsto_zero coefficient hasOddDegree
          vertices edges hconnected
      finiteHamiltonian := fun population vector hrademacher ↦
        balancedRankOneCovariance_rademacherExponent_eq_finiteCW
          baseline spikeStrength temperature (population + 1) vector hrademacher
      lowerGroundStateUnchanged := fun population ↦
        balancedRankOneCovariance_groundState_certificate baseline spikeStrength
          (population + 1) hspike (Nat.succ_pos population)
      pressureConverges :=
        balancedRankOneCovariancePressure_tendsto_variational
          baseline temperature spikeStrength hcoupling
      pressureStrictlyPositive :=
        cwVariationalPressureGap_pos_of_supercritical
          (temperature * spikeStrength) hcritical }

/-- At fixed nonnegative temperature, convergence of the complete rank-one
pressure is uniform over every nonnegative spike strength, including the
unbounded half-line. -/
theorem finiteRankOneRademacherPressure_tendstoUniformlyOn_nonnegativeSpike
    (baseline temperature : ℝ) (htemperature : 0 ≤ temperature) :
    FiniteRankOnePressureUniformLimitStatement baseline temperature := by
  unfold FiniteRankOnePressureUniformLimitStatement
  rw [Metric.tendstoUniformlyOn_iff]
  intro epsilon hepsilon
  have hsmall : ∀ᶠ population : ℕ in Filter.atTop,
      Real.log (((population + 2 : ℕ) : ℝ)) /
          ((population + 1 : ℕ) : ℝ) < epsilon :=
    finiteCWTypeCount_log_div_tendsto_zero.eventually_lt_const hepsilon
  filter_upwards [hsmall] with population hpopulationSmall
  intro spikeStrength hspikeStrength
  have hcoupling : 0 ≤ temperature * spikeStrength :=
    mul_nonneg htemperature hspikeStrength
  have herror := finiteCWPressureGap_abs_sub_variational_le_typeCount
    (population + 1) (temperature * spikeStrength)
    (Nat.succ_pos population) hcoupling
  have hstrict : |finiteCWPressureGap (population + 1)
      (temperature * spikeStrength) -
        cwVariationalPressureGap (temperature * spikeStrength)| < epsilon :=
    herror.trans_lt (by
      convert hpopulationSmall using 1
      all_goals norm_num [Nat.cast_add]
      all_goals ring)
  simpa [finiteRankOneRademacherPressure, Real.dist_eq, abs_sub_comm] using hstrict

/-- **Positive-cone traffic counterexample at the exact variational level.**
Every fixed graph has finitely many nonempty spike-edge terms; once identity
edges are contracted, their complete correction vanishes by the connected
rank-one bound.  Nevertheless the Curie--Weiss variational pressure is strictly
positive above `tλ = 1`.

The full finite-pressure theorem below additionally identifies this
variational pressure as the genuine thermodynamic limit. -/
theorem finiteRankOneTraffic_invisible_variationalPressure_visible
    {Term : Type*} [Fintype Term]
    (coefficient : Term → ℝ) (hasOddDegree : Term → Bool)
    (vertices edges : Term → ℕ)
    (hconnected : ∀ term, hasOddDegree term = false → vertices term ≤ edges term)
    (tlam : ℝ) (hcritical : 1 < tlam) :
    Filter.Tendsto
        (fun population : ℕ ↦
          finiteRankOneTrafficCorrection coefficient hasOddDegree vertices edges
            (population + 1))
        Filter.atTop (nhds 0) ∧
      0 < cwVariationalPressureGap tlam :=
  ⟨finiteRankOneTrafficCorrection_tendsto_zero
      coefficient hasOddDegree vertices edges hconnected,
    cwVariationalPressureGap_pos_of_supercritical tlam hcritical⟩

/-- **The finite-volume properties one rank-one spike has at once**, as one
proposition: every fixed traffic correction vanishes, the genuine pressure
converges to the variational value, and one positive interior witness uniformly
lower-bounds every finite pressure, so that pressure cannot vanish
asymptotically.

Named for the same reason as `RankOneSpikeRefutesBothDichotomies`: the theorem that proves
it, the genomic restatement that cites that theorem, and the obstruction registry each
carried the conjunction in full, so a change to one copy would have been a silent divergence
rather than a build error.

Empirical status: NOT AN EMPIRICAL CLAIM. This names four propositions, each
proved below at finite volume on an explicit spike, so there is no measurement
that could agree or disagree with it. What a measurement could bear on is
whether a real LD spike is rank-one, which nothing here asserts. An UNTESTED
marker would read as a measurement owed, and none is. -/
def RankOneSpikeInvisibleWithFinitePressure {Term : Type*} [Fintype Term]
    (coefficient : Term → ℝ) (hasOddDegree : Term → Bool)
    (vertices edges : Term → ℕ) (tlam : ℝ) : Prop :=
  Filter.Tendsto
      (fun population : ℕ ↦
        finiteRankOneTrafficCorrection coefficient hasOddDegree vertices edges
          (population + 1))
      Filter.atTop (nhds 0) ∧
    Filter.Tendsto
      (fun population : ℕ ↦ finiteCWPressureGap (population + 1) tlam)
      Filter.atTop (nhds (cwVariationalPressureGap tlam)) ∧
    ∃ m : ℝ, |m| < 1 ∧ 0 < cwObjective tlam m ∧
      (∀ population : ℕ,
        cwObjective tlam m ≤ finiteCWPressureGap (population + 1) tlam) ∧
      ¬ Filter.Tendsto
        (fun population : ℕ ↦ finiteCWPressureGap (population + 1) tlam)
        Filter.atTop (nhds 0)

/-- **Positive-cone traffic counterexample for the genuine finite partition
function throughout the full supercritical regime.**  Every fixed traffic
correction vanishes, while for every coupling above `1` one interior trial law
supplies a positive population-uniform lower bound on normalized Rademacher
pressure.  The companion finite-pressure theorem proves convergence to zero
at and below `1`; neither statement requires an LDP or Varadhan premise. -/
theorem finiteRankOneTraffic_invisible_finitePressure_visible
    {Term : Type*} [Fintype Term]
    (coefficient : Term → ℝ) (hasOddDegree : Term → Bool)
    (vertices edges : Term → ℕ)
    (hconnected : ∀ term, hasOddDegree term = false → vertices term ≤ edges term)
    (tlam : ℝ) (hcritical : 1 < tlam) :
    RankOneSpikeInvisibleWithFinitePressure coefficient hasOddDegree vertices edges tlam := by
  obtain ⟨m, hm, hobjective, hlower⟩ :=
    finiteCWPressureGap_supercritical_uniformWitness tlam hcritical
  exact ⟨finiteRankOneTrafficCorrection_tendsto_zero
      coefficient hasOddDegree vertices edges hconnected,
    finiteCWPressureGap_tendsto_variationalPressure tlam
      (le_trans (by norm_num) hcritical.le),
    ⟨m, hm, hobjective,
      ⟨fun population ↦ hlower (population + 1) (Nat.succ_pos population),
        finiteCWPressureGap_not_tendsto_zero_of_supercritical tlam hcritical⟩⟩⟩

/-- **The four properties one positive rank-one spike has at once**, as one proposition.

The theorem below establishes it, `DynamicsContrast` restates it in genomic vocabulary and
cites that theorem, and the obstruction registry carries it as a field.  Written out, the
conjunction stood in the corpus three times, and a change to any one copy would have been a
silent divergence between them rather than a build error.

Empirical status: NOT AN EMPIRICAL CLAIM. This names a conjunction of four
propositions, each proved below on an explicit spike, so there is no measurement
that could agree or disagree with it. What a measurement could bear on is
whether a real LD spike is rank-one, which nothing here asserts. An UNTESTED
marker would read as a measurement owed, and none is. -/
def RankOneSpikeRefutesBothDichotomies
    {Term Spin : Type*} [Fintype Term]
    (coefficient : Term → ℝ) (hasOddDegree : Term → Bool)
    (vertices edges : Term → ℕ)
    (alignment : Spin → ℝ) (orthogonal aligned : Spin)
    (baseline spikeStrength population temperature : ℝ) : Prop :=
  Filter.Tendsto
      (fun size : ℕ ↦
        finiteRankOneTrafficCorrection coefficient hasOddDegree vertices edges (size + 1))
      Filter.atTop (nhds 0) ∧
    (∀ state, baseline ≤
      rankOneEnergyDensity baseline spikeStrength population (alignment state)) ∧
    rankOneEnergyDensity baseline spikeStrength population (alignment orthogonal) =
      baseline ∧
    baseline <
      rankOneEnergyDensity baseline spikeStrength population (alignment aligned) ∧
    0 < cwVariationalPressureGap (temperature * spikeStrength)

/-- **One exact witness refutes both the positive-cone traffic conjecture and
the lower-ground-state dichotomy at the variational level.**  The same positive
rank-one spike has all four properties:

1. every fixed traffic correction vanishes after its finite contraction
   expansion;
2. no state has energy below the unspiked baseline;
3. an orthogonal state attains that baseline exactly, while an aligned state
   has strictly larger energy; and
4. its Curie--Weiss variational pressure is positive when `temperature * λ > 1`.

The population and aligned-state hypotheses exclude the zero-dimensional and
zero-response junk cases explicitly. -/
theorem rankOneTraffic_groundState_pressure_counterexample
    {Term Spin : Type*} [Fintype Term]
    (coefficient : Term → ℝ) (hasOddDegree : Term → Bool)
    (vertices edges : Term → ℕ)
    (hconnected : ∀ term, hasOddDegree term = false → vertices term ≤ edges term)
    (alignment : Spin → ℝ) (orthogonal aligned : Spin)
    (baseline spikeStrength population temperature : ℝ)
    (hspike : 0 < spikeStrength) (hpopulation : population ≠ 0)
    (horthogonal : alignment orthogonal = 0)
    (haligned : alignment aligned = population)
    (hcritical : 1 < temperature * spikeStrength) :
    RankOneSpikeRefutesBothDichotomies coefficient hasOddDegree vertices edges
      alignment orthogonal aligned baseline spikeStrength population temperature := by
  have htraffic := finiteRankOneTrafficCorrection_tendsto_zero
    coefficient hasOddDegree vertices edges hconnected
  obtain ⟨hlower, hground⟩ := rankOne_groundState_certificate
    alignment orthogonal baseline spikeStrength population hspike.le horthogonal
  have hupper : baseline <
      rankOneEnergyDensity baseline spikeStrength population (alignment aligned) := by
    rw [haligned, rankOneEnergyDensity_aligned baseline spikeStrength population hpopulation]
    linarith
  exact ⟨htraffic, hlower, hground, hupper,
    cwVariationalPressureGap_pos_of_supercritical
      (temperature * spikeStrength) hcritical⟩

end CurieWeissWindow

end TrafficInvariantSeparation
end Descent.Blindness
