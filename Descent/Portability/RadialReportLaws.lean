/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.RadialInterpolation
import Descent.Portability.UniversalMetricIdentification

assert_below Descent.Decision Descent.Program

/-!
# Whole report laws are hidden, not only their means

PL Corollary 7.3. Replacing the two templates of Theorem 7.2 by two direction laws `P₀`
and `Q₀` on a finite family of valid templates, the same radial split produces two
outcome laws that still share every joint raw moment of total degree at most `k`, while
the law of the report under each is the mixture `(a P₀ + b Q₀)/(a+b)` of equation (7.6),
with `a/(a+b) = posShare` and `b/(a+b) = negShare` computed from the radial total
variation. Each mixture is within `b/(a+b)` of its target report law in total variation,
which is the boxed claim of the corollary.

Total variation is the corpus' `Portability.FiniteReportLaw.totalVariation`, so the bound
transfers to every bounded metric of the report through
`FiniteReportLaw.abs_expectation_sub_le_totalVariation`. The radial machinery is
`RadialInterpolation.radial_gap_general`, `radialWeight_sum`, `radialWeight_moment` and
`one_le_radialTotal`; the laws are `Portability.weightedExp` probability vectors.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.RadialReportLaws

open Foundations RadialInterpolation

noncomputable section

variable {k : ℕ} {N D : Type*} [Fintype N] [Fintype D]

/-- The share `a/(a+b)` of the radial mass that keeps its own direction law. -/
def posShare (r : Fin (k + 1) → ℝ) : ℝ := (radialTotal r + 1) / (2 * radialTotal r)

/-- The share `b/(a+b)` of the radial mass that is exchanged: the bound of PL
Corollary 7.3. -/
def negShare (r : Fin (k + 1) → ℝ) : ℝ := (radialTotal r - 1) / (2 * radialTotal r)

/-- The two shares are a probability split. -/
theorem posShare_add_negShare (r : Fin (k + 1) → ℝ) (hinj : Function.Injective r) :
    posShare r + negShare r = 1 := by
  have h1 : (1 : ℝ) ≤ radialTotal r := one_le_radialTotal r hinj
  have h0 : radialTotal r ≠ 0 := by linarith
  unfold posShare negShare
  field_simp
  ring

/-- The exchanged share is nonnegative. -/
theorem negShare_nonneg (r : Fin (k + 1) → ℝ) (hinj : Function.Injective r) :
    0 ≤ negShare r := by
  have h1 : (1 : ℝ) ≤ radialTotal r := one_le_radialTotal r hinj
  unfold negShare
  apply div_nonneg <;> linarith

/-- The kept share is nonnegative. -/
theorem posShare_nonneg (r : Fin (k + 1) → ℝ) (hinj : Function.Injective r) :
    0 ≤ posShare r := by
  have h1 : (1 : ℝ) ≤ radialTotal r := one_le_radialTotal r hinj
  unfold posShare
  apply div_nonneg <;> linarith

/-- The positive part of the radial weights totals `(c+1)/2`. -/
theorem sum_pos_part (r : Fin (k + 1) → ℝ) (hinj : Function.Injective r) :
    (∑ i, (|radialWeight r i| + radialWeight r i) / 2) = (radialTotal r + 1) / 2 := by
  unfold radialTotal
  rw [← Finset.sum_div, Finset.sum_add_distrib, radialWeight_sum r hinj]

/-- The negative part of the radial weights totals `(c-1)/2`. -/
theorem sum_neg_part (r : Fin (k + 1) → ℝ) (hinj : Function.Injective r) :
    (∑ i, (|radialWeight r i| - radialWeight r i) / 2) = (radialTotal r - 1) / 2 := by
  unfold radialTotal
  rw [← Finset.sum_div, Finset.sum_sub_distrib, radialWeight_sum r hinj]

/-- The joint law of PL Corollary 7.3: a radial support point together with a direction
drawn from the direction law attached to that branch. -/
def radialDirectionLaw (r : Fin (k + 1) → ℝ) (P₀ Q₀ : FiniteReportLaw D) (s : Bool)
    (z : (Fin (k + 1) × Bool) × D) : ℝ :=
  radialLaw r s z.1 * (if z.1.2 then P₀.mass z.2 else Q₀.mass z.2)

/-- The joint law is nonnegative. -/
theorem radialDirectionLaw_nonneg (r : Fin (k + 1) → ℝ) (P₀ Q₀ : FiniteReportLaw D)
    (s : Bool) (z : (Fin (k + 1) × Bool) × D) : 0 ≤ radialDirectionLaw r P₀ Q₀ s z := by
  unfold radialDirectionLaw
  refine mul_nonneg (radialLaw_nonneg r s z.1) ?_
  split
  · exact P₀.mass_nonneg z.2
  · exact Q₀.mass_nonneg z.2

/-- The joint law is a probability law. -/
theorem radialDirectionLaw_sum (r : Fin (k + 1) → ℝ) (hinj : Function.Injective r)
    (P₀ Q₀ : FiniteReportLaw D) (s : Bool) :
    ∑ z, radialDirectionLaw r P₀ Q₀ s z = 1 := by
  rw [Fintype.sum_prod_type]
  have hterm : ∀ zb : Fin (k + 1) × Bool,
      (∑ d, radialDirectionLaw r P₀ Q₀ s (zb, d)) = radialLaw r s zb := by
    intro zb
    simp only [radialDirectionLaw, ← Finset.mul_sum]
    by_cases hb : zb.2 = true
    · simp [hb, P₀.mass_sum]
    · simp [hb, Q₀.mass_sum]
  rw [Finset.sum_congr rfl fun zb _ ↦ hterm zb]
  exact radialLaw_sum r hinj s

/-- The two moment-matched outcome expectations of PL Corollary 7.3. -/
def radialDirectionExp (r : Fin (k + 1) → ℝ) (hinj : Function.Injective r)
    (P₀ Q₀ : FiniteReportLaw D) (s : Bool) :
    ExpFunctional ((Fin (k + 1) × Bool) × D) :=
  weightedExp (radialDirectionLaw r P₀ Q₀ s) (radialDirectionLaw_nonneg r P₀ Q₀ s)
    (radialDirectionLaw_sum r hinj P₀ Q₀ s)

/-- The outcome vector of a joint draw: the drawn direction, scaled by the drawn
radius. -/
def radialDirectionPoint (r : Fin (k + 1) → ℝ) (dir : D → N → ℝ)
    (z : (Fin (k + 1) × Bool) × D) : N → ℝ := r z.1.1 • dir z.2

/-- Integrating out the direction reduces the joint expectation to a radial one. -/
theorem radialDirectionExp_eq (r : Fin (k + 1) → ℝ) (hinj : Function.Injective r)
    (P₀ Q₀ : FiniteReportLaw D) (dir : D → N → ℝ) (s : Bool) (g : (N → ℝ) → ℝ) :
    radialDirectionExp r hinj P₀ Q₀ s (fun z ↦ g (radialDirectionPoint r dir z)) =
      radialExp r hinj s (fun zb ↦ if zb.2 then ∑ d, P₀.mass d * g (r zb.1 • dir d)
        else ∑ d, Q₀.mass d * g (r zb.1 • dir d)) := by
  simp only [radialDirectionExp, radialExp, weightedExp_apply]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun zb _ ↦ ?_
  have key : ∀ (c : ℝ) (m : D → ℝ),
      (∑ d, c * m d * g (r zb.1 • dir d)) = c * ∑ d, m d * g (r zb.1 • dir d) := by
    intro c m
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun d _ ↦ by ring
  cases hz : zb.2
  · have hif : ∀ a b : ℝ, (if zb.2 then a else b) = b := by
      intro a b; rw [hz]; rfl
    simp only [radialDirectionLaw, radialDirectionPoint, hif]
    exact key (radialLaw r s zb) (fun d ↦ Q₀.mass d)
  · have hif : ∀ a b : ℝ, (if zb.2 then a else b) = a := by
      intro a b; rw [hz]; rfl
    simp only [radialDirectionLaw, radialDirectionPoint, hif]
    exact key (radialLaw r s zb) (fun d ↦ P₀.mass d)

/-- **The master gap identity with direction laws.** -/
theorem radialDirection_gap (r : Fin (k + 1) → ℝ) (hinj : Function.Injective r)
    (P₀ Q₀ : FiniteReportLaw D) (dir : D → N → ℝ) (g : (N → ℝ) → ℝ) :
    radialDirectionExp r hinj P₀ Q₀ false (fun z ↦ g (radialDirectionPoint r dir z)) -
        radialDirectionExp r hinj P₀ Q₀ true (fun z ↦ g (radialDirectionPoint r dir z)) =
      (∑ i, radialWeight r i * ((∑ d, P₀.mass d * g (r i • dir d)) -
        ∑ d, Q₀.mass d * g (r i • dir d))) / radialTotal r := by
  rw [radialDirectionExp_eq r hinj P₀ Q₀ dir false g,
    radialDirectionExp_eq r hinj P₀ Q₀ dir true g]
  exact radial_gap_general r hinj _

/-- **PL Corollary 7.3, moment matching.** The two direction-law outcome laws share every
joint raw moment of total degree at most `k`. -/
theorem radialDirection_moment_match (r : Fin (k + 1) → ℝ) (hinj : Function.Injective r)
    (P₀ Q₀ : FiniteReportLaw D) (dir : D → N → ℝ) (α : N → ℕ) (hα : ∑ i, α i ≤ k) :
    radialDirectionExp r hinj P₀ Q₀ false
        (fun z ↦ monomialEval α (radialDirectionPoint r dir z)) =
      radialDirectionExp r hinj P₀ Q₀ true
        (fun z ↦ monomialEval α (radialDirectionPoint r dir z)) := by
  have hgap := radialDirection_gap r hinj P₀ Q₀ dir (monomialEval α)
  have hexp : ∀ (L : FiniteReportLaw D) (i : Fin (k + 1)),
      (∑ d, L.mass d * monomialEval α (r i • dir d)) =
        r i ^ (∑ j, α j) * ∑ d, L.mass d * monomialEval α (dir d) := by
    intro L i
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun d _ ↦ by rw [monomialEval_smul]; ring
  have hzero : (∑ i, radialWeight r i * ((∑ d, P₀.mass d * monomialEval α (r i • dir d)) -
      ∑ d, Q₀.mass d * monomialEval α (r i • dir d))) = 0 := by
    have hterm : ∀ i : Fin (k + 1),
        radialWeight r i * ((∑ d, P₀.mass d * monomialEval α (r i • dir d)) -
            ∑ d, Q₀.mass d * monomialEval α (r i • dir d)) =
          ((∑ d, P₀.mass d * monomialEval α (dir d)) -
            ∑ d, Q₀.mass d * monomialEval α (dir d)) *
              (radialWeight r i * r i ^ (∑ j, α j)) := by
      intro i
      rw [hexp P₀ i, hexp Q₀ i]
      ring
    rw [Finset.sum_congr rfl fun i _ ↦ hterm i, ← Finset.mul_sum]
    rcases Nat.eq_zero_or_pos (∑ j, α j) with h | h
    · have hone : ∀ L : FiniteReportLaw D,
          (∑ d, L.mass d * monomialEval α (dir d)) = 1 := by
        intro L
        have hm : ∀ y : N → ℝ, monomialEval α y = 1 := by
          intro y
          unfold monomialEval
          refine Finset.prod_eq_one fun j _ ↦ ?_
          rw [Finset.sum_eq_zero_iff.mp h j (Finset.mem_univ j), pow_zero]
        simp only [hm, mul_one]
        exact L.mass_sum
      rw [hone P₀, hone Q₀]
      ring
    · rw [radialWeight_moment r hinj h hα, mul_zero]
  rw [hzero, zero_div] at hgap
  linarith

/-- The direction marginal of the joint law: the mixture of equation (7.6). -/
def directionMarginal (r : Fin (k + 1) → ℝ) (hinj : Function.Injective r) (s : Bool)
    (P₀ Q₀ : FiniteReportLaw D) : FiniteReportLaw D where
  mass d := if s then negShare r * P₀.mass d + posShare r * Q₀.mass d
    else posShare r * P₀.mass d + negShare r * Q₀.mass d
  mass_nonneg d := by
    have hp := posShare_nonneg r hinj
    have hn := negShare_nonneg r hinj
    have h1 := P₀.mass_nonneg d
    have h2 := Q₀.mass_nonneg d
    split
    · exact add_nonneg (mul_nonneg hn h1) (mul_nonneg hp h2)
    · exact add_nonneg (mul_nonneg hp h1) (mul_nonneg hn h2)
  mass_sum := by
    have hpn := posShare_add_negShare r hinj
    cases s
    · show (∑ d, (posShare r * P₀.mass d + negShare r * Q₀.mass d)) = 1
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
        P₀.mass_sum, Q₀.mass_sum]
      linarith
    · show (∑ d, (negShare r * P₀.mass d + posShare r * Q₀.mass d)) = 1
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
        P₀.mass_sum, Q₀.mass_sum]
      linarith

/-- The direction marginal's mass, branch by branch. -/
theorem directionMarginal_mass (r : Fin (k + 1) → ℝ) (hinj : Function.Injective r)
    (s : Bool) (P₀ Q₀ : FiniteReportLaw D) (d : D) :
    (directionMarginal r hinj s P₀ Q₀).mass d =
      if s then negShare r * P₀.mass d + posShare r * Q₀.mass d
      else posShare r * P₀.mass d + negShare r * Q₀.mass d := rfl

/-- **PL equation (7.6).** The direction marginal of the joint law is exactly the
mixture `(a P₀ + b Q₀)/(a+b)`, with the roles exchanged under the second law. -/
theorem directionMarginal_mass_eq (r : Fin (k + 1) → ℝ) (hinj : Function.Injective r)
    (s : Bool) (P₀ Q₀ : FiniteReportLaw D) (d : D) :
    (∑ zb : Fin (k + 1) × Bool,
      radialLaw r s zb * (if zb.2 then P₀.mass d else Q₀.mass d)) =
      (directionMarginal r hinj s P₀ Q₀).mass d := by
  have hpos := sum_pos_part r hinj
  have hneg := sum_neg_part r hinj
  have hc : (1 : ℝ) ≤ radialTotal r := one_le_radialTotal r hinj
  have hc0 : radialTotal r ≠ 0 := by linarith
  rw [Fintype.sum_prod_type]
  cases s
  · have hstep : ∀ i : Fin (k + 1),
        (∑ bb : Bool, radialLaw r false (i, bb) *
          (if bb then P₀.mass d else Q₀.mass d)) =
        ((|radialWeight r i| + radialWeight r i) / 2) * (P₀.mass d / radialTotal r) +
          ((|radialWeight r i| - radialWeight r i) / 2) *
            (Q₀.mass d / radialTotal r) := by
      intro i
      have hb : (∑ bb : Bool, radialLaw r false (i, bb) *
          (if bb then P₀.mass d else Q₀.mass d)) =
          (|radialWeight r i| + radialWeight r i) / 2 / radialTotal r * P₀.mass d +
            (|radialWeight r i| - radialWeight r i) / 2 / radialTotal r * Q₀.mass d :=
        Fintype.sum_bool _
      rw [hb]
      ring
    have hm : (directionMarginal r hinj false P₀ Q₀).mass d =
        posShare r * P₀.mass d + negShare r * Q₀.mass d := rfl
    rw [Finset.sum_congr rfl fun i _ ↦ hstep i, Finset.sum_add_distrib,
      ← Finset.sum_mul, ← Finset.sum_mul, hpos, hneg, hm]
    unfold posShare negShare
    first
      | (field_simp; ring)
      | field_simp
  · have hstep : ∀ i : Fin (k + 1),
        (∑ bb : Bool, radialLaw r true (i, bb) *
          (if bb then P₀.mass d else Q₀.mass d)) =
        ((|radialWeight r i| - radialWeight r i) / 2) * (P₀.mass d / radialTotal r) +
          ((|radialWeight r i| + radialWeight r i) / 2) *
            (Q₀.mass d / radialTotal r) := by
      intro i
      have hb : (∑ bb : Bool, radialLaw r true (i, bb) *
          (if bb then P₀.mass d else Q₀.mass d)) =
          (|radialWeight r i| - radialWeight r i) / 2 / radialTotal r * P₀.mass d +
            (|radialWeight r i| + radialWeight r i) / 2 / radialTotal r * Q₀.mass d :=
        Fintype.sum_bool _
      rw [hb]
      ring
    have hm : (directionMarginal r hinj true P₀ Q₀).mass d =
        negShare r * P₀.mass d + posShare r * Q₀.mass d := rfl
    rw [Finset.sum_congr rfl fun i _ ↦ hstep i, Finset.sum_add_distrib,
      ← Finset.sum_mul, ← Finset.sum_mul, hneg, hpos, hm]
    unfold posShare negShare
    first
      | (field_simp; ring)
      | field_simp

omit [Fintype N] in
/-- A scale-invariant observable of the outcome integrates against the direction
marginal alone. -/
theorem radialDirection_scale_invariant_exp (r : Fin (k + 1) → ℝ)
    (hinj : Function.Injective r) (hpos : ∀ i, 0 < r i) (P₀ Q₀ : FiniteReportLaw D)
    (dir : D → N → ℝ) (h : (N → ℝ) → ℝ)
    (hh : ∀ t : ℝ, 0 < t → ∀ y : N → ℝ, h (t • y) = h y) (s : Bool) :
    radialDirectionExp r hinj P₀ Q₀ s (fun z ↦ h (radialDirectionPoint r dir z)) =
      (directionMarginal r hinj s P₀ Q₀).expectation (fun d ↦ h (dir d)) := by
  simp only [radialDirectionExp, weightedExp_apply, FiniteReportLaw.expectation]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ ↦ ?_
  rw [← directionMarginal_mass_eq r hinj s P₀ Q₀ d, Finset.sum_mul]
  refine Finset.sum_congr rfl fun zb _ ↦ ?_
  simp only [radialDirectionLaw, radialDirectionPoint]
  rw [hh (r zb.1) (hpos zb.1) (dir d)]

/-- **PL Corollary 7.3, the boxed bound.** Each report-law mixture is within `b/(a+b)`
of its target direction law in total variation. -/
theorem directionMarginal_totalVariation_le (r : Fin (k + 1) → ℝ)
    (hinj : Function.Injective r) (s : Bool) (P₀ Q₀ : FiniteReportLaw D) :
    (directionMarginal r hinj s P₀ Q₀).totalVariation (if s then Q₀ else P₀) ≤
      negShare r := by
  have hpn := posShare_add_negShare r hinj
  have hnn := negShare_nonneg r hinj
  have hterm : ∀ d : D,
      |(directionMarginal r hinj s P₀ Q₀).mass d - (if s then Q₀ else P₀).mass d| =
        negShare r * |P₀.mass d - Q₀.mass d| := by
    intro d
    cases s
    · show |posShare r * P₀.mass d + negShare r * Q₀.mass d - P₀.mass d| = _
      rw [show posShare r * P₀.mass d + negShare r * Q₀.mass d - P₀.mass d =
        negShare r * (Q₀.mass d - P₀.mass d) by linear_combination P₀.mass d * hpn]
      rw [abs_mul, abs_of_nonneg hnn, abs_sub_comm]
    · show |negShare r * P₀.mass d + posShare r * Q₀.mass d - Q₀.mass d| = _
      rw [show negShare r * P₀.mass d + posShare r * Q₀.mass d - Q₀.mass d =
        negShare r * (P₀.mass d - Q₀.mass d) by linear_combination Q₀.mass d * hpn]
      rw [abs_mul, abs_of_nonneg hnn]
  rw [FiniteReportLaw.totalVariation_eq_half_sum_abs,
    Finset.sum_congr rfl fun d _ ↦ hterm d]
  calc (∑ d, negShare r * |P₀.mass d - Q₀.mass d|) / 2
      = negShare r * ((∑ d, |P₀.mass d - Q₀.mass d|) / 2) := by
        rw [← Finset.mul_sum]; ring
    _ = negShare r * P₀.totalVariation Q₀ := by
        rw [FiniteReportLaw.totalVariation_eq_half_sum_abs]
    _ ≤ negShare r * 1 := mul_le_mul_of_nonneg_left (P₀.totalVariation_le_one Q₀) hnn
    _ = negShare r := mul_one _

/-- **PL Corollary 7.3, report form.** Every bounded metric of a scale-invariant report
has expectation within `b/(a+b)` of its value under the target direction law, which is
the total-variation statement transported through
`FiniteReportLaw.abs_expectation_sub_le_totalVariation`. -/
theorem radial_report_law_totalVariation (r : Fin (k + 1) → ℝ)
    (hinj : Function.Injective r) (hpos : ∀ i, 0 < r i) (P₀ Q₀ : FiniteReportLaw D)
    (dir : D → N → ℝ) (F : (N → ℝ) → ℝ)
    (hF : ∀ t : ℝ, 0 < t → ∀ y : N → ℝ, F (t • y) = F y) (φ : ℝ → ℝ)
    (hφ : ∀ d : D, 0 ≤ φ (F (dir d)) ∧ φ (F (dir d)) ≤ 1) (s : Bool) :
    |radialDirectionExp r hinj P₀ Q₀ s
          (fun z ↦ φ (F (radialDirectionPoint r dir z))) -
        (if s then Q₀ else P₀).expectation (fun d ↦ φ (F (dir d)))| ≤ negShare r := by
  rw [radialDirection_scale_invariant_exp r hinj hpos P₀ Q₀ dir (fun y ↦ φ (F y))
    (fun t ht y ↦ by simp only [hF t ht y]) s]
  refine le_trans (FiniteReportLaw.abs_expectation_sub_le_totalVariation _ _ _ hφ) ?_
  exact directionMarginal_totalVariation_le r hinj s P₀ Q₀

/-- **PL Corollary 7.3, the limit.** For every `η > 0` there are `k+1` distinct positive
radii whose two moment-matched direction-law outcome laws have report laws within `η` of
their respective targets in total variation. -/
theorem exists_radii_report_law_close (k : ℕ) (η : ℝ) (hη : 0 < η) :
    ∃ t : ℝ, 0 < t ∧ t < 1 ∧ negShare (radii k t) ≤ η := by
  obtain ⟨t, ht, ht1, htot⟩ := exists_radii_total_lt k (2 * η) (by linarith)
  refine ⟨t, ht, ht1, ?_⟩
  have hinj := radii_injective k t ht ht1
  have hc : (1 : ℝ) ≤ radialTotal (radii k t) := one_le_radialTotal _ hinj
  unfold negShare
  rw [div_le_iff₀ (by linarith)]
  nlinarith

end

end Descent.Portability.RadialReportLaws
