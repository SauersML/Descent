/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.PartialHaplotypeDualGenerator

assert_below Descent.Decision Descent.Program

/-!
# Second-order Taylor bounds for frequency polynomials along short segments

The microscopic kernels of NOTE1 §2.3 and §4.2a move a population state a short distance along a
segment: a resampling step `x ↦ x + ε (e_g − x_i)` and a drift step `x ↦ x + ρ μ(x)`.  Their
first-order expansions need, for every frequency polynomial, a uniform bound on the second-order
Taylor remainder along such segments.  This module proves that bound by induction on the
polynomial.  The directional derivatives are sums of `MvPolynomial.pderiv`, the same partial
derivatives that define the neutral generator of `PartialHaplotypeDualGenerator`.

`exists_lineTaylor_bound`: for every frequency polynomial there is a constant `B` with the
following property, for starting points in the unit box, directions in the box of radius two and
segment fractions `ε ∈ [0, 1]`.  The value of the polynomial at both ends of the segment and its
first and second directional derivatives are at most `B` in absolute value, and the second-order
remainder `p(x + ε v) − p(x) − ε D_v p(x) − (ε² / 2) D²_v p(x)` is at most `B ε³`.  The constant
is built along the construction of the polynomial from constants, sums and products with one
coordinate at a time (`directionalDerivative_mul_X`, `secondDirectionalDerivative_mul_X`,
`lineRemainder_mul_X`).

## Empirical status

None.  The bodies here are algebra and elementary inequalities about polynomials, so no
measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.PartialHaplotypeLineTaylor

open PartialHaplotypeDualGenerator MvPolynomial

variable {Deme Locus : Type*} {Allele : Locus → Type*}
variable [Fintype Deme] [DecidableEq Deme] [Fintype Locus] [DecidableEq Locus]
  [∀ ℓ, Fintype (Allele ℓ)] [∀ ℓ, DecidableEq (Allele ℓ)]

noncomputable section

/-- The directional derivative `Σ_u ∂_u p(x) v_u` of a frequency polynomial. -/
def directionalDerivative (p : FrequencyPolynomial Deme Locus Allele)
    (x v : FrequencyVariable Deme Locus Allele → ℝ) : ℝ :=
  ∑ u, eval x (pderiv u p) * v u

/-- The second directional derivative `Σ_{u,w} ∂_u ∂_w p(x) v_u v_w` of a frequency
polynomial. -/
def secondDirectionalDerivative (p : FrequencyPolynomial Deme Locus Allele)
    (x v : FrequencyVariable Deme Locus Allele → ℝ) : ℝ :=
  ∑ u, ∑ w, eval x (pderiv u (pderiv w p)) * (v u * v w)

/-- The second-order Taylor remainder of a frequency polynomial along the segment from `x` in
direction `v`, at fraction `ε`. -/
def lineRemainder (p : FrequencyPolynomial Deme Locus Allele)
    (x v : FrequencyVariable Deme Locus Allele → ℝ) (ε : ℝ) : ℝ :=
  eval (x + ε • v) p - eval x p - ε * directionalDerivative p x v
    - ε ^ 2 / 2 * secondDirectionalDerivative p x v

/-- The partial derivative of a coordinate is the indicator of that coordinate. -/
theorem pderiv_X_eq_ite (n a : FrequencyVariable Deme Locus Allele) :
    pderiv a (X n : FrequencyPolynomial Deme Locus Allele) = if n = a then 1 else 0 := by
  by_cases h : n = a
  · subst h
    rw [if_pos rfl, pderiv_X_self]
  · rw [if_neg h, pderiv_X_of_ne h]

/-- The partial derivative of a constant indicator vanishes. -/
theorem pderiv_ite_one_zero (a : FrequencyVariable Deme Locus Allele) (c : Prop) [Decidable c] :
    pderiv a (if c then (1 : FrequencyPolynomial Deme Locus Allele) else 0) = 0 := by
  split_ifs
  · exact pderiv_one
  · exact map_zero _

/-- A constant has zero directional derivative. -/
theorem directionalDerivative_C (a : ℝ) (x v : FrequencyVariable Deme Locus Allele → ℝ) :
    directionalDerivative (C a : FrequencyPolynomial Deme Locus Allele) x v = 0 := by
  simp [directionalDerivative, pderiv_C]

/-- A constant has zero second directional derivative. -/
theorem secondDirectionalDerivative_C (a : ℝ) (x v : FrequencyVariable Deme Locus Allele → ℝ) :
    secondDirectionalDerivative (C a : FrequencyPolynomial Deme Locus Allele) x v = 0 := by
  simp [secondDirectionalDerivative, pderiv_C]

/-- A constant has zero segment remainder. -/
theorem lineRemainder_C (a : ℝ) (x v : FrequencyVariable Deme Locus Allele → ℝ) (ε : ℝ) :
    lineRemainder (C a : FrequencyPolynomial Deme Locus Allele) x v ε = 0 := by
  rw [lineRemainder, directionalDerivative_C, secondDirectionalDerivative_C, eval_C, eval_C]
  ring

/-- Directional derivatives are additive in the polynomial. -/
theorem directionalDerivative_add (p q : FrequencyPolynomial Deme Locus Allele)
    (x v : FrequencyVariable Deme Locus Allele → ℝ) :
    directionalDerivative (p + q) x v
      = directionalDerivative p x v + directionalDerivative q x v := by
  simp only [directionalDerivative, map_add, add_mul, Finset.sum_add_distrib]

/-- Second directional derivatives are additive in the polynomial. -/
theorem secondDirectionalDerivative_add (p q : FrequencyPolynomial Deme Locus Allele)
    (x v : FrequencyVariable Deme Locus Allele → ℝ) :
    secondDirectionalDerivative (p + q) x v
      = secondDirectionalDerivative p x v + secondDirectionalDerivative q x v := by
  simp only [secondDirectionalDerivative, map_add, add_mul, Finset.sum_add_distrib]

/-- Segment remainders are additive in the polynomial. -/
theorem lineRemainder_add (p q : FrequencyPolynomial Deme Locus Allele)
    (x v : FrequencyVariable Deme Locus Allele → ℝ) (ε : ℝ) :
    lineRemainder (p + q) x v ε = lineRemainder p x v ε + lineRemainder q x v ε := by
  simp only [lineRemainder, directionalDerivative_add, secondDirectionalDerivative_add, map_add]
  ring

/-- The directional derivative of a product with a coordinate: the Leibniz rule. -/
theorem directionalDerivative_mul_X (p : FrequencyPolynomial Deme Locus Allele)
    (n : FrequencyVariable Deme Locus Allele) (x v : FrequencyVariable Deme Locus Allele → ℝ) :
    directionalDerivative (p * X n) x v
      = directionalDerivative p x v * x n + eval x p * v n := by
  have hterm : ∀ u, eval x (pderiv u (p * X n)) * v u
      = eval x (pderiv u p) * v u * x n + eval x p * ((if n = u then 1 else 0) * v u) := by
    intro u
    rw [pderiv_mul, pderiv_X_eq_ite, map_add, map_mul, map_mul, eval_X, apply_ite (eval x),
      map_one, map_zero]
    ring
  rw [directionalDerivative, Finset.sum_congr rfl fun u _ ↦ hterm u, Finset.sum_add_distrib,
    ← Finset.sum_mul, ← Finset.mul_sum]
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  rfl

/-- The second directional derivative of a product with a coordinate. -/
theorem secondDirectionalDerivative_mul_X (p : FrequencyPolynomial Deme Locus Allele)
    (n : FrequencyVariable Deme Locus Allele) (x v : FrequencyVariable Deme Locus Allele → ℝ) :
    secondDirectionalDerivative (p * X n) x v
      = secondDirectionalDerivative p x v * x n + 2 * (directionalDerivative p x v * v n) := by
  have hterm : ∀ u w, eval x (pderiv u (pderiv w (p * X n))) * (v u * v w)
      = eval x (pderiv u (pderiv w p)) * (v u * v w) * x n
        + eval x (pderiv w p) * ((if n = u then 1 else 0) * (v u * v w))
        + eval x (pderiv u p) * ((if n = w then 1 else 0) * (v u * v w)) := by
    intro u w
    rw [pderiv_mul, map_add, pderiv_mul, pderiv_mul, pderiv_X_eq_ite, pderiv_X_eq_ite,
      pderiv_ite_one_zero]
    simp only [map_add, map_mul, eval_X, apply_ite (eval x), map_one, map_zero]
    ring
  have hsecond : ∑ u, ∑ w, eval x (pderiv u (pderiv w p)) * (v u * v w) * x n
      = secondDirectionalDerivative p x v * x n := by
    rw [secondDirectionalDerivative, Finset.sum_mul]
    exact Finset.sum_congr rfl fun u _ ↦ by rw [Finset.sum_mul]
  have hleft : ∑ u, ∑ w, eval x (pderiv w p) * ((if n = u then 1 else 0) * (v u * v w))
      = directionalDerivative p x v * v n := by
    rw [Finset.sum_eq_single n]
    · rw [directionalDerivative, Finset.sum_mul]
      refine Finset.sum_congr rfl fun w _ ↦ ?_
      simp only [eq_self_iff_true, ↓reduceIte, one_mul]
      ring
    · intro u _ hu
      exact Finset.sum_eq_zero fun w _ ↦ by simp [Ne.symm hu]
    · intro hn
      exact absurd (Finset.mem_univ n) hn
  have hright : ∑ u, ∑ w, eval x (pderiv u p) * ((if n = w then 1 else 0) * (v u * v w))
      = directionalDerivative p x v * v n := by
    rw [directionalDerivative, Finset.sum_mul]
    refine Finset.sum_congr rfl fun u _ ↦ ?_
    rw [Finset.sum_eq_single n]
    · simp only [eq_self_iff_true, ↓reduceIte, one_mul]
      ring
    · intro w _ hw
      simp [Ne.symm hw]
    · intro hn
      exact absurd (Finset.mem_univ n) hn
  rw [secondDirectionalDerivative,
    Finset.sum_congr rfl fun u _ ↦ Finset.sum_congr rfl fun w _ ↦ hterm u w]
  simp only [Finset.sum_add_distrib]
  rw [hsecond, hleft, hright]
  ring

/-- The segment remainder of a product with a coordinate. -/
theorem lineRemainder_mul_X (p : FrequencyPolynomial Deme Locus Allele)
    (n : FrequencyVariable Deme Locus Allele) (x v : FrequencyVariable Deme Locus Allele → ℝ)
    (ε : ℝ) :
    lineRemainder (p * X n) x v ε
      = ε ^ 3 / 2 * (secondDirectionalDerivative p x v * v n)
        + lineRemainder p x v ε * (x n + ε * v n) := by
  simp only [lineRemainder, directionalDerivative_mul_X, secondDirectionalDerivative_mul_X,
    map_mul, eval_X, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- **Uniform Taylor bounds along short segments.**  For every frequency polynomial there is a
constant bounding, for starting points in the unit box, directions in the box of radius two and
fractions `ε ∈ [0, 1]`: the value at both ends of the segment, the first and second directional
derivatives, and the second-order remainder by `B ε³`. -/
theorem exists_lineTaylor_bound (p : FrequencyPolynomial Deme Locus Allele) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x v : FrequencyVariable Deme Locus Allele → ℝ,
      (∀ u, |x u| ≤ 1) → (∀ u, |v u| ≤ 2) → ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 →
        |eval x p| ≤ B ∧ |eval (x + ε • v) p| ≤ B ∧ |directionalDerivative p x v| ≤ B
          ∧ |secondDirectionalDerivative p x v| ≤ B ∧ |lineRemainder p x v ε| ≤ B * ε ^ 3 := by
  refine MvPolynomial.induction_on (motive := fun q ↦ ∃ B : ℝ, 0 ≤ B ∧
      ∀ x v : FrequencyVariable Deme Locus Allele → ℝ, (∀ u, |x u| ≤ 1) → (∀ u, |v u| ≤ 2) →
        ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 →
          |eval x q| ≤ B ∧ |eval (x + ε • v) q| ≤ B ∧ |directionalDerivative q x v| ≤ B
            ∧ |secondDirectionalDerivative q x v| ≤ B ∧ |lineRemainder q x v ε| ≤ B * ε ^ 3)
    p ?_ ?_ ?_
  · intro a
    refine ⟨|a|, abs_nonneg a, fun x v _ _ ε hε0 _ ↦ ?_⟩
    rw [directionalDerivative_C, secondDirectionalDerivative_C, lineRemainder_C, eval_C, eval_C,
      abs_zero]
    exact ⟨le_rfl, le_rfl, abs_nonneg a, abs_nonneg a,
      mul_nonneg (abs_nonneg a) (pow_nonneg hε0 3)⟩
  · rintro q r ⟨Bq, hBq, hq⟩ ⟨Br, hBr, hr⟩
    refine ⟨Bq + Br, add_nonneg hBq hBr, fun x v hx hv ε hε0 hε1 ↦ ?_⟩
    obtain ⟨hq1, hq2, hq3, hq4, hq5⟩ := hq x v hx hv ε hε0 hε1
    obtain ⟨hr1, hr2, hr3, hr4, hr5⟩ := hr x v hx hv ε hε0 hε1
    rw [map_add, map_add, directionalDerivative_add, secondDirectionalDerivative_add,
      lineRemainder_add]
    refine ⟨(abs_add_le _ _).trans (add_le_add hq1 hr1),
      (abs_add_le _ _).trans (add_le_add hq2 hr2), (abs_add_le _ _).trans (add_le_add hq3 hr3),
      (abs_add_le _ _).trans (add_le_add hq4 hr4), ?_⟩
    calc |lineRemainder q x v ε + lineRemainder r x v ε|
        ≤ |lineRemainder q x v ε| + |lineRemainder r x v ε| := abs_add_le _ _
      _ ≤ Bq * ε ^ 3 + Br * ε ^ 3 := add_le_add hq5 hr5
      _ = (Bq + Br) * ε ^ 3 := by ring
  · rintro q n ⟨B, hB, hq⟩
    refine ⟨5 * B, by linarith, fun x v hx hv ε hε0 hε1 ↦ ?_⟩
    obtain ⟨h1, h2, h3, h4, h5⟩ := hq x v hx hv ε hε0 hε1
    have hxn : |x n| ≤ 1 := hx n
    have hvn : |v n| ≤ 2 := hv n
    have hε3 : 0 ≤ ε ^ 3 := pow_nonneg hε0 3
    have hyn : |x n + ε * v n| ≤ 3 := by
      calc |x n + ε * v n| ≤ |x n| + |ε * v n| := abs_add_le _ _
        _ = |x n| + ε * |v n| := by rw [abs_mul, abs_of_nonneg hε0]
        _ ≤ 1 + 1 * 2 := add_le_add hxn (mul_le_mul hε1 hvn (abs_nonneg _) zero_le_one)
        _ = 3 := by norm_num
    have heval : eval (x + ε • v) (q * X n) = eval (x + ε • v) q * (x n + ε * v n) := by
      simp only [map_mul, eval_X, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [map_mul, eval_X, abs_mul]
      nlinarith [abs_nonneg (eval x q), abs_nonneg (x n)]
    · rw [heval, abs_mul]
      nlinarith [abs_nonneg (eval (x + ε • v) q), abs_nonneg (x n + ε * v n)]
    · rw [directionalDerivative_mul_X]
      calc |directionalDerivative q x v * x n + eval x q * v n|
          ≤ |directionalDerivative q x v * x n| + |eval x q * v n| := abs_add_le _ _
        _ = |directionalDerivative q x v| * |x n| + |eval x q| * |v n| := by
          rw [abs_mul, abs_mul]
        _ ≤ B * 1 + B * 2 :=
          add_le_add (mul_le_mul h3 hxn (abs_nonneg _) hB) (mul_le_mul h1 hvn (abs_nonneg _) hB)
        _ ≤ 5 * B := by linarith
    · rw [secondDirectionalDerivative_mul_X]
      calc |secondDirectionalDerivative q x v * x n + 2 * (directionalDerivative q x v * v n)|
          ≤ |secondDirectionalDerivative q x v * x n|
            + |2 * (directionalDerivative q x v * v n)| := abs_add_le _ _
        _ = |secondDirectionalDerivative q x v| * |x n|
            + 2 * (|directionalDerivative q x v| * |v n|) := by
          rw [abs_mul, abs_mul, abs_mul, abs_two]
        _ ≤ B * 1 + 2 * (B * 2) :=
          add_le_add (mul_le_mul h4 hxn (abs_nonneg _) hB)
            (mul_le_mul_of_nonneg_left (mul_le_mul h3 hvn (abs_nonneg _) hB) zero_le_two)
        _ ≤ 5 * B := by linarith
    · rw [lineRemainder_mul_X]
      calc |ε ^ 3 / 2 * (secondDirectionalDerivative q x v * v n)
            + lineRemainder q x v ε * (x n + ε * v n)|
          ≤ |ε ^ 3 / 2 * (secondDirectionalDerivative q x v * v n)|
            + |lineRemainder q x v ε * (x n + ε * v n)| := abs_add_le _ _
        _ = ε ^ 3 / 2 * (|secondDirectionalDerivative q x v| * |v n|)
            + |lineRemainder q x v ε| * |x n + ε * v n| := by
          rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (div_nonneg hε3 zero_le_two)]
        _ ≤ ε ^ 3 / 2 * (B * 2) + B * ε ^ 3 * 3 :=
          add_le_add
            (mul_le_mul_of_nonneg_left (mul_le_mul h4 hvn (abs_nonneg _) hB)
              (div_nonneg hε3 zero_le_two))
            (mul_le_mul h5 hyn (abs_nonneg _) (mul_nonneg hB hε3))
        _ ≤ 5 * B * ε ^ 3 := by nlinarith [mul_nonneg hB hε3]

end

end Descent.Portability.PartialHaplotypeLineTaylor
