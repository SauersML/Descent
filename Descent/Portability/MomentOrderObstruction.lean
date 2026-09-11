/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.RadialInterpolation
import Mathlib.Algebra.Group.ForwardDiff

assert_below Descent.Decision Descent.Program

/-!
# No fixed joint-moment order identifies an expected fitted report

DC Lemmas 8.1 and 8.2. For every `k` the alternating binomial weights of order `k+1`,
split by sign, give two finitely supported laws on the arithmetic progression
`a, a+h, …, a+(k+1)h` with identical moments through degree `k`, and their expectations
of a test function differ by exactly `2^{-k}` times its `(k+1)`-st finite difference.
The hypotheses are the manuscript's domain conditions: a polynomial of degree at most
`k` for the matching statement, a nonzero finite difference for the separation.

The annihilation step is Mathlib's `Polynomial.fwdDiff_iter_eq_zero_of_degree_lt`. The
step from "real analytic and not a polynomial" to "some finite difference is nonzero"
is a Taylor estimate that is NOT formalized here; instead each concrete report below
comes with an explicit nonzero finite difference, and the "for every finite `k`" form of
DC Theorems 8.3 and 8.4 is proved unconditionally through
`RadialInterpolation.radial_report_gap`, which needs no analyticity at all. The laws are
`Portability.weightedExp` probability vectors on `Fin (k+2)`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.MomentOrderObstruction

open Foundations fwdDiff RadialInterpolation

noncomputable section

/-- The signed binomial weight of DC equation (8.1). -/
def alternatingWeight (k j : ℕ) : ℝ := (-1) ^ j * ((k + 1).choose j : ℝ) / 2 ^ k

/-- The magnitude of the signed binomial weight is the normalized binomial
coefficient. -/
theorem abs_alternatingWeight (k j : ℕ) :
    |alternatingWeight k j| = ((k + 1).choose j : ℝ) / 2 ^ k := by
  have h1 : |(-1 : ℝ) ^ j| = 1 := by rw [abs_pow, abs_neg, abs_one, one_pow]
  have h2 : |((k + 1).choose j : ℝ)| = ((k + 1).choose j : ℝ) :=
    abs_of_nonneg (by positivity)
  have h3 : |(2 : ℝ) ^ k| = 2 ^ k := abs_of_nonneg (by positivity)
  unfold alternatingWeight
  rw [abs_div, abs_mul, h1, h2, h3, one_mul]

/-- **The annihilation identity.** The alternating binomial weights of order `k+1` kill
every polynomial of degree at most `k` sampled on an arithmetic progression. -/
theorem alternating_annihilates (k : ℕ) (a step : ℝ) (P : Polynomial ℝ)
    (hdeg : P.natDegree ≤ k) :
    ∑ j ∈ Finset.range (k + 2),
      (-1 : ℝ) ^ j * ((k + 1).choose j : ℝ) * P.eval (a + j * step) = 0 := by
  set Q : Polynomial ℝ := P.comp (Polynomial.C step * Polynomial.X + Polynomial.C a)
    with hQdef
  have hlin : (Polynomial.C step * Polynomial.X + Polynomial.C a).natDegree ≤ 1 := by
    refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ ?_)
    · exact Polynomial.natDegree_mul_le.trans (by simp)
    · simp
  have hQdeg : Q.natDegree < k + 1 := by
    refine lt_of_le_of_lt (Polynomial.natDegree_comp_le.trans ?_) (Nat.lt_succ_self k)
    calc P.natDegree * (Polynomial.C step * Polynomial.X + Polynomial.C a).natDegree
        ≤ P.natDegree * 1 := Nat.mul_le_mul_left _ hlin
      _ = P.natDegree := by ring
      _ ≤ k := hdeg
  have hzero : Δ_[(1 : ℝ)]^[k + 1] Q.eval = 0 :=
    Polynomial.fwdDiff_iter_eq_zero_of_degree_lt hQdeg
  have hexp := fwdDiff_iter_eq_sum_shift (1 : ℝ) Q.eval (k + 1) 0
  rw [hzero] at hexp
  have hval : ∀ j : ℕ, Q.eval ((0 : ℝ) + (j : ℕ) • (1 : ℝ)) = P.eval (a + j * step) := by
    intro j
    simp only [hQdef, Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_X, nsmul_eq_mul, mul_one, zero_add]
    ring_nf
  have hsum : ∑ j ∈ Finset.range (k + 2),
      ((-1 : ℝ) ^ (k + 1 - j) * ((k + 1).choose j : ℝ)) * P.eval (a + j * step) = 0 := by
    have := hexp.symm
    simp only [Pi.zero_apply] at this
    rw [← this]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [← hval j, zsmul_eq_mul]
    push_cast
    ring
  have hsign : ∀ j ∈ Finset.range (k + 2),
      ((-1 : ℝ) ^ (k + 1 - j) * ((k + 1).choose j : ℝ)) * P.eval (a + j * step) =
        (-1 : ℝ) ^ (k + 1) *
          ((-1 : ℝ) ^ j * ((k + 1).choose j : ℝ) * P.eval (a + j * step)) := by
    intro j hj
    have hjle : j ≤ k + 1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have hsq : ((-1 : ℝ) ^ j) * ((-1 : ℝ) ^ j) = 1 := by
      rw [← pow_add]
      exact Even.neg_one_pow ⟨j, rfl⟩
    have hcancel : (-1 : ℝ) ^ (k + 1 - j) * (-1 : ℝ) ^ j = (-1 : ℝ) ^ (k + 1) := by
      rw [← pow_add, Nat.sub_add_cancel hjle]
    have hkey : (-1 : ℝ) ^ (k + 1 - j) = (-1 : ℝ) ^ (k + 1) * (-1 : ℝ) ^ j := by
      calc (-1 : ℝ) ^ (k + 1 - j)
          = (-1 : ℝ) ^ (k + 1 - j) * ((-1 : ℝ) ^ j * (-1 : ℝ) ^ j) := by rw [hsq, mul_one]
        _ = ((-1 : ℝ) ^ (k + 1 - j) * (-1 : ℝ) ^ j) * (-1 : ℝ) ^ j := by ring
        _ = (-1 : ℝ) ^ (k + 1) * (-1 : ℝ) ^ j := by rw [hcancel]
    rw [hkey]; ring
  rw [Finset.sum_congr rfl hsign, ← Finset.mul_sum] at hsum
  have hne : ((-1 : ℝ) ^ (k + 1)) ≠ 0 := by
    intro hc
    have := abs_eq_zero.mpr hc
    rw [abs_pow, abs_neg, abs_one, one_pow] at this
    norm_num at this
  exact (mul_eq_zero.mp hsum).resolve_left hne

/-- The signed binomial weights sum to zero, so the two parity laws are both
normalized. -/
theorem sum_alternatingWeight (k : ℕ) :
    ∑ j ∈ Finset.range (k + 2), alternatingWeight k j = 0 := by
  have h := alternating_annihilates k 0 0 1 (by simp)
  simp only [Polynomial.eval_one, mul_one] at h
  unfold alternatingWeight
  rw [← Finset.sum_div, h, zero_div]

/-- The signed binomial weights have total variation two. -/
theorem sum_abs_alternatingWeight (k : ℕ) :
    ∑ j ∈ Finset.range (k + 2), |alternatingWeight k j| = 2 := by
  have h2k : ((2 : ℝ) ^ k) ≠ 0 := by positivity
  have hnat : ∑ j ∈ Finset.range (k + 2), ((k + 1).choose j : ℝ) = 2 ^ (k + 1) := by
    exact_mod_cast Nat.sum_range_choose (k + 1)
  simp only [abs_alternatingWeight]
  rw [← Finset.sum_div, hnat, pow_succ]
  field_simp

/-- The parity laws `P₊` (`s = false`) and `P₋` (`s = true`) of DC equation (8.1). -/
def parityMass (k : ℕ) (s : Bool) (j : ℕ) : ℝ :=
  if s then (|alternatingWeight k j| - alternatingWeight k j) / 2
  else (|alternatingWeight k j| + alternatingWeight k j) / 2

/-- Each parity mass is nonnegative. -/
theorem parityMass_nonneg (k : ℕ) (s : Bool) (j : ℕ) : 0 ≤ parityMass k s j := by
  unfold parityMass
  split
  · linarith [le_abs_self (alternatingWeight k j)]
  · linarith [neg_abs_le (alternatingWeight k j)]

/-- Each parity law is a probability law. -/
theorem parityMass_sum (k : ℕ) (s : Bool) :
    ∑ j : Fin (k + 2), parityMass k s j = 1 := by
  rw [Fin.sum_univ_eq_sum_range (fun j ↦ parityMass k s j) (k + 2)]
  have hsplit : ∀ j : ℕ, parityMass k s j =
      (|alternatingWeight k j| + (if s then -1 else 1) * alternatingWeight k j) / 2 := by
    intro j
    unfold parityMass
    split <;> ring
  rw [Finset.sum_congr rfl fun j _ ↦ hsplit j, ← Finset.sum_div, Finset.sum_add_distrib,
    ← Finset.mul_sum, sum_alternatingWeight, sum_abs_alternatingWeight]
  ring

/-- The two moment-matched expectations of DC Lemma 8.1. -/
def parityExp (k : ℕ) (s : Bool) : ExpFunctional (Fin (k + 2)) :=
  weightedExp (fun j ↦ parityMass k s j) (fun j ↦ parityMass_nonneg k s j)
    (parityMass_sum k s)

/-- **DC Lemma 8.1, gap formula.** The two parity laws differ on any test function by
exactly `2^{-k}` times its `(k+1)`-st finite difference along the progression. -/
theorem parity_gap (k : ℕ) (a step : ℝ) (f : ℝ → ℝ) :
    parityExp k false (fun j ↦ f (a + (j : ℕ) * step)) -
        parityExp k true (fun j ↦ f (a + (j : ℕ) * step)) =
      (∑ j ∈ Finset.range (k + 2),
        (-1 : ℝ) ^ j * ((k + 1).choose j : ℝ) * f (a + j * step)) / 2 ^ k := by
  simp only [parityExp, weightedExp_apply]
  rw [← Finset.sum_sub_distrib,
    Fin.sum_univ_eq_sum_range
      (fun j ↦ parityMass k false j * f (a + j * step) -
        parityMass k true j * f (a + j * step)) (k + 2),
    Finset.sum_div]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  have hdiff : parityMass k false j - parityMass k true j = alternatingWeight k j := by
    have h0 : parityMass k false j =
        (|alternatingWeight k j| + alternatingWeight k j) / 2 := rfl
    have h1 : parityMass k true j =
        (|alternatingWeight k j| - alternatingWeight k j) / 2 := rfl
    rw [h0, h1]; ring
  have hfac : parityMass k false j * f (a + j * step) -
      parityMass k true j * f (a + j * step) =
        (parityMass k false j - parityMass k true j) * f (a + j * step) := by ring
  rw [hfac, hdiff]
  unfold alternatingWeight
  ring

/-- **DC Lemma 8.1, moment matching.** The two parity laws share every moment through
degree `k`. -/
theorem parity_moment_match (k : ℕ) (a step : ℝ) (P : Polynomial ℝ)
    (hdeg : P.natDegree ≤ k) :
    parityExp k false (fun j ↦ P.eval (a + (j : ℕ) * step)) =
      parityExp k true (fun j ↦ P.eval (a + (j : ℕ) * step)) := by
  have h := parity_gap k a step (fun x ↦ P.eval x)
  rw [alternating_annihilates k a step P hdeg, zero_div] at h
  linarith

/-- **DC Lemma 8.2, usable form.** A nonzero `(k+1)`-st finite difference separates the
two moment-matched laws. The manuscript deduces such a finite difference from real
analyticity and nonpolynomiality by a Taylor estimate; that deduction is not formalized
here, and every application below supplies the finite difference explicitly. -/
theorem parity_separates (k : ℕ) (a step : ℝ) (f : ℝ → ℝ)
    (hne : ∑ j ∈ Finset.range (k + 2),
      (-1 : ℝ) ^ j * ((k + 1).choose j : ℝ) * f (a + j * step) ≠ 0) :
    parityExp k false (fun j ↦ f (a + (j : ℕ) * step)) ≠
      parityExp k true (fun j ↦ f (a + (j : ℕ) * step)) := by
  intro hEq
  have h := parity_gap k a step f
  rw [hEq, sub_self] at h
  have h2k : ((2 : ℝ) ^ k) ≠ 0 := by positivity
  exact hne (by field_simp at h; linarith [h])

/-- **DC Lemma 8.1 on the unit progression.** The gap formula with `a = 0` and step `1`. -/
theorem parity_gap_nodes (k : ℕ) (f : ℝ → ℝ) :
    parityExp k false (fun j ↦ f ((j : ℕ) : ℝ)) -
        parityExp k true (fun j ↦ f ((j : ℕ) : ℝ)) =
      (∑ j ∈ Finset.range (k + 2),
        (-1 : ℝ) ^ j * ((k + 1).choose j : ℝ) * f j) / 2 ^ k := by
  simpa using parity_gap k 0 1 f

section GroupReport

variable {N : Type*} [Fintype N] [DecidableEq N]

/-- Scaling the right argument scales the inner sum. -/
theorem dot_smul_right (t : ℝ) (x y : N → ℝ) : dot x (t • y) = t * dot x y := by
  simp only [dot, Descent.Core.innerSum, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ ↦ by ring

/-- **DC Proposition 7.1, equation (7.2).** The exact group partial squared correlation
of a residualized phenotype against a residualized score. -/
def partialR2 (z r : N → ℝ) : ℝ := dot z r ^ 2 / (dot z z * dot r r)

/-- The group report is invariant under nonzero rescaling of the phenotype, which is
what makes it a scale-invariant report in the sense of PL Theorem 7.2. -/
theorem partialR2_smul (z r : N → ℝ) (t : ℝ) (ht : t ≠ 0) :
    partialR2 z (t • r) = partialR2 z r := by
  have ht2 : (t ^ 2) ≠ 0 := pow_ne_zero 2 ht
  have h1 : dot z (t • r) = t * dot z r := dot_smul_right t z r
  have h2 : dot (t • r) (t • r) = t ^ 2 * dot r r := by
    simp only [dot, Descent.Core.innerSum, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ ↦ by ring
  unfold partialR2
  rw [h1, h2,
    show (t * dot z r) ^ 2 = t ^ 2 * dot z r ^ 2 by ring,
    show dot z z * (t ^ 2 * dot r r) = t ^ 2 * (dot z z * dot r r) by ring]
  exact mul_div_mul_left _ _ ht2

/-- The group report of the residualized score itself is one. -/
theorem partialR2_self (z : N → ℝ) (hz : dot z z ≠ 0) : partialR2 z z = 1 := by
  unfold partialR2
  rw [sq]
  exact div_self (mul_ne_zero hz hz)

/-- The group report of an orthogonal direction is zero. -/
theorem partialR2_orthogonal (z u : N → ℝ) (hzu : dot z u = 0) : partialR2 z u = 0 := by
  unfold partialR2
  rw [hzu]
  norm_num

/-- The outcome line `y(x) = x z + u` of DC Theorem 8.3. -/
def lineOutcome (z u : N → ℝ) (x : ℝ) : N → ℝ := fun i ↦ x * z i + u i

/-- **DC equation (8.2).** On the outcome line through an orthogonal template of equal
norm, the group report is exactly `x² / (1 + x²)`. -/
theorem partialR2_line (z u : N → ℝ) (hzu : dot z u = 0) (hnorm : dot u u = dot z z)
    (hz : dot z z ≠ 0) (x : ℝ) :
    partialR2 z (lineOutcome z u x) = x ^ 2 / (1 + x ^ 2) := by
  have hx : (1 : ℝ) + x ^ 2 ≠ 0 := by positivity
  have h1 : dot z (lineOutcome z u x) = x * dot z z + dot z u := by
    simp only [dot, Descent.Core.innerSum, lineOutcome, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ ↦ by ring
  have h2 : dot (lineOutcome z u x) (lineOutcome z u x) =
      x ^ 2 * dot z z + 2 * x * dot z u + dot u u := by
    simp only [dot, Descent.Core.innerSum, lineOutcome, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ ↦ by ring
  have hdd : dot z z * dot z z ≠ 0 := mul_ne_zero hz hz
  unfold partialR2
  rw [h1, h2, hzu, hnorm,
    show (x * dot z z + 0) ^ 2 = dot z z * dot z z * x ^ 2 by ring,
    show dot z z * (x ^ 2 * dot z z + 2 * x * 0 + dot z z) =
      dot z z * dot z z * (1 + x ^ 2) by ring]
  exact mul_div_mul_left _ _ hdd

/-- **DC Theorem 8.3, exact fourth-order instance, equation (8.3).** The two order-four
parity laws on `0,…,5`, pushed through the outcome line, give expected partial squared
correlations differing by exactly `27/1768`. -/
theorem partial_r2_fourth_order_gap (z u : N → ℝ) (hzu : dot z u = 0)
    (hnorm : dot u u = dot z z) (hz : dot z z ≠ 0) :
    parityExp 4 false (fun j ↦ partialR2 z (lineOutcome z u ((j : ℕ) : ℝ))) -
        parityExp 4 true (fun j ↦ partialR2 z (lineOutcome z u ((j : ℕ) : ℝ))) =
      27 / 1768 := by
  have hval : ∀ x : ℝ, partialR2 z (lineOutcome z u x) = x ^ 2 / (1 + x ^ 2) :=
    partialR2_line z u hzu hnorm hz
  rw [parity_gap_nodes 4 (fun x ↦ partialR2 z (lineOutcome z u x))]
  simp only [hval]
  norm_num [Finset.sum_range_succ, Nat.choose]

/-- **DC Theorem 8.3, every finite order.** For every `k` and every choice of `k+1`
distinct positive radii, the two radial laws share every joint raw moment of total
degree at most `k` yet report partial squared correlations differing by the reciprocal
of the weight total variation, which is nonzero. -/
theorem partial_r2_no_finite_moment_order {k : ℕ} (r : Fin (k + 1) → ℝ)
    (hinj : Function.Injective r) (hpos : ∀ i, 0 < r i) (z u : N → ℝ)
    (hzu : dot z u = 0) (hz : dot z z ≠ 0) :
    (∀ α : N → ℕ, ∑ i, α i ≤ k →
        radialExp r hinj false (fun w ↦ monomialEval α (radialPoint r z u w)) =
          radialExp r hinj true (fun w ↦ monomialEval α (radialPoint r z u w))) ∧
      radialExp r hinj false (fun w ↦ partialR2 z (radialPoint r z u w)) -
          radialExp r hinj true (fun w ↦ partialR2 z (radialPoint r z u w)) =
        1 / radialTotal r := by
  refine ⟨fun α hα ↦ radial_moment_match r hinj z u α hα, ?_⟩
  have hgap := radial_report_gap r hinj hpos z u (partialR2 z)
    (fun t ht y ↦ partialR2_smul z y t ht.ne')
  rw [hgap, partialR2_self z hz, partialR2_orthogonal z u hzu, sub_zero]

end GroupReport

section IndividualReport

/-- A six-subject column written coordinatewise. -/
def vec6 (a b c d e f : ℝ) : Fin 6 → ℝ :=
  fun i ↦ if (i : ℕ) = 0 then a else if (i : ℕ) = 1 then b else if (i : ℕ) = 2 then c
    else if (i : ℕ) = 3 then d else if (i : ℕ) = 4 then e else f

/-- Coordinatewise evaluation of a six-subject column. -/
theorem vec6_apply (a b c d e f : ℝ) :
    vec6 a b c d e f 0 = a ∧ vec6 a b c d e f 1 = b ∧ vec6 a b c d e f 2 = c ∧
      vec6 a b c d e f 3 = d ∧ vec6 a b c d e f 4 = e ∧ vec6 a b c d e f 5 = f :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Coordinatewise squaring of a six-subject column. -/
theorem vec6_sq (a b c d e f : ℝ) :
    (fun i ↦ vec6 a b c d e f i ^ 2) =
      vec6 (a ^ 2) (b ^ 2) (c ^ 2) (d ^ 2) (e ^ 2) (f ^ 2) := by
  funext i
  fin_cases i <;> rfl

/-- The inner sum of two six-subject columns. -/
theorem dot_vec6 (a b c d e f a' b' c' d' e' f' : ℝ) :
    dot (vec6 a b c d e f) (vec6 a' b' c' d' e' f') =
      a * a' + b * b' + c * c' + d * d' + e * e' + f * f' := by
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := vec6_apply a b c d e f
  obtain ⟨g0, g1, g2, g3, g4, g5⟩ := vec6_apply a' b' c' d' e' f'
  simp only [dot, Descent.Core.innerSum, Fin.sum_univ_six, h0, h1, h2, h3, h4, h5,
    g0, g1, g2, g3, g4, g5]

/-- The two-bin loss-regression projection `P_H` of DC Theorem 8.4: subjects `0,1` form
the first bin and `2,3,4,5` the second. -/
def binProjection (l : Fin 6 → ℝ) : Fin 6 → ℝ :=
  fun i ↦ if (i : ℕ) < 2 then (l 0 + l 1) / 2 else (l 2 + l 3 + l 4 + l 5) / 4

/-- The intercept projection `P_1`: the grand mean. -/
def meanProjection (l : Fin 6 → ℝ) : Fin 6 → ℝ :=
  fun _ ↦ (l 0 + l 1 + l 2 + l 3 + l 4 + l 5) / 6

/-- `binProjection` really is the orthogonal projection onto the two-bin design: the
residual is orthogonal to every vector constant on each bin. -/
theorem binProjection_orthogonal (l : Fin 6 → ℝ) (a b : ℝ) :
    dot (fun i ↦ l i - binProjection l i) (fun i ↦ if (i : ℕ) < 2 then a else b) = 0 := by
  simp only [dot, Descent.Core.innerSum, binProjection, Fin.sum_univ_six]
  norm_num
  ring

/-- `meanProjection` really is the orthogonal projection onto the intercept. -/
theorem meanProjection_orthogonal (l : Fin 6 → ℝ) (a : ℝ) :
    dot (fun i ↦ l i - meanProjection l i) (fun _ ↦ a) = 0 := by
  simp only [dot, Descent.Core.innerSum, meanProjection, Fin.sum_univ_six]
  ring

/-- The explained centered sum `ℓᵀ(P_H - P_1)ℓ` of DC equation (7.4). -/
def explainedSum (l : Fin 6 → ℝ) : ℝ := dot l (binProjection l) - dot l (meanProjection l)

/-- The total centered sum `ℓᵀ(I - P_1)ℓ` of DC equation (7.4). -/
def centeredSum (l : Fin 6 → ℝ) : ℝ := dot l l - dot l (meanProjection l)

/-- **DC Proposition 7.2, equation (7.4).** The fitted individual loss-explainability
report of a squared-loss vector. -/
def fittedLossExplainability (l : Fin 6 → ℝ) : ℝ := explainedSum l / centeredSum l

/-- The fitted individual report of an outcome vector: square the residuals, then (7.4).
On this design every residualization in DC equation (7.3) is the identity, by
`lineResidual_orthogonal`. -/
def lossReport (y : Fin 6 → ℝ) : ℝ := fittedLossExplainability (fun i ↦ y i ^ 2)

/-- The explained sum in closed form: bin sizes times squared bin means, minus the
grand-mean term. -/
theorem explainedSum_closed (l : Fin 6 → ℝ) :
    explainedSum l = 2 * ((l 0 + l 1) / 2) ^ 2 + 4 * ((l 2 + l 3 + l 4 + l 5) / 4) ^ 2 -
      6 * ((l 0 + l 1 + l 2 + l 3 + l 4 + l 5) / 6) ^ 2 := by
  simp only [explainedSum, dot, Descent.Core.innerSum, binProjection, meanProjection,
    Fin.sum_univ_six]
  norm_num
  ring

/-- The total centered sum in closed form. -/
theorem centeredSum_closed (l : Fin 6 → ℝ) :
    centeredSum l = (l 0 ^ 2 + l 1 ^ 2 + l 2 ^ 2 + l 3 ^ 2 + l 4 ^ 2 + l 5 ^ 2) -
      6 * ((l 0 + l 1 + l 2 + l 3 + l 4 + l 5) / 6) ^ 2 := by
  simp only [centeredSum, dot, Descent.Core.innerSum, meanProjection, Fin.sum_univ_six]
  ring

/-- The explained sum of a coordinatewise column. -/
theorem explainedSum_vec6 (a b c d e f : ℝ) :
    explainedSum (vec6 a b c d e f) =
      2 * ((a + b) / 2) ^ 2 + 4 * ((c + d + e + f) / 4) ^ 2 -
        6 * ((a + b + c + d + e + f) / 6) ^ 2 := by
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := vec6_apply a b c d e f
  rw [explainedSum_closed, h0, h1, h2, h3, h4, h5]

/-- The total centered sum of a coordinatewise column. -/
theorem centeredSum_vec6 (a b c d e f : ℝ) :
    centeredSum (vec6 a b c d e f) =
      (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 + e ^ 2 + f ^ 2) -
        6 * ((a + b + c + d + e + f) / 6) ^ 2 := by
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := vec6_apply a b c d e f
  rw [centeredSum_closed, h0, h1, h2, h3, h4, h5]

/-- The outcome line of DC Theorem 8.4. -/
def lineResidual (x : ℝ) : Fin 6 → ℝ := vec6 1 (-1) x (-x) 0 0

/-- The outcome line is orthogonal to the intercept, to both bin indicators, and to the
score, so every residualization in DC equation (7.3) leaves it unchanged. -/
theorem lineResidual_orthogonal (x : ℝ) :
    dot (lineResidual x) (vec6 1 1 1 1 1 1) = 0 ∧
      dot (lineResidual x) (vec6 1 1 0 0 0 0) = 0 ∧
      dot (lineResidual x) (vec6 0 0 1 1 1 1) = 0 ∧
      dot (lineResidual x) (vec6 1 1 (-1) (-1) 0 0) = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    · rw [lineResidual, dot_vec6]
      ring

/-- **DC equation (8.4).** On the outcome line the fitted individual report is exactly
`(x² - 2)² / (4 (x⁴ - x² + 1))`. -/
theorem lossReport_line (x : ℝ) :
    lossReport (lineResidual x) = (x ^ 2 - 2) ^ 2 / (4 * (x ^ 4 - x ^ 2 + 1)) := by
  have hden : (0 : ℝ) < x ^ 4 - x ^ 2 + 1 := by nlinarith [sq_nonneg (x ^ 2 - 1 / 2)]
  have h1 : (4 : ℝ) * (x ^ 4 - x ^ 2 + 1) / 3 ≠ 0 := by intro hc; linarith
  have h2 : (4 : ℝ) * (x ^ 4 - x ^ 2 + 1) ≠ 0 := by intro hc; linarith
  have hE : explainedSum (vec6 ((1 : ℝ) ^ 2) ((-1 : ℝ) ^ 2) (x ^ 2) ((-x) ^ 2)
      ((0 : ℝ) ^ 2) ((0 : ℝ) ^ 2)) = (x ^ 2 - 2) ^ 2 / 3 := by
    rw [explainedSum_vec6]; ring
  have hC : centeredSum (vec6 ((1 : ℝ) ^ 2) ((-1 : ℝ) ^ 2) (x ^ 2) ((-x) ^ 2)
      ((0 : ℝ) ^ 2) ((0 : ℝ) ^ 2)) = 4 * (x ^ 4 - x ^ 2 + 1) / 3 := by
    rw [centeredSum_vec6]; ring
  unfold lossReport
  rw [lineResidual, vec6_sq]
  unfold fittedLossExplainability
  rw [hE, hC, div_eq_div_iff h1 h2]
  ring

/-- The explained centered sum is homogeneous of degree two in the loss vector. -/
theorem explainedSum_smul (c : ℝ) (l : Fin 6 → ℝ) :
    explainedSum (fun i ↦ c * l i) = c ^ 2 * explainedSum l := by
  simp only [explainedSum_closed]
  ring

/-- The total centered sum is homogeneous of degree two in the loss vector. -/
theorem centeredSum_smul (c : ℝ) (l : Fin 6 → ℝ) :
    centeredSum (fun i ↦ c * l i) = c ^ 2 * centeredSum l := by
  simp only [centeredSum_closed]
  ring

/-- The fitted individual report is invariant under nonzero rescaling of the outcome
vector, which is what makes it a scale-invariant report. -/
theorem lossReport_smul (t : ℝ) (ht : t ≠ 0) (y : Fin 6 → ℝ) :
    lossReport (t • y) = lossReport y := by
  have ht2 : ((t ^ 2) ^ 2 : ℝ) ≠ 0 := pow_ne_zero 2 (pow_ne_zero 2 ht)
  have hsq : (fun i ↦ (t • y) i ^ 2) = fun i ↦ t ^ 2 * y i ^ 2 := by
    funext i
    simp [mul_pow]
  unfold lossReport fittedLossExplainability
  rw [hsq, explainedSum_smul, centeredSum_smul]
  exact mul_div_mul_left _ _ ht2

/-- **DC Theorem 8.4, exact fourth-order instance, equation (8.5).** The two order-four
parity laws give expected fitted loss-explainability differing by exactly
`-24900075/1099632872`. -/
theorem loss_report_fourth_order_gap :
    parityExp 4 false (fun j ↦ lossReport (lineResidual ((j : ℕ) : ℝ))) -
        parityExp 4 true (fun j ↦ lossReport (lineResidual ((j : ℕ) : ℝ))) =
      -(24900075 / 1099632872) := by
  rw [parity_gap_nodes 4 (fun x ↦ lossReport (lineResidual x))]
  simp only [lossReport_line]
  norm_num [Finset.sum_range_succ, Nat.choose]

/-- **DC Theorem 8.4, every finite order.** For every `k` and every choice of `k+1`
distinct positive radii, the two radial laws on the templates `y(0)` and `y(1)` share
every joint raw moment of total degree at most `k` yet report fitted individual
loss-explainability differing by `3/4` divided by the weight total variation. -/
theorem loss_report_no_finite_moment_order {k : ℕ} (r : Fin (k + 1) → ℝ)
    (hinj : Function.Injective r) (hpos : ∀ i, 0 < r i) :
    (∀ α : Fin 6 → ℕ, ∑ i, α i ≤ k →
        radialExp r hinj false (fun w ↦ monomialEval α
            (radialPoint r (lineResidual 0) (lineResidual 1) w)) =
          radialExp r hinj true (fun w ↦ monomialEval α
            (radialPoint r (lineResidual 0) (lineResidual 1) w))) ∧
      radialExp r hinj false
          (fun w ↦ lossReport (radialPoint r (lineResidual 0) (lineResidual 1) w)) -
        radialExp r hinj true
          (fun w ↦ lossReport (radialPoint r (lineResidual 0) (lineResidual 1) w)) =
        (3 / 4) / radialTotal r := by
  refine ⟨fun α hα ↦ radial_moment_match r hinj _ _ α hα, ?_⟩
  have hgap := radial_report_gap r hinj hpos (lineResidual 0) (lineResidual 1) lossReport
    (fun t ht y ↦ lossReport_smul t ht.ne' y)
  rw [hgap, lossReport_line 0, lossReport_line 1]
  norm_num

end IndividualReport

end

end Descent.Portability.MomentOrderObstruction
