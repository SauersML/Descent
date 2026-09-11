/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.TurnoverArchitectureMetrics

assert_below Descent.Decision Descent.Program

/-!
# Dependence enters the accuracy report through a quadratic-variation term

This module formalizes DC Theorem 4.4 and PL Theorem 5.2 in the discrete skeleton of
`Descent.Portability.ConvexOrderCoupling`: a family of one-step kernels on `{0,1}ⁿ`
indexed by the entire past, each row a probability vector flipping every coordinate with
probability `τ λ`, which is PL (5.4) written for a skeleton and imposes no independence,
exchangeability or Markov property.

The weighted alignment `A_σ = ∑ wᵢσᵢ` of
`Descent.Portability.TurnoverArchitectureMetrics.alignment` then has a drift fixed by the
coordinate rates alone, so `E A` -- and therefore the mean squared error report -- is the
same for every admissible coupling. Its square does not: one step satisfies exactly
`E A'² = (1 - 4τλ) A² + Γ`, where `Γ = ∑ K (A' - A)²` is the quadratic variation of the
alignment, nonnegative and zero only for couplings whose jumps leave `A` unchanged. That
identity is DC (4.8) and PL (5.5) in skeleton form, and it makes the excess accuracy a
property of the geometry of joint jumps, not of one-coordinate frequencies.

At the source-aligned state the sharp bounds `4τλ ∑ wᵢ² ≤ Γ ≤ 4τλ` of PL (5.6) hold, so
the fastest allowed one-step decline of `E A²` is controlled by the weight concentration
`∑ wᵢ²`.

Domain conditions: nonnegative score weights summing to one, a nonnegative flip
probability, and (for the multi-step excess bound) a step short enough that `1 - 4τλ ≥ 0`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.TurnoverQuadraticVariation

open Foundations TurnoverArchitectureMetrics

noncomputable section

/-! ## The weight carried by the flipped loci -/

/-- Sum of squares is at most the square of the sum, for nonnegative terms. -/
theorem sum_sq_le_sq_sum {ι : Type*} [DecidableEq ι] (t : Finset ι) (x : ι → ℝ)
    (hx : ∀ i ∈ t, 0 ≤ x i) : ∑ i ∈ t, x i ^ 2 ≤ (∑ i ∈ t, x i) ^ 2 := by
  induction t using Finset.induction_on with
  | empty => simp
  | @insert j t hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj]
    have hxj : 0 ≤ x j := hx j (Finset.mem_insert_self j t)
    have hsum : 0 ≤ ∑ i ∈ t, x i :=
      Finset.sum_nonneg fun i hi ↦ hx i (Finset.mem_insert_of_mem hi)
    have hih := ih fun i hi ↦ hx i (Finset.mem_insert_of_mem hi)
    nlinarith

/-- The total score weight carried by the loci that change in one step. -/
def flipWeight {n : ℕ} (w : Fin n → ℝ) (s s' : Fin n → Bool) : ℝ :=
  ∑ i, (if s' i = s i then (0 : ℝ) else w i)

/-- The flipped weight is nonnegative. -/
theorem flipWeight_nonneg {n : ℕ} (w : Fin n → ℝ) (s s' : Fin n → Bool)
    (hw : ∀ i, 0 ≤ w i) : 0 ≤ flipWeight w s s' :=
  Finset.sum_nonneg fun i _ ↦ by
    by_cases h : s' i = s i <;> simp [h, hw i]

/-- The flipped weight is at most the total weight. -/
theorem flipWeight_le_total {n : ℕ} (w : Fin n → ℝ) (s s' : Fin n → Bool)
    (hw : ∀ i, 0 ≤ w i) : flipWeight w s s' ≤ ∑ i, w i :=
  Finset.sum_le_sum fun i _ ↦ by
    by_cases h : s' i = s i <;> simp [h, hw i]

/-- Squaring the flipped weight can only lose, when the total weight is one. -/
theorem flipWeight_sq_le {n : ℕ} (w : Fin n → ℝ) (s s' : Fin n → Bool) (hw : ∀ i, 0 ≤ w i)
    (htot : ∑ i, w i = 1) : flipWeight w s s' ^ 2 ≤ flipWeight w s s' := by
  have h0 := flipWeight_nonneg w s s' hw
  have h1 := flipWeight_le_total w s s' hw
  rw [htot] at h1
  nlinarith

/-- Squaring the flipped weight can only gain against the flipped squared weight: the
cross terms that a dependent coupling adds are exactly what is dropped here. -/
theorem flipWeight_sq_ge {n : ℕ} (w : Fin n → ℝ) (s s' : Fin n → Bool) (hw : ∀ i, 0 ≤ w i) :
    flipWeight (fun i ↦ w i ^ 2) s s' ≤ flipWeight w s s' ^ 2 := by
  have hpt : ∀ i : Fin n,
      (if s' i = s i then (0 : ℝ) else w i ^ 2)
        = (if s' i = s i then (0 : ℝ) else w i) ^ 2 := by
    intro i
    by_cases h : s' i = s i
    · rw [if_pos h, if_pos h]
      norm_num
    · rw [if_neg h, if_neg h]
  simp only [flipWeight]
  rw [Finset.sum_congr rfl fun i _ ↦ hpt i]
  exact sum_sq_le_sq_sum Finset.univ _ fun i _ ↦ by
    by_cases h : s' i = s i <;> simp [h, hw i]

/-- **The flipped weight has a coupling-independent mean.**  Summing the coordinate-flip
constraint PL (5.4) over loci gives `E[flipWeight] = τλ ∑ wᵢ`, whatever the joint geometry
of the flips. -/
theorem sum_kernel_flipWeight {n : ℕ} (w : Fin n → ℝ) (q : ℝ)
    (K : (Fin n → Bool) → (Fin n → Bool) → ℝ) (s : Fin n → Bool)
    (hflip : ∀ i : Fin n, ∑ s', (if s' i = s i then (0 : ℝ) else K s s') = q) :
    ∑ s', K s s' * flipWeight w s s' = q * ∑ i, w i := by
  have hswap : ∑ s' : Fin n → Bool, K s s' * flipWeight w s s'
      = ∑ i : Fin n, w i * ∑ s' : Fin n → Bool, (if s' i = s i then (0 : ℝ) else K s s') := by
    simp only [flipWeight, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun s' _ ↦ ?_
    by_cases h : s' i = s i
    · rw [if_pos h, if_pos h]
      ring
    · rw [if_neg h, if_neg h]
      ring
  rw [hswap]
  simp only [hflip]
  rw [← Finset.sum_mul]
  ring

/-! ## Drift and quadratic variation of the alignment -/

/-- One coordinate's mean sign contracts by exactly `1 - 2τλ` in one step. -/
theorem kernel_signValue_drift {n : ℕ} (q : ℝ)
    (K : (Fin n → Bool) → (Fin n → Bool) → ℝ) (s : Fin n → Bool) (i : Fin n)
    (hK1 : ∑ s', K s s' = 1)
    (hflip : ∑ s', (if s' i = s i then (0 : ℝ) else K s s') = q) :
    ∑ s', K s s' * signValue (s' i) = (1 - 2 * q) * signValue (s i) := by
  have hpt : ∀ s' : Fin n → Bool,
      K s s' * signValue (s' i)
        = K s s' * signValue (s i)
          + (if s' i = s i then (0 : ℝ) else K s s') * (-2 * signValue (s i)) := by
    intro s'
    by_cases h : s' i = s i
    · rw [if_pos h, h]
      ring
    · rw [if_neg h]
      have hb : signValue (s' i) = -signValue (s i) := by
        cases hs : s i <;> cases hs' : s' i <;>
          simp_all [signValue, TraitPortabilityRange.sign]
      rw [hb]
      ring
  rw [Finset.sum_congr rfl fun s' _ ↦ hpt s', Finset.sum_add_distrib, ← Finset.sum_mul,
    ← Finset.sum_mul, hK1, hflip]
  ring

/-- **PL (5.5), first identity, in skeleton form.**  The alignment's drift is fixed by the
coordinate rates: `E A' = (1 - 2τλ) A` for every admissible one-step kernel. -/
theorem kernel_alignment_drift {n : ℕ} (a : Fin n → ℝ) (q : ℝ)
    (K : (Fin n → Bool) → (Fin n → Bool) → ℝ) (s : Fin n → Bool)
    (hK1 : ∑ s', K s s' = 1)
    (hflip : ∀ i : Fin n, ∑ s', (if s' i = s i then (0 : ℝ) else K s s') = q) :
    ∑ s', K s s' * alignment a s' = (1 - 2 * q) * alignment a s := by
  have hswap : ∑ s' : Fin n → Bool, K s s' * alignment a s'
      = ∑ i : Fin n, a i ^ 2 * ∑ s' : Fin n → Bool, K s s' * signValue (s' i) := by
    simp only [alignment, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun s' _ ↦ by ring
  have hi : ∀ i : Fin n, a i ^ 2 * ∑ s' : Fin n → Bool, K s s' * signValue (s' i)
      = (1 - 2 * q) * (a i ^ 2 * signValue (s i)) := by
    intro i
    rw [kernel_signValue_drift q K s i hK1 (hflip i)]
    ring
  rw [hswap, Finset.sum_congr rfl fun i _ ↦ hi i, ← Finset.mul_sum]
  rfl

/-- **DC (4.8) / PL (5.5), second identity, in skeleton form.**  The square of the
alignment obeys an exact one-step identity whose only coupling-dependent term is the
quadratic variation `Γ = ∑ K (A' - A)²`. -/
theorem kernel_alignment_quadratic_variation {n : ℕ} (a : Fin n → ℝ) (q : ℝ)
    (K : (Fin n → Bool) → (Fin n → Bool) → ℝ) (s : Fin n → Bool)
    (hK1 : ∑ s', K s s' = 1)
    (hflip : ∀ i : Fin n, ∑ s', (if s' i = s i then (0 : ℝ) else K s s') = q) :
    ∑ s', K s s' * alignment a s' ^ 2
      = (1 - 4 * q) * alignment a s ^ 2
        + ∑ s', K s s' * (alignment a s' - alignment a s) ^ 2 := by
  have hpt : ∀ s' : Fin n → Bool,
      K s s' * alignment a s' ^ 2
        = K s s' * (alignment a s' - alignment a s) ^ 2
          + 2 * alignment a s * (K s s' * alignment a s')
          - alignment a s ^ 2 * K s s' := fun s' ↦ by ring
  rw [Finset.sum_congr rfl fun s' _ ↦ hpt s', Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, hK1, kernel_alignment_drift a q K s hK1 hflip]
  ring

/-- The quadratic variation is nonnegative: dependence can only raise the mean squared
alignment above the independent-drift value. -/
theorem quadraticVariation_nonneg {n : ℕ} (a : Fin n → ℝ)
    (K : (Fin n → Bool) → (Fin n → Bool) → ℝ) (s : Fin n → Bool)
    (hK0 : ∀ s', 0 ≤ K s s') :
    0 ≤ ∑ s', K s s' * (alignment a s' - alignment a s) ^ 2 :=
  Finset.sum_nonneg fun s' _ ↦ mul_nonneg (hK0 s') (sq_nonneg _)

/-! ## Multi-step consequences along a history-dependent coupling -/

/-- **The mean alignment is the same for every admissible coupling**: `E A_m = (1-2τλ)^m A₀`,
DC (4.5) / PL Theorem 5.2. -/
theorem pathExp_alignment {n : ℕ} (a : Fin n → ℝ) (q : ℝ)
    (K : List (Fin n → Bool) → (Fin n → Bool) → (Fin n → Bool) → ℝ)
    (hK1 : ∀ hist s, ∑ s', K hist s s' = 1)
    (hflip : ∀ (hist : List (Fin n → Bool)) (s : Fin n → Bool) (i : Fin n),
      ∑ s', (if s' i = s i then (0 : ℝ) else K hist s s') = q) (m : ℕ) :
    ∀ (hist : List (Fin n → Bool)) (s : Fin n → Bool),
      ConvexOrderCoupling.pathExp K m hist s (fun x ↦ alignment a x)
        = (1 - 2 * q) ^ m * alignment a s := by
  induction m with
  | zero => intro hist s; simp [ConvexOrderCoupling.pathExp]
  | succ m ih =>
    intro hist s
    have hpt : ∀ s' : Fin n → Bool,
        K hist s s' * ConvexOrderCoupling.pathExp K m (s :: hist) s' (fun x ↦ alignment a x)
          = (1 - 2 * q) ^ m * (K hist s s' * alignment a s') := by
      intro s'
      rw [ih (s :: hist) s']
      ring
    simp only [ConvexOrderCoupling.pathExp]
    rw [Finset.sum_congr rfl fun s' _ ↦ hpt s', ← Finset.mul_sum,
      kernel_alignment_drift a q (K hist) s (hK1 hist s) (hflip hist s)]
    ring

/-- **DC (4.5) / PL Theorem 5.2**: the mean squared error report is invariant across the
whole admissible class, because it is affine in the alignment. -/
theorem pathExp_mse_invariant {n : ℕ} (a : Fin n → ℝ) (q ν : ℝ)
    (K : List (Fin n → Bool) → (Fin n → Bool) → (Fin n → Bool) → ℝ)
    (hK1 : ∀ hist s, ∑ s', K hist s s' = 1)
    (hflip : ∀ (hist : List (Fin n → Bool)) (s : Fin n → Bool) (i : Fin n),
      ∑ s', (if s' i = s i then (0 : ℝ) else K hist s s') = q) (m : ℕ)
    (hist : List (Fin n → Bool)) (s : Fin n → Bool) :
    ConvexOrderCoupling.pathExp K m hist s (fun x ↦ ν + 2 * (1 - alignment a x))
      = ν + 2 * (1 - (1 - 2 * q) ^ m * alignment a s) := by
  have hfun : (fun x : Fin n → Bool ↦ ν + 2 * (1 - alignment a x))
      = fun x ↦ (ν + 2) + (-2) * alignment a x := by
    funext x
    ring
  rw [hfun, ConvexOrderCoupling.pathExp_affine K hK1 (ν + 2) (-2)
    (fun x ↦ alignment a x) m hist s, pathExp_alignment a q K hK1 hflip m hist s]
  ring

/-- **DC (4.8), the excess-accuracy inequality.**  Along any admissible history-dependent
coupling the mean squared alignment is at least the pure-drift value, the excess being the
accumulated quadratic variation. -/
theorem pathExp_alignment_sq_ge {n : ℕ} (a : Fin n → ℝ) (q : ℝ)
    (K : List (Fin n → Bool) → (Fin n → Bool) → (Fin n → Bool) → ℝ)
    (hK0 : ∀ hist s s', 0 ≤ K hist s s') (hK1 : ∀ hist s, ∑ s', K hist s s' = 1)
    (hflip : ∀ (hist : List (Fin n → Bool)) (s : Fin n → Bool) (i : Fin n),
      ∑ s', (if s' i = s i then (0 : ℝ) else K hist s s') = q)
    (h4 : 0 ≤ 1 - 4 * q) (m : ℕ) :
    ∀ (hist : List (Fin n → Bool)) (s : Fin n → Bool),
      (1 - 4 * q) ^ m * alignment a s ^ 2
        ≤ ConvexOrderCoupling.pathExp K m hist s (fun x ↦ alignment a x ^ 2) := by
  induction m with
  | zero => intro hist s; simp [ConvexOrderCoupling.pathExp]
  | succ m ih =>
    intro hist s
    have hstep : ∑ s' : Fin n → Bool,
        K hist s s' * ((1 - 4 * q) ^ m * alignment a s' ^ 2)
        ≤ ∑ s' : Fin n → Bool, K hist s s'
          * ConvexOrderCoupling.pathExp K m (s :: hist) s' (fun x ↦ alignment a x ^ 2) :=
      Finset.sum_le_sum fun s' _ ↦
        mul_le_mul_of_nonneg_left (ih (s :: hist) s') (hK0 hist s s')
    have hval : ∑ s' : Fin n → Bool, K hist s s' * ((1 - 4 * q) ^ m * alignment a s' ^ 2)
        = (1 - 4 * q) ^ m * ((1 - 4 * q) * alignment a s ^ 2
          + ∑ s' : Fin n → Bool, K hist s s' * (alignment a s' - alignment a s) ^ 2) := by
      have hpt : ∀ s' : Fin n → Bool,
          K hist s s' * ((1 - 4 * q) ^ m * alignment a s' ^ 2)
            = (1 - 4 * q) ^ m * (K hist s s' * alignment a s' ^ 2) := fun s' ↦ by ring
      rw [Finset.sum_congr rfl fun s' _ ↦ hpt s', ← Finset.mul_sum,
        kernel_alignment_quadratic_variation a q (K hist) s (hK1 hist s) (hflip hist s)]
    have hgam : 0 ≤ ∑ s' : Fin n → Bool,
        K hist s s' * (alignment a s' - alignment a s) ^ 2 :=
      quadraticVariation_nonneg a (K hist) s (hK0 hist s)
    have hpow : 0 ≤ (1 - 4 * q) ^ m := pow_nonneg h4 m
    simp only [ConvexOrderCoupling.pathExp]
    refine le_trans ?_ hstep
    rw [hval, pow_succ]
    nlinarith [mul_nonneg hpow hgam]

/-! ## The sharp one-step bounds at the source-aligned state, PL (5.6) -/

/-- At the source-aligned state the alignment increment is `-2` times the flipped weight. -/
theorem alignment_diff_allTrue {n : ℕ} (a : Fin n → ℝ) (s' : Fin n → Bool) :
    alignment a s' - alignment a (fun _ ↦ true)
      = -2 * flipWeight (fun i ↦ a i ^ 2) (fun _ ↦ true) s' := by
  simp only [alignment, flipWeight, ← Finset.sum_sub_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  by_cases h : s' i = true
  · rw [h]
    show a i ^ 2 * signValue true - a i ^ 2 * signValue true
      = -2 * (if (true : Bool) = true then (0 : ℝ) else a i ^ 2)
    rw [if_pos rfl]
    ring
  · have hf : s' i = false := by simpa using h
    rw [hf]
    show a i ^ 2 * signValue false - a i ^ 2 * signValue true
      = -2 * (if (false : Bool) = true then (0 : ℝ) else a i ^ 2)
    rw [if_neg (by decide)]
    show a i ^ 2 * (-1 : ℝ) - a i ^ 2 * (1 : ℝ) = -2 * a i ^ 2
    ring

/-- **PL (5.6), upper bound.**  The quadratic variation at the source-aligned state is at
most `4τλ`, attained by a synchronous all-coordinate flip. -/
theorem quadraticVariation_le {n : ℕ} (a : Fin n → ℝ) (q : ℝ)
    (hw : ∀ i, 0 ≤ a i ^ 2) (hnorm : ∑ i, a i ^ 2 = 1)
    (K : (Fin n → Bool) → (Fin n → Bool) → ℝ)
    (hK0 : ∀ s', 0 ≤ K (fun _ ↦ true) s')
    (hflip : ∀ i : Fin n,
      ∑ s', (if s' i = (fun _ : Fin n ↦ true) i then (0 : ℝ) else K (fun _ ↦ true) s') = q) :
    ∑ s', K (fun _ ↦ true) s' * (alignment a s' - alignment a (fun _ ↦ true)) ^ 2
      ≤ 4 * q := by
  have hbound : ∀ s' : Fin n → Bool,
      K (fun _ ↦ true) s' * (alignment a s' - alignment a (fun _ ↦ true)) ^ 2
        ≤ 4 * (K (fun _ ↦ true) s' * flipWeight (fun i ↦ a i ^ 2) (fun _ ↦ true) s') := by
    intro s'
    rw [alignment_diff_allTrue a s']
    have hsq := flipWeight_sq_le (fun i ↦ a i ^ 2) (fun _ ↦ true) s' hw hnorm
    nlinarith [hK0 s', hsq]
  have hsum : ∑ s' : Fin n → Bool,
      4 * (K (fun _ ↦ true) s' * flipWeight (fun i ↦ a i ^ 2) (fun _ ↦ true) s')
      = 4 * (q * ∑ i, a i ^ 2) := by
    rw [← Finset.mul_sum,
      sum_kernel_flipWeight (fun i ↦ a i ^ 2) q K (fun _ ↦ true) hflip]
  calc ∑ s' : Fin n → Bool,
        K (fun _ ↦ true) s' * (alignment a s' - alignment a (fun _ ↦ true)) ^ 2
      ≤ ∑ s' : Fin n → Bool,
        4 * (K (fun _ ↦ true) s' * flipWeight (fun i ↦ a i ^ 2) (fun _ ↦ true) s') :=
        Finset.sum_le_sum fun s' _ ↦ hbound s'
    _ = 4 * (q * ∑ i, a i ^ 2) := hsum
    _ = 4 * q := by rw [hnorm]; ring

/-- **PL (5.6), lower bound.**  The quadratic variation at the source-aligned state is at
least `4τλ ∑ wᵢ²`, attained by single-coordinate flips.  The gap between the two bounds is
exactly the effective-number-of-contributions factor `1 - ∑ wᵢ²`. -/
theorem quadraticVariation_ge {n : ℕ} (a : Fin n → ℝ) (q : ℝ)
    (hw : ∀ i, 0 ≤ a i ^ 2)
    (K : (Fin n → Bool) → (Fin n → Bool) → ℝ)
    (hK0 : ∀ s', 0 ≤ K (fun _ ↦ true) s')
    (hflip : ∀ i : Fin n,
      ∑ s', (if s' i = (fun _ : Fin n ↦ true) i then (0 : ℝ) else K (fun _ ↦ true) s') = q) :
    4 * (q * ∑ i, (a i ^ 2) ^ 2)
      ≤ ∑ s', K (fun _ ↦ true) s' * (alignment a s' - alignment a (fun _ ↦ true)) ^ 2 := by
  have hbound : ∀ s' : Fin n → Bool,
      4 * (K (fun _ ↦ true) s' * flipWeight (fun i ↦ (a i ^ 2) ^ 2) (fun _ ↦ true) s')
        ≤ K (fun _ ↦ true) s' * (alignment a s' - alignment a (fun _ ↦ true)) ^ 2 := by
    intro s'
    rw [alignment_diff_allTrue a s']
    have hsq := flipWeight_sq_ge (fun i ↦ a i ^ 2) (fun _ ↦ true) s' hw
    nlinarith [hK0 s', hsq]
  have hsum : ∑ s' : Fin n → Bool,
      4 * (K (fun _ ↦ true) s' * flipWeight (fun i ↦ (a i ^ 2) ^ 2) (fun _ ↦ true) s')
      = 4 * (q * ∑ i, (a i ^ 2) ^ 2) := by
    rw [← Finset.mul_sum,
      sum_kernel_flipWeight (fun i ↦ (a i ^ 2) ^ 2) q K (fun _ ↦ true) hflip]
  calc 4 * (q * ∑ i, (a i ^ 2) ^ 2)
      = ∑ s' : Fin n → Bool,
        4 * (K (fun _ ↦ true) s' * flipWeight (fun i ↦ (a i ^ 2) ^ 2) (fun _ ↦ true) s') :=
        hsum.symm
    _ ≤ ∑ s' : Fin n → Bool,
        K (fun _ ↦ true) s' * (alignment a s' - alignment a (fun _ ↦ true)) ^ 2 :=
        Finset.sum_le_sum fun s' _ ↦ hbound s'

end

end Descent.Portability.TurnoverQuadraticVariation
