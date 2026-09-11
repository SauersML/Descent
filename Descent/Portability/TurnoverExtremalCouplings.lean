/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.NonanticipationCost

assert_below Descent.Decision Descent.Program

/-!
# The symmetric count generator in closed form, and an explicit admissible coupling

Two things the dynamic convex-order theorem needs beyond the comparison itself.

First, the nearest-drift generator of DC (3.4) applied to the squared aggregate report
`(2k - n)²` has the exact closed form `-4λ M² + 4λ|M|` with `M = 2k - n`, for every `n`,
odd or even. That is the generator behind DC (4.8) for even `n` -- where the `4λ|M|` term
is the `4λ n e^{-2λt}` source -- and behind the odd-locus backward equations DC (4.6),
where `|M|` steps down by two at rate `λ|M|` and the extra term never vanishes because
`M = 0` is unreachable. It is stated here as one identity rather than two.

Second, `synchronousKernel` is an explicit one-step kernel on `{0,1}ⁿ`: the whole aligned
block flips with probability `τα` and the whole unaligned block with probability `τβ`,
independently of each other. Every coordinate then flips with exactly the prescribed
probability, so the kernel is admissible in the sense of DC (3.2) / PL (5.7), while the
joint law is maximally dependent. This inhabits the admissible class, so the comparison
theorems of `Descent.Portability.ConvexOrderCoupling` are not vacuous, and it is the
construction DC Theorem 3.1 uses to attain the endpoint chord bound (3.6).

Domain conditions: nonnegative rates, and a step short enough that `τα` and `τβ` are
probabilities.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.TurnoverExtremalCouplings

open Foundations NonanticipationCost TurnoverArchitectureMetrics

noncomputable section

/-! ## The symmetric generator of the squared aggregate report -/

/-- **The nearest-drift generator of `(2k - n)²` at symmetric rates**, in closed form.
With `M = 2k - n` it equals `-4λM² + 4λ|M|`.  For even `n` this is DC (4.8); for odd `n`
it is the generator of the backward equations DC (4.6), in which `|M|` steps down by two
at rate `λ|M|` and never reaches zero. -/
theorem nearestDriftGen_squareReport_symmetric (n : ℕ) (lam : ℝ) (hlam : 0 ≤ lam) (k : ℤ) :
    ConvexOrderCoupling.nearestDriftGen n lam lam (squareReport n) k
      = -4 * lam * (2 * (k : ℝ) - (n : ℝ)) ^ 2 + 4 * lam * |2 * (k : ℝ) - (n : ℝ)| := by
  have hcd : ConvexOrderCoupling.countDrift n lam lam k = -(lam * (2 * (k : ℝ) - (n : ℝ))) := by
    simp only [ConvexOrderCoupling.countDrift]
    ring
  rcases le_total 0 (2 * (k : ℝ) - (n : ℝ)) with hM | hM
  · have hup : ConvexOrderCoupling.upRate n lam lam k = 0 := by
      simp only [ConvexOrderCoupling.upRate, hcd]
      exact max_eq_right (by nlinarith)
    have hdn : ConvexOrderCoupling.downRate n lam lam k
        = lam * (2 * (k : ℝ) - (n : ℝ)) := by
      simp only [ConvexOrderCoupling.downRate, hcd, neg_neg]
      exact max_eq_left (by nlinarith)
    rw [ConvexOrderCoupling.nearestDriftGen, hup, hdn, abs_of_nonneg hM]
    simp only [squareReport]
    push_cast
    ring
  · have hup : ConvexOrderCoupling.upRate n lam lam k
        = -(lam * (2 * (k : ℝ) - (n : ℝ))) := by
      simp only [ConvexOrderCoupling.upRate, hcd]
      exact max_eq_left (by nlinarith)
    have hdn : ConvexOrderCoupling.downRate n lam lam k = 0 := by
      simp only [ConvexOrderCoupling.downRate, hcd, neg_neg]
      exact max_eq_right (by nlinarith)
    rw [ConvexOrderCoupling.nearestDriftGen, hup, hdn, abs_of_nonpos hM]
    simp only [squareReport]
    push_cast
    ring

/-! ## An explicit admissible coupling -/

/-- **The synchronous coupling.**  At any configuration the whole aligned block flips with
probability `τα` and the whole unaligned block flips with probability `τβ`, the two events
being independent.  The four reachable targets are the current configuration, the constant
`false` configuration, the constant `true` configuration and the pointwise negation. -/
def synchronousKernel (n : ℕ) (α β τ : ℝ) (s s' : Fin n → Bool) : ℝ :=
  (if s' = s then (1 - τ * α) * (1 - τ * β) else 0)
    + (if s' = fun _ ↦ false then (τ * α) * (1 - τ * β) else 0)
    + (if s' = fun _ ↦ true then (1 - τ * α) * (τ * β) else 0)
    + (if s' = fun i ↦ !s i then (τ * α) * (τ * β) else 0)

/-- Every row of the synchronous kernel is a probability vector. -/
theorem synchronousKernel_sum (n : ℕ) (α β τ : ℝ) (s : Fin n → Bool) :
    ∑ s', synchronousKernel n α β τ s s' = 1 := by
  simp only [synchronousKernel, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ,
    if_true]
  ring

/-- The synchronous kernel is nonnegative when the step is short enough. -/
theorem synchronousKernel_nonneg (n : ℕ) (α β τ : ℝ) (hα0 : 0 ≤ τ * α) (hα1 : τ * α ≤ 1)
    (hβ0 : 0 ≤ τ * β) (hβ1 : τ * β ≤ 1) (s s' : Fin n → Bool) :
    0 ≤ synchronousKernel n α β τ s s' := by
  have h1 : (0 : ℝ) ≤ (1 - τ * α) * (1 - τ * β) := mul_nonneg (by linarith) (by linarith)
  have h2 : (0 : ℝ) ≤ (τ * α) * (1 - τ * β) := mul_nonneg hα0 (by linarith)
  have h3 : (0 : ℝ) ≤ (1 - τ * α) * (τ * β) := mul_nonneg (by linarith) hβ0
  have h4 : (0 : ℝ) ≤ (τ * α) * (τ * β) := mul_nonneg hα0 hβ0
  simp only [synchronousKernel]
  split_ifs <;> linarith

/-- **The synchronous coupling is admissible**: every coordinate flips with exactly the
prescribed probability `τα` when it is aligned and `τβ` when it is not, which is DC (3.2) /
PL (5.7) for a skeleton step.  The joint law is nevertheless maximally dependent. -/
theorem synchronousKernel_flip (n : ℕ) (α β τ : ℝ) (s : Fin n → Bool) (i : Fin n) :
    ∑ s', (if s' i = s i then (0 : ℝ) else synchronousKernel n α β τ s s')
      = τ * (if s i = true then α else β) := by
  have hpt : ∀ s' : Fin n → Bool,
      (if s' i = s i then (0 : ℝ) else synchronousKernel n α β τ s s')
        = (if s' i = s i then (0 : ℝ) else 1) * synchronousKernel n α β τ s s' := by
    intro s'
    by_cases h : s' i = s i
    · rw [if_pos h, if_pos h]
      ring
    · rw [if_neg h, if_neg h]
      ring
  rw [Finset.sum_congr rfl fun s' _ ↦ hpt s']
  simp only [synchronousKernel, mul_add, Finset.sum_add_distrib, mul_ite, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rcases Bool.eq_false_or_eq_true (s i) with h | h <;> simp [h] <;> ring

/-- **The admissible class is inhabited.**  The synchronous coupling satisfies every
hypothesis of the convex-order comparison, so DC Theorem 3.1 / PL Theorem 5.3 is a
statement about something. -/
theorem synchronous_pathExp_nearestDrift_le (n : ℕ) (α β τ : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hτ : 0 ≤ τ) (hshort : τ * (2 * (n : ℝ) * (α + β)) ≤ 1) (hα0 : 0 ≤ τ * α)
    (hα1 : τ * α ≤ 1) (hβ0 : 0 ≤ τ * β) (hβ1 : τ * β ≤ 1) (f : ℤ → ℝ)
    (hf : ∀ j : ℤ, 1 ≤ j → j + 1 ≤ (n : ℤ) → 0 ≤ f (j - 1) - 2 * f j + f (j + 1)) (m : ℕ)
    (hist : List (Fin n → Bool)) (s : Fin n → Bool) :
    (ConvexOrderCoupling.driftStep n α β τ)^[m] f
        ((ConvexOrderCoupling.occupiedCount s : ℕ) : ℤ)
      ≤ ConvexOrderCoupling.pathExp (fun _ ↦ synchronousKernel n α β τ) m hist s
          (fun x ↦ f ((ConvexOrderCoupling.occupiedCount x : ℕ) : ℤ)) :=
  ConvexOrderCoupling.pathExp_nearestDrift_le α β τ hα hβ hτ hshort
    (fun _ ↦ synchronousKernel n α β τ)
    (fun _ s s' ↦ synchronousKernel_nonneg n α β τ hα0 hα1 hβ0 hβ1 s s')
    (fun _ s ↦ synchronousKernel_sum n α β τ s)
    (fun _ s i ↦ synchronousKernel_flip n α β τ s i) f hf m hist s


/-! ## Both sharp quadratic-variation bounds are attained -/

/-- Evaluating a report against the synchronous kernel's row. -/
theorem synchronousKernel_apply {n : ℕ} (α β τ : ℝ) (s : Fin n → Bool)
    (g : (Fin n → Bool) → ℝ) :
    ∑ s', synchronousKernel n α β τ s s' * g s'
      = (1 - τ * α) * (1 - τ * β) * g s + (τ * α) * (1 - τ * β) * g (fun _ ↦ false)
        + (1 - τ * α) * (τ * β) * g (fun _ ↦ true)
        + (τ * α) * (τ * β) * g (fun i ↦ !s i) := by
  simp only [synchronousKernel, add_mul, Finset.sum_add_distrib, ite_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-- The alignment of the source-aligned configuration is the total score weight. -/
theorem alignment_allTrue {n : ℕ} (a : Fin n → ℝ) :
    alignment a (fun _ ↦ true) = ∑ i, a i ^ 2 := by
  have hpt : ∀ i : Fin n, a i ^ 2 * signValue ((fun _ : Fin n ↦ true) i) = a i ^ 2 := by
    intro i
    show a i ^ 2 * (1 : ℝ) = a i ^ 2
    ring
  simp only [alignment]
  exact Finset.sum_congr rfl fun i _ ↦ hpt i

/-- The alignment of the fully reversed configuration is minus the total score weight. -/
theorem alignment_allFalse {n : ℕ} (a : Fin n → ℝ) :
    alignment a (fun _ ↦ false) = -∑ i, a i ^ 2 := by
  have hpt : ∀ i : Fin n, a i ^ 2 * signValue ((fun _ : Fin n ↦ false) i) = -(a i ^ 2) := by
    intro i
    show a i ^ 2 * (-1 : ℝ) = -(a i ^ 2)
    ring
  simp only [alignment]
  rw [Finset.sum_congr rfl fun i _ ↦ hpt i, Finset.sum_neg_distrib]

/-- Flipping one locus of the source-aligned configuration moves the alignment by `-2wᵢ`. -/
theorem alignment_flipCoord_allTrue {n : ℕ} (a : Fin n → ℝ) (i : Fin n) :
    alignment a (flipCoord i (fun _ ↦ true)) = (∑ j, a j ^ 2) - 2 * a i ^ 2 := by
  have hpt : ∀ j : Fin n,
      a j ^ 2 * signValue (flipCoord i (fun _ : Fin n ↦ true) j)
        = a j ^ 2 - 2 * (if j = i then a j ^ 2 else 0) := by
    intro j
    by_cases h : j = i
    · subst h
      simp only [flipCoord_self, if_pos rfl]
      show a j ^ 2 * (-1 : ℝ) = a j ^ 2 - 2 * a j ^ 2
      ring
    · rw [flipCoord_ne i h, if_neg h]
      show a j ^ 2 * (1 : ℝ) = a j ^ 2 - 2 * 0
      ring
  simp only [alignment]
  rw [Finset.sum_congr rfl fun j _ ↦ hpt j, Finset.sum_sub_distrib, ← Finset.mul_sum,
    Finset.sum_ite_eq' Finset.univ i (fun j ↦ a j ^ 2), if_pos (Finset.mem_univ i)]

/-- **PL (5.6), upper bound attained.**  The synchronous coupling's quadratic variation at
the source-aligned state is exactly `4τλ`, the largest value the sharp bound allows. -/
theorem synchronous_quadraticVariation {n : ℕ} (a : Fin n → ℝ) (lam τ : ℝ)
    (hnorm : ∑ i, a i ^ 2 = 1) :
    ∑ s', synchronousKernel n lam lam τ (fun _ ↦ true) s'
        * (alignment a s' - alignment a (fun _ ↦ true)) ^ 2 = 4 * (τ * lam) := by
  have hneg : (fun i ↦ !(fun _ : Fin n ↦ true) i) = (fun _ : Fin n ↦ false) := by
    funext i
    simp
  rw [synchronousKernel_apply lam lam τ (fun _ ↦ true)
    (fun s' ↦ (alignment a s' - alignment a (fun _ ↦ true)) ^ 2), hneg,
    alignment_allTrue, alignment_allFalse, hnorm]
  ring

/-- **The single-flip coupling.**  Each locus flips alone with probability `τλ` and nothing
else happens.  This is the independent-coordinate coupling PL Theorem 5.2 names as attaining
the lower slope bound. -/
def singleFlipKernel (n : ℕ) (lam τ : ℝ) (s s' : Fin n → Bool) : ℝ :=
  (if s' = s then 1 - (n : ℝ) * (τ * lam) else 0)
    + ∑ i, (if s' = flipCoord i s then τ * lam else 0)

/-- Evaluating a report against the single-flip kernel's row. -/
theorem singleFlipKernel_apply {n : ℕ} (lam τ : ℝ) (s : Fin n → Bool)
    (g : (Fin n → Bool) → ℝ) :
    ∑ s', singleFlipKernel n lam τ s s' * g s'
      = (1 - (n : ℝ) * (τ * lam)) * g s + ∑ i, (τ * lam) * g (flipCoord i s) := by
  have h1 : ∑ s' : Fin n → Bool,
      (if s' = s then 1 - (n : ℝ) * (τ * lam) else 0) * g s'
      = (1 - (n : ℝ) * (τ * lam)) * g s := by
    simp only [ite_mul, zero_mul]
    rw [Finset.sum_ite_eq' Finset.univ s (fun s' ↦ (1 - (n : ℝ) * (τ * lam)) * g s'),
      if_pos (Finset.mem_univ s)]
  have h2 : ∑ s' : Fin n → Bool,
      (∑ i, (if s' = flipCoord i s then τ * lam else 0)) * g s'
      = ∑ i, (τ * lam) * g (flipCoord i s) := by
    simp only [Finset.sum_mul, ite_mul, zero_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Finset.sum_ite_eq' Finset.univ (flipCoord i s) (fun s' ↦ (τ * lam) * g s'),
      if_pos (Finset.mem_univ _)]
  simp only [singleFlipKernel, add_mul, Finset.sum_add_distrib]
  rw [h1, h2]

/-- Every row of the single-flip kernel is a probability vector. -/
theorem singleFlipKernel_sum {n : ℕ} (lam τ : ℝ) (s : Fin n → Bool) :
    ∑ s', singleFlipKernel n lam τ s s' = 1 := by
  have h := singleFlipKernel_apply lam τ s (fun _ ↦ (1 : ℝ))
  simp only [mul_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
  rw [h]
  ring

/-- The single-flip kernel is nonnegative when the step is short enough. -/
theorem singleFlipKernel_nonneg {n : ℕ} (lam τ : ℝ) (h0 : 0 ≤ τ * lam)
    (h1 : (n : ℝ) * (τ * lam) ≤ 1) (s s' : Fin n → Bool) :
    0 ≤ singleFlipKernel n lam τ s s' := by
  refine add_nonneg ?_ (Finset.sum_nonneg fun i _ ↦ ?_)
  · split
    · linarith
    · exact le_rfl
  · split
    · exact h0
    · exact le_rfl

/-- **The single-flip coupling is admissible**: every locus flips with probability exactly
`τλ`, which is PL (5.4) for a skeleton step. -/
theorem singleFlipKernel_flip {n : ℕ} (lam τ : ℝ) (s : Fin n → Bool) (i : Fin n) :
    ∑ s', (if s' i = s i then (0 : ℝ) else singleFlipKernel n lam τ s s') = τ * lam := by
  have hpt : ∀ s' : Fin n → Bool,
      (if s' i = s i then (0 : ℝ) else singleFlipKernel n lam τ s s')
        = singleFlipKernel n lam τ s s' * (if s' i = s i then (0 : ℝ) else 1) := by
    intro s'
    by_cases h : s' i = s i
    · rw [if_pos h, if_pos h]
      ring
    · rw [if_neg h, if_neg h]
      ring
  have hind : ∀ j : Fin n,
      (if flipCoord j s i = s i then (0 : ℝ) else 1) = (if j = i then (1 : ℝ) else 0) := by
    intro j
    by_cases h : j = i
    · subst h
      rw [flipCoord_self, if_pos rfl, if_neg]
      exact fun hc ↦ by simp at hc
    · rw [flipCoord_ne j (Ne.symm h), if_pos rfl, if_neg h]
  rw [Finset.sum_congr rfl fun s' _ ↦ hpt s',
    singleFlipKernel_apply lam τ s (fun s' ↦ if s' i = s i then (0 : ℝ) else 1), if_pos rfl]
  simp only [hind, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq' Finset.univ i (fun _ ↦ τ * lam), if_pos (Finset.mem_univ i)]
  ring

/-- **PL (5.6), lower bound attained.**  The single-flip coupling's quadratic variation at
the source-aligned state is exactly `4τλ ∑ wᵢ²`, the smallest value the sharp bound allows.
The ratio between the two attained values is the effective number of score-weight
contributions. -/
theorem singleFlip_quadraticVariation {n : ℕ} (a : Fin n → ℝ) (lam τ : ℝ) :
    ∑ s', singleFlipKernel n lam τ (fun _ ↦ true) s'
        * (alignment a s' - alignment a (fun _ ↦ true)) ^ 2
      = 4 * (τ * lam) * ∑ i, (a i ^ 2) ^ 2 := by
  have hpt : ∀ i : Fin n,
      (τ * lam) * (alignment a (flipCoord i (fun _ ↦ true))
          - alignment a (fun _ ↦ true)) ^ 2
        = (4 * (τ * lam)) * (a i ^ 2) ^ 2 := by
    intro i
    rw [alignment_flipCoord_allTrue, alignment_allTrue]
    ring
  rw [singleFlipKernel_apply lam τ (fun _ ↦ true)
    (fun s' ↦ (alignment a s' - alignment a (fun _ ↦ true)) ^ 2),
    Finset.sum_congr rfl fun i _ ↦ hpt i, ← Finset.mul_sum]
  ring

end

end Descent.Portability.TurnoverExtremalCouplings
