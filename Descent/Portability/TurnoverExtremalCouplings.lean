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

open Foundations NonanticipationCost

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

end

end Descent.Portability.TurnoverExtremalCouplings
