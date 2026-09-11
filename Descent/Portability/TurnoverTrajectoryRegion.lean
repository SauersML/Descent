/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.TurnoverCouplingPolytope

assert_below Descent.Decision Descent.Program

/-!
# The complete turnover-trajectory region for two equal-effect loci

Two loci carry signs that both start at `+1`; conditional on the entire past each
locus flips with the same probability `p ≤ 1/2`, with arbitrary joint dependence
between the two. The accuracy of the two-equal-effect architecture is
`H` times the agreement indicator, so the whole trajectory question is about
`a_t`, the probability that the two signs agree at time `t`.

UPT Theorem 5.4 is proved here in both directions. Necessity: for every
coadapted coupling of `TurnoverCouplingPolytope.Coadapted`, the agreement
sequence starts at one and satisfies `(1-2p) a_t ≤ a_{t+1} ≤ a_t + 2p(1-a_t)`.
The bound comes from the four joint next-state masses: the two one-locus
marginal constraints and normalisation pin the agreement transition to an
interval of width `2p` whose position depends only on whether the current state
agrees. Sufficiency: every sequence obeying those inequalities is produced
exactly by an explicit coadapted coupling whose one-locus flip probability is
`p` after every history.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.TurnoverTrajectoryRegion

open Foundations TurnoverCouplingPolytope

noncomputable section

section Enumeration

/-- A two-locus sign state is its pair of coordinates. -/
def pairEquiv : (Fin 2 → Bool) ≃ Bool × Bool where
  toFun a := (a 0, a 1)
  invFun q := ![q.1, q.2]
  left_inv a := by
    funext i
    fin_cases i <;> rfl
  right_inv q := rfl

/-- Enumeration of the four two-locus sign states. -/
theorem sum_pi_two (f : (Fin 2 → Bool) → ℝ) :
    ∑ a : Fin 2 → Bool, f a
      = f ![true, true] + f ![true, false] + (f ![false, true] + f ![false, false]) := by
  rw [← Equiv.sum_comp pairEquiv.symm f, Fintype.sum_prod_type, Fintype.sum_bool,
    Fintype.sum_bool, Fintype.sum_bool]
  rfl

end Enumeration

section Model

/-- The agreement indicator of a two-locus sign state. -/
def agree (z : Fin 2 → Bool) : ℝ := if z 0 = z 1 then 1 else 0

/-- The agreement indicator takes only the values zero and one. -/
theorem agree_cases (z : Fin 2 → Bool) : agree z = 1 ∨ agree z = 0 := by
  unfold agree
  by_cases hz : z 0 = z 1
  · exact Or.inl (if_pos hz)
  · exact Or.inr (if_neg hz)

/-- Both signs start at `+1`. -/
def startLaw : (Fin 2 → Bool) → ℝ := fun a ↦ if a 0 = true ∧ a 1 = true then 1 else 0

/-- The prescribed one-locus law: each locus flips with probability `p` at every step. -/
def flipKernel (p : ℝ) (_t : ℕ) (i : Fin 2) (z : Fin 2 → Bool) (b : Bool) : ℝ :=
  if b = z i then 1 - p else p

/-- The agreement probability of the next state given a history. -/
def stepAgree (J : List (Fin 2 → Bool) → (Fin 2 → Bool) → ℝ) (v : List (Fin 2 → Bool)) : ℝ :=
  ∑ a, J v a * agree a

/-- The mass of a length-indexed path under the path law. -/
def pathMass (μ : (Fin 2 → Bool) → ℝ) (J : List (Fin 2 → Bool) → (Fin 2 → Bool) → ℝ)
    (t : ℕ) (u : Fin (t + 1) → Fin 2 → Bool) : ℝ := pathLaw μ J (List.ofFn u)

/-- The agreement probability at time `t`. -/
def agreeProb (μ : (Fin 2 → Bool) → ℝ) (J : List (Fin 2 → Bool) → (Fin 2 → Bool) → ℝ)
    (t : ℕ) : ℝ := ∑ u, pathMass μ J t u * agree (u 0)

/-- The total path mass at time `t`. -/
def totalMass (μ : (Fin 2 → Bool) → ℝ) (J : List (Fin 2 → Bool) → (Fin 2 → Bool) → ℝ)
    (t : ℕ) : ℝ := ∑ u, pathMass μ J t u

end Model

section PathSums

/-- Splitting a path sum on its most recent state. -/
theorem sum_succ_paths {t : ℕ} (F : (Fin (t + 2) → Fin 2 → Bool) → ℝ) :
    ∑ w, F w = ∑ a : Fin 2 → Bool, ∑ u : Fin (t + 1) → Fin 2 → Bool, F (Fin.cons a u) := by
  rw [← Equiv.sum_comp (Fin.consEquiv fun _ : Fin (t + 2) ↦ (Fin 2 → Bool)) F,
    Fintype.sum_prod_type]
  rfl

/-- A one-step path sum is a sum over states. -/
theorem sum_fin_one (F : (Fin 1 → Fin 2 → Bool) → ℝ) :
    ∑ u : Fin 1 → Fin 2 → Bool, F u = ∑ a : Fin 2 → Bool, F fun _ ↦ a := by
  rw [← Equiv.sum_comp (Equiv.funUnique (Fin 1) (Fin 2 → Bool)).symm F]
  rfl

/-- The initial path mass is the initial law. -/
theorem pathMass_zero (μ : (Fin 2 → Bool) → ℝ)
    (J : List (Fin 2 → Bool) → (Fin 2 → Bool) → ℝ) (u : Fin 1 → Fin 2 → Bool) :
    pathMass μ J 0 u = μ (u 0) := by
  rw [pathMass, List.ofFn_succ, List.ofFn_zero, pathLaw_single]

/-- Path masses multiply by the joint kernel at the appended state. -/
theorem pathMass_cons {t : ℕ} (μ : (Fin 2 → Bool) → ℝ)
    (J : List (Fin 2 → Bool) → (Fin 2 → Bool) → ℝ) (a : Fin 2 → Bool)
    (u : Fin (t + 1) → Fin 2 → Bool) :
    pathMass μ J (t + 1) (Fin.cons a u) = pathMass μ J t u * J (List.ofFn u) a := by
  have hsplit : List.ofFn u = u 0 :: List.ofFn fun i : Fin t ↦ u i.succ := List.ofFn_succ
  have hcons : List.ofFn (Fin.cons a u) = a :: List.ofFn u := by
    simp [List.ofFn_succ]
  rw [pathMass, pathMass, hcons, hsplit, pathLaw_cons, ← hsplit]

/-- Total path mass is conserved by a coadapted family.

Assumes: `Coadapted (flipKernel p) J`, witnessed by `flipCoupling_coadapted`. -/
theorem totalMass_eq_one {μ : (Fin 2 → Bool) → ℝ}
    {J : List (Fin 2 → Bool) → (Fin 2 → Bool) → ℝ} {K : ℕ → Fin 2 → (Fin 2 → Bool) → Bool → ℝ}
    (hJ : Coadapted K J) (hμ : ∑ a, μ a = 1) : ∀ t : ℕ, totalMass μ J t = 1
  | 0 => by
      rw [totalMass, sum_fin_one]
      rw [Finset.sum_congr rfl fun a _ ↦ pathMass_zero μ J fun _ ↦ a]
      exact hμ
  | t + 1 => by
      rw [totalMass, sum_succ_paths]
      have hin : ∀ (a : Fin 2 → Bool) (u : Fin (t + 1) → Fin 2 → Bool),
          pathMass μ J (t + 1) (Fin.cons a u) = pathMass μ J t u * J (List.ofFn u) a :=
        pathMass_cons μ J
      rw [Finset.sum_congr rfl fun a _ ↦ Finset.sum_congr rfl fun u _ ↦ hin a u,
        Finset.sum_comm]
      have hone : ∀ u : Fin (t + 1) → Fin 2 → Bool,
          (∑ a, pathMass μ J t u * J (List.ofFn u) a) = pathMass μ J t u := by
        intro u
        have hne : List.ofFn u = u 0 :: List.ofFn fun i : Fin t ↦ u i.succ := List.ofFn_succ
        rw [← Finset.mul_sum, hne, (hJ (u 0) _).2.1, mul_one]
      rw [Finset.sum_congr rfl fun u _ ↦ hone u]
      exact totalMass_eq_one hJ hμ t

/-- Backward form of the agreement probability. -/
theorem agreeProb_succ (μ : (Fin 2 → Bool) → ℝ)
    (J : List (Fin 2 → Bool) → (Fin 2 → Bool) → ℝ) (t : ℕ) :
    agreeProb μ J (t + 1)
      = ∑ u : Fin (t + 1) → Fin 2 → Bool, pathMass μ J t u * stepAgree J (List.ofFn u) := by
  rw [agreeProb, sum_succ_paths]
  have hin : ∀ (a : Fin 2 → Bool) (u : Fin (t + 1) → Fin 2 → Bool),
      pathMass μ J (t + 1) (Fin.cons a u)
          * agree ((Fin.cons a u : Fin (t + 2) → Fin 2 → Bool) 0)
        = pathMass μ J t u * (J (List.ofFn u) a * agree a) := by
    intro a u
    rw [pathMass_cons, Fin.cons_zero]
    ring
  rw [Finset.sum_congr rfl fun a _ ↦ Finset.sum_congr rfl fun u _ ↦ hin a u, Finset.sum_comm]
  refine Finset.sum_congr rfl fun u _ ↦ ?_
  rw [stepAgree, Finset.mul_sum]

/-- Path masses are nonnegative.

Assumes: `Coadapted K J`, witnessed by `flipCoupling_coadapted`. -/
theorem pathMass_nonneg {μ : (Fin 2 → Bool) → ℝ} (hμ : ∀ a, 0 ≤ μ a)
    {J : List (Fin 2 → Bool) → (Fin 2 → Bool) → ℝ} {K : ℕ → Fin 2 → (Fin 2 → Bool) → Bool → ℝ}
    (hJ : Coadapted K J) (t : ℕ) (u : Fin (t + 1) → Fin 2 → Bool) : 0 ≤ pathMass μ J t u :=
  pathLaw_nonneg hμ hJ (List.ofFn u)

end PathSums

section Necessity

/-- **The one-step agreement transition lies in an interval of width `2p`.**  Only the two
one-locus marginal constraints and normalisation are used; the joint dependence is free.

Assumes: `Coadapted (flipKernel p) J`, witnessed by `flipCoupling_coadapted`. -/
theorem stepAgree_bounds (p : ℝ) (hp0 : 0 ≤ p) (hp2 : p ≤ 1 / 2)
    {J : List (Fin 2 → Bool) → (Fin 2 → Bool) → ℝ} (hJ : Coadapted (flipKernel p) J)
    (z : Fin 2 → Bool) (h : List (Fin 2 → Bool)) :
    (1 - 2 * p) * agree z ≤ stepAgree J (z :: h) ∧
      stepAgree J (z :: h) ≤ agree z + 2 * p * (1 - agree z) := by
  obtain ⟨hnn, hsum, hmarg⟩ := hJ z h
  have hx : 0 ≤ J (z :: h) ![true, true] := hnn _
  have hy : 0 ≤ J (z :: h) ![true, false] := hnn _
  have hu : 0 ≤ J (z :: h) ![false, true] := hnn _
  have hw : 0 ≤ J (z :: h) ![false, false] := hnn _
  have hS : J (z :: h) ![true, true] + J (z :: h) ![true, false]
      + (J (z :: h) ![false, true] + J (z :: h) ![false, false]) = 1 := by
    rw [← sum_pi_two fun a ↦ J (z :: h) a]
    exact hsum
  have hM0 : J (z :: h) ![true, true] + J (z :: h) ![true, false]
      = flipKernel p h.length 0 z true := by
    have hm := hmarg 0 true
    rw [Finset.sum_filter, sum_pi_two] at hm
    simpa using hm
  have hM1 : J (z :: h) ![true, true] + J (z :: h) ![false, true]
      = flipKernel p h.length 1 z true := by
    have hm := hmarg 1 true
    rw [Finset.sum_filter, sum_pi_two] at hm
    simpa using hm
  have hstep : stepAgree J (z :: h)
      = J (z :: h) ![true, true] + J (z :: h) ![false, false] := by
    rw [stepAgree, sum_pi_two]
    simp [agree]
  rw [hstep]
  unfold flipKernel at hM0 hM1
  unfold agree
  cases hz0 : z 0 <;> cases hz1 : z 1 <;>
    simp only [hz0, hz1, reduceIte, reduceCtorEq] at hM0 hM1 ⊢ <;>
    constructor <;> linarith [hp0, hp2]

/-- **UPT Theorem 5.4, necessity.**  Every coadapted coupling with one-locus flip
probability `p` obeys the trajectory inequalities (5.7).

Assumes: `Coadapted (flipKernel p) J`, witnessed by `flipCoupling_coadapted`. -/
theorem agreeProb_trajectory_bounds (p : ℝ) (hp0 : 0 ≤ p) (hp2 : p ≤ 1 / 2)
    {μ : (Fin 2 → Bool) → ℝ} (hμnn : ∀ a, 0 ≤ μ a) (hμ : ∑ a, μ a = 1)
    {J : List (Fin 2 → Bool) → (Fin 2 → Bool) → ℝ} (hJ : Coadapted (flipKernel p) J)
    (t : ℕ) :
    (1 - 2 * p) * agreeProb μ J t ≤ agreeProb μ J (t + 1) ∧
      agreeProb μ J (t + 1)
        ≤ agreeProb μ J t + 2 * p * (1 - agreeProb μ J t) := by
  have hsplit : ∀ u : Fin (t + 1) → Fin 2 → Bool,
      List.ofFn u = u 0 :: List.ofFn fun i : Fin t ↦ u i.succ := fun _ ↦ List.ofFn_succ
  have hlow : ∀ u : Fin (t + 1) → Fin 2 → Bool,
      pathMass μ J t u * ((1 - 2 * p) * agree (u 0))
        ≤ pathMass μ J t u * stepAgree J (List.ofFn u) := by
    intro u
    refine mul_le_mul_of_nonneg_left ?_ (pathMass_nonneg hμnn hJ t u)
    rw [hsplit u]
    exact (stepAgree_bounds p hp0 hp2 hJ (u 0) _).1
  have hhigh : ∀ u : Fin (t + 1) → Fin 2 → Bool,
      pathMass μ J t u * stepAgree J (List.ofFn u)
        ≤ pathMass μ J t u * (agree (u 0) + 2 * p * (1 - agree (u 0))) := by
    intro u
    refine mul_le_mul_of_nonneg_left ?_ (pathMass_nonneg hμnn hJ t u)
    rw [hsplit u]
    exact (stepAgree_bounds p hp0 hp2 hJ (u 0) _).2
  have hlowsum : ∑ u : Fin (t + 1) → Fin 2 → Bool,
      pathMass μ J t u * ((1 - 2 * p) * agree (u 0)) = (1 - 2 * p) * agreeProb μ J t := by
    rw [agreeProb, Finset.mul_sum]
    exact Finset.sum_congr rfl fun u _ ↦ by ring
  have hhighsum : ∑ u : Fin (t + 1) → Fin 2 → Bool,
      pathMass μ J t u * (agree (u 0) + 2 * p * (1 - agree (u 0)))
        = agreeProb μ J t + 2 * p * (totalMass μ J t - agreeProb μ J t) := by
    have hrw : ∀ u : Fin (t + 1) → Fin 2 → Bool,
        pathMass μ J t u * (agree (u 0) + 2 * p * (1 - agree (u 0)))
          = pathMass μ J t u * agree (u 0)
            + 2 * p * (pathMass μ J t u - pathMass μ J t u * agree (u 0)) := fun u ↦ by ring
    rw [Finset.sum_congr rfl fun u _ ↦ hrw u, Finset.sum_add_distrib, ← Finset.mul_sum,
      Finset.sum_sub_distrib, agreeProb, totalMass]
  have htot : totalMass μ J t = 1 := totalMass_eq_one hJ hμ t
  rw [agreeProb_succ]
  constructor
  · rw [← hlowsum]
    exact Finset.sum_le_sum fun u _ ↦ hlow u
  · refine le_trans (Finset.sum_le_sum fun u _ ↦ hhigh u) ?_
    rw [hhighsum, htot]

/-- The agreement probability starts at one. -/
theorem agreeProb_zero_startLaw (J : List (Fin 2 → Bool) → (Fin 2 → Bool) → ℝ) :
    agreeProb startLaw J 0 = 1 := by
  rw [agreeProb, sum_fin_one]
  have hrw : ∀ a : Fin 2 → Bool,
      pathMass startLaw J 0 (fun _ ↦ a) * agree ((fun _ : Fin 1 ↦ a) 0) = startLaw a * agree a :=
    fun a ↦ by rw [pathMass_zero]
  rw [Finset.sum_congr rfl fun a _ ↦ hrw a, sum_pi_two]
  simp [startLaw, agree]

/-- The initial law is a probability vector concentrated on the agreeing state. -/
theorem startLaw_isLaw : (∀ a, 0 ≤ startLaw a) ∧ ∑ a, startLaw a = 1 := by
  constructor
  · intro a
    unfold startLaw
    by_cases hc : a 0 = true ∧ a 1 = true
    · rw [if_pos hc]
      norm_num
    · rw [if_neg hc]
  · rw [sum_pi_two]
    simp [startLaw]

end Necessity

end

end Descent.Portability.TurnoverTrajectoryRegion
