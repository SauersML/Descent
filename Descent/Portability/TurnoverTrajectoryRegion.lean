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
theorem stepAgree_bounds (p : ℝ)
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
    constructor <;> linarith

/-- **UPT Theorem 5.4, necessity.**  Every coadapted coupling with one-locus flip
probability `p` obeys the trajectory inequalities (5.7).

Assumes: `Coadapted (flipKernel p) J`, witnessed by `flipCoupling_coadapted`. -/
theorem agreeProb_trajectory_bounds (p : ℝ) {μ : (Fin 2 → Bool) → ℝ}
    (hμnn : ∀ a, 0 ≤ μ a) (hμ : ∑ a, μ a = 1)
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
    exact (stepAgree_bounds p hJ (u 0) _).1
  have hhigh : ∀ u : Fin (t + 1) → Fin 2 → Bool,
      pathMass μ J t u * stepAgree J (List.ofFn u)
        ≤ pathMass μ J t u * (agree (u 0) + 2 * p * (1 - agree (u 0))) := by
    intro u
    refine mul_le_mul_of_nonneg_left ?_ (pathMass_nonneg hμnn hJ t u)
    rw [hsplit u]
    exact (stepAgree_bounds p hJ (u 0) _).2
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

section Sufficiency

/-- **The explicit coadapted coupling.**  At an agreeing state exactly one locus flips with
probability `uu t`, at a disagreeing state with probability `vv t`, and the remaining mass is
split between the no-flip and both-flip events so that each locus flips with probability
`p` after every history. -/
def flipCoupling (p : ℝ) (uu vv : ℕ → ℝ) : List (Fin 2 → Bool) → (Fin 2 → Bool) → ℝ
  | [] => fun _ ↦ 0
  | z :: h => fun a ↦
      if z 0 = z 1 then
        (if a 0 = a 1 then
            (if a 0 = z 0 then 1 - p - uu h.length / 2 else p - uu h.length / 2)
          else uu h.length / 2)
      else
        (if a 0 = a 1 then vv h.length / 2
          else (if a 0 = z 0 then 1 - p - vv h.length / 2 else p - vv h.length / 2))

/-- Value of the explicit coupling at a nonempty history. -/
@[simp] theorem flipCoupling_cons (p : ℝ) (uu vv : ℕ → ℝ) (z : Fin 2 → Bool)
    (h : List (Fin 2 → Bool)) (a : Fin 2 → Bool) :
    flipCoupling p uu vv (z :: h) a =
      if z 0 = z 1 then
        (if a 0 = a 1 then
            (if a 0 = z 0 then 1 - p - uu h.length / 2 else p - uu h.length / 2)
          else uu h.length / 2)
      else
        (if a 0 = a 1 then vv h.length / 2
          else (if a 0 = z 0 then 1 - p - vv h.length / 2 else p - vv h.length / 2)) := rfl

/-- **The explicit coupling is coadapted**: after every history each locus flips with
probability exactly `p`. -/
theorem flipCoupling_coadapted (p : ℝ) (hp0 : 0 ≤ p) (hp2 : p ≤ 1 / 2) (uu vv : ℕ → ℝ)
    (huu : ∀ t, 0 ≤ uu t ∧ uu t ≤ 2 * p) (hvv : ∀ t, 0 ≤ vv t ∧ vv t ≤ 2 * p) :
    Coadapted (flipKernel p) (flipCoupling p uu vv) := by
  intro z h
  obtain ⟨hu0, hu2⟩ := huu h.length
  obtain ⟨hv0, hv2⟩ := hvv h.length
  refine ⟨?_, ?_, ?_⟩
  · intro a
    rw [flipCoupling_cons]
    split_ifs <;> linarith
  · rw [sum_pi_two]
    cases hz0 : z 0 <;> cases hz1 : z 1 <;> simp [flipCoupling, hz0, hz1] <;> ring
  · intro i b
    rw [Finset.sum_filter, sum_pi_two]
    fin_cases i <;> cases b <;> cases hz0 : z 0 <;> cases hz1 : z 1 <;>
      simp [flipCoupling, flipKernel, hz0, hz1] <;> ring

/-- **Exact one-step agreement transition of the explicit coupling**, UPT (5.9). -/
theorem stepAgree_flipCoupling (p : ℝ) (uu vv : ℕ → ℝ) (z : Fin 2 → Bool)
    (h : List (Fin 2 → Bool)) :
    stepAgree (flipCoupling p uu vv) (z :: h)
      = agree z * (1 - uu h.length) + (1 - agree z) * vv h.length := by
  rw [stepAgree, sum_pi_two]
  unfold agree
  cases hz0 : z 0 <;> cases hz1 : z 1 <;> simp [flipCoupling, hz0, hz1] <;> ring

/-- **The agreement recursion (5.9) of the explicit coupling.** -/
theorem agreeProb_flipCoupling_succ (p : ℝ) (uu vv : ℕ → ℝ)
    (hcoad : Coadapted (flipKernel p) (flipCoupling p uu vv)) (t : ℕ) :
    agreeProb startLaw (flipCoupling p uu vv) (t + 1)
      = agreeProb startLaw (flipCoupling p uu vv) t * (1 - uu t)
        + (1 - agreeProb startLaw (flipCoupling p uu vv) t) * vv t := by
  have htot : totalMass startLaw (flipCoupling p uu vv) t = 1 :=
    totalMass_eq_one hcoad startLaw_isLaw.2 t
  have hterm : ∀ u : Fin (t + 1) → Fin 2 → Bool,
      pathMass startLaw (flipCoupling p uu vv) t u
          * stepAgree (flipCoupling p uu vv) (List.ofFn u)
        = pathMass startLaw (flipCoupling p uu vv) t u * agree (u 0) * (1 - uu t)
          + (pathMass startLaw (flipCoupling p uu vv) t u
              - pathMass startLaw (flipCoupling p uu vv) t u * agree (u 0)) * vv t := by
    intro u
    have hsplit : List.ofFn u = u 0 :: List.ofFn fun i : Fin t ↦ u i.succ := List.ofFn_succ
    have hlen : (List.ofFn fun i : Fin t ↦ u i.succ).length = t := List.length_ofFn
    rw [hsplit, stepAgree_flipCoupling, hlen]
    ring
  rw [agreeProb_succ, Finset.sum_congr rfl fun u _ ↦ hterm u, Finset.sum_add_distrib,
    ← Finset.sum_mul, ← Finset.sum_mul, Finset.sum_sub_distrib]
  have hA : (∑ u : Fin (t + 1) → Fin 2 → Bool,
      pathMass startLaw (flipCoupling p uu vv) t u * agree (u 0))
      = agreeProb startLaw (flipCoupling p uu vv) t := rfl
  have hT : (∑ u : Fin (t + 1) → Fin 2 → Bool, pathMass startLaw (flipCoupling p uu vv) t u)
      = totalMass startLaw (flipCoupling p uu vv) t := rfl
  rw [hA, hT, htot]

end Sufficiency

section Trajectories

/-- The agreement trajectory stays in the unit interval. -/
theorem traj_mem_unit (p : ℝ) (hp0 : 0 ≤ p) (hp2 : p ≤ 1 / 2) (A : ℕ → ℝ) (hA0 : A 0 = 1)
    (hA : ∀ t, (1 - 2 * p) * A t ≤ A (t + 1) ∧ A (t + 1) ≤ A t + 2 * p * (1 - A t)) :
    ∀ t, 0 ≤ A t ∧ A t ≤ 1
  | 0 => by
      rw [hA0]
      norm_num
  | t + 1 => by
      obtain ⟨h1, h2⟩ := traj_mem_unit p hp0 hp2 A hA0 hA t
      obtain ⟨g1, g2⟩ := hA t
      constructor <;> nlinarith

/-- The exactly-one-flip probability at an agreeing state that realises the trajectory. -/
def trajU (A : ℕ → ℝ) (t : ℕ) : ℝ :=
  if A (t + 1) ≤ A t then (if A t = 0 then 0 else (A t - A (t + 1)) / A t) else 0

/-- The exactly-one-flip probability at a disagreeing state that realises the trajectory. -/
def trajV (A : ℕ → ℝ) (t : ℕ) : ℝ :=
  if A (t + 1) ≤ A t then 0 else (A (t + 1) - A t) / (1 - A t)

/-- The realising probabilities are valid exactly-one-flip probabilities. -/
theorem trajU_bounds (p : ℝ) (hp0 : 0 ≤ p) (hp2 : p ≤ 1 / 2) (A : ℕ → ℝ) (hA0 : A 0 = 1)
    (hA : ∀ t, (1 - 2 * p) * A t ≤ A (t + 1) ∧ A (t + 1) ≤ A t + 2 * p * (1 - A t)) (t : ℕ) :
    0 ≤ trajU A t ∧ trajU A t ≤ 2 * p := by
  obtain ⟨hA0t, hA1t⟩ := traj_mem_unit p hp0 hp2 A hA0 hA t
  obtain ⟨hlow, hhigh⟩ := hA t
  unfold trajU
  by_cases hcase : A (t + 1) ≤ A t
  · rw [if_pos hcase]
    by_cases hz : A t = 0
    · rw [if_pos hz]
      constructor <;> linarith
    · rw [if_neg hz]
      have hpos : 0 < A t := lt_of_le_of_ne hA0t (Ne.symm hz)
      constructor
      · exact div_nonneg (by linarith) hpos.le
      · rw [div_le_iff₀ hpos]
        linarith
  · rw [if_neg hcase]
    constructor <;> linarith

/-- The realising probabilities are valid exactly-one-flip probabilities. -/
theorem trajV_bounds (p : ℝ) (hp0 : 0 ≤ p) (hp2 : p ≤ 1 / 2) (A : ℕ → ℝ) (hA0 : A 0 = 1)
    (hA : ∀ t, (1 - 2 * p) * A t ≤ A (t + 1) ∧ A (t + 1) ≤ A t + 2 * p * (1 - A t)) (t : ℕ) :
    0 ≤ trajV A t ∧ trajV A t ≤ 2 * p := by
  obtain ⟨hA0t, hA1t⟩ := traj_mem_unit p hp0 hp2 A hA0 hA t
  obtain ⟨hlow, hhigh⟩ := hA t
  unfold trajV
  by_cases hcase : A (t + 1) ≤ A t
  · rw [if_pos hcase]
    constructor <;> linarith
  · rw [if_neg hcase]
    push_neg at hcase
    have hlt : A t < 1 := by nlinarith
    have hpos : (0 : ℝ) < 1 - A t := by linarith
    constructor
    · exact div_nonneg (by linarith) hpos.le
    · rw [div_le_iff₀ hpos]
      linarith

/-- The realising probabilities reproduce the trajectory step exactly. -/
theorem traj_recursion (p : ℝ) (hp0 : 0 ≤ p) (hp2 : p ≤ 1 / 2) (A : ℕ → ℝ) (hA0 : A 0 = 1)
    (hA : ∀ t, (1 - 2 * p) * A t ≤ A (t + 1) ∧ A (t + 1) ≤ A t + 2 * p * (1 - A t)) (t : ℕ) :
    A t * (1 - trajU A t) + (1 - A t) * trajV A t = A (t + 1) := by
  obtain ⟨hA0t, hA1t⟩ := traj_mem_unit p hp0 hp2 A hA0 hA t
  obtain ⟨hlow, hhigh⟩ := hA t
  unfold trajU trajV
  by_cases hcase : A (t + 1) ≤ A t
  · rw [if_pos hcase, if_pos hcase]
    by_cases hz : A t = 0
    · rw [if_pos hz, hz]
      have hzero : A (t + 1) = 0 := by
        rw [hz] at hlow hcase
        linarith
      rw [hzero]
      ring
    · rw [if_neg hz]
      have hpos : 0 < A t := lt_of_le_of_ne hA0t (Ne.symm hz)
      field_simp
  · rw [if_neg hcase, if_neg hcase]
    push_neg at hcase
    have hlt : A t < 1 := by nlinarith
    have hne : (1 : ℝ) - A t ≠ 0 := by linarith
    field_simp

/-- **UPT Theorem 5.4, sufficiency.**  Every sequence obeying the trajectory inequalities
(5.7) is exactly the agreement trajectory of a coadapted coupling with one-locus flip
probability `p` after every history. -/
theorem trajectory_attained (p : ℝ) (hp0 : 0 ≤ p) (hp2 : p ≤ 1 / 2) (A : ℕ → ℝ)
    (hA0 : A 0 = 1)
    (hA : ∀ t, (1 - 2 * p) * A t ≤ A (t + 1) ∧ A (t + 1) ≤ A t + 2 * p * (1 - A t)) :
    Coadapted (flipKernel p) (flipCoupling p (trajU A) (trajV A)) ∧
      ∀ t, agreeProb startLaw (flipCoupling p (trajU A) (trajV A)) t = A t := by
  have hcoad : Coadapted (flipKernel p) (flipCoupling p (trajU A) (trajV A)) :=
    flipCoupling_coadapted p hp0 hp2 (trajU A) (trajV A)
      (trajU_bounds p hp0 hp2 A hA0 hA) (trajV_bounds p hp0 hp2 A hA0 hA)
  refine ⟨hcoad, ?_⟩
  intro t
  induction t with
  | zero =>
      rw [agreeProb_zero_startLaw]
      exact hA0.symm
  | succ t ih =>
      rw [agreeProb_flipCoupling_succ p (trajU A) (trajV A) hcoad t, ih]
      exact traj_recursion p hp0 hp2 A hA0 hA t

/-- **UPT (5.8), the terminal bound.**  Every coadapted coupling keeps the terminal
agreement probability in `[(1-2p)^T, 1]`.

Assumes: `Coadapted (flipKernel p) J`, witnessed by `flipCoupling_coadapted`. -/
theorem terminal_range_bounds (p : ℝ) (hp0 : 0 ≤ p) (hp2 : p ≤ 1 / 2)
    {J : List (Fin 2 → Bool) → (Fin 2 → Bool) → ℝ} (hJ : Coadapted (flipKernel p) J) :
    ∀ T : ℕ, (1 - 2 * p) ^ T ≤ agreeProb startLaw J T ∧ agreeProb startLaw J T ≤ 1
  | 0 => by
      rw [agreeProb_zero_startLaw]
      norm_num
  | T + 1 => by
      obtain ⟨h1, h2⟩ := terminal_range_bounds p hp0 hp2 hJ T
      obtain ⟨g1, g2⟩ :=
        agreeProb_trajectory_bounds p startLaw_isLaw.1 startLaw_isLaw.2 hJ T
      have hbase : (0 : ℝ) ≤ 1 - 2 * p := by linarith
      have hpow : (0 : ℝ) ≤ (1 - 2 * p) ^ T := pow_nonneg hbase T
      constructor
      · rw [pow_succ]
        nlinarith
      · nlinarith

/-- The one-parameter family of trajectories interpolating between total decay and perfect
synchrony. -/
def mixTrajectory (p θ : ℝ) (t : ℕ) : ℝ := θ * (1 - 2 * p) ^ t + (1 - θ)

/-- **UPT (5.8), attainment.**  Every value of `[(1-2p)^T, 1]` is the terminal agreement
probability of a coadapted coupling with the same complete one-locus laws. -/
theorem terminal_range_attained (p : ℝ) (hp0 : 0 ≤ p) (hp2 : p ≤ 1 / 2) (T : ℕ) (y : ℝ)
    (hy1 : (1 - 2 * p) ^ T ≤ y) (hy2 : y ≤ 1) :
    ∃ uu vv : ℕ → ℝ, Coadapted (flipKernel p) (flipCoupling p uu vv) ∧
      agreeProb startLaw (flipCoupling p uu vv) T = y := by
  have hbase : (0 : ℝ) ≤ 1 - 2 * p := by linarith
  have hbase1 : (1 - 2 * p) ≤ 1 := by linarith
  have hpow1 : (1 - 2 * p) ^ T ≤ 1 := pow_le_one₀ hbase hbase1
  have hpow0 : (0 : ℝ) ≤ (1 - 2 * p) ^ T := pow_nonneg hbase T
  set θ : ℝ := if (1 - 2 * p) ^ T = 1 then 0 else (1 - y) / (1 - (1 - 2 * p) ^ T) with hθdef
  have hθ0 : 0 ≤ θ := by
    rw [hθdef]
    by_cases hd : (1 - 2 * p) ^ T = 1
    · rw [if_pos hd]
    · rw [if_neg hd]
      exact div_nonneg (by linarith) (by
        have : (1 - 2 * p) ^ T < 1 := lt_of_le_of_ne hpow1 hd
        linarith)
  have hθ1 : θ ≤ 1 := by
    rw [hθdef]
    by_cases hd : (1 - 2 * p) ^ T = 1
    · rw [if_pos hd]
      norm_num
    · rw [if_neg hd]
      have hlt : (1 - 2 * p) ^ T < 1 := lt_of_le_of_ne hpow1 hd
      rw [div_le_one (by linarith)]
      linarith
  have hterm : mixTrajectory p θ T = y := by
    unfold mixTrajectory
    rw [hθdef]
    by_cases hd : (1 - 2 * p) ^ T = 1
    · rw [if_pos hd, hd]
      have : y = 1 := le_antisymm hy2 (by rw [hd] at hy1; exact hy1)
      rw [this]
      ring
    · rw [if_neg hd]
      have hlt : (1 - 2 * p) ^ T < 1 := lt_of_le_of_ne hpow1 hd
      have hne : (1 : ℝ) - (1 - 2 * p) ^ T ≠ 0 := by linarith
      field_simp
      ring
  have hA0 : mixTrajectory p θ 0 = 1 := by
    unfold mixTrajectory
    norm_num
  have hA : ∀ t, (1 - 2 * p) * mixTrajectory p θ t ≤ mixTrajectory p θ (t + 1) ∧
      mixTrajectory p θ (t + 1)
        ≤ mixTrajectory p θ t + 2 * p * (1 - mixTrajectory p θ t) := by
    intro t
    unfold mixTrajectory
    rw [pow_succ]
    constructor <;> nlinarith [pow_nonneg hbase t]
  obtain ⟨hcoad, hval⟩ :=
    trajectory_attained p hp0 hp2 (mixTrajectory p θ) hA0 hA
  exact ⟨trajU (mixTrajectory p θ), trajV (mixTrajectory p θ), hcoad, (hval T).trans hterm⟩

end Trajectories

end

end Descent.Portability.TurnoverTrajectoryRegion
