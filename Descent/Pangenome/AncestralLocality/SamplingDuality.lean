/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.AncestralLocality.AncestralDecision
import Descent.Coalescent.Rates
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Order.Interval.Finset.Fin

assert_below Descent.PopGen Descent.Spectral Descent.Blindness Descent.Conditionals
assert_below Descent.Portability Descent.Decision Descent.Program

/-!
# Sampling duality: the forward generator on sampling observables is the backward circuit

Theorem 6 of the research note "Ancestral locality" connects the forward population process on
`P(H)` with the backward rewriting of observations in
`Descent.Pangenome.AncestralLocality.AncestralDecision`. This file proves the generator identity
behind it, with the forward generator (7.1) written with actual partial derivatives.

The partial derivatives are Mathlib's line derivatives along coordinate directions:
`firstPartial F p z` is `∂_z F(p)` and `secondPartial F p x y` is `∂_{xy} F(p)`. A sampling
observable `H_f(p) = ∑_x f(x) ∏_a p(x_a)` is a polynomial, and its derivatives are computed here,
not assumed: `lineDeriv_samplingObservable` differentiates one argument and
`secondPartial_samplingObservable` two distinct ones. The forward generator (7.1) is
`forwardGenerator c r T`, the sum of the resampling part `resamplingGenerator c` and the decision
part `decisionGenerator r T`, in which every event `e` has rate `r e` and acts through the
population map `reproduce` of (2.1) with the exchange kernel `ruleKernel (T e)` of its rule.

* **The resampling term is coalescence.** On a vector of total mass one,
  `resamplingGenerator c H_f (p) = c ∑_{a<b} (H_{C_ab f} - H_f)(p)`
  (`resamplingGenerator_samplingObservable`).
* **The drift term is decision branching.** On every vector,
  `decisionGenerator r T H_f (p) = ∑_e r_e ∑_a (H_{B_{a,e} f} - H_f)(p)`
  (`decisionGenerator_samplingObservable`), through the sampling identity (7.4) in the form
  `reproduce_ruleKernel`.
* **Theorem 6 at generator level.** The forward generator applied to `H_f` at `p` is the backward
  generator applied to `f` and read at `p` (`forwardGenerator_samplingObservable`); for the
  ordered children `orderedChild i j` on the edges `i → j` this is
  `forwardGenerator_orderedChild`.

The backward generator is a jump generator (`backwardGenerator_eq_jump`) whose total rate from `n`
arguments is `c d_n + n R` (`dualExitRate_eq`), where `d_n = n(n-1)/2` is Kingman's pair count
`Descent.Coalescent.deathRate` (`sum_card_Iio_eq_deathRate`): quadratic in the arity only through
coalescence, which lowers the arity, and linear through branching, which raises it.

Scope. The identity is between generators at one vector, and the forward generator is the formula
(7.1) applied to the polynomial extension of `H_f` off the simplex. The semigroup statement (7.5),
`E_p[H_f(P_t)] = E_f[H_{f_t}(p)]`, is not proved: no forward diffusion on `P(H)` and no backward
jump process are constructed, and nonexplosion appears only as the exit rate `c d_n + n R`. The
span of sampling observables of bounded arity is not closed under branching, so no
finite-dimensional matrix exponential carries the identity to semigroups here.

## Empirical status

None. The bodies here are derivatives of polynomials and finite sums over a supplied state space,
rate table, rule family and vector, so no measurement can bear on them.
-/

namespace Descent.Pangenome.AncestralLocality

open Finset

variable {H : Type*} {n : ℕ}

/-! ### Partial derivatives and the forward generator -/

/-- **The partial derivative `∂_z F(p)`**: the derivative of `F` at `p` along the coordinate
direction of `z`. -/
noncomputable def firstPartial [DecidableEq H] (F : (H → ℝ) → ℝ) (p : H → ℝ) (z : H) : ℝ :=
  lineDeriv ℝ F p (Pi.single z 1)

/-- **The second partial derivative `∂_{xy} F(p)`**: the derivative along `x` of the derivative
along `y`. -/
noncomputable def secondPartial [DecidableEq H] (F : (H → ℝ) → ℝ) (p : H → ℝ) (x y : H) : ℝ :=
  lineDeriv ℝ (fun q ↦ lineDeriv ℝ F q (Pi.single y 1)) p (Pi.single x 1)

/-- **The resampling part of the forward generator (7.1)**,
`(c/2) ∑_{x,y} p_x (1{x=y} - p_y) ∂_{xy} F(p)`. -/
noncomputable def resamplingGenerator [Fintype H] [DecidableEq H] (c : ℝ) (F : (H → ℝ) → ℝ)
    (p : H → ℝ) : ℝ :=
  c / 2 * ∑ x, ∑ y, p x * ((if x = y then 1 else 0) - p y) * secondPartial F p x y

/-- **The decision part of the forward generator (7.1)**,
`∑_e r_e ∑_z (R_{K_e}(p)(z) - p_z) ∂_z F(p)`, where `K_e` is the exchange kernel of the rule of
event `e`. -/
noncomputable def decisionGenerator [Fintype H] [DecidableEq H] {E : Type*} [Fintype E]
    (r : E → ℝ) (T : E → H → H → H) (F : (H → ℝ) → ℝ) (p : H → ℝ) : ℝ :=
  ∑ e, r e * ∑ z, (reproduce (ruleKernel (T e)) p z - p z) * firstPartial F p z

/-- **The forward generator (7.1)** of the population on `P(H)`: resampling at rate `c` and the
events `e` at rates `r e`. -/
noncomputable def forwardGenerator [Fintype H] [DecidableEq H] {E : Type*} [Fintype E] (c : ℝ)
    (r : E → ℝ) (T : E → H → H → H) (F : (H → ℝ) → ℝ) (p : H → ℝ) : ℝ :=
  resamplingGenerator c F p + decisionGenerator r T F p

/-- **The backward generator applied to `f`, read at `p`**: coalescence of every pair `a < b` at
rate `c`, and branching of every argument by every event `e` at rate `r e`. -/
noncomputable def backwardGenerator [Fintype H] [DecidableEq H] {E : Type*} [Fintype E] (c : ℝ)
    (r : E → ℝ) (T : E → H → H → H) (f : (Fin n → H) → ℝ) (p : H → ℝ) : ℝ :=
  c * ∑ b, ∑ a ∈ Iio b,
      (samplingObservable (coalesceArguments a b f) p - samplingObservable f p) +
    ∑ e, r e * ∑ a, (samplingObservable (decisionBranch (T e) a f) p - samplingObservable f p)

/-! ### Derivatives of sampling observables -/

/-- **A product along a line.** `t ↦ ∏_{c ∈ S} (q + t v)(x_c)` has derivative
`∑_{b ∈ S} v(x_b) ∏_{c ∈ S, c ≠ b} q(x_c)` at `t = 0`. -/
theorem hasDerivAt_prod_line (S : Finset (Fin n)) (w : Fin n → H) (q v : H → ℝ) :
    HasDerivAt (fun t : ℝ ↦ ∏ c ∈ S, (q + t • v) (w c))
      (∑ b ∈ S, v (w b) * ∏ c ∈ S.erase b, q (w c)) 0 := by
  have h := HasDerivAt.fun_finset_prod (u := S) (x := (0 : ℝ))
    (f := fun c t ↦ (q + t • v) (w c)) (f' := fun c ↦ v (w c)) fun c _ ↦ by
      simpa using ((hasDerivAt_id (x := (0 : ℝ))).mul_const (v (w c))).const_add (q (w c))
  convert h using 1
  refine sum_congr rfl fun b _ ↦ ?_
  simp only [zero_smul, add_zero, smul_eq_mul]
  exact mul_comm _ _

/-- **The derivative of a sampling observable along a line**:
`d/dt H_f(q + t v) = ∑_x f(x) ∑_a v(x_a) ∏_{c ≠ a} q(x_c)` at `t = 0`. -/
theorem hasDerivAt_samplingObservable_line [Fintype H] (f : (Fin n → H) → ℝ) (q v : H → ℝ) :
    HasDerivAt (fun t : ℝ ↦ samplingObservable f (q + t • v))
      (∑ w, f w * ∑ a, v (w a) * ∏ c ∈ univ.erase a, q (w c)) 0 := by
  unfold samplingObservable
  exact HasDerivAt.fun_sum fun w _ ↦ (hasDerivAt_prod_line univ w q v).const_mul (f w)

/-- **The line derivative of a sampling observable**: one argument at a time is differentiated. -/
theorem lineDeriv_samplingObservable [Fintype H] (f : (Fin n → H) → ℝ) (q v : H → ℝ) :
    lineDeriv ℝ (samplingObservable f) q v =
      ∑ w, f w * ∑ a, v (w a) * ∏ c ∈ univ.erase a, q (w c) :=
  (hasDerivAt_samplingObservable_line f q v).deriv

/-- **The second partial derivative of a sampling observable**: two distinct arguments are
differentiated, one in the direction `y` and the other in the direction `x`. -/
theorem secondPartial_samplingObservable [Fintype H] [DecidableEq H] (f : (Fin n → H) → ℝ)
    (p : H → ℝ) (x y : H) :
    secondPartial (samplingObservable f) p x y =
      ∑ w, f w * ∑ a, Pi.single y (1 : ℝ) (w a) *
        ∑ b ∈ univ.erase a, Pi.single x (1 : ℝ) (w b) *
          ∏ c ∈ (univ.erase a).erase b, p (w c) := by
  have hfun : (fun q ↦ lineDeriv ℝ (samplingObservable f) q (Pi.single y 1)) =
      fun q ↦ ∑ w, f w * ∑ a, Pi.single y (1 : ℝ) (w a) * ∏ c ∈ univ.erase a, q (w c) :=
    funext fun q ↦ lineDeriv_samplingObservable f q _
  rw [secondPartial, hfun]
  refine HasDerivAt.deriv ?_
  exact HasDerivAt.fun_sum fun w _ ↦ (HasDerivAt.fun_sum fun a _ ↦
    (hasDerivAt_prod_line (univ.erase a) w p (Pi.single x 1)).const_mul _).const_mul (f w)

/-! ### The resampling term is coalescence -/

/-- Two sums over finite types pass through a third sum. -/
theorem sum_sum_sum_comm {α β ι : Type*} [Fintype α] [Fintype β] (s : Finset ι)
    (F : α → β → ι → ℝ) :
    ∑ x, ∑ y, ∑ i ∈ s, F x y i = ∑ i ∈ s, ∑ x, ∑ y, F x y i :=
  calc ∑ x, ∑ y, ∑ i ∈ s, F x y i = ∑ x, ∑ i ∈ s, ∑ y, F x y i :=
        sum_congr rfl fun _ _ ↦ sum_comm
    _ = ∑ i ∈ s, ∑ x, ∑ y, F x y i := sum_comm

/-- A sum over the arguments below `b`, written as a sum with an indicator. -/
theorem sum_ite_lt_eq_sum_Iio (b : Fin n) (G : Fin n → ℝ) :
    ∑ a, (if a < b then G a else 0) = ∑ a ∈ Iio b, G a := by
  rw [← sum_filter]
  congr 1
  ext a
  simp

/-- **Ordered pairs of distinct arguments are twice the pairs `a < b`** for a symmetric summand. -/
theorem sum_erase_eq_two_mul_sum_Iio {g : Fin n → Fin n → ℝ}
    (hg : ∀ a b, a ≠ b → g a b = g b a) :
    ∑ a, ∑ b ∈ univ.erase a, g a b = 2 * ∑ b, ∑ a ∈ Iio b, g a b := by
  have hsplit : ∀ a, ∑ b ∈ univ.erase a, g a b =
      ∑ b, (if a < b then g a b else 0) + ∑ b, (if b < a then g b a else 0) := by
    intro a
    rw [← sum_add_distrib,
      ← sum_erase univ (f := fun b ↦ (if a < b then g a b else 0) + (if b < a then g b a else 0))
        (a := a) (by simp)]
    refine sum_congr rfl fun b hb ↦ ?_
    show g a b = (if a < b then g a b else 0) + (if b < a then g b a else 0)
    rcases lt_trichotomy a b with h | h | h
    · rw [if_pos h, if_neg (not_lt.mpr h.le), add_zero]
    · exact absurd h.symm (ne_of_mem_erase hb)
    · rw [if_neg (not_lt.mpr h.le), if_pos h, zero_add, hg a b (ne_of_mem_erase hb).symm]
  have hfirst : ∑ a, ∑ b, (if a < b then g a b else 0) = ∑ b, ∑ a ∈ Iio b, g a b := by
    rw [sum_comm]
    exact sum_congr rfl fun b _ ↦ sum_ite_lt_eq_sum_Iio b fun a ↦ g a b
  have hsecond : ∑ a, ∑ b, (if b < a then g b a else 0) = ∑ b, ∑ a ∈ Iio b, g a b :=
    sum_congr rfl fun a _ ↦ sum_ite_lt_eq_sum_Iio a fun b ↦ g b a
  rw [sum_congr rfl fun a _ ↦ hsplit a, sum_add_distrib, hfirst, hsecond]
  ring

/-- **The resampling term is coalescence (Theorem 6).** On a vector of total mass one the resampling
part of the forward generator, applied to a sampling observable, is
`c ∑_{a<b} (H_{C_ab f} - H_f)(p)`. -/
theorem resamplingGenerator_samplingObservable [Fintype H] [DecidableEq H] (c : ℝ)
    (f : (Fin n → H) → ℝ) {p : H → ℝ} (hp : ∑ h, p h = 1) :
    resamplingGenerator c (samplingObservable f) p =
      c * ∑ b, ∑ a ∈ Iio b,
        (samplingObservable (coalesceArguments a b f) p - samplingObservable f p) := by
  have hcollapse : ∀ (u v : H) (K : ℝ), ∑ x, ∑ y, p x * ((if x = y then 1 else 0) - p y) *
      (Pi.single y (1 : ℝ) u * (Pi.single x (1 : ℝ) v * K)) =
        p v * ((if v = u then 1 else 0) - p u) * K := by
    intro u v K
    have hpt : ∀ x y, p x * ((if x = y then 1 else 0) - p y) *
        (Pi.single y (1 : ℝ) u * (Pi.single x (1 : ℝ) v * K)) =
          if u = y then (if v = x then p x * ((if x = y then 1 else 0) - p y) * K else 0)
          else 0 := by
      intro x y
      simp only [Pi.single_apply]
      split_ifs <;> ring
    simp only [hpt, sum_ite_eq, mem_univ, if_true]
  have hexpand : ∀ x y, secondPartial (samplingObservable f) p x y =
      ∑ w, ∑ a, ∑ b ∈ univ.erase a, Pi.single y (1 : ℝ) (w a) *
        (Pi.single x (1 : ℝ) (w b) * (f w * ∏ c ∈ (univ.erase a).erase b, p (w c))) := by
    intro x y
    rw [secondPartial_samplingObservable]
    refine sum_congr rfl fun w _ ↦ ?_
    rw [mul_sum]
    refine sum_congr rfl fun a _ ↦ ?_
    rw [mul_sum, mul_sum]
    refine sum_congr rfl fun b _ ↦ ?_
    ring
  have hpair : ∀ (w : Fin n → H) (a : Fin n), ∀ b ∈ univ.erase a,
      p (w b) * ((if w b = w a then 1 else 0) - p (w a)) *
        (f w * ∏ c ∈ (univ.erase a).erase b, p (w c)) =
      (if w a = w b then f w * ∏ c ∈ univ.erase a, p (w c) else 0) - f w * ∏ c, p (w c) := by
    intro w a b hb
    have h1 : p (w b) * ∏ c ∈ (univ.erase a).erase b, p (w c) = ∏ c ∈ univ.erase a, p (w c) :=
      mul_prod_erase _ (fun c ↦ p (w c)) hb
    have h2 : p (w a) * ∏ c ∈ univ.erase a, p (w c) = ∏ c, p (w c) :=
      mul_prod_erase _ (fun c ↦ p (w c)) (mem_univ a)
    by_cases hw : w a = w b
    · rw [if_pos hw.symm, if_pos hw, ← h2, ← h1]
      ring
    · rw [if_neg fun h ↦ hw h.symm, if_neg hw, ← h2, ← h1]
      ring
  have hmain : resamplingGenerator c (samplingObservable f) p =
      c / 2 * ∑ a, ∑ b ∈ univ.erase a,
        (samplingObservable (coalesceArguments a b f) p - samplingObservable f p) := by
    rw [resamplingGenerator]
    congr 1
    calc ∑ x, ∑ y, p x * ((if x = y then 1 else 0) - p y) *
          secondPartial (samplingObservable f) p x y
        = ∑ w, ∑ a, ∑ b ∈ univ.erase a, p (w b) * ((if w b = w a then 1 else 0) - p (w a)) *
            (f w * ∏ c ∈ (univ.erase a).erase b, p (w c)) := by
          simp only [hexpand, mul_sum]
          rw [sum_sum_sum_comm]
          refine sum_congr rfl fun w _ ↦ ?_
          rw [sum_sum_sum_comm]
          refine sum_congr rfl fun a _ ↦ ?_
          rw [sum_sum_sum_comm]
          exact sum_congr rfl fun b _ ↦ hcollapse (w a) (w b) _
      _ = ∑ w, ∑ a, ∑ b ∈ univ.erase a,
            ((if w a = w b then f w * ∏ c ∈ univ.erase a, p (w c) else 0) -
              f w * ∏ c, p (w c)) :=
          sum_congr rfl fun w _ ↦ sum_congr rfl fun a _ ↦ sum_congr rfl fun b hb ↦
            hpair w a b hb
      _ = ∑ a, ∑ b ∈ univ.erase a,
            (samplingObservable (coalesceArguments a b f) p - samplingObservable f p) := by
          rw [sum_comm]
          refine sum_congr rfl fun a _ ↦ ?_
          rw [sum_comm]
          refine sum_congr rfl fun b hb ↦ ?_
          rw [sum_sub_distrib,
            samplingObservable_coalesceArguments (ne_of_mem_erase hb).symm f hp]
          rfl
  have hsym : ∀ a b : Fin n, a ≠ b →
      samplingObservable (coalesceArguments a b f) p - samplingObservable f p =
        samplingObservable (coalesceArguments b a f) p - samplingObservable f p :=
    fun a b hab ↦ by rw [samplingObservable_coalesceArguments_comm hab f hp]
  rw [hmain, sum_erase_eq_two_mul_sum_Iio hsym]
  ring

/-! ### The drift term is decision branching -/

/-- **The population map of a rule kernel is the law of the ordered child** `T(x, y)` under
`p ⊗ p`: the sampling identity (7.4) read at an indicator. -/
theorem reproduce_ruleKernel [Fintype H] [DecidableEq H] (T : H → H → H) (p : H → ℝ) (z : H) :
    reproduce (ruleKernel T) p z = ∑ x, ∑ y, p x * p y * if T x y = z then 1 else 0 := by
  rw [← sampling_identity T p fun h ↦ if h = z then 1 else 0]
  simp only [mul_ite, mul_one, mul_zero, sum_ite_eq', mem_univ, if_true]
  rfl

/-- **The branched observable through the population map.** Replacing argument `a` of a sample by
a child drawn from `R_{K_T}(p)` gives the observable of the branched function. -/
theorem samplingObservable_decisionBranch_eq_sum [Fintype H] [DecidableEq H] (T : H → H → H)
    (a : Fin n) (f : (Fin n → H) → ℝ) (p : H → ℝ) :
    samplingObservable (decisionBranch T a f) p =
      ∑ w, reproduce (ruleKernel T) p (w a) * (f w * ∏ c ∈ univ.erase a, p (w c)) := by
  have hrest : ∀ w h, ∏ c ∈ univ.erase a, p (Function.update w a h c) =
      ∏ c ∈ univ.erase a, p (w c) := fun w h ↦
    prod_congr rfl fun c hc ↦ by rw [Function.update_of_ne (ne_of_mem_erase hc)]
  have hpoint : ∀ w : Fin n → H, reproduce (ruleKernel T) p (w a) *
      (f w * ∏ c ∈ univ.erase a, p (w c)) =
        ∑ x, ∑ y, if w a = T x y then p x * p y * (f w * ∏ c ∈ univ.erase a, p (w c))
          else 0 := by
    intro w
    rw [reproduce_ruleKernel, sum_mul]
    refine sum_congr rfl fun x _ ↦ ?_
    rw [sum_mul]
    refine sum_congr rfl fun y _ ↦ ?_
    by_cases h : w a = T x y
    · rw [if_pos h, if_pos h.symm]
      ring
    · rw [if_neg h, if_neg fun h' ↦ h h'.symm]
      ring
  have hmove : ∀ x y, ∑ w : Fin n → H, (if w a = T x y then
      p x * p y * (f w * ∏ c ∈ univ.erase a, p (w c)) else 0) =
        ∑ w : Fin n → H, if w a = x then
          p x * p y * (f (Function.update w a (T x y)) * ∏ c ∈ univ.erase a, p (w c))
          else 0 := by
    intro x y
    have key := sum_filter_update a (fun _ : Fin n → H ↦ T x y) (fun _ _ ↦ rfl) x
      (fun w : Fin n → H ↦ p x * p y * (f w * ∏ c ∈ univ.erase a, p (w c)))
    simp only [sum_filter, hrest] at key
    exact key
  have hlast : ∀ w : Fin n → H, ∑ x, ∑ y, (if w a = x then
      p x * p y * (f (Function.update w a (T x y)) * ∏ c ∈ univ.erase a, p (w c)) else 0) =
        ∑ y, f (Function.update w a (T (w a) y)) * (∏ c, p (w c)) * p y := by
    intro w
    have h2 : p (w a) * ∏ c ∈ univ.erase a, p (w c) = ∏ c, p (w c) :=
      mul_prod_erase _ (fun c ↦ p (w c)) (mem_univ a)
    rw [sum_comm]
    refine sum_congr rfl fun y _ ↦ ?_
    rw [sum_ite_eq, if_pos (mem_univ _), ← h2]
    ring
  rw [samplingObservable_decisionBranch, sum_congr rfl fun w _ ↦ hpoint w,
    ← sum_sum_sum_comm univ, sum_congr rfl fun x _ ↦ sum_congr rfl fun y _ ↦ hmove x y,
    sum_sum_sum_comm univ]
  exact sum_congr rfl fun w _ ↦ (hlast w).symm

/-- **The drift term of one rule is decision branching (Theorem 6).** On every vector,
`∑_z (R_{K_T}(p)(z) - p_z) ∂_z H_f(p) = ∑_a (H_{B_{a,T} f} - H_f)(p)`. -/
theorem driftTerm_samplingObservable [Fintype H] [DecidableEq H] (T : H → H → H)
    (f : (Fin n → H) → ℝ) (p : H → ℝ) :
    ∑ z, (reproduce (ruleKernel T) p z - p z) * firstPartial (samplingObservable f) p z =
      ∑ a, (samplingObservable (decisionBranch T a f) p - samplingObservable f p) := by
  have hfirst : ∀ z, firstPartial (samplingObservable f) p z =
      ∑ w, ∑ a, Pi.single z (1 : ℝ) (w a) * (f w * ∏ c ∈ univ.erase a, p (w c)) := by
    intro z
    rw [firstPartial, lineDeriv_samplingObservable]
    refine sum_congr rfl fun w _ ↦ ?_
    rw [mul_sum]
    refine sum_congr rfl fun a _ ↦ ?_
    ring
  have hcollapse : ∀ (u : H) (K : ℝ),
      ∑ z, (reproduce (ruleKernel T) p z - p z) * (Pi.single z (1 : ℝ) u * K) =
        (reproduce (ruleKernel T) p u - p u) * K := by
    intro u K
    simp only [Pi.single_apply, ite_mul, one_mul, zero_mul, mul_ite, mul_zero, sum_ite_eq,
      mem_univ, if_true]
  calc ∑ z, (reproduce (ruleKernel T) p z - p z) * firstPartial (samplingObservable f) p z
      = ∑ w, ∑ a, ∑ z, (reproduce (ruleKernel T) p z - p z) *
          (Pi.single z (1 : ℝ) (w a) * (f w * ∏ c ∈ univ.erase a, p (w c))) := by
        simp only [hfirst, mul_sum]
        exact (sum_sum_sum_comm univ _).symm
    _ = ∑ w, ∑ a, (reproduce (ruleKernel T) p (w a) - p (w a)) *
          (f w * ∏ c ∈ univ.erase a, p (w c)) :=
        sum_congr rfl fun w _ ↦ sum_congr rfl fun a _ ↦ hcollapse (w a) _
    _ = ∑ a, (samplingObservable (decisionBranch T a f) p - samplingObservable f p) := by
        rw [sum_comm]
        refine sum_congr rfl fun a _ ↦ ?_
        rw [samplingObservable_decisionBranch_eq_sum, samplingObservable, ← sum_sub_distrib]
        refine sum_congr rfl fun w _ ↦ ?_
        have h2 : p (w a) * ∏ c ∈ univ.erase a, p (w c) = ∏ c, p (w c) :=
          mul_prod_erase _ (fun c ↦ p (w c)) (mem_univ a)
        rw [← h2]
        ring

/-- **The decision part of the forward generator is decision branching (Theorem 6).** -/
theorem decisionGenerator_samplingObservable [Fintype H] [DecidableEq H] {E : Type*} [Fintype E]
    (r : E → ℝ) (T : E → H → H → H) (f : (Fin n → H) → ℝ) (p : H → ℝ) :
    decisionGenerator r T (samplingObservable f) p =
      ∑ e, r e * ∑ a,
        (samplingObservable (decisionBranch (T e) a f) p - samplingObservable f p) :=
  sum_congr rfl fun e _ ↦ congrArg (r e * ·) (driftTerm_samplingObservable (T e) f p)

/-! ### Theorem 6 at generator level -/

/-- **Theorem 6, the generator identity.** On a vector `p` of total mass one, the forward generator
(7.1) applied to the sampling observable `H_f` is the backward generator applied to `f` and read at
`p`: coalescence of the pairs of arguments at rate `c`, and decision branching of every argument by
every event at its rate. -/
theorem forwardGenerator_samplingObservable [Fintype H] [DecidableEq H] {E : Type*} [Fintype E]
    (c : ℝ) (r : E → ℝ) (T : E → H → H → H) (f : (Fin n → H) → ℝ) {p : H → ℝ}
    (hp : ∑ h, p h = 1) :
    forwardGenerator c r T (samplingObservable f) p = backwardGenerator c r T f p := by
  rw [forwardGenerator, resamplingGenerator_samplingObservable c f hp,
    decisionGenerator_samplingObservable]
  rfl

/-- **Theorem 6 for the checked-exchange model.** With an event for every ordered pair `(i, j)`,
at rate `r (i, j)` (zero off the edges of the checking graph) and with the ordered child (4.1) as
its rule, the forward generator on sampling observables is the ancestral decision circuit. -/
theorem forwardGenerator_orderedChild {V : Type*} [Fintype V] [DecidableEq V] (c : ℝ)
    (r : V × V → ℝ) (f : (Fin n → V → Bool) → ℝ) {p : (V → Bool) → ℝ} (hp : ∑ h, p h = 1) :
    forwardGenerator c r (fun e ↦ orderedChild e.1 e.2) (samplingObservable f) p =
      backwardGenerator c r (fun e ↦ orderedChild e.1 e.2) f p :=
  forwardGenerator_samplingObservable c r _ f hp

/-! ### The jump rates of the backward circuit -/

/-- **The number of coalescence events from `n` arguments is Kingman's pair count**
`d_n = n(n-1)/2`, `Descent.Coalescent.deathRate`. -/
theorem sum_card_Iio_eq_deathRate (n : ℕ) :
    ∑ b : Fin n, ((Iio b).card : ℝ) = Coalescent.deathRate n := by
  simp only [Fin.card_Iio]
  rw [Coalescent.deathRate, Descent.Core.pairCount]
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.coe_castSucc, Fin.val_last]
    rw [ih]
    push_cast
    ring

/-- **The total jump rate of the backward circuit** from `n` arguments: every pair `a < b`
coalesces at rate `c`, and every argument branches by every event `e` at rate `r e`. -/
noncomputable def dualExitRate {E : Type*} [Fintype E] (c : ℝ) (r : E → ℝ) (n : ℕ) : ℝ :=
  c * ∑ b : Fin n, ((Iio b).card : ℝ) + n * ∑ e, r e

/-- **The exit rate is `c d_n + n R`**: quadratic in the arity through coalescence, which lowers
the arity, and linear through branching, which raises it by one. -/
theorem dualExitRate_eq {E : Type*} [Fintype E] (c : ℝ) (r : E → ℝ) (n : ℕ) :
    dualExitRate c r n = c * Coalescent.deathRate n + n * ∑ e, r e := by
  rw [dualExitRate, sum_card_Iio_eq_deathRate]

/-- **The backward generator is a jump generator**: the observables of the substituted functions
at their rates, minus the exit rate times the observable itself. -/
theorem backwardGenerator_eq_jump [Fintype H] [DecidableEq H] {E : Type*} [Fintype E] (c : ℝ)
    (r : E → ℝ) (T : E → H → H → H) (f : (Fin n → H) → ℝ) (p : H → ℝ) :
    backwardGenerator c r T f p =
      c * ∑ b, ∑ a ∈ Iio b, samplingObservable (coalesceArguments a b f) p +
        ∑ e, r e * ∑ a, samplingObservable (decisionBranch (T e) a f) p -
          dualExitRate c r n * samplingObservable f p := by
  have hcoal : ∑ b : Fin n, ∑ a ∈ Iio b,
      (samplingObservable (coalesceArguments a b f) p - samplingObservable f p) =
        ∑ b, ∑ a ∈ Iio b, samplingObservable (coalesceArguments a b f) p -
          (∑ b : Fin n, ((Iio b).card : ℝ)) * samplingObservable f p := by
    rw [sum_mul, ← sum_sub_distrib]
    refine sum_congr rfl fun b _ ↦ ?_
    rw [sum_sub_distrib, sum_const, nsmul_eq_mul]
  have hdec : ∑ e, r e * ∑ a : Fin n,
      (samplingObservable (decisionBranch (T e) a f) p - samplingObservable f p) =
        ∑ e, r e * ∑ a, samplingObservable (decisionBranch (T e) a f) p -
          (∑ e, r e) * (n * samplingObservable f p) := by
    rw [sum_mul, ← sum_sub_distrib]
    refine sum_congr rfl fun e _ ↦ ?_
    rw [sum_sub_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  rw [backwardGenerator, dualExitRate, hcoal, hdec]
  ring

end Descent.Pangenome.AncestralLocality
