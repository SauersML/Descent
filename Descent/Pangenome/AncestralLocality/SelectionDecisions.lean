/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.AncestralLocality.DecisionDualMoments

assert_below Descent.PopGen Descent.Spectral Descent.Blindness Descent.Conditionals
assert_below Descent.Portability Descent.Decision Descent.Program

/-!
# Selection as ancestral decisions

The research note "Ancestral locality" has neutral decisions only: an event copies coordinate `i`
from a second parent according to a deterministic rule. Natural selection fits the same framework
once an event is allowed a random child. A **kernel event** at rate `r` draws two parents from `p`
and a child from a kernel `K(x, y; ·)`; its drift is `r (R_K(p) - p)` with the population map
`reproduce` of (2.1). Decisions are the point-mass kernels `z ↦ 1{T(x,y) = z}`, and selection is
the kernel `selectionKernel s σ`.

* **Selection is a kernel event.** For a fitness `s` with values in `[0, σ]`, the child is the
  second parent `y` with probability `s(y)/σ` and the first parent `x` otherwise. At rate `σ` its
  drift is the classical selective drift `p_z (s(z) - s̄(p))` with mean fitness
  `s̄(p) = ∑_y p_y s(y)` (`reproduce_selectionKernel`), on every vector of total mass one.
* **A kernel event acts on observations as a kernel branching.** The substitution
  `kernelBranch K a f` replaces argument `a` by a child drawn from `K(x_a, x_{n+1}; ·)` of its own
  genome and a new parental genome. Its sampling observable sums the new parent and the child out
  (`samplingObservable_kernelBranch`, `samplingObservable_kernelBranch_eq_sum`). The drift of any
  kernel event on a sampling observable is the kernel branching of every argument,
  `∑_z (R_K(p)(z) - p_z) ∂_z H_f(p) = ∑_a (H_{B_{a,K} f} - H_f)(p)`
  (`kernelDriftTerm_samplingObservable`), with no symmetry of `K` needed. For the selection kernel
  this branching is the ancestral selection graph: the incoming parent wins with probability
  `s(y)/σ`. For a point-mass kernel it is the decision branching of
  `Descent.Pangenome.AncestralLocality.AncestralDecision` (`kernelBranch_indicator`).

Scope. This file is being written. It currently proves the forward selection kernel and the
generator identity for kernel events. The moment uniqueness with selective branching and the
support-tag bounds under selection are not yet in it.

## Empirical status

None. The bodies here are finite sums over a supplied state space, fitness, kernel and vector, so no
measurement can bear on them.
-/

namespace Descent.Pangenome.AncestralLocality

open Finset

variable {H : Type*} {n : ℕ}

/-! ### Selection as a kernel event -/

/-- **The mean fitness** `s̄(p) = ∑_y p_y s(y)` of a vector `p`. -/
def meanFitness [Fintype H] (s p : H → ℝ) : ℝ :=
  ∑ y, p y * s y

/-- **The selection kernel.** The child is the second parent `y` with probability `s(y)/σ` and the
first parent `x` otherwise: a fitness-weighted replacement, the forward form of a selective
event. -/
noncomputable def selectionKernel [DecidableEq H] (s : H → ℝ) (σ : ℝ) (x y z : H) : ℝ :=
  s y / σ * (if y = z then 1 else 0) + (1 - s y / σ) * (if x = z then 1 else 0)

/-- **Selection at rate `σ` is the classical selective drift.** On a vector of total mass one,
`σ (R_{K_s}(p)(z) - p_z) = p_z (s(z) - s̄(p))`. -/
theorem reproduce_selectionKernel [Fintype H] [DecidableEq H] (s : H → ℝ) {σ : ℝ} (hσ : σ ≠ 0)
    {p : H → ℝ} (hp : ∑ h, p h = 1) (z : H) :
    σ * (reproduce (selectionKernel s σ) p z - p z) = p z * (s z - meanFitness s p) := by
  have hterm : ∀ x y, p x * p y * selectionKernel s σ x y z =
      (if y = z then p x * (p z * (s z / σ)) else 0) +
        (if x = z then p z * (p y * (1 - s y / σ)) else 0) := by
    intro x y
    rw [selectionKernel]
    by_cases h1 : y = z
    · by_cases h2 : x = z
      · rw [if_pos h1, if_pos h2, if_pos h1, if_pos h2, h1, h2]
        ring
      · rw [if_pos h1, if_neg h2, if_pos h1, if_neg h2, h1]
        ring
    · by_cases h2 : x = z
      · rw [if_neg h1, if_pos h2, if_neg h1, if_pos h2, h2]
        ring
      · rw [if_neg h1, if_neg h2, if_neg h1, if_neg h2]
        ring
  have hA : ∑ x, ∑ y, (if y = z then p x * (p z * (s z / σ)) else 0) = p z * (s z / σ) := by
    simp only [sum_ite_eq', mem_univ, if_true]
    rw [← sum_mul, hp, one_mul]
  have hB : ∑ x, ∑ y, (if x = z then p z * (p y * (1 - s y / σ)) else 0) =
      p z * (1 - meanFitness s p / σ) := by
    rw [sum_comm]
    simp only [sum_ite_eq', mem_univ, if_true]
    rw [← mul_sum]
    congr 1
    have hsplit : ∑ y, p y * (1 - s y / σ) = ∑ y, p y - ∑ y, p y * s y / σ := by
      rw [← sum_sub_distrib]
      exact sum_congr rfl fun y _ ↦ by ring
    rw [hsplit, hp, meanFitness, sum_div]
  have hrep : reproduce (selectionKernel s σ) p z = p z * (s z / σ) +
      p z * (1 - meanFitness s p / σ) := by
    rw [reproduce, ← hA, ← hB, ← sum_add_distrib]
    refine sum_congr rfl fun x _ ↦ ?_
    rw [← sum_add_distrib]
    exact sum_congr rfl fun y _ ↦ hterm x y
  rw [hrep]
  field_simp <;> ring

/-! ### Kernel branching on observations -/

/-- **Kernel branching `B_{a,K}`.** Argument `a` is replaced by a child drawn from
`K(x_a, x_{n+1}; ·)` of its own genome and a new parental genome in the last argument. -/
def kernelBranch [Fintype H] (K : H → H → H → ℝ) (a : Fin n) (f : (Fin n → H) → ℝ) :
    (Fin (n + 1) → H) → ℝ :=
  fun u ↦ ∑ z, K (u a.castSucc) (u (Fin.last n)) z * f (Function.update (Fin.init u) a z)

/-- **A point-mass kernel branches as its rule.** The kernel `z ↦ 1{T(x,y) = z}` gives the
decision branching of `T`. -/
theorem kernelBranch_indicator [Fintype H] [DecidableEq H] (T : H → H → H) (a : Fin n)
    (f : (Fin n → H) → ℝ) :
    kernelBranch (fun x y z ↦ if T x y = z then 1 else 0) a f = decisionBranch T a f := by
  funext u
  simp only [kernelBranch, decisionBranch, ite_mul, one_mul, zero_mul, sum_ite_eq, mem_univ,
    if_true]

/-- **The branched observable sums the new parent and the child out.** -/
theorem samplingObservable_kernelBranch [Fintype H] (K : H → H → H → ℝ) (a : Fin n)
    (f : (Fin n → H) → ℝ) (p : H → ℝ) :
    samplingObservable (kernelBranch K a f) p =
      ∑ w, ∑ y, ∑ z, K (w a) y z * f (Function.update w a z) * (∏ c, p (w c)) * p y := by
  rw [samplingObservable, sum_tuple_snoc]
  refine sum_congr rfl fun w _ ↦ sum_congr rfl fun y _ ↦ ?_
  simp only [kernelBranch, Fin.init_snoc, Fin.snoc_castSucc, Fin.snoc_last,
    Fin.prod_univ_castSucc, sum_mul]
  refine sum_congr rfl fun z _ ↦ ?_
  ring

/-- **The kernel-branched observable through the population map.** Replacing argument `a` of a
sample by a child drawn from `R_K(p)` gives the observable of the branched function, for every
kernel. -/
theorem samplingObservable_kernelBranch_eq_sum [Fintype H] [DecidableEq H] (K : H → H → H → ℝ)
    (a : Fin n) (f : (Fin n → H) → ℝ) (p : H → ℝ) :
    samplingObservable (kernelBranch K a f) p =
      ∑ w, reproduce K p (w a) * (f w * ∏ c ∈ univ.erase a, p (w c)) := by
  have hrest : ∀ w h, ∏ c ∈ univ.erase a, p (Function.update w a h c) =
      ∏ c ∈ univ.erase a, p (w c) := fun w h ↦
    prod_congr rfl fun c hc ↦ by rw [Function.update_of_ne (ne_of_mem_erase hc)]
  have hmove : ∀ x z : H, ∑ w : Fin n → H,
      (if w a = x then f (Function.update w a z) * ∏ c ∈ univ.erase a, p (w c) else 0) =
        ∑ w : Fin n → H, if w a = z then f w * ∏ c ∈ univ.erase a, p (w c) else 0 := by
    intro x z
    have key := sum_filter_update a (fun _ : Fin n → H ↦ z) (fun _ _ ↦ rfl) x
      (fun w : Fin n → H ↦ f w * ∏ c ∈ univ.erase a, p (w c))
    simp only [sum_filter, hrest] at key
    exact key.symm
  have hleft : ∀ w : Fin n → H, ∑ y, ∑ z, K (w a) y z * f (Function.update w a z) *
      (∏ c, p (w c)) * p y =
        ∑ x, ∑ y, ∑ z, if w a = x then
          p x * p y * K x y z * (f (Function.update w a z) * ∏ c ∈ univ.erase a, p (w c))
          else 0 := by
    intro w
    have h2 : p (w a) * ∏ c ∈ univ.erase a, p (w c) = ∏ c, p (w c) :=
      mul_prod_erase _ (fun c ↦ p (w c)) (mem_univ a)
    refine Eq.trans ?_ (sum_sum_sum_comm univ _)
    refine sum_congr rfl fun y _ ↦ sum_congr rfl fun z _ ↦ ?_
    rw [sum_ite_eq, if_pos (mem_univ _), ← h2]
    ring
  calc samplingObservable (kernelBranch K a f) p
      = ∑ w : Fin n → H, ∑ x, ∑ y, ∑ z, (if w a = x then
          p x * p y * K x y z * (f (Function.update w a z) * ∏ c ∈ univ.erase a, p (w c))
          else 0) := by
        rw [samplingObservable_kernelBranch]
        exact sum_congr rfl fun w _ ↦ hleft w
    _ = ∑ x, ∑ y, ∑ z, p x * p y * K x y z * ∑ w : Fin n → H,
          (if w a = x then f (Function.update w a z) * ∏ c ∈ univ.erase a, p (w c) else 0) := by
        refine sum_comm.trans ?_
        refine sum_congr rfl fun x _ ↦ ?_
        refine (sum_sum_sum_comm univ _).symm.trans ?_
        refine sum_congr rfl fun y _ ↦ sum_congr rfl fun z _ ↦ ?_
        rw [mul_sum]
        refine sum_congr rfl fun w _ ↦ ?_
        rw [mul_ite, mul_zero]
    _ = ∑ x, ∑ y, ∑ z, p x * p y * K x y z * ∑ w : Fin n → H,
          (if w a = z then f w * ∏ c ∈ univ.erase a, p (w c) else 0) :=
        sum_congr rfl fun x _ ↦ sum_congr rfl fun y _ ↦ sum_congr rfl fun z _ ↦ by
          rw [hmove x z]
    _ = ∑ x, ∑ y, ∑ w : Fin n → H,
          p x * p y * K x y (w a) * (f w * ∏ c ∈ univ.erase a, p (w c)) := by
        refine sum_congr rfl fun x _ ↦ sum_congr rfl fun y _ ↦ ?_
        simp only [mul_sum]
        rw [sum_comm]
        refine sum_congr rfl fun w _ ↦ ?_
        simp only [mul_ite, mul_zero, sum_ite_eq, mem_univ, if_true]
    _ = ∑ w : Fin n → H, reproduce K p (w a) * (f w * ∏ c ∈ univ.erase a, p (w c)) := by
        rw [sum_sum_sum_comm]
        refine sum_congr rfl fun w _ ↦ ?_
        rw [reproduce, sum_mul]
        refine sum_congr rfl fun x _ ↦ ?_
        rw [sum_mul]

/-- **The drift of a kernel event is kernel branching (Theorem 6 for kernel events).** On every
vector, `∑_z (R_K(p)(z) - p_z) ∂_z H_f(p) = ∑_a (H_{B_{a,K} f} - H_f)(p)`, for every kernel `K`.
-/
theorem kernelDriftTerm_samplingObservable [Fintype H] [DecidableEq H] (K : H → H → H → ℝ)
    (f : (Fin n → H) → ℝ) (p : H → ℝ) :
    ∑ z, (reproduce K p z - p z) * firstPartial (samplingObservable f) p z =
      ∑ a, (samplingObservable (kernelBranch K a f) p - samplingObservable f p) := by
  have hfirst : ∀ z, firstPartial (samplingObservable f) p z =
      ∑ w, ∑ a, (Pi.single z 1 : H → ℝ) (w a) * (f w * ∏ c ∈ univ.erase a, p (w c)) := by
    intro z
    rw [firstPartial, lineDeriv_samplingObservable]
    refine sum_congr rfl fun w _ ↦ ?_
    rw [mul_sum]
    refine sum_congr rfl fun a _ ↦ ?_
    ring
  have hcollapse : ∀ (u : H) (L : ℝ),
      ∑ z, (reproduce K p z - p z) * ((Pi.single z 1 : H → ℝ) u * L) =
        (reproduce K p u - p u) * L := by
    intro u L
    simp only [Pi.single_apply, ite_mul, one_mul, zero_mul, mul_ite, mul_zero, sum_ite_eq,
      mem_univ, if_true]
  calc ∑ z, (reproduce K p z - p z) * firstPartial (samplingObservable f) p z
      = ∑ w, ∑ a, ∑ z, (reproduce K p z - p z) *
          ((Pi.single z 1 : H → ℝ) (w a) * (f w * ∏ c ∈ univ.erase a, p (w c))) := by
        simp only [hfirst, mul_sum]
        exact (sum_sum_sum_comm univ _).symm
    _ = ∑ w, ∑ a, (reproduce K p (w a) - p (w a)) * (f w * ∏ c ∈ univ.erase a, p (w c)) :=
        sum_congr rfl fun w _ ↦ sum_congr rfl fun a _ ↦ hcollapse (w a) _
    _ = ∑ a, (samplingObservable (kernelBranch K a f) p - samplingObservable f p) := by
        rw [sum_comm]
        refine sum_congr rfl fun a _ ↦ ?_
        rw [samplingObservable_kernelBranch_eq_sum, samplingObservable, ← sum_sub_distrib]
        refine sum_congr rfl fun w _ ↦ ?_
        have h2 : p (w a) * ∏ c ∈ univ.erase a, p (w c) = ∏ c, p (w c) :=
          mul_prod_erase _ (fun c ↦ p (w c)) (mem_univ a)
        rw [← h2]
        ring

end Descent.Pangenome.AncestralLocality
