/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.AncestralLocality.DecisionDualMoments

assert_below Descent.PopGen Descent.Spectral Descent.Blindness Descent.Conditionals
assert_below Descent.Portability Descent.Decision Descent.Program

/-!
# Selection as ancestral decisions: one branching mechanism

The research note "Ancestral locality" has neutral decisions only: an event copies coordinate `i`
from a second parent by a deterministic rule. Natural selection fits the same framework once an
event may have a random child. A **kernel event** at rate `r` draws two parents from `p` and a
child from a kernel `K(x, y; ·)`; its drift is `r (R_K(p) - p)` with the population map `reproduce`
of (2.1). Decisions are point-mass kernels, and selection is `selectionKernel s σ`. This file proves
that the three results of the note's §7-§8 (the generator identity, the moment form of the duality,
and the support drift bounds) hold for kernel events, and so for selection.

**Selection is a kernel event.** For a fitness `s` with values in `[0, σ]`, the child is the second
parent `y` with probability `s(y)/σ` and the first parent `x` otherwise (`selectionKernel`, a
probability kernel by `selectionKernel_nonneg` and `sum_selectionKernel`). At rate `σ` its drift is
the classical selective drift `p_z (s(z) - s̄(p))`, with mean fitness `s̄(p) = ∑_y p_y s(y)`, on
every vector of total mass one (`reproduce_selectionKernel`, `selectionGenerator_eq_drift`).

**Theorem 6 with selection.** The substitution `kernelBranch K a f` replaces argument `a` by a child
drawn from `K(x_a, x_{n+1}; ·)` of its own genome and a new parental genome
(`samplingObservable_kernelBranch`, `samplingObservable_kernelBranch_eq_sum`). On every sampling
observable the drift of any kernel event is the kernel branching of every argument,
`∑_z (R_K(p)(z) - p_z) ∂_z H_f(p) = ∑_a (H_{B_{a,K} f} - H_f)(p)`
(`kernelDriftTerm_samplingObservable`), with no symmetry of `K` needed. A point-mass kernel branches
as its rule (`kernelBranch_indicator`). The selection kernel branches as the ancestral selection
graph: the incoming parent wins with probability `s(y)/σ` (`kernelBranch_selectionKernel`), and
the selective part of the forward generator is `σ ∑_a (H_{B_{a,K_s} f} - H_f)`
(`selectionGenerator_samplingObservable`).

**The duality (7.5) with selection, in moment form.** The uniqueness proof of
`Descent.Pangenome.AncestralLocality.DecisionDualMoments` uses only two facts about branching: it
is linear, and it costs at most `k R` in sup norm from arity `k`. Here it is stated once for every
such branching gain `G` (`branchingMomentGenerator`, `hasDerivAt_duhamel_branching`,
`abs_moment_le_choose_mul_pow_branching`, `moment_eq_zero_branching`,
`moments_eq_of_branchingEquation`). Decisions are one instance
(`momentGenerator_eq_branchingMomentGenerator`). Probability kernels contract the sup norm
(`norm_kernelBranch_le`, `norm_kernelBranchingGain_le`), so kernel events are another: two bounded
moment families obeying the moment equation of decisions and selection together, equal at time zero,
agree at every time (`moments_eq_of_kernelMomentEquation`).

**Locality survives selection.** A fitness read at a set `S` of coordinates (`FitnessDetermined`,
witness `fitnessDetermined_restrict`) gives support tags `selectionTags S a A`. A selective
branching on an argument with an empty tag does not read the new parent; otherwise the new parent
needs `A_a ∪ S` (`tagDetermined_selectionBranch`). The support weight rises by at most
`w(A_a) + w(S)` (`tagWeight_selectionTags_le`, `tagCount_selectionTags_le`). For weights at least
one on every coordinate, as the light-cone weights `a^{d(v, A ∪ S)}` are, the selective increments
at rate `σ` per nonempty argument total at most `σ (1 + w(S)) Z^{(w)}` (`selectionWeightRate_le`).
With the decision increments of `Descent.Pangenome.AncestralLocality.AncestralDecision`, the
support drift is at most `(3D + σ (1 + |S|)) Z` (`supportDrift_le`). This is the constant `3D` of
Theorem 7 with selection added. Distance is measured from the query together with the fitness
support: selection copies whole genomes, so a distant fitness locus enters the cone at once.

Scope. The generator identity and the moment uniqueness are proved in full for finite state spaces,
nonnegative rates and probability kernels. The fitness takes values in `[0, σ]`, and a general
fitness is first shifted. The support-drift statements are the generator-level increment and rate
bounds. The expectation bounds (8.2), (8.3), (9.1) and (9.2) under selection follow by the
Grönwall and Dynkin arguments of `Descent.Pangenome.AncestralLocality.LocalityBounds`, which are
not re-derived here. The backward jump process and the forward diffusion are not constructed.

## Empirical status

None. The bodies here are finite sums, linear operators and exponentials over a supplied state
space, fitness, kernel family, rate table and moment family, so no measurement can bear on them.
-/

namespace Descent.Pangenome.AncestralLocality

open Finset Filter Topology

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

/-- The selection kernel is nonnegative for a fitness with values in `[0, σ]`. -/
theorem selectionKernel_nonneg [DecidableEq H] {s : H → ℝ} {σ : ℝ} (hσ : 0 < σ)
    (hs0 : ∀ y, 0 ≤ s y) (hsσ : ∀ y, s y ≤ σ) (x y z : H) : 0 ≤ selectionKernel s σ x y z := by
  have h1 : 0 ≤ s y / σ := div_nonneg (hs0 y) hσ.le
  have h2 : 0 ≤ 1 - s y / σ := by
    rw [sub_nonneg, div_le_one hσ]
    exact hsσ y
  rw [selectionKernel]
  refine add_nonneg (mul_nonneg h1 ?_) (mul_nonneg h2 ?_)
  · split_ifs <;> norm_num
  · split_ifs <;> norm_num

/-- The selection kernel sums to one. -/
theorem sum_selectionKernel [Fintype H] [DecidableEq H] (s : H → ℝ) (σ : ℝ) (x y : H) :
    ∑ z, selectionKernel s σ x y z = 1 := by
  simp only [selectionKernel, sum_add_distrib, ← mul_sum, sum_ite_eq, mem_univ, if_true]
  ring

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

/-- **The selection kernel branches as the ancestral selection graph**: the incoming parent wins
with probability `s(y)/σ`, and the continuing genome is kept otherwise. -/
theorem kernelBranch_selectionKernel [Fintype H] [DecidableEq H] (s : H → ℝ) (σ : ℝ) (a : Fin n)
    (f : (Fin n → H) → ℝ) (u : Fin (n + 1) → H) :
    kernelBranch (selectionKernel s σ) a f u =
      s (u (Fin.last n)) / σ * f (Function.update (Fin.init u) a (u (Fin.last n))) +
        (1 - s (u (Fin.last n)) / σ) * f (Function.update (Fin.init u) a (u a.castSucc)) := by
  simp only [kernelBranch, selectionKernel, add_mul, mul_assoc, sum_add_distrib, ← mul_sum,
    ite_mul, one_mul, zero_mul, sum_ite_eq, mem_univ, if_true]

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

/-- **The selective part of the forward generator (7.1)**, `σ ∑_z (R_{K_s}(p)(z) - p_z) ∂_z F(p)`.
-/
noncomputable def selectionGenerator [Fintype H] [DecidableEq H] (s : H → ℝ) (σ : ℝ)
    (F : (H → ℝ) → ℝ) (p : H → ℝ) : ℝ :=
  σ * ∑ z, (reproduce (selectionKernel s σ) p z - p z) * firstPartial F p z

/-- **The selective generator is the classical selective drift**
`∑_z p_z (s(z) - s̄(p)) ∂_z F(p)` on a vector of total mass one. -/
theorem selectionGenerator_eq_drift [Fintype H] [DecidableEq H] (s : H → ℝ) {σ : ℝ} (hσ : σ ≠ 0)
    (F : (H → ℝ) → ℝ) {p : H → ℝ} (hp : ∑ h, p h = 1) :
    selectionGenerator s σ F p = ∑ z, p z * (s z - meanFitness s p) * firstPartial F p z := by
  rw [selectionGenerator, mul_sum]
  refine sum_congr rfl fun z _ ↦ ?_
  rw [← mul_assoc, reproduce_selectionKernel s hσ hp z]

/-- **Theorem 6 with selection.** On every vector the selective part of the forward generator,
applied to a sampling observable, is selective branching at rate `σ` of every argument. -/
theorem selectionGenerator_samplingObservable [Fintype H] [DecidableEq H] (s : H → ℝ) (σ : ℝ)
    (f : (Fin n → H) → ℝ) (p : H → ℝ) :
    selectionGenerator s σ (samplingObservable f) p =
      σ * ∑ a, (samplingObservable (kernelBranch (selectionKernel s σ) a f) p -
        samplingObservable f p) := by
  rw [selectionGenerator, kernelDriftTerm_samplingObservable]

/-! ### One branching mechanism: the moment uniqueness -/

/-- **The exit rate of a branching mechanism** `c d_k + k R` from arity `k`. -/
def branchingExitRate (c R : ℝ) (k : ℕ) : ℝ :=
  c * ∑ b : Fin k, ((Iio b).card : ℝ) + k * R

/-- The exit rate of the decision circuit is the branching exit rate with `R = ∑_e r_e`. -/
theorem dualExitRate_eq_branchingExitRate {E : Type*} [Fintype E] (c : ℝ) (r : E → ℝ) (k : ℕ) :
    dualExitRate c r k = branchingExitRate c (∑ e, r e) k :=
  rfl

/-- **The moment generator of a branching mechanism**: the coalescence gain, a branching gain `G`
into arity `k + 1`, and the loss at the exit rate `c d_k + k R`. -/
def branchingMomentGenerator (c R : ℝ)
    (G : (k : ℕ) → ((Fin k → H) → ℝ) →ₗ[ℝ] ((Fin (k + 1) → H) → ℝ))
    (m : (k : ℕ) → ((Fin k → H) → ℝ) →ₗ[ℝ] ℝ) (k : ℕ) (g : (Fin k → H) → ℝ) : ℝ :=
  m k (coalescenceGain c g) + m (k + 1) (G k g) - branchingExitRate c R k * m k g

/-- **Decisions are a branching mechanism**, with branching gain `branchingGain r T`. -/
theorem momentGenerator_eq_branchingMomentGenerator {E : Type*} [Fintype E] (c : ℝ) (r : E → ℝ)
    (T : E → H → H → H) (m : (k : ℕ) → ((Fin k → H) → ℝ) →ₗ[ℝ] ℝ) (k : ℕ)
    (g : (Fin k → H) → ℝ) :
    momentGenerator c r T m k g =
      branchingMomentGenerator c (∑ e, r e) (fun j ↦ branchingGain r T) m k g := by
  rw [momentGenerator_eq, branchingMomentGenerator, dualExitRate_eq_branchingExitRate]

/-- The branching moment generator is linear in the family. -/
theorem branchingMomentGenerator_sub (c R : ℝ)
    (G : (k : ℕ) → ((Fin k → H) → ℝ) →ₗ[ℝ] ((Fin (k + 1) → H) → ℝ))
    (m m' : (k : ℕ) → ((Fin k → H) → ℝ) →ₗ[ℝ] ℝ) (k : ℕ) (g : (Fin k → H) → ℝ) :
    branchingMomentGenerator c R G (fun j ↦ m j - m' j) k g =
      branchingMomentGenerator c R G m k g - branchingMomentGenerator c R G m' k g := by
  simp only [branchingMomentGenerator, LinearMap.sub_apply]
  ring

/-- **Duhamel's formula for a branching mechanism.** Along
`u ↦ e^{-λ(t-u)} m_u(e^{(t-u)P} f)` with `λ = c d_n + n R`, coalescence and the loss cancel and only
the branching gain into arity `n + 1` remains. -/
theorem hasDerivAt_duhamel_branching [Fintype H] [DecidableEq H] (c R : ℝ)
    (G : (k : ℕ) → ((Fin k → H) → ℝ) →ₗ[ℝ] ((Fin (k + 1) → H) → ℝ))
    (m : ℝ → (k : ℕ) → ((Fin k → H) → ℝ) →ₗ[ℝ] ℝ)
    (hm : ∀ s k (g : (Fin k → H) → ℝ),
      HasDerivAt (fun u ↦ m u k g) (branchingMomentGenerator c R G (m s) k g) s)
    (t s : ℝ) (f : (Fin n → H) → ℝ) :
    HasDerivAt
      (fun u ↦ Real.exp (-branchingExitRate c R n * (t - u)) * m u n (gainSemigroup c (t - u) f))
      (Real.exp (-branchingExitRate c R n * (t - s)) *
        m s (n + 1) (G n (gainSemigroup c (t - s) f))) s := by
  have hdecomp : ∀ (u : ℝ) (x : (Fin n → H) → ℝ),
      m u n x = ∑ w, x w * m u n (fun j ↦ if w = j then 1 else 0) := fun u x ↦ by
    conv_lhs => rw [pi_eq_sum_univ x]
    simp only [map_sum, map_smul, smul_eq_mul]
  have hlinear : ∀ x : (Fin n → H) → ℝ,
      ∑ w, x w * branchingMomentGenerator c R G (m s) n (fun j ↦ if w = j then 1 else 0) =
        branchingMomentGenerator c R G (m s) n x := fun x ↦ by
    have hP : m s n (coalescenceGain c x) =
        ∑ w, x w * m s n (coalescenceGain c (fun j ↦ if w = j then 1 else 0)) := by
      conv_lhs => rw [pi_eq_sum_univ x]
      simp only [map_sum, map_smul, smul_eq_mul]
    have hG : m s (n + 1) (G n x) =
        ∑ w, x w * m s (n + 1) (G n (fun j ↦ if w = j then 1 else 0)) := by
      conv_lhs => rw [pi_eq_sum_univ x]
      simp only [map_sum, map_smul, smul_eq_mul]
    simp only [branchingMomentGenerator, mul_sub, mul_add, sum_sub_distrib, sum_add_distrib]
    rw [hP, hG, hdecomp s x, mul_sum]
    congr 1
    refine sum_congr rfl fun w _ ↦ ?_
    ring
  have hv : HasDerivAt (fun u ↦ gainSemigroup c (t - u) f)
      ((-1 : ℝ) • coalescenceGain c (gainSemigroup c (t - s) f)) s :=
    HasDerivAt.scomp (hg := hasDerivAt_gainSemigroup_apply c (t - s) f)
      (hh := (hasDerivAt_id (x := s)).const_sub t)
  have hsum : HasDerivAt
      (fun u ↦ ∑ w, gainSemigroup c (t - u) f w * m u n (fun j ↦ if w = j then 1 else 0))
      (∑ w, (((-1 : ℝ) • coalescenceGain c (gainSemigroup c (t - s) f)) w *
          m s n (fun j ↦ if w = j then 1 else 0) +
        gainSemigroup c (t - s) f w *
          branchingMomentGenerator c R G (m s) n (fun j ↦ if w = j then 1 else 0))) s :=
    HasDerivAt.fun_sum fun w _ ↦ (HasFDerivAt.comp_hasDerivAt
      (hl := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n → H ↦ ℝ) w).hasFDerivAt)
      (hf := hv)).mul (hm s n _)
  have hvalue : ∑ w, (((-1 : ℝ) • coalescenceGain c (gainSemigroup c (t - s) f)) w *
        m s n (fun j ↦ if w = j then 1 else 0) +
      gainSemigroup c (t - s) f w *
        branchingMomentGenerator c R G (m s) n (fun j ↦ if w = j then 1 else 0)) =
      m s (n + 1) (G n (gainSemigroup c (t - s) f)) -
        branchingExitRate c R n * m s n (gainSemigroup c (t - s) f) := by
    rw [sum_add_distrib, ← hdecomp, hlinear, branchingMomentGenerator, map_smul, smul_eq_mul]
    ring
  rw [hvalue] at hsum
  have hψ := hsum.congr_of_eventuallyEq (Filter.Eventually.of_forall fun u ↦ hdecomp u _)
  have hexp : HasDerivAt (fun u ↦ Real.exp (-branchingExitRate c R n * (t - u)))
      (Real.exp (-branchingExitRate c R n * (t - s)) * (-branchingExitRate c R n * -1)) s :=
    (((hasDerivAt_id (x := s)).const_sub t).const_mul (-branchingExitRate c R n)).exp
  convert hexp.mul hψ using 1
  ring

/-- **Every branching costs a factor `R t`.** For a moment family obeying the moment equation of a
branching mechanism with `‖G g‖ ≤ k R ‖g‖`, with `|m_t(f)| ≤ K ‖f‖` and zero initial moments,
`|m_t(f)| ≤ K ‖f‖ C(j + n, n) (R t)^j` at every time `t ≥ 0` and for every `j`. -/
theorem abs_moment_le_choose_mul_pow_branching [Fintype H] [DecidableEq H] {c : ℝ} (hc : 0 ≤ c)
    {R : ℝ} (hR : 0 ≤ R) (G : (k : ℕ) → ((Fin k → H) → ℝ) →ₗ[ℝ] ((Fin (k + 1) → H) → ℝ))
    (hGnorm : ∀ k (g : (Fin k → H) → ℝ), ‖G k g‖ ≤ (k * R) * ‖g‖)
    (m : ℝ → (k : ℕ) → ((Fin k → H) → ℝ) →ₗ[ℝ] ℝ) {K : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ s k (g : (Fin k → H) → ℝ), |m s k g| ≤ K * ‖g‖)
    (hm : ∀ s k (g : (Fin k → H) → ℝ),
      HasDerivAt (fun u ↦ m u k g) (branchingMomentGenerator c R G (m s) k g) s)
    (h0 : ∀ k (g : (Fin k → H) → ℝ), m 0 k g = 0) (j : ℕ) :
    ∀ (k : ℕ) (g : (Fin k → H) → ℝ) {s : ℝ}, 0 ≤ s →
      |m s k g| ≤ K * ‖g‖ * (((j + k).choose k : ℝ) * (R * s) ^ j) := by
  induction j with
  | zero =>
    intro k g s _
    simpa using hbound s k g
  | succ j ih =>
    intro k g t ht
    have hbnd : ∀ u ∈ Set.Ico (0 : ℝ) t,
        ‖Real.exp (-branchingExitRate c R k * (t - u)) *
          m u (k + 1) (G k (gainSemigroup c (t - u) g))‖ ≤
        K * ‖g‖ * ((j + 1 + k).choose k : ℝ) * R ^ (j + 1) * (((j + 1 : ℕ) : ℝ) * u ^ j) := by
      intro u hu
      obtain ⟨hu0, hut⟩ := hu
      have htu : 0 ≤ t - u := sub_nonneg.mpr hut.le
      have hexp_le : Real.exp (-branchingExitRate c R k * (t - u)) *
          Real.exp ((c * ∑ b : Fin k, ((Iio b).card : ℝ)) * (t - u)) ≤ 1 := by
        rw [← Real.exp_add, Real.exp_le_one_iff, branchingExitRate]
        nlinarith [mul_nonneg (mul_nonneg (Nat.cast_nonneg (α := ℝ) k) hR) htu]
      have hG' : ‖G k (gainSemigroup c (t - u) g)‖ ≤
          (k * R) * (‖g‖ * Real.exp ((c * ∑ b : Fin k, ((Iio b).card : ℝ)) * (t - u))) :=
        (hGnorm k _).trans
          (mul_le_mul_of_nonneg_left (norm_gainSemigroup_le hc htu g)
            (mul_nonneg (Nat.cast_nonneg _) hR))
      have hih := ih (k + 1) (G k (gainSemigroup c (t - u) g)) hu0
      have hchoose : (k : ℝ) * ((j + (k + 1)).choose (k + 1) : ℝ) ≤
          ((j + 1 + k).choose k : ℝ) * ((j + 1 : ℕ) : ℝ) := by
        have h := Nat.choose_succ_right_eq (j + 1 + k) k
        rw [show j + 1 + k - k = j + 1 by omega] at h
        rw [show j + (k + 1) = j + 1 + k by omega]
        have hcast : ((j + 1 + k).choose (k + 1) : ℝ) * ((k : ℝ) + 1) =
            ((j + 1 + k).choose k : ℝ) * ((j + 1 : ℕ) : ℝ) := by
          exact_mod_cast h
        nlinarith [Nat.cast_nonneg (α := ℝ) ((j + 1 + k).choose (k + 1))]
      have hC1 : 0 ≤ ((j + (k + 1)).choose (k + 1) : ℝ) * (R * u) ^ j :=
        mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (mul_nonneg hR hu0) j)
      have hX : 0 ≤ K * ‖g‖ * R ^ (j + 1) * u ^ j :=
        mul_nonneg (mul_nonneg (mul_nonneg hK (norm_nonneg g)) (pow_nonneg hR _))
          (pow_nonneg hu0 _)
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, Real.abs_exp]
      calc Real.exp (-branchingExitRate c R k * (t - u)) *
            |m u (k + 1) (G k (gainSemigroup c (t - u) g))|
          ≤ Real.exp (-branchingExitRate c R k * (t - u)) *
            (K * ((k * R) *
                (‖g‖ * Real.exp ((c * ∑ b : Fin k, ((Iio b).card : ℝ)) * (t - u)))) *
              (((j + (k + 1)).choose (k + 1) : ℝ) * (R * u) ^ j)) :=
            mul_le_mul_of_nonneg_left
              (hih.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hG' hK) hC1))
              (Real.exp_pos _).le
        _ = (K * ‖g‖ * R ^ (j + 1) * u ^ j) *
              ((k : ℝ) * ((j + (k + 1)).choose (k + 1) : ℝ)) *
              (Real.exp (-branchingExitRate c R k * (t - u)) *
                Real.exp ((c * ∑ b : Fin k, ((Iio b).card : ℝ)) * (t - u))) := by
            ring
        _ ≤ (K * ‖g‖ * R ^ (j + 1) * u ^ j) *
              ((k : ℝ) * ((j + (k + 1)).choose (k + 1) : ℝ)) * 1 :=
            mul_le_mul_of_nonneg_left hexp_le
              (mul_nonneg hX (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)))
        _ ≤ (K * ‖g‖ * R ^ (j + 1) * u ^ j) *
              (((j + 1 + k).choose k : ℝ) * ((j + 1 : ℕ) : ℝ)) := by
            rw [mul_one]
            exact mul_le_mul_of_nonneg_left hchoose hX
        _ = K * ‖g‖ * ((j + 1 + k).choose k : ℝ) * R ^ (j + 1) *
              (((j + 1 : ℕ) : ℝ) * u ^ j) := by
            ring
    have hmain := image_norm_le_of_norm_deriv_right_le_deriv_boundary
      (f := fun u ↦ Real.exp (-branchingExitRate c R k * (t - u)) *
        m u k (gainSemigroup c (t - u) g))
      (f' := fun u ↦ Real.exp (-branchingExitRate c R k * (t - u)) *
        m u (k + 1) (G k (gainSemigroup c (t - u) g)))
      (a := 0) (b := t)
      (B := fun u ↦ K * ‖g‖ * ((j + 1 + k).choose k : ℝ) * R ^ (j + 1) * u ^ (j + 1))
      (B' := fun u ↦ K * ‖g‖ * ((j + 1 + k).choose k : ℝ) * R ^ (j + 1) *
        (((j + 1 : ℕ) : ℝ) * u ^ j))
      (fun u _ ↦ (hasDerivAt_duhamel_branching c R G m hm t u g).continuousAt.continuousWithinAt)
      (fun u _ ↦ (hasDerivAt_duhamel_branching c R G m hm t u g).hasDerivWithinAt)
      (by simp [h0])
      (fun u ↦ by
        simpa using (hasDerivAt_pow (j + 1) u).const_mul
          (K * ‖g‖ * ((j + 1 + k).choose k : ℝ) * R ^ (j + 1)))
      hbnd (Set.right_mem_Icc.mpr ht)
    have hφt : Real.exp (-branchingExitRate c R k * (t - t)) *
        m t k (gainSemigroup c (t - t) g) = m t k g := by
      rw [sub_self, mul_zero, Real.exp_zero, one_mul, gainSemigroup_zero,
        ContinuousLinearMap.one_apply]
    have h : ‖Real.exp (-branchingExitRate c R k * (t - t)) *
        m t k (gainSemigroup c (t - t) g)‖ ≤
        K * ‖g‖ * ((j + 1 + k).choose k : ℝ) * R ^ (j + 1) * t ^ (j + 1) := hmain
    rw [hφt, Real.norm_eq_abs] at h
    calc |m t k g| ≤ K * ‖g‖ * ((j + 1 + k).choose k : ℝ) * R ^ (j + 1) * t ^ (j + 1) := h
      _ = K * ‖g‖ * (((j + 1 + k).choose k : ℝ) * (R * t) ^ (j + 1)) := by ring

/-- **A family starting at zero stays at zero** under a branching mechanism: first while `R t < 1`
by the branching bound, then at every `t ≥ 0` by shifting time in steps of `1/(R + 1)`. -/
theorem moment_eq_zero_branching [Fintype H] [DecidableEq H] {c : ℝ} (hc : 0 ≤ c) {R : ℝ}
    (hR : 0 ≤ R) (G : (k : ℕ) → ((Fin k → H) → ℝ) →ₗ[ℝ] ((Fin (k + 1) → H) → ℝ))
    (hGnorm : ∀ k (g : (Fin k → H) → ℝ), ‖G k g‖ ≤ (k * R) * ‖g‖)
    (m : ℝ → (k : ℕ) → ((Fin k → H) → ℝ) →ₗ[ℝ] ℝ) {K : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ s k (g : (Fin k → H) → ℝ), |m s k g| ≤ K * ‖g‖)
    (hm : ∀ s k (g : (Fin k → H) → ℝ),
      HasDerivAt (fun u ↦ m u k g) (branchingMomentGenerator c R G (m s) k g) s)
    (h0 : ∀ k (g : (Fin k → H) → ℝ), m 0 k g = 0) {t : ℝ} (ht : 0 ≤ t) (k : ℕ)
    (g : (Fin k → H) → ℝ) : m t k g = 0 := by
  have hshort : ∀ (m : ℝ → (k : ℕ) → ((Fin k → H) → ℝ) →ₗ[ℝ] ℝ),
      (∀ s k (g : (Fin k → H) → ℝ), |m s k g| ≤ K * ‖g‖) →
      (∀ s k (g : (Fin k → H) → ℝ),
        HasDerivAt (fun u ↦ m u k g) (branchingMomentGenerator c R G (m s) k g) s) →
      (∀ k (g : (Fin k → H) → ℝ), m 0 k g = 0) →
      ∀ s, 0 ≤ s → R * s < 1 → ∀ k (g : (Fin k → H) → ℝ), m s k g = 0 := by
    intro m hbound hm h0 s hs hRs k g
    have hx0 : 0 ≤ R * s := mul_nonneg hR hs
    have hsum := summable_choose_mul_geometric_of_norm_lt_one k (r := R * s)
      (by rwa [Real.norm_of_nonneg hx0])
    have htends : Tendsto (fun j : ℕ ↦ K * ‖g‖ * (((j + k).choose k : ℝ) * (R * s) ^ j))
        atTop (𝓝 0) := by
      have h := hsum.tendsto_cofinite_zero
      rw [Nat.cofinite_eq_atTop] at h
      simpa using h.const_mul (K * ‖g‖)
    have hle : |m s k g| ≤ 0 := ge_of_tendsto' htends fun j ↦
      abs_moment_le_choose_mul_pow_branching hc hR G hGnorm m hK hbound hm h0 j k g hs
    exact abs_nonpos_iff.mp hle
  have hτ0 : 0 < 1 / (R + 1) := one_div_pos.mpr (by linarith)
  have hRτ : R * (1 / (R + 1)) < 1 := by
    rw [mul_one_div, div_lt_one (by linarith)]
    linarith
  have hshift : ∀ j : ℕ, ∀ s : ℝ, 0 ≤ s → s ≤ j * (1 / (R + 1)) →
      ∀ (k : ℕ) (g : (Fin k → H) → ℝ), m s k g = 0 := by
    intro j
    induction j with
    | zero =>
      intro s hs0 hs k g
      have hs' : s = 0 := le_antisymm (by simpa using hs) hs0
      rw [hs']
      exact h0 k g
    | succ j ih =>
      intro s hs0 hs k g
      by_cases hsj : s ≤ j * (1 / (R + 1))
      · exact ih s hs0 hsj k g
      · push_neg at hsj
        have hj0 : 0 ≤ (j : ℝ) * (1 / (R + 1)) := mul_nonneg (Nat.cast_nonneg j) hτ0.le
        have hmshift : ∀ (u : ℝ) (k : ℕ) (g : (Fin k → H) → ℝ),
            HasDerivAt (fun v ↦ m (j * (1 / (R + 1)) + v) k g)
              (branchingMomentGenerator c R G (m (j * (1 / (R + 1)) + u)) k g) u :=
          fun u k g ↦ by
            have h := HasDerivAt.comp (hh₂ := hm (j * (1 / (R + 1)) + u) k g)
              (hh := (hasDerivAt_id (x := u)).const_add ((j : ℝ) * (1 / (R + 1))))
            simpa using h
        have hzero := hshort (fun u ↦ m (j * (1 / (R + 1)) + u)) (fun u k g ↦ hbound _ k g)
          hmshift (fun k g ↦ by simpa using ih _ hj0 le_rfl k g) (s - j * (1 / (R + 1)))
          (sub_nonneg.mpr hsj.le)
          (by
            push_cast at hs
            calc R * (s - j * (1 / (R + 1))) ≤ R * (1 / (R + 1)) :=
                  mul_le_mul_of_nonneg_left (by linarith) hR
              _ < 1 := hRτ)
          k g
        simpa using hzero
  obtain ⟨j, hj⟩ := exists_nat_ge (t / (1 / (R + 1)))
  exact hshift j t ht (by rwa [div_le_iff₀ hτ0] at hj) k g

/-- **The moment form of (7.5) for a branching mechanism.** Two families of moment functionals on
observations of every arity, bounded by the sup norm and obeying the moment equation of a branching
mechanism with `‖G g‖ ≤ k R ‖g‖`, that agree at time zero agree at every time `t ≥ 0`. -/
theorem moments_eq_of_branchingEquation [Fintype H] [DecidableEq H] {c : ℝ} (hc : 0 ≤ c) {R : ℝ}
    (hR : 0 ≤ R) (G : (k : ℕ) → ((Fin k → H) → ℝ) →ₗ[ℝ] ((Fin (k + 1) → H) → ℝ))
    (hGnorm : ∀ k (g : (Fin k → H) → ℝ), ‖G k g‖ ≤ (k * R) * ‖g‖)
    (m m' : ℝ → (k : ℕ) → ((Fin k → H) → ℝ) →ₗ[ℝ] ℝ)
    (hbound : ∀ s k (g : (Fin k → H) → ℝ), |m s k g| ≤ ‖g‖)
    (hbound' : ∀ s k (g : (Fin k → H) → ℝ), |m' s k g| ≤ ‖g‖)
    (hm : ∀ s k (g : (Fin k → H) → ℝ),
      HasDerivAt (fun u ↦ m u k g) (branchingMomentGenerator c R G (m s) k g) s)
    (hm' : ∀ s k (g : (Fin k → H) → ℝ),
      HasDerivAt (fun u ↦ m' u k g) (branchingMomentGenerator c R G (m' s) k g) s)
    (h0 : ∀ k (g : (Fin k → H) → ℝ), m 0 k g = m' 0 k g) {t : ℝ} (ht : 0 ≤ t) (k : ℕ)
    (g : (Fin k → H) → ℝ) : m t k g = m' t k g := by
  have hdiff := moment_eq_zero_branching hc hR G hGnorm (fun s k ↦ m s k - m' s k) (K := 2)
    (by norm_num)
    (fun s k g ↦ by
      show |m s k g - m' s k g| ≤ 2 * ‖g‖
      have h1 := abs_le.mp (hbound s k g)
      have h2 := abs_le.mp (hbound' s k g)
      exact abs_le.mpr ⟨by linarith [h1.1, h2.2], by linarith [h1.2, h2.1]⟩)
    (fun s k g ↦ by
      have h := (hm s k g).sub (hm' s k g)
      rw [← branchingMomentGenerator_sub] at h
      exact h)
    (fun k g ↦ by
      show m 0 k g - m' 0 k g = 0
      rw [h0, sub_self])
    ht k g
  exact sub_eq_zero.mp hdiff

/-! ### Kernel events are a branching mechanism -/

/-- **The kernel branching gain** `G f = ∑_e r_e ∑_a B_{a,K_e} f`, raising the arity by one. -/
def kernelBranchingGain [Fintype H] {E : Type*} [Fintype E] (r : E → ℝ)
    (K : E → H → H → H → ℝ) : ((Fin n → H) → ℝ) →ₗ[ℝ] ((Fin (n + 1) → H) → ℝ) where
  toFun f := ∑ e, r e • ∑ a, kernelBranch (K e) a f
  map_add' f g := by
    have hadd : ∀ (e : E) (a : Fin n), kernelBranch (K e) a (f + g) =
        kernelBranch (K e) a f + kernelBranch (K e) a g := fun e a ↦ by
      funext u
      simp only [kernelBranch, Pi.add_apply, mul_add, sum_add_distrib]
    simp only [hadd, sum_add_distrib, smul_add]
  map_smul' d f := by
    have hsmul : ∀ (e : E) (a : Fin n), kernelBranch (K e) a (d • f) =
        d • kernelBranch (K e) a f := fun e a ↦ by
      funext u
      simp only [kernelBranch, Pi.smul_apply, smul_eq_mul, mul_sum]
      exact sum_congr rfl fun z _ ↦ by ring
    have hcomm : ∀ (e : E) (x : (Fin (n + 1) → H) → ℝ), r e • d • x = d • r e • x :=
      fun _ _ ↦ smul_comm _ _ _
    simp only [hsmul, ← smul_sum, hcomm, RingHom.id_apply]

/-- **A probability kernel does not raise the sup norm.** -/
theorem norm_kernelBranch_le [Fintype H] {K : H → H → H → ℝ} (hK0 : ∀ x y z, 0 ≤ K x y z)
    (hK1 : ∀ x y, ∑ z, K x y z = 1) (a : Fin n) (f : (Fin n → H) → ℝ) :
    ‖kernelBranch K a f‖ ≤ ‖f‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg f)).mpr fun u ↦ ?_
  calc ‖kernelBranch K a f u‖
      ≤ ∑ z, ‖K (u a.castSucc) (u (Fin.last n)) z * f (Function.update (Fin.init u) a z)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ z, K (u a.castSucc) (u (Fin.last n)) z * ‖f‖ := by
        refine sum_le_sum fun z _ ↦ ?_
        rw [norm_mul, Real.norm_of_nonneg (hK0 _ _ _)]
        exact mul_le_mul_of_nonneg_left (norm_le_pi_norm f _) (hK0 _ _ _)
    _ = ‖f‖ := by rw [← sum_mul, hK1, one_mul]

/-- **The kernel branching gain costs at most `n R`**, `R = ∑_e r_e`, for probability kernels. -/
theorem norm_kernelBranchingGain_le [Fintype H] {E : Type*} [Fintype E] {r : E → ℝ}
    (hr : ∀ e, 0 ≤ r e) {K : E → H → H → H → ℝ} (hK0 : ∀ e x y z, 0 ≤ K e x y z)
    (hK1 : ∀ e x y, ∑ z, K e x y z = 1) (f : (Fin n → H) → ℝ) :
    ‖kernelBranchingGain r K f‖ ≤ (n * ∑ e, r e) * ‖f‖ := by
  show ‖∑ e, r e • ∑ a, kernelBranch (K e) a f‖ ≤ _
  refine (norm_sum_le _ _).trans ?_
  calc ∑ e, ‖r e • ∑ a, kernelBranch (K e) a f‖ ≤ ∑ e, r e * (n * ‖f‖) := by
        refine sum_le_sum fun e _ ↦ ?_
        rw [norm_smul, Real.norm_of_nonneg (hr e)]
        refine mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans ?_) (hr e)
        exact (sum_le_sum fun a _ ↦ norm_kernelBranch_le (hK0 e) (hK1 e) a f).trans_eq
          (by rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul])
    _ = (n * ∑ e, r e) * ‖f‖ := by
        rw [← sum_mul]
        ring

/-- **The moment generator with kernel events.** Coalescence of every pair `a < b` at rate `c`, and
kernel branching of every argument by every event `e` at rate `r e`, read through `m`. -/
def kernelMomentGenerator [Fintype H] {E : Type*} [Fintype E] (c : ℝ) (r : E → ℝ)
    (K : E → H → H → H → ℝ) (m : (k : ℕ) → ((Fin k → H) → ℝ) →ₗ[ℝ] ℝ) (n : ℕ)
    (f : (Fin n → H) → ℝ) : ℝ :=
  c * ∑ b, ∑ a ∈ Iio b, (m n (coalesceArguments a b f) - m n f) +
    ∑ e, r e * ∑ a, (m (n + 1) (kernelBranch (K e) a f) - m n f)

/-- **Kernel events are a branching mechanism**, with branching gain `kernelBranchingGain r K`. -/
theorem kernelMomentGenerator_eq [Fintype H] {E : Type*} [Fintype E] (c : ℝ) (r : E → ℝ)
    (K : E → H → H → H → ℝ) (m : (k : ℕ) → ((Fin k → H) → ℝ) →ₗ[ℝ] ℝ) (n : ℕ)
    (f : (Fin n → H) → ℝ) :
    kernelMomentGenerator c r K m n f =
      branchingMomentGenerator c (∑ e, r e) (fun j ↦ kernelBranchingGain r K) m n f := by
  have hgain : m n (coalescenceGain c f) =
      c * ∑ b, ∑ a ∈ Iio b, m n (coalesceArguments a b f) := by
    show m n (c • ∑ b, ∑ a ∈ Iio b, coalesceArguments a b f) = _
    simp only [map_smul, map_sum, smul_eq_mul]
  have hbranch : m (n + 1) (kernelBranchingGain r K f) =
      ∑ e, r e * ∑ a, m (n + 1) (kernelBranch (K e) a f) := by
    show m (n + 1) (∑ e, r e • ∑ a, kernelBranch (K e) a f) = _
    simp only [map_smul, map_sum, smul_eq_mul]
  have hcoal : ∑ b : Fin n, ∑ a ∈ Iio b, (m n (coalesceArguments a b f) - m n f) =
      ∑ b, ∑ a ∈ Iio b, m n (coalesceArguments a b f) -
        (∑ b : Fin n, ((Iio b).card : ℝ)) * m n f := by
    rw [sum_mul, ← sum_sub_distrib]
    refine sum_congr rfl fun b _ ↦ ?_
    rw [sum_sub_distrib, sum_const, nsmul_eq_mul]
  have hdec : ∑ e, r e * ∑ a : Fin n, (m (n + 1) (kernelBranch (K e) a f) - m n f) =
      ∑ e, r e * ∑ a, m (n + 1) (kernelBranch (K e) a f) - (∑ e, r e) * (n * m n f) := by
    rw [sum_mul, ← sum_sub_distrib]
    refine sum_congr rfl fun e _ ↦ ?_
    rw [sum_sub_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  rw [kernelMomentGenerator, branchingMomentGenerator, hgain, hbranch, hcoal, hdec,
    branchingExitRate]
  ring

/-- **The duality (7.5) with decisions and selection, in moment form.** For probability kernel
events at nonnegative rates (point-mass decisions, selection kernels, or both), two sup-norm-bounded
moment families obeying the moment equation of the kernel circuit that agree at time zero agree at
every time `t ≥ 0`. -/
theorem moments_eq_of_kernelMomentEquation [Fintype H] [DecidableEq H] {E : Type*} [Fintype E]
    {c : ℝ} (hc : 0 ≤ c) {r : E → ℝ} (hr : ∀ e, 0 ≤ r e) {K : E → H → H → H → ℝ}
    (hK0 : ∀ e x y z, 0 ≤ K e x y z) (hK1 : ∀ e x y, ∑ z, K e x y z = 1)
    (m m' : ℝ → (k : ℕ) → ((Fin k → H) → ℝ) →ₗ[ℝ] ℝ)
    (hbound : ∀ s k (g : (Fin k → H) → ℝ), |m s k g| ≤ ‖g‖)
    (hbound' : ∀ s k (g : (Fin k → H) → ℝ), |m' s k g| ≤ ‖g‖)
    (hm : ∀ s k (g : (Fin k → H) → ℝ),
      HasDerivAt (fun u ↦ m u k g) (kernelMomentGenerator c r K (m s) k g) s)
    (hm' : ∀ s k (g : (Fin k → H) → ℝ),
      HasDerivAt (fun u ↦ m' u k g) (kernelMomentGenerator c r K (m' s) k g) s)
    (h0 : ∀ k (g : (Fin k → H) → ℝ), m 0 k g = m' 0 k g) {t : ℝ} (ht : 0 ≤ t) (k : ℕ)
    (g : (Fin k → H) → ℝ) : m t k g = m' t k g :=
  moments_eq_of_branchingEquation hc (sum_nonneg fun e _ ↦ hr e) (fun j ↦ kernelBranchingGain r K)
    (fun j g ↦ norm_kernelBranchingGain_le hr hK0 hK1 g) m m' hbound hbound'
    (fun s k g ↦ by simpa only [kernelMomentGenerator_eq] using hm s k g)
    (fun s k g ↦ by simpa only [kernelMomentGenerator_eq] using hm' s k g) h0 ht k g

/-! ### Locality under selection -/

variable {V : Type*}

/-- **A fitness read at a set of coordinates**: two genomes that agree on `S` have one fitness. -/
def FitnessDetermined (s : (V → Bool) → ℝ) (S : Finset V) : Prop :=
  ∀ x x' : V → Bool, (∀ v ∈ S, x v = x' v) → s x = s x'

/-- **A fitness of the alleles at `S` is read at `S`**: the witness of `FitnessDetermined`. -/
theorem fitnessDetermined_restrict (S : Finset V) (g : (S → Bool) → ℝ) :
    FitnessDetermined (fun x : V → Bool ↦ g fun v ↦ x v) S := by
  intro x x' hx
  exact congrArg g (funext fun v ↦ hx v.1 v.2)

/-- **Selection tags.** A selective branching on argument `a` keeps every old tag, and the new
parent needs `A_a ∪ S` when argument `a` is read at all, and nothing otherwise. -/
def selectionTags [DecidableEq V] (S : Finset V) (a : Fin n) (A : Fin n → Finset V) :
    Fin (n + 1) → Finset V :=
  Fin.snoc A (if (A a).Nonempty then A a ∪ S else ∅)

/-- The selection tag of an old argument is its old tag. -/
theorem selectionTags_castSucc [DecidableEq V] (S : Finset V) (a c : Fin n)
    (A : Fin n → Finset V) : selectionTags S a A c.castSucc = A c := by
  simp only [selectionTags, Fin.snoc_castSucc]

/-- The selection tag of the new parent. -/
theorem selectionTags_last [DecidableEq V] (S : Finset V) (a : Fin n) (A : Fin n → Finset V) :
    selectionTags S a A (Fin.last n) = if (A a).Nonempty then A a ∪ S else ∅ := by
  simp only [selectionTags, Fin.snoc_last]

/-- **A selective branching keeps the observable determined by its tags.** The new parent is read
at `A_a ∪ S` when argument `a` is read, and not at all when `A_a = ∅`.

Assumes: `FitnessDetermined s S` and `TagDetermined f A`. -/
theorem tagDetermined_selectionBranch [Fintype V] [DecidableEq V] {s : (V → Bool) → ℝ}
    {S : Finset V} (hs : FitnessDetermined s S) (σ : ℝ) (a : Fin n)
    {f : (Fin n → V → Bool) → ℝ} {A : Fin n → Finset V} (hf : TagDetermined f A) :
    TagDetermined (kernelBranch (selectionKernel s σ) a f) (selectionTags S a A) := by
  intro u u' hu
  rw [kernelBranch_selectionKernel, kernelBranch_selectionKernel]
  have hold : ∀ c v, v ∈ A c → u c.castSucc v = u' c.castSucc v := fun c v hv ↦
    hu c.castSucc v (by rw [selectionTags_castSucc]; exact hv)
  have hinit : f (Function.update (Fin.init u) a (u a.castSucc)) =
      f (Function.update (Fin.init u') a (u' a.castSucc)) :=
    hf _ _ fun c v hv ↦ by
      by_cases hca : c = a
      · rw [hca] at hv ⊢
        rw [Function.update_self, Function.update_self]
        exact hold a v hv
      · rw [Function.update_of_ne hca, Function.update_of_ne hca]
        exact hold c v hv
  by_cases hA : (A a).Nonempty
  · have hlast : ∀ v ∈ A a ∪ S, u (Fin.last n) v = u' (Fin.last n) v := fun v hv ↦
      hu (Fin.last n) v (by rw [selectionTags_last, if_pos hA]; exact hv)
    have hfit : s (u (Fin.last n)) = s (u' (Fin.last n)) :=
      hs _ _ fun v hv ↦ hlast v (mem_union_right _ hv)
    have hnew : f (Function.update (Fin.init u) a (u (Fin.last n))) =
        f (Function.update (Fin.init u') a (u' (Fin.last n))) :=
      hf _ _ fun c v hv ↦ by
        by_cases hca : c = a
        · rw [hca] at hv ⊢
          rw [Function.update_self, Function.update_self]
          exact hlast v (mem_union_left _ hv)
        · rw [Function.update_of_ne hca, Function.update_of_ne hca]
          exact hold c v hv
    rw [hfit, hnew, hinit]
  · have hempty : A a = ∅ := not_nonempty_iff_eq_empty.mp hA
    have hig : ∀ (w : Fin n → V → Bool) (h : V → Bool), f (Function.update w a h) = f w :=
      fun w h ↦ hf _ _ fun c v hv ↦ by
        by_cases hca : c = a
        · rw [hca, hempty] at hv
          exact absurd hv (by simp)
        · rw [Function.update_of_ne hca]
    have heq : f (Fin.init u) = f (Fin.init u') := hf _ _ fun c v hv ↦ hold c v hv
    rw [hig, hig, hig, hig, heq]
    ring

/-- **A selective branching raises a nonnegative tag weight by at most `w(A_a) + w(S)`.** -/
theorem tagWeight_selectionTags_le [DecidableEq V] {w : V → ℝ} (hw : ∀ v, 0 ≤ w v)
    (S : Finset V) (a : Fin n) (A : Fin n → Finset V) :
    tagWeight w (selectionTags S a A) ≤ tagWeight w A + (∑ v ∈ A a, w v + ∑ v ∈ S, w v) := by
  have hlast : ∑ v ∈ (if (A a).Nonempty then A a ∪ S else ∅), w v ≤
      ∑ v ∈ A a, w v + ∑ v ∈ S, w v := by
    split_ifs
    · have hunion := sum_union_inter (s₁ := A a) (s₂ := S) (f := w)
      have hinter : 0 ≤ ∑ v ∈ A a ∩ S, w v := sum_nonneg fun v _ ↦ hw v
      linarith
    · rw [sum_empty]
      exact add_nonneg (sum_nonneg fun v _ ↦ hw v) (sum_nonneg fun v _ ↦ hw v)
  rw [tagWeight, Fin.sum_univ_castSucc]
  simp only [selectionTags_castSucc, selectionTags_last]
  exact add_le_add_left hlast _

/-- **A selective branching adds at most `|A_a| + |S|` coordinate occurrences.** -/
theorem tagCount_selectionTags_le [DecidableEq V] (S : Finset V) (a : Fin n)
    (A : Fin n → Finset V) :
    tagCount (selectionTags S a A) ≤ tagCount A + ((A a).card + S.card) := by
  have h := tagWeight_selectionTags_le (w := fun _ ↦ (1 : ℝ)) (fun _ ↦ zero_le_one) S a A
  simp only [tagWeight_one, sum_const, nsmul_eq_mul, mul_one] at h
  exact_mod_cast h

/-- **The selective increments at rate `σ` total at most `σ (1 + w(S)) Z^{(w)}`.** Each argument
with a nonempty tag meets a selective branching at rate `σ` and gains at most `w(A_a) + w(S)`. For
weights at least one on every coordinate, as light-cone weights are, the number of nonempty tags is
at most the weight. -/
theorem selectionWeightRate_le {w : V → ℝ} (hw1 : ∀ v, 1 ≤ w v) {σ : ℝ} (hσ : 0 ≤ σ)
    (S : Finset V) (A : Fin n → Finset V) :
    σ * ∑ a ∈ univ.filter (fun a ↦ (A a).Nonempty), (∑ v ∈ A a, w v + ∑ v ∈ S, w v) ≤
      σ * (1 + ∑ v ∈ S, w v) * tagWeight w A := by
  have hw0 : ∀ v, 0 ≤ w v := fun v ↦ zero_le_one.trans (hw1 v)
  have hsub : ∑ a ∈ univ.filter (fun a ↦ (A a).Nonempty), ∑ v ∈ A a, w v ≤ tagWeight w A :=
    sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun a _ _ ↦ sum_nonneg fun v _ ↦ hw0 v
  have hcount : ((univ.filter fun a ↦ (A a).Nonempty).card : ℝ) ≤ tagWeight w A := by
    calc ((univ.filter fun a ↦ (A a).Nonempty).card : ℝ)
        = ∑ a ∈ univ.filter (fun a ↦ (A a).Nonempty), (1 : ℝ) := by
          rw [sum_const, nsmul_eq_mul, mul_one]
      _ ≤ ∑ a ∈ univ.filter (fun a ↦ (A a).Nonempty), ∑ v ∈ A a, w v := by
          refine sum_le_sum fun a ha ↦ ?_
          obtain ⟨v, hv⟩ := (mem_filter.mp ha).2
          calc (1 : ℝ) ≤ w v := hw1 v
            _ ≤ ∑ v ∈ A a, w v := single_le_sum (fun v _ ↦ hw0 v) hv
      _ ≤ tagWeight w A := hsub
  have hS : 0 ≤ ∑ v ∈ S, w v := sum_nonneg fun v _ ↦ hw0 v
  rw [sum_add_distrib, sum_const, nsmul_eq_mul]
  nlinarith [mul_le_mul_of_nonneg_left hcount hS]

/-- **The support drift under decisions and selection is at most `(3D + σ (1 + |S|)) Z`.** Decisions
at every target of a tag, with outgoing rates summing to at most `D`, add at most three occurrences
each; selective branchings at rate `σ` add at most `|A_a| + |S|`. This is Theorem 7's constant `3D`
with selection added. -/
theorem supportDrift_le [Fintype V] {r : V → V → ℝ} {D σ : ℝ} (hD : ∀ i, ∑ j, r i j ≤ D)
    (hσ : 0 ≤ σ) (S : Finset V) (A : Fin n → Finset V) :
    3 * decisionRate r A +
        σ * ∑ a ∈ univ.filter (fun a ↦ (A a).Nonempty), (((A a).card : ℝ) + S.card) ≤
      (3 * D + σ * (1 + S.card)) * tagCount A := by
  have h1 := decisionRate_le hD A
  have h2 := selectionWeightRate_le (w := fun _ ↦ (1 : ℝ)) (fun _ ↦ le_rfl) hσ S A
  simp only [tagWeight_one, sum_const, nsmul_eq_mul, mul_one] at h2
  linarith

end Descent.Pangenome.AncestralLocality
