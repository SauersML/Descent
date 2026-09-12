/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Layer
import Descent.Pangenome.AncestralLocality.CompatibilityNeutrality
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Data.Setoid.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

assert_below Descent.PopGen Descent.Spectral Descent.Blindness Descent.Conditionals
assert_below Descent.Portability Descent.Decision Descent.Program

/-!
# Heredity kernels, observations and hereditary autonomy

The finite object of `ANCESTRAL_LOCALITY.md` §2. A finite set `H` of genome states carries a
two-parent inheritance kernel `K : H → H → H → ℝ`: `K x y z` is the probability that the child
of parents `x` and `y` is in state `z`. `IsHeredityKernel K` says that every row is a
probability vector and that the kernel does not see the order of the parents. The mass
`kernelMass K x y B` of a finite set `B` is the note's `K(x,y;B)`. The reproduction operator
`reproduce K p`, `R_K(p)(z) = Σ_{x,y} p_x p_y K(x,y;z)` of (2.1), and the pushforward
`pushforward π p` along an observation are the ones `CompatibilityNeutrality` declares;
`reproduce_mem_stdSimplex` shows that `R_K` maps `stdSimplex ℝ H` to itself.

An observation is a map `π : H → O`. Its fibers `fiber π o` are the blocks of the partition
`P_π`, which is Mathlib's `Setoid.ker π` (`block_ker`), and `pushforward_eq_sum_fiber` reads the
pushforward as a sum over fibers. The observation is hereditarily autonomous, (2.2), when some
`K̄` on `O` reproduces every fiber mass from the observed parents:
`HereditarilyAutonomous K π` asks for `K(x,y;π⁻¹(o)) = K̄(πx,πy;o)` at all parental states. The
same property for a setoid is `IsAutonomous K P`: the mass `blockMass K P x y w` of every block
is unchanged when either parent is replaced by a `P`-equivalent state.
`hereditarilyAutonomous_iff` identifies the two for `P = Setoid.ker π`, and
`isHeredityKernel_of_kernelMass_fiber_eq` shows that for a surjective observation every such
`K̄` is itself a heredity kernel. The identity observation is autonomous for every kernel
(`hereditarilyAutonomous_id`).

The two-child kernels `childKernel T`, half the mass on `T x y` and half on `T y x`, have the
shape (4.2) of the note's exchange kernels; `isHeredityKernel_childKernel` shows that every one
is a heredity kernel, and `childKernel (fun x _ ↦ x)` is unbiased parental copying.

For the operational reading of autonomy the module carries the point masses `pointMass x` and
the two-point mixtures `pairMidpoint x y`, with their observed images (`pushforward_pointMass`,
`pushforward_pairMidpoint`). `pushforward_reproduce` says that the observed next generation is
the `p ⊗ p` average of the fiber masses, and `sum_sum_mul_comp_eq_sum_sum_pushforward` that an
average of a function of the observed parents depends on `p` only through `π_# p`.

Scope. States form a `Fintype` and probabilities are real numbers. The annotated kernels of
§2.2, which carry correspondence witnesses for physical ancestry, are not modelled: everything
here is prediction from `K`. The note asks `π` to be a surjection; `HereditarilyAutonomous` does
not, and surjectivity is assumed only where `K̄` is shown to be a kernel.

## Empirical status

None. The bodies here are finite sums of supplied real numbers and equivalence relations on a
finite set; no measurement can bear on them.
-/

namespace Descent.Pangenome.AncestralLocality

noncomputable section

variable {H : Type*} [Fintype H]

/-! ### Kernels and reproduction -/

/-- A **heredity kernel**, the note's symmetric two-parent inheritance kernel
`K : H × H → P(H)`: every row `K x y` is a probability vector on `H`, and the order of the two
parents does not matter. -/
structure IsHeredityKernel (K : H → H → H → ℝ) : Prop where
  /-- Probabilities are nonnegative. -/
  nonneg : ∀ x y z, 0 ≤ K x y z
  /-- Each row is a probability vector. -/
  sum_eq_one : ∀ x y, ∑ z, K x y z = 1
  /-- The kernel is symmetric in the two parents. -/
  symm : ∀ x y z, K x y z = K y x z

/-- `K(x,y;B)`, the probability that the child of `x` and `y` lands in `B`. -/
def kernelMass (K : H → H → H → ℝ) (x y : H) (B : Finset H) : ℝ :=
  ∑ z ∈ B, K x y z

/-- The mass of a finite set does not see the order of the parents.
Assumes: `IsHeredityKernel K`. -/
theorem kernelMass_symm {K : H → H → H → ℝ} (hK : IsHeredityKernel K) (x y : H)
    (B : Finset H) : kernelMass K x y B = kernelMass K y x B :=
  Finset.sum_congr rfl fun z _ ↦ hK.symm x y z

/-- The reproduction operator maps probability vectors to probability vectors.
Assumes: `IsHeredityKernel K`. -/
theorem reproduce_mem_stdSimplex {K : H → H → H → ℝ} (hK : IsHeredityKernel K) {p : H → ℝ}
    (hp : p ∈ stdSimplex ℝ H) : reproduce K p ∈ stdSimplex ℝ H := by
  refine ⟨fun z ↦ Finset.sum_nonneg fun x _ ↦ Finset.sum_nonneg fun y _ ↦
    mul_nonneg (mul_nonneg (hp.1 x) (hp.1 y)) (hK.nonneg x y z), ?_⟩
  calc ∑ z, reproduce K p z = ∑ x, ∑ y, p x * p y * ∑ z, K x y z := by
        simp only [reproduce, Finset.mul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun x _ ↦ Finset.sum_comm
    _ = (∑ x, p x) * ∑ y, p y := by
        simp only [hK.sum_eq_one, mul_one, Finset.sum_mul_sum]
    _ = 1 := by rw [hp.2, one_mul]

/-! ### Observations, blocks and autonomy -/

/-- The fiber `π⁻¹(o)` of an observation, as a finite set of states. -/
def fiber {O : Type*} [DecidableEq O] (π : H → O) (o : O) : Finset H :=
  Finset.univ.filter fun z ↦ π z = o

theorem mem_fiber_iff {O : Type*} [DecidableEq O] (π : H → O) (o : O) (z : H) :
    z ∈ fiber π o ↔ π z = o := by
  simp [fiber]

/-- The pushforward of `CompatibilityNeutrality` sums a vector over the fibers of the
observation. -/
theorem pushforward_eq_sum_fiber {O : Type*} [DecidableEq O] (π : H → O) (p : H → ℝ) (o : O) :
    pushforward π p o = ∑ z ∈ fiber π o, p z :=
  rfl

open Classical in
/-- The block `{z | P z w}` of the state `w` in a partition `P`, as a finite set of states. -/
def block (P : Setoid H) (w : H) : Finset H :=
  Finset.univ.filter fun z ↦ P z w

theorem mem_block_iff (P : Setoid H) (w z : H) : z ∈ block P w ↔ P z w := by
  simp [block]

/-- The blocks of the kernel partition `P_π` of an observation are its fibers. -/
theorem block_ker {O : Type*} [DecidableEq O] (π : H → O) (w : H) :
    block (Setoid.ker π) w = fiber π (π w) := by
  ext z
  rw [mem_block_iff, mem_fiber_iff, Setoid.ker_def]

/-- `K(x,y;B)` for the block `B` of the state `w` in a partition `P`. -/
def blockMass (K : H → H → H → ℝ) (P : Setoid H) (x y w : H) : ℝ :=
  kernelMass K x y (block P w)

/-- Block masses do not see the order of the parents. Assumes: `IsHeredityKernel K`. -/
theorem blockMass_symm {K : H → H → H → ℝ} (hK : IsHeredityKernel K) (P : Setoid H)
    (x y w : H) : blockMass K P x y w = blockMass K P y x w :=
  kernelMass_symm hK x y (block P w)

/-- **Hereditary autonomy** (2.2): some `K̄` on observed values reproduces the mass of every
fiber from the observed values of the parents, `K(x,y;π⁻¹(o)) = K̄(πx,πy;o)`. -/
def HereditarilyAutonomous {O : Type*} [DecidableEq O] (K : H → H → H → ℝ) (π : H → O) :
    Prop :=
  ∃ Kbar : O → O → O → ℝ, ∀ x y o, kernelMass K x y (fiber π o) = Kbar (π x) (π y) o

/-- **Autonomy of a partition.** The mass of every block of `P` is unchanged when the parents
are replaced by `P`-equivalent states. -/
def IsAutonomous (K : H → H → H → ℝ) (P : Setoid H) : Prop :=
  ∀ ⦃x x' y y' : H⦄, P x x' → P y y' → ∀ w, blockMass K P x y w = blockMass K P x' y' w

/-- The identity observation is hereditarily autonomous for every kernel, with `K̄ = K`. -/
theorem hereditarilyAutonomous_id [DecidableEq H] (K : H → H → H → ℝ) :
    HereditarilyAutonomous K (id : H → H) :=
  ⟨K, fun _ _ o ↦ Finset.sum_eq_single_of_mem o ((mem_fiber_iff id o o).mpr rfl)
    fun z hz hzo ↦ absurd ((mem_fiber_iff id o z).mp hz) hzo⟩

/-- Under autonomy of `P_π`, the mass of a fiber depends on the parents only through their
observed values. Assumes: `IsAutonomous K (Setoid.ker π)`. -/
theorem kernelMass_fiber_congr {O : Type*} [DecidableEq O] {K : H → H → H → ℝ} {π : H → O}
    (hA : IsAutonomous K (Setoid.ker π)) {x x' y y' : H} (hx : π x = π x') (hy : π y = π y')
    (o : O) : kernelMass K x y (fiber π o) = kernelMass K x' y' (fiber π o) := by
  by_cases ho : ∃ w, π w = o
  · obtain ⟨w, rfl⟩ := ho
    rw [← block_ker π w]
    exact hA (Setoid.ker_def.mpr hx) (Setoid.ker_def.mpr hy) w
  · have hz : ∀ z ∈ fiber π o, K x y z = 0 ∧ K x' y' z = 0 := fun z hz ↦
      (ho ⟨z, (mem_fiber_iff π o z).mp hz⟩).elim
    rw [kernelMass, kernelMass, Finset.sum_eq_zero fun z hz' ↦ (hz z hz').1,
      Finset.sum_eq_zero fun z hz' ↦ (hz z hz').2]

/-- **Autonomy of an observation is autonomy of its partition.** A `K̄` as in (2.2) exists
exactly when block masses of `P_π = Setoid.ker π` are constant on pairs of blocks. -/
theorem hereditarilyAutonomous_iff {O : Type*} [DecidableEq O] (K : H → H → H → ℝ)
    (π : H → O) : HereditarilyAutonomous K π ↔ IsAutonomous K (Setoid.ker π) := by
  constructor
  · rintro ⟨Kbar, hKbar⟩ x x' y y' hx hy w
    simp only [blockMass, block_ker]
    rw [hKbar, hKbar, Setoid.ker_def.mp hx, Setoid.ker_def.mp hy]
  · intro hA
    refine ⟨fun a b o ↦ if h : (∃ x, π x = a) ∧ ∃ y, π y = b then
      kernelMass K h.1.choose h.2.choose (fiber π o) else 0, fun x y o ↦ ?_⟩
    have h : (∃ a, π a = π x) ∧ ∃ b, π b = π y := ⟨⟨x, rfl⟩, ⟨y, rfl⟩⟩
    simp only [dif_pos h]
    exact kernelMass_fiber_congr hA h.1.choose_spec.symm h.2.choose_spec.symm o

/-- **`K̄` is a kernel.** For a surjective observation of a heredity kernel, every `K̄`
satisfying (2.2) is a heredity kernel on the observed values. Assumes: `IsHeredityKernel K`. -/
theorem isHeredityKernel_of_kernelMass_fiber_eq {O : Type*} [Fintype O] [DecidableEq O]
    {K : H → H → H → ℝ} (hK : IsHeredityKernel K) {π : H → O} (hπ : Function.Surjective π)
    {Kbar : O → O → O → ℝ}
    (hKbar : ∀ x y o, kernelMass K x y (fiber π o) = Kbar (π x) (π y) o) :
    IsHeredityKernel Kbar where
  nonneg a b o := by
    obtain ⟨x, rfl⟩ := hπ a
    obtain ⟨y, rfl⟩ := hπ b
    rw [← hKbar]
    exact Finset.sum_nonneg fun z _ ↦ hK.nonneg x y z
  sum_eq_one a b := by
    obtain ⟨x, rfl⟩ := hπ a
    obtain ⟨y, rfl⟩ := hπ b
    simp only [← hKbar, kernelMass, fiber]
    rw [Finset.sum_fiberwise Finset.univ π (K x y), hK.sum_eq_one]
  symm a b o := by
    obtain ⟨x, rfl⟩ := hπ a
    obtain ⟨y, rfl⟩ := hπ b
    rw [← hKbar, ← hKbar, kernelMass_symm hK]

/-! ### Two-child kernels -/

/-- **Two-child kernels**, the shape (4.2) of the note: an ordered child map `T` puts half the
mass on `T x y` and half on `T y x`. -/
def childKernel [DecidableEq H] (T : H → H → H) (x y z : H) : ℝ :=
  (if T x y = z then 1 / 2 else 0) + if T y x = z then 1 / 2 else 0

omit [Fintype H] in
/-- The mass of a set under a two-child kernel counts the two ordered children in it. -/
theorem kernelMass_childKernel [DecidableEq H] (T : H → H → H) (x y : H) (B : Finset H) :
    kernelMass (childKernel T) x y B =
      (if T x y ∈ B then 1 / 2 else 0) + if T y x ∈ B then 1 / 2 else 0 := by
  simp only [kernelMass, childKernel, Finset.sum_add_distrib, Finset.sum_ite_eq]

/-- **Every two-child kernel is a heredity kernel.** -/
theorem isHeredityKernel_childKernel [DecidableEq H] (T : H → H → H) :
    IsHeredityKernel (childKernel T) where
  nonneg x y z := by
    unfold childKernel
    split_ifs <;> norm_num
  sum_eq_one x y := by
    have h := kernelMass_childKernel T x y Finset.univ
    simp only [kernelMass, Finset.mem_univ, ↓reduceIte] at h
    rw [h]
    norm_num
  symm x y z := add_comm _ _

/-! ### Pushforwards, point masses and the observed next generation -/

/-- **The observed next generation.** `π_# R_K(p)` is the `p ⊗ p` average of the fiber
masses. -/
theorem pushforward_reproduce {O : Type*} [DecidableEq O] (K : H → H → H → ℝ) (π : H → O)
    (p : H → ℝ) (o : O) :
    pushforward π (reproduce K p) o = ∑ x, ∑ y, p x * p y * kernelMass K x y (fiber π o) := by
  simp only [pushforward_eq_sum_fiber, reproduce, kernelMass, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun x _ ↦ Finset.sum_comm

/-- An average of a function of the observed state is an average against `π_# p`. -/
theorem sum_mul_comp_eq_sum_pushforward {O : Type*} [Fintype O] [DecidableEq O] (π : H → O)
    (p : H → ℝ) (f : O → ℝ) : ∑ x, p x * f (π x) = ∑ a, pushforward π p a * f a := by
  rw [← Finset.sum_fiberwise Finset.univ π]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [pushforward_eq_sum_fiber, Finset.sum_mul]
  exact Finset.sum_congr rfl fun x hx ↦ by rw [(mem_fiber_iff π a x).mp hx]

/-- **Averages over observed parents depend only on `π_# p`.** -/
theorem sum_sum_mul_comp_eq_sum_sum_pushforward {O : Type*} [Fintype O] [DecidableEq O]
    (π : H → O) (p : H → ℝ) (g : O → O → ℝ) :
    ∑ x, ∑ y, p x * p y * g (π x) (π y) =
      ∑ a, ∑ b, pushforward π p a * pushforward π p b * g a b := by
  have h : ∀ x, ∑ y, p x * p y * g (π x) (π y) =
      p x * ∑ b, pushforward π p b * g (π x) b := by
    intro x
    rw [← sum_mul_comp_eq_sum_pushforward π p (g (π x)), Finset.mul_sum]
    exact Finset.sum_congr rfl fun y _ ↦ mul_assoc _ _ _
  refine (Finset.sum_congr rfl fun x _ ↦ h x).trans ?_
  refine (sum_mul_comp_eq_sum_pushforward π p fun a ↦ ∑ b, pushforward π p b * g a b).trans ?_
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  simp only [Finset.mul_sum, mul_assoc]

section PointMass

variable [DecidableEq H]

/-- The point mass `δ_x`. -/
def pointMass (x z : H) : ℝ :=
  if x = z then 1 else 0

/-- The two-point mixture `½δ_x + ½δ_y`. -/
def pairMidpoint (x y z : H) : ℝ :=
  2⁻¹ * (pointMass x z + pointMass y z)

theorem pointMass_mem_stdSimplex (x : H) : pointMass x ∈ stdSimplex ℝ H :=
  ite_eq_mem_stdSimplex (𝕜 := ℝ) (ι := H) x

/-- Averaging against `δ_x` evaluates at `x`. -/
theorem sum_pointMass_mul (x : H) (f : H → ℝ) : ∑ a, pointMass x a * f a = f x := by
  simp only [pointMass, boole_mul, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]

/-- Averaging against `½δ_x + ½δ_y` is the mean of the two values. -/
theorem sum_pairMidpoint_mul (x y : H) (f : H → ℝ) :
    ∑ a, pairMidpoint x y a * f a = 2⁻¹ * (f x + f y) := by
  rw [← sum_pointMass_mul x f, ← sum_pointMass_mul y f, ← Finset.sum_add_distrib,
    Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ ↦ by simp only [pairMidpoint]; ring

theorem pairMidpoint_mem_stdSimplex (x y : H) : pairMidpoint x y ∈ stdSimplex ℝ H := by
  refine ⟨fun z ↦ ?_, ?_⟩
  · unfold pairMidpoint pointMass
    split_ifs <;> norm_num
  · have h := sum_pairMidpoint_mul x y fun _ ↦ 1
    simp only [mul_one] at h
    rw [h]
    norm_num

/-- `Σ_{a,b} δ_x(a) δ_x(b) g(a,b) = g(x,x)`. -/
theorem sum_sum_pointMass (x : H) (g : H → H → ℝ) :
    ∑ a, ∑ b, pointMass x a * pointMass x b * g a b = g x x := by
  have h : ∀ a, ∑ b, pointMass x a * pointMass x b * g a b = pointMass x a * g a x := by
    intro a
    simp only [mul_assoc]
    rw [← Finset.mul_sum, sum_pointMass_mul x (g a)]
  rw [Finset.sum_congr rfl fun a _ ↦ h a, sum_pointMass_mul x fun a ↦ g a x]

/-- **Polarization**: the `p ⊗ p` average for `p = ½δ_x + ½δ_y` is
`¼ g(x,x) + ¼ g(x,y) + ¼ g(y,x) + ¼ g(y,y)`. -/
theorem sum_sum_pairMidpoint (x y : H) (g : H → H → ℝ) :
    ∑ a, ∑ b, pairMidpoint x y a * pairMidpoint x y b * g a b =
      2⁻¹ * (2⁻¹ * (g x x + g x y) + 2⁻¹ * (g y x + g y y)) := by
  have h : ∀ a, ∑ b, pairMidpoint x y a * pairMidpoint x y b * g a b =
      pairMidpoint x y a * (2⁻¹ * (g a x + g a y)) := by
    intro a
    simp only [mul_assoc]
    rw [← Finset.mul_sum, sum_pairMidpoint_mul x y (g a)]
  rw [Finset.sum_congr rfl fun a _ ↦ h a,
    sum_pairMidpoint_mul x y fun a ↦ 2⁻¹ * (g a x + g a y)]

/-- The observed image of a point mass is the point mass of the observed state. -/
theorem pushforward_pointMass {O : Type*} [DecidableEq O] (π : H → O) (x : H) :
    pushforward π (pointMass x) = pointMass (π x) := by
  funext o
  simp only [pushforward_eq_sum_fiber, pointMass, Finset.sum_ite_eq, mem_fiber_iff]

/-- The observed image of `½δ_x + ½δ_y` is `½δ_{πx} + ½δ_{πy}`. -/
theorem pushforward_pairMidpoint {O : Type*} [DecidableEq O] (π : H → O) (x y : H) :
    pushforward π (pairMidpoint x y) = pairMidpoint (π x) (π y) := by
  funext o
  have hx := congrFun (pushforward_pointMass π x) o
  have hy := congrFun (pushforward_pointMass π y) o
  simp only [pushforward_eq_sum_fiber] at hx hy
  simp only [pushforward_eq_sum_fiber, pairMidpoint, ← Finset.mul_sum, Finset.sum_add_distrib,
    hx, hy]

end PointMass

end

end Descent.Pangenome.AncestralLocality
