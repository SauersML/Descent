/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.AncestralLocality.HereditaryClosure
import Descent.Pangenome.AncestralLocality.OperationalAutonomy
import Mathlib.Algebra.BigOperators.Field

assert_below Descent.PopGen Descent.Spectral Descent.Blindness Descent.Conditionals
assert_below Descent.Portability Descent.Decision Descent.Program

/-!
# Hereditary closure under selection

Research front F4 of `ANCESTRAL_LOCALITY.md`: fecundity selection `K_s(x,y;z) ∝ s(x) s(y) K(x,y;z)`
with a positive fitness `s`, and when hereditary autonomy and the closure of Theorem 1 survive it.

**Selection does not change the kernel.** Normalized per parental pair, `s(x) s(y) K(x,y;·)` is
`K(x,y;·)` (`selectedKernel_eq`), so autonomy (2.2) and `hereditaryClosure` are unchanged
(`hereditaryClosure_selectedKernel`). Selection acts on who reproduces: the selected next
generation `selectedReproduce K s p` is the reproduction of the size-biased population
`sizeBias s p = s·p/⟨s,p⟩` (`selectedReproduce_eq`), which is again a probability vector
(`sizeBias_mem_stdSimplex`).

**Operational autonomy under selection.** `SelectionAutonomous K s π` asks that the observed
selected next generation depend only on the observed law of the parents. When the fitness is a
function of the observation, size bias commutes with observing (`pushforward_sizeBias_of_factor`)
and can be undone (`sizeBias_sizeBias_inv`), so for a symmetric kernel selection-autonomy is
hereditary autonomy (`selectionAutonomous_iff_of_factor`): selection on an observed feature keeps
it autonomous, and cannot make a non-autonomous observation autonomous.

**The selection closure.** `selectionClosure K s P` is `hereditaryClosure K (P ⊓ Setoid.ker s)`,
the closure of the observation joined with fitness. It is the greatest autonomous partition below
`P` on whose blocks the fitness is constant (`isGreatest_selectionClosure`), its quotient map is
selection-autonomous (`selectionAutonomous_closureMap`), and it lies below
`hereditaryClosure K P ⊓ Setoid.ker s` (`selectionClosure_le_inf`). Selection leaves the closure
unchanged exactly when the fitness is constant on the blocks of the closure
(`selectionClosure_eq_hereditaryClosure_iff`).

**The candidate formula is false.** The closure under selection is not
`hereditaryClosure K P ⊓ Setoid.ker s`. For the gated exchange of §3.2 with fitness on feature `b`,
observing `a` gives a join `(a, b)` that is not autonomous, so the selection closure also pulls in
the checker and is strictly finer (`selectionClosure_ne_inf_gated`). Nor is fitness on a hidden
feature always pulled in. Under unbiased copying `halfMix` every observation is autonomous
(`hereditarilyAutonomous_halfMix`), and with at least two observed values selection-autonomy holds
exactly when the fitness factors through the observation (`selectionAutonomous_halfMix_iff`):
there, hidden fitness always breaks autonomy by hitchhiking. But a kernel whose observed fiber
masses do not depend on the parents is selection-autonomous for every fitness
(`selectionAutonomous_of_kernelMass_eq`), with a hidden fitness in the example
`selectionAutonomous_parentFree`.

Scope. Selection is fecundity selection on both parents with a positive fitness; viability
selection on children, mutation and finite populations are not treated. Selection-autonomy is
characterized when the fitness factors through the observation and for unbiased copying; for a
general kernel with hidden fitness only the sufficient conditions above are proved.

## Empirical status

None. The bodies here are finite sums and equivalence relations on a finite set; kernels, fitness
and populations are supplied, and no measurement can bear on these statements.
-/

namespace Descent.Pangenome.AncestralLocality

noncomputable section

variable {H : Type*} [Fintype H]

/-! ### Selection on the kernel and on the population -/

/-- The fitness-weighted kernel `s(x) s(y) K(x,y;z)`, normalized for each pair of parents. -/
def selectedKernel (K : H → H → H → ℝ) (s : H → ℝ) (x y z : H) : ℝ :=
  s x * s y * K x y z / ∑ w, s x * s y * K x y w

/-- **Normalized per pair, selection does not change the kernel.**
Assumes: `IsHeredityKernel K`. -/
theorem selectedKernel_eq {K : H → H → H → ℝ} (hK : IsHeredityKernel K) {s : H → ℝ}
    (hs : ∀ x, 0 < s x) : selectedKernel K s = K := by
  funext x y z
  have hne : s x * s y ≠ 0 := (mul_pos (hs x) (hs y)).ne'
  rw [selectedKernel, ← Finset.mul_sum, hK.sum_eq_one, mul_one, mul_div_cancel_left₀ _ hne]

/-- The hereditary closure of the selected kernel is that of the kernel.
Assumes: `IsHeredityKernel K`. -/
theorem hereditaryClosure_selectedKernel {K : H → H → H → ℝ} (hK : IsHeredityKernel K)
    {s : H → ℝ} (hs : ∀ x, 0 < s x) (P : Setoid H) :
    hereditaryClosure (selectedKernel K s) P = hereditaryClosure K P := by
  rw [selectedKernel_eq hK hs]

/-- The size-biased population `s·p/⟨s,p⟩`: parents chosen in proportion to their fitness. -/
def sizeBias (s p : H → ℝ) (x : H) : ℝ :=
  s x * p x / ∑ y, s y * p y

/-- **The selected next generation** `Σ_{x,y} s(x)p(x) s(y)p(y) K(x,y;z) / ⟨s,p⟩²`. -/
def selectedReproduce (K : H → H → H → ℝ) (s p : H → ℝ) (z : H) : ℝ :=
  (∑ x, ∑ y, s x * p x * (s y * p y) * K x y z) / (∑ x, s x * p x) ^ 2

/-- **Selection is reproduction of the size-biased population.** -/
theorem selectedReproduce_eq (K : H → H → H → ℝ) (s p : H → ℝ) :
    selectedReproduce K s p = reproduce K (sizeBias s p) := by
  funext z
  rw [selectedReproduce, reproduce, Finset.sum_div]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun y _ ↦ ?_
  rw [sizeBias, sizeBias]
  ring

/-- A positive fitness has positive mean under a probability vector. -/
theorem sum_mul_pos_of_mem_stdSimplex {s p : H → ℝ} (hs : ∀ x, 0 < s x)
    (hp : p ∈ stdSimplex ℝ H) : 0 < ∑ x, s x * p x := by
  by_contra h
  have hnn : ∀ x ∈ Finset.univ, 0 ≤ s x * p x := fun x _ ↦ mul_nonneg (hs x).le (hp.1 x)
  have hz := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp
    (le_antisymm (not_lt.mp h) (Finset.sum_nonneg hnn))
  have hp0 : ∀ x, p x = 0 := fun x ↦
    (mul_eq_zero.mp (hz x (Finset.mem_univ x))).resolve_left (hs x).ne'
  have h1 := hp.2
  simp only [hp0, Finset.sum_const_zero] at h1
  exact zero_ne_one h1

/-- The size-biased population is a probability vector. -/
theorem sizeBias_mem_stdSimplex {s p : H → ℝ} (hs : ∀ x, 0 < s x) (hp : p ∈ stdSimplex ℝ H) :
    sizeBias s p ∈ stdSimplex ℝ H := by
  have hS := sum_mul_pos_of_mem_stdSimplex hs hp
  refine ⟨fun x ↦ div_nonneg (mul_nonneg (hs x).le (hp.1 x)) hS.le, ?_⟩
  simp only [sizeBias, ← Finset.sum_div]
  exact div_self hS.ne'

/-- **Selection can be undone**: size-biasing by `s` after size-biasing by `1/s` returns the
population. -/
theorem sizeBias_sizeBias_inv {s q : H → ℝ} (hs : ∀ x, 0 < s x) (hq : q ∈ stdSimplex ℝ H) :
    sizeBias s (sizeBias (fun x ↦ (s x)⁻¹) q) = q := by
  have hT := sum_mul_pos_of_mem_stdSimplex (fun x ↦ inv_pos.mpr (hs x)) hq
  have hterm : ∀ x, s x * sizeBias (fun x ↦ (s x)⁻¹) q x = q x / ∑ y, (s y)⁻¹ * q y := by
    intro x
    rw [sizeBias, ← mul_div_assoc, ← mul_assoc, mul_inv_cancel₀ (hs x).ne', one_mul]
  have hsum : ∑ y, s y * sizeBias (fun x ↦ (s x)⁻¹) q y = 1 / ∑ y, (s y)⁻¹ * q y := by
    simp only [hterm, ← Finset.sum_div, hq.2]
  funext x
  rw [sizeBias, hterm, hsum, one_div, div_inv_eq_mul, div_mul_cancel₀ (q x) hT.ne']

/-- **Size bias commutes with observing** when the fitness is a function of the observation. -/
theorem pushforward_sizeBias_of_factor {O : Type*} [Fintype O] [DecidableEq O] {s : H → ℝ}
    {π : H → O} {sbar : O → ℝ} (hs : ∀ x, s x = sbar (π x)) (p : H → ℝ) :
    pushforward π (sizeBias s p) = sizeBias sbar (pushforward π p) := by
  funext o
  have hden : ∑ y, s y * p y = ∑ a, sbar a * pushforward π p a := by
    have h := sum_mul_comp_eq_sum_pushforward π p sbar
    simp only [hs]
    convert h using 1 <;> exact Finset.sum_congr rfl fun _ _ ↦ mul_comm _ _
  rw [pushforward_eq_sum_fiber, sizeBias, ← hden]
  simp only [sizeBias, ← Finset.sum_div]
  congr 1
  rw [pushforward_eq_sum_fiber, Finset.mul_sum]
  exact Finset.sum_congr rfl fun z hz ↦ by rw [hs, (mem_fiber_iff π o z).mp hz]

/-! ### Operational autonomy under selection -/

/-- **Selection-autonomy**: the observed selected next generation depends on the population only
through its observed law. -/
def SelectionAutonomous {O : Type*} [DecidableEq O] (K : H → H → H → ℝ) (s : H → ℝ)
    (π : H → O) : Prop :=
  ∀ p ∈ stdSimplex ℝ H, ∀ q ∈ stdSimplex ℝ H, pushforward π p = pushforward π q →
    pushforward π (reproduce K (sizeBias s p)) = pushforward π (reproduce K (sizeBias s q))

/-- **Selection on an observed feature.** For a symmetric kernel and a positive fitness that is a
function of the observation, selection-autonomy is hereditary autonomy.
Assumes: `∀ x y z, K x y z = K y x z`. -/
theorem selectionAutonomous_iff_of_factor [DecidableEq H] {O : Type*} [Fintype O]
    [DecidableEq O] {K : H → H → H → ℝ} (hK : ∀ x y z, K x y z = K y x z) {s : H → ℝ}
    (hs : ∀ x, 0 < s x) {π : H → O} {sbar : O → ℝ} (hsbar : ∀ x, s x = sbar (π x)) :
    SelectionAutonomous K s π ↔ HereditarilyAutonomous K π := by
  rw [hereditarilyAutonomous_iff_pushforward_reproduce_determined K hK π]
  have hinv : ∀ x, (s x)⁻¹ = (sbar (π x))⁻¹ := fun x ↦ by rw [hsbar]
  constructor
  · intro hA q hq q' hq' hqq'
    have h := hA _ (sizeBias_mem_stdSimplex (fun x ↦ inv_pos.mpr (hs x)) hq) _
      (sizeBias_mem_stdSimplex (fun x ↦ inv_pos.mpr (hs x)) hq')
      (by rw [pushforward_sizeBias_of_factor (sbar := fun a ↦ (sbar a)⁻¹) hinv,
        pushforward_sizeBias_of_factor (sbar := fun a ↦ (sbar a)⁻¹) hinv, hqq'])
    rwa [sizeBias_sizeBias_inv hs hq, sizeBias_sizeBias_inv hs hq'] at h
  · intro hA p hp q hq hpq
    exact hA _ (sizeBias_mem_stdSimplex hs hp) _ (sizeBias_mem_stdSimplex hs hq)
      (by rw [pushforward_sizeBias_of_factor hsbar, pushforward_sizeBias_of_factor hsbar, hpq])

/-! ### The selection closure -/

/-- **The selection closure**: the hereditary closure of the observation joined with fitness. -/
def selectionClosure (K : H → H → H → ℝ) (s : H → ℝ) (P : Setoid H) : Setoid H :=
  hereditaryClosure K (P ⊓ Setoid.ker s)

/-- **The selection closure is the greatest autonomous partition below `P` on whose blocks the
fitness is constant.** Assumes: `IsHeredityKernel K`. -/
theorem isGreatest_selectionClosure {K : H → H → H → ℝ} (hK : IsHeredityKernel K) (s : H → ℝ)
    (P : Setoid H) :
    IsGreatest {Q | IsAutonomous K Q ∧ Q ≤ P ∧ Q ≤ Setoid.ker s} (selectionClosure K s P) :=
  ⟨⟨isAutonomous_hereditaryClosure hK _, le_inf_iff.mp (hereditaryClosure_le K _)⟩,
    fun _ hQ ↦ le_hereditaryClosure_of_isAutonomous hQ.1 (le_inf hQ.2.1 hQ.2.2)⟩

/-- The selection closure lies below the closure of the observation met with the fitness
partition. Assumes: `IsHeredityKernel K`. -/
theorem selectionClosure_le_inf {K : H → H → H → ℝ} (hK : IsHeredityKernel K) (s : H → ℝ)
    (P : Setoid H) : selectionClosure K s P ≤ hereditaryClosure K P ⊓ Setoid.ker s := by
  have hle := hereditaryClosure_le K (P ⊓ Setoid.ker s)
  exact le_inf (le_hereditaryClosure_of_isAutonomous (isAutonomous_hereditaryClosure hK _)
    (le_trans hle inf_le_left)) (le_trans hle inf_le_right)

/-- **Selection leaves the closure unchanged exactly when the fitness is constant on its blocks.**
Assumes: `IsHeredityKernel K`. -/
theorem selectionClosure_eq_hereditaryClosure_iff {K : H → H → H → ℝ} (hK : IsHeredityKernel K)
    (s : H → ℝ) (P : Setoid H) :
    selectionClosure K s P = hereditaryClosure K P ↔ hereditaryClosure K P ≤ Setoid.ker s := by
  constructor
  · intro h
    rw [← h]
    exact le_trans (hereditaryClosure_le K _) inf_le_right
  · intro h
    exact le_antisymm (le_trans (selectionClosure_le_inf hK s P) inf_le_left)
      (le_hereditaryClosure_of_isAutonomous (isAutonomous_hereditaryClosure hK P)
        (le_inf (hereditaryClosure_le K P) h))

open Classical in
/-- **The selection closure predicts selection.** The quotient map onto the blocks of the
selection closure of `π` is selection-autonomous. Assumes: `IsHeredityKernel K`. -/
theorem selectionAutonomous_closureMap {O : Type*} {K : H → H → H → ℝ} (hK : IsHeredityKernel K)
    {s : H → ℝ} (hs : ∀ x, 0 < s x) (π : H → O) :
    SelectionAutonomous K s (Quotient.mk (selectionClosure K s (Setoid.ker π))) := by
  have hker : Setoid.ker (Quotient.mk (selectionClosure K s (Setoid.ker π))) =
      selectionClosure K s (Setoid.ker π) :=
    Setoid.ext fun _ _ ↦ ⟨Quotient.exact, Quotient.sound⟩
  have hA : HereditarilyAutonomous K (Quotient.mk (selectionClosure K s (Setoid.ker π))) := by
    rw [hereditarilyAutonomous_iff, hker]
    exact isAutonomous_hereditaryClosure hK _
  exact (selectionAutonomous_iff_of_factor hK.symm hs
    (sbar := Quotient.lift s fun a b h ↦
      (le_trans (hereditaryClosure_le K (Setoid.ker π ⊓ Setoid.ker s)) inf_le_right) h)
    fun _ ↦ rfl).mpr hA

/-! ### Hidden fitness under unbiased copying -/

section Copying

variable [DecidableEq H]

omit [Fintype H] in
/-- Unbiased copying does not see the order of the parents. -/
theorem halfMix_symm (x y z : H) : halfMix x y z = halfMix y x z := by
  unfold halfMix
  ring

/-- **Under unbiased copying every observation is autonomous.** -/
theorem hereditarilyAutonomous_halfMix {O : Type*} [DecidableEq O] (π : H → O) :
    HereditarilyAutonomous (halfMix : H → H → H → ℝ) π :=
  ⟨halfMix, fun x y o ↦ sum_filter_halfMix x y fun z ↦ π z = o⟩

/-- **Unbiased copying reproduces every probability vector.** -/
theorem reproduce_halfMix_eq {q : H → ℝ} (hq : ∑ x, q x = 1) : reproduce halfMix q = q := by
  funext z
  have hinner : ∀ x, ∑ y, q y * halfMix x y z = (if x = z then 1 else 0) / 2 + q z / 2 := by
    intro x
    have hy : ∀ y, q y * halfMix x y z =
        q y * ((if x = z then 1 else 0) / 2) + (if y = z then q y else 0) / 2 := by
      intro y
      unfold halfMix
      split_ifs <;> ring
    rw [Finset.sum_congr rfl fun y _ ↦ hy y, Finset.sum_add_distrib, ← Finset.sum_mul, hq,
      one_mul, ← Finset.sum_div, Finset.sum_ite_eq' Finset.univ z, if_pos (Finset.mem_univ z)]
  have hx : ∀ x, ∑ y, q x * q y * halfMix x y z =
      (if x = z then q x else 0) / 2 + q x * (q z / 2) := by
    intro x
    calc ∑ y, q x * q y * halfMix x y z = q x * ∑ y, q y * halfMix x y z := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun y _ ↦ mul_assoc _ _ _
      _ = (if x = z then q x else 0) / 2 + q x * (q z / 2) := by
          rw [hinner x]
          split_ifs <;> ring
  rw [reproduce, Finset.sum_congr rfl fun x _ ↦ hx x, Finset.sum_add_distrib, ← Finset.sum_div,
    Finset.sum_ite_eq' Finset.univ z, if_pos (Finset.mem_univ z), ← Finset.sum_mul, hq]
  ring

/-- Selecting from `½δ_x + ½δ_y` with `y` in another observed class gives `x`'s class the share
`s(x) / (s(x) + s(y))`. -/
theorem pushforward_sizeBias_pairMidpoint {O : Type*} [DecidableEq O] (s : H → ℝ) (π : H → O)
    {x y : H} (hxy : π y ≠ π x) :
    pushforward π (sizeBias s (pairMidpoint x y)) (π x) = s x / (s x + s y) := by
  have hD : ∑ w, s w * pairMidpoint x y w = 2⁻¹ * (s x + s y) := by
    rw [← sum_pairMidpoint_mul x y s]
    exact Finset.sum_congr rfl fun w _ ↦ mul_comm _ _
  have hz : ∀ z, s z * pairMidpoint x y z =
      2⁻¹ * ((if x = z then s z else 0) + (if y = z then s z else 0)) := by
    intro z
    unfold pairMidpoint pointMass
    split_ifs <;> ring
  have hN : ∑ z ∈ fiber π (π x), s z * pairMidpoint x y z = 2⁻¹ * s x := by
    rw [Finset.sum_congr rfl fun z _ ↦ hz z, ← Finset.mul_sum, Finset.sum_add_distrib,
      Finset.sum_ite_eq, Finset.sum_ite_eq, if_pos ((mem_fiber_iff π (π x) x).mpr rfl),
      if_neg fun h ↦ hxy ((mem_fiber_iff π (π x) y).mp h), add_zero]
  rw [pushforward_eq_sum_fiber]
  simp only [sizeBias]
  rw [← Finset.sum_div, hN, hD, mul_div_mul_left _ _ (by norm_num : (2⁻¹ : ℝ) ≠ 0)]

/-- **Hitchhiking under copying.** If unbiased copying is selection-autonomous for `π`, the
fitness agrees on two states of one observed class whenever a state outside the class exists. -/
theorem fitness_eq_of_selectionAutonomous_halfMix {O : Type*} [DecidableEq O] {s : H → ℝ}
    (hs : ∀ x, 0 < s x) {π : H → O} (h : SelectionAutonomous (halfMix : H → H → H → ℝ) s π)
    {x x' y : H} (hx : π x = π x') (hy : π y ≠ π x) : s x = s x' := by
  have hy' : π y ≠ π x' := fun h' ↦ hy (h'.trans hx.symm)
  have hp := pairMidpoint_mem_stdSimplex x y
  have hq := pairMidpoint_mem_stdSimplex x' y
  have hobs : pushforward π (pairMidpoint x y) = pushforward π (pairMidpoint x' y) := by
    rw [pushforward_pairMidpoint, pushforward_pairMidpoint, hx]
  have hsel := congrFun (h _ hp _ hq hobs) (π x)
  rw [reproduce_halfMix_eq (sizeBias_mem_stdSimplex hs hp).2,
    reproduce_halfMix_eq (sizeBias_mem_stdSimplex hs hq).2,
    pushforward_sizeBias_pairMidpoint s π hy, hx, pushforward_sizeBias_pairMidpoint s π hy',
    div_eq_div_iff (add_pos (hs x) (hs y)).ne' (add_pos (hs x') (hs y)).ne'] at hsel
  have hprod : (s x - s x') * s y = 0 := by linear_combination hsel
  exact sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_right (hs y).ne')

/-- **Selection under unbiased copying.** When every observed class has a state outside it,
copying is selection-autonomous for `π` exactly when the fitness is a function of the
observation. -/
theorem selectionAutonomous_halfMix_iff {O : Type*} [Fintype O] [DecidableEq O] {s : H → ℝ}
    (hs : ∀ x, 0 < s x) {π : H → O} (hπ : ∀ x, ∃ y, π y ≠ π x) :
    SelectionAutonomous (halfMix : H → H → H → ℝ) s π ↔ ∀ x x', π x = π x' → s x = s x' := by
  constructor
  · intro h x x' hx
    obtain ⟨y, hy⟩ := hπ x
    exact fitness_eq_of_selectionAutonomous_halfMix hs h hx hy
  · intro hfac
    classical
    refine (selectionAutonomous_iff_of_factor halfMix_symm hs
      (sbar := fun o ↦ if h : ∃ x, π x = o then s h.choose else 1) fun x ↦ ?_).mpr
      (hereditarilyAutonomous_halfMix π)
    have h : ∃ x', π x' = π x := ⟨x, rfl⟩
    show s x = if h : ∃ x', π x' = π x then s h.choose else 1
    rw [dif_pos h]
    exact hfac x h.choose h.choose_spec.symm

end Copying

/-! ### Flat fiber masses and the gated exchange -/

/-- A population average of a parent-independent quantity is that quantity. -/
theorem sum_sum_mul_const {q : H → ℝ} (hq : ∑ x, q x = 1) (c : ℝ) :
    ∑ x, ∑ y, q x * q y * c = c := by
  simp only [← Finset.sum_mul, ← Finset.mul_sum, hq, mul_one, one_mul]

/-- **Flat fiber masses ignore selection.** If the mass of every observed class under the kernel
does not depend on the parents, the observation is selection-autonomous for every positive
fitness. -/
theorem selectionAutonomous_of_kernelMass_eq {O : Type*} [DecidableEq O] {K : H → H → H → ℝ}
    {π : H → O} {c : O → ℝ} (hc : ∀ x y o, kernelMass K x y (fiber π o) = c o) {s : H → ℝ}
    (hs : ∀ x, 0 < s x) : SelectionAutonomous K s π := by
  intro p hp q hq _
  funext o
  rw [pushforward_reproduce, pushforward_reproduce]
  simp only [hc]
  rw [sum_sum_mul_const (sizeBias_mem_stdSimplex hs hp).2,
    sum_sum_mul_const (sizeBias_mem_stdSimplex hs hq).2]

/-- A kernel whose child does not depend on the parents. -/
def parentFreeKernel (μ : H → ℝ) (_ _ : H) (z : H) : ℝ :=
  μ z

/-- The fitness `2` on states whose second feature is `true`, and `1` otherwise. -/
def hiddenFitness (x : Bool × Bool) : ℝ :=
  if x.2 then 2 else 1

/-- **Hidden fitness need not enter the closure.** For a kernel whose child ignores the parents,
observing the first feature stays selection-autonomous under a fitness on the second, which is
not a function of the observation. -/
theorem selectionAutonomous_parentFree (μ : Bool × Bool → ℝ) :
    SelectionAutonomous (parentFreeKernel μ) hiddenFitness Prod.fst ∧
      hiddenFitness (false, false) ≠ hiddenFitness (false, true) := by
  refine ⟨selectionAutonomous_of_kernelMass_eq (c := fun o ↦ pushforward Prod.fst μ o)
    (fun _ _ _ ↦ rfl) fun x ↦ ?_, ?_⟩
  · unfold hiddenFitness
    split_ifs <;> norm_num
  · norm_num [hiddenFitness]

/-- A fitness on the feature `b` of the gated-exchange states. -/
def bFitness (x : Bool × Bool × Bool) : ℝ :=
  if x.2.1 then 2 else 1

/-- Meeting the partition of `a` with the fitness partition gives the partition of `(a, b)`. -/
theorem ker_observeA_inf_ker_bFitness :
    Setoid.ker observeA ⊓ Setoid.ker bFitness = Setoid.ker fun x ↦ (observeA x, observeB x) := by
  refine Setoid.ext fun x y ↦ ?_
  show observeA x = observeA y ∧ bFitness x = bFitness y ↔
    (observeA x, observeB x) = (observeA y, observeB y)
  obtain ⟨a, b, h⟩ := x
  obtain ⟨a', b', h'⟩ := y
  cases b <;> cases b' <;> norm_num [observeA, observeB, bFitness]

/-- **The candidate formula fails.** For the gated exchange, observing `a` with fitness on `b`:
the join `(a, b)` is not autonomous, so the selection closure is strictly finer than the closure
of `a` met with the fitness partition. -/
theorem selectionClosure_ne_inf_gated :
    selectionClosure gatedKernel bFitness (Setoid.ker observeA) ≠
      hereditaryClosure gatedKernel (Setoid.ker observeA) ⊓ Setoid.ker bFitness := by
  intro h
  have hK : IsHeredityKernel gatedKernel := isHeredityKernel_childKernel gatedExchange
  have hA : IsAutonomous gatedKernel (Setoid.ker observeA) :=
    (hereditarilyAutonomous_iff _ _).mp hereditarilyAutonomous_observeA
  have hcl : hereditaryClosure gatedKernel (Setoid.ker observeA) = Setoid.ker observeA :=
    le_antisymm (hereditaryClosure_le _ _) (le_hereditaryClosure_of_isAutonomous hA le_rfl)
  have hsel : IsAutonomous gatedKernel
      (selectionClosure gatedKernel bFitness (Setoid.ker observeA)) :=
    isAutonomous_hereditaryClosure hK _
  rw [h, hcl, ker_observeA_inf_ker_bFitness] at hsel
  exact not_hereditarilyAutonomous_observeAB ((hereditarilyAutonomous_iff _ _).mpr hsel)

end

end Descent.Pangenome.AncestralLocality
