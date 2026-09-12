/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.AncestralLocality.HereditaryClosure
import Descent.Pangenome.AncestralLocality.OperationalAutonomy

assert_below Descent.PopGen Descent.Spectral Descent.Blindness Descent.Conditionals
assert_below Descent.Portability Descent.Decision Descent.Program

/-!
# Annotated kernels: state kernels predict but do not identify ancestry

The remark of `ANCESTRAL_LOCALITY.md` §2.2. A state kernel `K(x,y;z)` says which genome the child
of `x` and `y` has, not which parent each piece of it came from. Ancestry needs an annotated kernel
`𝒦(x,y;dz,dη)` whose witness `η` records the correspondence, and the closure results of §3 concern
prediction from `K` alone. This module makes the remark exact on finite sets.

**Annotated kernels.** `IsAnnotatedKernel σ A` is a kernel `A x y z η` from pairs of parents to
children with witnesses in a finite `W`, symmetric in the parents under a witness relabelling
`σ : W ≃ W`. Its state marginal `stateMarginal A` is a heredity kernel
(`isHeredityKernel_stateMarginal`), and its witness law `witnessLaw A x y` is a probability vector
(`sum_witnessLaw`).

**Prediction sees only the marginal.** Forgetting the witnesses of the annotated next generation
`annotatedReproduce A p` gives `reproduce (stateMarginal A) p` (`sum_annotatedReproduce`); the mass
`annotatedMass A x y B` of the children whose state lies in `B` is the marginal's `kernelMass`
(`annotatedMass_eq_kernelMass`), so hereditary autonomy computed from those masses is
`HereditarilyAutonomous (stateMarginal A)` (`hereditarilyAutonomous_stateMarginal_iff`). Two
annotated kernels with one marginal have the same observed next generations, the same autonomous
observations and the same `hereditaryClosure` (`sum_annotatedReproduce_congr`,
`hereditarilyAutonomous_stateMarginal_congr`, `hereditaryClosure_stateMarginal_congr`).

**Non-identification.** Reading the parents in the other order, `swapParents A`, keeps the marginal
(`stateMarginal_swapParents`). The donor annotation `donorAnnotation T` of a two-child kernel marks
the child `T x y`, whose copied material came from the second parent, with `true` and the child
`T y x` with `false`; its marginal is `childKernel T` (`stateMarginal_donorAnnotation`), and for
the note's exchange (4.2) that is `exchangeKernel` (`stateMarginal_donorAnnotation_orderedChild`).
When the two ordered children differ, the donor annotation and its parent swap give the child
`T x y` different witnesses (`donorAnnotation_ne_swapParents`), which happens for the exchange as
soon as the parents agree at the checker and differ at the target
(`donorAnnotation_orderedChild_ne_swapParents`). Even for identical parents the donor is a fair
coin that no state records (`donorAnnotation_self`).

A flag that depends only on the parents gives `flagAnnotation K f`, with marginal `K`
(`stateMarginal_flagAnnotation`) and witness law the point mass at the flag
(`witnessLaw_flagAnnotation`). On the exchange kernel, `exchangePerformed` flags every accepted
exchange and `exchangeVisible` only those that change the child. In a population of clones every
child carries an exchange event under the first and none under the second, while the marginal,
every prediction and every hereditary closure agree
(`performed_visible_same_closure_different_witnessLaw`).

Scope. Witnesses form a finite type and the annotated kernels are finite real tables; witnesses
are attached to one reproduction step and are not composed across generations into genealogies.
The non-identification examples are the donor and event annotations above, not a classification
of all annotations of a kernel.

## Empirical status

None. The bodies here are finite sums of supplied real numbers on finite sets; the kernels and the
witnesses are supplied, and no measurement can bear on these statements.
-/

namespace Descent.Pangenome.AncestralLocality

noncomputable section

variable {H W : Type*} [Fintype H] [Fintype W]

/-! ### Annotated kernels and their marginals -/

/-- An **annotated kernel** `𝒦(x,y;z,η)`: for each ordered pair of parents, a probability table on
children `z` with correspondence witnesses `η`, symmetric in the parents once the witnesses are
relabelled by `σ`. -/
structure IsAnnotatedKernel (σ : W ≃ W) (A : H → H → H → W → ℝ) : Prop where
  /-- Probabilities are nonnegative. -/
  nonneg : ∀ x y z η, 0 ≤ A x y z η
  /-- Each row is a probability table on children and witnesses. -/
  sum_eq_one : ∀ x y, ∑ z, ∑ η, A x y z η = 1
  /-- Exchanging the parents relabels the witnesses. -/
  symm : ∀ x y z η, A x y z η = A y x z (σ η)

/-- The state marginal `K(x,y;z) = Σ_η 𝒦(x,y;z,η)`: the kernel with the witnesses forgotten. -/
def stateMarginal (A : H → H → H → W → ℝ) (x y z : H) : ℝ :=
  ∑ η, A x y z η

/-- The witness law `Σ_z 𝒦(x,y;z,η)`: the correspondence with the child forgotten. -/
def witnessLaw (A : H → H → H → W → ℝ) (x y : H) (η : W) : ℝ :=
  ∑ z, A x y z η

/-- **The state marginal of an annotated kernel is a heredity kernel.**
Assumes: `IsAnnotatedKernel σ A`. -/
theorem isHeredityKernel_stateMarginal {σ : W ≃ W} {A : H → H → H → W → ℝ}
    (hA : IsAnnotatedKernel σ A) : IsHeredityKernel (stateMarginal A) where
  nonneg x y z := Finset.sum_nonneg fun η _ ↦ hA.nonneg x y z η
  sum_eq_one x y := hA.sum_eq_one x y
  symm x y z := by
    show ∑ η, A x y z η = ∑ η, A y x z η
    exact (Finset.sum_congr rfl fun η _ ↦ hA.symm x y z η).trans (Equiv.sum_comp σ (A y x z))

/-- The witness law is a probability vector. Assumes: `IsAnnotatedKernel σ A`. -/
theorem sum_witnessLaw {σ : W ≃ W} {A : H → H → H → W → ℝ} (hA : IsAnnotatedKernel σ A)
    (x y : H) : ∑ η, witnessLaw A x y η = 1 := by
  unfold witnessLaw
  rw [Finset.sum_comm]
  exact hA.sum_eq_one x y

/-! ### Prediction through the marginal -/

/-- **The annotated next generation**: the joint law of the child's state and witness when both
parents are drawn independently from `p`. -/
def annotatedReproduce (A : H → H → H → W → ℝ) (p : H → ℝ) (z : H) (η : W) : ℝ :=
  ∑ x, ∑ y, p x * p y * A x y z η

/-- **Forgetting the witnesses of the next generation is reproducing with the marginal.** -/
theorem sum_annotatedReproduce (A : H → H → H → W → ℝ) (p : H → ℝ) (z : H) :
    ∑ η, annotatedReproduce A p z η = reproduce (stateMarginal A) p z := by
  simp only [annotatedReproduce, reproduce, stateMarginal, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun x _ ↦ Finset.sum_comm

/-- In a population of clones of `x` the witnesses of the next generation follow the witness law
of the pair `(x, x)`. -/
theorem sum_annotatedReproduce_pointMass [DecidableEq H] (A : H → H → H → W → ℝ) (x : H)
    (η : W) : ∑ z, annotatedReproduce A (pointMass x) z η = witnessLaw A x x η := by
  show ∑ z, annotatedReproduce A (pointMass x) z η = ∑ z, A x x z η
  exact Finset.sum_congr rfl fun z _ ↦ sum_sum_pointMass x fun a b ↦ A a b z η

/-- `𝒦(x,y; B × W)`: the probability that the annotated child's state lies in `B`, whatever its
witness. -/
def annotatedMass (A : H → H → H → W → ℝ) (x y : H) (B : Finset H) : ℝ :=
  ∑ zη ∈ B ×ˢ (Finset.univ : Finset W), A x y zη.1 zη.2

/-- The mass of a set of child states under the annotated kernel is its mass under the marginal. -/
theorem annotatedMass_eq_kernelMass (A : H → H → H → W → ℝ) (x y : H) (B : Finset H) :
    annotatedMass A x y B = kernelMass (stateMarginal A) x y B := by
  rw [annotatedMass, Finset.sum_product]
  rfl

/-- **Autonomy computed from the annotated kernel is autonomy of its marginal**: a kernel on
observed values reproduces the annotated fiber masses exactly when it satisfies (2.2) for the
marginal. -/
theorem hereditarilyAutonomous_stateMarginal_iff {O : Type*} [DecidableEq O]
    (A : H → H → H → W → ℝ) (π : H → O) :
    HereditarilyAutonomous (stateMarginal A) π ↔
      ∃ Kbar : O → O → O → ℝ, ∀ x y o, annotatedMass A x y (fiber π o) = Kbar (π x) (π y) o := by
  unfold HereditarilyAutonomous
  simp only [annotatedMass_eq_kernelMass]

/-- Annotated kernels with one marginal have the same observed next generations. -/
theorem sum_annotatedReproduce_congr {A A' : H → H → H → W → ℝ}
    (h : stateMarginal A = stateMarginal A') (p : H → ℝ) (z : H) :
    ∑ η, annotatedReproduce A p z η = ∑ η, annotatedReproduce A' p z η := by
  rw [sum_annotatedReproduce, sum_annotatedReproduce, h]

/-- Annotated kernels with one marginal have the same hereditarily autonomous observations. -/
theorem hereditarilyAutonomous_stateMarginal_congr {O : Type*} [DecidableEq O]
    {A A' : H → H → H → W → ℝ} (h : stateMarginal A = stateMarginal A') (π : H → O) :
    HereditarilyAutonomous (stateMarginal A) π ↔ HereditarilyAutonomous (stateMarginal A') π := by
  rw [h]

/-- **The hereditary closure depends on an annotated kernel only through its marginal.** -/
theorem hereditaryClosure_stateMarginal_congr {A A' : H → H → H → W → ℝ}
    (h : stateMarginal A = stateMarginal A') (P : Setoid H) :
    hereditaryClosure (stateMarginal A) P = hereditaryClosure (stateMarginal A') P := by
  rw [h]

/-! ### Non-identification -/

/-- An annotated kernel read with its parents in the other order. -/
def swapParents (A : H → H → H → W → ℝ) (x y z : H) (η : W) : ℝ :=
  A y x z η

/-- Reading the parents in the other order gives an annotated kernel.
Assumes: `IsAnnotatedKernel σ A`. -/
theorem isAnnotatedKernel_swapParents {σ : W ≃ W} {A : H → H → H → W → ℝ}
    (hA : IsAnnotatedKernel σ A) : IsAnnotatedKernel σ (swapParents A) where
  nonneg x y z η := hA.nonneg y x z η
  sum_eq_one x y := hA.sum_eq_one y x
  symm x y z η := hA.symm y x z η

/-- Reading the parents in the other order keeps the state marginal.
Assumes: `IsAnnotatedKernel σ A`. -/
theorem stateMarginal_swapParents {σ : W ≃ W} {A : H → H → H → W → ℝ}
    (hA : IsAnnotatedKernel σ A) : stateMarginal (swapParents A) = stateMarginal A :=
  funext fun x ↦ funext fun y ↦ funext fun z ↦ (isHeredityKernel_stateMarginal hA).symm y x z

/-- **The donor annotation** of a two-child kernel: the child `T x y`, whose copied material came
from the second parent, carries the witness `true`, and the child `T y x` carries `false`. -/
def donorAnnotation [DecidableEq H] (T : H → H → H) (x y z : H) (η : Bool) : ℝ :=
  (if T x y = z ∧ η = true then 1 / 2 else 0) + if T y x = z ∧ η = false then 1 / 2 else 0

/-- The donor annotation forgets to the two-child kernel. -/
theorem stateMarginal_donorAnnotation [DecidableEq H] (T : H → H → H) :
    stateMarginal (donorAnnotation T) = childKernel T := by
  funext x y z
  rw [stateMarginal, Fintype.sum_bool]
  simp [donorAnnotation, childKernel]

/-- **The donor annotation is an annotated kernel**: exchanging the parents exchanges the donor
labels. -/
theorem isAnnotatedKernel_donorAnnotation [DecidableEq H] (T : H → H → H) :
    IsAnnotatedKernel (Equiv.swap true false) (donorAnnotation T) where
  nonneg x y z η := by
    unfold donorAnnotation
    split_ifs <;> norm_num
  sum_eq_one x y := by
    show ∑ z, stateMarginal (donorAnnotation T) x y z = 1
    rw [stateMarginal_donorAnnotation]
    exact (isHeredityKernel_childKernel T).sum_eq_one x y
  symm x y z η := by
    cases η <;> simp [donorAnnotation]

omit [Fintype H] in
/-- **For identical parents the donor is a fair coin**: the child is the same whichever parent
donated, and each donor label has probability one half. -/
theorem donorAnnotation_self [DecidableEq H] (T : H → H → H) (x : H) (η : Bool) :
    donorAnnotation T x x (T x x) η = 1 / 2 := by
  cases η <;> simp [donorAnnotation]

omit [Fintype H] in
/-- **The two ordered-child annotations disagree.** When the two ordered children differ, the
donor annotation gives the child `T x y` the donor label `true` with probability one half, and
its parent swap gives it probability zero. -/
theorem donorAnnotation_ne_swapParents [DecidableEq H] (T : H → H → H) {x y : H}
    (h : T x y ≠ T y x) :
    donorAnnotation T x y (T x y) true ≠ swapParents (donorAnnotation T) x y (T x y) true := by
  norm_num [donorAnnotation, swapParents, h, Ne.symm h]

section Exchange

variable {V : Type*} [DecidableEq V] [Fintype V]

omit [Fintype V] in
/-- The two ordered children (4.1) differ when the parents agree at the checker `j` and differ at
the target `i`. -/
theorem orderedChild_ne_swap {i j : V} {x y : V → Bool} (hj : x j = y j) (hi : x i ≠ y i) :
    orderedChild i j x y ≠ orderedChild i j y x := by
  intro h
  have hk : (if i = i ∧ x j = y j then y i else x i) =
      (if i = i ∧ y j = x j then x i else y i) := congrFun h i
  rw [if_pos ⟨rfl, hj⟩, if_pos ⟨rfl, hj.symm⟩] at hk
  exact hi hk.symm

/-- The donor annotation of the ordered child forgets to the exchange kernel (4.2). -/
theorem stateMarginal_donorAnnotation_orderedChild (i j : V) :
    stateMarginal (donorAnnotation (orderedChild i j)) = exchangeKernel i j := by
  rw [stateMarginal_donorAnnotation]
  funext x y z
  exact (exchangeKernel_eq_childKernel i j x y z).symm

/-- **Same exchange kernel, different donors.** For parents that agree at the checker and differ
at the target, the donor annotation of the exchange and its parent swap disagree about which
parent the copied coordinate came from. -/
theorem donorAnnotation_orderedChild_ne_swapParents {i j : V} {x y : V → Bool} (hj : x j = y j)
    (hi : x i ≠ y i) :
    donorAnnotation (orderedChild i j) x y (orderedChild i j x y) true ≠
      swapParents (donorAnnotation (orderedChild i j)) x y (orderedChild i j x y) true :=
  donorAnnotation_ne_swapParents _ (orderedChild_ne_swap hj hi)

end Exchange

/-! ### Event annotations -/

/-- **Annotation by a parental flag**: the child keeps its law under `K` and carries the witness
`f x y`. -/
def flagAnnotation [DecidableEq W] (K : H → H → H → ℝ) (f : H → H → W) (x y z : H) (η : W) :
    ℝ :=
  if f x y = η then K x y z else 0

/-- A flag annotation forgets to its kernel. -/
theorem stateMarginal_flagAnnotation [DecidableEq W] (K : H → H → H → ℝ) (f : H → H → W) :
    stateMarginal (flagAnnotation K f) = K := by
  funext x y z
  simp [stateMarginal, flagAnnotation]

/-- The witness law of a flag annotation is the point mass at the flag.
Assumes: `IsHeredityKernel K`. -/
theorem witnessLaw_flagAnnotation [DecidableEq W] {K : H → H → H → ℝ} (hK : IsHeredityKernel K)
    (f : H → H → W) (x y : H) (η : W) :
    witnessLaw (flagAnnotation K f) x y η = if f x y = η then 1 else 0 := by
  by_cases h : f x y = η
  · simp [witnessLaw, flagAnnotation, h, hK.sum_eq_one]
  · simp [witnessLaw, flagAnnotation, h]

/-- A symmetric flag on a heredity kernel gives an annotated kernel with trivial relabelling.
Assumes: `IsHeredityKernel K`. -/
theorem isAnnotatedKernel_flagAnnotation [DecidableEq W] {K : H → H → H → ℝ}
    (hK : IsHeredityKernel K) {f : H → H → W} (hf : ∀ x y, f x y = f y x) :
    IsAnnotatedKernel (Equiv.refl W) (flagAnnotation K f) where
  nonneg x y z η := by
    unfold flagAnnotation
    split_ifs
    · exact hK.nonneg x y z
    · exact le_rfl
  sum_eq_one x y := by
    show ∑ z, stateMarginal (flagAnnotation K f) x y z = 1
    rw [stateMarginal_flagAnnotation]
    exact hK.sum_eq_one x y
  symm x y z η := by
    simp only [flagAnnotation, Equiv.refl_apply, hf x y, hK.symm x y z]

section Exchange

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- The exchange at a checker `j` is performed: the parents agree at `j`. -/
def exchangePerformed (j : V) (x y : V → Bool) : Bool :=
  decide (x j = y j)

/-- The exchange at target `i` and checker `j` is visible: it is performed and the parents differ
at `i`, so the child is not a copy of its template parent. -/
def exchangeVisible (i j : V) (x y : V → Bool) : Bool :=
  decide (x j = y j ∧ x i ≠ y i)

omit [Fintype V] in
theorem exchangePerformed_comm (j : V) (x y : V → Bool) :
    exchangePerformed j x y = exchangePerformed j y x := by
  unfold exchangePerformed
  by_cases h : x j = y j
  · simp [h]
  · simp [h, Ne.symm h]

omit [Fintype V] in
theorem exchangeVisible_comm (i j : V) (x y : V → Bool) :
    exchangeVisible i j x y = exchangeVisible i j y x := by
  unfold exchangeVisible
  by_cases hj : x j = y j
  · by_cases hi : x i = y i
    · simp [hj, hi]
    · simp [hj, hi, Ne.symm hi]
  · simp [hj, Ne.symm hj]

/-- Under the performed-event annotation, identical parents always carry an exchange event. -/
theorem witnessLaw_exchangePerformed_self (i j : V) (x : V → Bool) :
    witnessLaw (flagAnnotation (exchangeKernel i j) (exchangePerformed j)) x x true = 1 := by
  rw [witnessLaw_flagAnnotation (isHeredityKernel_exchangeKernel i j)]
  simp [exchangePerformed]

/-- Under the visible-event annotation, identical parents never carry an exchange event. -/
theorem witnessLaw_exchangeVisible_self (i j : V) (x : V → Bool) :
    witnessLaw (flagAnnotation (exchangeKernel i j) (exchangeVisible i j)) x x true = 0 := by
  rw [witnessLaw_flagAnnotation (isHeredityKernel_exchangeKernel i j)]
  simp [exchangeVisible]

/-- **§2.2: prediction from the kernel does not identify ancestry.** The performed-event and the
visible-event annotations of the exchange kernel have one state marginal, hence one hereditary
closure of every partition; yet in a population of clones every child of the first carries an
exchange event and no child of the second does. -/
theorem performed_visible_same_closure_different_witnessLaw (i j : V) (x : V → Bool) :
    stateMarginal (flagAnnotation (exchangeKernel i j) (exchangePerformed j)) =
        stateMarginal (flagAnnotation (exchangeKernel i j) (exchangeVisible i j)) ∧
      (∀ P : Setoid (V → Bool),
        hereditaryClosure
            (stateMarginal (flagAnnotation (exchangeKernel i j) (exchangePerformed j))) P =
          hereditaryClosure
            (stateMarginal (flagAnnotation (exchangeKernel i j) (exchangeVisible i j))) P) ∧
      ∑ z, annotatedReproduce (flagAnnotation (exchangeKernel i j) (exchangePerformed j))
          (pointMass x) z true = 1 ∧
      ∑ z, annotatedReproduce (flagAnnotation (exchangeKernel i j) (exchangeVisible i j))
          (pointMass x) z true = 0 := by
  have h : stateMarginal (flagAnnotation (exchangeKernel i j) (exchangePerformed j)) =
      stateMarginal (flagAnnotation (exchangeKernel i j) (exchangeVisible i j)) := by
    rw [stateMarginal_flagAnnotation, stateMarginal_flagAnnotation]
  refine ⟨h, fun P ↦ hereditaryClosure_stateMarginal_congr h P, ?_, ?_⟩
  · rw [sum_annotatedReproduce_pointMass, witnessLaw_exchangePerformed_self]
  · rw [sum_annotatedReproduce_pointMass, witnessLaw_exchangeVisible_self]

end Exchange

end

end Descent.Pangenome.AncestralLocality
