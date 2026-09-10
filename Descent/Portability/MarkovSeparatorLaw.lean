/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.ConditionalSeparatorLaw

assert_below Descent.Decision Descent.Program

/-!
Deriving simultaneous conditional independence from a positive finite law's
single-site Markov condition. Invariance of a density ratio under each coordinate
update forces a product law. This closes the passage from local conditionals to
the full separator factorization; independence is the conclusion.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.MarkovSeparatorLaw

open ConditionalSeparatorLaw

variable {X Y D : Type*} [Fintype X] [Fintype Y] [Fintype D] [DecidableEq D]

omit [Fintype X] in
/-- Every configuration can be reached by finitely many single-coordinate updates. -/
theorem constant_of_update_invariant (r : (D → X) → ℝ)
    (hr : ∀ x i v, r (Function.update x i v) = r x) (x base : D → X) :
    r x = r base := by
  classical
  let mix := fun (s : Finset D) i ↦ if i ∈ s then x i else base i
  have hall : ∀ s : Finset D, r (mix s) = r base := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp [mix]
    | @insert i s hi ih =>
      have hm : mix (insert i s) = Function.update (mix s) i (x i) := by
        funext j
        by_cases hji : j = i
        · subst j
          simp [mix]
        · simp [mix, hji]
      rw [hm, hr, ih]
  simpa [mix] using hall Finset.univ

/-- Actual single-site conditional probabilities, written without division. -/
def LocalSeparatorCondition (p : FiniteReportLaw (Y × (D → X)))
    (k : Y → D → FiniteReportLaw X) : Prop :=
  ∀ y x i, p.mass (y, x) =
    (k y i).mass (x i) * ∑ v : X, p.mass (y, Function.update x i v)

/-- Local conditionals obey the exact coordinate-update balance identity. -/
theorem local_update_balance (p : FiniteReportLaw (Y × (D → X)))
    (k : Y → D → FiniteReportLaw X) (hl : LocalSeparatorCondition p k)
    (y : Y) (x : D → X) (i : D) (v : X) :
    p.mass (y, x) * (k y i).mass v =
      p.mass (y, Function.update x i v) * (k y i).mass (x i) := by
  rw [hl y x i, hl y (Function.update x i v) i]
  simp only [Function.update_idem, Function.update_self]
  ring

/-- Strictly positive joint masses force strictly positive local conditional masses. -/
theorem local_mass_pos [Nonempty X] (p : FiniteReportLaw (Y × (D → X)))
    (hp : ∀ y x, 0 < p.mass (y, x)) (k : Y → D → FiniteReportLaw X)
    (hl : LocalSeparatorCondition p k) (y : Y) (i : D) (v : X) :
    0 < (k y i).mass v := by
  classical
  let x : D → X := fun _ ↦ v
  have h := hp y x
  rw [hl y x i] at h
  exact (mul_pos_iff.mp h).resolve_right (fun hneg ↦
    (not_lt_of_ge ((k y i).mass_nonneg v)) hneg.1) |>.1

/-- The density ratio against the conditional product law is invariant under updates. -/
theorem density_ratio_update [Nonempty X] (p : FiniteReportLaw (Y × (D → X)))
    (hp : ∀ y x, 0 < p.mass (y, x)) (k : Y → D → FiniteReportLaw X)
    (hl : LocalSeparatorCondition p k) (y : Y) (x : D → X) (i : D) (v : X) :
    p.mass (y, Function.update x i v) / (∏ j, (k y j).mass (Function.update x i v j)) =
      p.mass (y, x) / (∏ j, (k y j).mass (x j)) := by
  have hprod : ∀ z : D → X, (∏ j, (k y j).mass (z j)) ≠ 0 := by
    intro z
    exact (Finset.prod_pos (fun j _ ↦ local_mass_pos p hp k hl y j (z j))).ne'
  apply (div_eq_div_iff (hprod _) (hprod _)).mpr
  have he : (∏ j ∈ Finset.univ.erase i, (k y j).mass (Function.update x i v j)) =
      ∏ j ∈ Finset.univ.erase i, (k y j).mass (x j) := by
    apply Finset.prod_congr rfl
    intro j hj
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i),
    ← Finset.prod_erase_mul _ _ (Finset.mem_univ i), he, Function.update_self]
  have hb := local_update_balance p k hl y x i v
  linear_combination -(∏ j ∈ Finset.univ.erase i, (k y j).mass (x j)) * hb

/-- The complement distribution is obtained by marginalizing the original joint law. -/
noncomputable def complementLaw (p : FiniteReportLaw (Y × (D → X))) : FiniteReportLaw Y where
  mass y := ∑ x, p.mass (y, x)
  mass_nonneg y := Finset.sum_nonneg (fun x _ ↦ p.mass_nonneg _)
  mass_sum := by simpa only [Fintype.sum_prod_type] using p.mass_sum

/-- Positive local Markov conditionals imply the full simultaneous separator factorization. -/
theorem local_implies_separator [Nonempty X] (p : FiniteReportLaw (Y × (D → X)))
    (hp : ∀ y x, 0 < p.mass (y, x)) (k : Y → D → FiniteReportLaw X)
    (hl : LocalSeparatorCondition p k) : p = separatorLaw (complementLaw p) k := by
  classical
  let base : D → X := fun _ ↦ Classical.choice inferInstance
  apply FiniteReportLaw.ext
  rintro ⟨y, x⟩
  let C := p.mass (y, base) / ∏ i, (k y i).mass (base i)
  have hfactor : ∀ z : D → X, p.mass (y, z) = C * ∏ i, (k y i).mass (z i) := by
    intro z
    have h := constant_of_update_invariant
      (fun z ↦ p.mass (y, z) / ∏ i, (k y i).mass (z i))
      (density_ratio_update p hp k hl y) z base
    have hprod : (∏ i, (k y i).mass (z i)) ≠ 0 :=
      (Finset.prod_pos (fun i _ ↦ local_mass_pos p hp k hl y i (z i))).ne'
    calc
      _ = (p.mass (y, z) / ∏ i, (k y i).mass (z i)) * ∏ i, (k y i).mass (z i) :=
        (div_mul_cancel₀ _ hprod).symm
      _ = _ := by rw [h]
  have hC : (complementLaw p).mass y = C := by
    change (∑ z, p.mass (y, z)) = C
    simp_rw [hfactor]
    rw [← Finset.mul_sum, ← Fintype.prod_sum]
    simp only [FiniteReportLaw.mass_sum, Finset.prod_const_one, mul_one]
  change p.mass (y, x) = (complementLaw p).mass y * ∏ i, (k y i).mass (x i)
  rw [hC, hfactor]

/-- Attenuation follows from local Markov conditionals of the actual positive joint law. -/
theorem local_markov_attenuation [Nonempty X] (p : FiniteReportLaw (Y × (D → X)))
    (hp : ∀ y x, 0 < p.mass (y, x)) (k : Y → D → FiniteReportLaw X)
    (hl : LocalSeparatorCondition p k) (ν : D → FiniteReportLaw X)
    (η : D → ℝ) (hη : ∀ i, 0 ≤ η i) (hηone : ∀ i, η i ≤ 1)
    (hminor : ∀ y i x, η i * (ν i).mass x ≤ (k y i).mass x)
    (u : Y → ℂ) (hu : ∀ y, ‖u y‖ ≤ 1)
    (z : D → X → ℂ) (hz : ∀ i x, ‖z i x‖ ≤ 1) :
    ‖phaseMean p (fun yx ↦ u yx.1 * ∏ i, z i (yx.2 i))‖ ≤
      Real.exp (-∑ i, η i * (1 - ‖phaseMean (ν i) (z i)‖)) := by
  rw [local_implies_separator p hp k hl]
  exact separator_phase_exp_bound (complementLaw p) k ν η hη hηone hminor u hu z hz

section Graph

variable {C : Type*} [Fintype C] [DecidableEq C] [Nonempty X]

/-- A local conditional kernel depends only on the adjacent vertices of its graph. -/
def NeighborLocal (adj : (D ⊕ C) → (D ⊕ C) → Prop)
    (K : D → ((D ⊕ C) → X) → FiniteReportLaw X) : Prop :=
  ∀ i f g, (∀ v, adj (Sum.inl i) v → f v = g v) → K i f = K i g

/-- The actual one-site conditional probabilities of the full finite graph law. -/
def GraphLocalCondition (p : FiniteReportLaw ((C → X) × (D → X)))
    (K : D → ((D ⊕ C) → X) → FiniteReportLaw X) : Prop :=
  ∀ y x i, p.mass (y, x) = (K i (Sum.elim x y)).mass (x i) *
    ∑ v : X, p.mass (y, Function.update x i v)

omit [Nonempty X] in
/-- Fixing the complement makes kernels on an independent set independent of all its states. -/
theorem independent_set_local_condition
    (p : FiniteReportLaw ((C → X) × (D → X)))
    (adj : (D ⊕ C) → (D ⊕ C) → Prop)
    (hind : ∀ i j, ¬ adj (Sum.inl i) (Sum.inl j))
    (K : D → ((D ⊕ C) → X) → FiniteReportLaw X)
    (hn : NeighborLocal adj K) (hl : GraphLocalCondition p K) (base : D → X) :
    LocalSeparatorCondition p (fun y i ↦ K i (Sum.elim base y)) := by
  intro y x i
  have hk : K i (Sum.elim x y) = K i (Sum.elim base y) := by
    apply hn i
    intro v hv
    cases v with
    | inl j => exact False.elim (hind i j hv)
    | inr j => rfl
  rw [hl y x i, hk]

/-- Graph Markov locality and an independent set imply actual joint factorization. -/
theorem independent_set_factorization
    (p : FiniteReportLaw ((C → X) × (D → X))) (hp : ∀ y x, 0 < p.mass (y, x))
    (adj : (D ⊕ C) → (D ⊕ C) → Prop)
    (hind : ∀ i j, ¬ adj (Sum.inl i) (Sum.inl j))
    (K : D → ((D ⊕ C) → X) → FiniteReportLaw X)
    (hn : NeighborLocal adj K) (hl : GraphLocalCondition p K) (base : D → X) :
    p = separatorLaw (complementLaw p) (fun y i ↦ K i (Sum.elim base y)) :=
  local_implies_separator p hp _ (independent_set_local_condition p adj hind K hn hl base)

/-- Full graph-phase attenuation for an independent set, with no independence postulate. -/
theorem independent_set_attenuation
    (p : FiniteReportLaw ((C → X) × (D → X))) (hp : ∀ y x, 0 < p.mass (y, x))
    (adj : (D ⊕ C) → (D ⊕ C) → Prop)
    (hind : ∀ i j, ¬ adj (Sum.inl i) (Sum.inl j))
    (K : D → ((D ⊕ C) → X) → FiniteReportLaw X)
    (hn : NeighborLocal adj K) (hl : GraphLocalCondition p K)
    (ν : D → FiniteReportLaw X) (η : D → ℝ)
    (hη : ∀ i, 0 ≤ η i) (hηone : ∀ i, η i ≤ 1)
    (hminor : ∀ f i x, η i * (ν i).mass x ≤ (K i f).mass x)
    (z : (D ⊕ C) → X → ℂ) (hz : ∀ v x, ‖z v x‖ ≤ 1) :
    ‖phaseMean p (fun yx ↦ ∏ v, z v (Sum.elim yx.2 yx.1 v))‖ ≤
      Real.exp (-∑ i, η i * (1 - ‖phaseMean (ν i) (z (Sum.inl i))‖)) := by
  classical
  let base : D → X := fun _ ↦ Classical.choice inferInstance
  have hphase : (fun yx : (C → X) × (D → X) ↦ ∏ v, z v (Sum.elim yx.2 yx.1 v)) =
      fun yx ↦ (∏ j : C, z (Sum.inr j) (yx.1 j)) * ∏ i : D, z (Sum.inl i) (yx.2 i) := by
    funext yx
    rw [Fintype.prod_sum_type]
    exact mul_comm _ _
  rw [hphase]
  have hcomp : ∀ y : C → X, ‖∏ j : C, z (Sum.inr j) (y j)‖ ≤ 1 := by
    intro y
    rw [norm_prod]
    simpa using (Finset.prod_le_prod (fun j _ ↦ norm_nonneg (z (Sum.inr j) (y j)))
      (fun j _ ↦ hz (Sum.inr j) (y j)))
  exact local_markov_attenuation p hp (fun y i ↦ K i (Sum.elim base y))
    (independent_set_local_condition p adj hind K hn hl base) ν η hη hηone
    (fun y i x ↦ hminor (Sum.elim base y) i x)
    (fun y ↦ ∏ j : C, z (Sum.inr j) (y j)) hcomp
    (fun i ↦ z (Sum.inl i)) (fun i x ↦ hz (Sum.inl i) x)

end Graph

end Descent.Portability.MarkovSeparatorLaw
