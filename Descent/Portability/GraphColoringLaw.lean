/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.MarkovSeparatorLaw

assert_below Descent.Decision Descent.Program

/-!
Reindexing an arbitrary finite graph into a chosen independent set and its
complement, without changing its probability law or its joint phase. Proper
colorings then provide the stated total-weight divided by color-count bound.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.GraphColoringLaw

open ConditionalSeparatorLaw MarkovSeparatorLaw

variable {V D C X : Type*} [Fintype V] [Fintype D] [Fintype C] [Fintype X]
  [DecidableEq V] [DecidableEq D] [DecidableEq C]

/-- Assemble the same genotype configuration after partitioning and reindexing vertices. -/
def assembleEquiv (e : D ⊕ C ≃ V) : ((C → X) × (D → X)) ≃ (V → X) where
  toFun yx v := Sum.elim yx.2 yx.1 (e.symm v)
  invFun f := (fun j ↦ f (e (Sum.inr j)), fun i ↦ f (e (Sum.inl i)))
  left_inv yx := by ext <;> simp
  right_inv f := by
    funext v
    obtain ⟨w, rfl⟩ := e.surjective v
    cases w <;> simp

omit [Fintype V] [Fintype D] [Fintype C] [Fintype X] [DecidableEq C] in
/-- Reindexing carries each one-site update to the identical update at its original vertex. -/
theorem assemble_update (e : D ⊕ C ≃ V) (y : C → X) (x : D → X) (i : D) (a : X) :
    assembleEquiv e (y, Function.update x i a) =
      Function.update (assembleEquiv e (y, x)) (e (Sum.inl i)) a := by
  funext v
  obtain ⟨w, rfl⟩ := e.surjective v
  cases w with
  | inl j =>
    by_cases hji : j = i
    · subst j
      simp [assembleEquiv]
    · simp [assembleEquiv, hji, Function.update_of_ne]
  | inr j => simp [assembleEquiv, Function.update_of_ne]

/-- Pullback along a configuration equivalence preserves the full probability law. -/
noncomputable def partitionLaw (p : FiniteReportLaw (V → X)) (e : D ⊕ C ≃ V) :
    FiniteReportLaw ((C → X) × (D → X)) where
  mass yx := p.mass (assembleEquiv e yx)
  mass_nonneg yx := p.mass_nonneg _
  mass_sum := by rw [Equiv.sum_comp (assembleEquiv e), p.mass_sum]

/-- The whole-graph complex phase is invariant under this reindexing. -/
theorem partition_phase (p : FiniteReportLaw (V → X)) (e : D ⊕ C ≃ V)
    (z : V → X → ℂ) :
    phaseMean (partitionLaw p e) (fun yx ↦ ∏ w, z (e w) (Sum.elim yx.2 yx.1 w)) =
      phaseMean p (fun f ↦ ∏ v, z v (f v)) := by
  have hphase : ∀ yx : (C → X) × (D → X),
      (∏ w, z (e w) (Sum.elim yx.2 yx.1 w)) =
        ∏ v, z v (assembleEquiv e yx v) := by
    intro yx
    have h := Equiv.prod_comp e (fun v ↦ z v (assembleEquiv e yx v))
    simpa [assembleEquiv] using h
  simp_rw [phaseMean, partitionLaw, hphase]
  exact Equiv.sum_comp (assembleEquiv e) (fun f ↦ (p.mass f : ℂ) * ∏ v, z v (f v))

/-- Finite graph locality is a statement about the actual single-site conditional kernels. -/
def FullNeighborLocal (adj : V → V → Prop)
    (K : V → (V → X) → FiniteReportLaw X) : Prop :=
  ∀ v f g, (∀ w, adj v w → f w = g w) → K v f = K v g

/-- The full one-site conditional equation of a finite Markov random field. -/
def FullLocalCondition (p : FiniteReportLaw (V → X))
    (K : V → (V → X) → FiniteReportLaw X) : Prop :=
  ∀ f v, p.mass f = (K v f).mass (f v) * ∑ a : X, p.mass (Function.update f v a)

/-- Arbitrary independent sets can be reindexed without changing the attenuation endpoint. -/
theorem reindexed_independent_attenuation [Nonempty X]
    (p : FiniteReportLaw (V → X)) (hp : ∀ f, 0 < p.mass f)
    (adj : V → V → Prop) (K : V → (V → X) → FiniteReportLaw X)
    (hn : FullNeighborLocal adj K) (hl : FullLocalCondition p K)
    (e : D ⊕ C ≃ V) (hind : ∀ i j, ¬ adj (e (Sum.inl i)) (e (Sum.inl j)))
    (ν : V → FiniteReportLaw X) (η : V → ℝ)
    (hη : ∀ v, 0 ≤ η v) (hηone : ∀ v, η v ≤ 1)
    (hminor : ∀ f v a, η v * (ν v).mass a ≤ (K v f).mass a)
    (z : V → X → ℂ) (hz : ∀ v a, ‖z v a‖ ≤ 1) :
    ‖phaseMean p (fun f ↦ ∏ v, z v (f v))‖ ≤
      Real.exp (-∑ i : D, η (e (Sum.inl i)) *
        (1 - ‖phaseMean (ν (e (Sum.inl i))) (z (e (Sum.inl i)))‖)) := by
  let K' : D → ((D ⊕ C) → X) → FiniteReportLaw X :=
    fun i f ↦ K (e (Sum.inl i)) (fun v ↦ f (e.symm v))
  have hn' : NeighborLocal (fun v w ↦ adj (e v) (e w)) K' := by
    intro i f g hfg
    apply hn
    intro v hv
    exact hfg (e.symm v) (by simpa using hv)
  have hl' : GraphLocalCondition (partitionLaw p e) K' := by
    intro y x i
    have h := hl (assembleEquiv e (y, x)) (e (Sum.inl i))
    change p.mass (assembleEquiv e (y, x)) =
      (K (e (Sum.inl i)) (assembleEquiv e (y, x))).mass (x i) *
        ∑ a, p.mass (assembleEquiv e (y, Function.update x i a))
    simp_rw [assemble_update]
    have heval : assembleEquiv e (y, x) (e (Sum.inl i)) = x i := by
      change Sum.elim x y (e.symm (e (Sum.inl i))) = x i
      rw [e.symm_apply_apply]
      rfl
    rw [heval] at h
    exact h
  rw [← partition_phase p e z]
  exact independent_set_attenuation (partitionLaw p e) (fun y x ↦ hp _) _ hind K' hn' hl'
    (fun i ↦ ν (e (Sum.inl i))) (fun i ↦ η (e (Sum.inl i)))
    (fun i ↦ hη _) (fun i ↦ hηone _)
    (fun f i a ↦ hminor (fun v ↦ f (e.symm v)) (e (Sum.inl i)) a)
    (fun w ↦ z (e w)) (fun w a ↦ hz (e w) a)

section Coloring

variable {Color : Type*} [Fintype Color] [DecidableEq Color] [Nonempty Color]

/-- Total weight carried by one color class. -/
noncomputable def classWeight (color : V → Color) (w : V → ℝ) (c : Color) : ℝ :=
  ∑ v, if color v = c then w v else 0

omit [DecidableEq V] [Fintype Color] [Nonempty Color] in
theorem classWeight_subtype (color : V → Color) (w : V → ℝ) (c : Color) :
    classWeight color w c = ∑ v : {v // color v = c}, w v := by
  unfold classWeight
  rw [← Finset.sum_filter]
  exact Finset.sum_subtype _ (by simp) w

omit [DecidableEq V] [Nonempty Color] in
theorem classWeight_sum (color : V → Color) (w : V → ℝ) :
    (∑ c, classWeight color w c) = ∑ v, w v := by
  unfold classWeight
  rw [Finset.sum_comm]
  simp

omit [DecidableEq V] in
/-- At least one color class carries at least the average share of total weight. -/
theorem exists_average_color (color : V → Color) (w : V → ℝ) :
    ∃ c, (∑ v, w v) / Fintype.card Color ≤ classWeight color w c := by
  classical
  by_contra h
  push_neg at h
  let c : Color := Classical.choice inferInstance
  have hsum := Finset.sum_lt_sum (fun j (_ : j ∈ (Finset.univ : Finset Color)) ↦ (h j).le)
    ⟨c, Finset.mem_univ c, h c⟩
  have havg : (∑ _ : Color, (∑ v, w v) / (Fintype.card Color : ℝ)) = ∑ v, w v := by
    have hc : (Fintype.card Color : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp
  rw [classWeight_sum, havg] at hsum
  exact lt_irrefl _ hsum

/-- Proper graph coloring yields the full joint-phase bound with total weight divided by χ. -/
theorem proper_coloring_attenuation [Nonempty X]
    (p : FiniteReportLaw (V → X)) (hp : ∀ f, 0 < p.mass f)
    (adj : V → V → Prop) (K : V → (V → X) → FiniteReportLaw X)
    (hn : FullNeighborLocal adj K) (hl : FullLocalCondition p K)
    (color : V → Color) (hproper : ∀ v w, adj v w → color v ≠ color w)
    (ν : V → FiniteReportLaw X) (η : V → ℝ)
    (hη : ∀ v, 0 ≤ η v) (hηone : ∀ v, η v ≤ 1)
    (hminor : ∀ f v a, η v * (ν v).mass a ≤ (K v f).mass a)
    (z : V → X → ℂ) (hz : ∀ v a, ‖z v a‖ ≤ 1) :
    ‖phaseMean p (fun f ↦ ∏ v, z v (f v))‖ ≤
      Real.exp (-(∑ v, η v * (1 - ‖phaseMean (ν v) (z v)‖)) / Fintype.card Color) := by
  classical
  let w := fun v ↦ η v * (1 - ‖phaseMean (ν v) (z v)‖)
  have hcolor : ∀ c, ‖phaseMean p (fun f ↦ ∏ v, z v (f v))‖ ≤
      Real.exp (-classWeight color w c) := by
    intro c
    have hind : ∀ i j : {v // color v = c}, ¬ adj i.val j.val := by
      intro i j hij
      exact hproper i.val j.val hij (i.property.trans j.property.symm)
    have h := reindexed_independent_attenuation p hp adj K hn hl
      (Equiv.sumCompl (fun v ↦ color v = c)) hind ν η hη hηone hminor z hz
    rw [classWeight_subtype]
    simpa only [Equiv.sumCompl_apply_inl] using h
  obtain ⟨c, hc⟩ := exists_average_color color w
  apply (hcolor c).trans
  apply Real.exp_le_exp.mpr
  dsimp only [w] at hc
  simpa only [neg_div] using neg_le_neg hc

end Coloring

end Descent.Portability.GraphColoringLaw
