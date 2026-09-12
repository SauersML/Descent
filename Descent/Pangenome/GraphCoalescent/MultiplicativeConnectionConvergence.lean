/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.GraphCoalescent.MultiplicativeConnectionLimit

assert_below Descent.PopGen Descent.Spectral Descent.Blindness Descent.Conditionals
assert_below Descent.Portability Descent.Decision Descent.Program

/-!
# (F3): the scaled connection clock of a compressed pangenome converges to `T_p`

Theorem F of the hidden-clock note ends with

  `n² τ_{q_n} ⇒ T_p`   (fixed `w`),                                                    (F3)

where `T_p` is the connection time of the random graph on the `w` fibers whose edge `{i, j}`
switches on at an independent exponential clock of rate `p_i p_j`, and `p` is the limit of the
fiber proportions `p^(n)_i = c_i/n`.  `MultiplicativeConnectionLaw.connectionProbability p u` is
`Pr(T_p ≤ u)`, with its Möbius law (F4).

`Descent.Pangenome.GraphCoalescent.MultiplicativeConnectionLimit` puts the probability that the
graph's report is connected at scaled time `U` within `U²/(4n)` of a Möbius sum over the
partitions of the individuals above the interface.  This file transports that sum to the fiber
labels, where it is `connectionProbability p^(n) U`, and takes the limit.

## The transport

An interface with `w` fibers is a surjective labelling `label : Fin n → Fin w`
(`labelInterface`, `graphKer_labelInterface`).  The partitions above it are the pull-backs of the
partitions of the labels (`ker_le_comap`, `comap_label_injective`,
`comap_mapOfSurjective_label`), a pull-back has as many blocks as the partition it pulls back
(`blocks_comap_label`), and its crossing mass in individuals is the crossing rate of the fiber
proportions (`two_mul_pairProductSum_comap_label`, `two_mul_crossingRate`).  So the Möbius sum is
`connectionProbability (fiberProportion label) U` (`sum_topMobius_graphKer_labelInterface`).

## Main results

- `abs_reportConnectionProbability_sub_connectionProbability_le`: at scaled time `U`, the report
  is connected with probability within `U²/(4n)` of `Pr(T_{p^(n)} ≤ U)`.
- `tendsto_reportConnectionProbability`: **(F3)**.  Along panels `n_k → ∞` with `w` fibers whose
  proportions converge to `p`, the probability that the report is connected at scaled time `U`
  converges to `Pr(T_p ≤ U)`, for every `U ≥ 0`.

## Scope

Time is the rate-one uniformization in scaled time of
`Descent.Pangenome.GraphCoalescent.MultiplicativeCoupling`, and the report only coarsens, so being
connected at scaled time `U` is `n² τ_q ≤ U` for that construction.  The limit is the pointwise
convergence of the distribution functions at every `U ≥ 0`; since the limit distribution function
is continuous, that is convergence in distribution, and the passage from one to the other is not
restated here.

## Empirical status

None.  Every declaration here is a finite sum over equivalence relations on a finite set, a Poisson
series, or a limit of such sums.  The reading of a labelling as a real graph's interface is stated
in `Descent.Pangenome.GraphCoalescent.Observation` and is not asserted of any dataset.
-/

namespace Descent.Pangenome.GraphCoalescent

open Coalescent Finset Filter Topology

open scoped Classical

noncomputable section

/-! ### Interfaces from fiber labels -/

/-- **The interface of a fiber labelling**: every haplotype is sent to a fixed representative of
its label, so two haplotypes share a graph state exactly when they share a label.

Empirical status: NOT AN EMPIRICAL CLAIM.  A composite of a labelling with a section. -/
def labelInterface {n w : ℕ} (label : Fin n → Fin w) (hsurj : Function.Surjective label) :
    Fin n → Fin n :=
  Function.surjInv hsurj ∘ label

/-- The graph's merge at a labelling's interface is the kernel of the labelling. -/
theorem graphKer_labelInterface {n w : ℕ} (label : Fin n → Fin w)
    (hsurj : Function.Surjective label) :
    graphKer (labelInterface label hsurj) = Setoid.ker label := by
  refine Setoid.ext fun x y ↦ ?_
  show (graphKer (labelInterface label hsurj)).r x y ↔ label x = label y
  rw [graphKer_rel_iff]
  exact (Function.injective_surjInv hsurj).eq_iff

/-- **The fiber proportions** `p_i = c_i/n` of a labelling.

Empirical status: NOT AN EMPIRICAL CLAIM.  A count divided by the panel size. -/
def fiberProportion {n w : ℕ} (label : Fin n → Fin w) (i : Fin w) : ℝ :=
  ((univ.filter fun x ↦ label x = i).card : ℝ) / n

/-! ### Partitions above the interface are partitions of the labels -/

/-- A pulled-back partition lies above the interface. -/
theorem ker_le_comap {n w : ℕ} (label : Fin n → Fin w) (τ : ER w) :
    Setoid.ker label ≤ Setoid.comap label τ := by
  intro x y hxy
  have hl : label x = label y := hxy
  show τ.r (label x) (label y)
  rw [hl]
  exact τ.iseqv.refl _

/-- Pulling back along a surjective labelling forgets nothing. -/
theorem comap_label_injective {n w : ℕ} {label : Fin n → Fin w}
    (hsurj : Function.Surjective label) :
    Function.Injective (fun τ : ER w ↦ Setoid.comap label τ) := by
  intro τ₁ τ₂ h
  have h' : Setoid.comap label τ₁ = Setoid.comap label τ₂ := h
  refine Setoid.ext fun i j ↦ ?_
  obtain ⟨x, rfl⟩ := hsurj i
  obtain ⟨y, rfl⟩ := hsurj j
  have hxy : (Setoid.comap label τ₁).r x y ↔ (Setoid.comap label τ₂).r x y := by rw [h']
  exact hxy

/-- Every partition above the interface is a pull-back. -/
theorem comap_mapOfSurjective_label {n w : ℕ} {label : Fin n → Fin w}
    (hsurj : Function.Surjective label) {σ : ER n} (h : Setoid.ker label ≤ σ) :
    Setoid.comap label (Setoid.mapOfSurjective σ label h hsurj) = σ := by
  refine Setoid.ext fun x y ↦ ?_
  show Relation.Map σ.r label label (label x) (label y) ↔ σ.r x y
  constructor
  · rintro ⟨a, b, hab, ha, hb⟩
    exact σ.iseqv.trans (σ.iseqv.symm (h ha)) (σ.iseqv.trans hab (h hb))
  · intro hxy
    exact ⟨x, y, hxy, rfl, rfl⟩

/-- **A pull-back has as many blocks as the partition it pulls back.** -/
theorem blocks_comap_label {n w : ℕ} {label : Fin n → Fin w}
    (hsurj : Function.Surjective label) (τ : ER w) :
    blocks (Setoid.comap label τ) = blocks τ := by
  let f : Quotient (Setoid.comap label τ) → Quotient τ :=
    Quotient.lift (fun x ↦ Quotient.mk τ (label x)) fun _ _ hab ↦ Quotient.sound hab
  have hbij : Function.Bijective f := by
    constructor
    · intro q₁ q₂ hq
      obtain ⟨x, rfl⟩ := quotient_mk_surjective _ q₁
      obtain ⟨y, rfl⟩ := quotient_mk_surjective _ q₂
      have hq' : Quotient.mk τ (label x) = Quotient.mk τ (label y) := hq
      exact Quotient.sound (Quotient.exact hq')
    · intro q
      obtain ⟨i, rfl⟩ := quotient_mk_surjective τ q
      obtain ⟨x, rfl⟩ := hsurj i
      exact ⟨Quotient.mk _ x, rfl⟩
  exact Nat.card_eq_of_bijective f hbij

/-! ### The crossing mass in fiber proportions -/

/-- **The crossing mass of a pull-back, in fiber proportions.** -/
theorem two_mul_pairProductSum_comap_label {n w : ℕ} (label : Fin n → Fin w) (τ : ER w) :
    2 * pairProductSum (blockMass (unitMass n) (Setoid.comap label τ))
      = ∑ i, ∑ j, if τ.r i j then 0 else fiberProportion label i * fiberProportion label j := by
  have hconst : ∀ i j : Fin w, ∑ x ∈ univ.filter (fun x ↦ label x = i),
      ∑ y ∈ univ.filter (fun y ↦ label y = j),
        (if (Setoid.comap label τ).r x y then (0 : ℝ) else unitMass n x * unitMass n y)
      = if τ.r i j then 0 else fiberProportion label i * fiberProportion label j := by
    intro i j
    have hpoint : ∀ x ∈ univ.filter (fun x ↦ label x = i),
        ∀ y ∈ univ.filter (fun y ↦ label y = j),
        (if (Setoid.comap label τ).r x y then (0 : ℝ) else unitMass n x * unitMass n y)
          = if τ.r i j then 0 else 1 / (n : ℝ) * (1 / n) := by
      intro x hx y hy
      have hxi : label x = i := (Finset.mem_filter.mp hx).2
      have hyj : label y = j := (Finset.mem_filter.mp hy).2
      show (if τ.r (label x) (label y) then (0 : ℝ) else 1 / (n : ℝ) * (1 / n)) = _
      rw [hxi, hyj]
    rw [Finset.sum_congr rfl fun x hx ↦ Finset.sum_congr rfl (hpoint x hx), Finset.sum_const,
      Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul]
    simp only [fiberProportion]
    split_ifs <;> ring
  rw [two_mul_pairProductSum_blockMass_unitMass]
  calc ∑ x, ∑ y, (if (Setoid.comap label τ).r x y then (0 : ℝ) else unitMass n x * unitMass n y)
      = ∑ i, ∑ x ∈ univ.filter (fun x ↦ label x = i), ∑ j,
          ∑ y ∈ univ.filter (fun y ↦ label y = j),
            (if (Setoid.comap label τ).r x y then (0 : ℝ) else unitMass n x * unitMass n y) := by
        refine (Finset.sum_fiberwise univ label _).symm.trans ?_
        exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun x _ ↦
          (Finset.sum_fiberwise univ label _).symm
    _ = ∑ i, ∑ j, ∑ x ∈ univ.filter (fun x ↦ label x = i),
          ∑ y ∈ univ.filter (fun y ↦ label y = j),
            (if (Setoid.comap label τ).r x y then (0 : ℝ) else unitMass n x * unitMass n y) :=
        Finset.sum_congr rfl fun i _ ↦ Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ hconst i j

/-- **The crossing rate of the random graph, twice, as a sum over ordered pairs of labels.** -/
theorem two_mul_crossingRate {w : ℕ} (p : Fin w → ℝ) (τ : ER w) :
    2 * crossingRate p τ = ∑ i, ∑ j, if τ.r i j then 0 else p i * p j := by
  set g : Fin w → Fin w → ℝ := fun i j ↦ if τ.r i j then 0 else p i * p j with hg
  have hsymm : ∀ i j, g i j = g j i := by
    intro i j
    simp only [hg]
    by_cases h : τ.r i j
    · rw [if_pos h, if_pos (τ.iseqv.symm h)]
    · rw [if_neg h, if_neg fun h' ↦ h (τ.iseqv.symm h'), mul_comm]
  have hdiag : ∀ i, g i i = 0 := fun i ↦ by
    simp only [hg]
    exact if_pos (τ.iseqv.refl i)
  have hcr : crossingRate p τ
      = ∑ x ∈ univ.filter (fun x : Fin w × Fin w ↦ x.1 < x.2), g x.1 x.2 := by
    show ∑ e : FiberPair w, g e.1.1 e.1.2 = _
    exact (Finset.sum_subtype _ (fun x ↦ by simp) fun x ↦ g x.1 x.2).symm
  have hprod : ∑ i, ∑ j, g i j = ∑ x : Fin w × Fin w, g x.1 x.2 := by
    rw [← Finset.univ_product_univ]
    exact (Finset.sum_product' _ _ g).symm
  have hle : ∑ x ∈ univ.filter (fun x : Fin w × Fin w ↦ ¬ x.1 < x.2), g x.1 x.2
      = ∑ x ∈ univ.filter (fun x : Fin w × Fin w ↦ x.2 < x.1), g x.1 x.2 := by
    rw [← Finset.sum_filter_add_sum_filter_not
      (univ.filter fun x : Fin w × Fin w ↦ ¬ x.1 < x.2) (fun x ↦ x.2 < x.1)]
    have hzero : ∑ x ∈ (univ.filter fun x : Fin w × Fin w ↦ ¬ x.1 < x.2).filter
        (fun x ↦ ¬ x.2 < x.1), g x.1 x.2 = 0 := by
      refine Finset.sum_eq_zero fun x hx ↦ ?_
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hx
      rw [le_antisymm hx.2 hx.1]
      exact hdiag _
    rw [hzero, add_zero, Finset.filter_filter]
    refine Finset.sum_congr (Finset.ext fun x ↦ ?_) fun _ _ ↦ rfl
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun h ↦ h.2, fun h ↦ ⟨not_lt.mpr h.le, h⟩⟩
  have hswap : ∑ x ∈ univ.filter (fun x : Fin w × Fin w ↦ x.2 < x.1), g x.1 x.2
      = ∑ x ∈ univ.filter (fun x : Fin w × Fin w ↦ x.1 < x.2), g x.1 x.2 := by
    refine Finset.sum_nbij' Prod.swap Prod.swap ?_ ?_ ?_ ?_ ?_
    · intro x hx
      simpa using hx
    · intro x hx
      simpa using hx
    · intro x _
      rfl
    · intro x _
      rfl
    · intro x _
      exact hsymm x.1 x.2
  have hsplit : ∑ i, ∑ j, g i j
      = ∑ x ∈ univ.filter (fun x : Fin w × Fin w ↦ x.1 < x.2), g x.1 x.2
        + ∑ x ∈ univ.filter (fun x : Fin w × Fin w ↦ x.2 < x.1), g x.1 x.2 := by
    rw [hprod, ← Finset.sum_filter_add_sum_filter_not univ
      (fun x : Fin w × Fin w ↦ x.1 < x.2), hle]
  rw [hcr, hsplit, hswap]
  ring

/-! ### The Möbius sum is the random-graph law -/

/-- **The Möbius sum over the partitions above a labelling's interface is `Pr(T_{p^(n)} ≤ U)`.** -/
theorem sum_topMobius_graphKer_labelInterface {n w : ℕ} [NeZero w] (label : Fin n → Fin w)
    (hsurj : Function.Surjective label) (U : NNReal) :
    ∑ σ : ER n, (topMobius (blocks σ) : ℝ)
        * (if graphKer (labelInterface label hsurj) ≤ σ then
            Real.exp (-((U : ℝ) * pairProductSum (blockMass (unitMass n) σ))) else 0)
      = connectionProbability (fiberProportion label) U := by
  rw [connectionProbability_eq_mobius_sum, graphKer_labelInterface]
  have hleft : ∑ σ : ER n, (topMobius (blocks σ) : ℝ)
        * (if Setoid.ker label ≤ σ then
            Real.exp (-((U : ℝ) * pairProductSum (blockMass (unitMass n) σ))) else 0)
      = ∑ σ ∈ univ.filter (Setoid.ker label ≤ ·), (topMobius (blocks σ) : ℝ)
          * Real.exp (-((U : ℝ) * pairProductSum (blockMass (unitMass n) σ))) := by
    rw [Finset.sum_filter]
    exact Finset.sum_congr rfl fun σ _ ↦ by split_ifs <;> simp
  rw [hleft]
  symm
  refine Finset.sum_nbij (fun τ ↦ Setoid.comap label τ) (fun τ _ ↦ ?_) ?_ ?_ fun τ _ ↦ ?_
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ker_le_comap label τ⟩
  · exact (comap_label_injective hsurj).injOn
  · intro σ hσ
    have hle := (Finset.mem_filter.mp (Finset.mem_coe.mp hσ)).2
    exact ⟨Setoid.mapOfSurjective σ label hle hsurj, Finset.mem_coe.mpr (Finset.mem_univ _),
      comap_mapOfSurjective_label hsurj hle⟩
  · have hκ : pairProductSum (blockMass (unitMass n) (Setoid.comap label τ))
        = crossingRate (fiberProportion label) τ := by
      have h1 := two_mul_pairProductSum_comap_label label τ
      have h2 := two_mul_crossingRate (fiberProportion label) τ
      linarith
    rw [blocks_comap_label hsurj τ, hκ]

/-- **(F3), quantitative, on the fiber labels.**  At scaled time `U` the graph's report is
connected with probability within `U²/(4n)` of `Pr(T_{p^(n)} ≤ U)`, the connection probability of
the random graph on the fibers with the fiber proportions of the panel.

Assumes: `0 < n`. -/
theorem abs_reportConnectionProbability_sub_connectionProbability_le {n w : ℕ} [NeZero w]
    (hn : 0 < n) (label : Fin n → Fin w) (hsurj : Function.Surjective label) (U : NNReal) :
    |reportConnectionProbability (labelInterface label hsurj) U
        - connectionProbability (fiberProportion label) U| ≤ (U : ℝ) ^ 2 / (4 * n) := by
  rw [← sum_topMobius_graphKer_labelInterface label hsurj U]
  exact abs_reportConnectionProbability_sub_le hn (labelInterface label hsurj) U

/-! ### The limit -/

/-- The random-graph connection probability depends continuously on the fiber proportions. -/
theorem continuous_connectionProbability {w : ℕ} [NeZero w] (U : NNReal) :
    Continuous fun p : Fin w → ℝ ↦ connectionProbability p U := by
  simp only [connectionProbability_eq_mobius_sum]
  refine continuous_finset_sum _ fun σ _ ↦ continuous_const.mul
    (Real.continuous_exp.comp ((continuous_const.mul ?_).neg))
  show Continuous fun p : Fin w → ℝ ↦
    ∑ e : FiberPair w, if σ e.1.1 e.1.2 then 0 else pairRate p e
  refine continuous_finset_sum _ fun e _ ↦ ?_
  by_cases h : σ e.1.1 e.1.2
  · simp only [if_pos h]
    exact continuous_const
  · simp only [if_neg h, pairRate]
    exact (continuous_apply _).mul (continuous_apply _)

/-- **Theorem F, (F3).**  Along panels of sizes `N k → ∞` carrying surjective labellings into `w`
fibers whose proportions converge to `p`, the probability that the graph's report is connected at
scaled time `U` converges to `Pr(T_p ≤ U)`, the connection probability of the random graph on the
fibers with edge rates `p_i p_j`. -/
theorem tendsto_reportConnectionProbability {w : ℕ} [NeZero w] {N : ℕ → ℕ}
    (hN : Tendsto N atTop atTop) (label : (k : ℕ) → Fin (N k) → Fin w)
    (hsurj : ∀ k, Function.Surjective (label k)) {p : Fin w → ℝ}
    (hp : Tendsto (fun k ↦ fiberProportion (label k)) atTop (𝓝 p)) (U : NNReal) :
    Tendsto (fun k ↦ reportConnectionProbability (labelInterface (label k) (hsurj k)) U) atTop
      (𝓝 (connectionProbability p U)) := by
  have hpos : ∀ k, 0 < N k := fun k ↦ by
    obtain ⟨x, -⟩ := hsurj k 0
    exact lt_of_le_of_lt (Nat.zero_le _) x.isLt
  have hlim := ((continuous_connectionProbability U).tendsto p).comp hp
  have hbound : ∀ k, ‖reportConnectionProbability (labelInterface (label k) (hsurj k)) U
      - connectionProbability (fiberProportion (label k)) U‖ ≤ (U : ℝ) ^ 2 / 4 / (N k : ℝ) := by
    intro k
    rw [Real.norm_eq_abs, div_div]
    exact abs_reportConnectionProbability_sub_connectionProbability_le (hpos k) (label k)
      (hsurj k) U
  have hzero : Tendsto (fun k ↦ (U : ℝ) ^ 2 / 4 / (N k : ℝ)) atTop (𝓝 0) :=
    (tendsto_const_div_atTop_nhds_zero_nat ((U : ℝ) ^ 2 / 4)).comp hN
  refine (hlim.add (squeeze_zero_norm hbound hzero)).congr fun k ↦ ?_
  simp only [Function.comp_apply]
  ring

end

end Descent.Pangenome.GraphCoalescent
