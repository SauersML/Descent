/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.GraphCoalescent.MultiplicativeConnectionLaw

assert_below Descent.PopGen Descent.Spectral Descent.Blindness Descent.Conditionals
assert_below Descent.Portability Descent.Decision Descent.Program

/-!
# Two and three fibers: explicit connection laws of the multiplicative clock

Theorem F of the pangenome hidden-clock note states, after (F4), the two smallest cases of the
connection time `T_p`: on two fibers `T_p` is exponential with rate `p₁ p₂`, and on three
fibers of equal mass `Pr(T_p > u) = 3 e^(−2u/9) − 2 e^(−u/3)`. This module proves both for the
random graph of `MultiplicativeConnectionLaw`, whose edge `{i, j}` is present at time `u` with
probability `1 − e^(−u p_i p_j)` independently.

On two fibers the graph has one edge (`uniqueFiberPairTwo`), the components are the top
partition exactly when that edge is present (`componentPartition_two_eq_top_iff`), and
`connectionProbability_two` gives `1 − e^(−u p₀ p₁)`.

On three fibers the computation is inclusion–exclusion over the events that a fiber is
isolated. `isolatePartition i` separates fiber `i` from the other two. Every partition of three
fibers is the top partition or refines some isolation (`eq_top_or_le_isolatePartition`), and
two isolations of distinct fibers together force the bottom partition
(`le_bot_of_le_isolatePartition`). So the indicator of connection is one minus the three
isolation indicators plus twice the indicator of the empty graph (`top_indicator_three`), and
`connectionProbability_three` writes the connection probability through the crossing rates of
the isolations and of the bottom partition, for arbitrary masses. At equal masses those rates
are `2/9` and `1/3`, and `connectionSurvival_three_equal` is the formula of the note.

Both evaluations are derived from the random graph directly, through
`MultiplicativeConnectionLaw.sum_configMass_componentPartition_le`, rather than by enumerating
the partitions in the Möbius sum of (F4).

## Empirical status

None. The bodies here are algebra: each statement evaluates a finite sum over the edge
configurations of a graph on two or three vertices, so no measurement on any pangenome can bear
on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Pangenome.GraphCoalescent

open Coalescent Finset
open scoped Classical

noncomputable section

/-- The complete graph on two fibers has exactly one edge. -/
instance uniqueFiberPairTwo : Unique (FiberPair 2) where
  default := ⟨(0, 1), by decide⟩
  uniq := by
    rintro ⟨⟨a, b⟩, hab⟩
    apply Subtype.ext
    fin_cases a <;> fin_cases b <;> first | rfl | exact absurd hab (by decide)

/-- On two fibers the graph is connected exactly when its one edge is present. -/
theorem componentPartition_two_eq_top_iff (G : FiberPair 2 → Bool) :
    componentPartition G = ⊤ ↔ G default = true := by
  constructor
  · intro htop
    by_contra habsent
    have hle : componentPartition G ≤ ⊥ := by
      rw [componentPartition_le_iff]
      intro e he
      rw [Unique.eq_default e] at he
      exact absurd he habsent
    rw [htop] at hle
    have hbot : (⊥ : ER 2) 0 1 := hle trivial
    have hzeroOne : (0 : Fin 2) = 1 := hbot
    exact absurd hzeroOne (by decide)
  · intro hpresent
    rw [Setoid.eq_top_iff]
    have hadj : configAdjacent G 0 1 := ⟨default, hpresent, Or.inl ⟨rfl, rfl⟩⟩
    have hjoin : componentPartition G 0 1 := Relation.EqvGen.rel _ _ hadj
    intro a b
    fin_cases a <;> fin_cases b
    · exact (componentPartition G).refl' 0
    · exact hjoin
    · exact (componentPartition G).symm' hjoin
    · exact (componentPartition G).refl' 1

/-- **Two fibers.** The connection time on two fibers is exponential with rate `p₀ p₁`:
`Pr(T_p ≤ u) = 1 − e^(−u p₀ p₁)`. -/
theorem connectionProbability_two (p : Fin 2 → ℝ) (u : ℝ) :
    connectionProbability p u = 1 - Real.exp (-(u * (p 0 * p 1))) := by
  have hterm : ∀ G : FiberPair 2 → Bool,
      configMass p u G * (if componentPartition G = ⊤ then 1 else 0) =
        (if G default then 1 - Real.exp (-(u * (p 0 * p 1)))
          else Real.exp (-(u * (p 0 * p 1)))) * (if G default = true then 1 else 0) := by
    intro G
    rw [configMass, Fintype.prod_unique,
      if_congr (componentPartition_two_eq_top_iff G) rfl rfl]
    rfl
  unfold connectionProbability
  rw [Fintype.sum_equiv (Equiv.funUnique (FiberPair 2) Bool) _
    (fun b : Bool ↦ (if b then 1 - Real.exp (-(u * (p 0 * p 1)))
      else Real.exp (-(u * (p 0 * p 1)))) * (if b = true then 1 else 0)) hterm,
    Fintype.sum_bool]
  simp

/-- The partition of three fibers that separates fiber `i` from the other two. -/
def isolatePartition (i : Fin 3) : ER 3 := Setoid.ker fun j : Fin 3 ↦ (j = i)

/-- Two fibers lie in one block of the isolation of `i` exactly when both are `i` or neither
is. -/
theorem isolatePartition_rel (i a b : Fin 3) :
    isolatePartition i a b ↔ (a = i ↔ b = i) := by
  rw [isolatePartition, Setoid.ker_def, eq_iff_iff]

/-- A partition of three fibers in which fiber `i` is related to no other fiber refines the
isolation of `i`. -/
theorem le_isolatePartition {σ : ER 3} {i : Fin 3} (hisolated : ∀ x, x ≠ i → ¬ σ i x) :
    σ ≤ isolatePartition i := by
  intro x y hxy
  rw [isolatePartition_rel]
  constructor
  · intro hx
    subst hx
    by_contra hy
    exact hisolated y hy hxy
  · intro hy
    subst hy
    by_contra hx
    exact hisolated x hx (σ.symm' hxy)

/-- Every partition of three fibers is the top partition or isolates some fiber. -/
theorem eq_top_or_le_isolatePartition (σ : ER 3) :
    σ = ⊤ ∨ σ ≤ isolatePartition 0 ∨ σ ≤ isolatePartition 1 ∨ σ ≤ isolatePartition 2 := by
  by_cases h01 : σ 0 1 <;> by_cases h02 : σ 0 2
  · left
    have hzero : ∀ x, σ x 0 := by
      intro x
      fin_cases x
      · exact σ.refl' 0
      · exact σ.symm' h01
      · exact σ.symm' h02
    exact Setoid.eq_top_iff.mpr fun x y ↦ σ.trans' (hzero x) (σ.symm' (hzero y))
  · refine Or.inr (Or.inr (Or.inr (le_isolatePartition fun x hx hrel ↦ ?_)))
    fin_cases x
    · exact h02 (σ.symm' hrel)
    · exact h02 (σ.trans' h01 (σ.symm' hrel))
    · exact hx rfl
  · refine Or.inr (Or.inr (Or.inl (le_isolatePartition fun x hx hrel ↦ ?_)))
    fin_cases x
    · exact h01 (σ.symm' hrel)
    · exact hx rfl
    · exact h01 (σ.trans' h02 (σ.symm' hrel))
  · refine Or.inr (Or.inl (le_isolatePartition fun x hx hrel ↦ ?_))
    fin_cases x
    · exact hx rfl
    · exact h01 hrel
    · exact h02 hrel

/-- Two isolations of distinct fibers together refine the bottom partition: a pair related in
both lies in no block other than a singleton. -/
theorem le_bot_of_le_isolatePartition {σ : ER 3} {i j : Fin 3} (hij : i ≠ j)
    (hi : σ ≤ isolatePartition i) (hj : σ ≤ isolatePartition j) : σ ≤ ⊥ := by
  intro a b hab
  have hai := (isolatePartition_rel i a b).mp (hi hab)
  have haj := (isolatePartition_rel j a b).mp (hj hab)
  show a = b
  by_contra hne
  have h1 : a.val ≠ i.val := fun h ↦ hne ((Fin.ext h).trans (hai.mp (Fin.ext h)).symm)
  have h2 : a.val ≠ j.val := fun h ↦ hne ((Fin.ext h).trans (haj.mp (Fin.ext h)).symm)
  have h3 : b.val ≠ i.val := fun h ↦ hne ((hai.mpr (Fin.ext h)).trans (Fin.ext h).symm)
  have h4 : b.val ≠ j.val := fun h ↦ hne ((haj.mpr (Fin.ext h)).trans (Fin.ext h).symm)
  have h5 : a.val ≠ b.val := fun h ↦ hne (Fin.ext h)
  have h6 : i.val ≠ j.val := fun h ↦ hij (Fin.ext h)
  have ha := a.isLt
  have hb := b.isLt
  have hi3 := i.isLt
  have hj3 := j.isLt
  omega

/-- Inclusion–exclusion on three fibers: the indicator of the top partition is one minus the
three isolation indicators plus twice the indicator of the bottom partition. -/
theorem top_indicator_three (σ : ER 3) :
    (if σ = ⊤ then (1 : ℝ) else 0) =
      1 - (if σ ≤ isolatePartition 0 then 1 else 0) -
        (if σ ≤ isolatePartition 1 then 1 else 0) -
        (if σ ≤ isolatePartition 2 then 1 else 0) + 2 * (if σ ≤ ⊥ then 1 else 0) := by
  have h01 := le_bot_of_le_isolatePartition (σ := σ) (by decide : (0 : Fin 3) ≠ 1)
  have h02 := le_bot_of_le_isolatePartition (σ := σ) (by decide : (0 : Fin 3) ≠ 2)
  have h12 := le_bot_of_le_isolatePartition (σ := σ) (by decide : (1 : Fin 3) ≠ 2)
  by_cases hT : σ = ⊤
  · have hA0 : ¬ σ ≤ isolatePartition 0 := fun hle ↦ by
      rw [hT] at hle
      exact absurd ((isolatePartition_rel 0 0 1).mp (hle trivial)) (by decide)
    have hA1 : ¬ σ ≤ isolatePartition 1 := fun hle ↦ by
      rw [hT] at hle
      exact absurd ((isolatePartition_rel 1 1 0).mp (hle trivial)) (by decide)
    have hA2 : ¬ σ ≤ isolatePartition 2 := fun hle ↦ by
      rw [hT] at hle
      exact absurd ((isolatePartition_rel 2 2 0).mp (hle trivial)) (by decide)
    have hB : ¬ σ ≤ ⊥ := fun hle ↦ hA0 (le_trans hle bot_le)
    rw [if_pos hT, if_neg hA0, if_neg hA1, if_neg hA2, if_neg hB]
    norm_num
  · by_cases hB : σ ≤ ⊥
    · rw [if_neg hT, if_pos (le_trans hB (bot_le (a := isolatePartition 0))),
        if_pos (le_trans hB (bot_le (a := isolatePartition 1))),
        if_pos (le_trans hB (bot_le (a := isolatePartition 2))), if_pos hB]
      norm_num
    · rcases eq_top_or_le_isolatePartition σ with htop | hA0 | hA1 | hA2
      · exact absurd htop hT
      · rw [if_neg hT, if_pos hA0, if_neg fun h ↦ hB (h01 hA0 h),
          if_neg fun h ↦ hB (h02 hA0 h), if_neg hB]
        norm_num
      · rw [if_neg hT, if_neg fun h ↦ hB (h01 h hA1), if_pos hA1,
          if_neg fun h ↦ hB (h12 hA1 h), if_neg hB]
        norm_num
      · rw [if_neg hT, if_neg fun h ↦ hB (h02 h hA2), if_neg fun h ↦ hB (h12 h hA2),
          if_pos hA2, if_neg hB]
        norm_num

/-- **Three fibers, arbitrary masses.** The connection probability of the random graph on three
fibers is `1 − Σ_i e^(−u κ(isolate i)) + 2 e^(−u κ(⊥))`. -/
theorem connectionProbability_three (p : Fin 3 → ℝ) (u : ℝ) :
    connectionProbability p u =
      1 - Real.exp (-(u * crossingRate p (isolatePartition 0))) -
        Real.exp (-(u * crossingRate p (isolatePartition 1))) -
        Real.exp (-(u * crossingRate p (isolatePartition 2))) +
        2 * Real.exp (-(u * crossingRate p ⊥)) := by
  have htopRate : crossingRate p ⊤ = 0 := by
    rw [crossingRate]
    exact sum_eq_zero fun e _ ↦ if_pos trivial
  have hterm : ∀ G : FiberPair 3 → Bool,
      configMass p u G * (if componentPartition G = ⊤ then 1 else 0) =
        configMass p u G * (if componentPartition G ≤ ⊤ then 1 else 0) -
          configMass p u G * (if componentPartition G ≤ isolatePartition 0 then 1 else 0) -
          configMass p u G * (if componentPartition G ≤ isolatePartition 1 then 1 else 0) -
          configMass p u G * (if componentPartition G ≤ isolatePartition 2 then 1 else 0) +
          2 * (configMass p u G * (if componentPartition G ≤ ⊥ then 1 else 0)) := by
    intro G
    rw [top_indicator_three, if_pos le_top]
    ring
  unfold connectionProbability
  rw [sum_congr rfl fun G _ ↦ hterm G, sum_add_distrib, sum_sub_distrib, sum_sub_distrib,
    sum_sub_distrib, ← mul_sum, sum_configMass_componentPartition_le,
    sum_configMass_componentPartition_le, sum_configMass_componentPartition_le,
    sum_configMass_componentPartition_le, sum_configMass_componentPartition_le, htopRate,
    mul_zero, neg_zero, Real.exp_zero]

/-- The fiber pairs of three fibers, listed as `01`, `02`, `12`. -/
def fiberPairThreeEquiv : Fin 3 ≃ FiberPair 3 where
  toFun := ![⟨(0, 1), by decide⟩, ⟨(0, 2), by decide⟩, ⟨(1, 2), by decide⟩]
  invFun e := if e.1 = (0, 1) then 0 else if e.1 = (0, 2) then 1 else 2
  left_inv i := by
    fin_cases i <;> rfl
  right_inv := by
    rintro ⟨⟨a, b⟩, hab⟩
    fin_cases a <;> fin_cases b <;> first | rfl | exact absurd hab (by decide)

/-- A sum over the edges of the complete graph on three fibers has three terms. -/
theorem sum_fiberPair_three (g : FiberPair 3 → ℝ) :
    ∑ e, g e = g ⟨(0, 1), by decide⟩ + g ⟨(0, 2), by decide⟩ + g ⟨(1, 2), by decide⟩ := by
  calc ∑ e, g e = ∑ i : Fin 3, g (fiberPairThreeEquiv i) :=
        (Fintype.sum_equiv fiberPairThreeEquiv (fun i ↦ g (fiberPairThreeEquiv i)) g
          fun _ ↦ rfl).symm
    _ = g ⟨(0, 1), by decide⟩ + g ⟨(0, 2), by decide⟩ + g ⟨(1, 2), by decide⟩ :=
        Fin.sum_univ_three _

/-- At equal masses the isolation of a fiber is crossed by two edges of rate `1/9`. -/
theorem crossingRate_isolatePartition_equal (i : Fin 3) :
    crossingRate (fun _ : Fin 3 ↦ (1 / 3 : ℝ)) (isolatePartition i) = 2 / 9 := by
  rw [crossingRate, sum_fiberPair_three]
  simp only [isolatePartition_rel, pairRate]
  fin_cases i <;> simp (config := { decide := true }) <;> norm_num

/-- At equal masses the bottom partition is crossed by all three edges of rate `1/9`. -/
theorem crossingRate_bot_equal :
    crossingRate (fun _ : Fin 3 ↦ (1 / 3 : ℝ)) ⊥ = 1 / 3 := by
  rw [crossingRate, sum_fiberPair_three]
  simp only [Setoid.bot_def, pairRate]
  simp (config := { decide := true })
  norm_num

/-- **Three equal fibers.** With `p = (1/3, 1/3, 1/3)` the connection time has survival
`Pr(T_p > u) = 3 e^(−2u/9) − 2 e^(−u/3)`. -/
theorem connectionSurvival_three_equal (u : ℝ) :
    1 - connectionProbability (fun _ : Fin 3 ↦ (1 / 3 : ℝ)) u =
      3 * Real.exp (-(2 * u / 9)) - 2 * Real.exp (-(u / 3)) := by
  rw [connectionProbability_three, crossingRate_isolatePartition_equal,
    crossingRate_isolatePartition_equal, crossingRate_isolatePartition_equal,
    crossingRate_bot_equal]
  have hisolated : -(u * (2 / 9)) = -(2 * u / 9) := by ring
  have hempty : -(u * (1 / 3)) = -(u / 3) := by ring
  rw [hisolated, hempty]
  ring

end

end Descent.Pangenome.GraphCoalescent
