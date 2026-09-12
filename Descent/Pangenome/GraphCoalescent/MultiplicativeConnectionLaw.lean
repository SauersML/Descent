/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Coalescent.StateSpace
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.Analysis.SpecialFunctions.Exp

assert_below Descent.PopGen Descent.Spectral Descent.Blindness Descent.Conditionals
assert_below Descent.Portability Descent.Decision Descent.Program

/-!
# The multiplicative connection law of the pangenome hidden-clock note

Theorem F of the hidden-clock note, in its limit (F3), identifies the scaled connection time of
a highly compressed report with `T_p`, the connection time of the complete graph on the `w`
fiber labels whose edge `{i, j}` switches on at an independent exponential clock of rate
`p_i p_j`. Its exact law (F4) is a Möbius sum over the partitions of the fibers:
`Pr(T_p ≤ u) = Σ_σ (−1)^(|σ|−1) (|σ|−1)! e^(−u κ_σ)`, with `κ_σ` the total rate of the edges
that cross `σ`.

The event `T_p ≤ u` is the event that the graph of the edges whose clocks have rung by time `u`
is connected, and each edge has rung by `u` with probability `1 − e^(−u p_i p_j)`,
independently. This module proves (F4) for that finite random graph. `connectionProbability p u`
is the probability that the edge configuration at time `u` connects every fiber, and
`connectionProbability_eq_mobius_sum` is (F4). The exponential clocks enter only through their
distribution functions at the fixed time `u`; the passage from clocks on the real line to the
configuration at time `u` is not formalised here.

The proof is Möbius inversion on the partition lattice of the fibers. For a configuration, the
partition into connected components refines `σ` exactly when no present edge crosses `σ`
(`componentPartition_le_iff`), and that event has probability `e^(−u κ_σ)`
(`sum_configMass_componentPartition_le`). The key lemma is the arbitrary-order Möbius identity
`sum_topMobius_blocks_ge`: for every partition `τ`, the coefficients `(−1)^(|σ|−1) (|σ|−1)!`
summed over the partitions `σ` coarser than `τ` give one when `τ` is the top partition and zero
otherwise. It is derived from the counting identity
`Σ_{σ ≥ τ} x (x − 1) ⋯ (x − |σ| + 1) = x^|τ|` (`sum_descFactorial_blocks_ge`), which groups the
maps from the sample to `x` labels that are constant on the blocks of `τ` by their kernels,
lifted to an identity of integer polynomials and read at the linear coefficient.
`Descent.Pangenome.TripleGluing` records the same coefficient at order three.

The two-fiber and three-equal-fiber evaluations of the note are in
`MultiplicativeConnectionExamples`.

## Empirical status

None. The bodies here are algebra: the connection probability is a finite sum over edge
configurations, and the Möbius identity is a counting identity on the partitions of a finite
set, so no measurement on any pangenome can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Pangenome.GraphCoalescent

open Coalescent Finset
open scoped Classical Polynomial

noncomputable section

/-- A partition of a finite sample is determined by its relation, so a finite sample has
finitely many partitions. -/
theorem finite_ER (n : ℕ) : Finite (ER n) :=
  Finite.of_injective (fun σ : ER n ↦ σ.r) fun _ _ h ↦
    Setoid.ext fun a b ↦ Iff.of_eq (congrFun (congrFun h a) b)

/-- The partitions of a finite sample, enumerated for the sums of this module. -/
local instance fintypeER (n : ℕ) : Fintype (ER n) :=
  @Fintype.ofFinite _ (finite_ER n)

/-- The Möbius coefficient of the partition lattice at its top element, as a function of the
number of blocks: `μ(σ, ⊤) = (−1)^(|σ| − 1) (|σ| − 1)!`. -/
def topMobius (j : ℕ) : ℤ := (-1) ^ (j - 1) * ((j - 1).factorial : ℤ)

/-- The linear coefficient of the falling factorial `x (x − 1) ⋯ (x − k)` is `(−1)^k k!`. -/
theorem coeff_one_descPochhammer_succ (k : ℕ) :
    (descPochhammer ℤ (k + 1)).coeff 1 = (-1) ^ k * (k.factorial : ℤ) := by
  induction k with
  | zero => simp [descPochhammer_one]
  | succ k ih =>
    have hzero : (descPochhammer ℤ (k + 1)).coeff 0 = 0 := by
      rw [Polynomial.coeff_zero_eq_eval_zero, descPochhammer_eval_zero,
        if_neg (Nat.succ_ne_zero k)]
    have hstep : (descPochhammer ℤ (k + 1 + 1)).coeff 1 =
        (descPochhammer ℤ (k + 1)).coeff 0 -
          (descPochhammer ℤ (k + 1)).coeff 1 * ((k + 1 : ℕ) : ℤ) := by
      rw [descPochhammer_succ_right, ← Polynomial.C_eq_natCast]
      exact Polynomial.coeff_mul_X_sub_C
    rw [hstep, hzero, ih, Nat.factorial_succ, pow_succ]
    push_cast
    ring

/-- The linear coefficient of the falling factorial with `j ≥ 1` factors is the top Möbius
coefficient of a partition with `j` blocks. -/
theorem coeff_one_descPochhammer (j : ℕ) (hj : 0 < j) :
    (descPochhammer ℤ j).coeff 1 = topMobius j := by
  cases j with
  | zero => exact absurd hj (lt_irrefl 0)
  | succ k => rw [coeff_one_descPochhammer_succ, topMobius, Nat.add_sub_cancel]

/-- The maps from the sample to `x` labels whose kernel is the partition `σ` correspond to the
injections of the blocks of `σ` into the labels. -/
def kernelMapEquiv {w x : ℕ} (σ : ER w) :
    {f : Fin w → Fin x // Setoid.ker f = σ} ≃ (Quotient σ ↪ Fin x) where
  toFun f := by
    refine ⟨Quotient.lift f.1 fun a b hab ↦ ?_, fun c d hcd ↦ ?_⟩
    · have hker : Setoid.ker f.1 a b := by
        rw [f.2]
        exact hab
      exact Setoid.ker_def.mp hker
    · obtain ⟨a, rfl⟩ := Quotient.exists_rep c
      obtain ⟨b, rfl⟩ := Quotient.exists_rep d
      apply Quotient.sound
      have hker : Setoid.ker f.1 a b := Setoid.ker_def.mpr hcd
      rw [f.2] at hker
      exact hker
  invFun g := ⟨fun a ↦ g (Quotient.mk σ a), Setoid.ext fun a b ↦
    ⟨fun hab ↦ Quotient.exact (g.injective hab), fun hab ↦ congrArg g (Quotient.sound hab)⟩⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Function.Embedding.ext fun c ↦ Quotient.inductionOn c fun _ ↦ rfl

/-- The maps from the sample to `x` labels that are constant on the blocks of `τ` correspond to
the maps from the blocks of `τ` to the labels. -/
def blockLabelEquiv {w x : ℕ} (τ : ER w) :
    {f : Fin w → Fin x // τ ≤ Setoid.ker f} ≃ (Quotient τ → Fin x) where
  toFun f := Quotient.lift f.1 fun _ _ hab ↦ Setoid.ker_def.mp (f.2 hab)
  invFun g := ⟨fun a ↦ g (Quotient.mk τ a), fun _ _ hab ↦ congrArg g (Quotient.sound hab)⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := funext fun c ↦ Quotient.inductionOn c fun _ ↦ rfl

/-- The number of maps from the sample to `x` labels with kernel `σ` is the falling factorial
`x (x − 1) ⋯ (x − |σ| + 1)`. -/
theorem card_kernel_eq {w : ℕ} (x : ℕ) (σ : ER w) :
    (univ.filter fun f : Fin w → Fin x ↦ Setoid.ker f = σ).card =
      x.descFactorial (blocks σ) := by
  rw [← Fintype.card_subtype, Fintype.card_congr (kernelMapEquiv σ),
    Fintype.card_embedding_eq, Fintype.card_fin, blocks, Nat.card_eq_fintype_card]

/-- Grouping the maps that are constant on the blocks of `τ` by their kernels:
`Σ_{σ ≥ τ} x (x − 1) ⋯ (x − |σ| + 1) = x^|τ|`. -/
theorem sum_descFactorial_blocks_ge {w : ℕ} (τ : ER w) (x : ℕ) :
    ∑ σ ∈ univ.filter (τ ≤ ·), x.descFactorial (blocks σ) = x ^ blocks τ := by
  have hcount : (univ.filter fun f : Fin w → Fin x ↦ τ ≤ Setoid.ker f).card =
      x ^ blocks τ := by
    rw [← Fintype.card_subtype, Fintype.card_congr (blockLabelEquiv τ), Fintype.card_fun,
      Fintype.card_fin, blocks, Nat.card_eq_fintype_card]
  rw [← hcount, card_eq_sum_card_fiberwise (f := fun f : Fin w → Fin x ↦ Setoid.ker f)
    (s := univ.filter fun f : Fin w → Fin x ↦ τ ≤ Setoid.ker f) (t := univ.filter (τ ≤ ·))
    fun f hf ↦ by simpa using (mem_filter.mp hf).2]
  refine sum_congr rfl fun σ hσ ↦ ?_
  rw [← card_kernel_eq x σ, filter_filter]
  congr 1
  refine filter_congr fun f _ ↦ ⟨fun hker ↦ ⟨?_, hker⟩, fun hboth ↦ hboth.2⟩
  rw [hker]
  exact (mem_filter.mp hσ).2

/-- The counting identity as an identity of integer polynomials:
`Σ_{σ ≥ τ} X (X − 1) ⋯ (X − |σ| + 1) = X^|τ|`. -/
theorem sum_descPochhammer_blocks_ge {w : ℕ} (τ : ER w) :
    ∑ σ ∈ univ.filter (τ ≤ ·), descPochhammer ℤ (blocks σ) =
      (Polynomial.X : ℤ[X]) ^ blocks τ := by
  apply Polynomial.eq_of_infinite_eval_eq
  apply Set.infinite_of_injective_forall_mem (f := fun x : ℕ ↦ (x : ℤ)) Nat.cast_injective
  intro x
  simp only [Set.mem_setOf_eq, Polynomial.eval_finset_sum, descPochhammer_eval_eq_descFactorial,
    Polynomial.eval_pow, Polynomial.eval_X]
  exact_mod_cast sum_descFactorial_blocks_ge τ x

/-- **The partition-lattice Möbius identity at arbitrary order.** For every partition `τ` of a
nonempty sample, the top Möbius coefficients of the partitions coarser than `τ` add to one when
`τ` is the top partition and to zero otherwise. -/
theorem sum_topMobius_blocks_ge {w : ℕ} [NeZero w] (τ : ER w) :
    ∑ σ ∈ univ.filter (τ ≤ ·), topMobius (blocks σ) = if τ = ⊤ then 1 else 0 := by
  have hcoeff := congrArg (fun P : ℤ[X] ↦ P.coeff 1) (sum_descPochhammer_blocks_ge τ)
  simp only [Polynomial.finset_sum_coeff, Polynomial.coeff_X_pow] at hcoeff
  rw [sum_congr rfl fun σ _ ↦
    (coeff_one_descPochhammer (blocks σ) (blocks_pos σ)).symm, hcoeff]
  by_cases htop : τ = ⊤
  · rw [if_pos htop, if_pos ((blocks_eq_one_iff τ).mpr htop).symm]
  · rw [if_neg htop, if_neg fun hone ↦ htop ((blocks_eq_one_iff τ).mp hone.symm)]

/-- The unordered pairs of fiber labels, each written with its smaller label first: the edges of
the complete graph on the `w` fibers. -/
abbrev FiberPair (w : ℕ) := {e : Fin w × Fin w // e.1 < e.2}

/-- The clock rate of the edge between fibers `i < j`: `p_i p_j`. -/
def pairRate {w : ℕ} (p : Fin w → ℝ) (e : FiberPair w) : ℝ := p e.1.1 * p e.1.2

/-- Two fiber labels are adjacent in an edge configuration when a present edge joins them. -/
def configAdjacent {w : ℕ} (G : FiberPair w → Bool) (i j : Fin w) : Prop :=
  ∃ e : FiberPair w, G e = true ∧ ((e.1.1 = i ∧ e.1.2 = j) ∨ (e.1.1 = j ∧ e.1.2 = i))

/-- The partition of the fibers into the connected components of an edge configuration: the
equivalence relation generated by adjacency. -/
def componentPartition {w : ℕ} (G : FiberPair w → Bool) : ER w :=
  Relation.EqvGen.setoid (configAdjacent G)

/-- The components of a configuration refine a partition exactly when no present edge crosses
it. -/
theorem componentPartition_le_iff {w : ℕ} (G : FiberPair w → Bool) (σ : ER w) :
    componentPartition G ≤ σ ↔ ∀ e : FiberPair w, G e = true → σ e.1.1 e.1.2 := by
  constructor
  · intro hle e he
    have hadj : configAdjacent G e.1.1 e.1.2 := ⟨e, he, Or.inl ⟨rfl, rfl⟩⟩
    exact hle (Relation.EqvGen.rel _ _ hadj)
  · intro hedge
    apply Setoid.eqvGen_le
    rintro i j ⟨e, he, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
    · exact hedge e he
    · exact σ.symm (hedge e he)

/-- The mass of an edge configuration at time `u`: every edge is present with probability
`1 − e^(−u p_i p_j)`, independently of the others. -/
def configMass {w : ℕ} (p : Fin w → ℝ) (u : ℝ) (G : FiberPair w → Bool) : ℝ :=
  ∏ e, if G e then 1 - Real.exp (-(u * pairRate p e)) else Real.exp (-(u * pairRate p e))

/-- `Pr(T_p ≤ u)`: the probability that the edge configuration at time `u` connects every
fiber. -/
def connectionProbability {w : ℕ} (p : Fin w → ℝ) (u : ℝ) : ℝ :=
  ∑ G : FiberPair w → Bool, configMass p u G * if componentPartition G = ⊤ then 1 else 0

/-- `κ_σ`: the total clock rate of the edges that cross the partition `σ`, summed edge by
edge. -/
def crossingRate {w : ℕ} (p : Fin w → ℝ) (σ : ER w) : ℝ :=
  ∑ e : FiberPair w, if σ e.1.1 e.1.2 then 0 else pairRate p e

/-- The probability that the components of the configuration at time `u` refine `σ`, that is,
that no edge crossing `σ` is present, is `e^(−u κ_σ)`. -/
theorem sum_configMass_componentPartition_le {w : ℕ} (p : Fin w → ℝ) (u : ℝ) (σ : ER w) :
    ∑ G : FiberPair w → Bool,
        configMass p u G * (if componentPartition G ≤ σ then 1 else 0) =
      Real.exp (-(u * crossingRate p σ)) := by
  have hindicator : ∀ G : FiberPair w → Bool,
      (if componentPartition G ≤ σ then (1 : ℝ) else 0) =
        ∏ e, if G e = true ∧ ¬ σ e.1.1 e.1.2 then (0 : ℝ) else 1 := by
    intro G
    by_cases hall : ∀ e : FiberPair w, G e = true → σ e.1.1 e.1.2
    · rw [if_pos ((componentPartition_le_iff G σ).mpr hall)]
      symm
      exact prod_eq_one fun e _ ↦ if_neg fun hbad ↦ hbad.2 (hall e hbad.1)
    · rw [if_neg fun hle ↦ hall ((componentPartition_le_iff G σ).mp hle)]
      push_neg at hall
      obtain ⟨e, he, hcross⟩ := hall
      symm
      exact prod_eq_zero (mem_univ e) (if_pos ⟨he, hcross⟩)
  have hedge : ∀ e : FiberPair w,
      (∑ b : Bool, (if b then 1 - Real.exp (-(u * pairRate p e))
          else Real.exp (-(u * pairRate p e))) *
        (if b = true ∧ ¬ σ e.1.1 e.1.2 then (0 : ℝ) else 1)) =
        Real.exp (-(u * if σ e.1.1 e.1.2 then 0 else pairRate p e)) := by
    intro e
    rw [Fintype.sum_bool]
    by_cases hrel : σ e.1.1 e.1.2 <;> simp [hrel]
  have hexpand := prod_univ_sum (fun _ : FiberPair w ↦ (univ : Finset Bool))
    fun (e : FiberPair w) (b : Bool) ↦
      (if b then 1 - Real.exp (-(u * pairRate p e)) else Real.exp (-(u * pairRate p e))) *
        (if b = true ∧ ¬ σ e.1.1 e.1.2 then (0 : ℝ) else 1)
  rw [Fintype.piFinset_univ] at hexpand
  calc ∑ G : FiberPair w → Bool,
        configMass p u G * (if componentPartition G ≤ σ then 1 else 0)
      = ∑ G : FiberPair w → Bool, ∏ e, (if G e then 1 - Real.exp (-(u * pairRate p e))
            else Real.exp (-(u * pairRate p e))) *
          (if G e = true ∧ ¬ σ e.1.1 e.1.2 then (0 : ℝ) else 1) := by
        refine sum_congr rfl fun G _ ↦ ?_
        rw [hindicator G, configMass, ← prod_mul_distrib]
    _ = ∏ e, Real.exp (-(u * if σ e.1.1 e.1.2 then 0 else pairRate p e)) := by
        rw [← hexpand]
        exact prod_congr rfl fun e _ ↦ hedge e
    _ = Real.exp (-(u * crossingRate p σ)) := by
        rw [← Real.exp_sum, crossingRate, mul_sum, ← sum_neg_distrib]

/-- **(F4), the multiplicative connection law.** The probability that the random graph on the
`w` fibers, whose edge `{i, j}` is present at time `u` with probability `1 − e^(−u p_i p_j)`
independently of the others, is connected is the Möbius sum
`Σ_σ (−1)^(|σ|−1) (|σ|−1)! e^(−u κ_σ)` over the partitions of the fibers. -/
theorem connectionProbability_eq_mobius_sum {w : ℕ} [NeZero w] (p : Fin w → ℝ) (u : ℝ) :
    connectionProbability p u =
      ∑ σ : ER w, (topMobius (blocks σ) : ℝ) * Real.exp (-(u * crossingRate p σ)) := by
  have hmobius : ∀ G : FiberPair w → Bool,
      (if componentPartition G = ⊤ then (1 : ℝ) else 0) =
        ∑ σ : ER w, (topMobius (blocks σ) : ℝ) *
          (if componentPartition G ≤ σ then 1 else 0) := by
    intro G
    have hsum := sum_topMobius_blocks_ge (componentPartition G)
    rw [sum_filter] at hsum
    have hcast : ((∑ σ : ER w,
        if componentPartition G ≤ σ then topMobius (blocks σ) else 0 : ℤ) : ℝ) =
        ((if componentPartition G = ⊤ then 1 else 0 : ℤ) : ℝ) := by
      rw [hsum]
    push_cast at hcast
    rw [← hcast]
    refine sum_congr rfl fun σ _ ↦ ?_
    split_ifs <;> simp
  unfold connectionProbability
  calc ∑ G : FiberPair w → Bool,
        configMass p u G * (if componentPartition G = ⊤ then 1 else 0)
      = ∑ G : FiberPair w → Bool, ∑ σ : ER w, (topMobius (blocks σ) : ℝ) *
          (configMass p u G * if componentPartition G ≤ σ then 1 else 0) := by
        refine sum_congr rfl fun G _ ↦ ?_
        rw [hmobius G, mul_sum]
        exact sum_congr rfl fun σ _ ↦ by ring
    _ = ∑ σ : ER w, (topMobius (blocks σ) : ℝ) *
          ∑ G : FiberPair w → Bool,
            configMass p u G * if componentPartition G ≤ σ then 1 else 0 := by
        rw [sum_comm]
        exact sum_congr rfl fun σ _ ↦ by rw [mul_sum]
    _ = ∑ σ : ER w, (topMobius (blocks σ) : ℝ) * Real.exp (-(u * crossingRate p σ)) :=
        sum_congr rfl fun σ _ ↦ by rw [sum_configMass_componentPartition_le]

end

end Descent.Pangenome.GraphCoalescent
