/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Layer
import Mathlib.Algebra.BigOperators.Ring.Multiset
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Data.Multiset.Powerset
import Mathlib.MeasureTheory.Integral.Bochner.Basic

assert_below Descent.PopGen Descent.Spectral Descent.Blindness Descent.Conditionals
assert_below Descent.Portability Descent.Decision Descent.Program

/-!
# Locality bounds: the support drift and the genomic light cone

The spec is `ANCESTRAL_LOCALITY.md` §8-9: Theorems 7 and 8, Corollary 8.1 and the numbers of
§9.1.

As far as its support tags go, the backward decision circuit of the sampling dual is the
multiset of the supports `A_a ⊆ V` of its arguments. `branchSupports` is the update (7.6) of a
decision along `i → j`, `coalesceSupports` joins the supports of two identified arguments, and
`supportGenerator` is the ancestral generator on functions of the state.

## Theorem 7

A decision raises the weighted count `weightedCount w` by at most `w i + 2 w j`
(`weightedCount_branchSupports_le`), and a coalescence does not raise it
(`weightedCount_coalesceSupports_le`). With `Σ_j r i j ≤ D` and `w j ≤ κ w i` on every edge of
positive rate the generator obeys `L Z^{(w)} ≤ D (1 + 2κ) Z^{(w)}`
(`supportGenerator_weightedCount_le`); the plain count gives `L Z ≤ 3 D Z`
(`supportGenerator_supportSize_le`), and the decision rate is at most `D Z` (`decisionRate_le`).
-/

namespace Descent.Pangenome.AncestralLocality

open Finset MeasureTheory

noncomputable section

section Supports

variable {V : Type*}

/-! ### The tagged support state -/

/-- **The weighted support count** `Z^{(w)} = Σ_b Σ_{v ∈ A_b} w(v)` of a tagged state, recorded
as the multiset of the supports `A_b` of the circuit's arguments. -/
def weightedCount (w : V → ℝ) (s : Multiset (Finset V)) : ℝ :=
  (s.map fun S ↦ ∑ v ∈ S, w v).sum

/-- **The total support size** `Z = Σ_a |A_a|` of a tagged state. -/
def supportSize (s : Multiset (Finset V)) : ℝ :=
  (s.map fun S ↦ (S.card : ℝ)).sum

/-- The weighted count of a state with one more argument. -/
theorem weightedCount_cons (w : V → ℝ) (S : Finset V) (s : Multiset (Finset V)) :
    weightedCount w (S ::ₘ s) = ∑ v ∈ S, w v + weightedCount w s := by
  simp only [weightedCount, Multiset.map_cons, Multiset.sum_cons]

/-- The weighted count adds over a sum of states. -/
theorem weightedCount_add (w : V → ℝ) (s s' : Multiset (Finset V)) :
    weightedCount w (s + s') = weightedCount w s + weightedCount w s' := by
  simp only [weightedCount, Multiset.map_add, Multiset.sum_add]

/-- The unit weight counts support sizes: `Z^{(1)} = Z`. -/
theorem weightedCount_one (s : Multiset (Finset V)) :
    weightedCount (fun _ ↦ 1) s = supportSize s := by
  simp [weightedCount, supportSize]

/-- A nonnegative weight has a nonnegative count. -/
theorem weightedCount_nonneg {w : V → ℝ} (hw : ∀ v, 0 ≤ w v) (s : Multiset (Finset V)) :
    0 ≤ weightedCount w s :=
  Multiset.sum_nonneg fun _ hx ↦ by
    obtain ⟨S, _, rfl⟩ := Multiset.mem_map.mp hx
    exact Finset.sum_nonneg fun v _ ↦ hw v

/-- One argument's weighted support is at most the whole count. -/
theorem sum_le_weightedCount {w : V → ℝ} (hw : ∀ v, 0 ≤ w v) {s : Multiset (Finset V)}
    {S : Finset V} (hS : S ∈ s) : ∑ v ∈ S, w v ≤ weightedCount w s := by
  classical
  rw [← Multiset.cons_erase hS, weightedCount_cons]
  linarith [weightedCount_nonneg hw (s.erase S)]

variable [DecidableEq V]

/-- A nonnegative weight is subadditive over a union of supports. -/
theorem sum_union_le_add {w : V → ℝ} (hw : ∀ v, 0 ≤ w v) (S S' : Finset V) :
    ∑ v ∈ S ∪ S', w v ≤ ∑ v ∈ S, w v + ∑ v ∈ S', w v := by
  have h := Finset.sum_union_inter (s₁ := S) (s₂ := S') (f := w)
  linarith [Finset.sum_nonneg fun v (_ : v ∈ S ∩ S') ↦ hw v]

/-- **The support update (7.6) of a decision branching.** An argument with support `S`
containing the target `i` checks `i` against `j`: its support becomes `S ∪ {j}`, and a new
parental argument with support `{i, j}` joins the circuit. -/
def branchSupports (s : Multiset (Finset V)) (S : Finset V) (i j : V) : Multiset (Finset V) :=
  insert j S ::ₘ {i, j} ::ₘ s.erase S

/-- **A decision raises the weighted count by at most `w i + 2 w j`.** -/
theorem weightedCount_branchSupports_le {w : V → ℝ} (hw : ∀ v, 0 ≤ w v)
    {s : Multiset (Finset V)} {S : Finset V} (hS : S ∈ s) (i j : V) :
    weightedCount w (branchSupports s S i j) ≤ weightedCount w s + w i + 2 * w j := by
  have hsplit := weightedCount_cons w S (s.erase S)
  rw [Multiset.cons_erase hS] at hsplit
  have hinsert : ∑ v ∈ insert j S, w v ≤ w j + ∑ v ∈ S, w v := by
    have h := sum_union_le_add hw {j} S
    rwa [← Finset.insert_eq, Finset.sum_singleton] at h
  have hpair : ∑ v ∈ ({i, j} : Finset V), w v ≤ w i + w j := by
    have h := sum_union_le_add hw {i} {j}
    rwa [← Finset.insert_eq, Finset.sum_singleton, Finset.sum_singleton] at h
  rw [branchSupports, weightedCount_cons, weightedCount_cons]
  linarith

/-- **The support update of a coalescence.** The two arguments of `t`, a sub-multiset of size
two, are identified, and the merged argument carries the union of their supports. -/
def coalesceSupports (s t : Multiset (Finset V)) : Multiset (Finset V) :=
  t.sup ::ₘ (s - t)

/-- **A coalescence does not raise the weighted count.** -/
theorem weightedCount_coalesceSupports_le {w : V → ℝ} (hw : ∀ v, 0 ≤ w v)
    {s t : Multiset (Finset V)} (ht : t ∈ s.powersetCard 2) :
    weightedCount w (coalesceSupports s t) ≤ weightedCount w s := by
  obtain ⟨hle, hcard⟩ := Multiset.mem_powersetCard.mp ht
  obtain ⟨S, S', rfl⟩ := Multiset.card_eq_two.mp hcard
  have hsplit := congrArg (weightedCount w) (tsub_add_cancel_of_le hle)
  rw [weightedCount_add] at hsplit
  have hpair : weightedCount w {S, S'} = ∑ v ∈ S, w v + ∑ v ∈ S', w v := by
    simp [weightedCount, Multiset.insert_eq_cons]
  have hsup : ({S, S'} : Multiset (Finset V)).sup = S ∪ S' := by
    rw [Multiset.insert_eq_cons, Multiset.sup_cons, Multiset.sup_singleton, Finset.sup_eq_union]
  rw [coalesceSupports, weightedCount_cons, hsup]
  linarith [sum_union_le_add hw S S']

variable [Fintype V]

/-- **The ancestral generator on functions of the tagged state.** At rate `r i j` every argument
whose support contains `i` branches along `i → j` (an event whose target lies outside the
support leaves the circuit unchanged and is omitted), and at rate `c` every unordered pair of
arguments coalesces. -/
def supportGenerator (r : V → V → ℝ) (c : ℝ) (F : Multiset (Finset V) → ℝ)
    (s : Multiset (Finset V)) : ℝ :=
  (s.map fun S ↦ ∑ i ∈ S, ∑ j, r i j * (F (branchSupports s S i j) - F s)).sum +
    c * ((s.powersetCard 2).map fun t ↦ F (coalesceSupports s t) - F s).sum

/-- **The total rate of decision branchings** from a tagged state. -/
def decisionRate (r : V → V → ℝ) (s : Multiset (Finset V)) : ℝ :=
  (s.map fun S ↦ ∑ i ∈ S, ∑ j, r i j).sum

/-- **The weighted drift inequality.** If every row of rates sums to at most `D` and the weight
grows by at most the factor `κ` along every edge of positive rate, then
`L Z^{(w)} ≤ D (1 + 2κ) Z^{(w)}`. -/
theorem supportGenerator_weightedCount_le {r : V → V → ℝ} {c D κ : ℝ} {w : V → ℝ}
    (hr : ∀ i j, 0 ≤ r i j) (hD : ∀ i, ∑ j, r i j ≤ D) (hc : 0 ≤ c) (hw : ∀ v, 0 ≤ w v)
    (hκ : 0 ≤ κ) (hedge : ∀ i j, 0 < r i j → w j ≤ κ * w i) (s : Multiset (Finset V)) :
    supportGenerator r c (weightedCount w) s ≤ D * (1 + 2 * κ) * weightedCount w s := by
  have hbranch : ∀ S ∈ s, ∑ i ∈ S, ∑ j, r i j *
      (weightedCount w (branchSupports s S i j) - weightedCount w s) ≤
        D * (1 + 2 * κ) * ∑ v ∈ S, w v := by
    intro S hS
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ ↦ ?_
    have hterm : ∀ j, r i j * (weightedCount w (branchSupports s S i j) - weightedCount w s) ≤
        r i j * ((1 + 2 * κ) * w i) := by
      intro j
      rcases (hr i j).eq_or_lt with hzero | hpos
      · rw [← hzero, zero_mul, zero_mul]
      · refine mul_le_mul_of_nonneg_left ?_ (hr i j)
        linarith [weightedCount_branchSupports_le hw hS i j, hedge i j hpos]
    calc ∑ j, r i j * (weightedCount w (branchSupports s S i j) - weightedCount w s)
        ≤ ∑ j, r i j * ((1 + 2 * κ) * w i) := Finset.sum_le_sum fun j _ ↦ hterm j
      _ = (∑ j, r i j) * ((1 + 2 * κ) * w i) := by rw [Finset.sum_mul]
      _ ≤ D * ((1 + 2 * κ) * w i) :=
        mul_le_mul_of_nonneg_right (hD i) (mul_nonneg (by linarith) (hw i))
      _ = D * (1 + 2 * κ) * w i := by ring
  have hsum : (s.map fun S ↦ ∑ i ∈ S, ∑ j, r i j *
      (weightedCount w (branchSupports s S i j) - weightedCount w s)).sum ≤
        D * (1 + 2 * κ) * weightedCount w s := by
    have hright : D * (1 + 2 * κ) * weightedCount w s =
        (s.map fun S ↦ D * (1 + 2 * κ) * ∑ v ∈ S, w v).sum :=
      Multiset.sum_map_mul_left.symm
    rw [hright]
    exact Multiset.sum_map_le_sum_map _ _ hbranch
  have hcoal : ((s.powersetCard 2).map fun t ↦
      weightedCount w (coalesceSupports s t) - weightedCount w s).sum ≤ 0 := by
    have h := Multiset.sum_map_le_sum_map (s := s.powersetCard 2)
      (fun t ↦ weightedCount w (coalesceSupports s t) - weightedCount w s) (fun _ ↦ 0)
      fun t ht ↦ sub_nonpos.mpr (weightedCount_coalesceSupports_le hw ht)
    simpa using h
  have hscaled : c * ((s.powersetCard 2).map fun t ↦
      weightedCount w (coalesceSupports s t) - weightedCount w s).sum ≤ 0 := by
    nlinarith
  rw [supportGenerator]
  linarith

/-- **Theorem 7, the drift inequality `L_anc Z ≤ 3 D Z`.** -/
theorem supportGenerator_supportSize_le {r : V → V → ℝ} {c D : ℝ} (hr : ∀ i j, 0 ≤ r i j)
    (hD : ∀ i, ∑ j, r i j ≤ D) (hc : 0 ≤ c) (s : Multiset (Finset V)) :
    supportGenerator r c supportSize s ≤ 3 * D * supportSize s := by
  have h := supportGenerator_weightedCount_le (w := fun _ ↦ 1) hr hD hc (fun _ ↦ zero_le_one)
    zero_le_one (fun _ _ _ ↦ by norm_num) s
  rw [show weightedCount (fun _ : V ↦ (1 : ℝ)) = supportSize from funext weightedCount_one] at h
  linarith

/-- **The decision rate is at most `D Z`.** -/
theorem decisionRate_le {r : V → V → ℝ} {D : ℝ} (hD : ∀ i, ∑ j, r i j ≤ D)
    (s : Multiset (Finset V)) : decisionRate r s ≤ D * supportSize s := by
  have hright : D * supportSize s = (s.map fun S ↦ D * (S.card : ℝ)).sum :=
    Multiset.sum_map_mul_left.symm
  rw [hright, decisionRate]
  refine Multiset.sum_map_le_sum_map _ _ fun S _ ↦ ?_
  calc ∑ i ∈ S, ∑ j, r i j ≤ ∑ _i ∈ S, D := Finset.sum_le_sum fun i _ ↦ hD i
    _ = D * S.card := by rw [Finset.sum_const, nsmul_eq_mul, mul_comm]

/-- `n` arguments each carrying the observation set `A` have total support size `n |A|`. -/
theorem supportSize_replicate (A : Finset V) (n : ℕ) :
    supportSize (Multiset.replicate n A) = n * A.card := by
  simp [supportSize]

end Supports

end

end Descent.Pangenome.AncestralLocality
