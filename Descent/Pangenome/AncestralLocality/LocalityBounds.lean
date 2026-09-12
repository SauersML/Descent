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

omit [DecidableEq V] in
/-- **The decision rate is at most `D Z`.** -/
theorem decisionRate_le {r : V → V → ℝ} {D : ℝ} (hD : ∀ i, ∑ j, r i j ≤ D)
    (s : Multiset (Finset V)) : decisionRate r s ≤ D * supportSize s := by
  have hright : D * supportSize s = (s.map fun S ↦ D * (S.card : ℝ)).sum :=
    Multiset.sum_map_mul_left.symm
  rw [hright, decisionRate]
  refine Multiset.sum_map_le_sum_map _ _ fun S _ ↦ ?_
  calc ∑ i ∈ S, ∑ j, r i j ≤ ∑ _i ∈ S, D := Finset.sum_le_sum fun i _ ↦ hD i
    _ = D * S.card := by rw [Finset.sum_const, nsmul_eq_mul, mul_comm]

omit [DecidableEq V] [Fintype V] in
/-- `n` arguments each carrying the observation set `A` have total support size `n |A|`. -/
theorem supportSize_replicate (A : Finset V) (n : ℕ) :
    supportSize (Multiset.replicate n A) = n * A.card := by
  simp [supportSize]

/-! ### The light cone -/

/-- **The directed ball `B_k(A)`**: the coordinates reachable from `A` along at most `k` edges of
positive rate. -/
def lightBall (r : V → V → ℝ) (A : Finset V) : ℕ → Finset V
  | 0 => A
  | k + 1 => lightBall r A k ∪ univ.filter fun j ↦ ∃ i ∈ lightBall r A k, 0 < r i j

/-- The balls grow with the radius. -/
theorem lightBall_mono (r : V → V → ℝ) (A : Finset V) : Monotone (lightBall r A) :=
  monotone_nat_of_le_succ fun _ ↦ Finset.subset_union_left

/-- An edge of positive rate leads one radius out. -/
theorem mem_lightBall_succ {r : V → V → ℝ} {A : Finset V} {k : ℕ} {i j : V}
    (hi : i ∈ lightBall r A k) (hij : 0 < r i j) : j ∈ lightBall r A (k + 1) := by
  simp only [lightBall, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
  exact Or.inr ⟨i, hi, hij⟩

/-- **The directed distance `d(v, A)`, truncated at `ℓ`**: the number of radii `k < ℓ` whose ball
misses `v`. A coordinate of `A` has depth zero (`lightDepth_eq_zero`), and a coordinate outside
every ball of radius below `ℓ` has depth `ℓ` (`lightDepth_eq_of_forall`). -/
def lightDepth (r : V → V → ℝ) (A : Finset V) (ℓ : ℕ) (v : V) : ℕ :=
  ((range ℓ).filter fun k ↦ v ∉ lightBall r A k).card

/-- The observed coordinates have depth zero. -/
theorem lightDepth_eq_zero {r : V → V → ℝ} {A : Finset V} {v : V} (hv : v ∈ A) (ℓ : ℕ) :
    lightDepth r A ℓ v = 0 := by
  rw [lightDepth, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  exact fun k _ hk ↦ hk (lightBall_mono r A (Nat.zero_le k) hv)

/-- A coordinate outside every ball of radius below `ℓ` has depth `ℓ`. -/
theorem lightDepth_eq_of_forall {r : V → V → ℝ} {A : Finset V} {ℓ : ℕ} {v : V}
    (hv : ∀ k < ℓ, v ∉ lightBall r A k) : lightDepth r A ℓ v = ℓ := by
  rw [lightDepth, Finset.filter_true_of_mem fun k hk ↦ hv k (Finset.mem_range.mp hk),
    Finset.card_range]

/-- **The depth grows by at most one along an edge of positive rate.** -/
theorem lightDepth_le_succ {r : V → V → ℝ} {A : Finset V} {ℓ : ℕ} {i j : V}
    (hij : 0 < r i j) : lightDepth r A ℓ j ≤ lightDepth r A ℓ i + 1 := by
  have hsub : (range ℓ).filter (fun k ↦ j ∉ lightBall r A k) ⊆
      insert 0 (((range ℓ).filter fun k ↦ i ∉ lightBall r A k).image (· + 1)) := by
    intro k hk
    rw [Finset.mem_filter, Finset.mem_range] at hk
    rcases k with _ | k
    · exact Finset.mem_insert_self 0 _
    · refine Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨k, ?_, rfl⟩)
      rw [Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, fun hi ↦ hk.2 (mem_lightBall_succ hi hij)⟩
  exact (Finset.card_le_card hsub).trans ((Finset.card_insert_le _ _).trans
    (Nat.add_le_add_right Finset.card_image_le 1))

/-- **The light-cone weight `w(v) = a^{d(v, A)}`**, with the distance truncated at `ℓ`. -/
def lightWeight (r : V → V → ℝ) (A : Finset V) (ℓ : ℕ) (a : ℝ) (v : V) : ℝ :=
  a ^ lightDepth r A ℓ v

/-- A nonnegative base gives a nonnegative weight. -/
theorem lightWeight_nonneg {r : V → V → ℝ} {A : Finset V} {ℓ : ℕ} {a : ℝ} (ha : 0 ≤ a)
    (v : V) : 0 ≤ lightWeight r A ℓ a v :=
  pow_nonneg ha _

/-- **The edge inequality `w(j) ≤ a w(i)`** along every edge `i → j` of positive rate. -/
theorem lightWeight_le_mul {r : V → V → ℝ} {A : Finset V} {ℓ : ℕ} {a : ℝ} (ha : 1 ≤ a)
    {i j : V} (hij : 0 < r i j) : lightWeight r A ℓ a j ≤ a * lightWeight r A ℓ a i := by
  rw [lightWeight, lightWeight, ← pow_succ']
  exact pow_le_pow_right₀ ha (lightDepth_le_succ hij)

/-- **Theorem 8, the weighted drift `L_anc Z^{(a)} ≤ D (1 + 2a) Z^{(a)}`.** -/
theorem supportGenerator_lightWeight_le {r : V → V → ℝ} {c D a : ℝ} {A : Finset V} {ℓ : ℕ}
    (hr : ∀ i j, 0 ≤ r i j) (hD : ∀ i, ∑ j, r i j ≤ D) (hc : 0 ≤ c) (ha : 1 ≤ a)
    (s : Multiset (Finset V)) :
    supportGenerator r c (weightedCount (lightWeight r A ℓ a)) s ≤
      D * (1 + 2 * a) * weightedCount (lightWeight r A ℓ a) s :=
  supportGenerator_weightedCount_le hr hD hc (lightWeight_nonneg (by linarith)) (by linarith)
    (fun _ _ hij ↦ lightWeight_le_mul ha hij) s

/-- `n` arguments carrying `A` have light-cone count `n |A|`: every coordinate of `A` weighs one. -/
theorem weightedCount_replicate_lightWeight (r : V → V → ℝ) (A : Finset V) (ℓ : ℕ) (a : ℝ)
    (n : ℕ) : weightedCount (lightWeight r A ℓ a) (Multiset.replicate n A) = n * A.card := by
  have hA : ∑ v ∈ A, lightWeight r A ℓ a v = A.card := by
    calc ∑ v ∈ A, lightWeight r A ℓ a v = ∑ _v ∈ A, (1 : ℝ) :=
          Finset.sum_congr rfl fun v hv ↦ by rw [lightWeight, lightDepth_eq_zero hv, pow_zero]
      _ = A.card := by simp
  simp only [weightedCount, Multiset.map_replicate, Multiset.sum_replicate, hA, nsmul_eq_mul]

/-- **The escape event `E_ℓ`**: the circuit holds a coordinate outside every ball of radius below
`ℓ`, that is, at directed distance at least `ℓ` from `A`. -/
def escapeSet (r : V → V → ℝ) (A : Finset V) (ℓ : ℕ) : Set (Multiset (Finset V)) :=
  {s | ∃ S ∈ s, ∃ v ∈ S, ∀ k < ℓ, v ∉ lightBall r A k}

/-- **Escape forces `Z^{(a)} ≥ a^ℓ`.** -/
theorem pow_le_weightedCount_of_mem_escapeSet {r : V → V → ℝ} {A : Finset V} {ℓ : ℕ} {a : ℝ}
    (ha : 0 ≤ a) {s : Multiset (Finset V)} (hs : s ∈ escapeSet r A ℓ) :
    a ^ ℓ ≤ weightedCount (lightWeight r A ℓ a) s := by
  obtain ⟨S, hS, v, hv, hfar⟩ := hs
  calc a ^ ℓ = lightWeight r A ℓ a v := by rw [lightWeight, lightDepth_eq_of_forall hfar]
    _ ≤ ∑ u ∈ S, lightWeight r A ℓ a u :=
      Finset.single_le_sum (fun u _ ↦ lightWeight_nonneg ha u) hv
    _ ≤ weightedCount (lightWeight r A ℓ a) s := sum_le_weightedCount (lightWeight_nonneg ha) hS

/-- The initial circuit, `n` arguments carrying `A`, has not escaped at a positive radius. -/
theorem replicate_not_mem_escapeSet (r : V → V → ℝ) (A : Finset V) {ℓ : ℕ} (hℓ : 0 < ℓ)
    (n : ℕ) : Multiset.replicate n A ∉ escapeSet r A ℓ := by
  rintro ⟨S, hS, v, hv, hfar⟩
  rw [Multiset.eq_of_mem_replicate hS] at hv
  exact hfar 0 hℓ hv

/-- **Escape is permanent under a decision**: supports only grow. -/
theorem branchSupports_mem_escapeSet {r : V → V → ℝ} {A : Finset V} {ℓ : ℕ}
    {s : Multiset (Finset V)} {S : Finset V} (hS : S ∈ s) (i j : V)
    (hs : s ∈ escapeSet r A ℓ) : branchSupports s S i j ∈ escapeSet r A ℓ := by
  obtain ⟨S', hS', v, hv, hfar⟩ := hs
  by_cases hSS' : S' = S
  · subst hSS'
    exact ⟨insert j S', Multiset.mem_cons.mpr (Or.inl rfl), v, Finset.mem_insert_of_mem hv, hfar⟩
  · refine ⟨S', Multiset.mem_cons.mpr (Or.inr (Multiset.mem_cons.mpr (Or.inr ?_))), v, hv, hfar⟩
    exact (Multiset.mem_erase_of_ne hSS').mpr hS'

/-- **Escape is permanent under a coalescence**: the merged support is the union. -/
theorem coalesceSupports_mem_escapeSet {r : V → V → ℝ} {A : Finset V} {ℓ : ℕ}
    {s t : Multiset (Finset V)} (hs : s ∈ escapeSet r A ℓ) :
    coalesceSupports s t ∈ escapeSet r A ℓ := by
  obtain ⟨S, hS, v, hv, hfar⟩ := hs
  by_cases hSt : S ∈ t
  · exact ⟨t.sup, Multiset.mem_cons.mpr (Or.inl rfl), v, Multiset.le_sup hSt hv, hfar⟩
  · refine ⟨S, Multiset.mem_cons.mpr (Or.inr ?_), v, hv, hfar⟩
    rw [← Multiset.count_pos, Multiset.count_sub, Multiset.count_eq_zero.mpr hSt, Nat.sub_zero]
    exact Multiset.count_pos.mpr hS

end Supports

end

end Descent.Pangenome.AncestralLocality
