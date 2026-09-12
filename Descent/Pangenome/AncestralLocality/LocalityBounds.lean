/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Layer
import Descent.Pangenome.AncestralLocality.AncestralDecision
import Descent.Pangenome.AncestralLocality.LocalityCoupling
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
`supportGenerator` is the ancestral generator on functions of the state. A tag state
`A : Fin n → Finset V` of `Descent.Pangenome.AncestralLocality.AncestralDecision` gives the
multiset `univ.val.map A`. Its weighted count is `tagWeight w A` (`weightedCount_map_univ`), its
size is `tagCount A` (`supportSize_map_univ`), and its decision rate is `decisionRate r A`
(`supportDecisionRate_map_univ`).

## Theorem 7

A decision raises the weighted count `weightedCount w` by at most `w i + 2 w j`
(`weightedCount_branchSupports_le`), and a coalescence does not raise it
(`weightedCount_coalesceSupports_le`). With `Σ_j r i j ≤ D` and `w j ≤ κ w i` on every edge of
positive rate the generator obeys `L Z^{(w)} ≤ D (1 + 2κ) Z^{(w)}`
(`supportGenerator_weightedCount_le`); the plain count gives `L Z ≤ 3 D Z`
(`supportGenerator_supportSize_le`), and the decision rate is at most `D Z`
(`supportDecisionRate_le`).

Grönwall's inequality along a right derivative is `le_mul_exp_of_hasDerivWithinAt`. Through it,
`integral_le_mul_exp_of_supportGenerator_le` turns a pointwise bound `L_anc F ≤ K F` into
`∫ F dμ_t ≤ C e^{K t}` for marginal laws `μ t` that start at `s₀` with `F s₀ ≤ C` and obey
Dynkin's formula. With `F = Z` this is (8.2), `integral_supportSize_le`. With the compensator
formula for the decision count it gives (8.3), `integral_branchings_le`, through the integrated
bound `le_div_three_mul_exp_sub_one`.

## Theorem 8

`lightBall r A k` is the directed ball `B_k(A)` along edges of positive rate, `lightDepth` is the
distance `d(v, A)` truncated at `ℓ`, and `lightWeight` is the weight `w(v) = a^{d(v, A)}`. The
depth rises by at most one along an edge (`lightDepth_le_succ`). That gives the edge inequality
`w(j) ≤ a w(i)` (`lightWeight_le_mul`), hence `L_anc Z^{(a)} ≤ D (1 + 2a) Z^{(a)}`
(`supportGenerator_lightWeight_le`).

`escapeSet r A ℓ` is the set of states holding a coordinate at distance at least `ℓ` from `A`.
The initial circuit lies outside it (`replicate_not_mem_escapeSet`), and both support updates
keep an escaped state escaped (`branchSupports_mem_escapeSet`, `coalesceSupports_mem_escapeSet`).
Escape forces `Z^{(a)} ≥ a^ℓ` (`pow_le_weightedCount_of_mem_escapeSet`). Markov's inequality
(`measureReal_escapeSet_le`) with the expected count (`integral_lightWeight_le`) gives (9.1),
`measureReal_escapeSet_le_exp`. The radius choice `a = ℓ / (2 D T)` turns that bound into (9.2)
by the identity `exp_div_pow_eq_of_radius`. When `D T = 0`, (9.1) at every `a > 1` forces the
escape probability to zero (`eq_zero_of_forall_escape_bound`).

## Corollary 8.1

Outcomes on one probability space that agree off an event `E` differ only on `E`
(`measureReal_preimage_sub_eq`). Their laws are therefore within `P(E)` at every set
(`abs_measureReal_preimage_sub_le`) and within `P(E)` in the `totalVariation` of
`Descent.Pangenome.AncestralLocality.LocalityCoupling` (`totalVariation_measureReal_fiber_le`).
That module proves the finite-weight form of the corollary and the numbers of §9.1
(`twenty_mul_exp_three_mem_Icc`, `escapeBound_twenty_le`), so they are not restated here.

Scope. The backward tagged process has no path law in the corpus, and none is constructed here.
There is no Markov chain on tagged states, no nonexplosion argument and no proof of Dynkin's
formula. Theorems 7 and 8 are proved for any family of marginal laws `μ t` that starts at `n`
arguments carrying `A`, satisfies Dynkin's formula for the count in question, and has the stated
integrability and continuity. (8.3) also assumes the compensator formula for the decision count.
The tagged state records only the multiset of supports, not the argument order or the function
`f` of the sampling dual. The genome is finite (`[Fintype V]`), and the rates are real with
`r i j ≥ 0` and row sums at most `D`. The distance is truncated at `ℓ`, which is all that escape
reads. Corollary 8.1 is the coupling inequality for two outcomes on a common probability space.
It is not formalized that the circuit run against `p` and against `q`, or against the truncated
graph on `B_{ℓ-1}(A)`, is such a coupling. Theorem 9, the infinite genome, is not here.

## Empirical status

None. The bodies here are counts on finite multisets, calculus and measure inequalities. The
rates, laws and outcomes are supplied, and no measurement can bear on them.
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
def supportDecisionRate (r : V → V → ℝ) (s : Multiset (Finset V)) : ℝ :=
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
theorem supportDecisionRate_le {r : V → V → ℝ} {D : ℝ} (hD : ∀ i, ∑ j, r i j ≤ D)
    (s : Multiset (Finset V)) : supportDecisionRate r s ≤ D * supportSize s := by
  have hright : D * supportSize s = (s.map fun S ↦ D * (S.card : ℝ)).sum :=
    Multiset.sum_map_mul_left.symm
  rw [hright, supportDecisionRate]
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

/-! ### The tag form of `AncestralDecision` -/

section Tags

variable {V : Type*} {n : ℕ}

/-- **The multiset count is the tag weight.** The supports of the arguments `A : Fin n → Finset V`,
read as a multiset, have weighted count `tagWeight w A`. -/
theorem weightedCount_map_univ (w : V → ℝ) (A : Fin n → Finset V) :
    weightedCount w (univ.val.map A) = tagWeight w A := by
  rw [weightedCount, Multiset.map_map]
  rfl

/-- **The multiset support size is the tag count** `tagCount A`. -/
theorem supportSize_map_univ (A : Fin n → Finset V) :
    supportSize (univ.val.map A) = tagCount A := by
  rw [← weightedCount_one, weightedCount_map_univ, tagWeight_one]

/-- **The multiset decision rate is the tag decision rate** `decisionRate r A`. -/
theorem supportDecisionRate_map_univ [Fintype V] (r : V → V → ℝ) (A : Fin n → Finset V) :
    supportDecisionRate r (univ.val.map A) = decisionRate r A := by
  rw [supportDecisionRate, Multiset.map_map]
  rfl

end Tags

/-! ### Grönwall's inequality along a right derivative -/

/-- **Grönwall's inequality for a right derivative.** A function continuous on `[0, T]` whose
right derivative `m'` satisfies `m' t ≤ K m t` on `[0, T)` is at most `C e^{K t}` there, for any
`C ≥ m 0`. -/
theorem le_mul_exp_of_hasDerivWithinAt {m m' : ℝ → ℝ} {K T C : ℝ}
    (hcont : ContinuousOn m (Set.Icc 0 T))
    (hderiv : ∀ t ∈ Set.Ico 0 T, HasDerivWithinAt m (m' t) (Set.Ici t) t)
    (hdrift : ∀ t ∈ Set.Ico 0 T, m' t ≤ K * m t) (hinit : m 0 ≤ C) :
    ∀ t ∈ Set.Icc 0 T, m t ≤ C * Real.exp (K * t) := by
  intro t ht
  have h := le_gronwallBound_of_liminf_deriv_right_le (K := K) (ε := 0) hcont
    (fun x hx _r hr ↦ (hderiv x hx).liminf_right_slope_le hr) hinit
    (fun x hx ↦ by rw [add_zero]; exact hdrift x hx) t ht
  rwa [gronwallBound_ε0, sub_zero] at h

/-- **The integrated exponential bound.** If `m t ≤ C e^{3 D t}` on `[0, T]` and
`b ≤ D ∫_0^T m`, then `b ≤ (C / 3) (e^{3 D T} - 1)`. -/
theorem le_div_three_mul_exp_sub_one {m : ℝ → ℝ} {b C D T : ℝ} (hD : 0 ≤ D) (hT : 0 ≤ T)
    (hcont : ContinuousOn m (Set.Icc 0 T))
    (hm : ∀ t ∈ Set.Icc 0 T, m t ≤ C * Real.exp (3 * D * t))
    (hb : b ≤ D * ∫ t in (0 : ℝ)..T, m t) : b ≤ C / 3 * (Real.exp (3 * D * T) - 1) := by
  have hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) T,
      HasDerivAt (fun t ↦ C / 3 * (Real.exp (3 * D * t) - 1)) (D * (C * Real.exp (3 * D * t)))
        t := fun t _ ↦
    ((((hasDerivAt_id' (x := t)).const_mul (3 * D)).exp.sub_const 1).const_mul
      (C / 3)).congr_deriv (by ring)
  have hprimitive : ∫ t in (0 : ℝ)..T, D * (C * Real.exp (3 * D * t)) =
      C / 3 * (Real.exp (3 * D * T) - 1) := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
      (Continuous.intervalIntegrable (by fun_prop) 0 T)]
    simp
  have hmono : ∫ t in (0 : ℝ)..T, m t ≤ ∫ t in (0 : ℝ)..T, C * Real.exp (3 * D * t) :=
    intervalIntegral.integral_mono_on hT (hcont.intervalIntegrable_of_Icc hT)
      (Continuous.intervalIntegrable (by fun_prop) 0 T) hm
  calc b ≤ D * ∫ t in (0 : ℝ)..T, m t := hb
    _ ≤ D * ∫ t in (0 : ℝ)..T, C * Real.exp (3 * D * t) := mul_le_mul_of_nonneg_left hmono hD
    _ = ∫ t in (0 : ℝ)..T, D * (C * Real.exp (3 * D * t)) :=
      (intervalIntegral.integral_const_mul _ _).symm
    _ = C / 3 * (Real.exp (3 * D * T) - 1) := hprimitive

/-! ### Theorems 7 and 8 along marginal laws of the circuit -/

section Marginals

variable {V : Type*} [DecidableEq V] [Fintype V] [MeasurableSpace (Multiset (Finset V))]

/-- **Expected growth from a pointwise generator bound.** If `L_anc F ≤ K F` at every state and
the marginal laws `μ t` of the circuit start at `s₀` with `F s₀ ≤ C`, then
`∫ F dμ_t ≤ C e^{K t}` on `[0, T]`.

Assumes: Dynkin's formula for `F` along `μ` (`hdynkin`: the right derivative of `∫ F dμ_t` is
`∫ L_anc F dμ_t`), with `F` and `L_anc F` integrable and `∫ F dμ_t` continuous on `[0, T]`. -/
theorem integral_le_mul_exp_of_supportGenerator_le [MeasurableSingletonClass (Multiset (Finset V))]
    {r : V → V → ℝ} {c K T C : ℝ} {F : Multiset (Finset V) → ℝ}
    (hLF : ∀ s, supportGenerator r c F s ≤ K * F s)
    {μ : ℝ → Measure (Multiset (Finset V))} {s₀ : Multiset (Finset V)}
    (hμ0 : μ 0 = Measure.dirac s₀) (hF0 : F s₀ ≤ C)
    (hint : ∀ t ∈ Set.Icc 0 T, Integrable F (μ t))
    (hintL : ∀ t ∈ Set.Icc 0 T, Integrable (supportGenerator r c F) (μ t))
    (hcont : ContinuousOn (fun t ↦ ∫ s, F s ∂μ t) (Set.Icc 0 T))
    (hdynkin : ∀ t ∈ Set.Ico 0 T, HasDerivWithinAt (fun t ↦ ∫ s, F s ∂μ t)
      (∫ s, supportGenerator r c F s ∂μ t) (Set.Ici t) t) :
    ∀ t ∈ Set.Icc 0 T, ∫ s, F s ∂μ t ≤ C * Real.exp (K * t) := by
  refine le_mul_exp_of_hasDerivWithinAt hcont hdynkin (fun t ht ↦ ?_) ?_
  · have ht' := Set.Ico_subset_Icc_self ht
    show ∫ s, supportGenerator r c F s ∂μ t ≤ K * ∫ s, F s ∂μ t
    rw [← integral_const_mul]
    exact integral_mono (hintL t ht') ((hint t ht').const_mul _) fun s ↦ hLF s
  · show ∫ s, F s ∂μ 0 ≤ C
    rwa [hμ0, integral_dirac]

/-- **Theorem 7, (8.2): `E Z_t ≤ n |A| e^{3 D t}`** on `[0, T]`, for the circuit started from `n`
arguments carrying `A`.

Assumes: the conditions of `integral_le_mul_exp_of_supportGenerator_le` for `F = Z`. -/
theorem integral_supportSize_le [MeasurableSingletonClass (Multiset (Finset V))]
    {r : V → V → ℝ} {c D T : ℝ} {n : ℕ} {A : Finset V}
    (hr : ∀ i j, 0 ≤ r i j) (hD : ∀ i, ∑ j, r i j ≤ D) (hc : 0 ≤ c)
    {μ : ℝ → Measure (Multiset (Finset V))} (hμ0 : μ 0 = Measure.dirac (Multiset.replicate n A))
    (hint : ∀ t ∈ Set.Icc 0 T, Integrable supportSize (μ t))
    (hintL : ∀ t ∈ Set.Icc 0 T, Integrable (supportGenerator r c supportSize) (μ t))
    (hcont : ContinuousOn (fun t ↦ ∫ s, supportSize s ∂μ t) (Set.Icc 0 T))
    (hdynkin : ∀ t ∈ Set.Ico 0 T, HasDerivWithinAt (fun t ↦ ∫ s, supportSize s ∂μ t)
      (∫ s, supportGenerator r c supportSize s ∂μ t) (Set.Ici t) t) :
    ∀ t ∈ Set.Icc 0 T, ∫ s, supportSize s ∂μ t ≤ n * A.card * Real.exp (3 * D * t) :=
  integral_le_mul_exp_of_supportGenerator_le (supportGenerator_supportSize_le hr hD hc) hμ0
    (supportSize_replicate A n).le hint hintL hcont hdynkin

/-- **Theorem 7, (8.3): `E B_T ≤ (n |A| / 3) (e^{3 D T} - 1)`** for the expected number `b` of
decision branchings by time `T`.

Assumes: the compensator formula `b = ∫_0^T ∫ supportDecisionRate dμ_t dt` (`hcomp`), the decision
rate integrable, and the conditions of `integral_supportSize_le`. -/
theorem integral_branchings_le [MeasurableSingletonClass (Multiset (Finset V))]
    {r : V → V → ℝ} {c D T b : ℝ} {n : ℕ} {A : Finset V}
    (hr : ∀ i j, 0 ≤ r i j) (hD : ∀ i, ∑ j, r i j ≤ D) (hD0 : 0 ≤ D) (hc : 0 ≤ c) (hT : 0 ≤ T)
    {μ : ℝ → Measure (Multiset (Finset V))} (hμ0 : μ 0 = Measure.dirac (Multiset.replicate n A))
    (hint : ∀ t ∈ Set.Icc 0 T, Integrable supportSize (μ t))
    (hintL : ∀ t ∈ Set.Icc 0 T, Integrable (supportGenerator r c supportSize) (μ t))
    (hintR : ∀ t ∈ Set.Icc 0 T, Integrable (supportDecisionRate r) (μ t))
    (hcont : ContinuousOn (fun t ↦ ∫ s, supportSize s ∂μ t) (Set.Icc 0 T))
    (hdynkin : ∀ t ∈ Set.Ico 0 T, HasDerivWithinAt (fun t ↦ ∫ s, supportSize s ∂μ t)
      (∫ s, supportGenerator r c supportSize s ∂μ t) (Set.Ici t) t)
    (hrate : IntervalIntegrable (fun t ↦ ∫ s, supportDecisionRate r s ∂μ t) volume 0 T)
    (hcomp : b = ∫ t in (0 : ℝ)..T, ∫ s, supportDecisionRate r s ∂μ t) :
    b ≤ n * A.card / 3 * (Real.exp (3 * D * T) - 1) := by
  have hstep : ∫ t in (0 : ℝ)..T, ∫ s, supportDecisionRate r s ∂μ t ≤
      ∫ t in (0 : ℝ)..T, D * ∫ s, supportSize s ∂μ t :=
    intervalIntegral.integral_mono_on hT hrate ((hcont.intervalIntegrable_of_Icc hT).const_mul D)
      fun t ht ↦ by
        rw [← integral_const_mul]
        exact integral_mono (hintR t ht) ((hint t ht).const_mul _)
          fun s ↦ supportDecisionRate_le hD s
  refine le_div_three_mul_exp_sub_one hD0 hT hcont
    (integral_supportSize_le hr hD hc hμ0 hint hintL hcont hdynkin) ?_
  rw [hcomp, ← intervalIntegral.integral_const_mul]
  exact hstep

/-- **Theorem 8, the expected light-cone count `E Z^{(a)}_t ≤ n |A| e^{D (1 + 2a) t}`** on
`[0, T]`, for `a ≥ 1`.

Assumes: the conditions of `integral_le_mul_exp_of_supportGenerator_le` for `F = Z^{(a)}`. -/
theorem integral_lightWeight_le [MeasurableSingletonClass (Multiset (Finset V))]
    {r : V → V → ℝ} {c D T a : ℝ} {n ℓ : ℕ} {A : Finset V}
    (hr : ∀ i j, 0 ≤ r i j) (hD : ∀ i, ∑ j, r i j ≤ D) (hc : 0 ≤ c) (ha : 1 ≤ a)
    {μ : ℝ → Measure (Multiset (Finset V))} (hμ0 : μ 0 = Measure.dirac (Multiset.replicate n A))
    (hint : ∀ t ∈ Set.Icc 0 T, Integrable (weightedCount (lightWeight r A ℓ a)) (μ t))
    (hintL : ∀ t ∈ Set.Icc 0 T,
      Integrable (supportGenerator r c (weightedCount (lightWeight r A ℓ a))) (μ t))
    (hcont : ContinuousOn (fun t ↦ ∫ s, weightedCount (lightWeight r A ℓ a) s ∂μ t)
      (Set.Icc 0 T))
    (hdynkin : ∀ t ∈ Set.Ico 0 T,
      HasDerivWithinAt (fun t ↦ ∫ s, weightedCount (lightWeight r A ℓ a) s ∂μ t)
        (∫ s, supportGenerator r c (weightedCount (lightWeight r A ℓ a)) s ∂μ t) (Set.Ici t) t) :
    ∀ t ∈ Set.Icc 0 T, ∫ s, weightedCount (lightWeight r A ℓ a) s ∂μ t ≤
      n * A.card * Real.exp (D * (1 + 2 * a) * t) :=
  integral_le_mul_exp_of_supportGenerator_le (supportGenerator_lightWeight_le hr hD hc ha) hμ0
    (weightedCount_replicate_lightWeight r A ℓ a n).le hint hintL hcont hdynkin

/-- **Markov's inequality for escape.** For a law `ν` of the circuit and `a ≥ 1`, the escape
probability is at most `min {1, C / a^ℓ}` whenever `E_ν Z^{(a)} ≤ C`. -/
theorem measureReal_escapeSet_le {r : V → V → ℝ} {A : Finset V} {ℓ : ℕ} {a C : ℝ} (ha : 1 ≤ a)
    (ν : Measure (Multiset (Finset V))) [IsProbabilityMeasure ν]
    (hint : Integrable (weightedCount (lightWeight r A ℓ a)) ν)
    (hmean : ∫ s, weightedCount (lightWeight r A ℓ a) s ∂ν ≤ C) :
    ν.real (escapeSet r A ℓ) ≤ min 1 (C / a ^ ℓ) := by
  have hpos : 0 < a ^ ℓ := pow_pos (by linarith) ℓ
  have hmarkov := mul_meas_ge_le_integral_of_nonneg
    (ae_of_all _ fun s ↦ weightedCount_nonneg (lightWeight_nonneg (by linarith)) s) hint (a ^ ℓ)
  have hsub : ν.real (escapeSet r A ℓ) ≤
      ν.real {s | a ^ ℓ ≤ weightedCount (lightWeight r A ℓ a) s} :=
    measureReal_mono fun s hs ↦ pow_le_weightedCount_of_mem_escapeSet (by linarith) hs
  refine le_min measureReal_le_one ?_
  rw [le_div_iff₀ hpos]
  nlinarith

/-- **Theorem 8, (9.1): `Pr(E_{ℓ,T}) ≤ min {1, n |A| e^{D (1 + 2a) T} / a^ℓ}`** for `a ≥ 1`.

Assumes: the conditions of `integral_lightWeight_le`, with every `μ t` a probability law. -/
theorem measureReal_escapeSet_le_exp [MeasurableSingletonClass (Multiset (Finset V))]
    {r : V → V → ℝ} {c D T a : ℝ} {n ℓ : ℕ} {A : Finset V}
    (hr : ∀ i j, 0 ≤ r i j) (hD : ∀ i, ∑ j, r i j ≤ D) (hc : 0 ≤ c) (ha : 1 ≤ a) (hT : 0 ≤ T)
    {μ : ℝ → Measure (Multiset (Finset V))} [∀ t, IsProbabilityMeasure (μ t)]
    (hμ0 : μ 0 = Measure.dirac (Multiset.replicate n A))
    (hint : ∀ t ∈ Set.Icc 0 T, Integrable (weightedCount (lightWeight r A ℓ a)) (μ t))
    (hintL : ∀ t ∈ Set.Icc 0 T,
      Integrable (supportGenerator r c (weightedCount (lightWeight r A ℓ a))) (μ t))
    (hcont : ContinuousOn (fun t ↦ ∫ s, weightedCount (lightWeight r A ℓ a) s ∂μ t)
      (Set.Icc 0 T))
    (hdynkin : ∀ t ∈ Set.Ico 0 T,
      HasDerivWithinAt (fun t ↦ ∫ s, weightedCount (lightWeight r A ℓ a) s ∂μ t)
        (∫ s, supportGenerator r c (weightedCount (lightWeight r A ℓ a)) s ∂μ t) (Set.Ici t) t) :
    (μ T).real (escapeSet r A ℓ) ≤
      min 1 (n * A.card * Real.exp (D * (1 + 2 * a) * T) / a ^ ℓ) :=
  measureReal_escapeSet_le ha (μ T) (hint T ⟨hT, le_rfl⟩)
    (integral_lightWeight_le hr hD hc ha hμ0 hint hintL hcont hdynkin T ⟨hT, le_rfl⟩)

end Marginals

/-! ### The radius choice (9.2) and the case `D T = 0` -/

/-- **The choice `a = ℓ / (2 D T)` in (9.1) gives (9.2)**:
`N e^{D (1 + 2a) T} / a^ℓ = N e^{D T} (2 e D T / ℓ)^ℓ`. -/
theorem exp_div_pow_eq_of_radius {D T N : ℝ} {ℓ : ℕ} (hDT : D * T ≠ 0) :
    N * Real.exp (D * (1 + 2 * (ℓ / (2 * D * T))) * T) / (ℓ / (2 * D * T)) ^ ℓ =
      N * Real.exp (D * T) * (2 * Real.exp 1 * D * T / ℓ) ^ ℓ := by
  have hne : 2 * D * T ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero (left_ne_zero_of_mul hDT)) (right_ne_zero_of_mul hDT)
  have hexp : D * (1 + 2 * (ℓ / (2 * D * T))) * T = D * T + ℓ := by
    linear_combination div_mul_cancel₀ (ℓ : ℝ) hne
  have hpow : Real.exp ℓ = Real.exp 1 ^ ℓ := by rw [← Real.exp_nat_mul, mul_one]
  have hbase : 2 * Real.exp 1 * D * T / ℓ = Real.exp 1 / (ℓ / (2 * D * T)) := by
    rw [div_div_eq_mul_div]
    ring
  rw [hexp, Real.exp_add, hpow, hbase, div_pow (Real.exp 1)]
  ring

/-- A number bounded by `N / a^ℓ` for every `a > 1`, with `ℓ ≥ 1`, is not positive. -/
theorem eq_zero_of_forall_le_div_pow {x N : ℝ} {ℓ : ℕ} (hℓ : 1 ≤ ℓ) (hx : 0 ≤ x)
    (h : ∀ a : ℝ, 1 < a → x ≤ N / a ^ ℓ) : x = 0 := by
  by_contra hne
  have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hne)
  have hN : 0 ≤ N := by
    by_contra hN
    have hneg : N / 2 ^ ℓ < 0 := div_neg_of_neg_of_pos (not_le.mp hN) (by positivity)
    linarith [h 2 one_lt_two]
  have ha : 1 < N / x + 2 := by linarith [div_nonneg hN hx]
  have hpow : N / x + 2 ≤ (N / x + 2) ^ ℓ := le_self_pow₀ ha.le (by omega)
  have hle : N / (N / x + 2) ^ ℓ ≤ N / (N / x + 2) :=
    div_le_div_of_nonneg_left hN (by linarith) hpow
  have hlt : N / (N / x + 2) < x := by
    rw [div_lt_iff₀ (by linarith)]
    nlinarith [div_mul_cancel₀ N hxpos.ne']
  linarith [h _ ha]

/-- **When `D T = 0` the escape probability is zero.** A probability obeying the bound (9.1) for
every `a > 1` vanishes at every radius `ℓ ≥ 1`. -/
theorem eq_zero_of_forall_escape_bound {x N D T : ℝ} {ℓ : ℕ} (hDT : D * T = 0) (hℓ : 1 ≤ ℓ)
    (hx : 0 ≤ x) (h : ∀ a : ℝ, 1 < a → x ≤ min 1 (N * Real.exp (D * (1 + 2 * a) * T) / a ^ ℓ)) :
    x = 0 :=
  eq_zero_of_forall_le_div_pow hℓ hx fun a ha ↦ by
    have hzero : D * (1 + 2 * a) * T = 0 := by linear_combination (1 + 2 * a) * hDT
    have hb := (h a ha).trans (min_le_right _ _)
    rwa [hzero, Real.exp_zero, mul_one] at hb

/-! ### Corollary 8.1: the coupling inequality -/

section Coupling

variable {Ω α : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ] {X Y : Ω → α}
  {E : Set Ω}

/-- **Outcomes equal off an event differ only on it.** If `X` and `Y` agree outside `E`, then
`P(X ∈ B) - P(Y ∈ B) = P(X ∈ B, E) - P(Y ∈ B, E)` for every set `B`. -/
theorem measureReal_preimage_sub_eq (hE : MeasurableSet E) (hagree : ∀ ω ∉ E, X ω = Y ω)
    (B : Set α) : μ.real (X ⁻¹' B) - μ.real (Y ⁻¹' B) =
      μ.real (X ⁻¹' B ∩ E) - μ.real (Y ⁻¹' B ∩ E) := by
  have hdiff : X ⁻¹' B \ E = Y ⁻¹' B \ E := by
    ext ω
    simp only [Set.mem_diff, Set.mem_preimage]
    constructor
    · rintro ⟨hω, hωE⟩
      exact ⟨by rwa [← hagree ω hωE], hωE⟩
    · rintro ⟨hω, hωE⟩
      exact ⟨by rwa [hagree ω hωE], hωE⟩
  have hX := measureReal_inter_add_diff (μ := μ) (s := X ⁻¹' B) hE
  have hY := measureReal_inter_add_diff (μ := μ) (s := Y ⁻¹' B) hE
  rw [hdiff] at hX
  linarith

/-- **Corollary 8.1, the coupling inequality at a set.** Two outcomes on one probability space
that agree off the event `E` have laws within `P(E)` at every set:
`|P(X ∈ B) - P(Y ∈ B)| ≤ P(E)`. -/
theorem abs_measureReal_preimage_sub_le (hE : MeasurableSet E) (hagree : ∀ ω ∉ E, X ω = Y ω)
    (B : Set α) : |μ.real (X ⁻¹' B) - μ.real (Y ⁻¹' B)| ≤ μ.real E := by
  rw [measureReal_preimage_sub_eq hE hagree, abs_sub_le_iff]
  have hXE : μ.real (X ⁻¹' B ∩ E) ≤ μ.real E := measureReal_mono Set.inter_subset_right
  have hYE : μ.real (Y ⁻¹' B ∩ E) ≤ μ.real E := measureReal_mono Set.inter_subset_right
  constructor <;> linarith [measureReal_nonneg (μ := μ) (s := X ⁻¹' B ∩ E),
    measureReal_nonneg (μ := μ) (s := Y ⁻¹' B ∩ E)]

/-- **Corollary 8.1, the total-variation form (9.3).** Outcomes in a finite set that agree off
`E` have laws within `P(E)` in `totalVariation`: `½ Σ_x |P(X = x) - P(Y = x)| ≤ P(E)`. -/
theorem totalVariation_measureReal_fiber_le [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (hX : Measurable X) (hY : Measurable Y) (hE : MeasurableSet E)
    (hagree : ∀ ω ∉ E, X ω = Y ω) :
    totalVariation (fun x ↦ μ.real (X ⁻¹' {x})) (fun x ↦ μ.real (Y ⁻¹' {x})) ≤ μ.real E := by
  show (∑ x, |μ.real (X ⁻¹' {x}) - μ.real (Y ⁻¹' {x})|) / 2 ≤ μ.real E
  have hfiber : ∀ Z : Ω → α, Measurable Z → ∑ x, μ.real (Z ⁻¹' {x} ∩ E) = μ.real E := by
    intro Z hZ
    have h := sum_measureReal_preimage_singleton (μ := μ.restrict E) Finset.univ
      (f := Z) fun x _ ↦ hZ (measurableSet_singleton x)
    simp only [Finset.coe_univ, Set.preimage_univ, measureReal_restrict_apply_univ] at h
    rw [← h]
    exact Finset.sum_congr rfl fun x _ ↦
      (measureReal_restrict_apply (hZ (measurableSet_singleton x))).symm
  have hpoint : ∀ x, |μ.real (X ⁻¹' {x}) - μ.real (Y ⁻¹' {x})| ≤
      μ.real (X ⁻¹' {x} ∩ E) + μ.real (Y ⁻¹' {x} ∩ E) := fun x ↦ by
    rw [measureReal_preimage_sub_eq hE hagree, abs_sub_le_iff]
    constructor <;> linarith [measureReal_nonneg (μ := μ) (s := X ⁻¹' {x} ∩ E),
      measureReal_nonneg (μ := μ) (s := Y ⁻¹' {x} ∩ E)]
  have hsum := Finset.sum_le_sum fun x (_ : x ∈ Finset.univ) ↦ hpoint x
  rw [Finset.sum_add_distrib, hfiber X hX, hfiber Y hY] at hsum
  linarith

end Coupling

end

end Descent.Pangenome.AncestralLocality
