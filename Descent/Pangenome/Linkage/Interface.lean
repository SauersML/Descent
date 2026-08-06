/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic
import Descent.Layer

assert_below Descent.PopGen Descent.Spectral Descent.Blindness
assert_below Descent.Conditionals Descent.Portability Descent.Decision Descent.Program

/-!
# What one pangenome interface forgets

A pangenome graph compresses a panel of haplotypes by merging homologous sequence, and the
merge that saves topology also forgets which thread entered the merged state.  This file
measures one such merge.  `Descent.Pangenome.Linkage.Chain` composes the measurements along
an ordered chain of interfaces, and `Descent.Pangenome.Linkage.Barrier` turns the total into
a count of the mosaic paths the topology is thereby forced to admit.

## The model

A panel is a finite type `ι` of thread identities.  An interface is a map `s : ι → ι`: the
graph state each thread occupies there.  Only the FIBERS of that map carry meaning — two
threads are indistinguishable at the interface exactly when `s` sends them to the same
value — so nothing below inspects a state's name, and `occupies_iff` records that the
codomain may be taken to be the panel itself without loss.  That is why the state type is
`ι` rather than a second parameter per interface: at most `Fintype.card ι` states are
occupied, an unoccupied state is invisible to every definition here, and a uniform codomain
is what lets a chain of interfaces be an ordinary `List`.

## The measurements

* `fiber`, `fiberCard`: the threads sharing a thread's state, and how many.
* `width`: the number of OCCUPIED states, the `w` of the width law.
* `identityLoss`: `(1/m) ∑ log (fiberCard)`, in nats.  For a uniform panel this is exactly
  the conditional entropy `H(J ∣ S)` of thread identity given graph state, which is the
  unit in which everything downstream is denominated.
* `stateFreq`, `imbalance`: the state-frequency vector `q` and its Kullback–Leibler
  divergence from uniform.

## The results

* `sum_mul_log_le_log_sum` — weighted Jensen for `Real.log`, from `log x ≤ x - 1` and
  nothing else.  It is the group's only CONVEXITY input: the chain law, the tree law, the
  width law, the imbalance tax and the frequency-weighted law are all this inequality
  applied to different weights.  Monotonicity of `log` is used as well, to clear the
  logarithms out of the width law; nothing else analytic is.
* `sum_mul_log_div_nonneg` — Gibbs: relative entropy is nonnegative.
* `identityLoss_eq_width_add_imbalance` — `H(J ∣ S) = log (m/w) + D(q ‖ u)`.
* `imbalance_nonneg`, and hence `log_card_sub_log_width_le_identityLoss` — an interface of
  occupied width `w` forgets at least `log (m/w)` nats, with equality exactly at balance.
* `identityLoss_le_comp`, `width_comp_le` — coarsening an interface can only forget more and
  occupy fewer states, so the bound downstream is monotone in how much a builder merges.

## Empirical status

None.  Every declaration in this file is a statement about a finite partition and its
logarithms; a measurement disagreeing with one of them would be an arithmetic error rather
than an observation.  What carries empirical weight is the reading of `identityLoss` as
`H(J ∣ S)` for a panel drawn uniformly, and that reading is stated in the docstrings as an
interpretation of the algebra rather than asserted as a fact about any panel.
-/

namespace Descent.Pangenome.Linkage

open Finset

universe u

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

/-! ### Fibers, widths, and the generality of the encoding -/

/-- The threads whose graph state at interface `s` is `a`. -/
def stateFiber (s : ι → ι) (a : ι) : Finset ι := Finset.univ.filter fun g ↦ s g = a

/-- The threads that interface `s` cannot tell apart from `h`. -/
def fiber (s : ι → ι) (h : ι) : Finset ι := stateFiber s (s h)

/-- How many panel threads share `h`'s graph state at interface `s`. -/
def fiberCard (s : ι → ι) (h : ι) : ℕ := (fiber s h).card

/-- The number of OCCUPIED graph states at interface `s`.  States no thread reaches are
invisible to every statement here, which is what makes this the right `w`. -/
def width (s : ι → ι) : ℕ := (Finset.univ.image s).card

@[simp] theorem mem_stateFiber {s : ι → ι} {a g : ι} : g ∈ stateFiber s a ↔ s g = a := by
  simp [stateFiber]

@[simp] theorem mem_fiber {s : ι → ι} {h g : ι} : g ∈ fiber s h ↔ s g = s h := by
  simp [fiber]

theorem self_mem_fiber (s : ι → ι) (h : ι) : h ∈ fiber s h := by simp

theorem fiber_eq_of_mem {s : ι → ι} {h g : ι} (hg : g ∈ fiber s h) :
    fiber s g = fiber s h := by
  simp only [mem_fiber] at hg
  simp [fiber, hg]

theorem fiberCard_pos (s : ι → ι) (h : ι) : 0 < fiberCard s h :=
  Finset.card_pos.mpr ⟨h, self_mem_fiber s h⟩

theorem fiberCard_eq_of_mem {s : ι → ι} {h g : ι} (hg : g ∈ fiber s h) :
    fiberCard s g = fiberCard s h := by
  simp [fiberCard, fiber_eq_of_mem hg]

theorem card_stateFiber_pos {s : ι → ι} {a : ι} (ha : a ∈ Finset.univ.image s) :
    0 < (stateFiber s a).card := by
  obtain ⟨h, -, rfl⟩ := Finset.mem_image.mp ha
  exact Finset.card_pos.mpr ⟨h, by simp⟩

theorem width_pos [Nonempty ι] (s : ι → ι) : 0 < width s :=
  Finset.card_pos.mpr
    ⟨s (Classical.arbitrary ι), Finset.mem_image_of_mem s (Finset.mem_univ _)⟩

theorem width_le_card (s : ι → ι) : width s ≤ Fintype.card ι := by
  simpa [width, Finset.card_univ] using Finset.card_image_le (s := Finset.univ) (f := s)

omit [Fintype ι] [DecidableEq ι] in
/-- **The encoding costs no generality.**  Any way of declaring two threads indistinguishable
at an interface — any setoid on the panel — is the fiber relation of a map `ι → ι`, so
taking the state type to be the panel itself excludes no interface.  This is what licenses
`Chain ι := List (ι → ι)`: one codomain for every interface in a chain. -/
theorem exists_stateMap (r : Setoid ι) :
    ∃ s : ι → ι, ∀ g h : ι, s g = s h ↔ r.r g h := by
  classical
  refine ⟨fun a ↦ (Quotient.mk r a).out, fun g h ↦ ?_⟩
  constructor
  · intro hgh
    have h1 : (Quotient.mk r g) = (Quotient.mk r h) := by
      have hcong := congrArg (Quotient.mk r) hgh
      simpa [Quotient.out_eq] using hcong
    exact Quotient.exact h1
  · intro hgh
    exact congrArg Quotient.out (Quotient.sound hgh)

/-! ### Regrouping a sum over the fibers of an interface

Both halves of the group's arithmetic are this one lemma: the width identity below, and the
step inequality of `Descent.Pangenome.Linkage.Barrier` that carries a geometric mean across
an interface. -/

/-- A sum over the panel, regrouped over the occupied states of an interface. -/
theorem sum_fiberwise {M : Type*} [AddCommMonoid M] (s : ι → ι) (f : ι → M) :
    ∑ a ∈ Finset.univ.image s, ∑ h ∈ stateFiber s a, f h = ∑ h, f h := by
  have hdisj : (↑(Finset.univ.image s) : Set ι).PairwiseDisjoint (stateFiber s) := by
    intro a _ b _ hab
    refine Finset.disjoint_left.mpr fun x hxa hxb ↦ ?_
    simp only [mem_stateFiber] at hxa hxb
    exact hab (by rw [← hxa]; exact hxb)
  have hcover : (Finset.univ.image s).biUnion (stateFiber s) = Finset.univ := by
    ext h
    simp only [Finset.mem_univ, iff_true, Finset.mem_biUnion]
    exact ⟨s h, Finset.mem_image_of_mem s (Finset.mem_univ h), by simp⟩
  rw [← Finset.sum_biUnion hdisj, hcover]

/-- The panel size, regrouped over occupied states. -/
theorem sum_card_stateFiber (s : ι → ι) :
    ∑ a ∈ Finset.univ.image s, (stateFiber s a).card = Fintype.card ι := by
  simpa [stateFiber, Finset.card_univ] using
    (Finset.card_eq_sum_card_image s Finset.univ).symm

/-- **The width, read off the fiber sizes.**  Each occupied state contributes its own
reciprocal weight exactly once, so the reciprocal fiber sizes sum to the number of states. -/
theorem sum_inv_fiberCard (s : ι → ι) :
    ∑ h : ι, ((fiberCard s h : ℝ))⁻¹ = width s := by
  rw [← sum_fiberwise s fun h ↦ ((fiberCard s h : ℝ))⁻¹]
  have hinner : ∀ a ∈ Finset.univ.image s,
      ∑ h ∈ stateFiber s a, ((fiberCard s h : ℝ))⁻¹ = 1 := by
    intro a ha
    have hconst : ∀ h ∈ stateFiber s a,
        ((fiberCard s h : ℝ))⁻¹ = (((stateFiber s a).card : ℝ))⁻¹ := by
      intro h hh
      simp only [mem_stateFiber] at hh
      simp [fiberCard, fiber, hh]
    have hne : ((stateFiber s a).card : ℝ) ≠ 0 := by
      exact_mod_cast Nat.pos_iff_ne_zero.mp (card_stateFiber_pos ha)
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul, mul_inv_cancel₀ hne]
  rw [Finset.sum_congr rfl hinner, Finset.sum_const, nsmul_eq_mul, mul_one, width]

/-! ### The one analytic input

Everything the group proves about logarithms comes from `Real.log_le_sub_one_of_pos`, by way
of the two lemmas here.  Isolating them is deliberate: the chain law, the width law and the
imbalance tax then differ only in which weights they are handed. -/

/-- **Weighted Jensen for the logarithm.**  The mean of logarithms is at most the logarithm
of the mean. -/
theorem sum_mul_log_le_log_sum {κ : Type*} (t : Finset κ) (w z : κ → ℝ)
    (hw : ∀ i ∈ t, 0 ≤ w i) (hw1 : ∑ i ∈ t, w i = 1) (hz : ∀ i ∈ t, 0 < z i) :
    ∑ i ∈ t, w i * Real.log (z i) ≤ Real.log (∑ i ∈ t, w i * z i) := by
  obtain ⟨i₀, hi₀t, hi₀⟩ : ∃ i ∈ t, 0 < w i := by
    by_contra hcon
    push_neg at hcon
    have hzero : ∑ i ∈ t, w i = 0 :=
      Finset.sum_eq_zero fun i hi ↦ le_antisymm (hcon i hi) (hw i hi)
    rw [hw1] at hzero
    exact one_ne_zero hzero
  set A := ∑ i ∈ t, w i * z i with hA
  have hApos : 0 < A := by
    rw [hA]
    exact Finset.sum_pos' (fun i hi ↦ mul_nonneg (hw i hi) (hz i hi).le)
      ⟨i₀, hi₀t, mul_pos hi₀ (hz i₀ hi₀t)⟩
  have step : ∀ i ∈ t, w i * (Real.log (z i) - Real.log A) ≤ w i * (z i * A⁻¹ - 1) := by
    intro i hi
    have h1 : Real.log (z i / A) ≤ z i / A - 1 :=
      Real.log_le_sub_one_of_pos (div_pos (hz i hi) hApos)
    rw [Real.log_div (ne_of_gt (hz i hi)) (ne_of_gt hApos), div_eq_mul_inv] at h1
    exact mul_le_mul_of_nonneg_left h1 (hw i hi)
  have hsum := Finset.sum_le_sum step
  have hL : ∑ i ∈ t, w i * (Real.log (z i) - Real.log A)
      = (∑ i ∈ t, w i * Real.log (z i)) - Real.log A := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hw1, one_mul]
  have hR : ∑ i ∈ t, w i * (z i * A⁻¹ - 1) = 0 := by
    have hstep : ∑ i ∈ t, w i * (z i * A⁻¹ - 1)
        = (∑ i ∈ t, w i * z i) * A⁻¹ - ∑ i ∈ t, w i := by
      simp only [mul_sub, mul_one, Finset.sum_sub_distrib, ← mul_assoc, ← Finset.sum_mul]
    rw [hstep, hw1, ← hA, mul_inv_cancel₀ (ne_of_gt hApos), sub_self]
  linarith

/-- **Gibbs' inequality.**  Relative entropy between two laws on the same finite set is
nonnegative. -/
theorem sum_mul_log_div_nonneg {κ : Type*} (t : Finset κ) (q z : κ → ℝ)
    (hq0 : ∀ i ∈ t, 0 < q i) (hq1 : ∑ i ∈ t, q i = 1)
    (hz0 : ∀ i ∈ t, 0 < z i) (hz1 : ∑ i ∈ t, z i = 1) :
    0 ≤ ∑ i ∈ t, q i * Real.log (q i / z i) := by
  have hJ := sum_mul_log_le_log_sum t q (fun i ↦ z i / q i)
    (fun i hi ↦ (hq0 i hi).le) hq1 (fun i hi ↦ div_pos (hz0 i hi) (hq0 i hi))
  have hsum : ∑ i ∈ t, q i * (z i / q i) = 1 := by
    rw [← hz1]
    exact Finset.sum_congr rfl fun i hi ↦ by
      have hqi : q i ≠ 0 := ne_of_gt (hq0 i hi)
      field_simp
  rw [hsum, Real.log_one] at hJ
  have hsplit1 : ∑ i ∈ t, q i * Real.log (z i / q i)
      = (∑ i ∈ t, q i * Real.log (z i)) - ∑ i ∈ t, q i * Real.log (q i) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i hi ↦ by
      rw [Real.log_div (ne_of_gt (hz0 i hi)) (ne_of_gt (hq0 i hi)), mul_sub]
  have hsplit2 : ∑ i ∈ t, q i * Real.log (q i / z i)
      = (∑ i ∈ t, q i * Real.log (q i)) - ∑ i ∈ t, q i * Real.log (z i) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i hi ↦ by
      rw [Real.log_div (ne_of_gt (hq0 i hi)) (ne_of_gt (hz0 i hi)), mul_sub]
  linarith

omit [DecidableEq ι] in
/-- **Arithmetic–geometric mean over the panel**, the uniform-weight case of
`sum_mul_log_le_log_sum`. -/
theorem mean_log_le_log_mean [Nonempty ι] (v : ι → ℝ) (hv : ∀ h, 0 < v h) :
    (Fintype.card ι : ℝ)⁻¹ * ∑ h, Real.log (v h)
      ≤ Real.log ((Fintype.card ι : ℝ)⁻¹ * ∑ h, v h) := by
  have hcard : (0 : ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  have hw1 : ∑ _h : ι, (Fintype.card ι : ℝ)⁻¹ = 1 := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_inv_cancel₀ (ne_of_gt hcard)]
  have key := sum_mul_log_le_log_sum Finset.univ (fun _ ↦ (Fintype.card ι : ℝ)⁻¹) v
    (fun _ _ ↦ by positivity) hw1 (fun i _ ↦ hv i)
  rw [Finset.mul_sum, Finset.mul_sum]
  exact key

/-! ### The identity an interface forgets -/

/-- **The identity a single interface forgets**, in nats.

For a thread `J` drawn uniformly from the panel and `S = s J` its graph state, this is
exactly the conditional entropy `H(J ∣ S)`: the residual uncertainty about which haplotype
arrived, once the topology has said only which state it is in.  Written as a mean over
threads rather than over states, so that `sum_fiberwise` moves it either way. -/
noncomputable def identityLoss (s : ι → ι) : ℝ :=
  (Fintype.card ι : ℝ)⁻¹ * ∑ h : ι, Real.log (fiberCard s h : ℝ)

/-- The fraction of the panel occupying graph state `a`: the vector `q` of the width law. -/
noncomputable def stateFreq (s : ι → ι) (a : ι) : ℝ :=
  ((stateFiber s a).card : ℝ) / (Fintype.card ι : ℝ)

/-- **The imbalance tax**: the Kullback–Leibler divergence, in nats, of the state-frequency
vector from the uniform law on the occupied states. -/
noncomputable def imbalance (s : ι → ι) : ℝ :=
  ∑ a ∈ Finset.univ.image s, stateFreq s a * Real.log (stateFreq s a * (width s : ℝ))

theorem identityLoss_nonneg (s : ι → ι) : 0 ≤ identityLoss s := by
  refine mul_nonneg (by positivity) (Finset.sum_nonneg fun h _ ↦ ?_)
  exact Real.log_natCast_nonneg _

theorem stateFreq_pos [Nonempty ι] {s : ι → ι} {a : ι} (ha : a ∈ Finset.univ.image s) :
    0 < stateFreq s a := by
  have hn : (0 : ℝ) < ((stateFiber s a).card : ℝ) := by exact_mod_cast card_stateFiber_pos ha
  have hm : (0 : ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  exact div_pos hn hm

theorem sum_stateFreq [Nonempty ι] (s : ι → ι) :
    ∑ a ∈ Finset.univ.image s, stateFreq s a = 1 := by
  have hcard : ((Fintype.card ι : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  simp only [stateFreq, div_eq_mul_inv, ← Finset.sum_mul, ← Nat.cast_sum, sum_card_stateFiber]
  exact mul_inv_cancel₀ hcard

/-- `identityLoss` regrouped over occupied states: `H(J ∣ S) = ∑ q_a log n_a`. -/
theorem identityLoss_eq [Nonempty ι] (s : ι → ι) :
    identityLoss s
      = ∑ a ∈ Finset.univ.image s, stateFreq s a * Real.log ((stateFiber s a).card : ℝ) := by
  rw [identityLoss, ← sum_fiberwise s fun h ↦ Real.log (fiberCard s h : ℝ), Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  have hconst : ∀ h ∈ stateFiber s a,
      Real.log (fiberCard s h : ℝ) = Real.log ((stateFiber s a).card : ℝ) := by
    intro h hh
    simp only [mem_stateFiber] at hh
    simp [fiberCard, fiber, hh]
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul, stateFreq]
  ring

/-- **The width-plus-imbalance law for one interface**: `H(J ∣ S) = log (m/w) + D(q ‖ u)`.

The identity a merge forgets splits into a part fixed by how many states it leaves occupied
and a part paid for merging them unevenly.  Both terms are nonnegative, and the second
vanishes exactly at balance. -/
theorem identityLoss_eq_width_add_imbalance [Nonempty ι] (s : ι → ι) :
    identityLoss s
      = Real.log (Fintype.card ι : ℝ) - Real.log (width s : ℝ) + imbalance s := by
  have hm : (0 : ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  have hw : (0 : ℝ) < (width s : ℝ) := by exact_mod_cast width_pos s
  have hterm : ∀ a ∈ Finset.univ.image s,
      stateFreq s a * Real.log ((stateFiber s a).card : ℝ)
        = stateFreq s a * (Real.log (Fintype.card ι : ℝ) - Real.log (width s : ℝ))
          + stateFreq s a * Real.log (stateFreq s a * (width s : ℝ)) := by
    intro a ha
    have hn : (0 : ℝ) < ((stateFiber s a).card : ℝ) := by exact_mod_cast card_stateFiber_pos ha
    have hq : stateFreq s a * (width s : ℝ)
        = ((stateFiber s a).card : ℝ) * (width s : ℝ) / (Fintype.card ι : ℝ) := by
      rw [stateFreq]; ring
    rw [hq, Real.log_div (by positivity) (ne_of_gt hm),
      Real.log_mul (ne_of_gt hn) (ne_of_gt hw), stateFreq]
    ring
  rw [identityLoss_eq, Finset.sum_congr rfl hterm, Finset.sum_add_distrib, ← Finset.sum_mul,
    sum_stateFreq, one_mul, imbalance]

/-- **The imbalance tax is a tax.**  Uneven merging forgets strictly more identity than even
merging at the same occupied width. -/
theorem imbalance_nonneg [Nonempty ι] (s : ι → ι) : 0 ≤ imbalance s := by
  have hw : (0 : ℝ) < (width s : ℝ) := by exact_mod_cast width_pos s
  have huniform : ∑ _a ∈ Finset.univ.image s, ((width s : ℝ))⁻¹ = 1 := by
    rw [Finset.sum_const, nsmul_eq_mul]
    show ((width s : ℝ)) * ((width s : ℝ))⁻¹ = 1
    exact mul_inv_cancel₀ (ne_of_gt hw)
  have key := sum_mul_log_div_nonneg (Finset.univ.image s) (stateFreq s)
    (fun _ ↦ ((width s : ℝ))⁻¹) (fun a ha ↦ stateFreq_pos ha) (sum_stateFreq s)
    (fun _ _ ↦ by positivity) huniform
  have hterm : ∀ a ∈ Finset.univ.image s,
      stateFreq s a * Real.log (stateFreq s a / ((width s : ℝ))⁻¹)
        = stateFreq s a * Real.log (stateFreq s a * (width s : ℝ)) := by
    intro a _
    rw [div_eq_mul_inv, inv_inv]
  rwa [Finset.sum_congr rfl hterm, ← imbalance] at key

/-! ### Merging states only forgets more

An interface is coarsened by composing its state map with anything: `φ ∘ s` cannot tell apart
two threads that `s` could not.  Both measures move the way they must. -/

theorem fiber_subset_comp (s φ : ι → ι) (h : ι) : fiber s h ⊆ fiber (φ ∘ s) h := by
  intro g hg
  simp only [mem_fiber] at hg ⊢
  simp [hg]

theorem width_comp_le (s φ : ι → ι) : width (φ ∘ s) ≤ width s := by
  have himg : Finset.univ.image (φ ∘ s) = (Finset.univ.image s).image φ := by
    rw [Finset.image_image]
  rw [width, width, himg]
  exact Finset.card_image_le

/-- **Coarsening an interface cannot reduce the identity it forgets.**  Linkage-entropy
pressure is monotone under merging graph states, so a construction that merges more can only
raise the bound of `Descent.Pangenome.Linkage.Barrier`, never lower it. -/
theorem identityLoss_le_comp (s φ : ι → ι) : identityLoss s ≤ identityLoss (φ ∘ s) := by
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun h _ ↦ ?_) (by positivity)
  refine Real.log_le_log (by exact_mod_cast fiberCard_pos s h) ?_
  exact_mod_cast Finset.card_le_card (fiber_subset_comp s φ h)

/-- **An interface of occupied width `w` forgets at least `log (m/w)` nats.**  This is the
width law for one cut; `Descent.Pangenome.Linkage.Barrier` adds it along a chain. -/
theorem log_card_sub_log_width_le_identityLoss [Nonempty ι] (s : ι → ι) :
    Real.log (Fintype.card ι : ℝ) - Real.log (width s : ℝ) ≤ identityLoss s := by
  have h := identityLoss_eq_width_add_imbalance s
  have hi := imbalance_nonneg s
  linarith

/-- Equality in the width law is exactly balance. -/
theorem identityLoss_eq_log_ratio_iff [Nonempty ι] (s : ι → ι) :
    identityLoss s = Real.log (Fintype.card ι : ℝ) - Real.log (width s : ℝ)
      ↔ imbalance s = 0 := by
  have h := identityLoss_eq_width_add_imbalance s
  constructor <;> intro hh <;> linarith

end Descent.Pangenome.Linkage
