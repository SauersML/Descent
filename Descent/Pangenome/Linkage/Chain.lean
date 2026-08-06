/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.Linkage.Interface

assert_below Descent.PopGen Descent.Spectral Descent.Blindness Descent.Conditionals Descent.Portability Descent.Decision Descent.Program

/-!
# The mosaic language of an interface chain

`Descent.Pangenome.Linkage.Interface` measures what one separator forgets.  This file builds
the object that measurement is about: the set of ancestry-resolved derivations a chain of
separators admits, together with the recursion that counts them without enumerating them.

## The language

A chain is a `List (ι → ι)`, one state map per interface, in the order the panel threads
cross them.  A derivation is the list of donors supplying the modules between consecutive
interfaces, and it is legal exactly when consecutive donors occupy the same state at the
interface they meet at.  `mosaicsFrom c h` collects the legal derivations whose first module
comes from `h`, and `mosaics c` collects all of them.  The `m` constant lists are the panel
threads themselves; every other member is a donor mosaic.

## One recursion, three readings

`sum_mosaicsFrom` is the only structural fact used below: a sum over the derivations of
`s :: c` regroups as a sum over the fiber of `s` of sums over the derivations of `c`.  The
count, the balanced product formula and the switch grading are that lemma under three
choices of summand, which is why none of them is proved twice.

* `card_mosaicsFrom`, `card_mosaics` — the dynamic program of the counting section, and its
  proof that it counts what it claims to.  `O(m·r)` arithmetic operations, no path
  enumeration.
* `card_mosaics_of_balanced` — with every fiber of interface `j` of size `b j`, the language
  has exactly `m · ∏ b j` members.  This is the extremal case: the width law of
  `Descent.Pangenome.Linkage.Barrier` is attained here, and attained no matter how the
  partitions at different interfaces overlap.
* `sum_pow_switches_mosaicsFrom`, `switchPolynomial_of_balanced` — the switch-grading
  generating function `∑ z ^ switches`, which factorises as `m · ∏ (1 + (b j - 1) z)` in the
  balanced case.  Setting `z = 1` recovers the count; the coefficient of `z ^ k` says how
  many mosaics recombine `k` times, so the explosion is not a thin shell of one-switch
  errors.

## Empirical status

None.  A derivation is a list of donors and the results here count lists; a panel would have
to be misdescribed, not mismeasured, for one of them to fail.  The claim that these lists
correspond to paths through a sequence graph is made — and carries its hypotheses — in
`Descent.Pangenome.Linkage.Splicing`.
-/

namespace Descent.Pangenome.Linkage

open Finset

universe u

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

/-! ### The compatible language -/

/-- An ordered interface chain: one state map per separator, in crossing order. -/
abbrev Chain (ι : Type u) : Type u := List (ι → ι)

/-- The ancestry-resolved derivations over `c` whose first module is supplied by donor `h`.
A derivation over a chain of `r` interfaces is a list of `r + 1` donors, and switching is
permitted only between donors sharing a state at the interface they meet at. -/
def mosaicsFrom : Chain ι → ι → Finset (List ι)
  | [], h => {[h]}
  | s :: c, h => (fiber s h).biUnion fun g ↦ (mosaicsFrom c g).image (h :: ·)

/-- Every ancestry-resolved derivation over the chain `c`. -/
def mosaics (c : Chain ι) : Finset (List ι) := Finset.univ.biUnion (mosaicsFrom c)

/-- A derivation records its own first donor, which is what keeps the branches of the
recursion below disjoint. -/
theorem mem_mosaicsFrom_head {c : Chain ι} {h : ι} {x : List ι} (hx : x ∈ mosaicsFrom c h) :
    ∃ t, x = h :: t := by
  cases c with
  | nil =>
    simp only [mosaicsFrom, Finset.mem_singleton] at hx
    exact ⟨[], hx⟩
  | cons s c =>
    simp only [mosaicsFrom, Finset.mem_biUnion, Finset.mem_image] at hx
    obtain ⟨g, -, y, -, rfl⟩ := hx
    exact ⟨y, rfl⟩

/-- A derivation over `r` interfaces names a donor for each of the `r + 1` modules. -/
theorem length_of_mem_mosaicsFrom {c : Chain ι} {h : ι} {x : List ι}
    (hx : x ∈ mosaicsFrom c h) : x.length = c.length + 1 := by
  induction c generalizing h x with
  | nil =>
    simp only [mosaicsFrom, Finset.mem_singleton] at hx
    simp [hx]
  | cons s c ih =>
    simp only [mosaicsFrom, Finset.mem_biUnion, Finset.mem_image] at hx
    obtain ⟨g, -, y, hy, rfl⟩ := hx
    simp [ih hy]

theorem mosaicsFrom_nonempty (c : Chain ι) (h : ι) : (mosaicsFrom c h).Nonempty := by
  induction c generalizing h with
  | nil => exact ⟨[h], by simp [mosaicsFrom]⟩
  | cons s c ih =>
    obtain ⟨y, hy⟩ := ih h
    exact ⟨h :: y, by
      simp only [mosaicsFrom, Finset.mem_biUnion, Finset.mem_image]
      exact ⟨h, self_mem_fiber s h, y, hy, rfl⟩⟩

/-! ### The one structural lemma

Everything counted below is a sum over `mosaics`, and every such sum is evaluated by this
regrouping.  Stating it for an arbitrary commutative monoid is what lets the plain count and
the switch-graded count share a proof. -/

/-- **Sums over a chain's derivations regroup over the first interface's fiber.** -/
theorem sum_mosaicsFrom {M : Type*} [AddCommMonoid M] (s : ι → ι) (c : Chain ι) (h : ι)
    (F : List ι → M) :
    ∑ x ∈ mosaicsFrom (s :: c) h, F x
      = ∑ g ∈ fiber s h, ∑ y ∈ mosaicsFrom c g, F (h :: y) := by
  have hdisj : ((fiber s h : Finset ι) : Set ι).PairwiseDisjoint
      fun g ↦ (mosaicsFrom c g).image (h :: ·) := by
    intro g₁ _ g₂ _ hne
    refine Finset.disjoint_left.mpr fun x hx₁ hx₂ ↦ hne ?_
    obtain ⟨y₁, hy₁, rfl⟩ := Finset.mem_image.mp hx₁
    obtain ⟨y₂, hy₂, hEq⟩ := Finset.mem_image.mp hx₂
    obtain ⟨t₁, rfl⟩ := mem_mosaicsFrom_head hy₁
    obtain ⟨t₂, rfl⟩ := mem_mosaicsFrom_head hy₂
    injection hEq with _ hTail
    injection hTail with hg _
    exact hg.symm
  rw [mosaicsFrom, Finset.sum_biUnion hdisj]
  refine Finset.sum_congr rfl fun g _ ↦ ?_
  exact Finset.sum_image fun y₁ _ y₂ _ hy ↦ by injection hy

/-- The same regrouping at the top: a sum over all derivations is a sum over first donors. -/
theorem sum_mosaics {M : Type*} [AddCommMonoid M] (c : Chain ι) (F : List ι → M) :
    ∑ x ∈ mosaics c, F x = ∑ h : ι, ∑ x ∈ mosaicsFrom c h, F x := by
  have hdisj : ((Finset.univ : Finset ι) : Set ι).PairwiseDisjoint (mosaicsFrom c) := by
    intro h₁ _ h₂ _ hne
    refine Finset.disjoint_left.mpr fun x hx₁ hx₂ ↦ hne ?_
    obtain ⟨t₁, rfl⟩ := mem_mosaicsFrom_head hx₁
    obtain ⟨t₂, hEq⟩ := mem_mosaicsFrom_head hx₂
    injection hEq with hh _
  rw [mosaics, Finset.sum_biUnion hdisj]

/-! ### The dynamic program -/

/-- The number of legal continuations of a prefix ending at donor `h`: the chain form of the
tree dynamic program.  Each interface costs one pass over the panel, so the whole count is
`O(m·r)` arithmetic operations and never enumerates a path. -/
def derivationCount : Chain ι → ι → ℕ
  | [], _ => 1
  | s :: c, h => ∑ g ∈ fiber s h, derivationCount c g

theorem derivationCount_pos (c : Chain ι) (h : ι) : 0 < derivationCount c h := by
  induction c generalizing h with
  | nil => exact Nat.one_pos
  | cons s c ih =>
    exact Finset.sum_pos (fun g _ ↦ ih g) ⟨h, self_mem_fiber s h⟩

/-- **The dynamic program counts the language it claims to.** -/
theorem card_mosaicsFrom (c : Chain ι) (h : ι) :
    (mosaicsFrom c h).card = derivationCount c h := by
  induction c generalizing h with
  | nil => simp [mosaicsFrom, derivationCount]
  | cons s c ih =>
    rw [Finset.card_eq_sum_ones, sum_mosaicsFrom, derivationCount]
    refine Finset.sum_congr rfl fun g _ ↦ ?_
    rw [← ih g, Finset.card_eq_sum_ones]

/-- The size of the whole compatible language, from the same recursion. -/
theorem card_mosaics (c : Chain ι) :
    (mosaics c).card = ∑ h : ι, derivationCount c h := by
  rw [Finset.card_eq_sum_ones, sum_mosaics]
  exact Finset.sum_congr rfl fun h _ ↦ by
    rw [← Finset.card_eq_sum_ones, card_mosaicsFrom]

/-! ### The balanced case is exact

At a fixed occupied width, the fibers can be balanced or not.  Balanced is the extremal
choice, and the count there is a bare product — with no condition relating the partitions at
different interfaces, because a chain has no cycle along which a consistency condition could
propagate. -/

/-- `Balanced c bs` says interface `j` of `c` has every fiber of size `bs[j]`. -/
inductive Balanced : Chain ι → List ℕ → Prop
  | nil : Balanced [] []
  | cons {s : ι → ι} {c : Chain ι} {b : ℕ} {bs : List ℕ} :
      (∀ h, fiberCard s h = b) → Balanced c bs → Balanced (s :: c) (b :: bs)

/-- A balanced interface splits the panel evenly: `w · b = m`. -/
theorem width_mul_of_balanced {s : ι → ι} {b : ℕ} (hb : ∀ h, fiberCard s h = b) :
    width s * b = Fintype.card ι := by
  have hconst : ∀ a ∈ Finset.univ.image s, (stateFiber s a).card = b := by
    intro a ha
    obtain ⟨h, -, rfl⟩ := Finset.mem_image.mp ha
    exact hb h
  rw [← sum_card_stateFiber s, Finset.sum_congr rfl hconst, Finset.sum_const, smul_eq_mul, width]

theorem derivationCount_of_balanced {c : Chain ι} {bs : List ℕ} (hb : Balanced c bs) (h : ι) :
    derivationCount c h = bs.prod := by
  induction hb generalizing h with
  | nil => simp [derivationCount]
  | @cons s c b bs hfib _ ih =>
    have hcard : (fiber s h).card = b := hfib h
    rw [derivationCount, Finset.sum_congr rfl (fun g _ ↦ ih g), Finset.sum_const, smul_eq_mul,
      hcard, List.prod_cons]

/-- **The balanced chain counts exactly `m · ∏ b`.**

This is the extremal theorem: the width law cannot do better, and the value does not depend
on how the partitions at different interfaces overlap. -/
theorem card_mosaics_of_balanced {c : Chain ι} {bs : List ℕ} (hb : Balanced c bs) :
    (mosaics c).card = Fintype.card ι * bs.prod := by
  rw [card_mosaics, Finset.sum_congr rfl fun h _ ↦ derivationCount_of_balanced hb h,
    Finset.sum_const, Finset.card_univ, smul_eq_mul]

/-! ### The switch grading

Counting mosaics hides how recombinant they are.  The same recursion, carrying a formal
weight `z` on each donor change, resolves the count by number of switches. -/

/-- The number of interfaces at which a derivation changes donor. -/
def switches : List ι → ℕ
  | [] => 0
  | [_] => 0
  | a :: b :: t => (if a = b then 0 else 1) + switches (b :: t)

/-- The switch-graded derivation count: the dynamic program with a weight `z` charged at
every donor change. -/
noncomputable def switchPolynomial : Chain ι → ι → ℝ → ℝ
  | [], _, _ => 1
  | s :: c, h, z => ∑ g ∈ fiber s h, (if h = g then 1 else z) * switchPolynomial c g z

/-- **The graded count is what the graded recursion computes.**  At `z = 1` this is
`card_mosaicsFrom`; at general `z` the coefficient of `z ^ k` counts the `k`-switch
mosaics. -/
theorem sum_pow_switches_mosaicsFrom (c : Chain ι) (h : ι) (z : ℝ) :
    ∑ x ∈ mosaicsFrom c h, z ^ switches x = switchPolynomial c h z := by
  induction c generalizing h with
  | nil => simp [mosaicsFrom, switchPolynomial, switches]
  | cons s c ih =>
    rw [sum_mosaicsFrom, switchPolynomial]
    refine Finset.sum_congr rfl fun g _ ↦ ?_
    rw [← ih g, Finset.mul_sum]
    refine Finset.sum_congr rfl fun y hy ↦ ?_
    obtain ⟨t, rfl⟩ := mem_mosaicsFrom_head hy
    by_cases hhg : h = g
    · subst hhg
      simp [switches]
    · rw [switches, if_neg hhg, if_neg hhg, pow_add, pow_one, mul_comm]

/-- **The switch spectrum of a balanced chain factorises.**  Interface `j` contributes
`1 + (b j - 1) z`: one way not to switch, and `b j - 1` ways to switch inside its fiber. -/
theorem switchPolynomial_of_balanced {c : Chain ι} {bs : List ℕ} (hb : Balanced c bs) (h : ι)
    (z : ℝ) :
    switchPolynomial c h z = (bs.map fun b : ℕ ↦ 1 + ((b : ℝ) - 1) * z).prod := by
  induction hb generalizing h with
  | nil => simp [switchPolynomial]
  | @cons s c b bs hfib _ ih =>
    have hcard : (fiber s h).card = b := hfib h
    have hsplit : ∀ g : ι,
        (if h = g then (1 : ℝ) else z) = z + (if h = g then 1 - z else 0) := by
      intro g
      by_cases hhg : h = g <;> simp [hhg]
    rw [switchPolynomial, Finset.sum_congr rfl (fun g _ ↦ by rw [ih g]), ← Finset.sum_mul,
      Finset.sum_congr rfl (fun g _ ↦ hsplit g), Finset.sum_add_distrib, Finset.sum_const,
      Finset.sum_ite_eq, if_pos (self_mem_fiber s h), nsmul_eq_mul, hcard, List.map_cons,
      List.prod_cons]
    ring

/-- The whole language's switch spectrum, summed over first donors. -/
theorem sum_pow_switches_mosaics_of_balanced {c : Chain ι} {bs : List ℕ} (hb : Balanced c bs)
    (z : ℝ) :
    ∑ x ∈ mosaics c, z ^ switches x
      = (Fintype.card ι : ℝ) * (bs.map fun b : ℕ ↦ 1 + ((b : ℝ) - 1) * z).prod := by
  rw [sum_mosaics, Finset.sum_congr rfl fun h _ ↦ sum_pow_switches_mosaicsFrom c h z,
    Finset.sum_congr rfl fun h _ ↦ switchPolynomial_of_balanced hb h z, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul]

end Descent.Pangenome.Linkage
