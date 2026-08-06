/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.Linkage.Barrier

assert_below Descent.PopGen Descent.Spectral Descent.Blindness Descent.Conditionals Descent.Portability Descent.Decision Descent.Program

/-!
# The barrier on a tree of modules

`Descent.Pangenome.Linkage.Barrier` proves the linkage law along a CHAIN, which is the shape
a pangenome interface system has.  The law does not need the chain.  It holds on any tree of
modules whose edges carry unrelated equivalence relations on the panel, and this file proves
that — which is where the statement stops being about pangenomes and becomes a counting
inequality about edge-coloured trees.

## The shape

`Arbor` is a rooted tree in first-child/next-sibling form: `child s t rest` is a module with
the subtree `t` attached across interface `s`, together with `rest`, the remaining children of
the same module.  `nil` is the empty list of children.  A tree with `n` edges therefore has
`n + 1` modules, and `Arbor.size` counts the edges.

Nothing relates the interfaces at different edges.  They may be nested, aligned,
adversarially misaligned, or share no structure at all; each is an arbitrary map `ι → ι` and
the theorem does not look at how two of them interact.

## The results

* `card_arborMosaicsFrom`, `card_arborMosaics` — the tree dynamic program, with the proof
  that it counts the labellings.  Tree derivations are serialised in first-child order, and
  the shape fixes every segment's length, which is what makes the serialisation injective.
* `log_card_add_arborPressure_le` — the barrier: `log m + ∑ H(J ∣ S_e) ≤ log |Ω|`, summing
  over EVERY edge of the tree.
* `pow_card_le_arborWidthProd_mul_card_arborMosaics` — `m ^ (|E| + 1) ≤ (∏ w_e) · |Ω|`
  between natural numbers, and `arborWidthProd_mul_card_arborMosaics_of_balanced` turns it
  into an equality for balanced edge relations.  So on a tree, as on a chain, balance is
  extremal and the bound is exact.

## Why the chain results are not superseded

`chainArbor` embeds a chain as a tree and `arborCount_chainArbor`, `size_chainArbor`,
`arborPressure_chainArbor`, `arborWidthProd_chainArbor` and `card_arborMosaics_chainArbor`
say every quantity agrees.  The chain file is kept because it is what the pangenome
application uses and because its switch grading has no tree analogue stated here, not because
its theorems are independent of these.

## Empirical status

None.  Every statement is a count of labellings of a finite tree, or a logarithm of one.

## What is not claimed

`Arbor` is a ROOTED tree, and the serialisation of a derivation depends on that root.  The
counts do not: `arborCount` at a module is the number of ways to complete its subtree, and
the total is a sum over root donors, which is the same number whichever module is called the
root.  That invariance is not proved here — the results are stated for the rooted object
actually built.
-/

namespace Descent.Pangenome.Linkage

open Finset

universe u

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

/-! ### Trees of modules -/

/-- A rooted tree of modules, in first-child/next-sibling form.  `child s t rest` attaches
the subtree `t` across interface `s` and carries `rest`, the remaining children of the same
module.  Each `child` is one edge, so a tree of `size` edges has `size + 1` modules. -/
inductive Arbor (ι : Type u) : Type u
  | nil : Arbor ι
  | child : (ι → ι) → Arbor ι → Arbor ι → Arbor ι

/-- The number of edges, equivalently the number of modules other than the root. -/
def Arbor.size : Arbor ι → ℕ
  | Arbor.nil => 0
  | Arbor.child _ t rest => 1 + t.size + rest.size

/-- The product of the occupied widths over every edge of the tree. -/
def arborWidthProd : Arbor ι → ℕ
  | Arbor.nil => 1
  | Arbor.child s t rest => width s * arborWidthProd t * arborWidthProd rest

theorem arborWidthProd_pos [Nonempty ι] (a : Arbor ι) : 0 < arborWidthProd a := by
  induction a with
  | nil => exact Nat.one_pos
  | child s t rest iht ihrest =>
    exact Nat.mul_pos (Nat.mul_pos (width_pos s) iht) ihrest

/-! ### The tree dynamic program and what it counts -/

/-- The number of ways to complete the subtree below a module supplied by donor `h`. -/
def arborCount : Arbor ι → ι → ℕ
  | Arbor.nil, _ => 1
  | Arbor.child s t rest, h => (∑ g ∈ fiber s h, arborCount t g) * arborCount rest h

theorem arborCount_pos (a : Arbor ι) (h : ι) : 0 < arborCount a h := by
  induction a generalizing h with
  | nil => exact Nat.one_pos
  | child s t rest iht ihrest =>
    exact Nat.mul_pos (Finset.sum_pos (fun g _ ↦ iht g) ⟨h, self_mem_fiber s h⟩) (ihrest h)

/-- The derivations completing the subtree below a module supplied by `h`, serialised in
first-child order.  The donor of the module itself is NOT in the list; it is the `h` the
list is indexed by, and the top-level `arborMosaics` puts it back. -/
def arborMosaicsFrom : Arbor ι → ι → Finset (List ι)
  | Arbor.nil, _ => {[]}
  | Arbor.child s t rest, h => (fiber s h).biUnion fun g ↦
      ((arborMosaicsFrom t g) ×ˢ (arborMosaicsFrom rest h)).image fun p ↦ g :: (p.1 ++ p.2)

/-- Every derivation over a tree names one donor per edge, in an order the shape fixes.
This is what makes the serialisation injective: the split point of `y ++ z` is determined by
the subtree, not by the donors. -/
theorem length_arborMosaicsFrom {a : Arbor ι} {h : ι} {x : List ι}
    (hx : x ∈ arborMosaicsFrom a h) : x.length = a.size := by
  induction a generalizing h x with
  | nil =>
    simp only [arborMosaicsFrom, Finset.mem_singleton] at hx
    simp [hx, Arbor.size]
  | child s t rest iht ihrest =>
    simp only [arborMosaicsFrom, Finset.mem_biUnion, Finset.mem_image, Finset.mem_product] at hx
    obtain ⟨g, -, p, ⟨hp1, hp2⟩, rfl⟩ := hx
    have h1 := iht hp1
    have h2 := ihrest hp2
    simp only [List.length_cons, List.length_append, Arbor.size]
    omega

/-- **The tree dynamic program counts the derivations.** -/
theorem card_arborMosaicsFrom (a : Arbor ι) (h : ι) :
    (arborMosaicsFrom a h).card = arborCount a h := by
  induction a generalizing h with
  | nil => simp [arborMosaicsFrom, arborCount]
  | child s t rest iht ihrest =>
    have hdisj : ((fiber s h : Finset ι) : Set ι).PairwiseDisjoint
        fun g ↦ ((arborMosaicsFrom t g) ×ˢ (arborMosaicsFrom rest h)).image
          fun p ↦ g :: (p.1 ++ p.2) := by
      intro g₁ _ g₂ _ hne
      refine Finset.disjoint_left.mpr fun x hx₁ hx₂ ↦ hne ?_
      obtain ⟨p₁, -, rfl⟩ := Finset.mem_image.mp hx₁
      obtain ⟨p₂, -, hEq⟩ := Finset.mem_image.mp hx₂
      injection hEq with hg _
      exact hg.symm
    rw [arborMosaicsFrom, Finset.card_biUnion hdisj, arborCount, Finset.sum_mul]
    refine Finset.sum_congr rfl fun g _ ↦ ?_
    have hinj : ∀ p₁ ∈ (arborMosaicsFrom t g) ×ˢ (arborMosaicsFrom rest h),
        ∀ p₂ ∈ (arborMosaicsFrom t g) ×ˢ (arborMosaicsFrom rest h),
        g :: (p₁.1 ++ p₁.2) = g :: (p₂.1 ++ p₂.2) → p₁ = p₂ := by
      intro p₁ hp₁ p₂ hp₂ hEq
      rw [Finset.mem_product] at hp₁ hp₂
      injection hEq with _ hApp
      have hlen : p₁.1.length = p₂.1.length := by
        rw [length_arborMosaicsFrom hp₁.1, length_arborMosaicsFrom hp₂.1]
      obtain ⟨h1, h2⟩ := List.append_inj hApp hlen
      exact Prod.ext h1 h2
    rw [Finset.card_image_of_injOn hinj, Finset.card_product, iht g, ihrest h]

/-- Every derivation over the tree, with the root module's donor at the head. -/
def arborMosaics (a : Arbor ι) : Finset (List ι) :=
  Finset.univ.biUnion fun h ↦ (arborMosaicsFrom a h).image (h :: ·)

theorem card_arborMosaics (a : Arbor ι) :
    (arborMosaics a).card = ∑ h : ι, arborCount a h := by
  have hdisj : ((Finset.univ : Finset ι) : Set ι).PairwiseDisjoint
      fun h ↦ (arborMosaicsFrom a h).image (h :: ·) := by
    intro h₁ _ h₂ _ hne
    refine Finset.disjoint_left.mpr fun x hx₁ hx₂ ↦ hne ?_
    obtain ⟨y₁, -, rfl⟩ := Finset.mem_image.mp hx₁
    obtain ⟨y₂, -, hEq⟩ := Finset.mem_image.mp hx₂
    injection hEq with hh _
    exact hh.symm
  rw [arborMosaics, Finset.card_biUnion hdisj]
  refine Finset.sum_congr rfl fun h _ ↦ ?_
  rw [Finset.card_image_of_injective _ (fun y₁ y₂ hy ↦ by injection hy), card_arborMosaicsFrom]

theorem card_arborMosaics_pos [Nonempty ι] (a : Arbor ι) : 0 < (arborMosaics a).card := by
  rw [card_arborMosaics]
  exact Finset.sum_pos (fun h _ ↦ arborCount_pos a h) Finset.univ_nonempty

/-! ### The barrier, edge by edge

The potential is the same one the chain carries, and it gains an edge's `identityLoss` by the
same `meanLog_step`.  What the tree adds is that a module with several children multiplies
its children's counts, and `meanLog` turns that product into a sum. -/

omit [DecidableEq ι] in
theorem meanLog_mul [Nonempty ι] (u v : ι → ℝ) (hu : ∀ h, 0 < u h) (hv : ∀ h, 0 < v h) :
    meanLog (fun h ↦ u h * v h) = meanLog u + meanLog v := by
  have hlog : ∀ h : ι, Real.log (u h * v h) = Real.log (u h) + Real.log (v h) := fun h ↦
    Real.log_mul (ne_of_gt (hu h)) (ne_of_gt (hv h))
  rw [meanLog, meanLog, meanLog, Finset.sum_congr rfl fun h _ ↦ hlog h, Finset.sum_add_distrib,
    mul_add]

/-- **Linkage-entropy pressure over a tree**: the identity every edge forgets, summed. -/
noncomputable def arborPressure : Arbor ι → ℝ
  | Arbor.nil => 0
  | Arbor.child s t rest => identityLoss s + arborPressure t + arborPressure rest

theorem arborPressure_le_meanLog [Nonempty ι] (a : Arbor ι) :
    arborPressure a ≤ meanLog fun h ↦ (arborCount a h : ℝ) := by
  induction a with
  | nil => simp [arborPressure, meanLog, arborCount]
  | child s t rest iht ihrest =>
    have hpt : ∀ h : ι, (0 : ℝ) < (arborCount t h : ℝ) := fun h ↦ by
      exact_mod_cast arborCount_pos t h
    have hpr : ∀ h : ι, (0 : ℝ) < (arborCount rest h : ℝ) := fun h ↦ by
      exact_mod_cast arborCount_pos rest h
    have hstep := meanLog_step s (fun h ↦ (arborCount t h : ℝ)) hpt
    have hsumpos : ∀ h : ι, (0 : ℝ) < ∑ g ∈ fiber s h, (arborCount t g : ℝ) := fun h ↦
      Finset.sum_pos (fun g _ ↦ hpt g) ⟨h, self_mem_fiber s h⟩
    have hsplit : meanLog (fun h ↦ (arborCount (Arbor.child s t rest) h : ℝ))
        = meanLog (fun h ↦ ∑ g ∈ fiber s h, (arborCount t g : ℝ))
          + meanLog fun h ↦ (arborCount rest h : ℝ) := by
      rw [← meanLog_mul _ _ hsumpos hpr]
      refine congrArg meanLog (funext fun h ↦ ?_)
      rw [arborCount, Nat.cast_mul, Nat.cast_sum]
    rw [arborPressure, hsplit]
    linarith

/-- **The linkage–entropy barrier on a tree.**  Identity forgotten at every edge, whatever
the edges' relations are and however they overlap, reappears additively as capacity. -/
theorem log_card_add_arborPressure_le [Nonempty ι] (a : Arbor ι) :
    Real.log (Fintype.card ι : ℝ) + arborPressure a
      ≤ Real.log ((arborMosaics a).card : ℝ) := by
  have hpos : ∀ h : ι, (0 : ℝ) < (arborCount a h : ℝ) := fun h ↦ by
    exact_mod_cast arborCount_pos a h
  have hsum : ((arborMosaics a).card : ℝ) = ∑ h : ι, (arborCount a h : ℝ) := by
    rw [card_arborMosaics, Nat.cast_sum]
  have hAM := meanLog_le_log_sum (fun h ↦ (arborCount a h : ℝ)) hpos
  have hchain := arborPressure_le_meanLog a
  rw [hsum]
  linarith

/-! ### The width law on a tree -/

theorem log_arborWidthProd_le_arborPressure [Nonempty ι] (a : Arbor ι) :
    (a.size : ℝ) * Real.log (Fintype.card ι : ℝ) - Real.log (arborWidthProd a : ℝ)
      ≤ arborPressure a := by
  induction a with
  | nil => simp [Arbor.size, arborWidthProd, arborPressure]
  | child s t rest iht ihrest =>
    have hw : (0 : ℝ) < (width s : ℝ) := by exact_mod_cast width_pos s
    have hwt : (0 : ℝ) < (arborWidthProd t : ℝ) := by exact_mod_cast arborWidthProd_pos t
    have hwr : (0 : ℝ) < (arborWidthProd rest : ℝ) := by exact_mod_cast arborWidthProd_pos rest
    have hedge := log_card_sub_log_width_le_identityLoss s
    have hlog : Real.log (arborWidthProd (Arbor.child s t rest) : ℝ)
        = Real.log (width s : ℝ) + Real.log (arborWidthProd t : ℝ)
          + Real.log (arborWidthProd rest : ℝ) := by
      rw [arborWidthProd, Nat.cast_mul, Nat.cast_mul,
        Real.log_mul (by positivity) (ne_of_gt hwr),
        Real.log_mul (ne_of_gt hw) (ne_of_gt hwt)]
    rw [arborPressure, hlog, Arbor.size]
    push_cast
    linarith

/-- **The width law on a tree.**  A tree of `n` edges of occupied widths `w_e` over a panel of
`m` threads admits at least `m ^ (n+1) / ∏ w_e` derivations, stated without division. -/
theorem pow_card_le_arborWidthProd_mul_card_arborMosaics [Nonempty ι] (a : Arbor ι) :
    Fintype.card ι ^ (a.size + 1) ≤ arborWidthProd a * (arborMosaics a).card := by
  have hwpos : 0 < arborWidthProd a := arborWidthProd_pos a
  have hOpos : 0 < (arborMosaics a).card := card_arborMosaics_pos a
  have hwR : (0 : ℝ) < ((arborWidthProd a : ℕ) : ℝ) := by exact_mod_cast hwpos
  have hOR : (0 : ℝ) < (((arborMosaics a).card : ℕ) : ℝ) := by exact_mod_cast hOpos
  have hbar := log_card_add_arborPressure_le a
  have hpress := log_arborWidthProd_le_arborPressure a
  have hlog : Real.log (((Fintype.card ι ^ (a.size + 1) : ℕ) : ℝ))
      ≤ Real.log ((((arborWidthProd a) * (arborMosaics a).card : ℕ) : ℝ)) := by
    rw [Nat.cast_pow, Real.log_pow, Nat.cast_mul,
      Real.log_mul (ne_of_gt hwR) (ne_of_gt hOR)]
    push_cast
    linarith
  exact_mod_cast (Real.log_le_log_iff (by positivity) (by positivity)).mp hlog

/-! ### Balance is extremal on a tree too -/

/-- `ArborBalanced a b` says every edge of `a` has all its fibers of one size, and `b` is the
product of those sizes. -/
inductive ArborBalanced : Arbor ι → ℕ → Prop
  | nil : ArborBalanced Arbor.nil 1
  | child {s : ι → ι} {t rest : Arbor ι} {b bt br : ℕ} :
      (∀ h, fiberCard s h = b) → ArborBalanced t bt → ArborBalanced rest br →
      ArborBalanced (Arbor.child s t rest) (b * bt * br)

theorem arborCount_of_balanced {a : Arbor ι} {b : ℕ} (hb : ArborBalanced a b) (h : ι) :
    arborCount a h = b := by
  induction hb generalizing h with
  | nil => simp [arborCount]
  | @child s t rest b bt br hfib _ _ iht ihrest =>
    have hcard : (fiber s h).card = b := hfib h
    rw [arborCount, Finset.sum_congr rfl (fun g _ ↦ iht g), Finset.sum_const, smul_eq_mul,
      hcard, ihrest h]

theorem card_arborMosaics_of_balanced {a : Arbor ι} {b : ℕ} (hb : ArborBalanced a b) :
    (arborMosaics a).card = Fintype.card ι * b := by
  rw [card_arborMosaics, Finset.sum_congr rfl fun h _ ↦ arborCount_of_balanced hb h,
    Finset.sum_const, Finset.card_univ, smul_eq_mul]

/-- Each edge contributes `w_e · b_e = m`, so the widths and the balanced fiber sizes
multiply to one factor of `m` per edge. -/
theorem arborWidthProd_mul_of_balanced {a : Arbor ι} {b : ℕ} (hb : ArborBalanced a b) :
    arborWidthProd a * b = Fintype.card ι ^ a.size := by
  induction hb with
  | nil => simp [arborWidthProd, Arbor.size]
  | @child s t rest b bt br hfib _ _ iht ihrest =>
    have hw := width_mul_of_balanced hfib
    rw [arborWidthProd, Arbor.size]
    calc width s * arborWidthProd t * arborWidthProd rest * (b * bt * br)
        = width s * b * ((arborWidthProd t * bt) * (arborWidthProd rest * br)) := by ring
      _ = Fintype.card ι * (Fintype.card ι ^ t.size * Fintype.card ι ^ rest.size) := by
          rw [hw, iht, ihrest]
      _ = Fintype.card ι ^ (1 + t.size + rest.size) := by
          rw [pow_add, pow_add, pow_one]
          ring

/-- **The tree width law is exact.**  Balanced edge relations turn the inequality into an
equality, whatever the tree's shape and however the edges' partitions overlap. -/
theorem arborWidthProd_mul_card_arborMosaics_of_balanced {a : Arbor ι} {b : ℕ}
    (hb : ArborBalanced a b) :
    arborWidthProd a * (arborMosaics a).card = Fintype.card ι ^ (a.size + 1) := by
  rw [card_arborMosaics_of_balanced hb, pow_succ]
  calc arborWidthProd a * (Fintype.card ι * b)
      = arborWidthProd a * b * Fintype.card ι := by ring
    _ = Fintype.card ι ^ a.size * Fintype.card ι := by rw [arborWidthProd_mul_of_balanced hb]

/-! ### A chain is a tree

Every quantity the chain file defines agrees with the tree quantity of the embedded chain, so
the chain barrier is this barrier at a tree with one child per module. -/

/-- A chain, as a tree in which every module has exactly one child. -/
def chainArbor : Chain ι → Arbor ι
  | [] => Arbor.nil
  | s :: c => Arbor.child s (chainArbor c) Arbor.nil

omit [Fintype ι] [DecidableEq ι] in
theorem size_chainArbor (c : Chain ι) : (chainArbor c).size = c.length := by
  induction c with
  | nil => rfl
  | cons s c ih =>
    simp only [chainArbor, Arbor.size, ih, List.length_cons]
    omega

theorem arborCount_chainArbor (c : Chain ι) (h : ι) :
    arborCount (chainArbor c) h = derivationCount c h := by
  induction c generalizing h with
  | nil => rfl
  | cons s c ih =>
    rw [chainArbor, arborCount, derivationCount, Finset.sum_congr rfl fun g _ ↦ ih g]
    simp [arborCount]

theorem arborPressure_chainArbor (c : Chain ι) :
    arborPressure (chainArbor c) = linkagePressure c := by
  induction c with
  | nil => simp [chainArbor, arborPressure, linkagePressure]
  | cons s c ih => rw [chainArbor, arborPressure, ih, linkagePressure_cons]; simp [arborPressure]

theorem arborWidthProd_chainArbor (c : Chain ι) :
    arborWidthProd (chainArbor c) = (c.map width).prod := by
  induction c with
  | nil => rfl
  | cons s c ih => simp [chainArbor, arborWidthProd, ih]

theorem card_arborMosaics_chainArbor (c : Chain ι) :
    (arborMosaics (chainArbor c)).card = (mosaics c).card := by
  rw [card_arborMosaics, card_mosaics]
  exact Finset.sum_congr rfl fun h _ ↦ arborCount_chainArbor c h

end Descent.Pangenome.Linkage
