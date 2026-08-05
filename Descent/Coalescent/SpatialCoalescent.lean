/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Coalescent.Lookdown
import Descent.Coalescent.Pedigree
import Mathlib.Tactic

namespace Descent

/-!
# Spatial coalescents: the voter model's dual is a pedigree

`Descent.Coalescent.Structured` carries the structured coalescent at the level of its rates,
and `Descent.Coalescent.Program` recorded spatial coalescents -- coalescing random walks, the
voter model, the stepping stone -- as absent.  They were absent for a reason worth naming:
the corpus had no mechanism in which a lineage could MOVE, only rates at which lineages in
labelled boxes coalesce.

The mechanism is short.  In the voter model a site adopts a neighbour's opinion, which is
exactly `Descent.Coalescent.Lookdown.lookdownApply` with the two levels read as two sites.
Trace an opinion backwards and it walks: from the site that holds it now to the site it was
copied from, one step per update.  Two opinions are identical exactly when their backward
walks have met.  That is the duality between the voter model and coalescing random walks,
and `voterConfig_eq_ancestor` is it -- proved by induction, with no probability in it.

  `c_t = c_0 ∘ A_t`,   where `A_{t+1} = A_t ∘ σ_t` and `σ_t` is the update's copy map.

The consequence is that a spatial coalescent is not a new kind of object.  `A_t` is built by
composing maps on sites exactly as `Descent.Coalescent.Pedigree`'s ancestor map is built by
composing parent maps, so `voterPedigree` presents the voter dual AS a pedigree and the
structural theory transfers unchanged: `ℛ_0 = Δ`, `ℛ_s ⊆ ℛ_{s+1}`, `Θ` is "the sample has a
common ancestor", and sub-sampling commutes with tracing.  A migration model needs no new
theorems about relations; it needs a different parent map.

The second half of the file is the reduction every spatial argument starts from.  Two
lineages on `ℤ` performing independent steps meet exactly when their DIFFERENCE walk hits
zero (`meet_iff_difference_walk_zero`), and the difference of two walks is a walk
(`walk_sub`).  So pairwise coalescence in space is a hitting-time problem for a single walk,
which is why recurrence decides whether spatial lineages coalesce at all.

## What is proved, and what is not

PROVED: the duality identity, the pedigree presentation and everything it inherits, and the
difference-walk reduction.  All pathwise, for arbitrary update sequences and arbitrary steps.

NOT PROVED: that the difference walk is recurrent in one and two dimensions and transient in
three or more -- hence that spatial lineages in low dimension coalesce almost surely and in
high dimension need not.  That is a theorem about random walks, not about genealogy, and
Mathlib does not have it.  Nor is the diffusive rescaling to the Brownian web here, nor
Cox-Griffeath's clustering rates.

## Main results

- `voterStepMap`, `voterConfig`, `voterAncestor`: the mechanism and its dual.
- `voterConfig_eq_ancestor`: **`c_t = c_0 ∘ A_t`**, the duality.
- `voterPedigree`, `voterAncestralRel`: the dual presented as a pedigree, inheriting
  `Descent.Coalescent.Pedigree`'s structure theorems.
- `walk_sub`, `meet_iff_difference_walk_zero`: pairwise coalescence is a hitting time.
-/

namespace Coalescent

/-! ### The voter model, and its dual -/

/-- The copy map of one voter update: site `j` copies site `i`, everything else stays.  This
is `Lookdown.lookdownApply` read on sites rather than levels, and it is the map the backward
lineage follows. -/
def voterStepMap {n : ℕ} (u : Fin n × Fin n) : Fin n → Fin n :=
  fun l ↦ if l = u.2 then u.1 else l

/-- The configuration of opinions after `t` updates. -/
def voterConfig {n : ℕ} {α : Type*} (u : ℕ → Fin n × Fin n) (c₀ : Fin n → α) :
    ℕ → Fin n → α
  | 0 => c₀
  | t + 1 => lookdownApply (u t).1 (u t).2 (voterConfig u c₀ t)

/-- The backward lineage after `t` updates: where the opinion now at a site came from. -/
def voterAncestor {n : ℕ} (u : ℕ → Fin n × Fin n) : ℕ → Fin n → Fin n
  | 0 => id
  | t + 1 => fun l ↦ voterAncestor u t (voterStepMap (u t) l)

/-- **The duality.**  The opinion at a site after `t` updates is the initial opinion at the
site its backward lineage reaches: `c_t = c_0 ∘ A_t`.

Forward the voter model spreads opinions; backward the same maps carry lineages, and the two
descriptions are one composition read in two directions.  Everything the coalescent says
about spatial models is downstream of this line. -/
theorem voterConfig_eq_ancestor {n : ℕ} {α : Type*} (u : ℕ → Fin n × Fin n)
    (c₀ : Fin n → α) (t : ℕ) :
    voterConfig u c₀ t = c₀ ∘ voterAncestor u t := by
  induction t with
  | zero => rfl
  | succ p ih =>
      funext l
      show lookdownApply (u p).1 (u p).2 (voterConfig u c₀ p) l
        = c₀ (voterAncestor u p (voterStepMap (u p) l))
      unfold lookdownApply voterStepMap
      by_cases hl : l = (u p).2
      · simp only [hl, if_pos rfl]
        rw [ih]
        rfl
      · simp only [if_neg hl]
        rw [ih]
        rfl

/-- **Two opinions agree exactly when their lineages have met.**  The coalescing-walk
description of the voter model, as an equivalence rather than an analogy. -/
theorem voterConfig_eq_iff {n : ℕ} {α : Type*} (u : ℕ → Fin n × Fin n) (c₀ : Fin n → α)
    (t : ℕ) (x y : Fin n) (hinj : Function.Injective c₀) :
    voterConfig u c₀ t x = voterConfig u c₀ t y ↔ voterAncestor u t x = voterAncestor u t y := by
  rw [voterConfig_eq_ancestor]
  exact ⟨fun h ↦ hinj h, fun h ↦ congrArg c₀ h⟩

/-! ### The dual is a pedigree -/

/-- **The voter dual, presented as a pedigree.**  Each update's copy map is a parent map, so
`Descent.Coalescent.Pedigree` applies verbatim and the spatial model inherits `ℛ_0 = Δ`,
`ℛ_s ⊆ ℛ_{s+1}`, the characterisation of `Θ`, and restriction consistency without a single
new theorem about relations.

Empirical status: NOT AN EMPIRICAL CLAIM.  It renames one construction as another; which
updates occur is the model, and a spatial one restricts the pairs `(i,j)` to neighbours. -/
def voterPedigree {n : ℕ} (u : ℕ → Fin n × Fin n) : Pedigree n :=
  fun s ↦ voterStepMap (u s)

/-- The spatial coalescent's state: which sampled sites share an opinion-ancestor.  It is
`Pedigree.ancestralRel` of the voter pedigree, so every structural theorem there is a
theorem here. -/
def voterAncestralRel {m n : ℕ} (u : ℕ → Fin n × Fin n) (sample : Fin m → Fin n) (s : ℕ) :
    ER m :=
  ancestralRel (voterPedigree u) sample s

/-- **`ℛ_0 = Δ` for the spatial model**, inherited: distinct sampled sites start unrelated. -/
theorem voterAncestralRel_zero {m n : ℕ} (u : ℕ → Fin n × Fin n) {sample : Fin m → Fin n}
    (hs : Function.Injective sample) : voterAncestralRel u sample 0 = Delta m :=
  ancestralRel_zero _ hs

/-- **`ℛ_s ⊆ ℛ_{s+1}` for the spatial model**, inherited: lineages that have met stay met,
whatever the geometry. -/
theorem voterAncestralRel_le_succ {m n : ℕ} (u : ℕ → Fin n × Fin n)
    (sample : Fin m → Fin n) (s : ℕ) :
    voterAncestralRel u sample s ≤ voterAncestralRel u sample (s + 1) :=
  ancestralRel_le_succ _ sample s

/-- **Restriction consistency for the spatial model**, inherited: a sub-sample of sites has
the sub-relation, pathwise. -/
theorem restrict_voterAncestralRel {l m n : ℕ} (h : l ≤ m) (u : ℕ → Fin n × Fin n)
    (sample : Fin m → Fin n) (s : ℕ) :
    restrict h (voterAncestralRel u sample s)
      = voterAncestralRel u (sample ∘ Fin.castLE h) s :=
  restrict_ancestralRel h _ sample s

/-! ### Coalescing walks on `ℤ` -/

/-- A walk on `ℤ` from `x₀` with the given increments. -/
def walk (x₀ : ℤ) (step : ℕ → ℤ) : ℕ → ℤ
  | 0 => x₀
  | t + 1 => walk x₀ step t + step t

@[simp] theorem walk_zero (x₀ : ℤ) (step : ℕ → ℤ) : walk x₀ step 0 = x₀ := rfl

@[simp] theorem walk_succ (x₀ : ℤ) (step : ℕ → ℤ) (t : ℕ) :
    walk x₀ step (t + 1) = walk x₀ step t + step t := rfl

/-- **The difference of two walks is a walk.**  With increments the differences of the
increments -- so two lineages moving independently are one lineage moving with the difference
step, and everything about their meeting is a statement about a single walk. -/
theorem walk_sub (x₀ y₀ : ℤ) (ξ η : ℕ → ℤ) (t : ℕ) :
    walk x₀ ξ t - walk y₀ η t = walk (x₀ - y₀) (fun s ↦ ξ s - η s) t := by
  induction t with
  | zero => rfl
  | succ p ih =>
      show walk x₀ ξ p + ξ p - (walk y₀ η p + η p)
        = walk (x₀ - y₀) (fun s ↦ ξ s - η s) p + (ξ p - η p)
      rw [← ih]
      ring

/-- **Two lineages meet exactly when the difference walk is at zero.**  Pairwise coalescence
in space is a hitting-time problem, which is why the dimension of the space decides whether
lineages coalesce: recurrence of the difference walk is the whole question.

That recurrence is not proved here, and `Descent.Coalescent.Program` records it as absent --
it is a theorem about random walks rather than about genealogy. -/
theorem meet_iff_difference_walk_zero (x₀ y₀ : ℤ) (ξ η : ℕ → ℤ) (t : ℕ) :
    walk x₀ ξ t = walk y₀ η t ↔ walk (x₀ - y₀) (fun s ↦ ξ s - η s) t = 0 := by
  rw [← walk_sub, sub_eq_zero]

/-- A lineage that never moves is a pedigree lineage: with zero increments the walk stands
still, which is the panmictic case `Descent.Coalescent.Structured` contrasts migration
against. -/
@[simp] theorem walk_zero_step (x₀ : ℤ) (t : ℕ) : walk x₀ (fun _ ↦ 0) t = x₀ := by
  induction t with
  | zero => rfl
  | succ p ih =>
      show walk x₀ (fun _ ↦ 0) p + 0 = x₀
      rw [ih]
      ring

end Coalescent

end Descent
