/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Descent.Layer

assert_below Descent.Coalescent Descent.Pangenome Descent.PopGen Descent.Spectral Descent.Blindness Descent.Conditionals Descent.Portability Descent.Decision Descent.Program

namespace Descent.Foundations

/-!
# Discriminating reference evaluations

A *reference evaluation* is a theorem that states the VALUE of a definition at a
specific point, on the reasoning that an inequality or an invariance leaves a
whole family of bodies satisfying it and a value does not.  That reasoning is
correct only where the value depends on the part of the body under test, and
this corpus shipped two reference evaluations where it did not.

`demographicSpike_at_reference_point` read `demographicSpike 1 1 1 = 0`.  The
body is `4 * F * effectiveSubgroupSize n m`, and at `m = n` the effective
subgroup size is zero, so the whole product collapses and **every** constant in
front of it satisfies the theorem.  The docstring claimed the opposite.
Differential testing against `map/correctability.rs` measured the cost: a body
with `2` in place of `4` passes that reference point and every other reference
point in its arc, while disagreeing with the shipped calculator on 7275 of 30624
compared outputs.  `pcCorrectabilityMargin_at_reference_point` had the same
defect at the same point.

Moving those two theorems to a live point repairs two instances.  It does not
stop the next reference evaluation from being written at a collapse point, and
nothing about a vacuous reference point looks wrong: it is true, it is
kernel-checked, its axiom report is clean, and it pins nothing.

## What makes a point live

The honest content of "this point pins the body" is *discrimination*: there is a
competing body that the reference evaluation rejects.  A value that a competitor
also satisfies has told nobody anything, which is the same standard this
project's empirical tier already applies to a simulation MATCH -- an oracle
algebraically pinned to the formula under test cannot reject a competing
formula, so a MATCH with no competitor carried is worthless.

`ReferenceEvaluation` below is that standard as a structure.  Its
`discriminates` field is an obligation, and at a collapse point the obligation
is FALSE, so the term cannot be built.  A vacuous reference evaluation stops
being a true-but-empty theorem and becomes an unprovable one.
-/

/-- A reference evaluation together with the competitor it rejects.

    Building this term is the claim that evaluating `body` at `point` and
    getting `value` rules something out.  `competitor` is what it rules out, and
    `discriminates` is the proof that it does. -/
structure ReferenceEvaluation (α : Type*) where
  /-- The evaluation point. -/
  point : α
  /-- The definition under test. -/
  body : α → ℝ
  /-- The value the reference theorem states. -/
  value : ℝ
  /-- A competing body the reference evaluation is supposed to reject. -/
  competitor : α → ℝ
  /-- The reference theorem itself. -/
  evaluates : body point = value
  /-- **The obligation.**  The competitor does not produce the stated value, so
      the stated value distinguishes the body from it.  At a point where the
      body collapses this is false and the term does not exist. -/
  discriminates : competitor point ≠ value

/-- The competitor and the body genuinely differ at the point. -/
theorem ReferenceEvaluation.competitor_ne_body {α : Type*}
    (r : ReferenceEvaluation α) :
    r.competitor r.point ≠ r.body r.point := by
  rw [r.evaluates]
  exact r.discriminates

/-- **A rescaled competitor is detected exactly where the body is nonzero.**

This is the whole category in one line.  The error that reference points are
supposed to catch -- a wrong constant factor in front of an otherwise correct
body -- is a rescaling, and a rescaling changes the value at a point if and only
if the value at that point is not zero.  So the non-degeneracy obligation for
this (very common) class of competitor is not an ad-hoc side condition: it is
equivalent to discrimination. -/
theorem scale_competitor_ne_iff {α : Type*} (body : α → ℝ) (p : α) (c : ℝ)
    (hc : c ≠ 1) :
    c * body p ≠ body p ↔ body p ≠ 0 := by
  constructor
  · intro hne hzero
    exact hne (by rw [hzero, mul_zero])
  · intro hbody hcontra
    have hfactor : (c - 1) * body p = 0 := by
      rw [sub_mul, one_mul, hcontra, sub_self]
    rcases mul_eq_zero.mp hfactor with hc1 | hb
    · exact hc (by linarith)
    · exact hbody hb

/-- **A collapse point discriminates nothing, proved rather than warned about.**
Where the body vanishes, every rescaling of it agrees with it exactly, so no
value stated there can separate the body from a wrong constant. -/
theorem scale_competitor_eq_of_body_eq_zero {α : Type*} (body : α → ℝ) (p : α)
    (hzero : body p = 0) (c : ℝ) :
    c * body p = body p := by
  rw [hzero, mul_zero]

/-- The canonical way to build one: evaluate at a point where the body is
nonzero, and carry the rescaled body as the competitor.

    The `hlive` argument is the non-degeneracy obligation.  It is not a
    stylistic hypothesis -- `scale_competitor_ne_iff` proves it is exactly what
    discrimination against a rescaling requires. -/
noncomputable def ReferenceEvaluation.ofScale {α : Type*} (body : α → ℝ) (p : α)
    (c : ℝ) (hc : c ≠ 1) (hlive : body p ≠ 0) : ReferenceEvaluation α where
  point := p
  body := body
  value := body p
  competitor := fun x ↦ c * body x
  evaluates := rfl
  discriminates := (scale_competitor_ne_iff body p c hc).mpr hlive

@[simp]
theorem ReferenceEvaluation.ofScale_value {α : Type*} (body : α → ℝ) (p : α)
    (c : ℝ) (hc : c ≠ 1) (hlive : body p ≠ 0) :
    (ReferenceEvaluation.ofScale body p c hc hlive).value = body p := rfl

/-- **The class is inhabited**, so the obligation is discharageable and the
structure is not a way of making reference evaluations impossible altogether. -/
noncomputable def ReferenceEvaluation.witness : ReferenceEvaluation ℝ :=
  ReferenceEvaluation.ofScale (fun x ↦ x) 1 2 (by norm_num) (by norm_num)

theorem ReferenceEvaluation.nonempty : Nonempty (ReferenceEvaluation ℝ) :=
  ⟨ReferenceEvaluation.witness⟩

end Descent.Foundations
