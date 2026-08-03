/-
Copyright (c) 2026 Sauers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sauers
-/
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

namespace Calibrator

/-!
# Fiber surgery on an effect-size distribution, and what estimators can see

This file is self-contained. It needs no other part of this development, and it is
written so that it can be read without any of it: everything below is about a
distribution on the real line, a rule for moving mass around inside it, and which
summaries of the distribution notice.

## The setting

Split a distribution by *magnitude*. For each level `s > 0` the two values `+s` and
`-s` form a **fiber**, carrying masses `massPos` and `massNeg`. A **transfer** moves
mass `δ` from the negative side to the positive side of one fiber, leaving every other
fiber alone.

Two numbers describe a fiber: its **total** `massPos + massNeg`, which is how much mass
sits at magnitude `s`, and its **imbalance** `massPos - massNeg`, which is how that mass
is split between the two signs. A transfer preserves the total and changes the
imbalance — that is the whole of what it does (`transfer_total`, `transfer_imbalance`).

## The result

> **Even summaries see only totals; odd summaries see only imbalances.**

An even function contributes `total * f s` on each fiber and an odd one contributes
`imbalance * f s` (`contribution_of_even`, `contribution_of_odd`). Since a transfer
fixes totals and moves imbalances, **every even summary is blind to it and every odd
summary detects it** (`even_summary_blind_to_transfer`, `odd_summary_detects_transfer`).

## Why this is about effect sizes

Write the distribution as the distribution of per-variant effects `β`. The summaries
that current methods compute are even functions of `β`, one and all:

* heritability is `M · E[β²]` — even, `sq_isEven`;
* LD-score regression regresses a **squared** z-score on the LD score — even;
* stratified heritability is `E[β²]` blockwise — even in each block;
* method-of-moments polygenicity uses `E[β⁴]` — even, `fourthPower_isEven`.

So all of them factor through the magnitudes, all of them are constant on fibers, and
all are blind to any redistribution of effect mass between `+s` and `-s`. That is a
non-identifiability result for the whole class at once, and it is not an analogy: it is
the same computation in each case.

## The asymmetry, which is the useful part

This is **not** the same kind of invisibility as a limit on what an experiment can
measure. The signs of the effect estimates are present in the data. What makes the odd
part invisible here is the *choice* of summary, so the obstruction is method-relative
and it is repairable:

* the identity `β ↦ β` is odd (`id_isOdd`), so any signed average detects a transfer;
* `β ↦ β³` is odd (`cube_isOdd`), so signed third moments do;
* sign concordance across cohorts, and the signed correlation between estimates and an
  annotation, are of the same shape.

Most methods assume a symmetric effect prior, which sets every imbalance to zero by
fiat. `symmetric_prior_untestable_by_even_summaries` and
`symmetric_prior_testable_by_odd_summaries` say exactly what that assumption costs: no
even summary can test it, and an odd one can. The recommendation follows without any
further theory — if the question is whether effects are symmetrically distributed, do
not answer it with a statistic that is constant on the fibers the question is about.
-/

/-- A function is **even** when it cannot tell `x` from `-x`. -/
def IsEvenSummary (f : ℝ → ℝ) : Prop := ∀ x : ℝ, f (-x) = f x

/-- A function is **odd** when reflecting the argument reverses its sign. -/
def IsOddSummary (f : ℝ → ℝ) : Prop := ∀ x : ℝ, f (-x) = -f x

theorem sq_isEven : IsEvenSummary (fun x ↦ x ^ 2) := by
  intro x
  ring

theorem fourthPower_isEven : IsEvenSummary (fun x ↦ x ^ 4) := by
  intro x
  ring

theorem abs_isEven : IsEvenSummary (fun x ↦ |x|) := by
  intro x
  exact abs_neg x

theorem id_isOdd : IsOddSummary (fun x ↦ x) := by
  intro x
  rfl

theorem cube_isOdd : IsOddSummary (fun x ↦ x ^ 3) := by
  intro x
  ring

/-- **A fiber**: the two values `± level`, with the mass sitting on each.
it carries no modelling content and no free parameter.

Empirical status: UNTESTED. A bookkeeping object for one magnitude of a distribution; -/
structure Fiber where
  /-- The magnitude shared by the two values. -/
  level : ℝ
  /-- Mass at `+ level`. -/
  massPos : ℝ
  /-- Mass at `- level`. -/
  massNeg : ℝ

namespace Fiber

variable (F : Fiber)

/-- How much mass sits at this magnitude, regardless of sign.

Empirical status: DERIVED. A sum of the fiber's own masses; no free parameter. -/
def total : ℝ := F.massPos + F.massNeg

/-- How that mass is split between the two signs.

Empirical status: DERIVED. A difference of the fiber's own masses; no free parameter. -/
def imbalance : ℝ := F.massPos - F.massNeg

/-- What this fiber contributes to the average of `f`.

Empirical status: DERIVED. The fiber's share of an expectation; no free parameter. -/
def contribution (f : ℝ → ℝ) : ℝ := F.massPos * f F.level + F.massNeg * f (-F.level)

/-- **Move mass `δ` from the negative side to the positive side.** This is the surgery,
and it is the only thing done to the distribution anywhere below.

Empirical status: UNTESTED. A redistribution rule, not a claim about data. -/
def transfer (shift : ℝ) : Fiber :=
  { level := F.level, massPos := F.massPos + shift, massNeg := F.massNeg - shift }

/-- **A transfer preserves the total.** The magnitude distribution does not move. -/
theorem transfer_total (shift : ℝ) : (F.transfer shift).total = F.total := by
  unfold transfer total
  ring

/-- **A transfer shifts the imbalance by `2δ`.** This is the entire effect of the
surgery, and it is invisible to anything that reads only totals. -/
theorem transfer_imbalance (shift : ℝ) :
    (F.transfer shift).imbalance = F.imbalance + 2 * shift := by
  unfold transfer imbalance
  ring

/-- **An even summary reads the total and nothing else.** -/
theorem contribution_of_even {f : ℝ → ℝ} (hf : IsEvenSummary f) :
    F.contribution f = F.total * f F.level := by
  unfold contribution total
  rw [hf F.level]
  ring

/-- **An odd summary reads the imbalance and nothing else.** -/
theorem contribution_of_odd {f : ℝ → ℝ} (hf : IsOddSummary f) :
    F.contribution f = F.imbalance * f F.level := by
  unfold contribution imbalance
  rw [hf F.level]
  ring

/-- **Every even summary is blind to the surgery.**

Heritability, LD-score regression, stratified heritability and moment-based polygenicity
are all of this form, so all of them return the same value before and after any
redistribution of effect mass between `+s` and `-s`. -/
theorem even_summary_blind_to_transfer {f : ℝ → ℝ} (hf : IsEvenSummary f) (shift : ℝ) :
    (F.transfer shift).contribution f = F.contribution f := by
  rw [contribution_of_even _ hf, contribution_of_even _ hf, transfer_total]
  unfold transfer
  rfl

/-- **Every odd summary detects the surgery**, provided the transfer is real and the
summary does not happen to vanish at that magnitude.

The signs of the effect estimates are in the data, so this is not a limit on what can be
measured — it is a statement about which summaries are worth computing. -/
theorem odd_summary_detects_transfer {f : ℝ → ℝ} (hf : IsOddSummary f) {shift : ℝ}
    (hshift : shift ≠ 0) (hlevel : f F.level ≠ 0) :
    (F.transfer shift).contribution f ≠ F.contribution f := by
  rw [contribution_of_odd _ hf, contribution_of_odd _ hf]
  have hlevel_eq : (F.transfer shift).level = F.level := rfl
  rw [hlevel_eq, transfer_imbalance]
  intro hcontra
  have hzero : 2 * shift * f F.level = 0 := by nlinarith [hcontra]
  rcases mul_eq_zero.mp hzero with htwo | hf0
  · rcases mul_eq_zero.mp htwo with h2 | hs
    · norm_num at h2
    · exact hshift hs
  · exact hlevel hf0

end Fiber

/-- **A symmetric effect prior is untestable by even summaries.**

Two fibers with the same magnitude and the same total — one symmetric, one not — agree
in every even summary. So no amount of heritability, LD-score or moment-based
polygenicity evidence bears on whether the effect distribution is symmetric. -/
theorem symmetric_prior_untestable_by_even_summaries
    (F G : Fiber) (hlevel : F.level = G.level) (htotal : F.total = G.total)
    {f : ℝ → ℝ} (hf : IsEvenSummary f) :
    F.contribution f = G.contribution f := by
  rw [Fiber.contribution_of_even _ hf, Fiber.contribution_of_even _ hf, htotal, hlevel]

/-- **A symmetric effect prior is testable by odd summaries.**

The same two fibers are separated by any odd summary that does not vanish at their
magnitude, as soon as their imbalances differ. Signed estimates are available, so the
test is available; what is missing is only the decision to compute it. -/
theorem symmetric_prior_testable_by_odd_summaries
    (F G : Fiber) (hlevel : F.level = G.level)
    (himbalance : F.imbalance ≠ G.imbalance)
    {f : ℝ → ℝ} (hf : IsOddSummary f) (hnonzero : f F.level ≠ 0) :
    F.contribution f ≠ G.contribution f := by
  rw [Fiber.contribution_of_odd _ hf, Fiber.contribution_of_odd _ hf, hlevel]
  intro hcontra
  rw [← hlevel] at hcontra
  exact himbalance (mul_right_cancel₀ hnonzero hcontra)

/-- **The two halves together**, which is the statement worth carrying elsewhere: a
redistribution of mass within magnitude fibers is invisible to every even summary and
visible to every non-degenerate odd one.

The first half is a non-identifiability result for a named class of estimators. The
second half is why it is a methodological finding rather than an impossibility: the
information is in the data and the summaries in use discard it. -/
theorem surgery_invisible_to_even_visible_to_odd (F : Fiber) {shift : ℝ}
    (hshift : shift ≠ 0)
    {even odd : ℝ → ℝ} (heven : IsEvenSummary even) (hodd : IsOddSummary odd)
    (hnonzero : odd F.level ≠ 0) :
    (F.transfer shift).contribution even = F.contribution even ∧
      (F.transfer shift).contribution odd ≠ F.contribution odd :=
  ⟨F.even_summary_blind_to_transfer heven shift,
    F.odd_summary_detects_transfer hodd hshift hnonzero⟩

end Calibrator
