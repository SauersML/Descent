/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.UniversalMetricIdentification
import Mathlib.Computability.Halting
import Mathlib.Analysis.SpecificLimits.Basic

assert_below Descent.Decision Descent.Program

/-!
# What "any input, all outputs" cannot promise: an expectation that decides halting

This is NOTE2 §10. Draw a step budget `N ≥ 1` with `P(N = k+1) = 2^{-(k+1)}`, simulate a
machine for `N` steps, and pay `2^N` exactly when the machine first halts at step `N` and
zero otherwise. Every run of this experiment terminates after finitely many simulated steps,
and the payout is a bounded rational number on each run, yet `expectedPayout_eq_one_iff`
proves the expectation is `1` when the machine halts on the given input and `0` when it does
not.

The simulation is Mathlib's step-bounded evaluator `Nat.Partrec.Code.evaln`. `firstHalt`
records that budget `k+1` produces an output while budget `k` does not; `firstHalt_unique`
shows at most one budget can be first, by monotonicity of `evaln` in the budget, and
`exists_firstHalt` shows one exists exactly when the unbounded evaluation is defined, by
`evaln_complete`. The series therefore has at most one nonzero term, and each nonzero term is
exactly `1` because the draw probability and the payout are reciprocal.

The reduction is then stated twice. `dom_iff_half_lt_of_approximates` is the mathematical
content with no computability in it: any real number within `1/3` of the expectation is above
`1/2` precisely when the machine halts. `not_computable_rational_approximation` is the
computability conclusion: there is no computable nonnegative-rational approximation, given as
a computable numerator and a computable strictly positive denominator, that is within `1/3`
of the expectation for every machine — such an approximation would decide
`ComputablePred.halting_problem`.

Scope. The approximation in the computability statement is presented as a pair of computable
natural-number functions rather than as a computable function into `ℚ`, because this Mathlib
pin has no primitive-recursive arithmetic on `ℚ` with which to compare a rational to one
half; the two formulations describe the same class of approximations, since every
nonnegative rational is such a quotient. The input is held fixed and the machine varies,
which is the form `ComputablePred.halting_problem` takes. Randomized machines, and the
question of what a physical device could compute, are not treated.

## Empirical status

None. The bodies here are algebra and computability: `payout` is a stipulated function of a
simulated step budget, and no statement below asserts that any measured quantity equals it.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.HaltingExpectationBoundary

open Nat.Partrec

noncomputable section

/-! ### The experiment of NOTE2 §10 -/

/-- The machine first produces an output at step `step + 1`: the budget `step + 1` suffices
and the budget `step` does not. -/
def firstHalt (code : Code) (input step : ℕ) : Bool :=
  (Code.evaln (step + 1) code input).isSome && !(Code.evaln step code input).isSome

/-- The geometric draw of NOTE2 §10: the budget `step + 1` is drawn with probability
`2^{-(step+1)}`. -/
def drawProbability (step : ℕ) : ℝ := (1 / 2) ^ (step + 1)

/-- The payout of NOTE2 §10: `2^{N}` exactly when the machine first halts at the drawn step
`N`, and zero otherwise. -/
def payout (code : Code) (input step : ℕ) : ℝ :=
  if firstHalt code input step then 2 ^ (step + 1) else 0

/-- The expected payout of the experiment of NOTE2 §10. -/
def expectedPayout (code : Code) (input : ℕ) : ℝ :=
  ∑' step, drawProbability step * payout code input step

/-- The geometric draw is a probability law: the budgets `1, 2, …` carry total mass one. -/
theorem drawProbability_tsum : ∑' step, drawProbability step = 1 := by
  have hterm : ∀ step : ℕ, drawProbability step = (1 / 2 : ℝ) * (1 / 2 : ℝ) ^ step := by
    intro step
    unfold drawProbability
    rw [pow_succ]
    ring
  rw [tsum_congr hterm, tsum_mul_left,
    tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
  norm_num

/-! ### At most one, and at least one, first halting step -/

/-- Unfolding the first-halt test. -/
theorem firstHalt_iff (code : Code) (input step : ℕ) :
    firstHalt code input step = true ↔
      (Code.evaln (step + 1) code input).isSome = true ∧
        (Code.evaln step code input).isSome = false := by
  constructor
  · intro h
    rw [firstHalt, Bool.and_eq_true] at h
    exact ⟨h.1, by simpa using h.2⟩
  · rintro ⟨h1, h2⟩
    rw [firstHalt, Bool.and_eq_true]
    exact ⟨h1, by simp [h2]⟩

/-- A larger step budget cannot lose an output that a smaller budget already produced. -/
theorem isSome_evaln_mono (code : Code) (input step step' : ℕ) (hle : step ≤ step')
    (h : (Code.evaln step code input).isSome = true) :
    (Code.evaln step' code input).isSome = true := by
  obtain ⟨value, hvalue⟩ := Option.isSome_iff_exists.mp h
  have hmem : value ∈ Code.evaln step code input := hvalue
  rw [Option.isSome_iff_exists]
  exact ⟨value, Code.evaln_mono hle hmem⟩

/-- **At most one first halting step.** Monotonicity of the step-bounded evaluator makes the
payout of NOTE2 §10 a single-term series. -/
theorem firstHalt_unique (code : Code) (input step step' : ℕ)
    (h : firstHalt code input step = true) (h' : firstHalt code input step' = true) :
    step = step' := by
  rw [firstHalt_iff] at h h'
  rcases lt_trichotomy step step' with hlt | heq | hgt
  · exfalso
    have hmono := isSome_evaln_mono code input (step + 1) step' hlt h.1
    rw [h'.2] at hmono
    exact Bool.false_ne_true hmono
  · exact heq
  · exfalso
    have hmono := isSome_evaln_mono code input (step' + 1) step hgt h'.1
    rw [h.2] at hmono
    exact Bool.false_ne_true hmono

/-- **A first halting step exists exactly when the computation is defined.** -/
theorem exists_firstHalt (code : Code) (input : ℕ) (hdom : (Code.eval code input).Dom) :
    ∃ step, firstHalt code input step = true := by
  classical
  have hmem : (Code.eval code input).get hdom ∈ Code.eval code input := Part.get_mem hdom
  obtain ⟨budget, hbudget⟩ := Code.evaln_complete.mp hmem
  have hex : ∃ b, (Code.evaln b code input).isSome = true :=
    ⟨budget, Option.isSome_iff_exists.mpr ⟨_, hbudget⟩⟩
  have hspec := Nat.find_spec hex
  have hne : Nat.find hex ≠ 0 := by
    intro hzero
    rw [hzero] at hspec
    obtain ⟨value, hvalue⟩ := Option.isSome_iff_exists.mp hspec
    have hmem0 : value ∈ Code.evaln 0 code input := hvalue
    exact absurd (Code.evaln_bound hmem0) (Nat.not_lt_zero input)
  obtain ⟨earlier, hearlier⟩ := Nat.exists_eq_succ_of_ne_zero hne
  refine ⟨earlier, (firstHalt_iff code input earlier).mpr ⟨?_, ?_⟩⟩
  · have hsucc : Nat.find hex = earlier + 1 := hearlier
    rw [← hsucc]
    exact hspec
  · have hlt : earlier < Nat.find hex := by
      rw [hearlier]
      exact Nat.lt_succ_self earlier
    simpa using Nat.find_min hex hlt

/-- A first halting step witnesses that the unbounded computation is defined. -/
theorem dom_of_firstHalt (code : Code) (input step : ℕ)
    (h : firstHalt code input step = true) : (Code.eval code input).Dom := by
  obtain ⟨value, hvalue⟩ :=
    Option.isSome_iff_exists.mp ((firstHalt_iff code input step).mp h).1
  have hmem : value ∈ Code.evaln (step + 1) code input := hvalue
  exact Part.dom_iff_mem.mpr ⟨value, Code.evaln_sound hmem⟩

/-! ### The expectation is exactly the halting verdict -/

/-- The draw probability and the payout are reciprocal, so every term of the series is one or
zero. -/
theorem drawProbability_mul_payout (code : Code) (input step : ℕ) :
    drawProbability step * payout code input step =
      if firstHalt code input step then (1 : ℝ) else 0 := by
  unfold drawProbability payout
  split_ifs with h
  · rw [← mul_pow]
    norm_num
  · ring

/-- **NOTE2 §10.** When the machine halts on the given input, the expected payout is one. -/
theorem expectedPayout_eq_one_of_dom (code : Code) (input : ℕ)
    (hdom : (Code.eval code input).Dom) : expectedPayout code input = 1 := by
  obtain ⟨first, hfirst⟩ := exists_firstHalt code input hdom
  unfold expectedPayout
  rw [tsum_congr (drawProbability_mul_payout code input)]
  have hfun : (fun step ↦ if firstHalt code input step then (1 : ℝ) else 0) =
      fun step ↦ if step = first then (1 : ℝ) else 0 := by
    funext step
    by_cases hstep : firstHalt code input step = true
    · rw [if_pos hstep, if_pos (firstHalt_unique code input step first hstep hfirst)]
    · have hne : step ≠ first := by
        intro heq
        exact hstep (heq ▸ hfirst)
      rw [if_neg hstep, if_neg hne]
  rw [hfun, tsum_ite_eq]

/-- **NOTE2 §10.** When the machine does not halt on the given input, the expected payout is
zero, even though every individual run terminates. -/
theorem expectedPayout_eq_zero_of_not_dom (code : Code) (input : ℕ)
    (hdom : ¬(Code.eval code input).Dom) : expectedPayout code input = 0 := by
  unfold expectedPayout
  rw [tsum_congr (drawProbability_mul_payout code input)]
  have hfun : (fun step ↦ if firstHalt code input step then (1 : ℝ) else 0) =
      fun _ ↦ (0 : ℝ) := by
    funext step
    exact if_neg fun h ↦ hdom (dom_of_firstHalt code input step h)
  rw [hfun, tsum_zero]

/-- **NOTE2 §10, the expectation identity.** The expected payout is one exactly when the
machine halts. -/
theorem expectedPayout_eq_one_iff (code : Code) (input : ℕ) :
    expectedPayout code input = 1 ↔ (Code.eval code input).Dom := by
  constructor
  · intro h
    by_contra hdom
    rw [expectedPayout_eq_zero_of_not_dom code input hdom] at h
    norm_num at h
  · exact expectedPayout_eq_one_of_dom code input

/-- The expected payout is the expectation of the halting indicator under the corpus point
mass at the verdict, which is the sense in which this experiment reports the verdict
exactly. The verdict is supplied by the caller as the data it is. -/
theorem expectedPayout_eq_pointMass_expectation (code : Code) (input : ℕ) (verdict : Bool)
    (hverdict : verdict = true ↔ (Code.eval code input).Dom) :
    expectedPayout code input =
      (FiniteReportLaw.pointMass verdict).expectation fun outcome ↦
        if outcome then (1 : ℝ) else 0 := by
  cases verdict with
  | false =>
    have hdom : ¬(Code.eval code input).Dom := by
      intro hcontra
      simpa using hverdict.mpr hcontra
    rw [expectedPayout_eq_zero_of_not_dom code input hdom]
    norm_num [FiniteReportLaw.expectation, FiniteReportLaw.pointMass, Fintype.sum_bool]
  | true =>
    rw [expectedPayout_eq_one_of_dom code input (hverdict.mp rfl)]
    norm_num [FiniteReportLaw.expectation, FiniteReportLaw.pointMass, Fintype.sum_bool]

/-! ### The reduction to the halting problem -/

/-- **NOTE2 §10, the reduction, with no computability in it.** Any real number within `1/3`
of the expected payout exceeds one half exactly when the machine halts. -/
theorem dom_iff_half_lt_of_approximates (code : Code) (input : ℕ) (approximation : ℝ)
    (h : |approximation - expectedPayout code input| < 1 / 3) :
    1 / 2 < approximation ↔ (Code.eval code input).Dom := by
  rw [abs_lt] at h
  by_cases hdom : (Code.eval code input).Dom
  · rw [expectedPayout_eq_one_of_dom code input hdom] at h
    exact ⟨fun _ ↦ hdom, fun _ ↦ by linarith [h.1]⟩
  · rw [expectedPayout_eq_zero_of_not_dom code input hdom] at h
    constructor
    · intro hlt
      exact absurd hdom (by linarith [h.2] : False).elim
    · intro hcontra
      exact absurd hcontra hdom

/-- **NOTE2 §10, the computability conclusion.** No computable nonnegative-rational
approximation, presented as a computable numerator and a computable strictly positive
denominator, is within `1/3` of the expected payout for every machine: such an approximation
would decide the halting problem. -/
theorem not_computable_rational_approximation (input : ℕ) :
    ¬∃ numerator denominator : Code → ℕ,
        Computable numerator ∧ Computable denominator ∧ (∀ code, 0 < denominator code) ∧
          ∀ code, |(numerator code : ℝ) / (denominator code : ℝ) -
            expectedPayout code input| < 1 / 3 := by
  rintro ⟨numerator, denominator, hnum, hden, hpos, happrox⟩
  have hmul : Computable fun code ↦ 2 * numerator code :=
    (Primrec₂.to_comp Primrec.nat_mul).comp (Computable.const 2) hnum
  have hltcomp : Computable fun pair : ℕ × ℕ ↦ decide (pair.1 < pair.2) := by
    obtain ⟨_, hltprim⟩ := (Primrec.nat_lt : PrimrecRel ((· < ·) : ℕ → ℕ → Prop))
    exact hltprim.to_comp.of_eq fun _ ↦ decide_eq_decide.mpr Iff.rfl
  have hcomp : Computable fun code ↦ decide (denominator code < 2 * numerator code) :=
    hltcomp.comp (hden.pair hmul)
  have hiff : ∀ code : Code,
      denominator code < 2 * numerator code ↔ (Code.eval code input).Dom := by
    intro code
    have hb : (0 : ℝ) < (denominator code : ℝ) := by exact_mod_cast hpos code
    rw [← dom_iff_half_lt_of_approximates code input _ (happrox code), lt_div_iff₀ hb]
    constructor
    · intro hlt
      have hcast : (denominator code : ℝ) < 2 * (numerator code : ℝ) := by
        exact_mod_cast hlt
      linarith
    · intro hlt
      have hcast : (denominator code : ℝ) < 2 * (numerator code : ℝ) := by linarith
      exact_mod_cast hcast
  exact ComputablePred.halting_problem input
    (ComputablePred.of_eq (Computable.computablePred hcomp) hiff)

end

end Descent.Portability.HaltingExpectationBoundary
