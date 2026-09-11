/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.SublawReportCertificate
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecificLimits.Basic

assert_below Descent.Decision Descent.Program

/-!
# Certified interval evaluators and the halting sublaw

NOTE2 Theorem 5 states two things about continuous primitives. A nested family of lower and
upper cylinder evaluations that brackets a bounded integrand and whose widths vanish gives
nested valid bounds on its exact expectation, and those bounds converge to it. And a
countable report of an almost surely terminating random-bit program is the law
`P = sum over minimal halting prefixes of two to the minus length times the point mass of the
report`, of which a finite prefix enumeration is a positive sublaw whose missing mass is
known exactly. This module proves both.

The evaluator is a structure carrying the two evaluation sequences, their measurability, the
bracketing inequalities, a common bound, and the vanishing of the widths. It is inhabited by
an explicit nondegenerate evaluator whose brackets are strictly wider than the integrand at
every stage, so the hypothesis class is not vacuous. The two integral bounds are integral
monotonicity, and the two convergences are dominated convergence with the constant bound as
dominating function, which is integrable because the measure is finite.

The partial-metric form is interval arithmetic on a ratio: when the definedness mass and the
weighted numerator are separately bracketed and the definedness lower bound is positive, the
reported conditional mean of NOTE2 (2) lies between the two extreme ratios. That bracket
complements the completion-based certificate of `SublawReportCertificate.ratio_bounds`, which
brackets the same quantity from a single missing-mass budget instead.

Kraft's inequality is proved in full for a finite prefix-free set of bit strings, by
induction on a bound for the word lengths: either the empty word is present, in which case
prefix-freeness forces the set to be exactly the empty word, or every word starts with a bit
and the two branches are prefix-free sets one level shallower whose dyadic weights are each
at most one half. The halting sublaw of NOTE2 (32) is then a `ReportSublaw` of the corpus,
and the mass its finite enumeration misses is exactly one minus the enumerated weight.

Not formalized here: the cylinder structure itself, which enters only through the
measurability and bracketing hypotheses; the a.s. termination of the underlying program,
which enters only through the choice of the prefix set; and the infinite halting law of (32),
since the corpus report space is finite and only its finite enumerations are represented.

## Empirical status

None. The bodies here are algebra and measure theory: the evaluator and the prefix set are
supplied inputs, and every conclusion is a consequence of monotone integration, dominated
convergence and a counting argument, so no measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.IntervalEvaluatorCertificate

open MeasureTheory Filter

open scoped BigOperators

variable {Ω : Type*} [MeasurableSpace Ω]
variable {integrand : Ω → ℝ} {bound : ℝ}

/-- NOTE2 Theorem 5: a nested interval evaluator for a bounded measurable integrand. At
every stage the lower and upper evaluations bracket the integrand everywhere, both stay
inside a common bound, and their widths vanish pointwise. Assumes: the integrand is
measurable and each stage's evaluations are exact. -/
structure IntervalEvaluator (integrand : Ω → ℝ) (bound : ℝ) where
  lower : ℕ → Ω → ℝ
  upper : ℕ → Ω → ℝ
  integrand_measurable : Measurable integrand
  lower_measurable : ∀ stage, Measurable (lower stage)
  upper_measurable : ∀ stage, Measurable (upper stage)
  lower_le : ∀ stage state, lower stage state ≤ integrand state
  le_upper : ∀ stage state, integrand state ≤ upper stage state
  lower_abs_le : ∀ stage state, |lower stage state| ≤ bound
  upper_abs_le : ∀ stage state, |upper stage state| ≤ bound
  width_tendsto : ∀ state,
    Tendsto (fun stage ↦ upper stage state - lower stage state) atTop (nhds 0)

/-- The stage-indexed slack of the inhabiting evaluator. -/
def slack (stage : ℕ) : ℝ := 1 / ((stage : ℝ) + 1)

theorem slack_pos (stage : ℕ) : 0 < slack stage := by
  rw [slack]
  positivity

theorem slack_le_one (stage : ℕ) : slack stage ≤ 1 := by
  rw [slack, div_le_one (by positivity)]
  have hcast : (0:ℝ) ≤ (stage : ℝ) := Nat.cast_nonneg stage
  linarith

theorem tendsto_slack : Tendsto (fun stage : ℕ ↦ 2 * slack stage) atTop (nhds 0) := by
  simpa [slack] using tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (2:ℝ)

/-- Every bounded measurable integrand carries an evaluator whose brackets are strictly
wider than it at every stage and close only in the limit, so the hypothesis class is
inhabited by a nondegenerate evaluator rather than merely assumed nonempty. -/
def slackEvaluator (integrand : Ω → ℝ) (bound : ℝ) (hmeasurable : Measurable integrand)
    (hbound : ∀ state, |integrand state| ≤ bound) :
    IntervalEvaluator integrand (bound + 1) where
  lower := fun stage state ↦ integrand state - slack stage
  upper := fun stage state ↦ integrand state + slack stage
  integrand_measurable := hmeasurable
  lower_measurable := fun _ ↦ hmeasurable.sub measurable_const
  upper_measurable := fun _ ↦ hmeasurable.add measurable_const
  lower_le := fun stage state ↦ by
    show integrand state - slack stage ≤ integrand state
    have hpos := slack_pos stage
    linarith
  le_upper := fun stage state ↦ by
    show integrand state ≤ integrand state + slack stage
    have hpos := slack_pos stage
    linarith
  lower_abs_le := fun stage state ↦ by
    show |integrand state - slack stage| ≤ bound + 1
    have hpos := slack_pos stage
    have hle := slack_le_one stage
    have habs := hbound state
    rw [abs_le] at habs ⊢
    constructor <;> linarith
  upper_abs_le := fun stage state ↦ by
    show |integrand state + slack stage| ≤ bound + 1
    have hpos := slack_pos stage
    have hle := slack_le_one stage
    have habs := hbound state
    rw [abs_le] at habs ⊢
    constructor <;> linarith
  width_tendsto := fun state ↦ by
    refine tendsto_slack.congr fun stage ↦ ?_
    show 2 * slack stage = integrand state + slack stage - (integrand state - slack stage)
    ring

/-- A measurable function bounded in absolute value is integrable against a finite
measure. -/
theorem integrable_of_abs_le_const (μ : Measure Ω) [IsFiniteMeasure μ] {value : Ω → ℝ}
    (hmeasurable : Measurable value) (cap : ℝ) (hcap : ∀ state, |value state| ≤ cap) :
    Integrable value μ := by
  refine Integrable.mono (integrable_const cap) hmeasurable.aestronglyMeasurable ?_
  filter_upwards with state
  rw [Real.norm_eq_abs, Real.norm_eq_abs]
  exact le_trans (hcap state) (le_abs_self cap)

namespace IntervalEvaluator

theorem integrable_lower (evaluator : IntervalEvaluator integrand bound) (μ : Measure Ω)
    [IsFiniteMeasure μ] (stage : ℕ) : Integrable (evaluator.lower stage) μ :=
  integrable_of_abs_le_const μ (evaluator.lower_measurable stage) bound
    (evaluator.lower_abs_le stage)

theorem integrable_upper (evaluator : IntervalEvaluator integrand bound) (μ : Measure Ω)
    [IsFiniteMeasure μ] (stage : ℕ) : Integrable (evaluator.upper stage) μ :=
  integrable_of_abs_le_const μ (evaluator.upper_measurable stage) bound
    (evaluator.upper_abs_le stage)

/-- The bracketed integrand inherits the bound, hence integrability. -/
theorem integrable_integrand (evaluator : IntervalEvaluator integrand bound)
    (μ : Measure Ω) [IsFiniteMeasure μ] : Integrable integrand μ := by
  refine integrable_of_abs_le_const μ evaluator.integrand_measurable bound fun state ↦ ?_
  have hlow := evaluator.lower_le 0 state
  have hhigh := evaluator.le_upper 0 state
  have hlowbound := evaluator.lower_abs_le 0 state
  have hhighbound := evaluator.upper_abs_le 0 state
  rw [abs_le] at hlowbound hhighbound ⊢
  constructor <;> linarith

/-- NOTE2 Theorem 5: every stage's lower evaluation is a valid lower bound on the exact
expectation. -/
theorem integral_lower_le (evaluator : IntervalEvaluator integrand bound) (μ : Measure Ω)
    [IsFiniteMeasure μ] (stage : ℕ) :
    ∫ state, evaluator.lower stage state ∂μ ≤ ∫ state, integrand state ∂μ :=
  integral_mono (evaluator.integrable_lower μ stage) (evaluator.integrable_integrand μ)
    (evaluator.lower_le stage)

/-- NOTE2 Theorem 5: every stage's upper evaluation is a valid upper bound on the exact
expectation. -/
theorem integral_le_upper (evaluator : IntervalEvaluator integrand bound) (μ : Measure Ω)
    [IsFiniteMeasure μ] (stage : ℕ) :
    ∫ state, integrand state ∂μ ≤ ∫ state, evaluator.upper stage state ∂μ :=
  integral_mono (evaluator.integrable_integrand μ) (evaluator.integrable_upper μ stage)
    (evaluator.le_upper stage)

/-- Vanishing widths squeeze the lower evaluations onto the integrand pointwise. -/
theorem tendsto_lower (evaluator : IntervalEvaluator integrand bound) (state : Ω) :
    Tendsto (fun stage ↦ evaluator.lower stage state) atTop (nhds (integrand state)) := by
  have hzero : Tendsto (fun stage ↦ integrand state - evaluator.lower stage state) atTop
      (nhds 0) :=
    squeeze_zero (fun stage ↦ by linarith [evaluator.lower_le stage state])
      (fun stage ↦ by linarith [evaluator.le_upper stage state])
      (evaluator.width_tendsto state)
  have hneg := hzero.neg
  rw [neg_zero] at hneg
  have hfun : (fun stage ↦ -(integrand state - evaluator.lower stage state)) =
      fun stage ↦ evaluator.lower stage state - integrand state := by
    funext stage
    ring
  rw [hfun] at hneg
  exact tendsto_sub_nhds_zero_iff.mp hneg

/-- Vanishing widths squeeze the upper evaluations onto the integrand pointwise. -/
theorem tendsto_upper (evaluator : IntervalEvaluator integrand bound) (state : Ω) :
    Tendsto (fun stage ↦ evaluator.upper stage state) atTop (nhds (integrand state)) := by
  have hzero : Tendsto (fun stage ↦ evaluator.upper stage state - integrand state) atTop
      (nhds 0) :=
    squeeze_zero (fun stage ↦ by linarith [evaluator.le_upper stage state])
      (fun stage ↦ by linarith [evaluator.lower_le stage state])
      (evaluator.width_tendsto state)
  exact tendsto_sub_nhds_zero_iff.mp hzero

/-- NOTE2 Theorem 5: the lower evaluation integrals converge to the exact expectation, by
dominated convergence against the constant bound. -/
theorem tendsto_integral_lower (evaluator : IntervalEvaluator integrand bound)
    (μ : Measure Ω) [IsFiniteMeasure μ] :
    Tendsto (fun stage ↦ ∫ state, evaluator.lower stage state ∂μ) atTop
      (nhds (∫ state, integrand state ∂μ)) := by
  refine tendsto_integral_of_dominated_convergence (fun _ ↦ bound)
    (fun stage ↦ (evaluator.lower_measurable stage).aestronglyMeasurable)
    (integrable_const bound) (fun stage ↦ ?_) ?_
  · filter_upwards with state
    rw [Real.norm_eq_abs]
    exact evaluator.lower_abs_le stage state
  · filter_upwards with state
    exact evaluator.tendsto_lower state

/-- NOTE2 Theorem 5: the upper evaluation integrals converge to the exact expectation. -/
theorem tendsto_integral_upper (evaluator : IntervalEvaluator integrand bound)
    (μ : Measure Ω) [IsFiniteMeasure μ] :
    Tendsto (fun stage ↦ ∫ state, evaluator.upper stage state ∂μ) atTop
      (nhds (∫ state, integrand state ∂μ)) := by
  refine tendsto_integral_of_dominated_convergence (fun _ ↦ bound)
    (fun stage ↦ (evaluator.upper_measurable stage).aestronglyMeasurable)
    (integrable_const bound) (fun stage ↦ ?_) ?_
  · filter_upwards with state
    rw [Real.norm_eq_abs]
    exact evaluator.upper_abs_le stage state
  · filter_upwards with state
    exact evaluator.tendsto_upper state

end IntervalEvaluator

/-- Interval arithmetic on a ratio: a quotient whose numerator and denominator are each
bracketed lies between the two extreme quotients, provided the denominator's lower bound is
positive and the numerator's lower bound is nonnegative. -/
theorem bracketed_ratio_bounds (numerator denominator numeratorLower numeratorUpper
    denominatorLower denominatorUpper : ℝ)
    (hnumeratorLower : numeratorLower ≤ numerator)
    (hnumeratorUpper : numerator ≤ numeratorUpper)
    (hdenominatorLower : denominatorLower ≤ denominator)
    (hdenominatorUpper : denominator ≤ denominatorUpper)
    (hnumeratorNonneg : 0 ≤ numeratorLower) (hdenominatorPos : 0 < denominatorLower) :
    numeratorLower / denominatorUpper ≤ numerator / denominator ∧
      numerator / denominator ≤ numeratorUpper / denominatorLower := by
  have hden : 0 < denominator := lt_of_lt_of_le hdenominatorPos hdenominatorLower
  have hdenUp : 0 < denominatorUpper := lt_of_lt_of_le hden hdenominatorUpper
  have hnum : 0 ≤ numerator := le_trans hnumeratorNonneg hnumeratorLower
  have hnumUp : 0 ≤ numeratorUpper := le_trans hnum hnumeratorUpper
  constructor
  · rw [div_le_div_iff₀ hdenUp hden]
    linarith [mul_le_mul_of_nonneg_right hnumeratorLower hden.le,
      mul_le_mul_of_nonneg_left hdenominatorUpper hnum]
  · rw [div_le_div_iff₀ hden hdenominatorPos]
    linarith [mul_le_mul_of_nonneg_right hnumeratorUpper hdenominatorPos.le,
      mul_le_mul_of_nonneg_left hdenominatorLower hnumUp]

/-- NOTE2 Theorem 5 for a partial metric: evaluating the definedness indicator and the
indicator-weighted metric with separate interval evaluators brackets the reported
conditional mean of NOTE2 (2) at every stage, with no information about the unresolved part
beyond the two evaluations. -/
theorem conditionalMean_bracket (μ : Measure Ω) [IsFiniteMeasure μ]
    (metric indicator : Ω → ℝ) (numeratorBound definednessBound : ℝ)
    (weighted : IntervalEvaluator (fun state ↦ indicator state * metric state) numeratorBound)
    (definedness : IntervalEvaluator indicator definednessBound) (stage : ℕ)
    (hnumeratorNonneg : 0 ≤ ∫ state, weighted.lower stage state ∂μ)
    (hdefinednessPos : 0 < ∫ state, definedness.lower stage state ∂μ) :
    (∫ state, weighted.lower stage state ∂μ) /
          (∫ state, definedness.upper stage state ∂μ) ≤
        (∫ state, indicator state * metric state ∂μ) /
          (∫ state, indicator state ∂μ) ∧
      (∫ state, indicator state * metric state ∂μ) /
          (∫ state, indicator state ∂μ) ≤
        (∫ state, weighted.upper stage state ∂μ) /
          (∫ state, definedness.lower stage state ∂μ) :=
  bracketed_ratio_bounds _ _ _ _ _ _
    (weighted.integral_lower_le μ stage) (weighted.integral_le_upper μ stage)
    (definedness.integral_lower_le μ stage) (definedness.integral_le_upper μ stage)
    hnumeratorNonneg hdefinednessPos

/-- A finite set of bit strings is prefix-free when no member is a prefix of another. These
are the minimal halting prefixes of an almost surely terminating random-bit program. -/
def PrefixFree (words : Finset (List Bool)) : Prop :=
  ∀ first ∈ words, ∀ second ∈ words, first <+: second → first = second

/-- The singleton containing only the empty word is prefix-free, which inhabits the
hypothesis class with an actual halting set. -/
theorem prefixFree_singleton_nil : PrefixFree {([] : List Bool)} := by
  intro first hfirst second hsecond _
  rw [Finset.mem_singleton] at hfirst hsecond
  rw [hfirst, hsecond]

/-- A word set that reduces to the empty word carries dyadic weight at most one. -/
theorem dyadic_sum_le_one_of_subset_nil (words : Finset (List Bool))
    (hsubset : words ⊆ {([] : List Bool)}) :
    ∑ word ∈ words, (1 / 2 : ℝ) ^ word.length ≤ 1 := by
  have hcongr : ∀ word ∈ words, (1 / 2 : ℝ) ^ word.length = 1 := by
    intro word hword
    rw [Finset.mem_singleton.mp (hsubset hword)]
    simp
  rw [Finset.sum_congr rfl hcongr, Finset.sum_const, nsmul_eq_mul, mul_one]
  have hcard : words.card ≤ 1 := by simpa using Finset.card_le_card hsubset
  exact_mod_cast hcard

/-- Kraft's inequality by induction on a bound for the word lengths. Either the empty word
is present, and prefix-freeness collapses the set onto it, or every word starts with a bit
and the two branch sets are prefix-free one level shallower. -/
theorem dyadic_sum_le_one_of_length_le : ∀ (depth : ℕ) (words : Finset (List Bool)),
    (∀ word ∈ words, word.length ≤ depth) → PrefixFree words →
    ∑ word ∈ words, (1 / 2 : ℝ) ^ word.length ≤ 1 := by
  intro depth
  induction depth with
  | zero =>
    intro words hlength _
    refine dyadic_sum_le_one_of_subset_nil words fun word hword ↦ ?_
    rw [Finset.mem_singleton]
    have hzero : word.length = 0 := Nat.le_zero.mp (hlength word hword)
    simpa using hzero
  | succ depth ih =>
    intro words hlength hfree
    by_cases hnil : ([] : List Bool) ∈ words
    · refine dyadic_sum_le_one_of_subset_nil words fun word hword ↦ ?_
      rw [Finset.mem_singleton]
      exact (hfree [] hnil word hword List.nil_prefix).symm
    · have hbranch : ∀ (flag : Bool) (branch : Finset (List Bool)), branch ⊆ words →
          (∀ word ∈ branch, word.headI = flag) →
          ∑ word ∈ branch, (1 / 2 : ℝ) ^ word.length ≤ 1 / 2 := by
        intro flag branch hsubset hhead
        have hnonnil : ∀ word ∈ branch, word ≠ [] := by
          intro word hword hzero
          exact hnil (hzero ▸ hsubset hword)
        have hcons : ∀ word ∈ branch, flag :: word.tail = word := by
          intro word hword
          obtain ⟨first, rest, hshape⟩ := List.exists_cons_of_ne_nil (hnonnil word hword)
          have hflag : first = flag := by
            have hhd := hhead word hword
            rw [hshape] at hhd
            simpa using hhd
          rw [hshape]
          simp [hflag]
        have hlen : ∀ word ∈ branch, word.length = word.tail.length + 1 := by
          intro word hword
          conv_lhs => rw [← hcons word hword]
          simp
        have hinjective : ∀ first ∈ branch, ∀ second ∈ branch,
            first.tail = second.tail → first = second := by
          intro first hfirst second hsecond hequal
          rw [← hcons first hfirst, ← hcons second hsecond, hequal]
        have hdepth : ∀ tail ∈ branch.image List.tail, tail.length ≤ depth := by
          intro tail htail
          obtain ⟨word, hword, hmap⟩ := Finset.mem_image.mp htail
          have hbound := hlength word (hsubset hword)
          have hsplit := hlen word hword
          rw [← hmap]
          omega
        have hfreetail : PrefixFree (branch.image List.tail) := by
          intro first hfirst second hsecond hprefix
          obtain ⟨x, hx, hxmap⟩ := Finset.mem_image.mp hfirst
          obtain ⟨y, hy, hymap⟩ := Finset.mem_image.mp hsecond
          subst hxmap
          subst hymap
          obtain ⟨suffix, hsuffix⟩ := hprefix
          have hfull : x <+: y := by
            refine ⟨suffix, ?_⟩
            rw [← hcons x hx, ← hcons y hy, List.cons_append, hsuffix]
          exact congrArg List.tail (hfree x (hsubset hx) y (hsubset hy) hfull)
        have hinner := ih (branch.image List.tail) hdepth hfreetail
        have hreindex : ∑ tail ∈ branch.image List.tail, (1 / 2 : ℝ) ^ tail.length =
            ∑ word ∈ branch, (1 / 2 : ℝ) ^ word.tail.length :=
          Finset.sum_image hinjective
        have hterm : ∀ word ∈ branch, (1 / 2 : ℝ) ^ word.length =
            (1 / 2 : ℝ) ^ word.tail.length * (1 / 2) := by
          intro word hword
          rw [hlen word hword, pow_succ]
        calc ∑ word ∈ branch, (1 / 2 : ℝ) ^ word.length
            = ∑ word ∈ branch, (1 / 2 : ℝ) ^ word.tail.length * (1 / 2) :=
              Finset.sum_congr rfl hterm
          _ = (∑ word ∈ branch, (1 / 2 : ℝ) ^ word.tail.length) * (1 / 2) := by
              rw [Finset.sum_mul]
          _ ≤ 1 * (1 / 2) := by
              refine mul_le_mul_of_nonneg_right ?_ (by norm_num)
              rw [← hreindex]
              exact hinner
          _ = 1 / 2 := by ring
      have hother : ∀ word ∈ words.filter (fun word ↦ ¬ (word.headI = false)),
          word.headI = true := by
        intro word hword
        have hne := (Finset.mem_filter.mp hword).2
        cases hflag : word.headI
        · exact absurd hflag hne
        · rfl
      have hfalse := hbranch false (words.filter (fun word ↦ word.headI = false))
        (Finset.filter_subset _ _) fun word hword ↦ (Finset.mem_filter.mp hword).2
      have htrue := hbranch true (words.filter (fun word ↦ ¬ (word.headI = false)))
        (Finset.filter_subset _ _) hother
      have hsplit : ∑ word ∈ words.filter (fun word ↦ word.headI = false),
            (1 / 2 : ℝ) ^ word.length +
          ∑ word ∈ words.filter (fun word ↦ ¬ (word.headI = false)),
            (1 / 2 : ℝ) ^ word.length =
          ∑ word ∈ words, (1 / 2 : ℝ) ^ word.length :=
        Finset.sum_filter_add_sum_filter_not words (fun word ↦ word.headI = false) _
      linarith

/-- Kraft's inequality: the dyadic weights of a finite prefix-free set of bit strings sum to
at most one, so the halting prefixes of NOTE2 (32) carry a genuine positive sublaw. -/
theorem kraft_sum_le_one (words : Finset (List Bool)) (hfree : PrefixFree words) :
    ∑ word ∈ words, (1 / 2 : ℝ) ^ word.length ≤ 1 :=
  dyadic_sum_le_one_of_length_le (words.sup List.length) words
    (fun word hword ↦ Finset.le_sup hword) hfree

/-- NOTE2 (32): the halting law of an almost surely terminating random-bit program,
enumerated to a finite set of minimal halting prefixes. Each report carries the dyadic
weight of the prefixes producing it, and Kraft's inequality makes the total a sublaw. -/
noncomputable def haltingSublaw {Report : Type*} [Fintype Report] [DecidableEq Report]
    (words : Finset (List Bool)) (hfree : PrefixFree words) (report : List Bool → Report) :
    SublawReportCertificate.ReportSublaw Report where
  mass := fun target ↦
    ∑ word ∈ words.filter (fun word ↦ report word = target), (1 / 2 : ℝ) ^ word.length
  mass_nonneg := fun _ ↦ Finset.sum_nonneg fun _ _ ↦ by positivity
  mass_sum_le_one := by
    show ∑ target, ∑ word ∈ words.filter (fun word ↦ report word = target),
      (1 / 2 : ℝ) ^ word.length ≤ 1
    rw [Finset.sum_fiberwise_of_maps_to (fun word _ ↦ Finset.mem_univ (report word))]
    exact kraft_sum_le_one words hfree

/-- NOTE2 (32): the mass a finite prefix enumeration misses is exactly one minus the
enumerated dyadic weight. The error of the sublaw is known, not merely bounded. -/
theorem haltingSublaw_missingMass {Report : Type*} [Fintype Report] [DecidableEq Report]
    (words : Finset (List Bool)) (hfree : PrefixFree words) (report : List Bool → Report) :
    (haltingSublaw words hfree report).missingMass =
      1 - ∑ word ∈ words, (1 / 2 : ℝ) ^ word.length := by
  rw [SublawReportCertificate.ReportSublaw.missingMass]
  congr 1
  exact Finset.sum_fiberwise_of_maps_to (fun word _ ↦ Finset.mem_univ (report word)) _

end Descent.Portability.IntervalEvaluatorCertificate
