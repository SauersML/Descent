/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.CylinderIntervalCertificate

assert_below Descent.Decision Descent.Program

/-!
# Threshold metrics on cylinders, unresolved boundary mass, and coordinate rounding

NOTE2 §7.2 adds two cautions to Theorem 5. A threshold or optimizer comparison needs either a
proof that its boundary is resolved or an explicit bound on the unresolved boundary mass, and
atoms at a tie are not automatically negligible. And for genuinely continuous reports a finite
atomic discretization generally does not converge in total variation: a finite discrete
approximation and a non-atomic law can be at total variation one at every resolution. This
module proves both on the fair-bit stream space of `CylinderIntervalCertificate`.

For a score carrying a `CylinderEvaluator` and a rational threshold, `resolvedMass` is the
total mass of the cylinders whose lower value already reaches the threshold, and
`unresolvedMass` the total mass of those whose lower value is below it and whose upper value
reaches it. `resolvedMass_le_and_le_add` is the certificate: at every stage the probability
that the score reaches the threshold lies between the resolved mass and the resolved mass plus
the unresolved mass. `resolvedMass_le_succ` and `resolvedMass_add_unresolvedMass_succ_le` are
the nesting. `tendsto_unresolvedMass` shows that the unresolved mass vanishes when the boundary
event `score = threshold` is null, and `tendsto_resolvedMass` that the certificate then
converges. `tieEvaluator` is the tie atom: a score sitting at the threshold, evaluated with
brackets that shrink onto it on every stream, keeps every cylinder unresolved at every stage,
so the certificate stays at `[0, 1]` while the probability is one
(`resolvedMass_tieEvaluator`, `unresolvedMass_tieEvaluator`). The null-boundary hypothesis
cannot be dropped.

For the second caution, `bitMeasure_singleton` shows that the fair-bit law has no atoms, and
`discretization_event_gap` that any law concentrated on countably many streams puts mass one
on an event of fair-bit mass zero. `roundToResolution` is coordinate rounding: it keeps the
first bits of a stream and sets the rest to `false`. `roundedLaw_cylinder` shows that the
rounded law reproduces the mass of every cylinder of depth at most the resolution, and
`roundedLaw_range_gap` that it is nevertheless at event distance one from the stream law, at
every resolution.

An optimizer comparison between two scores is the threshold certificate of their difference at
zero. `differenceEvaluator` evaluates the difference on the finer of the two cylinder
partitions, `comparison_certificate` brackets the probability that the first score is at least
the second, and `tendsto_comparison_resolvedMass` shows that the bracket converges when ties are
null.

Not formalized here: total variation as a supremum over events; the gap is exhibited on one
event, which bounds that supremum below by one.

## Empirical status

None. The bodies here are measure theory and algebra: the evaluator and the threshold are
supplied inputs, and every conclusion follows from monotonicity and additivity of the fair-bit
product measure and dominated convergence, so no measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.CylinderThresholdCertificate

open MeasureTheory Filter CylinderIntervalCertificate

open scoped ENNReal Topology

noncomputable section

/-! ### Events of finitely many bits -/

/-- The streams whose first `length` bits satisfy a decidable property form a measurable
event. -/
theorem measurableSet_prefix (length : ℕ) (property : List Bool → Prop)
    [DecidablePred property] :
    MeasurableSet {stream : ℕ → Bool | property (prefixOf stream length)} := by
  have hmeasurable := measurable_prefix length fun word ↦ if property word then (1 : ℝ) else 0
  have hset : {stream : ℕ → Bool | property (prefixOf stream length)} =
      (fun stream : ℕ → Bool ↦ if property (prefixOf stream length) then (1 : ℝ) else 0) ⁻¹'
        {1} := by
    ext stream
    by_cases hproperty : property (prefixOf stream length) <;> simp [hproperty]
  rw [hset]
  exact hmeasurable (measurableSet_singleton 1)

/-- The fair-bit probability of an event of the first `length` bits is the total mass of the
cylinders of that depth whose word satisfies it. -/
theorem bitMeasure_real_prefix (length : ℕ) (property : List Bool → Prop)
    [DecidablePred property] :
    bitMeasure.real {stream : ℕ → Bool | property (prefixOf stream length)} =
      ∑ word ∈ wordsOfLength length, (1 / 2 : ℝ) ^ length * (if property word then 1 else 0) := by
  rw [← integral_prefix length fun word ↦ if property word then (1 : ℝ) else 0,
    ← integral_indicator_one (measurableSet_prefix length property)]
  refine integral_congr_ae (ae_of_all _ fun stream ↦ ?_)
  by_cases hproperty : property (prefixOf stream length) <;>
    simp [hproperty]

/-! ### The threshold certificate -/

variable {score : (ℕ → Bool) → ℝ}

/-- The rational lower value of the cylinder of a stream at a stage. -/
def lowerValue (evaluator : CylinderEvaluator score) (stage : ℕ) (stream : ℕ → Bool) : ℚ :=
  evaluator.lower stage (prefixOf stream (evaluator.depth stage))

/-- The rational upper value of the cylinder of a stream at a stage. -/
def upperValue (evaluator : CylinderEvaluator score) (stage : ℕ) (stream : ℕ → Bool) : ℚ :=
  evaluator.upper stage (prefixOf stream (evaluator.depth stage))

/-- The rational lower value of a cylinder is the real lower evaluation of the stream. -/
theorem cast_lowerValue (evaluator : CylinderEvaluator score) (stage : ℕ)
    (stream : ℕ → Bool) :
    (lowerValue evaluator stage stream : ℝ) = evaluator.lowerEvaluation stage stream :=
  rfl

/-- The rational upper value of a cylinder is the real upper evaluation of the stream. -/
theorem cast_upperValue (evaluator : CylinderEvaluator score) (stage : ℕ)
    (stream : ℕ → Bool) :
    (upperValue evaluator stage stream : ℝ) = evaluator.upperEvaluation stage stream :=
  rfl

/-- NOTE2 §7.2: the resolved threshold mass at a stage, the total mass of the cylinders whose
lower value already reaches the threshold, on which the score reaches it on every
continuation. -/
def resolvedMass (evaluator : CylinderEvaluator score) (threshold : ℚ) (stage : ℕ) : ℚ :=
  ∑ word ∈ wordsOfLength (evaluator.depth stage),
    (1 / 2 : ℚ) ^ evaluator.depth stage *
      (if threshold ≤ evaluator.lower stage word then 1 else 0)

/-- NOTE2 §7.2: the unresolved boundary mass at a stage, the total mass of the cylinders whose
lower value is below the threshold and whose upper value reaches it. -/
def unresolvedMass (evaluator : CylinderEvaluator score) (threshold : ℚ) (stage : ℕ) : ℚ :=
  ∑ word ∈ wordsOfLength (evaluator.depth stage),
    (1 / 2 : ℚ) ^ evaluator.depth stage *
      (if evaluator.lower stage word < threshold ∧ threshold ≤ evaluator.upper stage word then 1
        else 0)

/-- The resolved mass is the fair-bit probability that the cylinder of the stream has lower
value at or above the threshold. -/
theorem resolvedMass_cast (evaluator : CylinderEvaluator score) (threshold : ℚ) (stage : ℕ) :
    (resolvedMass evaluator threshold stage : ℝ) =
      bitMeasure.real {stream | threshold ≤ lowerValue evaluator stage stream} := by
  have hmass := bitMeasure_real_prefix (evaluator.depth stage)
    fun word ↦ threshold ≤ evaluator.lower stage word
  rw [resolvedMass]
  push_cast [apply_ite (Rat.cast : ℚ → ℝ)]
  exact hmass.symm

/-- The unresolved mass is the fair-bit probability that the cylinder of the stream straddles
the threshold. -/
theorem unresolvedMass_cast (evaluator : CylinderEvaluator score) (threshold : ℚ)
    (stage : ℕ) :
    (unresolvedMass evaluator threshold stage : ℝ) =
      bitMeasure.real {stream | lowerValue evaluator stage stream < threshold ∧
        threshold ≤ upperValue evaluator stage stream} := by
  have hmass := bitMeasure_real_prefix (evaluator.depth stage)
    fun word ↦ evaluator.lower stage word < threshold ∧ threshold ≤ evaluator.upper stage word
  rw [unresolvedMass]
  push_cast [apply_ite (Rat.cast : ℚ → ℝ)]
  exact hmass.symm

/-- NOTE2 §7.2, validity of the threshold certificate: at every stage the probability that the
score reaches the threshold lies between the resolved mass and the resolved mass plus the
unresolved boundary mass. -/
theorem resolvedMass_le_and_le_add (evaluator : CylinderEvaluator score) (threshold : ℚ)
    (stage : ℕ) :
    (resolvedMass evaluator threshold stage : ℝ) ≤
        bitMeasure.real {stream | (threshold : ℝ) ≤ score stream} ∧
      bitMeasure.real {stream | (threshold : ℝ) ≤ score stream} ≤
        (resolvedMass evaluator threshold stage : ℝ) +
          unresolvedMass evaluator threshold stage := by
  rw [resolvedMass_cast, unresolvedMass_cast]
  constructor
  · refine measureReal_mono (fun stream hstream ↦ ?_) (measure_ne_top _ _)
    have hcast : (threshold : ℝ) ≤ lowerValue evaluator stage stream := by exact_mod_cast hstream
    exact le_trans hcast (evaluator.lowerEvaluation_le stage stream)
  · refine le_trans (measureReal_mono (fun stream hstream ↦ ?_) (measure_ne_top _ _))
      (measureReal_union_le _ _)
    have hscore : (threshold : ℝ) ≤ score stream := hstream
    by_cases hresolved : threshold ≤ lowerValue evaluator stage stream
    · exact Set.mem_union_left _ hresolved
    · have hcast : (threshold : ℝ) ≤ upperValue evaluator stage stream :=
        le_trans hscore (evaluator.le_upperEvaluation stage stream)
      exact Set.mem_union_right _ ⟨not_le.mp hresolved, by exact_mod_cast hcast⟩

/-- The resolved mass plus the unresolved mass is the fair-bit probability that the cylinder of
the stream has upper value at or above the threshold. -/
theorem resolvedMass_add_unresolvedMass_cast (evaluator : CylinderEvaluator score)
    (threshold : ℚ) (stage : ℕ) :
    (resolvedMass evaluator threshold stage : ℝ) + unresolvedMass evaluator threshold stage =
      bitMeasure.real {stream | threshold ≤ upperValue evaluator stage stream} := by
  have hdisjoint : Disjoint {stream | threshold ≤ lowerValue evaluator stage stream}
      {stream | lowerValue evaluator stage stream < threshold ∧
        threshold ≤ upperValue evaluator stage stream} :=
    Set.disjoint_left.mpr fun _ hresolved hunresolved ↦
      absurd hresolved (not_le.mpr hunresolved.1)
  have hmeasurable : MeasurableSet {stream | lowerValue evaluator stage stream < threshold ∧
      threshold ≤ upperValue evaluator stage stream} :=
    measurableSet_prefix (evaluator.depth stage)
      fun word ↦ evaluator.lower stage word < threshold ∧ threshold ≤ evaluator.upper stage word
  have hunion : {stream | threshold ≤ lowerValue evaluator stage stream} ∪
      {stream | lowerValue evaluator stage stream < threshold ∧
        threshold ≤ upperValue evaluator stage stream} =
      {stream | threshold ≤ upperValue evaluator stage stream} := by
    ext stream
    have hbracket : lowerValue evaluator stage stream ≤ upperValue evaluator stage stream := by
      have hreal : (lowerValue evaluator stage stream : ℝ) ≤ upperValue evaluator stage stream :=
        le_trans (evaluator.lowerEvaluation_le stage stream)
          (evaluator.le_upperEvaluation stage stream)
      exact_mod_cast hreal
    simp only [Set.mem_union, Set.mem_setOf_eq]
    constructor
    · rintro (hresolved | ⟨_, hupper⟩)
      · exact le_trans hresolved hbracket
      · exact hupper
    · intro hupper
      by_cases hresolved : threshold ≤ lowerValue evaluator stage stream
      · exact Or.inl hresolved
      · exact Or.inr ⟨not_le.mp hresolved, hupper⟩
  rw [resolvedMass_cast, unresolvedMass_cast, ← measureReal_union hdisjoint hmeasurable, hunion]

/-- NOTE2 §7.2, nesting from below: the resolved mass increases with the stage, because the
lower values increase along every stream. -/
theorem resolvedMass_le_succ (evaluator : CylinderEvaluator score) (threshold : ℚ)
    (stage : ℕ) :
    resolvedMass evaluator threshold stage ≤ resolvedMass evaluator threshold (stage + 1) := by
  have hreal : (resolvedMass evaluator threshold stage : ℝ) ≤
      resolvedMass evaluator threshold (stage + 1) := by
    rw [resolvedMass_cast, resolvedMass_cast]
    refine measureReal_mono (fun stream hstream ↦ ?_) (measure_ne_top _ _)
    have hstep : (lowerValue evaluator stage stream : ℝ) ≤
        lowerValue evaluator (stage + 1) stream :=
      evaluator.lowerEvaluation_le_succ stage stream
    have hstepRational : lowerValue evaluator stage stream ≤
        lowerValue evaluator (stage + 1) stream := by
      exact_mod_cast hstep
    exact le_trans hstream hstepRational
  exact_mod_cast hreal

/-- NOTE2 §7.2, nesting from above: the resolved mass plus the unresolved mass decreases with
the stage, because the upper values decrease along every stream. -/
theorem resolvedMass_add_unresolvedMass_succ_le (evaluator : CylinderEvaluator score)
    (threshold : ℚ) (stage : ℕ) :
    resolvedMass evaluator threshold (stage + 1) + unresolvedMass evaluator threshold (stage + 1) ≤
      resolvedMass evaluator threshold stage + unresolvedMass evaluator threshold stage := by
  have hreal : (resolvedMass evaluator threshold (stage + 1) : ℝ) +
      unresolvedMass evaluator threshold (stage + 1) ≤
      (resolvedMass evaluator threshold stage : ℝ) + unresolvedMass evaluator threshold stage := by
    rw [resolvedMass_add_unresolvedMass_cast, resolvedMass_add_unresolvedMass_cast]
    refine measureReal_mono (fun stream hstream ↦ ?_) (measure_ne_top _ _)
    have hstep : (upperValue evaluator (stage + 1) stream : ℝ) ≤
        upperValue evaluator stage stream :=
      evaluator.upperEvaluation_succ_le stage stream
    have hstepRational : upperValue evaluator (stage + 1) stream ≤
        upperValue evaluator stage stream := by
      exact_mod_cast hstep
    exact le_trans hstream hstepRational
  exact_mod_cast hreal

/-- The unresolved mass is the stage integral of the indicator that the cylinder of the stream
straddles the threshold. -/
theorem unresolvedMass_integral (evaluator : CylinderEvaluator score) (threshold : ℚ)
    (stage : ℕ) :
    (unresolvedMass evaluator threshold stage : ℝ) =
      ∫ stream, (if lowerValue evaluator stage stream < threshold ∧
        threshold ≤ upperValue evaluator stage stream then (1 : ℝ) else 0) ∂bitMeasure := by
  rw [unresolvedMass]
  push_cast [apply_ite (Rat.cast : ℚ → ℝ)]
  exact (integral_prefix (evaluator.depth stage) fun word ↦
    if evaluator.lower stage word < threshold ∧ threshold ≤ evaluator.upper stage word then
      (1 : ℝ) else 0).symm

/-- NOTE2 §7.2: when the boundary event on which the score equals the threshold is null, the
unresolved boundary mass tends to zero. Off the boundary the score lies strictly on one side of
the threshold, and the evaluations converging onto it eventually resolve the cylinder.
Assumes: the fair-bit probability that the score equals the threshold is zero. -/
theorem tendsto_unresolvedMass (evaluator : CylinderEvaluator score) (threshold : ℚ)
    (hboundary : bitMeasure {stream | score stream = threshold} = 0) :
    Tendsto (fun stage ↦ (unresolvedMass evaluator threshold stage : ℝ)) atTop (𝓝 0) := by
  have hnotBoundary : ∀ᵐ stream ∂bitMeasure, score stream ≠ threshold := by
    rw [ae_iff]
    simpa only [ne_eq, not_not] using hboundary
  have hlimit : ∀ᵐ stream ∂bitMeasure, Tendsto (fun stage ↦
      if lowerValue evaluator stage stream < threshold ∧
        threshold ≤ upperValue evaluator stage stream then (1 : ℝ) else 0) atTop (𝓝 0) := by
    filter_upwards [evaluator.tendsto_evaluations_ae, hnotBoundary] with stream hconverge hne
    refine tendsto_const_nhds.congr' ?_
    rcases lt_or_gt_of_ne hne with hbelow | habove
    · filter_upwards [hconverge.2.eventually (gt_mem_nhds hbelow)] with stage hstage
      have hreal : (upperValue evaluator stage stream : ℝ) < threshold := hstage
      have hrational : upperValue evaluator stage stream < threshold := by exact_mod_cast hreal
      rw [if_neg fun hboth ↦ absurd hboth.2 (not_le.mpr hrational)]
    · filter_upwards [hconverge.1.eventually (lt_mem_nhds habove)] with stage hstage
      have hreal : (threshold : ℝ) < lowerValue evaluator stage stream := hstage
      have hrational : threshold < lowerValue evaluator stage stream := by exact_mod_cast hreal
      rw [if_neg fun hboth ↦ absurd hboth.1 (not_lt.mpr hrational.le)]
  have hdominated := tendsto_integral_of_dominated_convergence (fun _ ↦ (1 : ℝ))
    (fun stage ↦ (measurable_prefix (evaluator.depth stage) fun word ↦
      if evaluator.lower stage word < threshold ∧ threshold ≤ evaluator.upper stage word then
        (1 : ℝ) else 0).aestronglyMeasurable)
    (integrable_const _)
    (fun stage ↦ ae_of_all _ fun stream ↦ by split_ifs <;> simp) hlimit
  rw [integral_zero] at hdominated
  simpa only [unresolvedMass_integral] using hdominated

/-- NOTE2 §7.2: when the boundary is null the resolved mass converges to the probability that
the score reaches the threshold, squeezed by the certificate. Assumes: the fair-bit
probability that the score equals the threshold is zero. -/
theorem tendsto_resolvedMass (evaluator : CylinderEvaluator score) (threshold : ℚ)
    (hboundary : bitMeasure {stream | score stream = threshold} = 0) :
    Tendsto (fun stage ↦ (resolvedMass evaluator threshold stage : ℝ)) atTop
      (𝓝 (bitMeasure.real {stream | (threshold : ℝ) ≤ score stream})) := by
  have hconst : Tendsto (fun _ : ℕ ↦ bitMeasure.real {stream | (threshold : ℝ) ≤ score stream})
      atTop (𝓝 (bitMeasure.real {stream | (threshold : ℝ) ≤ score stream})) :=
    tendsto_const_nhds
  have hbelow := hconst.sub (tendsto_unresolvedMass evaluator threshold hboundary)
  rw [sub_zero] at hbelow
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hbelow hconst (fun stage ↦ ?_)
    fun stage ↦ (resolvedMass_le_and_le_add evaluator threshold stage).1
  have hbracket := (resolvedMass_le_and_le_add evaluator threshold stage).2
  show bitMeasure.real {stream | (threshold : ℝ) ≤ score stream} -
    (unresolvedMass evaluator threshold stage : ℝ) ≤ (resolvedMass evaluator threshold stage : ℝ)
  linarith

/-- A score sitting exactly at the threshold, evaluated with brackets of half-width two to the
minus the stage, whose widths vanish on every stream. -/
def tieEvaluator (threshold : ℚ) : CylinderEvaluator fun _ ↦ (threshold : ℝ) where
  depth := fun stage ↦ stage
  lower := fun stage _ ↦ threshold - (1 / 2) ^ stage
  upper := fun stage _ ↦ threshold + (1 / 2) ^ stage
  depth_mono := monotone_id
  lower_le := fun stage _ _ _ _ ↦ by
    show ((threshold - (1 / 2) ^ stage : ℚ) : ℝ) ≤ threshold
    have hpositive : (0 : ℚ) < (1 / 2) ^ stage := by positivity
    exact_mod_cast (by linarith : threshold - (1 / 2) ^ stage ≤ threshold)
  le_upper := fun stage _ _ _ _ ↦ by
    show (threshold : ℝ) ≤ ((threshold + (1 / 2) ^ stage : ℚ) : ℝ)
    have hpositive : (0 : ℚ) < (1 / 2) ^ stage := by positivity
    exact_mod_cast (by linarith : threshold ≤ threshold + (1 / 2) ^ stage)
  lower_nested := fun stage _ _ ↦ by
    show threshold - (1 / 2) ^ stage ≤ threshold - (1 / 2) ^ (stage + 1)
    have hpositive : (0 : ℚ) ≤ (1 / 2) ^ stage := by positivity
    rw [pow_succ]
    linarith
  upper_nested := fun stage _ _ ↦ by
    show threshold + (1 / 2) ^ (stage + 1) ≤ threshold + (1 / 2) ^ stage
    have hpositive : (0 : ℚ) ≤ (1 / 2) ^ stage := by positivity
    rw [pow_succ]
    linarith
  width_ae := ae_of_all _ fun _ ↦ by
    have hlimit := (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num)
      (by norm_num)).const_mul 2
    rw [mul_zero] at hlimit
    refine hlimit.congr fun stage ↦ ?_
    push_cast
    ring

/-- The tie atom is never resolved: at every stage every cylinder of the tie evaluator
straddles the threshold, so its unresolved mass is one. -/
theorem unresolvedMass_tieEvaluator (threshold : ℚ) (stage : ℕ) :
    unresolvedMass (tieEvaluator threshold) threshold stage = 1 := by
  have hreal : (unresolvedMass (tieEvaluator threshold) threshold stage : ℝ) = 1 := by
    rw [unresolvedMass_cast]
    have hall : {stream : ℕ → Bool | lowerValue (tieEvaluator threshold) stage stream < threshold ∧
        threshold ≤ upperValue (tieEvaluator threshold) stage stream} = Set.univ := by
      ext stream
      have hpositive : (0 : ℚ) < (1 / 2) ^ stage := by positivity
      simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
      refine ⟨?_, ?_⟩
      · show threshold - (1 / 2) ^ stage < threshold
        linarith
      · show threshold ≤ threshold + (1 / 2) ^ stage
        linarith
    rw [hall, measureReal_univ_eq_one]
  exact_mod_cast hreal

/-- The tie atom is never resolved from below: at every stage the resolved mass of the tie
evaluator is zero, although the score reaches the threshold on every stream. -/
theorem resolvedMass_tieEvaluator (threshold : ℚ) (stage : ℕ) :
    resolvedMass (tieEvaluator threshold) threshold stage = 0 ∧
      bitMeasure.real {stream : ℕ → Bool | (threshold : ℝ) ≤ (fun _ ↦ (threshold : ℝ)) stream} =
        1 := by
  constructor
  · have hreal : (resolvedMass (tieEvaluator threshold) threshold stage : ℝ) = 0 := by
      rw [resolvedMass_cast]
      have hnone : {stream : ℕ → Bool |
          threshold ≤ lowerValue (tieEvaluator threshold) stage stream} = ∅ := by
        ext stream
        have hpositive : (0 : ℚ) < (1 / 2) ^ stage := by positivity
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_le]
        show threshold - (1 / 2) ^ stage < threshold
        linarith
      rw [hnone, measureReal_empty]
    exact_mod_cast hreal
  · have hall : {stream : ℕ → Bool | (threshold : ℝ) ≤ (fun _ ↦ (threshold : ℝ)) stream} =
        Set.univ := by
      ext stream
      simp
    rw [hall, measureReal_univ_eq_one]

/-! ### Optimizer comparisons -/

/-- A truncation of a word to a length at most its own has that length. -/
theorem length_take_of_le {word : List Bool} {length : ℕ} (hle : length ≤ word.length) :
    (word.take length).length = length := by
  rw [List.length_take, min_eq_left hle]

/-- A stream in the cylinder of a word lies in the cylinder of every truncation of the
word. -/
theorem take_mem_cylinder {word : List Bool} {stream : ℕ → Bool}
    (hstream : stream ∈ cylinder word) {length : ℕ} (hle : length ≤ word.length) :
    stream ∈ cylinder (word.take length) := by
  have hprefix := (mem_cylinder_iff word stream).mp hstream
  rw [mem_cylinder_iff, length_take_of_le hle, ← hprefix, take_prefixOf stream hle]

/-- A stream in the cylinder of a word of length `max left right` lies in the cylinders of the
truncations of the word to `left` and to `right`, and those truncations have those lengths. -/
theorem take_max_mem_cylinder {word : List Bool} {stream : ℕ → Bool}
    (hstream : stream ∈ cylinder word) {left right : ℕ}
    (hlength : word.length = max left right) :
    ((word.take left).length = left ∧ stream ∈ cylinder (word.take left)) ∧
      ((word.take right).length = right ∧ stream ∈ cylinder (word.take right)) := by
  have hleft : left ≤ word.length := le_of_le_of_eq (le_max_left left right) hlength.symm
  have hright : right ≤ word.length := le_of_le_of_eq (le_max_right left right) hlength.symm
  exact ⟨⟨length_take_of_le hleft, take_mem_cylinder hstream hleft⟩,
    ⟨length_take_of_le hright, take_mem_cylinder hstream hright⟩⟩

/-- NOTE2 §7.2 for an optimizer comparison: the cylinder evaluator of the difference of two
scores, on the finer of their two cylinder partitions. Its lower value is the lower value of
the first score minus the upper value of the second, and its upper value is the upper value of
the first minus the lower value of the second. -/
def differenceEvaluator {first second : (ℕ → Bool) → ℝ}
    (firstEvaluator : CylinderEvaluator first) (secondEvaluator : CylinderEvaluator second) :
    CylinderEvaluator fun stream ↦ first stream - second stream where
  depth := fun stage ↦ max (firstEvaluator.depth stage) (secondEvaluator.depth stage)
  lower := fun stage word ↦ firstEvaluator.lower stage (word.take (firstEvaluator.depth stage)) -
    secondEvaluator.upper stage (word.take (secondEvaluator.depth stage))
  upper := fun stage word ↦ firstEvaluator.upper stage (word.take (firstEvaluator.depth stage)) -
    secondEvaluator.lower stage (word.take (secondEvaluator.depth stage))
  depth_mono := fun _ _ hle ↦
    max_le_max (firstEvaluator.depth_mono hle) (secondEvaluator.depth_mono hle)
  lower_le := fun stage word hlength stream hstream ↦ by
    obtain ⟨⟨hfirstLength, hfirst⟩, ⟨hsecondLength, hsecond⟩⟩ :=
      take_max_mem_cylinder hstream hlength
    have hlow := firstEvaluator.lower_le stage _ hfirstLength stream hfirst
    have hhigh := secondEvaluator.le_upper stage _ hsecondLength stream hsecond
    show ((firstEvaluator.lower stage (word.take (firstEvaluator.depth stage)) -
      secondEvaluator.upper stage (word.take (secondEvaluator.depth stage)) : ℚ) : ℝ) ≤
        first stream - second stream
    push_cast
    linarith
  le_upper := fun stage word hlength stream hstream ↦ by
    obtain ⟨⟨hfirstLength, hfirst⟩, ⟨hsecondLength, hsecond⟩⟩ :=
      take_max_mem_cylinder hstream hlength
    have hhigh := firstEvaluator.le_upper stage _ hfirstLength stream hfirst
    have hlow := secondEvaluator.lower_le stage _ hsecondLength stream hsecond
    show first stream - second stream ≤
      ((firstEvaluator.upper stage (word.take (firstEvaluator.depth stage)) -
        secondEvaluator.lower stage (word.take (secondEvaluator.depth stage)) : ℚ) : ℝ)
    push_cast
    linarith
  lower_nested := fun stage word hlength ↦ by
    dsimp only
    rw [List.take_take, List.take_take, min_eq_left (le_max_left _ _),
      min_eq_left (le_max_right _ _)]
    have hfirstNested := firstEvaluator.lower_nested stage _
      (length_take_of_le (le_of_le_of_eq (le_max_left _ _) hlength.symm))
    have hsecondNested := secondEvaluator.upper_nested stage _
      (length_take_of_le (le_of_le_of_eq (le_max_right _ _) hlength.symm))
    rw [List.take_take, min_eq_left (firstEvaluator.depth_mono (Nat.le_succ stage))]
      at hfirstNested
    rw [List.take_take, min_eq_left (secondEvaluator.depth_mono (Nat.le_succ stage))]
      at hsecondNested
    linarith
  upper_nested := fun stage word hlength ↦ by
    dsimp only
    rw [List.take_take, List.take_take, min_eq_left (le_max_left _ _),
      min_eq_left (le_max_right _ _)]
    have hfirstNested := firstEvaluator.upper_nested stage _
      (length_take_of_le (le_of_le_of_eq (le_max_left _ _) hlength.symm))
    have hsecondNested := secondEvaluator.lower_nested stage _
      (length_take_of_le (le_of_le_of_eq (le_max_right _ _) hlength.symm))
    rw [List.take_take, min_eq_left (firstEvaluator.depth_mono (Nat.le_succ stage))]
      at hfirstNested
    rw [List.take_take, min_eq_left (secondEvaluator.depth_mono (Nat.le_succ stage))]
      at hsecondNested
    linarith
  width_ae := by
    filter_upwards [firstEvaluator.width_ae, secondEvaluator.width_ae] with stream hfirst hsecond
    have hsum := hfirst.add hsecond
    rw [add_zero] at hsum
    refine hsum.congr fun stage ↦ ?_
    simp only [take_prefixOf stream (le_max_left _ _), take_prefixOf stream (le_max_right _ _)]
    push_cast
    ring

/-- The event that the first score is at least the second is the event that their difference
reaches zero. -/
theorem setOf_le_eq_threshold (first second : (ℕ → Bool) → ℝ) :
    {stream : ℕ → Bool | second stream ≤ first stream} =
      {stream | ((0 : ℚ) : ℝ) ≤ first stream - second stream} := by
  ext stream
  simp [sub_nonneg]

/-- NOTE2 §7.2 for an optimizer comparison: at every stage the probability that the first score
is at least the second lies between the resolved mass of the difference evaluator at zero and
that mass plus its unresolved boundary mass. -/
theorem comparison_certificate {first second : (ℕ → Bool) → ℝ}
    (firstEvaluator : CylinderEvaluator first) (secondEvaluator : CylinderEvaluator second)
    (stage : ℕ) :
    (resolvedMass (differenceEvaluator firstEvaluator secondEvaluator) 0 stage : ℝ) ≤
        bitMeasure.real {stream | second stream ≤ first stream} ∧
      bitMeasure.real {stream | second stream ≤ first stream} ≤
        (resolvedMass (differenceEvaluator firstEvaluator secondEvaluator) 0 stage : ℝ) +
          unresolvedMass (differenceEvaluator firstEvaluator secondEvaluator) 0 stage := by
  rw [setOf_le_eq_threshold]
  exact resolvedMass_le_and_le_add (differenceEvaluator firstEvaluator secondEvaluator) 0 stage

/-- NOTE2 §7.2 for an optimizer comparison: when ties between the two scores are null, the
resolved mass of the difference evaluator converges to the probability that the first score is
at least the second. Assumes: the fair-bit probability of a tie is zero. -/
theorem tendsto_comparison_resolvedMass {first second : (ℕ → Bool) → ℝ}
    (firstEvaluator : CylinderEvaluator first) (secondEvaluator : CylinderEvaluator second)
    (hties : bitMeasure {stream | first stream = second stream} = 0) :
    Tendsto (fun stage ↦
        (resolvedMass (differenceEvaluator firstEvaluator secondEvaluator) 0 stage : ℝ)) atTop
      (𝓝 (bitMeasure.real {stream | second stream ≤ first stream})) := by
  rw [setOf_le_eq_threshold]
  exact tendsto_resolvedMass (differenceEvaluator firstEvaluator secondEvaluator) 0
    (by simpa [sub_eq_zero] using hties)

/-! ### Atomic discretizations are far from the stream law -/

/-- The fair-bit stream law has no atoms: a single stream lies in the cylinder of its prefix
of every length, whose mass two to the minus that length tends to zero. -/
theorem bitMeasure_singleton (stream : ℕ → Bool) : bitMeasure {stream} = 0 := by
  have hbound : ∀ length : ℕ, bitMeasure {stream} ≤ 2⁻¹ ^ length := fun length ↦ by
    calc bitMeasure {stream} ≤ bitMeasure (cylinder (prefixOf stream length)) :=
          measure_mono (Set.singleton_subset_iff.mpr (mem_cylinder_prefixOf stream length))
      _ = 2⁻¹ ^ length := by rw [bitMeasure_cylinder, length_prefixOf]
  have hlimit : Tendsto (fun length : ℕ ↦ (2⁻¹ : ℝ≥0∞) ^ length) atTop (𝓝 0) :=
    ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (ENNReal.inv_lt_one.mpr ENNReal.one_lt_two)
  exact le_antisymm (ge_of_tendsto' hlimit hbound) (zero_le _)

/-- The fair-bit stream law is non-atomic. -/
instance noAtoms_bitMeasure : NoAtoms bitMeasure :=
  ⟨bitMeasure_singleton⟩

/-- NOTE2 §7.2: a law concentrated on countably many streams, in particular any atomic
discretization, puts mass one on an event of fair-bit mass zero, so its distance from the
stream law on that event is one. -/
theorem discretization_event_gap (law : Measure (ℕ → Bool)) [IsProbabilityMeasure law]
    {support : Set (ℕ → Bool)} (hsupport : support.Countable)
    (hconcentrated : law supportᶜ = 0) :
    law.real support - bitMeasure.real support = 1 := by
  have hfull : law support = 1 :=
    (prob_compl_eq_zero_iff hsupport.measurableSet).mp hconcentrated
  rw [measureReal_def, measureReal_def, hfull, hsupport.measure_zero bitMeasure]
  simp

/-- Coordinate rounding at a resolution: keep the first `resolution` bits of a stream and set
every later bit to `false`. -/
def roundToResolution (resolution : ℕ) (stream : ℕ → Bool) (index : ℕ) : Bool :=
  if index < resolution then stream index else false

/-- Coordinate rounding is measurable. -/
theorem measurable_roundToResolution (resolution : ℕ) :
    Measurable (roundToResolution resolution) := by
  refine measurable_pi_lambda _ fun index ↦ ?_
  by_cases hindex : index < resolution
  · simp only [roundToResolution, if_pos hindex]
    exact measurable_pi_apply index
  · simp only [roundToResolution, if_neg hindex]
    exact measurable_const

/-- Rounding at a resolution does not move a stream into or out of a cylinder of depth at most
that resolution. -/
theorem roundToResolution_mem_cylinder_iff (resolution : ℕ) {word : List Bool}
    (hword : word.length ≤ resolution) (stream : ℕ → Bool) :
    roundToResolution resolution stream ∈ cylinder word ↔ stream ∈ cylinder word := by
  simp only [CylinderIntervalCertificate.cylinder, Set.mem_pi, Finset.coe_range, Set.mem_Iio,
    Set.mem_singleton_iff]
  refine forall_congr' fun index ↦ imp_congr_right fun hindex ↦ ?_
  simp only [roundToResolution, if_pos (lt_of_lt_of_le hindex hword)]

/-- NOTE2 §7.2: the law of the rounded stream reproduces the mass of every cylinder of depth
at most the resolution. -/
theorem roundedLaw_cylinder (resolution : ℕ) {word : List Bool}
    (hword : word.length ≤ resolution) :
    bitMeasure.map (roundToResolution resolution) (cylinder word) =
      bitMeasure (cylinder word) := by
  rw [Measure.map_apply (measurable_roundToResolution resolution) (measurableSet_cylinder word)]
  congr 1
  ext stream
  exact roundToResolution_mem_cylinder_iff resolution hword stream

/-- The rounded streams at a resolution form a countable set: each is determined by its word
of that length. -/
theorem countable_range_roundToResolution (resolution : ℕ) :
    (Set.range (roundToResolution resolution)).Countable := by
  have hsubset : Set.range (roundToResolution resolution) ⊆
      Set.range fun word : wordsOfLength resolution ↦
        roundToResolution resolution fun index ↦ (word : List Bool).getD index false := by
    rintro _ ⟨stream, rfl⟩
    refine ⟨⟨prefixOf stream resolution,
      mem_wordsOfLength.mpr (length_prefixOf stream resolution)⟩, ?_⟩
    funext index
    by_cases hindex : index < resolution
    · simp only [roundToResolution, if_pos hindex]
      exact getD_prefixOf stream hindex
    · simp only [roundToResolution, if_neg hindex]
  exact (Set.finite_range _).countable.mono hsubset

/-- NOTE2 §7.2: coordinate rounding is at event distance one from the stream law at every
resolution. The rounded law puts all its mass on its own countable range, which the stream law
does not see, although it reproduces every cylinder of depth at most the resolution. -/
theorem roundedLaw_range_gap (resolution : ℕ) :
    (bitMeasure.map (roundToResolution resolution)).real
        (Set.range (roundToResolution resolution)) -
      bitMeasure.real (Set.range (roundToResolution resolution)) = 1 := by
  haveI := Measure.isProbabilityMeasure_map (μ := bitMeasure)
    (measurable_roundToResolution resolution).aemeasurable
  refine discretization_event_gap _ (countable_range_roundToResolution resolution) ?_
  rw [Measure.map_apply (measurable_roundToResolution resolution)
    (countable_range_roundToResolution resolution).measurableSet.compl]
  have hempty : roundToResolution resolution ⁻¹' (Set.range (roundToResolution resolution))ᶜ =
      ∅ := by
    ext stream
    simp
  rw [hempty, measure_empty]

end

end Descent.Portability.CylinderThresholdCertificate
