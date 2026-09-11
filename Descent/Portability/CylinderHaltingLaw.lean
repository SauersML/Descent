/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.CylinderIntervalCertificate

assert_below Descent.Decision Descent.Program

/-!
# The halting law of an almost surely terminating random-bit program

NOTE2 (32) says that a countable report produced by an almost surely terminating random-bit
program has the exact law `P = sum over minimal halting prefixes w of two to the minus |w|
times the point mass at the report of w`, that a finite prefix enumeration is a positive
sublaw of mass `1 - ε` with `ε` known exactly and tending to zero, and that the same residual
mass certifies every bounded countable-report expectation. This module proves all three on
the fair-bit stream space of `CylinderIntervalCertificate`.

A `HaltingProgram` is a countable set of halting prefixes, the report produced on each, the
prefix-freeness of the set, and almost sure termination stated as total cylinder mass one.
`pairwiseDisjoint_cylinder` turns prefix-freeness into disjoint cylinders, and `law` is the
measure of (32) as a countable sum of scaled point masses. `law_apply` shows that it is the
law of the report: each event of reports has the fair-bit mass of the union of the cylinders
of the prefixes reporting into it, and `isProbabilityMeasure_law` is almost sure termination.
`integral_law` evaluates every bounded report expectation as the dyadic series over the
halting prefixes.

A finite enumeration of halting prefixes gives `enumeratedLaw`, a finite sum of point masses
below `law` of total mass `1 - missingMass`. `missingMass_eq_tsum_compl` shows that the
residual mass is exactly the dyadic mass of the unenumerated prefixes, `missingMass_eq_bitMeasure`
that it is the fair-bit probability of halting at one of them, and `tendsto_missingMass` and
`tendsto_missingMass_enumeration` that it tends to zero along finite sets and along any
enumeration. `expectation_bounds` is NOTE 1 (24) on a countable report space, and
`conditional_expectation_bounds` is NOTE 1 (25) and NOTE2 (35) there, through the corpus
`SublawReportCertificate.ratio_bounds`. On a finite report space `haltingSublaw_missingMass_eq`
identifies the missing mass with that of the corpus `IntervalEvaluatorCertificate.haltingSublaw`.

The witness `waitForTrue` reads bits until the first `true` and reports how many `false` bits
it read. It halts almost surely and not surely, because the all-`false` stream never halts,
so the almost sure clause is doing work.

Not formalized here: that almost sure termination can be established for a given program,
which NOTE2 notes is not decidable in general and which enters here only as the structure
field; and computability of the report map.

## Empirical status

None. The bodies here are measure theory and algebra: the program is a supplied object, and
every conclusion follows from countable additivity of the fair-bit product measure and
bounds on series, so no measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.CylinderHaltingLaw

open MeasureTheory Filter CylinderIntervalCertificate

open scoped ENNReal Topology

noncomputable section

/-- The dyadic weight of a word, two to the minus its length. -/
def dyadicWeight (word : List Bool) : ℝ :=
  (1 / 2 : ℝ) ^ word.length

/-- Dyadic weights are nonnegative. -/
theorem dyadicWeight_nonneg (word : List Bool) : 0 ≤ dyadicWeight word := by
  unfold dyadicWeight
  positivity

/-- The dyadic weight of a word is the fair-bit mass of its cylinder. -/
theorem bitMeasure_real_cylinder_eq_dyadicWeight (word : List Bool) :
    bitMeasure.real (cylinder word) = dyadicWeight word :=
  bitMeasure_real_cylinder word

/-- NOTE2 (32): a random-bit program with a countable report, presented by its minimal halting
prefixes and the report produced on each. The prefixes are prefix-free, and their cylinders
carry total mass one, which is almost sure termination. -/
structure HaltingProgram (Report : Type*) where
  halting : Set (List Bool)
  report : List Bool → Report
  prefixFree : ∀ first ∈ halting, ∀ second ∈ halting, first <+: second → first = second
  halts_ae : bitMeasure (⋃ word ∈ halting, cylinder word) = 1

namespace HaltingProgram

variable {Report : Type*}

/-- Distinct halting prefixes have disjoint cylinders: a stream in both would carry both as
prefixes, and the shorter would be a prefix of the longer. -/
theorem pairwiseDisjoint_cylinder (program : HaltingProgram Report) :
    program.halting.PairwiseDisjoint cylinder := by
  intro first hfirst second hsecond hdifferent
  show Disjoint (cylinder first) (cylinder second)
  refine Set.disjoint_left.mpr fun stream hstreamFirst hstreamSecond ↦ hdifferent ?_
  rw [mem_cylinder_iff] at hstreamFirst hstreamSecond
  rcases le_total first.length second.length with hle | hle
  · refine program.prefixFree first hfirst second hsecond ?_
    rw [← hstreamFirst, ← hstreamSecond, ← take_prefixOf stream hle]
    exact List.take_prefix _ _
  · refine (program.prefixFree second hsecond first hfirst ?_).symm
    rw [← hstreamFirst, ← hstreamSecond, ← take_prefixOf stream hle]
    exact List.take_prefix _ _

/-- NOTE2 (32): the law of the report of a halting program, the countable sum over its
minimal halting prefixes of two to the minus the length times the point mass at the
report. -/
def law [MeasurableSpace Report] (program : HaltingProgram Report) : Measure Report :=
  Measure.sum fun word : program.halting ↦
    (2⁻¹ : ℝ≥0∞) ^ (word : List Bool).length • Measure.dirac (program.report word)

/-- NOTE2 (32) is the law of the report: every measurable event of reports has the fair-bit
mass of the union of the cylinders of the halting prefixes whose report lies in it. -/
theorem law_apply [MeasurableSpace Report] (program : HaltingProgram Report)
    {event : Set Report} (hevent : MeasurableSet event) :
    program.law event =
      bitMeasure (⋃ word ∈ {word ∈ program.halting | program.report word ∈ event},
        cylinder word) := by
  rw [measure_biUnion (Set.to_countable _)
    (program.pairwiseDisjoint_cylinder.subset fun _ hword ↦ hword.1)
    fun word _ ↦ measurableSet_cylinder word, law, Measure.sum_apply _ hevent]
  simp only [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply' _ hevent,
    bitMeasure_cylinder]
  rw [tsum_subtype program.halting
      (fun word ↦ (2⁻¹ : ℝ≥0∞) ^ word.length * event.indicator 1 (program.report word)),
    tsum_subtype {word ∈ program.halting | program.report word ∈ event}
      (fun word : List Bool ↦ (2⁻¹ : ℝ≥0∞) ^ word.length)]
  refine tsum_congr fun word ↦ ?_
  by_cases hword : word ∈ program.halting <;>
    by_cases hreport : program.report word ∈ event <;>
    simp [Set.indicator_apply, hword, hreport]

/-- NOTE2 (32): the halting law is a probability law, because the halting cylinders carry
total mass one. -/
theorem isProbabilityMeasure_law [MeasurableSpace Report] (program : HaltingProgram Report) :
    IsProbabilityMeasure program.law := by
  constructor
  rw [program.law_apply MeasurableSet.univ]
  simpa only [Set.mem_univ, and_true, Set.sep_true, Set.setOf_mem_eq] using program.halts_ae

/-- Almost sure termination in dyadic form: the weights of the halting prefixes sum to
one. -/
theorem hasSum_dyadicWeight (program : HaltingProgram Report) :
    HasSum (fun word : program.halting ↦ dyadicWeight word) 1 := by
  have hmeasure : ∑' word : program.halting, bitMeasure (cylinder word) = 1 :=
    (measure_biUnion (Set.to_countable _) program.pairwiseDisjoint_cylinder
      fun word _ ↦ measurableSet_cylinder word).symm.trans program.halts_ae
  have hsummable := ENNReal.summable_toReal
    (f := fun word : program.halting ↦ bitMeasure (cylinder word))
    (by rw [hmeasure]; exact ENNReal.one_ne_top)
  have htsum := ENNReal.tsum_toReal_eq
    (f := fun word : program.halting ↦ bitMeasure (cylinder word))
    fun _ ↦ measure_ne_top bitMeasure _
  rw [hmeasure, ENNReal.toReal_one] at htsum
  have hweight : ∀ word : program.halting,
      (bitMeasure (cylinder word)).toReal = dyadicWeight word :=
    fun word ↦ bitMeasure_real_cylinder word
  simp only [hweight] at hsummable htsum
  rw [htsum]
  exact hsummable.hasSum

/-- The dyadic mass accounted by a finite enumeration of halting prefixes. -/
def enumeratedMass (program : HaltingProgram Report) (enumerated : Finset program.halting) :
    ℝ :=
  ∑ word ∈ enumerated, dyadicWeight word

/-- NOTE2 (32): the mass a finite enumeration of halting prefixes misses. -/
def missingMass (program : HaltingProgram Report) (enumerated : Finset program.halting) : ℝ :=
  1 - program.enumeratedMass enumerated

/-- NOTE2 (32): the missing mass is exactly the dyadic mass of the halting prefixes that the
enumeration did not reach. -/
theorem missingMass_eq_tsum_compl (program : HaltingProgram Report)
    (enumerated : Finset program.halting) :
    program.missingMass enumerated =
      ∑' word : ↑((enumerated : Set program.halting)ᶜ), dyadicWeight word := by
  have hsplit := program.hasSum_dyadicWeight.summable.sum_add_tsum_compl (s := enumerated)
  rw [program.hasSum_dyadicWeight.tsum_eq] at hsplit
  rw [missingMass, enumeratedMass]
  linarith

/-- The missing mass of a finite enumeration is nonnegative. -/
theorem missingMass_nonneg (program : HaltingProgram Report)
    (enumerated : Finset program.halting) : 0 ≤ program.missingMass enumerated := by
  rw [missingMass_eq_tsum_compl]
  exact tsum_nonneg fun _ ↦ dyadicWeight_nonneg _

/-- NOTE2 (32): the missing mass is the fair-bit probability that the program halts at a
prefix the enumeration did not reach. -/
theorem missingMass_eq_bitMeasure (program : HaltingProgram Report)
    (enumerated : Finset program.halting) :
    program.missingMass enumerated =
      bitMeasure.real (⋃ word ∈ ((enumerated : Set program.halting)ᶜ),
        cylinder (word : List Bool)) := by
  have hdisjoint : ((enumerated : Set program.halting)ᶜ).PairwiseDisjoint
      fun word : program.halting ↦ cylinder (word : List Bool) := by
    intro first _ second _ hdifferent
    exact program.pairwiseDisjoint_cylinder first.2 second.2
      fun hequal ↦ hdifferent (Subtype.ext hequal)
  rw [missingMass_eq_tsum_compl, measureReal_def, measure_biUnion (Set.to_countable _) hdisjoint
    fun word _ ↦ measurableSet_cylinder _, ENNReal.tsum_toReal_eq fun _ ↦ measure_ne_top _ _]
  exact tsum_congr fun word ↦ (bitMeasure_real_cylinder _).symm

/-- NOTE2 (32): the missing mass tends to zero along the finite sets of halting prefixes. -/
theorem tendsto_missingMass (program : HaltingProgram Report) :
    Tendsto program.missingMass atTop (𝓝 0) := by
  have hsum : Tendsto (fun enumerated : Finset program.halting ↦
      program.enumeratedMass enumerated) atTop (𝓝 1) :=
    program.hasSum_dyadicWeight
  have hconst : Tendsto (fun _ : Finset program.halting ↦ (1 : ℝ)) atTop (𝓝 1) :=
    tendsto_const_nhds
  have hdifference := hconst.sub hsum
  rw [sub_self] at hdifference
  exact hdifference

/-- NOTE2 (32): along any enumeration of the halting prefixes, the missing mass of the first
`count` enumerated prefixes tends to zero. -/
theorem tendsto_missingMass_enumeration (program : HaltingProgram Report)
    (enumerate : ℕ → program.halting) (hsurjective : Function.Surjective enumerate) :
    Tendsto (fun count ↦ program.missingMass ((Finset.range count).image enumerate)) atTop
      (𝓝 0) := by
  refine program.tendsto_missingMass.comp (tendsto_atTop_finset_of_monotone ?_ ?_)
  · intro first second hle
    exact Finset.image_subset_image (Finset.range_mono hle)
  · intro word
    obtain ⟨index, hindex⟩ := hsurjective word
    exact ⟨index + 1,
      Finset.mem_image.mpr ⟨index, Finset.mem_range.mpr (Nat.lt_succ_self index), hindex⟩⟩

/-- NOTE2 (32): the positive sublaw of a finite enumeration, the finite sum of the point
masses at the reports of the enumerated prefixes, weighted by their dyadic masses. -/
def enumeratedLaw [MeasurableSpace Report] (program : HaltingProgram Report)
    (enumerated : Finset program.halting) : Measure Report :=
  ∑ word ∈ enumerated,
    (2⁻¹ : ℝ≥0∞) ^ (word : List Bool).length • Measure.dirac (program.report word)

/-- NOTE2 (32): the enumerated sublaw never exceeds the halting law. -/
theorem enumeratedLaw_le_law [MeasurableSpace Report] (program : HaltingProgram Report)
    (enumerated : Finset program.halting) : program.enumeratedLaw enumerated ≤ program.law := by
  refine Measure.le_iff.mpr fun event hevent ↦ ?_
  rw [enumeratedLaw, Measure.coe_finset_sum, Finset.sum_apply, law, Measure.sum_apply _ hevent]
  exact ENNReal.sum_le_tsum enumerated

/-- NOTE2 (32): the enumerated sublaw has total mass one minus the missing mass. -/
theorem enumeratedLaw_real_univ [MeasurableSpace Report] (program : HaltingProgram Report)
    (enumerated : Finset program.halting) :
    (program.enumeratedLaw enumerated).real Set.univ = 1 - program.missingMass enumerated := by
  have hfinite : ∀ word ∈ enumerated, ((2⁻¹ : ℝ≥0∞) ^ (word : List Bool).length •
      Measure.dirac (program.report word)) Set.univ ≠ ⊤ := fun _ _ ↦ by simp
  rw [measureReal_def, enumeratedLaw, Measure.coe_finset_sum, Finset.sum_apply,
    ENNReal.toReal_sum hfinite]
  simp [missingMass, enumeratedMass, dyadicWeight]

/-- The weighted report values of the halting prefixes are summable for a bounded value. -/
theorem summable_weighted (program : HaltingProgram Report) (value : Report → ℝ) {bound : ℝ}
    (hbound : ∀ report, |value report| ≤ bound) :
    Summable fun word : program.halting ↦ dyadicWeight word * value (program.report word) :=
  (program.hasSum_dyadicWeight.summable.mul_right bound).of_norm_bounded fun word ↦ by
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (dyadicWeight_nonneg _)]
    exact mul_le_mul_of_nonneg_left (hbound _) (dyadicWeight_nonneg _)

/-- NOTE2 (32): the expectation of a bounded report value under the halting law is the dyadic
series over the halting prefixes. -/
theorem integral_law [MeasurableSpace Report] [MeasurableSingletonClass Report]
    [Countable Report] (program : HaltingProgram Report) (value : Report → ℝ) {bound : ℝ}
    (hbound : ∀ report, |value report| ≤ bound) :
    ∫ report, value report ∂program.law =
      ∑' word : program.halting, dyadicWeight word * value (program.report word) := by
  haveI := program.isProbabilityMeasure_law
  have hintegrable : Integrable value program.law :=
    IntervalEvaluatorCertificate.integrable_of_abs_le_const program.law
      (measurable_of_countable value) bound hbound
  rw [law, integral_sum_measure hintegrable]
  refine tsum_congr fun word ↦ ?_
  rw [integral_smul_measure, integral_dirac, ENNReal.toReal_pow, ENNReal.toReal_inv,
    ENNReal.toReal_ofNat, smul_eq_mul, dyadicWeight, one_div]

/-- The accounted report total of a finite enumeration of halting prefixes. -/
def enumeratedTotal (program : HaltingProgram Report) (enumerated : Finset program.halting)
    (value : Report → ℝ) : ℝ :=
  ∑ word ∈ enumerated, dyadicWeight word * value (program.report word)

/-- A bounded report expectation under the halting law splits into the accounted total of a
finite enumeration and the dyadic series over the unenumerated prefixes. -/
theorem integral_law_eq_enumeratedTotal_add [MeasurableSpace Report]
    [MeasurableSingletonClass Report] [Countable Report] (program : HaltingProgram Report)
    (enumerated : Finset program.halting) (value : Report → ℝ) {bound : ℝ}
    (hbound : ∀ report, |value report| ≤ bound) :
    ∫ report, value report ∂program.law =
      program.enumeratedTotal enumerated value +
        ∑' word : ↑((enumerated : Set program.halting)ᶜ),
          dyadicWeight word * value (program.report word) := by
  rw [program.integral_law value hbound, enumeratedTotal]
  exact ((program.summable_weighted value hbound).sum_add_tsum_compl (s := enumerated)).symm

end HaltingProgram

/-- A nonnegative summable weighting of a value squeezed between two constants has weighted
series squeezed between the constants times the total weight. -/
theorem tsum_weighted_value_bounds {Index : Type*} (weight : Index → ℝ)
    (hweight : ∀ index, 0 ≤ weight index) (hsummable : Summable weight) (value : Index → ℝ)
    (lower upper : ℝ) (hlower : ∀ index, lower ≤ value index)
    (hupper : ∀ index, value index ≤ upper) :
    lower * ∑' index, weight index ≤ ∑' index, weight index * value index ∧
      ∑' index, weight index * value index ≤ upper * ∑' index, weight index := by
  have hvalue : Summable fun index ↦ weight index * value index :=
    (hsummable.mul_right (|lower| + |upper|)).of_norm_bounded fun index ↦ by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hweight index)]
      refine mul_le_mul_of_nonneg_left ?_ (hweight index)
      have hbelow := hlower index
      have habove := hupper index
      have hlowerAbs := neg_abs_le lower
      have hupperAbs := le_abs_self upper
      have hlowerNonneg := abs_nonneg lower
      have hupperNonneg := abs_nonneg upper
      rw [abs_le]
      constructor <;> linarith
  constructor
  · rw [mul_comm lower, ← tsum_mul_right]
    exact Summable.tsum_le_tsum
      (fun index ↦ mul_le_mul_of_nonneg_left (hlower index) (hweight index))
      (hsummable.mul_right lower) hvalue
  · rw [mul_comm upper, ← tsum_mul_right]
    exact Summable.tsum_le_tsum
      (fun index ↦ mul_le_mul_of_nonneg_left (hupper index) (hweight index))
      hvalue (hsummable.mul_right upper)

namespace HaltingProgram

variable {Report : Type*}

/-- NOTE2 (32), certification of every bounded countable-report expectation, which is NOTE 1
(24) on a countable report space. A finite enumeration of halting prefixes certifies the
expectation of every report value in `[lower, upper]`: it lies between the accounted total
plus `lower` times the missing mass and the accounted total plus `upper` times the missing
mass. -/
theorem expectation_bounds [MeasurableSpace Report] [MeasurableSingletonClass Report]
    [Countable Report] (program : HaltingProgram Report) (enumerated : Finset program.halting)
    (value : Report → ℝ) (lower upper : ℝ) (hlower : ∀ report, lower ≤ value report)
    (hupper : ∀ report, value report ≤ upper) :
    program.enumeratedTotal enumerated value + lower * program.missingMass enumerated ≤
        ∫ report, value report ∂program.law ∧
      ∫ report, value report ∂program.law ≤
        program.enumeratedTotal enumerated value + upper * program.missingMass enumerated := by
  have hbound : ∀ report, |value report| ≤ |lower| + |upper| := fun report ↦ by
    have hbelow := hlower report
    have habove := hupper report
    have hlowerAbs := neg_abs_le lower
    have hupperAbs := le_abs_self upper
    have hlowerNonneg := abs_nonneg lower
    have hupperNonneg := abs_nonneg upper
    rw [abs_le]
    constructor <;> linarith
  have hsplit := program.integral_law_eq_enumeratedTotal_add enumerated value hbound
  obtain ⟨htailBelow, htailAbove⟩ := tsum_weighted_value_bounds
    (fun word : ↑((enumerated : Set program.halting)ᶜ) ↦ dyadicWeight word)
    (fun _ ↦ dyadicWeight_nonneg _) (program.hasSum_dyadicWeight.summable.subtype _)
    (fun word ↦ value (program.report word)) lower upper (fun _ ↦ hlower _) (fun _ ↦ hupper _)
  beta_reduce at htailBelow htailAbove
  rw [← program.missingMass_eq_tsum_compl] at htailBelow htailAbove
  constructor <;> linarith

/-- NOTE 1 (25) and NOTE2 (35) on a countable report space. When a finite enumeration of
halting prefixes already accounts for positive definedness mass, the conditional expectation
of a report value in `[lower, upper]` given a decidable definedness event lies between the two
ratios obtained by adding the whole missing mass to the accounted definedness mass and the
extreme values times the missing mass to the accounted defined total. The algebra is the
corpus `SublawReportCertificate.ratio_bounds`. Assumes: the accounted definedness mass is
positive. -/
theorem conditional_expectation_bounds [MeasurableSpace Report]
    [MeasurableSingletonClass Report] [Countable Report] (program : HaltingProgram Report)
    (enumerated : Finset program.halting) (defined : Report → Prop) [DecidablePred defined]
    (value : Report → ℝ) (lower upper : ℝ) (hlower : ∀ report, lower ≤ value report)
    (hupper : ∀ report, value report ≤ upper)
    (hpositive : 0 < program.enumeratedTotal enumerated
      (SublawReportCertificate.definedIndicator defined)) :
    (program.enumeratedTotal enumerated
          (fun report ↦ SublawReportCertificate.definedIndicator defined report * value report) +
        lower * program.missingMass enumerated) /
        (program.enumeratedTotal enumerated (SublawReportCertificate.definedIndicator defined) +
          program.missingMass enumerated) ≤
      (∫ report, SublawReportCertificate.definedIndicator defined report * value report
          ∂program.law) /
        ∫ report, SublawReportCertificate.definedIndicator defined report ∂program.law ∧
    (∫ report, SublawReportCertificate.definedIndicator defined report * value report
          ∂program.law) /
        ∫ report, SublawReportCertificate.definedIndicator defined report ∂program.law ≤
      (program.enumeratedTotal enumerated
          (fun report ↦ SublawReportCertificate.definedIndicator defined report * value report) +
        upper * program.missingMass enumerated) /
        (program.enumeratedTotal enumerated (SublawReportCertificate.definedIndicator defined) +
          program.missingMass enumerated) := by
  have hindicatorBelow := SublawReportCertificate.definedIndicator_nonneg defined
  have hindicatorAbove := SublawReportCertificate.definedIndicator_le_one defined
  have hbound : ∀ report, |value report| ≤ |lower| + |upper| := fun report ↦ by
    have hbelow := hlower report
    have habove := hupper report
    have hlowerAbs := neg_abs_le lower
    have hupperAbs := le_abs_self upper
    have hlowerNonneg := abs_nonneg lower
    have hupperNonneg := abs_nonneg upper
    rw [abs_le]
    constructor <;> linarith
  have hindicatorBound : ∀ report,
      |SublawReportCertificate.definedIndicator defined report| ≤ 1 := fun report ↦ by
    rw [abs_of_nonneg (hindicatorBelow report)]
    exact hindicatorAbove report
  have hproductBound : ∀ report,
      |SublawReportCertificate.definedIndicator defined report * value report| ≤
        |lower| + |upper| := fun report ↦ by
    rw [abs_mul]
    calc |SublawReportCertificate.definedIndicator defined report| * |value report|
        ≤ 1 * |value report| :=
          mul_le_mul_of_nonneg_right (hindicatorBound report) (abs_nonneg _)
      _ ≤ |lower| + |upper| := by rw [one_mul]; exact hbound report
  have hmassSplit := program.integral_law_eq_enumeratedTotal_add enumerated
    (SublawReportCertificate.definedIndicator defined) hindicatorBound
  have htotalSplit := program.integral_law_eq_enumeratedTotal_add enumerated
    (fun report ↦ SublawReportCertificate.definedIndicator defined report * value report)
    hproductBound
  obtain ⟨hmassTailBelow, hmassTailAbove⟩ := tsum_weighted_value_bounds
    (fun word : ↑((enumerated : Set program.halting)ᶜ) ↦ dyadicWeight word)
    (fun _ ↦ dyadicWeight_nonneg _) (program.hasSum_dyadicWeight.summable.subtype _)
    (fun word ↦ SublawReportCertificate.definedIndicator defined (program.report word)) 0 1
    (fun _ ↦ hindicatorBelow _) (fun _ ↦ hindicatorAbove _)
  beta_reduce at hmassTailBelow hmassTailAbove
  rw [← program.missingMass_eq_tsum_compl] at hmassTailBelow hmassTailAbove
  have hweightedSummable : Summable fun word : ↑((enumerated : Set program.halting)ᶜ) ↦
      dyadicWeight word * SublawReportCertificate.definedIndicator defined
        (program.report word) :=
    (program.summable_weighted _ hindicatorBound).subtype _
  obtain ⟨htotalTailBelow, htotalTailAbove⟩ := tsum_weighted_value_bounds
    (fun word : ↑((enumerated : Set program.halting)ᶜ) ↦
      dyadicWeight word * SublawReportCertificate.definedIndicator defined
        (program.report word))
    (fun _ ↦ mul_nonneg (dyadicWeight_nonneg _) (hindicatorBelow _)) hweightedSummable
    (fun word ↦ value (program.report word)) lower upper (fun _ ↦ hlower _) (fun _ ↦ hupper _)
  beta_reduce at htotalTailBelow htotalTailAbove
  have hassociate : ∑' word : ↑((enumerated : Set program.halting)ᶜ),
      dyadicWeight word * SublawReportCertificate.definedIndicator defined
        (program.report word) * value (program.report word) =
      ∑' word : ↑((enumerated : Set program.halting)ᶜ),
        dyadicWeight word * (SublawReportCertificate.definedIndicator defined
          (program.report word) * value (program.report word)) :=
    tsum_congr fun _ ↦ mul_assoc _ _ _
  rw [hassociate] at htotalTailBelow htotalTailAbove
  have haccountedBelow : lower * program.enumeratedTotal enumerated
      (SublawReportCertificate.definedIndicator defined) ≤
      program.enumeratedTotal enumerated
        (fun report ↦ SublawReportCertificate.definedIndicator defined report * value report) := by
    rw [enumeratedTotal, enumeratedTotal, Finset.mul_sum]
    refine Finset.sum_le_sum fun word _ ↦ ?_
    have hweight := mul_nonneg (dyadicWeight_nonneg (word : List Bool))
      (hindicatorBelow (program.report word))
    nlinarith [mul_le_mul_of_nonneg_left (hlower (program.report word)) hweight]
  have haccountedAbove : program.enumeratedTotal enumerated
      (fun report ↦ SublawReportCertificate.definedIndicator defined report * value report) ≤
      upper * program.enumeratedTotal enumerated
        (SublawReportCertificate.definedIndicator defined) := by
    rw [enumeratedTotal, enumeratedTotal, Finset.mul_sum]
    refine Finset.sum_le_sum fun word _ ↦ ?_
    have hweight := mul_nonneg (dyadicWeight_nonneg (word : List Bool))
      (hindicatorBelow (program.report word))
    nlinarith [mul_le_mul_of_nonneg_left (hupper (program.report word)) hweight]
  obtain ⟨hratioBelow, hratioAbove⟩ := SublawReportCertificate.ratio_bounds lower upper
    (program.enumeratedTotal enumerated (SublawReportCertificate.definedIndicator defined))
    (program.enumeratedTotal enumerated
      (fun report ↦ SublawReportCertificate.definedIndicator defined report * value report))
    (∑' word : ↑((enumerated : Set program.halting)ᶜ),
      dyadicWeight word * SublawReportCertificate.definedIndicator defined (program.report word))
    (∑' word : ↑((enumerated : Set program.halting)ᶜ),
      dyadicWeight word * (SublawReportCertificate.definedIndicator defined
        (program.report word) * value (program.report word)))
    (program.missingMass enumerated) hpositive (by linarith) (by linarith)
    haccountedBelow haccountedAbove htotalTailBelow htotalTailAbove
  rw [← hmassSplit, ← htotalSplit] at hratioBelow hratioAbove
  exact ⟨hratioBelow, hratioAbove⟩

/-- A finite enumeration of halting prefixes, read as a finite set of words. -/
def enumeratedWords (program : HaltingProgram Report) (enumerated : Finset program.halting) :
    Finset (List Bool) :=
  enumerated.map (Function.Embedding.subtype _)

/-- A finite enumeration of halting prefixes is a prefix-free set of words in the sense of the
corpus Kraft inequality. -/
theorem prefixFree_enumeratedWords (program : HaltingProgram Report)
    (enumerated : Finset program.halting) :
    IntervalEvaluatorCertificate.PrefixFree (program.enumeratedWords enumerated) := by
  intro first hfirst second hsecond hprefix
  obtain ⟨firstWord, _, rfl⟩ := Finset.mem_map.mp hfirst
  obtain ⟨secondWord, _, rfl⟩ := Finset.mem_map.mp hsecond
  exact program.prefixFree _ firstWord.2 _ secondWord.2 hprefix

/-- NOTE2 (32) on a finite report space: the corpus halting sublaw of a finite enumeration
misses exactly the missing mass of that enumeration. -/
theorem haltingSublaw_missingMass_eq [Fintype Report] [DecidableEq Report]
    (program : HaltingProgram Report) (enumerated : Finset program.halting) :
    (IntervalEvaluatorCertificate.haltingSublaw (program.enumeratedWords enumerated)
      (program.prefixFree_enumeratedWords enumerated) program.report).missingMass =
      program.missingMass enumerated := by
  rw [IntervalEvaluatorCertificate.haltingSublaw_missingMass, enumeratedWords, Finset.sum_map]
  rfl

end HaltingProgram

/-! ### A program that halts almost surely and not surely -/

/-- The minimal halting prefixes of the program that reads fair bits until the first `true`:
some number of `false` bits followed by one `true` bit. -/
def waitingWords : Set (List Bool) :=
  Set.range fun count : ℕ ↦ List.replicate count false ++ [true]

/-- The waiting words are prefix-free: a shorter one ends in `true` where a longer one still
reads `false`. -/
theorem waitingWords_prefixFree :
    ∀ first ∈ waitingWords, ∀ second ∈ waitingWords, first <+: second → first = second := by
  rintro _ ⟨shorter, rfl⟩ _ ⟨longer, rfl⟩ hprefix
  have hlength : shorter ≤ longer := by
    have hle := hprefix.length_le
    simp only [List.length_append, List.length_replicate, List.length_singleton] at hle
    omega
  rcases lt_or_eq_of_le hlength with hlt | heq
  · exfalso
    have hget := hprefix.getElem (i := shorter) (by simp)
    rw [List.getElem_append_right (as := List.replicate shorter false) (bs := [true])
      (i := shorter) (by simp), List.getElem_append_left (as := List.replicate longer false)
      (bs := [true]) (by simpa using hlt)] at hget
    simp at hget
  · rw [heq]

/-- Every stream containing a `true` bit lies in the cylinder of a waiting word: its prefix
up to and including its first `true` bit. -/
theorem exists_waitingWord_cylinder {stream : ℕ → Bool}
    (htrue : ∃ index, stream index = true) :
    ∃ word ∈ waitingWords, stream ∈ cylinder word := by
  refine ⟨List.replicate (Nat.find htrue) false ++ [true], ⟨Nat.find htrue, rfl⟩, ?_⟩
  simp only [cylinder, Set.mem_pi, Finset.coe_range, Set.mem_Iio, Set.mem_singleton_iff,
    List.length_append, List.length_replicate, List.length_singleton]
  intro index hindex
  rcases Nat.lt_succ_iff_lt_or_eq.mp hindex with hbefore | hat
  · have hfalse : stream index = false :=
      Bool.eq_false_iff.mpr (Nat.find_min htrue hbefore)
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left, List.getElem?_replicate,
      hbefore, hfalse]
  · have htrueAt : stream (Nat.find htrue) = true := Nat.find_spec htrue
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_right, hat, htrueAt]

/-- The program that waits for a `true` bit halts almost surely: its halting cylinders cover
every stream containing a `true` bit, and the remaining all-`false` stream is null. -/
theorem waitingWords_halts_ae : bitMeasure (⋃ word ∈ waitingWords, cylinder word) = 1 := by
  have hmeasurable : MeasurableSet (⋃ word ∈ waitingWords, cylinder word) :=
    MeasurableSet.biUnion (Set.to_countable _) fun word _ ↦ measurableSet_cylinder word
  refine (prob_compl_eq_zero_iff hmeasurable).mp
    (measure_mono_null ?_ (ae_iff.mp ae_exists_true))
  intro stream hstream
  simp only [Set.mem_compl_iff, Set.mem_iUnion, not_exists] at hstream
  simp only [Set.mem_setOf_eq]
  intro htrue
  obtain ⟨word, hword, hmem⟩ := exists_waitingWord_cylinder htrue
  exact hstream word hword hmem

/-- NOTE2 (32), inhabited with no hypothesis: the program that reads fair bits until the first
`true` and reports how many `false` bits it read. It halts almost surely and not surely,
because the all-`false` stream never halts, and its report law is the geometric law. -/
def waitForTrue : HaltingProgram ℕ where
  halting := waitingWords
  report := fun word ↦ word.length - 1
  prefixFree := waitingWords_prefixFree
  halts_ae := waitingWords_halts_ae

end

end Descent.Portability.CylinderHaltingLaw
