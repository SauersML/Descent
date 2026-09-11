/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.IntervalEvaluatorCertificate
import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.Distributions.Uniform
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Data.Set.Finite.List

assert_below Descent.Decision Descent.Program

/-!
# Cylinder interval evaluators on fair-bit streams

NOTE2 §7.2 represents a continuous primitive by a stream of fair random bits and certifies a
bounded integrand by finite cylinder partitions carrying rational lower and upper values.
Theorem 5 says that the cylinder sums of those values are nested valid bounds on the exact
expectation and converge to it when the interval width tends to zero almost surely. This
module builds the cylinder structure and proves Theorem 5 on it, together with the
partial-metric form in which definedness and the zero-extended numerator are evaluated
together.

The probability space is `bitMeasure`, Mathlib's infinite product `Measure.infinitePi` of the
uniform law on `Bool`. The cylinder of a word is the set of streams whose first bits spell
it, and `bitMeasure_cylinder` shows that its mass is two to the minus its length. The words
of one length index a partition of the streams, and `integral_prefix` shows that a function
of the first bits integrates to the finite sum of cylinder masses times its values.

A `CylinderEvaluator` carries a monotone depth, rational lower and upper values on the words
of each depth that bound the integrand on every continuation, the nesting of those values
under refinement, and the almost sure vanishing of the width along a stream. Nothing else is
assumed: the boundedness of the evaluations is read off the finitely many stage-zero values,
and the measurability of the integrand comes from the almost sure limit.
`lowerSum_le_integral`, `integral_le_upperSum`, `lowerSum_le_succ` and `upperSum_succ_le` are
the nested validity of Theorem 5, and `tendsto_lowerSum` and `tendsto_upperSum` its
convergence, which is bounded convergence under the almost sure hypothesis rather than a
pointwise one. The witness `hasTrueBitEvaluator` needs that generality: it certifies the
halting indicator of the program that waits for a `true` bit, whose width stays one on the
all-`false` stream and is eventually zero on every other, and `ae_exists_true` shows that the
exceptional stream is null.

For a partial metric the numerator and its complement, zero-extended off the definedness
event, are lower-evaluated and the definedness indicator is upper-evaluated.
`conditionalMean_mem_coupledBracket` is NOTE2 (18) at every stage: with `L` the numerator
certificate, `H` the sum of the two lower certificates and `τ` the definedness upper
certificate minus `H`, the conditional mean lies between `L / (H + τ)` and
`(L + τ) / (H + τ)`, and `tendsto_coupledBracket` shows that both ends converge to it. When
the widths vanish on every stream, `toIntervalEvaluator` turns a cylinder evaluator into the
corpus `IntervalEvaluatorCertificate.IntervalEvaluator` with the same stage integrals.

Not formalized here: that the rational values are produced by an algorithm, which the
structure records only as data; representations of Gaussian or exponential primitives by bit
streams; the resolution of threshold boundaries and atoms; and the remark that atomic
discretizations of continuous reports do not converge in total variation.

## Empirical status

None. The bodies here are measure theory and algebra: the evaluator is a supplied object, and
every conclusion follows from the product measure of cylinders, monotone limits and dominated
convergence, so no measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.CylinderIntervalCertificate

open MeasureTheory Filter

open scoped ENNReal Topology

noncomputable section

/-! ### Fair-bit streams and their cylinders -/

/-- A fair bit: the uniform law on `Bool`, giving each value mass one half. -/
def fairBit : Measure Bool :=
  (PMF.uniformOfFintype Bool).toMeasure

/-- The fair bit is a probability law. -/
instance isProbabilityMeasure_fairBit : IsProbabilityMeasure fairBit :=
  inferInstanceAs (IsProbabilityMeasure (PMF.uniformOfFintype Bool).toMeasure)

/-- The law of an infinite stream of independent fair bits. -/
def bitMeasure : Measure (ℕ → Bool) :=
  Measure.infinitePi fun _ : ℕ ↦ fairBit

/-- The fair-bit stream law is a probability law. -/
instance isProbabilityMeasure_bitMeasure : IsProbabilityMeasure bitMeasure :=
  inferInstanceAs (IsProbabilityMeasure (Measure.infinitePi fun _ : ℕ ↦ fairBit))

/-- A fair bit takes each value with mass one half. -/
theorem fairBit_singleton (bit : Bool) : fairBit {bit} = 2⁻¹ := by
  have hmass := PMF.toMeasure_apply_singleton (PMF.uniformOfFintype Bool) bit
    (measurableSet_singleton bit)
  rw [PMF.uniformOfFintype_apply, Fintype.card_bool] at hmass
  simp only [fairBit, hmass, Nat.cast_ofNat]

/-- The first `length` bits of a stream, read as a word. -/
def prefixOf (stream : ℕ → Bool) (length : ℕ) : List Bool :=
  (List.range length).map stream

/-- The prefix of a given length has that length. -/
theorem length_prefixOf (stream : ℕ → Bool) (length : ℕ) :
    (prefixOf stream length).length = length := by
  rw [prefixOf, List.length_map, List.length_range]

/-- A bit inside a prefix is the corresponding bit of the stream. -/
theorem getD_prefixOf (stream : ℕ → Bool) {length index : ℕ} (hindex : index < length) :
    (prefixOf stream length).getD index false = stream index := by
  simp [prefixOf, List.getD_eq_getElem?_getD, hindex]

/-- A shorter prefix is the truncation of a longer one. -/
theorem take_prefixOf (stream : ℕ → Bool) {shorter longer : ℕ} (hle : shorter ≤ longer) :
    (prefixOf stream longer).take shorter = prefixOf stream shorter := by
  simp only [prefixOf]
  rw [← List.map_take, List.take_range, min_eq_left hle]

/-- The cylinder of a word: the streams whose first bits spell the word. -/
def cylinder (word : List Bool) : Set (ℕ → Bool) :=
  Set.pi (Finset.range word.length : Set ℕ) fun index ↦ {word.getD index false}

/-- Cylinders are measurable events. -/
theorem measurableSet_cylinder (word : List Bool) : MeasurableSet (cylinder word) :=
  MeasurableSet.pi (Finset.countable_toSet _) fun _ _ ↦ measurableSet_singleton _

/-- A stream lies in the cylinder of a word exactly when the word is its prefix. -/
theorem mem_cylinder_iff (word : List Bool) (stream : ℕ → Bool) :
    stream ∈ cylinder word ↔ prefixOf stream word.length = word := by
  simp only [cylinder, Set.mem_pi, Finset.coe_range, Set.mem_Iio, Set.mem_singleton_iff]
  constructor
  · intro hbits
    refine List.ext_getElem (length_prefixOf stream word.length) fun index _ hindex ↦ ?_
    simp only [prefixOf, List.getElem_map, List.getElem_range]
    rw [hbits index hindex, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hindex,
      Option.getD_some]
  · intro hprefix index hindex
    rw [← getD_prefixOf stream hindex, hprefix]

/-- Every stream lies in the cylinder of its own prefix. -/
theorem mem_cylinder_prefixOf (stream : ℕ → Bool) (length : ℕ) :
    stream ∈ cylinder (prefixOf stream length) := by
  rw [mem_cylinder_iff, length_prefixOf]

/-- The cylinders of the words of one length partition the streams: a stream lies in the
cylinder of such a word exactly when the word is its prefix of that length. -/
theorem mem_cylinder_iff_prefixOf_eq {length : ℕ} {word : List Bool}
    (hword : word.length = length) (stream : ℕ → Bool) :
    stream ∈ cylinder word ↔ prefixOf stream length = word := by
  rw [mem_cylinder_iff, hword]

/-- Deepening the partition refines it: the cylinder of a longer prefix of a stream lies
inside the cylinder of a shorter one. -/
theorem cylinder_prefixOf_subset (stream : ℕ → Bool) {shorter longer : ℕ}
    (hle : shorter ≤ longer) :
    cylinder (prefixOf stream longer) ⊆ cylinder (prefixOf stream shorter) := by
  intro other hother
  rw [mem_cylinder_iff, length_prefixOf] at hother ⊢
  rw [← take_prefixOf other hle, hother, take_prefixOf stream hle]

/-- NOTE2 §7.2: the cylinder of a word has mass two to the minus its length. -/
theorem bitMeasure_cylinder (word : List Bool) :
    bitMeasure (cylinder word) = 2⁻¹ ^ word.length := by
  rw [bitMeasure, cylinder, Measure.infinitePi_pi (fun _ : ℕ ↦ fairBit)
    (s := Finset.range word.length) (t := fun index ↦ {word.getD index false})
    fun _ _ ↦ measurableSet_singleton _]
  simp only [fairBit_singleton, Finset.prod_const, Finset.card_range]

/-- The cylinder mass of a word as a real number. -/
theorem bitMeasure_real_cylinder (word : List Bool) :
    bitMeasure.real (cylinder word) = (1 / 2 : ℝ) ^ word.length := by
  rw [measureReal_def, bitMeasure_cylinder]
  simp

/-- The words of a given length: the index set of the cylinder partition at that depth. -/
def wordsOfLength (length : ℕ) : Finset (List Bool) :=
  (List.finite_length_eq Bool length).toFinset

/-- A word indexes the partition at a depth exactly when it has that length. -/
theorem mem_wordsOfLength {length : ℕ} {word : List Bool} :
    word ∈ wordsOfLength length ↔ word.length = length := by
  rw [wordsOfLength, Set.Finite.mem_toFinset, Set.mem_setOf_eq]

/-- A function of the first `length` bits is the sum, over the cylinders of that depth, of
its value on each cylinder times the indicator of the cylinder. -/
theorem prefix_eq_sum_indicator (length : ℕ) (value : List Bool → ℝ) (stream : ℕ → Bool) :
    value (prefixOf stream length) =
      ∑ word ∈ wordsOfLength length,
        (cylinder word).indicator (fun _ ↦ value word) stream := by
  rw [Finset.sum_eq_single (prefixOf stream length)]
  · rw [Set.indicator_of_mem (mem_cylinder_prefixOf stream length)]
  · intro word hword hne
    refine Set.indicator_of_notMem (fun hmem ↦ hne ?_) _
    exact ((mem_cylinder_iff_prefixOf_eq (mem_wordsOfLength.mp hword) stream).mp hmem).symm
  · intro hnot
    exact absurd (mem_wordsOfLength.mpr (length_prefixOf stream length)) hnot

/-- Every function of finitely many bits is measurable. -/
theorem measurable_prefix (length : ℕ) (value : List Bool → ℝ) :
    Measurable fun stream : ℕ → Bool ↦ value (prefixOf stream length) := by
  simp only [prefix_eq_sum_indicator length value]
  exact Finset.measurable_sum _ fun word _ ↦
    measurable_const.indicator (measurableSet_cylinder word)

/-- NOTE2 §7.2: a function of the first `length` bits integrates against the fair-bit stream
to the sum over the cylinders of that depth of their mass times its value on them. -/
theorem integral_prefix (length : ℕ) (value : List Bool → ℝ) :
    ∫ stream, value (prefixOf stream length) ∂bitMeasure =
      ∑ word ∈ wordsOfLength length, (1 / 2 : ℝ) ^ length * value word := by
  simp only [prefix_eq_sum_indicator length value]
  rw [integral_finset_sum _ fun word _ ↦
    (integrable_const (value word)).indicator (measurableSet_cylinder word)]
  refine Finset.sum_congr rfl fun word hword ↦ ?_
  rw [integral_indicator_const _ (measurableSet_cylinder word), bitMeasure_real_cylinder,
    mem_wordsOfLength.mp hword, smul_eq_mul]

/-! ### Theorem 5 on cylinder partitions -/

/-- NOTE2 Theorem 5: a certified cylinder interval evaluator for an integrand on fair-bit
streams. At stage `stage` the streams are partitioned into the cylinders of the words of
length `depth stage`, and the partitions refine as the stage grows. Each such word carries a
rational lower and upper value that bound the integrand on every continuation of the word,
the values are nested under refinement, and the width along a stream tends to zero almost
surely. -/
structure CylinderEvaluator (integrand : (ℕ → Bool) → ℝ) where
  depth : ℕ → ℕ
  lower : ℕ → List Bool → ℚ
  upper : ℕ → List Bool → ℚ
  depth_mono : Monotone depth
  lower_le : ∀ stage word, word.length = depth stage →
    ∀ stream ∈ cylinder word, (lower stage word : ℝ) ≤ integrand stream
  le_upper : ∀ stage word, word.length = depth stage →
    ∀ stream ∈ cylinder word, integrand stream ≤ upper stage word
  lower_nested : ∀ stage word, word.length = depth (stage + 1) →
    lower stage (word.take (depth stage)) ≤ lower (stage + 1) word
  upper_nested : ∀ stage word, word.length = depth (stage + 1) →
    upper (stage + 1) word ≤ upper stage (word.take (depth stage))
  width_ae : ∀ᵐ stream ∂bitMeasure, Tendsto (fun stage ↦
    (upper stage (prefixOf stream (depth stage)) : ℝ) -
      lower stage (prefixOf stream (depth stage))) atTop (𝓝 0)

namespace CylinderEvaluator

variable {integrand : (ℕ → Bool) → ℝ}

/-- The lower evaluation along a stream: the lower value of its cylinder at the stage. -/
def lowerEvaluation (evaluator : CylinderEvaluator integrand) (stage : ℕ)
    (stream : ℕ → Bool) : ℝ :=
  evaluator.lower stage (prefixOf stream (evaluator.depth stage))

/-- The upper evaluation along a stream: the upper value of its cylinder at the stage. -/
def upperEvaluation (evaluator : CylinderEvaluator integrand) (stage : ℕ)
    (stream : ℕ → Bool) : ℝ :=
  evaluator.upper stage (prefixOf stream (evaluator.depth stage))

/-- NOTE2 Theorem 5: the rational lower certificate at a stage, the sum over the cylinders of
the partition of their mass times their lower value. -/
def lowerSum (evaluator : CylinderEvaluator integrand) (stage : ℕ) : ℚ :=
  ∑ word ∈ wordsOfLength (evaluator.depth stage),
    (1 / 2 : ℚ) ^ evaluator.depth stage * evaluator.lower stage word

/-- NOTE2 Theorem 5: the rational upper certificate at a stage, the sum over the cylinders of
the partition of their mass times their upper value. -/
def upperSum (evaluator : CylinderEvaluator integrand) (stage : ℕ) : ℚ :=
  ∑ word ∈ wordsOfLength (evaluator.depth stage),
    (1 / 2 : ℚ) ^ evaluator.depth stage * evaluator.upper stage word

/-- A bound on every evaluation at every stage, read off the finitely many stage-zero
values. -/
def stageZeroBound (evaluator : CylinderEvaluator integrand) : ℝ :=
  ∑ word ∈ wordsOfLength (evaluator.depth 0),
    (|(evaluator.lower 0 word : ℝ)| + |(evaluator.upper 0 word : ℝ)|)

/-- The lower evaluation bounds the integrand from below along every stream, because every
stream continues the word of its own cylinder. -/
theorem lowerEvaluation_le (evaluator : CylinderEvaluator integrand) (stage : ℕ)
    (stream : ℕ → Bool) : evaluator.lowerEvaluation stage stream ≤ integrand stream :=
  evaluator.lower_le stage _ (length_prefixOf stream _) stream (mem_cylinder_prefixOf stream _)

/-- The upper evaluation bounds the integrand from above along every stream. -/
theorem le_upperEvaluation (evaluator : CylinderEvaluator integrand) (stage : ℕ)
    (stream : ℕ → Bool) : integrand stream ≤ evaluator.upperEvaluation stage stream :=
  evaluator.le_upper stage _ (length_prefixOf stream _) stream (mem_cylinder_prefixOf stream _)

/-- Along every stream the lower evaluations increase with the stage, because the cylinder of
the next stage refines the current one. -/
theorem lowerEvaluation_le_succ (evaluator : CylinderEvaluator integrand) (stage : ℕ)
    (stream : ℕ → Bool) :
    evaluator.lowerEvaluation stage stream ≤ evaluator.lowerEvaluation (stage + 1) stream := by
  have hnested := evaluator.lower_nested stage (prefixOf stream (evaluator.depth (stage + 1)))
    (length_prefixOf stream _)
  rw [take_prefixOf stream (evaluator.depth_mono (Nat.le_succ stage))] at hnested
  unfold lowerEvaluation
  exact_mod_cast hnested

/-- Along every stream the upper evaluations decrease with the stage. -/
theorem upperEvaluation_succ_le (evaluator : CylinderEvaluator integrand) (stage : ℕ)
    (stream : ℕ → Bool) :
    evaluator.upperEvaluation (stage + 1) stream ≤ evaluator.upperEvaluation stage stream := by
  have hnested := evaluator.upper_nested stage (prefixOf stream (evaluator.depth (stage + 1)))
    (length_prefixOf stream _)
  rw [take_prefixOf stream (evaluator.depth_mono (Nat.le_succ stage))] at hnested
  unfold upperEvaluation
  exact_mod_cast hnested

/-- The lower evaluations along a stream form a nondecreasing sequence. -/
theorem monotone_lowerEvaluation (evaluator : CylinderEvaluator integrand)
    (stream : ℕ → Bool) : Monotone fun stage ↦ evaluator.lowerEvaluation stage stream :=
  monotone_nat_of_le_succ fun stage ↦ evaluator.lowerEvaluation_le_succ stage stream

/-- The upper evaluations along a stream form a nonincreasing sequence. -/
theorem antitone_upperEvaluation (evaluator : CylinderEvaluator integrand)
    (stream : ℕ → Bool) : Antitone fun stage ↦ evaluator.upperEvaluation stage stream :=
  antitone_nat_of_succ_le fun stage ↦ evaluator.upperEvaluation_succ_le stage stream

/-- Every evaluation is bounded by the stage-zero bound: nesting traps it between the
stage-zero values of the cylinder of the stream. -/
theorem abs_evaluations_le (evaluator : CylinderEvaluator integrand) (stage : ℕ)
    (stream : ℕ → Bool) :
    |evaluator.lowerEvaluation stage stream| ≤ evaluator.stageZeroBound ∧
      |evaluator.upperEvaluation stage stream| ≤ evaluator.stageZeroBound := by
  have hlower : evaluator.lowerEvaluation 0 stream ≤ evaluator.lowerEvaluation stage stream :=
    evaluator.monotone_lowerEvaluation stream (Nat.zero_le stage)
  have hupper : evaluator.upperEvaluation stage stream ≤ evaluator.upperEvaluation 0 stream :=
    evaluator.antitone_upperEvaluation stream (Nat.zero_le stage)
  have hbelow := evaluator.lowerEvaluation_le stage stream
  have habove := evaluator.le_upperEvaluation stage stream
  have hcell : |evaluator.lowerEvaluation 0 stream| + |evaluator.upperEvaluation 0 stream| ≤
      evaluator.stageZeroBound :=
    Finset.single_le_sum
      (f := fun word ↦ |(evaluator.lower 0 word : ℝ)| + |(evaluator.upper 0 word : ℝ)|)
      (fun _ _ ↦ add_nonneg (abs_nonneg _) (abs_nonneg _))
      (mem_wordsOfLength.mpr (length_prefixOf stream _))
  have hlowZero := neg_abs_le (evaluator.lowerEvaluation 0 stream)
  have hhighZero := le_abs_self (evaluator.upperEvaluation 0 stream)
  have hlowAbs := abs_nonneg (evaluator.lowerEvaluation 0 stream)
  have hhighAbs := abs_nonneg (evaluator.upperEvaluation 0 stream)
  constructor <;> rw [abs_le] <;> constructor <;> linarith

/-- Almost every stream sees both evaluations converge to the integrand: the width vanishes
almost surely and squeezes them onto it. -/
theorem tendsto_evaluations_ae (evaluator : CylinderEvaluator integrand) :
    ∀ᵐ stream ∂bitMeasure,
      Tendsto (fun stage ↦ evaluator.lowerEvaluation stage stream) atTop
          (𝓝 (integrand stream)) ∧
        Tendsto (fun stage ↦ evaluator.upperEvaluation stage stream) atTop
          (𝓝 (integrand stream)) := by
  filter_upwards [evaluator.width_ae] with stream hwidth
  have hconst : Tendsto (fun _ : ℕ ↦ integrand stream) atTop (𝓝 (integrand stream)) :=
    tendsto_const_nhds
  have hgap : Tendsto (fun stage ↦ evaluator.upperEvaluation stage stream -
      evaluator.lowerEvaluation stage stream) atTop (𝓝 0) := hwidth
  have hbelow := hconst.sub hgap
  have habove := hconst.add hgap
  rw [sub_zero] at hbelow
  rw [add_zero] at habove
  constructor
  · refine tendsto_of_tendsto_of_tendsto_of_le_of_le hbelow hconst (fun stage ↦ ?_)
      fun stage ↦ evaluator.lowerEvaluation_le stage stream
    have hup := evaluator.le_upperEvaluation stage stream
    show integrand stream - (evaluator.upperEvaluation stage stream -
      evaluator.lowerEvaluation stage stream) ≤ evaluator.lowerEvaluation stage stream
    linarith
  · refine tendsto_of_tendsto_of_tendsto_of_le_of_le hconst habove
      (fun stage ↦ evaluator.le_upperEvaluation stage stream) fun stage ↦ ?_
    have hlow := evaluator.lowerEvaluation_le stage stream
    show evaluator.upperEvaluation stage stream ≤ integrand stream +
      (evaluator.upperEvaluation stage stream - evaluator.lowerEvaluation stage stream)
    linarith

/-- Every lower evaluation is integrable: it is measurable and bounded. -/
theorem integrable_lowerEvaluation (evaluator : CylinderEvaluator integrand) (stage : ℕ) :
    Integrable (evaluator.lowerEvaluation stage) bitMeasure :=
  IntervalEvaluatorCertificate.integrable_of_abs_le_const bitMeasure
    (measurable_prefix (evaluator.depth stage) fun word ↦ (evaluator.lower stage word : ℝ))
    evaluator.stageZeroBound fun stream ↦ (evaluator.abs_evaluations_le stage stream).1

/-- Every upper evaluation is integrable: it is measurable and bounded. -/
theorem integrable_upperEvaluation (evaluator : CylinderEvaluator integrand) (stage : ℕ) :
    Integrable (evaluator.upperEvaluation stage) bitMeasure :=
  IntervalEvaluatorCertificate.integrable_of_abs_le_const bitMeasure
    (measurable_prefix (evaluator.depth stage) fun word ↦ (evaluator.upper stage word : ℝ))
    evaluator.stageZeroBound fun stream ↦ (evaluator.abs_evaluations_le stage stream).2

/-- The integrand is integrable: it is an almost sure limit of measurable evaluations and is
trapped between bounded ones. -/
theorem integrable_integrand (evaluator : CylinderEvaluator integrand) :
    Integrable integrand bitMeasure := by
  have hmeasurable : AEStronglyMeasurable integrand bitMeasure :=
    aestronglyMeasurable_of_tendsto_ae atTop
      (fun stage ↦ (evaluator.integrable_lowerEvaluation stage).aestronglyMeasurable)
      (evaluator.tendsto_evaluations_ae.mono fun _ hstream ↦ hstream.1)
  refine Integrable.of_bound hmeasurable evaluator.stageZeroBound (ae_of_all _ fun stream ↦ ?_)
  obtain ⟨hlowBelow, hlowAbove⟩ := abs_le.mp (evaluator.abs_evaluations_le 0 stream).1
  obtain ⟨hhighBelow, hhighAbove⟩ := abs_le.mp (evaluator.abs_evaluations_le 0 stream).2
  have hbelow := evaluator.lowerEvaluation_le 0 stream
  have habove := evaluator.le_upperEvaluation 0 stream
  rw [Real.norm_eq_abs, abs_le]
  constructor <;> linarith

/-- NOTE2 Theorem 5: the stage integrals of the lower evaluations converge to the exact
expectation, by bounded convergence under the almost sure width hypothesis. -/
theorem tendsto_integral_lowerEvaluation (evaluator : CylinderEvaluator integrand) :
    Tendsto (fun stage ↦ ∫ stream, evaluator.lowerEvaluation stage stream ∂bitMeasure) atTop
      (𝓝 (∫ stream, integrand stream ∂bitMeasure)) :=
  tendsto_integral_of_dominated_convergence (fun _ ↦ evaluator.stageZeroBound)
    (fun stage ↦ (evaluator.integrable_lowerEvaluation stage).aestronglyMeasurable)
    (integrable_const _)
    (fun stage ↦ ae_of_all _ fun stream ↦ by
      rw [Real.norm_eq_abs]
      exact (evaluator.abs_evaluations_le stage stream).1)
    (evaluator.tendsto_evaluations_ae.mono fun _ hstream ↦ hstream.1)

/-- NOTE2 Theorem 5: the stage integrals of the upper evaluations converge to the exact
expectation. -/
theorem tendsto_integral_upperEvaluation (evaluator : CylinderEvaluator integrand) :
    Tendsto (fun stage ↦ ∫ stream, evaluator.upperEvaluation stage stream ∂bitMeasure) atTop
      (𝓝 (∫ stream, integrand stream ∂bitMeasure)) :=
  tendsto_integral_of_dominated_convergence (fun _ ↦ evaluator.stageZeroBound)
    (fun stage ↦ (evaluator.integrable_upperEvaluation stage).aestronglyMeasurable)
    (integrable_const _)
    (fun stage ↦ ae_of_all _ fun stream ↦ by
      rw [Real.norm_eq_abs]
      exact (evaluator.abs_evaluations_le stage stream).2)
    (evaluator.tendsto_evaluations_ae.mono fun _ hstream ↦ hstream.2)

/-- NOTE2 Theorem 5: the rational lower certificate is the stage integral of the lower
evaluation. -/
theorem lowerSum_cast (evaluator : CylinderEvaluator integrand) (stage : ℕ) :
    (evaluator.lowerSum stage : ℝ) =
      ∫ stream, evaluator.lowerEvaluation stage stream ∂bitMeasure := by
  rw [lowerSum]
  push_cast
  exact (integral_prefix (evaluator.depth stage)
    fun word ↦ (evaluator.lower stage word : ℝ)).symm

/-- NOTE2 Theorem 5: the rational upper certificate is the stage integral of the upper
evaluation. -/
theorem upperSum_cast (evaluator : CylinderEvaluator integrand) (stage : ℕ) :
    (evaluator.upperSum stage : ℝ) =
      ∫ stream, evaluator.upperEvaluation stage stream ∂bitMeasure := by
  rw [upperSum]
  push_cast
  exact (integral_prefix (evaluator.depth stage)
    fun word ↦ (evaluator.upper stage word : ℝ)).symm

/-- NOTE2 Theorem 5, nesting: the rational lower certificates increase with the stage. -/
theorem lowerSum_le_succ (evaluator : CylinderEvaluator integrand) (stage : ℕ) :
    evaluator.lowerSum stage ≤ evaluator.lowerSum (stage + 1) := by
  have hreal : (evaluator.lowerSum stage : ℝ) ≤ evaluator.lowerSum (stage + 1) := by
    rw [evaluator.lowerSum_cast, evaluator.lowerSum_cast]
    exact integral_mono (evaluator.integrable_lowerEvaluation stage)
      (evaluator.integrable_lowerEvaluation (stage + 1))
      fun stream ↦ evaluator.lowerEvaluation_le_succ stage stream
  exact_mod_cast hreal

/-- NOTE2 Theorem 5, nesting: the rational upper certificates decrease with the stage. -/
theorem upperSum_succ_le (evaluator : CylinderEvaluator integrand) (stage : ℕ) :
    evaluator.upperSum (stage + 1) ≤ evaluator.upperSum stage := by
  have hreal : (evaluator.upperSum (stage + 1) : ℝ) ≤ evaluator.upperSum stage := by
    rw [evaluator.upperSum_cast, evaluator.upperSum_cast]
    exact integral_mono (evaluator.integrable_upperEvaluation (stage + 1))
      (evaluator.integrable_upperEvaluation stage)
      fun stream ↦ evaluator.upperEvaluation_succ_le stage stream
  exact_mod_cast hreal

/-- The real lower certificates form a nondecreasing sequence. -/
theorem monotone_lowerSum (evaluator : CylinderEvaluator integrand) :
    Monotone fun stage ↦ (evaluator.lowerSum stage : ℝ) :=
  monotone_nat_of_le_succ fun stage ↦ by exact_mod_cast evaluator.lowerSum_le_succ stage

/-- The real upper certificates form a nonincreasing sequence. -/
theorem antitone_upperSum (evaluator : CylinderEvaluator integrand) :
    Antitone fun stage ↦ (evaluator.upperSum stage : ℝ) :=
  antitone_nat_of_succ_le fun stage ↦ by exact_mod_cast evaluator.upperSum_succ_le stage

/-- NOTE2 Theorem 5, convergence: the rational lower certificates converge to the exact
expectation. -/
theorem tendsto_lowerSum (evaluator : CylinderEvaluator integrand) :
    Tendsto (fun stage ↦ (evaluator.lowerSum stage : ℝ)) atTop
      (𝓝 (∫ stream, integrand stream ∂bitMeasure)) := by
  simpa only [evaluator.lowerSum_cast] using evaluator.tendsto_integral_lowerEvaluation

/-- NOTE2 Theorem 5, convergence: the rational upper certificates converge to the exact
expectation. -/
theorem tendsto_upperSum (evaluator : CylinderEvaluator integrand) :
    Tendsto (fun stage ↦ (evaluator.upperSum stage : ℝ)) atTop
      (𝓝 (∫ stream, integrand stream ∂bitMeasure)) := by
  simpa only [evaluator.upperSum_cast] using evaluator.tendsto_integral_upperEvaluation

/-- NOTE2 Theorem 5, validity: every rational lower certificate is a lower bound on the exact
expectation. -/
theorem lowerSum_le_integral (evaluator : CylinderEvaluator integrand) (stage : ℕ) :
    (evaluator.lowerSum stage : ℝ) ≤ ∫ stream, integrand stream ∂bitMeasure :=
  evaluator.monotone_lowerSum.ge_of_tendsto evaluator.tendsto_lowerSum stage

/-- NOTE2 Theorem 5, validity: every rational upper certificate is an upper bound on the exact
expectation. -/
theorem integral_le_upperSum (evaluator : CylinderEvaluator integrand) (stage : ℕ) :
    ∫ stream, integrand stream ∂bitMeasure ≤ (evaluator.upperSum stage : ℝ) :=
  evaluator.antitone_upperSum.le_of_tendsto evaluator.tendsto_upperSum stage

/-- NOTE2 Theorem 5: the width of the rational certificate tends to zero. -/
theorem tendsto_upperSum_sub_lowerSum (evaluator : CylinderEvaluator integrand) :
    Tendsto (fun stage ↦ ((evaluator.upperSum stage - evaluator.lowerSum stage : ℚ) : ℝ))
      atTop (𝓝 0) := by
  have hgap := evaluator.tendsto_upperSum.sub evaluator.tendsto_lowerSum
  rw [sub_self] at hgap
  simpa only [Rat.cast_sub] using hgap

/-- A cylinder evaluator whose widths vanish on every stream, for a measurable integrand, is
an interval evaluator of the corpus with the stage-zero bound as its common bound. -/
def toIntervalEvaluator (evaluator : CylinderEvaluator integrand)
    (hmeasurable : Measurable integrand)
    (hwidth : ∀ stream, Tendsto (fun stage ↦
      evaluator.upperEvaluation stage stream - evaluator.lowerEvaluation stage stream) atTop
        (𝓝 0)) :
    IntervalEvaluatorCertificate.IntervalEvaluator integrand evaluator.stageZeroBound where
  lower := evaluator.lowerEvaluation
  upper := evaluator.upperEvaluation
  integrand_measurable := hmeasurable
  lower_measurable := fun stage ↦
    measurable_prefix (evaluator.depth stage) fun word ↦ (evaluator.lower stage word : ℝ)
  upper_measurable := fun stage ↦
    measurable_prefix (evaluator.depth stage) fun word ↦ (evaluator.upper stage word : ℝ)
  lower_le := evaluator.lowerEvaluation_le
  le_upper := evaluator.le_upperEvaluation
  lower_abs_le := fun stage stream ↦ (evaluator.abs_evaluations_le stage stream).1
  upper_abs_le := fun stage stream ↦ (evaluator.abs_evaluations_le stage stream).2
  width_tendsto := hwidth

/-- The stage integrals of the corpus interval evaluator built from a cylinder evaluator are
the rational cylinder certificates. -/
theorem integral_toIntervalEvaluator_lower (evaluator : CylinderEvaluator integrand)
    (hmeasurable : Measurable integrand)
    (hwidth : ∀ stream, Tendsto (fun stage ↦
      evaluator.upperEvaluation stage stream - evaluator.lowerEvaluation stage stream) atTop
        (𝓝 0)) (stage : ℕ) :
    ∫ stream, (evaluator.toIntervalEvaluator hmeasurable hwidth :
        IntervalEvaluatorCertificate.IntervalEvaluator integrand evaluator.stageZeroBound).lower
          stage stream ∂bitMeasure =
      (evaluator.lowerSum stage : ℝ) :=
  (evaluator.lowerSum_cast stage).symm

end CylinderEvaluator

/-! ### A hypothesis-free evaluator whose width vanishes only almost surely -/

/-- Almost every fair-bit stream contains a `true` bit: the streams without one lie in the
cylinder of the all-`false` word of every length, whose mass two to the minus that length
tends to zero. -/
theorem ae_exists_true : ∀ᵐ stream ∂bitMeasure, ∃ index, stream index = true := by
  rw [ae_iff]
  have hbound : ∀ length : ℕ,
      bitMeasure {stream : ℕ → Bool | ¬∃ index, stream index = true} ≤ 2⁻¹ ^ length := by
    intro length
    calc bitMeasure {stream : ℕ → Bool | ¬∃ index, stream index = true}
        ≤ bitMeasure (cylinder (List.replicate length false)) := by
          refine measure_mono fun stream hstream ↦ ?_
          simp only [Set.mem_setOf_eq, not_exists, Bool.not_eq_true] at hstream
          simp only [cylinder, Set.mem_pi, Finset.coe_range, Set.mem_Iio,
            Set.mem_singleton_iff, List.length_replicate]
          intro index hindex
          simp [hstream index, List.getD_eq_getElem?_getD, hindex]
      _ = 2⁻¹ ^ length := by rw [bitMeasure_cylinder, List.length_replicate]
  have hlimit : Tendsto (fun length : ℕ ↦ (2⁻¹ : ℝ≥0∞) ^ length) atTop (𝓝 0) :=
    ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (ENNReal.inv_lt_one.mpr ENNReal.one_lt_two)
  exact le_antisymm (ge_of_tendsto' hlimit hbound) (zero_le _)

/-- The halting indicator of the program that reads fair bits until the first `true`: one on
every stream containing a `true` bit and zero on the all-`false` stream. -/
def hasTrueBit (stream : ℕ → Bool) : ℝ := by
  classical
  exact if ∃ index, stream index = true then 1 else 0

/-- The halting indicator is one on a stream containing a `true` bit. -/
theorem hasTrueBit_eq_one {stream : ℕ → Bool} (htrue : ∃ index, stream index = true) :
    hasTrueBit stream = 1 := by
  unfold hasTrueBit
  exact if_pos htrue

/-- The halting indicator takes values in the unit interval. -/
theorem hasTrueBit_mem_unitInterval (stream : ℕ → Bool) :
    0 ≤ hasTrueBit stream ∧ hasTrueBit stream ≤ 1 := by
  unfold hasTrueBit
  split_ifs <;> norm_num

/-- A hypothesis-free cylinder evaluator whose width vanishes only almost surely. It certifies
the halting indicator of the program that waits for a `true` bit: at stage `stage` the
cylinder of a word of that length gets lower value one when the word contains a `true` bit
and zero otherwise, and upper value one. On the all-`false` stream the width stays one at
every stage, so no evaluator with pointwise vanishing widths describes this program, and on
every other stream the width is eventually zero. -/
def hasTrueBitEvaluator : CylinderEvaluator hasTrueBit where
  depth := fun stage ↦ stage
  lower := fun _ word ↦ if true ∈ word then 1 else 0
  upper := fun _ _ ↦ 1
  depth_mono := monotone_id
  lower_le := fun stage word hlength stream hstream ↦ by
    show ((if true ∈ word then 1 else 0 : ℚ) : ℝ) ≤ hasTrueBit stream
    by_cases htrue : true ∈ word
    · have hexists : ∃ index, stream index = true := by
        rw [mem_cylinder_iff_prefixOf_eq hlength, prefixOf] at hstream
        rw [← hstream, List.mem_map] at htrue
        obtain ⟨index, _, hindex⟩ := htrue
        exact ⟨index, hindex⟩
      simp only [if_pos htrue, Rat.cast_one, hasTrueBit_eq_one hexists, le_refl]
    · rw [if_neg htrue, Rat.cast_zero]
      exact (hasTrueBit_mem_unitInterval stream).1
  le_upper := fun _ _ _ stream _ ↦ by
    show hasTrueBit stream ≤ ((1 : ℚ) : ℝ)
    rw [Rat.cast_one]
    exact (hasTrueBit_mem_unitInterval stream).2
  lower_nested := fun stage word _ ↦ by
    show (if true ∈ word.take stage then (1 : ℚ) else 0) ≤ if true ∈ word then 1 else 0
    by_cases htake : true ∈ word.take stage
    · simp only [if_pos htake, if_pos (List.mem_of_mem_take htake), le_refl]
    · rw [if_neg htake]
      split_ifs <;> norm_num
  upper_nested := fun _ _ _ ↦ le_rfl
  width_ae := by
    filter_upwards [ae_exists_true] with stream hstream
    obtain ⟨index, hindex⟩ := hstream
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop index] with stage hstage
    have hmem : true ∈ prefixOf stream stage :=
      List.mem_map.mpr ⟨index, List.mem_range.mpr hstage, hindex⟩
    show (0 : ℝ) = ((1 : ℚ) : ℝ) - ((if true ∈ prefixOf stream stage then 1 else 0 : ℚ) : ℝ)
    rw [if_pos hmem]
    norm_num

/-! ### Partial metrics: the coupled definedness bracket -/

/-- The algebra of NOTE2 (18) for a partial metric. A nonnegative numerator and complement add
up to a positive definedness mass; given lower bounds on both parts and an upper bound on the
definedness mass, the ratio of numerator to definedness lies between the numerator lower bound
over the definedness upper bound and one minus the complement lower bound over it. -/
theorem coupled_ratio_bracket (numerator complement definedness numeratorLower
    complementLower definednessUpper : ℝ) (hsum : numerator + complement = definedness)
    (hnumerator : 0 ≤ numerator) (hcomplement : 0 ≤ complement)
    (hnumeratorLower : numeratorLower ≤ numerator)
    (hcomplementLower : complementLower ≤ complement)
    (hdefinednessUpper : definedness ≤ definednessUpper) (hdefined : 0 < definedness) :
    numeratorLower / definednessUpper ≤ numerator / definedness ∧
      numerator / definedness ≤ 1 - complementLower / definednessUpper := by
  have hupper : 0 < definednessUpper := lt_of_lt_of_le hdefined hdefinednessUpper
  have hcomplementRatio : complementLower / definednessUpper ≤ complement / definedness := by
    rw [div_le_div_iff₀ hupper hdefined]
    linarith [mul_le_mul_of_nonneg_right hcomplementLower hdefined.le,
      mul_le_mul_of_nonneg_left hdefinednessUpper hcomplement]
  have hsplit : numerator / definedness = 1 - complement / definedness := by
    rw [eq_sub_iff_add_eq, ← add_div, hsum, div_self hdefined.ne']
  constructor
  · rw [div_le_div_iff₀ hupper hdefined]
    linarith [mul_le_mul_of_nonneg_right hnumeratorLower hdefined.le,
      mul_le_mul_of_nonneg_left hdefinednessUpper hnumerator]
  · linarith

/-- A split of the definedness indicator into a numerator and a complement, each carrying a
cylinder evaluator, splits its expectation. -/
theorem integral_add_of_split {numerator complement definedness : (ℕ → Bool) → ℝ}
    (numeratorEvaluator : CylinderEvaluator numerator)
    (complementEvaluator : CylinderEvaluator complement)
    (hsplit : ∀ stream, numerator stream + complement stream = definedness stream) :
    (∫ stream, numerator stream ∂bitMeasure) + ∫ stream, complement stream ∂bitMeasure =
      ∫ stream, definedness stream ∂bitMeasure := by
  rw [← integral_add numeratorEvaluator.integrable_integrand
    complementEvaluator.integrable_integrand]
  simp only [hsplit]

/-- NOTE2 §7.2 for a partial metric, in the coupled form of NOTE2 (18). The zero-extended
metric numerator and its zero-extended complement are nonnegative and add up to the
definedness indicator; both are lower-evaluated on cylinders and the definedness indicator is
upper-evaluated. With `L` the numerator certificate, `H` the sum of the two lower
certificates and `τ` the definedness upper certificate minus `H`, the conditional mean of the
metric given definedness lies between `L / (H + τ)` and `(L + τ) / (H + τ)` at every stage.
Assumes: the definedness probability is positive. -/
theorem conditionalMean_mem_coupledBracket
    {numerator complement definedness : (ℕ → Bool) → ℝ}
    (numeratorEvaluator : CylinderEvaluator numerator)
    (complementEvaluator : CylinderEvaluator complement)
    (definednessEvaluator : CylinderEvaluator definedness)
    (hsplit : ∀ stream, numerator stream + complement stream = definedness stream)
    (hnumerator : ∀ stream, 0 ≤ numerator stream)
    (hcomplement : ∀ stream, 0 ≤ complement stream)
    (hdefined : 0 < ∫ stream, definedness stream ∂bitMeasure) (stage : ℕ) :
    (numeratorEvaluator.lowerSum stage : ℝ) / definednessEvaluator.upperSum stage ≤
        (∫ stream, numerator stream ∂bitMeasure) / ∫ stream, definedness stream ∂bitMeasure ∧
      (∫ stream, numerator stream ∂bitMeasure) / ∫ stream, definedness stream ∂bitMeasure ≤
        1 - (complementEvaluator.lowerSum stage : ℝ) / definednessEvaluator.upperSum stage :=
  coupled_ratio_bracket _ _ _ _ _ _
    (integral_add_of_split numeratorEvaluator complementEvaluator hsplit)
    (integral_nonneg hnumerator) (integral_nonneg hcomplement)
    (numeratorEvaluator.lowerSum_le_integral stage)
    (complementEvaluator.lowerSum_le_integral stage)
    (definednessEvaluator.integral_le_upperSum stage) hdefined

/-- NOTE2 §7.2 for a partial metric: both ends of the coupled bracket converge to the
conditional mean, because each certificate converges to its exact expectation. Assumes: the
definedness probability is positive. -/
theorem tendsto_coupledBracket {numerator complement definedness : (ℕ → Bool) → ℝ}
    (numeratorEvaluator : CylinderEvaluator numerator)
    (complementEvaluator : CylinderEvaluator complement)
    (definednessEvaluator : CylinderEvaluator definedness)
    (hsplit : ∀ stream, numerator stream + complement stream = definedness stream)
    (hdefined : 0 < ∫ stream, definedness stream ∂bitMeasure) :
    Tendsto (fun stage ↦
        (numeratorEvaluator.lowerSum stage : ℝ) / definednessEvaluator.upperSum stage) atTop
        (𝓝 ((∫ stream, numerator stream ∂bitMeasure) /
          ∫ stream, definedness stream ∂bitMeasure)) ∧
      Tendsto (fun stage ↦
          1 - (complementEvaluator.lowerSum stage : ℝ) / definednessEvaluator.upperSum stage)
        atTop (𝓝 ((∫ stream, numerator stream ∂bitMeasure) /
          ∫ stream, definedness stream ∂bitMeasure)) := by
  have hsum := integral_add_of_split numeratorEvaluator complementEvaluator hsplit
  have hconst : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  have hcomplement := hconst.sub
    (complementEvaluator.tendsto_lowerSum.div definednessEvaluator.tendsto_upperSum
      hdefined.ne')
  have hlimit : 1 - (∫ stream, complement stream ∂bitMeasure) /
      ∫ stream, definedness stream ∂bitMeasure =
      (∫ stream, numerator stream ∂bitMeasure) / ∫ stream, definedness stream ∂bitMeasure := by
    rw [sub_eq_iff_eq_add, ← add_div, hsum, div_self hdefined.ne']
  rw [hlimit] at hcomplement
  exact ⟨numeratorEvaluator.tendsto_lowerSum.div definednessEvaluator.tendsto_upperSum
    hdefined.ne', hcomplement⟩

end

end Descent.Portability.CylinderIntervalCertificate
