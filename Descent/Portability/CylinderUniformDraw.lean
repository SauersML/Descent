/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.CylinderIntervalCertificate

assert_below Descent.Decision Descent.Program

/-!
# Executed Theorem 5: the uniform draw from fair bits

NOTE2 §7.2 represents a continuous primitive by a stream of fair random bits. The canonical
primitive is the uniform draw, the binary number whose digits are the bits. This module
certifies its expectation with a cylinder interval evaluator and derives the exact value one
half from the certificate, so Theorem 5 of `CylinderIntervalCertificate` is executed on an
integrand that no finite cylinder partition resolves.

`uniformDraw` is the series of the digits `bit i / 2^(i+1)` and `truncatedDraw` its first
`stage` digits. `truncatedDraw_le_uniformDraw` and `uniformDraw_le_truncatedDraw_add` bracket
the draw between the truncation and the truncation plus two to the minus the stage.
`uniformEvaluator` is the cylinder evaluator with those brackets as rational values on words:
nested, because each new digit is at most the slack it closes, and with width two to the minus
the stage on every stream. `integral_truncatedDraw` computes the stage integral of the
truncation in closed form from the fair-bit marginals, so the rational certificates are
`lowerSum_uniformEvaluator`, `(1 - 2^(-stage)) / 2`, and `upperSum_uniformEvaluator`,
`(1 + 2^(-stage)) / 2`. `integral_uniformDraw` recovers the exact expectation one half as the
limit that Theorem 5 guarantees.

## Empirical status

None. The bodies here are algebra and measure theory: the draw is a stipulated function of the
bit stream, and every conclusion follows from geometric series and the fair-bit marginals, so
no measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.CylinderUniformDraw

open MeasureTheory Filter CylinderIntervalCertificate

open scoped ENNReal Topology

noncomputable section

/-- The binary digit contributed by one bit of a stream: two to the minus one more than its
index when the bit is true, and zero otherwise. -/
def binaryDigit (stream : ℕ → Bool) (index : ℕ) : ℝ :=
  if stream index then (1 / 2 : ℝ) ^ (index + 1) else 0

/-- Binary digits are nonnegative. -/
theorem binaryDigit_nonneg (stream : ℕ → Bool) (index : ℕ) : 0 ≤ binaryDigit stream index := by
  unfold binaryDigit
  split_ifs <;> positivity

/-- A binary digit is at most its place value. -/
theorem binaryDigit_le (stream : ℕ → Bool) (index : ℕ) :
    binaryDigit stream index ≤ (1 / 2 : ℝ) ^ (index + 1) := by
  unfold binaryDigit
  split_ifs
  · exact le_rfl
  · positivity

/-- The binary digits of a stream are summable, being dominated by the place values. -/
theorem summable_binaryDigit (stream : ℕ → Bool) : Summable (binaryDigit stream) :=
  Summable.of_nonneg_of_le (binaryDigit_nonneg stream) (binaryDigit_le stream)
    ((summable_nat_add_iff 1).mpr (summable_geometric_of_lt_one (by norm_num) (by norm_num)))

/-- The uniform draw encoded by a fair-bit stream: the binary number whose digits are its
bits. -/
def uniformDraw (stream : ℕ → Bool) : ℝ :=
  ∑' index, binaryDigit stream index

/-- The value of the first `stage` binary digits of a stream. -/
def truncatedDraw (stage : ℕ) (stream : ℕ → Bool) : ℝ :=
  ∑ index ∈ Finset.range stage, binaryDigit stream index

/-- The truncation of the draw is a lower bound on the draw. -/
theorem truncatedDraw_le_uniformDraw (stage : ℕ) (stream : ℕ → Bool) :
    truncatedDraw stage stream ≤ uniformDraw stream :=
  Summable.sum_le_tsum (Finset.range stage) (fun index _ ↦ binaryDigit_nonneg stream index)
    (summable_binaryDigit stream)

/-- The unread digits contribute at most two to the minus the stage. -/
theorem uniformDraw_le_truncatedDraw_add (stage : ℕ) (stream : ℕ → Bool) :
    uniformDraw stream ≤ truncatedDraw stage stream + (1 / 2 : ℝ) ^ stage := by
  have hsplit := (summable_binaryDigit stream).sum_add_tsum_nat_add stage
  have hgeometric : Summable fun index : ℕ ↦ (1 / 2 : ℝ) ^ stage * ((1 / 2) * (1 / 2) ^ index) :=
    ((summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left (1 / 2)).mul_left
      ((1 / 2) ^ stage)
  have htail : ∑' index, binaryDigit stream (index + stage) ≤ (1 / 2 : ℝ) ^ stage := by
    calc ∑' index, binaryDigit stream (index + stage)
        ≤ ∑' index : ℕ, (1 / 2 : ℝ) ^ stage * ((1 / 2) * (1 / 2) ^ index) :=
          Summable.tsum_le_tsum
            (fun index ↦ le_of_le_of_eq (binaryDigit_le stream (index + stage)) (by ring))
            ((summable_nat_add_iff stage).mpr (summable_binaryDigit stream)) hgeometric
      _ = (1 / 2 : ℝ) ^ stage := by
          rw [tsum_mul_left, tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
          norm_num
  unfold uniformDraw truncatedDraw
  linarith

/-- The rational value of the first `stage` binary digits spelled by a word. -/
def wordDraw (stage : ℕ) (word : List Bool) : ℚ :=
  ∑ index ∈ Finset.range stage, if word.getD index false then (1 / 2 : ℚ) ^ (index + 1) else 0

/-- The digits spelled by the prefix of a stream are the first digits of its draw. -/
theorem wordDraw_prefixOf (stage : ℕ) (stream : ℕ → Bool) :
    (wordDraw stage (prefixOf stream stage) : ℝ) = truncatedDraw stage stream := by
  unfold wordDraw truncatedDraw binaryDigit
  push_cast [apply_ite (Rat.cast : ℚ → ℝ)]
  refine Finset.sum_congr rfl fun index hindex ↦ ?_
  rw [getD_prefixOf stream (Finset.mem_range.mp hindex)]

/-- Truncating a word to the stage does not change the digits it spells up to that stage. -/
theorem wordDraw_take (stage : ℕ) (word : List Bool) :
    wordDraw stage (word.take stage) = wordDraw stage word := by
  unfold wordDraw
  refine Finset.sum_congr rfl fun index hindex ↦ ?_
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take,
    if_pos (Finset.mem_range.mp hindex)]

/-- One more stage adds the digit of the next bit. -/
theorem wordDraw_succ (stage : ℕ) (word : List Bool) :
    wordDraw (stage + 1) word =
      wordDraw stage word + if word.getD stage false then (1 / 2 : ℚ) ^ (stage + 1) else 0 := by
  unfold wordDraw
  rw [Finset.sum_range_succ]

/-- NOTE2 Theorem 5, executed: the cylinder evaluator of the uniform draw. On a word of length
`stage` its lower value is the value of the digits the word spells, and its upper value adds
two to the minus `stage`, the most the unread digits can contribute. -/
def uniformEvaluator : CylinderEvaluator uniformDraw where
  depth := fun stage ↦ stage
  lower := fun stage word ↦ wordDraw stage word
  upper := fun stage word ↦ wordDraw stage word + (1 / 2) ^ stage
  depth_mono := monotone_id
  lower_le := fun stage word hlength stream hstream ↦ by
    have hprefix := (mem_cylinder_iff_prefixOf_eq hlength stream).mp hstream
    show (wordDraw stage word : ℝ) ≤ uniformDraw stream
    rw [← hprefix, wordDraw_prefixOf]
    exact truncatedDraw_le_uniformDraw stage stream
  le_upper := fun stage word hlength stream hstream ↦ by
    have hprefix := (mem_cylinder_iff_prefixOf_eq hlength stream).mp hstream
    show uniformDraw stream ≤ ((wordDraw stage word + (1 / 2) ^ stage : ℚ) : ℝ)
    rw [← hprefix]
    push_cast
    rw [wordDraw_prefixOf]
    exact uniformDraw_le_truncatedDraw_add stage stream
  lower_nested := fun stage word _ ↦ by
    show wordDraw stage (word.take stage) ≤ wordDraw (stage + 1) word
    rw [wordDraw_take, wordDraw_succ]
    have hdigit : (0 : ℚ) ≤ if word.getD stage false then (1 / 2 : ℚ) ^ (stage + 1) else 0 := by
      split_ifs <;> positivity
    linarith
  upper_nested := fun stage word _ ↦ by
    show wordDraw (stage + 1) word + (1 / 2) ^ (stage + 1) ≤
      wordDraw stage (word.take stage) + (1 / 2) ^ stage
    rw [wordDraw_take, wordDraw_succ]
    have hdigit : (if word.getD stage false then (1 / 2 : ℚ) ^ (stage + 1) else 0) ≤
        (1 / 2) ^ (stage + 1) := by
      split_ifs
      · exact le_rfl
      · positivity
    have hhalf : (1 / 2 : ℚ) ^ (stage + 1) + (1 / 2) ^ (stage + 1) = (1 / 2) ^ stage := by ring
    linarith
  width_ae := ae_of_all _ fun stream ↦ by
    have hlimit := tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num)
      (by norm_num)
    refine hlimit.congr fun stage ↦ ?_
    push_cast
    ring

/-- The streams whose bit at an index is true form a measurable event. -/
theorem measurableSet_bit_true (index : ℕ) :
    MeasurableSet {stream : ℕ → Bool | stream index = true} :=
  measurable_pi_apply index (measurableSet_singleton true)

/-- A fair bit is true with probability one half. -/
theorem bitMeasure_real_bit_true (index : ℕ) :
    bitMeasure.real {stream : ℕ → Bool | stream index = true} = 1 / 2 := by
  have hset : {stream : ℕ → Bool | stream index = true} =
      Set.pi (({index} : Finset ℕ) : Set ℕ) fun _ ↦ {true} := by
    ext stream
    simp
  rw [measureReal_def, hset, bitMeasure, Measure.infinitePi_pi (fun _ : ℕ ↦ fairBit)
    (s := {index}) (t := fun _ ↦ {true}) fun _ _ ↦ measurableSet_singleton _]
  simp [fairBit_singleton]

/-- A binary digit is its place value on the event that its bit is true. -/
theorem binaryDigit_eq_indicator (index : ℕ) :
    (fun stream ↦ binaryDigit stream index) =
      {stream : ℕ → Bool | stream index = true}.indicator fun _ ↦ (1 / 2 : ℝ) ^ (index + 1) := by
  funext stream
  by_cases hbit : stream index = true <;> simp [binaryDigit, Set.indicator_apply, hbit]

/-- Each binary digit is integrable. -/
theorem integrable_binaryDigit (index : ℕ) :
    Integrable (fun stream ↦ binaryDigit stream index) bitMeasure := by
  rw [binaryDigit_eq_indicator]
  exact (integrable_const _).indicator (measurableSet_bit_true index)

/-- The expectation of one binary digit is half its place value. -/
theorem integral_binaryDigit (index : ℕ) :
    ∫ stream, binaryDigit stream index ∂bitMeasure = (1 / 2 : ℝ) ^ (index + 1) * (1 / 2) := by
  rw [binaryDigit_eq_indicator, integral_indicator_const _ (measurableSet_bit_true index),
    bitMeasure_real_bit_true, smul_eq_mul, mul_comm]

/-- The truncated draw is integrable. -/
theorem integrable_truncatedDraw (stage : ℕ) :
    Integrable (truncatedDraw stage) bitMeasure :=
  integrable_finset_sum _ fun index _ ↦ integrable_binaryDigit index

/-- NOTE2 Theorem 5, executed: the stage integral of the truncated draw is
`(1 - 2^(-stage)) / 2`. -/
theorem integral_truncatedDraw (stage : ℕ) :
    ∫ stream, truncatedDraw stage stream ∂bitMeasure = (1 - (1 / 2 : ℝ) ^ stage) / 2 := by
  unfold truncatedDraw
  rw [integral_finset_sum _ fun index _ ↦ integrable_binaryDigit index]
  simp only [integral_binaryDigit]
  induction stage with
  | zero => simp
  | succ stage ih =>
    rw [Finset.sum_range_succ, ih]
    ring

/-- NOTE2 Theorem 5, executed: the rational lower certificate of the uniform draw at a stage is
`(1 - 2^(-stage)) / 2`. -/
theorem lowerSum_uniformEvaluator (stage : ℕ) :
    (uniformEvaluator.lowerSum stage : ℝ) = (1 - (1 / 2 : ℝ) ^ stage) / 2 := by
  rw [uniformEvaluator.lowerSum_cast, ← integral_truncatedDraw]
  refine integral_congr_ae (ae_of_all _ fun stream ↦ ?_)
  exact wordDraw_prefixOf stage stream

/-- NOTE2 Theorem 5, executed: the rational upper certificate of the uniform draw at a stage is
`(1 + 2^(-stage)) / 2`. -/
theorem upperSum_uniformEvaluator (stage : ℕ) :
    (uniformEvaluator.upperSum stage : ℝ) = (1 + (1 / 2 : ℝ) ^ stage) / 2 := by
  rw [uniformEvaluator.upperSum_cast]
  have hfun : (fun stream ↦ uniformEvaluator.upperEvaluation stage stream) =
      fun stream ↦ truncatedDraw stage stream + (1 / 2 : ℝ) ^ stage := by
    funext stream
    show ((wordDraw stage (prefixOf stream stage) + (1 / 2) ^ stage : ℚ) : ℝ) = _
    push_cast
    rw [wordDraw_prefixOf]
  rw [hfun, integral_add (integrable_truncatedDraw stage) (integrable_const _), integral_const,
    integral_truncatedDraw]
  simp only [measureReal_univ_eq_one, one_smul]
  ring

/-- NOTE2 Theorem 5, executed: the exact expectation of the uniform draw is one half, obtained as
the limit of the rational cylinder certificates. -/
theorem integral_uniformDraw : ∫ stream, uniformDraw stream ∂bitMeasure = 1 / 2 := by
  have hcertificate := uniformEvaluator.tendsto_lowerSum
  have hclosed : Tendsto (fun stage ↦ (uniformEvaluator.lowerSum stage : ℝ)) atTop
      (𝓝 (1 / 2)) := by
    have hpower := tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num)
      (by norm_num)
    have hconst : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
    have hlimit := (hconst.sub hpower).div_const 2
    rw [sub_zero] at hlimit
    refine hlimit.congr fun stage ↦ ?_
    rw [lowerSum_uniformEvaluator]
  exact tendsto_nhds_unique hcertificate hclosed

end

end Descent.Portability.CylinderUniformDraw
