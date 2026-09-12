/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.CylinderUniformDraw
import Descent.Portability.UniformPenetranceArchitecture

assert_below Descent.Decision Descent.Program

/-!
# Executed Theorem 5 for the uniform-penetrance architecture

NOTE2 §9.1 draws the shared penetrance from the uniform law and reports the population squared
correlation `θ / (2 - θ)` and area under the curve `(3 - θ) / (2 (2 - θ))`, whose exact
expectations `2 log 2 - 1` and `(1 + log 2) / 2` are `UniformPenetranceArchitecture`'s
`integral_unit_ratio` and `integral_unit_auc`. This module certifies both expectations by
Theorem 5: the penetrance is the uniform draw of `CylinderUniformDraw` from fair bits, each
metric is evaluated on cylinders with rational interval values, and the nested rational bounds
converge to the two closed forms.

`metricEvaluator` is the cylinder evaluator of an increasing metric of the draw that is Lipschitz
on the unit interval: on a word of length `stage` its lower value is the metric at the digits
the word spells and its upper value is the metric at those digits plus two to the minus
`stage`. `sum_wordsOfLength_wordDraw` is the dyadic census: over the words of length `stage`
the spelled digits run through the grid `k / 2^stage` once each. So the rational certificates
are the left and right dyadic Riemann sums of the metric (`lowerSum_metricEvaluator`,
`upperSum_metricEvaluator`), which bracket the interval integral of an increasing curve
(`riemannSums_bracket_integral`) and differ by two to the minus `stage` times its total
increase (`riemannSums_gap`). `squaredCorrelationEvaluator` and `aucEvaluator` instantiate the
construction with no hypothesis. `squaredCorrelation_certificate`,
`tendsto_squaredCorrelation_certificate`, `auc_certificate` and `tendsto_auc_certificate` are
the executed Theorem 5. Because Theorem 5 also sends the certificates to the bit-stream
expectation, `integral_squaredCorrelation_penetranceLaw_uniformDraw` and
`integral_binaryAUC_penetranceLaw_uniformDraw` show that the corpus metrics of the architecture
at the uniform draw have the same two expectations under the fair-bit law.

Not formalized here: the replica coefficients `E[N (1 - D)^k]` of the reduced polynomial
representation and the other metrics of §9.1, whose expectations the corpus proves by
integration without a cylinder certificate.

## Empirical status

None. The bodies here are algebra and measure theory: the architecture and the draw are
stipulated, and every conclusion follows from the dyadic census, monotone integral bounds and
the corpus closed forms, so no measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.UniformPenetranceCertificate

open MeasureTheory Filter CylinderIntervalCertificate CylinderUniformDraw
  UniformPenetranceArchitecture

open scoped ENNReal Topology

noncomputable section

/-! ### The dyadic census of words -/

/-- The digits spelled by a word have nonnegative value. -/
theorem wordDraw_nonneg (stage : ℕ) (word : List Bool) : 0 ≤ wordDraw stage word :=
  Finset.sum_nonneg fun _ _ ↦ by split_ifs <;> positivity

/-- The digits spelled by a word plus the most the unread digits can add is at most one. -/
theorem wordDraw_add_le_one (stage : ℕ) (word : List Bool) :
    wordDraw stage word + (1 / 2 : ℚ) ^ stage ≤ 1 := by
  induction stage with
  | zero => simp [wordDraw]
  | succ stage ih =>
    rw [wordDraw_succ]
    have hplace : (0 : ℚ) ≤ (1 / 2) ^ (stage + 1) := by positivity
    have hsplit : (1 / 2 : ℚ) ^ stage = 2 * (1 / 2) ^ (stage + 1) := by ring
    split_ifs <;> linarith

/-- Prepending a bit halves the value of the digits and adds one half when the bit is true. -/
theorem wordDraw_cons (stage : ℕ) (bit : Bool) (word : List Bool) :
    wordDraw (stage + 1) (bit :: word) =
      (if bit then (1 / 2 : ℚ) else 0) + wordDraw stage word / 2 := by
  unfold wordDraw
  rw [Finset.sum_range_succ', Finset.sum_div]
  have hsum : ∀ index ∈ Finset.range stage,
      (if (bit :: word).getD (index + 1) false then (1 / 2 : ℚ) ^ (index + 1 + 1) else 0) =
        (if word.getD index false then (1 / 2 : ℚ) ^ (index + 1) else 0) / 2 := by
    intro index _
    simp only [List.getD_eq_getElem?_getD, List.getElem?_cons_succ]
    split_ifs <;> ring
  rw [Finset.sum_congr rfl hsum]
  cases bit <;> simp [List.getD_eq_getElem?_getD, add_comm]

/-- Prepending a false bit halves the value of the digits. -/
theorem wordDraw_cons_false (stage : ℕ) (word : List Bool) :
    wordDraw (stage + 1) (false :: word) = wordDraw stage word / 2 := by
  rw [wordDraw_cons]
  simp

/-- Prepending a true bit halves the value of the digits and adds one half. -/
theorem wordDraw_cons_true (stage : ℕ) (word : List Bool) :
    wordDraw (stage + 1) (true :: word) = 1 / 2 + wordDraw stage word / 2 := by
  rw [wordDraw_cons]
  simp

/-- The only word of length zero is the empty word. -/
theorem wordsOfLength_zero : wordsOfLength 0 = {[]} := by
  ext word
  rw [mem_wordsOfLength, Finset.mem_singleton, List.length_eq_zero_iff]

/-- The words of one more letter are the words of the current length with a bit prepended. -/
theorem wordsOfLength_succ (stage : ℕ) :
    wordsOfLength (stage + 1) =
      (Finset.univ ×ˢ wordsOfLength stage).image fun pair : Bool × List Bool ↦
        pair.1 :: pair.2 := by
  ext word
  simp only [Finset.mem_image, Finset.mem_product, Finset.mem_univ, true_and,
    mem_wordsOfLength, Prod.exists]
  constructor
  · intro hlength
    cases word with
    | nil => simp at hlength
    | cons bit rest => exact ⟨bit, rest, by simpa using hlength, rfl⟩
  · rintro ⟨bit, rest, hrest, rfl⟩
    simp [hrest]

/-- A sum over the words of one more letter splits by the first bit. -/
theorem sum_wordsOfLength_succ (stage : ℕ) (value : List Bool → ℝ) :
    ∑ word ∈ wordsOfLength (stage + 1), value word =
      ∑ word ∈ wordsOfLength stage, value (false :: word) +
        ∑ word ∈ wordsOfLength stage, value (true :: word) := by
  rw [wordsOfLength_succ, Finset.sum_image, Finset.sum_product, Fintype.sum_bool]
  · exact add_comm _ _
  · intro first _ second _ hequal
    simp only [List.cons.injEq] at hequal
    exact Prod.ext hequal.1 hequal.2

/-- NOTE2 §7.2, the dyadic census: over the words of length `stage`, the value of the spelled
digits runs through the grid `k / 2^stage` once each. -/
theorem sum_wordsOfLength_wordDraw (stage : ℕ) (value : ℚ → ℝ) :
    ∑ word ∈ wordsOfLength stage, value (wordDraw stage word) =
      ∑ index ∈ Finset.range (2 ^ stage), value ((index : ℚ) / 2 ^ stage) := by
  induction stage generalizing value with
  | zero => simp [wordsOfLength_zero, wordDraw]
  | succ stage ih =>
    rw [sum_wordsOfLength_succ]
    simp only [wordDraw_cons_false, wordDraw_cons_true]
    have hfalse : ∑ word ∈ wordsOfLength stage, value (wordDraw stage word / 2) =
        ∑ index ∈ Finset.range (2 ^ stage), value ((index : ℚ) / 2 ^ stage / 2) :=
      ih fun draw ↦ value (draw / 2)
    have htrue : ∑ word ∈ wordsOfLength stage, value (1 / 2 + wordDraw stage word / 2) =
        ∑ index ∈ Finset.range (2 ^ stage), value (1 / 2 + (index : ℚ) / 2 ^ stage / 2) :=
      ih fun draw ↦ value (1 / 2 + draw / 2)
    rw [hfalse, htrue, show 2 ^ (stage + 1) = 2 ^ stage + 2 ^ stage by ring,
      Finset.sum_range_add]
    congr 1
    · refine Finset.sum_congr rfl fun index _ ↦ congrArg value ?_
      rw [pow_succ, div_div]
    · refine Finset.sum_congr rfl fun index _ ↦ congrArg value ?_
      push_cast
      field_simp
      ring

/-! ### Increasing metrics of the uniform draw -/

/-- Along every stream the truncated draw and the draw lie in the unit interval, with the draw
between the truncation and the truncation plus two to the minus the stage. -/
theorem draw_bracket (stage : ℕ) (stream : ℕ → Bool) :
    0 ≤ truncatedDraw stage stream ∧ truncatedDraw stage stream ≤ uniformDraw stream ∧
      uniformDraw stream ≤ truncatedDraw stage stream + (1 / 2 : ℝ) ^ stage ∧
        truncatedDraw stage stream + (1 / 2 : ℝ) ^ stage ≤ 1 := by
  refine ⟨Finset.sum_nonneg fun index _ ↦ binaryDigit_nonneg stream index,
    truncatedDraw_le_uniformDraw stage stream, uniformDraw_le_truncatedDraw_add stage stream, ?_⟩
  have hrational : ((wordDraw stage (prefixOf stream stage) + (1 / 2 : ℚ) ^ stage : ℚ) : ℝ) ≤
      ((1 : ℚ) : ℝ) := by
    exact_mod_cast wordDraw_add_le_one stage (prefixOf stream stage)
  push_cast at hrational
  rw [← wordDraw_prefixOf]
  exact hrational

/-- NOTE2 Theorem 5 for a metric of the uniform draw: the cylinder evaluator whose lower value
on a word is the metric at the spelled digits and whose upper value is the metric at those
digits plus two to the minus the stage. Assumes: the rational metric is the restriction of a
real curve that increases on the unit interval and is Lipschitz there with the supplied
constant. -/
def metricEvaluator (metric : ℚ → ℚ) (curve : ℝ → ℝ) (constant : ℝ)
    (hcast : ∀ draw : ℚ, (metric draw : ℝ) = curve draw)
    (hincrease : ∀ first second : ℝ, 0 ≤ first → first ≤ second → second ≤ 1 →
      0 ≤ curve second - curve first ∧
        curve second - curve first ≤ constant * (second - first)) :
    CylinderEvaluator fun stream ↦ curve (uniformDraw stream) where
  depth := fun stage ↦ stage
  lower := fun stage word ↦ metric (wordDraw stage word)
  upper := fun stage word ↦ metric (wordDraw stage word + (1 / 2) ^ stage)
  depth_mono := monotone_id
  lower_le := fun stage word hlength stream hstream ↦ by
    have hprefix := (mem_cylinder_iff_prefixOf_eq hlength stream).mp hstream
    show (metric (wordDraw stage word) : ℝ) ≤ curve (uniformDraw stream)
    rw [hcast, ← hprefix, wordDraw_prefixOf]
    obtain ⟨hbase, hdraw, hslack, hceiling⟩ := draw_bracket stage stream
    exact sub_nonneg.mp (hincrease _ _ hbase hdraw (by linarith)).1
  le_upper := fun stage word hlength stream hstream ↦ by
    have hprefix := (mem_cylinder_iff_prefixOf_eq hlength stream).mp hstream
    show curve (uniformDraw stream) ≤ (metric (wordDraw stage word + (1 / 2) ^ stage) : ℝ)
    rw [hcast, ← hprefix]
    push_cast
    rw [wordDraw_prefixOf]
    obtain ⟨hbase, hdraw, hslack, hceiling⟩ := draw_bracket stage stream
    exact sub_nonneg.mp (hincrease _ _ (by linarith) hslack hceiling).1
  lower_nested := fun stage word hlength ↦ by
    have hstep : wordDraw stage (word.take stage) ≤ wordDraw (stage + 1) word :=
      uniformEvaluator.lower_nested stage word hlength
    have hbase := wordDraw_nonneg stage (word.take stage)
    have hceiling := wordDraw_add_le_one (stage + 1) word
    have hpower : (0 : ℚ) ≤ (1 / 2) ^ (stage + 1) := by positivity
    have hreal := (hincrease (wordDraw stage (word.take stage) : ℝ)
      (wordDraw (stage + 1) word : ℝ) (by exact_mod_cast hbase) (by exact_mod_cast hstep)
      (by have hone : wordDraw (stage + 1) word ≤ 1 := by linarith
          exact_mod_cast hone)).1
    rw [← hcast, ← hcast, sub_nonneg] at hreal
    exact_mod_cast hreal
  upper_nested := fun stage word hlength ↦ by
    have hstep : wordDraw (stage + 1) word + (1 / 2) ^ (stage + 1) ≤
        wordDraw stage (word.take stage) + (1 / 2) ^ stage :=
      uniformEvaluator.upper_nested stage word hlength
    have hbase := wordDraw_nonneg (stage + 1) word
    have hceiling := wordDraw_add_le_one stage (word.take stage)
    have hpower : (0 : ℚ) ≤ (1 / 2) ^ (stage + 1) := by positivity
    have hreal := (hincrease ((wordDraw (stage + 1) word + (1 / 2) ^ (stage + 1) : ℚ) : ℝ)
      ((wordDraw stage (word.take stage) + (1 / 2) ^ stage : ℚ) : ℝ)
      (by have hzero : (0 : ℚ) ≤ wordDraw (stage + 1) word + (1 / 2) ^ (stage + 1) := by
            linarith
          exact_mod_cast hzero)
      (by exact_mod_cast hstep) (by exact_mod_cast hceiling)).1
    rw [← hcast, ← hcast, sub_nonneg] at hreal
    exact_mod_cast hreal
  width_ae := ae_of_all _ fun stream ↦ by
    have hwidth : ∀ stage : ℕ,
        0 ≤ curve (truncatedDraw stage stream + (1 / 2) ^ stage) -
            curve (truncatedDraw stage stream) ∧
          curve (truncatedDraw stage stream + (1 / 2) ^ stage) -
            curve (truncatedDraw stage stream) ≤ constant * (1 / 2) ^ stage := by
      intro stage
      obtain ⟨hbase, _, _, hceiling⟩ := draw_bracket stage stream
      have hpower : (0 : ℝ) ≤ (1 / 2) ^ stage := by positivity
      have hincrement := hincrease _ _ hbase (by linarith) hceiling
      rwa [add_sub_cancel_left] at hincrement
    have hformula : ∀ stage : ℕ,
        ((metric (wordDraw stage (prefixOf stream stage) + (1 / 2) ^ stage) : ℚ) : ℝ) -
            (metric (wordDraw stage (prefixOf stream stage)) : ℝ) =
          curve (truncatedDraw stage stream + (1 / 2) ^ stage) -
            curve (truncatedDraw stage stream) := by
      intro stage
      rw [hcast, hcast]
      push_cast
      rw [wordDraw_prefixOf]
    have hlimit := (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num)
      (by norm_num)).const_mul constant
    rw [mul_zero] at hlimit
    refine squeeze_zero (fun stage ↦ ?_) (fun stage ↦ ?_) hlimit
    · show (0 : ℝ) ≤
        ((metric (wordDraw stage (prefixOf stream stage) + (1 / 2) ^ stage) : ℚ) : ℝ) -
          (metric (wordDraw stage (prefixOf stream stage)) : ℝ)
      rw [hformula]
      exact (hwidth stage).1
    · show ((metric (wordDraw stage (prefixOf stream stage) + (1 / 2) ^ stage) : ℚ) : ℝ) -
          (metric (wordDraw stage (prefixOf stream stage)) : ℝ) ≤ constant * (1 / 2) ^ stage
      rw [hformula]
      exact (hwidth stage).2

/-- NOTE2 Theorem 5, executed: the rational lower certificate of a metric of the uniform draw is
the left dyadic Riemann sum of its curve. -/
theorem lowerSum_metricEvaluator (metric : ℚ → ℚ) (curve : ℝ → ℝ) (constant : ℝ)
    (hcast : ∀ draw : ℚ, (metric draw : ℝ) = curve draw)
    (hincrease : ∀ first second : ℝ, 0 ≤ first → first ≤ second → second ≤ 1 →
      0 ≤ curve second - curve first ∧
        curve second - curve first ≤ constant * (second - first)) (stage : ℕ) :
    ((metricEvaluator metric curve constant hcast hincrease).lowerSum stage : ℝ) =
      ∑ index ∈ Finset.range (2 ^ stage),
        (1 / 2 : ℝ) ^ stage * curve ((index : ℝ) / 2 ^ stage) := by
  have hcensus := sum_wordsOfLength_wordDraw stage fun draw ↦
    (1 / 2 : ℝ) ^ stage * (metric draw : ℝ)
  rw [CylinderEvaluator.lowerSum]
  push_cast
  refine hcensus.trans (Finset.sum_congr rfl fun index _ ↦ ?_)
  show (1 / 2 : ℝ) ^ stage * (metric ((index : ℚ) / 2 ^ stage) : ℝ) = _
  rw [hcast]
  push_cast
  rfl

/-- NOTE2 Theorem 5, executed: the rational upper certificate of a metric of the uniform draw is
the right dyadic Riemann sum of its curve. -/
theorem upperSum_metricEvaluator (metric : ℚ → ℚ) (curve : ℝ → ℝ) (constant : ℝ)
    (hcast : ∀ draw : ℚ, (metric draw : ℝ) = curve draw)
    (hincrease : ∀ first second : ℝ, 0 ≤ first → first ≤ second → second ≤ 1 →
      0 ≤ curve second - curve first ∧
        curve second - curve first ≤ constant * (second - first)) (stage : ℕ) :
    ((metricEvaluator metric curve constant hcast hincrease).upperSum stage : ℝ) =
      ∑ index ∈ Finset.range (2 ^ stage),
        (1 / 2 : ℝ) ^ stage * curve (((index : ℝ) + 1) / 2 ^ stage) := by
  have hcensus := sum_wordsOfLength_wordDraw stage fun draw ↦
    (1 / 2 : ℝ) ^ stage * (metric (draw + (1 / 2) ^ stage) : ℝ)
  rw [CylinderEvaluator.upperSum]
  push_cast
  refine hcensus.trans (Finset.sum_congr rfl fun index _ ↦ ?_)
  show (1 / 2 : ℝ) ^ stage * (metric ((index : ℚ) / 2 ^ stage + (1 / 2) ^ stage) : ℝ) = _
  rw [hcast]
  congr 1
  congr 1
  push_cast
  rw [one_div_pow, ← add_div]

/-! ### Dyadic Riemann sums of an increasing curve -/

/-- The unit interval is the union of the dyadic intervals of a stage, and so is its integral. -/
theorem integral_unit_eq_sum_dyadic (curve : ℝ → ℝ) (hmonotone : MonotoneOn curve (Set.Icc 0 1))
    (stage : ℕ) :
    ∫ θ in (0:ℝ)..1, curve θ =
      ∑ index ∈ Finset.range (2 ^ stage),
        ∫ θ in (index : ℝ) / 2 ^ stage..((index + 1 : ℕ) : ℝ) / 2 ^ stage, curve θ := by
  have hpieces : ∀ index : ℕ, index < 2 ^ stage → IntervalIntegrable curve volume
      ((index : ℝ) / 2 ^ stage) (((index + 1 : ℕ) : ℝ) / 2 ^ stage) := by
    intro index hindex
    refine (hmonotone.mono ?_).intervalIntegrable
    have hle : (index : ℝ) / 2 ^ stage ≤ ((index + 1 : ℕ) : ℝ) / 2 ^ stage := by
      gcongr
      exact_mod_cast Nat.le_succ index
    have hupper : ((index + 1 : ℕ) : ℝ) / 2 ^ stage ≤ 1 := by
      rw [div_le_one (by positivity)]
      exact_mod_cast hindex
    rw [Set.uIcc_of_le hle]
    exact Set.Icc_subset_Icc (by positivity) hupper
  have hsum := intervalIntegral.sum_integral_adjacent_intervals (μ := volume) (f := curve)
    (a := fun index : ℕ ↦ (index : ℝ) / 2 ^ stage) hpieces
  have hstart : ((0 : ℕ) : ℝ) / 2 ^ stage = 0 := by simp
  have hfinish : ((2 ^ stage : ℕ) : ℝ) / 2 ^ stage = 1 := by
    push_cast
    exact div_self (by positivity)
  simp only [hstart, hfinish] at hsum
  exact hsum.symm

/-- On one dyadic interval an increasing curve integrates between its endpoint values times the
width. -/
theorem integral_dyadic_bracket (curve : ℝ → ℝ) (hmonotone : MonotoneOn curve (Set.Icc 0 1))
    (stage : ℕ) {index : ℕ} (hindex : index < 2 ^ stage) :
    (1 / 2 : ℝ) ^ stage * curve ((index : ℝ) / 2 ^ stage) ≤
        ∫ θ in (index : ℝ) / 2 ^ stage..((index + 1 : ℕ) : ℝ) / 2 ^ stage, curve θ ∧
      ∫ θ in (index : ℝ) / 2 ^ stage..((index + 1 : ℕ) : ℝ) / 2 ^ stage, curve θ ≤
        (1 / 2 : ℝ) ^ stage * curve (((index : ℝ) + 1) / 2 ^ stage) := by
  have hle : (index : ℝ) / 2 ^ stage ≤ ((index + 1 : ℕ) : ℝ) / 2 ^ stage := by
    gcongr
    exact_mod_cast Nat.le_succ index
  have hlower : (0 : ℝ) ≤ (index : ℝ) / 2 ^ stage := by positivity
  have hupper : ((index + 1 : ℕ) : ℝ) / 2 ^ stage ≤ 1 := by
    rw [div_le_one (by positivity)]
    exact_mod_cast hindex
  have hmember : ∀ θ ∈ Set.Icc ((index : ℝ) / 2 ^ stage) (((index + 1 : ℕ) : ℝ) / 2 ^ stage),
      θ ∈ Set.Icc (0 : ℝ) 1 := fun θ hθ ↦ ⟨le_trans hlower hθ.1, le_trans hθ.2 hupper⟩
  have hintegrable : IntervalIntegrable curve volume ((index : ℝ) / 2 ^ stage)
      (((index + 1 : ℕ) : ℝ) / 2 ^ stage) := by
    refine (hmonotone.mono ?_).intervalIntegrable
    rw [Set.uIcc_of_le hle]
    exact Set.Icc_subset_Icc hlower hupper
  have hwidth : ((index + 1 : ℕ) : ℝ) / 2 ^ stage - (index : ℝ) / 2 ^ stage =
      (1 / 2) ^ stage := by
    push_cast
    rw [← sub_div, add_sub_cancel_left, one_div_pow]
  have hleft : (index : ℝ) / 2 ^ stage ∈ Set.Icc (0 : ℝ) 1 := hmember _ ⟨le_rfl, hle⟩
  have hright : ((index + 1 : ℕ) : ℝ) / 2 ^ stage ∈ Set.Icc (0 : ℝ) 1 := hmember _ ⟨hle, le_rfl⟩
  constructor
  · calc (1 / 2 : ℝ) ^ stage * curve ((index : ℝ) / 2 ^ stage)
        = ∫ _ in (index : ℝ) / 2 ^ stage..((index + 1 : ℕ) : ℝ) / 2 ^ stage,
            curve ((index : ℝ) / 2 ^ stage) := by
          rw [intervalIntegral.integral_const, hwidth, smul_eq_mul]
      _ ≤ ∫ θ in (index : ℝ) / 2 ^ stage..((index + 1 : ℕ) : ℝ) / 2 ^ stage, curve θ :=
          intervalIntegral.integral_mono_on hle intervalIntegrable_const hintegrable
            fun θ hθ ↦ hmonotone hleft (hmember θ hθ) hθ.1
  · calc ∫ θ in (index : ℝ) / 2 ^ stage..((index + 1 : ℕ) : ℝ) / 2 ^ stage, curve θ
        ≤ ∫ _ in (index : ℝ) / 2 ^ stage..((index + 1 : ℕ) : ℝ) / 2 ^ stage,
            curve (((index + 1 : ℕ) : ℝ) / 2 ^ stage) :=
          intervalIntegral.integral_mono_on hle hintegrable intervalIntegrable_const
            fun θ hθ ↦ hmonotone (hmember θ hθ) hright hθ.2
      _ = (1 / 2 : ℝ) ^ stage * curve (((index : ℝ) + 1) / 2 ^ stage) := by
          rw [intervalIntegral.integral_const, hwidth, smul_eq_mul]
          push_cast
          rfl

/-- The left and right dyadic Riemann sums of an increasing curve bracket its integral over the
unit interval. -/
theorem riemannSums_bracket_integral (curve : ℝ → ℝ)
    (hmonotone : MonotoneOn curve (Set.Icc 0 1)) (stage : ℕ) :
    ∑ index ∈ Finset.range (2 ^ stage), (1 / 2 : ℝ) ^ stage * curve ((index : ℝ) / 2 ^ stage) ≤
        ∫ θ in (0:ℝ)..1, curve θ ∧
      ∫ θ in (0:ℝ)..1, curve θ ≤
        ∑ index ∈ Finset.range (2 ^ stage),
          (1 / 2 : ℝ) ^ stage * curve (((index : ℝ) + 1) / 2 ^ stage) := by
  rw [integral_unit_eq_sum_dyadic curve hmonotone stage]
  exact ⟨Finset.sum_le_sum fun index hindex ↦
      (integral_dyadic_bracket curve hmonotone stage (Finset.mem_range.mp hindex)).1,
    Finset.sum_le_sum fun index hindex ↦
      (integral_dyadic_bracket curve hmonotone stage (Finset.mem_range.mp hindex)).2⟩

/-- The right and left dyadic Riemann sums differ by two to the minus the stage times the total
increase of the curve over the unit interval. -/
theorem riemannSums_gap (curve : ℝ → ℝ) (stage : ℕ) :
    ∑ index ∈ Finset.range (2 ^ stage),
        (1 / 2 : ℝ) ^ stage * curve (((index : ℝ) + 1) / 2 ^ stage) -
      ∑ index ∈ Finset.range (2 ^ stage), (1 / 2 : ℝ) ^ stage * curve ((index : ℝ) / 2 ^ stage) =
      (1 / 2 : ℝ) ^ stage * (curve 1 - curve 0) := by
  have htelescope := Finset.sum_range_sub
    (fun index : ℕ ↦ curve ((index : ℝ) / 2 ^ stage)) (2 ^ stage)
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_zero,
    zero_div] at htelescope
  rw [div_self (by positivity)] at htelescope
  rw [← Finset.sum_sub_distrib, ← htelescope, Finset.mul_sum]
  refine Finset.sum_congr rfl fun index _ ↦ ?_
  ring

/-- The dyadic Riemann sums of an increasing curve converge to its integral over the unit
interval. -/
theorem tendsto_riemannSums (curve : ℝ → ℝ) (hmonotone : MonotoneOn curve (Set.Icc 0 1)) :
    Tendsto (fun stage : ℕ ↦ ∑ index ∈ Finset.range (2 ^ stage),
        (1 / 2 : ℝ) ^ stage * curve ((index : ℝ) / 2 ^ stage)) atTop
        (𝓝 (∫ θ in (0:ℝ)..1, curve θ)) ∧
      Tendsto (fun stage : ℕ ↦ ∑ index ∈ Finset.range (2 ^ stage),
          (1 / 2 : ℝ) ^ stage * curve (((index : ℝ) + 1) / 2 ^ stage)) atTop
        (𝓝 (∫ θ in (0:ℝ)..1, curve θ)) := by
  have hgap := (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num)
    (by norm_num)).mul_const (curve 1 - curve 0)
  rw [zero_mul] at hgap
  have hconst : Tendsto (fun _ : ℕ ↦ ∫ θ in (0:ℝ)..1, curve θ) atTop
      (𝓝 (∫ θ in (0:ℝ)..1, curve θ)) := tendsto_const_nhds
  have hbelow := hconst.sub hgap
  have habove := hconst.add hgap
  rw [sub_zero] at hbelow
  rw [add_zero] at habove
  constructor
  · refine tendsto_of_tendsto_of_tendsto_of_le_of_le hbelow hconst (fun stage ↦ ?_)
      fun stage ↦ (riemannSums_bracket_integral curve hmonotone stage).1
    have hbracket := (riemannSums_bracket_integral curve hmonotone stage).2
    have hdifference := riemannSums_gap curve stage
    show (∫ θ in (0:ℝ)..1, curve θ) - (1 / 2 : ℝ) ^ stage * (curve 1 - curve 0) ≤ _
    linarith
  · refine tendsto_of_tendsto_of_tendsto_of_le_of_le hconst habove
      (fun stage ↦ (riemannSums_bracket_integral curve hmonotone stage).2) fun stage ↦ ?_
    have hbracket := (riemannSums_bracket_integral curve hmonotone stage).1
    have hdifference := riemannSums_gap curve stage
    show _ ≤ (∫ θ in (0:ℝ)..1, curve θ) + (1 / 2 : ℝ) ^ stage * (curve 1 - curve 0)
    linarith

/-- NOTE2 Theorem 5, executed for an increasing metric of the uniform draw: at every stage the
rational certificates bracket the integral of the curve over the unit interval, and both
converge to it. -/
theorem metricEvaluator_certificate (metric : ℚ → ℚ) (curve : ℝ → ℝ) (constant : ℝ)
    (hcast : ∀ draw : ℚ, (metric draw : ℝ) = curve draw)
    (hincrease : ∀ first second : ℝ, 0 ≤ first → first ≤ second → second ≤ 1 →
      0 ≤ curve second - curve first ∧
        curve second - curve first ≤ constant * (second - first)) :
    (∀ stage, ((metricEvaluator metric curve constant hcast hincrease).lowerSum stage : ℝ) ≤
        ∫ θ in (0:ℝ)..1, curve θ ∧
      ∫ θ in (0:ℝ)..1, curve θ ≤
        ((metricEvaluator metric curve constant hcast hincrease).upperSum stage : ℝ)) ∧
    Tendsto (fun stage ↦
        ((metricEvaluator metric curve constant hcast hincrease).lowerSum stage : ℝ)) atTop
        (𝓝 (∫ θ in (0:ℝ)..1, curve θ)) ∧
      Tendsto (fun stage ↦
          ((metricEvaluator metric curve constant hcast hincrease).upperSum stage : ℝ)) atTop
        (𝓝 (∫ θ in (0:ℝ)..1, curve θ)) := by
  have hmonotone : MonotoneOn curve (Set.Icc 0 1) := fun first hfirst second hsecond hle ↦
    sub_nonneg.mp (hincrease first second hfirst.1 hle hsecond.2).1
  simp only [lowerSum_metricEvaluator, upperSum_metricEvaluator]
  exact ⟨riemannSums_bracket_integral curve hmonotone, tendsto_riemannSums curve hmonotone⟩

/-! ### The squared correlation and the area under the curve -/

/-- NOTE2 §9.1: the population squared correlation as a function of the penetrance. -/
def squaredCorrelationFormula {K : Type*} [Field K] (θ : K) : K :=
  θ / (2 - θ)

/-- At a real penetrance the squared-correlation formula is the corpus report
`ThetaFamilyNonclosure.thetaReport` of NOTE2 (13). -/
theorem squaredCorrelationFormula_eq_thetaReport (θ : ℝ) :
    squaredCorrelationFormula θ = ThetaFamilyNonclosure.thetaReport θ :=
  rfl

/-- NOTE2 §9.1: the population area under the curve as a function of the penetrance. -/
def aucFormula {K : Type*} [Field K] (θ : K) : K :=
  (3 - θ) / (2 * (2 - θ))

/-- The rational squared-correlation formula is the real one at the rational point. -/
theorem cast_squaredCorrelationFormula (θ : ℚ) :
    ((squaredCorrelationFormula θ : ℚ) : ℝ) = squaredCorrelationFormula (θ : ℝ) := by
  simp only [squaredCorrelationFormula, Rat.cast_div, Rat.cast_sub, Rat.cast_ofNat]

/-- The rational area-under-the-curve formula is the real one at the rational point. -/
theorem cast_aucFormula (θ : ℚ) : ((aucFormula θ : ℚ) : ℝ) = aucFormula (θ : ℝ) := by
  simp only [aucFormula, Rat.cast_div, Rat.cast_sub, Rat.cast_mul, Rat.cast_ofNat]

/-- On the unit interval the squared correlation increases, by at most twice the increase of
the penetrance. -/
theorem squaredCorrelationFormula_increase (first second : ℝ) (_hfirst : 0 ≤ first)
    (hle : first ≤ second) (hsecond : second ≤ 1) :
    0 ≤ squaredCorrelationFormula second - squaredCorrelationFormula first ∧
      squaredCorrelationFormula second - squaredCorrelationFormula first ≤
        2 * (second - first) := by
  have hfirstPositive : 0 < 2 - first := by linarith
  have hsecondPositive : 0 < 2 - second := by linarith
  have hdifference : squaredCorrelationFormula second - squaredCorrelationFormula first =
      2 * (second - first) / ((2 - second) * (2 - first)) := by
    unfold squaredCorrelationFormula
    rw [div_sub_div _ _ hsecondPositive.ne' hfirstPositive.ne']
    congr 1
    ring
  have hproduct : 1 ≤ (2 - second) * (2 - first) := by nlinarith
  rw [hdifference]
  constructor
  · exact div_nonneg (by linarith) (by positivity)
  · rw [div_le_iff₀ (by positivity)]
    nlinarith [mul_nonneg (sub_nonneg.mpr hle) (sub_nonneg.mpr hproduct)]

/-- On the unit interval the area under the curve increases, by at most half the increase of
the penetrance. -/
theorem aucFormula_increase (first second : ℝ) (_hfirst : 0 ≤ first) (hle : first ≤ second)
    (hsecond : second ≤ 1) :
    0 ≤ aucFormula second - aucFormula first ∧
      aucFormula second - aucFormula first ≤ 1 / 2 * (second - first) := by
  have hfirstPositive : 0 < 2 * (2 - first) := by linarith
  have hsecondPositive : 0 < 2 * (2 - second) := by linarith
  have hdifference : aucFormula second - aucFormula first =
      2 * (second - first) / (2 * (2 - second) * (2 * (2 - first))) := by
    unfold aucFormula
    rw [div_sub_div _ _ hsecondPositive.ne' hfirstPositive.ne']
    congr 1
    ring
  have hproduct : 4 ≤ 2 * (2 - second) * (2 * (2 - first)) := by nlinarith
  rw [hdifference]
  constructor
  · exact div_nonneg (by linarith) (by positivity)
  · rw [div_le_iff₀ (by positivity)]
    nlinarith [mul_nonneg (sub_nonneg.mpr hle) (sub_nonneg.mpr hproduct)]

/-- NOTE2 Theorem 5 on §9.1: the hypothesis-free cylinder evaluator of the population squared
correlation at the uniform draw. -/
def squaredCorrelationEvaluator :
    CylinderEvaluator fun stream ↦ squaredCorrelationFormula (uniformDraw stream) :=
  metricEvaluator squaredCorrelationFormula squaredCorrelationFormula 2
    cast_squaredCorrelationFormula squaredCorrelationFormula_increase

/-- NOTE2 Theorem 5 on §9.1: the hypothesis-free cylinder evaluator of the population area
under the curve at the uniform draw.

Regime: the §9.1 architecture, whose case prevalence at each penetrance draw is carried by
`aucFormula` itself. -/
def aucEvaluator : CylinderEvaluator fun stream ↦ aucFormula (uniformDraw stream) :=
  metricEvaluator aucFormula aucFormula (1 / 2) cast_aucFormula aucFormula_increase

/-- NOTE2 §9.1, executed Theorem 5: at every stage the rational certificates of the squared
correlation bracket its exact expectation `2 log 2 - 1`. -/
theorem squaredCorrelation_certificate (stage : ℕ) :
    (squaredCorrelationEvaluator.lowerSum stage : ℝ) ≤ 2 * Real.log 2 - 1 ∧
      2 * Real.log 2 - 1 ≤ (squaredCorrelationEvaluator.upperSum stage : ℝ) := by
  have hvalue : ∫ θ in (0:ℝ)..1, squaredCorrelationFormula θ = 2 * Real.log 2 - 1 :=
    integral_unit_ratio
  rw [← hvalue]
  exact (metricEvaluator_certificate squaredCorrelationFormula squaredCorrelationFormula 2
    cast_squaredCorrelationFormula squaredCorrelationFormula_increase).1 stage

/-- NOTE2 §9.1, executed Theorem 5: the rational certificates of the squared correlation
converge to `2 log 2 - 1`. -/
theorem tendsto_squaredCorrelation_certificate :
    Tendsto (fun stage ↦ (squaredCorrelationEvaluator.lowerSum stage : ℝ)) atTop
        (𝓝 (2 * Real.log 2 - 1)) ∧
      Tendsto (fun stage ↦ (squaredCorrelationEvaluator.upperSum stage : ℝ)) atTop
        (𝓝 (2 * Real.log 2 - 1)) := by
  have hvalue : ∫ θ in (0:ℝ)..1, squaredCorrelationFormula θ = 2 * Real.log 2 - 1 :=
    integral_unit_ratio
  rw [← hvalue]
  exact (metricEvaluator_certificate squaredCorrelationFormula squaredCorrelationFormula 2
    cast_squaredCorrelationFormula squaredCorrelationFormula_increase).2

/-- NOTE2 §9.1, executed Theorem 5: at every stage the rational certificates of the area under
the curve bracket its exact expectation `(1 + log 2) / 2`. -/
theorem auc_certificate (stage : ℕ) :
    (aucEvaluator.lowerSum stage : ℝ) ≤ (1 + Real.log 2) / 2 ∧
      (1 + Real.log 2) / 2 ≤ (aucEvaluator.upperSum stage : ℝ) := by
  have hvalue : ∫ θ in (0:ℝ)..1, aucFormula θ = (1 + Real.log 2) / 2 := integral_unit_auc
  rw [← hvalue]
  exact (metricEvaluator_certificate aucFormula aucFormula (1 / 2) cast_aucFormula
    aucFormula_increase).1 stage

/-- NOTE2 §9.1, executed Theorem 5: the rational certificates of the area under the curve
converge to `(1 + log 2) / 2`. -/
theorem tendsto_auc_certificate :
    Tendsto (fun stage ↦ (aucEvaluator.lowerSum stage : ℝ)) atTop
        (𝓝 ((1 + Real.log 2) / 2)) ∧
      Tendsto (fun stage ↦ (aucEvaluator.upperSum stage : ℝ)) atTop
        (𝓝 ((1 + Real.log 2) / 2)) := by
  have hvalue : ∫ θ in (0:ℝ)..1, aucFormula θ = (1 + Real.log 2) / 2 := integral_unit_auc
  rw [← hvalue]
  exact (metricEvaluator_certificate aucFormula aucFormula (1 / 2) cast_aucFormula
    aucFormula_increase).2

/-! ### The corpus metrics under the fair-bit law -/

/-- A stream containing a true bit encodes a positive draw. -/
theorem uniformDraw_pos {stream : ℕ → Bool} (htrue : ∃ index, stream index = true) :
    0 < uniformDraw stream := by
  obtain ⟨index, hindex⟩ := htrue
  have hdigit : binaryDigit stream index = (1 / 2 : ℝ) ^ (index + 1) := by
    simp [binaryDigit, hindex]
  have hle := (summable_binaryDigit stream).le_tsum index fun other _ ↦
    binaryDigit_nonneg stream other
  have hpositive : (0 : ℝ) < (1 / 2) ^ (index + 1) := by positivity
  unfold uniformDraw
  linarith

/-- The draw encoded by a stream is at most one. -/
theorem uniformDraw_le_one (stream : ℕ → Bool) : uniformDraw stream ≤ 1 := by
  obtain ⟨_, _, hslack, hceiling⟩ := draw_bracket 0 stream
  linarith

/-- NOTE2 §9.1 on fair bits: the population squared correlation reported by the corpus metric at
the uniform draw has fair-bit expectation `2 log 2 - 1`, the common limit of the rational
certificates and of Theorem 5. -/
theorem integral_squaredCorrelation_penetranceLaw_uniformDraw :
    ∫ stream, ((penetranceLaw (uniformDraw stream)).squaredCorrelation cellScore
        cellOutcome).getD 0 ∂bitMeasure = 2 * Real.log 2 - 1 := by
  have hexpectation : ∫ stream, squaredCorrelationFormula (uniformDraw stream) ∂bitMeasure =
      2 * Real.log 2 - 1 :=
    tendsto_nhds_unique squaredCorrelationEvaluator.tendsto_lowerSum
      tendsto_squaredCorrelation_certificate.1
  rw [← hexpectation]
  refine integral_congr_ae ?_
  filter_upwards [ae_exists_true] with stream htrue
  simp only [squaredCorrelation_penetranceLaw _ (uniformDraw_pos htrue)
    (uniformDraw_le_one stream), Option.getD_some, squaredCorrelationFormula]

/-- NOTE2 §9.1 on fair bits: the population area under the curve reported by the corpus metric
at the uniform draw has fair-bit expectation `(1 + log 2) / 2`, the common limit of the rational
certificates and of Theorem 5. -/
theorem integral_binaryAUC_penetranceLaw_uniformDraw :
    ∫ stream, ((penetranceLaw (uniformDraw stream)).binaryAUC cellScore outcomeFlag).getD 0
        ∂bitMeasure = (1 + Real.log 2) / 2 := by
  have hexpectation : ∫ stream, aucFormula (uniformDraw stream) ∂bitMeasure =
      (1 + Real.log 2) / 2 :=
    tendsto_nhds_unique aucEvaluator.tendsto_lowerSum tendsto_auc_certificate.1
  rw [← hexpectation]
  refine integral_congr_ae ?_
  filter_upwards [ae_exists_true] with stream htrue
  simp only [binaryAUC_penetranceLaw _ (uniformDraw_pos htrue) (uniformDraw_le_one stream),
    Option.getD_some, aucFormula]

end

end Descent.Portability.UniformPenetranceCertificate
