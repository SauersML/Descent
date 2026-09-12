/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.CylinderGaussianQuadrant

assert_below Descent.Decision Descent.Program

/-!
# Computable cylinder certificates

NOTE2 Theorem 5 certifies an expectation by rational cylinder sums. `CylinderIntervalCertificate`
records the rational values of an evaluator only as data, and its certificates `lowerSum` and
`upperSum` sum over `wordsOfLength`, a finset read off the finiteness of a set by choice, so they
are not computed by an algorithm. This module gives the algorithm and proves that it computes the
certificates.

`wordSum length value` sums a rational function over all words of a length by structural
recursion on the length, prepending `true` and `false` to the words of one letter less.
`sum_wordsOfLength_eq_wordSum` identifies it with the finset sum over `wordsOfLength`, and
`cylinderSum depth value` multiplies it by the cylinder mass `2^(-depth)`. For every evaluator the
certificates are these sums of its values (`lowerSum_eq_cylinderSum`, `upperSum_eq_cylinderSum`),
so the computed sums bracket the exact expectation at every stage and converge to it
(`computed_bracket`, `tendsto_computed`).

Two instances run the algorithm. `uniformLowerCertificate` and `uniformUpperCertificate` are the
certificates of the uniform draw of `CylinderUniformDraw`, whose values are the digits a word
spells, with closed forms `(1 ∓ 2^(-stage)) / 2` (`cast_uniformLowerCertificate`,
`cast_uniformUpperCertificate`). `quadrantLowerCertificate` and `quadrantUpperCertificate` are the
certificates of the quadrant indicator of the Box–Muller pair of `CylinderGaussianQuadrant`, whose
values compare interlaced digits with rational thresholds; they bracket one quarter and converge
to it (`quadrant_computed_bracket`, `tendsto_quadrant_computed`). The definitions of this module
sit outside any `noncomputable section`, so the compiler accepts every one of them as executable
code, and the check file evaluates several stages in the kernel by `decide`.

Not formalized here: an efficient algorithm (the enumeration visits all `2^depth` words), and
kernel evaluations of the exponential and radial certificates, whose values are also rational
functions of words but whose logarithmic series make the reductions large.

## Empirical status

None. The bodies here are algebra: the certificates are stipulated rational sums, and every
conclusion follows from the recursion on word length and the certified evaluators, so no
measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.CylinderComputableCertificate

open MeasureTheory Filter CylinderIntervalCertificate CylinderUniformDraw
  UniformPenetranceCertificate CylinderGaussianQuadrant

open scoped Topology

/-! ### Summing over the words of a length -/

/-- The sum of a rational function over all words of a length, by recursion on the length: the
words of one more letter are the words of the length with `true` or `false` prepended. -/
def wordSum : ℕ → (List Bool → ℚ) → ℚ
  | 0, value => value []
  | length + 1, value => wordSum length fun word ↦ value (true :: word) + value (false :: word)

/-- The cylinder sum at a depth: the cylinder mass `2^(-depth)` times the sum of a rational
function over the words of that length. -/
def cylinderSum (depth : ℕ) (value : List Bool → ℚ) : ℚ :=
  (1 / 2) ^ depth * wordSum depth value

/-- A rational sum over the words of one more letter splits by the first bit. -/
theorem sum_wordsOfLength_succ_rat (length : ℕ) (value : List Bool → ℚ) :
    ∑ word ∈ wordsOfLength (length + 1), value word =
      ∑ word ∈ wordsOfLength length, (value (true :: word) + value (false :: word)) := by
  rw [wordsOfLength_succ, Finset.sum_image, Finset.sum_product, Fintype.sum_bool]
  · exact Finset.sum_add_distrib.symm
  · intro first _ second _ hequal
    simp only [List.cons.injEq] at hequal
    exact Prod.ext hequal.1 hequal.2

/-- NOTE2 Theorem 5, computed: the recursion `wordSum` computes the sum over `wordsOfLength`. -/
theorem sum_wordsOfLength_eq_wordSum (length : ℕ) (value : List Bool → ℚ) :
    ∑ word ∈ wordsOfLength length, value word = wordSum length value := by
  induction length generalizing value with
  | zero =>
    rw [wordsOfLength_zero, Finset.sum_singleton]
    rfl
  | succ length ih =>
    rw [sum_wordsOfLength_succ_rat, ih]
    rfl

section Evaluator

variable {integrand : (ℕ → Bool) → ℝ}

/-- NOTE2 Theorem 5, computed: the lower certificate of an evaluator is the cylinder sum of its
lower values. -/
theorem lowerSum_eq_cylinderSum (evaluator : CylinderEvaluator integrand) (stage : ℕ) :
    evaluator.lowerSum stage = cylinderSum (evaluator.depth stage) (evaluator.lower stage) := by
  rw [CylinderEvaluator.lowerSum, ← Finset.mul_sum, sum_wordsOfLength_eq_wordSum]
  rfl

/-- NOTE2 Theorem 5, computed: the upper certificate of an evaluator is the cylinder sum of its
upper values. -/
theorem upperSum_eq_cylinderSum (evaluator : CylinderEvaluator integrand) (stage : ℕ) :
    evaluator.upperSum stage = cylinderSum (evaluator.depth stage) (evaluator.upper stage) := by
  rw [CylinderEvaluator.upperSum, ← Finset.mul_sum, sum_wordsOfLength_eq_wordSum]
  rfl

/-- NOTE2 Theorem 5, computed: at every stage the computed cylinder sums of an evaluator bracket
the exact expectation of its integrand. -/
theorem computed_bracket (evaluator : CylinderEvaluator integrand) (stage : ℕ) :
    (cylinderSum (evaluator.depth stage) (evaluator.lower stage) : ℝ) ≤
        ∫ stream, integrand stream ∂bitMeasure ∧
      ∫ stream, integrand stream ∂bitMeasure ≤
        (cylinderSum (evaluator.depth stage) (evaluator.upper stage) : ℝ) := by
  rw [← lowerSum_eq_cylinderSum, ← upperSum_eq_cylinderSum]
  exact ⟨evaluator.lowerSum_le_integral stage, evaluator.integral_le_upperSum stage⟩

/-- NOTE2 Theorem 5, computed: the computed cylinder sums of an evaluator converge to the exact
expectation of its integrand. -/
theorem tendsto_computed (evaluator : CylinderEvaluator integrand) :
    Tendsto (fun stage ↦ (cylinderSum (evaluator.depth stage) (evaluator.lower stage) : ℝ))
        atTop (𝓝 (∫ stream, integrand stream ∂bitMeasure)) ∧
      Tendsto (fun stage ↦ (cylinderSum (evaluator.depth stage) (evaluator.upper stage) : ℝ))
        atTop (𝓝 (∫ stream, integrand stream ∂bitMeasure)) := by
  simp only [← lowerSum_eq_cylinderSum, ← upperSum_eq_cylinderSum]
  exact ⟨evaluator.tendsto_lowerSum, evaluator.tendsto_upperSum⟩

end Evaluator

/-! ### The uniform draw -/

/-- The computed lower certificate of the uniform draw at a stage: the cylinder sum of the
digits spelled by the words of the stage. -/
def uniformLowerCertificate (stage : ℕ) : ℚ :=
  cylinderSum stage (wordDraw stage)

/-- The computed upper certificate of the uniform draw at a stage: the cylinder sum of the
digits plus the slack `2^(-stage)`. -/
def uniformUpperCertificate (stage : ℕ) : ℚ :=
  cylinderSum stage fun word ↦ wordDraw stage word + (1 / 2) ^ stage

/-- The computed lower certificate of the uniform draw is the certificate of its evaluator. -/
theorem uniformEvaluator_lowerSum_eq (stage : ℕ) :
    uniformEvaluator.lowerSum stage = uniformLowerCertificate stage :=
  lowerSum_eq_cylinderSum uniformEvaluator stage

/-- The computed upper certificate of the uniform draw is the certificate of its evaluator. -/
theorem uniformEvaluator_upperSum_eq (stage : ℕ) :
    uniformEvaluator.upperSum stage = uniformUpperCertificate stage :=
  upperSum_eq_cylinderSum uniformEvaluator stage

/-- NOTE2 Theorem 5, computed: the computed lower certificate of the uniform draw is
`(1 - 2^(-stage)) / 2`. -/
theorem cast_uniformLowerCertificate (stage : ℕ) :
    (uniformLowerCertificate stage : ℝ) = (1 - (1 / 2 : ℝ) ^ stage) / 2 := by
  rw [← uniformEvaluator_lowerSum_eq, lowerSum_uniformEvaluator]

/-- NOTE2 Theorem 5, computed: the computed upper certificate of the uniform draw is
`(1 + 2^(-stage)) / 2`. -/
theorem cast_uniformUpperCertificate (stage : ℕ) :
    (uniformUpperCertificate stage : ℝ) = (1 + (1 / 2 : ℝ) ^ stage) / 2 := by
  rw [← uniformEvaluator_upperSum_eq, upperSum_uniformEvaluator]

/-! ### The quadrant indicator of the Box–Muller pair -/

/-- The computed lower certificate of the quadrant indicator at a stage: the cylinder sum of the
rational lower values on the words of length `2 stage`. -/
def quadrantLowerCertificate (stage : ℕ) : ℚ :=
  cylinderSum (2 * stage) (quadrantLower stage)

/-- The computed upper certificate of the quadrant indicator at a stage: the cylinder sum of the
rational upper values on the words of length `2 stage`. -/
def quadrantUpperCertificate (stage : ℕ) : ℚ :=
  cylinderSum (2 * stage) (quadrantUpper stage)

/-- The computed lower certificate of the quadrant indicator is the certificate of its
evaluator. -/
theorem quadrantEvaluator_lowerSum_eq (stage : ℕ) :
    quadrantEvaluator.lowerSum stage = quadrantLowerCertificate stage :=
  lowerSum_eq_cylinderSum quadrantEvaluator stage

/-- The computed upper certificate of the quadrant indicator is the certificate of its
evaluator. -/
theorem quadrantEvaluator_upperSum_eq (stage : ℕ) :
    quadrantEvaluator.upperSum stage = quadrantUpperCertificate stage :=
  upperSum_eq_cylinderSum quadrantEvaluator stage

/-- NOTE2 §7.2, computed: at every stage the computed certificates of the quadrant indicator
bracket one quarter, the Gaussian mass of the open positive quadrant. -/
theorem quadrant_computed_bracket (stage : ℕ) :
    (quadrantLowerCertificate stage : ℝ) ≤ 1 / 4 ∧
      1 / 4 ≤ (quadrantUpperCertificate stage : ℝ) := by
  rw [← quadrantEvaluator_lowerSum_eq, ← quadrantEvaluator_upperSum_eq]
  exact quadrant_certificate stage

/-- NOTE2 §7.2, computed: the computed certificates of the quadrant indicator converge to one
quarter. -/
theorem tendsto_quadrant_computed :
    Tendsto (fun stage ↦ (quadrantLowerCertificate stage : ℝ)) atTop (𝓝 (1 / 4)) ∧
      Tendsto (fun stage ↦ (quadrantUpperCertificate stage : ℝ)) atTop (𝓝 (1 / 4)) := by
  simp only [← quadrantEvaluator_lowerSum_eq, ← quadrantEvaluator_upperSum_eq]
  exact tendsto_quadrant_certificate

end Descent.Portability.CylinderComputableCertificate
