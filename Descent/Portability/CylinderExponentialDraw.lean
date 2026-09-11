/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.UniformPenetranceCertificate
import Descent.Portability.LogLossSeriesCertificate
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

assert_below Descent.Decision Descent.Program

/-!
# Executed Theorem 5 for the exponential draw from fair bits

NOTE2 §7.2 names an exponential waiting time among the continuous primitives that are not made
finite by naming their integral. This module represents it on the fair-bit stream as
`exponentialDraw`, the negative logarithm of the uniform draw of `CylinderUniformDraw`, and
certifies the expectation of the bounded integrand `min X 1` by Theorem 5, with rational
cylinder values and the exact limit `1 - e^(-1)`.

The rational values come from the logarithmic series of NOTE2 (30), formalized in
`LogLossSeriesCertificate`: `logLower` is its partial sum and `logUpper` adds the tail bound.
`exponentialCap` is the continuous decreasing curve `u ↦ -log (max u e^(-1))`, which equals
`min (-log u) 1` at every positive `u` (`exponentialCap_eq_min`). On the cylinder of a word
spelling the digits `a` at depth `stage`, `exponentialEvaluator` takes the partial sum at the
right end `a + 2^(-stage)` as lower value and the enclosed upper bound at the left end as upper
value, each capped at one. Nesting follows from the monotonicity of the series in the point and
in the order. The width vanishes on every stream containing a true bit: once such a bit bounds
the draw below by `c`, the width is at most `2 / ((stage + 1) c) + 2^(-stage) / c`
(`exponentialWidth_le`).

The exact value needs the law of the draw only through integrals of monotone curves.
`integral_uniformDraw_of_antitoneOn` shows for every continuous decreasing curve on the unit
interval that its expectation at the uniform draw is its interval integral, by dominated
convergence from the truncated draws, whose expectations are the dyadic Riemann sums of
`UniformPenetranceCertificate`. `integral_exponentialCap` computes `1 - e^(-1)`.
`exponential_certificate` and `tendsto_exponential_certificate` are the executed Theorem 5, and
`integral_min_exponentialDraw` identifies the certified value with the expectation of
`min X 1`.

Not formalized here: that the exponential draw has the exponential law as a measure; only the
certified expectation of the bounded integrand is proved.

## Empirical status

None. The bodies here are analysis and measure theory: the draw is a stipulated function of the
bit stream, and every conclusion follows from the logarithmic series, dyadic Riemann sums and
dominated convergence, so no measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.CylinderExponentialDraw

open MeasureTheory Filter CylinderIntervalCertificate CylinderUniformDraw
  UniformPenetranceCertificate LogLossSeriesCertificate

open scoped ENNReal Topology

noncomputable section

/-! ### Integrals of continuous decreasing curves at the uniform draw -/

/-- Along every stream the truncated draws converge to the draw. -/
theorem tendsto_truncatedDraw (stream : ℕ → Bool) :
    Tendsto (fun stage ↦ truncatedDraw stage stream) atTop (𝓝 (uniformDraw stream)) := by
  have hpower := tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num)
    (by norm_num)
  have hconst : Tendsto (fun _ : ℕ ↦ uniformDraw stream) atTop (𝓝 (uniformDraw stream)) :=
    tendsto_const_nhds
  have hbelow := hconst.sub hpower
  rw [sub_zero] at hbelow
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hbelow hconst (fun stage ↦ ?_)
    fun stage ↦ truncatedDraw_le_uniformDraw stage stream
  have hslack := uniformDraw_le_truncatedDraw_add stage stream
  show uniformDraw stream - (1 / 2 : ℝ) ^ stage ≤ truncatedDraw stage stream
  linarith

/-- A curve at the truncated draw is a function of the first bits of the stream. -/
theorem curve_truncatedDraw_eq (curve : ℝ → ℝ) (stage : ℕ) :
    (fun stream ↦ curve (truncatedDraw stage stream)) =
      fun stream ↦ (fun word ↦ curve (wordDraw stage word : ℝ)) (prefixOf stream stage) := by
  funext stream
  rw [← wordDraw_prefixOf]

/-- The expectation of a curve at a truncated draw is the left dyadic Riemann sum of the
curve. -/
theorem integral_truncatedDraw_curve (curve : ℝ → ℝ) (stage : ℕ) :
    ∫ stream, curve (truncatedDraw stage stream) ∂bitMeasure =
      ∑ index ∈ Finset.range (2 ^ stage),
        (1 / 2 : ℝ) ^ stage * curve ((index : ℝ) / 2 ^ stage) := by
  rw [curve_truncatedDraw_eq, integral_prefix stage fun word ↦ curve (wordDraw stage word : ℝ),
    sum_wordsOfLength_wordDraw stage fun draw ↦ (1 / 2 : ℝ) ^ stage * curve (draw : ℝ)]
  refine Finset.sum_congr rfl fun index _ ↦ ?_
  push_cast
  rfl

/-- NOTE2 §7.2: the expectation of a continuous decreasing curve at the uniform draw of the
fair-bit stream is its integral over the unit interval. -/
theorem integral_uniformDraw_of_antitoneOn (curve : ℝ → ℝ)
    (hantitone : AntitoneOn curve (Set.Icc 0 1))
    (hcontinuous : ContinuousOn curve (Set.Icc 0 1)) :
    ∫ stream, curve (uniformDraw stream) ∂bitMeasure = ∫ u in (0:ℝ)..1, curve u := by
  have hmember : ∀ stage stream, truncatedDraw stage stream ∈ Set.Icc (0:ℝ) 1 :=
    fun stage stream ↦ by
      obtain ⟨hbase, _, _, hceiling⟩ := draw_bracket stage stream
      have hpower : (0:ℝ) < (1 / 2) ^ stage := by positivity
      exact ⟨hbase, by linarith⟩
  have hdraw : ∀ stream, uniformDraw stream ∈ Set.Icc (0:ℝ) 1 := fun stream ↦ by
    obtain ⟨hbase, hbelow, hslack, hceiling⟩ := draw_bracket 0 stream
    exact ⟨le_trans hbase hbelow, by linarith⟩
  have hzero : (0:ℝ) ∈ Set.Icc (0:ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have hone : (1:ℝ) ∈ Set.Icc (0:ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have hbound : ∀ x ∈ Set.Icc (0:ℝ) 1, ‖curve x‖ ≤ |curve 0| + |curve 1| := fun x hx ↦ by
    have hbelowZero := hantitone hzero hx hx.1
    have haboveOne := hantitone hx hone hx.2
    have hzeroAbs := le_abs_self (curve 0)
    have honeAbs := neg_abs_le (curve 1)
    have hzeroNonneg := abs_nonneg (curve 0)
    have honeNonneg := abs_nonneg (curve 1)
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith
  have hlimit : ∀ᵐ stream ∂bitMeasure, Tendsto (fun stage ↦ curve (truncatedDraw stage stream))
      atTop (𝓝 (curve (uniformDraw stream))) := ae_of_all _ fun stream ↦ by
    have hwithin : Tendsto (fun stage ↦ truncatedDraw stage stream) atTop
        (𝓝[Set.Icc 0 1] uniformDraw stream) :=
      tendsto_nhdsWithin_iff.mpr
        ⟨tendsto_truncatedDraw stream, Eventually.of_forall fun stage ↦ hmember stage stream⟩
    exact (hcontinuous (uniformDraw stream) (hdraw stream)).tendsto.comp hwithin
  have hmeasurable : ∀ stage, AEStronglyMeasurable
      (fun stream ↦ curve (truncatedDraw stage stream)) bitMeasure := fun stage ↦ by
    rw [curve_truncatedDraw_eq]
    exact (measurable_prefix stage fun word ↦ curve (wordDraw stage word : ℝ)).aestronglyMeasurable
  have hdominated := tendsto_integral_of_dominated_convergence
    (fun _ ↦ |curve 0| + |curve 1|) hmeasurable (integrable_const _)
    (fun stage ↦ ae_of_all _ fun stream ↦ hbound _ (hmember stage stream)) hlimit
  simp only [integral_truncatedDraw_curve] at hdominated
  have hriemann := (tendsto_riemannSums (fun u ↦ -curve u) hantitone.neg).1
  simp only [intervalIntegral.integral_neg, mul_neg, Finset.sum_neg_distrib] at hriemann
  have hriemannNeg := hriemann.neg
  simp only [neg_neg] at hriemannNeg
  exact tendsto_nhds_unique hdominated hriemannNeg

/-! ### The exponential cap -/

/-- The exponential cap: the negative logarithm of its argument floored at `e^(-1)`, a
continuous decreasing curve equal to `min (-log u) 1` at every positive `u`. -/
def exponentialCap (u : ℝ) : ℝ :=
  -Real.log (max u (Real.exp (-1)))

/-- The floor `e^(-1)` is at most one. -/
theorem exp_neg_one_le_one : Real.exp (-1) ≤ 1 := by
  have hstep := Real.exp_le_exp.mpr (show (-1:ℝ) ≤ 0 by norm_num)
  rwa [Real.exp_zero] at hstep

/-- The floored argument is positive. -/
theorem max_exp_neg_one_pos (u : ℝ) : 0 < max u (Real.exp (-1)) :=
  lt_of_lt_of_le (Real.exp_pos (-1)) (le_max_right _ _)

/-- The exponential cap is continuous. -/
theorem exponentialCap_continuous : Continuous exponentialCap :=
  ((continuous_id.max continuous_const).log fun u ↦ (max_exp_neg_one_pos u).ne').neg

/-- The exponential cap is decreasing. -/
theorem exponentialCap_antitone : Antitone exponentialCap := fun first second hle ↦ by
  unfold exponentialCap
  exact neg_le_neg (Real.log_le_log (max_exp_neg_one_pos first) (max_le_max hle le_rfl))

/-- The exponential cap is at most one. -/
theorem exponentialCap_le_one (u : ℝ) : exponentialCap u ≤ 1 := by
  unfold exponentialCap
  have hfloor := Real.log_le_log (Real.exp_pos (-1)) (le_max_right u (Real.exp (-1)))
  rw [Real.log_exp] at hfloor
  linarith

/-- The exponential cap is nonnegative at every argument at most one. -/
theorem exponentialCap_nonneg {u : ℝ} (hle : u ≤ 1) : 0 ≤ exponentialCap u := by
  unfold exponentialCap
  have hceiling : max u (Real.exp (-1)) ≤ 1 := max_le hle exp_neg_one_le_one
  linarith [Real.log_nonpos (max_exp_neg_one_pos u).le hceiling]

/-- At every positive argument the exponential cap is the negative logarithm capped at one. -/
theorem exponentialCap_eq_min {u : ℝ} (hpos : 0 < u) : exponentialCap u = min (-Real.log u) 1 := by
  unfold exponentialCap
  rcases le_total u (Real.exp (-1)) with hle | hle
  · have hlog : Real.log u ≤ -1 := by
      have hstep := Real.log_le_log hpos hle
      rwa [Real.log_exp] at hstep
    rw [max_eq_right hle, Real.log_exp, neg_neg, min_eq_right (by linarith)]
  · have hlog : -1 ≤ Real.log u := by
      have hstep := Real.log_le_log (Real.exp_pos (-1)) hle
      rwa [Real.log_exp] at hstep
    rw [max_eq_left hle, min_eq_left (by linarith)]

/-- NOTE2 §7.2: the integral of the exponential cap over the unit interval is `1 - e^(-1)`. -/
theorem integral_exponentialCap : ∫ u in (0:ℝ)..1, exponentialCap u = 1 - Real.exp (-1) := by
  have hfloorPos : 0 < Real.exp (-1) := Real.exp_pos (-1)
  have hleft : ∫ u in (0:ℝ)..Real.exp (-1), exponentialCap u = Real.exp (-1) := by
    rw [intervalIntegral.integral_congr (g := fun _ ↦ (1:ℝ)) ?_, intervalIntegral.integral_const,
      smul_eq_mul, mul_one, sub_zero]
    intro u hu
    rw [Set.uIcc_of_le hfloorPos.le] at hu
    show exponentialCap u = 1
    unfold exponentialCap
    rw [max_eq_right hu.2, Real.log_exp, neg_neg]
  have hright : ∫ u in Real.exp (-1)..1, exponentialCap u = 1 - 2 * Real.exp (-1) := by
    rw [intervalIntegral.integral_congr (g := fun u ↦ -Real.log u) ?_,
      intervalIntegral.integral_neg, integral_log, Real.log_one, Real.log_exp]
    · ring
    · intro u hu
      rw [Set.uIcc_of_le exp_neg_one_le_one] at hu
      show exponentialCap u = -Real.log u
      unfold exponentialCap
      rw [max_eq_left hu.1]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (exponentialCap_continuous.intervalIntegrable 0 (Real.exp (-1)))
    (exponentialCap_continuous.intervalIntegrable (Real.exp (-1)) 1), hleft, hright]
  ring

/-! ### Rational enclosures of the negative logarithm -/

/-- NOTE2 (30): the partial sum of the logarithmic series, in any field. -/
def logLower {K : Type*} [Field K] (terms : ℕ) (rate : K) : K :=
  ∑ index ∈ Finset.range terms, (1 - rate) ^ (index + 1) / ((index : K) + 1)

/-- NOTE2 (30): the partial sum of the logarithmic series plus its tail bound, in any
field. -/
def logUpper {K : Type*} [Field K] (terms : ℕ) (rate : K) : K :=
  logLower terms rate + (1 - rate) ^ (terms + 1) / (((terms : K) + 1) * rate)

/-- The rational partial sum is the real partial sum at the rational point. -/
theorem cast_logLower (terms : ℕ) (rate : ℚ) :
    ((logLower terms rate : ℚ) : ℝ) = logLower terms (rate : ℝ) := by
  simp only [logLower, Rat.cast_sum, Rat.cast_div, Rat.cast_pow, Rat.cast_sub, Rat.cast_one,
    Rat.cast_add, Rat.cast_natCast]

/-- The rational enclosure is the real enclosure at the rational point. -/
theorem cast_logUpper (terms : ℕ) (rate : ℚ) :
    ((logUpper terms rate : ℚ) : ℝ) = logUpper terms (rate : ℝ) := by
  simp only [logUpper, Rat.cast_add, Rat.cast_div, Rat.cast_pow, Rat.cast_sub, Rat.cast_one,
    Rat.cast_mul, Rat.cast_natCast, cast_logLower]

/-- NOTE2 (30), lower half: the partial sum is below the negative logarithm. -/
theorem logLower_le_neg_log (terms : ℕ) {rate : ℝ} (hpos : 0 < rate) (hle : rate ≤ 1) :
    logLower terms rate ≤ -Real.log rate :=
  partial_sum_le_neg_log rate hpos hle terms

/-- NOTE2 (30), upper half: the negative logarithm is below the enclosure. -/
theorem neg_log_le_logUpper (terms : ℕ) {rate : ℝ} (hpos : 0 < rate) (hle : rate ≤ 1) :
    -Real.log rate ≤ logUpper terms rate := by
  have htail := neg_log_tail_bound rate hpos hle terms
  unfold logUpper logLower
  linarith

/-- The partial sum decreases in the point on the unit interval. -/
theorem logLower_antitone_rate (terms : ℕ) {first second : ℚ} (hle : first ≤ second)
    (hsecond : second ≤ 1) : logLower terms second ≤ logLower terms first :=
  Finset.sum_le_sum fun _ _ ↦ div_le_div_of_nonneg_right
    (pow_le_pow_left₀ (by linarith) (by linarith) _) (by positivity)

/-- The partial sum increases in the order on the unit interval. -/
theorem logLower_le_succ (terms : ℕ) {rate : ℚ} (hle : rate ≤ 1) :
    logLower terms rate ≤ logLower (terms + 1) rate := by
  unfold logLower
  rw [Finset.sum_range_succ]
  have hterm : (0:ℚ) ≤ (1 - rate) ^ (terms + 1) / ((terms : ℚ) + 1) :=
    div_nonneg (pow_nonneg (by linarith) _) (by positivity)
  linarith

/-- The enclosure decreases in the order at every point of the half-open unit interval. -/
theorem logUpper_succ_le (terms : ℕ) {rate : ℚ} (hpos : 0 < rate) (hle : rate ≤ 1) :
    logUpper (terms + 1) rate ≤ logUpper terms rate := by
  have hsplit : logLower (terms + 1) rate =
      logLower terms rate + (1 - rate) ^ (terms + 1) / ((terms : ℚ) + 1) := by
    unfold logLower
    rw [Finset.sum_range_succ]
  have hdeficit : (0:ℚ) ≤ 1 - rate := by linarith
  have hpower : (0:ℚ) ≤ (1 - rate) ^ (terms + 1) := pow_nonneg hdeficit _
  have horder : (0:ℚ) < (terms : ℚ) + 1 := by positivity
  have hkey : (1 - rate) ^ (terms + 1) / ((terms : ℚ) + 1) +
      (1 - rate) ^ (terms + 1 + 1) / (((terms : ℚ) + 1 + 1) * rate) ≤
      (1 - rate) ^ (terms + 1) / (((terms : ℚ) + 1) * rate) := by
    rw [pow_succ (1 - rate) (terms + 1), div_add_div _ _ horder.ne' (by positivity),
      div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_nonneg (mul_nonneg (mul_nonneg hpower horder.le) hpos.le) hdeficit,
      mul_nonneg (mul_nonneg hpower horder.le) hpos.le]
  unfold logUpper
  rw [hsplit]
  push_cast
  linarith

/-- The enclosure decreases in the point on the half-open unit interval. -/
theorem logUpper_antitone_rate (terms : ℕ) {first second : ℚ} (hpos : 0 < first)
    (hle : first ≤ second) (hsecond : second ≤ 1) :
    logUpper terms second ≤ logUpper terms first := by
  have hsecondPos : 0 < second := lt_of_lt_of_le hpos hle
  have hlower := logLower_antitone_rate terms hle hsecond
  have hnumerator : (1 - second) ^ (terms + 1) ≤ (1 - first) ^ (terms + 1) :=
    pow_le_pow_left₀ (by linarith) (by linarith) _
  have horder : (0:ℚ) < (terms : ℚ) + 1 := by positivity
  have hproduct : (1 - second) ^ (terms + 1) * first ≤ (1 - first) ^ (terms + 1) * second :=
    mul_le_mul hnumerator hle hpos.le (pow_nonneg (by linarith) _)
  have htail : (1 - second) ^ (terms + 1) / (((terms : ℚ) + 1) * second) ≤
      (1 - first) ^ (terms + 1) / (((terms : ℚ) + 1) * first) := by
    rw [div_le_div_iff₀ (mul_pos horder hsecondPos) (mul_pos horder hpos)]
    nlinarith [mul_le_mul_of_nonneg_left hproduct horder.le]
  unfold logUpper
  linarith

/-! ### The cylinder evaluator of the exponential cap -/

/-- The rational lower value of the exponential cap on the cylinder of a word: the partial sum
of the logarithmic series at the right end of the cylinder, capped at one. -/
def capLower (stage : ℕ) (word : List Bool) : ℚ :=
  min (logLower stage (wordDraw stage word + (1 / 2) ^ stage)) 1

/-- The rational upper value of the exponential cap on the cylinder of a word: the enclosure of
the negative logarithm at the left end of the cylinder, capped at one, and one on the first
cylinder. -/
def capUpper (stage : ℕ) (word : List Bool) : ℚ :=
  if wordDraw stage word = 0 then 1 else min (logUpper stage (wordDraw stage word)) 1

/-- The lower value bounds the exponential cap at every point up to the right end of the
cylinder. -/
theorem capLower_le (stage : ℕ) (word : List Bool) {u : ℝ}
    (hu : u ≤ ((wordDraw stage word + (1 / 2) ^ stage : ℚ) : ℝ)) :
    (capLower stage word : ℝ) ≤ exponentialCap u := by
  have hpositive : (0:ℚ) < wordDraw stage word + (1 / 2) ^ stage :=
    add_pos_of_nonneg_of_pos (wordDraw_nonneg stage word) (by positivity)
  have hceiling := wordDraw_add_le_one stage word
  have hpositiveReal : (0:ℝ) < ((wordDraw stage word + (1 / 2) ^ stage : ℚ) : ℝ) := by
    exact_mod_cast hpositive
  have hceilingReal : ((wordDraw stage word + (1 / 2) ^ stage : ℚ) : ℝ) ≤ 1 := by
    exact_mod_cast hceiling
  rw [capLower, Rat.cast_min, Rat.cast_one, cast_logLower]
  calc min (logLower stage ((wordDraw stage word + (1 / 2) ^ stage : ℚ) : ℝ)) 1
      ≤ min (-Real.log ((wordDraw stage word + (1 / 2) ^ stage : ℚ) : ℝ)) 1 :=
        min_le_min_right 1 (logLower_le_neg_log stage hpositiveReal hceilingReal)
    _ = exponentialCap ((wordDraw stage word + (1 / 2) ^ stage : ℚ) : ℝ) :=
        (exponentialCap_eq_min hpositiveReal).symm
    _ ≤ exponentialCap u := exponentialCap_antitone hu

/-- The upper value bounds the exponential cap at every point from the left end of the
cylinder. -/
theorem le_capUpper (stage : ℕ) (word : List Bool) {u : ℝ}
    (hu : (wordDraw stage word : ℝ) ≤ u) :
    exponentialCap u ≤ (capUpper stage word : ℝ) := by
  unfold capUpper
  split_ifs with hzero
  · rw [Rat.cast_one]
    exact exponentialCap_le_one u
  · have hpositive : (0:ℚ) < wordDraw stage word :=
      lt_of_le_of_ne (wordDraw_nonneg stage word) (Ne.symm hzero)
    have hle : wordDraw stage word ≤ 1 := by
      have hceiling := wordDraw_add_le_one stage word
      have hpower : (0:ℚ) < (1 / 2) ^ stage := by positivity
      linarith
    have hpositiveReal : (0:ℝ) < (wordDraw stage word : ℝ) := by exact_mod_cast hpositive
    have hleReal : (wordDraw stage word : ℝ) ≤ 1 := by exact_mod_cast hle
    rw [Rat.cast_min, Rat.cast_one, cast_logUpper]
    calc exponentialCap u ≤ exponentialCap (wordDraw stage word : ℝ) := exponentialCap_antitone hu
      _ = min (-Real.log (wordDraw stage word : ℝ)) 1 := exponentialCap_eq_min hpositiveReal
      _ ≤ min (logUpper stage (wordDraw stage word : ℝ)) 1 :=
          min_le_min_right 1 (neg_log_le_logUpper stage hpositiveReal hleReal)

/-- Capping at one does not increase a difference. -/
theorem min_one_sub_min_one_le {first second : ℝ} (hle : second ≤ first) :
    min first 1 - min second 1 ≤ first - second := by
  rcases le_total first 1 with hfirst | hfirst <;>
    rcases le_total second 1 with hsecond | hsecond <;>
    simp only [min_eq_left, min_eq_right, hfirst, hsecond] <;> linarith

/-- The tail bound of the logarithmic series at a point at least `floor` is at most one over
the order plus one times `floor`. -/
theorem tail_le (terms : ℕ) {rate floor : ℝ} (hfloor : 0 < floor) (hrate : floor ≤ rate)
    (hle : rate ≤ 1) :
    (1 - rate) ^ (terms + 1) / (((terms : ℝ) + 1) * rate) ≤ 1 / (((terms : ℝ) + 1) * floor) := by
  have hpower : (1 - rate) ^ (terms + 1) ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
  have hratePos : 0 < rate := lt_of_lt_of_le hfloor hrate
  calc (1 - rate) ^ (terms + 1) / (((terms : ℝ) + 1) * rate)
      ≤ 1 / (((terms : ℝ) + 1) * rate) := div_le_div_of_nonneg_right hpower (by positivity)
    _ ≤ 1 / (((terms : ℝ) + 1) * floor) :=
        one_div_le_one_div_of_le (by positivity) (by gcongr)

/-- NOTE2 §7.2, the width of the exponential cap certificate: at a positive left end `a` at
least `floor`, the enclosure at `a` minus the partial sum at `a + 2^(-stage)` is at most twice
the tail over `floor` plus `2^(-stage) / floor`. -/
theorem exponentialWidth_le (stage : ℕ) {left floor : ℝ} (hfloor : 0 < floor)
    (hleft : floor ≤ left) (hright : left + (1 / 2) ^ stage ≤ 1) :
    logUpper stage left - logLower stage (left + (1 / 2) ^ stage) ≤
      2 / (((stage : ℝ) + 1) * floor) + (1 / 2) ^ stage / floor := by
  have hleftPos : 0 < left := lt_of_lt_of_le hfloor hleft
  have hpower : (0:ℝ) < (1 / 2) ^ stage := by positivity
  have hleftLe : left ≤ 1 := by linarith
  have hrightPos : 0 < left + (1 / 2) ^ stage := by linarith
  have hlowerLeft := logLower_le_neg_log stage hleftPos hleftLe
  have htailRight := neg_log_tail_bound (left + (1 / 2) ^ stage) hrightPos hright stage
  have htailLeftBound := tail_le stage hfloor hleft hleftLe
  have htailRightBound := tail_le stage hfloor (by linarith) hright
  have hlogIncrement : Real.log (left + (1 / 2) ^ stage) - Real.log left ≤
      (1 / 2) ^ stage / floor := by
    rw [← Real.log_div hrightPos.ne' hleftPos.ne']
    calc Real.log ((left + (1 / 2) ^ stage) / left)
        ≤ (left + (1 / 2) ^ stage) / left - 1 := Real.log_le_sub_one_of_pos (by positivity)
      _ = (1 / 2) ^ stage / left := by
          field_simp
          ring
      _ ≤ (1 / 2) ^ stage / floor := div_le_div_of_nonneg_left hpower.le hfloor hleft
  have hsplit : logUpper stage left = logLower stage left +
      (1 - left) ^ (stage + 1) / (((stage : ℝ) + 1) * left) := rfl
  have htwo : 2 / (((stage : ℝ) + 1) * floor) =
      1 / (((stage : ℝ) + 1) * floor) + 1 / (((stage : ℝ) + 1) * floor) := by ring
  unfold logLower at htailRight
  rw [hsplit, htwo]
  unfold logLower
  unfold logLower at hlowerLeft
  linarith

/-- The first `stage` digits of a stream bound its truncated draw from below by the place value
of any true bit among them. -/
theorem placeValue_le_truncatedDraw {stream : ℕ → Bool} {index stage : ℕ}
    (hindex : stream index = true) (hstage : index < stage) :
    (1 / 2 : ℝ) ^ (index + 1) ≤ truncatedDraw stage stream := by
  have hdigit : binaryDigit stream index = (1 / 2 : ℝ) ^ (index + 1) := by
    simp [binaryDigit, hindex]
  rw [← hdigit]
  exact Finset.single_le_sum (f := binaryDigit stream)
    (fun other _ ↦ binaryDigit_nonneg stream other) (Finset.mem_range.mpr hstage)

/-- NOTE2 Theorem 5 for the exponential draw: the cylinder evaluator of the exponential cap at
the uniform draw, with rational values from the logarithmic series. -/
def exponentialEvaluator : CylinderEvaluator fun stream ↦ exponentialCap (uniformDraw stream) where
  depth := fun stage ↦ stage
  lower := capLower
  upper := capUpper
  depth_mono := monotone_id
  lower_le := fun stage word hlength stream hstream ↦ by
    have hprefix := (mem_cylinder_iff_prefixOf_eq hlength stream).mp hstream
    obtain ⟨_, _, hslack, _⟩ := draw_bracket stage stream
    rw [← wordDraw_prefixOf, hprefix] at hslack
    exact capLower_le stage word (by push_cast; exact hslack)
  le_upper := fun stage word hlength stream hstream ↦ by
    have hprefix := (mem_cylinder_iff_prefixOf_eq hlength stream).mp hstream
    obtain ⟨_, hbelow, _, _⟩ := draw_bracket stage stream
    rw [← wordDraw_prefixOf, hprefix] at hbelow
    exact le_capUpper stage word hbelow
  lower_nested := fun stage word hlength ↦ by
    have hstep : wordDraw (stage + 1) word + (1 / 2) ^ (stage + 1) ≤
        wordDraw stage (word.take stage) + (1 / 2) ^ stage :=
      uniformEvaluator.upper_nested stage word hlength
    show capLower stage (word.take stage) ≤ capLower (stage + 1) word
    unfold capLower
    refine min_le_min_right 1 ?_
    calc logLower stage (wordDraw stage (word.take stage) + (1 / 2) ^ stage)
        ≤ logLower stage (wordDraw (stage + 1) word + (1 / 2) ^ (stage + 1)) :=
          logLower_antitone_rate stage hstep (wordDraw_add_le_one stage (word.take stage))
      _ ≤ logLower (stage + 1) (wordDraw (stage + 1) word + (1 / 2) ^ (stage + 1)) :=
          logLower_le_succ stage (wordDraw_add_le_one (stage + 1) word)
  upper_nested := fun stage word hlength ↦ by
    have hstep : wordDraw stage (word.take stage) ≤ wordDraw (stage + 1) word :=
      uniformEvaluator.lower_nested stage word hlength
    show capUpper (stage + 1) word ≤ capUpper stage (word.take stage)
    unfold capUpper
    by_cases hparent : wordDraw stage (word.take stage) = 0
    · rw [if_pos hparent]
      split_ifs
      · exact le_rfl
      · exact min_le_right _ _
    · have hparentPos : 0 < wordDraw stage (word.take stage) :=
        lt_of_le_of_ne (wordDraw_nonneg _ _) (Ne.symm hparent)
      have hchildPos : 0 < wordDraw (stage + 1) word := lt_of_lt_of_le hparentPos hstep
      have hchildLe : wordDraw (stage + 1) word ≤ 1 := by
        have hceiling := wordDraw_add_le_one (stage + 1) word
        have hpower : (0:ℚ) < (1 / 2) ^ (stage + 1) := by positivity
        linarith
      rw [if_neg hparent, if_neg hchildPos.ne']
      refine min_le_min_right 1 ?_
      calc logUpper (stage + 1) (wordDraw (stage + 1) word)
          ≤ logUpper stage (wordDraw (stage + 1) word) :=
            logUpper_succ_le stage hchildPos hchildLe
        _ ≤ logUpper stage (wordDraw stage (word.take stage)) :=
            logUpper_antitone_rate stage hparentPos hstep hchildLe
  width_ae := by
    filter_upwards [ae_exists_true] with stream htrue
    obtain ⟨index, hindex⟩ := htrue
    have hfloor : (0:ℝ) < (1 / 2) ^ (index + 1) := by positivity
    have hmajorant : Tendsto (fun stage : ℕ ↦ 2 / (((stage : ℝ) + 1) * (1 / 2) ^ (index + 1)) +
        (1 / 2 : ℝ) ^ stage / (1 / 2) ^ (index + 1)) atTop (𝓝 0) := by
      have hharmonic := (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul 2).div_const
        ((1 / 2 : ℝ) ^ (index + 1))
      have hpower := (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num)
        (by norm_num)).div_const ((1 / 2 : ℝ) ^ (index + 1))
      have hsum := hharmonic.add hpower
      rw [mul_zero, zero_div, add_zero] at hsum
      refine hsum.congr fun stage ↦ ?_
      rw [mul_one_div, div_div]
    have hconst : Tendsto (fun _ : ℕ ↦ (0:ℝ)) atTop (𝓝 0) := tendsto_const_nhds
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hconst hmajorant ?_ ?_
    · refine Eventually.of_forall fun stage ↦ ?_
      have hlow := capLower_le stage (prefixOf stream stage) (u := uniformDraw stream) (by
        push_cast
        rw [wordDraw_prefixOf]
        exact (draw_bracket stage stream).2.2.1)
      have hhigh := le_capUpper stage (prefixOf stream stage) (u := uniformDraw stream) (by
        rw [wordDraw_prefixOf]
        exact (draw_bracket stage stream).2.1)
      show (0:ℝ) ≤ (capUpper stage (prefixOf stream stage) : ℝ) -
        (capLower stage (prefixOf stream stage) : ℝ)
      linarith
    · filter_upwards [eventually_gt_atTop index] with stage hstage
      have hleft := placeValue_le_truncatedDraw hindex hstage
      obtain ⟨_, _, _, hceiling⟩ := draw_bracket stage stream
      have hdrawPos : (0:ℚ) < wordDraw stage (prefixOf stream stage) := by
        have hreal : (0:ℝ) < (wordDraw stage (prefixOf stream stage) : ℝ) := by
          rw [wordDraw_prefixOf]
          linarith
        exact_mod_cast hreal
      have hwidth := exponentialWidth_le stage hfloor hleft hceiling
      have hupperLower : logLower stage (truncatedDraw stage stream + (1 / 2) ^ stage) ≤
          logUpper stage (truncatedDraw stage stream) := by
        have hpower : (0:ℝ) < (1 / 2) ^ stage := by positivity
        have hleftPos : 0 < truncatedDraw stage stream := lt_of_lt_of_le hfloor hleft
        linarith [logLower_le_neg_log stage (by linarith) hceiling,
          neg_log_le_logUpper stage hleftPos (by linarith),
          Real.log_le_log hleftPos (le_add_of_nonneg_right hpower.le)]
      show (capUpper stage (prefixOf stream stage) : ℝ) -
          (capLower stage (prefixOf stream stage) : ℝ) ≤
        2 / (((stage : ℝ) + 1) * (1 / 2) ^ (index + 1)) +
          (1 / 2 : ℝ) ^ stage / (1 / 2) ^ (index + 1)
      rw [capUpper, if_neg hdrawPos.ne', capLower, Rat.cast_min, Rat.cast_min, Rat.cast_one,
        cast_logUpper, cast_logLower]
      push_cast
      rw [wordDraw_prefixOf]
      exact le_trans (min_one_sub_min_one_le hupperLower) hwidth

/-! ### The certified expectation -/

/-- The exact expectation of the exponential cap at the uniform draw is `1 - e^(-1)`. -/
theorem integral_exponentialCap_uniformDraw :
    ∫ stream, exponentialCap (uniformDraw stream) ∂bitMeasure = 1 - Real.exp (-1) := by
  rw [integral_uniformDraw_of_antitoneOn exponentialCap (exponentialCap_antitone.antitoneOn _)
    exponentialCap_continuous.continuousOn, integral_exponentialCap]

/-- NOTE2 §7.2, executed Theorem 5 for the exponential draw: at every stage the rational
certificates of the exponential cap bracket its exact expectation `1 - e^(-1)`. -/
theorem exponential_certificate (stage : ℕ) :
    (exponentialEvaluator.lowerSum stage : ℝ) ≤ 1 - Real.exp (-1) ∧
      1 - Real.exp (-1) ≤ (exponentialEvaluator.upperSum stage : ℝ) := by
  rw [← integral_exponentialCap_uniformDraw]
  exact ⟨exponentialEvaluator.lowerSum_le_integral stage,
    exponentialEvaluator.integral_le_upperSum stage⟩

/-- NOTE2 §7.2, executed Theorem 5 for the exponential draw: the rational certificates of the
exponential cap converge to `1 - e^(-1)`. -/
theorem tendsto_exponential_certificate :
    Tendsto (fun stage ↦ (exponentialEvaluator.lowerSum stage : ℝ)) atTop
        (𝓝 (1 - Real.exp (-1))) ∧
      Tendsto (fun stage ↦ (exponentialEvaluator.upperSum stage : ℝ)) atTop
        (𝓝 (1 - Real.exp (-1))) := by
  rw [← integral_exponentialCap_uniformDraw]
  exact ⟨exponentialEvaluator.tendsto_lowerSum, exponentialEvaluator.tendsto_upperSum⟩

/-- The exponential draw encoded by a fair-bit stream: the negative logarithm of its uniform
draw. -/
def exponentialDraw (stream : ℕ → Bool) : ℝ :=
  -Real.log (uniformDraw stream)

/-- NOTE2 §7.2: the expectation of the bounded integrand `min X 1` of the exponential draw is
`1 - e^(-1)`, the certified value. -/
theorem integral_min_exponentialDraw :
    ∫ stream, min (exponentialDraw stream) 1 ∂bitMeasure = 1 - Real.exp (-1) := by
  rw [← integral_exponentialCap_uniformDraw]
  refine integral_congr_ae ?_
  filter_upwards [ae_exists_true] with stream htrue
  exact (exponentialCap_eq_min (uniformDraw_pos htrue)).symm

end

end Descent.Portability.CylinderExponentialDraw
