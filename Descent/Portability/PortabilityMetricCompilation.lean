/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.ReplicaMetricInstances
import Descent.Portability.PortabilityRatioQueries
import Descent.Portability.RealizationBody
import Mathlib.Data.Matrix.Mul

assert_below Descent.Decision Descent.Program

/-!
# The metric side of the end-to-end portability law

Research front F8 states the end-to-end law as `portability = Φ(U_history · H(x₀))`: a
demographic history propagates the initial configuration moments, and a metric compilation `Φ`
reads the portability metrics off the propagated moments. This module is `Φ`.

## The compilation

A score `S` and an outcome `Y` enter through five second-moment coordinates
`m = (E S, E Y, E S², E S Y, E Y²)` (`SecondMoments`, `momentsOf`); for a panel these are linear
readouts of the budget-2 configuration moments. On them the variances, the covariance and the
metrics are explicit rational functions, `V_S = m₂ - m₀²`, `V_Y = m₄ - m₁²`, `C = m₃ - m₀ m₁`,
`R² = C² / (V_S V_Y)` and `slope = C / V_S`, and the portability ratio of `R²` from a source to
a target is `R²_t / R²_s` (`compiledSquaredCorrelation`, `compiledSlope`,
`compiledPortabilityRatio`). These are the corpus metrics.
`FiniteReportLaw.squaredCorrelation` is `some` of the compiled `R²` exactly when both compiled
variances are positive, and `none` otherwise (`squaredCorrelation_eq_compiled`). The calibration
slope behaves the same way (`calibrationSlope_eq_compiled`). The compiled ratio is
`PortabilityRatioQueries.portabilityRatio` of the four budget-4 accumulators
`correlationNumerator` and `correlationDenominator` of `ReplicaMetricInstances`
(`compiledPortabilityRatio_eq_portabilityRatio`).

## Definedness, positivity and continuity

`definedRegion`, where both compiled variances are positive, is open (`isOpen_definedRegion`).
The compiled `R²` is continuous on it (`continuousOn_compiledSquaredCorrelation`), the slope is
continuous where the score variance is positive (`continuousOn_compiledSlope`), and the ratio is
continuous where both laws are in the region and the source `R²` is positive
(`continuousOn_compiledPortabilityRatio`).

## Lipschitz constants

Take every coordinate in `[0, 1]`, as for `[0, 1]`-valued scores and outcomes, both variances at
least `ε > 0`, and the coordinate `ℓ¹` distance `momentDistance`. Then the slope is
`3 / ε²`-Lipschitz (`abs_compiledSlope_sub_le`) and `R²` is `6 / ε⁴`-Lipschitz
(`abs_compiledSquaredCorrelation_sub_le`). Where the source `R²` is at least `δ > 0`, the
portability ratio moves by at most `6 (d_s + d_t) / (ε⁶ δ²)`
(`abs_compiledPortabilityRatio_sub_le`). The budget-4 guarded ratio `N / D` is `1 / ε`-Lipschitz
where `D ≥ ε` and `|N| ≤ D` (`abs_guardedRatio_sub_le`), and `|N| ≤ D` holds for every law by
Cauchy–Schwarz (`abs_correlationNumerator_le_denominator`).

## On the realization body

The moment side supplies a vector `v : ι → ℝ` in the realization body of a feature map, and `Φ`
reads it through a coefficient matrix, `readout A v c = Σ_i A c i v i` (`readout`). The readout
multiplies the `ℓ¹` distance by at most `5 a` when every coefficient is at most `a` in absolute
value (`momentDistance_readout_le`). When every feature reads into the unit cube, so does every
point of the body, since the cube is convex and the readout is linear
(`readout_mem_cube_of_mem_realizationBody`). So `Φ ∘ readout` is Lipschitz on the body with the
constants above times `5 a` (`abs_compiledSquaredCorrelation_readout_sub_le`,
`abs_compiledSlope_readout_sub_le`).

## The cross ratio of the end-to-end law

`EndToEndPortabilityLaw` writes the portability ratio on propagated moments `v` as
`(a·v)(b·v) / ((c·v)(d·v))`, where `a`, `b`, `c`, `d` are the coefficient vectors of the target
numerator, the source denominator, the target denominator and the source numerator. It is
`PortabilityRatioQueries.portabilityRatio` of these four accumulators, with a positive
denominator, where the source numerator and both denominators are positive
(`crossRatio_eq_portabilityRatio`). For a feature map bounded by `B` coordinatewise, every point
of its realization body is bounded by `B` (`abs_apply_le_of_mem_realizationBody`), so
`|c·v| ≤ ‖c‖₁ B` and `|c·v - c·v'| ≤ ‖c‖₁ ‖v - v'‖` (`abs_dotProduct_le`,
`abs_dotProduct_sub_le`). Where `c·v` and `d·v` are at least `δ > 0`, the ratio is Lipschitz in
the sup distance with constant `4 B³ ‖a‖₁ ‖b‖₁ ‖c‖₁ ‖d‖₁ / δ⁴` (`abs_crossRatio_sub_le`).

Scope. The coordinates enter as a readout of the moment vector, so this module does not fix the
configuration indexing of the moment side. The constants are the ones this proof yields, not
optimal ones.

## Empirical status

None. The bodies here are identities and inequalities between rational functions of five real
coordinates, so no measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.PortabilityMetricCompilation

open Descent.Portability.ReplicaMetricInstances (correlationNumerator correlationDenominator)

noncomputable section

/-! ## The compiled metrics -/

/-- The five second-moment coordinates `(E S, E Y, E S², E S Y, E Y²)` of a score and an
outcome. -/
abbrev SecondMoments := Fin 5 → ℝ

variable {Ω : Type*} [Fintype Ω]

/-- The second-moment coordinates of a score and an outcome under a finite law. -/
def momentsOf (p : FiniteReportLaw Ω) (score outcome : Ω → ℝ) : SecondMoments :=
  ![p.expectation score, p.expectation outcome, p.expectation (fun s ↦ score s ^ 2),
    p.expectation (fun s ↦ score s * outcome s), p.expectation (fun s ↦ outcome s ^ 2)]

/-- The compiled score variance `V_S = m₂ - m₀²`. -/
def scoreVariance (m : SecondMoments) : ℝ := m 2 - m 0 ^ 2

/-- The compiled outcome variance `V_Y = m₄ - m₁²`. -/
def outcomeVariance (m : SecondMoments) : ℝ := m 4 - m 1 ^ 2

/-- The compiled covariance `C = m₃ - m₀ m₁`. -/
def scoreOutcomeCovariance (m : SecondMoments) : ℝ := m 3 - m 0 * m 1

/-- The compiled squared correlation `R² = C² / (V_S V_Y)`. -/
def compiledSquaredCorrelation (m : SecondMoments) : ℝ :=
  scoreOutcomeCovariance m ^ 2 / (scoreVariance m * outcomeVariance m)

/-- The compiled calibration slope `C / V_S`. -/
def compiledSlope (m : SecondMoments) : ℝ := scoreOutcomeCovariance m / scoreVariance m

/-- The compiled portability ratio of the squared correlation, target over source. -/
def compiledPortabilityRatio (source target : SecondMoments) : ℝ :=
  compiledSquaredCorrelation target / compiledSquaredCorrelation source

/-- The coordinate `ℓ¹` distance between two second-moment vectors. -/
def momentDistance (m m' : SecondMoments) : ℝ := ∑ c, |m c - m' c|

/-- The compiled score variance of a law is its score variance. -/
theorem scoreVariance_momentsOf (p : FiniteReportLaw Ω) (score outcome : Ω → ℝ) :
    scoreVariance (momentsOf p score outcome) = p.variance score :=
  (p.variance_eq_rawMoments score).symm

/-- The compiled outcome variance of a law is its outcome variance. -/
theorem outcomeVariance_momentsOf (p : FiniteReportLaw Ω) (score outcome : Ω → ℝ) :
    outcomeVariance (momentsOf p score outcome) = p.variance outcome :=
  (p.variance_eq_rawMoments outcome).symm

/-- The compiled covariance of a law is its covariance. -/
theorem scoreOutcomeCovariance_momentsOf (p : FiniteReportLaw Ω) (score outcome : Ω → ℝ) :
    scoreOutcomeCovariance (momentsOf p score outcome) = p.covariance score outcome :=
  (p.covariance_eq_rawMoments score outcome).symm

/-- **The compilation of `R²`.** The corpus squared correlation of a finite law is the compiled
`R²` of its second-moment coordinates, defined exactly when both compiled variances are
positive. -/
theorem squaredCorrelation_eq_compiled (p : FiniteReportLaw Ω) (score outcome : Ω → ℝ) :
    p.squaredCorrelation score outcome =
      if 0 < scoreVariance (momentsOf p score outcome) ∧
          0 < outcomeVariance (momentsOf p score outcome) then
        some (compiledSquaredCorrelation (momentsOf p score outcome))
      else none := by
  unfold FiniteReportLaw.squaredCorrelation compiledSquaredCorrelation
  rw [scoreVariance_momentsOf, outcomeVariance_momentsOf, scoreOutcomeCovariance_momentsOf]

/-- **The compilation of the calibration slope.** The corpus calibration slope of a finite law
is the compiled slope of its second-moment coordinates, defined exactly when the compiled score
variance is positive. -/
theorem calibrationSlope_eq_compiled (p : FiniteReportLaw Ω) (score outcome : Ω → ℝ) :
    p.calibrationSlope score outcome =
      if 0 < scoreVariance (momentsOf p score outcome) then
        some (compiledSlope (momentsOf p score outcome))
      else none := by
  unfold FiniteReportLaw.calibrationSlope compiledSlope
  rw [scoreVariance_momentsOf, scoreOutcomeCovariance_momentsOf]

/-- **The compilation of the portability ratio.** The compiled ratio of a source and a target
law is `PortabilityRatioQueries.portabilityRatio` of the budget-4 correlation numerators and
denominators of the two laws. -/
theorem compiledPortabilityRatio_eq_portabilityRatio (source target : FiniteReportLaw Ω)
    (score outcome : Ω → ℝ) :
    compiledPortabilityRatio (momentsOf source score outcome) (momentsOf target score outcome) =
      PortabilityRatioQueries.portabilityRatio
        (fun _ : Unit ↦ correlationNumerator source score outcome)
        (fun _ ↦ correlationDenominator source score outcome)
        (fun _ ↦ correlationNumerator target score outcome)
        (fun _ ↦ correlationDenominator target score outcome) () := by
  unfold compiledPortabilityRatio compiledSquaredCorrelation
    PortabilityRatioQueries.portabilityRatio correlationNumerator correlationDenominator
  rw [scoreVariance_momentsOf, outcomeVariance_momentsOf, scoreOutcomeCovariance_momentsOf,
    scoreVariance_momentsOf, outcomeVariance_momentsOf, scoreOutcomeCovariance_momentsOf,
    mul_div_mul_left _ _ (by norm_num : (16 : ℝ) ≠ 0),
    mul_div_mul_left _ _ (by norm_num : (16 : ℝ) ≠ 0)]

/-! ## Definedness and continuity -/

/-- The region where both compiled variances are positive, on which the compiled `R²` is
defined. -/
def definedRegion : Set SecondMoments := {m | 0 < scoreVariance m ∧ 0 < outcomeVariance m}

theorem continuous_scoreVariance : Continuous scoreVariance := by
  show Continuous fun m : SecondMoments ↦ m 2 - m 0 ^ 2
  fun_prop

theorem continuous_outcomeVariance : Continuous outcomeVariance := by
  show Continuous fun m : SecondMoments ↦ m 4 - m 1 ^ 2
  fun_prop

theorem continuous_scoreOutcomeCovariance : Continuous scoreOutcomeCovariance := by
  show Continuous fun m : SecondMoments ↦ m 3 - m 0 * m 1
  fun_prop

/-- The definedness region is open. -/
theorem isOpen_definedRegion : IsOpen definedRegion := by
  have h1 : IsOpen {m : SecondMoments | 0 < scoreVariance m} :=
    isOpen_lt continuous_const continuous_scoreVariance
  have h2 : IsOpen {m : SecondMoments | 0 < outcomeVariance m} :=
    isOpen_lt continuous_const continuous_outcomeVariance
  exact h1.inter h2

/-- The compiled `R²` is continuous on its definedness region. -/
theorem continuousOn_compiledSquaredCorrelation :
    ContinuousOn compiledSquaredCorrelation definedRegion :=
  (continuous_scoreOutcomeCovariance.pow 2).continuousOn.div
    (continuous_scoreVariance.mul continuous_outcomeVariance).continuousOn
    fun _ hm ↦ (mul_pos hm.1 hm.2).ne'

/-- The compiled slope is continuous where the compiled score variance is positive. -/
theorem continuousOn_compiledSlope :
    ContinuousOn compiledSlope {m | 0 < scoreVariance m} :=
  continuous_scoreOutcomeCovariance.continuousOn.div continuous_scoreVariance.continuousOn
    fun _ hm ↦ ne_of_gt hm

/-- The compiled portability ratio is continuous where both laws are in the definedness region
and the source `R²` is positive. -/
theorem continuousOn_compiledPortabilityRatio :
    ContinuousOn (fun mm : SecondMoments × SecondMoments ↦ compiledPortabilityRatio mm.1 mm.2)
      {mm | mm.1 ∈ definedRegion ∧ 0 < compiledSquaredCorrelation mm.1 ∧
        mm.2 ∈ definedRegion} := by
  have ht : ContinuousOn (fun mm : SecondMoments × SecondMoments ↦
      compiledSquaredCorrelation mm.2)
      {mm | mm.1 ∈ definedRegion ∧ 0 < compiledSquaredCorrelation mm.1 ∧
        mm.2 ∈ definedRegion} :=
    continuousOn_compiledSquaredCorrelation.comp continuous_snd.continuousOn
      fun _ hmm ↦ hmm.2.2
  have hs : ContinuousOn (fun mm : SecondMoments × SecondMoments ↦
      compiledSquaredCorrelation mm.1)
      {mm | mm.1 ∈ definedRegion ∧ 0 < compiledSquaredCorrelation mm.1 ∧
        mm.2 ∈ definedRegion} :=
    continuousOn_compiledSquaredCorrelation.comp continuous_fst.continuousOn
      fun _ hmm ↦ hmm.1
  exact ht.div hs fun _ hmm ↦ hmm.2.1.ne'

/-! ## Scalar quotient bounds -/

private theorem abs_sub_le_abs_add_abs (a b : ℝ) : |a - b| ≤ |a| + |b| := by
  have h := abs_add_le a (-b)
  rwa [abs_neg, ← sub_eq_add_neg] at h

private theorem abs_mul_sub_mul_le_split (a a' b b' : ℝ) :
    |a * b - a' * b'| ≤ |a - a'| * |b| + |a'| * |b - b'| := by
  have h : a * b - a' * b' = (a - a') * b + a' * (b - b') := by ring
  rw [h, ← abs_mul, ← abs_mul]
  exact abs_add_le _ _

/-- **The quotient bound.** For denominators at least `ε > 0`, the second denominator at most
`K` and the second numerator at most `L` in absolute value,
`|n/d - n'/d'| ≤ (K |n - n'| + L |d - d'|) / ε²`. -/
theorem abs_div_sub_div_le (n n' : ℝ) {d d' ε K L : ℝ} (hε : 0 < ε) (hd : ε ≤ d)
    (hd' : ε ≤ d') (hK : d' ≤ K) (hL : |n'| ≤ L) :
    |n / d - n' / d'| ≤ (K * |n - n'| + L * |d - d'|) / ε ^ 2 := by
  have hdpos : 0 < d := hε.trans_le hd
  have hd'pos : 0 < d' := hε.trans_le hd'
  have hid : n / d - n' / d' = ((n - n') * d' + n' * (d' - d)) / (d * d') := by
    rw [div_sub_div _ _ hdpos.ne' hd'pos.ne']
    congr 1
    ring
  have hnum : |(n - n') * d' + n' * (d' - d)| ≤ K * |n - n'| + L * |d - d'| := by
    calc |(n - n') * d' + n' * (d' - d)| ≤ |(n - n') * d'| + |n' * (d' - d)| := abs_add_le _ _
      _ = |n - n'| * d' + |n'| * |d - d'| := by
          rw [abs_mul, abs_mul, abs_of_pos hd'pos, abs_sub_comm d' d]
      _ ≤ |n - n'| * K + L * |d - d'| := by gcongr
      _ = K * |n - n'| + L * |d - d'| := by ring
  have hden : ε ^ 2 ≤ d * d' := by nlinarith [mul_le_mul hd hd' hε.le hdpos.le]
  have hX : 0 ≤ K * |n - n'| + L * |d - d'| := le_trans (abs_nonneg _) hnum
  rw [hid, abs_div, abs_of_pos (mul_pos hdpos hd'pos),
    div_le_div_iff₀ (mul_pos hdpos hd'pos) (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_right hnum (sq_nonneg ε), mul_le_mul_of_nonneg_left hden hX]

/-- **The budget-4 guarded ratio is `1/ε`-Lipschitz.** For denominators at least `ε > 0` and the
second numerator at most the second denominator in absolute value,
`|n/d - n'/d'| ≤ (|n - n'| + |d - d'|) / ε`. -/
theorem abs_guardedRatio_sub_le (n : ℝ) {n' d d' ε : ℝ} (hε : 0 < ε) (hd : ε ≤ d)
    (hd' : ε ≤ d') (hn' : |n'| ≤ d') :
    |n / d - n' / d'| ≤ (|n - n'| + |d - d'|) / ε := by
  have hdpos : 0 < d := hε.trans_le hd
  have hd'pos : 0 < d' := hε.trans_le hd'
  have hid : n / d - n' / d' = ((n - n') * d' + n' * (d' - d)) / (d * d') := by
    rw [div_sub_div _ _ hdpos.ne' hd'pos.ne']
    congr 1
    ring
  have hnum : |(n - n') * d' + n' * (d' - d)| ≤ d' * (|n - n'| + |d - d'|) := by
    calc |(n - n') * d' + n' * (d' - d)| ≤ |(n - n') * d'| + |n' * (d' - d)| := abs_add_le _ _
      _ = |n - n'| * d' + |n'| * |d - d'| := by
          rw [abs_mul, abs_mul, abs_of_pos hd'pos, abs_sub_comm d' d]
      _ ≤ |n - n'| * d' + d' * |d - d'| := by gcongr
      _ = d' * (|n - n'| + |d - d'|) := by ring
  have hsum : 0 ≤ |n - n'| + |d - d'| := add_nonneg (abs_nonneg _) (abs_nonneg _)
  rw [hid, abs_div, abs_of_pos (mul_pos hdpos hd'pos), div_le_div_iff₀ (mul_pos hdpos hd'pos) hε]
  nlinarith [mul_le_mul_of_nonneg_right hnum hε.le,
    mul_le_mul_of_nonneg_left hd (mul_nonneg hd'pos.le hsum)]

/-- For every finite law the budget-4 correlation numerator is at most the denominator in
absolute value, which is the hypothesis of `abs_guardedRatio_sub_le`. -/
theorem abs_correlationNumerator_le_denominator (p : FiniteReportLaw Ω)
    (score outcome : Ω → ℝ) :
    |correlationNumerator p score outcome| ≤ correlationDenominator p score outcome := by
  rw [abs_of_nonneg (ReplicaMetricInstances.correlationNumerator_nonneg p score outcome)]
  exact ReplicaMetricInstances.correlationNumerator_le_denominator p score outcome

/-! ## Lipschitz constants on the unit cube -/

/-- The coordinate distance written out over the five coordinates. -/
theorem momentDistance_eq (m m' : SecondMoments) :
    momentDistance m m'
      = |m 0 - m' 0| + |m 1 - m' 1| + |m 2 - m' 2| + |m 3 - m' 3| + |m 4 - m' 4| :=
  Fin.sum_univ_five _

section UnitCube

variable {m m' : SecondMoments}

/-- On the unit cube the compiled covariance lies in `[-1, 1]`. -/
theorem abs_scoreOutcomeCovariance_le_one (hm : ∀ c, 0 ≤ m c ∧ m c ≤ 1) :
    |scoreOutcomeCovariance m| ≤ 1 := by
  have h01 : 0 ≤ m 0 * m 1 := mul_nonneg (hm 0).1 (hm 1).1
  have h01' : m 0 * m 1 ≤ 1 := mul_le_one₀ (hm 0).2 (hm 1).1 (hm 1).2
  unfold scoreOutcomeCovariance
  rw [abs_le]
  constructor <;> linarith [(hm 3).1, (hm 3).2]

/-- On the unit cube the compiled score variance is at most one. -/
theorem scoreVariance_le_one (hm : ∀ c, 0 ≤ m c ∧ m c ≤ 1) : scoreVariance m ≤ 1 := by
  unfold scoreVariance
  nlinarith [sq_nonneg (m 0), (hm 2).2]

/-- On the unit cube the compiled outcome variance is at most one. -/
theorem outcomeVariance_le_one (hm : ∀ c, 0 ≤ m c ∧ m c ≤ 1) : outcomeVariance m ≤ 1 := by
  unfold outcomeVariance
  nlinarith [sq_nonneg (m 1), (hm 4).2]

/-- On the unit cube the compiled score variance is `2`-Lipschitz. -/
theorem abs_scoreVariance_sub_le (hm : ∀ c, 0 ≤ m c ∧ m c ≤ 1)
    (hm' : ∀ c, 0 ≤ m' c ∧ m' c ≤ 1) :
    |scoreVariance m - scoreVariance m'| ≤ 2 * momentDistance m m' := by
  have hsq := abs_mul_sub_mul_le_split (m 0) (m' 0) (m 0) (m' 0)
  have h0 : |m 0| ≤ 1 := abs_le.mpr ⟨by linarith [(hm 0).1], (hm 0).2⟩
  have h0' : |m' 0| ≤ 1 := abs_le.mpr ⟨by linarith [(hm' 0).1], (hm' 0).2⟩
  have hid : scoreVariance m - scoreVariance m'
      = (m 2 - m' 2) - (m 0 * m 0 - m' 0 * m' 0) := by
    unfold scoreVariance
    ring
  have htri := abs_sub_le_abs_add_abs (m 2 - m' 2) (m 0 * m 0 - m' 0 * m' 0)
  rw [hid, momentDistance_eq]
  linarith [mul_le_mul_of_nonneg_left h0 (abs_nonneg (m 0 - m' 0)),
    mul_le_mul_of_nonneg_right h0' (abs_nonneg (m 0 - m' 0)), abs_nonneg (m 1 - m' 1),
    abs_nonneg (m 3 - m' 3), abs_nonneg (m 4 - m' 4), abs_nonneg (m 0 - m' 0),
    abs_nonneg (m 2 - m' 2)]

/-- On the unit cube the compiled outcome variance is `2`-Lipschitz. -/
theorem abs_outcomeVariance_sub_le (hm : ∀ c, 0 ≤ m c ∧ m c ≤ 1)
    (hm' : ∀ c, 0 ≤ m' c ∧ m' c ≤ 1) :
    |outcomeVariance m - outcomeVariance m'| ≤ 2 * momentDistance m m' := by
  have hsq := abs_mul_sub_mul_le_split (m 1) (m' 1) (m 1) (m' 1)
  have h1 : |m 1| ≤ 1 := abs_le.mpr ⟨by linarith [(hm 1).1], (hm 1).2⟩
  have h1' : |m' 1| ≤ 1 := abs_le.mpr ⟨by linarith [(hm' 1).1], (hm' 1).2⟩
  have hid : outcomeVariance m - outcomeVariance m'
      = (m 4 - m' 4) - (m 1 * m 1 - m' 1 * m' 1) := by
    unfold outcomeVariance
    ring
  have htri := abs_sub_le_abs_add_abs (m 4 - m' 4) (m 1 * m 1 - m' 1 * m' 1)
  rw [hid, momentDistance_eq]
  linarith [mul_le_mul_of_nonneg_left h1 (abs_nonneg (m 1 - m' 1)),
    mul_le_mul_of_nonneg_right h1' (abs_nonneg (m 1 - m' 1)), abs_nonneg (m 0 - m' 0),
    abs_nonneg (m 2 - m' 2), abs_nonneg (m 3 - m' 3), abs_nonneg (m 1 - m' 1),
    abs_nonneg (m 4 - m' 4)]

/-- On the unit cube the compiled covariance is `1`-Lipschitz. -/
theorem abs_scoreOutcomeCovariance_sub_le (hm : ∀ c, 0 ≤ m c ∧ m c ≤ 1)
    (hm' : ∀ c, 0 ≤ m' c ∧ m' c ≤ 1) :
    |scoreOutcomeCovariance m - scoreOutcomeCovariance m'| ≤ momentDistance m m' := by
  have hprod := abs_mul_sub_mul_le_split (m 0) (m' 0) (m 1) (m' 1)
  have h1 : |m 1| ≤ 1 := abs_le.mpr ⟨by linarith [(hm 1).1], (hm 1).2⟩
  have h0' : |m' 0| ≤ 1 := abs_le.mpr ⟨by linarith [(hm' 0).1], (hm' 0).2⟩
  have hid : scoreOutcomeCovariance m - scoreOutcomeCovariance m'
      = (m 3 - m' 3) - (m 0 * m 1 - m' 0 * m' 1) := by
    unfold scoreOutcomeCovariance
    ring
  have htri := abs_sub_le_abs_add_abs (m 3 - m' 3) (m 0 * m 1 - m' 0 * m' 1)
  rw [hid, momentDistance_eq]
  linarith [mul_le_mul_of_nonneg_left h1 (abs_nonneg (m 0 - m' 0)),
    mul_le_mul_of_nonneg_right h0' (abs_nonneg (m 1 - m' 1)), abs_nonneg (m 2 - m' 2),
    abs_nonneg (m 4 - m' 4), abs_nonneg (m 0 - m' 0), abs_nonneg (m 1 - m' 1)]

/-- **The compiled slope is `3/ε²`-Lipschitz** on the unit cube where the score variance is at
least `ε > 0`. -/
theorem abs_compiledSlope_sub_le {ε : ℝ} (hε : 0 < ε) (hm : ∀ c, 0 ≤ m c ∧ m c ≤ 1)
    (hm' : ∀ c, 0 ≤ m' c ∧ m' c ≤ 1) (hs : ε ≤ scoreVariance m) (hs' : ε ≤ scoreVariance m') :
    |compiledSlope m - compiledSlope m'| ≤ 3 / ε ^ 2 * momentDistance m m' := by
  have hq := abs_div_sub_div_le (scoreOutcomeCovariance m) (scoreOutcomeCovariance m') hε hs hs'
    (scoreVariance_le_one hm') (abs_scoreOutcomeCovariance_le_one hm')
  have hC := abs_scoreOutcomeCovariance_sub_le hm hm'
  have hV := abs_scoreVariance_sub_le hm hm'
  unfold compiledSlope
  calc |scoreOutcomeCovariance m / scoreVariance m
        - scoreOutcomeCovariance m' / scoreVariance m'|
      ≤ (1 * |scoreOutcomeCovariance m - scoreOutcomeCovariance m'|
          + 1 * |scoreVariance m - scoreVariance m'|) / ε ^ 2 := hq
    _ ≤ (1 * momentDistance m m' + 1 * (2 * momentDistance m m')) / ε ^ 2 := by gcongr
    _ = 3 / ε ^ 2 * momentDistance m m' := by ring

/-- The compiled `R²` is nonnegative where both compiled variances are nonnegative. -/
theorem compiledSquaredCorrelation_nonneg (hs : 0 ≤ scoreVariance m)
    (ho : 0 ≤ outcomeVariance m) : 0 ≤ compiledSquaredCorrelation m :=
  div_nonneg (sq_nonneg _) (mul_nonneg hs ho)

/-- On the unit cube where both variances are at least `ε > 0`, the compiled `R²` is at most
`1/ε²`. -/
theorem compiledSquaredCorrelation_le_inv_sq {ε : ℝ} (hε : 0 < ε)
    (hm : ∀ c, 0 ≤ m c ∧ m c ≤ 1) (hs : ε ≤ scoreVariance m) (ho : ε ≤ outcomeVariance m) :
    compiledSquaredCorrelation m ≤ 1 / ε ^ 2 := by
  have hden : ε ^ 2 ≤ scoreVariance m * outcomeVariance m := by
    nlinarith [mul_le_mul hs ho hε.le (hε.le.trans hs)]
  have hC : scoreOutcomeCovariance m ^ 2 ≤ 1 := by
    rw [← sq_abs]
    exact pow_le_one₀ (abs_nonneg _) (abs_scoreOutcomeCovariance_le_one hm)
  have hε2 : 0 < ε ^ 2 := by positivity
  unfold compiledSquaredCorrelation
  rw [div_le_div_iff₀ (by linarith) hε2]
  nlinarith [mul_le_mul_of_nonneg_right hC hε2.le]

/-- **The compiled `R²` is `6/ε⁴`-Lipschitz** on the unit cube where both variances are at
least `ε > 0`. -/
theorem abs_compiledSquaredCorrelation_sub_le {ε : ℝ} (hε : 0 < ε)
    (hm : ∀ c, 0 ≤ m c ∧ m c ≤ 1) (hm' : ∀ c, 0 ≤ m' c ∧ m' c ≤ 1)
    (hs : ε ≤ scoreVariance m) (ho : ε ≤ outcomeVariance m)
    (hs' : ε ≤ scoreVariance m') (ho' : ε ≤ outcomeVariance m') :
    |compiledSquaredCorrelation m - compiledSquaredCorrelation m'|
      ≤ 6 / ε ^ 4 * momentDistance m m' := by
  have hε2 : 0 < ε ^ 2 := by positivity
  have hden : ε ^ 2 ≤ scoreVariance m * outcomeVariance m := by
    nlinarith [mul_le_mul hs ho hε.le (hε.le.trans hs)]
  have hden' : ε ^ 2 ≤ scoreVariance m' * outcomeVariance m' := by
    nlinarith [mul_le_mul hs' ho' hε.le (hε.le.trans hs')]
  have hK : scoreVariance m' * outcomeVariance m' ≤ 1 :=
    mul_le_one₀ (scoreVariance_le_one hm') (hε.le.trans ho') (outcomeVariance_le_one hm')
  have hL : |scoreOutcomeCovariance m' ^ 2| ≤ 1 := by
    rw [abs_of_nonneg (sq_nonneg _), ← sq_abs]
    exact pow_le_one₀ (abs_nonneg _) (abs_scoreOutcomeCovariance_le_one hm')
  have hq := abs_div_sub_div_le (scoreOutcomeCovariance m ^ 2) (scoreOutcomeCovariance m' ^ 2)
    hε2 hden hden' hK hL
  have hsq : |scoreOutcomeCovariance m ^ 2 - scoreOutcomeCovariance m' ^ 2|
      ≤ 2 * momentDistance m m' := by
    have h := abs_mul_sub_mul_le_split (scoreOutcomeCovariance m) (scoreOutcomeCovariance m')
      (scoreOutcomeCovariance m) (scoreOutcomeCovariance m')
    rw [← pow_two, ← pow_two] at h
    linarith [abs_scoreOutcomeCovariance_sub_le hm hm',
      mul_le_mul_of_nonneg_left (abs_scoreOutcomeCovariance_le_one hm)
        (abs_nonneg (scoreOutcomeCovariance m - scoreOutcomeCovariance m')),
      mul_le_mul_of_nonneg_right (abs_scoreOutcomeCovariance_le_one hm')
        (abs_nonneg (scoreOutcomeCovariance m - scoreOutcomeCovariance m'))]
  have hprod : |scoreVariance m * outcomeVariance m - scoreVariance m' * outcomeVariance m'|
      ≤ 4 * momentDistance m m' := by
    have h := abs_mul_sub_mul_le_split (scoreVariance m) (scoreVariance m')
      (outcomeVariance m) (outcomeVariance m')
    have hVY : |outcomeVariance m| ≤ 1 :=
      abs_le.mpr ⟨by linarith, outcomeVariance_le_one hm⟩
    have hVS' : |scoreVariance m'| ≤ 1 :=
      abs_le.mpr ⟨by linarith, scoreVariance_le_one hm'⟩
    linarith [abs_scoreVariance_sub_le hm hm', abs_outcomeVariance_sub_le hm hm',
      mul_le_mul_of_nonneg_left hVY (abs_nonneg (scoreVariance m - scoreVariance m')),
      mul_le_mul_of_nonneg_right hVS' (abs_nonneg (outcomeVariance m - outcomeVariance m'))]
  unfold compiledSquaredCorrelation
  calc |scoreOutcomeCovariance m ^ 2 / (scoreVariance m * outcomeVariance m)
        - scoreOutcomeCovariance m' ^ 2 / (scoreVariance m' * outcomeVariance m')|
      ≤ (1 * |scoreOutcomeCovariance m ^ 2 - scoreOutcomeCovariance m' ^ 2|
          + 1 * |scoreVariance m * outcomeVariance m
            - scoreVariance m' * outcomeVariance m'|) / (ε ^ 2) ^ 2 := hq
    _ ≤ (1 * (2 * momentDistance m m') + 1 * (4 * momentDistance m m')) / (ε ^ 2) ^ 2 := by
        gcongr
    _ = 6 / ε ^ 4 * momentDistance m m' := by ring

end UnitCube

/-- **The compiled portability ratio is Lipschitz.** On the unit cube where every variance is at
least `ε > 0` and both source `R²` values are at least `δ > 0`, the ratio moves by at most
`6 (d_s + d_t) / (ε⁶ δ²)`. -/
theorem abs_compiledPortabilityRatio_sub_le {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ)
    {s t s' t' : SecondMoments}
    (hsc : ∀ c, 0 ≤ s c ∧ s c ≤ 1) (htc : ∀ c, 0 ≤ t c ∧ t c ≤ 1)
    (hsc' : ∀ c, 0 ≤ s' c ∧ s' c ≤ 1) (htc' : ∀ c, 0 ≤ t' c ∧ t' c ≤ 1)
    (hss : ε ≤ scoreVariance s) (hso : ε ≤ outcomeVariance s)
    (hts : ε ≤ scoreVariance t) (hto : ε ≤ outcomeVariance t)
    (hss' : ε ≤ scoreVariance s') (hso' : ε ≤ outcomeVariance s')
    (hts' : ε ≤ scoreVariance t') (hto' : ε ≤ outcomeVariance t')
    (hr : δ ≤ compiledSquaredCorrelation s) (hr' : δ ≤ compiledSquaredCorrelation s') :
    |compiledPortabilityRatio s t - compiledPortabilityRatio s' t'|
      ≤ 6 / (ε ^ 6 * δ ^ 2) * (momentDistance s s' + momentDistance t t') := by
  have hK := compiledSquaredCorrelation_le_inv_sq hε hsc' hss' hso'
  have hL : |compiledSquaredCorrelation t'| ≤ 1 / ε ^ 2 := by
    rw [abs_of_nonneg (compiledSquaredCorrelation_nonneg (hε.le.trans hts') (hε.le.trans hto'))]
    exact compiledSquaredCorrelation_le_inv_sq hε htc' hts' hto'
  have hq := abs_div_sub_div_le (compiledSquaredCorrelation t) (compiledSquaredCorrelation t')
    hδ hr hr' hK hL
  have hRt := abs_compiledSquaredCorrelation_sub_le hε htc htc' hts hto hts' hto'
  have hRs := abs_compiledSquaredCorrelation_sub_le hε hsc hsc' hss hso hss' hso'
  unfold compiledPortabilityRatio
  calc |compiledSquaredCorrelation t / compiledSquaredCorrelation s
        - compiledSquaredCorrelation t' / compiledSquaredCorrelation s'|
      ≤ (1 / ε ^ 2 * |compiledSquaredCorrelation t - compiledSquaredCorrelation t'|
          + 1 / ε ^ 2 * |compiledSquaredCorrelation s - compiledSquaredCorrelation s'|)
            / δ ^ 2 := hq
    _ ≤ (1 / ε ^ 2 * (6 / ε ^ 4 * momentDistance t t')
          + 1 / ε ^ 2 * (6 / ε ^ 4 * momentDistance s s')) / δ ^ 2 := by gcongr
    _ = 6 / (ε ^ 6 * δ ^ 2) * (momentDistance s s' + momentDistance t t') := by ring

/-! ## On the realization body -/

/-- A linear readout of a moment vector into the five second-moment coordinates, by a
coefficient matrix. -/
def readout {ι : Type*} [Fintype ι] (A : Fin 5 → ι → ℝ) (v : ι → ℝ) : SecondMoments :=
  fun c ↦ ∑ i, A c i * v i

/-- The readout multiplies the `ℓ¹` distance by at most `5 a` when every coefficient is at most
`a` in absolute value. -/
theorem momentDistance_readout_le {ι : Type*} [Fintype ι] (A : Fin 5 → ι → ℝ) {a : ℝ}
    (hA : ∀ c i, |A c i| ≤ a) (v v' : ι → ℝ) :
    momentDistance (readout A v) (readout A v') ≤ 5 * a * ∑ i, |v i - v' i| := by
  unfold momentDistance readout
  calc ∑ c, |∑ i, A c i * v i - ∑ i, A c i * v' i|
      ≤ ∑ c, ∑ i, |A c i| * |v i - v' i| := by
        refine Finset.sum_le_sum fun c _ ↦ ?_
        rw [← Finset.sum_sub_distrib]
        refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [← mul_sub, abs_mul]
    _ ≤ ∑ c : Fin 5, ∑ i, a * |v i - v' i| :=
        Finset.sum_le_sum fun c _ ↦ Finset.sum_le_sum fun i _ ↦
          mul_le_mul_of_nonneg_right (hA c i) (abs_nonneg _)
    _ = 5 * a * ∑ i, |v i - v' i| := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          ← Finset.mul_sum]
        push_cast
        ring

/-- The moment vectors that read into the unit cube form a convex set. -/
theorem convex_readoutCube {ι : Type*} [Fintype ι] (A : Fin 5 → ι → ℝ) :
    Convex ℝ {v : ι → ℝ | ∀ c, 0 ≤ readout A v c ∧ readout A v c ≤ 1} := by
  intro x hx y hy a b ha hb hab
  have hx' : ∀ c, 0 ≤ readout A x c ∧ readout A x c ≤ 1 := hx
  have hy' : ∀ c, 0 ≤ readout A y c ∧ readout A y c ≤ 1 := hy
  show ∀ c, 0 ≤ readout A (a • x + b • y) c ∧ readout A (a • x + b • y) c ≤ 1
  intro c
  have hlin : readout A (a • x + b • y) c = a * readout A x c + b * readout A y c := by
    simp only [readout, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add,
      Finset.sum_add_distrib, Finset.mul_sum]
    congr 1 <;> exact Finset.sum_congr rfl fun i _ ↦ by ring
  rw [hlin]
  obtain ⟨hx0, hx1⟩ := hx' c
  obtain ⟨hy0, hy1⟩ := hy' c
  constructor <;> nlinarith

/-- **The realization body reads into the unit cube** when every feature does: the cube is
convex and the readout is linear. -/
theorem readout_mem_cube_of_mem_realizationBody {X ι : Type*} [Fintype ι] (φ : X → ι → ℝ)
    (A : Fin 5 → ι → ℝ) (hφ : ∀ x c, 0 ≤ readout A (φ x) c ∧ readout A (φ x) c ≤ 1)
    {v : ι → ℝ} (hv : v ∈ RealizationBody.realizationBody φ) :
    ∀ c, 0 ≤ readout A v c ∧ readout A v c ≤ 1 :=
  convexHull_min (by rintro _ ⟨x, rfl⟩; exact hφ x) (convex_readoutCube A) hv

/-- **`Φ` for `R²` is Lipschitz on the realization body.** For moment vectors in the body of a
feature map whose features read into the unit cube, with both compiled variances at least
`ε > 0`, the compiled `R²` of the readout moves by at most `6/ε⁴ · 5a` times the `ℓ¹` distance of
the moment vectors. -/
theorem abs_compiledSquaredCorrelation_readout_sub_le {X ι : Type*} [Fintype ι]
    (φ : X → ι → ℝ) (A : Fin 5 → ι → ℝ) {a ε : ℝ} (hε : 0 < ε) (hA : ∀ c i, |A c i| ≤ a)
    (hφ : ∀ x c, 0 ≤ readout A (φ x) c ∧ readout A (φ x) c ≤ 1) {v v' : ι → ℝ}
    (hv : v ∈ RealizationBody.realizationBody φ) (hv' : v' ∈ RealizationBody.realizationBody φ)
    (hs : ε ≤ scoreVariance (readout A v)) (ho : ε ≤ outcomeVariance (readout A v))
    (hs' : ε ≤ scoreVariance (readout A v')) (ho' : ε ≤ outcomeVariance (readout A v')) :
    |compiledSquaredCorrelation (readout A v) - compiledSquaredCorrelation (readout A v')|
      ≤ 6 / ε ^ 4 * (5 * a * ∑ i, |v i - v' i|) := by
  refine (abs_compiledSquaredCorrelation_sub_le hε
    (readout_mem_cube_of_mem_realizationBody φ A hφ hv)
    (readout_mem_cube_of_mem_realizationBody φ A hφ hv') hs ho hs' ho').trans ?_
  exact mul_le_mul_of_nonneg_left (momentDistance_readout_le A hA v v') (by positivity)

/-- **`Φ` for the slope is Lipschitz on the realization body**, with constant `3/ε² · 5a`. -/
theorem abs_compiledSlope_readout_sub_le {X ι : Type*} [Fintype ι] (φ : X → ι → ℝ)
    (A : Fin 5 → ι → ℝ) {a ε : ℝ} (hε : 0 < ε) (hA : ∀ c i, |A c i| ≤ a)
    (hφ : ∀ x c, 0 ≤ readout A (φ x) c ∧ readout A (φ x) c ≤ 1) {v v' : ι → ℝ}
    (hv : v ∈ RealizationBody.realizationBody φ) (hv' : v' ∈ RealizationBody.realizationBody φ)
    (hs : ε ≤ scoreVariance (readout A v)) (hs' : ε ≤ scoreVariance (readout A v')) :
    |compiledSlope (readout A v) - compiledSlope (readout A v')|
      ≤ 3 / ε ^ 2 * (5 * a * ∑ i, |v i - v' i|) := by
  refine (abs_compiledSlope_sub_le hε
    (readout_mem_cube_of_mem_realizationBody φ A hφ hv)
    (readout_mem_cube_of_mem_realizationBody φ A hφ hv') hs hs').trans ?_
  exact mul_le_mul_of_nonneg_left (momentDistance_readout_le A hA v v') (by positivity)

/-! ## The cross ratio of the end-to-end law -/

section CrossRatio

variable {X ι : Type*} [Fintype ι]

/-- A dot product is at most the `ℓ¹` norm of the coefficients times a coordinatewise bound on
the vector. -/
theorem abs_dotProduct_le (c v : ι → ℝ) {B : ℝ} (hv : ∀ i, |v i| ≤ B) :
    |c ⬝ᵥ v| ≤ (∑ i, |c i|) * B := by
  unfold dotProduct
  calc |∑ i, c i * v i| ≤ ∑ i, |c i * v i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, |c i| * B := Finset.sum_le_sum fun i _ ↦ by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hv i) (abs_nonneg _)
    _ = (∑ i, |c i|) * B := by rw [Finset.sum_mul]

/-- A dot product moves by at most the `ℓ¹` norm of the coefficients times the sup distance. -/
theorem abs_dotProduct_sub_le (c v v' : ι → ℝ) :
    |c ⬝ᵥ v - c ⬝ᵥ v'| ≤ (∑ i, |c i|) * ‖v - v'‖ := by
  rw [← dotProduct_sub]
  refine abs_dotProduct_le c (v - v') fun i ↦ ?_
  have h := norm_le_pi_norm (v - v') i
  rwa [Real.norm_eq_abs] at h

/-- The vectors bounded by `B` coordinatewise form a convex set. -/
theorem convex_box (B : ℝ) : Convex ℝ {v : ι → ℝ | ∀ i, |v i| ≤ B} := by
  intro x hx y hy a b ha hb hab
  have hx' : ∀ i, |x i| ≤ B := hx
  have hy' : ∀ i, |y i| ≤ B := hy
  show ∀ i, |(a • x + b • y) i| ≤ B
  intro i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  calc |a * x i + b * y i| ≤ |a * x i| + |b * y i| := abs_add_le _ _
    _ = a * |x i| + b * |y i| := by rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
    _ ≤ a * B + b * B :=
        add_le_add (mul_le_mul_of_nonneg_left (hx' i) ha) (mul_le_mul_of_nonneg_left (hy' i) hb)
    _ = B := by rw [← add_mul, hab, one_mul]

/-- **The realization body inherits the feature bound.** If every feature is bounded by `B`
coordinatewise, so is every point of the realization body. -/
theorem abs_apply_le_of_mem_realizationBody (φ : X → ι → ℝ) {B : ℝ} (hφ : ∀ x i, |φ x i| ≤ B)
    {v : ι → ℝ} (hv : v ∈ RealizationBody.realizationBody φ) : ∀ i, |v i| ≤ B :=
  convexHull_min (by rintro _ ⟨x, rfl⟩; exact hφ x) (convex_box B) hv

/-- **Definedness of the end-to-end ratio.** `(a·v)(b·v) / ((c·v)(d·v))` is
`PortabilityRatioQueries.portabilityRatio` of the source numerator `d·v`, the source denominator
`b·v`, the target numerator `a·v` and the target denominator `c·v`, and its denominator is
positive, wherever `b·v`, `c·v` and `d·v` are positive. -/
theorem crossRatio_eq_portabilityRatio (a b c d v : ι → ℝ) (hb : 0 < b ⬝ᵥ v)
    (hc : 0 < c ⬝ᵥ v) (hd : 0 < d ⬝ᵥ v) :
    (a ⬝ᵥ v) * (b ⬝ᵥ v) / ((c ⬝ᵥ v) * (d ⬝ᵥ v)) =
        PortabilityRatioQueries.portabilityRatio (fun _ : Unit ↦ d ⬝ᵥ v) (fun _ ↦ b ⬝ᵥ v)
          (fun _ ↦ a ⬝ᵥ v) (fun _ ↦ c ⬝ᵥ v) () ∧
      0 < (c ⬝ᵥ v) * (d ⬝ᵥ v) := by
  refine ⟨?_, mul_pos hc hd⟩
  rw [PortabilityRatioQueries.portabilityRatio_eq_cross (fun _ : Unit ↦ d ⬝ᵥ v) (fun _ ↦ b ⬝ᵥ v)
    (fun _ ↦ a ⬝ᵥ v) (fun _ ↦ c ⬝ᵥ v) () hb hc hd]

/-- **The end-to-end ratio is Lipschitz on the realization body.** For a feature map bounded by
`B` coordinatewise and moment vectors `v`, `v'` in its realization body at which `c·v` and `d·v`
are at least `δ > 0`, the ratio `(a·v)(b·v) / ((c·v)(d·v))` moves by at most
`4 B³ ‖a‖₁ ‖b‖₁ ‖c‖₁ ‖d‖₁ / δ⁴` times the sup distance `‖v - v'‖`. -/
theorem abs_crossRatio_sub_le (φ : X → ι → ℝ) {B δ : ℝ} (hδ : 0 < δ) (hφ : ∀ x i, |φ x i| ≤ B)
    (a b c d : ι → ℝ) {v v' : ι → ℝ} (hv : v ∈ RealizationBody.realizationBody φ)
    (hv' : v' ∈ RealizationBody.realizationBody φ) (hc : δ ≤ c ⬝ᵥ v) (hd : δ ≤ d ⬝ᵥ v)
    (hc' : δ ≤ c ⬝ᵥ v') (hd' : δ ≤ d ⬝ᵥ v') :
    |(a ⬝ᵥ v) * (b ⬝ᵥ v) / ((c ⬝ᵥ v) * (d ⬝ᵥ v))
        - (a ⬝ᵥ v') * (b ⬝ᵥ v') / ((c ⬝ᵥ v') * (d ⬝ᵥ v'))|
      ≤ 4 * B ^ 3 * (∑ i, |a i|) * (∑ i, |b i|) * (∑ i, |c i|) * (∑ i, |d i|) / δ ^ 4
          * ‖v - v'‖ := by
  have hbox := abs_apply_le_of_mem_realizationBody φ hφ hv
  have hbox' := abs_apply_le_of_mem_realizationBody φ hφ hv'
  have hA' := abs_dotProduct_le a v' hbox'
  have hBv := abs_dotProduct_le b v hbox
  have hBv' := abs_dotProduct_le b v' hbox'
  have hC' := abs_dotProduct_le c v' hbox'
  have hDv := abs_dotProduct_le d v hbox
  have hD' := abs_dotProduct_le d v' hbox'
  have hdA := abs_dotProduct_sub_le a v v'
  have hdB := abs_dotProduct_sub_le b v v'
  have hdC := abs_dotProduct_sub_le c v v'
  have hdD := abs_dotProduct_sub_le d v v'
  have hδ2 : 0 < δ ^ 2 := by positivity
  have hden : δ ^ 2 ≤ (c ⬝ᵥ v) * (d ⬝ᵥ v) := by
    nlinarith [mul_le_mul hc hd hδ.le (hδ.le.trans hc)]
  have hden' : δ ^ 2 ≤ (c ⬝ᵥ v') * (d ⬝ᵥ v') := by
    nlinarith [mul_le_mul hc' hd' hδ.le (hδ.le.trans hc')]
  have hK : (c ⬝ᵥ v') * (d ⬝ᵥ v') ≤ ((∑ i, |c i|) * B) * ((∑ i, |d i|) * B) := by
    calc (c ⬝ᵥ v') * (d ⬝ᵥ v') ≤ |(c ⬝ᵥ v') * (d ⬝ᵥ v')| := le_abs_self _
      _ = |c ⬝ᵥ v'| * |d ⬝ᵥ v'| := abs_mul _ _
      _ ≤ ((∑ i, |c i|) * B) * ((∑ i, |d i|) * B) :=
          mul_le_mul hC' hD' (abs_nonneg _) ((abs_nonneg _).trans hC')
  have hL : |(a ⬝ᵥ v') * (b ⬝ᵥ v')| ≤ ((∑ i, |a i|) * B) * ((∑ i, |b i|) * B) := by
    rw [abs_mul]
    exact mul_le_mul hA' hBv' (abs_nonneg _) ((abs_nonneg _).trans hA')
  have hq := abs_div_sub_div_le ((a ⬝ᵥ v) * (b ⬝ᵥ v)) ((a ⬝ᵥ v') * (b ⬝ᵥ v')) hδ2 hden hden'
    hK hL
  have hnum : |(a ⬝ᵥ v) * (b ⬝ᵥ v) - (a ⬝ᵥ v') * (b ⬝ᵥ v')|
      ≤ 2 * B * (∑ i, |a i|) * (∑ i, |b i|) * ‖v - v'‖ := by
    have h := abs_mul_sub_mul_le_split (a ⬝ᵥ v) (a ⬝ᵥ v') (b ⬝ᵥ v) (b ⬝ᵥ v')
    have h1 : |a ⬝ᵥ v - a ⬝ᵥ v'| * |b ⬝ᵥ v|
        ≤ ((∑ i, |a i|) * ‖v - v'‖) * ((∑ i, |b i|) * B) :=
      mul_le_mul hdA hBv (abs_nonneg _) (by positivity)
    have h2 : |a ⬝ᵥ v'| * |b ⬝ᵥ v - b ⬝ᵥ v'|
        ≤ ((∑ i, |a i|) * B) * ((∑ i, |b i|) * ‖v - v'‖) :=
      mul_le_mul hA' hdB (abs_nonneg _) ((abs_nonneg _).trans hA')
    linarith
  have hdenom : |(c ⬝ᵥ v) * (d ⬝ᵥ v) - (c ⬝ᵥ v') * (d ⬝ᵥ v')|
      ≤ 2 * B * (∑ i, |c i|) * (∑ i, |d i|) * ‖v - v'‖ := by
    have h := abs_mul_sub_mul_le_split (c ⬝ᵥ v) (c ⬝ᵥ v') (d ⬝ᵥ v) (d ⬝ᵥ v')
    have h1 : |c ⬝ᵥ v - c ⬝ᵥ v'| * |d ⬝ᵥ v|
        ≤ ((∑ i, |c i|) * ‖v - v'‖) * ((∑ i, |d i|) * B) :=
      mul_le_mul hdC hDv (abs_nonneg _) (by positivity)
    have h2 : |c ⬝ᵥ v'| * |d ⬝ᵥ v - d ⬝ᵥ v'|
        ≤ ((∑ i, |c i|) * B) * ((∑ i, |d i|) * ‖v - v'‖) :=
      mul_le_mul hC' hdD (abs_nonneg _) ((abs_nonneg _).trans hC')
    linarith
  have hK0 : 0 ≤ ((∑ i, |c i|) * B) * ((∑ i, |d i|) * B) := by linarith
  have hL0 : 0 ≤ ((∑ i, |a i|) * B) * ((∑ i, |b i|) * B) := (abs_nonneg _).trans hL
  refine hq.trans ?_
  rw [show (δ ^ 2) ^ 2 = δ ^ 4 by ring]
  calc (((∑ i, |c i|) * B) * ((∑ i, |d i|) * B)
          * |(a ⬝ᵥ v) * (b ⬝ᵥ v) - (a ⬝ᵥ v') * (b ⬝ᵥ v')|
        + ((∑ i, |a i|) * B) * ((∑ i, |b i|) * B)
          * |(c ⬝ᵥ v) * (d ⬝ᵥ v) - (c ⬝ᵥ v') * (d ⬝ᵥ v')|) / δ ^ 4
      ≤ (((∑ i, |c i|) * B) * ((∑ i, |d i|) * B)
          * (2 * B * (∑ i, |a i|) * (∑ i, |b i|) * ‖v - v'‖)
        + ((∑ i, |a i|) * B) * ((∑ i, |b i|) * B)
          * (2 * B * (∑ i, |c i|) * (∑ i, |d i|) * ‖v - v'‖)) / δ ^ 4 :=
        div_le_div_of_nonneg_right
          (add_le_add (mul_le_mul_of_nonneg_left hnum hK0) (mul_le_mul_of_nonneg_left hdenom hL0))
          (by positivity)
    _ = 4 * B ^ 3 * (∑ i, |a i|) * (∑ i, |b i|) * (∑ i, |c i|) * (∑ i, |d i|) / δ ^ 4
          * ‖v - v'‖ := by ring

end CrossRatio

end

end Descent.Portability.PortabilityMetricCompilation
