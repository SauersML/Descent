/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.CylinderBoxMullerLaw

assert_below Descent.Decision Descent.Program

/-!
# Executed Theorem 5 for an angular integrand of the Box–Muller pair

NOTE2 §7.2 asks certificates to represent Gaussian primitives by fair random bits.
`CylinderGaussianDraw` certified a radial integrand of the Box–Muller pair; this module certifies
an integrand that depends on the angle, the indicator that both coordinates of the pair are
positive. Its exact expectation is one quarter, and by the Box–Muller theorem of
`CylinderBoxMullerLaw` that value is the mass of the open positive quadrant under the standard
bivariate Gaussian law.

`boxMuller_mem_quadrant_iff` locates the quadrant in the unit square: for `u, v ∈ [0, 1]` the
point `√(-2 log u) (cos 2πv, sin 2πv)` has both coordinates positive exactly when `0 < u < 1` and
`0 < v < 1/4`. `interlacedDraw offset stage word` is the value of the digits a word spells at the
positions `2 index + offset`, so offsets zero and one read the radial and the angular draw
(`interlacedDraw_zero_eq`, `interlacedDraw_one_eq`).

`quadrantEvaluator` is the cylinder evaluator at even depths. On a word of length `2 stage`, with
radial digits `b`, angular digits `a` and slack `h = 2^(-stage)`, the lower value is one when
`0 < b`, `b + h < 1`, `0 < a` and `a + h < 1/4`, and zero otherwise; the upper value is zero when
`1/4 ≤ a` and one otherwise. The values are exact rationals, nested because refining a word only
narrows the intervals `[b, b + h]` and `[a, a + h]` (`interlacedDraw_succ_bounds`). The width
vanishes eventually on every stream whose radial and angular draws lie strictly inside the unit
interval and whose angular draw differs from `1/4`; the odd bits carry the fair-bit law
(`measurePreserving_oddBits`) and the uniform draw has no atoms (`ae_uniformDraw_ne`), so these
streams carry full mass.

`integral_quadrantIndicator` computes the value one quarter from the product law of the radial
and angular draws. `quadrant_certificate` and `tendsto_quadrant_certificate` are the executed
Theorem 5, and `standardGaussianPair_quadrant` reads the certified value back as the Gaussian mass
of the quadrant.

## Empirical status

None. The bodies here are measure theory and trigonometry: the pair is a stipulated function of
the bit stream, and every conclusion follows from the fair-bit law and the signs of cosine and
sine, so no measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.CylinderGaussianQuadrant

open MeasureTheory Filter CylinderIntervalCertificate CylinderUniformDraw
  UniformPenetranceCertificate CylinderExponentialDraw CylinderGaussianDraw CylinderUniformLaw
  CylinderBoxMullerLaw

open scoped ENNReal Topology

noncomputable section

/-! ### The quadrant in the unit square -/

/-- The angular draw lies in the unit interval. -/
theorem angularDraw_mem_unitInterval (stream : ℕ → Bool) :
    0 ≤ angularDraw stream ∧ angularDraw stream ≤ 1 := by
  obtain ⟨hbase, hbelow, _, _⟩ := draw_bracket 0 (oddBits stream)
  exact ⟨le_trans hbase hbelow, uniformDraw_le_one (oddBits stream)⟩

/-- NOTE2 §7.2: for `u, v ∈ [0, 1]` the Box–Muller point `√(-2 log u) (cos 2πv, sin 2πv)` has
both coordinates positive exactly when `0 < u < 1` and `0 < v < 1/4`. -/
theorem boxMuller_mem_quadrant_iff {u v : ℝ} (hu : 0 ≤ u ∧ u ≤ 1) (hv : 0 ≤ v ∧ v ≤ 1) :
    (0 < Real.sqrt (-2 * Real.log u) * Real.cos (2 * Real.pi * v) ∧
        0 < Real.sqrt (-2 * Real.log u) * Real.sin (2 * Real.pi * v)) ↔
      (0 < u ∧ u < 1) ∧ (0 < v ∧ v < 1 / 4) := by
  obtain ⟨hu0, hu1⟩ := hu
  obtain ⟨hv0, hv1⟩ := hv
  have hpi := Real.pi_pos
  constructor
  · rintro ⟨hfirst, hsecond⟩
    have hradius : 0 < Real.sqrt (-2 * Real.log u) := by
      rcases (Real.sqrt_nonneg (-2 * Real.log u)).lt_or_eq with hpos | hzero
      · exact hpos
      · rw [← hzero, zero_mul] at hfirst
        exact absurd hfirst (lt_irrefl 0)
    have hcos : 0 < Real.cos (2 * Real.pi * v) := pos_of_mul_pos_right hfirst hradius.le
    have hsin : 0 < Real.sin (2 * Real.pi * v) := pos_of_mul_pos_right hsecond hradius.le
    have hlog : Real.log u < 0 := by
      have hinside := Real.sqrt_pos.mp hradius
      linarith
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · rcases hu0.lt_or_eq with hpos | hzero
      · exact hpos
      · rw [← hzero, Real.log_zero] at hlog
        exact absurd hlog (lt_irrefl 0)
    · by_contra hge
      have hnonneg := Real.log_nonneg (not_lt.mp hge)
      linarith
    · rcases hv0.lt_or_eq with hpos | hzero
      · exact hpos
      · rw [← hzero, mul_zero, Real.sin_zero] at hsin
        exact absurd hsin (lt_irrefl 0)
    · by_contra hge
      have hquarter : 1 / 4 ≤ v := not_lt.mp hge
      by_cases hthreeQuarters : v ≤ 3 / 4
      · have hnonpos := Real.cos_nonpos_of_pi_div_two_le_of_le (x := 2 * Real.pi * v)
          (by nlinarith) (by nlinarith)
        linarith
      · have hlate : 3 / 4 < v := not_le.mp hthreeQuarters
        have hnonpos := Real.sin_nonpos_of_nonpos_of_neg_pi_le
          (x := 2 * Real.pi * v - 2 * Real.pi) (by nlinarith) (by nlinarith)
        rw [Real.sin_sub_two_pi] at hnonpos
        linarith
  · rintro ⟨⟨hupos, hult⟩, ⟨hvpos, hvlt⟩⟩
    have hradius : 0 < Real.sqrt (-2 * Real.log u) :=
      Real.sqrt_pos.mpr (by linarith [Real.log_neg hupos hult])
    have hcos : 0 < Real.cos (2 * Real.pi * v) :=
      Real.cos_pos_of_mem_Ioo ⟨by nlinarith, by nlinarith⟩
    have hsin : 0 < Real.sin (2 * Real.pi * v) :=
      Real.sin_pos_of_pos_of_lt_pi (by nlinarith) (by nlinarith)
    exact ⟨mul_pos hradius hcos, mul_pos hradius hsin⟩

/-! ### Interlaced digits of a word -/

/-- The value of the first `stage` digits a word spells at the positions `2 index + offset`. -/
def interlacedDraw (offset stage : ℕ) (word : List Bool) : ℚ :=
  ∑ index ∈ Finset.range stage,
    if word.getD (2 * index + offset) false then (1 / 2 : ℚ) ^ (index + 1) else 0

/-- On the cylinder of a word of length `2 stage`, the interlaced digits at offset zero or one are
the truncated draw of the bits at the positions `2 index + offset`. -/
theorem interlacedDraw_eq_truncatedDraw {offset stage : ℕ} {word : List Bool}
    (hoffset : offset ≤ 1) (hlength : word.length = 2 * stage) {stream : ℕ → Bool}
    (hstream : stream ∈ cylinder word) :
    (interlacedDraw offset stage word : ℝ) =
      truncatedDraw stage fun index ↦ stream (2 * index + offset) := by
  simp only [CylinderIntervalCertificate.cylinder, Set.mem_pi, Finset.coe_range, Set.mem_Iio,
    Set.mem_singleton_iff] at hstream
  unfold interlacedDraw truncatedDraw binaryDigit
  push_cast [apply_ite (Rat.cast : ℚ → ℝ)]
  refine Finset.sum_congr rfl fun index hindex ↦ ?_
  have hbound : 2 * index + offset < word.length := by
    have hmember := Finset.mem_range.mp hindex
    omega
  simp only [hstream (2 * index + offset) hbound]

/-- On the cylinder of a word of length `2 stage` the interlaced digits at offset zero are the
truncated draw of the even bits. -/
theorem interlacedDraw_zero_eq {stage : ℕ} {word : List Bool} (hlength : word.length = 2 * stage)
    {stream : ℕ → Bool} (hstream : stream ∈ cylinder word) :
    (interlacedDraw 0 stage word : ℝ) = truncatedDraw stage (evenBits stream) :=
  interlacedDraw_eq_truncatedDraw zero_le_one hlength hstream

/-- On the cylinder of a word of length `2 stage` the interlaced digits at offset one are the
truncated draw of the odd bits. -/
theorem interlacedDraw_one_eq {stage : ℕ} {word : List Bool} (hlength : word.length = 2 * stage)
    {stream : ℕ → Bool} (hstream : stream ∈ cylinder word) :
    (interlacedDraw 1 stage word : ℝ) = truncatedDraw stage (oddBits stream) :=
  interlacedDraw_eq_truncatedDraw le_rfl hlength hstream

/-- The interlaced digits of a prefix at offset zero are the truncated draw of the even bits. -/
theorem interlacedDraw_zero_prefixOf (stream : ℕ → Bool) (stage : ℕ) :
    (interlacedDraw 0 stage (prefixOf stream (2 * stage)) : ℝ) =
      truncatedDraw stage (evenBits stream) :=
  interlacedDraw_zero_eq (length_prefixOf stream (2 * stage))
    (mem_cylinder_prefixOf stream (2 * stage))

/-- The interlaced digits of a prefix at offset one are the truncated draw of the odd bits. -/
theorem interlacedDraw_one_prefixOf (stream : ℕ → Bool) (stage : ℕ) :
    (interlacedDraw 1 stage (prefixOf stream (2 * stage)) : ℝ) =
      truncatedDraw stage (oddBits stream) :=
  interlacedDraw_one_eq (length_prefixOf stream (2 * stage))
    (mem_cylinder_prefixOf stream (2 * stage))

/-- Truncating a word to twice a count does not change its interlaced digits up to that
count. -/
theorem interlacedDraw_take (offset stage : ℕ) (word : List Bool) (hoffset : offset ≤ 1) :
    interlacedDraw offset stage (word.take (2 * stage)) = interlacedDraw offset stage word := by
  unfold interlacedDraw
  refine Finset.sum_congr rfl fun index hindex ↦ ?_
  have hbound : 2 * index + offset < 2 * stage := by
    have hmember := Finset.mem_range.mp hindex
    omega
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take,
    if_pos hbound]

/-- One more count adds a digit that is at most the slack it closes: the interlaced digits grow,
and the digits plus the slack shrink. -/
theorem interlacedDraw_succ_bounds (offset stage : ℕ) (word : List Bool) :
    interlacedDraw offset stage word ≤ interlacedDraw offset (stage + 1) word ∧
      interlacedDraw offset (stage + 1) word + (1 / 2) ^ (stage + 1) ≤
        interlacedDraw offset stage word + (1 / 2) ^ stage := by
  unfold interlacedDraw
  rw [Finset.sum_range_succ]
  have hhalf : (1 / 2 : ℚ) ^ (stage + 1) + (1 / 2) ^ (stage + 1) = (1 / 2) ^ stage := by ring
  have hpositive : (0 : ℚ) < (1 / 2) ^ (stage + 1) := by positivity
  split_ifs
  · constructor <;> linarith
  · constructor <;> linarith

/-! ### The odd bits and the atoms of the uniform draw -/

/-- NOTE2 §7.2: the odd bits of a fair-bit stream are a fair-bit stream. -/
theorem measurePreserving_oddBits : MeasurePreserving oddBits bitMeasure bitMeasure := by
  refine ⟨measurable_oddBits, ?_⟩
  have hcomp : oddBits = Prod.snd ∘ fun stream ↦ (evenBits stream, oddBits stream) := rfl
  rw [hcomp, ← Measure.map_map measurable_snd (measurable_evenBits.prodMk measurable_oddBits),
    map_evenBits_oddBits, Measure.map_snd_prod, measure_univ, one_smul]

/-- Almost every fair-bit stream has its uniform draw different from a given point. -/
theorem ae_uniformDraw_ne (point : ℝ) : ∀ᵐ stream ∂bitMeasure, uniformDraw stream ≠ point := by
  have hmap : ∀ᵐ u ∂(Measure.map uniformDraw bitMeasure), u ≠ point := by
    rw [map_uniformDraw, ae_iff]
    have hset : {u : ℝ | ¬u ≠ point} = {point} := by
      ext u
      simp
    rw [hset, Measure.restrict_apply (measurableSet_singleton point)]
    exact measure_mono_null Set.inter_subset_left Real.volume_singleton
  exact ae_of_ae_map measurable_uniformDraw.aemeasurable hmap

/-! ### The quadrant indicator and its evaluator -/

/-- The indicator that both coordinates of the Box–Muller pair of a stream are positive. -/
def quadrantIndicator (stream : ℕ → Bool) : ℝ :=
  if 0 < (gaussianPair stream).1 ∧ 0 < (gaussianPair stream).2 then 1 else 0

/-- The quadrant indicator is one exactly when the radial draw lies in `(0, 1)` and the angular
draw in `(0, 1/4)`. -/
theorem quadrantIndicator_eq (stream : ℕ → Bool) :
    quadrantIndicator stream =
      if (0 < radialDraw stream ∧ radialDraw stream < 1) ∧
          (0 < angularDraw stream ∧ angularDraw stream < 1 / 4) then 1 else 0 := by
  have hiff : (0 < (gaussianPair stream).1 ∧ 0 < (gaussianPair stream).2) ↔
      (0 < radialDraw stream ∧ radialDraw stream < 1) ∧
        (0 < angularDraw stream ∧ angularDraw stream < 1 / 4) :=
    boxMuller_mem_quadrant_iff (radialDraw_mem_unitInterval stream)
      (angularDraw_mem_unitInterval stream)
  unfold quadrantIndicator
  by_cases hmember : (0 < radialDraw stream ∧ radialDraw stream < 1) ∧
      (0 < angularDraw stream ∧ angularDraw stream < 1 / 4)
  · rw [if_pos hmember, if_pos (hiff.mpr hmember)]
  · rw [if_neg hmember, if_neg (mt hiff.mp hmember)]

/-- The quadrant indicator is the indicator of the preimage of the open positive quadrant under
the Gaussian pair. -/
theorem quadrantIndicator_eq_indicator :
    quadrantIndicator =
      (gaussianPair ⁻¹' (Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ))).indicator fun _ ↦ (1 : ℝ) := by
  funext stream
  unfold quadrantIndicator
  by_cases hmember : 0 < (gaussianPair stream).1 ∧ 0 < (gaussianPair stream).2
  · have hin : stream ∈ gaussianPair ⁻¹' (Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ)) := hmember
    rw [if_pos hmember, Set.indicator_of_mem hin]
  · have hout : stream ∉ gaussianPair ⁻¹' (Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ)) := hmember
    rw [if_neg hmember, Set.indicator_of_notMem hout]

/-- The preimage of the open positive quadrant under the Gaussian pair is the event that the
radial draw lies in `(0, 1)` and the angular draw in `(0, 1/4)`. -/
theorem gaussianPair_preimage_quadrant :
    gaussianPair ⁻¹' (Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ)) =
      (fun stream ↦ (radialDraw stream, angularDraw stream)) ⁻¹'
        (Set.Ioo (0 : ℝ) 1 ×ˢ Set.Ioo (0 : ℝ) (1 / 4)) := by
  ext stream
  exact boxMuller_mem_quadrant_iff (radialDraw_mem_unitInterval stream)
    (angularDraw_mem_unitInterval stream)

/-- The quadrant indicator is nonnegative. -/
theorem quadrantIndicator_nonneg (stream : ℕ → Bool) : 0 ≤ quadrantIndicator stream := by
  unfold quadrantIndicator
  split_ifs <;> norm_num

/-- The quadrant indicator is at most one. -/
theorem quadrantIndicator_le_one (stream : ℕ → Bool) : quadrantIndicator stream ≤ 1 := by
  unfold quadrantIndicator
  split_ifs <;> norm_num

/-- The rational lower value of the quadrant indicator on a word of length `2 stage`: one when
the radial digits `b` and the angular digits `a` satisfy `0 < b`, `b + 2^(-stage) < 1`, `0 < a`
and `a + 2^(-stage) < 1/4`, and zero otherwise. -/
def quadrantLower (stage : ℕ) (word : List Bool) : ℚ :=
  if (0 < interlacedDraw 0 stage word ∧ interlacedDraw 0 stage word + (1 / 2) ^ stage < 1) ∧
      (0 < interlacedDraw 1 stage word ∧ interlacedDraw 1 stage word + (1 / 2) ^ stage < 1 / 4)
    then 1 else 0

/-- The rational upper value of the quadrant indicator on a word of length `2 stage`: zero when
the angular digits are at least `1/4`, and one otherwise. -/
def quadrantUpper (stage : ℕ) (word : List Bool) : ℚ :=
  if 1 / 4 ≤ interlacedDraw 1 stage word then 0 else 1

/-- The real cast of digits plus the slack of a stage. -/
theorem cast_add_slack (q : ℚ) (stage : ℕ) :
    ((q + (1 / 2) ^ stage : ℚ) : ℝ) = (q : ℝ) + (1 / 2 : ℝ) ^ stage := by
  norm_num

/-- The real cast of one quarter. -/
theorem cast_quarter : ((1 / 4 : ℚ) : ℝ) = 1 / 4 := by
  norm_num

/-- Digits plus slack stay below one in the reals exactly when they do in the rationals. -/
theorem slack_lt_one_iff (q : ℚ) (stage : ℕ) :
    (q : ℝ) + (1 / 2 : ℝ) ^ stage < 1 ↔ q + (1 / 2) ^ stage < 1 := by
  have hiff : ((q + (1 / 2) ^ stage : ℚ) : ℝ) < ((1 : ℚ) : ℝ) ↔ q + (1 / 2) ^ stage < 1 :=
    Rat.cast_lt
  rwa [cast_add_slack, Rat.cast_one] at hiff

/-- Digits plus slack stay below one quarter in the reals exactly when they do in the
rationals. -/
theorem slack_lt_quarter_iff (q : ℚ) (stage : ℕ) :
    (q : ℝ) + (1 / 2 : ℝ) ^ stage < 1 / 4 ↔ q + (1 / 2) ^ stage < 1 / 4 := by
  have hiff : ((q + (1 / 2) ^ stage : ℚ) : ℝ) < ((1 / 4 : ℚ) : ℝ) ↔
      q + (1 / 2) ^ stage < 1 / 4 :=
    Rat.cast_lt
  rwa [cast_add_slack, cast_quarter] at hiff

/-- Digits reach one quarter in the reals exactly when they do in the rationals. -/
theorem quarter_le_iff (q : ℚ) : (1 / 4 : ℝ) ≤ q ↔ 1 / 4 ≤ q := by
  have hiff : ((1 / 4 : ℚ) : ℝ) ≤ (q : ℝ) ↔ 1 / 4 ≤ q := Rat.cast_le
  rwa [cast_quarter] at hiff

/-- NOTE2 Theorem 5 for an angular integrand of the Box–Muller pair: the cylinder evaluator of the
quadrant indicator at even depths, with exact rational values read from the radial and angular
digits of a word. -/
def quadrantEvaluator : CylinderEvaluator quadrantIndicator where
  depth := fun stage ↦ 2 * stage
  lower := quadrantLower
  upper := quadrantUpper
  depth_mono := fun _ _ hle ↦ Nat.mul_le_mul_left 2 hle
  lower_le := fun stage word hlength stream hstream ↦ by
    have hradial := interlacedDraw_zero_eq hlength hstream
    have hangular := interlacedDraw_one_eq hlength hstream
    obtain ⟨_, hradialBelow, hradialAbove, _⟩ := draw_bracket stage (evenBits stream)
    obtain ⟨_, hangularBelow, hangularAbove, _⟩ := draw_bracket stage (oddBits stream)
    show ((quadrantLower stage word : ℚ) : ℝ) ≤ quadrantIndicator stream
    unfold quadrantLower
    split_ifs with hcondition
    · obtain ⟨⟨hradialPos, hradialSlack⟩, ⟨hangularPos, hangularSlack⟩⟩ := hcondition
      have hradialPos' : (0 : ℝ) < interlacedDraw 0 stage word := by exact_mod_cast hradialPos
      have hradialSlack' : (interlacedDraw 0 stage word : ℝ) + (1 / 2 : ℝ) ^ stage < 1 :=
        (slack_lt_one_iff _ stage).mpr hradialSlack
      have hangularPos' : (0 : ℝ) < interlacedDraw 1 stage word := by exact_mod_cast hangularPos
      have hangularSlack' : (interlacedDraw 1 stage word : ℝ) + (1 / 2 : ℝ) ^ stage < 1 / 4 :=
        (slack_lt_quarter_iff _ stage).mpr hangularSlack
      have hmember : (0 < radialDraw stream ∧ radialDraw stream < 1) ∧
          (0 < angularDraw stream ∧ angularDraw stream < 1 / 4) := by
        unfold radialDraw angularDraw
        exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
      rw [quadrantIndicator_eq, if_pos hmember]
      norm_num
    · exact_mod_cast quadrantIndicator_nonneg stream
  le_upper := fun stage word hlength stream hstream ↦ by
    have hangular := interlacedDraw_one_eq hlength hstream
    obtain ⟨_, hangularBelow, _, _⟩ := draw_bracket stage (oddBits stream)
    show quadrantIndicator stream ≤ ((quadrantUpper stage word : ℚ) : ℝ)
    unfold quadrantUpper
    split_ifs with hcondition
    · have hcondition' : (1 / 4 : ℝ) ≤ interlacedDraw 1 stage word :=
        (quarter_le_iff _).mpr hcondition
      have hnotMember : ¬((0 < radialDraw stream ∧ radialDraw stream < 1) ∧
          (0 < angularDraw stream ∧ angularDraw stream < 1 / 4)) := by
        rintro ⟨_, _, hbelow⟩
        unfold angularDraw at hbelow
        linarith
      rw [quadrantIndicator_eq, if_neg hnotMember]
      norm_num
    · exact_mod_cast quadrantIndicator_le_one stream
  lower_nested := fun stage word _ ↦ by
    obtain ⟨hradialLow, hradialHigh⟩ := interlacedDraw_succ_bounds 0 stage word
    obtain ⟨hangularLow, hangularHigh⟩ := interlacedDraw_succ_bounds 1 stage word
    show quadrantLower stage (word.take (2 * stage)) ≤ quadrantLower (stage + 1) word
    unfold quadrantLower
    rw [interlacedDraw_take 0 stage word zero_le_one, interlacedDraw_take 1 stage word le_rfl]
    split_ifs with hcoarse hfine hfine
    · exact le_rfl
    · obtain ⟨⟨hradialPos, hradialSlack⟩, ⟨hangularPos, hangularSlack⟩⟩ := hcoarse
      exact (hfine ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩).elim
    · exact zero_le_one
    · exact le_rfl
  upper_nested := fun stage word _ ↦ by
    obtain ⟨hangularLow, _⟩ := interlacedDraw_succ_bounds 1 stage word
    show quadrantUpper (stage + 1) word ≤ quadrantUpper stage (word.take (2 * stage))
    unfold quadrantUpper
    rw [interlacedDraw_take 1 stage word le_rfl]
    split_ifs with hfine hcoarse hcoarse
    · exact le_rfl
    · exact zero_le_one
    · exact (hfine (le_trans hcoarse hangularLow)).elim
    · exact le_rfl
  width_ae := by
    filter_upwards [measurePreserving_evenBits.quasiMeasurePreserving.ae ae_uniformDraw_mem_Ioo,
      measurePreserving_oddBits.quasiMeasurePreserving.ae ae_uniformDraw_mem_Ioo,
      measurePreserving_oddBits.quasiMeasurePreserving.ae (ae_uniformDraw_ne (1 / 4))]
      with stream hradial hangular hquarter
    have hpower := tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num)
      (by norm_num)
    have hradialLimit := tendsto_truncatedDraw (evenBits stream)
    have hangularLimit := tendsto_truncatedDraw (oddBits stream)
    refine tendsto_const_nhds.congr' ?_
    rcases lt_or_gt_of_ne hquarter with hbelow | habove
    · have hradialSlackEventually := (hradialLimit.add hpower).eventually
        (gt_mem_nhds (by rw [add_zero]; exact hradial.2))
      have hangularSlackEventually := (hangularLimit.add hpower).eventually
        (gt_mem_nhds (by rw [add_zero]; exact hbelow))
      filter_upwards [hradialLimit.eventually (lt_mem_nhds hradial.1),
        hangularLimit.eventually (lt_mem_nhds hangular.1), hradialSlackEventually,
        hangularSlackEventually] with stage hradialPos hangularPos hradialSlack hangularSlack
      have hradialDigits := interlacedDraw_zero_prefixOf stream stage
      have hangularDigits := interlacedDraw_one_prefixOf stream stage
      obtain ⟨_, hangularBelow, _, _⟩ := draw_bracket stage (oddBits stream)
      rw [← hradialDigits] at hradialPos hradialSlack
      rw [← hangularDigits] at hangularPos hangularSlack hangularBelow
      have hlower : quadrantLower stage (prefixOf stream (2 * stage)) = 1 := by
        unfold quadrantLower
        split_ifs with hcondition
        · rfl
        · exact (hcondition
            ⟨⟨by exact_mod_cast hradialPos, (slack_lt_one_iff _ stage).mp hradialSlack⟩,
              ⟨by exact_mod_cast hangularPos,
                (slack_lt_quarter_iff _ stage).mp hangularSlack⟩⟩).elim
      have hupper : quadrantUpper stage (prefixOf stream (2 * stage)) = 1 := by
        unfold quadrantUpper
        split_ifs with hcondition
        · have hcondition' :
              (1 / 4 : ℝ) ≤ interlacedDraw 1 stage (prefixOf stream (2 * stage)) :=
            (quarter_le_iff _).mpr hcondition
          exfalso
          linarith
        · rfl
      show (0 : ℝ) = ((quadrantUpper stage (prefixOf stream (2 * stage)) : ℚ) : ℝ) -
        ((quadrantLower stage (prefixOf stream (2 * stage)) : ℚ) : ℝ)
      rw [hlower, hupper]
      norm_num
    · filter_upwards [hangularLimit.eventually (lt_mem_nhds habove)] with stage hangularLarge
      have hangularDigits := interlacedDraw_one_prefixOf stream stage
      rw [← hangularDigits] at hangularLarge
      have hupper : quadrantUpper stage (prefixOf stream (2 * stage)) = 0 := by
        unfold quadrantUpper
        split_ifs with hcondition
        · rfl
        · exact (hcondition ((quarter_le_iff _).mp hangularLarge.le)).elim
      have hlower : quadrantLower stage (prefixOf stream (2 * stage)) = 0 := by
        unfold quadrantLower
        split_ifs with hcondition
        · obtain ⟨_, _, hslack⟩ := hcondition
          have hslack' : (interlacedDraw 1 stage (prefixOf stream (2 * stage)) : ℝ) +
              (1 / 2 : ℝ) ^ stage < 1 / 4 :=
            (slack_lt_quarter_iff _ stage).mpr hslack
          have hpositive : (0 : ℝ) < (1 / 2) ^ stage := by positivity
          exfalso
          linarith
        · rfl
      show (0 : ℝ) = ((quadrantUpper stage (prefixOf stream (2 * stage)) : ℚ) : ℝ) -
        ((quadrantLower stage (prefixOf stream (2 * stage)) : ℚ) : ℝ)
      rw [hlower, hupper]
      norm_num

/-! ### The certified expectation -/

/-- NOTE2 §7.2: the exact expectation of the quadrant indicator is one quarter, the unit mass of
the radial event times the length one quarter of the angular event. -/
theorem integral_quadrantIndicator : ∫ stream, quadrantIndicator stream ∂bitMeasure = 1 / 4 := by
  have hquarter : Set.Ioo (0 : ℝ) (1 / 4) ∩ Set.Ioo 0 1 = Set.Ioo 0 (1 / 4) :=
    Set.inter_eq_left.mpr (Set.Ioo_subset_Ioo_right (by norm_num))
  rw [quadrantIndicator_eq_indicator,
    integral_indicator_const _ (measurable_gaussianPair (measurableSet_Ioi.prod measurableSet_Ioi)),
    gaussianPair_preimage_quadrant, smul_eq_mul, mul_one, measureReal_def,
    ← Measure.map_apply measurable_radialDraw_angularDraw
      (measurableSet_Ioo.prod measurableSet_Ioo),
    map_radialDraw_angularDraw, Measure.prod_prod, Measure.restrict_apply measurableSet_Ioo,
    Measure.restrict_apply measurableSet_Ioo, Set.inter_self, hquarter, Real.volume_Ioo,
    Real.volume_Ioo, ← ENNReal.ofReal_mul (show (0 : ℝ) ≤ 1 - 0 by norm_num),
    ENNReal.toReal_ofReal (show (0 : ℝ) ≤ (1 - 0) * (1 / 4 - 0) by norm_num)]
  norm_num

/-- NOTE2 §7.2, executed Theorem 5 for an angular integrand of the Box–Muller pair: at every stage
the rational certificates of the quadrant indicator bracket its exact expectation one quarter. -/
theorem quadrant_certificate (stage : ℕ) :
    (quadrantEvaluator.lowerSum stage : ℝ) ≤ 1 / 4 ∧
      1 / 4 ≤ (quadrantEvaluator.upperSum stage : ℝ) := by
  rw [← integral_quadrantIndicator]
  exact ⟨quadrantEvaluator.lowerSum_le_integral stage,
    quadrantEvaluator.integral_le_upperSum stage⟩

/-- NOTE2 §7.2, executed Theorem 5 for an angular integrand of the Box–Muller pair: the rational
certificates of the quadrant indicator converge to one quarter. -/
theorem tendsto_quadrant_certificate :
    Tendsto (fun stage ↦ (quadrantEvaluator.lowerSum stage : ℝ)) atTop (𝓝 (1 / 4)) ∧
      Tendsto (fun stage ↦ (quadrantEvaluator.upperSum stage : ℝ)) atTop (𝓝 (1 / 4)) := by
  rw [← integral_quadrantIndicator]
  exact ⟨quadrantEvaluator.tendsto_lowerSum, quadrantEvaluator.tendsto_upperSum⟩

/-- NOTE2 §7.2: the standard bivariate Gaussian law gives the open positive quadrant mass one
quarter, the certified expectation of the quadrant indicator read through the Box–Muller
theorem. -/
theorem standardGaussianPair_quadrant :
    ((ProbabilityTheory.gaussianReal 0 1).prod (ProbabilityTheory.gaussianReal 0 1)).real
      (Set.Ioi 0 ×ˢ Set.Ioi 0) = 1 / 4 := by
  have hintegral := integral_quadrantIndicator
  rw [quadrantIndicator_eq_indicator,
    integral_indicator_const _ (measurable_gaussianPair (measurableSet_Ioi.prod measurableSet_Ioi)),
    smul_eq_mul, mul_one, measureReal_def,
    ← Measure.map_apply measurable_gaussianPair (measurableSet_Ioi.prod measurableSet_Ioi),
    map_gaussianPair, ← measureReal_def] at hintegral
  exact hintegral

end

end Descent.Portability.CylinderGaussianQuadrant
