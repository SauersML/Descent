/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.CylinderExponentialDraw
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

assert_below Descent.Decision Descent.Program

/-!
# Executed Theorem 5 for the Box–Muller Gaussian draw from fair bits

NOTE2 §7.2 names a conditional Gaussian effect law among the continuous primitives that a
certificate has to represent by fair random bits. This module builds the Box–Muller Gaussian
pair on the fair-bit stream and certifies the expectation of a bounded integrand of it by
Theorem 5, with rational cylinder values and a closed-form limit.

The stream is split into its even and odd bits. `measurePreserving_evenBits` shows that the
even bits of a fair-bit stream are again a fair-bit stream, by checking the product measure on
boxes. `radialDraw` and `angularDraw` are the uniform draws of the even and odd bits, and
`gaussianPair` is the Box–Muller pair `√(-2 log U₁) (cos 2πU₂, sin 2πU₂)`. Its squared radius
is `-2 log U₁` (`gaussianPair_sq_add_sq`), so the bounded integrand `min (Z₁² + Z₂²) 2` is twice
the exponential cap of `CylinderExponentialDraw` at the radial draw whenever that draw is
positive (`min_sq_add_sq_eq_two_mul_exponentialCap`).

`radialEvaluator` is the cylinder evaluator of that integrand at even depths: on a word of
length `2 stage` its values are twice the rational exponential values on the word's even
letters. Its validity and nesting are those of `exponentialEvaluator` read through the even
letters, and its width vanishes almost surely because the even bits carry the fair-bit law.
`radial_certificate` and `tendsto_radial_certificate` are the executed Theorem 5, with limit
`2 (1 - e^(-1))`, and `integral_min_gaussianRadius` identifies it with the expectation of
`min (Z₁² + Z₂²) 2`.

Not formalized here: the Box–Muller theorem itself, that the two coordinates are independent
standard Gaussian draws; the law of the odd bits; and integrands depending on the angle. The
certified integrand is radial, and its closed form is the exponential law of the squared
radius of a standard bivariate Gaussian.

## Empirical status

None. The bodies here are measure theory and algebra: the pair is a stipulated function of the
bit stream, and every conclusion follows from the product structure of the fair-bit law and
the exponential certificate, so no measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.CylinderGaussianDraw

open MeasureTheory Filter CylinderIntervalCertificate CylinderUniformDraw
  UniformPenetranceCertificate CylinderExponentialDraw

open scoped ENNReal Topology

noncomputable section

/-! ### Even and odd bits -/

/-- The even-indexed bits of a stream. -/
def evenBits (stream : ℕ → Bool) (index : ℕ) : Bool :=
  stream (2 * index)

/-- The odd-indexed bits of a stream. -/
def oddBits (stream : ℕ → Bool) (index : ℕ) : Bool :=
  stream (2 * index + 1)

/-- Reading the even bits is measurable. -/
theorem measurable_evenBits : Measurable evenBits :=
  measurable_pi_lambda _ fun index ↦ measurable_pi_apply (2 * index)

/-- A box on the even bits is a box on the stream, over the doubled indices. -/
theorem evenBits_preimage_pi (s : Finset ℕ) (t : ℕ → Set Bool) :
    evenBits ⁻¹' Set.pi (s : Set ℕ) t =
      Set.pi ((s.image fun index ↦ 2 * index : Finset ℕ) : Set ℕ)
        fun position ↦ t (position / 2) := by
  ext stream
  simp only [Set.mem_preimage, Set.mem_pi, Finset.mem_coe, Finset.mem_image, evenBits]
  constructor
  · rintro hbits _ ⟨index, hindex, rfl⟩
    rw [Nat.mul_div_cancel_left index two_pos]
    exact hbits index hindex
  · intro hbits index hindex
    have hbit := hbits (2 * index) ⟨index, hindex, rfl⟩
    rwa [Nat.mul_div_cancel_left index two_pos] at hbit

/-- NOTE2 §7.2: the even bits of a fair-bit stream are a fair-bit stream. -/
theorem measurePreserving_evenBits : MeasurePreserving evenBits bitMeasure bitMeasure := by
  refine ⟨measurable_evenBits, ?_⟩
  refine Measure.eq_infinitePi (fun _ : ℕ ↦ fairBit) fun s t hmeasurable ↦ ?_
  have hinjective : Set.InjOn (fun index : ℕ ↦ 2 * index) (s : Set ℕ) :=
    fun first _ second _ hequal ↦ by simpa using hequal
  have hboxes : ∀ position ∈ s.image fun index ↦ 2 * index,
      MeasurableSet (t (position / 2)) := by
    intro position hposition
    obtain ⟨index, hindex, rfl⟩ := Finset.mem_image.mp hposition
    rw [Nat.mul_div_cancel_left index two_pos]
    exact hmeasurable index hindex
  rw [Measure.map_apply measurable_evenBits
      (MeasurableSet.pi (Finset.countable_toSet s) hmeasurable), evenBits_preimage_pi,
    bitMeasure, Measure.infinitePi_pi (fun _ : ℕ ↦ fairBit) hboxes, Finset.prod_image hinjective]
  simp only [Nat.mul_div_cancel_left _ two_pos]

/-! ### The Box–Muller pair -/

/-- The radial uniform coordinate of the Box–Muller construction: the uniform draw of the even
bits. -/
def radialDraw (stream : ℕ → Bool) : ℝ :=
  uniformDraw (evenBits stream)

/-- The angular uniform coordinate of the Box–Muller construction: the uniform draw of the odd
bits. -/
def angularDraw (stream : ℕ → Bool) : ℝ :=
  uniformDraw (oddBits stream)

/-- NOTE2 §7.2: the Box–Muller Gaussian pair encoded by a fair-bit stream. -/
def gaussianPair (stream : ℕ → Bool) : ℝ × ℝ :=
  (Real.sqrt (-2 * Real.log (radialDraw stream)) * Real.cos (2 * Real.pi * angularDraw stream),
    Real.sqrt (-2 * Real.log (radialDraw stream)) * Real.sin (2 * Real.pi * angularDraw stream))

/-- The radial draw lies in the unit interval. -/
theorem radialDraw_mem_unitInterval (stream : ℕ → Bool) :
    0 ≤ radialDraw stream ∧ radialDraw stream ≤ 1 := by
  obtain ⟨hbase, hbelow, _, _⟩ := draw_bracket 0 (evenBits stream)
  exact ⟨le_trans hbase hbelow, uniformDraw_le_one (evenBits stream)⟩

/-- The squared radius of the Box–Muller pair is `-2 log U₁`. -/
theorem gaussianPair_sq_add_sq (stream : ℕ → Bool) :
    (gaussianPair stream).1 ^ 2 + (gaussianPair stream).2 ^ 2 =
      -2 * Real.log (radialDraw stream) := by
  obtain ⟨hbase, hceiling⟩ := radialDraw_mem_unitInterval stream
  have hnonneg : 0 ≤ -2 * Real.log (radialDraw stream) := by
    have hlog := Real.log_nonpos hbase hceiling
    linarith
  simp only [gaussianPair, mul_pow, Real.sq_sqrt hnonneg]
  rw [← mul_add, Real.cos_sq_add_sin_sq, mul_one]

/-- At a positive radial draw the capped squared radius of the Box–Muller pair is twice the
exponential cap. -/
theorem min_sq_add_sq_eq_two_mul_exponentialCap {stream : ℕ → Bool}
    (hpos : 0 < radialDraw stream) :
    min ((gaussianPair stream).1 ^ 2 + (gaussianPair stream).2 ^ 2) 2 =
      2 * exponentialCap (radialDraw stream) := by
  rw [gaussianPair_sq_add_sq, exponentialCap_eq_min hpos]
  rcases le_total (-Real.log (radialDraw stream)) 1 with hle | hle
  · rw [min_eq_left hle,
      min_eq_left (show -2 * Real.log (radialDraw stream) ≤ 2 by linarith)]
    ring
  · rw [min_eq_right hle,
      min_eq_right (show (2:ℝ) ≤ -2 * Real.log (radialDraw stream) by linarith)]
    ring

/-! ### The radial cylinder evaluator -/

/-- The letters of a word at the even positions below twice a count. -/
def evenLetters (count : ℕ) (word : List Bool) : List Bool :=
  (List.range count).map fun index ↦ word.getD (2 * index) false

/-- The even letters below twice a count form a word of that count. -/
theorem length_evenLetters (count : ℕ) (word : List Bool) :
    (evenLetters count word).length = count := by
  simp [evenLetters]

/-- The even bits of a stream in the cylinder of a word of twice a count lie in the cylinder of
the even letters of the word. -/
theorem evenBits_mem_cylinder {count : ℕ} {word : List Bool}
    (hlength : word.length = 2 * count) {stream : ℕ → Bool}
    (hstream : stream ∈ cylinder word) :
    evenBits stream ∈ cylinder (evenLetters count word) := by
  rw [mem_cylinder_iff, length_evenLetters]
  simp only [CylinderIntervalCertificate.cylinder, Set.mem_pi, Finset.coe_range, Set.mem_Iio,
    Set.mem_singleton_iff] at hstream
  show (List.range count).map (evenBits stream) =
    (List.range count).map fun index ↦ word.getD (2 * index) false
  refine List.map_congr_left fun index hindex ↦ ?_
  have hbound : 2 * index < word.length := by
    have hmember := List.mem_range.mp hindex
    omega
  exact hstream (2 * index) hbound

/-- Truncating a word to twice a smaller count truncates its even letters. -/
theorem evenLetters_take (count : ℕ) (word : List Bool) :
    (evenLetters (count + 1) word).take count = evenLetters count (word.take (2 * count)) := by
  unfold evenLetters
  rw [← List.map_take, List.take_range, min_eq_left (Nat.le_succ count)]
  refine List.map_congr_left fun index hindex ↦ ?_
  have hbound : 2 * index < 2 * count := by
    have hmember := List.mem_range.mp hindex
    omega
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take,
    if_pos hbound]

/-- The even letters of a prefix of twice a count are the prefix of the even bits. -/
theorem evenLetters_prefixOf (count : ℕ) (stream : ℕ → Bool) :
    evenLetters count (prefixOf stream (2 * count)) = prefixOf (evenBits stream) count := by
  show (List.range count).map (fun index ↦ (prefixOf stream (2 * count)).getD (2 * index) false) =
    (List.range count).map (evenBits stream)
  refine List.map_congr_left fun index hindex ↦ ?_
  have hbound : 2 * index < 2 * count := by
    have hmember := List.mem_range.mp hindex
    omega
  exact getD_prefixOf stream hbound

/-- NOTE2 Theorem 5 for the Box–Muller radius: the cylinder evaluator of twice the exponential
cap at the radial draw, whose values on a word of length `2 stage` are twice the rational
exponential values on its even letters. -/
def radialEvaluator : CylinderEvaluator fun stream ↦ 2 * exponentialCap (radialDraw stream) where
  depth := fun stage ↦ 2 * stage
  lower := fun stage word ↦ 2 * capLower stage (evenLetters stage word)
  upper := fun stage word ↦ 2 * capUpper stage (evenLetters stage word)
  depth_mono := fun _ _ hle ↦ Nat.mul_le_mul_left 2 hle
  lower_le := fun stage word hlength stream hstream ↦ by
    have hbound : (capLower stage (evenLetters stage word) : ℝ) ≤
        exponentialCap (uniformDraw (evenBits stream)) :=
      exponentialEvaluator.lower_le stage (evenLetters stage word)
        (length_evenLetters stage word) (evenBits stream) (evenBits_mem_cylinder hlength hstream)
    show ((2 * capLower stage (evenLetters stage word) : ℚ) : ℝ) ≤
      2 * exponentialCap (radialDraw stream)
    push_cast
    unfold radialDraw
    linarith
  le_upper := fun stage word hlength stream hstream ↦ by
    have hbound : exponentialCap (uniformDraw (evenBits stream)) ≤
        (capUpper stage (evenLetters stage word) : ℝ) :=
      exponentialEvaluator.le_upper stage (evenLetters stage word)
        (length_evenLetters stage word) (evenBits stream) (evenBits_mem_cylinder hlength hstream)
    show 2 * exponentialCap (radialDraw stream) ≤
      ((2 * capUpper stage (evenLetters stage word) : ℚ) : ℝ)
    push_cast
    unfold radialDraw
    linarith
  lower_nested := fun stage word _ ↦ by
    have hnested : capLower stage ((evenLetters (stage + 1) word).take stage) ≤
        capLower (stage + 1) (evenLetters (stage + 1) word) :=
      exponentialEvaluator.lower_nested stage _ (length_evenLetters (stage + 1) word)
    rw [evenLetters_take] at hnested
    show 2 * capLower stage (evenLetters stage (word.take (2 * stage))) ≤
      2 * capLower (stage + 1) (evenLetters (stage + 1) word)
    linarith
  upper_nested := fun stage word _ ↦ by
    have hnested : capUpper (stage + 1) (evenLetters (stage + 1) word) ≤
        capUpper stage ((evenLetters (stage + 1) word).take stage) :=
      exponentialEvaluator.upper_nested stage _ (length_evenLetters (stage + 1) word)
    rw [evenLetters_take] at hnested
    show 2 * capUpper (stage + 1) (evenLetters (stage + 1) word) ≤
      2 * capUpper stage (evenLetters stage (word.take (2 * stage)))
    linarith
  width_ae := by
    have hwidth := measurePreserving_evenBits.quasiMeasurePreserving.ae
      exponentialEvaluator.width_ae
    filter_upwards [hwidth] with stream hstream
    have hscaled := hstream.const_mul 2
    rw [mul_zero] at hscaled
    refine hscaled.congr fun stage ↦ ?_
    show 2 * ((capUpper stage (prefixOf (evenBits stream) stage) : ℝ) -
        (capLower stage (prefixOf (evenBits stream) stage) : ℝ)) =
      ((2 * capUpper stage (evenLetters stage (prefixOf stream (2 * stage))) : ℚ) : ℝ) -
        ((2 * capLower stage (evenLetters stage (prefixOf stream (2 * stage))) : ℚ) : ℝ)
    rw [evenLetters_prefixOf]
    push_cast
    ring

/-! ### The certified expectation -/

/-- The exact expectation of twice the exponential cap at the radial draw is `2 (1 - e^(-1))`,
because the even bits carry the fair-bit law. -/
theorem integral_twice_exponentialCap_radialDraw :
    ∫ stream, 2 * exponentialCap (radialDraw stream) ∂bitMeasure = 2 * (1 - Real.exp (-1)) := by
  rw [integral_const_mul, ← integral_exponentialCap_uniformDraw]
  congr 1
  have hmap := measurePreserving_evenBits.map_eq
  have hmeasurable : AEStronglyMeasurable (fun stream ↦ exponentialCap (uniformDraw stream))
      (Measure.map evenBits bitMeasure) := by
    rw [hmap]
    exact exponentialEvaluator.integrable_integrand.aestronglyMeasurable
  have htransport := integral_map measurable_evenBits.aemeasurable hmeasurable
  rw [hmap] at htransport
  exact htransport.symm

/-- NOTE2 §7.2, executed Theorem 5 for the Box–Muller pair: at every stage the rational
certificates of the capped squared radius bracket its exact expectation `2 (1 - e^(-1))`. -/
theorem radial_certificate (stage : ℕ) :
    (radialEvaluator.lowerSum stage : ℝ) ≤ 2 * (1 - Real.exp (-1)) ∧
      2 * (1 - Real.exp (-1)) ≤ (radialEvaluator.upperSum stage : ℝ) := by
  rw [← integral_twice_exponentialCap_radialDraw]
  exact ⟨radialEvaluator.lowerSum_le_integral stage, radialEvaluator.integral_le_upperSum stage⟩

/-- NOTE2 §7.2, executed Theorem 5 for the Box–Muller pair: the rational certificates of the
capped squared radius converge to `2 (1 - e^(-1))`. -/
theorem tendsto_radial_certificate :
    Tendsto (fun stage ↦ (radialEvaluator.lowerSum stage : ℝ)) atTop
        (𝓝 (2 * (1 - Real.exp (-1)))) ∧
      Tendsto (fun stage ↦ (radialEvaluator.upperSum stage : ℝ)) atTop
        (𝓝 (2 * (1 - Real.exp (-1)))) := by
  rw [← integral_twice_exponentialCap_radialDraw]
  exact ⟨radialEvaluator.tendsto_lowerSum, radialEvaluator.tendsto_upperSum⟩

/-- NOTE2 §7.2 executed for the Box–Muller pair: the expectation of the bounded integrand
`min (Z₁² + Z₂²) 2` of the Gaussian pair is `2 (1 - e^(-1))`, the certified value. -/
theorem integral_min_gaussianRadius :
    ∫ stream, min ((gaussianPair stream).1 ^ 2 + (gaussianPair stream).2 ^ 2) 2 ∂bitMeasure =
      2 * (1 - Real.exp (-1)) := by
  rw [← integral_twice_exponentialCap_radialDraw]
  refine integral_congr_ae ?_
  filter_upwards [measurePreserving_evenBits.quasiMeasurePreserving.ae ae_exists_true]
    with stream htrue
  exact min_sq_add_sq_eq_two_mul_exponentialCap (uniformDraw_pos htrue)

end

end Descent.Portability.CylinderGaussianDraw
