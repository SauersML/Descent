/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.CylinderGaussianDraw
import Descent.Portability.CylinderUniformLaw
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Probability.Distributions.Gaussian.Real

assert_below Descent.Decision Descent.Program

/-!
# The Box–Muller theorem on fair bits

NOTE2 §7.2 names a conditional Gaussian effect law among the continuous primitives that a
certificate represents by fair random bits. `CylinderGaussianDraw` builds the Box–Muller pair
`√(-2 log U₁) (cos 2πU₂, sin 2πU₂)` from the uniform draws of the even and odd bits of the stream
and certifies a radial integrand. This module proves the Box–Muller theorem for that pair: its
law under the fair-bit measure is the product of two standard Gaussian laws, so its coordinates
are independent standard Gaussian draws.

The proof has three steps.

Independence of the halves. `interleave` writes one stream on the even positions and another on
the odd positions. The preimage of a box is a product of two boxes, so interleaving carries the
product of two fair-bit measures to the fair-bit measure (`measurePreserving_interleave`).
Reading the even and odd bits inverts it, so the two halves of a fair-bit stream have the product
law (`map_evenBits_oddBits`), and with `map_uniformDraw` the radial and angular draws are
independent uniform points of the unit interval (`map_radialDraw_angularDraw`).

The analytic core. `boxMuller` is the Box–Muller map on the unit square. For a measurable
`F : ℝ × ℝ → [0, ∞]`, `lintegral_standardGaussianPair` writes the integral of `F` against the
standard bivariate Gaussian law as a double integral over the unit square, in four moves. The
product of the two Gaussian densities is `e^(-(x² + y²)/2) / 2π` (`gaussianPDF_mul_gaussianPDF`);
polar coordinates turn it into `r e^(-r²/2) / 2π` on `(0, ∞) × (-π, π)`
(`lintegral_standardGaussianPair_polar`); the angle `θ = 2πv - π` has Jacobian `2π`
(`lintegral_angle_substitution`); the radius `r = √(-2 log u)` inverts `u = e^(-r²/2)`, whose
Jacobian is `r e^(-r²/2)` (`lintegral_radius_substitution`). The shifted angle reverses the sign
of both coordinates, and the Gaussian product is symmetric under that sign change
(`map_neg_standardGaussianPair`), so `map_boxMuller` identifies the law of the Box–Muller map on
the unit square.

The theorem. `map_gaussianPair` composes the two identifications. `map_gaussianPair_fst` and
`map_gaussianPair_snd` give the standard Gaussian marginals and `indepFun_gaussianPair` the
independence of the coordinates. `integral_gaussianPair` transports every measurable integrand,
depending on the angle as well as the radius, to the Gaussian product, with the closed-form check
`integral_gaussianPair_fst_mul_snd`: the product of the two coordinates has expectation zero.

## Empirical status

None. The bodies here are measure theory and calculus: the pair is a stipulated function of the
bit stream, and every conclusion follows from the fair-bit law, polar coordinates and the
one-dimensional change of variables, so no measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.CylinderBoxMullerLaw

open MeasureTheory Filter CylinderIntervalCertificate CylinderUniformDraw CylinderGaussianDraw
  CylinderUniformLaw

open scoped ENNReal Topology

noncomputable section

/-! ### Independence of the even and odd bits -/

/-- Interleave two streams: the first on the even positions and the second on the odd ones. -/
def interleave (pair : (ℕ → Bool) × (ℕ → Bool)) (index : ℕ) : Bool :=
  if index % 2 = 0 then pair.1 (index / 2) else pair.2 (index / 2)

/-- Reading the odd bits is measurable. -/
theorem measurable_oddBits : Measurable oddBits :=
  measurable_pi_lambda _ fun index ↦ measurable_pi_apply (2 * index + 1)

/-- Interleaving is measurable. -/
theorem measurable_interleave : Measurable interleave := by
  refine measurable_pi_lambda _ fun index ↦ ?_
  by_cases hparity : index % 2 = 0
  · simp only [interleave, if_pos hparity]
    exact (measurable_pi_apply (index / 2)).comp measurable_fst
  · simp only [interleave, if_neg hparity]
    exact (measurable_pi_apply (index / 2)).comp measurable_snd

/-- An even index is twice its half. -/
theorem two_mul_half_of_even {index : ℕ} (hparity : index % 2 = 0) : 2 * (index / 2) = index := by
  omega

/-- An odd index is one more than twice its half. -/
theorem two_mul_half_add_one_of_odd {index : ℕ} (hparity : ¬index % 2 = 0) :
    2 * (index / 2) + 1 = index := by
  omega

/-- The even bits of an interleaved pair are its first stream. -/
theorem evenBits_interleave (pair : (ℕ → Bool) × (ℕ → Bool)) :
    evenBits (interleave pair) = pair.1 := by
  funext index
  have hparity : 2 * index % 2 = 0 := by omega
  have hhalf : 2 * index / 2 = index := by omega
  simp only [evenBits, interleave, if_pos hparity, hhalf]

/-- The odd bits of an interleaved pair are its second stream. -/
theorem oddBits_interleave (pair : (ℕ → Bool) × (ℕ → Bool)) :
    oddBits (interleave pair) = pair.2 := by
  funext index
  have hparity : ¬(2 * index + 1) % 2 = 0 := by omega
  have hhalf : (2 * index + 1) / 2 = index := by omega
  simp only [oddBits, interleave, if_neg hparity, hhalf]

/-- The preimage of a box under interleaving is the product of a box on the first stream, over
the halves of the even indices, and a box on the second stream, over the halves of the odd
indices. -/
theorem interleave_preimage_pi (s : Finset ℕ) (t : ℕ → Set Bool) :
    interleave ⁻¹' Set.pi (s : Set ℕ) t =
      Set.pi (((s.filter fun index ↦ index % 2 = 0).image fun index ↦ index / 2 : Finset ℕ) :
          Set ℕ) (fun position ↦ t (2 * position)) ×ˢ
        Set.pi (((s.filter fun index ↦ ¬index % 2 = 0).image fun index ↦ index / 2 : Finset ℕ) :
          Set ℕ) (fun position ↦ t (2 * position + 1)) := by
  ext pair
  simp only [Set.mem_preimage, Set.mem_pi, Set.mem_prod, Finset.mem_coe, Finset.mem_image,
    Finset.mem_filter]
  constructor
  · intro hbits
    refine ⟨?_, ?_⟩
    · rintro _ ⟨index, ⟨hindex, hparity⟩, rfl⟩
      have hbit := hbits index hindex
      rw [interleave, if_pos hparity] at hbit
      rwa [two_mul_half_of_even hparity]
    · rintro _ ⟨index, ⟨hindex, hparity⟩, rfl⟩
      have hbit := hbits index hindex
      rw [interleave, if_neg hparity] at hbit
      rwa [two_mul_half_add_one_of_odd hparity]
  · rintro ⟨heven, hodd⟩ index hindex
    by_cases hparity : index % 2 = 0
    · have hbit := heven (index / 2) ⟨index, ⟨hindex, hparity⟩, rfl⟩
      rw [two_mul_half_of_even hparity] at hbit
      rw [interleave, if_pos hparity]
      exact hbit
    · have hbit := hodd (index / 2) ⟨index, ⟨hindex, hparity⟩, rfl⟩
      rw [two_mul_half_add_one_of_odd hparity] at hbit
      rw [interleave, if_neg hparity]
      exact hbit

/-- Halving is injective on the even indices of a finite set. -/
theorem injOn_half_even (s : Finset ℕ) :
    Set.InjOn (fun index : ℕ ↦ index / 2) ((s.filter fun index ↦ index % 2 = 0 : Finset ℕ) :
      Set ℕ) := by
  intro first hfirst second hsecond hequal
  have hfirstParity := (Finset.mem_filter.mp hfirst).2
  have hsecondParity := (Finset.mem_filter.mp hsecond).2
  have hhalves : first / 2 = second / 2 := hequal
  omega

/-- Halving is injective on the odd indices of a finite set. -/
theorem injOn_half_odd (s : Finset ℕ) :
    Set.InjOn (fun index : ℕ ↦ index / 2) ((s.filter fun index ↦ ¬index % 2 = 0 : Finset ℕ) :
      Set ℕ) := by
  intro first hfirst second hsecond hequal
  have hfirstParity := (Finset.mem_filter.mp hfirst).2
  have hsecondParity := (Finset.mem_filter.mp hsecond).2
  have hhalves : first / 2 = second / 2 := hequal
  omega

/-- NOTE2 §7.2: interleaving two independent fair-bit streams gives a fair-bit stream. -/
theorem measurePreserving_interleave :
    MeasurePreserving interleave (bitMeasure.prod bitMeasure) bitMeasure := by
  refine ⟨measurable_interleave, ?_⟩
  refine Measure.eq_infinitePi (fun _ : ℕ ↦ fairBit) fun s t hmeasurable ↦ ?_
  have hevenBoxes : ∀ position ∈ (s.filter fun index ↦ index % 2 = 0).image fun index ↦ index / 2,
      MeasurableSet (t (2 * position)) := by
    intro position hposition
    obtain ⟨index, hindex, rfl⟩ := Finset.mem_image.mp hposition
    obtain ⟨hmember, hparity⟩ := Finset.mem_filter.mp hindex
    rw [two_mul_half_of_even hparity]
    exact hmeasurable index hmember
  have hoddBoxes : ∀ position ∈ (s.filter fun index ↦ ¬index % 2 = 0).image fun index ↦ index / 2,
      MeasurableSet (t (2 * position + 1)) := by
    intro position hposition
    obtain ⟨index, hindex, rfl⟩ := Finset.mem_image.mp hposition
    obtain ⟨hmember, hparity⟩ := Finset.mem_filter.mp hindex
    rw [two_mul_half_add_one_of_odd hparity]
    exact hmeasurable index hmember
  rw [Measure.map_apply measurable_interleave
      (MeasurableSet.pi (Finset.countable_toSet s) hmeasurable), interleave_preimage_pi,
    Measure.prod_prod, bitMeasure, Measure.infinitePi_pi (fun _ : ℕ ↦ fairBit) hevenBoxes,
    Measure.infinitePi_pi (fun _ : ℕ ↦ fairBit) hoddBoxes, Finset.prod_image (injOn_half_even s),
    Finset.prod_image (injOn_half_odd s),
    ← Finset.prod_filter_mul_prod_filter_not s fun index ↦ index % 2 = 0]
  congr 1
  · refine Finset.prod_congr rfl fun index hindex ↦ ?_
    show fairBit (t (2 * (index / 2))) = fairBit (t index)
    rw [two_mul_half_of_even (Finset.mem_filter.mp hindex).2]
  · refine Finset.prod_congr rfl fun index hindex ↦ ?_
    show fairBit (t (2 * (index / 2) + 1)) = fairBit (t index)
    rw [two_mul_half_add_one_of_odd (Finset.mem_filter.mp hindex).2]

/-- NOTE2 §7.2: the even and odd bits of a fair-bit stream are independent fair-bit streams. -/
theorem map_evenBits_oddBits :
    Measure.map (fun stream ↦ (evenBits stream, oddBits stream)) bitMeasure =
      bitMeasure.prod bitMeasure := by
  have hmeasurable : Measurable fun stream ↦ (evenBits stream, oddBits stream) :=
    measurable_evenBits.prodMk measurable_oddBits
  have hinverse : (fun stream ↦ (evenBits stream, oddBits stream)) ∘ interleave = id := by
    funext pair
    show (evenBits (interleave pair), oddBits (interleave pair)) = pair
    rw [evenBits_interleave, oddBits_interleave]
  calc Measure.map (fun stream ↦ (evenBits stream, oddBits stream)) bitMeasure
      = Measure.map (fun stream ↦ (evenBits stream, oddBits stream))
          (Measure.map interleave (bitMeasure.prod bitMeasure)) := by
        rw [measurePreserving_interleave.map_eq]
    _ = bitMeasure.prod bitMeasure := by
        rw [Measure.map_map hmeasurable measurable_interleave, hinverse, Measure.map_id]

/-- The radial and angular draws are jointly measurable. -/
theorem measurable_radialDraw_angularDraw :
    Measurable fun stream ↦ (radialDraw stream, angularDraw stream) :=
  (measurable_uniformDraw.comp measurable_evenBits).prodMk
    (measurable_uniformDraw.comp measurable_oddBits)

/-- NOTE2 §7.2: the radial and angular draws of a fair-bit stream are independent uniform points
of the open unit interval. -/
theorem map_radialDraw_angularDraw :
    Measure.map (fun stream ↦ (radialDraw stream, angularDraw stream)) bitMeasure =
      (volume.restrict (Set.Ioo (0 : ℝ) 1)).prod (volume.restrict (Set.Ioo (0 : ℝ) 1)) := by
  have hcomp : (fun stream ↦ (radialDraw stream, angularDraw stream)) =
      Prod.map uniformDraw uniformDraw ∘ fun stream ↦ (evenBits stream, oddBits stream) := rfl
  rw [hcomp, ← Measure.map_map (measurable_uniformDraw.prodMap measurable_uniformDraw)
      (measurable_evenBits.prodMk measurable_oddBits), map_evenBits_oddBits,
    ← Measure.map_prod_map _ _ measurable_uniformDraw measurable_uniformDraw, map_uniformDraw]

/-! ### The standard bivariate Gaussian law on the unit square -/

/-- The product of two standard Gaussian densities is `e^(-(x² + y²)/2) / 2π`. -/
theorem gaussianPDF_mul_gaussianPDF (first second : ℝ) :
    ProbabilityTheory.gaussianPDF 0 1 first * ProbabilityTheory.gaussianPDF 0 1 second =
      ENNReal.ofReal ((2 * Real.pi)⁻¹ * Real.exp (-(first ^ 2 + second ^ 2) / 2)) := by
  rw [ProbabilityTheory.gaussianPDF, ProbabilityTheory.gaussianPDF,
    ← ENNReal.ofReal_mul (ProbabilityTheory.gaussianPDFReal_nonneg 0 1 first)]
  congr 1
  simp only [ProbabilityTheory.gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
  have hroot : (2 * Real.pi)⁻¹ = (√(2 * Real.pi))⁻¹ * (√(2 * Real.pi))⁻¹ := by
    rw [← mul_inv, Real.mul_self_sqrt (by positivity)]
  have hexp : Real.exp (-(first ^ 2 + second ^ 2) / 2) =
      Real.exp (-first ^ 2 / 2) * Real.exp (-second ^ 2 / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hroot, hexp]
  ring

/-- NOTE2 §7.2: the integral of a measurable function against the standard bivariate Gaussian
law in polar coordinates, with density `r e^(-r²/2) / 2π` on `(0, ∞) × (-π, π)`. -/
theorem lintegral_standardGaussianPair_polar (F : ℝ × ℝ → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ point, F point ∂((ProbabilityTheory.gaussianReal 0 1).prod
        (ProbabilityTheory.gaussianReal 0 1)) =
      ∫⁻ radius in Set.Ioi 0, ∫⁻ angle in Set.Ioo (-Real.pi) Real.pi,
        ENNReal.ofReal ((2 * Real.pi)⁻¹ * (radius * Real.exp (-radius ^ 2 / 2))) *
          F (radius * Real.cos angle, radius * Real.sin angle) := by
  have hdensity : Measurable fun point : ℝ × ℝ ↦
      ProbabilityTheory.gaussianPDF 0 1 point.1 * ProbabilityTheory.gaussianPDF 0 1 point.2 :=
    ((ProbabilityTheory.measurable_gaussianPDF 0 1).comp measurable_fst).mul
      ((ProbabilityTheory.measurable_gaussianPDF 0 1).comp measurable_snd)
  have hpolar : Measurable fun point : ℝ × ℝ ↦
      ENNReal.ofReal ((2 * Real.pi)⁻¹ * (point.1 * Real.exp (-point.1 ^ 2 / 2))) *
        F (point.1 * Real.cos point.2, point.1 * Real.sin point.2) := by
    have hradial : Measurable fun point : ℝ × ℝ ↦
        (2 * Real.pi)⁻¹ * (point.1 * Real.exp (-point.1 ^ 2 / 2)) :=
      measurable_const.mul (measurable_fst.mul
        (Real.measurable_exp.comp ((measurable_fst.pow_const 2).neg.div_const 2)))
    have hpoint : Measurable fun point : ℝ × ℝ ↦
        (point.1 * Real.cos point.2, point.1 * Real.sin point.2) :=
      (measurable_fst.mul (Real.measurable_cos.comp measurable_snd)).prodMk
        (measurable_fst.mul (Real.measurable_sin.comp measurable_snd))
    exact (ENNReal.measurable_ofReal.comp hradial).mul (hF.comp hpoint)
  have htarget : polarCoord.target = Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi := rfl
  rw [ProbabilityTheory.gaussianReal_of_var_ne_zero 0 one_ne_zero,
    prod_withDensity (ProbabilityTheory.measurable_gaussianPDF 0 1)
      (ProbabilityTheory.measurable_gaussianPDF 0 1),
    ← Measure.volume_eq_prod, lintegral_withDensity_eq_lintegral_mul _ hdensity hF,
    ← lintegral_comp_polarCoord_symm, htarget,
    setLIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo)
      (g := fun point : ℝ × ℝ ↦
        ENNReal.ofReal ((2 * Real.pi)⁻¹ * (point.1 * Real.exp (-point.1 ^ 2 / 2))) *
          F (point.1 * Real.cos point.2, point.1 * Real.sin point.2)) ?_]
  · rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
    exact lintegral_prod _ hpolar.aemeasurable
  · intro point hpoint
    have hradius : 0 < point.1 := hpoint.1
    show ENNReal.ofReal point.1 *
        (ProbabilityTheory.gaussianPDF 0 1 (point.1 * Real.cos point.2) *
          ProbabilityTheory.gaussianPDF 0 1 (point.1 * Real.sin point.2) *
          F (point.1 * Real.cos point.2, point.1 * Real.sin point.2)) =
      ENNReal.ofReal ((2 * Real.pi)⁻¹ * (point.1 * Real.exp (-point.1 ^ 2 / 2))) *
        F (point.1 * Real.cos point.2, point.1 * Real.sin point.2)
    rw [gaussianPDF_mul_gaussianPDF, ← mul_assoc, ← ENNReal.ofReal_mul hradius.le, mul_pow,
      mul_pow, ← mul_add, Real.cos_sq_add_sin_sq, mul_one]
    congr 2
    ring

/-- The angle `θ = 2πv - π` carries the open unit interval onto `(-π, π)` with Jacobian `2π`. -/
theorem lintegral_angle_substitution (G : ℝ → ℝ≥0∞) :
    ∫⁻ angle in Set.Ioo (-Real.pi) Real.pi, G angle =
      ENNReal.ofReal (2 * Real.pi) * ∫⁻ v in Set.Ioo 0 1, G (2 * Real.pi * v - Real.pi) := by
  have hpi : 0 < 2 * Real.pi := Real.two_pi_pos
  have himage : (fun v : ℝ ↦ 2 * Real.pi * v - Real.pi) '' Set.Ioo 0 1 =
      Set.Ioo (-Real.pi) Real.pi := by
    ext angle
    simp only [Set.mem_image, Set.mem_Ioo]
    constructor
    · rintro ⟨v, ⟨hpos, hlt⟩, rfl⟩
      constructor <;> nlinarith
    · rintro ⟨hlow, hhigh⟩
      refine ⟨(angle + Real.pi) / (2 * Real.pi), ⟨div_pos (by linarith) hpi, ?_⟩, ?_⟩
      · rw [div_lt_one hpi]
        linarith
      · have hcancel : 2 * Real.pi * ((angle + Real.pi) / (2 * Real.pi)) = angle + Real.pi := by
          field_simp
        linarith
  have hderivative : ∀ v ∈ Set.Ioo (0 : ℝ) 1, HasDerivWithinAt
      (fun v : ℝ ↦ 2 * Real.pi * v - Real.pi) (2 * Real.pi) (Set.Ioo 0 1) v := fun v _ ↦
    ((((hasDerivAt_id' (x := v)).const_mul (2 * Real.pi)).sub_const Real.pi).congr_deriv
      (mul_one _)).hasDerivWithinAt
  have hinjective : Set.InjOn (fun v : ℝ ↦ 2 * Real.pi * v - Real.pi) (Set.Ioo 0 1) :=
    fun first _ second _ hequal ↦ by
      have hsame : 2 * Real.pi * first - Real.pi = 2 * Real.pi * second - Real.pi := hequal
      exact mul_left_cancel₀ hpi.ne' (by linarith)
  rw [← himage,
    lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioo hderivative hinjective,
    abs_of_pos hpi, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

/-- The radius `r = √(-2 log u)` inverts `u = e^(-r²/2)`, which carries `(0, ∞)` onto the open
unit interval with Jacobian `r e^(-r²/2)`. -/
theorem lintegral_radius_substitution (G : ℝ → ℝ≥0∞) :
    ∫⁻ u in Set.Ioo 0 1, G (Real.sqrt (-2 * Real.log u)) =
      ∫⁻ radius in Set.Ioi 0, ENNReal.ofReal (radius * Real.exp (-radius ^ 2 / 2)) * G radius := by
  have himage : (fun radius : ℝ ↦ Real.exp (-(radius * radius) / 2)) '' Set.Ioi 0 =
      Set.Ioo 0 1 := by
    ext u
    simp only [Set.mem_image, Set.mem_Ioi, Set.mem_Ioo]
    constructor
    · rintro ⟨radius, hradius, rfl⟩
      refine ⟨Real.exp_pos _, ?_⟩
      rw [← Real.exp_zero]
      exact Real.exp_lt_exp.mpr (by nlinarith)
    · rintro ⟨hpos, hlt⟩
      have hlog : Real.log u < 0 := Real.log_neg hpos hlt
      refine ⟨Real.sqrt (-2 * Real.log u), Real.sqrt_pos.mpr (by linarith), ?_⟩
      rw [Real.mul_self_sqrt (by linarith), show -(-2 * Real.log u) / 2 = Real.log u by ring,
        Real.exp_log hpos]
  have hderivative : ∀ radius ∈ Set.Ioi (0 : ℝ), HasDerivWithinAt
      (fun radius : ℝ ↦ Real.exp (-(radius * radius) / 2))
      (-(radius * Real.exp (-(radius * radius) / 2))) (Set.Ioi 0) radius := fun radius _ ↦
    (((((hasDerivAt_id' (x := radius)).mul (hasDerivAt_id' (x := radius))).neg.div_const
      2).exp).congr_deriv (by ring)).hasDerivWithinAt
  have hinjective : Set.InjOn (fun radius : ℝ ↦ Real.exp (-(radius * radius) / 2))
      (Set.Ioi 0) := fun first hfirst second hsecond hequal ↦ by
    have hsquares : -(first * first) / 2 = -(second * second) / 2 := Real.exp_injective hequal
    have hfirstPos : 0 < first := hfirst
    have hsecondPos : 0 < second := hsecond
    nlinarith
  rw [← himage,
    lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioi hderivative hinjective]
  refine setLIntegral_congr_fun measurableSet_Ioi fun radius hradius ↦ ?_
  have hpos : 0 < radius := hradius
  have hroot : Real.sqrt (-2 * Real.log (Real.exp (-(radius * radius) / 2))) = radius := by
    rw [Real.log_exp, show -2 * (-(radius * radius) / 2) = radius * radius by ring,
      Real.sqrt_mul_self hpos.le]
  have habs : |-(radius * Real.exp (-(radius * radius) / 2))| =
      radius * Real.exp (-radius ^ 2 / 2) := by
    rw [abs_neg, abs_of_pos (mul_pos hpos (Real.exp_pos _)), sq]
  show ENNReal.ofReal |-(radius * Real.exp (-(radius * radius) / 2))| *
      G (Real.sqrt (-2 * Real.log (Real.exp (-(radius * radius) / 2)))) =
    ENNReal.ofReal (radius * Real.exp (-radius ^ 2 / 2)) * G radius
  rw [hroot, habs]

/-- NOTE2 §7.2: the integral of a measurable function against the standard bivariate Gaussian
law is its integral over the open unit square at the shifted Box–Muller point
`√(-2 log u) (cos (2πv - π), sin (2πv - π))`. -/
theorem lintegral_standardGaussianPair (F : ℝ × ℝ → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ point, F point ∂((ProbabilityTheory.gaussianReal 0 1).prod
        (ProbabilityTheory.gaussianReal 0 1)) =
      ∫⁻ u in Set.Ioo 0 1, ∫⁻ v in Set.Ioo 0 1,
        F (Real.sqrt (-2 * Real.log u) * Real.cos (2 * Real.pi * v - Real.pi),
          Real.sqrt (-2 * Real.log u) * Real.sin (2 * Real.pi * v - Real.pi)) := by
  rw [lintegral_standardGaussianPair_polar F hF]
  have hangle : ∀ radius : ℝ,
      ∫⁻ angle in Set.Ioo (-Real.pi) Real.pi,
        ENNReal.ofReal ((2 * Real.pi)⁻¹ * (radius * Real.exp (-radius ^ 2 / 2))) *
          F (radius * Real.cos angle, radius * Real.sin angle) =
      ENNReal.ofReal (radius * Real.exp (-radius ^ 2 / 2)) *
        ∫⁻ v in Set.Ioo 0 1, F (radius * Real.cos (2 * Real.pi * v - Real.pi),
          radius * Real.sin (2 * Real.pi * v - Real.pi)) := fun radius ↦ by
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_angle_substitution,
      mul_left_comm (ENNReal.ofReal _) (ENNReal.ofReal (2 * Real.pi)), ← mul_assoc,
      ← ENNReal.ofReal_mul Real.two_pi_pos.le, mul_inv_cancel_left₀ Real.two_pi_pos.ne']
  simp only [hangle]
  exact (lintegral_radius_substitution fun radius ↦ ∫⁻ v in Set.Ioo 0 1,
    F (radius * Real.cos (2 * Real.pi * v - Real.pi),
      radius * Real.sin (2 * Real.pi * v - Real.pi))).symm

/-- The standard bivariate Gaussian law is symmetric under the sign change of both
coordinates. -/
theorem map_neg_standardGaussianPair :
    Measure.map (fun point : ℝ × ℝ ↦ -point)
        ((ProbabilityTheory.gaussianReal 0 1).prod (ProbabilityTheory.gaussianReal 0 1)) =
      (ProbabilityTheory.gaussianReal 0 1).prod (ProbabilityTheory.gaussianReal 0 1) := by
  have hprod : (fun point : ℝ × ℝ ↦ -point) = Prod.map (fun x : ℝ ↦ -x) (fun x : ℝ ↦ -x) := rfl
  rw [hprod, ← Measure.map_prod_map _ _ measurable_neg measurable_neg,
    ProbabilityTheory.gaussianReal_map_neg, neg_zero]

/-! ### The Box–Muller theorem -/

/-- The Box–Muller map of a point of the unit square. -/
def boxMuller (point : ℝ × ℝ) : ℝ × ℝ :=
  (Real.sqrt (-2 * Real.log point.1) * Real.cos (2 * Real.pi * point.2),
    Real.sqrt (-2 * Real.log point.1) * Real.sin (2 * Real.pi * point.2))

/-- The Box–Muller map is measurable. -/
theorem measurable_boxMuller : Measurable boxMuller := by
  have hradius : Measurable fun point : ℝ × ℝ ↦ Real.sqrt (-2 * Real.log point.1) :=
    (measurable_const.mul (Real.measurable_log.comp measurable_fst)).sqrt
  have hangle : Measurable fun point : ℝ × ℝ ↦ 2 * Real.pi * point.2 :=
    measurable_const.mul measurable_snd
  exact (hradius.mul (Real.measurable_cos.comp hangle)).prodMk
    (hradius.mul (Real.measurable_sin.comp hangle))

/-- NOTE2 §7.2, the Box–Muller theorem on the unit square: the Box–Muller map carries Lebesgue
measure on the open unit square to the product of two standard Gaussian laws. -/
theorem map_boxMuller :
    Measure.map boxMuller
        ((volume.restrict (Set.Ioo (0 : ℝ) 1)).prod (volume.restrict (Set.Ioo (0 : ℝ) 1))) =
      (ProbabilityTheory.gaussianReal 0 1).prod (ProbabilityTheory.gaussianReal 0 1) := by
  refine Measure.ext fun s hs ↦ ?_
  have hneg : Measurable fun point : ℝ × ℝ ↦ -point := measurable_fst.neg.prodMk measurable_snd.neg
  have hreflected : Measurable
      (((fun point : ℝ × ℝ ↦ -point) ⁻¹' s).indicator (1 : ℝ × ℝ → ℝ≥0∞)) :=
    measurable_one.indicator (hneg hs)
  have hpulled : Measurable ((boxMuller ⁻¹' s).indicator (1 : ℝ × ℝ → ℝ≥0∞)) :=
    measurable_one.indicator (measurable_boxMuller hs)
  rw [← map_neg_standardGaussianPair, Measure.map_apply hneg hs,
    Measure.map_apply measurable_boxMuller hs, ← lintegral_indicator_one (hneg hs),
    ← lintegral_indicator_one (measurable_boxMuller hs),
    lintegral_standardGaussianPair _ hreflected, lintegral_prod _ hpulled.aemeasurable]
  refine lintegral_congr fun u ↦ lintegral_congr fun v ↦ ?_
  have hpoint : -(Real.sqrt (-2 * Real.log u) * Real.cos (2 * Real.pi * v - Real.pi),
      Real.sqrt (-2 * Real.log u) * Real.sin (2 * Real.pi * v - Real.pi)) = boxMuller (u, v) := by
    rw [Real.cos_sub_pi, Real.sin_sub_pi, Prod.neg_mk, mul_neg, mul_neg, neg_neg, neg_neg]
    rfl
  simp only [Set.indicator_apply, Set.mem_preimage, hpoint, Pi.one_apply]

/-- The Gaussian pair is measurable. -/
theorem measurable_gaussianPair : Measurable gaussianPair :=
  measurable_boxMuller.comp measurable_radialDraw_angularDraw

/-- NOTE2 §7.2, the Box–Muller theorem on fair bits: the law of the Gaussian pair under the
fair-bit measure is the product of two standard Gaussian laws. -/
theorem map_gaussianPair :
    Measure.map gaussianPair bitMeasure =
      (ProbabilityTheory.gaussianReal 0 1).prod (ProbabilityTheory.gaussianReal 0 1) := by
  have hcomp : gaussianPair = boxMuller ∘ fun stream ↦ (radialDraw stream, angularDraw stream) :=
    rfl
  rw [hcomp, ← Measure.map_map measurable_boxMuller measurable_radialDraw_angularDraw,
    map_radialDraw_angularDraw, map_boxMuller]

/-- NOTE2 §7.2: the first coordinate of the Gaussian pair is a standard Gaussian draw. -/
theorem map_gaussianPair_fst :
    Measure.map (fun stream ↦ (gaussianPair stream).1) bitMeasure =
      ProbabilityTheory.gaussianReal 0 1 := by
  have hcomp : (fun stream ↦ (gaussianPair stream).1) = Prod.fst ∘ gaussianPair := rfl
  rw [hcomp, ← Measure.map_map measurable_fst measurable_gaussianPair, map_gaussianPair,
    Measure.map_fst_prod, measure_univ, one_smul]

/-- NOTE2 §7.2: the second coordinate of the Gaussian pair is a standard Gaussian draw. -/
theorem map_gaussianPair_snd :
    Measure.map (fun stream ↦ (gaussianPair stream).2) bitMeasure =
      ProbabilityTheory.gaussianReal 0 1 := by
  have hcomp : (fun stream ↦ (gaussianPair stream).2) = Prod.snd ∘ gaussianPair := rfl
  rw [hcomp, ← Measure.map_map measurable_snd measurable_gaussianPair, map_gaussianPair,
    Measure.map_snd_prod, measure_univ, one_smul]

/-- NOTE2 §7.2, the Box–Muller theorem on fair bits: the two coordinates of the Gaussian pair are
independent. -/
theorem indepFun_gaussianPair :
    ProbabilityTheory.IndepFun (fun stream ↦ (gaussianPair stream).1)
      (fun stream ↦ (gaussianPair stream).2) bitMeasure := by
  rw [ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map
      (measurable_fst.comp measurable_gaussianPair).aemeasurable
      (measurable_snd.comp measurable_gaussianPair).aemeasurable,
    map_gaussianPair_fst, map_gaussianPair_snd]
  exact map_gaussianPair

/-- NOTE2 §7.2: the expectation of a measurable integrand of the Gaussian pair, depending on the
angle as well as the radius, is its integral against the standard bivariate Gaussian law. -/
theorem integral_gaussianPair (f : ℝ × ℝ → ℝ) (hf : Measurable f) :
    ∫ stream, f (gaussianPair stream) ∂bitMeasure =
      ∫ point, f point ∂((ProbabilityTheory.gaussianReal 0 1).prod
        (ProbabilityTheory.gaussianReal 0 1)) := by
  rw [← map_gaussianPair,
    integral_map measurable_gaussianPair.aemeasurable hf.aestronglyMeasurable]

/-- NOTE2 §7.2, a closed-form check on an integrand depending on the angle: the product of the
two coordinates of the Gaussian pair has expectation zero. -/
theorem integral_gaussianPair_fst_mul_snd :
    ∫ stream, (gaussianPair stream).1 * (gaussianPair stream).2 ∂bitMeasure = 0 := by
  rw [integral_gaussianPair (fun point ↦ point.1 * point.2) (measurable_fst.mul measurable_snd),
    integral_prod_mul (fun x : ℝ ↦ x) (fun y : ℝ ↦ y),
    ProbabilityTheory.integral_id_gaussianReal, zero_mul]

end

end Descent.Portability.CylinderBoxMullerLaw
