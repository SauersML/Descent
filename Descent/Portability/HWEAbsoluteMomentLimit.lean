/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.HWEAmplitudeWeakLimit

assert_below Descent.Decision Descent.Program

/-!
The first absolute moment of the actual square-biased normalized interaction
converges to exp(-2K). The finite-row formula is a square root of the exact
zero-heterozygote mass plus the already controlled exceptional first moment.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.HWEAbsoluteMomentLimit

open scoped BigOperators Topology
open Filter Foundations HWEInteractionLaw HWEHomozygoteLimit HWEHomozygoteConditioning
open HWEAbsoluteLocusLaw HWEAbsoluteLocusBounds HWEExceptionalAmplitude HWEExceptionalLimit

/-- The homozygous absolute product is exactly the square root of its event probability. -/
theorem homo_product_sqrt {ι : Type*} [Fintype ι] [DecidableEq ι]
    (h : ι → HardyWeinbergModel)
    (h0 : ∀ i, 0 < (h i).altFreq) (h1 : ∀ i, (h i).altFreq < 1) :
    ∏ i, homoMass (h i) = Real.sqrt (zeroMass h) := by
  have he : zeroMass h = (∏ i, homoMass (h i)) ^ 2 := by
    simp only [zeroMass, ← Finset.prod_pow, homoMass_square _ (h0 _) (h1 _),
      HWEHeterozygosityLaw.probability]
  rw [he, Real.sqrt_sq (Finset.prod_nonneg (fun i _ ↦ (masses_nonneg _).1))]

/-- Exact finite-row first moment decomposition. -/
theorem absolute_moment_decomposition {ι : Type*} [Fintype ι] [DecidableEq ι]
    (h : ι → HardyWeinbergModel)
    (h0 : ∀ i, 0 < (h i).altFreq) (h1 : ∀ i, (h i).altFreq < 1) :
    (independentLaw (fun i ↦ squareBiasedLocus (h i) (h0 i) (h1 i))).expectation
      (fun x ↦ |normalized h x|) = exceptionalMoment h h0 h1 + Real.sqrt (zeroMass h) := by
  rw [exceptionalMoment, exceptional_product_difference, total_absolute_product,
    ← homo_product_sqrt h h0 h1]
  ring

/-- The derived absolute first-moment limit, under the same heterogeneous assumptions. -/
theorem absolute_moment_limit (h : (m : ℕ) → Fin m → HardyWeinbergModel)
    (h0 : ∀ m i, 0 < (h m i).altFreq) (h1 : ∀ m i, (h m i).altFreq < 1)
    (ε : ℕ → ℝ) (hcap : ∀ m i, |(h m i).altFreq - 1 / 2| ≤ ε m)
    (hε : Tendsto ε atTop (𝓝 0)) (K : ℝ)
    (hK : Tendsto (fun m ↦ ∑ i, ((h m i).altFreq - 1 / 2) ^ 2) atTop (𝓝 K)) :
    Tendsto (fun m ↦
      (independentLaw (fun i ↦ squareBiasedLocus (h m i) (h0 m i) (h1 m i))).expectation
        (fun x ↦ |normalized (h m) x|)) atTop (𝓝 (Real.exp (-2 * K))) := by
  have hz : Tendsto (fun m ↦ zeroMass (h m)) atTop (𝓝 (Real.exp (-4 * K))) := by
    simpa only [HWEHeterozygosityLimit.zero_count_probability, zeroMass] using
      HWEHeterozygosityLimit.zero_count_probability_limit h h0 h1 ε hcap hε K hK
  have hs := Real.continuous_sqrt.continuousAt.tendsto.comp hz
  have he : Real.sqrt (Real.exp (-4 * K)) = Real.exp (-2 * K) := by
    rw [← Real.exp_half]
    congr 1
    ring
  have hh := (exceptional_L1_limit h h0 h1 ε hcap hε K hK).add hs
  simpa only [Function.comp_def, he, zero_add, ← absolute_moment_decomposition] using hh

end Descent.Portability.HWEAbsoluteMomentLimit
