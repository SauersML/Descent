/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.HWEConditionalScaleLimit

assert_below Descent.Decision Descent.Program

/-!
The original conditional HWE amplitude has the same first absolute moment as
its reciprocal. This follows from the probability-preserving flip of all fair
homozygous signs. At a diverging amplitude scale the reciprocal tends to zero
in L1, providing a quantitative input for the escaping heterozygosity layers.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.HWEConditionalInverseMoment

open scoped BigOperators Topology NNReal
open Filter Foundations HWEInteractionLaw HWEHomozygoteLimit HWEConditionalScaleLimit
open BalancedHWEWeakLimit RademacherArrayWeakLimit RademacherParityLaw HWELogCoordinates

/-- Flip each of the actual fair homozygous signs. -/
def flipSigns {ι : Type*} : (ι → Bool) ≃ (ι → Bool) where
  toFun b := fun i ↦ !(b i)
  invFun b := fun i ↦ !(b i)
  left_inv b := by funext i; simp
  right_inv b := by funext i; simp

/-- Flipping a locus changes the standardized fair sign by a minus sign. -/
theorem signValue_not (b : Bool) : signValue (!b) = -signValue b := by
  cases b <;> norm_num [signValue]

/-- Sign flips negate the exact weighted log coordinate. -/
theorem weightedSum_flip {ι : Type*} [Fintype ι] (a : ι → ℝ) (b : ι → Bool) :
    weightedSum a (flipSigns b) = -weightedSum a b := by
  simp only [weightedSum, flipSigns, Equiv.coe_fn_mk, signValue_not, mul_neg,
    Finset.sum_neg_distrib]

/-- The entire finite fair-sign experiment is invariant under this flip. -/
theorem expectation_flip {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : (ι → Bool) → ℝ) :
    (independentLaw (fun _ : ι ↦ signLaw)).expectation (fun b ↦ f (flipSigns b)) =
      (independentLaw (fun _ : ι ↦ signLaw)).expectation f := by
  unfold FiniteReportLaw.expectation
  apply Fintype.sum_equiv flipSigns
  intro b
  rfl

/-- The actual amplitude's absolute value is its positive exponential log profile. -/
theorem sign_absolute_value {ι : Type*} [Fintype ι] [DecidableEq ι]
    (h : ι → HardyWeinbergModel)
    (h0 : ∀ i, 0 < (h i).altFreq) (h1 : ∀ i, (h i).altFreq < 1) (b : ι → Bool) :
    |signAmplitude h b| =
      Real.exp (-weightedSum (fun i ↦ coordinate ((h i).altFreq - 1 / 2)) b) := by
  rw [signAmplitude, normalized_homoVector h h0 h1]
  rcases sq_eq_one_iff.mp (parity_square b) with hb | hb <;>
    simp [hb, abs_of_pos (Real.exp_pos _)]

/-- Conditional homozygous amplitudes never vanish. -/
theorem signAmplitude_ne_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    (h : ι → HardyWeinbergModel)
    (h0 : ∀ i, 0 < (h i).altFreq) (h1 : ∀ i, (h i).altFreq < 1) (b : ι → Bool) :
    signAmplitude h b ≠ 0 := by
  apply abs_pos.mp
  rw [sign_absolute_value h h0 h1]
  exact Real.exp_pos _

/-- Reciprocal amplitude is exactly the flipped amplitude in absolute value. -/
theorem reciprocal_absolute_value {ι : Type*} [Fintype ι] [DecidableEq ι]
    (h : ι → HardyWeinbergModel)
    (h0 : ∀ i, 0 < (h i).altFreq) (h1 : ∀ i, (h i).altFreq < 1) (b : ι → Bool) :
    |(signAmplitude h b)⁻¹| = |signAmplitude h (flipSigns b)| := by
  rw [abs_inv, sign_absolute_value h h0 h1, sign_absolute_value h h0 h1,
    weightedSum_flip, neg_neg, ← Real.exp_neg, neg_neg]

/-- Exact equality of reciprocal and ordinary absolute moments under the actual sign law. -/
theorem reciprocal_absolute_moment {ι : Type*} [Fintype ι] [DecidableEq ι]
    (h : ι → HardyWeinbergModel)
    (h0 : ∀ i, 0 < (h i).altFreq) (h1 : ∀ i, (h i).altFreq < 1) :
    (independentLaw (fun _ : ι ↦ signLaw)).expectation (fun b ↦ |(signAmplitude h b)⁻¹|) =
      (independentLaw (fun _ : ι ↦ signLaw)).expectation (fun b ↦ |signAmplitude h b|) := by
  simp only [reciprocal_absolute_value h h0 h1]
  exact expectation_flip (fun b ↦ |signAmplitude h b|)

/-- Actual reciprocal L1 collapse whenever the deterministic amplitude scale escapes. -/
theorem reciprocal_scaled_limit (h : (m : ℕ) → Fin m → HardyWeinbergModel)
    (h0 : ∀ m i, 0 < (h m i).altFreq) (h1 : ∀ m i, (h m i).altFreq < 1)
    (ε : ℕ → ℝ) (hcap : ∀ m i, |(h m i).altFreq - 1 / 2| ≤ ε m)
    (hε : Tendsto ε atTop (𝓝 0)) (K : ℝ)
    (hK : Tendsto (fun m ↦ ∑ i, ((h m i).altFreq - 1 / 2) ^ 2) atTop (𝓝 K))
    (a : ℕ → ℝ) (ha : Tendsto (fun m ↦ |a m|) atTop atTop) :
    Tendsto (fun m ↦ (independentLaw (fun _ : Fin m ↦ signLaw)).expectation
      (fun b ↦ |(a m * signAmplitude (h m) b)⁻¹|)) atTop (𝓝 0) := by
  have he (m : ℕ) :
      (independentLaw (fun _ : Fin m ↦ signLaw)).expectation
        (fun b ↦ |(a m * signAmplitude (h m) b)⁻¹|) =
          |a m|⁻¹ * (independentLaw (fun _ : Fin m ↦ signLaw)).expectation
            (fun b ↦ |signAmplitude (h m) b|) := by
    rw [← reciprocal_absolute_moment (h m) (h0 m) (h1 m)]
    simp only [FiniteReportLaw.expectation, mul_inv_rev, abs_mul, abs_inv, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    ring
  simpa only [he, zero_mul] using
    (tendsto_inv_atTop_zero.comp ha).mul (sign_absolute_limit h h0 h1 ε hcap hε K hK)

end Descent.Portability.HWEConditionalInverseMoment
