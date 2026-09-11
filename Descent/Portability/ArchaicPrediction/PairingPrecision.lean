/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.ArchaicPrediction.ResponseGraph
import Descent.Portability.ArchaicPrediction.ResponsePanels
import Mathlib.MeasureTheory.Integral.Bochner.Basic

assert_below Descent.Decision Descent.Program

/-!
# Sum-incidence information and general measurement laws

The known-offset pairing model has a different design from response
differences. Its normal operator is the signless information form. Odd
cycles prove invertibility; a homozygote contributes twice its haplotype
coefficient. Precision identities below permit arbitrary noise distributions
with the stated first and second moments, including continuous Gaussian laws.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.ArchaicPrediction

open MeasureTheory
open scoped BigOperators RealInnerProductSpace
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ E]
  [FiniteDimensional ℝ F]

/-- The resistance covariance identity without finite support on the noise law. -/
theorem integral_contrast_precision {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (B : E →L[ℝ] F) (hB : Function.Injective B) (m c : E) (ε : Ω → F)
    (hmean : ∀ v : F, (∫ ω, ⟪v, ε ω⟫ ∂μ) = 0)
    (hcov : ∀ v : F, (∫ ω, ⟪v, ε ω⟫ ^ 2 ∂μ) = ⟪v, v⟫) :
    (∫ ω, ⟪c, contrastFit B (B m + ε ω) - m⟫ ∂μ) = 0 ∧
    (∫ ω, ⟪c, contrastFit B (B m + ε ω) - m⟫ ^ 2 ∂μ) = ⟪c, contrastInverse B c⟫ := by
  simp_rw [contrast_fit_error B hB]
  constructor
  · exact hmean _
  · rw [hcov, ← contrastNormal_inner, contrastInverse_right B hB]
    exact real_inner_comm _ _

variable {V A : Type*} [Fintype V] [Fintype A]

/-- Weighted sum-incidence design, with coefficient two on homozygous edges. -/
noncomputable def pairingDesign (left right : A → V) (w : A → ℝ) :
    EuclideanSpace ℝ V →L[ℝ] EuclideanSpace ℝ A :=
  LinearMap.toContinuousLinearMap
    { toFun := fun m => WithLp.toLp 2 (fun e => Real.sqrt (w e) * (m (left e) + m (right e)))
      map_add' := by intro a b; ext e; simp; ring
      map_smul' := by intro c a; ext e; simp; ring }

theorem pairingDesign_injective (left right : A → V) (w : A → ℝ) (hw : ∀ e, 0 < w e)
    (hc : PairingConnected (comparisonAdjacent left right))
    (ho : ∃ v n, PairingWalk (comparisonAdjacent left right) v v n ∧ Odd n) :
    Function.Injective (pairingDesign left right w) := by
  have hker (a : EuclideanSpace ℝ V) (ha : pairingDesign left right w a = 0) : a = 0 := by
    have he (e : A) : a (left e) + a (right e) = 0 := by
      have h := congrArg (fun b : EuclideanSpace ℝ A => b e) ha
      change Real.sqrt (w e) * (a (left e) + a (right e)) = 0 at h
      exact (mul_eq_zero.mp h).resolve_left (Real.sqrt_pos.mpr (hw e)).ne'
    have hn : PairingNull (comparisonAdjacent left right) (fun v => a v) := by
      intro u v huv
      obtain ⟨e, h | h⟩ := huv
      · obtain ⟨rfl, rfl⟩ := h
        exact he e
      · obtain ⟨rfl, rfl⟩ := h
        simpa only [add_comm] using he e
    obtain ⟨v, n, hp, hodd⟩ := ho
    have hz := pairing_null_zero_of_odd hc hn hp hodd
    ext v
    exact congrFun hz v
  intro a b hab
  exact sub_eq_zero.mp (hker (a - b) (by simp [hab]))

/-- The signless information form is positive definite when responses identify haplotypes. -/
theorem pairing_information_positive (left right : A → V) (w : A → ℝ) (hw : ∀ e, 0 < w e)
    (hc : PairingConnected (comparisonAdjacent left right))
    (ho : ∃ v n, PairingWalk (comparisonAdjacent left right) v v n ∧ Odd n)
    (a : EuclideanSpace ℝ V) (ha : a ≠ 0) :
    0 < ⟪a, contrastNormal (pairingDesign left right w) a⟫ := by
  rw [contrastNormal_inner, real_inner_self_eq_norm_sq]
  apply sq_pos_of_pos
  exact norm_pos_iff.mpr (fun hz => ha (pairingDesign_injective left right w hw hc ho
    (by simpa using hz)))

/-- Equation (7.7): the triangle contribution estimator has variance `3σ²/4`. -/
theorem triangle_contribution_variance {Ω : Type*} [Fintype Ω]
    (prob : Ω → ℝ) (noise : Fin 3 → Ω → ℝ) (noiseVar : ℝ)
    (hsecond : ∀ i j, weightedMean prob (fun ω => noise i ω * noise j ω) =
      if i = j then noiseVar else 0) :
    weightedMean prob (fun ω => ((noise 0 ω + noise 1 ω - noise 2 ω) / 2) ^ 2) =
      3 * noiseVar / 4 := by
  have h := orthogonal_noise_risk prob noise (fun _ => noiseVar) hsecond ![1/2, 1/2, -1/2]
  norm_num [Fin.sum_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two] at h
  convert h using 1
  · congr 1
    funext ω
    ring
  · ring

end Descent.Portability.ArchaicPrediction
