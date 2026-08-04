/-
Copyright (c) 2026 Gnomon contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gnomon contributors
-/
import Calibrator.UnifiedBiology

/-!
# Exact pooled-correction normal form in biology

This module identifies the algebraic correction split for the binary biological witness.  Pooling
retains one common mode and erases one contrast mode.  The canonical broadcast-after-pooling map
is an idempotent projection, and every field has an exact and unique common/contrast decomposition.
Thus the correction obstruction and the biological interpretation agree at the level of operators,
not merely at the level of one numerical example.
-/

namespace Calibrator

/-- The canonical correction that pools a biological field and broadcasts its mean back to both
dynamics. -/
noncomputable def dynamicsPooledProjector : (Bool → ℝ) →ₗ[ℝ] (Bool → ℝ) :=
  dynamicsBroadcast.comp dynamicsPoolingObservation

/-- The pooled projector replaces both dynamics-specific values by their arithmetic mean. -/
theorem dynamicsPooledProjector_apply (β : Bool → ℝ) (persists : Bool) :
    dynamicsPooledProjector β persists = (β false + β true) / 2 := by
  rfl

/-- Pooling and rebroadcasting is an idempotent correction. -/
theorem dynamicsPooledProjector_idempotent :
    dynamicsPooledProjector.comp dynamicsPooledProjector = dynamicsPooledProjector := by
  ext β persists
  simp only [LinearMap.comp_apply, dynamicsPooledProjector_apply]
  ring

/-- A biological field is fixed by pooled correction exactly when persistence and switching have
the same value. -/
theorem dynamicsPooledProjector_fixed_iff (β : Bool → ℝ) :
    dynamicsPooledProjector β = β ↔ β false = β true := by
  constructor
  · intro h
    have hfalse := congrFun h false
    have htrue := congrFun h true
    rw [dynamicsPooledProjector_apply] at hfalse htrue
    linarith
  · intro h
    funext persists
    rw [dynamicsPooledProjector_apply]
    cases persists
    · linarith
    · linarith

/-- The scalar amplitude of the persistence-versus-switching component of a biological field. -/
noncomputable def dynamicsContrastCoefficient (β : Bool → ℝ) : ℝ :=
  (β true - β false) / 2

/-- **Exact biological correction normal form.**  Every two-dynamics field is the sum of its
pooled, recoverable component and one scalar multiple of the correction-blind contrast. -/
theorem dynamics_common_contrast_decomposition (β : Bool → ℝ) :
    β = dynamicsPooledProjector β + dynamicsContrastCoefficient β • dynamicsContrast := by
  funext persists
  cases persists <;>
    simp [dynamicsPooledProjector_apply, dynamicsContrastCoefficient, dynamicsContrast] <;>
    ring

/-- The residual of canonical pooled correction is exactly the contrast component. -/
theorem dynamicsPooledProjector_residual (β : Bool → ℝ) :
    β - dynamicsPooledProjector β = dynamicsContrastCoefficient β • dynamicsContrast := by
  funext persists
  cases persists <;>
    simp [dynamicsPooledProjector_apply, dynamicsContrastCoefficient, dynamicsContrast] <;>
    ring

/-- The canonical pooled projector is representable by every positive uniform dictionary order. -/
theorem dynamicsPooledProjector_mem_uniformCorrectionFamily
    (k : ℕ) (hk : 0 < k) :
    dynamicsPooledProjector ∈ UniformCorrectionFamily dynamicsPoolingObservation k := by
  apply factorsThrough_subset_uniformCorrectionFamily dynamicsPoolingObservation k hk
  exact ⟨dynamicsBroadcast, rfl⟩

/-- Every admissible biological correction gives the same output to fields with the same pooled
sum, even if their persistence/switching contrasts differ. -/
theorem factoredDynamicsCorrection_eq_of_pooledSum_eq
    (C : (Bool → ℝ) →ₗ[ℝ] (Bool → ℝ))
    (hC : FactorsThrough dynamicsPoolingObservation C)
    (β γ : Bool → ℝ) (hpool : β false + β true = γ false + γ true) :
    C β = C γ := by
  apply hC.apply_eq_of_observation_eq dynamicsPoolingObservation C β γ
  exact hpool

/-- **Contrast-orbit blindness.**  Moving any biological field by any amount along the
persistence/switching contrast leaves every factored correction unchanged. -/
theorem factoredDynamicsCorrection_add_contrast
    (C : (Bool → ℝ) →ₗ[ℝ] (Bool → ℝ))
    (hC : FactorsThrough dynamicsPoolingObservation C)
    (β : Bool → ℝ) (c : ℝ) :
    C (β + c • dynamicsContrast) = C β := by
  apply hC.apply_eq_of_observation_eq dynamicsPoolingObservation C
  simp [dynamicsPoolingObservation, dynamicsContrast]
  ring

/-- Every finite uniform biological correction is constant along the entire contrast orbit. -/
theorem uniformDynamicsCorrection_add_contrast
    (k : ℕ) (C : (Bool → ℝ) →ₗ[ℝ] (Bool → ℝ))
    (hC : C ∈ UniformCorrectionFamily dynamicsPoolingObservation k)
    (β : Bool → ℝ) (c : ℝ) :
    C (β + c • dynamicsContrast) = C β := by
  exact factoredDynamicsCorrection_add_contrast C
    (uniformCorrectionFamily_subset_factorsThrough dynamicsPoolingObservation k hC) β c

/-- The contrast coefficient of the common mode vanishes. -/
theorem dynamicsContrastCoefficient_commonMode :
    dynamicsContrastCoefficient dynamicsCommonMode = 0 := by
  norm_num [dynamicsContrastCoefficient, dynamicsCommonMode, binaryFirstAnnotation,
    binarySecondAnnotation]

/-- The contrast coefficient of the normalized contrast is one. -/
theorem dynamicsContrastCoefficient_contrast :
    dynamicsContrastCoefficient dynamicsContrast = 1 := by
  norm_num [dynamicsContrastCoefficient, dynamicsContrast]

/-- The common coordinate in a common/contrast decomposition is the pooled mean. -/
theorem dynamics_common_coordinate_eq
    (β : Bool → ℝ) (common coefficient : ℝ)
    (hβ : β = (fun _ ↦ common) + coefficient • dynamicsContrast) :
    common = (β false + β true) / 2 := by
  have hfalse := congrFun hβ false
  have htrue := congrFun hβ true
  simp [dynamicsContrast] at hfalse htrue
  linarith

/-- The contrast coordinate in a common/contrast decomposition is the contrast coefficient. -/
theorem dynamics_contrast_coordinate_eq
    (β : Bool → ℝ) (common coefficient : ℝ)
    (hβ : β = (fun _ ↦ common) + coefficient • dynamicsContrast) :
    coefficient = dynamicsContrastCoefficient β := by
  have hfalse := congrFun hβ false
  have htrue := congrFun hβ true
  simp [dynamicsContrast, dynamicsContrastCoefficient] at hfalse htrue ⊢
  linarith

/-- The exact normal form bundled as the biological correction theorem consumed by downstream
applications. -/
structure BiologicalCorrectionNormalForm : Prop where
  /-- Pooling followed by broadcasting is idempotent. -/
  projector_idempotent :
    dynamicsPooledProjector.comp dynamicsPooledProjector = dynamicsPooledProjector
  /-- The fixed points are exactly the fields that agree across both dynamics. -/
  fixed_exactly_on_common_fields :
    ∀ β : Bool → ℝ, dynamicsPooledProjector β = β ↔ β false = β true
  /-- The correction residual is exactly the persistence/switching contrast. -/
  residual_exactly_contrast :
    ∀ β : Bool → ℝ,
      β - dynamicsPooledProjector β = dynamicsContrastCoefficient β • dynamicsContrast
  /-- Every positive dictionary order represents the pooled projector. -/
  represented_at_every_positive_order :
    ∀ k : ℕ, 0 < k → dynamicsPooledProjector ∈
      UniformCorrectionFamily dynamicsPoolingObservation k
  /-- Every represented correction is blind to translations along the contrast. -/
  all_uniform_corrections_contrast_blind :
    ∀ (k : ℕ) (C : (Bool → ℝ) →ₗ[ℝ] (Bool → ℝ)),
      C ∈ UniformCorrectionFamily dynamicsPoolingObservation k →
        ∀ (β : Bool → ℝ) (c : ℝ), C (β + c • dynamicsContrast) = C β

/-- **Biological correction theorem.**  Pooling is exactly a projection onto shared biology; its
entire complement is the one-dimensional dynamics contrast already identified with calibration
drift in `UnifiedBiology`. -/
theorem biologicalCorrectionNormalForm : BiologicalCorrectionNormalForm where
  projector_idempotent := dynamicsPooledProjector_idempotent
  fixed_exactly_on_common_fields := dynamicsPooledProjector_fixed_iff
  residual_exactly_contrast := dynamicsPooledProjector_residual
  represented_at_every_positive_order := dynamicsPooledProjector_mem_uniformCorrectionFamily
  all_uniform_corrections_contrast_blind := uniformDynamicsCorrection_add_contrast

end Calibrator
