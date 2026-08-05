/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Conditionals.DynamicsContrast

/-!
# Exact pooled-correction normal form in biology

This module identifies the algebraic correction split for the binary biological witness.  Pooling
retains one common mode and erases one contrast mode.  The canonical broadcast-after-pooling map
is an idempotent projection, and every field has an exact and unique common/contrast decomposition.
Thus the correction obstruction and the biological interpretation agree at the level of operators,
not merely at the level of one numerical example.
-/

namespace Descent.Portability

/-- The canonical correction that pools a biological field and broadcasts its mean back to both
dynamics. -/
noncomputable def dynamicsPooledProjector : (Bool → ℝ) →ₗ[ℝ] (Bool → ℝ) :=
  Conditionals.dynamicsBroadcast.comp Conditionals.dynamicsPoolingObservation

/-- The pooled projector replaces both dynamics-specific values by their arithmetic mean. -/
theorem dynamicsPooledProjector_apply (β : Bool → ℝ) (persists : Bool) :
    dynamicsPooledProjector β persists = (β false + β true) / 2 := by
  rfl

/-- Pooling and rebroadcasting is an idempotent correction. -/
theorem dynamicsPooledProjector_idempotent :
    dynamicsPooledProjector.comp dynamicsPooledProjector = dynamicsPooledProjector := by
  PopGen.ext β persists
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

/-- The residual of canonical pooled correction is exactly the contrast component. -/
theorem dynamicsPooledProjector_residual (β : Bool → ℝ) :
    β - dynamicsPooledProjector β = dynamicsContrastCoefficient β • Conditionals.dynamicsContrast := by
  funext persists
  cases persists <;>
    simp [dynamicsPooledProjector_apply, dynamicsContrastCoefficient, Conditionals.dynamicsContrast] <;>
    ring

/-- **Exact biological correction normal form.**  Every two-dynamics field is the sum of its
pooled, recoverable component and one scalar multiple of the correction-blind contrast.

This is the residual identity above rearranged, not a second computation: "what pooled
correction misses is the contrast" and "field = pooled + contrast" are one fact. -/
theorem dynamics_common_contrast_decomposition (β : Bool → ℝ) :
    β = dynamicsPooledProjector β + dynamicsContrastCoefficient β • Conditionals.dynamicsContrast :=
  sub_eq_iff_eq_add'.mp (dynamicsPooledProjector_residual β)

/-- **Exact pooling fiber.** Two persistence/switching fields have the same pooled observation
if and only if one is obtained from the other by the uniquely normalized contrast translation.
The coefficient is not existentially hidden: it is exactly the difference of the two contrast
coordinates.  Thus pooling loses precisely one biological direction and no other information. -/
theorem dynamicsPoolingObservation_eq_iff_contrast_translation (β γ : Bool → ℝ) :
    Conditionals.dynamicsPoolingObservation β = Conditionals.dynamicsPoolingObservation γ ↔
      γ = β + (dynamicsContrastCoefficient γ - dynamicsContrastCoefficient β) •
        dynamicsContrast := by
  constructor
  · intro hpool
    funext persists
    change β false + β true = γ false + γ true at hpool
    cases persists <;>
      simp [dynamicsContrastCoefficient, Conditionals.dynamicsContrast] <;>
      linarith
  · intro htranslation
    rw [htranslation]
    simp [Conditionals.dynamicsPoolingObservation, Conditionals.dynamicsContrast]
    ring

/-- Equivalent existential description of the same fiber.  The explicit theorem above gives the
canonical witness; this form is convenient when only orbit membership matters. -/
theorem dynamicsPoolingObservation_eq_iff_exists_add_contrast (β γ : Bool → ℝ) :
    Conditionals.dynamicsPoolingObservation β = Conditionals.dynamicsPoolingObservation γ ↔
      ∃ c : ℝ, γ = β + c • Conditionals.dynamicsContrast := by
  constructor
  · intro hpool
    exact ⟨dynamicsContrastCoefficient γ - dynamicsContrastCoefficient β,
      (dynamicsPoolingObservation_eq_iff_contrast_translation β γ).mp hpool⟩
  · rintro ⟨c, rfl⟩
    simp [Conditionals.dynamicsPoolingObservation, Conditionals.dynamicsContrast]
    ring

/-- The canonical pooled projector is representable by every positive uniform dictionary order. -/
theorem dynamicsPooledProjector_mem_uniformCorrectionFamily
    (k : ℕ) (hk : 0 < k) :
    dynamicsPooledProjector ∈ UniformCorrectionFamily Conditionals.dynamicsPoolingObservation k := by
  apply factorsThrough_subset_uniformCorrectionFamily Conditionals.dynamicsPoolingObservation k hk
  exact ⟨Conditionals.dynamicsBroadcast, rfl⟩

/-- Every admissible biological correction gives the same output to fields with the same pooled
sum, even if their persistence/switching contrasts differ. -/
theorem factoredDynamicsCorrection_eq_of_pooledSum_eq
    (C : (Bool → ℝ) →ₗ[ℝ] (Bool → ℝ))
    (hC : FactorsThroughObservation Conditionals.dynamicsPoolingObservation C)
    (β γ : Bool → ℝ) (hpool : β false + β true = γ false + γ true) :
    C β = C γ := by
  apply hC.apply_eq_of_observation_eq Conditionals.dynamicsPoolingObservation C β γ
  exact hpool

/-- **Contrast-orbit blindness.**  Moving any biological field by any amount along the
persistence/switching contrast leaves every factored correction unchanged. -/
theorem factoredDynamicsCorrection_add_contrast
    (C : (Bool → ℝ) →ₗ[ℝ] (Bool → ℝ))
    (hC : FactorsThroughObservation Conditionals.dynamicsPoolingObservation C)
    (β : Bool → ℝ) (c : ℝ) :
    C (β + c • Conditionals.dynamicsContrast) = C β := by
  apply hC.apply_eq_of_observation_eq Conditionals.dynamicsPoolingObservation C
  simp [Conditionals.dynamicsPoolingObservation, Conditionals.dynamicsContrast]
  ring

/-- Pooling after canonical correction preserves exactly the observed biological total. -/
theorem dynamicsPoolingObservation_projector (β : Bool → ℝ) :
    Conditionals.dynamicsPoolingObservation (dynamicsPooledProjector β) =
      Conditionals.dynamicsPoolingObservation β := by
  simp [Conditionals.dynamicsPoolingObservation, dynamicsPooledProjector_apply]

/-- **Canonicality of pooled biological correction.** Among all linear corrections that only use
the pooled observation, broadcasting the pooled mean is the unique correction that fixes every
field shared by persistence and switching. Thus the normal form is forced by the observation
model and exactness on common biology; it is not merely a convenient choice of representative. -/
theorem dynamicsPooledProjector_eq_of_factorsThrough_of_fixes_common
    (C : (Bool → ℝ) →ₗ[ℝ] (Bool → ℝ))
    (hC : FactorsThroughObservation Conditionals.dynamicsPoolingObservation C)
    (hcommon : ∀ c : ℝ, C (fun _ : Bool ↦ c) = fun _ : Bool ↦ c) :
    C = dynamicsPooledProjector := by
  apply LinearMap.ext
  intro field
  funext persists
  have hdecomp := dynamics_common_contrast_decomposition field
  have hblind := factoredDynamicsCorrection_add_contrast C hC
    (dynamicsPooledProjector field) (dynamicsContrastCoefficient field)
  have hCfield : C field = C (dynamicsPooledProjector field) := by
    calc
      C field = C (dynamicsPooledProjector field +
          dynamicsContrastCoefficient field • Conditionals.dynamicsContrast) := congrArg C hdecomp
      _ = C (dynamicsPooledProjector field) := hblind
  have hprojector :
      dynamicsPooledProjector field =
        fun _ : Bool ↦ (field false + field true) / 2 := by
    funext state
    exact dynamicsPooledProjector_apply field state
  have hCprojector : C (dynamicsPooledProjector field) = dynamicsPooledProjector field := by
    rw [hprojector]
    exact hcommon ((field false + field true) / 2)
  exact congrFun (hCfield.trans hCprojector) persists

/-- Every finite uniform correction that is exact on common biology is the canonical pooled
projector, independently of dictionary order. -/
theorem uniformDynamicsCorrection_eq_pooledProjector
    (k : ℕ) (C : (Bool → ℝ) →ₗ[ℝ] (Bool → ℝ))
    (hC : C ∈ UniformCorrectionFamily Conditionals.dynamicsPoolingObservation k)
    (hcommon : ∀ c : ℝ, C (fun _ : Bool ↦ c) = fun _ : Bool ↦ c) :
    C = dynamicsPooledProjector :=
  dynamicsPooledProjector_eq_of_factorsThrough_of_fixes_common C
    (uniformCorrectionFamily_subset_factorsThrough Conditionals.dynamicsPoolingObservation k hC) hcommon

/-- Every finite uniform biological correction is constant along the entire contrast orbit. -/
theorem uniformDynamicsCorrection_add_contrast
    (k : ℕ) (C : (Bool → ℝ) →ₗ[ℝ] (Bool → ℝ))
    (hC : C ∈ UniformCorrectionFamily Conditionals.dynamicsPoolingObservation k)
    (β : Bool → ℝ) (c : ℝ) :
    C (β + c • Conditionals.dynamicsContrast) = C β := by
  exact factoredDynamicsCorrection_add_contrast C
    (uniformCorrectionFamily_subset_factorsThrough Conditionals.dynamicsPoolingObservation k hC) β c

/-- The contrast coefficient of the common mode vanishes. -/
theorem dynamicsContrastCoefficient_commonMode :
    dynamicsContrastCoefficient Conditionals.dynamicsCommonMode = 0 := by
  norm_num [dynamicsContrastCoefficient, Conditionals.dynamicsCommonMode, Spectral.binaryFirstAnnotation,
    Spectral.binarySecondAnnotation]

/-- The contrast coefficient of the normalized contrast is one. -/
theorem dynamicsContrastCoefficient_contrast :
    dynamicsContrastCoefficient Conditionals.dynamicsContrast = 1 := by
  norm_num [dynamicsContrastCoefficient, Conditionals.dynamicsContrast]

/-- The common coordinate in a common/contrast decomposition is the pooled mean. -/
theorem dynamics_common_coordinate_eq
    (β : Bool → ℝ) (common coefficient : ℝ)
    (hβ : β = (fun _ ↦ common) + coefficient • Conditionals.dynamicsContrast) :
    common = (β false + β true) / 2 := by
  have hfalse := congrFun hβ false
  have htrue := congrFun hβ true
  simp [Conditionals.dynamicsContrast] at hfalse htrue
  linarith

/-- The contrast coordinate in a common/contrast decomposition is the contrast coefficient. -/
theorem dynamics_contrast_coordinate_eq
    (β : Bool → ℝ) (common coefficient : ℝ)
    (hβ : β = (fun _ ↦ common) + coefficient • Conditionals.dynamicsContrast) :
    coefficient = dynamicsContrastCoefficient β := by
  have hfalse := congrFun hβ false
  have htrue := congrFun hβ true
  simp [Conditionals.dynamicsContrast, dynamicsContrastCoefficient] at hfalse htrue ⊢
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
      β - dynamicsPooledProjector β = dynamicsContrastCoefficient β • Conditionals.dynamicsContrast
  /-- Observation fibers are exactly the affine orbits of the dynamics contrast. -/
  pooling_fiber_exact :
    ∀ β γ : Bool → ℝ,
      Conditionals.dynamicsPoolingObservation β = Conditionals.dynamicsPoolingObservation γ ↔
        γ = β + (dynamicsContrastCoefficient γ - dynamicsContrastCoefficient β) •
          Conditionals.dynamicsContrast
  /-- Every positive dictionary order represents the pooled projector. -/
  represented_at_every_positive_order :
    ∀ k : ℕ, 0 < k → dynamicsPooledProjector ∈
      UniformCorrectionFamily Conditionals.dynamicsPoolingObservation k
  /-- Every represented correction is blind to translations along the contrast. -/
  all_uniform_corrections_contrast_blind :
    ∀ (k : ℕ) (C : (Bool → ℝ) →ₗ[ℝ] (Bool → ℝ)),
      C ∈ UniformCorrectionFamily Conditionals.dynamicsPoolingObservation k →
        ∀ (β : Bool → ℝ) (c : ℝ), C (β + c • Conditionals.dynamicsContrast) = C β

/-- **Biological correction theorem.**  Pooling is exactly a projection onto shared biology; its
entire complement is the one-dimensional dynamics contrast already identified with calibration
drift in `DynamicsContrast`. -/
theorem biologicalCorrectionNormalForm : BiologicalCorrectionNormalForm where
  projector_idempotent := dynamicsPooledProjector_idempotent
  fixed_exactly_on_common_fields := dynamicsPooledProjector_fixed_iff
  residual_exactly_contrast := dynamicsPooledProjector_residual
  pooling_fiber_exact := dynamicsPoolingObservation_eq_iff_contrast_translation
  represented_at_every_positive_order := dynamicsPooledProjector_mem_uniformCorrectionFamily
  all_uniform_corrections_contrast_blind := uniformDynamicsCorrection_add_contrast

end Descent.Portability
