/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.AugmentedAuditLaw
import Descent.Portability.AuditVarianceGeometry

assert_below Descent.Decision Descent.Program

/-!
Decision-Directed Portability, Theorems 5 and 6. The envelope is an exact
optimization over actual probability measures supported on the supplied
interval. A two-endpoint law attains it, including degenerate mean bands.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.BoundedAuditCompletion

open MeasureTheory ProbabilityTheory AugmentedAuditLaw AuditVarianceGeometry

/-- Probability mass assigned to the upper support endpoint at a specified mean. -/
noncomputable def upperMass (L U m : ℝ) : ℝ := (m - L) / (U - L)

/-- The explicit outcome law attaining the support-constrained variance maximum. -/
noncomputable def endpointLaw (L U m : ℝ) : Measure ℝ :=
  ENNReal.ofReal (1 - upperMass L U m) • Measure.dirac L +
    ENNReal.ofReal (upperMass L U m) • Measure.dirac U

/-- Endpoint weights are valid probabilities for every admissible mean. -/
theorem upperMass_bounds (L U m : ℝ) (hLU : L < U) (hm : L ≤ m ∧ m ≤ U) :
    0 ≤ upperMass L U m ∧ upperMass L U m ≤ 1 := by
  unfold upperMass
  constructor
  · exact div_nonneg (sub_nonneg.mpr hm.1) (sub_pos.mpr hLU).le
  · apply (div_le_iff₀ (sub_pos.mpr hLU)).mpr
    linarith

/-- The attaining law is an actual normalized probability measure. -/
theorem endpointLaw_probability (L U m : ℝ) (hLU : L < U) (hm : L ≤ m ∧ m ≤ U) :
    IsProbabilityMeasure (endpointLaw L U m) := by
  have ht := upperMass_bounds L U m hLU hm
  constructor
  simp only [endpointLaw, Measure.add_apply, Measure.smul_apply, measure_univ,
    smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add (sub_nonneg.mpr ht.2) ht.1]
  norm_num

/-- The attaining law puts no probability outside the required support interval. -/
theorem endpointLaw_support (L U m : ℝ) (hLU : L ≤ U) :
    ∀ᵐ y ∂endpointLaw L U m, y ∈ Set.Icc L U := by
  unfold endpointLaw
  apply ae_add_measure_iff.mpr
  constructor
  · apply Measure.ae_smul_measure
    simp [hLU]
  · apply Measure.ae_smul_measure
    simp [hLU]

/-- Every real-valued function is integrable under this finite endpoint law. -/
theorem endpoint_integrable (L U m : ℝ) (f : ℝ → ℝ) :
    Integrable f (endpointLaw L U m) := by
  have hL : Integrable f (Measure.dirac L) := integrable_dirac (by simp)
  have hU : Integrable f (Measure.dirac U) := integrable_dirac (by simp)
  exact (hL.smul_measure ENNReal.ofReal_ne_top).add_measure
    (hU.smul_measure ENNReal.ofReal_ne_top)

/-- Exact expectation for the explicitly constructed attaining law. -/
theorem endpoint_integral (L U m : ℝ) (hLU : L < U) (hm : L ≤ m ∧ m ≤ U)
    (f : ℝ → ℝ) :
    (∫ y, f y ∂endpointLaw L U m) =
      (1 - upperMass L U m) * f L + upperMass L U m * f U := by
  have ht := upperMass_bounds L U m hLU hm
  have hL : Integrable f (Measure.dirac L) := integrable_dirac (by simp)
  have hU : Integrable f (Measure.dirac U) := integrable_dirac (by simp)
  rw [endpointLaw, integral_add_measure (hL.smul_measure ENNReal.ofReal_ne_top)
    (hU.smul_measure ENNReal.ofReal_ne_top), integral_smul_measure, integral_smul_measure]
  simp only [integral_dirac, ENNReal.toReal_ofReal (sub_nonneg.mpr ht.2),
    ENNReal.toReal_ofReal ht.1, smul_eq_mul]

/-- Its mean is precisely the chosen mean, rather than a supplied moment assumption. -/
theorem endpoint_mean (L U m : ℝ) (hLU : L < U) (hm : L ≤ m ∧ m ≤ U) :
    (∫ y, y ∂endpointLaw L U m) = m := by
  rw [endpoint_integral L U m hLU hm]
  unfold upperMass
  field_simp [(sub_pos.mpr hLU).ne']
  ring

/-- The support-constrained variance bound is attained exactly. -/
theorem endpoint_variance (L U m : ℝ) (hLU : L < U) (hm : L ≤ m ∧ m ≤ U) :
    Var[fun y : ℝ ↦ y; endpointLaw L U m] = (U - m) * (m - L) := by
  letI := endpointLaw_probability L U m hLU hm
  have hY : MemLp (fun y : ℝ ↦ y) 2 (endpointLaw L U m) :=
    (memLp_two_iff_integrable_sq measurable_id.aestronglyMeasurable).mpr
      (endpoint_integrable L U m _)
  rw [variance_eq_sub hY, endpoint_mean L U m hLU hm]
  simp only [Pi.pow_apply]
  rw [endpoint_integral L U m hLU hm]
  unfold upperMass
  field_simp [(sub_pos.mpr hLU).ne']
  ring

/-- Every bounded outcome law satisfies the exact mean-specific audit envelope. -/
theorem bounded_audit_upper (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (L U p q : ℝ) (hp : 0 < p ∧ p ≤ 1)
    (hs : ∀ᵐ y ∂μ, y ∈ Set.Icc L U) :
    Var[fun z : ℝ ↦ z; auditLaw μ p q] ≤ envelope L U p q (∫ y, y ∂μ) := by
  have hY := memLp_of_bounded hs measurable_id.aestronglyMeasurable 2
  rw [audit_variance μ p q hp hY]
  unfold envelope
  exact add_le_add_right
    (div_le_div_of_nonneg_right
      (variance_le_sub_mul_sub hs measurable_id.aemeasurable) hp.1.le) _

/-- Under the endpoint law, the upper audit envelope is attained exactly. -/
theorem endpoint_audit_variance (L U p q m : ℝ) (hLU : L < U)
    (hp : 0 < p ∧ p ≤ 1) (hm : L ≤ m ∧ m ≤ U) :
    Var[fun z : ℝ ↦ z; auditLaw (endpointLaw L U m) p q] = envelope L U p q m := by
  letI := endpointLaw_probability L U m hLU hm
  have hY := memLp_of_bounded (endpointLaw_support L U m hLU.le)
    measurable_id.aestronglyMeasurable 2
  rw [audit_variance _ p q hp hY, endpoint_variance L U m hLU hm,
    endpoint_mean L U m hLU hm]
  rfl

/-- The clipped vertex gives a sharp bound over all admissible probability laws. -/
theorem worst_case_upper (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (L U p q lo hi : ℝ) (hp : 0 < p ∧ p ≤ 1)
    (hs : ∀ᵐ y ∂μ, y ∈ Set.Icc L U)
    (hm : lo ≤ (∫ y, y ∂μ) ∧ (∫ y, y ∂μ) ≤ hi) :
    Var[fun z : ℝ ↦ z; auditLaw μ p q] ≤
      envelope L U p q (clip lo hi (vertex L U p q)) :=
  (bounded_audit_upper μ L U p q hp hs).trans
    (maximizing_mean L U p q lo hi _ hp.1.ne' hm)

/-- The worst-case upper bound is attained by an actual admissible outcome law. -/
theorem worst_case_attained (L U p q lo hi : ℝ) (hLU : L < U)
    (hp : 0 < p ∧ p ≤ 1) (hband : L ≤ lo ∧ lo ≤ hi ∧ hi ≤ U) :
    ∃ μ : Measure ℝ, IsProbabilityMeasure μ ∧
      (∀ᵐ y ∂μ, y ∈ Set.Icc L U) ∧
      (lo ≤ (∫ y, y ∂μ) ∧ (∫ y, y ∂μ) ≤ hi) ∧
      Var[fun z : ℝ ↦ z; auditLaw μ p q] =
        envelope L U p q (clip lo hi (vertex L U p q)) := by
  let m := clip lo hi (vertex L U p q)
  have hm := clip_mem lo hi (vertex L U p q) hband.2.1
  have hs : L ≤ m ∧ m ≤ U := ⟨hband.1.trans hm.1, hm.2.trans hband.2.2⟩
  refine ⟨endpointLaw L U m, endpointLaw_probability L U m hLU hs,
    endpointLaw_support L U m hLU.le, ?_, endpoint_audit_variance L U p q m hLU hp hs⟩
  rw [endpoint_mean L U m hLU hs]
  exact hm

/-- With the minimax proxy, all admissible laws obey the closed-form minimax value. -/
theorem minimax_upper (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (L U p lo hi : ℝ) (hp : 0 < p ∧ p ≤ 1)
    (hs : ∀ᵐ y ∂μ, y ∈ Set.Icc L U)
    (hm : lo ≤ (∫ y, y ∂μ) ∧ (∫ y, y ∂μ) ≤ hi) :
    Var[fun z : ℝ ↦ z; auditLaw μ p (proxy L U lo hi)] ≤
      (U - proxy L U lo hi) * (proxy L U lo hi - L) / p :=
  (bounded_audit_upper μ L U p (proxy L U lo hi) hp hs).trans
    (proxy_upper L U p lo hi _ hp.1 hm)

/-- One admissible endpoint law supplies the minimax lower bound against every proxy. -/
theorem minimax_attaining_law (L U p lo hi : ℝ) (hLU : L < U)
    (hp : 0 < p ∧ p ≤ 1) (hband : L ≤ lo ∧ lo ≤ hi ∧ hi ≤ U) :
    let q := proxy L U lo hi
    IsProbabilityMeasure (endpointLaw L U q) ∧
      (∀ᵐ y ∂endpointLaw L U q, y ∈ Set.Icc L U) ∧
      (lo ≤ (∫ y, y ∂endpointLaw L U q) ∧ (∫ y, y ∂endpointLaw L U q) ≤ hi) ∧
      (∀ z, (U - q) * (q - L) / p ≤
        Var[fun y : ℝ ↦ y; auditLaw (endpointLaw L U q) p z]) := by
  dsimp only
  have hm := clip_mem lo hi ((L + U) / 2) hband.2.1
  have hs : L ≤ proxy L U lo hi ∧ proxy L U lo hi ≤ U :=
    ⟨hband.1.trans hm.1, hm.2.trans hband.2.2⟩
  refine ⟨endpointLaw_probability _ _ _ hLU hs, endpointLaw_support _ _ _ hLU.le, ?_, ?_⟩
  · rw [endpoint_mean _ _ _ hLU hs]
    exact hm
  · intro z
    rw [endpoint_audit_variance L U p z _ hLU hp hs]
    exact (minimax_proxy L U p lo hi hp hband.2.1).2.2.2 z

end Descent.Portability.BoundedAuditCompletion
