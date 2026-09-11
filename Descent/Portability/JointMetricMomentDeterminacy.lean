/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.JointRatioFailureMasks
import Descent.Portability.ReplicaMeasureCertificate
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed

assert_below Descent.Decision Descent.Program

/-!
# The joint moments of a bounded metric vector determine its joint law

NOTE 2 section 6.1 turns a finite family of bounded ratio metrics `M_j = N_j / D_j` into one
vector with values in the cube `[0,1]^J`, computes every joint moment of that vector from the
positive ratio expansion (15) of the multi-index pairs (25), and concludes that these moments
determine the joint conditional law of the vector, and by inclusion and exclusion (26) its law
on each failure mask. This module proves those steps over arbitrary probability measures.

`measure_eq_of_separating_subalgebra` is the measure-theoretic core, for any compact Borel
space with outer approximations of closed sets: two finite measures integrating every member
of a point-separating subalgebra of continuous readouts alike are equal. It combines
Stone–Weierstrass with `MeasureTheory.ext_of_forall_integral_eq_of_IsFiniteMeasure`; the
passage from generators to their span is the kernel of the linear functional
`integralDifference`. `measure_eq_of_cube_moments_eq` specializes it to the cube `metricCube J`
and its joint moment readouts `cubeMonomial r`: two finite measures on `[0,1]^J` with equal
monomial moments are equal. `ReplicaMomentCompleteness` runs the same route on the simplex.

`metricVector` is the family of metrics as a point of the cube, each metric read as zero off
its own defined event, and `definedDomain den Finset.univ` is the common defined event `E_*`.
`integral_multiIndexRatio_eq_moment` shows that the multi-index ratio of
`JointRatioFailureMasks`, integrated over the whole population, is the joint moment
`∫_{E_*} ∏ⱼ M_j^{r_j}`, and `moment_eq_tsum_expansion` rewrites that moment as the series
(15), so every joint moment is a limit of finite-replica readouts.
`jointMetricLaw_eq_of_expansion_eq` is the conclusion of the note: two laws of the population
with the same expansions for every multi-index give the metric vector the same law on `E_*`,
and the same conditional law given `E_*` in Mathlib's conditional measure.

For failure masks, `maskEvent den A` is the event on which exactly the metrics of `A` are
defined. `maskStatistic_definedIndicators` identifies the mask statistic of
`JointRatioFailureMasks` with the indicator of that event, `masked_moment_expansion` is (26)
applied to metric monomials, and `maskMetricLaw_eq_of_masked_moments_eq` shows that masked
moments determine the law of the vector on the mask. `masked_moment_eq_zero` records that a
monomial with a positive exponent outside the mask has zero masked moment, which is why only
the monomials supported on the mask carry information. `subfamily_moment_eq_tsum` exhibits
each subfamily moment entering (26) as the expansion (15) of the family whose denominators
outside the subfamily are set to one, and `maskMetricLaw_eq_of_subfamily_moments_eq` closes the
chain: the subfamily moments of the monomials supported on a mask determine the law on it.

Scope: the bounds `0 ≤ N_j ≤ D_j ≤ 1` hold everywhere and all functionals are measurable. The
two populations compared are two laws on one measurable space carrying one family of
functionals, which is the situation of two mixing laws of one conditional population. The law
on `E_*` is normalized to a probability measure only in the conditional form. The portability
queries of section 6.2 are not formalized here.

## Empirical status

None. The bodies here are measure theory: every statement relates integrals of stipulated
functions of given measurable functionals under given measures, or is a property of compact
spaces, so no measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.JointMetricMomentDeterminacy

open MeasureTheory ProbabilityTheory PositiveRatioExpansion JointRatioFailureMasks

noncomputable section

section CompactDeterminacy

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]

/-- A continuous readout of a compact space is integrable against every finite measure. -/
theorem integrable_continuousReadout (μ : Measure X) [IsFiniteMeasure μ] (readout : C(X, ℝ)) :
    Integrable (fun x ↦ readout x) μ :=
  BoundedContinuousFunction.integrable μ (BoundedContinuousFunction.mkOfCompact readout)

/-- Integration against a finite measure moves a continuous readout by at most its sup-norm
distance times the total mass. -/
theorem abs_integral_sub_le_norm_mul_mass (μ : Measure X) [IsFiniteMeasure μ]
    (first second : C(X, ℝ)) :
    |∫ x, first x ∂μ - ∫ x, second x ∂μ| ≤ ‖first - second‖ * μ.real Set.univ := by
  rw [← integral_sub (integrable_continuousReadout μ first)
    (integrable_continuousReadout μ second), ← Real.norm_eq_abs]
  exact norm_integral_le_of_norm_le_const
    (ae_of_all _ fun x ↦ (first - second).norm_coe_le_norm x)

/-- The difference of the expectations of a continuous readout under two finite measures, as a
linear functional on the continuous readouts. -/
def integralDifference (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    C(X, ℝ) →ₗ[ℝ] ℝ where
  toFun readout := ∫ x, readout x ∂μ - ∫ x, readout x ∂ν
  map_add' first second := by
    simp only [ContinuousMap.add_apply]
    rw [integral_add (integrable_continuousReadout μ first)
        (integrable_continuousReadout μ second),
      integral_add (integrable_continuousReadout ν first)
        (integrable_continuousReadout ν second)]
    ring
  map_smul' scale readout := by
    simp only [ContinuousMap.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [integral_const_mul, integral_const_mul]
    ring

/-- Two finite measures that integrate every member of a family of continuous readouts alike
integrate every member of its linear span alike, because the span lies in the kernel of their
integral difference. -/
theorem integral_eq_of_mem_span (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (generators : Set C(X, ℝ))
    (hgenerators : ∀ readout ∈ generators, ∫ x, readout x ∂μ = ∫ x, readout x ∂ν)
    (readout : C(X, ℝ)) (hspan : readout ∈ Submodule.span ℝ generators) :
    ∫ x, readout x ∂μ = ∫ x, readout x ∂ν := by
  have hkernel : Submodule.span ℝ generators ≤ LinearMap.ker (integralDifference μ ν) :=
    Submodule.span_le.mpr fun generator hgenerator ↦
      LinearMap.mem_ker.mpr (sub_eq_zero.mpr (hgenerators generator hgenerator))
  exact sub_eq_zero.mp (LinearMap.mem_ker.mp (hkernel hspan))

/-- **Measure determinacy from a separating subalgebra.** On a compact Borel space with outer
approximations of closed sets, two finite measures that integrate every member of a
point-separating subalgebra of continuous readouts alike are equal. Stone–Weierstrass puts a
member of the subalgebra within any sup-norm distance of a bounded continuous readout, and
`MeasureTheory.ext_of_forall_integral_eq_of_IsFiniteMeasure` passes from bounded continuous
readouts to the measures. -/
theorem measure_eq_of_separating_subalgebra [HasOuterApproxClosed X] (μ ν : Measure X)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (readouts : Subalgebra ℝ C(X, ℝ))
    (hseparates : readouts.SeparatesPoints)
    (hintegral : ∀ readout ∈ readouts, ∫ x, readout x ∂μ = ∫ x, readout x ∂ν) :
    μ = ν := by
  refine ext_of_forall_integral_eq_of_IsFiniteMeasure fun bounded ↦ ?_
  refine eq_of_forall_dist_le fun ε hε ↦ ?_
  set target : C(X, ℝ) := bounded.toContinuousMap
  have hμ : (0 : ℝ) ≤ μ.real Set.univ := measureReal_nonneg
  have hν : (0 : ℝ) ≤ ν.real Set.univ := measureReal_nonneg
  have hscale : 0 < μ.real Set.univ + ν.real Set.univ + 1 := by linarith
  obtain ⟨near, hnear⟩ :=
    ContinuousMap.exists_mem_subalgebra_near_continuousMap_of_separatesPoints readouts
      hseparates target (ε / (μ.real Set.univ + ν.real Set.univ + 1)) (div_pos hε hscale)
  have hagree := hintegral near near.2
  have hfirst := abs_integral_sub_le_norm_mul_mass μ target near
  have hsecond := abs_integral_sub_le_norm_mul_mass ν near target
  rw [norm_sub_rev] at hfirst
  have htriangle : |∫ x, target x ∂μ - ∫ x, target x ∂ν| ≤
      |∫ x, target x ∂μ - ∫ x, (near : C(X, ℝ)) x ∂μ| +
        |∫ x, (near : C(X, ℝ)) x ∂ν - ∫ x, target x ∂ν| := by
    calc |∫ x, target x ∂μ - ∫ x, target x ∂ν|
        ≤ |∫ x, target x ∂μ - ∫ x, (near : C(X, ℝ)) x ∂μ| +
            |∫ x, (near : C(X, ℝ)) x ∂μ - ∫ x, target x ∂ν| := abs_sub_le _ _ _
      _ = |∫ x, target x ∂μ - ∫ x, (near : C(X, ℝ)) x ∂μ| +
            |∫ x, (near : C(X, ℝ)) x ∂ν - ∫ x, target x ∂ν| := by rw [hagree]
  have hcancel : ε / (μ.real Set.univ + ν.real Set.univ + 1) *
      (μ.real Set.univ + ν.real Set.univ + 1) = ε := by
    field_simp
  have hproduct :
      ‖(near : C(X, ℝ)) - target‖ * (μ.real Set.univ + ν.real Set.univ) ≤ ε := by
    calc ‖(near : C(X, ℝ)) - target‖ * (μ.real Set.univ + ν.real Set.univ)
        ≤ ε / (μ.real Set.univ + ν.real Set.univ + 1) *
            (μ.real Set.univ + ν.real Set.univ) :=
          mul_le_mul_of_nonneg_right hnear.le (by linarith)
      _ ≤ ε / (μ.real Set.univ + ν.real Set.univ + 1) *
            (μ.real Set.univ + ν.real Set.univ + 1) :=
          mul_le_mul_of_nonneg_left (by linarith) (div_pos hε hscale).le
      _ = ε := hcancel
  rw [Real.dist_eq]
  show |∫ x, target x ∂μ - ∫ x, target x ∂ν| ≤ ε
  linarith

end CompactDeterminacy

section Cube

/-- The unit cube `[0,1]^J` in which a vector of bounded ratio metrics takes its values. -/
def metricCube (Metric : Type*) : Set (Metric → ℝ) := Set.univ.pi fun _ ↦ Set.Icc 0 1

/-- The unit cube is compact, by Tychonoff's theorem. -/
instance metricCube_compactSpace (Metric : Type*) : CompactSpace ↥(metricCube Metric) :=
  isCompact_iff_compactSpace.mp (isCompact_univ_pi fun _ ↦ isCompact_Icc)

/-- The readout of one metric from a point of the cube, as a continuous function. -/
def cubeCoordinate (Metric : Type*) (index : Metric) : C(↥(metricCube Metric), ℝ) where
  toFun point := (point : Metric → ℝ) index
  continuous_toFun := (continuous_apply index).comp continuous_subtype_val

/-- The joint moment readout `x ↦ ∏ⱼ xⱼ ^ rⱼ` of a metric vector. -/
def cubeMonomial {Metric : Type*} [Fintype Metric] (order : Metric → ℕ) :
    C(↥(metricCube Metric), ℝ) :=
  ∏ index, cubeCoordinate Metric index ^ order index

/-- The joint moment readout is the product of the coordinates raised to the multi-index. -/
theorem cubeMonomial_apply {Metric : Type*} [Fintype Metric] (order : Metric → ℕ)
    (point : ↥(metricCube Metric)) :
    cubeMonomial order point = ∏ index, (point : Metric → ℝ) index ^ order index := by
  simp only [cubeMonomial, ContinuousMap.prod_apply, ContinuousMap.pow_apply]
  rfl

/-- The zero multi-index gives the constant readout one. -/
theorem cubeMonomial_zero {Metric : Type*} [Fintype Metric] :
    cubeMonomial (0 : Metric → ℕ) = 1 := by
  simp [cubeMonomial]

/-- Joint moment readouts multiply by adding multi-indices. -/
theorem cubeMonomial_add {Metric : Type*} [Fintype Metric] (first second : Metric → ℕ) :
    cubeMonomial (first + second) = cubeMonomial first * cubeMonomial second := by
  simp only [cubeMonomial, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun index _ ↦ by rw [Pi.add_apply, pow_add]

/-- The coordinate readout is the joint moment readout of a one-hot multi-index. -/
theorem cubeMonomial_single {Metric : Type*} [Fintype Metric] [DecidableEq Metric]
    (index : Metric) (point : ↥(metricCube Metric)) :
    cubeMonomial (fun other ↦ if other = index then 1 else 0) point =
      (point : Metric → ℝ) index := by
  rw [cubeMonomial_apply, Finset.prod_eq_single index]
  · simp
  · intro other _ hother
    simp [hother]
  · intro hmissing
    exact absurd (Finset.mem_univ index) hmissing

/-- The joint moment readouts form a multiplicative monoid. -/
def cubeMonomialMonoid (Metric : Type*) [Fintype Metric] :
    Submonoid C(↥(metricCube Metric), ℝ) where
  carrier := Set.range cubeMonomial
  mul_mem' := by
    rintro _ _ ⟨first, rfl⟩ ⟨second, rfl⟩
    exact ⟨first + second, cubeMonomial_add first second⟩
  one_mem' := ⟨0, cubeMonomial_zero⟩

/-- The polynomial readouts of a metric vector: the algebra generated by the joint moment
readouts. -/
def cubeAlgebra (Metric : Type*) [Fintype Metric] :
    Subalgebra ℝ C(↥(metricCube Metric), ℝ) :=
  Algebra.adjoin ℝ (Set.range cubeMonomial)

/-- Because joint moment readouts are closed under products, the algebra they generate is
their linear span. -/
theorem cubeAlgebra_toSubmodule (Metric : Type*) [Fintype Metric] :
    Subalgebra.toSubmodule (cubeAlgebra Metric) =
      Submodule.span ℝ (Set.range (cubeMonomial (Metric := Metric))) := by
  refine Algebra.adjoin_eq_span_of_subset ℝ fun readout hreadout ↦ ?_
  have hclosure : Submonoid.closure (Set.range (cubeMonomial (Metric := Metric))) ≤
      cubeMonomialMonoid Metric :=
    Submonoid.closure_le.mpr fun other hother ↦ hother
  exact Submodule.subset_span (hclosure hreadout)

/-- The polynomial readouts separate the points of the cube: distinct metric vectors differ in
some coordinate, and the coordinate readouts are joint moment readouts. -/
theorem cubeAlgebra_separatesPoints (Metric : Type*) [Fintype Metric] [DecidableEq Metric] :
    (cubeAlgebra Metric).SeparatesPoints := by
  intro first second hdistinct
  obtain ⟨index, hindex⟩ :
      ∃ index, (first : Metric → ℝ) index ≠ (second : Metric → ℝ) index := by
    by_contra hsame
    push_neg at hsame
    exact hdistinct (Subtype.ext (funext hsame))
  refine ⟨_, ⟨cubeMonomial fun other ↦ if other = index then 1 else 0,
    Algebra.subset_adjoin ⟨_, rfl⟩, rfl⟩, ?_⟩
  simpa only [cubeMonomial_single] using hindex

/-- **NOTE 2 section 6.1, moment determinacy on the cube.** Two finite measures on the unit
cube `[0,1]^J` with the same joint moments `∫ ∏ⱼ xⱼ ^ rⱼ` for every multi-index are equal. -/
theorem measure_eq_of_cube_moments_eq {Metric : Type*} [Fintype Metric] [DecidableEq Metric]
    (μ ν : Measure ↥(metricCube Metric)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hmoment : ∀ order : Metric → ℕ,
      ∫ point, cubeMonomial order point ∂μ = ∫ point, cubeMonomial order point ∂ν) :
    μ = ν := by
  refine measure_eq_of_separating_subalgebra μ ν (cubeAlgebra Metric)
    (cubeAlgebra_separatesPoints Metric) fun readout hreadout ↦ ?_
  have hspan :
      readout ∈ Submodule.span ℝ (Set.range (cubeMonomial (Metric := Metric))) := by
    rw [← cubeAlgebra_toSubmodule Metric]
    exact hreadout
  refine integral_eq_of_mem_span μ ν _ ?_ readout hspan
  rintro _ ⟨order, rfl⟩
  exact hmoment order

end Cube

section JointMetricLaw

variable {Ω : Type*} [MeasurableSpace Ω] {Metric : Type*} [Fintype Metric] [DecidableEq Metric]

/-- The vector `(M_j)_j` of a finite family of bounded ratio metrics, each read as zero off its
own defined event, as a point of the unit cube. -/
def metricVector (num den : Metric → Ω → ℝ) (hnum : ∀ index point, 0 ≤ num index point)
    (hle : ∀ index point, num index point ≤ den index point) (point : Ω) :
    ↥(metricCube Metric) :=
  ⟨fun index ↦ ratioOnDefined (num index) (den index) point,
    Set.mem_univ_pi.mpr fun index ↦
      ⟨ratioOnDefined_nonneg (num index) (den index) (hnum index) point,
        ratioOnDefined_le_one (num index) (den index) (hle index) point⟩⟩

omit [Fintype Metric] [DecidableEq Metric] in
/-- The metric vector of a measurable family is measurable. -/
theorem measurable_metricVector (num den : Metric → Ω → ℝ)
    (hnumMeasurable : ∀ index, Measurable (num index))
    (hdenMeasurable : ∀ index, Measurable (den index))
    (hnum : ∀ index point, 0 ≤ num index point)
    (hle : ∀ index point, num index point ≤ den index point) :
    Measurable (metricVector num den hnum hle) :=
  Measurable.subtype_mk (measurable_pi_lambda _ fun index ↦
    ReplicaMeasureCertificate.measurable_ratioOnDefined (num index) (den index)
      (hnumMeasurable index) (hdenMeasurable index))

/-- The event on which every metric of a subfamily is defined. The whole family gives the
common defined event `E_*` of NOTE 2 section 6.1. -/
def definedDomain (den : Metric → Ω → ℝ) (subfamily : Finset Metric) : Set Ω :=
  {point | ∀ index ∈ subfamily, 0 < den index point}

/-- The event on which a subfamily is defined is measurable. -/
theorem measurableSet_definedDomain (den : Metric → Ω → ℝ)
    (hdenMeasurable : ∀ index, Measurable (den index)) (subfamily : Finset Metric) :
    MeasurableSet (definedDomain den subfamily) := by
  rw [definedDomain, Set.setOf_forall]
  refine MeasurableSet.iInter fun index ↦ ?_
  by_cases hmem : index ∈ subfamily
  · simpa [hmem] using measurableSet_lt measurable_const (hdenMeasurable index)
  · simp [hmem]

/-- The failure-mask event on which exactly the metrics of `selected` are defined. -/
def maskEvent (den : Metric → Ω → ℝ) (selected : Finset Metric) : Set Ω :=
  {point | ∀ index, 0 < den index point ↔ index ∈ selected}

/-- A failure-mask event is measurable. -/
theorem measurableSet_maskEvent (den : Metric → Ω → ℝ)
    (hdenMeasurable : ∀ index, Measurable (den index)) (selected : Finset Metric) :
    MeasurableSet (maskEvent den selected) := by
  rw [maskEvent, Set.setOf_forall]
  refine MeasurableSet.iInter fun index ↦ ?_
  by_cases hmem : index ∈ selected
  · simpa [hmem] using measurableSet_lt measurable_const (hdenMeasurable index)
  · have hcomplement : {point | 0 < den index point ↔ index ∈ selected} =
        {point | 0 < den index point}ᶜ := by
      ext point
      simp [hmem]
    rw [hcomplement]
    exact (measurableSet_lt measurable_const (hdenMeasurable index)).compl

/-- The joint moment of a pushed-forward metric vector law is the population integral of the
product of the metrics raised to the multi-index. -/
theorem integral_cubeMonomial_map (ρ : Measure Ω) (num den : Metric → Ω → ℝ)
    (hnumMeasurable : ∀ index, Measurable (num index))
    (hdenMeasurable : ∀ index, Measurable (den index))
    (hnum : ∀ index point, 0 ≤ num index point)
    (hle : ∀ index point, num index point ≤ den index point) (order : Metric → ℕ) :
    ∫ point, cubeMonomial order point ∂ρ.map (metricVector num den hnum hle) =
      ∫ point, ∏ index, ratioOnDefined (num index) (den index) point ^ order index ∂ρ := by
  rw [integral_map
    (measurable_metricVector num den hnumMeasurable hdenMeasurable hnum hle).aemeasurable
    (cubeMonomial order).continuous.measurable.aestronglyMeasurable]
  simp only [cubeMonomial_apply]
  rfl

/-- **NOTE 2 equation (25) under a measure.** The multi-index ratio of the family, integrated
over the whole population, is the joint moment over the common defined event: there the ratio
is the product of the metrics raised to the multi-index, and off it some denominator vanishes,
so the multi-index denominator vanishes and the ratio reads zero. -/
theorem integral_multiIndexRatio_eq_moment (μ : Measure Ω) (num den : Metric → Ω → ℝ)
    (hdenMeasurable : ∀ index, Measurable (den index))
    (hnum : ∀ index point, 0 ≤ num index point)
    (hle : ∀ index point, num index point ≤ den index point) (order : Metric → ℕ) :
    ∫ point, ratioOnDefined (multiIndexNumerator num den order)
        (multiIndexDenominator den order) point ∂μ =
      ∫ point in definedDomain den Finset.univ,
        ∏ index, ratioOnDefined (num index) (den index) point ^ order index ∂μ := by
  classical
  rw [← integral_indicator (measurableSet_definedDomain den hdenMeasurable Finset.univ)]
  refine integral_congr_ae (ae_of_all μ fun point ↦ ?_)
  by_cases hdefined : ∀ index, 0 < den index point
  · have hmem : point ∈ definedDomain den Finset.univ := fun index _ ↦ hdefined index
    have hjointPos : 0 < multiIndexDenominator den order point :=
      Finset.prod_pos fun index _ ↦ pow_pos (hdefined index) _
    simp only [ratioOnDefined, hjointPos, hdefined, Set.indicator_apply, hmem, ↓reduceIte]
    exact multiIndexNumerator_ratio num den order point fun index ↦ (hdefined index).ne'
  · obtain ⟨index, hindex⟩ : ∃ index, den index point ≤ 0 := by simpa using hdefined
    have hzero : den index point = 0 :=
      le_antisymm hindex (le_trans (hnum index point) (hle index point))
    have hexponent : multiIndexExponent order index ≠ 0 :=
      (lt_of_lt_of_le zero_lt_one (le_max_left 1 (order index))).ne'
    have hjointZero : multiIndexDenominator den order point = 0 := by
      refine Finset.prod_eq_zero (Finset.mem_univ index) ?_
      show den index point ^ multiIndexExponent order index = 0
      rw [hzero, zero_pow hexponent]
    have hnotMem : point ∉ definedDomain den Finset.univ := fun hmem ↦
      absurd (hmem index (Finset.mem_univ index)) (not_lt.mpr hindex)
    simp only [ratioOnDefined, hjointZero, lt_self_iff_false, Set.indicator_apply, hnotMem,
      ↓reduceIte]

omit [DecidableEq Metric] in
/-- The multi-index numerator of a measurable family is measurable. -/
theorem measurable_multiIndexNumerator (num den : Metric → Ω → ℝ)
    (hnumMeasurable : ∀ index, Measurable (num index))
    (hdenMeasurable : ∀ index, Measurable (den index)) (order : Metric → ℕ) :
    Measurable (multiIndexNumerator num den order) :=
  Finset.measurable_prod _ fun index _ ↦
    ((hnumMeasurable index).pow_const _).mul ((hdenMeasurable index).pow_const _)

omit [DecidableEq Metric] in
/-- The multi-index denominator of a measurable family is measurable. -/
theorem measurable_multiIndexDenominator (den : Metric → Ω → ℝ)
    (hdenMeasurable : ∀ index, Measurable (den index)) (order : Metric → ℕ) :
    Measurable (multiIndexDenominator den order) :=
  Finset.measurable_prod _ fun index _ ↦ (hdenMeasurable index).pow_const _

/-- **NOTE 2 section 6.1.** Every joint metric moment over the common defined event is the sum
of the positive ratio expansion (15) of its multi-index pair (25), so every joint moment is a
limit of finite-replica readouts. -/
theorem moment_eq_tsum_expansion (μ : Measure Ω) [IsProbabilityMeasure μ]
    (num den : Metric → Ω → ℝ) (hnumMeasurable : ∀ index, Measurable (num index))
    (hdenMeasurable : ∀ index, Measurable (den index))
    (hnum : ∀ index point, 0 ≤ num index point)
    (hle : ∀ index point, num index point ≤ den index point)
    (hden : ∀ index point, den index point ≤ 1) (order : Metric → ℕ) :
    ∫ point in definedDomain den Finset.univ,
        ∏ index, ratioOnDefined (num index) (den index) point ^ order index ∂μ =
      ∑' power : ℕ, ∫ point, multiIndexNumerator num den order point *
        (1 - multiIndexDenominator den order point) ^ power ∂μ := by
  rw [← integral_multiIndexRatio_eq_moment μ num den hdenMeasurable hnum hle order]
  exact integral_ratioOnDefined_eq_tsum μ _ _
    (measurable_multiIndexNumerator num den hnumMeasurable hdenMeasurable order)
    (measurable_multiIndexDenominator den hdenMeasurable order)
    (multiIndexNumerator_nonneg num den hnum hle order)
    (multiIndexNumerator_le_multiIndexDenominator num den hnum hle order)
    (multiIndexDenominator_le_one den
      (fun index point ↦ le_trans (hnum index point) (hle index point)) hden order)

/-- **NOTE 2 section 6.1, joint law determinacy.** Two laws of the population under which the
positive ratio expansions (15) of every multi-index pair (25) agree give the metric vector the
same law on the common defined event, and the same conditional law given that event. -/
theorem jointMetricLaw_eq_of_expansion_eq (μ ν : Measure Ω) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (num den : Metric → Ω → ℝ)
    (hnumMeasurable : ∀ index, Measurable (num index))
    (hdenMeasurable : ∀ index, Measurable (den index))
    (hnum : ∀ index point, 0 ≤ num index point)
    (hle : ∀ index point, num index point ≤ den index point)
    (hden : ∀ index point, den index point ≤ 1)
    (hexpansion : ∀ order : Metric → ℕ,
      ∑' power : ℕ, ∫ point, multiIndexNumerator num den order point *
          (1 - multiIndexDenominator den order point) ^ power ∂μ =
        ∑' power : ℕ, ∫ point, multiIndexNumerator num den order point *
          (1 - multiIndexDenominator den order point) ^ power ∂ν) :
    (μ.restrict (definedDomain den Finset.univ)).map (metricVector num den hnum hle) =
        (ν.restrict (definedDomain den Finset.univ)).map (metricVector num den hnum hle) ∧
      (μ[|definedDomain den Finset.univ]).map (metricVector num den hnum hle) =
        (ν[|definedDomain den Finset.univ]).map (metricVector num den hnum hle) := by
  have hvector := measurable_metricVector num den hnumMeasurable hdenMeasurable hnum hle
  haveI : IsFiniteMeasure
      ((μ.restrict (definedDomain den Finset.univ)).map (metricVector num den hnum hle)) :=
    Measure.isFiniteMeasure_map _ _
  haveI : IsFiniteMeasure
      ((ν.restrict (definedDomain den Finset.univ)).map (metricVector num den hnum hle)) :=
    Measure.isFiniteMeasure_map _ _
  have hjoint :
      (μ.restrict (definedDomain den Finset.univ)).map (metricVector num den hnum hle) =
        (ν.restrict (definedDomain den Finset.univ)).map (metricVector num den hnum hle) := by
    refine measure_eq_of_cube_moments_eq _ _ fun order ↦ ?_
    rw [integral_cubeMonomial_map _ num den hnumMeasurable hdenMeasurable hnum hle order,
      integral_cubeMonomial_map _ num den hnumMeasurable hdenMeasurable hnum hle order,
      moment_eq_tsum_expansion μ num den hnumMeasurable hdenMeasurable hnum hle hden order,
      moment_eq_tsum_expansion ν num den hnumMeasurable hdenMeasurable hnum hle hden order]
    exact hexpansion order
  refine ⟨hjoint, ?_⟩
  have hmass : μ (definedDomain den Finset.univ) = ν (definedDomain den Finset.univ) := by
    have hunivMass :=
      congrArg (fun law : Measure ↥(metricCube Metric) ↦ law Set.univ) hjoint
    simpa only [Measure.map_apply hvector MeasurableSet.univ, Set.preimage_univ,
      Measure.restrict_apply_univ] using hunivMass
  rw [ProbabilityTheory.cond, ProbabilityTheory.cond, Measure.map_smul, Measure.map_smul,
    hjoint, hmass]

/-- The family with every denominator outside a subfamily replaced by one. -/
def subfamilyDenominator (den : Metric → Ω → ℝ) (subfamily : Finset Metric) :
    Metric → Ω → ℝ :=
  fun index point ↦ if index ∈ subfamily then den index point else 1

omit [MeasurableSpace Ω] in
/-- Setting the denominators outside a subfamily to one turns the common defined event into
the event on which that subfamily is defined. -/
theorem definedDomain_subfamilyDenominator (den : Metric → Ω → ℝ)
    (subfamily : Finset Metric) :
    definedDomain (subfamilyDenominator den subfamily) Finset.univ =
      definedDomain den subfamily := by
  ext point
  simp only [definedDomain, subfamilyDenominator, Set.mem_setOf_eq]
  constructor
  · intro hall index hindex
    simpa [hindex] using hall index (Finset.mem_univ index)
  · intro hall index _
    by_cases hindex : index ∈ subfamily
    · simpa [hindex] using hall index hindex
    · simp [hindex]

/-- **NOTE 2 section 6.1.** The moment of a metric monomial whose exponents vanish outside a
subfamily, on the event where that subfamily is defined, is the positive ratio expansion (15)
of the multi-index pair (25) of the family whose denominators outside the subfamily are set to
one. So every subfamily moment entering the inclusion and exclusion (26) is a limit of
finite-replica readouts. -/
theorem subfamily_moment_eq_tsum (μ : Measure Ω) [IsProbabilityMeasure μ]
    (num den : Metric → Ω → ℝ) (hnumMeasurable : ∀ index, Measurable (num index))
    (hdenMeasurable : ∀ index, Measurable (den index))
    (hnum : ∀ index point, 0 ≤ num index point)
    (hle : ∀ index point, num index point ≤ den index point)
    (hden : ∀ index point, den index point ≤ 1) (subfamily : Finset Metric)
    (order : Metric → ℕ) (hsupport : ∀ index ∉ subfamily, order index = 0) :
    ∫ point in definedDomain den subfamily,
        ∏ index, ratioOnDefined (num index) (den index) point ^ order index ∂μ =
      ∑' power : ℕ, ∫ point,
        multiIndexNumerator num (subfamilyDenominator den subfamily) order point *
          (1 - multiIndexDenominator (subfamilyDenominator den subfamily) order point) ^
            power ∂μ := by
  have hrestrictedLe : ∀ index point,
      num index point ≤ subfamilyDenominator den subfamily index point := by
    intro index point
    by_cases hindex : index ∈ subfamily
    · simp only [subfamilyDenominator, hindex, ↓reduceIte]
      exact hle index point
    · simp only [subfamilyDenominator, hindex, ↓reduceIte]
      exact le_trans (hle index point) (hden index point)
  have hrestrictedLeOne :
      ∀ index point, subfamilyDenominator den subfamily index point ≤ 1 := by
    intro index point
    by_cases hindex : index ∈ subfamily
    · simp only [subfamilyDenominator, hindex, ↓reduceIte]
      exact hden index point
    · simp only [subfamilyDenominator, hindex, ↓reduceIte]
      exact le_rfl
  have hrestrictedMeasurable :
      ∀ index, Measurable (subfamilyDenominator den subfamily index) := by
    intro index
    by_cases hindex : index ∈ subfamily
    · have hsame : subfamilyDenominator den subfamily index = den index :=
        funext fun point ↦ by simp [subfamilyDenominator, hindex]
      rw [hsame]
      exact hdenMeasurable index
    · have hsame : subfamilyDenominator den subfamily index = fun _ ↦ 1 :=
        funext fun point ↦ by simp [subfamilyDenominator, hindex]
      rw [hsame]
      exact measurable_const
  have hproduct : ∀ point,
      ∏ index, ratioOnDefined (num index) (den index) point ^ order index =
        ∏ index, ratioOnDefined (num index) (subfamilyDenominator den subfamily index) point ^
          order index := by
    intro point
    refine Finset.prod_congr rfl fun index _ ↦ ?_
    by_cases hindex : index ∈ subfamily
    · have hsame : subfamilyDenominator den subfamily index = den index :=
        funext fun other ↦ by simp [subfamilyDenominator, hindex]
      rw [hsame]
    · rw [hsupport index hindex, pow_zero, pow_zero]
  rw [← moment_eq_tsum_expansion μ num (subfamilyDenominator den subfamily) hnumMeasurable
    hrestrictedMeasurable hnum hrestrictedLe hrestrictedLeOne order,
    definedDomain_subfamilyDenominator]
  simp only [hproduct]

/-- The real definedness indicators of the family. -/
def definedIndicators (den : Metric → Ω → ℝ) : Metric → Ω → ℝ :=
  fun index point ↦ if 0 < den index point then 1 else 0

omit [MeasurableSpace Ω] in
/-- The mask statistic of `JointRatioFailureMasks`, evaluated on the definedness indicators, is
the indicator of the failure-mask event. -/
theorem maskStatistic_definedIndicators (den : Metric → Ω → ℝ) (selected : Finset Metric)
    (point : Ω) :
    maskStatistic (definedIndicators den) selected point =
      Set.indicator (maskEvent den selected) 1 point := by
  classical
  by_cases hmask : point ∈ maskEvent den selected
  · simp only [Set.indicator_apply, hmask, ↓reduceIte, Pi.one_apply]
    refine maskStatistic_eq_one _ selected point (fun index hindex ↦ ?_) fun index hindex ↦ ?_
    · have hpos : 0 < den index point := (hmask index).mpr hindex
      simp [definedIndicators, hpos]
    · have hnot : ¬ 0 < den index point := fun hpos ↦
        Finset.mem_compl.mp hindex ((hmask index).mp hpos)
      simp [definedIndicators, hnot]
  · simp only [Set.indicator_apply, hmask, ↓reduceIte]
    obtain ⟨index, hindex⟩ : ∃ index, ¬ (0 < den index point ↔ index ∈ selected) := by
      simpa only [maskEvent, Set.mem_setOf_eq, not_forall] using hmask
    by_cases hmem : index ∈ selected
    · have hnot : ¬ 0 < den index point := fun hpos ↦ hindex ⟨fun _ ↦ hmem, fun _ ↦ hpos⟩
      exact maskStatistic_eq_zero_of_mem _ selected point index hmem
        (by simp [definedIndicators, hnot])
    · have hpos : 0 < den index point := by
        by_contra hnot
        exact hindex ⟨fun hpos ↦ absurd hpos hnot, fun hmem' ↦ absurd hmem' hmem⟩
      exact maskStatistic_eq_zero_of_not_mem _ selected point index
        (Finset.mem_compl.mpr hmem) (by simp [definedIndicators, hpos])

omit [MeasurableSpace Ω] in
/-- The product of the definedness indicators over a subfamily is the indicator of the event
on which every metric of the subfamily is defined. -/
theorem prod_definedIndicators (den : Metric → Ω → ℝ) (subfamily : Finset Metric)
    (point : Ω) :
    ∏ index ∈ subfamily, definedIndicators den index point =
      Set.indicator (definedDomain den subfamily) 1 point := by
  classical
  simp only [definedIndicators]
  rw [Finset.prod_boole]
  by_cases hall : ∀ index ∈ subfamily, 0 < den index point
  · have hmem : point ∈ definedDomain den subfamily := hall
    rw [if_pos hall]
    simp only [Set.indicator_apply, hmem, ↓reduceIte, Pi.one_apply]
  · have hnotMem : point ∉ definedDomain den subfamily := hall
    rw [if_neg hall]
    simp only [Set.indicator_apply, hnotMem, ↓reduceIte]

/-- **NOTE 2 equation (26) for metric monomials.** The moment of a metric monomial on the
failure mask `A` is the alternating sum, over subsets `B` of the complementary family, of its
moments on the events where every metric of `A ∪ B` is defined. -/
theorem masked_moment_expansion (μ : Measure Ω) [IsProbabilityMeasure μ]
    (num den : Metric → Ω → ℝ) (hnumMeasurable : ∀ index, Measurable (num index))
    (hdenMeasurable : ∀ index, Measurable (den index))
    (hnum : ∀ index point, 0 ≤ num index point)
    (hle : ∀ index point, num index point ≤ den index point) (order : Metric → ℕ)
    (selected : Finset Metric) :
    ∫ point in maskEvent den selected,
        ∏ index, ratioOnDefined (num index) (den index) point ^ order index ∂μ =
      ∑ subset ∈ selectedᶜ.powerset, (-1 : ℝ) ^ subset.card *
        ∫ point in definedDomain den (selected ∪ subset),
          ∏ index, ratioOnDefined (num index) (den index) point ^ order index ∂μ := by
  classical
  set moment : Ω → ℝ := fun point ↦
    ∏ index, ratioOnDefined (num index) (den index) point ^ order index
  have hmomentIntegrable : Integrable moment μ := by
    refine ReplicaMeasureCertificate.integrable_of_unit_bounds μ moment
      (Finset.measurable_prod _ fun index _ ↦
        (ReplicaMeasureCertificate.measurable_ratioOnDefined (num index) (den index)
          (hnumMeasurable index) (hdenMeasurable index)).pow_const _)
      (fun point ↦ ?_) (fun point ↦ ?_)
    · exact Finset.prod_nonneg fun index _ ↦
        pow_nonneg (ratioOnDefined_nonneg (num index) (den index) (hnum index) point) _
    · exact Finset.prod_le_one (fun index _ ↦
          pow_nonneg (ratioOnDefined_nonneg (num index) (den index) (hnum index) point) _)
        fun index _ ↦ pow_le_one₀
          (ratioOnDefined_nonneg (num index) (den index) (hnum index) point)
          (ratioOnDefined_le_one (num index) (den index) (hle index) point)
  have hpoint : ∀ point, Set.indicator (maskEvent den selected) moment point =
      ∑ subset ∈ selectedᶜ.powerset, (-1 : ℝ) ^ subset.card *
        Set.indicator (definedDomain den (selected ∪ subset)) moment point := by
    intro point
    have hmask : Set.indicator (maskEvent den selected) moment point =
        maskStatistic (definedIndicators den) selected point * moment point := by
      rw [maskStatistic_definedIndicators]
      by_cases hmem : point ∈ maskEvent den selected
      · simp only [Set.indicator_apply, hmem, ↓reduceIte, Pi.one_apply, one_mul]
      · simp only [Set.indicator_apply, hmem, ↓reduceIte, zero_mul]
    have hsubfamily : ∀ subfamily : Finset Metric,
        Set.indicator (definedDomain den subfamily) moment point =
          (∏ index ∈ subfamily, definedIndicators den index point) * moment point := by
      intro subfamily
      rw [prod_definedIndicators]
      by_cases hmem : point ∈ definedDomain den subfamily
      · simp only [Set.indicator_apply, hmem, ↓reduceIte, Pi.one_apply, one_mul]
      · simp only [Set.indicator_apply, hmem, ↓reduceIte, zero_mul]
    rw [hmask]
    simp only [maskStatistic]
    rw [prod_mask_expansion, Finset.sum_mul]
    refine Finset.sum_congr rfl fun subset _ ↦ ?_
    rw [hsubfamily, mul_assoc]
  have htermIntegrable : ∀ subset ∈ selectedᶜ.powerset, Integrable (fun point ↦
      (-1 : ℝ) ^ subset.card *
        Set.indicator (definedDomain den (selected ∪ subset)) moment point) μ :=
    fun subset _ ↦ (hmomentIntegrable.indicator
      (measurableSet_definedDomain den hdenMeasurable (selected ∪ subset))).const_mul _
  rw [← integral_indicator (measurableSet_maskEvent den hdenMeasurable selected),
    integral_congr_ae (ae_of_all μ hpoint), integral_finset_sum _ htermIntegrable]
  refine Finset.sum_congr rfl fun subset _ ↦ ?_
  rw [integral_const_mul,
    integral_indicator (measurableSet_definedDomain den hdenMeasurable (selected ∪ subset))]

omit [DecidableEq Metric] in
/-- On a failure mask every metric outside the mask reads zero, so a metric monomial with a
positive exponent outside the mask has zero moment on the mask. -/
theorem masked_moment_eq_zero (μ : Measure Ω) (num den : Metric → Ω → ℝ)
    (selected : Finset Metric) (order : Metric → ℕ) (index : Metric)
    (hindex : index ∉ selected) (horder : order index ≠ 0) :
    ∫ point in maskEvent den selected,
      ∏ other, ratioOnDefined (num other) (den other) point ^ order other ∂μ = 0 := by
  refine setIntegral_eq_zero_of_forall_eq_zero fun point hpoint ↦ ?_
  have hnotPos : ¬ 0 < den index point := fun hpos ↦ hindex ((hpoint index).mp hpos)
  have hzero : ratioOnDefined (num index) (den index) point = 0 := by
    simp [ratioOnDefined, hnotPos]
  refine Finset.prod_eq_zero (Finset.mem_univ index) ?_
  show ratioOnDefined (num index) (den index) point ^ order index = 0
  rw [hzero, zero_pow horder]

/-- **NOTE 2 section 6.1, laws on a failure mask.** Two laws of the population under which
every metric monomial has the same moment on the failure mask `A` give the metric vector the
same law on that mask. -/
theorem maskMetricLaw_eq_of_masked_moments_eq (μ ν : Measure Ω) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] (num den : Metric → Ω → ℝ)
    (hnumMeasurable : ∀ index, Measurable (num index))
    (hdenMeasurable : ∀ index, Measurable (den index))
    (hnum : ∀ index point, 0 ≤ num index point)
    (hle : ∀ index point, num index point ≤ den index point) (selected : Finset Metric)
    (hmoment : ∀ order : Metric → ℕ,
      ∫ point in maskEvent den selected,
          ∏ index, ratioOnDefined (num index) (den index) point ^ order index ∂μ =
        ∫ point in maskEvent den selected,
          ∏ index, ratioOnDefined (num index) (den index) point ^ order index ∂ν) :
    (μ.restrict (maskEvent den selected)).map (metricVector num den hnum hle) =
      (ν.restrict (maskEvent den selected)).map (metricVector num den hnum hle) := by
  haveI : IsFiniteMeasure
      ((μ.restrict (maskEvent den selected)).map (metricVector num den hnum hle)) :=
    Measure.isFiniteMeasure_map _ _
  haveI : IsFiniteMeasure
      ((ν.restrict (maskEvent den selected)).map (metricVector num den hnum hle)) :=
    Measure.isFiniteMeasure_map _ _
  refine measure_eq_of_cube_moments_eq _ _ fun order ↦ ?_
  rw [integral_cubeMonomial_map _ num den hnumMeasurable hdenMeasurable hnum hle order,
    integral_cubeMonomial_map _ num den hnumMeasurable hdenMeasurable hnum hle order]
  exact hmoment order

/-- **NOTE 2 section 6.1, the mask law from subfamily moments.** If two laws of the population
give every metric monomial supported on the mask `A` the same moments on the events where every
metric of `A ∪ B` is defined, for every subset `B` of the complement, then the metric vector has
the same law on the failure mask `A` under both. Monomials with a positive exponent outside the
mask carry no information there, by `masked_moment_eq_zero`. -/
theorem maskMetricLaw_eq_of_subfamily_moments_eq (μ ν : Measure Ω) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (num den : Metric → Ω → ℝ)
    (hnumMeasurable : ∀ index, Measurable (num index))
    (hdenMeasurable : ∀ index, Measurable (den index))
    (hnum : ∀ index point, 0 ≤ num index point)
    (hle : ∀ index point, num index point ≤ den index point) (selected : Finset Metric)
    (hsubfamily : ∀ order : Metric → ℕ, (∀ index ∉ selected, order index = 0) →
      ∀ subset ∈ selectedᶜ.powerset,
        ∫ point in definedDomain den (selected ∪ subset),
            ∏ index, ratioOnDefined (num index) (den index) point ^ order index ∂μ =
          ∫ point in definedDomain den (selected ∪ subset),
            ∏ index, ratioOnDefined (num index) (den index) point ^ order index ∂ν) :
    (μ.restrict (maskEvent den selected)).map (metricVector num den hnum hle) =
      (ν.restrict (maskEvent den selected)).map (metricVector num den hnum hle) := by
  refine maskMetricLaw_eq_of_masked_moments_eq μ ν num den hnumMeasurable hdenMeasurable hnum
    hle selected fun order ↦ ?_
  by_cases hsupport : ∀ index ∉ selected, order index = 0
  · rw [masked_moment_expansion μ num den hnumMeasurable hdenMeasurable hnum hle order selected,
      masked_moment_expansion ν num den hnumMeasurable hdenMeasurable hnum hle order selected]
    refine Finset.sum_congr rfl fun subset hsubset ↦ ?_
    rw [hsubfamily order hsupport subset hsubset]
  · push_neg at hsupport
    obtain ⟨index, hindex, horder⟩ := hsupport
    rw [masked_moment_eq_zero μ num den selected order index hindex horder,
      masked_moment_eq_zero ν num den selected order index hindex horder]

end JointMetricLaw

end

end Descent.Portability.JointMetricMomentDeterminacy
