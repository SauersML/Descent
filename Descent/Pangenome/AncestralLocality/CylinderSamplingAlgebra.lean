/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Layer
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.MeasureTheory.Constructions.Cylinders
import Mathlib.Topology.ContinuousMap.StoneWeierstrass

assert_below Descent.PopGen Descent.Spectral Descent.Blindness Descent.Conditionals
assert_below Descent.Portability Descent.Decision Descent.Program

/-!
# Cylinder sampling polynomials on the genome laws of an infinite genome

Theorem 9 of the ancestral-locality note builds its Feller semigroup on `C(P(H))` for the genome
states `H = {0,1}^V` of a countable genome `V`, and its uniqueness step rests on the density of
the cylinder sampling polynomials in `C(P(H))`. Stone–Weierstrass gives that density once `P(H)`
is compact and the polynomials separate genome laws. This module proves both.

Compactness. For a compact Hausdorff Borel space `H`, `integralMap H` sends a probability measure
to its integrals against every continuous observable. It is continuous
(`continuous_integralMap`), and it induces the topology of weak convergence
(`isInducing_integralMap`), because weak convergence is convergence of all those integrals. Its
range is the set `positiveNormalizedFunctionals H` of additive, homogeneous, positive, normalized
functionals (`range_integralMap`): integrals have these properties (`integralMap_mem`), and every
such functional is the integral against the Riesz–Markov–Kakutani measure of the functional
(`exists_probabilityMeasure_of_mem`). That set is closed (`isClosed_positiveNormalizedFunctionals`)
and lies in the product of the intervals `[-‖g‖, ‖g‖]` (`abs_integralMap_le`), which is compact by
Tychonoff, so `P(H)` is compact (`compactSpace_probabilityMeasure`). This is Prokhorov's theorem on
a compact space, which Mathlib does not provide at this pin.

The sampling algebra. A cylinder observable (`cylinderObservable`) reads a genome through finitely
many features, and its integral against a genome law is a linear sampling observable
(`samplingMonomial`). `samplingAlgebra V` is the subalgebra they generate. Its members are the
sampling polynomials `H_f(p) = ∫ f(x_1, …, x_n) p(dx_1) … p(dx_n)` of cylinder readouts `f`:
products of linear sampling observables are those with product readouts, and a cylinder readout
of `n`
genomes is a finite combination of products. Two genome laws with equal linear sampling
observables are equal (`measure_eq_of_samplingMonomial_eq`), because the cylinders form a π-system
generating the product σ-algebra, so the algebra separates points
(`samplingAlgebra_separatesPoints`).

Density. The sampling algebra contains the constants (`algebraMap_mem_samplingAlgebra`) and
separates the points of the compact space `P(H)`, so Stone–Weierstrass makes its closure all of
`C(P(H))` (`samplingAlgebra_topologicalClosure_eq_top`): every continuous function of a genome law
is a uniform limit of cylinder sampling polynomials (`exists_samplingAlgebra_near`). This is the
uniqueness step of Theorem 9: two continuous maps on `C(P(H))` into a Hausdorff space that agree
on the sampling polynomials agree (`eq_of_eqOn_samplingAlgebra`).

Scope. The sampling polynomials of `n > 1` genomes are reached through the generated algebra, not
defined as integrals against product measures. Nothing about the dynamics is stated here.

## Empirical status

None. The bodies here are measure theory and topology: integrals of continuous observables,
compactness of a set of functionals, and uniqueness of measures agreeing on cylinders, so no
measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Pangenome.AncestralLocality.CylinderSamplingAlgebra

open MeasureTheory Filter Topology
open scoped CompactlySupported

noncomputable section

/-! ## Compactness of the probability measures on a compact space -/

section Compactness

variable (H : Type*) [TopologicalSpace H] [CompactSpace H] [T2Space H] [MeasurableSpace H]
  [BorelSpace H]

/-- The integrals of every continuous observable against a probability measure. -/
def integralMap : ProbabilityMeasure H → C(H, ℝ) → ℝ :=
  fun μ g ↦ ∫ x, g x ∂(μ : Measure H)

/-- The additive, homogeneous, positive and normalized functionals on the continuous
observables. -/
def positiveNormalizedFunctionals : Set (C(H, ℝ) → ℝ) :=
  {Λ | (∀ g h, Λ (g + h) = Λ g + Λ h) ∧ (∀ (c : ℝ) g, Λ (c • g) = c * Λ g) ∧
    (∀ g, 0 ≤ g → 0 ≤ Λ g) ∧ Λ 1 = 1}

omit [T2Space H] in
/-- Every continuous observable is integrable against a probability measure on a compact
space. -/
theorem integrable_observable (μ : ProbabilityMeasure H) (g : C(H, ℝ)) :
    Integrable (fun x ↦ g x) (μ : Measure H) :=
  (BoundedContinuousFunction.mkOfCompact g).integrable (μ := (μ : Measure H))

omit [T2Space H] in
/-- The integral map is continuous in the topology of weak convergence. -/
theorem continuous_integralMap : Continuous (integralMap H) :=
  continuous_pi fun g ↦ ProbabilityMeasure.continuous_integral_boundedContinuousFunction
    (BoundedContinuousFunction.mkOfCompact g)

/-- **The integral map induces the topology of weak convergence.** A filter converges to a
probability measure exactly when every integral of a continuous observable converges. -/
theorem isInducing_integralMap : IsInducing (integralMap H) := by
  refine isInducing_iff_nhds.mpr fun μ ↦ le_antisymm
    ((continuous_integralMap H).tendsto μ).le_comap ?_
  refine tendsto_id'.mp (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr fun f ↦ ?_)
  have hcoordinate : Continuous fun Λ : C(H, ℝ) → ℝ ↦ Λ f.toContinuousMap :=
    continuous_apply f.toContinuousMap
  exact (hcoordinate.tendsto _).comp tendsto_comap

/-- The integrals against a probability measure form a positive normalized functional. -/
theorem integralMap_mem (μ : ProbabilityMeasure H) :
    integralMap H μ ∈ positiveNormalizedFunctionals H := by
  refine ⟨fun g h ↦ ?_, fun c g ↦ ?_, fun g hg ↦ ?_, ?_⟩
  · show ∫ x, (g + h) x ∂(μ : Measure H) = _
    simp only [ContinuousMap.add_apply]
    exact integral_add (integrable_observable H μ g) (integrable_observable H μ h)
  · show ∫ x, (c • g) x ∂(μ : Measure H) = c * _
    simp only [ContinuousMap.smul_apply, smul_eq_mul]
    exact integral_const_mul c _
  · exact integral_nonneg fun x ↦ ContinuousMap.le_def.mp hg x
  · simp [integralMap]

/-- **Every positive normalized functional is an integral.** The Riesz–Markov–Kakutani measure of
the functional represents it, and it is a probability measure because the functional sends the
constant one to one. -/
theorem exists_probabilityMeasure_of_mem {Λ : C(H, ℝ) → ℝ}
    (hΛ : Λ ∈ positiveNormalizedFunctionals H) :
    ∃ μ : ProbabilityMeasure H, integralMap H μ = Λ := by
  obtain ⟨hadd, hsmul, hpos, hone⟩ := hΛ
  let functional : C_c(H, ℝ) →ₚ[ℝ] ℝ := PositiveLinearMap.mk₀
    { toFun := fun f ↦ Λ f.toContinuousMap
      map_add' := fun f g ↦ hadd f.toContinuousMap g.toContinuousMap
      map_smul' := fun c f ↦ hsmul c f.toContinuousMap }
    fun f hf ↦ hpos f.toContinuousMap (ContinuousMap.le_def.mpr fun y ↦
      CompactlySupportedContinuousMap.le_def.mp hf y)
  have hintegral : ∀ g : C(H, ℝ), ∫ x, g x ∂(RealRMK.rieszMeasure functional) = Λ g :=
    fun g ↦ RealRMK.integral_rieszMeasure functional
      (CompactlySupportedContinuousMap.ContinuousMap.liftCompactlySupported g)
  have hprobability : IsProbabilityMeasure (RealRMK.rieszMeasure functional) := by
    have hmass := hintegral 1
    simp only [hone, ContinuousMap.one_apply, integral_const, smul_eq_mul, mul_one] at hmass
    exact ⟨(ENNReal.toReal_eq_one_iff _).mp hmass⟩
  exact ⟨⟨RealRMK.rieszMeasure functional, hprobability⟩, funext hintegral⟩

/-- The range of the integral map is exactly the positive normalized functionals. -/
theorem range_integralMap : Set.range (integralMap H) = positiveNormalizedFunctionals H :=
  Set.Subset.antisymm (Set.range_subset_iff.mpr (integralMap_mem H))
    fun _ hΛ ↦ exists_probabilityMeasure_of_mem H hΛ

/-- The positive normalized functionals form a closed set of functionals: each defining condition
reads finitely many coordinates continuously. -/
theorem isClosed_positiveNormalizedFunctionals : IsClosed (positiveNormalizedFunctionals H) := by
  have hadd : IsClosed {Λ : C(H, ℝ) → ℝ | ∀ g h, Λ (g + h) = Λ g + Λ h} := by
    simp only [Set.setOf_forall]
    refine isClosed_iInter fun g ↦ isClosed_iInter fun h ↦ ?_
    have hsum : Continuous fun Λ : C(H, ℝ) → ℝ ↦ Λ g + Λ h :=
      (continuous_apply g).add (continuous_apply h)
    exact isClosed_eq (continuous_apply (g + h)) hsum
  have hsmul : IsClosed {Λ : C(H, ℝ) → ℝ | ∀ (c : ℝ) g, Λ (c • g) = c * Λ g} := by
    simp only [Set.setOf_forall]
    exact isClosed_iInter fun c ↦ isClosed_iInter fun g ↦
      isClosed_eq (continuous_apply _) (continuous_const.mul (continuous_apply _))
  have hpos : IsClosed {Λ : C(H, ℝ) → ℝ | ∀ g, 0 ≤ g → 0 ≤ Λ g} := by
    simp only [Set.setOf_forall]
    exact isClosed_iInter fun g ↦ isClosed_iInter fun _ ↦
      isClosed_le continuous_const (continuous_apply _)
  have hone : IsClosed {Λ : C(H, ℝ) → ℝ | Λ 1 = 1} :=
    isClosed_eq (continuous_apply _) continuous_const
  exact hadd.inter (hsmul.inter (hpos.inter hone))

omit [T2Space H] [BorelSpace H] in
/-- The integral of a continuous observable against a probability measure is at most its sup
norm. -/
theorem abs_integralMap_le (μ : ProbabilityMeasure H) (g : C(H, ℝ)) :
    |integralMap H μ g| ≤ ‖g‖ := by
  have hbound := norm_integral_le_of_norm_le_const (μ := (μ : Measure H))
    (Eventually.of_forall fun x ↦ ContinuousMap.norm_coe_le_norm g x)
  simpa [integralMap] using hbound

/-- **The probability measures on a compact Hausdorff Borel space form a compact space.** The
integral map is an inducing map onto a closed subset of a product of compact intervals. -/
instance compactSpace_probabilityMeasure : CompactSpace (ProbabilityMeasure H) := by
  have hsub : positiveNormalizedFunctionals H ⊆
      Set.pi Set.univ fun g : C(H, ℝ) ↦ Set.Icc (-‖g‖) ‖g‖ := by
    intro Λ hΛ g _
    obtain ⟨μ, rfl⟩ := exists_probabilityMeasure_of_mem H hΛ
    exact abs_le.mp (abs_integralMap_le H μ g)
  have hcompact : IsCompact (positiveNormalizedFunctionals H) :=
    (isCompact_univ_pi fun g ↦ isCompact_Icc).of_isClosed_subset
      (isClosed_positiveNormalizedFunctionals H) hsub
  refine ⟨(isInducing_integralMap H).isCompact_iff.mpr ?_⟩
  rw [Set.image_univ, range_integralMap]
  exact hcompact

end Compactness

/-! ## The cylinder sampling algebra -/

section Sampling

variable {V : Type*}

/-- A cylinder observable on the genome states `{0,1}^V`: a readout of finitely many features. -/
def cylinderObservable (features : Finset V) (readout : (features → Bool) → ℝ) :
    C(V → Bool, ℝ) where
  toFun x := readout (features.restrict x)
  continuous_toFun :=
    continuous_of_discreteTopology.comp (continuous_pi fun v ↦ continuous_apply v.1)

variable [Countable V]

/-- The linear sampling observable of a cylinder readout: its integral against a genome law. -/
def samplingMonomial (features : Finset V) (readout : (features → Bool) → ℝ) :
    C(ProbabilityMeasure (V → Bool), ℝ) where
  toFun μ := ∫ x, cylinderObservable features readout x ∂(μ : Measure (V → Bool))
  continuous_toFun := ProbabilityMeasure.continuous_integral_boundedContinuousFunction
    (BoundedContinuousFunction.mkOfCompact (cylinderObservable features readout))

variable (V) in
/-- **The cylinder sampling algebra**, generated by the linear sampling observables of cylinder
readouts. -/
def samplingAlgebra : Subalgebra ℝ C(ProbabilityMeasure (V → Bool), ℝ) :=
  Algebra.adjoin ℝ (Set.range fun readout : Σ features : Finset V, ((features → Bool) → ℝ) ↦
    samplingMonomial readout.1 readout.2)

/-- **Genome laws are determined by their cylinder integrals.** Two probability measures on
`{0,1}^V` with equal linear sampling observables agree on every cylinder, and the cylinders form a
π-system generating the product σ-algebra. -/
theorem measure_eq_of_samplingMonomial_eq {μ ν : ProbabilityMeasure (V → Bool)}
    (h : ∀ features readout,
      samplingMonomial features readout μ = samplingMonomial features readout ν) :
    μ = ν := by
  haveI : IsProbabilityMeasure (μ.1 : Measure (V → Bool)) := μ.2
  refine Subtype.ext (ext_of_generate_finite (measurableCylinders fun _ : V ↦ Bool)
    generateFrom_measurableCylinders.symm isPiSystem_measurableCylinders (fun C hC ↦ ?_) ?_)
  · obtain ⟨features, S, hS, rfl⟩ := (mem_measurableCylinders C).mp hC
    have hindicator : ∀ ρ : ProbabilityMeasure (V → Bool),
        samplingMonomial features (S.indicator 1) ρ =
          (ρ : Measure (V → Bool)).real (cylinder features S) := by
      intro ρ
      rw [← integral_indicator_one (measurableSet_cylinder features S hS)]
      refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
      simp only [cylinderObservable, ContinuousMap.coe_mk, Set.indicator_apply, mem_cylinder,
        Pi.one_apply]
    have hreal := h features (S.indicator 1)
    rw [hindicator, hindicator] at hreal
    exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp hreal
  · simp

/-- **The cylinder sampling algebra separates genome laws.** -/
theorem samplingAlgebra_separatesPoints : (samplingAlgebra V).SeparatesPoints := by
  intro μ ν hne
  by_contra hsame
  refine hne (measure_eq_of_samplingMonomial_eq fun features readout ↦ ?_)
  by_contra hdiff
  exact hsame ⟨samplingMonomial features readout,
    ⟨samplingMonomial features readout, Algebra.subset_adjoin ⟨⟨features, readout⟩, rfl⟩, rfl⟩,
    hdiff⟩

end Sampling

/-! ## Density of the sampling algebra -/

section Density

variable {V : Type*} [Countable V]

/-- The constants are cylinder sampling polynomials. -/
theorem algebraMap_mem_samplingAlgebra (c : ℝ) :
    algebraMap ℝ C(ProbabilityMeasure (V → Bool), ℝ) c ∈ samplingAlgebra V :=
  (samplingAlgebra V).algebraMap_mem c

/-- Every linear sampling observable of a cylinder readout is a cylinder sampling polynomial. -/
theorem samplingMonomial_mem_samplingAlgebra (features : Finset V)
    (readout : (features → Bool) → ℝ) :
    samplingMonomial features readout ∈ samplingAlgebra V :=
  Algebra.subset_adjoin ⟨⟨features, readout⟩, rfl⟩

/-- **The cylinder sampling polynomials are dense in `C(P(H))`.** By Stone–Weierstrass: the genome
laws form a compact space, and the sampling algebra contains the constants and separates them. -/
theorem samplingAlgebra_topologicalClosure_eq_top :
    (samplingAlgebra V).topologicalClosure = ⊤ :=
  ContinuousMap.subalgebra_topologicalClosure_eq_top_of_separatesPoints (samplingAlgebra V)
    samplingAlgebra_separatesPoints

/-- Every continuous function of a genome law is uniformly approximated, to any accuracy, by a
cylinder sampling polynomial. -/
theorem exists_samplingAlgebra_near (f : C(ProbabilityMeasure (V → Bool), ℝ)) {ε : ℝ}
    (hε : 0 < ε) : ∃ g ∈ samplingAlgebra V, ‖g - f‖ < ε := by
  obtain ⟨g, hg⟩ := ContinuousMap.exists_mem_subalgebra_near_continuousMap_of_separatesPoints
    (samplingAlgebra V) samplingAlgebra_separatesPoints f ε hε
  exact ⟨g, g.2, hg⟩

/-- **Uniqueness through the sampling algebra.** Two continuous maps on `C(P(H))` into a Hausdorff
space that agree on the cylinder sampling polynomials agree everywhere. -/
theorem eq_of_eqOn_samplingAlgebra {E : Type*} [TopologicalSpace E] [T2Space E]
    {first second : C(ProbabilityMeasure (V → Bool), ℝ) → E} (hfirst : Continuous first)
    (hsecond : Continuous second) (hagree : ∀ g ∈ samplingAlgebra V, first g = second g) :
    first = second := by
  have hdense : Dense (samplingAlgebra V : Set C(ProbabilityMeasure (V → Bool), ℝ)) := by
    intro f
    have hmember : f ∈ (samplingAlgebra V).topologicalClosure := by
      rw [samplingAlgebra_topologicalClosure_eq_top]
      exact Algebra.mem_top
    exact hmember
  exact hfirst.ext_on hdense hsecond hagree

end Density

end

end Descent.Pangenome.AncestralLocality.CylinderSamplingAlgebra
