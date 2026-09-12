/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.AncestralLocality.CylinderWindowProjection
import Descent.Pangenome.AncestralLocality.InfiniteGenomeLimit
import Descent.Portability.ResamplingWindowConsistency

assert_below Descent.Decision Descent.Program

/-!
# Theorem 9 without decisions: the resampling semigroup of an infinite genome

Theorem 9 of the research note "Ancestral locality" builds one Feller semigroup on `P({0,1}^V)` for
a countable genome `V`. `InfiniteGenomeLimit` proves the operator half from a light-cone
approximation hypothesis. Without decisions (`r = 0`) no hypothesis is needed. The window
semigroups are exactly consistent, so the light-cone error is zero, and this module constructs the
semigroup.

Laws of a window as window states. A law of finitely many genome types `G` is determined by the
masses of the single types, so `lawFrequency` sends it to a state of the window model of
`ResamplingWindowSemigroup`. It is continuous, injective and onto, hence a homeomorphism
(`lawFrequencyHomeomorph`). Read through it, the window semigroup is a positive contraction
semigroup on the continuous functions of window laws (`lawOperator`, with `lawOperator_zero`,
`lawOperator_add`, `lawOperator_one`, `norm_lawOperator_le`, `tendsto_lawOperator_zero`).

Consistency. Pushing a law of the letters on a window `W'` to a smaller window `W` is the window
marginalization of `ResamplingWindowConsistency` in the frequency coordinates
(`lawFrequency_shrinkLaw`). So the window operators commute with the pullbacks between windows on
every continuous observable (`lawOperator_shrinkPullback`). At every time they form a
`CylinderWindowProjection.WindowOperatorFamily` (`resamplingWindowFamily`), whose extended operator
on `C(P({0,1}^V))` is `resamplingOperator`. The sampling algebra of a window separates its laws
(`windowAlgebra_separatesPoints`). Hence, for a family of continuous window operators, the
extended operator applied to the pullback of any continuous function of a window law is the
pullback of the window operator (`extendedOperator_windowPullback`).

The Feller semigroup. The resampling operators contract (`norm_resamplingOperator_le`) and fix the
constants (`resamplingOperator_one`), so they are positive (`resamplingOperator_nonneg`). They start
at the identity (`resamplingOperator_zero`), obey the semigroup law (`resamplingOperator_add`) and
are strongly continuous at time zero (`tendsto_resamplingOperator_zero`). Each identity is checked
on the cylinder sampling polynomials through a window they read, then extended by the density of
`CylinderSamplingAlgebra.samplingAlgebra_topologicalClosure_eq_top`. Together they are a Feller
semigroup on `P({0,1}^V)` (`resamplingFellerSemigroup`). Any Feller semigroup that runs the window
semigroups on the window pullbacks is this one (`operator_eq_resamplingFellerSemigroup`).

Theorem 9 at `r = 0`. The constant exhaustion by the resampling semigroup satisfies the light-cone
approximation bound with zero escape (`resamplingApproximation`). So the infinite-genome semigroup
of `InfiniteGenomeLimit` exists with no hypothesis, and it is the resampling semigroup
(`infiniteGenomeSemigroup_resampling`, `infiniteGenomeSemigroup_operator_resampling`).

Scope. Only the pure-resampling case `r = 0` with coalescence rate one is treated.

## Empirical status

None. The bodies here are measure theory and functional analysis on laws of finite and countable
genomes, so no measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.ResamplingInfiniteGenome

open MeasureTheory Filter Topology PartialHaplotypeDualGenerator NeutralFellerGenerator
  PolynomialFellerExtension ResamplingWindowSemigroup ResamplingWindowConsistency
open Descent.Pangenome.AncestralLocality.CylinderSamplingAlgebra
  Descent.Pangenome.AncestralLocality.CylinderWindowProjection
  Descent.Pangenome.AncestralLocality.InfiniteGenomeLimit
open scoped NNReal

noncomputable section

/-! ## Precomposition -/

/-- Precomposition with a continuous map between compact spaces, as a continuous linear
contraction. -/
def precomposeContraction {X Y : Type*} [TopologicalSpace X] [CompactSpace X]
    [TopologicalSpace Y] [CompactSpace Y] (e : C(X, Y)) : C(Y, ℝ) →L[ℝ] C(X, ℝ) :=
  LinearMap.mkContinuous
    { toFun := fun g ↦ g.comp e
      map_add' := fun g g' ↦ ContinuousMap.add_comp g g' e
      map_smul' := fun c g ↦ ContinuousMap.smul_comp c g e } 1 fun g ↦ by
    rw [one_mul]
    exact (ContinuousMap.norm_le _ (norm_nonneg g)).mpr fun x ↦
      ContinuousMap.norm_coe_le_norm g (e x)

/-! ## Laws of genome types as window states -/

section Transport

variable {G : Type*} [Fintype G] [MeasurableSpace G] [MeasurableSingletonClass G]

/-- The mass of each genome type under a law, as window frequencies. -/
def lawFrequencyVector (ν : ProbabilityMeasure G) : FrequencyVariable Unit Unit (fun _ ↦ G) → ℝ :=
  fun v ↦ (ν : Measure G).real {v.2 ()}

/-- The masses of the genome types form a window state. -/
theorem lawFrequencyVector_mem (ν : ProbabilityMeasure G) :
    lawFrequencyVector ν ∈ frequencySimplex Unit Unit (fun _ ↦ G) := by
  refine ⟨fun _ ↦ measureReal_nonneg, fun _ ↦ ?_⟩
  change ∑ h : FullHaplotype Unit (fun _ ↦ G), (ν : Measure G).real {h ()} = 1
  have hsum : ∑ h : FullHaplotype Unit (fun _ ↦ G), (ν : Measure G).real {h ()}
      = ∑ g : G, (ν : Measure G).real {g} :=
    Fintype.sum_equiv (Equiv.funUnique Unit G) _ _ fun _ ↦ rfl
  rw [hsum, sum_measureReal_singleton, Finset.coe_univ, measureReal_univ_eq_one]

variable [TopologicalSpace G] [DiscreteTopology G] [BorelSpace G]

/-- **The window state of a law of genome types.** -/
def lawFrequency : C(ProbabilityMeasure G, FrequencyState Unit Unit (fun _ ↦ G)) where
  toFun ν := ⟨lawFrequencyVector ν, lawFrequencyVector_mem ν⟩
  continuous_toFun := by
    refine Continuous.subtype_mk (continuous_pi fun v ↦ ?_) _
    refine (ProbabilityMeasure.continuous_integral_boundedContinuousFunction
      (BoundedContinuousFunction.mkOfCompact
        ⟨({v.2 ()} : Set G).indicator (1 : G → ℝ), continuous_of_discreteTopology⟩)).congr
      fun ν ↦ ?_
    exact integral_indicator_one (MeasurableSet.singleton _)

/-- Every window state is the window state of a law. -/
theorem lawFrequency_surjective : Function.Surjective (lawFrequency (G := G)) := by
  intro y
  have hreal : ∑ g : G, y.1 ((), fun _ ↦ g) = 1 := by
    refine Eq.trans ?_ (sum_windowFrequency G y)
    exact (Fintype.sum_equiv (Equiv.funUnique Unit G) (windowFrequency G y)
      (fun g ↦ y.1 ((), fun _ ↦ g)) fun _ ↦ rfl).symm
  have hsum : ∑ g : G, ENNReal.ofReal (y.1 ((), fun _ ↦ g)) = 1 := by
    rw [← ENNReal.ofReal_one, ← hreal,
      ENNReal.ofReal_sum_of_nonneg fun g _ ↦ y.2.1 ((), fun _ ↦ g)]
  refine ⟨⟨(PMF.ofFintype (fun g : G ↦ ENNReal.ofReal (y.1 ((), fun _ ↦ g))) hsum).toMeasure,
    inferInstance⟩, Subtype.ext (funext fun v ↦ ?_)⟩
  obtain ⟨⟨⟩, h⟩ := v
  change ((PMF.ofFintype (fun g : G ↦ ENNReal.ofReal (y.1 ((), fun _ ↦ g))) hsum).toMeasure).real
    {h ()} = y.1 ((), h)
  rw [measureReal_def, PMF.toMeasure_apply_singleton _ _ (MeasurableSet.singleton _),
    PMF.ofFintype_apply]
  exact ENNReal.toReal_ofReal (y.2.1 _)

/-- A law is determined by its window state. -/
theorem lawFrequency_injective : Function.Injective (lawFrequency (G := G)) := by
  intro ν ν' hequal
  apply ProbabilityMeasure.toMeasure_injective
  refine Measure.ext_of_singleton fun g ↦ ?_
  have hcoordinate :=
    congrArg (fun y : FrequencyState Unit Unit (fun _ ↦ G) ↦ y.1 ((), fun _ ↦ g)) hequal
  change (ν : Measure G).real {g} = (ν' : Measure G).real {g} at hcoordinate
  exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp hcoordinate

/-- **Laws of genome types are window states**: `lawFrequency` is a homeomorphism. -/
def lawFrequencyHomeomorph : ProbabilityMeasure G ≃ₜ FrequencyState Unit Unit (fun _ ↦ G) :=
  Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective lawFrequency ⟨lawFrequency_injective, lawFrequency_surjective⟩)
    lawFrequency.continuous

/-- A function of laws, read at the law of a window state. -/
theorem comp_symm_lawFrequency (g : C(ProbabilityMeasure G, ℝ)) (ν : ProbabilityMeasure G) :
    (g.comp (lawFrequencyHomeomorph (G := G)).symm.toContinuousMap) (lawFrequency ν) = g ν :=
  congrArg g ((lawFrequencyHomeomorph (G := G)).symm_apply_apply ν)

variable [DecidableEq G]

variable (G) in
/-- **The resampling operator on laws of genome types** at time `t`: the window semigroup read
through the window states of laws. -/
def lawOperator (g₀ : G) (t : ℝ≥0) :
    C(ProbabilityMeasure G, ℝ) →L[ℝ] C(ProbabilityMeasure G, ℝ) :=
  (precomposeContraction (lawFrequency (G := G))).comp
    (((windowSemigroup G fun _ ↦ g₀).operator t).comp
      (precomposeContraction (lawFrequencyHomeomorph (G := G)).symm.toContinuousMap))

/-- The resampling operator evaluates the window semigroup at the window state of the law. -/
theorem lawOperator_apply (g₀ : G) (t : ℝ≥0) (g : C(ProbabilityMeasure G, ℝ))
    (ν : ProbabilityMeasure G) :
    lawOperator G g₀ t g ν = (windowSemigroup G fun _ ↦ g₀).operator t
      (g.comp (lawFrequencyHomeomorph (G := G)).symm.toContinuousMap) (lawFrequency ν) :=
  rfl

/-- The resampling operator at time zero is the identity. -/
theorem lawOperator_zero (g₀ : G) :
    lawOperator G g₀ 0 = ContinuousLinearMap.id ℝ C(ProbabilityMeasure G, ℝ) := by
  refine ContinuousLinearMap.ext fun g ↦ ContinuousMap.ext fun ν ↦ ?_
  rw [lawOperator_apply, (windowSemigroup G fun _ ↦ g₀).operator_zero,
    ContinuousLinearMap.id_apply, comp_symm_lawFrequency, ContinuousLinearMap.id_apply]

/-- **The semigroup law** of the resampling operators on laws. -/
theorem lawOperator_add (g₀ : G) (s t : ℝ≥0) :
    lawOperator G g₀ (s + t) = (lawOperator G g₀ s).comp (lawOperator G g₀ t) := by
  refine ContinuousLinearMap.ext fun g ↦ ContinuousMap.ext fun ν ↦ ?_
  have hinner : (lawOperator G g₀ t g).comp (lawFrequencyHomeomorph (G := G)).symm.toContinuousMap
      = (windowSemigroup G fun _ ↦ g₀).operator t
          (g.comp (lawFrequencyHomeomorph (G := G)).symm.toContinuousMap) := by
    ext y
    rw [ContinuousMap.comp_apply, lawOperator_apply]
    exact congrArg (fun z ↦ (windowSemigroup G fun _ ↦ g₀).operator t
      (g.comp (lawFrequencyHomeomorph (G := G)).symm.toContinuousMap) z)
      ((lawFrequencyHomeomorph (G := G)).apply_symm_apply y)
  rw [ContinuousLinearMap.comp_apply, lawOperator_apply, lawOperator_apply, hinner,
    (windowSemigroup G fun _ ↦ g₀).operator_add, ContinuousLinearMap.comp_apply]

/-- The resampling operators fix the constant one. -/
theorem lawOperator_one (g₀ : G) (t : ℝ≥0) : lawOperator G g₀ t 1 = 1 := by
  ext ν
  rw [lawOperator_apply, ContinuousMap.one_comp, (windowSemigroup G fun _ ↦ g₀).map_one,
    ContinuousMap.one_apply, ContinuousMap.one_apply]

/-- The resampling operators contract the sup norm. -/
theorem norm_lawOperator_le (g₀ : G) (t : ℝ≥0) (g : C(ProbabilityMeasure G, ℝ)) :
    ‖lawOperator G g₀ t g‖ ≤ ‖g‖ :=
  (ContinuousMap.norm_le _ (norm_nonneg g)).mpr fun ν ↦ by
    rw [lawOperator_apply]
    exact (ContinuousMap.norm_coe_le_norm _ _).trans
      (((windowSemigroup G fun _ ↦ g₀).norm_le t _).trans
        ((ContinuousMap.norm_le _ (norm_nonneg g)).mpr fun y ↦ ContinuousMap.norm_coe_le_norm g _))

/-- The resampling operators are strongly continuous at time zero. -/
theorem tendsto_lawOperator_zero (g₀ : G) (g : C(ProbabilityMeasure G, ℝ)) :
    Tendsto (fun t ↦ lawOperator G g₀ t g) (𝓝 0) (𝓝 g) := by
  have hwindow := tendsto_iff_norm_sub_tendsto_zero.mp
    ((windowSemigroup G fun _ ↦ g₀).tendsto_operator_zero
      (g.comp (lawFrequencyHomeomorph (G := G)).symm.toContinuousMap))
  refine tendsto_iff_norm_sub_tendsto_zero.mpr
    (squeeze_zero (fun _ ↦ norm_nonneg _) (fun t ↦ ?_) hwindow)
  refine (ContinuousMap.norm_le _ (norm_nonneg _)).mpr fun ν ↦ ?_
  rw [ContinuousMap.sub_apply, lawOperator_apply, ← comp_symm_lawFrequency g ν,
    ← ContinuousMap.sub_apply]
  exact ContinuousMap.norm_coe_le_norm _ _

end Transport

/-! ## The resampling operators of a countable genome -/

section Genome

variable {V : Type*} [Countable V] [DecidableEq V]

omit [Countable V] [DecidableEq V] in
/-- **Pushing a law to a smaller window is the window marginalization** in the frequency
coordinates. -/
theorem lawFrequency_shrinkLaw {W W' : Finset V} (h : W ⊆ W')
    (ν : ProbabilityMeasure (W' → Bool)) :
    lawFrequency (shrinkLaw h ν) = windowMarginal (shrinkWindow h) (lawFrequency ν) := by
  refine Subtype.ext (funext fun v ↦ ?_)
  obtain ⟨⟨⟩, letters⟩ := v
  change (shrinkLaw h ν : Measure (W → Bool)).real {letters ()}
    = pushVector (windowTypeMap (shrinkWindow h))
        (windowFrequency (W' → Bool) (lawFrequency ν)) letters
  have hpreimage : (shrinkWindow h ⁻¹' {letters ()} : Set (W' → Bool))
      = ↑(Finset.univ.filter fun l' : W' → Bool ↦ shrinkWindow h l' = letters ()) := by
    ext l'
    simp
  rw [shrinkLaw, ProbabilityMeasure.toMeasure_map,
    map_measureReal_apply (continuous_shrinkWindow h).measurable (MeasurableSet.singleton _),
    hpreimage, ← sum_measureReal_singleton, Finset.sum_filter]
  simp only [pushVector]
  rw [Finset.sum_filter]
  refine (Fintype.sum_equiv (Equiv.funUnique Unit (W' → Bool)) _ _ fun h' ↦ ?_).symm
  exact if_congr ⟨fun hequal ↦ congrFun hequal (), fun hequal ↦ funext fun _ ↦ hequal⟩ rfl rfl

omit [Countable V] in
/-- **The window operators are consistent.** Read through the pullback to a larger window, the
resampling operator of the larger window is the pullback of the smaller window's operator. -/
theorem lawOperator_shrinkPullback {W W' : Finset V} (h : W ⊆ W') (t : ℝ≥0)
    (g : C(ProbabilityMeasure (W → Bool), ℝ)) :
    lawOperator (W' → Bool) (fun _ ↦ false) t (shrinkPullback h g)
      = shrinkPullback h (lawOperator (W → Bool) (fun _ ↦ false) t g) := by
  have hcomp : (shrinkPullback h g).comp
        (lawFrequencyHomeomorph (G := W' → Bool)).symm.toContinuousMap
      = (g.comp (lawFrequencyHomeomorph (G := W → Bool)).symm.toContinuousMap).comp
          (windowMarginal (shrinkWindow h)) := by
    ext y
    obtain ⟨ν, rfl⟩ := lawFrequency_surjective (G := W' → Bool) y
    change g (shrinkLaw h ((lawFrequencyHomeomorph (G := W' → Bool)).symm
        (lawFrequencyHomeomorph ν)))
      = g ((lawFrequencyHomeomorph (G := W → Bool)).symm
          (windowMarginal (shrinkWindow h) (lawFrequency ν)))
    rw [Homeomorph.symm_apply_apply, ← lawFrequency_shrinkLaw]
    exact congrArg g ((lawFrequencyHomeomorph (G := W → Bool)).symm_apply_apply
      (shrinkLaw h ν)).symm
  ext ν
  rw [lawOperator_apply, hcomp,
    windowSemigroup_comp_windowMarginal (shrinkWindow h) (fun _ _ ↦ false) (fun _ _ ↦ false) t,
    ContinuousMap.comp_apply, shrinkPullback_apply, lawOperator_apply, lawFrequency_shrinkLaw]

variable (V) in
/-- **The resampling window operators** at time `t`, a consistent family of window operators. -/
def resamplingWindowFamily (t : ℝ≥0) : WindowOperatorFamily V where
  operator W := (lawOperator (W → Bool) (fun _ ↦ false) t).toLinearMap
  contraction W g := norm_lawOperator_le (fun _ ↦ false) t g
  consistent h g _ := lawOperator_shrinkPullback h t g

omit [DecidableEq V] in
/-- The sampling algebra of a window separates the laws of the window. -/
theorem windowAlgebra_separatesPoints (W : Finset V) : (windowAlgebra W).SeparatesPoints := by
  intro ν ν' hne
  by_contra hsame
  refine hne (lawFrequency_injective (Subtype.ext (funext fun v ↦ ?_)))
  by_contra hdiff
  have hindicator : ∀ μ : ProbabilityMeasure (W → Bool),
      windowMonomial W (({v.2 ()} : Set (W → Bool)).indicator 1) μ
        = (μ : Measure (W → Bool)).real {v.2 ()} :=
    fun μ ↦ integral_indicator_one (MeasurableSet.singleton _)
  exact hsame ⟨windowMonomial W (({v.2 ()} : Set (W → Bool)).indicator 1),
    ⟨windowMonomial W (({v.2 ()} : Set (W → Bool)).indicator 1),
      windowMonomial_mem_windowAlgebra W _, rfl⟩,
    by rwa [hindicator, hindicator]⟩

/-- **The extended operator on window pullbacks.** For a family of continuous window operators,
the extended operator applied to the pullback of any continuous function of a window law is the
pullback of the window operator. -/
theorem extendedOperator_windowPullback (T : WindowOperatorFamily V)
    (hT : ∀ W, Continuous (T.operator W)) (W : Finset V)
    (g : C(ProbabilityMeasure (W → Bool), ℝ)) :
    extendedOperator T (windowPullback W g) = windowPullback W (T.operator W g) := by
  have hcont₁ : Continuous fun g : C(ProbabilityMeasure (W → Bool), ℝ) ↦
      extendedOperator T (windowPullback W g) :=
    (extendedOperator T).continuous.comp
      (ContinuousMap.continuous_precomp ⟨windowLaw W, continuous_windowLaw W⟩)
  have hcont₂ : Continuous fun g : C(ProbabilityMeasure (W → Bool), ℝ) ↦
      windowPullback W (T.operator W g) :=
    (ContinuousMap.continuous_precomp ⟨windowLaw W, continuous_windowLaw W⟩).comp (hT W)
  have hagree := hcont₁.ext_on
    (dense_subalgebra_of_separatesPoints _ (windowAlgebra_separatesPoints W)) hcont₂
    fun g hg ↦ by
      change extendedOperator T
        ((⟨windowPullback W g, windowPullback_mem_samplingAlgebra hg⟩ :
          (samplingAlgebra V).toSubmodule) : C(ProbabilityMeasure (V → Bool), ℝ)) = _
      rw [extendedOperator_apply, gluedOperator_windowPullback T hg
        ⟨windowPullback W g, windowPullback_mem_samplingAlgebra hg⟩ rfl]
  exact congrFun hagree g

variable (V) in
/-- **The resampling operator** of the countable genome at time `t`. -/
def resamplingOperator (t : ℝ≥0) :
    C(ProbabilityMeasure (V → Bool), ℝ) →L[ℝ] C(ProbabilityMeasure (V → Bool), ℝ) :=
  extendedOperator (resamplingWindowFamily V t)

/-- Applied to the pullback of a function of a window law, the resampling operator runs the
window. -/
theorem resamplingOperator_windowPullback (t : ℝ≥0) (W : Finset V)
    (g : C(ProbabilityMeasure (W → Bool), ℝ)) :
    resamplingOperator V t (windowPullback W g)
      = windowPullback W (lawOperator (W → Bool) (fun _ ↦ false) t g) :=
  extendedOperator_windowPullback (resamplingWindowFamily V t)
    (fun W' ↦ (lawOperator (W' → Bool) (fun _ ↦ false) t).continuous) W g

/-- The resampling operators contract the sup norm. -/
theorem norm_resamplingOperator_le (t : ℝ≥0) (g : C(ProbabilityMeasure (V → Bool), ℝ)) :
    ‖resamplingOperator V t g‖ ≤ ‖g‖ :=
  ((resamplingOperator V t).le_opNorm g).trans
    (mul_le_of_le_one_left (norm_nonneg g) (norm_extendedOperator_le (resamplingWindowFamily V t)))

/-- The resampling operators fix the constant one. -/
theorem resamplingOperator_one (t : ℝ≥0) : resamplingOperator V t 1 = 1 := by
  have hone : (1 : C(ProbabilityMeasure (V → Bool), ℝ)) = windowPullback ∅ 1 := (map_one _).symm
  rw [hone, resamplingOperator_windowPullback, lawOperator_one]

/-- The resampling operators are positive. -/
theorem resamplingOperator_nonneg (t : ℝ≥0) (g : C(ProbabilityMeasure (V → Bool), ℝ))
    (hg : 0 ≤ g) : 0 ≤ resamplingOperator V t g :=
  nonneg_of_norm_le_of_map_unit LinearMap.id (resamplingOperator V t).toLinearMap 1 rfl
    (resamplingOperator_one t) (fun f ↦ norm_resamplingOperator_le t f) g hg

/-- The resampling operator at time zero is the identity. -/
theorem resamplingOperator_zero :
    resamplingOperator V 0 = ContinuousLinearMap.id ℝ C(ProbabilityMeasure (V → Bool), ℝ) := by
  refine ContinuousLinearMap.ext fun g ↦ congrFun (eq_of_eqOn_samplingAlgebra
    (resamplingOperator V 0).continuous continuous_id fun f hf ↦ ?_) g
  obtain ⟨W, k, _, rfl⟩ := exists_windowPullback hf
  rw [resamplingOperator_windowPullback, lawOperator_zero, ContinuousLinearMap.id_apply, id_eq]

/-- **The semigroup law** of the resampling operators. -/
theorem resamplingOperator_add (s t : ℝ≥0) :
    resamplingOperator V (s + t) = (resamplingOperator V s).comp (resamplingOperator V t) := by
  refine ContinuousLinearMap.ext fun g ↦ congrFun (eq_of_eqOn_samplingAlgebra
    (resamplingOperator V (s + t)).continuous
    ((resamplingOperator V s).comp (resamplingOperator V t)).continuous fun f hf ↦ ?_) g
  obtain ⟨W, k, _, rfl⟩ := exists_windowPullback hf
  rw [ContinuousLinearMap.comp_apply, resamplingOperator_windowPullback,
    resamplingOperator_windowPullback, resamplingOperator_windowPullback, lawOperator_add,
    ContinuousLinearMap.comp_apply]

/-- The resampling operators are strongly continuous at time zero. -/
theorem tendsto_resamplingOperator_zero (g : C(ProbabilityMeasure (V → Bool), ℝ)) :
    Tendsto (fun t ↦ resamplingOperator V t g) (𝓝 0) (𝓝 g) := by
  refine Metric.tendsto_nhds.mpr fun ε hε ↦ ?_
  obtain ⟨f, hf, hfg⟩ := exists_samplingAlgebra_near g (by positivity : (0 : ℝ) < ε / 3)
  obtain ⟨W, k, _, rfl⟩ := exists_windowPullback hf
  filter_upwards [Metric.tendsto_nhds.mp (tendsto_lawOperator_zero (G := W → Bool)
    (fun _ ↦ false) k) (ε / 3) (by positivity)] with t ht
  have hsplit : resamplingOperator V t g - g
      = resamplingOperator V t (g - windowPullback W k)
        + windowPullback W (lawOperator (W → Bool) (fun _ ↦ false) t k - k)
        + (windowPullback W k - g) := by
    simp only [map_sub, resamplingOperator_windowPullback]
    abel
  have h₁ : ‖resamplingOperator V t (g - windowPullback W k)‖ < ε / 3 :=
    (norm_resamplingOperator_le t _).trans_lt (by rwa [norm_sub_rev])
  have h₂ : ‖windowPullback W (lawOperator (W → Bool) (fun _ ↦ false) t k - k)‖ < ε / 3 := by
    rw [norm_windowPullback, ← dist_eq_norm]
    exact ht
  rw [dist_eq_norm, hsplit]
  exact norm_add₃_le.trans_lt (by linarith)

variable (V) in
/-- **Theorem 9 without decisions: the resampling Feller semigroup** on the genome laws of a
countable genome. -/
def resamplingFellerSemigroup : FellerSemigroup (ProbabilityMeasure (V → Bool)) where
  operator := resamplingOperator V
  norm_le := norm_resamplingOperator_le
  map_one := resamplingOperator_one
  nonneg t g hg := resamplingOperator_nonneg t g hg
  operator_zero := resamplingOperator_zero
  operator_add := resamplingOperator_add
  tendsto_operator_zero := tendsto_resamplingOperator_zero

/-- **Uniqueness.** A Feller semigroup on the genome laws that runs the resampling window
semigroups on the pullback of every window sampling polynomial is the resampling semigroup. -/
theorem operator_eq_resamplingFellerSemigroup
    (P : FellerSemigroup (ProbabilityMeasure (V → Bool)))
    (h : ∀ t (W : Finset V) (g : C(ProbabilityMeasure (W → Bool), ℝ)), g ∈ windowAlgebra W →
      P.operator t (windowPullback W g)
        = windowPullback W (lawOperator (W → Bool) (fun _ ↦ false) t g)) :
    P.operator = (resamplingFellerSemigroup V).operator :=
  operator_eq_of_eqOn P _ samplingAlgebra_separatesPoints fun t f hf ↦ by
    obtain ⟨W, g, hg, rfl⟩ := exists_windowPullback hf
    rw [h t W g hg]
    exact (resamplingOperator_windowPullback t W g).symm

variable (V) in
/-- The constant exhaustion by the resampling semigroup satisfies the light-cone approximation
bound with zero escape: the window semigroups agree on every cylinder sampling polynomial. -/
def resamplingApproximation :
    LightConeApproximation (fun _ : ℕ ↦ resamplingFellerSemigroup V) (samplingAlgebra V) where
  escape _ _ _ := 0
  escape_tendsto _ _ _ := tendsto_const_nhds
  norm_sub_le _ _ _ _ _ _ _ _ := by simp

/-- **Theorem 9 at `r = 0`, with no hypothesis.** The infinite-genome semigroup of
`InfiniteGenomeLimit` exists for the pure-resampling models and is the resampling semigroup. -/
theorem infiniteGenomeSemigroup_resampling (t : ℝ≥0) (g : C(ProbabilityMeasure (V → Bool), ℝ)) :
    (infiniteGenomeSemigroup (fun _ ↦ resamplingFellerSemigroup V)
        (resamplingApproximation V)).operator t g
      = (resamplingFellerSemigroup V).operator t g :=
  tendsto_nhds_unique
    (tendsto_infiniteGenomeSemigroup _ (resamplingApproximation V) t g) tendsto_const_nhds

/-- The infinite-genome operators at `r = 0` are the resampling operators. -/
theorem infiniteGenomeSemigroup_operator_resampling :
    (infiniteGenomeSemigroup (fun _ ↦ resamplingFellerSemigroup V)
        (resamplingApproximation V)).operator = (resamplingFellerSemigroup V).operator :=
  funext fun t ↦ ContinuousLinearMap.ext fun g ↦ infiniteGenomeSemigroup_resampling t g

end Genome

end

end Descent.Portability.ResamplingInfiniteGenome
