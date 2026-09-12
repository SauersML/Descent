/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.AncestralLocality.CylinderSamplingPolynomials
import Mathlib.Analysis.Normed.Operator.Completeness

assert_below Descent.PopGen Descent.Spectral Descent.Blindness Descent.Conditionals
assert_below Descent.Portability Descent.Decision Descent.Program

/-!
# Window projections of genome laws

Theorem 9 of the ancestral-locality note builds its infinite-genome semigroup on `C(P(H))` for
`H = {0,1}^V` from operators that each read finitely many features. This module supplies the
cylinder side of that construction: the laws a genome law puts on finite windows, the sampling
polynomials that read a window, and the gluing of a consistent family of window operators into
one contraction on the cylinder sampling algebra and on its closure.

Window pushforwards. For a finite window `W ⊆ V`, `windowLaw W` pushes a genome law forward along
the restriction of a genome to `W`, and `shrinkLaw h` pushes a law of the letters on `W'` forward
to a smaller window `W ⊆ W'`. Both are continuous (`continuous_windowLaw`,
`continuous_shrinkLaw`), and they compose (`shrinkLaw_windowLaw`). Every law of the letters on a
window is a window law, of the genome law that fills the other features with `false`
(`windowLaw_surjective`).

Pullbacks. `windowPullback W` and `shrinkPullback h` precompose continuous functions with the
pushforwards. They are algebra homomorphisms that compose (`windowPullback_shrinkPullback`), and
`windowPullback W` preserves the sup norm and is injective because `windowLaw W` is onto
(`norm_windowPullback`, `windowPullback_injective`). On the laws of a window the linear sampling
observable of a readout is its integral (`windowMonomial`), and `windowAlgebra W` is the algebra
they generate. A cylinder sampling monomial reading `W` is the pullback of the window monomial
(`windowPullback_windowMonomial`), and a sampling polynomial of `n` genomes reading `W` is the
pullback of the window sampling polynomial (`windowPullback_windowPolynomial`). Every member of
the cylinder sampling algebra reads a finite window: it is the pullback of a member of that
window's algebra (`exists_windowPullback`).

Gluing. A `WindowOperatorFamily` carries on the laws of each finite window a linear operator on
continuous functions, contracting and consistent with `shrinkPullback` on window polynomials.
Two representations of one cylinder polynomial through two windows give the same glued value
(`windowPullback_operator_agree`), so the family defines one linear operator on the cylinder
sampling algebra (`gluedOperator`, `gluedOperator_windowPullback`), and it contracts
(`norm_gluedOperator_le`). By the density of the algebra it extends to a continuous linear
contraction of `C(P(H))` (`extendedOperator`, `extendedOperator_apply`,
`norm_extendedOperator_le`). The identity family is a witness (`identityWindowOperators`).

## Empirical status

None. The bodies here are measure theory, topology and linear algebra: pushforwards along
restrictions, precomposition, and the extension of a uniformly continuous linear map, so no
measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Pangenome.AncestralLocality.CylinderWindowProjection

open MeasureTheory Topology CylinderSamplingAlgebra CylinderSamplingPolynomials

noncomputable section

variable {V : Type*} [Countable V] [DecidableEq V]

/-! ## Window pushforwards -/

omit [Countable V] [DecidableEq V] in
/-- Reading a genome through a finite window is continuous. -/
theorem continuous_windowRestrict (W : Finset V) :
    Continuous fun genome : V → Bool ↦ W.restrict genome :=
  continuous_pi fun v ↦ continuous_apply (v : V)

omit [Countable V] [DecidableEq V] in
/-- Restricting the letters of a window to a smaller window. -/
def shrinkWindow {W W' : Finset V} (h : W ⊆ W') (letters : W' → Bool) : W → Bool :=
  fun v ↦ letters ⟨v.1, h v.2⟩

omit [Countable V] [DecidableEq V] in
/-- Restricting the letters of a window to a smaller window is continuous. -/
theorem continuous_shrinkWindow {W W' : Finset V} (h : W ⊆ W') :
    Continuous (shrinkWindow h) :=
  continuous_of_discreteTopology

omit [Countable V] [DecidableEq V] in
/-- Restricting to a window and then to a smaller window is restricting to the smaller window. -/
theorem shrinkWindow_comp_restrict {W W' : Finset V} (h : W ⊆ W') :
    shrinkWindow h ∘ (fun genome : V → Bool ↦ W'.restrict genome) =
      fun genome ↦ W.restrict genome :=
  rfl

omit [DecidableEq V] in
/-- The law of the letters a genome law puts on a finite window. -/
def windowLaw (W : Finset V) (μ : ProbabilityMeasure (V → Bool)) :
    ProbabilityMeasure (W → Bool) :=
  μ.map (continuous_windowRestrict W).measurable.aemeasurable

omit [Countable V] [DecidableEq V] in
/-- The law of the letters on a smaller window, from a law of the letters on a larger one. -/
def shrinkLaw {W W' : Finset V} (h : W ⊆ W') (ν : ProbabilityMeasure (W' → Bool)) :
    ProbabilityMeasure (W → Bool) :=
  ν.map (continuous_shrinkWindow h).measurable.aemeasurable

omit [DecidableEq V] in
/-- The window pushforward of genome laws is continuous. -/
theorem continuous_windowLaw (W : Finset V) : Continuous (windowLaw (V := V) W) :=
  ProbabilityMeasure.continuous_map (continuous_windowRestrict W)

omit [Countable V] [DecidableEq V] in
/-- The pushforward between two windows is continuous. -/
theorem continuous_shrinkLaw {W W' : Finset V} (h : W ⊆ W') : Continuous (shrinkLaw h) :=
  ProbabilityMeasure.continuous_map (continuous_shrinkWindow h)

omit [DecidableEq V] in
/-- **The window pushforwards compose.** Pushing a genome law to a window and then to a smaller
window is pushing it to the smaller window. -/
theorem shrinkLaw_windowLaw {W W' : Finset V} (h : W ⊆ W') (μ : ProbabilityMeasure (V → Bool)) :
    shrinkLaw h (windowLaw W' μ) = windowLaw W μ := by
  apply ProbabilityMeasure.toMeasure_injective
  simp only [windowLaw, shrinkLaw, ProbabilityMeasure.toMeasure_map]
  rw [Measure.map_map (continuous_shrinkWindow h).measurable
    (continuous_windowRestrict W').measurable, shrinkWindow_comp_restrict]

omit [Countable V] in
/-- The genome that spells given letters on a window and `false` off it. -/
def extendWindow (W : Finset V) (letters : W → Bool) : V → Bool :=
  fun v ↦ if hv : v ∈ W then letters ⟨v, hv⟩ else false

omit [Countable V] in
/-- Extending the letters of a window to a genome is continuous. -/
theorem continuous_extendWindow (W : Finset V) : Continuous (extendWindow W) :=
  continuous_of_discreteTopology

omit [Countable V] in
/-- The extended genome spells the letters it extends. -/
theorem restrict_extendWindow (W : Finset V) (letters : W → Bool) :
    W.restrict (extendWindow W letters) = letters := by
  funext v
  simp [Finset.restrict, extendWindow, v.2]

/-- **Every law of the letters on a window is a window law.** -/
theorem windowLaw_surjective (W : Finset V) : Function.Surjective (windowLaw (V := V) W) := by
  intro ν
  refine ⟨ν.map (continuous_extendWindow W).measurable.aemeasurable, ?_⟩
  apply ProbabilityMeasure.toMeasure_injective
  simp only [windowLaw, ProbabilityMeasure.toMeasure_map]
  have hidentity : (fun genome : V → Bool ↦ W.restrict genome) ∘ extendWindow W = id :=
    funext (restrict_extendWindow W)
  rw [Measure.map_map (continuous_windowRestrict W).measurable
    (continuous_extendWindow W).measurable, hidentity, Measure.map_id]

/-! ## Pullbacks of continuous functions -/

omit [DecidableEq V] in
/-- Pulling a continuous function of window laws back to genome laws. -/
def windowPullback (W : Finset V) :
    C(ProbabilityMeasure (W → Bool), ℝ) →ₐ[ℝ] C(ProbabilityMeasure (V → Bool), ℝ) :=
  ContinuousMap.compRightAlgHom ℝ ℝ ⟨windowLaw W, continuous_windowLaw W⟩

omit [Countable V] [DecidableEq V] in
/-- Pulling a continuous function of the laws on a window back to the laws on a larger one. -/
def shrinkPullback {W W' : Finset V} (h : W ⊆ W') :
    C(ProbabilityMeasure (W → Bool), ℝ) →ₐ[ℝ] C(ProbabilityMeasure (W' → Bool), ℝ) :=
  ContinuousMap.compRightAlgHom ℝ ℝ ⟨shrinkLaw h, continuous_shrinkLaw h⟩

omit [DecidableEq V] in
/-- The pullback evaluates the function at the window law. -/
theorem windowPullback_apply (W : Finset V) (g : C(ProbabilityMeasure (W → Bool), ℝ))
    (μ : ProbabilityMeasure (V → Bool)) : windowPullback W g μ = g (windowLaw W μ) :=
  rfl

omit [Countable V] [DecidableEq V] in
/-- The pullback between windows evaluates the function at the smaller window law. -/
theorem shrinkPullback_apply {W W' : Finset V} (h : W ⊆ W')
    (g : C(ProbabilityMeasure (W → Bool), ℝ)) (ν : ProbabilityMeasure (W' → Bool)) :
    shrinkPullback h g ν = g (shrinkLaw h ν) :=
  rfl

omit [DecidableEq V] in
/-- **The pullbacks compose.** -/
theorem windowPullback_shrinkPullback {W W' : Finset V} (h : W ⊆ W')
    (g : C(ProbabilityMeasure (W → Bool), ℝ)) :
    windowPullback W' (shrinkPullback h g) = windowPullback W g := by
  ext μ
  rw [windowPullback_apply, shrinkPullback_apply, shrinkLaw_windowLaw, windowPullback_apply]

/-- The pullback to genome laws preserves the sup norm, because every window law is attained. -/
theorem norm_windowPullback (W : Finset V) (g : C(ProbabilityMeasure (W → Bool), ℝ)) :
    ‖windowPullback W g‖ = ‖g‖ := by
  refine le_antisymm ((ContinuousMap.norm_le (windowPullback W g) (norm_nonneg g)).mpr
    fun μ ↦ ?_) ((ContinuousMap.norm_le g (norm_nonneg _)).mpr fun ν ↦ ?_)
  · rw [windowPullback_apply]
    exact ContinuousMap.norm_coe_le_norm g _
  · obtain ⟨μ, rfl⟩ := windowLaw_surjective W ν
    rw [← windowPullback_apply]
    exact ContinuousMap.norm_coe_le_norm (windowPullback W g) μ

/-- The pullback to genome laws is injective. -/
theorem windowPullback_injective (W : Finset V) :
    Function.Injective (windowPullback (V := V) W) := by
  intro g g' hequal
  ext ν
  obtain ⟨μ, rfl⟩ := windowLaw_surjective W ν
  rw [← windowPullback_apply, ← windowPullback_apply, hequal]

/-! ## Window sampling polynomials -/

omit [Countable V] [DecidableEq V] in
/-- The linear sampling observable of a window readout on the laws of the window: its
integral. -/
def windowMonomial (W : Finset V) (readout : (W → Bool) → ℝ) :
    C(ProbabilityMeasure (W → Bool), ℝ) where
  toFun ν := ∫ letters, readout letters ∂(ν : Measure (W → Bool))
  continuous_toFun := ProbabilityMeasure.continuous_integral_boundedContinuousFunction
    (BoundedContinuousFunction.mkOfCompact ⟨readout, continuous_of_discreteTopology⟩)

omit [Countable V] [DecidableEq V] in
/-- **The sampling algebra of a window**, generated by the linear sampling observables of window
readouts. -/
def windowAlgebra (W : Finset V) : Subalgebra ℝ C(ProbabilityMeasure (W → Bool), ℝ) :=
  Algebra.adjoin ℝ (Set.range (windowMonomial W))

omit [Countable V] [DecidableEq V] in
/-- The window monomials lie in the window algebra. -/
theorem windowMonomial_mem_windowAlgebra (W : Finset V) (readout : (W → Bool) → ℝ) :
    windowMonomial W readout ∈ windowAlgebra W :=
  Algebra.subset_adjoin ⟨readout, rfl⟩

omit [DecidableEq V] in
/-- **A cylinder sampling monomial reading a window is the pullback of the window monomial.** -/
theorem windowPullback_windowMonomial (W : Finset V) (readout : (W → Bool) → ℝ) :
    windowPullback W (windowMonomial W readout) = samplingMonomial W readout := by
  ext μ
  rw [windowPullback_apply]
  show ∫ letters, readout letters ∂(windowLaw W μ : Measure (W → Bool)) =
    ∫ genome, cylinderObservable W readout genome ∂(μ : Measure (V → Bool))
  have hreadout : Continuous readout := continuous_of_discreteTopology
  rw [windowLaw, ProbabilityMeasure.toMeasure_map,
    integral_map (continuous_windowRestrict W).measurable.aemeasurable
      hreadout.aestronglyMeasurable]
  rfl

omit [Countable V] [DecidableEq V] in
/-- The pullback between windows sends a window monomial to the monomial of the restricted
readout. -/
theorem shrinkPullback_windowMonomial {W W' : Finset V} (h : W ⊆ W')
    (readout : (W → Bool) → ℝ) :
    shrinkPullback h (windowMonomial W readout) = windowMonomial W' (readout ∘ shrinkWindow h) := by
  ext ν
  rw [shrinkPullback_apply]
  show ∫ letters, readout letters ∂(shrinkLaw h ν : Measure (W → Bool)) =
    ∫ letters, (readout ∘ shrinkWindow h) letters ∂(ν : Measure (W' → Bool))
  have hreadout : Continuous readout := continuous_of_discreteTopology
  rw [shrinkLaw, ProbabilityMeasure.toMeasure_map,
    integral_map (continuous_shrinkWindow h).measurable.aemeasurable
      hreadout.aestronglyMeasurable]
  rfl

/-- The sampling polynomial of a readout of `n` genomes on the laws of a window. -/
def windowPolynomial (W : Finset V) (n : ℕ) (readout : (Fin n → W → Bool) → ℝ) :
    C(ProbabilityMeasure (W → Bool), ℝ) :=
  ∑ patterns : Fin n → W → Bool,
    readout patterns • ∏ k, windowMonomial W (patternIndicator W (patterns k))

omit [Countable V] in
/-- The window sampling polynomials lie in the window algebra. -/
theorem windowPolynomial_mem_windowAlgebra (W : Finset V) (n : ℕ)
    (readout : (Fin n → W → Bool) → ℝ) : windowPolynomial W n readout ∈ windowAlgebra W :=
  sum_mem fun _ _ ↦ SMulMemClass.smul_mem _
    (prod_mem fun _ _ ↦ windowMonomial_mem_windowAlgebra W _)

/-- **A cylinder sampling polynomial reading a window is the pullback of the window sampling
polynomial.** -/
theorem windowPullback_windowPolynomial (W : Finset V) (n : ℕ)
    (readout : (Fin n → W → Bool) → ℝ) :
    windowPullback W (windowPolynomial W n readout) = samplingPolynomial n W readout := by
  simp only [windowPolynomial, samplingPolynomial, map_sum, map_smul, map_prod,
    windowPullback_windowMonomial]

omit [DecidableEq V] in
/-- Pullbacks of window polynomials are cylinder sampling polynomials. -/
theorem windowPullback_mem_samplingAlgebra {W : Finset V}
    {g : C(ProbabilityMeasure (W → Bool), ℝ)} (hg : g ∈ windowAlgebra W) :
    windowPullback W g ∈ samplingAlgebra V := by
  have hle : windowAlgebra W ≤ (samplingAlgebra V).comap (windowPullback W) := by
    refine Algebra.adjoin_le ?_
    rintro _ ⟨readout, rfl⟩
    rw [SetLike.mem_coe, Subalgebra.mem_comap, windowPullback_windowMonomial]
    exact samplingMonomial_mem_samplingAlgebra W readout
  exact (Subalgebra.mem_comap _ _ _).mp (hle hg)

omit [Countable V] [DecidableEq V] in
/-- The pullback between windows maps window polynomials to window polynomials. -/
theorem shrinkPullback_mem_windowAlgebra {W W' : Finset V} (h : W ⊆ W')
    {g : C(ProbabilityMeasure (W → Bool), ℝ)} (hg : g ∈ windowAlgebra W) :
    shrinkPullback h g ∈ windowAlgebra W' := by
  have hle : windowAlgebra W ≤ (windowAlgebra W').comap (shrinkPullback h) := by
    refine Algebra.adjoin_le ?_
    rintro _ ⟨readout, rfl⟩
    rw [SetLike.mem_coe, Subalgebra.mem_comap, shrinkPullback_windowMonomial]
    exact windowMonomial_mem_windowAlgebra W' _
  exact (Subalgebra.mem_comap _ _ _).mp (hle hg)

omit [DecidableEq V] in
/-- **Every cylinder sampling polynomial reads a finite window**: it is the pullback of a member
of that window's sampling algebra. -/
theorem exists_windowPullback {f : C(ProbabilityMeasure (V → Bool), ℝ)}
    (hf : f ∈ samplingAlgebra V) :
    ∃ W : Finset V, ∃ g ∈ windowAlgebra W, windowPullback W g = f := by
  refine Algebra.adjoin_induction
    (p := fun f _ ↦ ∃ W : Finset V, ∃ g ∈ windowAlgebra W, windowPullback W g = f)
    (fun x hx ↦ ?_) (fun c ↦ ?_) (fun x y _ _ hx hy ↦ ?_) (fun x y _ _ hx hy ↦ ?_) hf
  · obtain ⟨⟨features, readout⟩, rfl⟩ := hx
    exact ⟨features, windowMonomial features readout,
      windowMonomial_mem_windowAlgebra features readout,
      windowPullback_windowMonomial features readout⟩
  · exact ⟨∅, algebraMap ℝ _ c, Subalgebra.algebraMap_mem _ c, AlgHom.commutes _ c⟩
  · obtain ⟨W₁, g₁, hg₁, rfl⟩ := hx
    obtain ⟨W₂, g₂, hg₂, rfl⟩ := hy
    have h₁ : W₁ ⊆ W₁ ∪ W₂ := fun _ hv ↦ Finset.mem_union_left W₂ hv
    have h₂ : W₂ ⊆ W₁ ∪ W₂ := fun _ hv ↦ Finset.mem_union_right W₁ hv
    refine ⟨W₁ ∪ W₂, shrinkPullback h₁ g₁ + shrinkPullback h₂ g₂,
      add_mem (shrinkPullback_mem_windowAlgebra h₁ hg₁) (shrinkPullback_mem_windowAlgebra h₂ hg₂),
      ?_⟩
    rw [map_add, windowPullback_shrinkPullback, windowPullback_shrinkPullback]
  · obtain ⟨W₁, g₁, hg₁, rfl⟩ := hx
    obtain ⟨W₂, g₂, hg₂, rfl⟩ := hy
    have h₁ : W₁ ⊆ W₁ ∪ W₂ := fun _ hv ↦ Finset.mem_union_left W₂ hv
    have h₂ : W₂ ⊆ W₁ ∪ W₂ := fun _ hv ↦ Finset.mem_union_right W₁ hv
    refine ⟨W₁ ∪ W₂, shrinkPullback h₁ g₁ * shrinkPullback h₂ g₂,
      mul_mem (shrinkPullback_mem_windowAlgebra h₁ hg₁) (shrinkPullback_mem_windowAlgebra h₂ hg₂),
      ?_⟩
    rw [map_mul, windowPullback_shrinkPullback, windowPullback_shrinkPullback]

/-! ## Gluing window operators -/

/-- **A family of window operators** for Theorem 9: on the laws of each finite window, a linear
operator on continuous functions that contracts the sup norm and is consistent with the pullback
along window inclusions on window sampling polynomials. -/
structure WindowOperatorFamily (V : Type*) [DecidableEq V] where
  operator : ∀ W : Finset V,
    C(ProbabilityMeasure (W → Bool), ℝ) →ₗ[ℝ] C(ProbabilityMeasure (W → Bool), ℝ)
  contraction : ∀ W g, ‖operator W g‖ ≤ ‖g‖
  consistent : ∀ {W W' : Finset V} (h : W ⊆ W') (g : C(ProbabilityMeasure (W → Bool), ℝ)),
    g ∈ windowAlgebra W → operator W' (shrinkPullback h g) = shrinkPullback h (operator W g)

omit [Countable V] in
/-- The identity family of window operators, a witness. -/
def identityWindowOperators : WindowOperatorFamily V where
  operator _ := LinearMap.id
  contraction _ _ := le_rfl
  consistent _ _ _ := rfl

/-- **Consistency across windows.** Two representations of one cylinder polynomial through two
windows give the same glued value. -/
theorem windowPullback_operator_agree (T : WindowOperatorFamily V) {W₁ W₂ : Finset V}
    {g₁ : C(ProbabilityMeasure (W₁ → Bool), ℝ)} {g₂ : C(ProbabilityMeasure (W₂ → Bool), ℝ)}
    (hg₁ : g₁ ∈ windowAlgebra W₁) (hg₂ : g₂ ∈ windowAlgebra W₂)
    (hequal : windowPullback W₁ g₁ = windowPullback W₂ g₂) :
    windowPullback W₁ (T.operator W₁ g₁) = windowPullback W₂ (T.operator W₂ g₂) := by
  have h₁ : W₁ ⊆ W₁ ∪ W₂ := fun _ hv ↦ Finset.mem_union_left W₂ hv
  have h₂ : W₂ ⊆ W₁ ∪ W₂ := fun _ hv ↦ Finset.mem_union_right W₁ hv
  have hshrink : shrinkPullback h₁ g₁ = shrinkPullback h₂ g₂ :=
    windowPullback_injective (W₁ ∪ W₂) (by
      rw [windowPullback_shrinkPullback, windowPullback_shrinkPullback, hequal])
  rw [← windowPullback_shrinkPullback h₁, ← windowPullback_shrinkPullback h₂,
    ← T.consistent h₁ g₁ hg₁, ← T.consistent h₂ g₂ hg₂, hshrink]

/-- The glued operator on a cylinder sampling polynomial, through a window it reads. -/
def gluedValue (T : WindowOperatorFamily V) (f : C(ProbabilityMeasure (V → Bool), ℝ))
    (hf : f ∈ samplingAlgebra V) : C(ProbabilityMeasure (V → Bool), ℝ) :=
  windowPullback (exists_windowPullback hf).choose
    (T.operator _ (exists_windowPullback hf).choose_spec.choose)

/-- The glued value is computed through any window the polynomial reads. -/
theorem gluedValue_eq (T : WindowOperatorFamily V) {W : Finset V}
    {g : C(ProbabilityMeasure (W → Bool), ℝ)} (hg : g ∈ windowAlgebra W)
    {f : C(ProbabilityMeasure (V → Bool), ℝ)} (hf : f ∈ samplingAlgebra V)
    (hpullback : windowPullback W g = f) :
    gluedValue T f hf = windowPullback W (T.operator W g) := by
  obtain ⟨hchosen, hchosenPullback⟩ := (exists_windowPullback hf).choose_spec.choose_spec
  exact windowPullback_operator_agree T hchosen hg (hchosenPullback.trans hpullback.symm)

/-- **The glued operator** of a window operator family, a linear map on the cylinder sampling
algebra. -/
def gluedOperator (T : WindowOperatorFamily V) :
    (samplingAlgebra V).toSubmodule →ₗ[ℝ] C(ProbabilityMeasure (V → Bool), ℝ) where
  toFun f := gluedValue T f f.2
  map_add' f f' := by
    obtain ⟨W, g, hg, hpullback⟩ := exists_windowPullback f.2
    obtain ⟨W', g', hg', hpullback'⟩ := exists_windowPullback f'.2
    have h₁ : W ⊆ W ∪ W' := fun _ hv ↦ Finset.mem_union_left W' hv
    have h₂ : W' ⊆ W ∪ W' := fun _ hv ↦ Finset.mem_union_right W hv
    have hsum : windowPullback (W ∪ W') (shrinkPullback h₁ g + shrinkPullback h₂ g') =
        ((f + f' : (samplingAlgebra V).toSubmodule) : C(ProbabilityMeasure (V → Bool), ℝ)) := by
      rw [Submodule.coe_add, map_add, windowPullback_shrinkPullback,
        windowPullback_shrinkPullback, hpullback, hpullback']
    rw [gluedValue_eq T (add_mem (shrinkPullback_mem_windowAlgebra h₁ hg)
        (shrinkPullback_mem_windowAlgebra h₂ hg')) _ hsum,
      gluedValue_eq T hg _ hpullback, gluedValue_eq T hg' _ hpullback', map_add,
      T.consistent h₁ g hg, T.consistent h₂ g' hg', map_add, windowPullback_shrinkPullback,
      windowPullback_shrinkPullback]
  map_smul' c f := by
    obtain ⟨W, g, hg, hpullback⟩ := exists_windowPullback f.2
    have hscaled : windowPullback W (c • g) =
        ((c • f : (samplingAlgebra V).toSubmodule) : C(ProbabilityMeasure (V → Bool), ℝ)) := by
      rw [Submodule.coe_smul, map_smul, hpullback]
    rw [RingHom.id_apply, gluedValue_eq T (SMulMemClass.smul_mem c hg) _ hscaled,
      gluedValue_eq T hg _ hpullback, map_smul, map_smul]

/-- The glued operator acts through any window the polynomial reads. -/
theorem gluedOperator_windowPullback (T : WindowOperatorFamily V) {W : Finset V}
    {g : C(ProbabilityMeasure (W → Bool), ℝ)} (hg : g ∈ windowAlgebra W)
    (f : (samplingAlgebra V).toSubmodule) (hpullback : windowPullback W g = f) :
    gluedOperator T f = windowPullback W (T.operator W g) :=
  gluedValue_eq T hg f.2 hpullback

/-- **The glued operator contracts the sup norm.** -/
theorem norm_gluedOperator_le (T : WindowOperatorFamily V) (f : (samplingAlgebra V).toSubmodule) :
    ‖gluedOperator T f‖ ≤ ‖(f : C(ProbabilityMeasure (V → Bool), ℝ))‖ := by
  obtain ⟨W, g, hg, hpullback⟩ := exists_windowPullback f.2
  rw [gluedOperator_windowPullback T hg f hpullback, norm_windowPullback, ← hpullback,
    norm_windowPullback]
  exact T.contraction W g

/-- The glued operator as a continuous linear map on the cylinder sampling algebra. -/
def continuousGluedOperator (T : WindowOperatorFamily V) :
    (samplingAlgebra V).toSubmodule →L[ℝ] C(ProbabilityMeasure (V → Bool), ℝ) :=
  (gluedOperator T).mkContinuous 1 fun f ↦ by
    rw [one_mul]
    exact norm_gluedOperator_le T f

omit [DecidableEq V] in
/-- The cylinder sampling algebra is a dense subspace of `C(P(H))`. -/
theorem denseRange_samplingAlgebra_subtypeL :
    DenseRange (samplingAlgebra V).toSubmodule.subtypeL := by
  have hdense : Dense (samplingAlgebra V : Set C(ProbabilityMeasure (V → Bool), ℝ)) := by
    intro f
    have hmember : f ∈ (samplingAlgebra V).topologicalClosure := by
      rw [samplingAlgebra_topologicalClosure_eq_top]
      exact Algebra.mem_top
    exact hmember
  exact hdense.denseRange_val

omit [DecidableEq V] in
/-- The inclusion of the cylinder sampling algebra keeps the norm. -/
theorem norm_le_subtypeL (f : (samplingAlgebra V).toSubmodule) :
    ‖f‖ ≤ ((1 : NNReal) : ℝ) * ‖(samplingAlgebra V).toSubmodule.subtypeL f‖ := by
  rw [NNReal.coe_one, one_mul]
  exact le_rfl

/-- **The extended operator**: the continuous linear extension of the glued operator from the
cylinder sampling algebra to all continuous functions of genome laws. -/
def extendedOperator (T : WindowOperatorFamily V) :
    C(ProbabilityMeasure (V → Bool), ℝ) →L[ℝ] C(ProbabilityMeasure (V → Bool), ℝ) :=
  (continuousGluedOperator T).extend (samplingAlgebra V).toSubmodule.subtypeL
    denseRange_samplingAlgebra_subtypeL
    (ContinuousLinearMap.isUniformEmbedding_of_bound _ norm_le_subtypeL).isUniformInducing

/-- The extended operator agrees with the glued operator on the cylinder sampling algebra. -/
theorem extendedOperator_apply (T : WindowOperatorFamily V) (f : (samplingAlgebra V).toSubmodule) :
    extendedOperator T f = gluedOperator T f :=
  ContinuousLinearMap.extend_eq _ _ _ _ f

/-- **The extended operator is a contraction of `C(P(H))`.** -/
theorem norm_extendedOperator_le (T : WindowOperatorFamily V) : ‖extendedOperator T‖ ≤ 1 := by
  have hextend := ContinuousLinearMap.opNorm_extend_le (f := continuousGluedOperator T)
    (e := (samplingAlgebra V).toSubmodule.subtypeL)
    (h_dense := denseRange_samplingAlgebra_subtypeL) (h_e := norm_le_subtypeL)
  rw [NNReal.coe_one, one_mul] at hextend
  exact hextend.trans (LinearMap.mkContinuous_norm_le _ zero_le_one _)

end

end Descent.Pangenome.AncestralLocality.CylinderWindowProjection
