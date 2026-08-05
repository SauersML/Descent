/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Foundations.Probability
import Mathlib.Tactic
import Descent.Core.Ratios

namespace Descent

open scoped BigOperators

/-!
# Functional descent across populations

A functional of a conditional biological law need not be a function of the retained covariate.
This module formalizes the set-level core of that question.  `DescendsOn supported section b`
allows any observability relation: positive probability, nonzero mass, assay detectability, or
study eligibility.  A `section` gives the conditional law realized by population `P` above
retained context `x`; `supported P x` says whether that version is observable.  The familiar
`FunctionalDescends mass section b` is exactly the positive-mass specialization.

The support condition is essential.  Conditional laws are only canonical where the corresponding
marginal has positive mass, so comparisons are made only on overlap.  Without a measurability
requirement, pairwise compatibility plus inhabitation of the total witness-function space is
necessary and sufficient.  On finite measurable spaces this is the exact dominated analogue; it
is not a claim that undominated standard-Borel gluing is automatic.

For polygenic-score portability, `x` can be an ancestry summary or score bin, `P` a cohort,
`section P x` the conditional genotype/phenotype law, and `b` risk, calibration, variance, or a
clinical utility functional.  The interaction and confounding witnesses below show why descent is
not monotone under adding or removing covariates.
-/

section Descent

variable {Population Context Conditional Value : Type*}

/-- A functional descends on an arbitrary observability relation when one total context function
agrees with it at every supported population/context pair.  Nothing here requires that support
come from a real-valued mass; positive probability, nonzero finite mass, censoring eligibility,
and assay detectability are all instances of the same calculus. -/
def DescendsOn (supported : Population → Context → Prop)
    (conditionalSection : Population → Context → Conditional) (b : Conditional → Value) : Prop :=
  ∃ witness : Context → Value, ∀ P x, supported P x → b (conditionalSection P x) = witness x

/-- The local compatibility condition for an arbitrary observability relation. -/
def PairwiseCompatibleOn (supported : Population → Context → Prop)
    (conditionalSection : Population → Context → Conditional) (b : Conditional → Value) : Prop :=
  ∀ P Q x, supported P x → supported Q x →
    b (conditionalSection P x) = b (conditionalSection Q x)

/-- Descent always implies pairwise compatibility wherever both populations are observable. -/
theorem pairwiseCompatibleOn_of_descendsOn (supported : Population → Context → Prop)
    (conditionalSection : Population → Context → Conditional) (b : Conditional → Value)
    (h : DescendsOn supported conditionalSection b) :
    PairwiseCompatibleOn supported conditionalSection b := by
  obtain ⟨witness, hw⟩ := h
  intro P Q x hP hQ
  rw [hw P x hP, hw Q x hQ]

/-- **Set-level gluing theorem.**  With no measurability requirement, pairwise compatibility
constructs a witness by choosing any observable population at each context.

The proof does not store a theorem inside model data and does not choose a conditional off its
support: the arbitrary default is used only at contexts unsupported by every population. -/
theorem descendsOn_of_pairwiseCompatibleOn
    (supported : Population → Context → Prop)
    (conditionalSection : Population → Context → Conditional) (b : Conditional → Value)
    (defaultWitness : Context → Value)
    (h : PairwiseCompatibleOn supported conditionalSection b) :
    DescendsOn supported conditionalSection b := by
  classical
  let witness : Context → Value := fun x ↦
    if hx : ∃ P, supported P x then b (conditionalSection (Classical.choose hx) x)
    else defaultWitness x
  refine ⟨witness, ?_⟩
  intro P x hP
  have hx : ∃ Q, supported Q x := ⟨P, hP⟩
  rw [show witness x = b (conditionalSection (Classical.choose hx) x) by simp [witness, hx]]
  exact h P (Classical.choose hx) x hP (Classical.choose_spec hx)

/-- **Exact gluing characterization.**  Pairwise compatibility is the only local condition.
The witness-space conjunct is the exact global existence condition, including empty types. -/
theorem descendsOn_iff_pairwiseCompatibleOn
    (supported : Population → Context → Prop)
    (conditionalSection : Population → Context → Conditional) (b : Conditional → Value) :
    DescendsOn supported conditionalSection b ↔
      PairwiseCompatibleOn supported conditionalSection b ∧ Nonempty (Context → Value) := by
  constructor
  · intro h
    exact ⟨pairwiseCompatibleOn_of_descendsOn supported conditionalSection b h, ⟨h.choose⟩⟩
  · rintro ⟨h, ⟨defaultWitness⟩⟩
    exact descendsOn_of_pairwiseCompatibleOn supported conditionalSection b defaultWitness h

/-- With an inhabited codomain, descent on any support relation is exactly pairwise
compatibility. -/
theorem descendsOn_iff_pairwiseCompatibleOn_of_nonempty [Nonempty Value]
    (supported : Population → Context → Prop)
    (conditionalSection : Population → Context → Conditional) (b : Conditional → Value) :
    DescendsOn supported conditionalSection b ↔
      PairwiseCompatibleOn supported conditionalSection b := by
  constructor
  · exact pairwiseCompatibleOn_of_descendsOn supported conditionalSection b
  · intro h
    exact (descendsOn_iff_pairwiseCompatibleOn supported conditionalSection b).mpr
      ⟨h, ⟨fun _ ↦ Classical.choice (inferInstance : Nonempty Value)⟩⟩

/-- Positive marginal mass is the standard probabilistic support relation. -/
abbrev FunctionalDescends (mass : Population → Context → ℝ)
    (conditionalSection : Population → Context → Conditional) (b : Conditional → Value) : Prop :=
  DescendsOn (fun P x ↦ 0 < mass P x) conditionalSection b

/-- Pairwise compatibility on the overlap of positive-mass contexts. -/
abbrev OverlapConsistent (mass : Population → Context → ℝ)
    (conditionalSection : Population → Context → Conditional) (b : Conditional → Value) : Prop :=
  PairwiseCompatibleOn (fun P x ↦ 0 < mass P x) conditionalSection b

/-- **Exact positive-mass characterization.**  Pairwise consistency is the only compatibility
condition.  The additional conjunct is not biological: it is the logically necessary ability to
define a total witness on contexts unsupported by every population.  Stating it as
`Nonempty (Context → Value)` is sharp, including the edge case where `Context` is empty and
`Value` is not inhabited. -/
theorem functionalDescends_iff_overlapConsistent
    (mass : Population → Context → ℝ)
    (conditionalSection : Population → Context → Conditional) (b : Conditional → Value) :
    FunctionalDescends mass conditionalSection b ↔
      OverlapConsistent mass conditionalSection b ∧ Nonempty (Context → Value) :=
  descendsOn_iff_pairwiseCompatibleOn _ conditionalSection b

/-- In the ordinary case of an inhabited value space, the witness-space obstruction is
automatic and descent is exactly pairwise overlap consistency. -/
theorem functionalDescends_iff_overlapConsistent_of_nonempty [Nonempty Value]
    (mass : Population → Context → ℝ)
    (conditionalSection : Population → Context → Conditional) (b : Conditional → Value) :
    FunctionalDescends mass conditionalSection b ↔
      OverlapConsistent mass conditionalSection b := by
  exact descendsOn_iff_pairwiseCompatibleOn_of_nonempty _ conditionalSection b

/-- **Kernel sufficiency is the all-functionals pole.**  If every population uses one shared
conditional section on its support, every functional descends, with no regularity assumption on
the functional. -/
theorem descends_of_sharedSection (mass : Population → Context → ℝ)
    (conditionalSection : Population → Context → Conditional)
    (shared : Context → Conditional)
    (hshared : ∀ P x, 0 < mass P x → conditionalSection P x = shared x)
    (b : Conditional → Value) : FunctionalDescends mass conditionalSection b := by
  refine ⟨fun x ↦ b (shared x), ?_⟩
  intro P x hP
  rw [hshared P x hP]

/-! ### Quantitative descent on a finite population family -/

/-- The diameter of the observable conditional section over `x`.  Unsupported population pairs
contribute zero, so the definition is total; nonnegativity of `rho` makes this convention neutral.
The `Nonempty Population` assumption is exact for using a finite maximum rather than a supremum. -/
noncomputable def finiteSectionDiameter [Fintype Population] [Nonempty Population]
    (supported : Population → Context → Prop)
    (conditionalSection : Population → Context → Conditional)
    (rho : Conditional → Conditional → ℝ) (x : Context) : ℝ := by
  classical
  exact (Finset.univ : Finset Population).sup'
    ⟨Classical.choice (inferInstance : Nonempty Population), Finset.mem_univ _⟩ fun P ↦
      (Finset.univ : Finset Population).sup'
        ⟨Classical.choice (inferInstance : Nonempty Population), Finset.mem_univ _⟩ fun Q ↦
          if supported P x ∧ supported Q x then
            rho (conditionalSection P x) (conditionalSection Q x)
          else 0

/-- The largest observable disagreement in the value of `b` over the section above `x`. -/
noncomputable def finiteSectionOscillation [Fintype Population] [Nonempty Population]
    (supported : Population → Context → Prop)
    (conditionalSection : Population → Context → Conditional)
    (b : Conditional → Value) (d : Value → Value → ℝ) (x : Context) : ℝ := by
  classical
  exact (Finset.univ : Finset Population).sup'
    ⟨Classical.choice (inferInstance : Nonempty Population), Finset.mem_univ _⟩ fun P ↦
      (Finset.univ : Finset Population).sup'
        ⟨Classical.choice (inferInstance : Nonempty Population), Finset.mem_univ _⟩ fun Q ↦
          if supported P x ∧ supported Q x then
            d (b (conditionalSection P x)) (b (conditionalSection Q x))
          else 0

/-- Every observable pairwise distance is bounded by the finite section diameter. -/
theorem sectionPairDistance_le_finiteSectionDiameter [Fintype Population] [Nonempty Population]
    (supported : Population → Context → Prop)
    (conditionalSection : Population → Context → Conditional)
    (rho : Conditional → Conditional → ℝ) (x : Context) (P Q : Population)
    (hP : supported P x) (hQ : supported Q x) :
    rho (conditionalSection P x) (conditionalSection Q x) ≤
      finiteSectionDiameter supported conditionalSection rho x := by
  unfold finiteSectionDiameter
  refine Finset.le_sup'_of_le _ (Finset.mem_univ P) ?_
  refine Finset.le_sup'_of_le _ (Finset.mem_univ Q) ?_
  simp [hP, hQ]

/-- Every observable pairwise disagreement contributes to the finite section oscillation. -/
theorem sectionPairValueDistance_le_finiteSectionOscillation
    [Fintype Population] [Nonempty Population]
    (supported : Population → Context → Prop)
    (conditionalSection : Population → Context → Conditional)
    (b : Conditional → Value) (d : Value → Value → ℝ) (x : Context) (P Q : Population)
    (hP : supported P x) (hQ : supported Q x) :
    d (b (conditionalSection P x)) (b (conditionalSection Q x)) ≤
      finiteSectionOscillation supported conditionalSection b d x := by
  unfold finiteSectionOscillation
  refine Finset.le_sup'_of_le _ (Finset.mem_univ P) ?_
  refine Finset.le_sup'_of_le _ (Finset.mem_univ Q) ?_
  simp [hP, hQ]

/-- A nonnegative conditional distance gives a nonnegative section diameter. -/
theorem finiteSectionDiameter_nonneg [Fintype Population] [Nonempty Population]
    (supported : Population → Context → Prop)
    (conditionalSection : Population → Context → Conditional)
    (rho : Conditional → Conditional → ℝ) (x : Context)
    (hrho : ∀ μ ν, 0 ≤ rho μ ν) :
    0 ≤ finiteSectionDiameter supported conditionalSection rho x := by
  let P : Population := Classical.choice (inferInstance : Nonempty Population)
  unfold finiteSectionDiameter
  refine le_trans ?_ (Finset.le_sup'_of_le _ (Finset.mem_univ P)
    (Finset.le_sup'_of_le _ (Finset.mem_univ P) (le_refl _)))
  by_cases hP : supported P x
  · simp [hP, hrho]
  · simp [hP]

/-- A uniform pairwise bound controls the finite section diameter.  The separate bound at zero
is necessary because unsupported pairs contribute zero by definition. -/
theorem finiteSectionDiameter_le_of_pairwise [Fintype Population] [Nonempty Population]
    (supported : Population → Context → Prop)
    (conditionalSection : Population → Context → Conditional)
    (rho : Conditional → Conditional → ℝ) (x : Context) (C : ℝ)
    (hC : 0 ≤ C)
    (hpair : ∀ P Q, supported P x → supported Q x →
      rho (conditionalSection P x) (conditionalSection Q x) ≤ C) :
    finiteSectionDiameter supported conditionalSection rho x ≤ C := by
  unfold finiteSectionDiameter
  refine Finset.sup'_le _ _ fun P _ ↦ ?_
  refine Finset.sup'_le _ _ fun Q _ ↦ ?_
  by_cases hsupported : supported P x ∧ supported Q x
  · rw [if_pos hsupported]
    exact hpair P Q hsupported.1 hsupported.2
  · rw [if_neg hsupported]
    exact hC

/-- **Uniform quantitative descent.**  A monotone modulus bounds the entire observable
oscillation by its value at the section diameter.  Unlike the former pointwise wrapper, this
theorem performs the finite maximization and derives a population-uniform statement. -/
theorem finiteSectionOscillation_le_modulus_diameter
    [Fintype Population] [Nonempty Population]
    (supported : Population → Context → Prop)
    (conditionalSection : Population → Context → Conditional)
    (b : Conditional → Value) (rho : Conditional → Conditional → ℝ)
    (d : Value → Value → ℝ) (omega : ℝ → ℝ) (x : Context)
    (hrho : ∀ μ ν, 0 ≤ rho μ ν) (homega : Monotone omega)
    (homega0 : 0 ≤ omega 0)
    (hmod : ∀ P Q, supported P x → supported Q x →
      d (b (conditionalSection P x)) (b (conditionalSection Q x)) ≤
        omega (rho (conditionalSection P x) (conditionalSection Q x))) :
    finiteSectionOscillation supported conditionalSection b d x ≤
      omega (finiteSectionDiameter supported conditionalSection rho x) := by
  unfold finiteSectionOscillation
  refine Finset.sup'_le _ _ fun P _ ↦ ?_
  refine Finset.sup'_le _ _ fun Q _ ↦ ?_
  by_cases hsupported : supported P x ∧ supported Q x
  · rw [if_pos hsupported]
    exact (hmod P Q hsupported.1 hsupported.2).trans (homega
      (sectionPairDistance_le_finiteSectionDiameter supported conditionalSection rho x P Q
        hsupported.1 hsupported.2))
  · rw [if_neg hsupported]
    exact homega0.trans (homega
      (finiteSectionDiameter_nonneg supported conditionalSection rho x hrho))

end Descent

/-! ## Affine functionals: the obstruction is an exact directional width -/

section Affine

variable {Fiber : Type*} [Fintype Fiber]

/-- Evaluation of a fiber statistic against a finite conditional mass function. -/
noncomputable def conditionalSectionMean (f : Fiber → ℝ) (mu : Fiber → ℝ) : ℝ :=
  ∑ y, mu y * f y

/-- For an affine functional there is no modulus loss: the difference of conditional values is
exactly the signed width of the two sections in direction `f`. -/
theorem conditionalSectionMean_sub_eq_width (f μ ν : Fiber → ℝ) :
    conditionalSectionMean f μ - conditionalSectionMean f ν =
      ∑ y, (μ y - ν y) * f y := by
  unfold conditionalSectionMean
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro y _
  ring

end Affine

/-! ## Effect modification: each margin descends, their join does not -/

abbrev BinaryDescentCovariate := Fin 2

/-- A binary interaction with no main effects.  `theta` is an ancestry-by-environment or
genotype-by-environment interaction invisible after averaging either coordinate separately. -/
noncomputable def interactionRisk (theta : ℝ)
    (u v : BinaryDescentCovariate) : ℝ :=
  if u = v then 1 / 2 + theta else 1 / 2 - theta

/-- Averaging over the second balanced covariate kills the interaction exactly. -/
theorem interactionRisk_average_second (theta : ℝ) (u : BinaryDescentCovariate) :
    (interactionRisk theta u 0 + interactionRisk theta u 1) / 2 = 1 / 2 := by
  fin_cases u <;> norm_num [interactionRisk]

/-- Averaging over the first balanced covariate also kills it. -/
theorem interactionRisk_average_first (theta : ℝ) (v : BinaryDescentCovariate) :
    (interactionRisk theta 0 v + interactionRisk theta 1 v) / 2 = 1 / 2 := by
  fin_cases v <;> norm_num [interactionRisk]

/-- The joint covariate exposes the population parameter.  Thus descent can hold along each
margin and fail along their join: effect modification is an order-theoretic obstruction, not
sampling noise. -/
theorem interactionRisk_joint_separates {theta eta : ℝ} (hne : theta ≠ eta) :
    interactionRisk theta 0 0 ≠ interactionRisk eta 0 0 := by
  intro heq
  simp only [interactionRisk, ↓reduceIte] at heq
  apply hne
  linarith

/-! ## Confounding: two informative reductions descend, their meet does not -/

/-- Outcome risk conditional on a binary confounder. -/
noncomputable def confoundedConditionalRisk (v : BinaryDescentCovariate) : ℝ :=
  if v = 0 then 1 / 4 else 3 / 4

/-- Reference evaluations: the two covariate strata carry a quarter and three quarters. -/
theorem confoundedConditionalRisk_at_reference_point :
    confoundedConditionalRisk 0 = 1 / 4 ∧ confoundedConditionalRisk 1 = 3 / 4 := by
  constructor <;> simp [confoundedConditionalRisk]


/-- Marginal risk when the confounder prevalence is `beta`. -/
noncomputable def confoundedMarginalRisk (beta : ℝ) : ℝ :=
  (1 - beta) * (1 / 4) + beta * (3 / 4)

theorem confoundedMarginalRisk_eq (beta : ℝ) :
    confoundedMarginalRisk beta = 1 / 4 + beta / 2 := by
  unfold confoundedMarginalRisk
  ring

/-- Removing the confounder loses descent: different cohort prevalences produce different
marginal risks even though the conditional risk function itself is cohort-independent. -/
theorem confoundedMarginalRisk_separates {beta gamma : ℝ} (hne : beta ≠ gamma) :
    confoundedMarginalRisk beta ≠ confoundedMarginalRisk gamma := by
  intro heq
  rw [confoundedMarginalRisk_eq, confoundedMarginalRisk_eq] at heq
  apply hne
  linarith

/-! ## Mixture posterior coordinates are a sufficiency pole -/

section ComponentMap

variable {Component Genome : Type*} [Fintype Component]

/-- Density of a component mixture at genome `g`. -/
noncomputable def componentMixtureDensity (q : Component → Genome → ℝ)
    (w : Component → ℝ) (g : Genome) : ℝ :=
  ∑ k, w k * q k g

/-- Posterior component weight under an interior reference mixture. -/
noncomputable def componentPosterior (q : Component → Genome → ℝ)
    (w0 : Component → ℝ) (g : Genome) (k : Component) : ℝ :=
  w0 k * q k g / componentMixtureDensity q w0 g

/-- With a vanishing denominator Mathlib returns `0`, which is a value this quantity can also
take legitimately, so the branch is named rather than left to be inferred from the result. -/
theorem componentPosterior_at_zero_denominator_is_junk
    (q : Component → Genome → ℝ) (w0 : Component → ℝ) (g : Genome) (k : Component)
    (hzero : componentMixtureDensity q w0 g = 0) :
    componentPosterior q w0 g k = 0 := by
  unfold componentPosterior
  rw [hzero, div_zero]


/-- The likelihood-ratio tilt expressed only through the posterior component coordinate. -/
noncomputable def posteriorTilt (q : Component → Genome → ℝ)
    (w0 w : Component → ℝ) (g : Genome) : ℝ :=
  ∑ k, componentPosterior q w0 g k * (w k / w0 k)

/-- Reference evaluation: a tilt toward the zero weighting is zero, whatever the posterior. -/
theorem posteriorTilt_at_zero_target (q : Component → Genome → ℝ) (w0 : Component → ℝ)
    (g : Genome) :
    posteriorTilt q w0 0 g = 0 := by
  unfold posteriorTilt
  simp


/-- A component with zero base weight contributes a junk ratio `w k / 0 = 0`, so the tilt drops
that component silently rather than reporting an undefined reweighting. -/
theorem posteriorTilt_at_zero_base_weight_is_junk
    (q : Component → Genome → ℝ) (w0 w : Component → ℝ) (g : Genome) (k : Component)
    (hzero : w0 k = 0) :
    componentPosterior q w0 g k * (w k / w0 k) = 0 := by
  rw [hzero, div_zero, mul_zero]


/-- **Component-map factorization.**  Every mixture density is the reference density times a
function of the posterior component vector.  This is the exact algebra behind sufficiency of
ancestry-posterior coordinates; it is not an imported factorization theorem. -/
theorem componentMixtureDensity_factorization
    (q : Component → Genome → ℝ) (w0 w : Component → ℝ) (g : Genome)
    (hw0 : ∀ k, w0 k ≠ 0) (hZ : componentMixtureDensity q w0 g ≠ 0) :
    componentMixtureDensity q w g =
      componentMixtureDensity q w0 g * posteriorTilt q w0 w g := by
  unfold posteriorTilt componentPosterior
  change (∑ k, w k * q k g) = _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  field_simp [hw0 k, hZ]

/-- The Radon--Nikodym ratio against the reference mixture is posterior-measurable. -/
theorem componentDensityRatio_eq_posteriorTilt
    (q : Component → Genome → ℝ) (w0 w : Component → ℝ) (g : Genome)
    (hw0 : ∀ k, w0 k ≠ 0) (hZ : componentMixtureDensity q w0 g ≠ 0) :
    componentMixtureDensity q w g / componentMixtureDensity q w0 g =
      posteriorTilt q w0 w g := by
  rw [componentMixtureDensity_factorization q w0 w g hw0 hZ]
  field_simp

end ComponentMap

/-! ## Localization and nonlinearity are different residuals -/

section Residual

variable {Component : Type*} [Fintype Component]

/-- Failure of the component-affine ansatz at posterior coordinate `a`. -/
noncomputable def componentRepresentationResidual (localValue : ℝ)
    (a componentValue : Component → ℝ) : ℝ :=
  localValue - ∑ k, a k * componentValue k

/-- Change caused by localizing a mixture to one posterior fiber. -/
noncomputable def localizationResidual (localValue mixtureValue : ℝ) : ℝ :=
  Descent.Core.difference localValue mixtureValue

/-- Reference evaluation; see `Descent.Core.Ratios` for what these pin and why. -/
theorem localizationResidual_at_reference_point :
    localizationResidual 2 1 = 1 := by
  norm_num [localizationResidual,
      Descent.Core.difference]


/-- Failure of a functional to commute with component mixing. -/
noncomputable def jensenResidual (mixtureValue : ℝ)
    (a componentValue : Component → ℝ) : ℝ :=
  mixtureValue - ∑ k, a k * componentValue k

/-- Reference evaluation: with no component weight the residual is the mixture value itself. -/
theorem jensenResidual_at_zero_weights (componentValue : Component → ℝ) :
    jensenResidual 5 (fun _ ↦ 0) componentValue = 5 := by
  unfold jensenResidual
  simp


/-- Reference evaluation: with a two-component average the residual is the stated gap. -/
theorem jensenResidual_at_reference_point (a componentValue : Component → ℝ)
    (hzero : ∑ k, a k * componentValue k = 0) (mixtureValue : ℝ) :
    jensenResidual mixtureValue a componentValue = mixtureValue := by
  unfold jensenResidual
  rw [hzero, sub_zero]


/-- **Exact two-residual law.**  Posterior-component representation error is the sum of a
localization error and a Jensen/nonlinearity error.  An affine functional can still have a large
localization residual; disjoint components can make both residuals vanish even for nonlinear
functionals. -/
theorem componentRepresentationResidual_decomposition (localValue mixtureValue : ℝ)
    (a componentValue : Component → ℝ) :
    componentRepresentationResidual localValue a componentValue =
      localizationResidual localValue mixtureValue +
        jensenResidual mixtureValue a componentValue := by
  unfold componentRepresentationResidual localizationResidual jensenResidual Descent.Core.difference
  ring

end Residual

end Descent
