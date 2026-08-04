/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Calibrator.Probability
import Mathlib.Tactic

namespace Calibrator

open scoped BigOperators

/-!
# Functional descent across populations

A functional of a conditional biological law need not be a function of the retained covariate.
This module formalizes the finite, exact core of that question.  A `section` gives the conditional
law realized by population `P` above retained context `x`; `mass P x` says whether that version is
observable.  `FunctionalDescends mass section b` means that one population-independent function of
`x` evaluates `b` on every realized section.

The support condition is essential.  Conditional laws are only canonical where the corresponding
marginal has positive mass, so comparisons are made only on overlap.  On finite spaces all
functions are measurable and the global uniformization obstruction disappears; consequently
pairwise overlap consistency is both necessary and sufficient.  This is the exact finite analogue
of the dominated theorem, not a claim that undominated standard-Borel gluing is automatic.

For polygenic-score portability, `x` can be an ancestry summary or score bin, `P` a cohort,
`section P x` the conditional genotype/phenotype law, and `b` risk, calibration, variance, or a
clinical utility functional.  The interaction and confounding witnesses below show why descent is
not monotone under adding or removing covariates.
-/

section Descent

variable {Population Context Conditional Value : Type*}

/-- A conditional functional descends when one context function agrees with it on every
population/context pair carrying positive marginal mass. -/
def FunctionalDescends (mass : Population → Context → ℝ)
    (conditionalSection : Population → Context → Conditional) (b : Conditional → Value) : Prop :=
  ∃ witness : Context → Value, ∀ P x, 0 < mass P x → b (conditionalSection P x) = witness x

/-- The canonical local condition: two versions are compared only where both populations put
positive marginal mass. -/
def OverlapConsistent (mass : Population → Context → ℝ)
    (conditionalSection : Population → Context → Conditional) (b : Conditional → Value) : Prop :=
  ∀ P Q x, 0 < mass P x → 0 < mass Q x →
    b (conditionalSection P x) = b (conditionalSection Q x)

/-- Descent always implies consistency on overlap.  At a common atom this is exact pointwise
equality, not equality of arbitrarily selected off-support versions. -/
theorem overlapConsistent_of_descends (mass : Population → Context → ℝ)
    (conditionalSection : Population → Context → Conditional) (b : Conditional → Value)
    (h : FunctionalDescends mass conditionalSection b) :
    OverlapConsistent mass conditionalSection b := by
  obtain ⟨witness, hw⟩ := h
  intro P Q x hP hQ
  rw [hw P x hP, hw Q x hQ]

/-- **Finite/dominated gluing theorem.**  With no measurability obstruction, pairwise overlap
consistency constructs a single witness by choosing any population present at each context.

The proof does not store a theorem inside model data and does not choose a conditional off its
support: the arbitrary default is used only at contexts with zero mass in every population. -/
theorem descends_of_overlapConsistent [Nonempty Value]
    (mass : Population → Context → ℝ)
    (conditionalSection : Population → Context → Conditional) (b : Conditional → Value)
    (h : OverlapConsistent mass conditionalSection b) :
    FunctionalDescends mass conditionalSection b := by
  classical
  let witness : Context → Value := fun x ↦
    if hx : ∃ P, 0 < mass P x then b (conditionalSection (Classical.choose hx) x)
    else Classical.choice inferInstance
  refine ⟨witness, ?_⟩
  intro P x hP
  have hx : ∃ Q, 0 < mass Q x := ⟨P, hP⟩
  rw [show witness x = b (conditionalSection (Classical.choose hx) x) by simp [witness, hx]]
  exact h P (Classical.choose hx) x hP (Classical.choose_spec hx)

/-- On finite-valued biological models the dominated characterization is an equivalence. -/
theorem functionalDescends_iff_overlapConsistent [Nonempty Value]
    (mass : Population → Context → ℝ)
    (conditionalSection : Population → Context → Conditional) (b : Conditional → Value) :
    FunctionalDescends mass conditionalSection b ↔
      OverlapConsistent mass conditionalSection b :=
  ⟨overlapConsistent_of_descends mass conditionalSection b,
    descends_of_overlapConsistent mass conditionalSection b⟩

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

/-- A modulus of continuity turns conditional-section distance into an explicit portability
bound.  This is the pointwise form of `Osc ≤ ω(diameter)`, before taking any supremum. -/
theorem section_modulus_bound
    (conditionalSection : Population → Context → Conditional) (b : Conditional → Value)
    (rho : Conditional → Conditional → ℝ) (d : Value → Value → ℝ)
    (omega : ℝ → ℝ)
    (hmod : ∀ μ ν, d (b μ) (b ν) ≤ omega (rho μ ν)) (P Q : Population) (x : Context) :
    d (b (conditionalSection P x)) (b (conditionalSection Q x)) ≤
      omega (rho (conditionalSection P x) (conditionalSection Q x)) :=
  hmod _ _

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

/-- The likelihood-ratio tilt expressed only through the posterior component coordinate. -/
noncomputable def posteriorTilt (q : Component → Genome → ℝ)
    (w0 w : Component → ℝ) (g : Genome) : ℝ :=
  ∑ k, componentPosterior q w0 g k * (w k / w0 k)

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
  localValue - mixtureValue

/-- Failure of a functional to commute with component mixing. -/
noncomputable def jensenResidual (mixtureValue : ℝ)
    (a componentValue : Component → ℝ) : ℝ :=
  mixtureValue - ∑ k, a k * componentValue k

/-- **Exact two-residual law.**  Posterior-component representation error is the sum of a
localization error and a Jensen/nonlinearity error.  An affine functional can still have a large
localization residual; disjoint components can make both residuals vanish even for nonlinear
functionals. -/
theorem componentRepresentationResidual_decomposition (localValue mixtureValue : ℝ)
    (a componentValue : Component → ℝ) :
    componentRepresentationResidual localValue a componentValue =
      localizationResidual localValue mixtureValue +
        jensenResidual mixtureValue a componentValue := by
  unfold componentRepresentationResidual localizationResidual jensenResidual
  ring

end Residual

end Calibrator
