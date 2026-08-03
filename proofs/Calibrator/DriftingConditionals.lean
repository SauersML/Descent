/-
Copyright (c) 2026 Sauers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sauers
-/
import Calibrator.HorizonCurve
import Calibrator.ReversibleMarkovSpectrum

/-!
# Drifting conditionals in finite biological state spaces

This module wires the finite, self-contained core of the drifting-conditionals
calculus into the population-genetics development. The state type can represent
ancestry, deme, local haplotype state, or an environmental stratum.

The analytic diffusion, infinite-dimensional realization, and observability
claims from the source derivation are not smuggled in as assumptions here. The
results below need only finite sums and are proved directly:

* a frozen binary mark and the population mass are transported by one kernel;
* row-stochastic transport preserves marked prevalence exactly;
* the transported response curve reconstructs the transported marked mass;
* shifting a latent population mean and its threshold together is invisible;
* an invariant population mean identifies threshold velocity when the biological
  generator has no constant forcing; and
* symmetric two-state ancestry switching acts on the ancestry contrast through
  the persistence eigenvalue already used by `ReversibleMarkovSpectrum`.

These are the pieces used by the biological core. Stronger manifold-rigidity,
backward-parabolic, and cited spectral-rate claims require separate formal
developments and are deliberately absent rather than represented by theorem
parameters.
-/

namespace Calibrator

open scoped BigOperators

/-! ## Frozen marks under one biological transport kernel -/

variable {ι : Type*} [Fintype ι]

/-- Transport a mass function through a finite kernel. The same operation is
used for total population mass and for the submass carrying a frozen mark. -/
noncomputable def transportMass (P : ι → ι → ℝ) (mass : ι → ℝ) (y : ι) : ℝ :=
  ∑ x, mass x * P x y

/-- Every source state sends total mass one. Nonnegativity is a separate model
condition; mass conservation needs only this normalization equation. -/
def IsMassPreservingKernel (P : ι → ι → ℝ) : Prop :=
  ∀ x, ∑ y, P x y = 1

/-- Row-stochastic transport preserves total mass. -/
theorem transportMass_total (P : ι → ι → ℝ) (mass : ι → ℝ)
    (hP : IsMassPreservingKernel P) :
    ∑ y, transportMass P mass y = ∑ x, mass x := by
  unfold transportMass
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  rw [← Finset.mul_sum, hP x, mul_one]

/-- The marked submass induced by a population mass and response curve. -/
noncomputable def markedMass (population response : ι → ℝ) (x : ι) : ℝ :=
  population x * response x

/-- Response curve after both population mass and frozen marked mass pass
through the same kernel. Positivity of every transported population cell is an
input because a real-valued conditional probability is undefined on an empty
cell. -/
noncomputable def transportedResponse (P : ι → ι → ℝ)
    (population response : ι → ℝ)
    (_hpositive : ∀ y, 0 < transportMass P population y) (y : ι) : ℝ :=
  transportMass P (markedMass population response) y /
    transportMass P population y

/-- Multiplying the reconstructed response by its transported population mass
recovers the transported frozen-mark mass exactly. -/
theorem transportedResponse_mul_population
    (P : ι → ι → ℝ) (population response : ι → ℝ)
    (hpositive : ∀ y, 0 < transportMass P population y) (y : ι) :
    transportMass P population y *
        transportedResponse P population response hpositive y =
      transportMass P (markedMass population response) y := by
  unfold transportedResponse
  field_simp [ne_of_gt (hpositive y)]

/-- Frozen-mark transport conserves prevalence. This is the finite biological
form of transporting the joint marked mass and the marginal by the same forward
equation. -/
theorem transportedResponse_prevalence_conserved
    (P : ι → ι → ℝ) (population response : ι → ℝ)
    (hP : IsMassPreservingKernel P)
    (hpositive : ∀ y, 0 < transportMass P population y) :
    ∑ y, transportMass P population y *
        transportedResponse P population response hpositive y =
      ∑ x, markedMass population response x := by
  calc
    ∑ y, transportMass P population y *
        transportedResponse P population response hpositive y =
        ∑ y, transportMass P (markedMass population response) y := by
          apply Finset.sum_congr rfl
          intro y _
          exact transportedResponse_mul_population P population response hpositive y
    _ = ∑ x, markedMass population response x :=
      transportMass_total P (markedMass population response) hP

/-! ## Static threshold gauge and dynamic identification -/

/-- A latent-threshold response with a fixed link. -/
def latentThresholdResponse {κ : Type*} (link : ℝ → ℝ) (populationMean : κ → ℝ)
    (threshold : ℝ) (x : κ) : ℝ :=
  link (populationMean x - threshold)

/-- A common shift of the latent population mean and threshold is statically
invisible to the entire response curve. -/
theorem latentThresholdResponse_add_gauge {κ : Type*}
    (link : ℝ → ℝ) (populationMean : κ → ℝ) (threshold shift : ℝ) :
    latentThresholdResponse link (fun x ↦ populationMean x + shift)
        (threshold + shift) =
      latentThresholdResponse link populationMean threshold := by
  funext x
  simp only [latentThresholdResponse]
  congr 1
  ring

/-- A population law has total mass one. -/
def IsProbabilityMass (population : ι → ℝ) : Prop :=
  ∑ x, population x = 1

/-- The population mean is invariant under a biological generator. -/
def HasInvariantMean (population : ι → ℝ)
    (generator : (ι → ℝ) → ι → ℝ) : Prop :=
  ∀ f, ∑ x, population x * generator f x = 0

/-- If linked-response velocity equals autonomous population drift minus one
threshold velocity, invariant averaging isolates the threshold velocity. This
is the finite algebraic form of the dynamic identification argument; allowing
an extra constant biological forcing would invalidate the conclusion. -/
theorem thresholdVelocity_eq_neg_invariantMean
    (population : ι → ℝ) (generator : (ι → ℝ) → ι → ℝ)
    (linkedResponse linkedResponseVelocity : ι → ℝ) (thresholdVelocity : ℝ)
    (hpopulation : IsProbabilityMass population)
    (hinvariant : HasInvariantMean population generator)
    (hevolution : ∀ x,
      linkedResponseVelocity x = generator linkedResponse x - thresholdVelocity) :
    thresholdVelocity = -∑ x, population x * linkedResponseVelocity x := by
  have hsum :
      ∑ x, population x * linkedResponseVelocity x =
        ∑ x, population x * (generator linkedResponse x - thresholdVelocity) := by
    apply Finset.sum_congr rfl
    intro x _
    rw [hevolution x]
  simp only [mul_sub] at hsum
  rw [hsum, Finset.sum_sub_distrib, hinvariant linkedResponse,
    ← Finset.sum_mul, hpopulation, one_mul]
  ring

/-! ## Two-state local-ancestry switching -/

/-- Symmetric switching between two local-ancestry or haplotype states. -/
def symmetricTwoStateKernel (switch : ℝ) (i j : Fin 2) : ℝ :=
  if i = j then 1 - switch else switch

theorem symmetricTwoStateKernel_mass_preserving (switch : ℝ) :
    IsMassPreservingKernel (symmetricTwoStateKernel switch) := by
  intro i
  fin_cases i <;>
    norm_num [symmetricTwoStateKernel, Fin.sum_univ_two]

/-- The uniform two-state population is stationary under symmetric switching. -/
theorem uniformTwo_stationary_symmetricTwoStateKernel (switch : ℝ) :
    IsStationaryKernel uniformTwo (symmetricTwoStateKernel switch) := by
  intro j
  fin_cases j <;>
    norm_num [uniformTwo, symmetricTwoStateKernel, Fin.sum_univ_two] <;>
    ring

/-- The centered ancestry contrast. -/
def twoStateContrast (i : Fin 2) : ℝ := if i = 0 then 1 else -1

/-- Symmetric ancestry switching damps the centered ancestry contrast by the
same persistence eigenvalue used by the reversible Markov spectral kernel. -/
theorem symmetricTwoStateKernel_contrast (switch : ℝ) (i : Fin 2) :
    ∑ j, symmetricTwoStateKernel switch i j * twoStateContrast j =
      twoStatePersistence switch switch * twoStateContrast i := by
  fin_cases i <;>
    norm_num [symmetricTwoStateKernel, twoStateContrast, twoStatePersistence,
      Fin.sum_univ_two] <;>
    ring

/-! ## The drifting probit index, and the constraint tying its two surfaces

Under Ornstein-Uhlenbeck drift of the covariate the probit single-index family
`Phi (a t * x + b t)` is carried to itself, with

  `a t = a0 * exp (-lam * t) / sqrt (1 + a0 ^ 2 * ouVariance lam t)`,
  `b t = b0 / sqrt (1 + a0 ^ 2 * ouVariance lam t)`.

The two surfaces share one denominator. That the family is invariant is an analytic fact
about the Gaussian semigroup which is NOT proved here; what is proved here is the algebraic
consequence, and it is the part a fitted model can be tested against.
-/

/-- Variance accumulated by an Ornstein-Uhlenbeck bridge over drift time `t` at rate `lam`.

    Empirical status: UNTESTED. -/
noncomputable def ouVariance (lam t : ℝ) : ℝ :=
  (1 - Real.exp (-(2 * lam * t))) / (2 * lam)

/-- The denominator shared by both surfaces of the drifting probit index.

    Empirical status: UNTESTED. -/
noncomputable def probitScaleFactor (a0 lam t : ℝ) : ℝ :=
  Real.sqrt (1 + a0 ^ 2 * ouVariance lam t)

/-- Slope surface of the drifting probit index.

    Empirical status: UNTESTED. -/
noncomputable def probitSlope (a0 lam t : ℝ) : ℝ :=
  a0 * Real.exp (-(lam * t)) / probitScaleFactor a0 lam t

/-- Intercept surface of the drifting probit index.

    Empirical status: UNTESTED. -/
noncomputable def probitIntercept (a0 b0 lam t : ℝ) : ℝ :=
  b0 / probitScaleFactor a0 lam t

/-- **The intercept and slope surfaces are not independent.**

    Their ratio is a single exponential in drift time with one rate:
    `b t / a t = (b0 / a0) * exp (lam * t)`. The shared `probitScaleFactor` cancels, so
    this needs nothing about the denominator beyond its being nonzero -- in particular it
    does not depend on the analytic invariance claim above.

    Two consequences, and they are the reason this is here rather than in prose.

    Fitting: an intercept surface and a slope surface estimated in separately penalized
    blocks carry one degree of freedom more than the drift model permits. Imposing this
    constraint removes it and leaves one interpretable parameter, the drift rate `lam`.

    Testing: `log (b t / a t)` is affine in `t` with slope `lam`. Curvature in that plot
    refutes Ornstein-Uhlenbeck drift rather than the fit, so this is falsifiable against
    data the corpus already produces.

    Empirical status: UNTESTED, and the test just described is how that changes. -/
theorem probitIntercept_div_probitSlope (a0 b0 lam t : ℝ) (ha : a0 ≠ 0)
    (hS : probitScaleFactor a0 lam t ≠ 0) :
    probitIntercept a0 b0 lam t / probitSlope a0 lam t = b0 / a0 * Real.exp (lam * t) := by
  have hE : Real.exp (lam * t) ≠ 0 := Real.exp_ne_zero _
  unfold probitIntercept probitSlope
  rw [Real.exp_neg]
  field_simp

/-- At drift time zero the ratio is the ratio of the initial parameters, so the invariant
    is anchored rather than merely proportional. -/
theorem probitIntercept_div_probitSlope_zero (a0 b0 lam : ℝ) (ha : a0 ≠ 0)
    (hS : probitScaleFactor a0 lam 0 ≠ 0) :
    probitIntercept a0 b0 lam 0 / probitSlope a0 lam 0 = b0 / a0 := by
  rw [probitIntercept_div_probitSlope a0 b0 lam 0 ha hS]
  simp

/-- The scale parameter `A = a ^ (-2)` linearizes the slope dynamics: if
    `a' = -lam * a - a ^ 3 / 2` then `A' = 2 * lam * A + 1`.

    Stated as the algebraic identity the derivative relation reduces to, so it is checkable
    without carrying a derivative. This linearization is what makes the closed form for the
    slope surface integrable in the first place. -/
theorem probit_scale_linearization (lam a da : ℝ) (ha : a ≠ 0)
    (h : da = -lam * a - a ^ 3 / 2) :
    -2 * da / a ^ 3 = 2 * lam / a ^ 2 + 1 := by
  subst h
  field_simp
  ring

end Calibrator
