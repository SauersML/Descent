/-
Copyright (c) 2026 Sauers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sauers
-/
import Calibrator.HorizonCurve
import Calibrator.ReversibleMarkovSpectrum
import Calibrator.DriftingConditional

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
* the imported identification layer separates static threshold gauge from
  dynamically identifiable threshold motion; and
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

/-! ## A stationary marginal does not identify the conditional -/

/-- A response concentrated in ancestry state zero. -/
def stateZeroResponse (i : Fin 2) : ℝ := if i = 0 then 1 else 0

/-- A response concentrated in ancestry state one. -/
def stateOneResponse (i : Fin 2) : ℝ := if i = 1 then 1 else 0

/-- The uniform two-state population remains positive under the kernel that
never moves. -/
theorem transportMass_stayKernel_uniformTwo_pos (y : Fin 2) :
    0 < transportMass stayKernel uniformTwo y := by
  fin_cases y <;>
    norm_num [transportMass, stayKernel, uniformTwo, Fin.sum_univ_two]

/-- **A stationary marginal carries no information about the conditional.**

    The same uniform population and the same stationary transport support two
    opposite response curves. Their transported population marginals agree at
    every state, while their transported responses at state zero are `1` and
    `0`. This is a concrete, non-vacuous counterexample to unconditional
    reconstruction of a conditional from a stationary marginal path. -/
theorem stationaryMarginal_does_not_identify_conditional :
    (∀ y, transportMass stayKernel uniformTwo y = uniformTwo y) ∧
      transportedResponse stayKernel uniformTwo stateZeroResponse
          transportMass_stayKernel_uniformTwo_pos 0 = 1 ∧
      transportedResponse stayKernel uniformTwo stateOneResponse
          transportMass_stayKernel_uniformTwo_pos 0 = 0 := by
  constructor
  · intro y
    fin_cases y <;>
      norm_num [transportMass, stayKernel, uniformTwo, Fin.sum_univ_two]
  · constructor <;>
      norm_num [transportedResponse, transportMass, markedMass, uniformTwo,
        stayKernel, stateZeroResponse, stateOneResponse, Fin.sum_univ_two]

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

/-! ## The portability law: which half of a calibration curve survives drift

A response curve on two ancestry states splits into a baseline (its mean) and a
score-dependent part (its contrast component). Repeated ancestry switching fixes the first
exactly and damps the second geometrically. That asymmetry is the portability law, and it
is the structural reason a recalibration that models the score distribution but not the
baseline loses the component with the longer half-life.
-/

/-- Act on a response curve by a transition kernel: `(applyKernel P f) i = ∑ j P i j * f j`.

    This is the action on functions, dual to `transportMass`'s action on masses. -/
noncomputable def applyKernel (P : ι → ι → ℝ) (f : ι → ℝ) (i : ι) : ℝ :=
  ∑ j, P i j * f j

/-- Repeated ancestry switching, `n` steps of drift. -/
noncomputable def applyKernelIter (P : ι → ι → ℝ) : ℕ → (ι → ℝ) → (ι → ℝ)
  | 0, f => f
  | n + 1, f => applyKernel P (applyKernelIter P n f)

/-- **The baseline is exactly conserved.** A row-stochastic kernel fixes constants, at every
    number of steps, so the durable part of a calibration curve is its level. -/
theorem applyKernelIter_const (P : ι → ι → ℝ) (hP : IsMassPreservingKernel P) (c : ℝ) :
    ∀ n, applyKernelIter P n (fun _ ↦ c) = fun _ ↦ c := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      funext i
      simp only [applyKernelIter, ih, applyKernel]
      rw [← Finset.sum_mul, hP i, one_mul]

/-- Two-state response curves decompose as baseline plus a multiple of the ancestry
    contrast. This is the split whose two halves have different fates. -/
noncomputable def twoStateCurve (baseline amplitude : ℝ) (i : Fin 2) : ℝ :=
  baseline + amplitude * twoStateContrast i

/-- **The score-dependent half decays geometrically.** One step of symmetric switching
    multiplies the contrast amplitude by the persistence eigenvalue and leaves the baseline
    alone. -/
theorem applyKernel_twoStateCurve (switch baseline amplitude : ℝ) :
    applyKernel (symmetricTwoStateKernel switch) (twoStateCurve baseline amplitude) =
      twoStateCurve baseline (twoStatePersistence switch switch * amplitude) := by
  funext i
  simp only [applyKernel, twoStateCurve]
  fin_cases i <;>
    simp only [symmetricTwoStateKernel, twoStateContrast, twoStatePersistence,
      Fin.sum_univ_two] <;>
    norm_num <;>
    ring

/-- **The portability law on two ancestry states.**

    After `n` steps of drift the baseline is untouched and the score-dependent amplitude
    carries a factor `persistence ^ n`. So the two halves of a calibration curve have
    different fates: the level is durable, the slope is perishable, and the curve flattens
    toward local prevalence at a geometric rate set by how fast ancestry mixes.

    The practical reading, which is why this is stated about a curve rather than about an
    eigenvalue: a recalibration that adjusts the score distribution but does not model the
    baseline discards precisely the component that survives longest. Far from training, the
    surviving content of a score is the local base rate. -/
theorem applyKernelIter_twoStateCurve (switch baseline amplitude : ℝ) (n : ℕ) :
    applyKernelIter (symmetricTwoStateKernel switch) n
        (twoStateCurve baseline amplitude) =
      twoStateCurve baseline (twoStatePersistence switch switch ^ n * amplitude) := by
  induction n with
  | zero => simp [applyKernelIter]
  | succ n ih =>
      rw [applyKernelIter, ih, applyKernel_twoStateCurve]
      congr 1
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

/-- A positive Ornstein-Uhlenbeck rate and a nonnegative biological drift
horizon. Keeping the domain facts in the data prevents the variance formula
from silently dividing by zero or describing negative time. -/
structure OUHorizon where
  rate : ℝ
  time : ℝ
  rate_pos : 0 < rate
  time_nonneg : 0 ≤ time

/-- The zero drift horizon at a positive relaxation rate. -/
def OUHorizon.zero (rate : ℝ) (hrate : 0 < rate) : OUHorizon where
  rate := rate
  time := 0
  rate_pos := hrate
  time_nonneg := le_rfl

/-- Variance accumulated by an Ornstein-Uhlenbeck bridge over a valid horizon.

    Empirical status: UNTESTED. -/
noncomputable def ouVariance (horizon : OUHorizon) : ℝ :=
  (1 - Real.exp (-(2 * horizon.rate * horizon.time))) / (2 * horizon.rate)

/-- The denominator shared by both surfaces of the drifting probit index.

    Empirical status: UNTESTED. -/
noncomputable def probitScaleFactor (a0 : ℝ) (horizon : OUHorizon) : ℝ :=
  Real.sqrt (1 + a0 ^ 2 * ouVariance horizon)

/-- Slope surface of the drifting probit index.

    Empirical status: UNTESTED. -/
noncomputable def probitSlope (a0 : ℝ) (horizon : OUHorizon) : ℝ :=
  a0 * Real.exp (-(horizon.rate * horizon.time)) /
    probitScaleFactor a0 horizon

/-- Intercept surface of the drifting probit index.

    Empirical status: UNTESTED. -/
noncomputable def probitIntercept (a0 b0 : ℝ) (horizon : OUHorizon) : ℝ :=
  b0 / probitScaleFactor a0 horizon

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
theorem probitIntercept_div_probitSlope (a0 b0 : ℝ) (horizon : OUHorizon)
    (ha : a0 ≠ 0) (hS : probitScaleFactor a0 horizon ≠ 0) :
    probitIntercept a0 b0 horizon / probitSlope a0 horizon =
      b0 / a0 * Real.exp (horizon.rate * horizon.time) := by
  have hE : Real.exp (horizon.rate * horizon.time) ≠ 0 := Real.exp_ne_zero _
  unfold probitIntercept probitSlope
  rw [Real.exp_neg]
  field_simp

/-- At drift time zero the ratio is the ratio of the initial parameters, so the invariant
    is anchored rather than merely proportional. -/
theorem probitIntercept_div_probitSlope_zero (a0 b0 lam : ℝ) (ha : a0 ≠ 0)
    (hlam : 0 < lam) (hS : probitScaleFactor a0 (OUHorizon.zero lam hlam) ≠ 0) :
    probitIntercept a0 b0 (OUHorizon.zero lam hlam) /
        probitSlope a0 (OUHorizon.zero lam hlam) = b0 / a0 := by
  simpa [OUHorizon.zero] using
    probitIntercept_div_probitSlope a0 b0 (OUHorizon.zero lam hlam) ha hS

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
