/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

namespace Calibrator

open scoped BigOperators

/-!
# A drifting response curve: what a moving threshold hides, and what the dynamics give back

Self-contained: imports only Mathlib.

A response curve is `c_t(s) = P(Y = 1 | S = s)` at time `t` — disease risk as a function of a
polygenic score, ancestry coordinate, or any covariate, in a population that is itself moving.
Three questions decide whether anything read off such a curve means anything: what is invisible
in principle, what survives the drift, and how much an interior estimate can be trusted.

## The threshold gauge, and why statics cannot break it

In a liability-threshold model `Y = 1[Z > θ]` — the standard reading of a polygenic score, with
`Z` liability and `θ` a diagnostic threshold — apply any strictly increasing `h` to the liability
axis. `indicator_lt_eq_of_strictMono` records that the indicator is unchanged. Every observable is
unchanged; the threshold path is changed into an arbitrary increasing relabelling, and can be
flattened to zero. **From response curves alone the threshold path is identifiable at most up to
monotone relabelling**, so a study reporting that diagnostic thresholds moved, on the strength of
fitted curves at several times, is reporting a gauge choice.

Fixing the noise shape narrows it to exactly one direction rather than all of them.
`linkedCurve_identified_modulo_constants` shows the observable determines `m_t - θ_t` and nothing
finer: the unidentified set is the constants-in-`s`, and it is exactly the constants. A
population shift that is uniform across the covariate and a threshold move of the same size are
the same observation, forever, at any density of sampling.

## The dynamics break it, because a generator kills constants

`sum_invariantWeight_mul_generator_eq_zero` is the mechanism: averaging against an invariant
distribution annihilates the population's own dynamics. So if the linked curve moves by a Markov
generator plus a spatially constant threshold velocity, the invariant average of its motion sees
only the threshold:

`invariantAverage_eq_neg_of_affine_evolution`: `Σ ϖ ∂ₜu = -θ̇`.

Everything on the right is observable. This is the whole content: **statics can never separate a
moving threshold from a moving population, and dynamics always can — provided the population
model carries no constant forcing.** `constantForcing_conflates_threshold` is the sharpness: add a
spatially uniform forcing `ζ` and the same average returns `ζ - θ̇`, so only the difference is
ever identified. A Markov generator is exactly a model whose forcing cone excludes constants,
which is why drift rescues an identification no amount of static data can reach.

For genetics the reading is direct. Secular change in diagnostic criteria, in ascertainment, or
in the definition of a case is a moving `θ`; environmental and demographic change is a moving
`m`. Cross-cohort recalibration studies routinely attribute drift in polygenic score performance
to one or the other. The separation is available, but only from the *motion*, and only if the
population's own dynamics are modelled as conservative — which is what a generator is.

## What survives a genuinely mixing drift

`continuousInvariant_eq_at_limit`: a continuous functional constant along the flow takes the same
value on the initial curve and on its limit. Under ergodic mixing the limit is the constant curve
at the base rate, so every continuous invariant of the response curve is a function of prevalence
alone. Discrimination, calibration slope, threshold location, curve shape: all transient. **Under
mixing the base rate is the only stable summary**, and the corpus's separate observation that
prevalence is the conserved charge of the drift is the same fact from the other side.

## How much an interior estimate can be trusted

`interiorError_sq_le_mul_endpoints` is the interpolation bound at the midpoint, in squared form so
that nothing is taken square roots of: the error energy at the midpoint is at most the product of
the endpoint energies. The constant is exactly one, and `singleMode_interiorError_eq` shows a
single spectral mode attains it, so the constant cannot be improved. An estimate of the response
curve between two observation times inherits the geometric mean of the errors at those times;
error does not blow up in the interior, and the hardest data are pure single modes.

## Scope

Everything here is finite-state or finite-mixture and proved as stated. The continuum statements
of the source analysis — the drift-diffusion evolution law for the curve, the probit rigidity
classification, the reconstruction operator built from the observed marginal — need diffusion
generators, Fréchet curve spaces and time-reversal as formal objects, and are not stated here in
any form. `stationaryDrift_collapses_to_generator` is the one continuum computation that is pure
algebra and is proved: at stationarity the curve's transport drift collapses back to the
generator's own drift, which is why the stationary flow is the semigroup itself.

Empirical status: DERIVED. The identification and stability results are proved at the stated
hypotheses; whether a given cohort series satisfies them — a conservative population model, a
known link, an invariant distribution — is an empirical question this asks to be answered rather
than assumed.
-/

/-! ## The threshold gauge -/

/-- **A monotone relabelling of the liability axis is invisible.** Applying any strictly
increasing map to liability and threshold together leaves the case indicator unchanged, so no
observable distinguishes them. -/
theorem indicator_lt_eq_of_strictMono (h : ℝ → ℝ) (hmono : StrictMono h) (Z θ : ℝ) :
    (if θ < Z then (1 : ℝ) else 0) = (if h θ < h Z then (1 : ℝ) else 0) := by
  by_cases hlt : θ < Z
  · simp [hlt, hmono hlt]
  · have hle : h Z ≤ h θ := hmono.le_iff_le.mpr (not_lt.mp hlt)
    simp [hlt, not_lt.mpr hle]

/-- **With the noise shape fixed, the unidentified set is exactly the constants.**

    The observable is the linked curve `m - θ`, with `θ` constant in the covariate. Two
    population/threshold pairs are observationally identical exactly when they differ by one
    number added to both. A uniform population shift and a threshold move of the same size are
    the same observation. -/
theorem linkedCurve_identified_modulo_constants {ι : Type*}
    (m m' : ι → ℝ) (θ θ' : ℝ) :
    (∀ s, m s - θ = m' s - θ') ↔ (∀ s, m' s = m s + (θ' - θ)) := by
  constructor
  · intro h s
    have := h s
    linarith
  · intro h s
    have := h s
    linarith

/-! ## The dynamics separate them -/

/-- A distribution invariant for the generator: `ϖ` is annihilated by `L` acting on the left. -/
def IsInvariantWeight {n : ℕ} (ϖ : Fin n → ℝ) (L : Fin n → Fin n → ℝ) : Prop :=
  ∀ j, ∑ i, ϖ i * L i j = 0

/-- The zero weight is invariant for every generator. This is a useful algebraic base case, but
it is not a probability weight because its total mass is zero. -/
theorem isInvariantWeight_zero {n : ℕ} (L : Fin n → Fin n → ℝ) :
    IsInvariantWeight (fun _ ↦ (0 : ℝ)) L := by
  intro j
  simp

/-- **The invariant-probability assumptions used below are jointly satisfiable.**

    On the nonempty state space `Fin (n + 1)`, put unit mass at state zero and take the zero
    generator. The weight has total mass one and is invariant. This explicit witness rules out
    vacuity without assuming that an arbitrary biological generator has a stationary law. -/
theorem exists_invariantProbabilityWeight (n : ℕ) :
    ∃ ϖ : Fin (n + 1) → ℝ, ∃ L : Fin (n + 1) → Fin (n + 1) → ℝ,
      (∀ i, 0 ≤ ϖ i) ∧ (∑ i, ϖ i = 1) ∧ IsInvariantWeight ϖ L := by
  refine ⟨fun i ↦ if i = 0 then 1 else 0, fun _ _ ↦ 0, ?_, ?_, ?_⟩
  · intro i
    positivity
  · simp
  · intro j
    simp

/-- A generator whose columns sum to zero admits the uniform weight as invariant, which is
    the witness that matters for a symmetric biological generator. -/
theorem isInvariantWeight_one_of_colSum_zero {n : ℕ} (L : Fin n → Fin n → ℝ)
    (hcol : ∀ j, ∑ i, L i j = 0) :
    IsInvariantWeight (fun _ ↦ (1 : ℝ)) L := by
  intro j
  simpa using hcol j

/-- **Averaging against an invariant distribution annihilates the population dynamics.** This is
the projection that exposes the exogenous constant. -/
theorem sum_invariantWeight_mul_generator_eq_zero {n : ℕ}
    (ϖ : Fin n → ℝ) (L : Fin n → Fin n → ℝ) (u : Fin n → ℝ)
    (hinv : IsInvariantWeight ϖ L) :
    ∑ i, ϖ i * (∑ j, L i j * u j) = 0 := by
  have hstep : ∀ i : Fin n, ϖ i * (∑ j, L i j * u j) = ∑ j, ϖ i * L i j * u j := by
    intro i
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ ↦ by ring
  rw [Finset.sum_congr rfl fun i _ ↦ hstep i, Finset.sum_comm]
  refine Finset.sum_eq_zero fun j _ ↦ ?_
  rw [← Finset.sum_mul, hinv j, zero_mul]

/-- **The threshold's velocity is minus the invariant average of the linked curve's motion.**

    `u` is the observed linked curve, moving by the population generator plus a spatially
    constant threshold velocity. Averaging against the invariant distribution kills the generator
    term and leaves `-θ̇`, with everything on the left observable.

    This is the exact separation that `linkedCurve_identified_modulo_constants` shows is
    impossible from statics: there the constant direction is unreachable at every fixed time, and
    here it is the only direction that survives. -/
theorem invariantAverage_eq_neg_of_affine_evolution {n : ℕ}
    (ϖ : Fin n → ℝ) (L : Fin n → Fin n → ℝ) (u du : Fin n → ℝ) (thetaDot : ℝ)
    (hmass : ∑ i, ϖ i = 1) (hinv : IsInvariantWeight ϖ L)
    (hdyn : ∀ i, du i = (∑ j, L i j * u j) - thetaDot) :
    ∑ i, ϖ i * du i = -thetaDot := by
  have hsplit : ∀ i : Fin n,
      ϖ i * du i = ϖ i * (∑ j, L i j * u j) - thetaDot * ϖ i := by
    intro i
    rw [hdyn i]
    ring
  rw [Finset.sum_congr rfl fun i _ ↦ hsplit i, Finset.sum_sub_distrib,
    sum_invariantWeight_mul_generator_eq_zero ϖ L u hinv, ← Finset.mul_sum, hmass]
  ring

/-- **Sharpness: a spatially uniform forcing is conflated with the threshold forever.**

    Add a constant forcing `ζ` to the population's motion and the same average returns
    `ζ - θ̇`. Only the difference is identified, at any sampling density, which is why the
    separation above needs the population model's forcing cone to exclude constants — and a
    Markov generator is exactly such a model. -/
theorem constantForcing_conflates_threshold {n : ℕ}
    (ϖ : Fin n → ℝ) (L : Fin n → Fin n → ℝ) (u du : Fin n → ℝ) (thetaDot zeta : ℝ)
    (hmass : ∑ i, ϖ i = 1) (hinv : IsInvariantWeight ϖ L)
    (hdyn : ∀ i, du i = (∑ j, L i j * u j) + zeta - thetaDot) :
    ∑ i, ϖ i * du i = zeta - thetaDot := by
  have hsplit : ∀ i : Fin n,
      ϖ i * du i = ϖ i * (∑ j, L i j * u j) + (zeta - thetaDot) * ϖ i := by
    intro i
    rw [hdyn i]
    ring
  rw [Finset.sum_congr rfl fun i _ ↦ hsplit i, Finset.sum_add_distrib,
    sum_invariantWeight_mul_generator_eq_zero ϖ L u hinv, ← Finset.mul_sum, hmass]
  ring

/-! ## What survives a mixing drift -/

/-- **A continuous invariant of the drift is determined by the drift's limit.**

    If a functional is constant along the flow and the flow converges, the functional's value on
    the initial curve equals its value at the limit. Under ergodic mixing that limit is the
    constant curve at the base rate, so every continuous invariant is a function of prevalence
    alone: discrimination, calibration and curve shape are all transient, and the base rate is
    the only stable summary. -/
theorem continuousInvariant_eq_at_limit {H : Type*} [TopologicalSpace H] [T2Space H]
    (Phi : H → ℝ) (hPhi : Continuous Phi) (flow : ℝ → H) (limit : H)
    (hinv : ∀ t, Phi (flow t) = Phi (flow 0))
    (hconv : Filter.Tendsto flow Filter.atTop (nhds limit)) :
    Phi (flow 0) = Phi limit := by
  have hcomp : Filter.Tendsto (fun t ↦ Phi (flow t)) Filter.atTop (nhds (Phi limit)) :=
    (hPhi.tendsto limit).comp hconv
  have hconst : Filter.Tendsto (fun t ↦ Phi (flow t)) Filter.atTop (nhds (Phi (flow 0))) := by
    simp [hinv]
  exact tendsto_nhds_unique hconst hcomp

/-! ## Interior estimates: the interpolation bound with constant one -/

/-- Error energy of a spectral mixture at time `t`: mode `k` carries weight `w k` and relaxes at
rate `lam k`. -/
noncomputable def errorEnergy {n : ℕ} (w lam : Fin n → ℝ) (t : ℝ) : ℝ :=
  ∑ k, w k * Real.exp (-(2 * lam k * t))

/-- **The interior error energy is at most the product of the endpoint energies.**

    Stated in squared form so nothing is square-rooted: at the midpoint of two observation times
    the error energy squared is bounded by the product of the energies there. The constant is
    exactly one, so an estimate between two observations inherits the geometric mean of their
    errors and cannot blow up in the interior. -/
theorem interiorError_sq_le_mul_endpoints {n : ℕ} (w lam : Fin n → ℝ) (t₁ t₂ : ℝ)
    (hw : ∀ k, 0 ≤ w k) :
    errorEnergy w lam ((t₁ + t₂) / 2) ^ 2 ≤
      errorEnergy w lam t₁ * errorEnergy w lam t₂ := by
  have key := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun k : Fin n ↦ Real.sqrt (w k * Real.exp (-(2 * lam k * t₁))))
    (fun k : Fin n ↦ Real.sqrt (w k * Real.exp (-(2 * lam k * t₂))))
  have hnn : ∀ (k : Fin n) (r : ℝ), 0 ≤ w k * Real.exp r := fun k r ↦
    mul_nonneg (hw k) (Real.exp_pos r).le
  have hexp : ∀ k : Fin n,
      Real.exp (-(2 * lam k * t₁)) * Real.exp (-(2 * lam k * t₂))
        = Real.exp (-(2 * lam k * ((t₁ + t₂) / 2))) ^ 2 := by
    intro k
    rw [← Real.exp_add, pow_two, ← Real.exp_add]
    congr 1
    ring
  have hprod : ∀ k : Fin n,
      Real.sqrt (w k * Real.exp (-(2 * lam k * t₁))) *
          Real.sqrt (w k * Real.exp (-(2 * lam k * t₂)))
        = w k * Real.exp (-(2 * lam k * ((t₁ + t₂) / 2))) := by
    intro k
    rw [← Real.sqrt_mul (hnn k _)]
    have hcollect : w k * Real.exp (-(2 * lam k * t₁)) * (w k * Real.exp (-(2 * lam k * t₂)))
        = (w k * Real.exp (-(2 * lam k * ((t₁ + t₂) / 2)))) ^ 2 := by
      calc w k * Real.exp (-(2 * lam k * t₁)) * (w k * Real.exp (-(2 * lam k * t₂)))
          = w k ^ 2 * (Real.exp (-(2 * lam k * t₁)) * Real.exp (-(2 * lam k * t₂))) := by ring
        _ = w k ^ 2 * Real.exp (-(2 * lam k * ((t₁ + t₂) / 2))) ^ 2 := by rw [hexp k]
        _ = (w k * Real.exp (-(2 * lam k * ((t₁ + t₂) / 2)))) ^ 2 := by ring
    rw [hcollect, Real.sqrt_sq (hnn k _)]
  have hsq₁ : ∀ k : Fin n,
      Real.sqrt (w k * Real.exp (-(2 * lam k * t₁))) ^ 2 = w k * Real.exp (-(2 * lam k * t₁)) :=
    fun k ↦ Real.sq_sqrt (hnn k _)
  have hsq₂ : ∀ k : Fin n,
      Real.sqrt (w k * Real.exp (-(2 * lam k * t₂))) ^ 2 = w k * Real.exp (-(2 * lam k * t₂)) :=
    fun k ↦ Real.sq_sqrt (hnn k _)
  rw [Finset.sum_congr rfl fun k _ ↦ hprod k,
    Finset.sum_congr rfl fun k _ ↦ hsq₁ k,
    Finset.sum_congr rfl fun k _ ↦ hsq₂ k] at key
  exact key

/-- **A single mode attains the bound**, so the constant one cannot be improved: the hardest data
    for interior reconstruction are pure spectral modes. -/
theorem singleMode_interiorError_eq (w lam t₁ t₂ : ℝ) :
    (w * Real.exp (-(2 * lam * ((t₁ + t₂) / 2)))) ^ 2
      = (w * Real.exp (-(2 * lam * t₁))) * (w * Real.exp (-(2 * lam * t₂))) := by
  have hexp : Real.exp (-(2 * lam * t₁)) * Real.exp (-(2 * lam * t₂))
      = Real.exp (-(2 * lam * ((t₁ + t₂) / 2))) ^ 2 := by
    rw [← Real.exp_add, pow_two, ← Real.exp_add]
    congr 1
    ring
  calc (w * Real.exp (-(2 * lam * ((t₁ + t₂) / 2)))) ^ 2
      = w ^ 2 * Real.exp (-(2 * lam * ((t₁ + t₂) / 2))) ^ 2 := by ring
    _ = w ^ 2 * (Real.exp (-(2 * lam * t₁)) * Real.exp (-(2 * lam * t₂))) := by rw [hexp]
    _ = (w * Real.exp (-(2 * lam * t₁))) * (w * Real.exp (-(2 * lam * t₂))) := by ring

/-! ## The probit realization dynamics

The one piece of the continuum realization theory that is calculus rather than analysis. Under
Ornstein-Uhlenbeck drift the probit family `Φ(a x + b)` is exactly invariant, and its parameters
obey `ȧ = -λ a - a³/2`. That planar system looks nonlinear and is not: the substitution
`A = a⁻²` linearises it to `Ȧ = 2λA + 1`, which is why the realization is integrable in closed
form rather than merely finite-dimensional.

What is proved here is exactly that substitution. The invariance of the family itself needs the
Gaussian identity `E[Φ(α + βZ)] = Φ(α/√(1+β²))` and the OU semigroup, neither of which is set up
in this file, and neither is asserted. -/

/-- **The inverse-square substitution linearises the probit realization flow.**

    If the slope parameter obeys `ȧ = -λ a - a³/2`, then `A = a⁻²` obeys `Ȧ = 2λ A + 1`. The
    nonlinearity is a coordinate artifact: the realization dynamics are affine, hence solvable in
    closed form, which is what makes the two-dimensional invariant family explicit rather than
    merely existent. -/
theorem inverseSquare_linearises_probit_flow
    (a : ℝ → ℝ) (lam t : ℝ) (hne : a t ≠ 0)
    (hderiv : HasDerivAt a (-(lam * a t) - a t ^ 3 / 2) t) :
    HasDerivAt (fun s => ((a s) ^ 2)⁻¹) (2 * lam * ((a t) ^ 2)⁻¹ + 1) t := by
  have hsqne : (a t) ^ 2 ≠ 0 := pow_ne_zero 2 hne
  have hsq : HasDerivAt (fun s => (a s) ^ 2)
      (2 * a t ^ 1 * (-(lam * a t) - a t ^ 3 / 2)) t := hderiv.pow 2
  have hinv := hsq.inv hsqne
  have hval : -(2 * a t ^ 1 * (-(lam * a t) - a t ^ 3 / 2)) / ((a t) ^ 2) ^ 2
      = 2 * lam * ((a t) ^ 2)⁻¹ + 1 := by
    field_simp
    ring
  rwa [hval] at hinv

/-! ## The stationary collapse -/

/-- **At stationarity the curve's transport drift is the generator's own drift.**

    The response curve moves with drift `a' + a (log p)' - b`, built from the observed population
    density `p`. Under reversibility the stationary density satisfies `b = a'/2 + a (log π)'/2`,
    and substituting it returns `b`: the drifting equation collapses to the generator. This is
    the algebraic step behind "at stationarity the curve flows by the semigroup itself", and it
    is the only continuum computation in this file that is pure algebra. -/
theorem stationaryDrift_collapses_to_generator (aPrime aTimesScore b : ℝ)
    (hrev : b = aPrime / 2 + aTimesScore / 2) :
    aPrime + aTimesScore - b = b := by
  rw [hrev]; ring

end Calibrator
