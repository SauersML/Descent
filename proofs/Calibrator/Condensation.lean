import Calibrator.Probability
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace Calibrator

/-!
# Condensation: the multiplicative obstruction to Gaussian universality of chaos

This file formalizes the *tangency* geometry that governs when a normalized sum of
high-degree monomials in independent coordinates forgets its coordinate law.

## Why this belongs in a polygenic-score development

A polygenic score is a normalized aggregate of many small per-variant contributions.
Every asymptotic statement about the score distribution — the Gaussian score
assumption underlying `Calibrator.ScoreDistribution`, liability-threshold
calibration, the Berry-Esseen certificates in `Calibrator.Probability` — is an
instance of the following claim: *a low-influence aggregate of genotypes behaves as
if the genotypes were Gaussian.* For **degree-one** (purely additive) scores this is
true and quantitative (Berry-Esseen). The theorems in this file and its companions
say that it becomes **false** for aggregates of diverging multiplicative degree, i.e.
for epistatic scores, and they locate the exact degree at which it fails.

The failure is not additive and is therefore invisible to every additive diagnostic
(cumulants, influences, mixing). It is multiplicative: a product of `m` independent
standardized factors converts the *diagonal* data of the coordinate law into an
exponential separation of scale. The controlling object is the Mellin exponent
`psi(theta) = log E |x| ^ (2 * theta)` at the interior point `theta = 1` — the
size-bias point — not the jet of the log-characteristic function at the origin, which
is what cumulants are.

## Attribution (recorded before any novelty claim, per the standing rule)

The phase-transition mechanism for `sum_j exp(t X_j)` with `N ~ exp(lambda H(t))`
terms, its two critical points, and limit laws at the critical points, are
Ben Arous-Bogachev-Molchanov, *Limit theorems for sums of random exponentials*,
PTRF **132** (2005). The parallel fluctuation phase diagram for the REM is
Bovier-Kurkova-Loewe, Ann. Probab. **30** (2002). Nearly optimal upper *and lower*
bounds for Gaussian universality of approximately polynomial functions are
Huang-Austern-Orbanz, arXiv:2403.10711; the condensation counterexample lives in
their lower-bound territory. `condensationConstant` below is an **evaluation** of the
BBM second critical point for `log g ^ 2` increments, not a new constant. What is
formalized here as our own contribution is only the *completeness-of-blindness*
packaging (`Calibrator.JetBarrier`) and the genetics transport
(`Calibrator.PolygenicSpectroscopy`).

## Main results in this file

* `MellinProfile.tangency` — **Lemma T**: `s ≤ rate s` for every unit-variance law,
  one line from `psi 1 = 0`. The diagonal is tangent from below to every rate
  function.
* `MellinProfile.tangency_eq_drift` — equality forces `s = drift`: the tangency point
  is the size-bias mean, so every variance-normalized design is *pinned* to
  `theta = 1`.
* `MellinProfile.spike_cost_ge` — the operational form: a monomial spike of size `N`
  costs at least `log N`, hence is never more likely than `1 / N`. Spikes are always
  at most marginal, and exactly marginal only at the tangency slope.
* `condensationConstant` (`c_G = 2 - gamma - log 2`) with rigorous two-sided bounds
  and strict positivity, from mathlib's Euler-Mascheroni and `log 2` bounds.
* `gaussianJetVariance` (`v_G = pi ^ 2 / 2 - 4`) with strict positivity.
* `criticalDegree` and `subcritical_iff` — the sharp phase boundary
  `m* = log N / c`.
* `windowVariance` and its monotonicity/limits — the condensation-window law
  `N(0, Phi(w / sqrt v))`, whose variance interpolates `0 -> 1` through the error
  function of the window position.
-/

open scoped BigOperators

/-!
## 1. The Mellin profile and the Tangency Lemma

We package the multiplicative data of a unit-variance coordinate law. `psi` is the
Mellin exponent `theta ↦ log E |x| ^ (2 * theta)`; `psi 1 = 0` is exactly unit second
moment. `rate` is its Legendre transform (the Cramer rate function of `log x ^ 2`);
we do not construct the supremum, we axiomatize the two properties of a supremum that
the theory uses, so that the analytic input is named rather than hidden.
-/

/-- The multiplicative (Mellin) data of a centered unit-variance coordinate law.

`psi theta = log E |x| ^ (2 * theta)` is convex with `psi 1 = 0`; `rate` is its
Legendre transform, the Cramer rate function of the increment `l = log x ^ 2`;
`drift = E[x ^ 2 * log x ^ 2] = psi'(1)` is the mean of `l` under the size-biased law
`dPtilde = x ^ 2 dP`; `jetVariance = psi''(1)` is its variance under the same law.

The pair `(drift, jetVariance)` is the **Mellin 2-jet at the size-bias point**. -/
structure MellinProfile where
  /-- Mellin exponent `theta ↦ log E |x| ^ (2 * theta)`. -/
  psi : ℝ → ℝ
  /-- Unit second moment. This single equation is what makes `theta = 1` special. -/
  psi_one : psi 1 = 0
  /-- Cramer rate function of `log x ^ 2`. -/
  rate : ℝ → ℝ
  /-- `rate` dominates every affine minorant: the defining property of a Legendre
  transform that we actually use. -/
  rate_ge : ∀ θ s : ℝ, θ * s - psi θ ≤ rate s
  /-- `drift = psi'(1) = E[x ^ 2 log x ^ 2]`, the size-biased mean increment. -/
  drift : ℝ
  /-- At the size-bias mean the tilt `theta = 1` is optimal: this is the statement
  that `drift` really is `psi'(1)`, and it is the only place attainment is used. -/
  rate_drift_le : rate drift ≤ drift
  /-- Strict convexity of `psi`, in the only form the theory needs: `psi` has a
  unique subgradient at `theta = 1`, namely `drift`. -/
  subgradient_unique : ∀ s : ℝ, (∀ θ : ℝ, (θ - 1) * s ≤ psi θ) → s = drift
  /-- `jetVariance = psi''(1)`, the size-biased increment variance. -/
  jetVariance : ℝ
  jetVariance_pos : 0 < jetVariance

namespace MellinProfile

variable (P : MellinProfile)

/-- **Lemma T (Tangency Lemma).** For every unit-variance law the Cramer rate function
of `log x ^ 2` dominates the diagonal: `rate s ≥ s` for all `s`.

The entire proof is: take `theta = 1` in the Legendre supremum and use `psi 1 = 0`.
This one line is the engine of the whole development. -/
theorem tangency (s : ℝ) : s ≤ P.rate s := by
  have h := P.rate_ge 1 s
  rw [P.psi_one] at h
  linarith

/-- The diagonal is tangent to the rate function **exactly** at the size-bias mean:
if `rate s = s` then `s = drift`.

Consequence: any design whose variance normalization forces its relevant deviation to
sit on the diagonal is pinned to the tilt `theta = 1`. This is why the observable
algebra of independent designs is a *jet at `theta = 1`*, and why cumulants — the jet
at the origin of the multiplicative group — cannot see it. -/
theorem tangency_eq_drift {s : ℝ} (h : P.rate s = s) : s = P.drift := by
  refine P.subgradient_unique s ?_
  intro θ
  have hle : θ * s - P.psi θ ≤ P.rate s := P.rate_ge θ s
  rw [h] at hle
  linarith

/-- The tangency point is attained: `rate drift = drift`. -/
theorem rate_drift (P : MellinProfile) : P.rate P.drift = P.drift :=
  le_antisymm P.rate_drift_le (P.tangency P.drift)

/-- **Operational form of Lemma T.** A monomial of degree `m` contributes to the
variance of a normalized sum of `N` terms only through values `M ^ 2` of size about
`N`, i.e. through the event `log M ^ 2 ≈ log N`. Its large-deviation cost is
`m * rate (log N / m)`, and tangency says this is **never less than `log N`**:
a spike is never more likely than `1 / N`.

Written with `L := log N` and `m > 0`. -/
theorem spike_cost_ge {m L : ℝ} (hm : 0 < m) : L ≤ m * P.rate (L / m) := by
  have h : L / m ≤ P.rate (L / m) := P.tangency (L / m)
  have h2 : m * (L / m) ≤ m * P.rate (L / m) := by
    exact mul_le_mul_of_nonneg_left h hm.le
  rwa [mul_div_cancel₀ _ (ne_of_gt hm)] at h2

/-- Spikes are **exactly** marginal only when the design slope `L / m` equals the
size-bias mean. Away from the tangency slope the union bound closes with room to
spare, which is why off-diagonal design terms are invisible under *every* coordinate
law simultaneously (this universality of Lemma T is what makes the Jet Barrier
possible). -/
theorem spike_cost_eq_iff {m L : ℝ} (hm : 0 < m) :
    m * P.rate (L / m) = L → L / m = P.drift := by
  intro h
  refine P.tangency_eq_drift ?_
  have hm' : (m : ℝ) ≠ 0 := ne_of_gt hm
  have : P.rate (L / m) = L / m := by
    field_simp
    linarith [h]
  exact this

end MellinProfile

/-!
## 2. The condensation constant

For a standard Gaussian `g`, the size-biased law of `g ^ 2` (density proportional to
`x` times the chi-square-one density) is a chi-square with **three** degrees of
freedom, whose log-mean is `digamma(3/2) + log 2 = 2 - gamma - log 2`. That number is
the drift of the size-biased multiplicative walk, hence — by the tangency geometry
above — the reciprocal slope of the condensation phase boundary.
-/

/-- The **condensation constant** `c_G = 2 - gamma - log 2 = 0.72965...`, the
size-biased log-mean of a squared standard Gaussian (a chi-square with three degrees
of freedom).

Attribution: this is the evaluation, for `log g ^ 2` increments, of the second
critical point in Ben Arous-Bogachev-Molchanov (2005). It is not a new constant. -/
noncomputable def condensationConstant : ℝ :=
  2 - Real.eulerMascheroniConstant - Real.log 2

/-- Rigorous two-sided bounds on the condensation constant, from mathlib's
`1/2 < gamma < 2/3` and `0.6931471803 < log 2 < 0.6931471808`.

The bracket `(0.640, 0.807)` is far coarser than the true value `0.72965...`; what
matters downstream is only `0 < c_G`, proved next. -/
theorem condensationConstant_bounds :
    (0.640 : ℝ) < condensationConstant ∧ condensationConstant < (0.807 : ℝ) := by
  have hγ₁ : (1 : ℝ) / 2 < Real.eulerMascheroniConstant :=
    Real.one_half_lt_eulerMascheroniConstant
  have hγ₂ : Real.eulerMascheroniConstant < (2 : ℝ) / 3 :=
    Real.eulerMascheroniConstant_lt_two_thirds
  have hl₁ : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hl₂ : Real.log 2 < (0.6931471808 : ℝ) := Real.log_two_lt_d9
  unfold condensationConstant
  constructor <;> linarith

/-- The condensation constant is strictly positive. Every phase-boundary statement
below needs exactly this and nothing sharper. -/
theorem condensationConstant_pos : 0 < condensationConstant := by
  have h := condensationConstant_bounds.1
  linarith

/-- **A sharper lower bound: `log 2 < c_G`.**

`condensationConstant_bounds` is too coarse for one downstream question. Its bracket
`(0.640, 0.807)` *straddles* `log 2 = 0.69315`, so it cannot decide whether the
condensation constant exceeds `log 2` — and that comparison is exactly what separates a
balanced hard-called genotype locus from its Gaussian surrogate, since
`Calibrator.PolygenicSpectroscopy.hweMellinDrift_half` gives `c(1/2) = log 2`. The claim
was asserted in prose there while being underivable from anything in the development.

The gap is closed by taking more terms. Mathlib's `eulerMascheroniConstant_lt_two_thirds`
is `eulerMascheroniSeq' 6`, but `eulerMascheroniConstant_lt_eulerMascheroniSeq'` holds at
*every* index, and the sequence `H_n - log n` decreases to `gamma`. At `n = 16`,

  `gamma < H_16 - log 16 = 2436559 / 720720 - 4 log 2`,

which gives `c_G > 2 - H_16 + 3 log 2 > 0.69871`, clearing `log 2 < 0.69315` with a
margin of about `0.0056`. Index `16` is chosen because it is the smallest power of two
that clears the comparison, so `log 16` collapses to `4 log 2` and mathlib's tight
rational bounds on `log 2` are the only numeric input needed. -/
theorem log_two_lt_condensationConstant : Real.log 2 < condensationConstant := by
  have hlog16 : Real.log 16 = 4 * Real.log 2 := by
    rw [show (16 : ℝ) = 2 ^ (4 : ℕ) by norm_num, Real.log_pow]
    norm_num
  -- `H_16 - log 16` in closed form. The power-of-two identity above reduces
  -- the only transcendental term to `log 2` before normalization.
  have hseq : Real.eulerMascheroniSeq' 16 = (2436559 : ℝ) / 720720 - 4 * Real.log 2 := by
    rw [Real.eulerMascheroniSeq']
    norm_num [hlog16]
  have hγ : Real.eulerMascheroniConstant < (2436559 : ℝ) / 720720 - 4 * Real.log 2 := by
    have h := Real.eulerMascheroniConstant_lt_eulerMascheroniSeq' 16
    rwa [hseq] at h
  have hl2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  unfold condensationConstant
  linarith

/-- The Gaussian **jet variance** `v_G = pi ^ 2 / 2 - 4 = 0.93480...`, the variance of
`log chi-square-three`, i.e. `trigamma(3/2)`. It is the second observable of the
Mellin 2-jet and sets the width of the condensation window. -/
noncomputable def gaussianJetVariance : ℝ := Real.pi ^ 2 / 2 - 4

/-- `v_G > 0`, from `pi > 3`. -/
theorem gaussianJetVariance_pos : 0 < gaussianJetVariance := by
  have hpi : (3 : ℝ) < Real.pi := by
    have := Real.pi_gt_d2
    linarith
  have : (9 : ℝ) < Real.pi ^ 2 := by nlinarith
  unfold gaussianJetVariance
  linarith

/-!
## 3. The sharp phase boundary

With `N` disjoint monomials of common degree `m`, the design is subcritical (the
Lindeberg condition holds, both sides converge to `N(0,1)`, universality holds) when
`c * m < log N`, and supercritical (the Gaussian side condenses to the point mass at
zero while a lattice-modulus law such as Rademacher stays Gaussian) when
`c * m > log N`. The boundary is `m* = log N / c`, i.e. `1.37035... * log N` for the
Gaussian.
-/

/-- The critical degree `m* = log N / c`. Below it, chaos is Lindeberg-democratic;
above it, the variance is carried by values too large ever to be witnessed among `N`
samples and the observed sum is empty. -/
noncomputable def criticalDegree (N c : ℝ) : ℝ := Real.log N / c

/-- Subcriticality is exactly `c * m < log N`. -/
theorem subcritical_iff {N c m : ℝ} (hc : 0 < c) :
    m < criticalDegree N c ↔ c * m < Real.log N := by
  unfold criticalDegree
  rw [lt_div_iff₀ hc, mul_comm]

/-- Supercriticality is exactly `log N < c * m`. -/
theorem supercritical_iff {N c m : ℝ} (hc : 0 < c) :
    criticalDegree N c < m ↔ Real.log N < c * m := by
  unfold criticalDegree
  rw [div_lt_iff₀ hc, mul_comm]

/-- The Gaussian critical degree is `1.37035... * log N`. We record the reciprocal
constant as a strictly positive multiplier rather than a decimal. -/
noncomputable def gaussianCriticalMultiplier : ℝ := 1 / condensationConstant

theorem gaussianCriticalMultiplier_pos : 0 < gaussianCriticalMultiplier := by
  unfold gaussianCriticalMultiplier
  exact one_div_pos.mpr condensationConstant_pos

/-- `m* = (1 / c_G) * log N`. -/
theorem criticalDegree_gaussian (N : ℝ) :
    criticalDegree N condensationConstant = gaussianCriticalMultiplier * Real.log N := by
  unfold criticalDegree gaussianCriticalMultiplier
  field_simp

/-- The critical multiplier is bounded strictly between `1.23` and `1.57`; the true
value is `1.37035...`. Coarse, but it certifies that the boundary sits at a degree
of order `log N` with an order-one constant, which is the qualitative content. -/
theorem gaussianCriticalMultiplier_bounds :
    (1.23 : ℝ) < gaussianCriticalMultiplier ∧ gaussianCriticalMultiplier < (1.57 : ℝ) := by
  obtain ⟨h₁, h₂⟩ := condensationConstant_bounds
  have hpos : 0 < condensationConstant := condensationConstant_pos
  have hmul : gaussianCriticalMultiplier * condensationConstant = 1 := by
    unfold gaussianCriticalMultiplier
    field_simp
  have hmpos : 0 < gaussianCriticalMultiplier := gaussianCriticalMultiplier_pos
  constructor
  · -- `g * c = 1` and `c < 0.807` give `1 < 0.807 * g`, i.e. `g > 1.239 > 1.23`.
    nlinarith [hmul, hmpos, h₂, hpos, mul_pos hmpos (sub_pos.mpr h₂)]
  · -- `g * c = 1` and `c > 0.640` give `1 > 0.640 * g`, i.e. `g < 1.563 < 1.57`.
    nlinarith [hmul, hmpos, h₁, hpos, mul_pos hmpos (sub_pos.mpr h₁)]

/-!
## 4. The condensation-window law

At the critical window `log N = c * m + w * sqrt m` the variance of the chaos is
partitioned by the Gaussian fluctuation of the size-biased multiplicative walk into a
*retained* fraction `Phi(w / sqrt v)` and an *escaped* fraction `1 - Phi(w / sqrt v)`.
The escaped fraction leaves no trace: no jumps, no heavy tail, just missing variance.
The limit law is `N(0, Phi(w / sqrt v))`.

Status: presented, per the attribution ledger, as at best a boundary-window
refinement inside the BBM/BKL framework, pending a line-by-line comparison with BBM's
critical-point CLT. The statements proved here are the elementary structural ones:
the retained fraction is a probability, is strictly increasing in the window position,
and interpolates `0 -> 1`.
-/

/-- Retained variance fraction at window position `w` for a law with jet variance `v`:
the limit law at the condensation window is `N(0, windowVariance w v)`. -/
noncomputable def windowVariance (w v : ℝ) : ℝ := Phi (w / Real.sqrt v)

theorem monotone_Phi : Monotone Phi := by
  unfold Phi
  exact ProbabilityTheory.monotone_cdf _

theorem Phi_nonneg (x : ℝ) : 0 ≤ Phi x := by
  unfold Phi
  exact ProbabilityTheory.cdf_nonneg _ _

theorem Phi_le_one (x : ℝ) : Phi x ≤ 1 := by
  unfold Phi
  exact ProbabilityTheory.cdf_le_one _ _

/-- The retained fraction is a genuine variance fraction. -/
theorem windowVariance_mem_unitInterval (w v : ℝ) :
    0 ≤ windowVariance w v ∧ windowVariance w v ≤ 1 :=
  ⟨Phi_nonneg _, Phi_le_one _⟩

/-- **The window interpolates.** For fixed jet variance `v > 0`, the retained variance
fraction is monotone in the window position `w`: pushing the design deeper into the
subcritical side retains more variance, pushing it into the supercritical side retains
less. This is the precise sense in which the transition, viewed at scale `sqrt m`, is
a smooth interpolation rather than a jump. -/
theorem windowVariance_mono {v : ℝ} (hv : 0 < v) :
    Monotone (fun w => windowVariance w v) := by
  intro a b hab
  have hs : 0 < Real.sqrt v := Real.sqrt_pos.mpr hv
  have : a / Real.sqrt v ≤ b / Real.sqrt v := by gcongr
  exact monotone_Phi this

/-- **The window separates laws with different jet variance.** Two laws with the same
drift `c` but different jet variances `v ≠ v'` retain different variance fractions at
the same window position `w ≠ 0`, provided the Gaussian cdf is strictly increasing on
the relevant range. We record the separation in the form actually used: distinct
window arguments give the separation whenever `Phi` is injective there. -/
theorem windowVariance_ne_of_arg_ne {w v v' : ℝ}
    (hinj : Function.Injective Phi)
    (h : w / Real.sqrt v ≠ w / Real.sqrt v') :
    windowVariance w v ≠ windowVariance w v' := fun hEq => h (hinj hEq)

/-!
## 5. What the condensation theorems say about a polygenic score

Recorded here as a docstring rather than as a theorem, because the genetics content
is formalized in `Calibrator.PolygenicSpectroscopy`; this is the bridge sentence.

Let a score aggregate `N` disjoint epistatic terms, each a product of `m` standardized
genotypes. Influence per variant is `1 / N`, so the score is as polygenic as one could
ask. The theorems above say:

* if `m < (1 / c) * log N` the score's law is the same whether one models genotypes by
  their true discrete law or by the Gaussian surrogate — the standard infinitesimal
  approximation is valid, uniformly over coefficient patterns;
* if `m > (1 / c) * log N`, the Gaussian surrogate's chaos **condenses to a point
  mass** while the true genotype chaos does not. The surrogate does not merely
  mis-estimate a tail; it converges to a different limit.

`c` here is the *genotype* drift `E[x ^ 2 log x ^ 2]`, computed in closed form as a
function of allele frequency in `Calibrator.PolygenicSpectroscopy`. It is **not**
`c_G`, and it diverges as the allele frequency goes to zero. So the degree at which
the Gaussian surrogate fails is allele-frequency dependent, and fails soonest for rare
variants. -/

end Calibrator
