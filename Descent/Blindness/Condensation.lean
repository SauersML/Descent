/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Foundations.Probability
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace Descent

/-!
# Condensation: the multiplicative obstruction to Gaussian universality of chaos

This file formalizes closed numerical pieces of the proposed condensation geometry.
The general tangency theorem is not exported because its former interface supplied the
Legendre-transform conclusions as structure fields instead of proving them.

## Why this belongs in a polygenic-score development

A polygenic score is a normalized aggregate of many small per-variant contributions.
Every asymptotic statement about the score distribution — the Gaussian score
assumption underlying `Descent.Portability.ScoreDistribution`, liability-threshold
calibration, the Berry-Esseen certificates in `Descent.Foundations.Probability` — is an
instance of the following claim: *a low-influence aggregate of genotypes behaves as
if the genotypes were Gaussian.* For **degree-one** (purely additive) scores this is
true and quantitative (Berry-Esseen). The condensation geometry PROPOSES that it
becomes false for aggregates of diverging multiplicative degree, i.e. for epistatic
scores, and locates the degree at which it fails.

**THAT PROPOSAL IS NOT PROVED IN THIS FILE.** What is formalized here is the closed
constant/window algebra, as the opening line and the attribution block below both say.

What the fifteen theorems below establish, exhaustively:
* numeric bounds and positivity for `condensationConstant = 2 - gamma - log 2` and
  for `gaussianJetVariance = pi ^ 2 / 2 - 4`, from mathlib's Euler-Mascheroni and
  `log 2` brackets -- real results, and the reason this file exists;
* elementary properties of `Phi` (monotone, into `[0,1]`) and of
  `windowVariance = Phi (w / sqrt v)` built from them;
* `criticalDegree N c = log N / c` as a DEFINITION, with `subcritical_iff` and
  `supercritical_iff` relating it to `c * m` -- these are `lt_div_iff₀` and
  `div_lt_iff₀`, i.e. arithmetic, not a phase transition.

NOT ONE THEOREM HERE MENTIONS CHAOS, UNIVERSALITY, OR A LIMIT LAW. `criticalDegree`
is a name given to `log N / c`; that the quantity so named is the boundary of a real
phase transition is the BBM result cited below, not something proved here. The name
carries the physics and the proof carries the arithmetic, and the two must not be
read as one.

What the arithmetic does deliver, and it is a study-design statement rather than a
limit theorem: `subcritical_iff_exp_lt` puts the boundary in panel units, as
`exp (c * m) < N`, and `two_pow_le_gaussian_panel_requirement` shows that requirement
exceeds `2 ^ m` at the Gaussian coupling because `log 2 < condensationConstant`. So
admissible interaction degree grows like the logarithm of the panel, and each further
unit of degree more than doubles the panel needed. That consequence is unconditional
on the transition: it is what the definition costs, whatever the definition turns out
to mark.

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
formalized here is the closed Gaussian constant/window algebra and its direct genetics
specializations. The proposed completeness-of-blindness theorem is not exported.

## Main results in this file

* `condensationConstant` (`c_G = 2 - gamma - log 2`) with rigorous two-sided bounds
  and strict positivity, from mathlib's Euler-Mascheroni and `log 2` bounds.
* `gaussianJetVariance` (`v_G = pi ^ 2 / 2 - 4`) with strict positivity.
* `criticalDegree` and `subcritical_iff` — the algebraic boundary `m* = log N / c`.
  `subcritical_iff` is the division rearrangement `m < log N / c ↔ c * m < log N` and
  nothing more; that this boundary is *sharp* — that the limit laws differ across it —
  is the BBM/BKL analysis, which is not formalized here.
* `windowVariance` and its monotonicity/limits — the condensation-window law
  `N(0, Phi(w / sqrt v))`, whose variance interpolates `0 -> 1` through the error
  function of the window position.
-/

open scoped BigOperators

/-!
## 1. The Mellin profile and the Tangency Lemma

No `MellinProfile` interface is exported. The defining properties of a Legendre
transform — tangency, uniqueness, positive jet variance — are analytic facts that must be
proved from an actual law and an actual transform, not accepted as structure fields.
-/

/-!
## 2. The condensation constant

For a standard Gaussian `g`, the size-biased law of `g ^ 2` (density proportional to
`x` times the chi-square-one density) is a chi-square with **three** degrees of
freedom, whose log-mean is `digamma(3/2) + log 2 = 2 - gamma - log 2`. That number is
the drift of the size-biased multiplicative walk, and — in the BBM phase diagram
cited above, NOT by anything proved in this file — the reciprocal slope of the
condensation phase boundary. No tangency geometry in this file supplies that step; it is
cited from BBM and nothing here discharges it.
-/

/-- The **condensation constant** `c_G = 2 - gamma - log 2 = 0.72965...`, the
size-biased log-mean of a squared standard Gaussian (a chi-square with three degrees
of freedom).

Attribution: this is the evaluation, for `log g ^ 2` increments, of the second
critical point in Ben Arous-Bogachev-Molchanov (2005). It is not a new constant. -/
noncomputable def condensationConstant : ℝ :=
  2 - Real.eulerMascheroniConstant - Real.log 2

/-- Reference evaluation in closed form. -/
theorem condensationConstant_at_reference_point :
    condensationConstant = 2 - Real.eulerMascheroniConstant - Real.log 2 := rfl


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
`Descent.PolygenicSpectroscopy.hweMellinDrift_half` gives `c(1/2) = log 2`. The claim
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

/-- Reference evaluation in closed form. -/
theorem gaussianJetVariance_at_reference_point :
    gaussianJetVariance = Real.pi ^ 2 / 2 - 4 := rfl


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

/-- **criticalDegree at zero c, named.** A zero coupling constant admits no condensation and the
critical degree diverges. Lean returns `0`, reporting that condensation begins at the empty graph.
Consumers must require `c ≠ 0`. -/
theorem criticalDegree_zero_c_is_junk (N : ℝ) :
    criticalDegree N 0 = 0 := by
  unfold criticalDegree
  simp

/-- **The critical degree scales logarithmically in the panel and inversely in the coupling.**
Squaring the panel size doubles the critical degree at fixed coupling, and halving the coupling
doubles it at fixed panel: the two enter at different orders, which is the content a body
multiplying them symmetrically would lose. -/
theorem criticalDegree_square (N c : ℝ) :
    criticalDegree (N ^ 2) c = 2 * criticalDegree N c := by
  unfold criticalDegree
  rw [Real.log_pow]
  push_cast
  ring

theorem criticalDegree_halve_coupling (N c : ℝ) (hc : c ≠ 0) :
    criticalDegree N (c / 2) = 2 * criticalDegree N c := by
  unfold criticalDegree
  field_simp

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

/-- **Subcriticality in panel units: the panel must exceed `exp (c * m)`.**

`subcritical_iff` states the boundary additively, as `c * m < log N`.  Exponentiating
puts it in the units a study is actually designed in, and the shape of the requirement
becomes visible: the admissible interaction degree grows like the LOGARITHM of the
panel, so the panel needed for a given degree grows exponentially in that degree.

This is arithmetic about the defined quantity `criticalDegree`, exactly as
`subcritical_iff` is.  That the quantity so named is where a real transition occurs is
the cited BBM result and is not proved here; what is proved is what the definition
costs in sample size. -/
theorem subcritical_iff_exp_lt {N c m : ℝ} (hc : 0 < c) (hN : 0 < N) :
    m < criticalDegree N c ↔ Real.exp (c * m) < N := by
  rw [subcritical_iff hc, Real.lt_log_iff_exp_lt hN]

/-- **Each unit of interaction degree more than doubles the panel required.**

At the Gaussian coupling the panel must exceed `exp (condensationConstant * m)`, and
`log 2 < condensationConstant` (`log_two_lt_condensationConstant`), so that requirement
is at least `2 ^ m`.

For a polygenic score this is the design statement behind the arc.  A purely additive
score is degree one and costs nothing here.  Admitting interactions of multiplicative
degree `m` — pairwise is `m = 2`, three-way is `m = 3` — requires a panel exponential in
`m` before the aggregate is even in the regime where a Gaussian score assumption could
hold.  Degree, not variant count, is what the panel has to outrun. -/
theorem two_pow_le_gaussian_panel_requirement (m : ℝ) (hm : 0 ≤ m) :
    (2 : ℝ) ^ m ≤ Real.exp (condensationConstant * m) := by
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  exact Real.exp_le_exp.2
    (mul_le_mul_of_nonneg_right (le_of_lt log_two_lt_condensationConstant) hm)

/-- The Gaussian critical degree is `1.37035... * log N`. We record the reciprocal
constant as a strictly positive multiplier rather than a decimal. -/
noncomputable def gaussianCriticalMultiplier : ℝ := 1 / condensationConstant

/-- Reference evaluation; see `Descent.Core.Ratios` for what these pin and why. -/
theorem gaussianCriticalMultiplier_at_reference_point :
    1 / gaussianCriticalMultiplier = 2 - Real.eulerMascheroniConstant - Real.log 2 := by
  unfold gaussianCriticalMultiplier condensationConstant
  rw [one_div_one_div]


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
noncomputable def windowVariance (w v : ℝ) : ℝ := Foundations.Phi (w / Real.sqrt v)

/-- **windowVariance at its junk point, named.** With no spread the standardised coordinate divides
by zero and is junk-zero, so the window probability collapses to `Phi 0` for EVERY half-width.
The dependence on the half-width -- the whole content of the quantity -- disappears silently.
Consumers must exclude the argument that makes the guard vanish. -/
theorem windowVariance_zero_spread_is_junk (w : ℝ) :
    windowVariance w 0 = Foundations.Phi 0 := by
  unfold windowVariance
  simp

/-- **A window at the centre carries half the mass.** Monotonicity in the window width is shared
by every increasing function of `w / sqrt v`; the value at zero is not, and it is what identifies
the standard normal cdf rather than some other sigmoid. -/
theorem windowVariance_zero_window (v : ℝ) : windowVariance 0 v = Foundations.Phi 0 := by
  unfold windowVariance
  norm_num

theorem Phi_nonneg (x : ℝ) : 0 ≤ Foundations.Phi x := by
  unfold Foundations.Phi
  exact ProbabilityTheory.cdf_nonneg _ _

theorem Phi_le_one (x : ℝ) : Foundations.Phi x ≤ 1 := by
  unfold Foundations.Phi
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
    Monotone (fun w ↦ windowVariance w v) := by
  intro a b hab
  have hs : 0 < Real.sqrt v := Real.sqrt_pos.mpr hv
  have : a / Real.sqrt v ≤ b / Real.sqrt v := by gcongr
  exact Foundations.Phi_monotone this

/-!
## 5. What the condensation theorems say about a polygenic score

Recorded here as a docstring rather than as a theorem, because the genetics content
is formalized in `Descent.Spectral.PolygenicSpectroscopy`; this is the bridge sentence.

Let a score aggregate `N` disjoint epistatic terms, each a product of `m` standardized
genotypes. Influence per variant is `1 / N`, so the score is as polygenic as one could
ask. The BBM/BKL phase picture predicts a transition at `m = (1 / c) * log N`, below
which the true and surrogate score laws agree and above which they do not.

**None of that is a theorem of this file.** What is proved above is the constant
algebra (`condensationConstant_bounds`, `gaussianJetVariance_pos`), the division
rearrangement `subcritical_iff`, and the elementary properties of `windowVariance`.
The limit laws on either side of the boundary are the analysis of Ben Arous-Bogachev-
Molchanov, not formalized here, and the direction of the effect — which side condenses
first — has been *measured to be the reverse of the obvious reading* in two of the
regimes tested; see the MEASURED block on
`Descent.PolygenicSpectroscopy.maxSafeEpistaticOrder`.

`c` here is the *genotype* drift `E[x ^ 2 log x ^ 2]`, computed in closed form as a
function of allele frequency in `Descent.Spectral.PolygenicSpectroscopy`. It is **not**
`c_G`, and it diverges as the allele frequency goes to zero. So the degree at which
the Gaussian surrogate fails is allele-frequency dependent, and fails soonest for rare
variants. -/

end Descent
