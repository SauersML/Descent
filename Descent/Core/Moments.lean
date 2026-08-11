/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Core.Parameters

assert_below Descent.Meta Descent.Foundations Descent.Coalescent Descent.Pangenome Descent.PopGen
assert_below Descent.Spectral Descent.Blindness Descent.Conditionals Descent.Portability
assert_below Descent.Decision Descent.Program

/-!
# Core: the moment tuple, and the spine it carries

**Depth 2. Imports `Core.Parameters`, `Core.Fst`, `Core.Ratios`, and nothing else from
this corpus.**

## The interface this file is

`PortabilityMasterTheorem`'s own header states the layer contract:

> Nothing here derives the input moments from a demographic history; that is the job of
> `Descent.PopGen`, and the interface between the two layers is the moment tuple this
> module consumes.

That tuple existed only as an anonymous `ℝ × ℝ × ℝ` inside the Portability layer, at the
top of the import graph, with in-degree zero. So the two layers named an interface that
neither could depend on, and the corpus had **two** theorems composing a demographic
function with a deployed metric -- out of 5,852.

`ScoreMoments` is that tuple, given a name and put at the bottom. `PopGen` produces one
from a demographic history; `Portability` consumes one into `R²`, a calibration slope, a
mean squared error. Neither layer needs the other, and the chain from `(Nₑ, m, μ, t)` to
a deployed metric is a composition of maps rather than a coincidence between two files.

## What a moment tuple is not

It is not a population and not a model. Three numbers -- how much the score varies, how
much it covaries with the outcome, how much the outcome varies -- are all any of the
second-moment metrics can see. That is the content of the minimality results in the
Portability layer, and it is why the interface is exactly this wide: a metric that could
be computed from more would need more, and none of them can.

## Empirical status

The metric laws here are algebra: given the three moments, `R²` IS the squared
covariance over the product of variances. What carries an empirical status is the claim
that a particular demographic history produces a particular tuple, and those claims live
on the named quantities in the subsystem modules with their own ledger rows.
-/

namespace Descent.Core

/-- **The moment tuple a second-moment metric consumes.**

`scoreVariance` is `Var(S)`, `predictiveCovariance` is `Cov(S, Y)`, `outcomeVariance` is
`Var(Y)`. Nothing else is needed to evaluate `R²`, a calibration slope, or a mean squared
error, and nothing else is available to them. -/
structure ScoreMoments where
  /-- `Var(S)`: how much the deployed score varies in this population. -/
  scoreVariance : ℝ
  /-- `Cov(S, Y)`: how much the score co-varies with the outcome. -/
  predictiveCovariance : ℝ
  /-- `Var(Y)`: how much the outcome varies. -/
  outcomeVariance : ℝ

namespace ScoreMoments

/-- **A tuple a metric can actually be read off.** Both variances strictly positive, and
the covariance within the Cauchy--Schwarz bound that any genuine pair of random variables
satisfies. A tuple failing this is not a population's moments, and every metric bound
below assumes it. -/
structure Admissible (m : ScoreMoments) : Prop where
  /-- A score that does not vary predicts nothing and has no calibration slope. -/
  scoreVariance_pos : 0 < m.scoreVariance
  /-- An outcome that does not vary has no variance to explain. -/
  outcomeVariance_pos : 0 < m.outcomeVariance
  /-- Cauchy--Schwarz. Not an assumption about the model: it holds for any two
  square-integrable random variables, and a tuple violating it did not come from a pair. -/
  cauchy_schwarz : m.predictiveCovariance ^ 2 ≤ m.scoreVariance * m.outcomeVariance

/-- **The tuple is inhabited, admissibly.** A theorem quantified over an uninhabited
structure is true and empty.

    Empirical status: NOT AN EMPIRICAL CLAIM -- this is a SHAPE, not a quantity.
    A kernel asserts nothing about a population, so no measurement can bear on it.
    What can be measured is a named quantity claiming this shape computes it, and
    those live in the subsystem modules with their own status lines and ledger rows. -/
noncomputable def witness : ScoreMoments where
  scoreVariance := 1
  predictiveCovariance := 1 / 2
  outcomeVariance := 1

/-- The witness satisfies the admissibility it is a witness for. -/
theorem witness_admissible : Admissible witness where
  scoreVariance_pos := by norm_num [witness]
  outcomeVariance_pos := by norm_num [witness]
  cauchy_schwarz := by norm_num [witness]

/-! ### The metric laws

Each is a closed expression in the three moments. There is no source law and no target
law: portability is two evaluations of one map, which is the whole reason the tuple is
the interface. -/

/-- **Deployed `R²`**, `Cov(S,Y)² / (Var(S) · Var(Y))`.

    Empirical status: NOT AN EMPIRICAL CLAIM -- this is a SHAPE, not a quantity.
    A kernel asserts nothing about a population, so no measurement can bear on it.
    What can be measured is a named quantity claiming this shape computes it, and
    those live in the subsystem modules with their own status lines and ledger rows. -/
noncomputable def r2 (m : ScoreMoments) : ℝ :=
  m.predictiveCovariance ^ 2 / (m.scoreVariance * m.outcomeVariance)

/-- **Calibration slope**, `Cov(S,Y) / Var(S)`: the coefficient a regression of the
outcome on the deployed score would fit. One means the score is on the right scale.

    Empirical status: NOT AN EMPIRICAL CLAIM -- this is a SHAPE, not a quantity.
    A kernel asserts nothing about a population, so no measurement can bear on it.
    What can be measured is a named quantity claiming this shape computes it, and
    those live in the subsystem modules with their own status lines and ledger rows. -/
noncomputable def calibrationSlope (m : ScoreMoments) : ℝ :=
  ratio m.predictiveCovariance m.scoreVariance

/-- **Mean squared error of the raw score**, `Var(Y) - 2Cov(S,Y) + Var(S)`, for a score
already centred on the outcome's mean.

    Empirical status: NOT AN EMPIRICAL CLAIM -- this is a SHAPE, not a quantity.
    A kernel asserts nothing about a population, so no measurement can bear on it.
    What can be measured is a named quantity claiming this shape computes it, and
    those live in the subsystem modules with their own status lines and ledger rows. -/
noncomputable def mse (m : ScoreMoments) : ℝ :=
  m.outcomeVariance - 2 * m.predictiveCovariance + m.scoreVariance

/-- **`R²` lands in the unit interval on an admissible tuple.** The bound every consumer
needs, proved once here rather than re-derived at each metric. -/
theorem r2_mem_unit (m : ScoreMoments) (h : m.Admissible) :
    0 ≤ m.r2 ∧ m.r2 ≤ 1 := by
  have hs := h.scoreVariance_pos
  have ho := h.outcomeVariance_pos
  have hprod : 0 < m.scoreVariance * m.outcomeVariance := mul_pos hs ho
  unfold r2
  constructor
  · positivity
  · rw [div_le_one hprod]
    exact h.cauchy_schwarz

/-- **A perfectly calibrated score has slope one**, which is the statement that fixes
what "calibrated" means for this tuple. -/
theorem calibrationSlope_eq_one_iff (m : ScoreMoments) (h : 0 < m.scoreVariance) :
    m.calibrationSlope = 1 ↔ m.predictiveCovariance = m.scoreVariance := by
  unfold calibrationSlope ratio
  rw [div_eq_one_iff_eq (ne_of_gt h)]

/-- **`R²` is the slope times the covariance-to-outcome-variance ratio.** The algebraic
relation between the two metrics, which is what makes a statement about one transfer to
the other. -/
theorem r2_eq_slope_mul (m : ScoreMoments) (h : 0 < m.scoreVariance) :
    m.r2 = m.calibrationSlope * (m.predictiveCovariance / m.outcomeVariance) := by
  unfold r2 calibrationSlope ratio
  rcases eq_or_ne m.outcomeVariance 0 with ho | ho
  · rw [ho]; simp
  · field_simp

/-! ### The spine: a demographic history produces a moment tuple

This is the composition the corpus had two instances of. `momentsUnderDrift` is the map
`PopGen` supplies and `Portability` consumes; every theorem below it is a link in the
chain `(Nₑ, m, μ) → F_ST → moments → metric`. -/

/-- **The moment tuple of a source-trained score deployed at differentiation `F_ST`.**

The score's causal weights were fitted in the source; in the target, allele frequencies
have drifted apart, and the covariance a score retains is eroded by `1 - F_ST`. Both the
score variance, the predictive covariance AND the additive part of the outcome variance
all carry that factor: the target's own additive variance is eroded by the same drift,
so `Var(Y) = V_A(1 - F) + V_E` and not `V_A + V_E`. Getting that wrong inflates the
denominator and understates the deployed `R²` -- it is the difference between dividing by
the ancestral additive variance and by the target's.

This is the drift regime and it says so: no selection, no gene-environment interaction,
no effect turnover, and the same causal variants in both populations. Those are the
assumptions under which `1 - F_ST` is the whole story, and the Portability layer's
turnover and context terms are what carry the rest.

    Empirical status: NOT AN EMPIRICAL CLAIM -- this is a SHAPE, not a quantity.
    A kernel asserts nothing about a population, so no measurement can bear on it.
    What can be measured is a named quantity claiming this shape computes it, and
    those live in the subsystem modules with their own status lines and ledger rows. -/
noncomputable def momentsUnderDrift (V_A V_E fst : ℝ) : ScoreMoments where
  scoreVariance := retainedFraction fst V_A
  predictiveCovariance := retainedFraction fst V_A
  outcomeVariance := retainedFraction fst V_A + V_E

/-- **The deployed `R²` under drift, from the tuple.** `V_A(1-F)/(V_A + V_E)`: the
familiar law, but now as a consequence of the moment interface rather than as a formula
written next to it. -/
theorem r2_momentsUnderDrift (V_A V_E fst : ℝ) (hV : 0 < V_A) (hE : 0 ≤ V_E)
    (hf : fst < 1) :
    (momentsUnderDrift V_A V_E fst).r2
      = share (retainedFraction fst V_A) V_E := by
  have hr : 0 < retainedFraction fst V_A := by
    unfold retainedFraction; nlinarith
  have hy : 0 < retainedFraction fst V_A + V_E := by linarith
  unfold r2 momentsUnderDrift share
  simp only
  field_simp

/-- **A source-trained score is perfectly calibrated in its own population.** At
`F_ST = 0` the slope is one; this is the anchor the whole drift law is a departure
from. -/
theorem calibrationSlope_momentsUnderDrift_at_zero (V_A V_E : ℝ) (hV : 0 < V_A) :
    (momentsUnderDrift V_A V_E 0).calibrationSlope = 1 := by
  unfold calibrationSlope momentsUnderDrift ratio retainedFraction
  simp only
  field_simp

/-- **The slope is one at every differentiation, and that is the point.**

Drift erodes the score's variance and its predictive covariance by the SAME factor, so
their ratio -- the calibration slope -- does not move. A polygenic score that transfers
badly in `R²` can be perfectly calibrated in the target, and this theorem is why: the two
metrics see different functions of the same tuple. A deployment judged only by
calibration would report no problem at all. -/
theorem calibrationSlope_momentsUnderDrift (V_A V_E fst : ℝ) (hV : 0 < V_A)
    (hf : fst < 1) :
    (momentsUnderDrift V_A V_E fst).calibrationSlope = 1 := by
  have hr : retainedFraction fst V_A ≠ 0 := by
    unfold retainedFraction; intro hc; nlinarith [hc]
  unfold calibrationSlope momentsUnderDrift ratio
  simp only
  exact div_self hr

/-- **More differentiation, less transferred `R²`.** The monotone law the whole
demography-to-metric chain exists to state, at the level of the tuple.

`V_E` must be STRICTLY positive, and that is not a technical convenience. At `V_E = 0`
the trait is purely additive, the score explains all of it, and `R² = 1` at every
differentiation -- drift erodes the numerator and the denominator by exactly the same
factor and they cancel. So the monotone law is a statement about traits with environmental variance,
and a corpus that stated it without the hypothesis would be
claiming portability loss for a case that has none. -/
theorem r2_momentsUnderDrift_anti (V_A V_E f₁ f₂ : ℝ) (hV : 0 < V_A) (hE : 0 < V_E)
    (h1 : f₁ < f₂) (h2 : f₂ < 1) :
    (momentsUnderDrift V_A V_E f₂).r2 < (momentsUnderDrift V_A V_E f₁).r2 := by
  rw [r2_momentsUnderDrift V_A V_E f₁ hV (le_of_lt hE) (by linarith),
    r2_momentsUnderDrift V_A V_E f₂ hV (le_of_lt hE) h2]
  have h1' : 0 < retainedFraction f₂ V_A := by unfold retainedFraction; nlinarith
  have h2' : retainedFraction f₂ V_A < retainedFraction f₁ V_A := by
    unfold retainedFraction; nlinarith
  have hb1 : 0 < retainedFraction f₂ V_A + V_E := by linarith
  have hb2 : 0 < retainedFraction f₁ V_A + V_E := by linarith
  unfold share
  rw [div_lt_div_iff₀ hb1 hb2]
  nlinarith

/-- **A purely additive trait transfers perfectly, whatever the differentiation.** The
boundary the monotone law excludes, stated rather than left implicit: at `V_E = 0` drift
erodes numerator and denominator alike and `R²` is `1` at every `F_ST`. -/
theorem r2_momentsUnderDrift_of_no_environment (V_A fst : ℝ) (hV : 0 < V_A)
    (hf : fst < 1) :
    (momentsUnderDrift V_A 0 fst).r2 = 1 := by
  have hr : 0 < retainedFraction fst V_A := by unfold retainedFraction; nlinarith
  rw [r2_momentsUnderDrift V_A 0 fst hV le_rfl hf]
  unfold share
  field_simp
  ring

/-! ### The chain, link by link

Each theorem below is one claim about how a demographic parameter reaches a deployed
metric. They are separate rather than bundled because they fail separately: a corpus
that proves only "R² decreases with F_ST" has not said which demographic parameters move
F_ST, in which direction, or what the metric does at the boundaries. -/

/-- **Source `R²` is the trait's heritability.** At no differentiation the score is
deployed in the population it was fitted in, and the metric it reports is
`V_A/(V_A + V_E)`. Every portability statement below is a departure from this. -/
theorem r2_momentsUnderDrift_at_source (V_A V_E : ℝ) (hV : 0 < V_A) (hE : 0 ≤ V_E) :
    (momentsUnderDrift V_A V_E 0).r2 = share V_A V_E := by
  rw [r2_momentsUnderDrift V_A V_E 0 hV hE (by norm_num)]
  unfold retainedFraction
  ring_nf

/-- **Complete differentiation transfers nothing.** At `F_ST = 1` the retained covariance
is zero and the deployed `R²` is zero -- the score is uncorrelated with the outcome in a
population sharing no allele frequencies with the one it was fitted in. -/
theorem r2_momentsUnderDrift_at_complete (V_A V_E : ℝ) (hE : 0 < V_E) :
    (momentsUnderDrift V_A V_E 1).r2 = 0 := by
  unfold r2 momentsUnderDrift retainedFraction
  simp

/-- **The deployed metric never exceeds the source metric.** The one-sided statement:
drift can only cost, and the corpus's portability results are all bounded by this. -/
theorem r2_momentsUnderDrift_le_source (V_A V_E fst : ℝ) (hV : 0 < V_A) (hE : 0 ≤ V_E)
    (hf0 : 0 ≤ fst) (hf : fst < 1) :
    (momentsUnderDrift V_A V_E fst).r2 ≤ (momentsUnderDrift V_A V_E 0).r2 := by
  rw [r2_momentsUnderDrift V_A V_E fst hV hE hf,
    r2_momentsUnderDrift V_A V_E 0 hV hE (by norm_num)]
  have hr : 0 < retainedFraction fst V_A := by unfold retainedFraction; nlinarith
  have hr0 : retainedFraction fst V_A ≤ retainedFraction 0 V_A := by
    unfold retainedFraction; nlinarith
  unfold share
  rw [div_le_div_iff₀ (by linarith) (by unfold retainedFraction; nlinarith)]
  nlinarith

/-- **The portability ratio.** Deployed `R²` against source `R²` -- the quantity the
literature reports and the one this whole development is about.

    Empirical status: NOT AN EMPIRICAL CLAIM -- this is a SHAPE, not a quantity.
    A kernel asserts nothing about a population, so no measurement can bear on it.
    What can be measured is a named quantity claiming this shape computes it, and
    those live in the subsystem modules with their own status lines and ledger rows. -/
noncomputable def portabilityRatio (V_A V_E fst : ℝ) : ℝ :=
  ratio (momentsUnderDrift V_A V_E fst).r2 (momentsUnderDrift V_A V_E 0).r2

/-- **The portability ratio lies in the unit interval**, which is the content of the
one-sided bound above transported to the ratio. -/
theorem portabilityRatio_mem_unit (V_A V_E fst : ℝ) (hV : 0 < V_A) (hE : 0 ≤ V_E)
    (hf0 : 0 ≤ fst) (hf : fst < 1) :
    0 ≤ portabilityRatio V_A V_E fst ∧ portabilityRatio V_A V_E fst ≤ 1 := by
  have hsrc : 0 < (momentsUnderDrift V_A V_E 0).r2 := by
    rw [r2_momentsUnderDrift V_A V_E 0 hV hE (by norm_num)]
    unfold share retainedFraction
    have : (0:ℝ) < (1 - 0) * V_A := by nlinarith
    positivity
  have hdep : 0 ≤ (momentsUnderDrift V_A V_E fst).r2 :=
    ((momentsUnderDrift V_A V_E fst).r2_mem_unit
      { scoreVariance_pos := by unfold momentsUnderDrift retainedFraction; simp; nlinarith
        outcomeVariance_pos := by
          unfold momentsUnderDrift retainedFraction; simp; nlinarith
        cauchy_schwarz := by
          unfold momentsUnderDrift retainedFraction; simp
          nlinarith [sq_nonneg ((1 - fst) * V_A), mul_nonneg (le_of_lt hV) hE] }).1
  unfold portabilityRatio ratio
  refine ⟨div_nonneg hdep (le_of_lt hsrc), ?_⟩
  rw [div_le_one hsrc]
  exact r2_momentsUnderDrift_le_source V_A V_E fst hV hE hf0 hf

/-- **The portability ratio is one exactly at no differentiation** on a trait with environmental
variance. A reported ratio below one is therefore evidence of
differentiation and not of a measurement artefact. -/
theorem portabilityRatio_at_source (V_A V_E : ℝ) (hV : 0 < V_A) (hE : 0 ≤ V_E) :
    portabilityRatio V_A V_E 0 = 1 := by
  have hsrc : (0:ℝ) < (momentsUnderDrift V_A V_E 0).r2 := by
    rw [r2_momentsUnderDrift V_A V_E 0 hV hE (by norm_num)]
    unfold share retainedFraction
    have : (0:ℝ) < (1 - 0) * V_A := by nlinarith
    positivity
  unfold portabilityRatio ratio
  exact div_self (ne_of_gt hsrc)

/-! ### Which demographic parameters move the metric, and in which direction -/

/-! ### The chain in split coordinates

The other route into `F_ST`: a clean split at time `t`, read through `τ/(1 + τ)` rather
than through a migration-mutation equilibrium. Both produce a differentiation, and the
same moment tuple consumes either. -/

/-- **Deployed `R²` after a clean split**, from the scaled coalescence time. Written
through `fstFromTau` so that this and the equilibrium route cannot acquire different
`F_ST` conventions: both are Hudson.

    Empirical status: NOT AN EMPIRICAL CLAIM -- this is a SHAPE, not a quantity.
    A kernel asserts nothing about a population, so no measurement can bear on it.
    What can be measured is a named quantity claiming this shape computes it, and
    those live in the subsystem modules with their own status lines and ledger rows. -/
noncomputable def deployedR2FromTau (V_A V_E : ℝ) (t : Tau) : ℝ :=
  (momentsUnderDrift V_A V_E (fstFromTau t)).r2

/-- **A longer split transfers less.** Monotone in the scaled coalescence time, which is
monotone in the divergence time at fixed effective size -- so the deployed metric decays
with time since the split. -/
theorem deployedR2FromTau_anti (V_A V_E : ℝ) (t₁ t₂ : Tau) (hV : 0 < V_A) (hE : 0 < V_E)
    (h0 : 0 ≤ t₁.value) (hlt : t₁.value < t₂.value) :
    deployedR2FromTau V_A V_E t₂ < deployedR2FromTau V_A V_E t₁ := by
  have hf1 := fstFromTau_lt_fstFromTau t₁ t₂ h0 hlt
  have hlt2 := fstFromTau_lt_one t₂ (by linarith)
  exact r2_momentsUnderDrift_anti V_A V_E (fstFromTau t₁) (fstFromTau t₂) hV hE hf1 hlt2

/-- **At the moment of the split nothing has been lost.** `τ = 0` gives `F_ST = 0` and
the deployed metric is the heritability. -/
theorem deployedR2FromTau_at_zero (V_A V_E : ℝ) (hV : 0 < V_A) (hE : 0 ≤ V_E) :
    deployedR2FromTau V_A V_E ⟨0⟩ = share V_A V_E := by
  unfold deployedR2FromTau fstFromTau saturation
  norm_num
  exact r2_momentsUnderDrift_at_source V_A V_E hV hE

/-! ### The full chain

`(Nₑ, m, μ) → F_ST → moments → R²`, as one composition. -/

/-- **Deployed `R²` from a demographic history.** The composition of
`PopGenParameters.fstEquilibrium` with `momentsUnderDrift` with `r2`: three named maps,
one function from a demography to a metric.

This is the object the corpus had no name for. Its `PopGen` layer computed `F_ST` from
`(Nₑ, m, μ, t)` and its `Portability` layer computed `R²` from moment tuples, and the two
were joined by two theorems out of 5,852 -- everything else took `fst` as a free real,
severing the metric from the population genetics meant to produce it.

    Empirical status: NOT AN EMPIRICAL CLAIM -- this is a SHAPE, not a quantity.
    A kernel asserts nothing about a population, so no measurement can bear on it.
    What can be measured is a named quantity claiming this shape computes it, and
    those live in the subsystem modules with their own status lines and ledger rows. -/
noncomputable def deployedR2 (p : PopGenParameters) (V_E : ℝ) : ℝ :=
  (momentsUnderDrift p.V_A V_E p.fstEquilibrium).r2

/-- **The chain, evaluated.** `V_A(1-F) / (V_A(1-F) + V_E)` where `F` is the equilibrium
the parameters determine, not a number supplied by the caller. -/
theorem deployedR2_eq (p : PopGenParameters) (V_E : ℝ) (hE : 0 ≤ V_E)
    (hflow : 0 < p.mu + p.mig) :
    deployedR2 p V_E
      = share (retainedFraction p.fstEquilibrium p.V_A) V_E :=
  r2_momentsUnderDrift p.V_A V_E p.fstEquilibrium p.V_A_pos hE
    (p.fstEquilibrium_lt_one hflow)

/-- **The two routes into the metric agree when they agree on `F_ST`.** Stated because
the corpus computes `F_ST` two ways -- an equilibrium under migration and mutation, and a
split law in coalescent time -- and a reader meeting both has no reason to assume the
moment tuple treats them alike. It does: the tuple sees a differentiation and nothing
about where it came from. -/
theorem deployedR2_eq_deployedR2FromTau (p : PopGenParameters) (V_E : ℝ) (t : Tau)
    (h : p.fstEquilibrium = fstFromTau t) :
    deployedR2 p V_E = deployedR2FromTau p.V_A V_E t := by
  unfold deployedR2 deployedR2FromTau
  rw [h]

/-- **And that is a real constraint, not a tautology**: the two routes agree on `F_ST`
exactly when the scaled coalescence time is the reciprocal of the total scaled flow.
`τ = 1/x` is the conversion between the corpus's two `F_ST` coordinates, and it is
recorded here rather than left for a reader to rediscover.

The flow is `scaledFlow`, which carries the deme correction. Written as `θ + 2M` this is
that flow at two demes and no other lattice size; the conversion is the same map either
way, and the coordinate it converts is the one the record computes. -/
theorem fstEquilibrium_eq_fstFromTau_iff (p : PopGenParameters) (t : Tau)
    (hx : 1 + scaledFlow p.bigM p.theta p.nDemes ≠ 0) (ht : 1 + t.value ≠ 0) :
    p.fstEquilibrium = fstFromTau t ↔
      1 = t.value * scaledFlow p.bigM p.theta p.nDemes := by
  unfold PopGenParameters.fstEquilibrium fstIslandEquilibrium fstFromFlow fstFromTau
    saturation
  rw [div_eq_div_iff hx ht]
  constructor <;> intro h <;> nlinarith [h]

/-- **More migration, more transferable score.** The end-to-end monotone law: increase
the migration rate in the demographic parameters and the deployed `R²` goes up, with every step --
equilibrium, moments, metric -- a named map rather than an assumption.

This is the statement the corpus's two layers were built to support and could not make.

Each of these laws now fixes the deme count across the comparison. That hypothesis is
what makes them statements about ONE demographic parameter moving: a comparison that let
the lattice change too would be about two changes, and `deployedR2_anti_in_demes` below
is the separate law for the other one. -/
theorem deployedR2_mono_in_migration (p q : PopGenParameters) (V_E : ℝ) (hE : 0 < V_E)
    (hNe : p.Ne = q.Ne) (hmu : p.mu = q.mu) (hd : p.nDemes = q.nDemes)
    (hV : p.V_A = q.V_A) (hlt : p.mig < q.mig) (hflow : 0 < p.mu + p.mig) :
    deployedR2 p V_E < deployedR2 q V_E := by
  have hfst : q.fstEquilibrium < p.fstEquilibrium :=
    PopGenParameters.fstEquilibrium_lt_of_mig_lt p q hNe hmu hd hlt
  unfold deployedR2
  rw [hV]
  exact r2_momentsUnderDrift_anti q.V_A V_E q.fstEquilibrium p.fstEquilibrium
    q.V_A_pos hE hfst (p.fstEquilibrium_lt_one hflow)

/-- **More mutation, higher deployed `R²`** -- the second end-to-end law, and one the
corpus could not previously state at all. -/
theorem deployedR2_mono_in_mutation (p q : PopGenParameters) (V_E : ℝ) (hE : 0 < V_E)
    (hNe : p.Ne = q.Ne) (hmig : p.mig = q.mig) (hd : p.nDemes = q.nDemes)
    (hV : p.V_A = q.V_A) (hlt : p.mu < q.mu) (hflow : 0 < p.mu + p.mig) :
    deployedR2 p V_E < deployedR2 q V_E := by
  have hfst : q.fstEquilibrium < p.fstEquilibrium :=
    PopGenParameters.fstEquilibrium_lt_of_mu_lt p q hNe hmig hd hlt
  unfold deployedR2
  rw [hV]
  exact r2_momentsUnderDrift_anti q.V_A V_E q.fstEquilibrium p.fstEquilibrium
    q.V_A_pos hE hfst (p.fstEquilibrium_lt_one hflow)

/-- **Larger effective size, higher deployed `R²`** -- the third.

This used to carry two flow hypotheses, `0 < mu + 2 mig` and `0 < mu + mig`, of which the
first was the two-deme migration coefficient written into an assumption. With the deme
correction carried as a field there is one hypothesis, because `d/(d-1)` is above one at
every admissible record and the two conditions have the same content. -/
theorem deployedR2_mono_in_Ne (p q : PopGenParameters) (V_E : ℝ) (hE : 0 < V_E)
    (hmu : p.mu = q.mu) (hmig : p.mig = q.mig) (hd : p.nDemes = q.nDemes)
    (hV : p.V_A = q.V_A) (hlt : p.Ne < q.Ne) (hflow : 0 < p.mu + p.mig) :
    deployedR2 p V_E < deployedR2 q V_E := by
  have hfst : q.fstEquilibrium < p.fstEquilibrium :=
    PopGenParameters.fstEquilibrium_lt_of_Ne_lt p q hmu hmig hd hflow hlt
  unfold deployedR2
  rw [hV]
  exact r2_momentsUnderDrift_anti q.V_A V_E q.fstEquilibrium p.fstEquilibrium
    q.V_A_pos hE hfst (p.fstEquilibrium_lt_one hflow)

/-- **The deployed metric is in the unit interval for any admissible history.** -/
theorem deployedR2_mem_unit (p : PopGenParameters) (V_E : ℝ) (hE : 0 ≤ V_E)
    (hflow : 0 < p.mu + p.mig) :
    0 ≤ deployedR2 p V_E ∧ deployedR2 p V_E ≤ 1 := by
  have hlt := p.fstEquilibrium_lt_one hflow
  have hge := p.fstEquilibrium_mem_unit.1
  have hr : 0 < retainedFraction p.fstEquilibrium p.V_A := by
    unfold retainedFraction
    have := p.V_A_pos
    nlinarith
  rw [deployedR2_eq p V_E hE hflow]
  unfold share
  constructor
  · positivity
  · rw [div_le_one (by linarith)]; linarith

/-- **The deployed metric never exceeds the heritability.** The ceiling every deployment
is under, expressed in the demographic coordinates: no history makes a score explain more
of the target's variance than the trait's own heritability in the source. -/
theorem deployedR2_le_heritability (p : PopGenParameters) (V_E : ℝ) (hE : 0 ≤ V_E)
    (hflow : 0 < p.mu + p.mig) :
    deployedR2 p V_E ≤ share p.V_A V_E := by
  have hlt := p.fstEquilibrium_lt_one hflow
  have hge := p.fstEquilibrium_mem_unit.1
  have hV := p.V_A_pos
  rw [deployedR2_eq p V_E hE hflow]
  unfold share retainedFraction
  have hnum : 0 < (1 - p.fstEquilibrium) * p.V_A := by nlinarith
  have hd1 : 0 < (1 - p.fstEquilibrium) * p.V_A + V_E := by linarith
  have hd2 : 0 < p.V_A + V_E := by linarith
  rw [div_le_div_iff₀ hd1 hd2]
  nlinarith [mul_nonneg (mul_nonneg hge (le_of_lt hV)) hE]

/-! ### The rest of the metric family

`R²` is one coordinate of a deployment report. A calibration slope, a mean squared error,
a Brier score and an AUC are the others, and they do not move together -- the slope does
not move at all under drift. Each is a function of the same tuple, so each composes with the same
demographic chain, and each needs its own statement. -/

/-- **Mean squared error under drift.** A score whose weights were fitted in the source is
deployed raw in the target: the error is `Var(Y) - 2Cov(S,Y) + Var(S)`, which under drift
collapses to the environmental variance alone. -/
theorem mse_momentsUnderDrift (V_A V_E fst : ℝ) :
    (momentsUnderDrift V_A V_E fst).mse = V_E := by
  unfold mse momentsUnderDrift
  ring

/-- **The raw mean squared error does NOT move with differentiation**, and that is a
finding rather than an accident.

Drift removes signal from the score and the same signal from the outcome, so the residual
is the environmental variance whatever the differentiation. A deployment audited on mean
squared error alone sees a perfectly stable number while `R²` collapses -- the same trap
as the calibration slope, in a second metric. What `R²` reports and MSE does not is how
much of a SHRINKING outcome variance the score accounts for. -/
theorem mse_momentsUnderDrift_const (V_A V_E f₁ f₂ : ℝ) :
    (momentsUnderDrift V_A V_E f₁).mse = (momentsUnderDrift V_A V_E f₂).mse := by
  rw [mse_momentsUnderDrift, mse_momentsUnderDrift]

/-- **Two metrics, three behaviours.** At a differentiation where `R²` has strictly
fallen, the slope and the MSE are unchanged. Stated as a single theorem because the
conjunction is the claim: no one of these numbers is a summary of a deployment. -/
theorem drift_moves_r2_alone (V_A V_E f : ℝ) (hV : 0 < V_A) (hE : 0 < V_E)
    (hf0 : 0 < f) (hf : f < 1) :
    (momentsUnderDrift V_A V_E f).r2 < (momentsUnderDrift V_A V_E 0).r2 ∧
    (momentsUnderDrift V_A V_E f).calibrationSlope
      = (momentsUnderDrift V_A V_E 0).calibrationSlope ∧
    (momentsUnderDrift V_A V_E f).mse = (momentsUnderDrift V_A V_E 0).mse := by
  refine ⟨r2_momentsUnderDrift_anti V_A V_E 0 f hV hE hf0 hf, ?_, ?_⟩
  · rw [calibrationSlope_momentsUnderDrift V_A V_E f hV hf,
      calibrationSlope_momentsUnderDrift V_A V_E 0 hV (by norm_num)]
  · exact mse_momentsUnderDrift_const V_A V_E f 0

/-- **Calibrated Brier score from a tuple and a prevalence**, `π(1-π)(1 - R²)`.

The binary-outcome coordinate. It is a function of the tuple only through `R²`, which is
why every `R²` result above transfers to it -- and why a deployment cannot report a Brier
score that disagrees with its `R²`.

    Empirical status: NOT AN EMPIRICAL CLAIM -- this is a SHAPE, not a quantity.
    A kernel asserts nothing about a population, so no measurement can bear on it.
    What can be measured is a named quantity claiming this shape computes it, and
    those live in the subsystem modules with their own status lines and ledger rows. -/
noncomputable def brier (π : ℝ) (m : ScoreMoments) : ℝ :=
  π * (1 - π) * complement m.r2

/-- **Brier at no information is the prevalence variance.** The baseline a
prevalence-only predictor scores, and the number every improvement is measured
against. -/
theorem brier_at_zero_r2 (π : ℝ) (m : ScoreMoments) (h : m.r2 = 0) :
    brier π m = π * (1 - π) := by
  unfold brier complement
  rw [h]; ring

/-- **Brier is anti-monotone in `R²`.** Lower error where more variance is explained --
the direction that makes it a loss rather than a score. -/
theorem brier_anti_in_r2 (π : ℝ) (m n : ScoreMoments) (hπ : 0 < π) (hπ1 : π < 1)
    (h : m.r2 < n.r2) : brier π n < brier π m := by
  unfold brier complement
  have hp : 0 < π * (1 - π) := by nlinarith
  nlinarith

/-- **More differentiation, worse Brier score.** The chain carried into the binary
coordinate. -/
theorem brier_momentsUnderDrift_mono (π V_A V_E f₁ f₂ : ℝ) (hπ : 0 < π) (hπ1 : π < 1)
    (hV : 0 < V_A) (hE : 0 < V_E) (h1 : f₁ < f₂) (h2 : f₂ < 1) :
    brier π (momentsUnderDrift V_A V_E f₁) < brier π (momentsUnderDrift V_A V_E f₂) :=
  brier_anti_in_r2 π (momentsUnderDrift V_A V_E f₂) (momentsUnderDrift V_A V_E f₁) hπ hπ1
    (r2_momentsUnderDrift_anti V_A V_E f₁ f₂ hV hE h1 h2)

/-- **The AUC argument**, `R² / (1 - R²)`.

The equal-variance Gaussian AUC is `Φ` of a strictly increasing function of this, and `Φ`
is strictly increasing -- so every ordering statement about an AUC is an ordering
statement about this quantity, and can be made without `Φ`, which this corpus has no
Mathlib form for. Writing the argument rather than a wrong closed form is the same
discipline `calibratedBrierFromVariances` records for the liability scale.

    Empirical status: NOT AN EMPIRICAL CLAIM -- this is a SHAPE, not a quantity.
    A kernel asserts nothing about a population, so no measurement can bear on it.
    What can be measured is a named quantity claiming this shape computes it, and
    those live in the subsystem modules with their own status lines and ledger rows. -/
noncomputable def aucArgument (m : ScoreMoments) : ℝ :=
  ratio m.r2 (complement m.r2)

/-- **The AUC argument is strictly increasing in `R²`** on the open unit interval, which
is what carries every `R²` ordering into an AUC ordering. -/
theorem aucArgument_mono (m n : ScoreMoments) (h0 : 0 ≤ m.r2) (h1 : n.r2 < 1)
    (h : m.r2 < n.r2) : aucArgument m < aucArgument n := by
  unfold aucArgument ratio complement
  rw [div_lt_div_iff₀ (by linarith) (by linarith)]
  nlinarith

/-- **More differentiation, lower AUC.** The chain carried into the discrimination
coordinate, by way of the argument rather than by way of a closed form for `Φ`. -/
theorem aucArgument_momentsUnderDrift_anti (V_A V_E f₁ f₂ : ℝ) (hV : 0 < V_A)
    (hE : 0 < V_E) (h1 : f₁ < f₂) (h2 : f₂ < 1) (h0 : 0 ≤ f₁) :
    aucArgument (momentsUnderDrift V_A V_E f₂)
      < aucArgument (momentsUnderDrift V_A V_E f₁) := by
  have hlt := r2_momentsUnderDrift_anti V_A V_E f₁ f₂ hV hE h1 h2
  have hadm : ∀ f : ℝ, f < 1 → (momentsUnderDrift V_A V_E f).Admissible := by
    intro f hf
    refine { scoreVariance_pos := ?_, outcomeVariance_pos := ?_, cauchy_schwarz := ?_ } <;>
      unfold momentsUnderDrift retainedFraction <;> simp
    · nlinarith
    · nlinarith
    · nlinarith [sq_nonneg ((1 - f) * V_A), mul_nonneg (le_of_lt hV) (le_of_lt hE)]
  have hn1 : (momentsUnderDrift V_A V_E f₁).r2 < 1 := by
    rw [r2_momentsUnderDrift V_A V_E f₁ hV (le_of_lt hE) (by linarith)]
    unfold share retainedFraction
    rw [div_lt_one (by nlinarith)]
    linarith
  exact aucArgument_mono _ _ (r2_mem_unit _ (hadm f₂ h2)).1 hn1 hlt

/-! ### The whole family, composed with a demographic history

Each of the four metrics, evaluated on the tuple a demographic history produces. These
are the compositions the layer contract promised. -/

/-- **Deployed calibration slope from a demographic history.** One at every history with some flow
-- which is the sharpest form of the warning: no demographic history produces a
miscalibrated score under pure drift, so calibration cannot detect this failure mode. -/
theorem deployedSlope_eq_one (p : PopGenParameters) (V_E : ℝ)
    (hflow : 0 < p.mu + p.mig) :
    (momentsUnderDrift p.V_A V_E p.fstEquilibrium).calibrationSlope = 1 :=
  calibrationSlope_momentsUnderDrift p.V_A V_E p.fstEquilibrium p.V_A_pos
    (p.fstEquilibrium_lt_one hflow)

/-- **Deployed mean squared error from a demographic history** is the environmental
variance, whatever the history. The second metric the chain leaves flat. -/
theorem deployedMse_eq (p : PopGenParameters) (V_E : ℝ) :
    (momentsUnderDrift p.V_A V_E p.fstEquilibrium).mse = V_E :=
  mse_momentsUnderDrift p.V_A V_E p.fstEquilibrium

/-- **Deployed Brier score from a demographic history.**

    Empirical status: NOT AN EMPIRICAL CLAIM -- this is a SHAPE, not a quantity.
    A kernel asserts nothing about a population, so no measurement can bear on it.
    What can be measured is a named quantity claiming this shape computes it, and
    those live in the subsystem modules with their own status lines and ledger rows. -/
noncomputable def deployedBrier (π : ℝ) (p : PopGenParameters) (V_E : ℝ) : ℝ :=
  brier π (momentsUnderDrift p.V_A V_E p.fstEquilibrium)

/-- **Any change that lowers the equilibrium `F_ST` improves the Brier score.**

The three monotonicity results below -- in migration, in mutation and in effective size
-- had identical eight-line bodies differing only in which `fstEquilibrium_lt_of_*`
lemma they cited, and the duplication guard reported the block three times. The
demography enters ONLY through that inequality, which is the content worth stating: the
Brier score does not care which parameter moved. -/
theorem deployedBrier_anti_of_fstEquilibrium_lt (π : ℝ) (p q : PopGenParameters)
    (V_E : ℝ) (hπ : 0 < π) (hπ1 : π < 1) (hE : 0 < V_E) (hV : p.V_A = q.V_A)
    (hfst : q.fstEquilibrium < p.fstEquilibrium) (hone : p.fstEquilibrium < 1) :
    deployedBrier π q V_E < deployedBrier π p V_E := by
  unfold deployedBrier
  rw [hV]
  exact brier_anti_in_r2 π _ _ hπ hπ1
    (r2_momentsUnderDrift_anti q.V_A V_E q.fstEquilibrium p.fstEquilibrium q.V_A_pos hE
      hfst hone)

/-- **More migration, better Brier score.** -/
theorem deployedBrier_mono_in_migration (π : ℝ) (p q : PopGenParameters) (V_E : ℝ)
    (hπ : 0 < π) (hπ1 : π < 1) (hE : 0 < V_E)
    (hNe : p.Ne = q.Ne) (hmu : p.mu = q.mu) (hd : p.nDemes = q.nDemes)
    (hV : p.V_A = q.V_A) (hlt : p.mig < q.mig) (hflow : 0 < p.mu + p.mig) :
    deployedBrier π q V_E < deployedBrier π p V_E := by
  exact deployedBrier_anti_of_fstEquilibrium_lt π p q V_E hπ hπ1 hE hV
    (PopGenParameters.fstEquilibrium_lt_of_mig_lt p q hNe hmu hd hlt)
    (p.fstEquilibrium_lt_one hflow)

/-- **More mutation, better Brier score.** -/
theorem deployedBrier_mono_in_mutation (π : ℝ) (p q : PopGenParameters) (V_E : ℝ)
    (hπ : 0 < π) (hπ1 : π < 1) (hE : 0 < V_E)
    (hNe : p.Ne = q.Ne) (hmig : p.mig = q.mig) (hd : p.nDemes = q.nDemes)
    (hV : p.V_A = q.V_A) (hlt : p.mu < q.mu) (hflow : 0 < p.mu + p.mig) :
    deployedBrier π q V_E < deployedBrier π p V_E := by
  exact deployedBrier_anti_of_fstEquilibrium_lt π p q V_E hπ hπ1 hE hV
    (PopGenParameters.fstEquilibrium_lt_of_mu_lt p q hNe hmig hd hlt)
    (p.fstEquilibrium_lt_one hflow)

/-- **Larger effective size, better Brier score.** -/
theorem deployedBrier_mono_in_Ne (π : ℝ) (p q : PopGenParameters) (V_E : ℝ)
    (hπ : 0 < π) (hπ1 : π < 1) (hE : 0 < V_E)
    (hmu : p.mu = q.mu) (hmig : p.mig = q.mig) (hd : p.nDemes = q.nDemes)
    (hV : p.V_A = q.V_A) (hlt : p.Ne < q.Ne) (hflow : 0 < p.mu + p.mig) :
    deployedBrier π q V_E < deployedBrier π p V_E := by
  exact deployedBrier_anti_of_fstEquilibrium_lt π p q V_E hπ hπ1 hE hV
    (PopGenParameters.fstEquilibrium_lt_of_Ne_lt p q hmu hmig hd hflow hlt)
    (p.fstEquilibrium_lt_one hflow)

/-- **Deployed Brier at the source is the heritability complement**, scaled by the
prevalence variance: the anchor the deployed value departs from. -/
theorem deployedBrier_at_no_flow_bound (π V_A V_E : ℝ) (hV : 0 < V_A) (hE : 0 ≤ V_E) :
    brier π (momentsUnderDrift V_A V_E 0) = π * (1 - π) * (1 - share V_A V_E) := by
  unfold brier complement
  rw [r2_momentsUnderDrift_at_source V_A V_E hV hE]

/-- **A longer split, worse Brier score.** The split-coordinate route into the binary
metric, so a result stated in divergence time and one stated in migration rate reach the
same place. -/
theorem brier_deployedR2FromTau_anti (π V_A V_E : ℝ) (t₁ t₂ : Tau) (hπ : 0 < π) (hπ1 : π < 1)
    (hV : 0 < V_A) (hE : 0 < V_E) (h0 : 0 ≤ t₁.value) (hlt : t₁.value < t₂.value) :
    brier π (momentsUnderDrift V_A V_E (fstFromTau t₁))
      < brier π (momentsUnderDrift V_A V_E (fstFromTau t₂)) := by
  have hf1 := fstFromTau_lt_fstFromTau t₁ t₂ h0 hlt
  have hlt2 := fstFromTau_lt_one t₂ (by linarith)
  exact brier_momentsUnderDrift_mono π V_A V_E (fstFromTau t₁) (fstFromTau t₂) hπ hπ1 hV hE
    hf1 hlt2

/-! ### The deme count reaches the metric

The island lattice is not decoration: the deme correction is a factor of two at the
two-population split and falls towards one as the lattice grows, and a factor on the
migration term is a factor on the deployed metric.

These are theorems about two HISTORIES differing in their lattice, and that is the point.
The deme count reached the metric through a SECOND function, `deployedR2FromIsland`,
taking six raw reals -- because the parameter record carried no deme count, so
`deployedR2` could express the two-deme case alone. Two routes from a demography to one
metric, in the two files written to end exactly that pattern, and a constraint added to
one reached the other only if someone noticed. `nDemes` is a field of `PopGenParameters`
now and the raw route is deleted. `deployedR2FromIsland_slope` and
`deployedR2FromIsland_mse` went with it: they said what `deployedSlope_eq_one` and
`deployedMse_eq` already say, in the other coordinates. -/

/-- **The two-deme reading, recovered.** At `p.nDemes = 2` the deployed metric is the one
this record produced before it carried a deme count: `1/(1 + θ + 2M)` into the moment
tuple, and on into `R²`.

This is the theorem that says what the batteries on `fstEquilibrium` measured. They
measured the two-deme member, so the deployment they bear on is this one, and a
deployment at any other lattice size inherits the SHAPE and not the verdict. -/
theorem deployedR2_at_two_demes (p : PopGenParameters) (V_E : ℝ) (hd : p.nDemes = 2) :
    deployedR2 p V_E
      = (momentsUnderDrift p.V_A V_E (fstFromFlow (p.theta.value + 2 * p.bigM.value))).r2 := by
  unfold deployedR2
  rw [p.fstEquilibrium_eq_scaled_two_demes hd]

/-- **The deployed metric reads five fields of the record and no others.**

`Ne`, `mu`, `mig`, `nDemes`, `V_A`. Not `t_div`, not `recomb`, and nothing a later hand
adds without a law to read it.

This is the machine-checkable form of the rule that a field must earn its place. A
selection coefficient, a locus count and a sample size were each considered for
`PopGenParameters` and each rejected, and this theorem is why the rejection is a fact
rather than a preference: under pure drift the chain sees genetic architecture only
through `V_A`, and a sample size is a property of an ESTIMATE of this metric rather than
of the metric, which is a population quantity with no sampling error. A field added with
nothing to do would leave this theorem true, and that is precisely what makes it a slot
rather than a parameter. -/
theorem deployedR2_congr (p q : PopGenParameters) (V_E : ℝ)
    (hNe : p.Ne = q.Ne) (hmu : p.mu = q.mu) (hmig : p.mig = q.mig)
    (hd : p.nDemes = q.nDemes) (hV : p.V_A = q.V_A) :
    deployedR2 p V_E = deployedR2 q V_E := by
  unfold deployedR2
  rw [hV, PopGenParameters.fstEquilibrium_congr p q hNe hmu hmig hd]

/-- **More demes, more differentiation between any two of them, less transferable score.**

The deme correction `d/(d-1)` FALLS with `d`, so the effective migration between a given
pair falls, so `F_ST` rises and the metric drops. Counter-intuitive read as "more
populations means more mixing" and correct read as "a fixed per-pair migration rate
spreads a deme's immigration over more sources".

The end-to-end deme law, and the fourth demographic parameter to reach the metric by a
named chain rather than by a coincidence between two files. It is stated on two records
differing only in `nDemes`, which is what makes it comparable to the migration, mutation
and effective-size laws above rather than a statement in a parallel vocabulary.

Migration must be strictly positive: at `m = 0` the deme count multiplies nothing, the
equilibrium is the pure mutation-drift balance at every lattice size, and there is no
monotonicity to state. That is a real case rather than an edge excluded by fiat.

This closes the question the empirical ledger raised.
`simcov/battery_falsrepair_c2.py` FALSIFIES the many-deme limit at `d = 20` at 3.92 sems
where the finite-deme form matches the same cells at 2.47: the deme count moves the
measured differentiation, and this says which way that moves the deployed metric. -/
theorem deployedR2_anti_in_demes (p q : PopGenParameters) (V_E : ℝ) (hE : 0 < V_E)
    (hNe : p.Ne = q.Ne) (hmu : p.mu = q.mu) (hmig : p.mig = q.mig) (hV : p.V_A = q.V_A)
    (hmigpos : 0 < p.mig) (hlt : p.nDemes < q.nDemes) :
    deployedR2 q V_E < deployedR2 p V_E := by
  have hfst := PopGenParameters.fstEquilibrium_lt_of_nDemes_lt p q hNe hmu hmig hmigpos hlt
  have hqmu := q.mu_nonneg
  have hflow : 0 < q.mu + q.mig := by
    rw [← hmig]
    linarith
  unfold deployedR2
  rw [hV]
  exact r2_momentsUnderDrift_anti q.V_A V_E p.fstEquilibrium q.fstEquilibrium
    q.V_A_pos hE hfst (q.fstEquilibrium_lt_one hflow)

/-- **More demes, worse Brier score**, by the same chain into the binary coordinate. -/
theorem deployedBrier_anti_in_demes (π : ℝ) (p q : PopGenParameters) (V_E : ℝ)
    (hπ : 0 < π) (hπ1 : π < 1) (hE : 0 < V_E)
    (hNe : p.Ne = q.Ne) (hmu : p.mu = q.mu) (hmig : p.mig = q.mig) (hV : p.V_A = q.V_A)
    (hmigpos : 0 < p.mig) (hlt : p.nDemes < q.nDemes) :
    deployedBrier π p V_E < deployedBrier π q V_E := by
  have hfst := PopGenParameters.fstEquilibrium_lt_of_nDemes_lt p q hNe hmu hmig hmigpos hlt
  have hqmu := q.mu_nonneg
  have hflow : 0 < q.mu + q.mig := by
    rw [← hmig]
    linarith
  unfold deployedBrier
  rw [hV]
  exact brier_anti_in_r2 π _ _ hπ hπ1
    (r2_momentsUnderDrift_anti q.V_A V_E p.fstEquilibrium q.fstEquilibrium q.V_A_pos hE
      hfst (q.fstEquilibrium_lt_one hflow))

/-! ### The split route, for the rest of the family -/

/-- **The calibration slope after a clean split is one at every divergence time.** -/
theorem deployedR2FromTau_slope (V_A V_E : ℝ) (t : Tau) (hV : 0 < V_A) (h : 0 ≤ t.value) :
    (momentsUnderDrift V_A V_E (fstFromTau t)).calibrationSlope = 1 := by
  refine calibrationSlope_momentsUnderDrift V_A V_E _ hV ?_
  unfold fstFromTau saturation
  rw [div_lt_one (by linarith)]
  linarith

/-- **And the mean squared error is flat along the split too.** Every metric except `R²`
and the metrics that are functions of `R²` is blind to a clean split. -/
theorem deployedR2FromTau_mse (V_A V_E : ℝ) (t : Tau) :
    (momentsUnderDrift V_A V_E (fstFromTau t)).mse = V_E :=
  mse_momentsUnderDrift V_A V_E _

/-- **At the split the deployed metric is the heritability**, so the whole decay is a
departure from a value the source population fixes. -/
theorem deployedR2FromTau_bounded (V_A V_E : ℝ) (t : Tau) (hV : 0 < V_A) (hE : 0 ≤ V_E)
    (h : 0 ≤ t.value) :
    (momentsUnderDrift V_A V_E (fstFromTau t)).r2 ≤ share V_A V_E := by
  have hf : fstFromTau t < 1 := by
    unfold fstFromTau saturation
    rw [div_lt_one (by linarith)]
    linarith
  have hf0 : 0 ≤ fstFromTau t := by
    unfold fstFromTau saturation
    positivity
  have := r2_momentsUnderDrift_le_source V_A V_E (fstFromTau t) hV hE hf0 hf
  rwa [r2_momentsUnderDrift_at_source V_A V_E hV hE] at this

/-- **The AUC argument decays along the split.** Discrimination falls with divergence
time, by the same route as `R²`. -/
theorem aucArgument_deployedR2FromTau_anti (V_A V_E : ℝ) (t₁ t₂ : Tau) (hV : 0 < V_A)
    (hE : 0 < V_E) (h0 : 0 ≤ t₁.value) (hlt : t₁.value < t₂.value) :
    aucArgument (momentsUnderDrift V_A V_E (fstFromTau t₂))
      < aucArgument (momentsUnderDrift V_A V_E (fstFromTau t₁)) := by
  have hf1 := fstFromTau_lt_fstFromTau t₁ t₂ h0 hlt
  have hlt2 := fstFromTau_lt_one t₂ (by linarith)
  have hf0 : 0 ≤ fstFromTau t₁ := by
    unfold fstFromTau saturation; positivity
  exact aucArgument_momentsUnderDrift_anti V_A V_E (fstFromTau t₁) (fstFromTau t₂) hV hE
    hf1 hlt2 hf0

/-- **The portability ratio along a split.** What a report comparing a target `R²` to a
source `R²` is measuring, expressed in divergence time.

    Empirical status: NOT AN EMPIRICAL CLAIM -- this is a SHAPE, not a quantity.
    A kernel asserts nothing about a population, so no measurement can bear on it.
    What can be measured is a named quantity claiming this shape computes it, and
    those live in the subsystem modules with their own status lines and ledger rows. -/
noncomputable def portabilityRatioFromTau (V_A V_E : ℝ) (t : Tau) : ℝ :=
  portabilityRatio V_A V_E (fstFromTau t)

/-- **A longer split gives a smaller portability ratio.** -/
theorem portabilityRatioFromTau_anti (V_A V_E : ℝ) (t₁ t₂ : Tau) (hV : 0 < V_A) (hE : 0 < V_E)
    (h0 : 0 ≤ t₁.value) (hlt : t₁.value < t₂.value) :
    portabilityRatioFromTau V_A V_E t₂ < portabilityRatioFromTau V_A V_E t₁ := by
  have hsrc : 0 < (momentsUnderDrift V_A V_E 0).r2 := by
    rw [r2_momentsUnderDrift_at_source V_A V_E hV (le_of_lt hE)]
    unfold share; positivity
  unfold portabilityRatioFromTau portabilityRatio ratio
  exact div_lt_div_of_pos_right
    (deployedR2FromTau_anti V_A V_E t₁ t₂ hV hE h0 hlt) hsrc

/-- **The portability ratio a demographic history produces.** What a paper reporting
"the score transfers at 40% of its source `R²`" is measuring, as a function of
`(Nₑ, m, μ)` rather than of a differentiation supplied by hand.

    Empirical status: NOT AN EMPIRICAL CLAIM -- this is a SHAPE, not a quantity.
    A kernel asserts nothing about a population, so no measurement can bear on it.
    What can be measured is a named quantity claiming this shape computes it, and
    those live in the subsystem modules with their own status lines and ledger rows. -/
noncomputable def deployedPortabilityRatio (p : PopGenParameters) (V_E : ℝ) : ℝ :=
  portabilityRatio p.V_A V_E p.fstEquilibrium

/-- **The deployed portability ratio lies in the unit interval at every history.** -/
theorem deployedPortabilityRatio_mem_unit (p : PopGenParameters) (V_E : ℝ)
    (hE : 0 ≤ V_E) (hflow : 0 < p.mu + p.mig) :
    0 ≤ deployedPortabilityRatio p V_E ∧ deployedPortabilityRatio p V_E ≤ 1 :=
  portabilityRatio_mem_unit p.V_A V_E p.fstEquilibrium p.V_A_pos hE
    p.fstEquilibrium_mem_unit.1 (p.fstEquilibrium_lt_one hflow)

/-- **A population's source `R2` is positive.**  Read at no differentiation, the deployed
`R2` is the share its additive variance commands of its own phenotypic variance, and that
share is positive because `V_A` is.  Every portability ratio divides by this, so it is
stated once rather than re-derived at each of them. -/
theorem r2_momentsUnderDrift_at_source_pos (p : PopGenParameters) (V_E : ℝ) (hE : 0 < V_E) :
    0 < r2 (momentsUnderDrift p.V_A V_E 0) := by
  rw [r2_momentsUnderDrift_at_source p.V_A V_E p.V_A_pos (le_of_lt hE)]
  unfold share
  have := p.V_A_pos
  positivity

/-- **Less differentiation, a higher portability ratio.**  The engine the four
demographic laws below share, stated on the `F_ST` ordering itself so that each of them is
the ordering plus a citation -- the same shape `deployedBrier_anti_of_fstEquilibrium_lt`
already has for the Brier score. -/
theorem deployedPortabilityRatio_lt_of_fstEquilibrium_lt (p q : PopGenParameters)
    (V_E : ℝ) (hE : 0 < V_E) (hV : p.V_A = q.V_A)
    (hfst : q.fstEquilibrium < p.fstEquilibrium) (hone : p.fstEquilibrium < 1) :
    deployedPortabilityRatio p V_E < deployedPortabilityRatio q V_E := by
  have hsrc := r2_momentsUnderDrift_at_source_pos q V_E hE
  unfold deployedPortabilityRatio portabilityRatio ratio
  rw [hV]
  exact div_lt_div_of_pos_right
    (r2_momentsUnderDrift_anti q.V_A V_E q.fstEquilibrium p.fstEquilibrium q.V_A_pos hE
      hfst hone) hsrc

/-- **More migration, a higher portability ratio.** The reported quantity, moved by a
demographic parameter, with every step a named map. -/
theorem deployedPortabilityRatio_mono_in_migration (p q : PopGenParameters) (V_E : ℝ)
    (hE : 0 < V_E) (hNe : p.Ne = q.Ne) (hmu : p.mu = q.mu) (hd : p.nDemes = q.nDemes)
    (hV : p.V_A = q.V_A) (hlt : p.mig < q.mig) (hflow : 0 < p.mu + p.mig) :
    deployedPortabilityRatio p V_E < deployedPortabilityRatio q V_E :=
  deployedPortabilityRatio_lt_of_fstEquilibrium_lt p q V_E hE hV
    (PopGenParameters.fstEquilibrium_lt_of_mig_lt p q hNe hmu hd hlt)
    (p.fstEquilibrium_lt_one hflow)

/-- **A history with no flow transfers nothing.** At zero migration and zero mutation the
equilibrium is complete differentiation and the deployed `R²` is zero: two populations
with nothing passing between them share no allele frequencies for a score to use. The
boundary the monotone laws approach. -/
theorem deployedR2_at_no_flow (p : PopGenParameters) (V_E : ℝ) (hmu : p.mu = 0)
    (hmig : p.mig = 0) (hE : 0 < V_E) :
    deployedR2 p V_E = 0 := by
  have hf : p.fstEquilibrium = 1 := by
    unfold PopGenParameters.fstEquilibrium fstIslandEquilibrium fstFromFlow scaledFlow
      PopGenParameters.theta PopGenParameters.bigM
    rw [hmu, hmig, Theta.value_ofRate, BigM.value_ofRate]
    norm_num
  unfold deployedR2
  rw [hf]
  exact r2_momentsUnderDrift_at_complete p.V_A V_E hE

/-- **A history with no flow leaves the Brier score at its uninformative baseline.**
The binary coordinate's version of the no-flow boundary: with nothing passing between the
populations, a deployed score does no better than knowing the prevalence. -/
theorem deployedBrier_at_no_flow (π : ℝ) (p : PopGenParameters) (V_E : ℝ)
    (hmu : p.mu = 0) (hmig : p.mig = 0) (hE : 0 < V_E) :
    deployedBrier π p V_E = π * (1 - π) := by
  have hf : p.fstEquilibrium = 1 := by
    unfold PopGenParameters.fstEquilibrium fstIslandEquilibrium fstFromFlow scaledFlow
      PopGenParameters.theta PopGenParameters.bigM
    rw [hmu, hmig, Theta.value_ofRate, BigM.value_ofRate]
    norm_num
  unfold deployedBrier
  rw [hf]
  exact brier_at_zero_r2 π _ (r2_momentsUnderDrift_at_complete p.V_A V_E hE)

/-- **The whole deployment report at a no-flow history, in one statement.** `R²` at zero,
the Brier score at its baseline, and -- the finding -- the calibration slope still exactly
one and the mean squared error still exactly the environmental variance. Two of the four
numbers a deployment reports are unchanged at the worst demographic history there is. -/
theorem deployedReport_at_no_flow (π : ℝ) (p : PopGenParameters) (V_E : ℝ)
    (hmu : p.mu = 0) (hmig : p.mig = 0) (hE : 0 < V_E) :
    deployedR2 p V_E = 0 ∧
    deployedBrier π p V_E = π * (1 - π) ∧
    (momentsUnderDrift p.V_A V_E p.fstEquilibrium).mse = V_E := by
  refine ⟨deployedR2_at_no_flow p V_E hmu hmig hE,
    deployedBrier_at_no_flow π p V_E hmu hmig hE,
    mse_momentsUnderDrift p.V_A V_E p.fstEquilibrium⟩

/-! ## The demography's own metrics

Every result above states a metric law over loose reals -- `V_A`, `V_E`, an `F_ST` -- and
a reader has to believe those came from a population. The results below say the same
things about `(p : PopGenParameters)` and the differentiation that record itself
predicts, so the demography reaches the deployed number inside one claim rather than
across a gap the reader closes.

That gap is not a formality: a theorem taking `F_ST` as a free real is a statement about
arithmetic, and the corpus's claim is about populations. `shape-routes` refuses the same
shape from the other side, by forbidding a
second entry point that re-supplies the record's fields as bare arguments.
-/

/-- **A demography's deployed portability ratio is a fraction.**  Its own equilibrium
differentiation, fed to the ratio, lands in the unit interval -- so the number a
deployment reports is a share of the source accuracy and not something that can exceed
it. -/
theorem portabilityRatio_mem_unit_of_params (p : PopGenParameters) (V_E : ℝ)
    (hE : 0 ≤ V_E) (hflow : 0 < p.mu + p.mig) :
    0 ≤ portabilityRatio p.V_A V_E p.fstEquilibrium ∧
      portabilityRatio p.V_A V_E p.fstEquilibrium ≤ 1 :=
  portabilityRatio_mem_unit p.V_A V_E p.fstEquilibrium p.V_A_pos hE
    p.fstEquilibrium_mem_unit.1 (p.fstEquilibrium_lt_one hflow)

/-- **At the source there is nothing to lose.**  Read at zero differentiation, the ratio
is one for every demography's additive variance. -/
theorem portabilityRatio_at_source_of_params (p : PopGenParameters) (V_E : ℝ)
    (hE : 0 ≤ V_E) : portabilityRatio p.V_A V_E 0 = 1 :=
  portabilityRatio_at_source p.V_A V_E p.V_A_pos hE

/-- **A demography with no coalescent separation deploys its full share.**  At `τ = 0`
the tau-form `R²` is the source share `V_A/(V_A + V_E)` of that population. -/
theorem deployedR2FromTau_at_zero_of_params (p : PopGenParameters) (V_E : ℝ)
    (hE : 0 ≤ V_E) : deployedR2FromTau p.V_A V_E ⟨0⟩ = share p.V_A V_E :=
  deployedR2FromTau_at_zero p.V_A V_E p.V_A_pos hE

/-- **Deeper separation deploys less, for a fixed demography.**  The additive variance is
the record's; only the coalescent time moves. -/
theorem deployedR2FromTau_anti_of_params (p : PopGenParameters) (V_E : ℝ) (t₁ t₂ : Tau)
    (hE : 0 < V_E) (h0 : 0 ≤ t₁.value) (hlt : t₁.value < t₂.value) :
    deployedR2FromTau p.V_A V_E t₂ < deployedR2FromTau p.V_A V_E t₁ :=
  deployedR2FromTau_anti p.V_A V_E t₁ t₂ p.V_A_pos hE h0 hlt

/-- **And the portability ratio falls with it.** -/
theorem portabilityRatioFromTau_anti_of_params (p : PopGenParameters) (V_E : ℝ)
    (t₁ t₂ : Tau) (hE : 0 < V_E) (h0 : 0 ≤ t₁.value) (hlt : t₁.value < t₂.value) :
    portabilityRatioFromTau p.V_A V_E t₂ < portabilityRatioFromTau p.V_A V_E t₁ :=
  portabilityRatioFromTau_anti p.V_A V_E t₁ t₂ p.V_A_pos hE h0 hlt

/-- **A demography with no flow pays its whole share in Brier risk.**  At `F_ST = 0` the
deployed Brier score is the base rate's variance discounted by exactly the share the
population's additive variance commands. -/
theorem deployedBrier_at_no_flow_bound_of_params (p : PopGenParameters) (π V_E : ℝ)
    (hE : 0 ≤ V_E) :
    brier π (momentsUnderDrift p.V_A V_E 0) = π * (1 - π) * (1 - share p.V_A V_E) :=
  deployedBrier_at_no_flow_bound π p.V_A V_E p.V_A_pos hE

/-- **Brier risk rises with separation, for one demography.**  The additive variance is
the record's and only the differentiation moves, which is the comparison a deployment
across two populations actually makes. -/
theorem brier_momentsUnderDrift_mono_of_params (p : PopGenParameters) (π V_E f₁ f₂ : ℝ)
    (hπ : 0 < π) (hπ1 : π < 1) (hE : 0 < V_E) (h1 : f₁ < f₂) (h2 : f₂ < 1) :
    brier π (momentsUnderDrift p.V_A V_E f₁) < brier π (momentsUnderDrift p.V_A V_E f₂) :=
  brier_momentsUnderDrift_mono π p.V_A V_E f₁ f₂ hπ hπ1 p.V_A_pos hE h1 h2

/-- **The AUC argument falls with separation, for one demography.** -/
theorem aucArgument_momentsUnderDrift_anti_of_params (p : PopGenParameters)
    (V_E f₁ f₂ : ℝ) (hE : 0 < V_E) (h1 : f₁ < f₂) (h2 : f₂ < 1) (h0 : 0 ≤ f₁) :
    aucArgument (momentsUnderDrift p.V_A V_E f₂) <
      aucArgument (momentsUnderDrift p.V_A V_E f₁) :=
  aucArgument_momentsUnderDrift_anti p.V_A V_E f₁ f₂ p.V_A_pos hE h1 h2 h0


/-- **Deeper coalescent separation costs a demography Brier accuracy.**  The additive
variance is the record's; only the separation moves. -/
theorem brier_deployedR2FromTau_anti_of_params (p : PopGenParameters) (π V_E : ℝ)
    (t₁ t₂ : Tau) (hπ : 0 < π) (hπ1 : π < 1) (hE : 0 < V_E) (h0 : 0 ≤ t₁.value)
    (hlt : t₁.value < t₂.value) :
    brier π (momentsUnderDrift p.V_A V_E (fstFromTau t₁))
      < brier π (momentsUnderDrift p.V_A V_E (fstFromTau t₂)) :=
  brier_deployedR2FromTau_anti π p.V_A V_E t₁ t₂ hπ hπ1 p.V_A_pos hE h0 hlt

/-- **And costs it discrimination.** -/
theorem aucArgument_deployedR2FromTau_anti_of_params (p : PopGenParameters) (V_E : ℝ)
    (t₁ t₂ : Tau) (hE : 0 < V_E) (h0 : 0 ≤ t₁.value) (hlt : t₁.value < t₂.value) :
    aucArgument (momentsUnderDrift p.V_A V_E (fstFromTau t₂))
      < aucArgument (momentsUnderDrift p.V_A V_E (fstFromTau t₁)) :=
  aucArgument_deployedR2FromTau_anti p.V_A V_E t₁ t₂ p.V_A_pos hE h0 hlt

/-- **More migration, strictly lower Brier risk.**  Two demographies alike but for
migration: the one exchanging more migrants sits at strictly lower equilibrium
differentiation, and a deployment against it reports strictly less Brier risk. The
demography enters, the deployed number comes out, and no free `F_ST` appears. -/
theorem brier_anti_in_migration_of_params (p q : PopGenParameters) (π V_E : ℝ)
    (hπ : 0 < π) (hπ1 : π < 1) (hE : 0 < V_E) (hNe : p.Ne = q.Ne) (hmu : p.mu = q.mu)
    (hd : p.nDemes = q.nDemes) (hV : p.V_A = q.V_A) (hlt : p.mig < q.mig)
    (hflow : 0 < p.mu + p.mig) :
    brier π (momentsUnderDrift q.V_A V_E q.fstEquilibrium)
      < brier π (momentsUnderDrift p.V_A V_E p.fstEquilibrium) := by
  have hfst : q.fstEquilibrium < p.fstEquilibrium :=
    PopGenParameters.fstEquilibrium_lt_of_mig_lt p q hNe hmu hd hlt
  have := brier_momentsUnderDrift_mono π q.V_A V_E q.fstEquilibrium p.fstEquilibrium hπ hπ1
    (hV ▸ p.V_A_pos) hE hfst (p.fstEquilibrium_lt_one hflow)
  rw [hV]
  exact this

/-- **And strictly better discrimination.**  Same two demographies, read through the AUC
argument rather than the Brier score. -/
theorem aucArgument_mono_in_migration_of_params (p q : PopGenParameters) (V_E : ℝ)
    (hE : 0 < V_E) (hNe : p.Ne = q.Ne) (hmu : p.mu = q.mu) (hd : p.nDemes = q.nDemes)
    (hV : p.V_A = q.V_A) (hlt : p.mig < q.mig) (hflow : 0 < p.mu + p.mig) :
    aucArgument (momentsUnderDrift p.V_A V_E p.fstEquilibrium)
      < aucArgument (momentsUnderDrift q.V_A V_E q.fstEquilibrium) := by
  have hfst : q.fstEquilibrium < p.fstEquilibrium :=
    PopGenParameters.fstEquilibrium_lt_of_mig_lt p q hNe hmu hd hlt
  have := aucArgument_momentsUnderDrift_anti q.V_A V_E q.fstEquilibrium p.fstEquilibrium
    (hV ▸ p.V_A_pos) hE hfst (p.fstEquilibrium_lt_one hflow) (q.fstEquilibrium_mem_unit).1
  rw [hV]
  exact this


/-! ### The AUC argument across the demographic axes

`deployedR2` and `deployedBrier` already have a law for each of the four axes a
`PopGenParameters` can differ along -- migration, mutation, effective size, deme count.
The AUC argument had one only for migration, so a deployment reading discrimination
rather than calibration had no statement to appeal to for the other three. These are
those statements, each proved through the same `fstEquilibrium_lt_of_*` ordering the
`deployedBrier` laws use. -/

/-- **More mutation, better discrimination.** -/
theorem aucArgument_mono_in_mutation_of_params (p q : PopGenParameters) (V_E : ℝ)
    (hE : 0 < V_E) (hNe : p.Ne = q.Ne) (hmig : p.mig = q.mig) (hd : p.nDemes = q.nDemes)
    (hV : p.V_A = q.V_A) (hlt : p.mu < q.mu) (hflow : 0 < p.mu + p.mig) :
    aucArgument (momentsUnderDrift p.V_A V_E p.fstEquilibrium)
      < aucArgument (momentsUnderDrift q.V_A V_E q.fstEquilibrium) := by
  have hfst : q.fstEquilibrium < p.fstEquilibrium :=
    PopGenParameters.fstEquilibrium_lt_of_mu_lt p q hNe hmig hd hlt
  have := aucArgument_momentsUnderDrift_anti q.V_A V_E q.fstEquilibrium p.fstEquilibrium
    (hV ▸ p.V_A_pos) hE hfst (p.fstEquilibrium_lt_one hflow) (q.fstEquilibrium_mem_unit).1
  rw [hV]
  exact this

/-- **A larger effective size, better discrimination.**  Drift is what differentiates, so
a population that drifts less carries more of its signal across. -/
theorem aucArgument_mono_in_Ne_of_params (p q : PopGenParameters) (V_E : ℝ)
    (hE : 0 < V_E) (hmu : p.mu = q.mu) (hmig : p.mig = q.mig) (hd : p.nDemes = q.nDemes)
    (hV : p.V_A = q.V_A) (hlt : p.Ne < q.Ne) (hflow : 0 < p.mu + p.mig) :
    aucArgument (momentsUnderDrift p.V_A V_E p.fstEquilibrium)
      < aucArgument (momentsUnderDrift q.V_A V_E q.fstEquilibrium) := by
  have hfst : q.fstEquilibrium < p.fstEquilibrium :=
    PopGenParameters.fstEquilibrium_lt_of_Ne_lt p q hmu hmig hd hflow hlt
  have := aucArgument_momentsUnderDrift_anti q.V_A V_E q.fstEquilibrium p.fstEquilibrium
    (hV ▸ p.V_A_pos) hE hfst (p.fstEquilibrium_lt_one hflow) (q.fstEquilibrium_mem_unit).1
  rw [hV]
  exact this

/-- **More demes, worse discrimination.**  The deme correction runs the other way: a
metapopulation split more finely differentiates further at the same flow. -/
theorem aucArgument_anti_in_demes_of_params (p q : PopGenParameters) (V_E : ℝ)
    (hE : 0 < V_E) (hNe : p.Ne = q.Ne) (hmu : p.mu = q.mu) (hmig : p.mig = q.mig)
    (hV : p.V_A = q.V_A) (hmigpos : 0 < p.mig) (hlt : p.nDemes < q.nDemes)
    (hflow : 0 < q.mu + q.mig) :
    aucArgument (momentsUnderDrift q.V_A V_E q.fstEquilibrium)
      < aucArgument (momentsUnderDrift p.V_A V_E p.fstEquilibrium) := by
  have hfst : p.fstEquilibrium < q.fstEquilibrium :=
    PopGenParameters.fstEquilibrium_lt_of_nDemes_lt p q hNe hmu hmig hmigpos hlt
  have := aucArgument_momentsUnderDrift_anti p.V_A V_E p.fstEquilibrium q.fstEquilibrium
    p.V_A_pos hE hfst (q.fstEquilibrium_lt_one hflow) (p.fstEquilibrium_mem_unit).1
  rw [← hV]
  exact this

/-! ### The Brier score along the last axis

`deployedBrier` has migration, mutation and effective size; the deme count was the one
axis without a law, and it is the axis whose direction is opposite to the other three. -/

/-- **More demes, worse Brier score.** -/
theorem deployedBrier_anti_in_demes_of_params (π : ℝ) (p q : PopGenParameters) (V_E : ℝ)
    (hπ : 0 < π) (hπ1 : π < 1) (hE : 0 < V_E) (hNe : p.Ne = q.Ne) (hmu : p.mu = q.mu)
    (hmig : p.mig = q.mig) (hV : p.V_A = q.V_A) (hmigpos : 0 < p.mig)
    (hlt : p.nDemes < q.nDemes) (hflow : 0 < q.mu + q.mig) :
    deployedBrier π p V_E < deployedBrier π q V_E :=
  deployedBrier_anti_of_fstEquilibrium_lt π q p V_E hπ hπ1 hE hV.symm
    (PopGenParameters.fstEquilibrium_lt_of_nDemes_lt p q hNe hmu hmig hmigpos hlt)
    (q.fstEquilibrium_lt_one hflow)


/-! ### The deployed portability ratio across the remaining axes

`deployedPortabilityRatio` had a law for migration alone.  The ratio is the deployed `R²`
over the same population's source `R²`, so it moves with differentiation exactly as the
Brier score and the AUC argument do, and the three axes below complete it. -/

/-- **More mutation, a higher portability ratio.** -/
theorem deployedPortabilityRatio_mono_in_mutation (p q : PopGenParameters) (V_E : ℝ)
    (hE : 0 < V_E) (hNe : p.Ne = q.Ne) (hmig : p.mig = q.mig) (hd : p.nDemes = q.nDemes)
    (hV : p.V_A = q.V_A) (hlt : p.mu < q.mu) (hflow : 0 < p.mu + p.mig) :
    deployedPortabilityRatio p V_E < deployedPortabilityRatio q V_E :=
  deployedPortabilityRatio_lt_of_fstEquilibrium_lt p q V_E hE hV
    (PopGenParameters.fstEquilibrium_lt_of_mu_lt p q hNe hmig hd hlt)
    (p.fstEquilibrium_lt_one hflow)

/-- **A larger effective size, a higher portability ratio.** -/
theorem deployedPortabilityRatio_mono_in_Ne (p q : PopGenParameters) (V_E : ℝ)
    (hE : 0 < V_E) (hmu : p.mu = q.mu) (hmig : p.mig = q.mig) (hd : p.nDemes = q.nDemes)
    (hV : p.V_A = q.V_A) (hlt : p.Ne < q.Ne) (hflow : 0 < p.mu + p.mig) :
    deployedPortabilityRatio p V_E < deployedPortabilityRatio q V_E :=
  deployedPortabilityRatio_lt_of_fstEquilibrium_lt p q V_E hE hV
    (PopGenParameters.fstEquilibrium_lt_of_Ne_lt p q hmu hmig hd hflow hlt)
    (p.fstEquilibrium_lt_one hflow)

/-- **More demes, a lower portability ratio.**  The one axis whose direction is opposite:
a metapopulation split more finely differentiates further at the same flow, so less of the
source accuracy survives the transport. -/
theorem deployedPortabilityRatio_anti_in_demes (p q : PopGenParameters) (V_E : ℝ)
    (hE : 0 < V_E) (hNe : p.Ne = q.Ne) (hmu : p.mu = q.mu) (hmig : p.mig = q.mig)
    (hV : p.V_A = q.V_A) (hmigpos : 0 < p.mig) (hlt : p.nDemes < q.nDemes)
    (hflow : 0 < q.mu + q.mig) :
    deployedPortabilityRatio q V_E < deployedPortabilityRatio p V_E :=
  deployedPortabilityRatio_lt_of_fstEquilibrium_lt q p V_E hE hV.symm
    (PopGenParameters.fstEquilibrium_lt_of_nDemes_lt p q hNe hmu hmig hmigpos hlt)
    (q.fstEquilibrium_lt_one hflow)


/-! ### What two demographies look like to each metric

The laws above say every deployed number moves the same way when a population's
demography changes.  These say the opposite thing about the other two metrics, and the
pair is the point: an audit that reads only the calibration slope or only the mean
squared error sees NOTHING when a score is transported between two genuinely different
populations, while the deployed `R²` between the same two has strictly fallen.

Stated about records rather than about a free `F_ST` because that is the claim a
deployment needs: not "the slope is flat in this parameter" but "these two populations,
which differ in how much migration they exchange, are indistinguishable to this metric". -/

/-- **A demography's deployed calibration slope is one.**  Drift erodes the score's
variance and its predictive covariance by the same factor, so their ratio does not move --
whatever population the score is carried to. -/
theorem calibrationSlope_of_params (p : PopGenParameters) (V_E : ℝ)
    (hflow : 0 < p.mu + p.mig) :
    calibrationSlope (momentsUnderDrift p.V_A V_E p.fstEquilibrium) = 1 :=
  calibrationSlope_momentsUnderDrift p.V_A V_E p.fstEquilibrium p.V_A_pos
    (p.fstEquilibrium_lt_one hflow)

/-- **Two demographies, one calibration slope.**  However far apart two populations sit,
a deployment judged on calibration alone reports the same number for both. -/
theorem calibrationSlope_eq_of_params (p q : PopGenParameters) (V_E : ℝ)
    (hp : 0 < p.mu + p.mig) (hq : 0 < q.mu + q.mig) :
    calibrationSlope (momentsUnderDrift p.V_A V_E p.fstEquilibrium) =
      calibrationSlope (momentsUnderDrift q.V_A V_E q.fstEquilibrium) := by
  rw [calibrationSlope_of_params p V_E hp, calibrationSlope_of_params q V_E hq]

/-- **A demography's deployed mean squared error is its environmental variance.**  Drift
removes signal from the score and the same signal from the outcome, so the residual does
not depend on the population at all. -/
theorem mse_of_params (p : PopGenParameters) (V_E : ℝ) :
    mse (momentsUnderDrift p.V_A V_E p.fstEquilibrium) = V_E :=
  mse_momentsUnderDrift p.V_A V_E p.fstEquilibrium

/-- **Two demographies with the same environmental variance, one mean squared error.**
The second metric that cannot tell two populations apart. -/
theorem mse_eq_of_params (p q : PopGenParameters) (V_E : ℝ) :
    mse (momentsUnderDrift p.V_A V_E p.fstEquilibrium) =
      mse (momentsUnderDrift q.V_A V_E q.fstEquilibrium) := by
  rw [mse_of_params p V_E, mse_of_params q V_E]

/-- **The audit gap, stated about two populations.**  Take two demographies alike but for
migration.  The deployed `R²` is strictly worse for the one exchanging fewer migrants,
and the calibration slope and the mean squared error are IDENTICAL for both.

That conjunction is what makes a single-metric audit unsafe rather than merely
incomplete: the two numbers a deployment is most often judged on are exactly the two that
cannot see the difference, and the one that can is the one being lost. -/
theorem audit_gap_between_demographies (p q : PopGenParameters) (V_E : ℝ)
    (hE : 0 < V_E) (hNe : p.Ne = q.Ne) (hmu : p.mu = q.mu) (hd : p.nDemes = q.nDemes)
    (hV : p.V_A = q.V_A) (hlt : p.mig < q.mig) (hflow : 0 < p.mu + p.mig) :
    deployedR2 p V_E < deployedR2 q V_E ∧
      calibrationSlope (momentsUnderDrift p.V_A V_E p.fstEquilibrium) =
        calibrationSlope (momentsUnderDrift q.V_A V_E q.fstEquilibrium) ∧
      mse (momentsUnderDrift p.V_A V_E p.fstEquilibrium) =
        mse (momentsUnderDrift q.V_A V_E q.fstEquilibrium) := by
  refine ⟨deployedR2_mono_in_migration p q V_E hE hNe hmu hd hV hlt hflow, ?_, ?_⟩
  · exact calibrationSlope_eq_of_params p q V_E hflow (by rw [← hmu]; linarith)
  · exact mse_eq_of_params p q V_E

/-- **The same gap read through the AUC argument.**  Discrimination falls with the
deployed `R²` while the calibration slope does not move, so a deployment audited on
calibration alone also misses a loss of ranking accuracy. -/
theorem audit_gap_discrimination (p q : PopGenParameters) (V_E : ℝ)
    (hE : 0 < V_E) (hNe : p.Ne = q.Ne) (hmu : p.mu = q.mu) (hd : p.nDemes = q.nDemes)
    (hV : p.V_A = q.V_A) (hlt : p.mig < q.mig) (hflow : 0 < p.mu + p.mig) :
    aucArgument (momentsUnderDrift p.V_A V_E p.fstEquilibrium)
        < aucArgument (momentsUnderDrift q.V_A V_E q.fstEquilibrium) ∧
      calibrationSlope (momentsUnderDrift p.V_A V_E p.fstEquilibrium) =
        calibrationSlope (momentsUnderDrift q.V_A V_E q.fstEquilibrium) := by
  refine ⟨aucArgument_mono_in_migration_of_params p q V_E hE hNe hmu hd hV hlt hflow, ?_⟩
  exact calibrationSlope_eq_of_params p q V_E hflow (by rw [← hmu]; linarith)


/-- **The audit gap along the deme axis.**  The same conjunction as
`audit_gap_between_demographies`, for two populations that differ in how finely they are
subdivided rather than in how much they migrate: the deployed `R²` is strictly worse for
the more finely split one, and the mean squared error is identical.

Stated separately because the deme count is the axis that runs the other way, and a
reader checking whether the audit gap is an artefact of one parameter's direction should
be able to see it holding in both. -/
theorem audit_gap_across_demes (p q : PopGenParameters) (V_E : ℝ)
    (hE : 0 < V_E) (hNe : p.Ne = q.Ne) (hmu : p.mu = q.mu) (hmig : p.mig = q.mig)
    (hV : p.V_A = q.V_A) (hmigpos : 0 < p.mig) (hlt : p.nDemes < q.nDemes)
    (hflow : 0 < q.mu + q.mig) :
    deployedR2 q V_E < deployedR2 p V_E ∧
      mse (momentsUnderDrift p.V_A V_E p.fstEquilibrium) =
        mse (momentsUnderDrift q.V_A V_E q.fstEquilibrium) := by
  refine ⟨?_, mse_eq_of_params p q V_E⟩
  have hfst : p.fstEquilibrium < q.fstEquilibrium :=
    PopGenParameters.fstEquilibrium_lt_of_nDemes_lt p q hNe hmu hmig hmigpos hlt
  unfold deployedR2
  rw [← hV]
  exact r2_momentsUnderDrift_anti p.V_A V_E p.fstEquilibrium q.fstEquilibrium p.V_A_pos hE
    hfst (q.fstEquilibrium_lt_one hflow)

end ScoreMoments

end Descent.Core
