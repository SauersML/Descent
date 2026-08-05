/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Core.Parameters

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
structure is true and empty. -/
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

/-- **Deployed `R²`**, `Cov(S,Y)² / (Var(S) · Var(Y))`. -/
noncomputable def r2 (m : ScoreMoments) : ℝ :=
  m.predictiveCovariance ^ 2 / (m.scoreVariance * m.outcomeVariance)

/-- **Calibration slope**, `Cov(S,Y) / Var(S)`: the coefficient a regression of the
outcome on the deployed score would fit. One means the score is on the right scale. -/
noncomputable def calibrationSlope (m : ScoreMoments) : ℝ :=
  ratio m.predictiveCovariance m.scoreVariance

/-- **Mean squared error of the raw score**, `Var(Y) - 2Cov(S,Y) + Var(S)`, for a score
already centred on the outcome's mean. -/
noncomputable def mse (m : ScoreMoments) : ℝ :=
  m.outcomeVariance - 2 * m.predictiveCovariance + m.scoreVariance

/-- **`R²` is a proportional reduction in error** -- against the best-recalibrated
score, not the raw one. Written through the kernel so that the corpus's other
`1 - residual/baseline` quantities and this one cannot drift apart. -/
noncomputable def r2FromResidual (residual baseline : ℝ) : ℝ :=
  proportionalReduction residual baseline

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
turnover and context terms are what carry the rest. -/
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
factor and they cancel. So the monotone law is a statement about traits with
environmental variance, and a corpus that stated it without the hypothesis would be
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

/-! ### The full chain

`(Nₑ, m, μ) → F_ST → moments → R²`, as one composition. -/

/-- **Deployed `R²` from a demographic history.** The composition of
`PopGenParameters.fstEquilibrium` with `momentsUnderDrift` with `r2`: three named maps,
one function from a demography to a metric.

This is the object the corpus had no name for. Its `PopGen` layer computed `F_ST` from
`(Nₑ, m, μ, t)` and its `Portability` layer computed `R²` from moment tuples, and the two
were joined by two theorems out of 5,852 -- everything else took `fst` as a free real,
severing the metric from the population genetics meant to produce it. -/
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

/-- **More migration, more transferable score.** The end-to-end monotone law: increase
the migration rate in the demographic parameters and the deployed `R²` goes up, with
every step -- equilibrium, moments, metric -- a named map rather than an assumption.

This is the statement the corpus's two layers were built to support and could not make. -/
theorem deployedR2_mono_in_migration (p q : PopGenParameters) (V_E : ℝ) (hE : 0 < V_E)
    (hNe : p.Ne = q.Ne) (hmu : p.mu = q.mu) (hV : p.V_A = q.V_A)
    (hlt : p.mig < q.mig) (hflow : 0 < p.mu + p.mig) :
    deployedR2 p V_E < deployedR2 q V_E := by
  have hfst : q.fstEquilibrium < p.fstEquilibrium :=
    PopGenParameters.fstEquilibrium_lt_of_mig_lt p q hNe hmu hlt
  unfold deployedR2
  rw [hV]
  exact r2_momentsUnderDrift_anti q.V_A V_E q.fstEquilibrium p.fstEquilibrium
    q.V_A_pos hE hfst (p.fstEquilibrium_lt_one hflow)

end ScoreMoments

end Descent.Core
