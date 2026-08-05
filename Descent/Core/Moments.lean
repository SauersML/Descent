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
literature reports and the one this whole development is about. -/
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

/-- **The portability ratio is one exactly at no differentiation** on a trait with
environmental variance. A reported ratio below one is therefore evidence of
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
`F_ST` conventions: both are Hudson. -/
noncomputable def deployedR2FromTau (V_A V_E tau : ℝ) : ℝ :=
  (momentsUnderDrift V_A V_E (fstFromTau tau)).r2

/-- **A longer split transfers less.** Monotone in the scaled coalescence time, which is
monotone in the divergence time at fixed effective size -- so the deployed metric decays
with time since the split. -/
theorem deployedR2FromTau_anti (V_A V_E t₁ t₂ : ℝ) (hV : 0 < V_A) (hE : 0 < V_E)
    (h0 : 0 ≤ t₁) (hlt : t₁ < t₂) :
    deployedR2FromTau V_A V_E t₂ < deployedR2FromTau V_A V_E t₁ := by
  have hf1 : fstFromTau t₁ < fstFromTau t₂ := by
    unfold fstFromTau saturation
    rw [div_lt_div_iff₀ (by linarith) (by linarith)]
    nlinarith
  have hlt2 : fstFromTau t₂ < 1 := by
    unfold fstFromTau saturation
    rw [div_lt_one (by linarith)]
    linarith
  exact r2_momentsUnderDrift_anti V_A V_E (fstFromTau t₁) (fstFromTau t₂) hV hE hf1 hlt2

/-- **At the moment of the split nothing has been lost.** `τ = 0` gives `F_ST = 0` and
the deployed metric is the heritability. -/
theorem deployedR2FromTau_at_zero (V_A V_E : ℝ) (hV : 0 < V_A) (hE : 0 ≤ V_E) :
    deployedR2FromTau V_A V_E 0 = share V_A V_E := by
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

/-- **The two routes into the metric agree when they agree on `F_ST`.** Stated because
the corpus computes `F_ST` two ways -- an equilibrium under migration and mutation, and a
split law in coalescent time -- and a reader meeting both has no reason to assume the
moment tuple treats them alike. It does: the tuple sees a differentiation and nothing
about where it came from. -/
theorem deployedR2_eq_deployedR2FromTau (p : PopGenParameters) (V_E tau : ℝ)
    (h : p.fstEquilibrium = fstFromTau tau) :
    deployedR2 p V_E = deployedR2FromTau p.V_A V_E tau := by
  unfold deployedR2 deployedR2FromTau
  rw [h]

/-- **And that is a real constraint, not a tautology**: the two routes agree on `F_ST`
exactly when the scaled coalescence time is the reciprocal of the total scaled flow.
`τ = 1/x` is the conversion between the corpus's two `F_ST` coordinates, and it is
recorded here rather than left for a reader to rediscover. -/
theorem fstEquilibrium_eq_fstFromTau_iff (p : PopGenParameters) (tau : ℝ)
    (hx : 1 + (p.theta + 2 * p.bigM) ≠ 0) (ht : 1 + tau ≠ 0) :
    p.fstEquilibrium = fstFromTau tau ↔
      1 = tau * (p.theta + 2 * p.bigM) := by
  unfold PopGenParameters.fstEquilibrium fstFromFlow fstFromTau saturation
  rw [div_eq_div_iff hx ht]
  constructor <;> intro h <;> nlinarith [h]

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

/-- **More mutation, higher deployed `R²`** -- the second end-to-end law, and one the
corpus could not previously state at all. -/
theorem deployedR2_mono_in_mutation (p q : PopGenParameters) (V_E : ℝ) (hE : 0 < V_E)
    (hNe : p.Ne = q.Ne) (hmig : p.mig = q.mig) (hV : p.V_A = q.V_A)
    (hlt : p.mu < q.mu) (hflow : 0 < p.mu + p.mig) :
    deployedR2 p V_E < deployedR2 q V_E := by
  have hfst : q.fstEquilibrium < p.fstEquilibrium :=
    PopGenParameters.fstEquilibrium_lt_of_mu_lt p q hNe hmig hlt
  unfold deployedR2
  rw [hV]
  exact r2_momentsUnderDrift_anti q.V_A V_E q.fstEquilibrium p.fstEquilibrium
    q.V_A_pos hE hfst (p.fstEquilibrium_lt_one hflow)

/-- **Larger effective size, higher deployed `R²`** -- the third. -/
theorem deployedR2_mono_in_Ne (p q : PopGenParameters) (V_E : ℝ) (hE : 0 < V_E)
    (hmu : p.mu = q.mu) (hmig : p.mig = q.mig) (hV : p.V_A = q.V_A)
    (hlt : p.Ne < q.Ne) (hflow2 : 0 < p.mu + 2 * p.mig) (hflow : 0 < p.mu + p.mig) :
    deployedR2 p V_E < deployedR2 q V_E := by
  have hfst : q.fstEquilibrium < p.fstEquilibrium :=
    PopGenParameters.fstEquilibrium_lt_of_Ne_lt p q hmu hmig hflow2 hlt
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
not move at all under drift. Each is a function of the same tuple, so each composes with
the same demographic chain, and each needs its own statement. -/

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
score that disagrees with its `R²`. -/
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
discipline `calibratedBrierFromVariances` records for the liability scale. -/
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

/-- **Deployed calibration slope from a demographic history.** One at every history with
some flow -- which is the sharpest form of the warning: no demographic history produces a
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

/-- **Deployed Brier score from a demographic history.** -/
noncomputable def deployedBrier (π : ℝ) (p : PopGenParameters) (V_E : ℝ) : ℝ :=
  brier π (momentsUnderDrift p.V_A V_E p.fstEquilibrium)

/-- **More migration, better Brier score.** -/
theorem deployedBrier_mono_in_migration (π : ℝ) (p q : PopGenParameters) (V_E : ℝ)
    (hπ : 0 < π) (hπ1 : π < 1) (hE : 0 < V_E)
    (hNe : p.Ne = q.Ne) (hmu : p.mu = q.mu) (hV : p.V_A = q.V_A)
    (hlt : p.mig < q.mig) (hflow : 0 < p.mu + p.mig) :
    deployedBrier π q V_E < deployedBrier π p V_E := by
  unfold deployedBrier
  rw [hV]
  exact brier_anti_in_r2 π _ _ hπ hπ1
    (r2_momentsUnderDrift_anti q.V_A V_E q.fstEquilibrium p.fstEquilibrium q.V_A_pos hE
      (PopGenParameters.fstEquilibrium_lt_of_mig_lt p q hNe hmu hlt)
      (p.fstEquilibrium_lt_one hflow))

/-- **More mutation, better Brier score.** -/
theorem deployedBrier_mono_in_mutation (π : ℝ) (p q : PopGenParameters) (V_E : ℝ)
    (hπ : 0 < π) (hπ1 : π < 1) (hE : 0 < V_E)
    (hNe : p.Ne = q.Ne) (hmig : p.mig = q.mig) (hV : p.V_A = q.V_A)
    (hlt : p.mu < q.mu) (hflow : 0 < p.mu + p.mig) :
    deployedBrier π q V_E < deployedBrier π p V_E := by
  unfold deployedBrier
  rw [hV]
  exact brier_anti_in_r2 π _ _ hπ hπ1
    (r2_momentsUnderDrift_anti q.V_A V_E q.fstEquilibrium p.fstEquilibrium q.V_A_pos hE
      (PopGenParameters.fstEquilibrium_lt_of_mu_lt p q hNe hmig hlt)
      (p.fstEquilibrium_lt_one hflow))

/-- **Larger effective size, better Brier score.** -/
theorem deployedBrier_mono_in_Ne (π : ℝ) (p q : PopGenParameters) (V_E : ℝ)
    (hπ : 0 < π) (hπ1 : π < 1) (hE : 0 < V_E)
    (hmu : p.mu = q.mu) (hmig : p.mig = q.mig) (hV : p.V_A = q.V_A)
    (hlt : p.Ne < q.Ne) (hflow2 : 0 < p.mu + 2 * p.mig) (hflow : 0 < p.mu + p.mig) :
    deployedBrier π q V_E < deployedBrier π p V_E := by
  unfold deployedBrier
  rw [hV]
  exact brier_anti_in_r2 π _ _ hπ hπ1
    (r2_momentsUnderDrift_anti q.V_A V_E q.fstEquilibrium p.fstEquilibrium q.V_A_pos hE
      (PopGenParameters.fstEquilibrium_lt_of_Ne_lt p q hmu hmig hflow2 hlt)
      (p.fstEquilibrium_lt_one hflow))

/-- **Deployed Brier at the source is the heritability complement**, scaled by the
prevalence variance: the anchor the deployed value departs from. -/
theorem deployedBrier_at_no_flow_bound (π V_A V_E : ℝ) (hV : 0 < V_A) (hE : 0 ≤ V_E) :
    brier π (momentsUnderDrift V_A V_E 0) = π * (1 - π) * (1 - share V_A V_E) := by
  unfold brier complement
  rw [r2_momentsUnderDrift_at_source V_A V_E hV hE]

/-- **A longer split, worse Brier score.** The split-coordinate route into the binary
metric, so a result stated in divergence time and one stated in migration rate reach the
same place. -/
theorem brier_deployedR2FromTau_anti (π V_A V_E t₁ t₂ : ℝ) (hπ : 0 < π) (hπ1 : π < 1)
    (hV : 0 < V_A) (hE : 0 < V_E) (h0 : 0 ≤ t₁) (hlt : t₁ < t₂) :
    brier π (momentsUnderDrift V_A V_E (fstFromTau t₁))
      < brier π (momentsUnderDrift V_A V_E (fstFromTau t₂)) := by
  have hf1 : fstFromTau t₁ < fstFromTau t₂ := by
    unfold fstFromTau saturation
    rw [div_lt_div_iff₀ (by linarith) (by linarith)]
    nlinarith
  have hlt2 : fstFromTau t₂ < 1 := by
    unfold fstFromTau saturation
    rw [div_lt_one (by linarith)]
    linarith
  exact brier_momentsUnderDrift_mono π V_A V_E (fstFromTau t₁) (fstFromTau t₂) hπ hπ1 hV hE
    hf1 hlt2


/-! ### The deme count reaches the metric

The island lattice is not decoration: the deme correction is a factor of two at the
two-population split, and a factor of two on the migration term is a factor on the
deployed metric. These theorems carry `nDemes` all the way through. -/

/-- **Deployed `R²` from raw island parameters.** The composition that takes
`(Nₑ, m, μ, d)` -- including the deme count -- to a deployed metric. -/
noncomputable def deployedR2FromIsland (Ne m μ nDemes V_A V_E : ℝ) : ℝ :=
  (momentsUnderDrift V_A V_E (fstIslandEquilibrium Ne m μ nDemes)).r2

/-- **The two-deme reading and the record's reading agree.** `PopGenParameters`'
`1/(1 + θ + 2M)` is the island law at `d = 2`, so the metric it produces is the island
metric at two demes -- and a reader who took the record for the many-deme law was reading
the wrong deployment. -/
theorem deployedR2_eq_island_two_demes (p : PopGenParameters) (V_E : ℝ) :
    deployedR2 p V_E = deployedR2FromIsland p.Ne p.mig p.mu 2 p.V_A V_E := by
  unfold deployedR2 deployedR2FromIsland
  rw [p.fstEquilibrium_eq_island_two_demes]

/-- **More demes, more differentiation between any two of them, less transferable score.**

The deme correction `d/(d-1)` FALLS with `d`, so the effective migration between a given
pair falls, so `F_ST` rises and the metric drops. Counter-intuitive read as "more
populations means more mixing" and correct read as "a fixed per-pair migration rate
spreads a deme's immigration over more sources". -/
theorem deployedR2FromIsland_anti_in_demes (Ne m μ d₁ d₂ V_A V_E : ℝ)
    (hV : 0 < V_A) (hE : 0 < V_E) (hNe : 0 < Ne) (hm : 0 < m) (hμ : 0 ≤ μ)
    (h1 : 1 < d₁) (hlt : d₁ < d₂) :
    deployedR2FromIsland Ne m μ d₂ V_A V_E < deployedR2FromIsland Ne m μ d₁ V_A V_E := by
  have hc : ∀ d : ℝ, 1 < d → 0 < islandDemeCorrection d := by
    intro d hd
    unfold islandDemeCorrection ratio
    exact div_pos (by linarith) (by linarith)
  have hflowpos : ∀ d : ℝ, 1 < d → 0 < scaledFlow Ne m μ d := by
    intro d hd
    have hcd := hc d hd
    have h4 : (0:ℝ) < 4 * Ne := by linarith
    have p1 : 0 < 4 * Ne * m * islandDemeCorrection d :=
      mul_pos (mul_pos h4 hm) hcd
    have p2 : 0 ≤ 4 * Ne * μ := by positivity
    unfold scaledFlow
    rw [scaledMigrationRate_eq, scaledMutationRate_eq]
    linarith
  have hlt1 : ∀ d : ℝ, 1 < d → fstIslandEquilibrium Ne m μ d < 1 := by
    intro d hd
    have := hflowpos d hd
    unfold fstIslandEquilibrium fstFromFlow
    rw [div_lt_one (by linarith)]
    linarith
  have hcorr : islandDemeCorrection d₂ < islandDemeCorrection d₁ := by
    unfold islandDemeCorrection ratio
    rw [div_lt_div_iff₀ (by linarith) (by linarith)]
    nlinarith
  have hf : fstIslandEquilibrium Ne m μ d₁ < fstIslandEquilibrium Ne m μ d₂ := by
    unfold fstIslandEquilibrium
    have hd2 : (1:ℝ) < d₂ := by linarith
    refine fstFromFlow_lt_of_lt _ _ (le_of_lt (hflowpos d₂ hd2)) ?_
    have h4 : (0:ℝ) < 4 * Ne := by linarith
    have key : 4 * Ne * m * islandDemeCorrection d₂ < 4 * Ne * m * islandDemeCorrection d₁ :=
      by
        have hm4 : 0 < 4 * Ne * m := mul_pos h4 hm
        exact (mul_lt_mul_left hm4).mpr hcorr
    unfold scaledFlow
    rw [scaledMigrationRate_eq, scaledMutationRate_eq]
    linarith
  exact r2_momentsUnderDrift_anti V_A V_E (fstIslandEquilibrium Ne m μ d₁)
    (fstIslandEquilibrium Ne m μ d₂) hV hE hf (hlt1 d₂ (by linarith : (1:ℝ) < d₂))

/-- **The calibration slope is one on the island route too.** Third statement of the same
warning, now with the deme count carried: no island configuration produces a
miscalibrated score under pure drift. -/
theorem deployedR2FromIsland_slope (Ne m μ nDemes V_A V_E : ℝ) (hV : 0 < V_A)
    (hf : fstIslandEquilibrium Ne m μ nDemes < 1) :
    (momentsUnderDrift V_A V_E (fstIslandEquilibrium Ne m μ nDemes)).calibrationSlope = 1 :=
  calibrationSlope_momentsUnderDrift V_A V_E _ hV hf

/-- **And the mean squared error is the environmental variance on the island route.** -/
theorem deployedR2FromIsland_mse (Ne m μ nDemes V_A V_E : ℝ) :
    (momentsUnderDrift V_A V_E (fstIslandEquilibrium Ne m μ nDemes)).mse = V_E :=
  mse_momentsUnderDrift V_A V_E _

/-! ### The split route, for the rest of the family -/

/-- **The calibration slope after a clean split is one at every divergence time.** -/
theorem deployedR2FromTau_slope (V_A V_E tau : ℝ) (hV : 0 < V_A) (h : 0 ≤ tau) :
    (momentsUnderDrift V_A V_E (fstFromTau tau)).calibrationSlope = 1 := by
  refine calibrationSlope_momentsUnderDrift V_A V_E _ hV ?_
  unfold fstFromTau saturation
  rw [div_lt_one (by linarith)]
  linarith

/-- **And the mean squared error is flat along the split too.** Every metric except `R²`
and the metrics that are functions of `R²` is blind to a clean split. -/
theorem deployedR2FromTau_mse (V_A V_E tau : ℝ) :
    (momentsUnderDrift V_A V_E (fstFromTau tau)).mse = V_E :=
  mse_momentsUnderDrift V_A V_E _

/-- **At the split the deployed metric is the heritability**, so the whole decay is a
departure from a value the source population fixes. -/
theorem deployedR2FromTau_bounded (V_A V_E tau : ℝ) (hV : 0 < V_A) (hE : 0 ≤ V_E)
    (h : 0 ≤ tau) :
    (momentsUnderDrift V_A V_E (fstFromTau tau)).r2 ≤ share V_A V_E := by
  have hf : fstFromTau tau < 1 := by
    unfold fstFromTau saturation
    rw [div_lt_one (by linarith)]
    linarith
  have hf0 : 0 ≤ fstFromTau tau := by
    unfold fstFromTau saturation
    positivity
  have := r2_momentsUnderDrift_le_source V_A V_E (fstFromTau tau) hV hE hf0 hf
  rwa [r2_momentsUnderDrift_at_source V_A V_E hV hE] at this

/-- **The AUC argument decays along the split.** Discrimination falls with divergence
time, by the same route as `R²`. -/
theorem aucArgument_deployedR2FromTau_anti (V_A V_E t₁ t₂ : ℝ) (hV : 0 < V_A)
    (hE : 0 < V_E) (h0 : 0 ≤ t₁) (hlt : t₁ < t₂) :
    aucArgument (momentsUnderDrift V_A V_E (fstFromTau t₂))
      < aucArgument (momentsUnderDrift V_A V_E (fstFromTau t₁)) := by
  have hf1 : fstFromTau t₁ < fstFromTau t₂ := by
    unfold fstFromTau saturation
    rw [div_lt_div_iff₀ (by linarith) (by linarith)]
    nlinarith
  have hlt2 : fstFromTau t₂ < 1 := by
    unfold fstFromTau saturation
    rw [div_lt_one (by linarith)]
    linarith
  have hf0 : 0 ≤ fstFromTau t₁ := by
    unfold fstFromTau saturation; positivity
  exact aucArgument_momentsUnderDrift_anti V_A V_E (fstFromTau t₁) (fstFromTau t₂) hV hE
    hf1 hlt2 hf0

/-- **The portability ratio along a split.** What a report comparing a target `R²` to a
source `R²` is measuring, expressed in divergence time. -/
noncomputable def portabilityRatioFromTau (V_A V_E tau : ℝ) : ℝ :=
  portabilityRatio V_A V_E (fstFromTau tau)

/-- **A longer split gives a smaller portability ratio.** -/
theorem portabilityRatioFromTau_anti (V_A V_E t₁ t₂ : ℝ) (hV : 0 < V_A) (hE : 0 < V_E)
    (h0 : 0 ≤ t₁) (hlt : t₁ < t₂) :
    portabilityRatioFromTau V_A V_E t₂ < portabilityRatioFromTau V_A V_E t₁ := by
  have hsrc : 0 < (momentsUnderDrift V_A V_E 0).r2 := by
    rw [r2_momentsUnderDrift_at_source V_A V_E hV (le_of_lt hE)]
    unfold share; positivity
  unfold portabilityRatioFromTau portabilityRatio ratio
  exact div_lt_div_of_pos_right
    (deployedR2FromTau_anti V_A V_E t₁ t₂ hV hE h0 hlt) hsrc


end ScoreMoments

end Descent.Core
