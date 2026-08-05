/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Foundations.TransportIdentities

namespace Descent

noncomputable section

/-!
# The portability master theorem: arbitrary generative input to exact output metrics

Every other portability module in this corpus fixes a *shape* first -- a diagonal LD
matrix, a scalar `F_ST`, an exponential decay chart, a shared-LD assumption -- and then
computes inside it.  This module fixes nothing.  It takes

* an arbitrary index set `J` of scored variants and `L` of causal variants (finite, no
  relation between them assumed: `J` need not contain, tag, or even intersect `L`),
* an arbitrary positive linear expectation functional per population (`ExpFunctional`,
  so no measure, no Gaussianity, no independence, no exchangeability),
* arbitrary scored genotypes `X : Ω → J → ℝ` and causal genotypes `C : Ω → L → ℝ`
  (any allele frequencies, any LD, any admixture, any ploidy coding, any standardisation),
* an arbitrary **population-specific** causal effect vector `β : L → ℝ` (allelic
  turnover, sign flips and effect-size heterogeneity are the general case here,
  not a perturbation of a shared vector),
* an arbitrary residual `h : Ω → ℝ` carrying everything that is not additive in `C`:
  environment, gene-environment interaction, dominance, epistasis, population
  stratification, ascertainment, measurement error, and causal variants outside `L`,
* an arbitrary deployed weight vector `w : J → ℝ`.

`w` is arbitrary on purpose.  A theory that only covered the source ERM optimum would
not cover clumping-and-thresholding, LDpred, lassosum, a winner's-cursed marginal-effect
score, a shrunk score, a multi-ancestry meta-analysed score, or a score someone rounded
to two decimal places.  Every one of those is a `w`, so every one of them is covered
by the same identities.

and returns the **exact** value of each deployed metric -- score variance, predictive
covariance, outcome variance, MSE, calibration slope, calibration intercept, and `R²` --
as a closed algebraic expression in those inputs.  No approximation, no limit, no
asymptotic regime, no side condition beyond the finiteness of the two index sets.

The results are of five kinds.

1. **Exact metric laws** (`§2`).  Each output metric equals a named closed form in the
   input moments.  These are identities, not bounds.
2. **The transport decomposition** (`§3`).  The source-to-target movement of each metric
   splits into named channels with *no remainder term*, and the `R²` ratio factors into
   three factors -- alignment, dispersion, outcome variance -- with allele-frequency
   change not among them, because it enters only through the objects the first two are
   built from.
3. **Completeness** (`§4`).  A three-real statistic is proved to determine `R²` and the
   calibration slope (sufficiency); its achievable set is proved to be exactly the
   Cauchy-Schwarz cone (range); and each of its three coordinates is proved separately
   necessary by realisable four-individual witnesses (minimality).  Sufficiency without
   minimality would be satisfied by the whole input tuple, and minimality without
   sufficiency by any three functionally independent quantities; together with the range
   statement they say the statistic is a coordinate system on the deployments rather
   than a lossy summary of a larger space.
4. **Recalibration** (`§5`).  The MSE of an arbitrary affine correction, its exact
   minimum `Var(Y)·(1 - R²)`, and the invariance of `R²` under the correction.  That
   pair is the exact division of portability loss into a repairable part -- the affine
   gauge -- and an unrepairable one, with nothing in between.
5. **The training leg and the scope boundary** (`§7`, `§8`).  A score fitted to a
   population is exactly calibrated in it, deploying any weights costs the target oracle
   plus the target LD quadratic form of the weight error with no cross term, and the
   weight error is two different matrix inverses applied to two different vectors.  `§8`
   then fixes the scope from the other side: two deployments identical in every
   second-moment metric refer twice as many people above a cut-off as each other, so the
   statistic covers the second-moment metrics and provably nothing beyond them.

`§6` names the junk branches, `§0` supplies the non-degenerate expectation functionals
the witnesses are built from, and `§1b` points at the covariance algebra in
`Descent.Foundations.TransportIdentities` that all of `§2` is an instance of.

## What is deliberately *not* proved here

Nothing here predicts a metric from a *scalar genetic distance*, because
`§4`'s minimality witnesses show no scalar can. Nothing here derives the input
moments from a demographic history; that is the job of `Descent.PopGen`, and the
interface between the two layers is the moment tuple this module consumes.
-/

section FiniteWitnesses

/-!
## §0 Non-degenerate expectation functionals

`ExpFunctional.evalAt` inhabits `ExpFunctional Ω`, which is what makes theorems over it
non-vacuous, but it is a Dirac: every variance it reports is `0`, every covariance is
`0`, and every `R²` built from it is the junk value `0/0`. Statements of the form "there
exist two deployments with different `R²`" cannot be witnessed by it at all.

`weightedExp` is the general finite-support expectation: an arbitrary probability vector
on an arbitrary finite type. It is what the minimality witnesses of `§4` are built from,
and it is realistic in the only sense that matters for a witness -- a finite population
of individuals with rational frequencies is an actual population, not an idealisation of
one.
-/

variable {Ω : Type*} [Fintype Ω]

/-- Expectation against an arbitrary finitely-supported probability vector. -/
def weightedExp (p : Ω → ℝ) (hp : ∀ ω, 0 ≤ p ω) (hsum : ∑ ω, p ω = 1) :
    ExpFunctional Ω where
  eval f := ∑ ω, p ω * f ω
  add_eval f g := by
    simp [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  smul_eval c f := by
    simp [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun ω _ ↦ by ring
  const_one := by simpa using hsum
  nonneg_eval f hf :=
    Finset.sum_nonneg fun ω _ ↦ mul_nonneg (hp ω) (hf ω)

@[simp] theorem weightedExp_apply (p : Ω → ℝ) (hp : ∀ ω, 0 ≤ p ω) (hsum : ∑ ω, p ω = 1)
    (f : Ω → ℝ) : weightedExp p hp hsum f = ∑ ω, p ω * f ω := rfl

/-- The uniform expectation on a nonempty finite type: the empirical distribution of a
finite population in which each individual is one observation. -/
def uniformExp (Ω : Type*) [Fintype Ω] [Nonempty Ω] : ExpFunctional Ω :=
  weightedExp (fun _ ↦ (Fintype.card Ω : ℝ)⁻¹)
    (fun _ ↦ by positivity)
    (by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      field_simp)

@[simp] theorem uniformExp_apply [Nonempty Ω] (f : Ω → ℝ) :
    uniformExp Ω f = ∑ ω, (Fintype.card Ω : ℝ)⁻¹ * f ω := rfl

/-- **A non-degenerate expectation functional exists**, and reports a nonzero variance.

    This is what `ExpFunctional.evalAt` cannot do.  Every `§4` witness needs a positive
    score variance somewhere -- an `R²` with a zero denominator is the junk `0`, so a
    pair of deployments distinguished only through such an `R²` would distinguish
    nothing. -/
theorem variance_uniformExp_two :
    variance (uniformExp (Fin 2)) (fun i ↦ (i : ℝ)) = 1 / 4 := by
  have hcard : (Fintype.card (Fin 2) : ℝ) = 2 := by simp
  unfold variance
  simp [uniformExp_apply, Fin.sum_univ_two]
  norm_num

end FiniteWitnesses

section GenerativeLayer

/-!
## §1 The generative input and the deployed metrics
-/

variable {Ω J L : Type*} [Fintype J] [DecidableEq J] [Fintype L] [DecidableEq L]

/-- **One deployment population.**

    Everything a population contributes to a polygenic score's behaviour, with no
    structure imposed on any of it.  `E` is any positive normalised linear functional;
    `X` and `C` are any real-valued genotype codings; `β` is this population's causal
    effect vector, unrelated to any other population's; `h` is any residual.

    The phenotype is `Cᵀβ + h`.  That is not an additivity assumption: `h` is an
    arbitrary function on `Ω`, so any dominance, epistatic, gene-environment or
    unmeasured-locus contribution is inside it, and `Cᵀβ` is then *by definition* the
    part of the phenotype additive in the `L` coordinates. The split is a definition of
    `β`, not a restriction on the phenotype. -/
structure DeploymentPopulation (Ω J L : Type*) where
  /-- The population's expectation functional. -/
  E : ExpFunctional Ω
  /-- Scored (genotyped, imputed, or otherwise available) variant codings. -/
  X : Ω → J → ℝ
  /-- Causal variant codings. -/
  C : Ω → L → ℝ
  /-- This population's causal effects.  Population-specific: turnover is the default. -/
  β : L → ℝ
  /-- Everything not additive in `C`. -/
  h : Ω → ℝ

namespace DeploymentPopulation

variable (P : DeploymentPopulation Ω J L)

/-- The realised phenotype, `Cᵀβ + h`. -/
def phenotype : Ω → ℝ := fun ω ↦ causalSignal P.β P.C ω + P.h ω

/-- The deployed score `wᵀX`. -/
def score (w : J → ℝ) : Ω → ℝ := linScore w P.X

/-- Scored-variant covariance ("LD") matrix in this population. -/
def sigmaX : Matrix J J ℝ := covarianceMatrix P.E P.X

/-- Causal-variant covariance matrix in this population. -/
def sigmaC : Matrix L L ℝ := covarianceMatrix P.E P.C

/-- Scored-to-causal covariance ("tagging") matrix in this population. -/
def kappa : Matrix J L ℝ := predictorCausalCovariance P.E P.X P.C

/-- Scored-variant-to-residual covariance: stratification, ancestry-correlated
environment, and any other route by which the residual is predictable from `X`. -/
def contextX : J → ℝ := contextCrossCovVector P.E P.X P.h

/-- Causal-variant-to-residual covariance. -/
def contextC : L → ℝ := contextCrossCovVector P.E P.C P.h

/-! ### The exact output metrics

Each is the textbook definition applied to the realised score and phenotype in this
population.  No closed form is built into any of them; the closed forms are the theorems
of `§2`. -/

/-- `Var(S)`. -/
def scoreVariance (w : J → ℝ) : ℝ := variance P.E (P.score w)

/-- `Cov(S, Y)`. -/
def predictiveCovariance (w : J → ℝ) : ℝ := covariance P.E (P.score w) P.phenotype

/-- `Var(Y)`. -/
def outcomeVariance : ℝ := variance P.E P.phenotype

/-- `E[(Y - S)²]`, the raw deployed mean squared error. -/
def deployedMse (w : J → ℝ) : ℝ := expMse P.E P.phenotype (P.score w)

/-- `Cov(S,Y)/Var(S)`, the regression-of-`Y`-on-`S` slope: `1` for a calibrated score. -/
def calibrationSlope (w : J → ℝ) : ℝ := P.predictiveCovariance w / P.scoreVariance w

/-- `E[Y] - slope · E[S]`. -/
def calibrationIntercept (w : J → ℝ) : ℝ :=
  P.E P.phenotype - P.calibrationSlope w * P.E (P.score w)

/-- `Cov(S,Y)² / (Var(S) · Var(Y))`, the squared Pearson correlation.

    This is the `R²` that portability studies report: the variance explained by the
    *best affine rescaling* of the score, not by the score as literally emitted.  It is
    the metric that is insensitive to the intercept and slope errors `calibrationSlope`
    and `calibrationIntercept` measure, which is exactly why the three are reported
    together and why `§4` needs all three. -/
def r2 (w : J → ℝ) : ℝ :=
  P.predictiveCovariance w ^ 2 / (P.scoreVariance w * P.outcomeVariance)

end DeploymentPopulation

end GenerativeLayer

section Bilinearity

/-!
## §1b Bilinearity of covariance on linear scores

The metric laws of `§2` are all instances of one fact: `covariance` is bilinear, so a
covariance between two linear combinations of coordinate families is the quadratic form
of the coordinate covariance matrix.  The lemmas themselves --- `covariance_comm`,
`variance_add`, `covariance_linScore_left`, `covariance_linScore_linScore`,
`variance_linScore`, `covariance_linScore_eq_dot_crossCov`, `variance_affine`,
`covariance_affine_right` --- are facts about an arbitrary positive linear functional
with no portability content, so they live in `Descent.Foundations.TransportIdentities`
alongside the rest of the covariance algebra rather than here.
-/

end Bilinearity

section ExactMetricLaws

/-!
## §2 The exact metric laws

Each theorem below evaluates one deployed metric as a closed algebraic expression in the
population's moment tuple `(Σ_X, Σ_C, K, c_X, c_C, Var h)` and the deployed weights `w`.
They hold in *every* population, source or target: there is no "source formula" and
"target formula", which is the point -- portability is then a statement about two
evaluations of one law, not about two laws.
-/

variable {Ω J L : Type*} [Fintype J] [DecidableEq J] [Fintype L] [DecidableEq L]
variable (P : DeploymentPopulation Ω J L) (w : J → ℝ)

namespace DeploymentPopulation

omit [Fintype L] [DecidableEq L] in
/-- **Exact score-variance law.**  `Var(S) = wᵀ Σ_X w`.

    No assumption on `X` at all: any LD structure, any admixture, any coding. -/
theorem scoreVariance_eq : P.scoreVariance w = dot w (P.sigmaX.mulVec w) :=
  variance_linScore P.E P.X w

/-- **Exact predictive-covariance law.**  `Cov(S, Y) = wᵀ K β + wᵀ c_X`.

    The first term is the genetic signal the score captures: tagging (`K`) composed with
    this population's effects (`β`).  The second is the part of the score's predictive
    covariance that runs through the residual rather than through `C` -- stratification
    and ancestry-correlated environment live here, and they contribute to a measured
    `R²` exactly as genuine signal does.  Nothing in the metric separates them, which is
    a fact about the metric and not a limitation of this proof. -/
theorem predictiveCovariance_eq :
    P.predictiveCovariance w = dot w (P.kappa.mulVec P.β) + dot w P.contextX := by
  unfold predictiveCovariance phenotype score
  rw [covariance_linScore_eq_dot_crossCov]
  have hsplit : contextCrossCovVector P.E P.X
        (fun ω ↦ causalSignal P.β P.C ω + P.h ω)
      = P.kappa.mulVec P.β + P.contextX := by
    have h := crossCovVector_decomposition P.E P.X P.C P.β P.h
    simpa [contextCrossCovVector, crossCovVector, kappa, contextX] using h
  rw [hsplit]
  unfold dot
  simp [Pi.add_apply, mul_add, Finset.sum_add_distrib]

omit [Fintype L] [DecidableEq L] in
/-- **Exact score-mean law.**  `E[S] = wᵀ μ_X`. -/
theorem eval_score_eq : P.E (P.score w) = dot w (fun j ↦ P.E (fun ω ↦ P.X ω j)) :=
  eval_linScore P.E P.X w

omit [Fintype J] [DecidableEq J] in
/-- **Exact phenotype-mean law.**  `E[Y] = βᵀ μ_C + E[h]`. -/
theorem eval_phenotype_eq :
    P.E P.phenotype = dot P.β (fun l ↦ P.E (fun ω ↦ P.C ω l)) + P.E P.h := by
  unfold phenotype
  have hsplit : (fun ω ↦ causalSignal P.β P.C ω + P.h ω)
      = causalSignal P.β P.C + P.h := rfl
  rw [hsplit, P.E.add_eval]
  congr 1
  exact eval_linScore P.E P.C P.β

omit [Fintype J] [DecidableEq J] in
/-- **Exact outcome-variance law.**  `Var(Y) = βᵀ Σ_C β + 2 βᵀ c_C + Var(h)`.

    The denominator of `R²` is a property of the *population*, not of the score.  Two
    populations with identical genetics and different residual variance report different
    `R²` for the same score, and this identity is where that enters. -/
theorem outcomeVariance_eq :
    P.outcomeVariance
      = dot P.β (P.sigmaC.mulVec P.β) + 2 * dot P.β P.contextC + variance P.E P.h := by
  unfold outcomeVariance phenotype
  rw [variance_add]
  congr 1
  · congr 1
    · exact variance_linScore P.E P.C P.β
    · congr 1
      exact covariance_linScore_eq_dot_crossCov P.E P.C P.β P.h

/-- **Exact `R²` law: the master formula.**

    Every input of the theory appears once, and nothing else does:
    `R² = (wᵀKβ + wᵀc_X)² / ((wᵀΣ_X w)(βᵀΣ_Cβ + 2βᵀc_C + Var h))`.

    Read it as the answer to "what is the deployed `R²`": given any population and any
    score, this expression is its exact value.  Every portability phenomenon in the
    literature is a statement about how the six inputs on the right differ between two
    populations, and `§3` turns each such difference into its exact effect on the left. -/
theorem r2_eq :
    P.r2 w =
      (dot w (P.kappa.mulVec P.β) + dot w P.contextX) ^ 2 /
        (dot w (P.sigmaX.mulVec w) *
          (dot P.β (P.sigmaC.mulVec P.β) + 2 * dot P.β P.contextC + variance P.E P.h)) := by
  unfold r2
  rw [P.predictiveCovariance_eq w, P.scoreVariance_eq w, P.outcomeVariance_eq]

/-- **Exact calibration-slope law.** -/
theorem calibrationSlope_eq :
    P.calibrationSlope w =
      (dot w (P.kappa.mulVec P.β) + dot w P.contextX) / dot w (P.sigmaX.mulVec w) := by
  unfold calibrationSlope
  rw [P.predictiveCovariance_eq w, P.scoreVariance_eq w]

/-- **Exact calibration-intercept law.**

    The intercept is the only metric here that reads the population's *first* moments.
    A score can therefore be perfectly discriminating and perfectly sloped and still sit
    at the wrong level in a target, purely because the mean genotype moved -- which is
    what an allele-frequency shift does and what an `R²` comparison cannot see. -/
theorem calibrationIntercept_eq :
    P.calibrationIntercept w
      = (dot P.β (fun l ↦ P.E (fun ω ↦ P.C ω l)) + P.E P.h)
        - ((dot w (P.kappa.mulVec P.β) + dot w P.contextX) / dot w (P.sigmaX.mulVec w))
          * dot w (fun j ↦ P.E (fun ω ↦ P.X ω j)) := by
  unfold calibrationIntercept
  rw [P.eval_phenotype_eq, P.calibrationSlope_eq w, P.eval_score_eq w]

/-- **Exact deployed-MSE law.**  `E[(Y-S)²] = Var Y + Var S - 2 Cov(S,Y) + (E S - E Y)²`,
    then each term by its own law.

    The raw MSE is the only metric here that is not invariant to the score's affine
    gauge, which is why it carries the bias term and why a score can have a perfect `R²`
    and an arbitrarily bad MSE. -/
theorem deployedMse_eq :
    P.deployedMse w =
      (dot P.β (P.sigmaC.mulVec P.β) + 2 * dot P.β P.contextC + variance P.E P.h)
        + dot w (P.sigmaX.mulVec w)
        - 2 * (dot w (P.kappa.mulVec P.β) + dot w P.contextX)
        + (P.E (P.score w) - P.E P.phenotype) ^ 2 := by
  unfold deployedMse
  rw [mse_eq_variance_add_variance_sub_two_cov_add_bias_sq]
  rw [show variance P.E P.phenotype = P.outcomeVariance from rfl,
    show variance P.E (P.score w) = P.scoreVariance w from rfl,
    show covariance P.E P.phenotype (P.score w) = P.predictiveCovariance w from
      covariance_comm _ _ _]
  rw [P.outcomeVariance_eq, P.scoreVariance_eq w, P.predictiveCovariance_eq w]
  unfold bias
  ring

end DeploymentPopulation

end ExactMetricLaws

section Transport

/-!
## §3 Transport: the exact channel decomposition

A deployment is one weight vector read in two populations.  The populations may live on
different sample spaces and carry different expectation functionals; all they share is
the scored-variant index `J` and the causal index `L`.  Sharing `L` costs nothing: take
`L` to be the union of the two causal sets and set `β l = 0` in a population where `l` is
not causal, which is exactly what "the variant is causal only over there" means.

Every theorem in this section is an identity with **no remainder term**.  That is the
content: the channels named below are not a decomposition chosen for interpretability
with an error term swept into the last line, they exhaust the difference.
-/

variable {ΩS ΩT J L : Type*} [Fintype J] [DecidableEq J] [Fintype L] [DecidableEq L]

/-- **One score deployed in two populations.** -/
structure Deployment (ΩS ΩT J L : Type*) where
  /-- The population the score was trained in (or, more precisely, the one it is being
  compared against; nothing here assumes `w` was fitted in it). -/
  source : DeploymentPopulation ΩS J L
  /-- The population the score is deployed in. -/
  target : DeploymentPopulation ΩT J L
  /-- The deployed weights.  One vector, read in both populations: this is what makes
  the comparison a portability question rather than two unrelated model fits. -/
  w : J → ℝ

namespace Deployment

variable (D : Deployment ΩS ΩT J L)

/-! ### The three channels of signal transport -/

/-- **Tagging-shift channel.**  The change in scored-to-causal covariance, read against
the *source* effect vector.  This is the linkage-disequilibrium term: the same causal
alleles, tagged differently. -/
def taggingShift : ℝ :=
  dot D.w ((D.target.kappa - D.source.kappa).mulVec D.source.β)

/-- **Effect-turnover channel.**  The change in causal effects, read against the
*target* tagging.  Sign flips, effect-size heterogeneity and variants causal in one
population only all land here. -/
def effectTurnover : ℝ :=
  dot D.w (D.target.kappa.mulVec (D.target.β - D.source.β))

/-- **Context-shift channel.**  The change in the covariance between the scored variants
and everything not additive in `C`: stratification, ancestry-correlated environment,
and any residual predictability of `h` from `X`. -/
def contextShift : ℝ :=
  dot D.w (D.target.contextX - D.source.contextX)

/-- **Linkage channel on the score's own variance.**  The scored-variant covariance
matrix changes, so the same weights produce a differently-dispersed score. -/
def scoreVarianceShift : ℝ :=
  dot D.w ((D.target.sigmaX - D.source.sigmaX).mulVec D.w)

/-- **Exact three-channel law for predictive covariance.**

    `Cov_T(S,Y) - Cov_S(S,Y) = tagging shift + effect turnover + context shift`,
    with nothing left over.

    The asymmetry of the first two channels -- the tagging shift is read against the
    source effects and the turnover against the target tagging -- is not a convention
    that could have gone the other way and stayed exact.  It is the exact algebraic
    split of `K_T β_T - K_S β_S`, and the mirror-image split (target effects against the
    tagging shift, source tagging against the turnover) is the equally exact *other*
    grouping.  What is not available is a symmetric split without an interaction term:
    the product `(K_T - K_S)(β_T - β_S)` has to be charged to one channel or the other,
    and here it is charged to turnover. -/
theorem predictiveCovariance_transport :
    D.target.predictiveCovariance D.w - D.source.predictiveCovariance D.w
      = D.taggingShift + D.effectTurnover + D.contextShift := by
  rw [D.target.predictiveCovariance_eq D.w, D.source.predictiveCovariance_eq D.w]
  unfold taggingShift effectTurnover contextShift
  rw [Matrix.sub_mulVec, Matrix.mulVec_sub, dot_sub_right', dot_sub_right', dot_sub_right']
  ring

omit [Fintype L] [DecidableEq L] in
/-- **Exact law for the score-variance shift.**  Only the scored-variant covariance
    matrix can move it: neither the effects nor the residual appear.

    This is why a score's variance changes across populations even when nothing about
    the trait's genetics has changed.  It is also the only channel that moves the
    calibration slope without moving the signal, which is what
    `dispersion_shift_lowers_slope_and_r2` isolates. -/
theorem scoreVariance_transport :
    D.target.scoreVariance D.w - D.source.scoreVariance D.w = D.scoreVarianceShift := by
  rw [D.target.scoreVariance_eq D.w, D.source.scoreVariance_eq D.w]
  unfold scoreVarianceShift
  rw [Matrix.sub_mulVec, dot_sub_right']

/-! ### The exact `R²` factorisation -/

/-- The squared-signal factor: how much the score's covariance with the phenotype
changed, squared because `R²` is quadratic in it. -/
def alignmentFactor : ℝ :=
  (D.target.predictiveCovariance D.w / D.source.predictiveCovariance D.w) ^ 2

/-- The dispersion factor: how much the score's own variance changed. -/
def dispersionFactor : ℝ :=
  D.source.scoreVariance D.w / D.target.scoreVariance D.w

/-- The outcome-variance factor: how much the phenotype's total variance changed.
Environmental heterogeneity between populations is entirely inside this factor, and
nothing genetic is. -/
def outcomeFactor : ℝ :=
  D.source.outcomeVariance / D.target.outcomeVariance

omit [DecidableEq J] [DecidableEq L] in
/-- **The exact `R²` portability factorisation.**

    `R²_T = R²_S × alignment × dispersion × outcome`, exactly, with exactly three
    factors and no residual.

    This is the theorem the informal "portability ratio = AF × LD × effect × env"
    decomposition is reaching for, and it differs from it in two ways that matter.
    First, it is proved rather than posited, from the generative model of `§1` with no
    shape assumption anywhere.  Second, the factorisation that comes out has *three*
    factors, not four, and allele-frequency change is not one of them: allele
    frequencies enter this identity only through `Σ_X` and `K`, which are also where LD
    and tagging enter, so on the right-hand side above there is no place an `F_ST` could
    occupy on its own.

    Read that as a fact about this identity, which is what is proved, and not as a
    nonexistence theorem about all possible factorisations, which is not.  What rules
    out an `F_ST`-indexed prediction of `R²` is `§4`'s
    `no_score_side_summary_determines_r2`, and it rules out considerably more than
    `F_ST`.

    The hypotheses are exactly the non-degeneracy of the *source* deployment: a score
    with no variance, in a population with no phenotypic variance, or with no covariance
    between the two, has no `R²` to be portable. Target degeneracy needs no hypothesis --
    both sides are then `0`. -/
theorem r2_transport_factorisation
    (hvar : D.source.scoreVariance D.w ≠ 0)
    (hout : D.source.outcomeVariance ≠ 0)
    (hcov : D.source.predictiveCovariance D.w ≠ 0) :
    D.target.r2 D.w
      = D.source.r2 D.w * D.alignmentFactor * D.dispersionFactor * D.outcomeFactor := by
  unfold DeploymentPopulation.r2 alignmentFactor dispersionFactor outcomeFactor
  by_cases hvT : D.target.scoreVariance D.w = 0
  · rw [hvT]
    simp
  by_cases hoT : D.target.outcomeVariance = 0
  · rw [hoT]
    simp
  field_simp

omit [DecidableEq J] [DecidableEq L] in
/-- **Three quiet channels give a portable `R²`.**

    Only the one direction is proved, and only the one direction is true: `R²` is a
    ratio, so channels cancel.  The pair in `§4`'s `r2_eq_slope_differs` has an
    alignment factor of `4` against a dispersion factor of `1/4` and an unchanged
    outcome factor, so all three channels are loud and `R²` does not move at all.  The
    name says "of no shift" rather than "iff" for that reason. -/
theorem r2_transport_of_no_shift
    (hcov : D.target.predictiveCovariance D.w = D.source.predictiveCovariance D.w)
    (hvar : D.target.scoreVariance D.w = D.source.scoreVariance D.w)
    (hout : D.target.outcomeVariance = D.source.outcomeVariance) :
    D.target.r2 D.w = D.source.r2 D.w := by
  unfold DeploymentPopulation.r2
  rw [hcov, hvar, hout]

omit [DecidableEq J] [DecidableEq L] in
/-- **A pure dispersion shift lowers both the calibration slope and `R²`.**

    Fix the signal (`Cov(S,Y)` unchanged) and the phenotype (`Var Y` unchanged), and let
    only the score's own variance grow.  Both metrics fall, which is what the conclusion
    says and all it says.

    Read narrowly.  This is not the claim that the two metrics move together in general
    -- `r2_eq_slope_differs` in `§4` is a pair with equal `R²` and unequal slope, so they
    do not -- and it is not a statement about what recalibration repairs, which is
    `§5`'s `bestAffine_mse_eq` and `r2_affine_invariant`.  It is the single channel on
    which the two happen to agree, isolated. -/
theorem dispersion_shift_lowers_slope_and_r2
    (hcov : D.target.predictiveCovariance D.w = D.source.predictiveCovariance D.w)
    (hout : D.target.outcomeVariance = D.source.outcomeVariance)
    (hS : 0 < D.source.scoreVariance D.w)
    (hgrow : D.source.scoreVariance D.w < D.target.scoreVariance D.w)
    (hcovpos : 0 < D.source.predictiveCovariance D.w)
    (houtpos : 0 < D.source.outcomeVariance) :
    D.target.calibrationSlope D.w < D.source.calibrationSlope D.w ∧
      D.target.r2 D.w < D.source.r2 D.w := by
  have hT : 0 < D.target.scoreVariance D.w := lt_trans hS hgrow
  constructor
  · unfold DeploymentPopulation.calibrationSlope
    rw [hcov]
    exact div_lt_div_of_pos_left hcovpos hS hgrow
  · unfold DeploymentPopulation.r2
    rw [hcov, hout]
    have hnum : 0 < D.source.predictiveCovariance D.w ^ 2 := by positivity
    exact div_lt_div_of_pos_left hnum (by positivity)
      (by nlinarith)

end Deployment

end Transport

section Completeness

/-!
## §4 Completeness of the metric statistic

`§2` writes every metric as a closed form in six input objects.  That alone does not say
the six are the right inputs: a formula can be exact and still be written in redundant
or insufficient coordinates.  This section pins the coordinates down.

* **Sufficiency.**  Three reals -- `(Var S, Cov(S,Y), Var Y)` -- determine `R²` and the
  calibration slope exactly, through explicit functions.  Everything else about the
  population and the score is irrelevant to those two metrics.
* **Range.**  The achievable set of those three reals is exactly the Cauchy-Schwarz cone
  `Cov² ≤ Var S · Var Y`.  Both directions: the bound is forced (so `R² ≤ 1` is a
  theorem, not a convention), and every point of the cone is realised by an actual finite
  population.
* **Minimality.**  Each of the three coordinates is separately necessary: for each one
  there are two realisable deployments agreeing on the other two whose `R²` differs.  So
  no two of the three, and a fortiori no single scalar summary, determines `R²`.

The three together are what "complete theory" means here.  Sufficiency alone is
satisfied by the whole input tuple; minimality alone by any three unrelated numbers;
the range statement is what stops the statistic from being a coordinate system on a set
larger than the one deployments actually occupy.
-/

section Bounds

variable {Ω J L : Type*} [Fintype J] [DecidableEq J] [Fintype L] [DecidableEq L]
variable (P : DeploymentPopulation Ω J L) (w : J → ℝ)

namespace DeploymentPopulation

omit [DecidableEq J] [DecidableEq L] in
/-- **Cauchy-Schwarz for the deployed metrics.**  `Cov(S,Y)² ≤ Var(S)·Var(Y)`.

    Proved, not assumed: it is the discriminant argument applied to the population's own
    expectation functional, and it needs the positivity field of `ExpFunctional`.  For a
    merely signed linear functional it is false, and then `R²` could exceed one. -/
theorem predictiveCovariance_sq_le :
    P.predictiveCovariance w ^ 2 ≤ P.scoreVariance w * P.outcomeVariance := by
  have h := P.E.cauchy_schwarz
    (fun ω ↦ P.score w ω - P.E (P.score w))
    (fun ω ↦ P.phenotype ω - P.E P.phenotype)
  simpa [predictiveCovariance, scoreVariance, outcomeVariance, covariance, variance]
    using h

omit [DecidableEq J] [DecidableEq L] in
/-- `0 ≤ R²`. -/
theorem r2_nonneg (hv : 0 ≤ P.scoreVariance w) (ho : 0 ≤ P.outcomeVariance) :
    0 ≤ P.r2 w :=
  div_nonneg (sq_nonneg _) (mul_nonneg hv ho)

omit [DecidableEq J] [DecidableEq L] in
/-- **`R² ≤ 1`, as a theorem about the generative model.**

    Nothing normalises `R²` by hand anywhere in this development; it is defined as the
    ratio `Cov²/(Var·Var)` of quantities computed from the population, and the bound
    falls out of positivity of the expectation functional. -/
theorem r2_le_one (hv : 0 < P.scoreVariance w) (ho : 0 < P.outcomeVariance) :
    P.r2 w ≤ 1 := by
  unfold r2
  rw [div_le_one (mul_pos hv ho)]
  exact P.predictiveCovariance_sq_le w

end DeploymentPopulation

end Bounds

section Sufficiency

variable {Ω J L : Type*} [Fintype J] [DecidableEq J] [Fintype L] [DecidableEq L]

/-- **The metric statistic.**  Score variance, predictive covariance, outcome
variance -- the three reals a deployment reduces to as far as `R²` and calibration
slope are concerned. -/
def portabilityStatistic (P : DeploymentPopulation Ω J L) (w : J → ℝ) : ℝ × ℝ × ℝ :=
  (P.scoreVariance w, P.predictiveCovariance w, P.outcomeVariance)

/-- `R²` as an explicit function of the statistic. -/
def r2OfStatistic (s : ℝ × ℝ × ℝ) : ℝ := s.2.1 ^ 2 / (s.1 * s.2.2)

/-- Calibration slope as an explicit function of the statistic. -/
def slopeOfStatistic (s : ℝ × ℝ × ℝ) : ℝ := s.2.1 / s.1

omit [DecidableEq J] [DecidableEq L] in
/-- **Sufficiency for `R²`.**  The metric factors through the statistic. -/
theorem r2_factors_through_statistic (P : DeploymentPopulation Ω J L) (w : J → ℝ) :
    P.r2 w = r2OfStatistic (portabilityStatistic P w) := rfl

omit [DecidableEq J] [DecidableEq L] in
/-- **Sufficiency for the calibration slope.** -/
theorem slope_factors_through_statistic (P : DeploymentPopulation Ω J L) (w : J → ℝ) :
    P.calibrationSlope w = slopeOfStatistic (portabilityStatistic P w) := rfl

/-- **Two deployments with the same statistic have the same `R²` and slope**, whatever
    else differs between them: different sample spaces, different numbers of causal
    variants, different LD, different effect vectors, different residuals.

    This is the precise sense in which the portability problem is three-dimensional. -/
theorem metrics_eq_of_statistic_eq
    {ΩS ΩT J' L₁ L₂ : Type*} [Fintype J'] [DecidableEq J']
    [Fintype L₁] [DecidableEq L₁] [Fintype L₂] [DecidableEq L₂]
    (P : DeploymentPopulation ΩS J' L₁) (Q : DeploymentPopulation ΩT J' L₂)
    (w v : J' → ℝ)
    (hstat : portabilityStatistic P w = portabilityStatistic Q v) :
    P.r2 w = Q.r2 v ∧ P.calibrationSlope w = Q.calibrationSlope v := by
  constructor
  · rw [r2_factors_through_statistic, r2_factors_through_statistic, hstat]
  · rw [slope_factors_through_statistic, slope_factors_through_statistic, hstat]

end Sufficiency

section Realisation

/-!
### Realisable witnesses

Four equally likely individuals and two orthogonal contrasts on them.  Everything in
this subsection is an actual finite population: no limit, no Gaussian, no asymptotic
sample size.  If a statement of the form "these two situations are indistinguishable"
holds here, it holds of real data, because these *are* data.
-/

/-- Uniform expectation over four individuals, evaluated. -/
theorem uniformExp_four (f : Fin 4 → ℝ) :
    uniformExp (Fin 4) f = (f 0 + f 1 + f 2 + f 3) / 4 := by
  simp [uniformExp_apply, Fin.sum_univ_four]
  ring

theorem covariance_uniformExp_four (f g : Fin 4 → ℝ) :
    covariance (uniformExp (Fin 4)) f g
      = (f 0 * g 0 + f 1 * g 1 + f 2 * g 2 + f 3 * g 3) / 4
        - ((f 0 + f 1 + f 2 + f 3) / 4) * ((g 0 + g 1 + g 2 + g 3) / 4) := by
  rw [covariance_eq_expect_mul_sub_means]
  simp only [uniformExp_four]

theorem variance_uniformExp_four (f : Fin 4 → ℝ) :
    variance (uniformExp (Fin 4)) f
      = (f 0 ^ 2 + f 1 ^ 2 + f 2 ^ 2 + f 3 ^ 2) / 4
        - ((f 0 + f 1 + f 2 + f 3) / 4) ^ 2 := by
  rw [variance_eq_covariance_self, covariance_uniformExp_four]
  ring

/-- First contrast: the scored-variant direction. -/
def rad1 : Fin 4 → ℝ := ![1, 1, -1, -1]

/-- Second contrast, orthogonal to the first: the residual direction. -/
def rad2 : Fin 4 → ℝ := ![1, -1, 1, -1]

/-- **The two-contrast population.**  One scored variant carrying `α` units of the first
    contrast, one causal variant carrying the first contrast with effect `γ`, and a
    residual carrying `δ` units of the orthogonal second contrast.

    Three free reals, and they move the three coordinates of the statistic
    independently: `α` the score variance, `γ` the alignment, `δ` the residual variance.
    That independence is what the minimality proofs need. -/
def twoContrastPopulation (α γ δ : ℝ) : DeploymentPopulation (Fin 4) (Fin 1) (Fin 1) where
  E := uniformExp (Fin 4)
  X := fun ω _ ↦ α * rad1 ω
  C := fun ω _ ↦ rad1 ω
  β := fun _ ↦ γ
  h := fun ω ↦ δ * rad2 ω

/-- The single scored variant is used with weight one. -/
def unitWeight : Fin 1 → ℝ := fun _ ↦ 1

theorem twoContrast_scoreVariance (α γ δ : ℝ) :
    (twoContrastPopulation α γ δ).scoreVariance unitWeight = α ^ 2 := by
  show variance (uniformExp (Fin 4)) _ = _
  rw [variance_uniformExp_four]
  simp [DeploymentPopulation.score, twoContrastPopulation, linScore, dot, unitWeight,
    rad1]
  ring

theorem twoContrast_predictiveCovariance (α γ δ : ℝ) :
    (twoContrastPopulation α γ δ).predictiveCovariance unitWeight = α * γ := by
  show covariance (uniformExp (Fin 4)) _ _ = _
  rw [covariance_uniformExp_four]
  simp [DeploymentPopulation.score, DeploymentPopulation.phenotype, twoContrastPopulation,
    linScore, causalSignal, dot, unitWeight, rad1, rad2]
  ring

theorem twoContrast_outcomeVariance (α γ δ : ℝ) :
    (twoContrastPopulation α γ δ).outcomeVariance = γ ^ 2 + δ ^ 2 := by
  show variance (uniformExp (Fin 4)) _ = _
  rw [variance_uniformExp_four]
  simp [DeploymentPopulation.phenotype, twoContrastPopulation, causalSignal, dot,
    rad1, rad2]
  ring

theorem twoContrast_statistic (α γ δ : ℝ) :
    portabilityStatistic (twoContrastPopulation α γ δ) unitWeight
      = (α ^ 2, α * γ, γ ^ 2 + δ ^ 2) := by
  unfold portabilityStatistic
  rw [twoContrast_scoreVariance, twoContrast_predictiveCovariance,
    twoContrast_outcomeVariance]

/-- **Every point of the Cauchy-Schwarz cone is realised.**

    Given any target `(Var S, Cov, Var Y)` with positive score variance and obeying the
    bound that `§4`'s `predictiveCovariance_sq_le` forces, there is a four-individual
    population
    and a weight vector whose deployed metrics are exactly those numbers.

    Together with `predictiveCovariance_sq_le` this says the achievable set is the cone
    and nothing less: the statistic is a coordinate system on the deployments, not a
    lossy summary of a larger space. -/
theorem exists_deployment_with_statistic
    (vS c vY : ℝ) (hvS : 0 < vS) (hcs : c ^ 2 ≤ vS * vY) :
    ∃ (P : DeploymentPopulation (Fin 4) (Fin 1) (Fin 1)) (w : Fin 1 → ℝ),
      portabilityStatistic P w = (vS, c, vY) := by
  have hsqrt : Real.sqrt vS ^ 2 = vS := Real.sq_sqrt hvS.le
  have hspos : 0 < Real.sqrt vS := Real.sqrt_pos.mpr hvS
  set α := Real.sqrt vS with hα
  set γ := c / α with hγ
  have hγsq : γ ^ 2 = c ^ 2 / vS := by
    rw [hγ, div_pow, hsqrt]
  have hrem : 0 ≤ vY - γ ^ 2 := by
    rw [hγsq, sub_nonneg, div_le_iff₀ hvS]
    linarith [hcs, mul_comm vS vY]
  refine ⟨twoContrastPopulation α γ (Real.sqrt (vY - γ ^ 2)), unitWeight, ?_⟩
  rw [twoContrast_statistic]
  have h1 : α ^ 2 = vS := hsqrt
  have h2 : α * γ = c := by
    rw [hγ]
    field_simp
  have h3 : γ ^ 2 + Real.sqrt (vY - γ ^ 2) ^ 2 = vY := by
    rw [Real.sq_sqrt hrem]
    ring
  rw [h1, h2, h3]

end Realisation

section Minimality

/-!
### Minimality: no coordinate is redundant

Each theorem below exhibits two realisable deployments that agree on two coordinates of
the statistic and disagree on `R²`.  Since `R²` factors through the statistic, the
disagreeing coordinate cannot be dropped.

The consequence for practice is the one the portability literature keeps rediscovering:
a scalar summary of genetic distance is a function of one thing, and `R²` is a function
of three, so no scalar can predict it.  `no_score_side_summary_determines_r2` states that
directly rather than by analogy.
-/

/-- **The outcome-variance coordinate is necessary.**  Two populations with the same
    score variance and the same predictive covariance, differing only in residual
    variance, have different `R²`.

    This is environmental heterogeneity: identical genetics, identical score, different
    reported accuracy.  Nothing genetic has moved between these two populations. -/
theorem outcomeVariance_coordinate_necessary :
    (twoContrastPopulation 1 1 0).scoreVariance unitWeight
        = (twoContrastPopulation 1 1 1).scoreVariance unitWeight ∧
      (twoContrastPopulation 1 1 0).predictiveCovariance unitWeight
        = (twoContrastPopulation 1 1 1).predictiveCovariance unitWeight ∧
      (twoContrastPopulation 1 1 0).r2 unitWeight
        ≠ (twoContrastPopulation 1 1 1).r2 unitWeight := by
  refine ⟨by rw [twoContrast_scoreVariance, twoContrast_scoreVariance],
    by rw [twoContrast_predictiveCovariance, twoContrast_predictiveCovariance], ?_⟩
  unfold DeploymentPopulation.r2
  rw [twoContrast_scoreVariance, twoContrast_predictiveCovariance,
    twoContrast_outcomeVariance, twoContrast_scoreVariance,
    twoContrast_predictiveCovariance, twoContrast_outcomeVariance]
  norm_num

/-- **The predictive-covariance coordinate is necessary.**  Two populations with the
    same score variance and the same outcome variance, differing only in how well the
    score aligns with the phenotype, have different `R²`.

    This is effect turnover and tagging change: the score is dispersed identically and
    the trait is as variable, but the alignment has decayed. -/
theorem predictiveCovariance_coordinate_necessary :
    (twoContrastPopulation 1 1 0).scoreVariance unitWeight
        = (twoContrastPopulation 1 0 1).scoreVariance unitWeight ∧
      (twoContrastPopulation 1 1 0).outcomeVariance
        = (twoContrastPopulation 1 0 1).outcomeVariance ∧
      (twoContrastPopulation 1 1 0).r2 unitWeight
        ≠ (twoContrastPopulation 1 0 1).r2 unitWeight := by
  refine ⟨by rw [twoContrast_scoreVariance, twoContrast_scoreVariance],
    by rw [twoContrast_outcomeVariance, twoContrast_outcomeVariance]; norm_num, ?_⟩
  unfold DeploymentPopulation.r2
  rw [twoContrast_scoreVariance, twoContrast_predictiveCovariance,
    twoContrast_outcomeVariance, twoContrast_scoreVariance,
    twoContrast_predictiveCovariance, twoContrast_outcomeVariance]
  norm_num

/-- **The score-variance coordinate is necessary.**  Two populations with the same
    predictive covariance and the same outcome variance, differing only in the score's
    own variance, have different `R²`.

    This is the pure linkage channel: the same weights on differently-correlated
    genotypes disperse the score differently. -/
theorem scoreVariance_coordinate_necessary :
    (twoContrastPopulation 1 1 1).predictiveCovariance unitWeight
        = (twoContrastPopulation 2 (1 / 2) (Real.sqrt (7 / 4))).predictiveCovariance
            unitWeight ∧
      (twoContrastPopulation 1 1 1).outcomeVariance
        = (twoContrastPopulation 2 (1 / 2) (Real.sqrt (7 / 4))).outcomeVariance ∧
      (twoContrastPopulation 1 1 1).r2 unitWeight
        ≠ (twoContrastPopulation 2 (1 / 2) (Real.sqrt (7 / 4))).r2 unitWeight := by
  have hs : Real.sqrt (7 / 4) ^ 2 = 7 / 4 := Real.sq_sqrt (by norm_num)
  refine ⟨by rw [twoContrast_predictiveCovariance, twoContrast_predictiveCovariance]; norm_num,
    by rw [twoContrast_outcomeVariance, twoContrast_outcomeVariance, hs]; norm_num, ?_⟩
  unfold DeploymentPopulation.r2
  rw [twoContrast_scoreVariance, twoContrast_predictiveCovariance,
    twoContrast_outcomeVariance, twoContrast_scoreVariance,
    twoContrast_predictiveCovariance, twoContrast_outcomeVariance, hs]
  norm_num

/-- **No summary of the score's own behaviour determines its `R²`.**

    Let `summary` be *any* function of the pair `(Var S, Cov(S,Y))` into any type: an
    `F_ST`, a PC distance, an admixture proportion, a divergence time, the full LD
    matrix, a neural network on the entire genotype matrix -- anything at all that can be
    computed without looking at the phenotype's non-genetic variance.  No such summary
    determines `R²`, because the two populations of
    `outcomeVariance_coordinate_necessary` agree on both coordinates it can see and
    differ in `R²`.

    `summary` is universally quantified rather than instantiated at `F_ST` because the
    point is not that `F_ST` in particular is a poor predictor.  It is that the
    predictand has a third coordinate, and no refinement of the first two reaches it. -/
theorem no_score_side_summary_determines_r2
    {Report : Type*} (summary : ℝ × ℝ → Report) :
    ¬ ∃ accept : Report → ℝ,
        ∀ δ : ℝ,
          (twoContrastPopulation 1 1 δ).r2 unitWeight
            = accept (summary ((twoContrastPopulation 1 1 δ).scoreVariance unitWeight,
                (twoContrastPopulation 1 1 δ).predictiveCovariance unitWeight)) := by
  rintro ⟨accept, hacc⟩
  have h0 := hacc 0
  have h1 := hacc 1
  rw [twoContrast_scoreVariance, twoContrast_predictiveCovariance] at h0 h1
  have hne := outcomeVariance_coordinate_necessary.2.2
  exact hne (h0.trans h1.symm)

end Minimality

section MetricSpecificity

/-!
### Metric-specific portability, exactly

The third open question of Wang et al. (2026) is that portability depends on which
metric is reported.  In this framework that is not a phenomenon to be explained but a
corollary of the statistic having three coordinates and the metrics being different
functions on it: two metrics agree across a pair of deployments only when the pair
happens to lie in the level set of both.
-/

/-- **Equal `R²`, different calibration slope.**  Two realisable deployments whose `R²`
    agree exactly and whose calibration slopes differ.

    A portability study reporting only `R²` would call these two equally portable; one
    of them is perfectly calibrated and the other is off by a factor of two. -/
theorem r2_eq_slope_differs :
    (twoContrastPopulation 1 1 0).r2 unitWeight
        = (twoContrastPopulation 2 1 0).r2 unitWeight ∧
      (twoContrastPopulation 1 1 0).calibrationSlope unitWeight
        ≠ (twoContrastPopulation 2 1 0).calibrationSlope unitWeight := by
  constructor
  · unfold DeploymentPopulation.r2
    rw [twoContrast_scoreVariance, twoContrast_predictiveCovariance,
      twoContrast_outcomeVariance, twoContrast_scoreVariance,
      twoContrast_predictiveCovariance, twoContrast_outcomeVariance]
    norm_num
  · unfold DeploymentPopulation.calibrationSlope
    rw [twoContrast_scoreVariance, twoContrast_predictiveCovariance,
      twoContrast_scoreVariance, twoContrast_predictiveCovariance]
    norm_num

/-- **Equal calibration slope, different `R²`.**  The converse failure, so neither
    metric refines the other and no monotone map relates them. -/
theorem slope_eq_r2_differs :
    (twoContrastPopulation 1 1 0).calibrationSlope unitWeight
        = (twoContrastPopulation 1 1 1).calibrationSlope unitWeight ∧
      (twoContrastPopulation 1 1 0).r2 unitWeight
        ≠ (twoContrastPopulation 1 1 1).r2 unitWeight := by
  refine ⟨?_, outcomeVariance_coordinate_necessary.2.2⟩
  unfold DeploymentPopulation.calibrationSlope
  rw [twoContrast_scoreVariance, twoContrast_predictiveCovariance,
    twoContrast_scoreVariance, twoContrast_predictiveCovariance]

end MetricSpecificity

end Completeness

section Recalibration

/-!
## §5 Exact recalibration: what an affine correction can and cannot repair

The metrics of `§2` respond very differently to rescaling the score, and the difference
is the whole content of the recalibration literature.  This section computes the deployed
MSE of an *arbitrary* affine correction `a + b·S` exactly, minimises it exactly, and
reads off the two consequences:

* the best affine correction drives the calibration slope to `1` and the intercept to
  `0` in the target, whatever they were;
* the MSE it achieves is `Var(Y)·(1 - R²)`, so the `R²` it started with is *exactly* what
  survives.  Recalibration cannot move `R²` at all.

That pair is the precise version of the informal claim that some portability loss is
recoverable and some is not.  The recoverable part is the affine gauge; the
irrecoverable part is `R²`, and there is nothing in between.
-/

section AffineMse

variable {Ω J L : Type*} [Fintype J] [DecidableEq J] [Fintype L] [DecidableEq L]

namespace DeploymentPopulation

variable (P : DeploymentPopulation Ω J L) (w : J → ℝ)

/-- The score after an affine correction `a + b·S`. -/
def recalibratedScore (a b : ℝ) : Ω → ℝ := fun ω ↦ a + b * P.score w ω

omit [DecidableEq J] [DecidableEq L] in
/-- **Exact MSE of an arbitrary affine correction.**

    A quadratic in `b` plus a square in `a`, with coefficients that are exactly the three
    coordinates of the metric statistic and the two means.  Everything about affine
    recalibration follows from this one identity. -/
theorem recalibrated_mse_eq (a b : ℝ) :
    expMse P.E P.phenotype (P.recalibratedScore w a b)
      = P.outcomeVariance - 2 * b * P.predictiveCovariance w
          + b ^ 2 * P.scoreVariance w
          + (a + b * P.E (P.score w) - P.E P.phenotype) ^ 2 := by
  rw [mse_eq_variance_add_variance_sub_two_cov_add_bias_sq]
  unfold recalibratedScore bias
  rw [variance_affine, covariance_affine_right]
  rw [eval_affine]
  rw [show variance P.E P.phenotype = P.outcomeVariance from rfl,
    show variance P.E (P.score w) = P.scoreVariance w from rfl,
    show covariance P.E P.phenotype (P.score w) = P.predictiveCovariance w from
      covariance_comm _ _ _]
  ring

/-- **The affine correction the population itself prescribes**: slope `Cov/Var S`,
intercept chosen to match the means. -/
def bestAffineScore : Ω → ℝ :=
  P.recalibratedScore w (P.calibrationIntercept w) (P.calibrationSlope w)

/-- The algebraic step behind `bestAffine_mse_eq`: rescaling the outcome variance by the
unexplained fraction is subtracting the explained variance.  Stated for plain reals with
the Cauchy-Schwarz premise, because it has to hold at `V = 0` too, where the ratio is the
totalised `0` and the premise forces `c = 0`. -/
theorem outcomeVariance_mul_one_sub_ratio (V c v : ℝ) (hv : v ≠ 0) (hcs : c ^ 2 ≤ v * V) :
    V * (1 - c ^ 2 / (v * V)) = V - c ^ 2 / v := by
  by_cases ho : V = 0
  · subst ho
    have hc : c ^ 2 = 0 := le_antisymm (by simpa using hcs) (sq_nonneg c)
    rw [hc]
    simp
  · field_simp

omit [DecidableEq J] [DecidableEq L] in
/-- **What recalibration achieves, exactly: `Var(Y)·(1 - R²)`.**

    The residual variance of the best affine correction is the outcome variance scaled
    by exactly the fraction `R²` does not explain.  No approximation and no Gaussian
    assumption: this is an identity about a positive linear functional. -/
theorem bestAffine_mse_eq (hv : P.scoreVariance w ≠ 0) :
    expMse P.E P.phenotype (P.bestAffineScore w)
      = P.outcomeVariance * (1 - P.r2 w) := by
  have hR : P.outcomeVariance * (1 - P.r2 w)
      = P.outcomeVariance - P.predictiveCovariance w ^ 2 / P.scoreVariance w :=
    outcomeVariance_mul_one_sub_ratio P.outcomeVariance (P.predictiveCovariance w)
      (P.scoreVariance w) hv (P.predictiveCovariance_sq_le w)
  rw [hR]
  unfold bestAffineScore
  rw [recalibrated_mse_eq]
  unfold calibrationIntercept calibrationSlope
  field_simp
  ring

omit [DecidableEq J] [DecidableEq L] in
/-- **The prescribed correction is optimal**: no affine rescaling does better.

    So the number in `bestAffine_mse_eq` is not one correction's score, it is the floor
    over all of them, and `Var(Y)(1 - R²)` is what an ideally recalibrated deployment
    achieves. -/
theorem bestAffine_mse_le (hv : 0 < P.scoreVariance w) (a b : ℝ) :
    expMse P.E P.phenotype (P.bestAffineScore w)
      ≤ expMse P.E P.phenotype (P.recalibratedScore w a b) := by
  rw [bestAffine_mse_eq P w hv.ne', recalibrated_mse_eq]
  unfold r2
  rw [outcomeVariance_mul_one_sub_ratio P.outcomeVariance (P.predictiveCovariance w)
    (P.scoreVariance w) hv.ne' (P.predictiveCovariance_sq_le w)]
  have hquad : 0 ≤ (b - P.predictiveCovariance w / P.scoreVariance w) ^ 2 *
      P.scoreVariance w := by positivity
  have hexpand : (b - P.predictiveCovariance w / P.scoreVariance w) ^ 2 *
      P.scoreVariance w
      = b ^ 2 * P.scoreVariance w - 2 * b * P.predictiveCovariance w
        + P.predictiveCovariance w ^ 2 / P.scoreVariance w := by
    field_simp
    ring
  nlinarith [sq_nonneg (a + b * P.E (P.score w) - P.E P.phenotype)]

omit [DecidableEq J] [DecidableEq L] in
/-- **Recalibration cannot move `R²`.**

    The recalibrated score is an affine image of the original, and `R²` is invariant
    under affine reparametrisation of the predictor for any nonzero slope.  Combined
    with `bestAffine_mse_eq`, this is the exact division of portability loss into a
    repairable part and an unrepairable one. -/
theorem r2_affine_invariant (a b : ℝ) (hb : b ≠ 0) :
    covariance P.E (P.recalibratedScore w a b) P.phenotype ^ 2 /
        (variance P.E (P.recalibratedScore w a b) * P.outcomeVariance)
      = P.r2 w := by
  unfold recalibratedScore r2
  rw [covariance_comm, covariance_affine_right, variance_affine]
  rw [show covariance P.E P.phenotype (P.score w) = P.predictiveCovariance w from
    covariance_comm _ _ _]
  rw [show variance P.E (P.score w) = P.scoreVariance w from rfl]
  rw [mul_pow]
  by_cases hv : P.scoreVariance w = 0
  · rw [hv]
    simp
  · by_cases ho : P.outcomeVariance = 0
    · rw [ho]
      simp
    · field_simp

end DeploymentPopulation

end AffineMse

end Recalibration

section JunkBranches

/-!
## §6 Named junk branches

Mathlib totalises division: `x / 0 = 0`.  Every definition in this file that divides can
therefore return a number where the modelled quantity has none, and the corpus
convention is to name that branch rather than leave a reader to infer it from a value
that is in range and means nothing.  Each theorem below states what is returned and what
a consumer must require.
-/

variable {Ω J L : Type*} [Fintype J] [DecidableEq J] [Fintype L] [DecidableEq L]

omit [DecidableEq J] [DecidableEq L] in
/-- **`calibrationSlope` where its denominator vanishes, named.**  A score with no
variance has no regression slope of the phenotype on it; the value returned is `0`,
which is also the legitimate slope of a score that carries no signal.  Consumers must
require `scoreVariance w ≠ 0`. -/
theorem calibrationSlope_at_zero_scoreVariance_is_junk
    (P : DeploymentPopulation Ω J L) (w : J → ℝ) (hzero : P.scoreVariance w = 0) :
    P.calibrationSlope w = 0 := by
  unfold DeploymentPopulation.calibrationSlope
  rw [hzero, div_zero]

omit [DecidableEq J] [DecidableEq L] in
/-- **`r2` where its denominator vanishes, named.**  A constant score, or a population
with no phenotypic variance, has no squared correlation; `0` is returned, and `0` is
also what a genuinely uninformative score scores.  Consumers must require both variances
nonzero -- `predictiveCovariance_sq_le` shows the numerator vanishes there too, so the
returned `0` is not even a limit of nearby values. -/
theorem r2_at_zero_denominator_is_junk
    (P : DeploymentPopulation Ω J L) (w : J → ℝ)
    (hzero : P.scoreVariance w * P.outcomeVariance = 0) :
    P.r2 w = 0 := by
  unfold DeploymentPopulation.r2
  rw [hzero, div_zero]

omit [DecidableEq J] [DecidableEq L] in
/-- **`r2OfStatistic` at a degenerate statistic, named.** -/
theorem r2OfStatistic_at_zero_denominator_is_junk (s : ℝ × ℝ × ℝ)
    (hzero : s.1 * s.2.2 = 0) : r2OfStatistic s = 0 := by
  unfold r2OfStatistic
  rw [hzero, div_zero]

omit [DecidableEq J] [DecidableEq L] in
/-- **`slopeOfStatistic` at a degenerate statistic, named.** -/
theorem slopeOfStatistic_at_zero_scoreVariance_is_junk (s : ℝ × ℝ × ℝ)
    (hzero : s.1 = 0) : slopeOfStatistic s = 0 := by
  unfold slopeOfStatistic
  rw [hzero, div_zero]

variable {ΩS ΩT : Type*}

omit [DecidableEq J] [DecidableEq L] in
/-- **`alignmentFactor` where the source carries no signal, named.**  The factorisation
`r2_transport_factorisation` requires `predictiveCovariance ≠ 0` in the source for
exactly this reason: with a source that predicts nothing, the ratio of target to source
alignment is not a number, and `0` is returned. -/
theorem alignmentFactor_at_zero_source_covariance_is_junk
    (D : Deployment ΩS ΩT J L) (hzero : D.source.predictiveCovariance D.w = 0) :
    D.alignmentFactor = 0 := by
  unfold Deployment.alignmentFactor
  rw [hzero, div_zero]
  norm_num

omit [Fintype L] [DecidableEq J] [DecidableEq L] in
/-- **`dispersionFactor` where the target score is constant, named.** -/
theorem dispersionFactor_at_zero_target_scoreVariance_is_junk
    (D : Deployment ΩS ΩT J L) (hzero : D.target.scoreVariance D.w = 0) :
    D.dispersionFactor = 0 := by
  unfold Deployment.dispersionFactor
  rw [hzero, div_zero]

omit [Fintype J] [DecidableEq J] [DecidableEq L] in
/-- **`outcomeFactor` where the target phenotype is constant, named.** -/
theorem outcomeFactor_at_zero_target_outcomeVariance_is_junk
    (D : Deployment ΩS ΩT J L) (hzero : D.target.outcomeVariance = 0) :
    D.outcomeFactor = 0 := by
  unfold Deployment.outcomeFactor
  rw [hzero, div_zero]

end JunkBranches

section Training

/-!
## §7 Where the weights come from, and the exact gap they leave

`§2` to `§6` never ask how `w` was produced, which is what makes them cover every scoring
pipeline.  This section closes the loop at the one end that has a canonical answer: the
weights a population's own second moments prescribe, `Σ⁻¹ Σ_{XY}`.

Three exact facts follow, and together they are the classic
train-in-source-deploy-in-target story with no approximation in it:

* a score fitted to a population is **exactly** calibrated in it -- slope `1`, and `R²`
  equal to the score's own variance share of the outcome variance;
* deploying **any** weights in a population costs exactly the target-oracle MSE plus the
  target LD quadratic form of the weight error, with no cross term;
* the weight error of a source-trained score is exactly
  `Σ_T⁻¹(K_Tβ_T + c_T) - Σ_S⁻¹(K_Sβ_S + c_S)`, which is where every channel of `§3`
  reappears -- and it is a difference of two matrix inverses applied to two different
  vectors, so no scalar shrinkage of the source weights reaches it.
-/

variable {Ω J L : Type*} [Fintype J] [DecidableEq J] [Fintype L]

namespace DeploymentPopulation

variable (P : DeploymentPopulation Ω J L)

/-- The weights this population's own moments prescribe. -/
def optimalWeights (sigmaInv : Matrix J J ℝ) : J → ℝ :=
  optimalWeightsFromMoments sigmaInv P.E P.X P.phenotype

/-- The predictive covariance is the weights read against the cross-covariance vector.
    A restatement of `covariance_linScore_eq_dot_crossCov` in this file's names, needed
    because `crossCovVector` and `contextCrossCovVector` are the same function under two
    names, one for each argument's intended role. -/
theorem predictiveCovariance_eq_dot_crossCov (w : J → ℝ) :
    P.predictiveCovariance w = dot w (crossCovVector P.E P.X P.phenotype) :=
  covariance_linScore_eq_dot_crossCov P.E P.X w P.phenotype

/-- **The prescribed weights make predictive covariance and score variance coincide.**

    This is the normal equations in metric form, and every calibration statement below is
    a corollary of it. -/
theorem predictiveCovariance_optimalWeights (sigmaInv : Matrix J J ℝ)
    (hsigmaInv : P.sigmaX * sigmaInv = 1) :
    P.predictiveCovariance (P.optimalWeights sigmaInv)
      = P.scoreVariance (P.optimalWeights sigmaInv) := by
  have hmul : P.sigmaX.mulVec (P.optimalWeights sigmaInv)
      = crossCovVector P.E P.X P.phenotype := by
    unfold optimalWeights optimalWeightsFromMoments
    have h := Matrix.mulVec_mulVec (crossCovVector P.E P.X P.phenotype) P.sigmaX sigmaInv
    rw [hsigmaInv, Matrix.one_mulVec] at h
    simpa using h
  rw [predictiveCovariance_eq_dot_crossCov, P.scoreVariance_eq, hmul]

/-- **A score is exactly calibrated in the population it was fitted to.**

    Slope exactly `1`, not approximately: the source calibration slope carries no error
    at all, so every departure from `1` measured in a target population is transport and
    nothing else. -/
theorem calibrationSlope_optimalWeights (sigmaInv : Matrix J J ℝ)
    (hsigmaInv : P.sigmaX * sigmaInv = 1)
    (hvar : P.scoreVariance (P.optimalWeights sigmaInv) ≠ 0) :
    P.calibrationSlope (P.optimalWeights sigmaInv) = 1 := by
  unfold calibrationSlope
  rw [predictiveCovariance_optimalWeights P sigmaInv hsigmaInv]
  exact div_self hvar

/-- **In-sample `R²` is the score's variance share of the outcome variance.** -/
theorem r2_optimalWeights (sigmaInv : Matrix J J ℝ)
    (hsigmaInv : P.sigmaX * sigmaInv = 1)
    (hvar : P.scoreVariance (P.optimalWeights sigmaInv) ≠ 0) :
    P.r2 (P.optimalWeights sigmaInv)
      = P.scoreVariance (P.optimalWeights sigmaInv) / P.outcomeVariance := by
  unfold r2
  rw [predictiveCovariance_optimalWeights P sigmaInv hsigmaInv, pow_two,
    mul_div_mul_left _ _ hvar]

/-- **Exact excess-MSE law.**  Deploying any weights costs the oracle MSE for this
    population plus the LD quadratic form of the weight error -- no cross term, because
    the oracle residual is orthogonal to every direction in the score's span.

    The centering hypothesis is the standardisation convention every polygenic score
    already applies to its genotypes, and it is the only place in this module where a
    convention on the inputs is used. -/
theorem deployedMse_excess (sigmaInv : Matrix J J ℝ) (w : J → ℝ)
    (hcentered : ∀ j, P.E (fun ω ↦ P.X ω j) = 0)
    (hsigmaInv : P.sigmaX * sigmaInv = 1) :
    P.deployedMse w
      = P.deployedMse (P.optimalWeights sigmaInv)
        + dot (fun j ↦ w j - P.optimalWeights sigmaInv j)
            (P.sigmaX.mulVec (fun j ↦ w j - P.optimalWeights sigmaInv j)) :=
  master_transport_identity_closed_form sigmaInv P.E P.X P.phenotype w hcentered hsigmaInv

end DeploymentPopulation

variable {ΩS ΩT : Type*}

namespace Deployment

variable (D : Deployment ΩS ΩT J L)

/-- **The exact deployment gap.**

    A source-trained score deployed in a target costs the target oracle's MSE plus the
    target LD quadratic form of the weight error, exactly.  `weightError` below names
    that error, and `weightError_eq` writes it in the transport channels of `§3`. -/
theorem target_deployedMse_excess (sigmaInvT : Matrix J J ℝ)
    (hcentered : ∀ j, D.target.E (fun ω ↦ D.target.X ω j) = 0)
    (hsigmaInv : D.target.sigmaX * sigmaInvT = 1) :
    D.target.deployedMse D.w
      = D.target.deployedMse (D.target.optimalWeights sigmaInvT)
        + dot (fun j ↦ D.w j - D.target.optimalWeights sigmaInvT j)
            (D.target.sigmaX.mulVec
              (fun j ↦ D.w j - D.target.optimalWeights sigmaInvT j)) :=
  D.target.deployedMse_excess sigmaInvT D.w hcentered hsigmaInv

omit [DecidableEq J] in
variable [DecidableEq L] in
/-- **The weight error of a source-trained score, in the channels of `§3`.**

    `Σ_T⁻¹(K_Tβ_T + c_T) - Σ_S⁻¹(K_Sβ_S + c_S)`.  Every object that differs between the
    two populations appears, and they appear inside two different matrix inverses.  That
    is the exact reason `mulVec_smul_ne_of_not_aligned` in `Program.OpenQuestions` finds
    no scalar recalibration that repairs an LD mismatch: `Σ_T⁻¹ v` is not a multiple of
    `Σ_S⁻¹ v` unless `v` happens to be a common eigenvector. -/
theorem weightError_eq (sigmaInvS sigmaInvT : Matrix J J ℝ) :
    (fun j ↦ D.target.optimalWeights sigmaInvT j - D.source.optimalWeights sigmaInvS j)
      = sigmaInvT.mulVec (D.target.kappa.mulVec D.target.β + D.target.contextX)
        - sigmaInvS.mulVec (D.source.kappa.mulVec D.source.β + D.source.contextX) := by
  funext j
  unfold DeploymentPopulation.optimalWeights optimalWeightsFromMoments
  have hT : crossCovVector D.target.E D.target.X D.target.phenotype
      = D.target.kappa.mulVec D.target.β + D.target.contextX :=
    crossCovVector_decomposition D.target.E D.target.X D.target.C D.target.β D.target.h
  have hS : crossCovVector D.source.E D.source.X D.source.phenotype
      = D.source.kappa.mulVec D.source.β + D.source.contextX :=
    crossCovVector_decomposition D.source.E D.source.X D.source.C D.source.β D.source.h
  rw [hT, hS]
  rfl

end Deployment

end Training

section StatisticBoundary

/-!
## §8 Where the statistic stops

`§4` proves the three-real statistic sufficient for `R²` and the calibration slope, and
each of its coordinates necessary.  A completeness claim is only as good as its stated
scope, so this section fixes the scope from the other side: the statistic is sufficient
for the *second-moment* metrics and for nothing beyond them.

`exceedance` is the simplest metric that is not a second-moment functional -- the
fraction of a population scoring above a cut-off, which is what a screening programme
actually deploys.  Two populations below have **identical** score variance, predictive
covariance and outcome variance, hence identical `R²`, calibration slope and
recalibrated MSE, and they put different fractions of the population above zero.

So the third open question of Wang et al. (2026) -- that portability depends on the
metric reported -- is not one phenomenon but two.  Within the second-moment metrics it
is `§4`'s minimality: the metrics are different functions on a three-dimensional
statistic, so they have different level sets.  Between second-moment and threshold
metrics it is this section: no amount of second-moment information determines a
threshold metric at all, and a study reporting `R²` has said nothing about the
sensitivity of the screen it is validating.
-/

/-- The fraction of the population whose score exceeds a cut-off.  The threshold metric
in its simplest form; sensitivity, specificity and precision are all built from
exceedances of the joint law. -/
def exceedance (P : DeploymentPopulation (Fin 4) (Fin 1) (Fin 1)) (w : Fin 1 → ℝ)
    (t : ℝ) : ℝ :=
  P.E (fun ω ↦ if t < P.score w ω then 1 else 0)

/-- **The one-contrast population.**  A single scored variant which is also the single
causal variant, with unit effect and no residual: score and phenotype coincide, so the
statistic is `(Var v, Var v, Var v)` for whatever contrast `v` is supplied and `R²` is
exactly `1`.  All that is left free is the *shape* of `v`, which is exactly the
information the statistic discards. -/
def oneContrastPopulation (v : Fin 4 → ℝ) : DeploymentPopulation (Fin 4) (Fin 1) (Fin 1) where
  E := uniformExp (Fin 4)
  X := fun ω _ ↦ v ω
  C := fun ω _ ↦ v ω
  β := fun _ ↦ 1
  h := fun _ ↦ 0

theorem oneContrast_statistic (v : Fin 4 → ℝ) :
    portabilityStatistic (oneContrastPopulation v) unitWeight
      = (variance (uniformExp (Fin 4)) v, variance (uniformExp (Fin 4)) v,
          variance (uniformExp (Fin 4)) v) := by
  have hscore : (oneContrastPopulation v).score unitWeight = v := by
    funext ω
    simp [DeploymentPopulation.score, oneContrastPopulation, linScore, dot, unitWeight]
  have hpheno : (oneContrastPopulation v).phenotype = v := by
    funext ω
    simp [DeploymentPopulation.phenotype, oneContrastPopulation, causalSignal, dot]
  unfold portabilityStatistic DeploymentPopulation.scoreVariance
    DeploymentPopulation.predictiveCovariance DeploymentPopulation.outcomeVariance
  rw [hscore, hpheno, ← variance_eq_covariance_self]
  rfl

/-- The balanced contrast: half the population above zero. -/
def balancedContrast : Fin 4 → ℝ := ![-1, -1, 1, 1]

/-- The spread contrast: the same variance, a quarter of the population above zero. -/
def spreadContrast : Fin 4 → ℝ := ![-Real.sqrt 2, 0, 0, Real.sqrt 2]

theorem variance_balancedContrast : variance (uniformExp (Fin 4)) balancedContrast = 1 := by
  rw [variance_uniformExp_four]
  simp [balancedContrast]
  norm_num

theorem variance_spreadContrast : variance (uniformExp (Fin 4)) spreadContrast = 1 := by
  rw [variance_uniformExp_four]
  simp [spreadContrast]
  norm_num

theorem exceedance_balancedContrast :
    exceedance (oneContrastPopulation balancedContrast) unitWeight 0 = 1 / 2 := by
  unfold exceedance
  have hscore : ∀ ω, (oneContrastPopulation balancedContrast).score unitWeight ω
      = balancedContrast ω := fun ω ↦ by
    simp [DeploymentPopulation.score, oneContrastPopulation, linScore, dot, unitWeight]
  simp only [hscore]
  show uniformExp (Fin 4) _ = _
  rw [uniformExp_four]
  norm_num [balancedContrast, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Matrix.head_cons]

theorem exceedance_spreadContrast :
    exceedance (oneContrastPopulation spreadContrast) unitWeight 0 = 1 / 4 := by
  have hpos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  unfold exceedance
  have hscore : ∀ ω, (oneContrastPopulation spreadContrast).score unitWeight ω
      = spreadContrast ω := fun ω ↦ by
    simp [DeploymentPopulation.score, oneContrastPopulation, linScore, dot, unitWeight]
  simp only [hscore]
  show uniformExp (Fin 4) _ = _
  rw [uniformExp_four]
  norm_num [spreadContrast, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Matrix.head_cons, hpos, hpos.not_gt]

/-- **The statistic does not determine a threshold metric.**

    Two realisable populations with the same score variance, the same predictive
    covariance and the same outcome variance -- hence the same `R²`, the same
    calibration slope, and the same optimally recalibrated MSE -- put `1/2` and `1/4` of
    their members above the same cut-off.

    This is not a small discrepancy at an unlucky threshold: the two deployments are
    indistinguishable to every second-moment metric there is, and one screen refers twice
    as many people as the other. -/
theorem statistic_does_not_determine_exceedance :
    portabilityStatistic (oneContrastPopulation balancedContrast) unitWeight
        = portabilityStatistic (oneContrastPopulation spreadContrast) unitWeight ∧
      (oneContrastPopulation balancedContrast).r2 unitWeight
        = (oneContrastPopulation spreadContrast).r2 unitWeight ∧
      (oneContrastPopulation balancedContrast).calibrationSlope unitWeight
        = (oneContrastPopulation spreadContrast).calibrationSlope unitWeight ∧
      exceedance (oneContrastPopulation balancedContrast) unitWeight 0
        ≠ exceedance (oneContrastPopulation spreadContrast) unitWeight 0 := by
  have hstat : portabilityStatistic (oneContrastPopulation balancedContrast) unitWeight
      = portabilityStatistic (oneContrastPopulation spreadContrast) unitWeight := by
    rw [oneContrast_statistic, oneContrast_statistic, variance_balancedContrast,
      variance_spreadContrast]
  refine ⟨hstat, ?_, ?_, ?_⟩
  · exact (metrics_eq_of_statistic_eq _ _ _ _ hstat).1
  · exact (metrics_eq_of_statistic_eq _ _ _ _ hstat).2
  · rw [exceedance_balancedContrast, exceedance_spreadContrast]
    norm_num

end StatisticBoundary

end

end Descent
