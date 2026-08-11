/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.PopGen.PolygenicArchitecture
import Descent.Decision.CertificateGrading
import Descent.Decision.TransportedMinimax

assert_below Descent.Program

namespace Descent.PopGen

open MeasureTheory

/-!
# `Decision.PolygenicNonsmoothSummaries`

The nonsmooth architecture summaries and their certificate calculus, split out of
`PopGen/PolygenicArchitecture.lean`.

WHY THIS FILE IS IN `Decision/` AND NOT IN `PopGen/`. The material below is a
decision-theoretic INSTANCE: it reads `Decision.CertificateGrading`'s finite priors, atom
moduli and grading calculus, and `Decision.TransportedMinimax`'s entropy exponents. A
PopGen module that names those is a lower layer that cannot be read or moved without the
higher one, which is the whole of what the layer order buys. The quantities are still
architecture quantities and keep the `Descent.PopGen` namespace, so no consumer's spelling
changes; what moves is which layer declares them.

The parts left behind in `PolygenicArchitecture` need nothing from `Decision`, and this
file is the only reader of what it takes.
-/

/-!
## Nonsmooth Architecture Summaries and What They Cost to Estimate

The quantities this file uses to summarise an effect-size distribution are not
all of the same difficulty, and nothing in the corpus recorded the difference.

`expectedSquaredEffect`, `spikeAndSlabVariance` and `additiveVariance` are
smooth — quadratic — functionals of the effect vector, and are estimable at the
usual root-`n` rate. `effectivePolygenicity` and the mean absolute effect
`q⁻¹ ∑ |β_j|` are not. The mean absolute effect is the canonical nonsmooth
functional: in the Gaussian sequence model over a box, estimating
`n⁻¹ ∑ |θ_i|` has minimax risk of order `1 / log n`, logarithmic, not
polynomial. It is the natural measure of total additive signal and the closest
kin in this file to a polygenicity or sparsity summary, and it is far harder to
estimate than the variance-type summaries standing beside it.

The second half is about certificates rather than estimators. Two hierarchies
must be kept separate. Forcing more architecture moments to agree shrinks the
moment-constrained modulus; allowing more atoms in the two mixing priors grows
the class of lower-bound certificates. The latter is method power. Grade two
contains the ordinary architecture-versus-architecture comparison, while
higher grades permit genuinely fuzzy hypotheses.

The earlier polynomial fixed-grade claim was removed rather than proved: its
finite interface treated catalogue size as sample size and chose the target,
moment probes, and observation kernel after seeing the requested bound. The
Gaussian-location-mixture audit also found that its order-eight
moment-constrained modulus recovered 99.93% of the unrestricted one. Neither
fact supports a biological rate law. What remains below is the exact,
experiment-derived calculus a future GWAS observation model must evaluate.

`Descent.Decision.PowerAnalysis` compares the logarithmic and polynomial benchmark
curves conditionally. Those comparisons are useful for falsifying a proposed
design calculation, but they are not sample-size guarantees for a GWAS until a
concrete observation model proves that its minimax risk and certificate modulus
are the stated curves.
-/

section NonsmoothSummaries

/-- **Mean absolute effect size across variants.**

    `q⁻¹ ∑_j |β_j|`, the natural summary of total additive signal on the effect
    scale rather than the squared-effect scale. Unlike `expectedSquaredEffect`
    it is not a smooth functional of the effect vector: it is Lipschitz but has
    no derivative at any coordinate through zero, and that is what governs how
    hard it is to estimate.

    Empirical status: NOT AN EMPIRICAL CLAIM. The body averages the absolute
    entries of the vector it is handed. `beta` is the caller's, so the value is
    fixed once the vector is and nothing observable can disagree with it -- the
    same reading, for the same reason, as `sourceEffectMass` above. The
    empirical questions in the neighbourhood are about what a real effect
    vector's entries ARE, and about the estimation difficulty this docstring
    describes; the second is a statement about estimators of this functional,
    not about the functional, and would be measured at an estimator. -/
noncomputable def meanAbsoluteEffect {q : ℕ} (beta : Fin q → ℝ) : ℝ :=
  (∑ j, |beta j|) / q

/-- **meanAbsoluteEffect over an empty index, named.** An architecture with no variants has no
mean absolute effect. The empty sum and the zero cast vanish together and Lean returns `0`, which
is also what an architecture of exactly-null effects gives -- so a missing panel and a null
architecture are indistinguishable. Consumers must require a nonempty index. -/
theorem meanAbsoluteEffect_empty_architecture_is_junk (beta : Fin 0 → ℝ) :
    meanAbsoluteEffect beta = 0 := by
  unfold meanAbsoluteEffect
  simp

theorem meanAbsoluteEffect_nonneg {q : ℕ} (beta : Fin q → ℝ) :
    0 ≤ meanAbsoluteEffect beta := by
  unfold meanAbsoluteEffect
  exact div_nonneg (Finset.sum_nonneg fun j _ ↦ abs_nonneg _) (Nat.cast_nonneg q)

/-- **On a nonempty catalogue, the nonsmooth summary is dominated by the smooth one.**

    `(q⁻¹ ∑ |β_j|)² ≤ q⁻¹ ∑ β_j²` by Cauchy–Schwarz. The point of recording it
    is the contrast it sets up: the smaller quantity is the harder one to
    estimate, so the ordering of the two summaries by magnitude runs opposite to
    their ordering by statistical difficulty. -/
theorem meanAbsoluteEffect_sq_le_meanSquaredEffect {q : ℕ} (beta : Fin q → ℝ) (hq : 0 < q) :
    (meanAbsoluteEffect beta) ^ 2 ≤ (∑ j, beta j ^ 2) / q := by
  have hq' : (0 : ℝ) < q := Nat.cast_pos.mpr hq
  have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin q))
    (fun _ ↦ (1 : ℝ)) (fun j ↦ |beta j|)
  have h3 : ∑ j : Fin q, |beta j| ^ 2 = ∑ j, beta j ^ 2 :=
    Finset.sum_congr rfl (fun j _ ↦ sq_abs _)
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one] at h
  rw [h3] at h
  unfold meanAbsoluteEffect
  rw [div_pow, div_le_div_iff₀ (by positivity) hq']
  have hmul := mul_le_mul_of_nonneg_right h (le_of_lt hq')
  nlinarith [hmul]

/-! ### A biological certificate problem with no theorem fields

The parameter is an additive-effect vector, the carrier is a closed ball, and
the target is `meanAbsoluteEffect`.  The structure below contains numerical
data only.  It cannot claim minimax duality, Donoho--Liu tightness, or a rate
gap by projection from an assumption field.
-/

/-- Bounded additive-effect architectures.  The absolute radius makes the set
nonempty and convex for every input, without a validity theorem parameter.

    Empirical status: NOT AN EMPIRICAL CLAIM -- the closed ball of radius
    `|B|` in the effect coordinates. A set, with no observable attached. -/
noncomputable def boundedEffectCarrier (q : ℕ) (B : ℝ) : Set (Fin q → ℝ) :=
  Metric.closedBall 0 |B|

theorem boundedEffectCarrier_nonempty (q : ℕ) (B : ℝ) :
    (boundedEffectCarrier q B).Nonempty :=
  ⟨0, Metric.mem_closedBall_self (abs_nonneg B)⟩

theorem boundedEffectCarrier_convex (q : ℕ) (B : ℝ) :
    Convex ℝ (boundedEffectCarrier q B) :=
  convex_closedBall 0 |B|

open Descent.Decision.CertificateGrading in
/-- A finite catalogue of additive architectures and a numerical discrepancy
between mixture experiments.  No field has type `Prop`; both the
moment-constrained modulus and the atom-complexity modulus are derived below
from the observation laws. -/
structure MeanAbsoluteEffectCertificateProblem (q n : ℕ) where
  architecture : Fin (n + 1) → Fin q → ℝ
  /-- Actual catalogue-indexed observation laws.  Prior discrepancies are
  derived as total variation between mixtures of these laws; they are not an
  arbitrary numerical input. -/
  observation : Fin (n + 1) → Decision.CertificateGrading.FinitePrior n
  logScale : ℝ

namespace MeanAbsoluteEffectCertificateProblem

open Descent.Decision.CertificateGrading

/-- A data-derived radius containing the whole finite architecture catalogue.
Using the sum of absolute coordinates is deliberately conservative but total:
there is no supplied radius and no side condition saying that the catalogue
fits inside it. -/
noncomputable def architectureRadius {q n : ℕ}
    (P : MeanAbsoluteEffectCertificateProblem q n) : ℝ :=
  ∑ i, ∑ j, |P.architecture i j|

/-- Reference evaluation: a zero architecture has zero radius. -/
theorem architectureRadius_at_zero {q n : ℕ} (P : MeanAbsoluteEffectCertificateProblem q n)
    (hzero : ∀ i j, P.architecture i j = 0) :
    architectureRadius P = 0 := by
  unfold architectureRadius
  simp [hzero]


theorem architectureRadius_nonneg {q n : ℕ}
    (P : MeanAbsoluteEffectCertificateProblem q n) :
    0 ≤ P.architectureRadius := by
  exact Finset.sum_nonneg fun i _ ↦ Finset.sum_nonneg fun j _ ↦ abs_nonneg _

/-- The effect vectors this problem ranges over: the ball whose radius is
derived from, and contains, the architecture catalogue.

    Empirical status: NOT AN EMPIRICAL CLAIM -- the carrier set a certificate
    problem ranges over. -/
noncomputable def effects {q n : ℕ} (P : MeanAbsoluteEffectCertificateProblem q n) :
    Set (Fin q → ℝ) := boundedEffectCarrier q P.architectureRadius

/-- Every catalogue entry belongs to the biological carrier.  This is a theorem
of the numerical construction, not a validity field supplied by the caller. -/
theorem architecture_mem_effects {q n : ℕ}
    (P : MeanAbsoluteEffectCertificateProblem q n) (i : Fin (n + 1)) :
    P.architecture i ∈ P.effects := by
  rw [effects, boundedEffectCarrier, Metric.mem_closedBall,
    abs_of_nonneg P.architectureRadius_nonneg,
    dist_pi_le_iff P.architectureRadius_nonneg]
  intro j
  simp only [Pi.zero_apply, dist_zero_right]
  calc
    |P.architecture i j| ≤ ∑ k, |P.architecture i k| :=
      Finset.single_le_sum (fun k _ ↦ abs_nonneg (P.architecture i k))
        (Finset.mem_univ j)
    _ ≤ P.architectureRadius :=
      Finset.single_le_sum
        (fun l _ ↦ Finset.sum_nonneg fun k _ ↦ abs_nonneg (P.architecture l k))
        (Finset.mem_univ i)

/-- Signed effect moment used by moment matching.  Order two, for example,
matches the catalogue-average signed effect and squared-effect mass before it
tries to separate the nonsmooth mean-absolute-effect target. -/
noncomputable def architectureMoment {q n : ℕ}
    (P : MeanAbsoluteEffectCertificateProblem q n) (r : ℕ)
    (i : Fin (n + 1)) : ℝ :=
  ∑ j, (P.architecture i j) ^ (r + 1)

/-- Reference evaluation: every moment of a zero architecture vanishes. -/
theorem architectureMoment_at_zero {q n : ℕ} (P : MeanAbsoluteEffectCertificateProblem q n)
    (r : ℕ) (i : Fin (n + 1)) (hzero : ∀ i' j, P.architecture i' j = 0) :
    architectureMoment P r i = 0 := by
  unfold architectureMoment
  simp [hzero]


noncomputable def mixtureExperiment {q n : ℕ}
    (P : MeanAbsoluteEffectCertificateProblem q n) :
    Decision.CertificateGrading.FiniteMixtureExperiment n n where
  target i := meanAbsoluteEffect (P.architecture i)
  moment := P.architectureMoment
  observation := P.observation

noncomputable def finiteProblem {q n : ℕ}
    (P : MeanAbsoluteEffectCertificateProblem q n) :
    Decision.CertificateGrading.FiniteMomentCertificateProblem n :=
  P.mixtureExperiment.certificateProblem

noncomputable def momentConstraintCalculus {q n : ℕ}
    (P : MeanAbsoluteEffectCertificateProblem q n) : Decision.CertificateGrading.CertificateCalculus
      :=
  Decision.CertificateGrading.explicitCalculus P.finiteProblem.modulus P.logScale

@[simp] theorem finiteProblem_target {q n : ℕ}
    (P : MeanAbsoluteEffectCertificateProblem q n) (i : Fin (n + 1)) :
    P.finiteProblem.target i = meanAbsoluteEffect (P.architecture i) := rfl

@[simp] theorem finiteProblem_moment {q n : ℕ}
    (P : MeanAbsoluteEffectCertificateProblem q n) (r : ℕ) (i : Fin (n + 1)) :
    P.finiteProblem.moment r i = P.architectureMoment r i := rfl

@[simp] theorem architectureMoment_zero {q n : ℕ}
    (P : MeanAbsoluteEffectCertificateProblem q n) (i : Fin (n + 1)) :
    P.architectureMoment 0 i = ∑ j, P.architecture i j := by
  simp [architectureMoment]

@[simp] theorem architectureMoment_one {q n : ℕ}
    (P : MeanAbsoluteEffectCertificateProblem q n) (i : Fin (n + 1)) :
    P.architectureMoment 1 i = ∑ j, (P.architecture i j) ^ 2 := by
  simp [architectureMoment]

/-- **What moment order two means biologically.**  It is not method power: the
two mixture priors have equal expected signed-effect sum and equal expected
squared-effect mass across the architecture catalogue.  The nonsmooth target
they may still separate is mean absolute effect. -/
theorem momentMatched_order_two_iff {q n : ℕ}
    (P : MeanAbsoluteEffectCertificateProblem q n)
    (A B : Decision.CertificateGrading.FinitePrior n) :
    P.finiteProblem.MomentMatched 2 A B ↔
      Decision.CertificateGrading.FinitePrior.mean A (fun i ↦ ∑ j, P.architecture i j) =
          Decision.CertificateGrading.FinitePrior.mean B (fun i ↦ ∑ j, P.architecture i j) ∧
        Decision.CertificateGrading.FinitePrior.mean A (fun i ↦ ∑ j, (P.architecture i j) ^ 2) =
          Decision.CertificateGrading.FinitePrior.mean B (fun i ↦ ∑ j, (P.architecture i j) ^ 2)
            := by
  constructor
  · intro h
    constructor
    · simpa only [Decision.CertificateGrading.FinitePrior.mean, finiteProblem_moment,
        architectureMoment_zero] using
        h 0 (by omega)
    · simpa only [Decision.CertificateGrading.FinitePrior.mean, finiteProblem_moment,
        architectureMoment_one] using
        h 1 (by omega)
  · rintro ⟨h0, h1⟩ r hr
    interval_cases r
    · simpa only [Decision.CertificateGrading.FinitePrior.mean, finiteProblem_moment,
        architectureMoment_zero] using h0
    · simpa only [Decision.CertificateGrading.FinitePrior.mean, finiteProblem_moment,
        architectureMoment_one] using h1

theorem effects_nonempty {q n : ℕ} (P : MeanAbsoluteEffectCertificateProblem q n) :
    P.effects.Nonempty := boundedEffectCarrier_nonempty q P.architectureRadius

theorem effects_convex {q n : ℕ} (P : MeanAbsoluteEffectCertificateProblem q n) :
    Convex ℝ P.effects := boundedEffectCarrier_convex q P.architectureRadius

/-- Exact biological specialization of the moment-constraint equality
criterion. -/
theorem momentConstraint_complete_iff_insensitive {q n : ℕ}
    (P : MeanAbsoluteEffectCertificateProblem q n) (K : ℕ) (h : ℝ) :
    P.momentConstraintCalculus.IsComplete K h ↔
      P.momentConstraintCalculus.GradeInsensitive K h :=
  Decision.CertificateGrading.isComplete_iff_gradeInsensitive P.momentConstraintCalculus K h

/-- Exact modulus-ratio identity for the mean-absolute-effect
moment-constraint problem. -/
theorem momentConstraint_deficit_eq_modulusRatio_sq {q n : ℕ}
    (P : MeanAbsoluteEffectCertificateProblem q n) (K : ℕ) (h : ℝ) :
    P.momentConstraintCalculus.deficit K h =
      (P.momentConstraintCalculus.modulus.Δ 0 h /
        P.momentConstraintCalculus.modulus.Δ K h) ^ 2 :=
  Decision.CertificateGrading.deficit_eq_modulus_ratio_sq P.momentConstraintCalculus K h

/-- Method-complexity gap for mean-absolute-effect lower bounds.  The numerator
allows arbitrary finite mixing priors on the architecture catalogue; the
denominator allows at most `K` atoms across the two priors. -/
noncomputable def atomCertificationGap {q n : ℕ}
    (P : MeanAbsoluteEffectCertificateProblem q n) (K : ℕ) (h : ℝ) : ℝ :=
  P.finiteProblem.modulus 0 h / P.finiteProblem.atomModulus K h

/-- Allowing more architecture atoms can only improve the certificate
modulus. -/
theorem atomModulus_mono {q n : ℕ}
    (P : MeanAbsoluteEffectCertificateProblem q n) {K L : ℕ}
    (hKL : K ≤ L) (h : ℝ) :
    P.finiteProblem.atomModulus K h ≤ P.finiteProblem.atomModulus L h :=
  P.finiteProblem.atomModulus_mono hKL h

/-- Every bounded-complexity biological certificate is available to the
unrestricted mixture calculus. -/
theorem atomModulus_le_unrestricted {q n : ℕ}
    (P : MeanAbsoluteEffectCertificateProblem q n) (K : ℕ) (h : ℝ) :
    P.finiteProblem.atomModulus K h ≤ P.finiteProblem.modulus 0 h :=
  P.finiteProblem.atomModulus_le_unrestricted K h

/-- Grade two is the ordinary comparison of two concrete genetic
architectures, evaluated with the actual prior-predictive total variation. -/
theorem atomFeasible_two_architectures_iff {q n : ℕ}
    (P : MeanAbsoluteEffectCertificateProblem q n) (h : ℝ)
    (i j : Fin (n + 1)) :
    P.finiteProblem.AtomFeasible 2 h (PMF.pure i) (PMF.pure j) ↔
      |P.mixtureExperiment.totalVariation (PMF.pure i) (PMF.pure j)| ≤ |h| :=
  P.finiteProblem.atomFeasible_two_pure_iff h i j

/-- The target separation of a point-versus-point biological certificate is
exactly the difference in mean absolute causal effect. -/
@[simp] theorem targetGap_two_architectures {q n : ℕ}
    (P : MeanAbsoluteEffectCertificateProblem q n) (i j : Fin (n + 1)) :
    P.finiteProblem.targetGap (PMF.pure i) (PMF.pure j) =
      |meanAbsoluteEffect (P.architecture i) -
        meanAbsoluteEffect (P.architecture j)| := by
  simp [Decision.CertificateGrading.FiniteMomentCertificateProblem.targetGap]

/-! #### Two architecture moments do not identify mean absolute effect

The following pair is a finite, exact witness to the biological obstruction behind the
moment-constrained calculus. Both three-locus architectures have total signed effect zero
and total squared-effect mass two:

* `β₀ = (1, -1, 0)`;
* `β₁ = (3/7, -8/7, 5/7)`.

Nevertheless their mean absolute effects are `2/3` and `16/21`. Thus even exact knowledge
of the first two architecture moments does not identify a nonsmooth sparsity/effect-size
summary. No asymptotics, literature theorem, or caller-supplied proposition enters this
witness.
-/

/-- Two three-locus architectures with the same first two power sums. Their observation
laws are deliberately identical, so every separation below comes from the biological
target rather than an arbitrary observation discrepancy. -/
noncomputable def orderTwoMomentTwinCatalogue :
    MeanAbsoluteEffectCertificateProblem 3 1 where
  architecture := ![![1, -1, 0], ![3 / 7, -8 / 7, 5 / 7]]
  observation := fun _ ↦ PMF.pure 0
  logScale := 0

/-- The two architectures have the same total signed effect. -/
theorem orderTwoMomentTwin_signedEffect :
    orderTwoMomentTwinCatalogue.architectureMoment 0 0 =
      orderTwoMomentTwinCatalogue.architectureMoment 0 1 := by
  norm_num [orderTwoMomentTwinCatalogue, architectureMoment, Fin.sum_univ_succ]

/-- The two architectures have the same total squared-effect mass. -/
theorem orderTwoMomentTwin_squaredEffect :
    orderTwoMomentTwinCatalogue.architectureMoment 1 0 =
      orderTwoMomentTwinCatalogue.architectureMoment 1 1 := by
  norm_num [orderTwoMomentTwinCatalogue, architectureMoment, Fin.sum_univ_succ]

/-- Hence the corresponding point priors match every architecture moment of order below
two. -/
theorem orderTwoMomentTwin_momentMatched :
    orderTwoMomentTwinCatalogue.finiteProblem.MomentMatched 2
      (PMF.pure 0) (PMF.pure 1) := by
  rw [momentMatched_order_two_iff]
  constructor
  · simpa only [Decision.CertificateGrading.FinitePrior.mean_pure, architectureMoment_zero] using
      orderTwoMomentTwin_signedEffect
  · simpa only [Decision.CertificateGrading.FinitePrior.mean_pure, architectureMoment_one] using
      orderTwoMomentTwin_squaredEffect

/-- Their mean absolute causal effects differ by exactly `2/21`. -/
theorem orderTwoMomentTwin_targetGap :
    orderTwoMomentTwinCatalogue.finiteProblem.targetGap (PMF.pure 0) (PMF.pure 1) =
      2 / 21 := by
  rw [targetGap_two_architectures]
  norm_num [orderTwoMomentTwinCatalogue, meanAbsoluteEffect, Fin.sum_univ_succ,
    abs_of_nonneg, abs_of_nonpos]

/-- **Biological non-identification at moment order two.** Equal mean signed effect and
equal additive variance do not determine mean absolute effect, even for two explicit
three-locus architectures. -/
theorem orderTwoMomentTwin_target_not_identified :
    orderTwoMomentTwinCatalogue.finiteProblem.MomentMatched 2
        (PMF.pure 0) (PMF.pure 1) ∧
      orderTwoMomentTwinCatalogue.finiteProblem.targetGap (PMF.pure 0) (PMF.pure 1) > 0 := by
  exact ⟨orderTwoMomentTwin_momentMatched, by rw [orderTwoMomentTwin_targetGap]; norm_num⟩

/-! #### The architecture hierarchy is strict

`atomModulus_mono` and `atomModulus_le_unrestricted` order the biological
certificate methods but permit the order to be flat, in which case
`atomCertificationGap` is one for every catalogue and grading a certificate by
how many architectures it mixes buys nothing. The catalogue below settles it.

Three one-locus architectures: a unit effect, the null, and the sign-flip of the
first. The target is mean **absolute** effect, so the two nonnull architectures
are indistinguishable targets and the null sits a full unit away. Their
observation laws are not indistinguishable -- the three emit the observation with probabilities `0`,
`1/2` and `1` -- and at information radius zero a certificate
must hold the prior-predictive law fixed.

A point-versus-point certificate then has to compare an architecture with itself,
because the three emission probabilities are distinct, so it certifies nothing.
Mixing the sign pair in equal parts reproduces the null's emission law exactly
while carrying the full unit of mean-absolute-effect separation. The sign
degeneracy of the target is what makes this possible, and it is the reason the
nonsmooth summary needs a method that mixes architectures rather than one that
compares them pairwise.
-/

/-- Unit effect, null, and sign-flip, emitting at rates `0`, `1/2`, `1`. -/
noncomputable def signPairCatalogue : MeanAbsoluteEffectCertificateProblem 1 2 where
  architecture := ![![1], ![0], ![-1]]
  observation := Decision.CertificateGrading.convexTargetObservation
  logScale := 0

theorem signPairCatalogue_target :
    signPairCatalogue.finiteProblem.target =
      Decision.CertificateGrading.convexTargetExperiment.certificateProblem.target := by
  funext i
  fin_cases i <;>
    simp [signPairCatalogue, finiteProblem, mixtureExperiment,
      Decision.CertificateGrading.FiniteMixtureExperiment.certificateProblem, meanAbsoluteEffect,
      Decision.CertificateGrading.convexTargetExperiment]

theorem signPairCatalogue_discrepancy :
    signPairCatalogue.finiteProblem.pairDiscrepancy =
      Decision.CertificateGrading.convexTargetExperiment.certificateProblem.pairDiscrepancy := by
  funext P Q
  exact Decision.CertificateGrading.FiniteMixtureExperiment.totalVariation_congr _ _ rfl P Q

/-- **Comparing architectures pairwise is strictly weaker than mixing them.**

For this catalogue the point-versus-point method certifies no
mean-absolute-effect separation at all, while the unrestricted mixture method
certifies a full unit. So the atom grade is a real hierarchy of biological
lower-bound methods, not a relabelling of one method. -/
theorem architecture_pairwise_certificates_incomplete :
    signPairCatalogue.finiteProblem.atomModulus 2 0 <
      signPairCatalogue.finiteProblem.modulus 0 0 := by
  rw [Decision.CertificateGrading.FiniteMomentCertificateProblem.atomModulus_congr _ _
        signPairCatalogue_target signPairCatalogue_discrepancy 2 0,
    Decision.CertificateGrading.FiniteMomentCertificateProblem.modulus_zero_congr _ _
        signPairCatalogue_target signPairCatalogue_discrepancy 0]
  exact Decision.CertificateGrading.twoAtom_certificates_incomplete

/-- The ratio form of the biological gap is junk at the catalogue that exhibits
the gap: `atomCertificationGap` divides by an atom modulus that is zero here, and
Lean's `x / 0 = 0` reports the smallest possible value for the largest possible
loss. `architecture_pairwise_certificates_incomplete` is the statement to read. -/
theorem signPairCatalogue_atomCertificationGap_is_junk :
    signPairCatalogue.atomCertificationGap 2 0 = 0 := by
  unfold atomCertificationGap
  rw [Decision.CertificateGrading.FiniteMomentCertificateProblem.atomModulus_congr _ _
    signPairCatalogue_target signPairCatalogue_discrepancy 2 0,
    Decision.CertificateGrading.convexTarget_atomModulus_two, div_zero]

end MeanAbsoluteEffectCertificateProblem

/-! ### Positivity buys an exponent: the moment body of architecture spectra

An architecture summary is a functional of a **positive** measure — the allele-frequency
spectrum, or the distribution of effect sizes. The set of moment sequences of such measures
is a *moment body*, and a moment body is much smaller than the coordinatewise box that
contains it.

Quantitatively, for the class whose boundary tail is at most `M t^α` the log covering number
is `Θ((M/ε)^(1/α))`, against `ε^(-2/(2α-1))` for the enclosing hyperrectangle. The two
exponents are named inputs here — the lower bound needs shell atoms and a
Varshamov–Gilbert argument, the upper bound needs smoothed convex hulls and Carl's
inequality, and neither is in Mathlib. **The comparison is the theorem**, and it holds at
every admissible `α` with no exceptional interval.

**Why this matters for a study.** Covering numbers are what set sample sizes for estimating
a class: the number of architectures distinguishable at resolution `ε` is what a design must
separate. Treating the architecture class as a box — which is what a coordinatewise
effect-size or frequency-bin prior amounts to — overstates that count **by a power of the
resolution**, not by a constant. So a sample-size calculation built on a box-shaped class is
conservative by a polynomial factor, and the positivity of the underlying spectrum is what
pays for the difference.

The entropy comparison is independent of the conditional certificate-gap proposal above.
It should not be used as evidence for that proposal: the first audit found no polynomial
certificate deficit in the tested Gaussian-mixture instance.

Empirical status: UNTESTED. -/

section MomentBodyEntropy

/-- Log covering number at resolution ratio `t = M/ε` and exponent `e`.

    Both classes below are of this shape and differ only in the exponent, which is why the
    comparison reduces to a comparison of exponents. -/
noncomputable def logCoveringAtExponent (t e : ℝ) : ℝ :=
  t ^ e

/-- **logCoveringAtExponent pinned at unit exponent.** No theorem in the corpus
evaluated this definition. A reference point with a fractional exponent is not
available to `norm_num` -- `(1/2) ^ (1/2)` is irrational -- so the pin is at
exponent one, where `Real.rpow_one` gives the base back and fixes that the second
argument is an exponent rather than a factor. -/
theorem logCoveringAtExponent_at_unit_exponent (t : ℝ) :
    logCoveringAtExponent t 1 = t := by
  unfold logCoveringAtExponent
  exact Real.rpow_one t

/-- **Strictly fewer distinguishable architectures, at every resolution finer than `M`.**

    Once the resolution ratio exceeds one — that is, once `ε < M`, the only regime in which
    a covering number is informative — the moment body's log covering number is strictly
    below the hyperrectangle's. The gap is a power of the resolution ratio, not a constant.

    This is the sample-size statement: a design that must separate the architecture class at
    resolution `ε` faces strictly fewer alternatives than a box-shaped class of the same
    tail order would present. -/
theorem momentBody_logCovering_lt (t α : ℝ) (ht : 1 < t) (hα : 1 / 2 < α) :
    logCoveringAtExponent t (Decision.momentBodyEntropyExponent α) <
      logCoveringAtExponent t (Decision.hyperrectangleEntropyExponent α) := by
  unfold logCoveringAtExponent
  exact Real.rpow_lt_rpow_left_iff ht |>.mpr
    (Decision.momentBody_entropy_exponent_lt α hα)

/-- The covering-number gap is a strict inequality of positive quantities, so the ratio of
    required alternative counts exceeds one. Recorded in the form a power calculation
    consumes. -/
theorem momentBody_logCovering_ratio_gt_one (t α : ℝ) (ht : 1 < t) (hα : 1 / 2 < α) :
    1 < logCoveringAtExponent t (Decision.hyperrectangleEntropyExponent α) /
      logCoveringAtExponent t (Decision.momentBodyEntropyExponent α) := by
  have ht0 : (0 : ℝ) < t := by linarith
  have hpos : 0 < logCoveringAtExponent t (Decision.momentBodyEntropyExponent α) :=
    Real.rpow_pos_of_pos ht0 _
  rw [lt_div_iff₀ hpos, one_mul]
  exact momentBody_logCovering_lt t α ht hα

end MomentBodyEntropy

end NonsmoothSummaries

end Descent.PopGen
