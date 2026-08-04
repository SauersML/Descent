/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Calibrator.ObservationalCeiling
import Calibrator.DriftRegime
import Calibrator.EpistaticChaos

namespace Calibrator

/-!
# The registry: seven instances of one law, and what a guard suite can buy

`Calibrator.ObservationalCeiling` states the law: a probe that reports the same data on
two objects certifies neither, so no criterion built from that probe decides any
property separating them. This file collects every instance the development now has,
and then proves the thing the collection is for.

## The instances

| # | probe | witness pair | kind | module |
|---|---|---|---|---|
| 1 | joint cumulant tensors of order `≤ K` | Gaussian vs. `tanh`-tilted blocks | mathematical | `CumulantBlindness` |
| 2 | normalized cumulant contractions, all orders | Gaussian vs. i.i.d. Rademacher | mathematical | `CumulantBlindness` |
| 3 | data on unions of `≤ r` cover elements | bipartite vs. non-bipartite Ramanujan twins | mathematical | `LocalToGlobalCoherence` |
| 4 | limits of disjoint-support chaos designs | Gaussian vs. a chameleon law | mathematical | `JetBarrier` |
| 5 | any complete invariant of the fiber relation | `ℓ∞`-divergent coded decay profiles | mathematical | `HiddenConeAmbiguity` |
| 6 | the cluster's internal cross-checks | two retention values | **methodological** | `DriftRegime` |
| 7 | a symmetric validation design | the ratio vs. its square | **methodological** | `DriftRegime` |
| 8 | Fisher's average effect | additive vs. dominant locus at `p = 1/2` | **genotypic** | this file |
| 9 | any statistic of normalised pairwise coalescence times | Kingman vs. Beta vs. Dirac coalescents | **methodological** | this file |

Instances 1-5 are theorems about the mathematics. Instances 6 and 7 are theorems about
the **development's own quality process**, and that is the point of assembling them in
one place: a cross-check is a probe, a validation design is a probe, and neither is
exempt from the law they are used to establish. A guard that cannot separate two
candidate definitions certifies neither of them, exactly as a cumulant that cannot
separate two laws certifies neither.

Instance 9 is the one that indicts this development's own measuring apparatus. With two
lineages a `Λ`-coalescent has a single exponential clock, so the pairwise coalescence time
is `Exp(λ)` and the reproductive regime enters ONLY through `λ`. Normalising by the mean
divides that rate straight out, and every model lands on `Exp(1)`. Measured
(`proofs/validation/empirical/simcov/battery_blind.py`), the raw mean pairwise time spans
four orders of magnitude across models -- `191.7` for Beta at `α = 1.1`, `977876` for a
Dirac coalescent -- while after normalisation every one of them agrees with Kingman:

  model              CV      skew    P(T > 2·mean)    sems from Kingman
  Kingman          1.0025   2.0876      0.1338              --
  Beta α = 1.9     0.9882   1.9541      0.1344         2.02 / 0.19
  Beta α = 1.5     0.9886   1.9199      0.1366         1.97 / 0.82
  Beta α = 1.1     0.9899   1.9663      0.1351         1.78 / 0.40
  Dirac ψ = 0.3    1.0024   2.0435      0.1323         0.01 / 0.43

The exponential values are `CV = 1`, `skew = 2`, `P = 0.1353`, and all five rows sit on
them. The site-frequency spectrum at `n = 10` separates the same models cleanly -- the
singleton fraction runs `0.3544` for Kingman to `0.4017` at `α = 1.1`, total variation up
to `0.047`, monotone in `α` -- because it reads branch lengths subtending three or more
leaves, which a pairwise probe never sees.

The merger sizes make the contrast as sharp as it can be made. Counting the arity of every
coalescence node over 3000 genealogies of twenty samples, on the SAME five models:

  model              binary   3-or-more    multiple-merger fraction
  Kingman             57000           0    0.0000 ± 0.0000
  Beta α = 1.9        54375        1186    0.0213 ± 0.0006
  Beta α = 1.5        43775        5634    0.1140 ± 0.0014
  Beta α = 1.1        33508        9397    0.2190 ± 0.0020
  Dirac ψ = 0.3       56590         182    0.0032 ± 0.0002

Kingman is exactly zero by construction and `α = 1.1` is more than a hundred sems away from
it, on the same runs whose normalised pairwise laws agreed to within two. A probe reading
three lineages at once separates what a probe reading two returns one number for. This is
the `λ₂,₂ = 1` versus `λ₃,₃ = 1/(β+2)` structure: normalisation forces the pairwise rate to
one for every measure, and the triple rate is what carries the regime.

**Why this belongs in a registry rather than a footnote.** Every `F_ST` in
`proofs/validation/empirical/simcov` is `1 - E[T_within] / E[T_between]`, a ratio of
pairwise quantities. So every `VALIDATED` marker that harness issued is valid *within
Kingman* and carries no information about any other regime, however many replicates were
run. Heterozygosity, `π`, and pairwise `F_ST` inherit the same ceiling. An instrument that
cannot report its own blind spot will eventually report someone else's answer as its own,
which is the rule `scripts/cluster-lean-build.sh` records for build logs and which applies
here unchanged.

Instance 8 is of a third kind. Its witness pair is two *loci*, and the property the probe
fails to certify — whether the heterozygote sits at the midpoint of the homozygotes — is a
genotypic fact a reader would expect a score to be sensitive to. It is the first entry
whose blindness has a direct experimental reading rather than a mathematical or procedural
one, and it is proved at the bottom of this file.

## What this file proves

The standing response to a discovered defect has been to add another guard. That
response works against *new* witness pairs and provably does not work against old ones:
`ProbeBlindness.ofWitnessFamily` says a single witness pair blinds an arbitrary family
of probes simultaneously, in any combination, under any rule for combining them.

`guard_stack_blind_to_retention` instantiates that at the incident. The three structural
guards that were in place — over-determination between related formulas, the duplicate
body check, and the naming-conflation check — all evaluate identically at every
retention value, because each of them examines the *algebra* relating cluster members
and the premise enters only as the *value* they share. So the suite as a whole was blind
before any of its members was written, and a fourth guard of the same kind would have
been blind too.

That is not an argument against guards. It is the criterion for what a new guard has to
do to be worth adding: **exhibit a pair the existing suite identifies and it separates.**
Guard 3j of `proofs/validation/code/check.py` (declare your regime) meets it — the two
regimes of `Calibrator.DriftRegime` are separated as objects, and a regime declaration is
data no algebraic check can supply. Guards 3k and 3l meet it for the same reason: they
read the *provenance* and the *power* of a validation, neither of which is a function of
the formulas.
-/

/-!
## 1. The structural guards, as probes on a candidate premise

The object under test is a candidate value of the shared premise `retention`. Each guard
is a predicate on that candidate: what the guard reports when the cluster is built from
it.
-/

/-- The three structural guards that were in place when the retention cluster was
written. Each is faithful to what the guard actually examines: a relation *among* the
cluster's members. -/
inductive StructuralGuard
  /-- Over-determination: relate independently written formulas so drift between them
  fails to compile (`Calibrator.Conventions`). -/
  | overDetermination
  /-- Duplicate bodies: one body under two names in two files, tied by nothing. -/
  | duplicateBody
  /-- Naming conflation: one formula carrying names from different concept families. -/
  | conflation

/-- What each guard reports when the cluster is instantiated at retention `r`.

Every one of these is a statement relating cluster members to each other. None of them
mentions an observable, and that is precisely the defect. -/
def StructuralGuard.verdict : StructuralGuard → ℝ → Prop
  | .overDetermination, r => targetHetOfRetention 1 r = 1 * (1 - lossOfRetention r)
  | .duplicateBody, r => lossOfRetention r = 1 - r
  | .conflation, r => targetPgsVarOfRetention 1 r = 1 * r

/-- **Every guard passes at every retention value.** The guards are satisfied by the
algebra alone, so they are satisfied by the wrong number exactly as readily as by the
right one. -/
theorem StructuralGuard.verdict_holds (g : StructuralGuard) (r : ℝ) : g.verdict r := by
  cases g <;>
    · simp only [StructuralGuard.verdict, targetHetOfRetention, lossOfRetention,
        targetPgsVarOfRetention]
      try ring

/-!
## 2. The suite is blind, as a suite
-/

/-- **The whole guard suite shares one witness pair.**

Two different retention values — the measured one and the one the cluster assumed —
produce identical reports from *every* structural guard. By
`ProbeBlindness.ofWitnessFamily`, no criterion reading the entire suite decides which
retention is correct, in any combination and under any rule.

This is why the same wrong number was certified five times: it was never five
independent certifications, it was one blind suite applied five times. -/
noncomputable def guard_stack_blind_to_retention {trueRetention wrongRetention : ℝ}
    (hne : wrongRetention ≠ trueRetention) :
    ProbeBlindness (fun r ↦ fun g : StructuralGuard ↦ g.verdict r)
      (fun r ↦ r = trueRetention) :=
  ProbeBlindness.ofWitnessFamily StructuralGuard.verdict _ trueRetention wrongRetention
    (fun g ↦ propext ⟨fun _ ↦ g.verdict_holds wrongRetention,
                       fun _ ↦ g.verdict_holds trueRetention⟩)
    rfl hne

/-- Spelled out, including every way of folding the suite's answers into one verdict:
no rule reading the structural guards decides whether the premise is right. -/
theorem no_guard_stack_criterion {trueRetention wrongRetention : ℝ}
    (hne : wrongRetention ≠ trueRetention)
    {Verdict : Type*} (combine : (StructuralGuard → Prop) → Verdict) :
    ¬ ∃ accept : Verdict → Prop,
        ∀ r : ℝ, r = trueRetention ↔ accept (combine (fun g ↦ g.verdict r)) :=
  (guard_stack_blind_to_retention hne).no_criterion_of_factors combine

/-- Adding a fourth guard of the same kind changes nothing: any predicate on candidate
retentions that is satisfied at every retention joins the suite without narrowing it. -/
noncomputable def extra_algebraic_guard_adds_nothing {trueRetention wrongRetention : ℝ}
    (hne : wrongRetention ≠ trueRetention)
    (newGuard : ℝ → Prop) (hnew : ∀ r, newGuard r) :
    ProbeBlindness (fun r ↦ (fun g : StructuralGuard ↦ g.verdict r, newGuard r))
      (fun r ↦ r = trueRetention) where
  positive := trueRetention
  negative := wrongRetention
  same_data := by
    have h₁ : (fun g : StructuralGuard ↦ g.verdict trueRetention)
        = fun g : StructuralGuard ↦ g.verdict wrongRetention := by
      funext g
      exact propext ⟨fun _ ↦ g.verdict_holds wrongRetention,
                     fun _ ↦ g.verdict_holds trueRetention⟩
    have h₂ : newGuard trueRetention = newGuard wrongRetention :=
      propext ⟨fun _ ↦ hnew wrongRetention, fun _ ↦ hnew trueRetention⟩
    rw [h₁, h₂]
  holds := rfl
  fails := hne

/-- The enlarged suite, spelled out the way `no_guard_stack_criterion` spells out the
original: no rule reading the structural guards together with the added one decides
whether the retention premise is right.

Stated because a blindness witness that no criterion theorem consumes proves nothing about
criteria -- it is a record with the right fields until something applies the law to it. -/
theorem no_enlarged_guard_stack_criterion {trueRetention wrongRetention : ℝ}
    (hne : wrongRetention ≠ trueRetention)
    (newGuard : ℝ → Prop) (hnew : ∀ r, newGuard r)
    {Verdict : Type*} (combine : ((StructuralGuard → Prop) × Prop) → Verdict) :
    ¬ ∃ accept : Verdict → Prop,
        ∀ r : ℝ, r = trueRetention ↔
          accept (combine (fun g : StructuralGuard ↦ g.verdict r, newGuard r)) :=
  (extra_algebraic_guard_adds_nothing hne newGuard hnew).no_criterion_of_factors combine

/-!
## 3. The criterion a new guard must meet

A guard is worth adding exactly when it separates a pair the existing suite identifies.
Stated as the contrapositive of the law: if the new guard is blind on the same pair, the
enlarged suite is blind on that pair (`extra_algebraic_guard_adds_nothing`); if it
separates the pair, it is not a function of the data the existing suite reads.

The three guards below are of the second kind, and each reads something the algebra does
not contain:

* **Regime declaration** reads the data-generating assumption. `DriftRegime.regimes_disagree`
  separates the two regimes as objects, so the declaration is not recoverable from any
  identity among formulas.
* **Validation provenance** reads whether a `VALIDATED` tag cites a measurement or a
  sibling. `DriftRegime.crossChecks_blind_to_retention` is exactly the statement that the
  sibling carries no information, so the distinction is real.
* **Validation power** reads the spread of the prediction across the design.
  `DriftRegime.symmetric_design_has_no_power` shows a design can have none, so the
  spread is not implied by the residual.

The general lesson, and the reason this registry exists rather than a longer list of
guards: an impossibility result and a quality process are the same kind of object. Both
are probes. Asking "what pair does this fail to separate?" is the only question that
distinguishes a check which can fail from one which cannot.
-/

/-!
## An instance with a genotypic referent: dominance at equal allele frequency

Every witness pair above separates two mathematical objects. This one separates two
*loci*, and the property it fails to certify is one a reader would assume a polygenic
score could see.

A one-locus architecture is a genotypic value `a` for the homozygote contrast and a
dominance deviation `d`, at allele frequency `p`. Fisher's average effect is
`α = a + d(1 - 2p)`: the coefficient a regression of phenotype on standardized dosage
recovers, and therefore the only thing a score built from dosages fits. `AdditiveInvariance`
already notes in prose that `α = a` when `d` vanishes; the point here is the converse
direction, which is sharper and is not recorded anywhere.

At `p = 1/2` the factor `1 - 2p` is zero, so `α = a` **whatever `d` is**. Two loci with the
same `a` and different dominance are then identical to the probe: same average effect, same
additive variance, same fitted weight, and they differ in a genotypic property — whether
the heterozygote sits at the midpoint of the homozygotes. Dominance is not attenuated at
equal frequency, it is *absent from the observable*.

This is why the corpus keeps meeting `p = 1/2` as a special point:
`EpistaticChaos.standardizedGenotype_symmetric_iff` locates it as the frequency at which
the standardized genotype is symmetric, and symmetry is exactly the collapse of the
odd coordinate that carries `d` into `α`. -/

/-- A one-locus genotypic architecture: additive contrast, dominance deviation, frequency. -/
structure OneLocusArchitecture where
  /-- Homozygote contrast. -/
  a : ℝ
  /-- Dominance deviation: displacement of the heterozygote from the midpoint. -/
  d : ℝ
  /-- Allele frequency. -/
  p : ℝ

/-- **Fisher's average effect**, the coefficient a dosage regression recovers.

    Empirical status: UNTESTED. -/
noncomputable def OneLocusArchitecture.averageEffect (m : OneLocusArchitecture) : ℝ :=
  m.a + m.d * (1 - 2 * m.p)

/-- **At equal allele frequencies the dominance deviation drops out of the average effect.**
This is why dominance is invisible to an additive scan run in a population at `p = 1/2`, and it is
the reference point that fixes the `1 - 2p` factor rather than any multiple of it. -/
theorem OneLocusArchitecture.averageEffect_at_half (m : OneLocusArchitecture) (h : m.p = 1 / 2) :
    m.averageEffect = m.a := by
  unfold OneLocusArchitecture.averageEffect
  rw [h]
  ring

/-! ### Wiring to the genotype core

The claim that the average effect is "what a dosage regression recovers" was carried by
the docstring above, which is the failure mode `Conventions` exists to prevent: a name
asserting a relationship to an observable that nothing connects it to. The architecture is
a triple of reals until it is attached to genotypes with frequencies.

`averageEffect_eq_regression_slope` is that attachment. It says the covariance of genotypic
value with allele dosage, under this development's own `HardyWeinbergModel` and its own
`genotypeProb`, is the genotype variance times the average effect — so the least-squares
slope of value on dosage *is* `α`. This is Fisher (1918) in one locus, and with it the
blindness instance below stops being about an abstract probe and becomes a statement about
regression on genotypes: the quantity a PGS fits.

Note what the wiring exposes. `d` enters the covariance only through the factor
`1 - 2 q`, and `genotypeVariance = 2 q (1 - q)` is symmetric about `q = 1/2` while
`1 - 2 q` vanishes there. The blindness is therefore not an artifact of the parameterisation
`(a, d)`; it is a property of the Hardy-Weinberg design matrix, which has no column that
separates the heterozygote from the homozygote midpoint when the two homozygotes are
equally frequent. -/

/-- Genotypic values: homozygotes at `∓a`, heterozygote displaced by `d` from their
midpoint.

    Empirical status: UNTESTED. Definitional within the model declared above: it
    fixes a contrast rather than predicting an observable. -/
def OneLocusArchitecture.genotypicValue (m : OneLocusArchitecture) : DiploidGenotype → ℝ
  | .homRef => -m.a
  | .het => m.d
  | .homAlt => m.a

/-- Mean genotypic value under Hardy-Weinberg proportions. -/
noncomputable def OneLocusArchitecture.meanValue
    (m : OneLocusArchitecture) (h : HardyWeinbergModel) : ℝ :=
  ∑ g : DiploidGenotype, h.genotypeProb g * m.genotypicValue g

/-- Covariance of genotypic value with allele dosage under Hardy-Weinberg. -/
noncomputable def OneLocusArchitecture.valueDosageCovariance
    (m : OneLocusArchitecture) (h : HardyWeinbergModel) : ℝ :=
  ∑ g : DiploidGenotype,
    h.genotypeProb g * (m.genotypicValue g - m.meanValue h) * h.centeredAltAlleleCount g

/-- **Fisher's theorem, one locus: the average effect is the dosage-regression slope.**

`Cov(value, dosage) = Var(dosage) · α`. Since `Var(dosage) = 2q(1-q)` is nonzero away from
fixation, the least-squares slope is exactly `α = a + d(1 - 2q)`, which is what makes the
average effect the observable rather than a definition. -/
theorem averageEffect_eq_regression_slope
    (m : OneLocusArchitecture) (h : HardyWeinbergModel) (hq : h.altFreq = m.p) :
    m.valueDosageCovariance h = h.genotypeVariance * m.averageEffect := by
  have hsum : h.refFreq + h.altFreq = 1 := by
    unfold HardyWeinbergModel.refFreq; ring
  unfold OneLocusArchitecture.valueDosageCovariance OneLocusArchitecture.meanValue
    HardyWeinbergModel.centeredAltAlleleCount OneLocusArchitecture.averageEffect
  rw [h.expectedAltAlleleCount_eq, h.genotypeVariance_eq]
  rw [sum_over_genotypes, sum_over_genotypes]
  simp only [HardyWeinbergModel.genotypeProb, altAlleleCount,
    OneLocusArchitecture.genotypicValue, HardyWeinbergModel.refFreq]
  rw [← hq]
  ring_nf

/-- **The average effect is blind to dominance at equal allele frequency.**

Instance 8 of the registry. Probe: the average effect. Witness pair: two loci with the same
homozygote contrast at `p = 1/2`, one additive and one not. Kind: genotypic.

The consequence, via `ProbeBlindness.no_criterion_of_factors`, is that *no* rule reading the
average effect — no significance threshold, no effect-size filter, no combination of them —
decides whether a locus is additive. A score fit on dosages is not approximately blind to
dominance at equal frequency; it is blind.

The probe is the observable and not merely a named quantity:
`averageEffect_eq_regression_slope` identifies it with the least-squares slope of genotypic
value on allele dosage under this development's own `HardyWeinbergModel`. So the object
this instance proves undecidable is the coefficient a polygenic score fits, not an
abstraction standing in for it.

    Empirical status: NOT AN EMPIRICAL CLAIM -- a proof object: it produces a
    `ProbeBlindness` witness, not a quantity. -/
noncomputable def averageEffect_blind_to_dominance {δ : ℝ} (hδ : δ ≠ 0) (a : ℝ) :
    ProbeBlindness OneLocusArchitecture.averageEffect (fun m ↦ m.d = 0) where
  positive := ⟨a, 0, 1 / 2⟩
  negative := ⟨a, δ, 1 / 2⟩
  same_data := by
    unfold OneLocusArchitecture.averageEffect
    norm_num
  holds := rfl
  fails := hδ

/-- **No criterion reading the average effect decides additivity.** -/
theorem no_averageEffect_criterion_for_additivity {δ : ℝ} (hδ : δ ≠ 0) (a : ℝ)
    {Verdict : Type*} (combine : ℝ → Verdict) :
    ¬ ∃ accept : Verdict → Prop,
        ∀ m : OneLocusArchitecture, m.d = 0 ↔ accept (combine m.averageEffect) :=
  (averageEffect_blind_to_dominance hδ a).no_criterion_of_factors combine

/-! ### The separation modulus, and why `p = 1/2` is not an isolated accident

Instance 8 is exact blindness at one frequency, and exact statements at single points are
the weakest kind of warning: a reader concludes the difficulty is confined to `p = 1/2` and
that any real panel avoids it. The quantitative statement says otherwise.

`averageEffect_separation` computes the modulus exactly: two loci differing by `Δ` in
dominance differ in average effect by `|1 - 2p| · Δ`. So the separation constant of
`ObservationalCeiling.ProbeSeparation` is here `σ(p) = |1 - 2p|`, and it does not fall off a
cliff at `1/2` — it decays linearly into it. `dominance_resolution_bound` is the
`δ / σ` form: at average-effect resolution `δ`, dominance is pinned only to `δ / |1 - 2p|`.

That is the practical reading of the whole registry. Instance 8 says common variants at
`p = 1/2` are a blind spot; this says the blind spot has a *neighbourhood*, with radius set
by the resolution of the study, and that common variants — the ones best powered for
additive effects — are exactly the ones in it. The two statements are the `σ = 0` and
`σ ≈ 0` faces of one fact. -/

/-- **The average effect separates dominance at rate `|1 - 2p|`.** -/
theorem averageEffect_separation (a d d' p : ℝ) :
    |(OneLocusArchitecture.mk a d p).averageEffect
        - (OneLocusArchitecture.mk a d' p).averageEffect|
      = |1 - 2 * p| * |d - d'| := by
  unfold OneLocusArchitecture.averageEffect
  have h : a + d * (1 - 2 * p) - (a + d' * (1 - 2 * p)) = (1 - 2 * p) * (d - d') := by ring
  simp only
  rw [h, abs_mul]

/-! ### Three facts, one fact

`q = 1/2` occurs three times in this development, proved separately each time:

* `EpistaticChaos.hweThirdCentralMoment_eq` gives the third central moment as
  `2q(1-q)(1-2q)`, which vanishes there;
* `EpistaticChaos.standardizedGenotype_symmetric_iff` shows a sign-symmetric coding exists
  exactly there;
* instance 8 above shows the average effect loses `d` exactly there.

They are the same fact. The Hardy-Weinberg dosage has one odd degree of freedom about its
mean; the third moment is its size, sign-symmetry is its vanishing, and the average effect's
sensitivity to dominance is what it carries. When it collapses, all three collapse together,
and none of the three is evidence for the others — they are one statement counted thrice.

The theorem below is that identification for the two ends of the chain that had not been
connected: the moment and the blindness. It matters because the corpus treats
`hweThirdCentralMoment ≠ 0` as a *hypothesis* in the epistasis arguments, and this says what
that hypothesis buys — precisely the visibility of dominance to a dosage regression. -/

/-- **The third central moment vanishes exactly when dominance is invisible.** -/
theorem thirdCentralMoment_zero_iff_dominance_invisible
    (h : HardyWeinbergModel) (hq0 : 0 < h.altFreq) (hq1 : h.altFreq < 1) :
    hweThirdCentralMoment h = 0 ↔
      ∀ a d d' : ℝ,
        (OneLocusArchitecture.mk a d h.altFreq).averageEffect =
          (OneLocusArchitecture.mk a d' h.altFreq).averageEffect := by
  have hne : h.altFreq * (1 - h.altFreq) ≠ 0 :=
    ne_of_gt (mul_pos hq0 (by linarith))
  rw [hweThirdCentralMoment_eq]
  constructor
  · intro hzero a d d'
    have hfac : 1 - 2 * h.altFreq = 0 := by
      rcases mul_eq_zero.mp (by linarith [hzero] :
          (2 * (h.altFreq * (1 - h.altFreq))) * (1 - 2 * h.altFreq) = 0) with hl | hr
      · exact absurd (by linarith : h.altFreq * (1 - h.altFreq) = 0) hne
      · exact hr
    unfold OneLocusArchitecture.averageEffect
    simp only
    rw [hfac]
    ring
  · intro hall
    have h1 := hall 0 1 0
    unfold OneLocusArchitecture.averageEffect at h1
    simp only at h1
    have hfac : 1 - 2 * h.altFreq = 0 := by linarith
    rw [hfac]
    ring

/-- **Dominance is pinned only to `δ / |1 - 2p|`.**

The recovery bound of `ProbeSeparation` in the genotypic instance: an average effect known
to resolution `δ` leaves a dominance interval that widens without bound as the allele
frequency approaches one half. -/
theorem dominance_resolution_bound (a d d' p δ : ℝ) (hp : 1 - 2 * p ≠ 0)
    (h : |(OneLocusArchitecture.mk a d p).averageEffect
          - (OneLocusArchitecture.mk a d' p).averageEffect| ≤ δ) :
    |d - d'| ≤ δ / |1 - 2 * p| := by
  rw [averageEffect_separation] at h
  rw [le_div_iff₀ (abs_pos.mpr hp), mul_comm]
  exact h

/-! ### Instance 9: normalised pairwise coalescence times

The mathematical core, stated on the survival function so it needs no measure theory.
With two lineages the only possible event is coalescence, so the time is exponential with
some rate `λ > 0` that carries the whole of the reproductive regime, and the mean is
`1 / λ`. Evaluating the survival function at `x` MEANS of that law gives `exp (-x)` for
every `λ`: the rate cancels. -/

/-- Survival function of the pairwise coalescence time at rate `lam`.

    Empirical status: NOT AN EMPIRICAL CLAIM in itself -- it is the exponential
    survival function, fixed by that description. What carries empirical content
    is instance 9 above, whose measurement is recorded there. -/
noncomputable def pairwiseCoalescentSurvival (lam t : ℝ) : ℝ := Real.exp (-(lam * t))

/-- **The normalised pairwise law does not depend on the rate.**

At `t = x / lam`, which is `x` multiples of the mean `1 / lam`, the survival probability is
`exp (-x)` whatever `lam` is. So no statistic of normalised pairwise coalescence times can
separate two `Λ`-coalescents, and the measured table above is what that looks like across
five models whose raw timescales differ by four orders of magnitude. -/
theorem pairwiseCoalescentSurvival_normalised (lam x : ℝ) (hlam : lam ≠ 0) :
    pairwiseCoalescentSurvival lam (x / lam) = Real.exp (-x) := by
  unfold pairwiseCoalescentSurvival
  rw [mul_div_cancel₀ x hlam]

/-- **Two regimes, one normalised law.** The blindness in the form the registry states its
other instances: two different rates, and the probe returns the same number at every `x`. -/
theorem normalised_pairwise_blind_to_rate (lam₁ lam₂ x : ℝ)
    (h₁ : lam₁ ≠ 0) (h₂ : lam₂ ≠ 0) :
    pairwiseCoalescentSurvival lam₁ (x / lam₁)
      = pairwiseCoalescentSurvival lam₂ (x / lam₂) := by
  rw [pairwiseCoalescentSurvival_normalised lam₁ x h₁,
    pairwiseCoalescentSurvival_normalised lam₂ x h₂]

end Calibrator
