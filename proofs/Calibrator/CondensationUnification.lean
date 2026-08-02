import Calibrator.PolygenicSpectroscopy
import Calibrator.EpistaticChaos
import Calibrator.LatentMechanismCollapse
import Calibrator.Conventions
import Calibrator.ScoreDistribution
import Calibrator.ImputationPortability
import Calibrator.PCCorrectability.Threshold

namespace Calibrator

/-!
# Unification: welding the condensation results onto the existing corpus

The condensation modules introduce new named population-genetic quantities, and
`Calibrator.Conventions` states the standing policy for exactly that situation:

> Against a wrong constant: over-determination. Derive the quantity from a primitive
> so the constant is forced, and relate independently written formulas so that drift
> between them fails to compile.

This file discharges that obligation for the new quantities, and then states the
concrete bridges to the four existing modules the new results touch.

## The guards

* `mellinDrift_uses_ploidy` — the standardization inside the Mellin drift is the
  *same* `ploidy` constant as the rest of the corpus. If anyone changes the factor of
  two in `Calibrator.Conventions.ploidy`, or writes `q (1 - q)` where the corpus means
  `2 q (1 - q)`, this file stops compiling. Without it, `hweMellinDrift` would be a
  free-floating formula with a population-genetic name and no obligation.
* `standardizedSquare_scale_invariant` — the whole Mellin observable triple is
  invariant under rescaling the dosage. This is what makes the lattice mechanism a
  genuinely *new* discrepancy rather than a restatement of imputation attenuation:
  attenuation is a variance rescaling, and rescalings act trivially here.

## The bridges

1. `additive_score_is_subcritical` — the additive apparatus is untouched.
2. `imputation_rescaling_cannot_repair_lattice` — a second, non-additive
   imputation discrepancy.
3. `scree_invariant_incomplete` — the number-of-PCs choice is a convention.
4. `mechanism_count_not_identifiable` — the number of GxE mechanisms is a convention.
-/

open scoped BigOperators

/-!
## 1. Over-determination guards
-/

/-- **Ploidy guard.** The genotype variance used to standardize the Mellin coordinate
is the corpus-wide `hweGenotypeVariance`, which is built from the single `ploidy`
constant. Drift between the two is now a compile error. -/
theorem mellinDrift_uses_ploidy (h : HardyWeinbergModel) :
    h.genotypeVariance = hweGenotypeVariance h.altFreq := by
  rw [h.genotypeVariance_eq]
  unfold hweGenotypeVariance ploidy HardyWeinbergModel.refFreq
  ring

/-- The same guard expressed on the standardized coordinate itself: the squared
standardized genotype is the squared centered dosage divided by the corpus genotype
variance, with no second convention introduced. -/
theorem standardizedSquare_eq_over_hweGenotypeVariance
    (h : HardyWeinbergModel) (g : DiploidGenotype) :
    h.standardizedSquare g =
      (h.centeredAltAlleleCount g) ^ 2 / hweGenotypeVariance h.altFreq := by
  unfold HardyWeinbergModel.standardizedSquare
  rw [mellinDrift_uses_ploidy]

/-- **Scale invariance of the multiplicative coordinate.** Rescaling the dosage by any
non-zero `λ` rescales the variance by `λ ^ 2` and leaves the squared standardized value
— hence the entire Mellin observable triple `(c, v, lattice datum)` — unchanged.

This is the precise reason the lattice discrepancy of `Calibrator.JetBarrier` is not a
restatement of the `r ^ 2` attenuation modelled in `Calibrator.ImputationPortability`:
attenuation is a rescaling, and rescalings act trivially on everything the
condensation theory measures. -/
theorem standardizedSquare_scale_invariant (c V lam : ℝ) (hV : V ≠ 0) (hlam : lam ≠ 0) :
    (lam * c) ^ 2 / (lam ^ 2 * V) = c ^ 2 / V := by
  rw [mul_pow, mul_div_mul_left _ _ (pow_ne_zero 2 hlam)]

/-!
## 2. The additive apparatus is untouched

`Calibrator.ScoreDistribution` and the Berry-Esseen certificates of
`Calibrator.Probability` describe degree-one aggregates. Those are deeply subcritical:
condensation never touches them, and the theorem below says so with an explicit
criterion rather than by assertion.
-/

/-- **The additive polygenic score is subcritical.** Whenever the number of terms
exceeds `exp (c(q))` — which for common variants means about three variants, and for a
variant at MAF `10 ^ (-4)` still only about five thousand — the additive score sits
strictly below the condensation boundary and the Gaussian surrogate is valid.

Genome-wide scores clear this by many orders of magnitude. The condensation theory
does not weaken the additive PGS apparatus; it bounds the degree to which that
apparatus may be extrapolated to interaction models. -/
theorem additive_score_is_subcritical {N q : ℝ}
    (hc : 0 < hweMellinDrift q) (hN : hweMellinDrift q < Real.log N) :
    1 < maxSafeEpistaticOrder N q := by
  rw [maxSafeEpistaticOrder_eq_criticalDegree, subcritical_iff hc]
  linarith

/-- The contrapositive form, in the vocabulary of an interaction model: an order-`m`
epistatic aggregate is past the boundary exactly when `m * c(q) ≥ log N`. Since `c(q)`
grows like `log (1 / q)`, the admissible order collapses for rare variants. -/
theorem epistatic_order_unsafe_iff {N q m : ℝ} (hc : 0 < hweMellinDrift q) :
    ¬ (m < maxSafeEpistaticOrder N q) ↔ Real.log N ≤ hweMellinDrift q * m := by
  rw [maxSafeEpistaticOrder_eq_criticalDegree, subcritical_iff hc, not_lt]

/-!
## 3. Imputation: a second discrepancy, not a restatement of the first
-/

/-- **Rescaling cannot repair the lattice discrepancy.**

`Calibrator.ImputationPortability` models the dosage/hard-call difference as an
attenuation of the second moment by the imputation `r ^ 2`, and that attenuation is
repaired exactly by rescaling. The lattice discrepancy is not: by
`standardizedSquare_scale_invariant` the observable triple is rescaling-invariant, so
for every rescaling factor the inflation factor at the hard-call lattice point stays
strictly above one.

Stated concretely: no choice of rescaling makes the hard-call intensity match a
nonlattice surrogate's. -/
theorem imputation_rescaling_cannot_repair_lattice (lam : ℝ) (hlam : lam ≠ 0) :
    1 < latticeInflation hardCallLatticeSpan ∧
      ∀ c V : ℝ, V ≠ 0 → (lam * c) ^ 2 / (lam ^ 2 * V) = c ^ 2 / V :=
  ⟨hardCall_intensity_inflated, fun c V hV => standardizedSquare_scale_invariant c V lam hV hlam⟩

/-!
## 4. The number of principal components is a convention
-/

/-- **No scree-type invariant is complete.**

A "scree invariant" is any assignment of a label to a loading-decay profile — an
eigenvalue-gap rule, an effective rank, a broken-stick cutoff, a parallel-analysis
threshold. If such an invariant were complete for the hidden-model equivalence, it
would separate every pair of profiles that are genuinely inequivalent. The theorem
says it must separate the coded profiles of any two `ℓ∞`-divergent sequences — while
those profiles have, by `Calibrator.HiddenConeAmbiguity`, *identical* complete
second-order observables.

So a complete scree invariant would be a function of data it provably does not see.
The number of principal components to retain is therefore a convention in the exact
sense of `Calibrator.Conventions`, and `Calibrator.PCCorrectability` correctly answers
the different question of what correction achieves *given* a convention. -/
theorem scree_invariant_incomplete
    {Invariant : Type*} (screeLabel : (ℕ → ℝ) → Invariant)
    (hcomplete : ∀ t t', BoundedLogDistortion t t' ↔ screeLabel t = screeLabel t')
    (B x y : ℕ → ℝ)
    (hdiv : ∀ C : ℝ, ∃ n : ℕ, C < |x n - y n|) :
    screeLabel (codedDecayProfile B x) ≠ screeLabel (codedDecayProfile B y) :=
  catalogue_induces_reduction screeLabel hcomplete B x y hdiv

/-- The positive half of the same dichotomy, in genetics vocabulary: if the ancestry
loadings are bounded below — finitely many components with a bounded condition number
— then the latent coordinates *are* recoverable and the convention is forced rather
than chosen. This is the regime in which PC correction is an inference. -/
theorem pc_loadings_identifiable_of_bounded_below
    {t t' : ℕ → ℝ} {a b a' b' : ℝ}
    (h : BoundedBelowAbove t a b) (h' : BoundedBelowAbove t' a' b') :
    BoundedLogDistortion t t' :=
  rigidity_of_boundedBelowAbove h h'

/-!
## 5. The number of gene-environment mechanisms is a convention
-/

/-- **Mechanism count is not identifiable from context variation.**

Instantiating `Calibrator.LatentMechanismCollapse.minimal_latent_dimension_is_constant`
with `Family` = smooth families of context-specific genotype-phenotype kernels: the
minimal latent dimension is `1` for every non-constant family, so it separates no two
families and carries no information about how many biological mechanisms generated the
data.

The repaired question, which does have content, is the boundary (Choquet-extreme)
factorization — in genetics, the archetypal-analysis requirement that mechanisms be
extremal profiles rather than interior blends. -/
theorem mechanism_count_not_identifiable
    {KernelFamily : Type*} (admitsDim : KernelFamily → ℕ → Prop)
    (minimalDim : KernelFamily → ℕ) (isContextInvariant : KernelFamily → Prop)
    (hminimal : ∀ F, admitsDim F (minimalDim F))
    (hleast : ∀ F r, admitsDim F r → minimalDim F ≤ r)
    (hcollapse : ∀ F, admitsDim F 1)
    (hnonzero : ∀ F, ¬ isContextInvariant F → ¬ admitsDim F 0) :
    ∀ F, ¬ isContextInvariant F → minimalDim F = 1 :=
  minimal_latent_dimension_is_constant admitsDim minimalDim isContextInvariant
    hminimal hleast hcollapse hnonzero

/-!
## 5b. Overlap is not free for genotypes

`Calibrator.EpistaticChaos.sign_erasure` shows that when a coding is **sign-symmetric**
— invariant under a value-negating relabelling — every truncated cross-moment between
distinct interaction monomials vanishes exactly.

Two separate things then have to be true before the independent-design theory of
`Calibrator.JetBarrier` could be quoted for a genome, and *both* fail.

1. Sign symmetry would have to hold for genotypes. It holds at `q = 1/2` and nowhere
   else in the polymorphic range, and at that frequency the second Mellin observable
   vanishes — this is `no_signSymmetric_nondegenerate_locus` below.
2. Sign symmetry would have to imply that overlapping designs behave like disjoint
   ones. It does not. Vanishing truncated cross-moments are a second-order statement,
   and the limit law of an overlapping design is not a second-order functional of the
   design: `Calibrator.EpistaticChaos.sign_symmetry_does_not_license_disjoint_reduction`
   exhibits, inside the symmetric class, a two-way interaction statistic with limiting
   fourth cumulant `6` where every disjoint design gives `0`.

So the honest statement is not "overlap is unresolved for genotypes" but "overlap is
resolved, negatively, for everyone": the licence for a Gaussian or chi-square null is
`Calibrator.EpistaticChaos.GenotypeDesign.VariantDisjoint`, and no property of the
coding substitutes for it.
-/

/-- **No polymorphic hard-called locus is both sign-symmetric and Mellin-non-degenerate.**

Two obstructions at complementary frequencies:

* away from `q = 1/2` the dosage has non-zero third central moment, so no
  value-negating relabelling exists and `sign_erasure` simply does not apply;
* at `q = 1/2` the relabelling exists, but the standardized square collapses to two
  values, `log x ^ 2` sits on a single point, and the second Mellin observable
  vanishes.

Consequence, and it is the honest statement of where the open direction lies: for real
genotypes the overlap between interaction terms — which in genetics *is* linkage
disequilibrium — cannot be argued away by symmetry. The disjoint-design theory proved
in this development is therefore not the whole story for a genome, and the overlapping
case remains exactly what `Calibrator.JetBarrier` says it is: the direction where the
observable algebra grows beyond the triple, and which is not proved here. -/
theorem no_signSymmetric_nondegenerate_locus
    (h : HardyWeinbergModel) (hq0 : 0 < h.altFreq) (hq1 : h.altFreq < 1) :
    (∀ coding : SymmetricCoding DiploidGenotype,
        (∀ g, coding.weight g = h.genotypeProb g) →
        (∀ g, coding.value g = h.centeredAltAlleleCount g) →
        h.altFreq = 1 / 2) ∧
      (h.altFreq = 1 / 2 → hweMellinJetVariance h.altFreq = 0) := by
  refine ⟨fun coding hweight hvalue => ?_, fun hhalf => ?_⟩
  · exact hwe_symmetricCoding_forces_half h hq0 hq1 coding hweight hvalue
  · rw [hhalf]
    exact hweMellinJetVariance_half

/-!
## 5c. The two gates on a set-based test, and where each comes from

The corpus already had one gate on an interaction analysis: `maxSafeEpistaticOrder`,
`log N / c(q)`, the interaction order past which condensation destroys the Gaussian
surrogate. That gate is about *order*. The overlap results supply a second gate, about
*structure*, and the two are logically independent — which is exactly why the first was
not enough.

`Calibrator.EpistaticChaos.GenotypeChaosLimits` states both directions over genotype
panels: `disjoint_segment` (Theorem D) says a design whose tested locus-sets are
pairwise disjoint has a Gaussian null with only the variance free, and
`maximal_spectrum` (Theorem S) says that at any prescribed polymorphic allele-frequency
family the non-disjoint designs realize the entire moment body. The theorems below weld
those to the drift and safe-order machinery of `Calibrator.PolygenicSpectroscopy`.
-/

/-- **Both gates, for a disjoint design.** Take a pairwise-disjoint admissible design
over polymorphic loci in linkage equilibrium, and a tested set `s` whose interaction
order `GenotypeDesign.interactionOrder` sits below the condensation boundary at the
allele frequency of one of its loci. Then both gates pass: the null is a centered
Gaussian with variance in `[0, 1]` (Theorem D), and the order is subcritical,
`c(q) * m < log N` (`epistatic_order_safe_iff`, hence `criticalDegree` through
`maxSafeEpistaticOrder_eq_criticalDegree`).

The conjuncts answer different questions and neither implies the other.
`maxSafeEpistaticOrder` says the aggregate has not condensed onto a few terms; Theorem D
says the surviving limit is Gaussian at all. Before the overlap results the corpus
carried only the first, and a reader could take "subcritical order" to mean "Gaussian
null". The next theorem shows that reading is wrong. -/
theorem disjoint_design_gaussian_null_below_condensation
    {ι : Type*} [Fintype ι] {n : ℕ} {Limit : Type*}
    (Sp : GenotypeChaosLimits n ι Limit) (design : GenotypeDesign n ι)
    (hadmissible : Sp.isAdmissible design) (hpolymorphic : design.Polymorphic)
    (hindependent : design.InLinkageEquilibrium) (hdisjoint : design.VariantDisjoint)
    (s : ι) (i : Fin n) {N : ℝ}
    (hdrift : 0 < hweMellinDrift (design.model i).altFreq)
    (hsafe : (design.interactionOrder s : ℝ) <
      maxSafeEpistaticOrder N (design.model i).altFreq) :
    (∃ s2 : ℝ, 0 ≤ s2 ∧ s2 ≤ 1 ∧ Sp.IsCenteredGaussian (Sp.limitLaw design) s2) ∧
      hweMellinDrift (design.model i).altFreq * design.interactionOrder s < Real.log N :=
  ⟨Sp.gaussian_null_licensed_of_disjoint design hadmissible hpolymorphic hindependent
      hdisjoint,
    (epistatic_order_safe_iff hdrift).mp hsafe⟩

/-- **A subcritical interaction order does not license an overlapping design.**

The hypotheses give a panel whose loci are polymorphic and an interaction order
strictly below the condensation boundary — everything the existing safe-order criterion
asks for. The conclusion is that the same panel still carries admissible designs whose
null is arbitrarily weakly close to *any* centered law with second moment at most one.

So `m < maxSafeEpistaticOrder N q` is necessary but not sufficient for a Gaussian null,
and the missing hypothesis is `GenotypeDesign.VariantDisjoint`. This is the precise
sense in which the safe-order table of `Calibrator.PolygenicSpectroscopy` must not be
read as a Gaussianity certificate for sliding-window or overlapping-panel scans. -/
theorem subcritical_order_does_not_license_overlapping_design
    {ι : Type*} [Fintype ι] {n : ℕ} {Limit : Type*}
    (Sp : GenotypeChaosLimits n ι Limit) (model : Fin n → HardyWeinbergModel)
    (hpolymorphic : ∀ i : Fin n, 0 < (model i).altFreq ∧ (model i).altFreq < 1)
    {N q m : ℝ} (hdrift : 0 < hweMellinDrift q) (hsafe : m < maxSafeEpistaticOrder N q)
    (target : Limit) (htarget : Sp.InMomentBody target) (ε : ℝ) (hε : 0 < ε) :
    hweMellinDrift q * m < Real.log N ∧
      ∃ design : GenotypeDesign n ι, design.model = model ∧
        design.InLinkageEquilibrium ∧ Sp.isAdmissible design ∧
        Sp.weakDistance (Sp.limitLaw design) target < ε :=
  ⟨(epistatic_order_safe_iff hdrift).mp hsafe,
    Sp.maximal_spectrum model hpolymorphic target htarget ε hε⟩

/-- **The moment body is reached at every drift profile.**

The design realizing an arbitrary target law sits on the *prescribed* panel, so its
per-locus Mellin drift is the panel's own `HardyWeinbergModel.mellinDrift`, equal in
closed form to `hweMellinDrift (q_i)` at each locus by
`HardyWeinbergModel.mellinDrift_eq`. The drift profile is therefore an arbitrary input
to the construction rather than an output of it: no value of `c(q)`, common or rare,
excludes any centered law with second moment at most one from being an overlapping
design's null.

This is the sharpest statement of how the two theories divide. The drift governs *when*
a high-order aggregate condenses; it says nothing whatever about the shape of the null
once the tested sets share variants. -/
theorem moment_body_reached_at_every_drift
    {ι : Type*} [Fintype ι] {n : ℕ} {Limit : Type*}
    (Sp : GenotypeChaosLimits n ι Limit) (model : Fin n → HardyWeinbergModel)
    (hpolymorphic : ∀ i : Fin n, 0 < (model i).altFreq ∧ (model i).altFreq < 1)
    (target : Limit) (htarget : Sp.InMomentBody target) (ε : ℝ) (hε : 0 < ε) :
    ∃ design : GenotypeDesign n ι, Sp.isAdmissible design ∧
      Sp.weakDistance (Sp.limitLaw design) target < ε ∧
      ∀ i : Fin n, (design.model i).mellinDrift = hweMellinDrift (model i).altFreq := by
  obtain ⟨design, hmodel, _, hadmissible, hclose⟩ :=
    Sp.maximal_spectrum model hpolymorphic target htarget ε hε
  refine ⟨design, hadmissible, hclose, fun i => ?_⟩
  rw [hmodel]
  exact (model i).mellinDrift_eq (hpolymorphic i).1 (hpolymorphic i).2

/-!
## 5d. Which set-based tests have a licensed Gaussian null

The practical output, derivable from the statements above rather than asserted here.

* **Licensed.** A gene-based burden or kernel test in which every variant is assigned
  to one gene: `Calibrator.EpistaticChaos.geneBurdenDesign_variantDisjoint` discharges
  disjointness, and `GenotypeChaosLimits.geneBurden_gaussian_null` returns a centered
  Gaussian null with the variance the only free parameter — at every allele frequency,
  needing polymorphism and linkage equilibrium and no symmetry.
* **Not licensed.** A sliding-window scan of width at least two:
  `Calibrator.EpistaticChaos.slidingWindowDesign_not_variantDisjoint` proves the tested
  sets share variants, so the licence does not apply, and by
  `subcritical_order_does_not_license_overlapping_design` the achievable nulls on that
  panel fill the whole moment body however low the interaction order is. The same holds
  for overlapping pathway or gene-set panels and for any pleiotropic variant recurring
  across tested sets, by `GenotypeDesign.not_variantDisjoint_of_recurrent`.

The gap between the two is not a variance mixture, which is what the folklore correction
for overlap supplies. A variance mixture of centered Gaussians is symmetric, unimodal
and has non-negative fourth cumulant; the moment body contains laws with none of those
properties, and the two-pool interaction statistic already leaves the mixture class with
fourth cumulant `6` at every allele frequency.

## 5e. Permutation and resampling calibration of overlapping designs

A set-based or interaction scan over overlapping locus-sets is routinely calibrated by
resampling: permute phenotypes, or reshuffle the variant-to-set assignment, recompute,
and read the null off the resampled distribution. The justification offered is that the
resampled design has *the same overlap statistics* — same number of sets, same set
sizes, same variant-recurrence profile.

That justification does not work, and the reason is structural rather than Monte Carlo
error. The null of an admissible overlapping design is a **spectral** invariant of its
overlap structure: `∑_k λ_k (W_k² - 1)` in the eigenvalues of the overlap operator.
Variant recurrence is a **profile** functional, and profile does not determine spectrum
— `Calibrator.EpistaticChaos.palindromic_circulant_spectra_differ` exhibits two `8 × 8`
palindromic circulants with the same entry multiset in every row and the same row sums
whose eigenvalue functions have different ranges, the first attaining `-4` where the
second cannot at any angle.
-/

/-- **Recurrence-preserving resampling is not a calibration.**

`resample` is any scheme preserving the variant-recurrence profile
`GenotypeDesign.variantRecurrence` — the summary a reshuffling scheme is designed to
hold fixed. If the null changes under it for even one design, then recurrence does not
determine the null, and no argument of the form "the resampled design has the same
overlap statistics" can justify the calibration.

The hypothesis `hnull` is what the spectral witness supplies: a resampling can move the
overlap spectrum while fixing every recurrence count. The theorem is silent on whether
a particular scheme is in fact miscalibrated, which is an empirical question about that
scheme. -/
theorem recurrence_preserving_resampling_is_not_a_calibration
    {ι : Type*} [Fintype ι] {n : ℕ} {Limit : Type*}
    (Sp : GenotypeChaosLimits n ι Limit)
    (resample : GenotypeDesign n ι → GenotypeDesign n ι)
    (hprofile : ∀ (design : GenotypeDesign n ι) (i : Fin n),
      (resample design).variantRecurrence i = design.variantRecurrence i)
    (start : GenotypeDesign n ι)
    (hnull : Sp.limitLaw (resample start) ≠ Sp.limitLaw start) :
    ¬ ∀ designOne designTwo : GenotypeDesign n ι,
        (∀ i : Fin n, designOne.variantRecurrence i = designTwo.variantRecurrence i) →
        Sp.limitLaw designOne = Sp.limitLaw designTwo := by
  intro hcomplete
  exact hnull (hcomplete (resample start) start (fun i => hprofile start i))

/-!
## 5f. The observable tower, and the fourth channel in closed form

The results above say what a *design* can hide. The Vertex-Weight Law says what a
*coding* can show, and for genotypes it lands on a computation this corpus can do
exactly.

In the diagram expansion of any truncated joint cumulant of an admissible design, the
coordinate law enters in three places: window factors, which see only the Mellin two-jet
`(c, v)` and the arithmetic type of `log x²`; even vertex weights at shared-variable
multiplicity `2j`, which are polynomials in the first `j` cumulants of `x²`; and odd
vertex weights — the sign couplings — which vanish exactly when the law is symmetric.

**A correction, which matters.** It does not follow that every cumulant of `x²` is
observable. Appearing in the range of the formula is not the same as being exposed by
some design, and the cumulants beyond the second are not: exposing the `j`-th for
`j ≥ 3` forces the second hub energy to diverge, which drives the design out of the
tempered class of `Calibrator.EpistaticChaos.GenotypeDesign.Tempered`, and in that phase
the limit is governed by the conditional-variance array rather than by cumulant rates —
an array that forgets them. So the naive list `{two-jet, arithmetic type, symmetry,
cumulants of x²}` overstates what is observable, and this file no longer asserts it. The
obstruction is exactly the hub-energy divergence already formalized here, which is why
`ObservableTower` carries it as a field rather than as a remark.

**The replacement is a recursion.** The conditional-variance array of an admissible
design is itself a design — multilinear in the centered squares, with coordinate law the
law of `x²` — so the observable algebra is self-similar:

> `OA(ν) = { two-jet(ν), arithmetic type(ν), symmetry(ν) } ∪ OA(law of x²)`,

to finite depth. The naive list is the shadow of the first two floors: `κ₂(x²)` is
exposed precisely because it is the *variance* of level two, which is what a second floor
reads. Whether the tower has a genuine second floor or truncates at depth one is **open
upstream** — the reachability computation that decides it is outstanding — so `depth` is
a parameter here and `TruncatesAtDepthOne` is a hypothesis, never an assertion.

**The fourth channel, exactly.** For a standardized Hardy-Weinberg genotype the fourth
moment is the reciprocal of the genotype variance,
`Calibrator.EpistaticChaos.standardizedGenotype_fourth_moment`, and in the corpus's own
primitive that reads `E[x⁴] = 1 / hweGenotypeVariance q`. Two consequences are stated
below and both are checkable: the level-two coordinate is never symmetric, at any allele
frequency, so that channel is always live one floor up; and the hub channel is blind at
one specific frequency, `MAF = (3 - √3)/6 = 0.211324…`, where the standardized genotype
has exactly Gaussian kurtosis.
-/

/-- **The fourth channel against the corpus primitive.** `E[x⁴] = 1 / hweGenotypeVariance q`.

This is the over-determination tie for the new observable: the fourth moment is not a
free constant but the reciprocal of the same `hweGenotypeVariance` that
`mellinDrift_uses_ploidy` pins to `ploidy`. Change the ploidy convention and this stops
compiling. -/
theorem hweStandardizedFourthMoment_eq_inv_hweGenotypeVariance (h : HardyWeinbergModel)
    (hq0 : 0 < h.altFreq) (hq1 : h.altFreq < 1) :
    ∑ g : DiploidGenotype, h.genotypeProb g * h.standardizedGenotype g ^ 4 =
      1 / hweGenotypeVariance h.altFreq := by
  rw [standardizedGenotype_fourth_moment h hq0 hq1, mellinDrift_uses_ploidy]

/-- The squared standardized genotype is the corpus's `standardizedSquare`: the level-two
coordinate of the tower is an object this development already had. -/
theorem standardizedGenotype_sq_eq_standardizedSquare (h : HardyWeinbergModel)
    (hq0 : 0 < h.altFreq) (hq1 : h.altFreq < 1) (g : DiploidGenotype) :
    h.standardizedGenotype g ^ 2 = h.standardizedSquare g := by
  have hvar : 0 < h.genotypeVariance := by
    rw [h.genotypeVariance_eq]
    unfold HardyWeinbergModel.refFreq
    have hcomp : (0 : ℝ) < 1 - h.altFreq := by linarith
    nlinarith [hq0, hcomp]
  have hsq : Real.sqrt h.genotypeVariance ^ 2 = h.genotypeVariance :=
    Real.sq_sqrt hvar.le
  unfold HardyWeinbergModel.standardizedGenotype HardyWeinbergModel.standardizedSquare
  rw [div_pow, hsq]

/-- **The level-two coordinate is never symmetric.** `x²` takes the three values
`2q/(1-q)`, `(1-2q)²/(2q(1-q))`, `2(1-q)/q`, all non-negative and not all zero, so no
value-negating relabelling exists at *any* polymorphic allele frequency — including
`q = 1/2`, where the level-one coordinate is symmetric.

The proof is the third-moment detector of `symmetricCoding_third_moment_zero`: a
symmetric coding has vanishing third moment, while `E[(x²)³]` is a sum of non-negative
terms with a strictly positive one.

So the sign-coupling channel, which at level one is live only away from `q = 1/2`
(`standardizedGenotype_symmetric_iff`), is live at level two at every frequency. Symmetry
fails one floor up, always. -/
theorem standardizedSquare_never_symmetric (h : HardyWeinbergModel)
    (hq0 : 0 < h.altFreq) (hq1 : h.altFreq < 1) :
    ¬ ∃ coding : SymmetricCoding DiploidGenotype,
        (∀ g, coding.weight g = h.genotypeProb g) ∧
        (∀ g, coding.value g = h.standardizedSquare g) := by
  rintro ⟨coding, hweight, hvalue⟩
  have hzero : ∑ g : DiploidGenotype,
      h.genotypeProb g * h.standardizedSquare g ^ 3 = 0 := by
    have hterm : ∀ g : DiploidGenotype,
        h.genotypeProb g * h.standardizedSquare g ^ 3 =
          coding.weight g * coding.value g ^ 3 := by
      intro g
      rw [hweight, hvalue]
    simp_rw [hterm]
    exact symmetricCoding_third_moment_zero coding
  obtain ⟨_, _, halt⟩ := standardizedSquare_values h hq0 hq1
  have hprob := genotypeProb_values h
  have hcomp : (0 : ℝ) < 1 - h.altFreq := by linarith
  have hvar : 0 < h.genotypeVariance := by
    rw [h.genotypeVariance_eq]
    unfold HardyWeinbergModel.refFreq
    nlinarith [hq0, hcomp]
  have hnonneg : ∀ g : DiploidGenotype,
      0 ≤ h.genotypeProb g * h.standardizedSquare g ^ 3 := by
    intro g
    have hp : 0 ≤ h.genotypeProb g := h.genotypeProb_nonneg g
    have hs : 0 ≤ h.standardizedSquare g := by
      have hdef : h.standardizedSquare g =
          h.centeredAltAlleleCount g ^ 2 / h.genotypeVariance := rfl
      rw [hdef]
      exact div_nonneg (sq_nonneg _) hvar.le
    exact mul_nonneg hp (pow_nonneg hs 3)
  have hpos : 0 < h.genotypeProb DiploidGenotype.homAlt *
      h.standardizedSquare DiploidGenotype.homAlt ^ 3 := by
    rw [halt, hprob.2.2]
    have hnum : (0 : ℝ) < 2 * (1 - h.altFreq) := by linarith
    have hval : 0 < 2 * (1 - h.altFreq) / h.altFreq := div_pos hnum hq0
    exact mul_pos (pow_pos hq0 2) (pow_pos hval 3)
  rw [sum_diploidGenotype] at hzero
  linarith [hzero, hnonneg DiploidGenotype.homRef, hnonneg DiploidGenotype.het, hpos]

/-- **The allele frequency at which the hub channel is blind**, `(3 - √3)/6 = 0.211324…`.

The fourth-cumulant channel separates a coordinate law from the Gaussian exactly when
`E[x⁴] ≠ 3`. Since `E[x⁴] = 1 / (2q(1-q))`, the channel closes when `2q(1-q) = 1/3`, that
is `6q² - 6q + 1 = 0`, whose polymorphic roots are `(3 ± √3)/6`. The minor-allele root is
this constant.

Empirical status: DERIVED. The constant is the polymorphic root of `6q² - 6q + 1`, forced
by `hweGenotypeVariance` through `standardizedGenotype_fourth_moment`;
`gaussianKurtosisMaf_genotypeVariance` proves the variance identity and
`standardizedGenotype_kurtosis_gaussian_at_blind_maf` proves the fourth moment is `3`
there. Nothing is fitted and there is no free parameter.

What is *not* tested is the consequence rather than the constant: the prediction that an
interaction statistic relying on fourth-cumulant separation loses power near this
frequency has not been checked in simulation. It is the most directly falsifiable number
this development produces. -/
noncomputable def gaussianKurtosisMaf : ℝ := (3 - Real.sqrt 3) / 6

theorem sqrt_three_sq : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)

theorem sqrt_three_lt_two : Real.sqrt 3 < 2 := by
  nlinarith [sqrt_three_sq, Real.sqrt_nonneg 3]

theorem sqrt_three_pos : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)

theorem gaussianKurtosisMaf_pos : 0 < gaussianKurtosisMaf := by
  unfold gaussianKurtosisMaf
  have := sqrt_three_lt_two
  linarith

theorem gaussianKurtosisMaf_lt_one : gaussianKurtosisMaf < 1 := by
  unfold gaussianKurtosisMaf
  have := sqrt_three_pos
  linarith

/-- At the blind frequency the genotype variance is exactly `1/3`. -/
theorem gaussianKurtosisMaf_genotypeVariance :
    hweGenotypeVariance gaussianKurtosisMaf = 1 / 3 := by
  unfold hweGenotypeVariance ploidy gaussianKurtosisMaf
  nlinarith [sqrt_three_sq]

/-- **The standardized genotype has exactly Gaussian kurtosis at `MAF = (3 - √3)/6`.**

At that frequency `E[x⁴] = 3`, so the fourth-cumulant channel cannot separate a genotype
coordinate from a Gaussian one, and an interaction statistic whose power comes from
fourth-cumulant separation — the two-pool witness of `Calibrator.EpistaticChaos` is the
model case, with its limiting fourth cumulant `6` — has no hub-channel signal there.

Read alongside the other two channels this gives a frequency-by-frequency map: symmetry
is available only at `MAF = 1/2` (`standardizedGenotype_symmetric_iff`), the drift grows
like `log (1/2q)` for rare variants (`rare_variant_drift_lower_bound`), and the hub
channel closes at this one interior frequency. No single frequency is blind in all
channels, but each channel has its own blind set, and this one is a point. -/
theorem standardizedGenotype_kurtosis_gaussian_at_blind_maf (h : HardyWeinbergModel)
    (hmaf : h.altFreq = gaussianKurtosisMaf) :
    ∑ g : DiploidGenotype, h.genotypeProb g * h.standardizedGenotype g ^ 4 = 3 := by
  have hq0 : 0 < h.altFreq := by
    rw [hmaf]
    exact gaussianKurtosisMaf_pos
  have hq1 : h.altFreq < 1 := by
    rw [hmaf]
    exact gaussianKurtosisMaf_lt_one
  rw [hweStandardizedFourthMoment_eq_inv_hweGenotypeVariance h hq0 hq1, hmaf,
    gaussianKurtosisMaf_genotypeVariance]
  norm_num

/-!
### The tower itself

`LevelChannels` is one floor: the two-jet, the arithmetic type, the symmetry verdict.
`ObservableTower` is the recursion, with the depth a parameter and the truncation a
hypothesis.
-/

/-- The channels available at one floor of the observable tower. -/
structure LevelChannels where
  /-- The size-biased drift `c = E[x² log x²]` of that floor's coordinate. -/
  drift : ℝ
  /-- The size-biased increment variance `v` of that floor's coordinate. -/
  jetVariance : ℝ
  /-- Whether that floor's `log x²` is supported on an arithmetic progression. -/
  IsLattice : Prop
  /-- Whether that floor's coordinate admits a value-negating relabelling. -/
  IsSignSymmetric : Prop

/-- Floor one of the tower for a Hardy-Weinberg locus, assembled from quantities this
corpus computes in closed form.

Empirical status: DERIVED from `hweMellinDrift`, `hweMellinJetVariance` and
`hweLatticeCondition`, each derived elsewhere in the corpus, together with the symmetry
characterization `standardizedGenotype_symmetric_iff`; no free parameter and nothing
fitted. -/
noncomputable def hweLevelOne (q : ℝ) : LevelChannels where
  drift := hweMellinDrift q
  jetVariance := hweMellinJetVariance q
  IsLattice := hweLatticeCondition q
  IsSignSymmetric := q = 1 / 2

/-- **Floor one is built from the corpus's own quantities**, component by component: the
over-determination guard for the completeness claim. If anyone changes what
`hweMellinDrift`, `hweMellinJetVariance` or `hweLatticeCondition` means, this stops
compiling rather than drifting. -/
theorem hweLevelOne_components (q : ℝ) :
    (hweLevelOne q).drift = hweMellinDrift q ∧
      (hweLevelOne q).jetVariance = hweMellinJetVariance q ∧
      (hweLevelOne q).IsLattice = hweLatticeCondition q ∧
      (hweLevelOne q).IsSignSymmetric = (q = 1 / 2) :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- **The symmetry slot of floor one is the corpus's proved characterization**, so it is
not a slot awaiting work: it is decided, and decided negatively away from `q = 1/2`. -/
theorem hweLevelOne_symmetry (h : HardyWeinbergModel)
    (hq0 : 0 < h.altFreq) (hq1 : h.altFreq < 1) :
    (hweLevelOne h.altFreq).IsSignSymmetric ↔
      (∃ coding : SymmetricCoding DiploidGenotype,
        (∀ g, coding.weight g = h.genotypeProb g) ∧
        (∀ g, coding.value g = h.standardizedGenotype g)) := by
  have hcomponent : (hweLevelOne h.altFreq).IsSignSymmetric = (h.altFreq = 1 / 2) := rfl
  rw [hcomponent]
  exact (standardizedGenotype_symmetric_iff h hq0 hq1).symm

/-- Where floor one is symmetric its jet variance vanishes: two of its channels collapse
together, which is `no_signSymmetric_nondegenerate_locus` read off the tower. -/
theorem hweLevelOne_symmetric_jetVariance_zero (q : ℝ)
    (hsymmetric : (hweLevelOne q).IsSignSymmetric) :
    (hweLevelOne q).jetVariance = 0 := by
  have hcomponent : (hweLevelOne q).IsSignSymmetric = (q = 1 / 2) := rfl
  rw [hcomponent] at hsymmetric
  have hjet : (hweLevelOne q).jetVariance = hweMellinJetVariance q := rfl
  rw [hjet, hsymmetric]
  exact hweMellinJetVariance_half

/-- Re-model a design: the same tested locus-sets, coefficients and joint law, at a
different allele-frequency family. This is what varying the coordinate law while holding
the design fixed means.

Empirical status: UNTESTED. A field update on a design; no modelling content and no free
parameter. -/
def GenotypeDesign.reModel {ι : Type*} {n : ℕ} (design : GenotypeDesign n ι)
    (model : Fin n → HardyWeinbergModel) : GenotypeDesign n ι :=
  { design with model := model }

/-- The observable tower over a genotype panel, with its depth a parameter.

`levelChannels design floor i` is the channel data of locus `i` at that floor. The
Vertex-Weight field says the limit depends on the allele-frequency family only through
the channels, floor by floor, up to the tower's depth — and through nothing else.

The `higher_cumulants_need_divergent_hub` field carries the correction: a design that
exposes a cumulant of `x²` beyond the second cannot have bounded hub recurrence, so it
sits outside the tempered class where cycle densities determine the limit. That is why
the naive list is not the answer and the recursion is. -/
structure ObservableTower (n : ℕ) (ι : Type*) (Limit : Type*) where
  /-- Minimum interaction order diverging, influence vanishing, unit variance. -/
  isAdmissible : GenotypeDesign n ι → Prop
  /-- The limit law of a design's statistic. -/
  limitLaw : GenotypeDesign n ι → Limit
  /-- How many floors the tower is taken to. -/
  depth : ℕ
  /-- The channel data of one locus at one floor: floor `0` is `hweLevelOne`. -/
  levelChannels : ℕ → ℝ → LevelChannels
  /-- Floor zero is the level-one channel data of the corpus. -/
  levelChannels_zero : ∀ q : ℝ, levelChannels 0 q = hweLevelOne q
  /-- Which square-cumulant order a design exposes. -/
  Exposes : GenotypeDesign n ι → ℕ → Prop
  /-- **The Vertex-Weight Law (analytic input).** Two allele-frequency families whose
  channels agree at every floor up to the depth give the same limit, for every design. -/
  vertex_weight : ∀ (design : GenotypeDesign n ι) (model model' : Fin n → HardyWeinbergModel),
    isAdmissible (design.reModel model) → isAdmissible (design.reModel model') →
    (∀ (floor : ℕ) (i : Fin n), floor ≤ depth →
      levelChannels floor (model i).altFreq = levelChannels floor (model' i).altFreq) →
    limitLaw (design.reModel model) = limitLaw (design.reModel model')
  /-- **The exposure correction (analytic input).** Exposing a square cumulant of order
  three or more forces the second hub energy to diverge, so no hub bound survives. -/
  higher_cumulants_need_divergent_hub : ∀ (design : GenotypeDesign n ι) (order : ℕ),
    3 ≤ order → Exposes design order → ∀ bound : ℕ, ¬ design.BoundedHubRecurrence bound

namespace ObservableTower

variable {n : ℕ} {ι : Type*} {Limit : Type*} (T : ObservableTower n ι Limit)

/-- **Observability completeness, to the tower's depth.** Any experiment reporting a
function of a design's limit is a function of the channel data alone: two panels agreeing
floor by floor are indistinguishable by every admissible design, at every interaction
order, through every diagram. -/
theorem experiment_factors_through_channels
    {Report : Type*} (experiment : Limit → Report)
    (design : GenotypeDesign n ι) (model model' : Fin n → HardyWeinbergModel)
    (hadmissible : T.isAdmissible (design.reModel model))
    (hadmissible' : T.isAdmissible (design.reModel model'))
    (hchannels : ∀ (floor : ℕ) (i : Fin n), floor ≤ T.depth →
      T.levelChannels floor (model i).altFreq = T.levelChannels floor (model' i).altFreq) :
    experiment (T.limitLaw (design.reModel model)) =
      experiment (T.limitLaw (design.reModel model')) := by
  rw [T.vertex_weight design model model' hadmissible hadmissible' hchannels]

/-- **A design that reaches past the second square cumulant has left the tempered class.**
The contrapositive of the exposure correction, in the form a practitioner meets it: if
every variant is tested a bounded number of times, no cumulant of `x²` beyond the second
is exposed, whatever the design does. -/
theorem boundedHub_exposes_no_higher_cumulant
    (design : GenotypeDesign n ι) (bound : ℕ)
    (hhub : design.BoundedHubRecurrence bound) (order : ℕ) (horder : 3 ≤ order) :
    ¬ T.Exposes design order := by
  intro hexposes
  exact T.higher_cumulants_need_divergent_hub design order horder hexposes bound hhub

/-- **If the tower truncates at depth one, the complete observable content of a genotype
coding is a four-element list**: the drift, the jet variance, the arithmetic type and the
symmetry verdict of floor one, together with the fourth moment `E[x⁴] = 1/(2q(1-q))`
which is the variance of floor two.

The truncation is the hypothesis `htruncates`, stated in the type rather than assumed in
prose, because the reachability computation that decides it is open upstream. If the tower
has a genuine second floor, this theorem is silent and the extra floors are given by
`levelChannels 1`, `levelChannels 2`, … applied to the law of `x²`. -/
theorem complete_content_of_truncation
    (htruncates : T.depth = 0)
    (design : GenotypeDesign n ι) (model model' : Fin n → HardyWeinbergModel)
    (hadmissible : T.isAdmissible (design.reModel model))
    (hadmissible' : T.isAdmissible (design.reModel model'))
    (hdrift : ∀ i : Fin n, hweMellinDrift (model i).altFreq =
      hweMellinDrift (model' i).altFreq)
    (hjet : ∀ i : Fin n, hweMellinJetVariance (model i).altFreq =
      hweMellinJetVariance (model' i).altFreq)
    (hlattice : ∀ i : Fin n, hweLatticeCondition (model i).altFreq =
      hweLatticeCondition (model' i).altFreq)
    (hsymmetry : ∀ i : Fin n, ((model i).altFreq = 1 / 2) = ((model' i).altFreq = 1 / 2)) :
    T.limitLaw (design.reModel model) = T.limitLaw (design.reModel model') := by
  refine T.vertex_weight design model model' hadmissible hadmissible' ?_
  intro floor i hfloor
  rw [htruncates] at hfloor
  have hzero : floor = 0 := Nat.le_zero.mp hfloor
  rw [hzero, T.levelChannels_zero, T.levelChannels_zero]
  unfold hweLevelOne
  rw [hdrift i, hjet i, hlattice i, hsymmetry i]

end ObservableTower

/-!
## 5g. Panels are mixtures, and that is where the tower bites

Floor two of the observable tower is real: the centered square `u = x² - 1` carries
Mellin data that no floor-one channel sees
(`Calibrator.EpistaticChaos.centeredSquare_third_moment_eq`), and the trap beside it —
tuning *uncentered* products, whose logarithm is the level-one walk again — is ruled out
by `uncentered_square_log_additive`.

For a single locus none of this matters, and that is proved rather than assumed:
`singleLocus_tower_collapses` shows two polymorphic loci agreeing in the fourth moment
agree in every even moment, because equal fourth moments force equal variance, equal
variance forces `q' ∈ {q, 1-q}`, and reflection makes those two agree on all even data.
A standardized Hardy-Weinberg coordinate has a one-parameter law and floor one already
pins it.

Panels are different, and the difference is the whole point. A real panel's effective
coordinate law is a **mixture** over its allele-frequency spectrum, and a mixture's
floor-one invariants are mixture averages: the drift, the jet variance, the lattice type,
and the fourth moment, which is the mixture mean of `1/(2q(1-q))`. Mixtures are not
determined by such low-order data. Two MAF spectra can agree on every floor-one invariant
and differ at floor two, hence give different nulls for the *same* interaction statistic.

That is a difference between things that genuinely differ between studies: MAF spectra
differ between populations, between arrays and sequencing platforms, and after any
frequency-based filtering. So the operational statement is the one below — matching
floor-one invariants across two panels does not license transporting a calibration
between them.
-/

/-- A panel's **allele-frequency spectrum**: the loci it contains and their weights. The
effective coordinate law of the panel is the corresponding mixture of standardized
genotype laws. -/
structure MafSpectrum (m : ℕ) where
  /-- The Hardy-Weinberg model of each spectrum atom. -/
  model : Fin m → HardyWeinbergModel
  /-- The weight of each atom. -/
  weight : Fin m → ℝ
  /-- Weights are non-negative. -/
  weight_nonneg : ∀ j, 0 ≤ weight j
  /-- Weights sum to one. -/
  weight_sum : ∑ j, weight j = 1

namespace MafSpectrum

variable {m : ℕ}

/-- The `k`-th moment of the panel's effective coordinate law: the mixture average of the
per-locus moments of the standardized genotype.

Empirical status: UNTESTED. A mixture average over the panel's own spectrum; no free
parameter beyond the spectrum itself, and nothing fitted. -/
noncomputable def moment (spectrum : MafSpectrum m) (k : ℕ) : ℝ :=
  ∑ j, spectrum.weight j *
    ∑ g : DiploidGenotype,
      (spectrum.model j).genotypeProb g * (spectrum.model j).standardizedGenotype g ^ k

/-- **The panel's fourth moment is the mixture mean of `1 / (2q(1-q))`.**

Per locus the fourth moment is the reciprocal of the genotype variance
(`standardizedGenotype_fourth_moment`), so the panel-level floor-one datum is an average
of reciprocals — which is exactly the functional that two different spectra can match
while differing elsewhere. -/
theorem fourthMoment_eq (spectrum : MafSpectrum m)
    (hpoly : ∀ j, 0 < (spectrum.model j).altFreq ∧ (spectrum.model j).altFreq < 1) :
    spectrum.moment 4 =
      ∑ j, spectrum.weight j / (spectrum.model j).genotypeVariance := by
  have hterm : ∀ j : Fin m,
      spectrum.weight j *
          ∑ g : DiploidGenotype,
            (spectrum.model j).genotypeProb g *
              (spectrum.model j).standardizedGenotype g ^ 4 =
        spectrum.weight j / (spectrum.model j).genotypeVariance := by
    intro j
    rw [standardizedGenotype_fourth_moment (spectrum.model j) (hpoly j).1 (hpoly j).2,
      mul_one_div]
  have hdef : spectrum.moment 4 =
      ∑ j, spectrum.weight j *
        ∑ g : DiploidGenotype,
          (spectrum.model j).genotypeProb g *
            (spectrum.model j).standardizedGenotype g ^ 4 := rfl
  rw [hdef]
  exact Finset.sum_congr rfl (fun j _ => hterm j)

/-- **The first floor-two datum of a panel**: the third moment of the centered square,
`E[u³] = E[x⁶] - 3 E[x⁴] + 2`, where the `+2` uses `E[x²] = 1`, which holds atom by atom
by `standardizedGenotype_second_moment_one` and hence for the mixture.

Empirical status: DERIVED from `MafSpectrum.moment` by the expansion
`(x² - 1)³ = x⁶ - 3x⁴ + 3x² - 1`, which is `centeredSquare_third_moment_eq` at each atom;
no free parameter. -/
noncomputable def centeredSquareThirdMoment (spectrum : MafSpectrum m) : ℝ :=
  spectrum.moment 6 - 3 * spectrum.moment 4 + 2

/-- **Floor one does not determine floor two, for panels.** Two spectra agreeing in the
fourth moment — a floor-one invariant — but differing in the sixth have different
floor-two data.

This is the mechanism in its smallest form. The sixth moment is not a floor-one
invariant: floor one sees `E[x⁴]` and the logarithmic two-jet, and neither pins the
mixture's sixth moment, because a mixture has as many degrees of freedom as it has atoms
while floor one imposes a fixed number of linear constraints on it. -/
theorem centeredSquareThirdMoment_differs_of_sixth (spectrum spectrum' : MafSpectrum m)
    (hfourth : spectrum.moment 4 = spectrum'.moment 4)
    (hsixth : spectrum.moment 6 ≠ spectrum'.moment 6) :
    spectrum.centeredSquareThirdMoment ≠ spectrum'.centeredSquareThirdMoment := by
  intro hcontra
  apply hsixth
  unfold centeredSquareThirdMoment at hcontra
  rw [hfourth] at hcontra
  linarith [hcontra]

end MafSpectrum

/-- **Matching floor one across two panels does not license transporting a calibration.**

`floorOneMatched` is the conjunction a study would check before reusing a calibration:
the two panels agree in the drift, the jet variance, the lattice type and the fourth
moment — every floor-one invariant, locus-weighted. `hfloorTwo` says they differ at floor
two, which by `centeredSquareThirdMoment_differs_of_sixth` needs only a difference in the
sixth moment. The conclusion is that the null laws differ, so a calibration valid for one
panel is not valid for the other.

The transport step itself — that different floor-two data give different nulls — is the
`floorTwo_separates` hypothesis, which is the second floor of the tower doing its work.
It is an argument rather than an assertion, because whether a *particular* pair of spectra
realizes the difference is a numerical question about MAF spectra, not a theorem. -/
theorem floorOne_match_does_not_transport_calibration
    {m : ℕ} {Limit : Type*} (nullLaw : MafSpectrum m → Limit)
    (spectrum spectrum' : MafSpectrum m)
    (_hdrift : ∀ j, hweMellinDrift (spectrum.model j).altFreq =
      hweMellinDrift (spectrum'.model j).altFreq)
    (_hjet : ∀ j, hweMellinJetVariance (spectrum.model j).altFreq =
      hweMellinJetVariance (spectrum'.model j).altFreq)
    (_hfourth : spectrum.moment 4 = spectrum'.moment 4)
    (floorTwo_separates : ∀ s s' : MafSpectrum m,
      s.centeredSquareThirdMoment ≠ s'.centeredSquareThirdMoment → nullLaw s ≠ nullLaw s')
    (hfloorTwo : spectrum.centeredSquareThirdMoment ≠ spectrum'.centeredSquareThirdMoment) :
    nullLaw spectrum ≠ nullLaw spectrum' :=
  floorTwo_separates spectrum spectrum' hfloorTwo

/-!
## 6. Where the whole development now stands

Four negative results, each with its positive complement, and each attached to a
module that was already here:

| result | what fails | what still holds | module |
|---|---|---|---|
| condensation | the Gaussian genotype surrogate above degree `log N / c(q)` | the additive score and its Berry-Esseen certificate | `ScoreDistribution` |
| jet barrier | every cumulant/moment diagnostic of Gaussianity | the trichotomy `(c, v, lattice)` is computable in closed form, for disjoint designs | `EpistasisAndNonAdditivity` |
| overlap spectrum | the Gaussian null for any design whose tested locus-sets share variants, and every calibration justified by a preserved overlap profile | the Gaussian segment for pairwise-disjoint designs, with variance the only free parameter | `EpistaticChaos` |
| local-to-global | bounded-radius coherence audits of summary statistics | coherence established by design | `LocalToGlobalCoherence` |
| hidden cones | any complete catalogue of loading-decay invariants | identifiability when loadings are bounded below | `PCCorrectability` |
| latent collapse | the number of latent GxE mechanisms | boundary/archetypal factorizations | `GeneEnvironmentInterplay` |

The shared shape is worth naming, because it is the same shape each time: a quantity
that is routinely *estimated* turns out not to be a function of the observables at all,
and the honest replacement is a convention plus a theorem about what the convention
buys. That is the programme `Calibrator.Conventions` already states; these five results
extend it from constants to structural quantities.
-/

end Calibrator
