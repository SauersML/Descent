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
## 5f. The Vertex-Weight Law: the observable content of a genotype coding is complete

The results above say what a *design* can hide. The Vertex-Weight Law says what a
*coding* can show, and for this corpus it is a completeness theorem about quantities
that are already computed here.

In the diagram expansion of any truncated joint cumulant of an admissible design, the
coordinate law enters in exactly three places: window factors, whose admissible limits
depend on the Mellin two-jet `(c, v)` and the arithmetic type of `log x²` alone; even
vertex weights at shared-variable multiplicity `2j`, which are polynomials in the first
`j` cumulants of `x²`; and odd vertex weights — the sign couplings — which vanish
identically exactly when the law is symmetric. Nothing else about the law appears
anywhere in any diagram, at any degree.

So the complete list of coordinate-law invariants that any admissible design can
transmit is

> two-jet, arithmetic type, symmetry, cumulant sequence of `x²`

and this corpus has already computed the first three for the standardized genotype:
`hweMellinDrift` is `c`, `hweMellinJetVariance` is `v`, `hweLatticeCondition` is the
arithmetic type, and `Calibrator.EpistaticChaos.standardizedGenotype_symmetric_iff`
settles symmetry — a single point, `q = 1/2`. The theorem below says those objects are
not a convenient summary of a genotype coding. They are all of it.
-/

/-- **The complete observable content of a coordinate law**, per the Vertex-Weight Law:
the Mellin two-jet, the arithmetic type of `log x²`, the symmetry verdict, and the
cumulant sequence of `x²`. -/
structure GenotypeObservableContent where
  /-- The size-biased drift `c = E[x² log x²]`. -/
  drift : ℝ
  /-- The size-biased increment variance `v`. -/
  jetVariance : ℝ
  /-- The arithmetic type: whether `log x²` is supported on an arithmetic progression. -/
  IsLattice : Prop
  /-- Whether the coding admits a value-negating relabelling. -/
  IsSignSymmetric : Prop
  /-- The cumulant sequence of `x²`, which supplies the even vertex weights. -/
  squareCumulant : ℕ → ℝ

/-- The observable content of a Hardy-Weinberg locus at allele frequency `q`, assembled
from the quantities this corpus already computes. The square-cumulant sequence is
supplied as a parameter because it is a sequence rather than a closed form; every other
component is a function of `q` already proved here.

Empirical status: DERIVED from `hweMellinDrift`, `hweMellinJetVariance` and
`hweLatticeCondition`, each of which is derived elsewhere in the corpus; no free
parameter beyond the supplied cumulant sequence, and nothing fitted. -/
def hweObservableContent (squareCumulant : ℝ → ℕ → ℝ) (q : ℝ) : GenotypeObservableContent where
  drift := hweMellinDrift q
  jetVariance := hweMellinJetVariance q
  IsLattice := hweLatticeCondition q
  IsSignSymmetric := q = 1 / 2
  squareCumulant := squareCumulant q

/-- **The observable content is built from the corpus's own quantities**, component by
component. This is the over-determination guard for the completeness claim: if anyone
changes what `hweMellinDrift` or `hweMellinJetVariance` or `hweLatticeCondition` means,
this stops compiling rather than drifting. -/
theorem hweObservableContent_components (squareCumulant : ℝ → ℕ → ℝ) (q : ℝ) :
    (hweObservableContent squareCumulant q).drift = hweMellinDrift q ∧
      (hweObservableContent squareCumulant q).jetVariance = hweMellinJetVariance q ∧
      (hweObservableContent squareCumulant q).IsLattice = hweLatticeCondition q ∧
      (hweObservableContent squareCumulant q).IsSignSymmetric = (q = 1 / 2) :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- **The symmetry component is the corpus's proved characterization.** The
`IsSignSymmetric` slot of the observable content holds exactly when the standardized
genotype admits a value-negating relabelling, which
`Calibrator.EpistaticChaos.standardizedGenotype_symmetric_iff` proves happens at
`q = 1/2` and nowhere else in the polymorphic range.

So the third of the four observable invariants is not a free slot to be filled later: it
is already decided for genotypes, and it is decided negatively almost everywhere. -/
theorem hweObservableContent_symmetry (squareCumulant : ℝ → ℕ → ℝ)
    (h : HardyWeinbergModel) (hq0 : 0 < h.altFreq) (hq1 : h.altFreq < 1) :
    (hweObservableContent squareCumulant h.altFreq).IsSignSymmetric ↔
      (∃ coding : SymmetricCoding DiploidGenotype,
        (∀ g, coding.weight g = h.genotypeProb g) ∧
        (∀ g, coding.value g = h.standardizedGenotype g)) := by
  have hcomponent : (hweObservableContent squareCumulant h.altFreq).IsSignSymmetric =
      (h.altFreq = 1 / 2) := rfl
  rw [hcomponent]
  exact (standardizedGenotype_symmetric_iff h hq0 hq1).symm

/-- **The one frequency where symmetry is available is the one where the second
observable dies.** If the symmetry component holds then the jet-variance component is
zero, by `hweMellinJetVariance_half`. Two of the four invariants collapse together, so a
genotype coding cannot be both sign-symmetric and Mellin-nondegenerate — the dichotomy
of `no_signSymmetric_nondegenerate_locus`, now read off the observable content. -/
theorem hweObservableContent_symmetric_jetVariance_zero (squareCumulant : ℝ → ℕ → ℝ)
    (q : ℝ) (hsymmetric : (hweObservableContent squareCumulant q).IsSignSymmetric) :
    (hweObservableContent squareCumulant q).jetVariance = 0 := by
  have hcomponent : (hweObservableContent squareCumulant q).IsSignSymmetric = (q = 1 / 2) := rfl
  rw [hcomponent] at hsymmetric
  have hjet : (hweObservableContent squareCumulant q).jetVariance = hweMellinJetVariance q := rfl
  rw [hjet, hsymmetric]
  exact hweMellinJetVariance_half

/-- Re-model a design: the same tested locus-sets, coefficients and joint law, at a
different allele-frequency family. This is what varying the coordinate law while holding
the design fixed means, and it is the comparison the Vertex-Weight Law is about.

Empirical status: UNTESTED. A field update on a design; no modelling content and no free
parameter. -/
def GenotypeDesign.reModel {ι : Type*} {n : ℕ} (design : GenotypeDesign n ι)
    (model : Fin n → HardyWeinbergModel) : GenotypeDesign n ι :=
  { design with model := model }

/-- The Vertex-Weight Law over a genotype panel, carried as a field.

`limitLaw` is the limit of a design's statistic. The field says the limit depends on the
allele-frequency family only through the observable content of each locus — the two-jet,
the arithmetic type, the symmetry verdict, and the square-cumulant sequence — and
through nothing else. -/
structure VertexWeightLaw (n : ℕ) (ι : Type*) (Limit : Type*) where
  /-- Minimum interaction order diverging, influence vanishing, unit variance. -/
  isAdmissible : GenotypeDesign n ι → Prop
  /-- The limit law of a design's statistic. -/
  limitLaw : GenotypeDesign n ι → Limit
  /-- The cumulant sequence of the squared standardized genotype, as a function of the
  allele frequency. -/
  squareCumulant : ℝ → ℕ → ℝ
  /-- **The Vertex-Weight Law (analytic input).** Two allele-frequency families with the
  same per-locus observable content give the same limit, for every design. The proof is
  the diagram expansion: window factors see only the two-jet and the arithmetic type,
  even vertex weights only the square cumulants, odd vertex weights only the symmetry
  verdict, and there is no fourth place for the law to enter. -/
  vertex_weight : ∀ (design : GenotypeDesign n ι) (model model' : Fin n → HardyWeinbergModel),
    isAdmissible (design.reModel model) → isAdmissible (design.reModel model') →
    (∀ i : Fin n, hweObservableContent squareCumulant (model i).altFreq =
      hweObservableContent squareCumulant (model' i).altFreq) →
    limitLaw (design.reModel model) = limitLaw (design.reModel model')

namespace VertexWeightLaw

variable {n : ℕ} {ι : Type*} {Limit : Type*} (VW : VertexWeightLaw n ι Limit)

/-- **Observability completeness for a genotype coding.** Any experiment reporting a
function of a design's limit is a function of the observable content alone: two
allele-frequency families agreeing in the two-jet, the arithmetic type, the symmetry
verdict and the square cumulants at every locus are indistinguishable by every admissible
design, at every interaction order, through every diagram.

Nothing outside that list is observable. In particular no diagnostic, however elaborate,
recovers any property of a genotype coding that is not a function of those four. -/
theorem experiment_factors_through_observable_content
    {Report : Type*} (experiment : Limit → Report)
    (design : GenotypeDesign n ι) (model model' : Fin n → HardyWeinbergModel)
    (hadmissible : VW.isAdmissible (design.reModel model))
    (hadmissible' : VW.isAdmissible (design.reModel model'))
    (hcontent : ∀ i : Fin n,
      hweObservableContent VW.squareCumulant (model i).altFreq =
        hweObservableContent VW.squareCumulant (model' i).altFreq) :
    experiment (VW.limitLaw (design.reModel model)) =
      experiment (VW.limitLaw (design.reModel model')) := by
  rw [VW.vertex_weight design model model' hadmissible hadmissible' hcontent]

/-- **The corpus's computed quantities are the complete observable summary.** Stated in
the form a reader can act on: if two panels agree locus by locus in `hweMellinDrift`,
`hweMellinJetVariance`, `hweLatticeCondition`, the symmetry point and the square
cumulants, then no admissible design distinguishes them.

Every hypothesis here names a quantity this corpus already computes in closed form,
which is what makes the completeness claim checkable rather than decorative. -/
theorem indistinguishable_of_matching_computed_quantities
    (design : GenotypeDesign n ι) (model model' : Fin n → HardyWeinbergModel)
    (hadmissible : VW.isAdmissible (design.reModel model))
    (hadmissible' : VW.isAdmissible (design.reModel model'))
    (hdrift : ∀ i : Fin n, hweMellinDrift (model i).altFreq =
      hweMellinDrift (model' i).altFreq)
    (hjet : ∀ i : Fin n, hweMellinJetVariance (model i).altFreq =
      hweMellinJetVariance (model' i).altFreq)
    (hlattice : ∀ i : Fin n, hweLatticeCondition (model i).altFreq =
      hweLatticeCondition (model' i).altFreq)
    (hsymmetry : ∀ i : Fin n, ((model i).altFreq = 1 / 2) = ((model' i).altFreq = 1 / 2))
    (hcumulant : ∀ i : Fin n, VW.squareCumulant (model i).altFreq =
      VW.squareCumulant (model' i).altFreq) :
    VW.limitLaw (design.reModel model) = VW.limitLaw (design.reModel model') := by
  refine VW.vertex_weight design model model' hadmissible hadmissible' (fun i => ?_)
  unfold hweObservableContent
  rw [hdrift i, hjet i, hlattice i, hsymmetry i, hcumulant i]

end VertexWeightLaw

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
