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
`Calibrator.EpistaticChaos.InteractionDesign.VariantDisjoint`, and no property of the
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

/-- **Both gates, for a disjoint design.** A pairwise-disjoint admissible design over
polymorphic loci in linkage equilibrium, tested at an interaction order below the
condensation boundary, passes both: its null is a centered Gaussian with variance in
`[0, 1]` (Theorem D), and its order is subcritical, `c(q) * m < log N`
(`epistatic_order_safe_iff`, i.e. `criticalDegree` via
`maxSafeEpistaticOrder_eq_criticalDegree`).

The two conjuncts answer different questions and neither implies the other.
`maxSafeEpistaticOrder` says the aggregate has not condensed onto a few terms; Theorem D
says the surviving limit is Gaussian at all. Before the overlap results the corpus had
only the first, and a reader could take "subcritical order" to mean "Gaussian null".
The next theorem shows that reading is wrong. -/
theorem disjoint_design_gaussian_null_below_condensation
    {ι : Type*} [Fintype ι] {n : ℕ} {Limit : Type*}
    (Sp : GenotypeChaosLimits n ι Limit) (design : GenotypeDesign n ι)
    (hadmissible : Sp.isAdmissible design) (hpolymorphic : design.Polymorphic)
    (hequilibrium : design.InLinkageEquilibrium) (hdisjoint : design.VariantDisjoint)
    {N q m : ℝ} (hdrift : 0 < hweMellinDrift q)
    (hsafe : m < maxSafeEpistaticOrder N q) :
    (∃ s2 : ℝ, 0 ≤ s2 ∧ s2 ≤ 1 ∧ Sp.IsCenteredGaussian (Sp.limitLaw design) s2) ∧
      hweMellinDrift q * m < Real.log N :=
  ⟨Sp.gaussian_null_licensed_of_disjoint design hadmissible hpolymorphic hequilibrium
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
