/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Calibrator.PolygenicSpectroscopy
import Calibrator.LatentMechanismCollapse
import Calibrator.Conventions

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
3. The number-of-PCs and GxE-mechanism-count readings, stated as readings. The three
   theorems that once carried them here were re-exports of imported results under
   genetics names, with no instance supplied, and are removed; see sections 4-5.
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
theorem standardizedSquare_scale_invariant (c V lam : ℝ) (hlam : lam ≠ 0) :
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
strictly below the condensation boundary, `1 < maxSafeEpistaticOrder N q`.

That is an inequality between two real numbers; validity of the Gaussian surrogate at
degree one is the Berry-Esseen apparatus of `Calibrator.Probability`, not this. Genome-wide
scores clear the boundary by many orders of magnitude, and the simulation reported at
`maxSafeEpistaticOrder` confirms genotype and surrogate score laws are indistinguishable at
`m = 1`. The condensation theory does not weaken the additive PGS apparatus; it bounds the
degree to which that apparatus may be extrapolated to interaction models. -/
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
repaired exactly by rescaling. The Mellin triple is rescaling-invariant
(`standardizedSquare_scale_invariant`), and the inflation factor at the hard-call lattice
point exceeds one (`hardCall_intensity_inflated`).

**The statement is the conjunction of those two facts and no more.** It does not prove
that no rescaling makes the hard-call intensity match a nonlattice surrogate's: that would
need the inflation factor to *be* an intensity ratio, which is the unproved local-limit
step of `Calibrator.JetBarrier`. Read it as: rescaling cannot move the quantity the lattice
mechanism is stated in terms of. -/
theorem imputation_rescaling_cannot_repair_lattice (lam : ℝ) (hlam : lam ≠ 0) :
    1 < latticeInflation hardCallLatticeSpan ∧
      ∀ c V : ℝ, V ≠ 0 → (lam * c) ^ 2 / (lam ^ 2 * V) = c ^ 2 / V :=
  ⟨hardCall_intensity_inflated, fun c V _hV ↦ standardizedSquare_scale_invariant c V lam hlam⟩

/-!
## 4-5. Two abstract results, and why they are not re-exported here

`HiddenConeAmbiguity.catalogue_induces_reduction`,
`HiddenConeAmbiguity.rigidity_of_boundedBelowAbove` and
`LatentMechanismCollapse.minimal_latent_dimension_is_constant` are what a caller should
use directly. Re-exporting them under genetics names would assert a domain applicability
no instance here establishes: nothing is instantiated, `Family` is never given the type of
context-specific genotype-phenotype kernels, and `screeLabel` is never given an
eigenvalue-gap rule, so a reader could not tell a re-export from a derivation.

The genetics readings are what this corpus believes, and they are stated here as readings
rather than as theorems. If a complete scree-type invariant of a
loading-decay profile existed it would have to separate profiles with identical complete
second-order observables, so the number of principal components to retain is a convention
in the sense of `Calibrator.Conventions`; `Calibrator.PCCorrectability` answers the
different question of what correction achieves *given* one. Where the ancestry loadings
are bounded below the latent coordinates are recoverable and the convention is forced.
And if every non-constant family of context-specific kernels admits a dimension-one
factorization, then minimal latent dimension is constant and so measures nothing about
how many biological mechanisms generated the data; the repaired question is the
boundary (Choquet-extreme) factorization, in genetics the archetypal-analysis
requirement that mechanisms be extremal profiles rather than interior blends.

Turning any of these into a theorem *about genotypes* means supplying the instance.
None is supplied here.
-/

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
  refine ⟨fun coding hweight hvalue ↦ ?_, fun hhalf ↦ ?_⟩
  · exact hwe_symmetricCoding_forces_half h hq0 hq1 coding hweight hvalue
  · rw [hhalf]
    exact hweMellinJetVariance_half

/-!
## 5c. Set-based null limits

The former bridge from genotype-design algebra to Gaussian/maximal-spectrum limits depended
entirely on theorem-valued `GenotypeChaosLimits` fields.  Those bridge theorems are removed.
The directly proved drift, safe-order, overlap, and finite cycle computations remain, but
none is advertised as a null-limit theorem without its analytic proof.
-/

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
cumulants of x²}` overstates what is observable, and this file asserts no such list. The
obstruction is the hub-energy divergence already formalized here. An `ObservableTower`
record carrying that obstruction as a field is absent on purpose, because such a record
takes the Vertex-Weight Law and the exposure correction as fields too. This paragraph is
therefore a note, and nothing in the file enforces it.

**A later correction, recorded here because this section is where a reader meets the
list.** §5i's rigidity theorem shows the floor-one channels are reconstructible from four
data — symmetry, `E[x⁴]`, and the odd parts of floors two and three — hence not a *minimal*
list, **at the Gaussian fiber**. Off that fiber the four determine nothing and the
reconstruction fails, and no polymorphic genotype is on it, so for genotype data
`hweMellinDrift` and `hweMellinJetVariance` stay independently informative. What is demoted
is their claim to minimality for a general coordinate law; what is minimal there includes
the odd part of the squared law, which no moment list mentions.

**The replacement is a recursion.** The conditional-variance array of an admissible
design is itself a design — multilinear in the centered squares, with coordinate law the
law of `x²` — so the observable algebra is self-similar:

> `OA(ν) = { two-jet(ν), arithmetic type(ν), symmetry(ν) } ∪ OA(law of x²)`,

to finite depth. The naive list is the shadow of the first two floors: `κ₂(x²)` is
exposed precisely because it is the *variance* of level two, which is what a second floor
reads. Whether the tower has a genuine second floor or truncates at depth one is **open
upstream** — the reachability computation that decides it is outstanding. The recursion
itself is not formalized in this file: there is no depth parameter and no truncation
hypothesis, only the explicit floor-one and panel-mixture calculations below.

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
  have hvar : 0 < h.genotypeVariance := h.genotypeVariance_pos hq0 hq1
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

**Read the scope of this theorem carefully.** It is about the *uncentered* square `x²`, which is
non-negative and therefore trivially never
symmetric. It is **not** about the tower's floor-two coordinate, which is the *centered*
square `u = (x² - 1)/σ₁`, and it does not settle the floor-two symmetry question.

That question has the opposite answer at the balanced locus. At `q = 1/2` the standardized
values are `-√2, 0, √2` with probabilities `1/4, 1/2, 1/4`, so `x²` is `2, 0, 2` and
`σ₁² = E[x⁴] - 1 = 1`, giving `u = +1, -1, +1` — the Rademacher law, which is symmetric
(`Calibrator.EpistaticChaos.centeredSquare_rademacher_at_half`). Away from `1/2` the
floor-two odd part is nonzero and grows as the variant gets rarer
(`centeredSquare_third_moment_zero_iff_balanced`).

So the balanced locus is symmetric at *both* floors, a sharper degeneracy than either the
level-one statement or a naive reading of this theorem suggests. The distinction between
`x²` and `u` is exactly the trap recorded at
`Calibrator.EpistaticChaos.uncentered_square_log_additive`: the uncentered square recycles
level-one data and looks like a new floor. This theorem is a true statement about the
uncentered object, and inferring the floor-two channel from it is the mistake the trap
predicts. -/
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
  rw [sum_over_genotypes] at hzero
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

**The constant is CONFIRMED and the gloss around it was BACKWARDS.**

Simulated at `n = 8000`, 2500 replicates per cell, 36 MAF points, each statistic calibrated
against its own null at its own frequency so size is exactly `0.05` everywhere. For the
**latent-locus** channel — excess kurtosis of `y` with the locus unobserved — power falls to
nominal `0.050` at MAF `0.210`, and the bias-corrected zero-crossing of the measured fourth
cumulant is `q = 0.21149 ± 0.00068` against `(3-√3)/6 = 0.21132`: **agreement within 0.25
standard errors.** A control arm with both loci measured held power `0.981`–`0.997` at all 36
points including `q*`, so the dip is interpretable.

Two corrections follow.

**The blind region is a wide asymmetric window, not a point.** Power is below `0.10` across
MAF `[0.19, 0.26]`, below `0.20` across `[0.165, 0.29]`, below `0.30` across `[0.155, 0.35]`.
Its half-width narrows only as `n^{-1/4}`, and it never closes on the common side — maximum
power above MAF `0.30` is `0.398`, for a locus explaining 30% of variance.

**The claim that "fourth-cumulant interaction tests go blind here" is refuted, and the truth
is its opposite.** Built on a *measured* locus, the natural fourth-order interaction test
`cum(y,y,x,x)` has power `0.47`–`0.80`, **flat, with no dip** — higher at MAF `0.21` (`0.712`)
than at `0.05` (`0.554`), with its null mean matching the closed form to three digits at every
point. What happens at `q*` is that this test, calibrated against the Gaussian surrogate, has
type-I error `1.000` across almost the whole spectrum and `0.051` only at MAF `0.21`. **`q*`
is the unique frequency at which a Gaussian-calibrated fourth-order interaction test is
valid**, not one at which it is blind.

So the blindness is real for the latent-locus channel and does **not** transfer to interaction
tests on genotyped loci. What needed narrowing was this gloss, not the constant.

Empirical status: **VALIDATED** (`proofs/validation/empirical/blind_maf/`). Scope caveat: HWE,
unlinked
loci, no LD or structure, and not every statistic that could be called fourth-cumulant-based
was constructed. -/
noncomputable def gaussianKurtosisMaf : ℝ := (3 - Real.sqrt 3) / 6

/-- Reference evaluation in closed surd form. -/
theorem gaussianKurtosisMaf_at_reference_point :
    gaussianKurtosisMaf = (3 - Real.sqrt 3) / 6 := rfl


/-- **The Gaussian kurtosis frequency is below a quarter.** A one-sided bound on a constant built
from a surd does not exclude the sign-flipped constant, which here is `(3 + √3)/6 > 3/4`. This
bound does. -/
theorem gaussianKurtosisMaf_lt_quarter : gaussianKurtosisMaf < 1 / 4 := by
  have h3 : (3 / 2 : ℝ) < Real.sqrt 3 := by
    have h : Real.sqrt ((3 / 2 : ℝ) ^ 2) < Real.sqrt 3 :=
      Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    rwa [Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 3 / 2)] at h
  unfold gaussianKurtosisMaf
  linarith

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
*coordinate* from a Gaussian one.

**Do not extend that to interaction tests; the extension was measured and is refuted.**
An interaction statistic drawing its power from fourth-cumulant separation does *not* lose
signal at `q*`, which is the natural guess. Simulation says the opposite: on a
measured locus the natural fourth-order test `cum(y,y,x,x)` holds power `0.47`–`0.80`
flat, *higher* at MAF `0.21` (`0.712`) than at `0.05` (`0.554`), with no dip. What
happens at `q*` is that the same test, calibrated against the Gaussian surrogate, has
type-I error `1.000` almost everywhere and `0.051` only there — `q*` is the one
frequency at which such a test is **valid**. The blindness is real for the latent-locus
channel and does not transfer. See the MEASURED block at `gaussianKurtosisMaf`.

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
The recursion above it is not formalized — a record for it would have to take the
Vertex-Weight Law as a field — so what follows is floor one only.
-/

/-- The channels available at one floor of the observable tower. -/
structure LevelChannels where
  /-- The size-biased drift `c = E[x² log x²]` of that floor's coordinate. -/
  drift : ℝ
  /-- The size-biased increment variance `v` of that floor's coordinate. -/
  jetVariance : ℝ
  /-- Whether that floor's `log x²` is supported on an arithmetic progression. -/
  isLattice : Bool
  /-- Whether that floor's coordinate admits a value-negating relabelling. -/
  isSignSymmetric : Bool

/-- Floor one of the tower for a Hardy-Weinberg locus, assembled from quantities this
corpus computes in closed form.

Empirical status: DERIVED from `hweMellinDrift`, `hweMellinJetVariance` and
`hweLatticeCondition`, each derived elsewhere in the corpus, together with the symmetry
characterization `standardizedGenotype_symmetric_iff`; no free parameter and nothing
fitted. -/
noncomputable def hweLevelOne (q : ℝ) : LevelChannels := by
  classical
  exact
    { drift := hweMellinDrift q
      jetVariance := hweMellinJetVariance q
      isLattice := decide (hweLatticeCondition q)
      isSignSymmetric := decide (q = 1 / 2) }

/-- **Floor one is built from the corpus's own quantities**, component by component: the
over-determination guard for the completeness claim. If anyone changes what
`hweMellinDrift`, `hweMellinJetVariance` or `hweLatticeCondition` means, this stops
compiling rather than drifting. -/
theorem hweLevelOne_components (q : ℝ) :
    (hweLevelOne q).drift = hweMellinDrift q ∧
      (hweLevelOne q).jetVariance = hweMellinJetVariance q ∧
      ((hweLevelOne q).isLattice = true ↔ hweLatticeCondition q) ∧
      ((hweLevelOne q).isSignSymmetric = true ↔ q = 1 / 2) := by
  classical
  refine ⟨rfl, rfl, ?_, ?_⟩
  · change decide (hweLatticeCondition q) = true ↔ hweLatticeCondition q
    exact ⟨of_decide_eq_true, decide_eq_true⟩
  · change decide (q = 1 / 2) = true ↔ q = 1 / 2
    exact ⟨of_decide_eq_true, decide_eq_true⟩

/-- **The symmetry slot of floor one is the corpus's proved characterization**, so it is
not a slot awaiting work: it is decided, and decided negatively away from `q = 1/2`. -/
theorem hweLevelOne_symmetry (h : HardyWeinbergModel)
    (hq0 : 0 < h.altFreq) (hq1 : h.altFreq < 1) :
    (hweLevelOne h.altFreq).isSignSymmetric = true ↔
      (∃ coding : SymmetricCoding DiploidGenotype,
        (∀ g, coding.weight g = h.genotypeProb g) ∧
        (∀ g, coding.value g = h.standardizedGenotype g)) := by
  change decide (h.altFreq = 1 / 2) = true ↔ _
  constructor
  · intro hdecide
    exact (standardizedGenotype_symmetric_iff h hq0 hq1).mpr
      (of_decide_eq_true hdecide)
  · intro hcoding
    exact decide_eq_true
      ((standardizedGenotype_symmetric_iff h hq0 hq1).mp hcoding)

/-- Where floor one is symmetric its jet variance vanishes: two of its channels collapse
together, which is `no_signSymmetric_nondegenerate_locus` read off the tower. -/
theorem hweLevelOne_symmetric_jetVariance_zero (q : ℝ)
    (hsymmetric : (hweLevelOne q).isSignSymmetric = true) :
    (hweLevelOne q).jetVariance = 0 := by
  have hcomponent : q = 1 / 2 :=
    of_decide_eq_true hsymmetric
  have hjet : (hweLevelOne q).jetVariance = hweMellinJetVariance q := rfl
  rw [hjet, hcomponent]
  exact hweMellinJetVariance_half

/-- Re-model a design: the same tested locus-sets, coefficients and joint law, at a
different allele-frequency family. This is what varying the coordinate law while holding
the design fixed means.
parameter.

Empirical status: UNTESTED. A field update on a design; no modelling content and no free -/
def GenotypeDesign.reModel {ι : Type*} {n : ℕ} (design : GenotypeDesign n ι)
    (model : Fin n → HardyWeinbergModel) : GenotypeDesign n ι :=
  { design with model := model }

/-- **What "holding the design fixed" means**, stated rather than left to the field update:
re-modelling moves the coordinate law and leaves the combinatorics alone, so the
interaction order of every tested set is unchanged. Without this, `reModel` is a record
update no statement distinguishes from an arbitrary design. -/
@[simp] theorem GenotypeDesign.reModel_interactionOrder {ι : Type*} {n : ℕ}
    (design : GenotypeDesign n ι) (model : Fin n → HardyWeinbergModel) (s : ι) :
    (design.reModel model).interactionOrder s = design.interactionOrder s := rfl

/-! No observable-tower record is exported: accepting the Vertex-Weight Law and the
exposure correction as fields would assume unproved analytic claims, and the explicit
panel-mixture calculations below do not depend on them. -/

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
frequency-based filtering. The operational reading — that matching floor-one invariants
across two panels does not license transporting a calibration between them — is what the
mechanism suggests. What is proved below is one step of it: the floor-two datum of a panel
is the across-locus spread of `1/(2q(1-q))`, and two spectra can match at floor one and
differ there. The step from a floor-two difference to a difference in null laws is not
available in this corpus.
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

/-- **The class is inhabited.**  A theorem quantified over an uninhabited structure is
true and empty: kernel-checked, clean axiom report, no content.  This is the witness that
makes the theorems below statements about something. -/
noncomputable def MafSpectrum.witness (m : ℕ) : MafSpectrum (m + 1) where
  model := fun _ ↦ HardyWeinbergModel.witness
  weight := fun j ↦ if j = 0 then 1 else 0
  weight_nonneg := fun j ↦ by split <;> norm_num
  weight_sum := by simp

namespace MafSpectrum

variable {m : ℕ}

/-- The `k`-th moment of the panel's effective coordinate law: the mixture average of the
per-locus moments of the standardized genotype.
parameter beyond the spectrum itself, and nothing fitted.

Empirical status: UNTESTED. A mixture average over the panel's own spectrum; no free -/
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
    rw [standardizedGenotype_fourth_moment (spectrum.model j) (hpoly j).1 (hpoly j).2, mul_one_div]
  have hdef : spectrum.moment 4 =
      ∑ j, spectrum.weight j *
        ∑ g : DiploidGenotype,
          (spectrum.model j).genotypeProb g *
            (spectrum.model j).standardizedGenotype g ^ 4 := rfl
  rw [hdef]
  exact Finset.sum_congr rfl (fun j _ ↦ hterm j)

/-- **The first floor-two datum of a panel**: the third moment of the centered square,
`E[u³] = E[x⁶] - 3 E[x⁴] + 2`, where the `+2` uses `E[x²] = 1`, which holds atom by atom
by `standardizedGenotype_second_moment_one` and hence for the mixture.

Empirical status: DERIVED from `MafSpectrum.moment` by the expansion
`(x² - 1)³ = x⁶ - 3x⁴ + 3x² - 1`, which is `centeredSquare_third_moment_eq` at each atom;
no free parameter. -/
noncomputable def centeredSquareThirdMoment (spectrum : MafSpectrum m) : ℝ :=
  spectrum.moment 6 - 3 * spectrum.moment 4 + 2

/-- **The across-locus dispersion of the fourth moment**: `∑ w_j (1/V_j)² - (∑ w_j /V_j)²`,
the variance of the per-locus `E[x⁴] = 1/(2q(1-q))` across the panel.

This is the panel's floor-two datum. Floor one sees the *mean* of `1/(2q(1-q))`; floor two
sees its spread. Two panels with the same mean and different spread agree at floor one and
differ at floor two.

Empirical status: UNTESTED. A dispersion computed from the panel's own allele-frequency
spectrum; no free parameter and nothing fitted. It is directly computable from any real
panel's MAF distribution without simulation. -/
noncomputable def fourthMomentDispersion (spectrum : MafSpectrum m) : ℝ :=
  (∑ j, spectrum.weight j * (1 / (spectrum.model j).genotypeVariance) ^ 2) -
    (spectrum.moment 4) ^ 2

/-- **The panel's sixth moment is floor-one data plus the dispersion.**

Per locus `E[x⁶] = (E[x⁴])² + 10 E[x⁴] - 20` exactly
(`standardizedGenotype_sixth_moment`), so for a single locus floor two is a *function* of
floor one. For a mixture the average of the quadratic is not the quadratic of the average,
and the whole gap is `fourthMomentDispersion`:

`M₆ = (M₄² + 10 M₄ - 20) + dispersion`.

So the panel effect is exactly the across-locus spread of `1/(2q(1-q))`, and two spectra
matching in floor one differ at floor two precisely when their MAF spectra differ in that
spread. This is what makes the claim checkable on real panels rather than only in
principle. -/
theorem sixthMoment_eq_floorOne_plus_dispersion (spectrum : MafSpectrum m)
    (hpoly : ∀ j, 0 < (spectrum.model j).altFreq ∧ (spectrum.model j).altFreq < 1) :
    spectrum.moment 6 =
      (spectrum.moment 4) ^ 2 + 10 * spectrum.moment 4 - 20 +
        spectrum.fourthMomentDispersion := by
  have hterm : ∀ j : Fin m,
      spectrum.weight j *
          ∑ g : DiploidGenotype,
            (spectrum.model j).genotypeProb g *
              (spectrum.model j).standardizedGenotype g ^ 6 =
        spectrum.weight j * (1 / (spectrum.model j).genotypeVariance) ^ 2 +
          (10 * (spectrum.weight j * (1 / (spectrum.model j).genotypeVariance)) -
            20 * spectrum.weight j) := by
    intro j
    rw [standardizedGenotype_sixth_moment (spectrum.model j) (hpoly j).1 (hpoly j).2]
    ring
  have hfour : ∀ j : Fin m,
      spectrum.weight j * (1 / (spectrum.model j).genotypeVariance) =
        spectrum.weight j *
          ∑ g : DiploidGenotype,
            (spectrum.model j).genotypeProb g *
              (spectrum.model j).standardizedGenotype g ^ 4 := by
    intro j
    rw [standardizedGenotype_fourth_moment (spectrum.model j) (hpoly j).1 (hpoly j).2]
  have hdef6 : spectrum.moment 6 =
      ∑ j, spectrum.weight j *
        ∑ g : DiploidGenotype,
          (spectrum.model j).genotypeProb g *
            (spectrum.model j).standardizedGenotype g ^ 6 := rfl
  have hdef4 : spectrum.moment 4 =
      ∑ j, spectrum.weight j *
        ∑ g : DiploidGenotype,
          (spectrum.model j).genotypeProb g *
            (spectrum.model j).standardizedGenotype g ^ 4 := rfl
  have hsplit : spectrum.moment 6 =
      (∑ j, spectrum.weight j * (1 / (spectrum.model j).genotypeVariance) ^ 2) +
        (10 * spectrum.moment 4 - 20) := by
    rw [hdef6]
    simp_rw [hterm]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      ← Finset.mul_sum, spectrum.weight_sum, mul_one]
    congr 2
    rw [hdef4]
    -- `congr 2` stops above the `10 *`, so the goal here is `10 * X = 10 * Y` and not
    -- `X = Y`; handing it the bare `Finset.sum_congr` gives a Type mismatch whose printed
    -- types differ only by that factor, which is easy to misread as a summand mismatch.
    -- Descend the extra level explicitly. Keeping alternative proof branches here hid two
    -- unreachable tactics from the linter; the goal shape is part of the checked theorem,
    -- so the exact congruence is the stronger and more maintainable proof.
    exact congrArg (fun s ↦ 10 * s) (Finset.sum_congr rfl (fun j _ ↦ hfour j))
  rw [hsplit]
  unfold fourthMomentDispersion
  ring

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

/-! The proved content of this section is `centeredSquareThirdMoment_differs_of_sixth`: two
spectra agreeing in the fourth moment and differing in the sixth differ in the floor-two
datum. Turning that into a statement about calibrations needs a theorem sending floor-two
data to null laws, which this corpus does not have. -/

/-!
## 5h. The squaring flow, its scale sequence, and why the tower is unreachable

Each floor of the tower is reached by the **normalized squaring flow**

> `X_{k+1} = (X_k² - 1) / σ_k`,  `σ_k² = Var(X_k²)`,

which centers the square and rescales it to unit variance. The sequence `σ_k` is the
object that decides whether the tower's floors can be separated, and for the Gaussian it
is not bounded — it grows doubly exponentially.

The first two values are computed here outright, from the standard normal moments
`1, 3, 15, 105` and nothing else:

* `σ₁² = E[X⁴] - 1 = 2`, so `σ₁ = √2 = 1.41421…`;
* the next floor's fourth moment is `E[(X²-1)⁴]/σ₁⁴ = (105 - 60 + 18 - 4 + 1)/4 = 15`,
  so `σ₂² = 15 - 1 = 14` and `σ₂ = √14 = 3.74166…`.

Numerically the sequence continues `19.07, 294.1, 72756, 4.699·10⁹, 2.005·10¹⁹`.

**All seven figures reproduce exactly; the description attached to them did not.** The
claim was that the logarithm doubles at each floor to four significant figures, so that
`σ_k ≈ exp(c · 2^k)` with a clean constant. The measured ratios
`log σ_{k+1} / log σ_k` are

  `3.807, 2.234, 1.928, 1.970, 1.989, 1.996`,

which approach `2` from both sides and are nowhere near `2` at the bottom of the tower —
the first ratio is off by `90%`. So the doubling is an asymptotic tendency, not a
per-floor identity, and the low floors are exactly the ones the reachability argument of
this section is about. The growth is doubly exponential in the limit; the constant `c` is
not pinned by these seven terms, and nothing here proves the limit exists. It is carried
as an unproved asymptotic claim with the two closed forms above as its only anchor.

### What the divergence does, and it is a rigidity mechanism rather than a defect

An escape argument for tower constructions needs the flow to be *expanding* beyond some
fixed threshold, so that points past it run away and the reflection constraints are
locally finite. That needs a bounded `σ`. With `σ_k` diverging the opposite happens: the
map `x ↦ (x² - 1)/σ` is a **contraction** on any fixed region once `σ` exceeds twice its
radius (`squaringFlow_lipschitz`), and it maps that region into itself
(`squaringFlow_maps_ball_into_itself`). The positive fixed point
`x* = (σ + √(σ² + 4))/2` is at least `σ` (`scale_le_squaringFixedPoint`) and so diverges
with it, swallowing every bounded set. So no fixed threshold escapes, the escape region is
asymptotically empty, and the constraint cascade is not locally finite — which is the
branch on which determinacy is plausible.

### The biology: the tower is finite in practice, with a brutal cutoff

Floor `k`'s datum is a variance-normalized quantity whose natural scale is `σ_k`, so
estimating it from data needs a sample size growing like `σ_k²`, hence like
`exp(2c · 2^k)`. With `σ₃ ≈ 19`, `σ₄ ≈ 294`, `σ₅ ≈ 7.3·10⁴`, the implied sample sizes are
of order `4·10²`, `9·10⁴`, `5·10⁹`. **The observable algebra is infinite in principle and
finite in practice, truncated at about floor three no matter how large the study.**

For genotypes the first floor's scale is not the Gaussian's. It is `σ₁² = 1/V - 1` with
`V = 2q(1-q)` (`hweFloorOneScaleSq_eq`), about `49` at MAF `0.01` and `1` at MAF `0.5`, so
rare variants start the tower further from the Gaussian and are harder to read at every
floor.

It equals the Gaussian's `2` at `gaussianKurtosisMaf`, the same `MAF = 0.2113…` at which
the hub channel goes blind — necessarily, not coincidentally: `σ₁² = E[x⁴] - 1`
identically, so the two conditions are the single equation `2q(1-q) = 1/3`. Floor-one
scale and coordinate kurtosis are one observable.
-/

/-- The squared scale of the normalized squaring flow at a unit-variance coordinate:
`σ² = Var(X²) = E[X⁴] - 1`.

Empirical status: DERIVED. The variance of the square of a unit-variance coordinate, with
no free parameter; for genotypes it is `standardizedSquare_second_cumulant`. -/
noncomputable def squaringScaleSq (fourthMoment : ℝ) : ℝ := fourthMoment - 1

/-- **The scale is the excess fourth moment over the Gaussian-normalised unit.** -/
theorem squaringScaleSq_add_one (fourthMoment : ℝ) :
    squaringScaleSq fourthMoment + 1 = fourthMoment := by
  unfold squaringScaleSq
  ring

/-- The fourth moment of the next floor, `E[((X² - 1)/σ)⁴]`, expanded in the current
floor's even moments: `(m₈ - 4m₆ + 6m₄ - 4m₂ + 1) / (m₄ - 1)²`.

Empirical status: DERIVED. The binomial expansion of `(X² - 1)⁴` divided by `σ⁴`; no free
parameter and nothing fitted.

**Numerical warning -- the expanded form must not be evaluated as written.** The
numerator is `E[(X² - 1)⁴]` with the fourth power multiplied out, so it is an
alternating sum of raw moments with binomial coefficients `1, -4, 6, -4, 1`. Raw
moments of a unit-variance coordinate are all `O(1)` while their alternating
combination is `O(σ⁸)`, and `σ² = m₄ - 1` is small precisely on the descent this
recurrence is built to follow. Measured float64 against a 60-digit reference,
arguments rounded to float64 first, along a Gaussian family and a near-two-point
family approaching `m₄ = 1`: **6 of 25 cells exceed 1e-6 relative error, worst
1.0** -- 100%, i.e. the next floor's fourth moment is returned as pure noise.
The divisor `(m₄ - 1)²` then squares the damage.

The stable evaluation never expands the power: form `Y = X² - 1` first and take
`E[Y⁴] / (E[Y²])²` from CENTERED moments of `Y`. That is the same number and it
has no cancellation in it. This body states which number is meant; it is not the
recipe for computing it. Consumers restricted to raw moments must additionally
require `m₄ - 1` bounded away from zero -- `nextFloorFourthMoment_unit_m4_is_junk`
below names the exact-zero case, but the whole neighbourhood is unusable, not
just the point. -/
noncomputable def nextFloorFourthMoment (m2 m4 m6 m8 : ℝ) : ℝ :=
  (m8 - 4 * m6 + 6 * m4 - 4 * m2 + 1) / (m4 - 1) ^ 2

/-- **nextFloorFourthMoment at unit m4, named.** A fourth moment of one is the Gaussian floor
itself, where the recurrence has nothing left to descend and the next floor is undefined. The
divisor `(m4 - 1) ^ 2` is zero and Lean returns `0`, a floor BELOW the Gaussian one, which the
moment hierarchy forbids. Consumers must require `m4 ≠ 1`. -/
theorem nextFloorFourthMoment_unit_m4_is_junk (m2 : ℝ) (m6 : ℝ) (m8 : ℝ) :
    nextFloorFourthMoment m2 1 m6 m8 = 0 := by
  unfold nextFloorFourthMoment
  simp

/-- **The next floor's fourth moment from the NEXT floor's own moments**: with
`Y = X² - 1`, it is just `E[Y⁴] / (E[Y²])²`.

This is the same number as `nextFloorFourthMoment` -- `nextFloorFourthMoment_eq_ofY`
below proves it at unit variance -- and it is the form an implementation must
evaluate. The stability does NOT come from the algebra here, which is a division
and nothing more; it comes from WHERE the two arguments are obtained. A consumer
holding sample data can accumulate `E[Y²]` and `E[Y⁴]` directly from the realised
`Y = X² - 1`, so the alternating binomial sum over raw moments is never formed and
its cancellation never happens. Feeding this body arguments that were themselves
computed as `m₄ - 2m₂ + 1` and `m₈ - 4m₆ + 6m₄ - 4m₂ + 1` recovers the instability
exactly; the name is a route, not a charm.

Empirical status: DERIVED. `E[Y⁴]/(E[Y²])²` is the standardised fourth moment of
`Y`, with no free parameter. -/
noncomputable def nextFloorFourthMomentOfY (secondY fourthY : ℝ) : ℝ :=
  fourthY / secondY ^ 2

/-- **The two routes agree at unit variance.** With `m₂ = 1` the squaring flow's
scale is `E[Y²] = m₄ - 1` and its fourth moment is `E[Y⁴] = m₈ - 4m₆ + 6m₄ - 3`,
so the expanded raw-moment body and the centred body are the same function. Unit
variance is not a restriction added to make this work: it is the normalisation the
whole squaring tower is defined under, and `squaringScaleSq` already reads the
scale as `m₄ - 1`, which is `E[Y²]` only when `m₂ = 1`. -/
theorem nextFloorFourthMoment_eq_ofY (m4 m6 m8 : ℝ) :
    nextFloorFourthMoment 1 m4 m6 m8 =
      nextFloorFourthMomentOfY (m4 - 1) (m8 - 4 * m6 + 6 * m4 - 3) := by
  unfold nextFloorFourthMoment nextFloorFourthMomentOfY
  ring_nf

/-- **Floor one of the Gaussian tower has `σ₁² = 2`.** From `E[X⁴] = 3`. -/
theorem gaussianFloorOneScaleSq : squaringScaleSq 3 = 2 := by
  unfold squaringScaleSq
  norm_num

/-- **The Gaussian's second floor has fourth moment `15`.** From the standard normal
moments `E[X²] = 1`, `E[X⁴] = 3`, `E[X⁶] = 15`, `E[X⁸] = 105`:
`(105 - 60 + 18 - 4 + 1)/4 = 60/4 = 15`. The numerator `60` is the fourth central moment
of a chi-square with one degree of freedom, which is the independent check.

Read the other way, this is the fixed point the tower is built on -- the squared floor of a
Gaussian has the same fourth moment as the Gaussian's sixth, which fixes every coefficient in
the numerator at once. That reading was a second theorem with this exact statement. -/
theorem gaussianFloorTwoFourthMoment : nextFloorFourthMoment 1 3 15 105 = 15 := by
  unfold nextFloorFourthMoment
  norm_num

/-- **Floor two of the Gaussian tower has `σ₂² = 14`**, so `σ₂ = √14 = 3.74166…`.

This is the second entry of a sequence nobody has written down, and with
`gaussianFloorOneScaleSq` it anchors the doubly-exponential growth carried below as a
hypothesis. -/
theorem gaussianFloorTwoScaleSq :
    squaringScaleSq (nextFloorFourthMoment 1 3 15 105) = 14 := by
  rw [gaussianFloorTwoFourthMoment]
  unfold squaringScaleSq
  norm_num

/-- **The genotype's floor-one scale**, in cleared form: `V · σ₁² = 1 - V`, that is
`σ₁² = 1/V - 1` with `V = 2q(1-q)`.

This is `standardizedSquare_second_cumulant` read as the first entry of the genotype's own
scale sequence. It exceeds the Gaussian's `2` for rare variants — about `49` at MAF `0.01`
— and falls below it for common ones. -/
theorem hweFloorOneScaleSq_eq (h : HardyWeinbergModel)
    (hq0 : 0 < h.altFreq) (hq1 : h.altFreq < 1) :
    h.genotypeVariance *
        squaringScaleSq
          (∑ g : DiploidGenotype, h.genotypeProb g * h.standardizedGenotype g ^ 4) =
      1 - h.genotypeVariance := by
  unfold squaringScaleSq
  exact standardizedSquare_second_cumulant h hq0 hq1

/-- **The genotype's floor-one scale equals the Gaussian's at the blind frequency**
`gaussianKurtosisMaf = (3 - √3)/6`, where the genotype variance is `1/3` and so
`σ₁² = 1/V - 1 = 2`.

**These are not two facts.** `squaringScaleSq` is `E[x⁴] - 1` by definition, so matching a
coordinate's kurtosis to the Gaussian's `3` and matching its floor-one scale to the
Gaussian's `2` are the same equation, `2q(1-q) = 1/3`. This theorem is therefore a
consistency check on the two derivations, not a coincidence between them, and nobody should
go looking for a mechanism that explains the agreement.

The identity behind it is the content worth keeping: **floor-one scale and coordinate
kurtosis are one observable**, differing by the constant `1`. What survives independently
of the framing is the direction — `σ₁² = 1/V - 1` is about `49` at MAF `0.01` and `1` at
MAF `0.5`, so rare variants start the tower further from the Gaussian and are harder to
read at every floor. -/
theorem hweFloorOneScaleSq_eq_gaussian_at_blind_maf (h : HardyWeinbergModel)
    (hmaf : h.altFreq = gaussianKurtosisMaf) :
    squaringScaleSq
        (∑ g : DiploidGenotype, h.genotypeProb g * h.standardizedGenotype g ^ 4) =
      squaringScaleSq 3 := by
  rw [standardizedGenotype_kurtosis_gaussian_at_blind_maf h hmaf]

/-!
### The flow is a contraction once the scale is large

Three facts about `x ↦ (x² - 1)/σ`, all proved: it is `2R/σ`-Lipschitz on the ball of
radius `R`, it maps that ball into itself once `σ` is large enough, and its positive fixed
point is at least `σ`. Together they say a diverging scale sequence leaves no escape
region.
-/

/-- The squaring map is `2R`-Lipschitz on the ball of radius `R`, before normalization.
Dividing by `σ` makes the constant `2R/σ`, which is below one as soon as `σ > 2R`. -/
theorem squaringFlow_lipschitz {R x y : ℝ} (hx : |x| ≤ R) (hy : |y| ≤ R) :
    |x ^ 2 - y ^ 2| ≤ 2 * R * |x - y| := by
  have hfactor : x ^ 2 - y ^ 2 = (x + y) * (x - y) := by ring
  have hsum : |x + y| ≤ 2 * R := by
    calc |x + y| ≤ |x| + |y| := abs_add_le x y
      _ ≤ R + R := by linarith
      _ = 2 * R := by ring
  rw [hfactor, abs_mul]
  exact mul_le_mul_of_nonneg_right hsum (abs_nonneg _)

/-- **The flow maps every bounded region into itself once the scale is large.** For
`σ ≥ (R² + 1)/R` the ball of radius `R` is invariant, so no point of it escapes — however
the threshold `R` was chosen.

This is the failure of the escape argument, stated positively: with `σ_k` diverging, every
fixed threshold is eventually swallowed. -/
theorem squaringFlow_maps_ball_into_itself {σ R x : ℝ} (hR : 0 < R) (hσ : 0 < σ)
    (hx : |x| ≤ R) (hlarge : (R ^ 2 + 1) / R ≤ σ) :
    |(x ^ 2 - 1) / σ| ≤ R := by
  have hxle : x ≤ R := (abs_le.mp hx).2
  have hxge : -R ≤ x := (abs_le.mp hx).1
  have hsq : x ^ 2 ≤ R ^ 2 := by nlinarith [hxle, hxge]
  have hnum : |x ^ 2 - 1| ≤ R ^ 2 + 1 := by
    rw [abs_le]
    constructor
    · nlinarith [sq_nonneg x]
    · nlinarith [hsq]
  have hmul : R ^ 2 + 1 ≤ σ * R := by
    rw [div_le_iff₀ hR] at hlarge
    linarith [hlarge]
  rw [abs_div, abs_of_pos hσ, div_le_iff₀ hσ]
  calc |x ^ 2 - 1| ≤ R ^ 2 + 1 := hnum
    _ ≤ σ * R := hmul
    _ = R * σ := by ring

/-- **The one-step map of the flow**: `x ↦ (x² - 1)/σ`, one floor of the tower applied to
a point rather than to a law.

Empirical status: DERIVED. The centering-and-rescaling step that defines the tower; the
centering constant is forced by `E[X²] = 1` and the scale by `Var(X²)`, so there is no free
parameter. -/
noncomputable def squaringStep (scale x : ℝ) : ℝ := (x ^ 2 - 1) / scale

/-- **squaringStep at zero scale, named.** A zero scale leaves the squaring step undefined. Lean
returns `0`, a fixed point of the recurrence, so an iteration through this branch stalls silently
rather than failing. Consumers must require `scale ≠ 0`. -/
theorem squaringStep_zero_scale_is_junk (x : ℝ) :
    squaringStep 0 x = 0 := by
  unfold squaringStep
  simp

/-- The positive fixed point of the normalized squaring flow, `(σ + √(σ² + 4))/2`.

Empirical status: DERIVED. The positive root of `x² - σx - 1 = 0`, which is the fixed-point
equation of `squaringStep`; no free parameter. -/
noncomputable def squaringFixedPoint (scale : ℝ) : ℝ :=
  (scale + Real.sqrt (scale ^ 2 + 4)) / 2

/-- Reference evaluation.  The value is computed through the definitions this body calls, but
the theorem states a number: an inequality or an invariance leaves a family of bodies
satisfying it, and a value does not. -/
theorem squaringFixedPoint_at_reference_point :
    squaringFixedPoint 0 = 1 := by
  norm_num [squaringFixedPoint]


/-- The defining identity in cleared form: `x*² - 1 = σ x*`. -/
theorem squaringFixedPoint_root (scale : ℝ) :
    squaringFixedPoint scale ^ 2 - 1 = scale * squaringFixedPoint scale := by
  have hsq : Real.sqrt (scale ^ 2 + 4) ^ 2 = scale ^ 2 + 4 :=
    Real.sq_sqrt (by positivity)
  unfold squaringFixedPoint
  nlinarith [hsq]

/-- **It is a fixed point of the one-step map**: `squaringStep σ x* = x*`. This is the
obligation a named fixed point carries — the map beside it, and the theorem tying them. -/
theorem squaringFixedPoint_isFixedPoint (scale : ℝ) (hscale : scale ≠ 0) :
    squaringStep scale (squaringFixedPoint scale) = squaringFixedPoint scale := by
  unfold squaringStep
  rw [squaringFixedPoint_root, mul_div_cancel_left₀ _ hscale]

/-- **The fixed point tracks the scale**: `σ ≤ x*`. So a diverging scale sequence has
diverging fixed points, and the region inside the fixed point — where the flow is
contracting — eventually contains any given bounded set. -/
theorem scale_le_squaringFixedPoint {scale : ℝ} (hscale : 0 ≤ scale) :
    scale ≤ squaringFixedPoint scale := by
  have hsq : Real.sqrt (scale ^ 2 + 4) ^ 2 = scale ^ 2 + 4 :=
    Real.sq_sqrt (by positivity)
  have hnonneg : 0 ≤ Real.sqrt (scale ^ 2 + 4) := Real.sqrt_nonneg _
  unfold squaringFixedPoint
  nlinarith [hsq, hnonneg, hscale]

/-! The tower-scale growth law is not represented by an externally populated record.
Exact low-floor identities remain above; asymptotic growth awaits a proof from a defined
scale recursion. -/

/-!
## 5i. The rigidity phase boundary, and where genotypes sit on it

The founding dichotomy of this arc — **universality holds exactly when the coordinate law
is Gaussian**, at the tower level from four data (symmetry, `σ₁ = √2`, equivalently
`E[x⁴] = 3`, and the odd parts of the floor-two and floor-three laws) — is **not proved
in this repository**. There is no such theorem in `proofs/Calibrator`; the claimed
mechanism is a contraction argument, and it is cited here, as it is in
`Calibrator.PolygenicSpectroscopy` §4c, only to name the hypotheses being ruled out.
Everything proved in this section is a moment computation about genotypes that stands
whatever becomes of the rigidity claim.

A *corollary* of the same proof gives rigidity of the tower fibre at any base law with
`E[x⁴] > 2`, the condition that keeps the confined squares below one — `1/σ₁² < 1`, that
is `σ₁² > 1`. Below that threshold the images straddle zero and the argument yields
nothing, so `E[x⁴] = 2` is a phase boundary.

**Keep the two apart.** `E[x⁴] > 2` is the corollary's phase condition; the theorem's own
hypotheses are symmetry, `E[x⁴] = 3`, and the two odd parts. They select very different
frequency sets — `> 2` is everything except `q = 1/2`, while `= 3` is the two points
`(3 ± √3)/6` — and conflating them produces a false statement about applicability.

Where genotypes sit on the boundary: since `q(1-q) ≤ 1/4` with equality only at `q = 1/2`,
the variance obeys `V = 2q(1-q) ≤ 1/2` and so `E[x⁴] = 1/V ≥ 2` at every polymorphic
frequency, with equality exactly at the balanced locus
(`standardizedGenotype_fourth_moment_ge_two`,
`standardizedGenotype_fourth_moment_eq_two_iff`). Rare variants sit far from the boundary,
since `1/(2q(1-q))` diverges as `q → 0`.

**But the theorem never applies to a genotype at all.** The hypotheses are jointly
unsatisfiable here, and the proof is two steps from facts above: symmetry pins the
frequency to `q = 1/2`, and there the fourth moment is `2`, not `3`
(`hwe_rigidity_hypotheses_unsatisfiable`). At the one frequency where the fourth moment
does match, `0.21132…`, the coordinate is not symmetric. Indeed the phase inequality and
the symmetry hypothesis are *complementary* on the spectrum — the first holds exactly
where the second fails (`phase_strict_iff_not_symmetric`) — so no allele frequency
satisfies both. That is stronger than "applies everywhere but one point".

### The balanced locus is special twice, from one cause

`q = 1/2` is now distinguished for two genuinely different reasons: it is the only
frequency where the coordinate is sign-symmetric (`standardizedGenotype_symmetric_iff`, a
statement about odd moments), and it is the only frequency on the kurtosis phase boundary
(a statement about the fourth). These are not the same condition — unlike floor-one scale
and kurtosis, which are one observable differing by `1`.

They have a **common cause** rather than being a coincidence, and the cause is provable
here: the reflection `q ↦ 1 - q` sends the standardized coordinate to its negative
(`reflect_standardizedGenotype`), so every even moment is reflection-invariant
(`fourthMoment_reflection_invariant`) and `q = 1/2` is the reflection's unique fixed point
(`balanced_locus_is_reflection_fixed_point`). A coordinate law equals its own negation
exactly at that fixed point, which is the symmetry; and a reflection-invariant function of
`q` has its extremum there, which is the kurtosis boundary. One symmetry of
`Binomial(2, q)`, two consequences.

### What is redundant, and exactly where

The rigidity theorem's corollary is that every other tower datum — all Mellin jets, all
arithmetic types, all higher floors, all cumulants of iterated squares — is reconstructible
from the four, hence logically redundant **at the Gaussian fiber, and only there**. The
qualifier is not decoration. Off that fiber, symmetry together with the scale and two odd
parts determines nothing, and the Mellin invariants are not reconstructible from them.

Since no polymorphic genotype is on the Gaussian fiber — `E[x⁴] = 1/(2q(1-q))` equals `3`
at two frequencies and the coordinate is symmetric at neither — `hweMellinDrift` and
`hweMellinJetVariance` remain **independently informative for exactly the objects this
corpus is about**. What the redundancy corollary demotes is their claim to be a minimal
complete list for a general coordinate law, not their content for genotypes.

The load in the rigidity argument is carried by the odd part of the *squared* law, which no
moment list mentions — which is why four successive finite lists failed to close the
question.

The corpus does **not** already own the decisive datum, and the tempting argument that it
does — that `standardizedSquare_never_symmetric` makes the odd part of the floor-two law
nonzero at every polymorphic frequency including `q = 1/2` — is false. It is the exact
misreading that theorem's own docstring warns against: it is about the *uncentered* square
`x²`, which is non-negative and so trivially never symmetric, while floor two is the
*centered* square, which at `q = 1/2` is Rademacher and symmetric
(`Calibrator.EpistaticChaos.centeredSquare_rademacher_at_half`). Away from `q = 1/2` the
floor-two odd part is indeed nonzero (`centeredSquare_third_moment_zero_iff_balanced`);
at the balanced locus it vanishes, and the corpus has no floor-two separation there.

### The horizon problem does not bite

Rigidity needs floors two and three only, with `σ₂ = √14`, comfortably inside any
sample-size horizon. The doubly-exponentially unreachable floors of §5h are exactly the
redundant ones, so the cutoff and the theorem never meet: the cutoff stands as a real limit
on what is measurable and costs the theorem nothing.

**Scope, kept explicit.** These are statements about *complete invariants* of a coordinate
law, not about what a design can see. The bridge from tower data to design-observable data
is open upstream, so nothing here should be read as "a design can measure the four".
-/

/-- The genotype variance is at most one half, with equality at the balanced locus:
`2q(1-q) ≤ 1/2` because `(2q-1)² ≥ 0`. -/
theorem hweGenotypeVariance_le_half (h : HardyWeinbergModel) :
    h.genotypeVariance ≤ 1 / 2 := by
  rw [h.genotypeVariance_eq]
  unfold HardyWeinbergModel.refFreq
  nlinarith [sq_nonneg (h.altFreq - 1 / 2)]

/-- **Every polymorphic genotype coordinate has `E[x⁴] ≥ 2`**, so it lies inside or on the
rigidity phase boundary. -/
theorem standardizedGenotype_fourth_moment_ge_two (h : HardyWeinbergModel)
    (hq0 : 0 < h.altFreq) (hq1 : h.altFreq < 1) :
    2 ≤ ∑ g : DiploidGenotype, h.genotypeProb g * h.standardizedGenotype g ^ 4 := by
  have hvar : 0 < h.genotypeVariance := h.genotypeVariance_pos hq0 hq1
  rw [standardizedGenotype_fourth_moment h hq0 hq1, le_div_iff₀ hvar]
  have hle := hweGenotypeVariance_le_half h
  linarith [hle]

/-- **Equality holds exactly at the balanced locus.** `E[x⁴] = 2` iff `q = 1/2`, so the
balanced genotype sits precisely on the phase boundary where the rigidity mechanism's
one-sided image collapses. -/
theorem standardizedGenotype_fourth_moment_eq_two_iff (h : HardyWeinbergModel)
    (hq0 : 0 < h.altFreq) (hq1 : h.altFreq < 1) :
    (∑ g : DiploidGenotype, h.genotypeProb g * h.standardizedGenotype g ^ 4) = 2 ↔
      h.altFreq = 1 / 2 := by
  have hvar : 0 < h.genotypeVariance := h.genotypeVariance_pos hq0 hq1
  have hveq : h.genotypeVariance = 2 * h.altFreq * (1 - h.altFreq) := by
    rw [h.genotypeVariance_eq]
    unfold HardyWeinbergModel.refFreq
    ring
  rw [standardizedGenotype_fourth_moment h hq0 hq1, div_eq_iff (ne_of_gt hvar)]
  constructor
  · intro heq
    rw [hveq] at heq
    have hsq : (2 * h.altFreq - 1) ^ 2 = 0 := by nlinarith [heq]
    have hzero : 2 * h.altFreq - 1 = 0 :=
      pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hsq
    linarith [hzero]
  · intro hhalf
    rw [hveq, hhalf]
    norm_num

/-- **The phase inequality `E[x⁴] > 2` holds off the balanced locus**, and only that.

This discharges the *phase* hypothesis of the kurtosis-boundary corollary, which is one
hypothesis among several. It says nothing about whether the rigidity theorem applies to a
genotype, and it must not be read that way: the theorem's own hypotheses are symmetry,
`E[x⁴] = 3`, and two matched odd parts, and for genotypes those are never jointly
satisfiable (`hwe_rigidity_hypotheses_unsatisfiable`).

Note also that the phase inequality holds exactly where the symmetry hypothesis fails —
they are complementary on the frequency spectrum, not cooperative
(`phase_strict_iff_not_symmetric`). -/
theorem hwe_phase_inequality_off_balanced (h : HardyWeinbergModel)
    (hq0 : 0 < h.altFreq) (hq1 : h.altFreq < 1) (hunbalanced : h.altFreq ≠ 1 / 2) :
    2 < ∑ g : DiploidGenotype, h.genotypeProb g * h.standardizedGenotype g ^ 4 := by
  have hge := standardizedGenotype_fourth_moment_ge_two h hq0 hq1
  have hne : (∑ g : DiploidGenotype, h.genotypeProb g * h.standardizedGenotype g ^ 4) ≠ 2 := by
    intro heq
    exact hunbalanced ((standardizedGenotype_fourth_moment_eq_two_iff h hq0 hq1).mp heq)
  exact lt_of_le_of_ne hge (Ne.symm hne)

/-- **The phase inequality holds exactly where symmetry fails.** For a polymorphic
genotype the strict inequality `E[x⁴] > 2` and the existence of a value-negating
relabelling are complementary: the first holds off `q = 1/2`, the second only at it.

So the two hypotheses select disjoint frequency sets, which is the structural reason the
rigidity theorem cannot be applied to genotype data. -/
theorem phase_strict_iff_not_symmetric (h : HardyWeinbergModel)
    (hq0 : 0 < h.altFreq) (hq1 : h.altFreq < 1) :
    2 < (∑ g : DiploidGenotype, h.genotypeProb g * h.standardizedGenotype g ^ 4) ↔
      ¬ (∃ coding : SymmetricCoding DiploidGenotype,
          (∀ g, coding.weight g = h.genotypeProb g) ∧
          (∀ g, coding.value g = h.standardizedGenotype g)) := by
  constructor
  · intro hstrict hsym
    have hhalf := (standardizedGenotype_symmetric_iff h hq0 hq1).mp hsym
    have htwo := (standardizedGenotype_fourth_moment_eq_two_iff h hq0 hq1).mpr hhalf
    rw [htwo] at hstrict
    exact absurd hstrict (by norm_num)
  · intro hnosym
    refine hwe_phase_inequality_off_balanced h hq0 hq1 ?_
    intro hhalf
    exact hnosym ((standardizedGenotype_symmetric_iff h hq0 hq1).mpr hhalf)

/-- **The rigidity theorem's hypotheses are never jointly satisfiable on genotype data.**

Symmetry pins the frequency to `q = 1/2` (`standardizedGenotype_symmetric_iff`), and there
the fourth moment is `2` (`standardizedGenotype_fourth_moment_eq_two_iff`), not the
Gaussian's `3`. The frequency where the fourth moment alone would match is
`gaussianKurtosisMaf = 0.21132…`, and the coordinate is not symmetric there.

So the headline rigidity result never gets a satisfied hypothesis on a standardized
Hardy-Weinberg coordinate — at any allele frequency. This is stronger than saying the
theorem applies away from a single point, and it is the honest statement of what the tower
result does and does not say about genotypes. -/
theorem hwe_rigidity_hypotheses_unsatisfiable (h : HardyWeinbergModel)
    (hq0 : 0 < h.altFreq) (hq1 : h.altFreq < 1)
    (hsym : ∃ coding : SymmetricCoding DiploidGenotype,
      (∀ g, coding.weight g = h.genotypeProb g) ∧
      (∀ g, coding.value g = h.standardizedGenotype g)) :
    (∑ g : DiploidGenotype, h.genotypeProb g * h.standardizedGenotype g ^ 4) ≠ 3 := by
  have hhalf := (standardizedGenotype_symmetric_iff h hq0 hq1).mp hsym
  have htwo := (standardizedGenotype_fourth_moment_eq_two_iff h hq0 hq1).mpr hhalf
  rw [htwo]
  norm_num

/-- The blind frequency is not the balanced one: `(3 - √3)/6 ≠ 1/2`, since `√3 > 0`.

So the one frequency where the fourth moment matches the Gaussian's is a frequency where
the symmetry hypothesis fails, which is the other half of the unsatisfiability. -/
theorem gaussianKurtosisMaf_ne_half : gaussianKurtosisMaf ≠ 1 / 2 := by
  unfold gaussianKurtosisMaf
  intro hcontra
  have hpos := sqrt_three_pos
  linarith [hcontra]

/-- The fourth moment is reflection-invariant, being even data: this is
`reflect_even_moment` at `k = 2`. -/
theorem fourthMoment_reflection_invariant (h : HardyWeinbergModel) :
    (∑ g : DiploidGenotype,
        h.reflect.genotypeProb g * h.reflect.standardizedGenotype g ^ 4) =
      ∑ g : DiploidGenotype, h.genotypeProb g * h.standardizedGenotype g ^ 4 := by
  have hk := reflect_even_moment h 2
  norm_num at hk
  exact hk

/-- **The balanced locus is the unique fixed point of the frequency reflection.**

This is the common cause of the balanced locus being special twice. The reflection sends
the coordinate to its negative, so a law equals its own negation exactly at the fixed point
— that is the symmetry — while every even moment is reflection-invariant and so takes its
extremum there — that is the kurtosis boundary. Two different statements, one symmetry of
`Binomial(2, q)`. -/
theorem balanced_locus_is_reflection_fixed_point (h : HardyWeinbergModel) :
    h.reflect.altFreq = h.altFreq ↔ h.altFreq = 1 / 2 := by
  rw [HardyWeinbergModel.reflect_altFreq]
  constructor
  · intro hfix
    linarith [hfix]
  · intro hhalf
    rw [hhalf]
    norm_num

/-! Tower rigidity remains an analytic target. The former theorem-valued record and its
projection consequence are removed. -/

/-!
## 5j. The sign bias, and the exposure mechanism it does not give

### The claim this section rules out

There is **no coupling channel** separate from the hub channel. A sliding-window design
carries no tuned-sector variance inflation `2b²/(1 - b²)` in the conditional sign bias
`b`, tunable through a window tilt `θ*`, and a bounded hub energy is therefore exactly as
much reassurance for a rare-variant window scan as it is anywhere else. The closed form
`2(1-2q)⁴/(1-(1-2q)⁴)`, and its exact rationals at MAF 0.05 and 0.01, describe nothing.

**Why the mechanism fails.** A tilt-bookkeeping error produces it. The
vanishing-first-order argument uses a `θ = 1/2` weight, which mixes a level-two
normalization into a level-one computation. At the correct weights the solo-factor mean is

> `E[u e^λ] / E[e^λ] = E[(x² - 1) x²] = σ₁² = 2`,

not zero. The first-order cross term therefore does not vanish, and what it exposes is
`Λ(2)` data — that is `E[x⁴]` — which the hub channel already exposes. The term is
**hub-redundant rather than a new channel**. Separation between the two channels is the
premise the mechanism needs, and no quantitative consequence survives without it.

A second retraction landed at the same time and is recorded here because this file leaned
on it: the jet-to-strip upgrade is false, since the window channel's exposed functional is
the truncated second moment at tilt `θ = 1` whatever the tuning slope. Changing the slope
moves the threshold *within* the `θ = 1` tilted walk rather than changing the tilt at which
the law is probed. That is what `Calibrator.JetBarrier` had already said, so the arc
contradicted its own theorem and the theorem was right.

Removed with the mechanism: `couplingVarianceInflation` and its closed form, the exact
rationals `13122/3439` and `11529602/485199` presented as a sliding-window inflation, and
`boundedHub_does_not_bound_coupling`, whose conclusion asserted an order-one correction a
bounded hub misses.

### What stands

* `Calibrator.EpistaticChaos.hweSignBias_eq` — `E[x|x|] = (1-2q)²` for `q ≤ 1/2`. This is
  arithmetic about the genotype law, derived here independently of the retracted mechanism,
  and nothing upstream touches it.
* `hweSignBias_zero_iff_balanced` — `b` vanishes exactly at the balanced locus, so the
  Sign-Erasure Lemma is the zero fibre of `b`.
* `b` as a well-defined object and as the correct *name* for the data a symmetric law
  destroys. That naming is retained upstream explicitly.

### What is open

**Whether any admissible design exposes `b` at all.** The one mechanism proposed for that
has been withdrawn and no replacement has been supplied. Until one is, `b` is a property of
the coordinate law with no established design-level consequence, and this file asserts none.
In particular nothing here now says a sliding-window scan is miscalibrated through `b`, and
nothing here says it is safe either — the hub statement remains a statement about the hub
channel, and the coupling question is open rather than answered in either direction.

## 5k. The dyadic Mellin ladder, and why the horizon is where it is

§5h recorded that the scale sequence diverges doubly exponentially and that the sample cost
of reading floor `k` therefore grows like `σ_k²`, truncating the tower at about floor three.
That was stated as a numerical fact about one sequence. It has a mechanism, and with the
mechanism it stops being a separate observation and becomes a consequence of how the
tower's coordinates are laid out.

The tower's coordinate system is a **dyadic Mellin ladder**: floor `k` carries the jet,
arithmetic, hub and coupling data of the log-square hierarchy at scale `2^(k-1)`. Floor one
sits at tilt `θ = 1` and reads second moments; the hub and shared blocks sit at `θ = 2` and
read fourth moments, which is `σ₁`; floor two sits near `θ = 2` and floor three near
`θ = 4`. The rungs are dyadic in *moment order*: successive floors probe moments of order
`2, 4, 8, 16, …`.

That is the mechanism. Reading a moment of order `2m` costs a sample budget growing with
the size of that moment, and for a standardized genotype those moments diverge — **at every
order, by proof rather than by pattern**:

> `Calibrator.EpistaticChaos.standardizedGenotype_even_moment_lower_bound` :
> `E[x^(2m)] ≥ (1-2q)^(2m) / V^(m-1)`,

obtained by keeping the heterozygote term and discarding the other two, which are
non-negative at every order. The general-order identity behind it is
`standardizedGenotype_even_moment_mul`, `E[x^(2m)] · V^m = E[(g-2q)^(2m)]`, where the
standardization contributes exactly `V^m` whatever the order.

The three orders this corpus computes in closed form are the instances:

| moment | value | growth as `V → 0` |
|---|---|---|
| `E[x²]` | `1` | bounded |
| `E[x⁴]` | `1/V` | `V⁻¹` |
| `E[x⁶]` | `1/V² + 10/V - 20` | `V⁻²` |

with `V = 2q(1-q)` (`standardizedGenotype_second_moment_one`,
`standardizedGenotype_fourth_moment`, `standardizedGenotype_sixth_moment`, collected as
`hweLadderMoments`). A symbolic check over `m = 1..5`
(`proofs/validation/empirical/coupling/ladder_moments.py`) confirms the sharp form the bound only
brackets: `V^(m-1) E[x^(2m)] → 1` at every order tested, and `V` divides the numerator
exactly, so that quantity is a polynomial in `q` equal to `1` at `q = 0`. The exponent of
`V⁻¹` advances by one per moment-order step of two, so along the ladder — whose steps
*double* the moment order — it advances by `2^(k-1)`. A doubling of moment order squares
the divergence.

So the doubly-exponential sample cost is not an accident of how the floors were normalized.
It is dyadic rung spacing measured against a polynomial sample budget: reachable floors go
like `log log n` because the ladder's rungs are dyadic in moment order and the budget is
not. A quantitative asymptotic theorem is not exported until the scale recursion is formalized,
and `ladderMomentOrder` below names the spacing it comes from.

The biology reads off the table. `E[x⁴] = 1/(2q(1-q))` already diverges as a variant gets
rarer, and each further rung squares that dependence, so a rare-variant panel is not merely
further from the Gaussian at floor one — it is further by an exponentially growing margin at
every floor above. Rare variants are hardest to read exactly where the ladder climbs
fastest.
-/

/-- **The moment order probed at rung `k` of the dyadic ladder**: `2^k`.

Floor one reads second moments, the hub and shared blocks read fourth moments, and each
subsequent floor doubles the order again.

Empirical status: DERIVED. The rung spacing of the tower's coordinate system, with no free
parameter and nothing fitted. -/
def ladderMomentOrder (rung : ℕ) : ℕ := 2 ^ rung

/-- The ladder's first three rungs are the moment orders `2`, `4` and `8`, the first two of
which this corpus computes in closed form. -/
theorem ladderMomentOrder_low_rungs :
    ladderMomentOrder 1 = 2 ∧ ladderMomentOrder 2 = 4 ∧ ladderMomentOrder 3 = 8 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    · unfold ladderMomentOrder
      norm_num

/-- **The rung spacing doubles.** This is the whole mechanism behind the horizon: a
polynomial sample budget advances the readable moment order linearly while the ladder
advances it geometrically, so the number of reachable rungs grows like the logarithm of the
logarithm of the budget. -/
theorem ladderMomentOrder_doubles (rung : ℕ) :
    ladderMomentOrder (rung + 1) = 2 * ladderMomentOrder rung := by
  unfold ladderMomentOrder
  rw [pow_succ]
  ring

/-- The genotype moments at the first three computed orders, collected so the growth
pattern `1`, `V⁻¹`, `V⁻²` is visible in one place and a later change to any of them
contradicts this theorem rather than drifting silently. -/
theorem hweLadderMoments (h : HardyWeinbergModel)
    (hq0 : 0 < h.altFreq) (hq1 : h.altFreq < 1) :
    (∑ g : DiploidGenotype, h.genotypeProb g * h.standardizedGenotype g ^ 2) = 1 ∧
      (∑ g : DiploidGenotype, h.genotypeProb g * h.standardizedGenotype g ^ 4) =
        1 / h.genotypeVariance ∧
      (∑ g : DiploidGenotype, h.genotypeProb g * h.standardizedGenotype g ^ 6) =
        (1 / h.genotypeVariance) ^ 2 + 10 * (1 / h.genotypeVariance) - 20 :=
  ⟨standardizedGenotype_second_moment_one h hq0 hq1,
    standardizedGenotype_fourth_moment h hq0 hq1,
    standardizedGenotype_sixth_moment h hq0 hq1⟩

/-!
## 5l. The ladder fiber is empty over genotype panels

A **ladder chameleon** has been constructed upstream: an explicit symmetric,
unit-variance, all-moments, nonlattice law that is not Gaussian and matches the Gaussian
in every proven-exposed invariant at every floor. It is built by **fiber splitting** —
for each `s`, the two preimages of `|u| = s` are the `x²` values `1 + s` and `1 - s`, and
mass is moved between them. That preserves the law of `|u|` exactly, hence every
functional of it, hence floors three and up as laws, and changes only the odd part of the
floor-two law.

**The dichotomy is therefore now believed FALSE in its final form** — *on the stratum
where it is proved*, which is the qualifier that matters here and is stated below. The
expected answer is that the observable algebra is exactly the ladder and the universality
class is the **ladder fiber** of the Gaussian, infinite-dimensional and explicitly
parameterized. This is not asserted as settled: the assembly is open and the remaining gap
is a limit-classification theorem rather than a construction.

**Scope, and genotypes are outside it.** The blindness argument runs through a
second-order Edgeworth expansion of walk-convolution profiles with an `O(b^(-3/2))`
remainder, and that needs **Cramér's condition on the log-square law**. Nonlattice
*atomic-modulus* laws violate it; there the per-coordinate remainder is only `o(b^(-1/2))`
and the coordinate count defeats it. The theorem was rescued for its own pair because both
members have smooth modulus densities, so the general statement re-scopes to
Cramér-modulus laws with the non-Cramér frontier an open annex.

A standardized genotype at a diallelic locus takes three values, so `x²` takes at most
three and `log x²` is **finitely supported** — purely atomic, and generically nonlattice,
since three points lie in an arithmetic progression only when their gaps are
commensurable, which is `hweLatticeCondition`. Genotype coordinates are therefore not
merely outside the proved stratum; they are the canonical member of the class the audit
carved out. **Nothing in the blindness theorem transfers to genotype data**, and this file
asserts no such transfer.

The corpus's own results point the same way from the other side, though weakly.
`Calibrator.JetBarrier` proves `one_lt_latticeInflation`: the factor
`h/(1 - e^(-h))` exceeds one. Reading that factor as a ratio of exceedance intensities at
a lattice-aligned threshold — hence as information a design can read — is the conjecture,
and it is a hypothesis of `inflated_intensity_ne_of_injective`, not a theorem. So this is a
worked *candidate* for the mechanism blindness requires to be absent, not a worked example
of it. Whether reflection data leaks through resonance-type window structure at atomic
modulus is open — and if it does, the odd parts are readable from genotype data, which is
the interesting direction rather than the disappointing one.

What follows in this section does not depend on any of that. The peeling result below is
exact linear algebra on the `|u|` law and holds whatever the modulus regularity.

### The genetic question, and its answer

A single locus has no freedom: three atoms, all determined by `q`. A panel is a MAF
mixture, and a mixture over `q` gives a rich law of `x²`. So: **can two MAF spectra
realize a fiber splitting** — two MAF distributions whose induced laws of `|u|` agree
exactly, with different odd parts of `u`?

**No.** The genotype fibers are too rigid, and the reason is the rare homozygote. Writing
`u = x² - 1`, a locus at frequency `q` contributes exactly three atoms,

| atom | value | mass |
|---|---|---|
| `u_ref` | `(3q-1)/(1-q)` | `(1-q)²` |
| `u_het` | `(1-6q+6q²)/(2q(1-q))` | `2q(1-q)` |
| `u_alt` | `2/q - 3` | `q²` |

and on the minor-allele range `(0, 1/2]` the third **strictly dominates** the other two
(`abs_centeredSquare_le_homAlt`) while being **strictly decreasing** in `q`
(`centeredSquare_homAlt_strictAnti`). So the rarest locus in a panel owns the strictly
largest `|u|` atom, and owns it alone (`rarest_locus_owns_largest_atom`).

That gives a peeling argument. Matching the `|u|` law is linear in the weights; at the
level of the largest atom the constraint involves exactly one locus, so that locus's
weight is forced; delete it and repeat. The matrix sending weights to the `|u|` law has
full column rank, its nullspace is trivial, and there is no direction along which the odd
part can move while `|u|` stays fixed.

Verified in exact rational arithmetic by
`proofs/validation/empirical/coupling/fiber_splitting.py` over uniform, rare-weighted, clustered
and fifty-locus frequency sets: nullity zero throughout. Its control is the reflection
`q ↔ 1-q`, which *must* produce a dependency — the two frequencies give identical laws of
`u` by `reflect_even_moment` — and does, with the odd part moving by exactly zero. A
search that found nothing anywhere would not have been shown to work; this one finds the
one dependency theory demands and no others.

**So matching the ladder pins the MAF spectrum.** The chameleon phenomenon has no genetic
realization: whatever the upstream limit classification concludes about laws in general,
two genotype panels that agree in the ladder are the same panel. That is the opposite of
the floor-one result, where matching four scalars left the spectrum badly
underdetermined, and it is worth stating as the sharp contrast — floor-one matching is
cheap and says little, ladder matching is rigid and says everything.

### A false positive, recorded

The first version of the search clustered `|u|` values with a `1e-9` tolerance and
reported a splitting. It was an artifact: the frequency list held `(3-√3)/6` and the
decimal `0.2113248654`, which differ at the eleventh place and straddle the root of
`u_het`. Both `|u_het|` values are about `1e-10`, so the tolerance merged them into one
level, while their *signs* are opposite because `u_het` changes sign at that root — and
every other atom of the two near-equal frequencies was silently merged too. The reported
direction was two nearly identical loci on opposite sides of a zero crossing. The search
is now exact and rejects duplicate frequencies rather than merging them.
-/

/-- The centered square as an offset of the corpus's `standardizedSquare`. -/
theorem centeredSquare_eq_standardizedSquare_sub_one (h : HardyWeinbergModel)
    (hq0 : 0 < h.altFreq) (hq1 : h.altFreq < 1) (g : DiploidGenotype) :
    h.centeredSquare g = h.standardizedSquare g - 1 := by
  unfold HardyWeinbergModel.centeredSquare
  rw [standardizedGenotype_sq_eq_standardizedSquare h hq0 hq1]

/-- The rare-homozygote atom in closed form: `u_alt = (2 - 3q)/q`. -/
theorem centeredSquare_homAlt_eq (h : HardyWeinbergModel)
    (hq0 : 0 < h.altFreq) (hq1 : h.altFreq < 1) :
    h.centeredSquare DiploidGenotype.homAlt = (2 - 3 * h.altFreq) / h.altFreq := by
  obtain ⟨_, _, halt⟩ := standardizedSquare_values h hq0 hq1
  rw [centeredSquare_eq_standardizedSquare_sub_one h hq0 hq1, halt, div_sub_one (ne_of_gt hq0)]
  congr 1
  ring

/-- **The rare-homozygote atom is strictly decreasing in the allele frequency.** This is
half the peeling argument: rarer loci carry strictly larger atoms, so the rarest locus in
a panel is identifiable from the `|u|` law alone. -/
theorem centeredSquare_homAlt_strictAnti (h h' : HardyWeinbergModel)
    (hq0 : 0 < h.altFreq) (hq1 : h.altFreq < 1)
    (hq0' : 0 < h'.altFreq) (hq1' : h'.altFreq < 1)
    (hrarer : h.altFreq < h'.altFreq) :
    h'.centeredSquare DiploidGenotype.homAlt <
      h.centeredSquare DiploidGenotype.homAlt := by
  rw [centeredSquare_homAlt_eq h hq0 hq1, centeredSquare_homAlt_eq h' hq0' hq1']
  rw [div_lt_div_iff₀ hq0' hq0]
  nlinarith [hq0, hq0', hrarer]

/-- **The rare-homozygote atom dominates the other two on the minor-allele range.**

At `q ≤ 1/2` every atom of a locus is at most `u_alt` in absolute value, with equality
only at the balanced locus, where all three coincide at `1` — the Rademacher case. This is
the other half of the peeling argument: the largest atom of a panel comes from the rarest
locus and from its rare homozygote. -/
theorem abs_centeredSquare_le_homAlt (h : HardyWeinbergModel)
    (hq0 : 0 < h.altFreq) (hhalf : h.altFreq ≤ 1 / 2) (g : DiploidGenotype) :
    |h.centeredSquare g| ≤ h.centeredSquare DiploidGenotype.homAlt := by
  have hq1 : h.altFreq < 1 := by linarith
  have hp : (0 : ℝ) < 1 - h.altFreq := by linarith
  obtain ⟨href, hhet, halt⟩ := standardizedSquare_values h hq0 hq1
  have haltval : h.centeredSquare DiploidGenotype.homAlt =
      (2 - 3 * h.altFreq) / h.altFreq := centeredSquare_homAlt_eq h hq0 hq1
  cases g with
  | homRef =>
      have hval : h.centeredSquare DiploidGenotype.homRef =
          (3 * h.altFreq - 1) / (1 - h.altFreq) := by
        rw [centeredSquare_eq_standardizedSquare_sub_one h hq0 hq1, href, div_sub_one (ne_of_gt hp)]
        congr 1
        ring
      rw [hval, haltval, abs_div, abs_of_pos hp, div_le_div_iff₀ hp hq0]
      rcases abs_cases (3 * h.altFreq - 1) with ⟨heq, _⟩ | ⟨heq, _⟩ <;> rw [heq] <;>
        nlinarith [hq0, hhalf, hp]
  | het =>
      have hval : h.centeredSquare DiploidGenotype.het =
          (1 - 6 * h.altFreq + 6 * h.altFreq ^ 2) /
            (2 * h.altFreq * (1 - h.altFreq)) := by
        have hden : 2 * h.altFreq * (1 - h.altFreq) ≠ 0 := by positivity
        rw [centeredSquare_eq_standardizedSquare_sub_one h hq0 hq1, hhet, div_sub_one hden]
        congr 1
        ring
      have hden : (0 : ℝ) < 2 * h.altFreq * (1 - h.altFreq) := by positivity
      rw [hval, haltval, abs_div, abs_of_pos hden, div_le_div_iff₀ hden hq0]
      rcases abs_cases (1 - 6 * h.altFreq + 6 * h.altFreq ^ 2) with
        ⟨heq, _⟩ | ⟨heq, _⟩ <;> rw [heq] <;>
        nlinarith [hq0, hhalf, hp, sq_nonneg (2 * h.altFreq - 1)]
  | homAlt =>
      have hnonneg : 0 ≤ h.centeredSquare DiploidGenotype.homAlt := by
        rw [haltval]
        apply div_nonneg _ hq0.le
        linarith
      rw [abs_of_nonneg hnonneg]

/-- **The rarest locus owns the strictly largest atom, alone.**

Every atom of a commoner locus is strictly smaller in absolute value than the rare
homozygote atom of a rarer one. So in a panel the largest `|u|` value identifies the
rarest frequency present, and the mass there involves that locus and no other — which
forces its weight, and by induction the whole spectrum.

This is the peeling step, and with it the matrix sending MAF weights to the `|u|` law has
trivial nullspace: **no fiber splitting exists over genotype panels**. -/
theorem rarest_locus_owns_largest_atom (h h' : HardyWeinbergModel)
    (hq0 : 0 < h.altFreq)
    (hq0' : 0 < h'.altFreq) (hhalf' : h'.altFreq ≤ 1 / 2)
    (hrarer : h.altFreq < h'.altFreq) (g : DiploidGenotype) :
    |h'.centeredSquare g| < h.centeredSquare DiploidGenotype.homAlt := by
  have hq1 : h.altFreq < 1 := by linarith
  have hq1' : h'.altFreq < 1 := by linarith
  calc |h'.centeredSquare g| ≤ h'.centeredSquare DiploidGenotype.homAlt :=
        abs_centeredSquare_le_homAlt h' hq0' hhalf' g
    _ < h.centeredSquare DiploidGenotype.homAlt :=
        centeredSquare_homAlt_strictAnti h h' hq0 hq1 hq0' hq1' hrarer

/-!
## 5m. Fiber surgery, the matched-order table, and the completeness/observability split

### The surgery, explicitly

The chameleon is built by moving mass inside the fibers of the square law about its
mean. For each `s ∈ (0,1)` the two preimages of `|u| = s` are the `x²` values `1 + s`
and `1 - s`, and a transfer moves mass from one to the other. Transferring unit mass
from `1-s` to `1+s` moves a moment by that moment's **profile**, and the profiles are
what the constraints are integrated against:

| profile | value | fixes |
|---|---|---|
| `varianceProfile s` | `(1+s) - (1-s) = 2s` | `E[x²]` |
| `fourthMomentProfile s` | `(1+s)² - (1-s)² = 4s` | `E[x⁴]` |
| `driftProfile s` | `log(1+s)(1+s) - log(1-s)(1-s)` | the floor-one drift |
| `jetProfile s` | `log²(1+s)(1+s) - log²(1-s)(1-s)` | the floor-one jet variance |

**The `4s` coincidence.** `fourthMomentProfile = 2 · varianceProfile` identically
(`fourthMomentProfile_eq_two_mul_varianceProfile`, one `ring` step), so a transfer
annihilating the variance profile annihilates the fourth-moment profile automatically.
Three imposed constraints buy four matched moments.

**Ledger question, ruled: it is genuinely one coincidence, used once.** The identity is
asked to do two things — free fourth-moment matching, and the death of `J₂⁰` — and
those are the *same equation in two vocabularies*. Writing `λ = log x²`, the table's
entries are `J_θ^j = ∫ λ^j e^{θλ} dω`, so `e^{θλ} = x^{2θ}` and

> `J₁⁰ = Δ E[x²]`,  `J₁¹ = Δ E[x² log x²]`,  `J₁² = Δ E[x² log²x²]`,  `J₂⁰ = Δ E[x⁴]`.

`J₂⁰ = 0` *is* fourth-moment matching, not a second consequence of it. The second use
needs nothing beyond the first, and `jProfile_two_zero_eq_two_mul_jProfile_one_zero`
records it as the identity `J₂⁰-profile = 2 · J₁⁰-profile` rather than as a remark.

So the four checkable zeros are three constraints plus one free rider:

| zero | is | status |
|---|---|---|
| `J₁⁰ = 0` | variance matched | imposed |
| `J₁¹ = 0` | drift matched | imposed |
| `J₁² = 0` | jet variance matched | imposed |
| `J₂⁰ = 0` | fourth moment matched | **free**, by the `4s` identity |

### Scope, in the signature and not only in prose

No `LadderObservability` record carries `CramerModulus` as a field with the blindness
input taken as a hypothesis at both laws: that would hold the blindness theorem itself as a
parameter. So the scope note is prose only: the general ladder-measurability claim
re-scopes to the smooth-modulus stratum and
the non-Cramér frontier is open. See §5l for why genotypes sit outside that scope. What
remains formalized below is the profile arithmetic, which needs no scope condition at all.

### The portable statement

The two halves belong in one theorem because that is the form in which the idea
travels. Tower Rigidity says the tower data — modulus data *and* odd parts — separates
laws. Blindness says no admissible experiment reads the odd parts. Put together:

> **there is an invariant that determines the object and is invisible to every
> admissible measurement of it**, and the gap between the two is exactly the
> fiber-splitting freedom.

Complete for objects, strictly incomplete for experiments. That shape is not special to
chaos theory — it is available to identifiability theory, to statistical decision
theory, and to any field with a complete invariant and a restricted measurement class.
-/

/-- The variance profile of a fiber transfer at `s`: `(1+s) - (1-s)`.

Empirical status: DERIVED. The first-moment displacement of moving unit mass between
the two preimages of `|u| = s`; no free parameter. -/
def varianceProfile (s : ℝ) : ℝ := (1 + s) - (1 - s)

/-- **varianceProfile pinned at a reference point.** No theorem in the corpus evaluated this
definition, so every body agreeing with it in sign and monotonicity was indistinguishable from
it. At all arguments equal to `1 / 2` it is `1`, which fixes the coefficients a one-sided bound
or an invariance leaves free. -/
theorem varianceProfile_at_reference_point :
    varianceProfile (1 / 2) = 1 := by
  unfold varianceProfile
  norm_num

/-- The fourth-moment profile of a fiber transfer at `s`: `(1+s)² - (1-s)²`.

Empirical status: DERIVED. As for `varianceProfile`, one order up; no free parameter. -/
def fourthMomentProfile (s : ℝ) : ℝ := (1 + s) ^ 2 - (1 - s) ^ 2

/-- **fourthMomentProfile pinned at a reference point.** No theorem in the corpus evaluated this
definition, so every body agreeing with it in sign and monotonicity was indistinguishable from
it. At all arguments equal to `1 / 2` it is `2`, which fixes the coefficients a one-sided bound
or an invariance leaves free. -/
theorem fourthMomentProfile_at_reference_point :
    fourthMomentProfile (1 / 2) = 2 := by
  unfold fourthMomentProfile
  norm_num

theorem varianceProfile_eq (s : ℝ) : varianceProfile s = 2 * s := by
  unfold varianceProfile
  ring

theorem fourthMomentProfile_eq (s : ℝ) : fourthMomentProfile s = 4 * s := by
  unfold fourthMomentProfile
  ring

/-- **The `4s` coincidence.** The fourth-moment profile is exactly twice the variance
profile, so one constraint kills both and fourth-moment matching is free. Without it the
hub channel would separate the pair and the dichotomy would close the other way. -/
theorem fourthMomentProfile_eq_two_mul_varianceProfile (s : ℝ) :
    fourthMomentProfile s = 2 * varianceProfile s := by
  unfold fourthMomentProfile varianceProfile
  ring

/-- The table entry `J_θ^j` as a profile in `s`: `log^j(1+s)(1+s)^θ - log^j(1-s)(1-s)^θ`,
the displacement of `∫ λ^j e^{θλ}` under a unit transfer at `s`, where `λ = log x²`.

Empirical status: DERIVED. The integrand of the matched-order table, with no free
parameter. -/
noncomputable def jProfile (tilt order : ℕ) (s : ℝ) : ℝ :=
  Real.log (1 + s) ^ order * (1 + s) ^ tilt -
    Real.log (1 - s) ^ order * (1 - s) ^ tilt

/-- At full tilt `Real.log (1 - s)` is Mathlib's junk `0`, so for any positive order the second
half of the profile vanishes and only the growing branch is reported.  The true profile
diverges there; every result above keeps `s` strictly inside the unit interval. -/
theorem jProfile_at_unit_argument_is_junk (tilt order : ℕ) :
    jProfile tilt (order + 1) 1 = Real.log 2 ^ (order + 1) * 2 ^ tilt := by
  unfold jProfile
  have hlog : Real.log (1 - (1 : ℝ)) = 0 := by norm_num
  rw [hlog, zero_pow (Nat.succ_ne_zero order)]
  norm_num


/-- `J₁⁰` is the variance profile: tilt one, order zero. -/
theorem jProfile_one_zero (s : ℝ) : jProfile 1 0 s = varianceProfile s := by
  unfold jProfile varianceProfile
  simp

/-- `J₂⁰` is the fourth-moment profile: tilt two, order zero. -/
theorem jProfile_two_zero (s : ℝ) : jProfile 2 0 s = fourthMomentProfile s := by
  unfold jProfile fourthMomentProfile
  simp

/-- **`J₂⁰` is twice `J₁⁰`, identically.** This is the `4s` coincidence in the table's
own vocabulary, and it is why the fourth zero costs nothing: the second use of the
identity needs nothing beyond the first. -/
theorem jProfile_two_zero_eq_two_mul_jProfile_one_zero (s : ℝ) :
    jProfile 2 0 s = 2 * jProfile 1 0 s := by
  rw [jProfile_two_zero, jProfile_one_zero, fourthMomentProfile_eq_two_mul_varianceProfile]

/-- A finite fiber splitting: signed masses at finitely many transfer locations. The
generic three-bump solution of the three constraints is the case `k = 3`. -/
structure FiberSplitting (k : ℕ) where
  /-- Where each transfer happens, inside `(0, 1)`. -/
  location : Fin k → ℝ
  /-- How much mass each transfer moves, signed. -/
  mass : Fin k → ℝ
  /-- Locations are interior, so both preimages are genuine points of the square law. -/
  location_pos : ∀ j, 0 < location j
  location_lt_one : ∀ j, location j < 1

/-- **The class is inhabited.**  A theorem quantified over an uninhabited structure is
true and empty: kernel-checked, clean axiom report, no content.  This is the witness that
makes the theorems below statements about something. -/
noncomputable def FiberSplitting.witness (k : ℕ) : FiberSplitting k where
  location := fun _ ↦ 1 / 2
  mass := fun _ ↦ 0
  location_pos := fun _ ↦ by norm_num
  location_lt_one := fun _ ↦ by norm_num

/-- The displacement a splitting produces in the moment whose profile is `profile`. -/
noncomputable def FiberSplitting.displacement {k : ℕ} (F : FiberSplitting k)
    (profile : ℝ → ℝ) : ℝ :=
  ∑ j, F.mass j * profile (F.location j)

/-- **Fourth-moment matching is free.** A splitting that matches the variance matches
the fourth moment, with no further constraint imposed — the `4s` identity, integrated.

This is `J₂⁰ = 0` as a consequence of `J₁⁰ = 0`, and it is the whole content of the
coincidence doing "double duty": one equation, two names. -/
theorem FiberSplitting.fourthMoment_free {k : ℕ} (F : FiberSplitting k)
    (hvariance : F.displacement varianceProfile = 0) :
    F.displacement fourthMomentProfile = 0 := by
  have hterm : ∀ j : Fin k,
      F.mass j * fourthMomentProfile (F.location j) =
        2 * (F.mass j * varianceProfile (F.location j)) := by
    intro j
    rw [fourthMomentProfile_eq_two_mul_varianceProfile]
    ring
  unfold FiberSplitting.displacement at hvariance ⊢
  simp_rw [hterm]
  rw [← Finset.mul_sum, hvariance, mul_zero]

/-! Ladder observability and rigidity are not exported as theorem parameters.  The explicit
fiber-splitting identities above remain proved; their global experimental interpretation
awaits a formal blindness theorem. -/

/-!
## 6. Where the whole development now stands

Six threads, each attached to a module that was already here. The middle column is what
the thread *claims* fails; the status column says whether this corpus proves it.

| thread | what is claimed to fail | proved here? | module |
|---|---|---|---|
| condensation | the Gaussian genotype surrogate above degree `log N / c(q)` | **no** — the boundary algebra is proved, the limit laws are BBM/BKL, and the degree is measured optimistic by up to `2.64x` on common variants | `ScoreDistribution` |
| jet barrier | every cumulant/moment diagnostic of Gaussianity | **no** — the barrier is absent; the lattice arithmetic is proved | `EpistasisAndNonAdditivity` |
| overlap spectrum | the Gaussian null for any design whose tested locus-sets share variants | **partly** — `sign_symmetry_does_not_license_disjoint_reduction` exhibits limiting fourth cumulant `6` inside the symmetric class; the maximal-spectrum claim is a conjecture | `EpistaticChaos` |
| local-to-global | bounded-radius coherence audits of summary statistics | yes | `LocalToGlobalCoherence` |
| hidden cones | any complete catalogue of loading-decay invariants | yes | `PCCorrectability` |
| latent collapse | the number of latent GxE mechanisms | yes | `GeneEnvironmentInterplay` |

The shared shape is worth naming, because it is the same shape each time: a quantity
that is routinely *estimated* turns out not to be a function of the observables at all,
and the honest replacement is a convention plus a theorem about what the convention
buys. That is the programme `Calibrator.Conventions` already states, and the three
proved rows extend it from constants to structural quantities. The first two rows are
where the programme is aimed, not where it has landed.
-/

/-- **The two-mechanism mixture is the corpus's convex-combination map.**

`LatentMechanismCollapse.twoMechanismMixture` weights the mechanism values
`2/10` and `9/10` by `w` and `1 - w`, which is `Conventions.convexMix` at those
two points. `spikeAndSlabVariance`, `averagePhaseInteraction` and
`ancestrySpecificEffect` are already tied to that map; this puts the mixture
used for latent-mechanism collapse in the same family, so a change to the
mixing convention in either file fails to compile rather than leaving two
mixtures that disagree about which weight goes with which point. -/
theorem twoMechanismMixture_eq_convexMix (w : ℝ) :
    twoMechanismMixture w = convexMix w (2 / 10) (9 / 10) := rfl

end Calibrator
