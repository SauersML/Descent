/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Init.Data.ULift
import Init.GrindInstances.Nat
import Init.GrindInstances.Ring.Fin
import Init.GrindInstances.Ring.Nat
import Init.Data.List.Nat.Pairwise
import Mathlib.Probability.CDF
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Descent.Core.Ratios
import Descent.Core.Population
import Descent.Core.Genome

open scoped InnerProductSpace
open InnerProductSpace

open MeasureTheory
open scoped ENNReal

namespace Descent.Foundations

/-- Unit interval as a subtype, used for Bernoulli probabilities. -/
abbrev UnitProb := Set.Icc (0 : ℝ) 1

namespace InformationTheoryBridge

/-- Bernoulli probability measure, from mathlib's canonical PMF construction. -/
noncomputable def bernoulliMeasure (p : NNReal) (hp : p ≤ 1) : Measure Bool :=
  (PMF.bernoulli p hp).toMeasure

/-- KL divergence between Bernoulli laws, via `InformationTheory.klDiv`. -/
noncomputable def bernoulliKL (p q : NNReal) (hp : p ≤ 1) (hq : q ≤ 1) : ENNReal :=
  InformationTheory.klDiv (bernoulliMeasure p hp) (bernoulliMeasure q hq)

@[simp] theorem bernoulliKL_self (p : NNReal) (hp : p ≤ 1) :
    bernoulliKL p p hp hp = 0 := by
  simp [bernoulliKL, bernoulliMeasure, PMF.bernoulli]

theorem bernoulliKL_eq_zero_iff (p q : NNReal) (hp : p ≤ 1) (hq : q ≤ 1)
    [IsFiniteMeasure (bernoulliMeasure p hp)] [IsFiniteMeasure (bernoulliMeasure q hq)] :
    bernoulliKL p q hp hq = 0 ↔
      bernoulliMeasure p hp = bernoulliMeasure q hq := by
  simpa [bernoulliKL] using
    (InformationTheory.klDiv_eq_zero_iff
      (μ := bernoulliMeasure p hp) (ν := bernoulliMeasure q hq))

/-- Coercion helper from `[0,1]` real probabilities to `NNReal`. -/
def unitProbToNNReal (p : UnitProb) : NNReal :=
  ⟨p.1, p.2.1⟩

lemma unitProbToNNReal_le_one (p : UnitProb) : unitProbToNNReal p ≤ 1 := by
  change (p.1 : ℝ) ≤ 1
  exact p.2.2

/-- KL divergence between Bernoulli laws parameterized by probabilities in `[0,1]`. -/
noncomputable def klBern (p q : UnitProb) : ENNReal :=
  bernoulliKL (unitProbToNNReal p) (unitProbToNNReal q)
    (unitProbToNNReal_le_one p) (unitProbToNNReal_le_one q)

/-- `klBern` is exactly `InformationTheory.klDiv` on Bernoulli measures. -/
theorem klBern_eq_klDiv (p q : UnitProb) :
    klBern p q =
      InformationTheory.klDiv
        (bernoulliMeasure (unitProbToNNReal p) (unitProbToNNReal_le_one p))
        (bernoulliMeasure (unitProbToNNReal q) (unitProbToNNReal_le_one q)) := by
  simp [klBern, bernoulliKL]

/-- Equivalent PMF-level view of `klBern` (via `toMeasure`). -/
theorem klBern_eq_klDiv_pmf (p q : UnitProb) :
    klBern p q =
      InformationTheory.klDiv
        ((PMF.bernoulli (unitProbToNNReal p) (unitProbToNNReal_le_one p)).toMeasure)
        ((PMF.bernoulli (unitProbToNNReal q) (unitProbToNNReal_le_one q)).toMeasure) := by
  simp [klBern, bernoulliKL, bernoulliMeasure, PMF.bernoulli]

end InformationTheoryBridge

/-!
=================================================================
## Part 0: Gaussian Measure Integrability
=================================================================

For any natural number n, the function x^n is integrable with respect to the
standard Gaussian measure. This is foundational for all L² projection arguments.
-/

/-- The standard Gaussian measure μ = N(0,1). -/
noncomputable def stdGaussianMeasure : MeasureTheory.Measure Real :=
  ProbabilityTheory.gaussianReal 0 1

/-- Polynomial function x^n. -/
def poly_n (n : Nat) (x : Real) : Real := x ^ n

/-- For any natural number n, x^n is integrable with respect to the standard Gaussian measure.

Mathlib already carries the finiteness of Gaussian moments as `memLp_id_gaussianReal`,
so nothing here re-derives it from the Gaussian density: the only step left is that
`|x| ^ n` dominates `x ^ n`, which is `abs_pow`. -/
theorem integrable_poly_n (n : Nat) : MeasureTheory.Integrable (poly_n n) stdGaussianMeasure := by
  unfold poly_n stdGaussianMeasure
  have hmem : MeasureTheory.MemLp (id : ℝ → ℝ) (n : ENNReal)
      (ProbabilityTheory.gaussianReal 0 1) := by
    simpa using ProbabilityTheory.memLp_id_gaussianReal (μ := 0) (v := 1) (n : NNReal)
  refine (hmem.integrable_norm_pow' (p := n)).mono'
    ((measurable_id.pow_const n).aestronglyMeasurable) ?_
  filter_upwards with x
  simp [Real.norm_eq_abs]

/-- x^2 is integrable with respect to the standard Gaussian measure. -/
theorem integrable_sq_gaussian : MeasureTheory.Integrable (fun x ↦ x ^ 2) stdGaussianMeasure := by
  apply integrable_poly_n 2

/-- x is integrable with respect to the standard Gaussian measure. -/
theorem integrable_id_gaussian : MeasureTheory.Integrable (fun x ↦ x) stdGaussianMeasure := by
  have h := integrable_poly_n 1
  unfold poly_n at h
  simp only [pow_one] at h
  exact h

/-- x^4 is integrable with respect to the standard Gaussian measure (useful for variance
    calculations). -/
theorem integrable_pow4_gaussian : MeasureTheory.Integrable (fun x ↦ x ^ 4) stdGaussianMeasure := by
  apply integrable_poly_n 4

/-! **`integrable_prod_mul` was deleted here.** It read

    theorem integrable_prod_mul ... [SigmaFinite μ] [SigmaFinite ν]
        (f) (g) (hf : Integrable f μ) (hg : Integrable g ν) :
        Integrable (fun p : X × Y ↦ f p.1 * g p.2) (μ.prod ν) :=
      hf.mul_prod hg

and was `MeasureTheory.Integrable.mul_prod` with the arguments moved around. A
scan of the kernel-accepted proof terms found both `SigmaFinite` instances
unused, which is the tell: the upstream lemma does not need them, so the two
instance binders were narrowing the corpus's copy below the general statement
for no reason -- exactly the failure mode the `mathlib` guard exists to catch.
Nothing in the corpus referenced it. Use `Integrable.mul_prod` directly. -/

/-!
=================================================================
## Part 1: Definitions
=================================================================
-/

variable {Ω : Type*} [MeasureSpace Ω] {ℙ : Measure Ω} [IsProbabilityMeasure ℙ]


/-! ### Discrete Genotypes, Hardy-Weinberg Equilibrium, and Score Approximation

This block replaces the "score is Gaussian by assumption" shortcut with a discrete
genotype model. Each locus is diploid with genotype in `{0, 1, 2}` alternative alleles.
Hardy-Weinberg equilibrium determines the one-locus genotype law, and polygenic scores
are finite weighted sums of these bounded random variables.

The Gaussian score formulas are then interpreted as approximations with an explicit
Berry-Esseen-style error term rather than as exact biology.
-/

/-- **A diploid genotype at a biallelic locus** -- `Descent.Core.Genotype`, under the name
this module introduced it with.

The type used to be declared here, with its own `Fin 3` equivalence and sum expansion, and
two other encodings of a genotype existed elsewhere with nothing shared between them.  It
now lives at the bottom of the import graph, in `Core/Genome`, beside the alleles a
genotype is made of and the panel it is measured in; `DiploidGenotype` stays as a reducible
abbreviation so the name this module's statements are written in still reads.

The constructors and the equivalence are reached under the type's own name --
`Descent.Core.Genotype.homRef`, `Descent.Core.Genotype.equivFin3` -- because Lean resolves a
dotted NAME against the literal namespace and does not unfold an abbreviation to find it. -/
abbrev DiploidGenotype := Descent.Core.Genotype

/-- **A sum over genotypes is its three terms.**

Every closed form at a Hardy-Weinberg locus is proved by expanding this sum, and the
expansion was written out separately at each site — routed through `equivFin3` and
`Fin.sum_univ_three` by hand in `genotypeVariance_eq`, again as a `private` lemma in
`EpistaticChaos`, and again wherever else a moment was computed. A private copy is not
reusable by construction, so the third and fourth sites had no choice but to repeat it.

It belongs here, beside the equivalence it uses and above every module that computes a
genotype moment. -/
theorem sum_over_genotypes (f : DiploidGenotype → ℝ) :
    (∑ g : DiploidGenotype, f g) =
      f Descent.Core.Genotype.homRef + f Descent.Core.Genotype.het
        + f Descent.Core.Genotype.homAlt :=
  Descent.Core.Genotype.sum_univ f

/-- Number of alternative alleles carried by a diploid genotype.

    Empirical status: NOT AN EMPIRICAL CLAIM. This is the corpus's genotype
    CODING, `0/1/2` for the three diploid genotypes, and a coding cannot
    disagree with a population: it fixes what the symbol `dosage` denotes
    everywhere downstream. What is empirical is what the coding buys, and that
    is tested where it is used -- `BlindnessRegistry.averageEffect` is the
    least-squares slope of genotypic value on THIS dosage, and a different
    coding would move that slope. -/
def altAlleleCount : DiploidGenotype → ℝ := Descent.Core.Genotype.dosage

/-- One-locus Hardy-Weinberg model with alternative-allele frequency `q ∈ [0,1]`. -/
structure HardyWeinbergModel where
  altFreq : ℝ
  altFreq_nonneg : 0 ≤ altFreq
  altFreq_le_one : altFreq ≤ 1

/-- **The class is inhabited.**  A theorem quantified over an uninhabited structure is
true and empty: kernel-checked, clean axiom report, no content.  This is the witness that
makes the theorems below statements about something. -/
noncomputable def HardyWeinbergModel.witness : HardyWeinbergModel where
  altFreq := 1 / 2
  altFreq_nonneg := by norm_num
  altFreq_le_one := by norm_num

/-- Reference-allele frequency `p = 1 - q`. -/
def HardyWeinbergModel.refFreq (h : HardyWeinbergModel) : ℝ :=
  1 - h.altFreq

/-- **The two allele frequencies sum to one.** Nonnegativity is shared by every body bounded
below by zero; this is the identity that makes it the complementary frequency. -/
theorem HardyWeinbergModel.refFreq_add_altFreq (h : HardyWeinbergModel) :
    h.refFreq + h.altFreq = 1 := by
  unfold HardyWeinbergModel.refFreq
  ring

theorem HardyWeinbergModel.refFreq_nonneg (h : HardyWeinbergModel) :
    0 ≤ h.refFreq := by
  unfold HardyWeinbergModel.refFreq
  linarith [h.altFreq_le_one]

theorem HardyWeinbergModel.refFreq_le_one (h : HardyWeinbergModel) :
    h.refFreq ≤ 1 := by
  unfold HardyWeinbergModel.refFreq
  linarith [h.altFreq_nonneg]

/-- Hardy-Weinberg genotype probabilities:
`P(AA) = p^2`, `P(Aa) = 2pq`, `P(aa) = q^2`, where `q` is the alternative-allele frequency.

    Regime: random union of gametes -- random mating, no selection, no
    inbreeding, one generation. Those are the assumptions the factor of two
    rests on, not decoration.

    Empirical status: **VALIDATED** (`simcov/battery_bulk28.py`, `group_a`).
    Gametes are paired at random and genotypes are COUNTED; the body is never
    evaluated to build the oracle. Over `p` = 0.05, 0.2, 0.5, 0.8, across all
    three genotypes, the worst cell is 1.20 sems at 0.02% relative on 4×10⁶
    individuals per cell.

    Power: the heterozygote term without its factor of two -- the classic
    error, and the one a table of counts settles instantly -- is carried on the
    same cells and is FALSIFIED at 1000 sems (50% relative). An oracle pinned
    to the body could not reject it, so the factor of two is chosen by the
    counts. Control: the realised allele frequency recovers `p` on the same
    draws. -/
def HardyWeinbergModel.genotypeProb (h : HardyWeinbergModel) : DiploidGenotype → ℝ
  | .homRef => h.refFreq ^ 2
  | .het => 2 * h.refFreq * h.altFreq
  | .homAlt => h.altFreq ^ 2

theorem HardyWeinbergModel.genotypeProb_nonneg
    (h : HardyWeinbergModel) (g : DiploidGenotype) :
    0 ≤ h.genotypeProb g := by
  cases g with
  | homRef =>
      simp [HardyWeinbergModel.genotypeProb, sq_nonneg]
  | het =>
      simp [HardyWeinbergModel.genotypeProb]
      nlinarith [h.refFreq_nonneg, h.altFreq_nonneg]
  | homAlt =>
      simp [HardyWeinbergModel.genotypeProb, sq_nonneg]

/-- Hardy-Weinberg genotype probabilities sum to `1`. -/
theorem HardyWeinbergModel.genotypeProb_sum (h : HardyWeinbergModel) :
    (∑ g : DiploidGenotype, h.genotypeProb g) = 1 := by
  have hsum : h.refFreq + h.altFreq = 1 := by
    unfold HardyWeinbergModel.refFreq
    ring
  have hrewrite :
      (∑ g : DiploidGenotype, h.genotypeProb g) =
        ∑ i : Fin 3, h.genotypeProb (Descent.Core.Genotype.equivFin3.symm i) :=
    Fintype.sum_equiv Descent.Core.Genotype.equivFin3 _ _ (by
      intro x
      rw [Descent.Core.Genotype.equivFin3_symm_apply_apply])
  rw [hrewrite]
  rw [Fin.sum_univ_three]
  simp [Descent.Core.Genotype.equivFin3, HardyWeinbergModel.genotypeProb]
  calc
    h.refFreq ^ 2 + 2 * h.refFreq * h.altFreq + h.altFreq ^ 2
        = (h.refFreq + h.altFreq) ^ 2 := by ring
    _ = 1 := by rw [hsum]; norm_num

/-- Expected alternative-allele count under Hardy-Weinberg equilibrium.

    Empirical status: **VALIDATED**
    (`validation/empirical/simcov/battery_linalg.py`,
    `test_hwe_moments`). Two million Hardy-Weinberg genotypes per cell, worst
    1.1 sems over a prediction spanning 0.20000 to 1.00000. -/
noncomputable def HardyWeinbergModel.expectedAltAlleleCount (h : HardyWeinbergModel) : ℝ :=
  ∑ g : DiploidGenotype, altAlleleCount g * h.genotypeProb g

theorem HardyWeinbergModel.expectedAltAlleleCount_eq
    (h : HardyWeinbergModel) :
    h.expectedAltAlleleCount = 2 * h.altFreq := by
  have hsum : h.refFreq + h.altFreq = 1 := by
    unfold HardyWeinbergModel.refFreq
    ring
  unfold HardyWeinbergModel.expectedAltAlleleCount
  have hrewrite :
      (∑ g : DiploidGenotype, altAlleleCount g * h.genotypeProb g) =
        ∑ i : Fin 3, altAlleleCount (Descent.Core.Genotype.equivFin3.symm i) *
          h.genotypeProb (Descent.Core.Genotype.equivFin3.symm i) :=
    Fintype.sum_equiv Descent.Core.Genotype.equivFin3 _ _ (by
      intro x
      rw [Descent.Core.Genotype.equivFin3_symm_apply_apply])
  rw [hrewrite]
  rw [Fin.sum_univ_three]
  simp [Descent.Core.Genotype.equivFin3, HardyWeinbergModel.genotypeProb]
  calc
    altAlleleCount Descent.Core.Genotype.homRef * h.refFreq ^ 2 +
        altAlleleCount Descent.Core.Genotype.het * (2 * h.refFreq * h.altFreq) +
        altAlleleCount Descent.Core.Genotype.homAlt * h.altFreq ^ 2
        = 2 * (h.refFreq * h.altFreq) + 2 * h.altFreq ^ 2 := by
          simp [altAlleleCount, Descent.Core.Genotype.dosage]
          ring
    _ 
        = 2 * h.altFreq * (h.refFreq + h.altFreq) := by ring
    _ = 2 * h.altFreq := by rw [hsum]; ring

/-- Centered alternative-allele count at one locus.

    Empirical status: NOT AN EMPIRICAL CLAIM. Subtracting a quantity's own
    expectation is centering, and centering is an operation rather than a
    prediction: it has no free coefficient a measurement could find wrong. The
    empirical content sits one level down, in `expectedAltAlleleCount = 2q`,
    which is the Hardy-Weinberg claim and is proved against `genotypeProb`
    immediately above. -/
noncomputable def HardyWeinbergModel.centeredAltAlleleCount
    (h : HardyWeinbergModel) (g : DiploidGenotype) : ℝ :=
  altAlleleCount g - h.expectedAltAlleleCount

/-- One-locus genotype variance under Hardy-Weinberg equilibrium.

    Empirical status: **VALIDATED**
    (`validation/empirical/simcov/battery_linalg.py`,
    `test_hwe_moments`). Two million Hardy-Weinberg genotypes per cell, worst
    1.0 sems over a prediction spanning 0.18000 to 0.50000. -/
noncomputable def HardyWeinbergModel.genotypeVariance (h : HardyWeinbergModel) : ℝ :=
  ∑ g : DiploidGenotype,
    h.genotypeProb g * (h.centeredAltAlleleCount g) ^ 2

theorem HardyWeinbergModel.genotypeVariance_eq
    (h : HardyWeinbergModel) :
    h.genotypeVariance = 2 * h.altFreq * h.refFreq := by
  have hsum : h.refFreq + h.altFreq = 1 := by
    unfold HardyWeinbergModel.refFreq
    ring
  unfold HardyWeinbergModel.genotypeVariance HardyWeinbergModel.centeredAltAlleleCount
  rw [h.expectedAltAlleleCount_eq, sum_over_genotypes]
  -- `altAlleleCount` now delegates to `Core.Genotype.dosage`, so unfolding the
  -- wrapper alone leaves the coding unexpanded and the arithmetic unfinished.
  -- The THREE EQUATION LEMMAS, not the definition: `dosage` is defined by cases
  -- on the constructor, and `simp only [dosage]` does not reduce it applied to
  -- one -- it left `Core.Genotype.homRef.dosage` standing in the goal and the
  -- `ring_nf` below had nothing to close. `dosage_homRef`/`_het`/`_homAlt` are
  -- the `rfl` lemmas declared beside the definition for exactly this.
  simp only [HardyWeinbergModel.genotypeProb, altAlleleCount,
    Descent.Core.Genotype.dosage_homRef, Descent.Core.Genotype.dosage_het,
    Descent.Core.Genotype.dosage_homAlt, HardyWeinbergModel.refFreq]
  ring_nf

/-- **A polymorphic locus has positive genotype variance.**

Ten proofs across `StandardizedGenotypeMoments` and `EpistaticChaos` opened by deriving this
from `genotypeVariance_eq` in the same four lines.  It is one fact about the model and it is
named here, beside the identity it comes from. -/
theorem HardyWeinbergModel.genotypeVariance_pos
    (h : HardyWeinbergModel) (hq0 : 0 < h.altFreq) (hq1 : h.altFreq < 1) :
    0 < h.genotypeVariance := by
  rw [h.genotypeVariance_eq]
  unfold HardyWeinbergModel.refFreq
  have hcomp : (0 : ℝ) < 1 - h.altFreq := by linarith
  nlinarith [hq0, hcomp]

/-- Absolute third centered moment at one Hardy-Weinberg locus. This is the term that
enters the Berry-Esseen numerator for weighted sums of bounded genotype variables.

    Empirical status: **VALIDATED**
    (`validation/empirical/simcov/battery_linalg.py`,
    `test_hwe_moments`). Two million Hardy-Weinberg genotypes per cell, worst
    1.0 sems over a prediction spanning 0.15696 to 0.50000. The third ABSOLUTE
    moment is not the third central moment: the latter vanishes at `p = 1/2`
    and this does not, which is what the design at `p = 0.5` checks. -/
noncomputable def HardyWeinbergModel.genotypeThirdAbsMoment
    (h : HardyWeinbergModel) : ℝ :=
  ∑ g : DiploidGenotype,
    h.genotypeProb g * |h.centeredAltAlleleCount g| ^ 3

theorem HardyWeinbergModel.genotypeThirdAbsMoment_nonneg
    (h : HardyWeinbergModel) :
    0 ≤ h.genotypeThirdAbsMoment := by
  unfold HardyWeinbergModel.genotypeThirdAbsMoment
  refine Finset.sum_nonneg ?_
  intro g _
  exact mul_nonneg (h.genotypeProb_nonneg g) (by positivity)


/-- Locuswise Hardy-Weinberg panel for a polygenic score architecture. -/
structure HWEScoreModel (m : ℕ) where
  alleleFreq : Fin m → HardyWeinbergModel
  effect : Fin m → ℝ

/-- **The equal-locus panel**: `m` loci sharing one allele frequency and one
effect size. This is the standard reference architecture -- equal effects at
equal frequency -- and it is the inhabitant `HWEScoreModel` previously lacked,
so the Berry-Esseen results stated over the class now have a family they apply
to rather than a possibly-empty domain.

It is a family rather than a fixed witness on purpose: the frequency and the
effect stay free, so the theorems below hold across the whole one-parameter
architecture instead of at one point of it.

    Empirical status: NOT AN EMPIRICAL CLAIM -- a labelling of `m` copies of a
    supplied one-locus model, with no free parameter of its own and nothing a
    measurement could disagree with. The one-locus model it repeats carries its
    own status. -/
def HWEScoreModel.uniform {m : ℕ} (freq : HardyWeinbergModel) (effect : ℝ) :
    HWEScoreModel m where
  alleleFreq := fun _ ↦ freq
  effect := fun _ ↦ effect

instance HWEScoreModel.instNonempty (m : ℕ) : Nonempty (HWEScoreModel m) :=
  ⟨HWEScoreModel.uniform HardyWeinbergModel.witness 0⟩

/-- Exact HWE score mean from one-locus expectations. -/
noncomputable def HWEScoreModel.scoreMean {m : ℕ} [Fintype (Fin m)]
    (model : HWEScoreModel m) : ℝ :=
  ∑ i : Fin m, model.effect i * (model.alleleFreq i).expectedAltAlleleCount

/-- Exact HWE score variance under locus independence. -/
noncomputable def HWEScoreModel.scoreVariance {m : ℕ} [Fintype (Fin m)]
    (model : HWEScoreModel m) : ℝ :=
  ∑ i : Fin m, (model.effect i) ^ 2 * (model.alleleFreq i).genotypeVariance

/-- **The equal-locus panel's score mean is `m β · 2q`.** Means add across loci
exactly as variances do, so both moments of the reference architecture are linear
in the locus count -- which is why the score's standard deviation grows like `√m`
while its mean grows like `m`, and why a polygenic score has to be standardized
before populations are compared.

As with `scoreVariance_uniform` the locus count appears as `Fintype.card (Fin m)`
because this file carries `[Fintype (Fin m)]` as an instance binder. -/
theorem HWEScoreModel.scoreMean_uniform {m : ℕ} [Fintype (Fin m)]
    (freq : HardyWeinbergModel) (effect : ℝ) :
    (HWEScoreModel.uniform (m := m) freq effect).scoreMean =
      Fintype.card (Fin m) * (effect * freq.expectedAltAlleleCount) := by
  have hbody : ∀ i : Fin m,
      (HWEScoreModel.uniform (m := m) freq effect).effect i *
          ((HWEScoreModel.uniform (m := m) freq effect).alleleFreq i).expectedAltAlleleCount =
        effect * freq.expectedAltAlleleCount := fun _ ↦ rfl
  unfold HWEScoreModel.scoreMean
  rw [Finset.sum_congr rfl (fun i _ ↦ hbody i), Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul]

/-- Berry-Esseen numerator for the weighted HWE score under locus independence. -/
noncomputable def HWEScoreModel.scoreThirdAbsMomentBound {m : ℕ} [Fintype (Fin m)]
    (model : HWEScoreModel m) : ℝ :=
  ∑ i : Fin m, |model.effect i| ^ 3 * (model.alleleFreq i).genotypeThirdAbsMoment

/-- **The equal-locus panel's score variance is `m β² · 2q(1-q)`**: variance adds
across independent loci, so it is linear in the locus count at fixed per-locus
contribution.

This is what makes `scoreVariance_nonneg` and the Berry-Esseen bound above
non-vacuous rather than merely well-typed, and it is the exact statement the
`√m` in a polygenic score's standard deviation comes from.

The locus count appears as `Fintype.card (Fin m)` rather than as `m` on purpose.
This file carries `[Fintype (Fin m)]` as an instance BINDER, so the instance in
scope is not syntactically Lean's canonical `Fin.fintype`, and `Fintype.card_fin`
does not apply to it. Writing the cardinality of the panel's own index type says
what is meant and needs no appeal to which instance was supplied; it is `m` under
the standard one. -/
theorem HWEScoreModel.scoreVariance_uniform {m : ℕ} [Fintype (Fin m)]
    (freq : HardyWeinbergModel) (effect : ℝ) :
    (HWEScoreModel.uniform (m := m) freq effect).scoreVariance =
      Fintype.card (Fin m) * (effect ^ 2 * freq.genotypeVariance) := by
  have hbody : ∀ i : Fin m,
      (HWEScoreModel.uniform (m := m) freq effect).effect i ^ 2 *
          ((HWEScoreModel.uniform (m := m) freq effect).alleleFreq i).genotypeVariance =
        effect ^ 2 * freq.genotypeVariance := fun _ ↦ rfl
  unfold HWEScoreModel.scoreVariance
  rw [Finset.sum_congr rfl (fun i _ ↦ hbody i), Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul]

theorem HWEScoreModel.scoreVariance_nonneg {m : ℕ} [Fintype (Fin m)]
    (model : HWEScoreModel m) :
    0 ≤ model.scoreVariance := by
  unfold HWEScoreModel.scoreVariance
  refine Finset.sum_nonneg ?_
  intro i _
  have hvar_nonneg : 0 ≤ (model.alleleFreq i).genotypeVariance := by
    rw [(model.alleleFreq i).genotypeVariance_eq]
    exact mul_nonneg (mul_nonneg (by norm_num) (model.alleleFreq i).altFreq_nonneg)
      ((model.alleleFreq i).refFreq_nonneg)
  exact mul_nonneg (sq_nonneg (model.effect i)) hvar_nonneg

theorem HWEScoreModel.scoreThirdAbsMomentBound_nonneg {m : ℕ} [Fintype (Fin m)]
    (model : HWEScoreModel m) :
    0 ≤ model.scoreThirdAbsMomentBound := by
  unfold HWEScoreModel.scoreThirdAbsMomentBound
  refine Finset.sum_nonneg ?_
  intro i _
  exact mul_nonneg (by positivity)
    ((model.alleleFreq i).genotypeThirdAbsMoment_nonneg)

/-- Berry-Esseen error term for a centered score with variance `σ²` and third-moment sum `ρ₃`.
We write the denominator as `σ² * sqrt(σ²)` to stay inside the existing real-analysis library. -/
noncomputable def berryEsseenErrorBound (berryEsseenConstant variance thirdMomentSum : ℝ) : ℝ :=
  berryEsseenConstant * thirdMomentSum / (variance * Real.sqrt variance)

/-- **berryEsseenErrorBound at zero variance, named.** With zero variance the standardised sum is
not defined and the Berry-Esseen bound does not apply. Lean returns `0`: a normal approximation
certified as exact where the central limit theorem has no content. An error bound that vanishes
where the approximation is meaningless certifies rather than warns. Consumers must require
`variance ≠ 0`. -/
theorem berryEsseenErrorBound_zero_variance_is_junk (berryEsseenConstant : ℝ) (thirdMomentSum : ℝ) :
    berryEsseenErrorBound berryEsseenConstant 0 thirdMomentSum = 0 := by
  unfold berryEsseenErrorBound
  simp

theorem berryEsseenErrorBound_nonneg
    (berryEsseenConstant variance thirdMomentSum : ℝ)
    (hC : 0 ≤ berryEsseenConstant)
    (hVar : 0 ≤ variance)
    (hThird : 0 ≤ thirdMomentSum) :
    0 ≤ berryEsseenErrorBound berryEsseenConstant variance thirdMomentSum := by
  unfold berryEsseenErrorBound
  by_cases hzero : variance * Real.sqrt variance = 0
  · simp [hzero]
  · exact div_nonneg (mul_nonneg hC hThird) (mul_nonneg hVar (Real.sqrt_nonneg _))

/-- Berry-Esseen error bound specialized to the HWE score model. -/
noncomputable def HWEScoreModel.berryEsseenErrorBound {m : ℕ} [Fintype (Fin m)]
    (model : HWEScoreModel m) (berryEsseenConstant : ℝ) : ℝ :=
  Descent.Foundations.berryEsseenErrorBound
    berryEsseenConstant model.scoreVariance model.scoreThirdAbsMomentBound

theorem HWEScoreModel.berryEsseenErrorBound_nonneg {m : ℕ} [Fintype (Fin m)]
    (model : HWEScoreModel m) (berryEsseenConstant : ℝ)
    (hC : 0 ≤ berryEsseenConstant) :
    0 ≤ model.berryEsseenErrorBound berryEsseenConstant :=
  Descent.Foundations.berryEsseenErrorBound_nonneg
    berryEsseenConstant model.scoreVariance model.scoreThirdAbsMomentBound
    hC (model.scoreVariance_nonneg) (model.scoreThirdAbsMomentBound_nonneg)

/-- Closed interval of values consistent with an approximation center and error radius. -/
def approximationInterval (center epsilon : ℝ) : Set ℝ :=
  Set.Icc (center - epsilon) (center + epsilon)

/-- Any quantity within absolute error `ε` belongs to the corresponding approximation interval. -/
theorem mem_approximationInterval_of_abs_sub_le
    (x center epsilon : ℝ)
    (h : |x - center| ≤ epsilon) :
    x ∈ approximationInterval center epsilon := by
  unfold approximationInterval
  constructor <;> linarith [abs_le.mp h |>.1, abs_le.mp h |>.2]

/-! `aucApproximationInterval` and `r2ApproximationInterval` used to sit here as two names for
`approximationInterval`. They are removed: identical bodies under different names meant that
nothing in any statement using them would detect swapping AUC for `R²`, which is precisely the
distinction the names were there to make. Callers use `approximationInterval` and say in their
own statement which functional they mean. -/

noncomputable def stdNormalProdMeasure (k : ℕ) [Fintype (Fin k)] : Measure (ℝ × (Fin k → ℝ)) :=
  (ProbabilityTheory.gaussianReal 0 1).prod (Measure.pi (fun (_ : Fin k) ↦
      ProbabilityTheory.gaussianReal 0 1))

instance stdNormalProdMeasure_is_prob {k : ℕ} [Fintype (Fin
    k)] : IsProbabilityMeasure (stdNormalProdMeasure k) := by
  unfold stdNormalProdMeasure
  infer_instance

/-! ### Measure-Theoretic Environment and Gaussian Noise

This block sets up a canonical random-variable environment for disease modeling:
- `Ω_k = ℝ × ℝ^k × ℝ`, with coordinates `(S, x, E)`
- `S`: score coordinate, interpreted either as an exact score or as a Gaussian approximation center
- `x`: principal-component coordinates
- `E`: environmental noise

The key assumption is heteroscedastic Gaussian noise:
`E | x ~ N(0, σ²(x))`.
Integrating out `E` then yields conditional probabilities through Gaussian CDFs (`Φ`). -/


/-- Standard normal CDF, written as `Φ`. -/
noncomputable def Phi : ℝ → ℝ := ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1)

/-- **`Φ` is strictly monotone.**

`Φ` is not an opaque function: it is the CDF of `gaussianReal 0 1`, so this is a theorem,
not an assumption. Carrying it as a hypothesis `hPhiStrict : StrictMono Phi` — which 27
sites across seven files would otherwise need — makes every theorem downstream of an AUC
or threshold chart conditional on a fact the corpus simply has. This theorem discharges
all of them.

The argument: `Φ b - Φ a` is the Gaussian mass of `Ioc a b`, and the Gaussian measure
gives positive mass to every nonempty interval because Lebesgue measure is absolutely
continuous with respect to it (`gaussianReal_absolutelyContinuous'`, which holds because
the Gaussian density is everywhere positive). Finiteness of a probability measure then
carries the strict inequality through `ENNReal.toReal`. -/
theorem strictMono_Phi : StrictMono Phi := by
  intro a b hab
  have hv : (1 : NNReal) ≠ 0 := one_ne_zero
  have hpos : 0 < (ProbabilityTheory.gaussianReal 0 1) (Set.Ioc a b) := by
    rw [pos_iff_ne_zero]
    intro h0
    have hac : (volume : Measure ℝ) ≪ ProbabilityTheory.gaussianReal 0 1 :=
      ProbabilityTheory.gaussianReal_absolutelyContinuous' 0 hv
    have hvol : (volume : Measure ℝ) (Set.Ioc a b) = 0 := hac h0
    rw [Real.volume_Ioc] at hvol
    have hba : (0 : ℝ) < b - a := by linarith
    exact (ENNReal.ofReal_pos.mpr hba).ne' hvol
  have hsplit :
      (ProbabilityTheory.gaussianReal 0 1) (Set.Iic b)
        = (ProbabilityTheory.gaussianReal 0 1) (Set.Iic a)
          + (ProbabilityTheory.gaussianReal 0 1) (Set.Ioc a b) := by
    rw [← measure_union (Set.Iic_disjoint_Ioc le_rfl) measurableSet_Ioc,
      Set.Iic_union_Ioc_eq_Iic hab.le]
  have hlt :
      (ProbabilityTheory.gaussianReal 0 1) (Set.Iic a)
        < (ProbabilityTheory.gaussianReal 0 1) (Set.Iic b) := by
    rw [hsplit]
    exact ENNReal.lt_add_right (measure_ne_top _ _) hpos.ne'
  show Phi a < Phi b
  unfold Phi
  rw [ProbabilityTheory.cdf_eq_real, ProbabilityTheory.cdf_eq_real,
    measureReal_def, measureReal_def]
  exact ENNReal.toReal_lt_toReal (measure_ne_top _ _) (measure_ne_top _ _) |>.mpr hlt

/-- Monotonicity of `Phi`, the weak corollary of `strictMono_Phi`.  It lives here, beside the
strict form it follows from, rather than being restated in each file that uses it. -/
theorem Phi_monotone : Monotone Phi := strictMono_Phi.monotone

/-- Heteroscedastic Gaussian noise assumption:
for each ancestry coordinate `x`, the environmental noise follows `N(0, σ²(x))`. -/
structure GaussianNoiseAssumption (k : ℕ) where
  sigma2 : (Fin k → ℝ) → NNReal

/-- **The homoscedastic assumption inside the heteroscedastic class**: one noise
variance at every ancestry coordinate.

`GaussianNoiseAssumption` is stated heteroscedastically -- `σ²` is a function of
`x` -- which is the generality the portability results need, and which also
means the class had no exhibited member. This is the member every classical
model uses, and naming it here says which specialisation the general results
are a generalisation OF. The variance is left free, so it is the whole
homoscedastic family and not one point of it.

    Empirical status: NOT AN EMPIRICAL CLAIM -- a constant function. The claim
    with content is that a real population is homoscedastic in ancestry, which
    this does not assert and the surrounding results deliberately do not
    assume. -/
def GaussianNoiseAssumption.homoscedastic {k : ℕ} (sigma2 : NNReal) :
    GaussianNoiseAssumption k where
  sigma2 := fun _ ↦ sigma2

instance GaussianNoiseAssumption.instNonempty (k : ℕ) :
    Nonempty (GaussianNoiseAssumption k) :=
  ⟨GaussianNoiseAssumption.homoscedastic 1⟩

/-- Conditional noise law `E | x`. -/
noncomputable def noiseMeasureGivenX {k : ℕ}
    (hN : GaussianNoiseAssumption k) (x : Fin k → ℝ) : Measure ℝ :=
  ProbabilityTheory.gaussianReal 0 (hN.sigma2 x)

instance noiseMeasureGivenX_isProb {k : ℕ}
    (hN : GaussianNoiseAssumption k) (x : Fin k → ℝ) :
    IsProbabilityMeasure (noiseMeasureGivenX hN x) := by
  unfold noiseMeasureGivenX
  infer_instance

/-- The homoscedastic member is exactly the one whose noise law does not move
with ancestry, which is the property the heteroscedastic results are stated so
as not to assume. -/
theorem noiseMeasureGivenX_homoscedastic {k : ℕ} (sigma2 : NNReal)
    (x y : Fin k → ℝ) :
    noiseMeasureGivenX (GaussianNoiseAssumption.homoscedastic (k := k) sigma2) x =
      noiseMeasureGivenX (GaussianNoiseAssumption.homoscedastic (k := k) sigma2) y :=
  rfl

/-- Integrating out Gaussian environmental noise gives a Gaussian CDF at threshold `t`:
`P(μ + E ≤ t | x) = CDF_{N(μ,σ²(x))}(t)`. -/
theorem noise_integrated_cdf {k : ℕ} (hN : GaussianNoiseAssumption k)
    (x : Fin k → ℝ) (μ t : ℝ) :
    noiseMeasureGivenX hN x {e : ℝ | μ + e ≤ t} =
      ENNReal.ofReal (ProbabilityTheory.cdf
        (ProbabilityTheory.gaussianReal μ (hN.sigma2 x)) t) := by
  calc
    noiseMeasureGivenX hN x {e : ℝ | μ + e ≤ t}
        = ((noiseMeasureGivenX hN x).map (fun e : ℝ ↦ μ + e)) (Set.Iic t) := by
            rw [Measure.map_apply (by fun_prop) measurableSet_Iic]
            rfl
    _ = (ProbabilityTheory.gaussianReal μ (hN.sigma2 x)) (Set.Iic t) := by
          simp [noiseMeasureGivenX, ProbabilityTheory.gaussianReal_map_const_add]
    _ = ENNReal.ofReal (ProbabilityTheory.cdf
          (ProbabilityTheory.gaussianReal μ (hN.sigma2 x)) t) := by
          symm
          simpa using (ProbabilityTheory.ofReal_cdf
            (μ := ProbabilityTheory.gaussianReal μ (hN.sigma2 x)) t)

/-- In particular at threshold `0`, integrating out `E` yields a probit-form conditional
    probability. -/
theorem noise_integrated_cdf_zero {k : ℕ} (hN : GaussianNoiseAssumption k)
    (x : Fin k → ℝ) (μ : ℝ) :
    noiseMeasureGivenX hN x {e : ℝ | μ + e ≤ 0} =
      ENNReal.ofReal (ProbabilityTheory.cdf
        (ProbabilityTheory.gaussianReal μ (hN.sigma2 x)) 0) := by
  simpa using noise_integrated_cdf hN x μ 0

/-! ### Biological Truth: Liability Threshold Model -/

/-- Latent liability `L = S + E`.

    Empirical status: NOT AN EMPIRICAL CLAIM. This is the DECLARATION of the
    liability-threshold model's additive decomposition, and the definition of
    what the symbols `S` and `E` mean in the rest of this file. Whether real
    liability is additive in a genetic and an environmental part is an empirical
    question, but it is not a question about this body: any answer leaves
    `s + e` as the definition of the sum. The testable consequences live in the
    threshold quantities built on it -- `etaLiabilityThreshold`, the prevalence
    and the observed-scale `R²` -- where a wrong decomposition would show. -/
noncomputable def latentLiability (s e : ℝ) : ℝ :=
  Descent.Core.sum s e

/-- **Liability is additive, so the genetic part is recoverable given the environment.** This is
what makes the threshold model identifiable at all, and it is the decomposition a body carrying
an interaction term would break. -/
theorem latentLiability_sub_environment (s e : ℝ) :
    latentLiability s e - e = s := by
  unfold latentLiability Descent.Core.sum
  ring

/-- Disease event under an ancestry-dependent threshold: `L > T(x)`. -/
def diseaseEvent {k : ℕ} (T : (Fin k → ℝ) → ℝ) (x : Fin k → ℝ) (s : ℝ) : Set ℝ :=
  {e : ℝ | latentLiability s e > T x}


/-- Exact threshold-event probability after integrating Gaussian environmental noise:
`P(Y=1 | S=s, x) = 1 - P(L ≤ T(x) | S=s, x)`. -/
theorem liability_threshold_probit_raw {k : ℕ} (hN : GaussianNoiseAssumption k)
    (T : (Fin k → ℝ) → ℝ) (x : Fin k → ℝ) (s : ℝ) :
    noiseMeasureGivenX hN x (diseaseEvent T x s) =
      1 - ENNReal.ofReal (ProbabilityTheory.cdf
        (ProbabilityTheory.gaussianReal s (hN.sigma2 x)) (T x)) := by
  have h_le :
      noiseMeasureGivenX hN x {e : ℝ | latentLiability s e ≤ T x} =
        ENNReal.ofReal (ProbabilityTheory.cdf
          (ProbabilityTheory.gaussianReal s (hN.sigma2 x)) (T x)) := by
    simpa [latentLiability,
      Descent.Core.sum] using noise_integrated_cdf hN x s (T x)
  have h_le_set :
      ({e : ℝ | latentLiability s e ≤ T x} : Set ℝ) = Set.Iic (T x - s) := by
    ext e
    constructor
    · intro h
      change e ≤ T x - s
      have hsle : latentLiability s e ≤ T x := by simpa using h
      dsimp [latentLiability,
      Descent.Core.sum] at hsle
      linarith
    · intro h
      change latentLiability s e ≤ T x
      have hle : e ≤ T x - s := by simpa [Set.mem_Iic] using h
      dsimp [latentLiability,
      Descent.Core.sum]
      linarith
  have h_event :
      diseaseEvent T x s = (Set.Iic (T x - s))ᶜ := by
    ext e
    constructor
    · intro h
      change ¬ e ≤ T x - s
      intro hle
      have hsle : s + e ≤ T x := by linarith
      exact (not_le_of_gt h) hsle
    · intro h
      change s + e > T x
      by_contra hnot
      have hsle : s + e ≤ T x := le_of_not_gt hnot
      have hle : e ≤ T x - s := by linarith
      exact h hle
  have h_meas_le : MeasurableSet (Set.Iic (T x - s) : Set ℝ) := measurableSet_Iic
  have h_le' :
      noiseMeasureGivenX hN x (Set.Iic (T x - s)) =
        ENNReal.ofReal (ProbabilityTheory.cdf
          (ProbabilityTheory.gaussianReal s (hN.sigma2 x)) (T x)) := by
    simpa [h_le_set] using h_le
  rw [h_event]
  rw [measure_compl (s := (Set.Iic (T x - s) : Set ℝ)) h_meas_le
    (measure_ne_top (noiseMeasureGivenX hN x) _)]
  rw [measure_univ, h_le']

/-- Real-valued form of the liability-threshold probability:
`P(Y=1 | S=s, x) = 1 - CDF_{N(s,σ²(x))}(T(x))`. -/
theorem liability_threshold_probit_real {k : ℕ} (hN : GaussianNoiseAssumption k)
    (T : (Fin k → ℝ) → ℝ) (x : Fin k → ℝ) (s : ℝ) :
    (noiseMeasureGivenX hN x (diseaseEvent T x s)).toReal =
      1 - ProbabilityTheory.cdf
        (ProbabilityTheory.gaussianReal s (hN.sigma2 x)) (T x) := by
  rw [liability_threshold_probit_raw hN T x s]
  have h_le :
      ENNReal.ofReal
        (ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal s (hN.sigma2 x)) (T x))
      ≤ (1 : ENNReal) := by
    exact_mod_cast
      (ProbabilityTheory.cdf_le_one
        (μ := ProbabilityTheory.gaussianReal s (hN.sigma2 x)) (T x))
  rw [ENNReal.toReal_sub_of_le h_le (by simp)]
  simp [ProbabilityTheory.cdf_nonneg]

/-- Conditional disease probability under the liability-threshold model.

    Empirical status: NOT AN EMPIRICAL CLAIM. The body is the measure of
    `diseaseEvent T x s` under the noise law the model already carries, which is
    the DEFINITION of `P(Y = 1 | X = x)` in that model, not a prediction about
    it. No population can make the probability of an event a different number
    than the measure assigns it. The theorem immediately below,
    `etaLiabilityThreshold_eq_gaussian_threshold`, evaluates it to
    `1 - Φ((T(x) - s)/σ(x))`, and that evaluation is Gaussian analysis rather
    than measurement. The empirical content of the liability-threshold model
    sits in its INPUTS -- that the residual is Gaussian
    (`GaussianNoiseAssumption`) and that a fixed threshold `T` exists -- and
    those are hypotheses a consumer supplies, not consequences of this map. -/
noncomputable def etaLiabilityThreshold {k : ℕ} (hN : GaussianNoiseAssumption k)
    (T : (Fin k → ℝ) → ℝ) (s : ℝ) (x : Fin k → ℝ) : ℝ :=
  (noiseMeasureGivenX hN x (diseaseEvent T x s)).toReal

/-- Under `E|X=x ~ N(0,σ²(x))` and `Y = 1{S+E>T(x)}`, the true conditional
probability is the Gaussian-threshold expression. -/
theorem etaLiabilityThreshold_eq_gaussian_threshold {k : ℕ} (hN : GaussianNoiseAssumption k)
    (T : (Fin k → ℝ) → ℝ) (s : ℝ) (x : Fin k → ℝ) :
    etaLiabilityThreshold hN T s x =
      1 - ProbabilityTheory.cdf
        (ProbabilityTheory.gaussianReal s (hN.sigma2 x)) (T x) :=
  liability_threshold_probit_real hN T x s

/-- A data generating process parametrized by k principal components.

    `trueExpectation` stores E[Y|P,C], and `jointMeasure` stores the marginal
    law on `(P,C)`. -/
structure DataGeneratingProcess (k : ℕ) where
  trueExpectation : ℝ → (Fin k → ℝ) → ℝ
  jointMeasure : Measure (ℝ × (Fin k → ℝ))
  is_prob : IsProbabilityMeasure jointMeasure := by infer_instance

instance dgp_is_prob {k : ℕ} (dgp : DataGeneratingProcess
    k) : IsProbabilityMeasure dgp.jointMeasure := dgp.is_prob

/-! ### Predictor Abstraction and Proper Risk

Working directly with predictors (functions ℝ → (Fin k → ℝ) → ℝ) avoids
parameterization-dependent statements: risk depends on the predictor function,
not on how it is represented. -/

/-- A predictor is a function from (PGS, PCs) → ℝ. Bayes optimality and risk
    should be stated at this level to avoid representation dependence. -/
abbrev Predictor (k : ℕ) := ℝ → (Fin k → ℝ) → ℝ

/-- MSE risk of a predictor relative to the conditional mean E[Y|P,C]. -/
noncomputable def mseRisk {k : ℕ} [Fintype (Fin k)] (dgp : DataGeneratingProcess k) (f : Predictor
    k) : ℝ :=
  ∫ x, (dgp.trueExpectation x.1 x.2 - f x.1 x.2)^2 ∂dgp.jointMeasure

/-- Upgraded DGP that explicitly names the conditional mean and provides
    the orthogonality characterization of conditional expectation.

    This is the proper statistical framework: `μ` is a joint law on (P, C, Y),
    and `m` satisfies E[(Y - m(P,C)) · φ(P,C)] = 0 for all square-integrable φ.

    Fully deriving E[Y|P,C] via disintegration is heavy in Mathlib; this structure
    captures the *characterizing property* that proofs actually need. -/
structure ConditionalMeanDGP (k : ℕ) where
  /- Joint law on (P, C, Y). -/
  μ : Measure (ℝ × (Fin k → ℝ) × ℝ)
  prob : IsProbabilityMeasure μ := by infer_instance
  /-- Conditional mean function m = E[Y | P, C]. -/
  m : ℝ → (Fin k → ℝ) → ℝ
  /-- Orthogonality characterization: for all square-integrable φ(P,C),
      E[(Y - m(P,C)) · φ(P,C)] = 0. This is the defining property of
      conditional expectation as an L² projection. -/
  m_spec :
    ∀ (φ : ℝ × (Fin k → ℝ) → ℝ),
      Integrable (fun x : ℝ × (Fin k → ℝ) × ℝ ↦ (x.2.2 - m x.1 x.2.1) * φ (x.1, x.2.1)) μ →
      (∫ x, (x.2.2 - m x.1 x.2.1) * φ (x.1, x.2.1) ∂μ) = 0

/-- Every `ConditionalMeanDGP` supplies `prob` as a field, so the probability-measure fact
is registered once, here, as an instance.  Sites needing it then obtain it by resolution.
The alternative -- a local `letI : IsProbabilityMeasure cmdgp.μ := cmdgp.prob` at each use
-- reads as installing an instance to satisfy a goal, which is the shape used to move an
obligation onto whoever supplied the argument; this way there is nothing local to inspect. -/
instance {k : ℕ} (cmdgp : ConditionalMeanDGP k) :
    IsProbabilityMeasure cmdgp.μ := cmdgp.prob

/-- **The class is inhabited**, by the point mass at the origin with conditional mean `0`.

    A theorem quantified over an unconstructed structure is true and empty.  At the single
    atom the response is `0` and `m` is `0`, so the orthogonality residual `Y - m(P,C)`
    vanishes there and every test functional integrates to zero.  The law is degenerate:
    this establishes that the risk decompositions below are about something, not that they
    are about anything interesting. -/
noncomputable def ConditionalMeanDGP.witness (k : ℕ) : ConditionalMeanDGP k where
  μ := Measure.dirac 0
  m := fun _ _ ↦ 0
  m_spec := by
    intro φ _
    simp [integral_dirac]

/-- Full predictive risk under a joint law on `(P,C,Y)`.
    This is the explicit `E[(Y - f(P,C))^2]` objective. -/
noncomputable def predictionRiskY {k : ℕ} [Fintype (Fin k)]
    (dgp : ConditionalMeanDGP k) (f : Predictor k) : ℝ :=
  ∫ x, (x.2.2 - f x.1 x.2.1)^2 ∂dgp.μ

/-- Convert a ConditionalMeanDGP to the simpler DataGeneratingProcess format.
    The marginal on (P,C) is obtained by mapping out Y. -/
noncomputable def ConditionalMeanDGP.toDGP {k : ℕ} (cmdgp : ConditionalMeanDGP
    k) : DataGeneratingProcess k where
  trueExpectation := cmdgp.m
  jointMeasure := cmdgp.μ.map (fun x ↦ (x.1, x.2.1))
  is_prob := by
    simpa using
      (Measure.isProbabilityMeasure_map (μ := cmdgp.μ)
        (f := fun x : ℝ × (Fin k → ℝ) × ℝ ↦ (x.1, x.2.1))
        (by fun_prop))

/-!
=================================================================
## Part 2: Fully Formalized Theorems and Proofs
=================================================================
-/


/-- **Lemma**: Moments of the standard Gaussian distribution are integrable.
    Specifically, x^n is integrable w.r.t N(0,1). -/
lemma gaussian_moments_integrable (n : ℕ) :
    Integrable (fun x : ℝ ↦ x ^ n) (ProbabilityTheory.gaussianReal 0 1) := by
  simpa [poly_n, stdGaussianMeasure] using (integrable_poly_n n)

/-! ### Gaussian Moment Facts

These lemmas derive standard moments of N(0,1) from the integrability
infrastructure so population-level DGP proofs can use canonical moment facts. -/

/-- E[P] = 0 under the standard Gaussian. -/
theorem gaussian_mean_zero :
    ∫ x, x ∂(ProbabilityTheory.gaussianReal 0 1) = 0 := by
  simp [ProbabilityTheory.integral_id_gaussianReal]

/-- E[P²] = 1 under the standard Gaussian (variance = 1). -/
theorem gaussian_second_moment :
    ∫ x, x ^ 2 ∂(ProbabilityTheory.gaussianReal 0 1) = 1 := by
  have h_var : ProbabilityTheory.variance id (ProbabilityTheory.gaussianReal 0 1) = (1 : ℝ) := by
    norm_num [ProbabilityTheory.variance_id_gaussianReal]
  have h_var_int :
      ProbabilityTheory.variance id (ProbabilityTheory.gaussianReal 0 1) =
        ∫ x, (x - ∫ t, t ∂(ProbabilityTheory.gaussianReal 0 1)) ^ 2
          ∂(ProbabilityTheory.gaussianReal 0 1) := by
    simpa using
      (ProbabilityTheory.variance_eq_integral (μ := ProbabilityTheory.gaussianReal 0 1)
        (X := id) measurable_id.aemeasurable)
  rw [h_var_int] at h_var
  simpa [gaussian_mean_zero] using h_var

/-- E[P · C_l] = 0 when P and C are independent standard normals.
    This is the key fact that eliminates cross-terms in risk calculations. -/
theorem independent_product_mean_zero {k : ℕ} [Fintype (Fin k)] (l : Fin k) :
    ∫ pc, pc.1 * pc.2 l ∂(stdNormalProdMeasure k) = 0 := by
  let μP : Measure ℝ := ProbabilityTheory.gaussianReal 0 1
  let μC : Measure (Fin k → ℝ) :=
    Measure.pi (fun (_ : Fin k) ↦ ProbabilityTheory.gaussianReal 0 1)
  have hPC :
      ∫ pc, pc.1 * pc.2 l ∂(μP.prod μC) =
        (∫ p, p ∂μP) * (∫ c, c l ∂μC) := by
    simpa using
      (MeasureTheory.integral_prod_mul (μ := μP) (ν := μC)
        (f := fun p : ℝ ↦ p) (g := fun c : Fin k → ℝ ↦ c l))
  have hC_map : μC.map (Function.eval l) = ProbabilityTheory.gaussianReal 0 1 := by
    simpa [μC] using
      (MeasureTheory.measurePreserving_eval
        (μ := fun (_ : Fin k) ↦ ProbabilityTheory.gaussianReal 0 1) l).map_eq
  have h_eval_ae : AEMeasurable (Function.eval l) μC := by
    exact
      (MeasureTheory.measurePreserving_eval
        (μ := fun (_ : Fin k) ↦ ProbabilityTheory.gaussianReal 0 1) l).measurable.aemeasurable
  have hC0 : (∫ c, c l ∂μC) = 0 := by
    calc
      ∫ c, c l ∂μC = ∫ x, x ∂(μC.map (Function.eval l)) := by
        simpa using
          (MeasureTheory.integral_map (μ := μC) (φ := Function.eval l)
            (f := fun x : ℝ ↦ x) h_eval_ae aestronglyMeasurable_id).symm
      _ = ∫ x, x ∂(ProbabilityTheory.gaussianReal 0 1) := by rw [hC_map]
      _ = 0 := gaussian_mean_zero
  have h_prod : stdNormalProdMeasure k = μP.prod μC := by
    simp [stdNormalProdMeasure, μP, μC]
  calc
    ∫ pc, pc.1 * pc.2 l ∂(stdNormalProdMeasure k)
        = ∫ pc, pc.1 * pc.2 l ∂(μP.prod μC) := by rw [h_prod]
    _ = (∫ p, p ∂μP) * (∫ c, c l ∂μC) := hPC
    _ = 0 := by simp [hC0]

/-- Transpose-dot identity: `(A u) ⬝ v = u ⬝ (Aᵀ v)`. -/
lemma sum_mulVec_mul_eq_sum_mul_transpose_mulVec {p : ℕ}
    (A : Matrix (Fin p) (Fin p) ℝ) (u v : Fin p → ℝ) :
    ∑ i, (A.mulVec u) i * v i = ∑ i, u i * ((Matrix.transpose A).mulVec v) i := by
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply]
  simp only [Finset.sum_mul, Finset.mul_sum]
  simp only [← Finset.sum_product']
  refine Finset.sum_equiv (Equiv.prodComm (Fin p) (Fin p)) ?_ ?_
  · intro _
    simp
  · intro ⟨i, j⟩ _
    simp only [Equiv.prodComm_apply, Prod.swap_prod_mk]
    ring

/-! ### Standardized a.e. → Pointwise Upgrade

For continuous functions on a measure with full support (`IsOpenPosMeasure`),
a.e. equality implies pointwise equality. -/

/-- If two continuous functions agree a.e. on a measure with `IsOpenPosMeasure`,
    they agree everywhere. -/
theorem eq_of_ae_eq_of_continuous {α : Type*} [TopologicalSpace α]
    [MeasurableSpace α] {μ : Measure α} [μ.IsOpenPosMeasure] {f g : α → ℝ}
    (hf : Continuous f) (hg : Continuous g)
    (h_ae : f =ᵐ[μ] g) : f = g :=
  Measure.eq_of_ae_eq h_ae hf hg

/-- **Heterozygosity rises with allele frequency below one half.**

`2 p (1 - p)` is the genotype variance at Hardy-Weinberg, and this is the only fact about
its shape the corpus uses.  It was proved three times: once about rare against common
variants in `RareVariantPortability`, once about neutral against balanced sites in
`SelectionArchitecture`, and once through the named `genotypeVarianceHWE` in
`GeneticArchitectureDiscovery` -- three modules, one `nlinarith` on the same two squares,
and no theorem relating any two of them.

It belongs here, above all three, because it is a fact about a real number in `[0, 1/2]`
and not about rarity, selection or discovery. -/
theorem two_mul_one_sub_strictMono_le_half (p q : ℝ)
    (h_lt : p < q) (h_q_half : q ≤ 1 / 2) :
    2 * p * (1 - p) < 2 * q * (1 - q) := by
  nlinarith [sq_nonneg (q - 1 / 2), sq_nonneg (p - 1 / 2)]

end Descent.Foundations
