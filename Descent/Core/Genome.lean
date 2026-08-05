/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Core.Fst
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

/-!
# Core: the genome

**The objects the rest of this development is about.**

A census of the corpus found that 94 of 2,203 definitions -- 4.3% -- mention any
genotype, allele or population type in their signature, and 1,215 are bare `ℝ → ℝ`.
That is not a complaint about style.  A quantity of type `ℝ → ℝ` named `hweHeterozygosity`
is a function on the reals with a biological name, and nothing stops it being applied to a
number that is not an allele frequency, composed with a function that is not a frequency
map, or confused with a different `ℝ → ℝ` that happens to have the same body.  The names
carry the biology and the types carry none of it, so every agreement between two
biological quantities is an agreement between two people about what a real number meant.

Three separate encodings of a genotype existed and none was shared:

  * `Foundations.Probability.DiploidGenotype` -- `homRef | het | homAlt`, with an
    equivalence to `Fin 3` and a sum expansion, used for Hardy-Weinberg moments;
  * `Pangenome.Gauge.Allele` -- `A | C | G`, a three-symbol alphabet doubling as
    haplotype and reference tree in the pangenome gauge counterexample;
  * `Blindness.EpistaticChaos.GenotypeDesign` -- not a genotype type at all but a
    namespace of designs over `Fin n → V` coordinates, whose `V` is *intended* to be a
    standardized Hardy-Weinberg genotype and is quantified over instead.

This file is the one they fold into.  `Genotype` here is the first of those, moved to the
bottom of the import graph so that everything can use it; `Foundations.Probability` keeps
`DiploidGenotype` as a reducible abbreviation, so `DiploidGenotype.homRef` and every
existing pattern match read unchanged.

## What is here, and why each piece

`Allele` and `Genotype` are separate types because a diploid genotype is a MULTISET of two
alleles and not a pair: `Genotype.ofAlleles` is symmetric, and `ofAlleles_comm` is the
theorem that says so.  A development that encoded genotypes as `Allele × Allele` would
have `(ref, alt)` and `(alt, ref)` as different objects and would need every downstream
statement to quotient by that, silently, by hand.

`Haplotype` and `Genome` are the per-locus versions, and `Genome.ofHaplotypes` is the
mechanism: a diploid genome is what two gametes make.  This is the only place in the
corpus where that sentence is a definition rather than a comment.

`hweProb` is the one-locus Hardy-Weinberg law, and the two theorems about it are the
reason this file imports `Core.Fst`: the HETEROZYGOTE PROBABILITY and the DOSAGE VARIANCE
under Hardy-Weinberg are both `hweHeterozygosity`, the quantity `Core.Fst` already defines
and the whole `F_ST` layer is written in.  Those two facts are what make `2 q (1 - q)` one
quantity appearing twice rather than two quantities that happen to agree.

`Panel` is a genotype matrix with its empirical allele frequency, bounded in `[0, 1]` by
a theorem rather than by a hypothesis someone remembered to state.
-/

namespace Descent.Core

open scoped BigOperators

/-! ## Alleles and genotypes at a biallelic locus -/

/-- **An allele at a biallelic locus**: the reference copy or the alternative copy.

Biallelic because that is what the rest of the corpus assumes -- every `F_ST`,
heterozygosity and linkage-disequilibrium quantity here is written for two alleles, and a
type admitting more would be promising a generality no theorem below delivers.  The
pangenome's three-symbol alphabet is a different object doing a different job (a reference
path through a graph, not a state at a site) and is not folded into this. -/
inductive Allele
  | ref
  | alt
  deriving DecidableEq, Fintype, Repr

/-- **A diploid genotype at a biallelic locus.**

This is the type `Foundations.Probability` introduced as `DiploidGenotype`, moved here.
It is an enumeration of three states and not a pair of alleles, because the two gene
copies of a diploid are unordered: see `ofAlleles` and `ofAlleles_comm`. -/
inductive Genotype
  | homRef
  | het
  | homAlt
  deriving DecidableEq, Fintype, Repr

namespace Genotype

/-- Concrete enumeration of the three genotypes by `Fin 3`. -/
def equivFin3 : Genotype ≃ Fin 3 where
  toFun
    | .homRef => 0
    | .het => 1
    | .homAlt => 2
  invFun
    | ⟨0, _⟩ => .homRef
    | ⟨1, _⟩ => .het
    | ⟨2, _⟩ => .homAlt
  left_inv g := by
    cases g <;> rfl
  right_inv i := by
    fin_cases i <;> rfl

@[simp] theorem equivFin3_symm_apply (i : Fin 3) :
    equivFin3.symm i =
      match i with
      | ⟨0, _⟩ => Genotype.homRef
      | ⟨1, _⟩ => Genotype.het
      | ⟨2, _⟩ => Genotype.homAlt := by
  fin_cases i <;> rfl

@[simp] theorem equivFin3_symm_apply_apply (g : Genotype) :
    equivFin3.symm (equivFin3 g) = g :=
  equivFin3.left_inv g

/-- **A sum over genotypes is its three terms.**

Every closed form at a Hardy-Weinberg locus is proved by expanding this sum.  Before the
type moved here the expansion was written out separately at each site -- routed through
`equivFin3` and `Fin.sum_univ_three` by hand in `genotypeVariance_eq`, again as a
`private` lemma in `EpistaticChaos`, and again wherever else a moment was computed.  A
`private` copy is not reusable by construction, so the third and fourth sites had no
choice but to repeat it. -/
theorem sum_univ {M : Type*} [AddCommMonoid M] (f : Genotype → M) :
    (∑ g : Genotype, f g) = f Genotype.homRef + f Genotype.het + f Genotype.homAlt := by
  have hrewrite : (∑ g : Genotype, f g) = ∑ i : Fin 3, f (equivFin3.symm i) :=
    Fintype.sum_equiv equivFin3 _ _ (by
      intro x
      rw [equivFin3_symm_apply_apply])
  rw [hrewrite, Fin.sum_univ_three]
  rfl

/-- **The genotype two gametes make.**

A diploid individual's genotype at a locus is determined by the two alleles it inherits,
and by nothing else about which parent supplied which.  Making this a function rather than
a remark is what lets `ofAlleles_comm` be a theorem. -/
def ofAlleles : Allele → Allele → Genotype
  | .ref, .ref => .homRef
  | .ref, .alt => .het
  | .alt, .ref => .het
  | .alt, .alt => .homAlt

/-- **The two gene copies of a diploid are unordered.**

This is the reason `Genotype` is a three-state enumeration and not `Allele × Allele`.
With the pair encoding this statement is false, and every downstream result would have to
carry a quotient by it. -/
theorem ofAlleles_comm (a b : Allele) : ofAlleles a b = ofAlleles b a := by
  cases a <;> cases b <;> rfl

/-- **Number of alternative alleles carried**, the corpus's `0/1/2` genotype coding.

Empirical status: NOT AN EMPIRICAL CLAIM.  This is a CODING, and a coding cannot disagree
with a population: it fixes what the symbol `dosage` denotes everywhere downstream.  What
is empirical is what the coding buys, and that is tested where it is used --
`BlindnessRegistry.averageEffect` is the least-squares slope of genotypic value on THIS
dosage, and a different coding would move that slope. -/
def dosage : Genotype → ℝ
  | .homRef => 0
  | .het => 1
  | .homAlt => 2

@[simp] theorem dosage_homRef : dosage .homRef = 0 := rfl
@[simp] theorem dosage_het : dosage .het = 1 := rfl
@[simp] theorem dosage_homAlt : dosage .homAlt = 2 := rfl

theorem dosage_nonneg (g : Genotype) : 0 ≤ dosage g := by
  cases g <;> norm_num [dosage]

/-- The dosage never exceeds the ploidy: a diploid carries at most two alternative
copies.  Stated against `Core.ploidy` rather than against the literal `2`, so that the
bound moves with the convention instead of having to be found and edited. -/
theorem dosage_le_ploidy (g : Genotype) : dosage g ≤ ploidy := by
  cases g <;> norm_num [dosage, ploidy]

end Genotype

/-! ## Loci, haplotypes, genomes, panels -/

/-- **A locus**: an index into a set of `n` sites.

An abbreviation and not a structure.  There is nothing to know about a locus in this
development beyond which one it is -- position, chromosome and reference base never enter
a statement -- and a one-field structure would buy no invariant while costing every
theorem a projection. -/
abbrev Locus (n : ℕ) := Fin n

/-- **A haplotype**: one allele at each of `n` loci.  A gamete. -/
abbrev Haplotype (n : ℕ) := Locus n → Allele

/-- **A genome**: one diploid genotype at each of `n` loci. -/
abbrev Genome (n : ℕ) := Locus n → Genotype

/-- **A diploid genome is what two gametes make**, locus by locus. -/
def Genome.ofHaplotypes {n : ℕ} (h₁ h₂ : Haplotype n) : Genome n :=
  fun l ↦ Genotype.ofAlleles (h₁ l) (h₂ l)

/-- **Which gamete came from which parent does not enter the genome.** -/
theorem Genome.ofHaplotypes_comm {n : ℕ} (h₁ h₂ : Haplotype n) :
    Genome.ofHaplotypes h₁ h₂ = Genome.ofHaplotypes h₂ h₁ := by
  funext l
  exact Genotype.ofAlleles_comm _ _

/-- **An allele-frequency vector**: the alternative-allele frequency at each of `n` loci.

Named rather than written `Fin n → ℝ` at each use, so that a theorem quantified over
allele frequencies says so in its statement. -/
abbrev AlleleFreq (n : ℕ) := Locus n → ℝ

/-- The predicate that makes an `AlleleFreq` a frequency.  Carried as a hypothesis where
it is needed rather than bundled, because most statements about frequencies hold on all
of `ℝ` and bundling would make them harder to apply, not safer. -/
def IsAlleleFreq {n : ℕ} (q : AlleleFreq n) : Prop := ∀ l, q l ∈ Set.Icc (0 : ℝ) 1

/-- **A linkage-disequilibrium matrix** over `n` loci. -/
abbrev LDMatrix (n : ℕ) := Locus n → Locus n → ℝ

/-- **A genotyped panel**: `nSamples` individuals called at `nLoci` sites.

This is the object every empirical claim in the corpus is ultimately about -- a genotype
matrix -- and until now the corpus had no type for it, only real-valued summaries of one. -/
structure Panel where
  nSamples : ℕ
  nLoci : ℕ
  call : Fin nSamples → Genome nLoci

namespace Panel

/-- **The class is inhabited.**  A theorem quantified over an uninhabited structure is true
and empty: kernel-checked, clean axiom report, no content. -/
def witness : Panel where
  nSamples := 1
  nLoci := 1
  call := fun _ _ ↦ Genotype.het

/-- **The empirical alternative-allele frequency at a locus**: total alternative copies
over total copies, the estimator every `F_ST` and heterozygosity measurement in the
validation tier actually computes. -/
noncomputable def altFreq (P : Panel) (l : Locus P.nLoci) : ℝ :=
  (∑ i, (P.call i l).dosage) / (ploidy * (P.nSamples : ℝ))

theorem altFreq_nonneg (P : Panel) (l : Locus P.nLoci) : 0 ≤ P.altFreq l := by
  have hp : (0 : ℝ) ≤ ploidy := by norm_num [ploidy]
  refine div_nonneg (Finset.sum_nonneg fun i _ ↦ Genotype.dosage_nonneg _) ?_
  exact mul_nonneg hp (Nat.cast_nonneg _)

/-- **The empirical frequency is a frequency.**

A bound, not a hypothesis.  Every module that takes an allele frequency as a free real and
assumes `0 ≤ q ≤ 1` is assuming what the estimator already delivers, and an assumption
cannot notice when the estimator changes. -/
theorem altFreq_le_one (P : Panel) (hP : 0 < P.nSamples) (l : Locus P.nLoci) :
    P.altFreq l ≤ 1 := by
  have hp : (0 : ℝ) < ploidy := by norm_num [ploidy]
  have hn : (0 : ℝ) < (P.nSamples : ℝ) := by exact_mod_cast hP
  have hsum : (∑ i, (P.call i l).dosage) ≤ ploidy * (P.nSamples : ℝ) := by
    calc (∑ i, (P.call i l).dosage)
        ≤ ∑ _i : Fin P.nSamples, ploidy :=
          Finset.sum_le_sum fun i _ ↦ Genotype.dosage_le_ploidy _
      _ = (P.nSamples : ℝ) * ploidy := by
          simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ = ploidy * (P.nSamples : ℝ) := by ring
  -- `rw` is syntactic, and the goal is a `def` until it is unfolded: `div_le_one`
  -- has no division to match against `P.altFreq l ≤ 1`.
  unfold altFreq
  rw [div_le_one (mul_pos hp hn)]
  exact hsum

/-- **The estimator delivers a frequency**, in the sense of the predicate.

`IsAlleleFreq` exists so that "this vector is a vector of allele frequencies" is a
statement rather than a convention, and this is the theorem that makes it inhabited by
something the corpus actually computes rather than by an assumption. -/
theorem isAlleleFreq (P : Panel) (hP : 0 < P.nSamples) : IsAlleleFreq P.altFreq :=
  fun l ↦ Set.mem_Icc.mpr ⟨P.altFreq_nonneg l, P.altFreq_le_one hP l⟩

/-- **The panel's dosage covariance**: the unnormalised linkage-disequilibrium matrix.

Linkage disequilibrium enters the corpus as a real matrix with an `LDMatrix`-shaped role
and no definition connecting it to genotypes.  This is that connection: the entries are
covariances of the dosage coding across the panel's samples, so an `LDMatrix` is something
a genotype matrix PRODUCES rather than something a theorem is handed. -/
noncomputable def dosageCovariance (P : Panel) : LDMatrix P.nLoci :=
  fun l₁ l₂ ↦
    (∑ i, ((P.call i l₁).dosage - ploidy * P.altFreq l₁) *
          ((P.call i l₂).dosage - ploidy * P.altFreq l₂)) / (P.nSamples : ℝ)

/-- **Linkage disequilibrium is symmetric**, because a covariance is.  Stated because the
`r²` and `D` quantities downstream all assume it and none of them says so. -/
theorem dosageCovariance_symm (P : Panel) (l₁ l₂ : Locus P.nLoci) :
    P.dosageCovariance l₁ l₂ = P.dosageCovariance l₂ l₁ := by
  unfold dosageCovariance
  congr 1
  exact Finset.sum_congr rfl fun i _ ↦ by ring

end Panel

/-! ## Hardy-Weinberg: the one-locus genotype law

Two theorems, and they are the reason this file sits above `Core.Fst` rather than beside
it.  `hweHeterozygosity` is defined there as `ploidy · q · (1 - q)`, and the whole `F_ST`
layer is written in it.  Below, that same expression is (i) the probability of drawing a
heterozygote and (ii) the variance of the dosage -- so the three are one quantity, and a
change to the ploidy convention moves all three together. -/

/-- **The Hardy-Weinberg genotype law** at alternative-allele frequency `q`.

The `2` in the heterozygote term is the binomial coefficient `C(2,1)`: a heterozygote can
arise in two ways, alt-from-the-first-gamete and alt-from-the-second, and `Genotype`
identifies them.  It is not the ploidy convention, although it counts the same two gene
copies; `hweProb_het` below is where the two meet. -/
noncomputable def hweProb (q : ℝ) : Genotype → ℝ
  | .homRef => (1 - q) ^ 2
  | .het => 2 * q * (1 - q)
  | .homAlt => q ^ 2

/-- **The law is a probability distribution**, at every `q` -- no range hypothesis needed
for the mass, which is an algebraic identity. -/
theorem sum_hweProb (q : ℝ) : (∑ g : Genotype, hweProb q g) = 1 := by
  rw [Genotype.sum_univ]
  unfold hweProb
  ring

/-- **The heterozygote probability IS `hweHeterozygosity`.**

`Core.Fst.hweHeterozygosity q = ploidy · q · (1 - q)` was written as a scalar formula with a biological name and no genotype anywhere in its type.  This is the statement that the
name is earned: it is the probability that a Hardy-Weinberg individual is a heterozygote. -/
theorem hweProb_het (q : ℝ) : hweProb q Genotype.het = hweHeterozygosity q := by
  unfold hweProb hweHeterozygosity ploidy
  ring

/-- **The dosage variance under Hardy-Weinberg is also `hweHeterozygosity`.**

`Var(dosage) = 2 q (1 - q)` for a `Binomial(2, q)` count, which is the same expression
again.  Two different questions -- how often is an individual heterozygous, and how much
does the dosage vary -- have one answer, and stating it here is what stops the `F_ST`
layer's `2 q (1 - q)` and the moment layer's `2 q (1 - q)` from drifting apart. -/
theorem hwe_dosage_variance (q : ℝ) :
    (∑ g : Genotype, hweProb q g * (Genotype.dosage g - ploidy * q) ^ 2)
      = hweHeterozygosity q := by
  rw [Genotype.sum_univ]
  unfold hweProb hweHeterozygosity ploidy Genotype.dosage
  ring

/-- **The mean dosage is `ploidy · q`**: the coding is unbiased for the allele frequency,
up to the ploidy factor, which is what makes `altFreq` above an estimator of `q` rather
than of something else. -/
theorem hwe_mean_dosage (q : ℝ) :
    (∑ g : Genotype, hweProb q g * Genotype.dosage g) = ploidy * q := by
  rw [Genotype.sum_univ]
  unfold hweProb ploidy Genotype.dosage
  ring

end Descent.Core
