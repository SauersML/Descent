/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.FiniteGeneticTransition
import Descent.Portability.FiniteReproductiveKernel

assert_below Descent.Decision Descent.Program

/-!
# Meiosis, viability selection and the gamete pool

NOTE2 (3) to (6) build the biological transition out of four primitives: a meiosis mask that
chooses, locus by locus, which parental strand a gamete carries; a transmission kernel that
may mutate the selected strand; a fitness-weighted parental law inside each deme; and a
gamete-migration convention that pools gametes across demes. This module constructs each of
them for an arbitrary finite locus set with an arbitrary finite allele alphabet at each
locus, and states the exact mass formula that each note equation asserts.

The gamete law of NOTE2 (3) is a `FiniteReportLaw.bind` of the supplied mask law through the
supplied transmission kernel, so its normalization is a consequence of the construction. Two
concrete instances are supplied rather than assumed: the fair independent-switch mask law,
which is the corpus product law `FiniteGeneticTransition.piLaw` over fair binary switches and
is proved uniform over masks; and the independent-site transmission kernel of NOTE2 section
2.1, which is the same product law over per-locus mutation kernels. The construction is tied
back to the corpus binary-allele gamete law: `FiniteGeneticTransition.gameteLaw` is exactly
this law at a two-letter alphabet, a parent-independent mask law and the independent-site
kernel.

NOTE2 (4) is the corpus `FiniteReproductiveKernel.selectedParent` read at the diploid census,
and the ratio theorem here shows its total viability weight, the only denominator anywhere in
the transition, cancels between genotypes. NOTE2 (5) is the two-stage bind over the migration
row and the parental law, and NOTE2 (6) is the corpus multinomial census law applied to two
independently drawn gametes.

Not formalized here: state-dependent fitness and state-dependent mask laws are carried as
supplied inputs rather than derived, exactly as the note states; the explicit failure rule
for a deme of zero total viability weight is the positivity premise on the corpus parental
law rather than a separate distinguished outcome; and no linkage-disequilibrium closure is
taken, since the state retains every haplotype.

## Empirical status

None. The bodies here are algebra: the mask law, the mutation kernels, the fitnesses and the
migration row are supplied inputs, and each theorem states what the constructed composition
computes, so no measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.MeiosisGameteLaw

open scoped BigOperators

noncomputable section

variable {Locus : Type*} [Fintype Locus] [DecidableEq Locus]
variable {Allele : Locus → Type*} [∀ locus, Fintype (Allele locus)]
  [∀ locus, DecidableEq (Allele locus)]
variable {Deme : Type*} [Fintype Deme]

/-- A phased haplotype: one allele at every locus. -/
abbrev Haplotype (Allele : Locus → Type*) := ∀ locus, Allele locus

/-- The meiosis mask of NOTE2 section 2.1: at each locus the gamete carries the second
parental strand when the mask is set there and the first strand otherwise. -/
def selectStrand (parent : Haplotype Allele × Haplotype Allele) (mask : Locus → Bool) :
    Haplotype Allele :=
  fun locus ↦ if mask locus then parent.2 locus else parent.1 locus

/-- NOTE2 (3): the exact gamete law. Draw a meiosis mask from the supplied mask law, read the
strand it selects, and pass that strand through the supplied transmission kernel. -/
def meiosisGameteLaw
    (maskLaw : Haplotype Allele × Haplotype Allele → FiniteReportLaw (Locus → Bool))
    (transmission : Haplotype Allele → FiniteReportLaw (Haplotype Allele))
    (parent : Haplotype Allele × Haplotype Allele) : FiniteReportLaw (Haplotype Allele) :=
  (maskLaw parent).bind fun mask ↦ transmission (selectStrand parent mask)

omit [(locus : Locus) → DecidableEq (Allele locus)] in
/-- NOTE2 (3) entrywise: the gamete probability is the mask law summed against the
transmission probability of the strand that mask selects. -/
theorem meiosisGameteLaw_mass
    (maskLaw : Haplotype Allele × Haplotype Allele → FiniteReportLaw (Locus → Bool))
    (transmission : Haplotype Allele → FiniteReportLaw (Haplotype Allele))
    (parent : Haplotype Allele × Haplotype Allele) (gamete : Haplotype Allele) :
    (meiosisGameteLaw maskLaw transmission parent).mass gamete =
      ∑ mask : Locus → Bool, (maskLaw parent).mass mask *
        (transmission (selectStrand parent mask)).mass gamete := rfl

/-- A fair binary switch: the elementary randomization of one meiosis decision. -/
def fairSwitch : FiniteReportLaw Bool where
  mass := fun _ ↦ 1 / 2
  mass_nonneg := fun _ ↦ by norm_num
  mass_sum := by norm_num [Fintype.sum_bool]

/-- The fair independent-switch mask law: every locus decides independently which parental
strand it transmits, with no bias and no linkage between loci. -/
def fairMaskLaw : FiniteReportLaw (Locus → Bool) :=
  FiniteGeneticTransition.piLaw fun _ : Locus ↦ fairSwitch

/-- The fair mask law is uniform over the masks: every one of the two-to-the-loci meiosis
outcomes carries the same probability. -/
theorem fairMaskLaw_mass (mask : Locus → Bool) :
    (fairMaskLaw (Locus := Locus)).mass mask = (1 / 2) ^ Fintype.card Locus := by
  rw [fairMaskLaw, FiniteGeneticTransition.piLaw_mass]
  simp [fairSwitch, Finset.prod_const, Finset.card_univ]

/-- The independent-site transmission kernel of NOTE2 section 2.1: each locus passes through
its own mutation kernel, independently of every other locus. -/
def independentSiteKernel
    (mutate : ∀ locus, Allele locus → FiniteReportLaw (Allele locus))
    (strand : Haplotype Allele) : FiniteReportLaw (Haplotype Allele) :=
  FiniteGeneticTransition.piLaw fun locus ↦ mutate locus (strand locus)

omit [(locus : Locus) → DecidableEq (Allele locus)] in
/-- The independent-site kernel factorizes exactly over the loci. -/
theorem independentSiteKernel_mass
    (mutate : ∀ locus, Allele locus → FiniteReportLaw (Allele locus))
    (strand gamete : Haplotype Allele) :
    (independentSiteKernel mutate strand).mass gamete =
      ∏ locus, (mutate locus (strand locus)).mass (gamete locus) := rfl

/-- NOTE2 (3) at the two supplied default primitives: the gamete probability is a uniform
average over masks of a product of per-locus mutation probabilities. -/
theorem meiosisGameteLaw_default_mass
    (mutate : ∀ locus, Allele locus → FiniteReportLaw (Allele locus))
    (parent : Haplotype Allele × Haplotype Allele) (gamete : Haplotype Allele) :
    (meiosisGameteLaw (fun _ ↦ fairMaskLaw) (independentSiteKernel mutate) parent).mass
        gamete =
      ∑ mask : Locus → Bool, (1 / 2) ^ Fintype.card Locus *
        ∏ locus, (mutate locus (selectStrand parent mask locus)).mass (gamete locus) := by
  rw [meiosisGameteLaw_mass]
  exact Finset.sum_congr rfl fun mask _ ↦ by
    rw [fairMaskLaw_mass, independentSiteKernel_mass]

/-- A parent whose two strands agree transmits the same law whatever mask law is supplied:
without heterozygosity the meiosis randomization is invisible in the gamete law. -/
theorem meiosisGameteLaw_of_homozygous
    (maskLaw : Haplotype Allele × Haplotype Allele → FiniteReportLaw (Locus → Bool))
    (transmission : Haplotype Allele → FiniteReportLaw (Haplotype Allele))
    (parent : Haplotype Allele × Haplotype Allele) (hparent : parent.1 = parent.2) :
    meiosisGameteLaw maskLaw transmission parent = transmission parent.1 := by
  have hselect : ∀ mask : Locus → Bool, selectStrand parent mask = parent.1 := by
    intro mask
    funext locus
    simp only [selectStrand]
    split_ifs with hmask
    · rw [hparent]
    · rfl
  refine FiniteReportLaw.ext fun gamete ↦ ?_
  rw [meiosisGameteLaw_mass]
  simp only [hselect, ← Finset.sum_mul, (maskLaw parent).mass_sum, one_mul]

/-- The corpus binary-allele gamete law is this construction read at a two-letter alphabet,
a parent-independent mask law and the independent-site mutation kernel. -/
theorem meiosisGameteLaw_eq_corpus (strandLaw : FiniteReportLaw (Locus → Bool))
    (mutate : Locus → Bool → FiniteReportLaw Bool) (parent : Bool → Locus → Bool) :
    meiosisGameteLaw (Allele := fun _ ↦ Bool) (fun _ ↦ strandLaw)
        (independentSiteKernel mutate) (parent false, parent true) =
      FiniteGeneticTransition.gameteLaw strandLaw mutate parent := by
  have hselect : ∀ mask : Locus → Bool,
      selectStrand (Allele := fun _ ↦ Bool) (parent false, parent true) mask =
        FiniteGeneticTransition.segregatedHaplotype parent mask := by
    intro mask
    funext locus
    simp only [selectStrand, FiniteGeneticTransition.segregatedHaplotype]
    cases hmask : mask locus <;> simp [hmask]
  refine FiniteReportLaw.ext fun gamete ↦ ?_
  rw [meiosisGameteLaw_mass]
  refine Finset.sum_congr rfl fun mask _ ↦ ?_
  rw [hselect mask]
  rfl

/-- NOTE2 (4): the fitness-weighted parental law inside one deme. This is the corpus
`FiniteReproductiveKernel.selectedParent` read at the diploid census, and its entries are
census times viability over the total viability weight. -/
theorem selectedParent_mass (population : ℕ)
    (counts : FiniteReproductiveKernel.Counts
      (Haplotype Allele × Haplotype Allele) population)
    (fitness : Haplotype Allele × Haplotype Allele → ℝ)
    (hfitness : ∀ genotype, 0 ≤ fitness genotype)
    (htotal : 0 < FiniteReproductiveKernel.fitnessTotal counts fitness)
    (genotype : Haplotype Allele × Haplotype Allele) :
    (FiniteReproductiveKernel.selectedParent counts fitness hfitness htotal).mass genotype =
      (counts.val genotype : ℝ) * fitness genotype /
        FiniteReproductiveKernel.fitnessTotal counts fitness := rfl

/-- NOTE2 (4): the total viability weight, the only denominator in the whole transition,
cancels from every ratio of parental probabilities. -/
theorem selectedParent_ratio (population : ℕ)
    (counts : FiniteReproductiveKernel.Counts
      (Haplotype Allele × Haplotype Allele) population)
    (fitness : Haplotype Allele × Haplotype Allele → ℝ)
    (hfitness : ∀ genotype, 0 ≤ fitness genotype)
    (htotal : 0 < FiniteReproductiveKernel.fitnessTotal counts fitness)
    (first second : Haplotype Allele × Haplotype Allele)
    (hsecond : 0 < (counts.val second : ℝ) * fitness second) :
    0 < (FiniteReproductiveKernel.selectedParent counts fitness hfitness htotal).mass
        second ∧
      (FiniteReproductiveKernel.selectedParent counts fitness hfitness htotal).mass first /
        (FiniteReproductiveKernel.selectedParent counts fitness hfitness htotal).mass
          second =
      ((counts.val first : ℝ) * fitness first) /
        ((counts.val second : ℝ) * fitness second) := by
  constructor
  · rw [selectedParent_mass population counts fitness hfitness htotal second]
    exact div_pos hsecond htotal
  rw [selectedParent_mass population counts fitness hfitness htotal first,
    selectedParent_mass population counts fitness hfitness htotal second]
  rw [div_div_div_cancel_right₀]
  exact ne_of_gt htotal

/-- NOTE2 (5): the gamete pool of a deme. Draw the source deme from the gamete-migration
row, the parent from that deme's parental law, and the gamete from that parent's meiosis
law. -/
def gametePool (migration : FiniteReportLaw Deme)
    (parentalLaw : Deme → FiniteReportLaw (Haplotype Allele × Haplotype Allele))
    (maskLaw : Haplotype Allele × Haplotype Allele → FiniteReportLaw (Locus → Bool))
    (transmission : Haplotype Allele → FiniteReportLaw (Haplotype Allele)) :
    FiniteReportLaw (Haplotype Allele) :=
  migration.bind fun source ↦
    (parentalLaw source).bind (meiosisGameteLaw maskLaw transmission)

omit [(locus : Locus) → DecidableEq (Allele locus)] in
/-- NOTE2 (5) entrywise: the migration row summed against the parental law summed against
the gamete law of NOTE2 (3). -/
theorem gametePool_mass (migration : FiniteReportLaw Deme)
    (parentalLaw : Deme → FiniteReportLaw (Haplotype Allele × Haplotype Allele))
    (maskLaw : Haplotype Allele × Haplotype Allele → FiniteReportLaw (Locus → Bool))
    (transmission : Haplotype Allele → FiniteReportLaw (Haplotype Allele))
    (gamete : Haplotype Allele) :
    (gametePool migration parentalLaw maskLaw transmission).mass gamete =
      ∑ source, migration.mass source *
        ∑ parent, (parentalLaw source).mass parent *
          (meiosisGameteLaw maskLaw transmission parent).mass gamete := rfl

omit [(locus : Locus) → DecidableEq (Allele locus)] in
/-- NOTE2 (5) with independent maternal and paternal gametes: the diploid offspring law is
the product of two copies of the gamete pool. -/
theorem independentMating_gametePool_mass (migration : FiniteReportLaw Deme)
    (parentalLaw : Deme → FiniteReportLaw (Haplotype Allele × Haplotype Allele))
    (maskLaw : Haplotype Allele × Haplotype Allele → FiniteReportLaw (Locus → Bool))
    (transmission : Haplotype Allele → FiniteReportLaw (Haplotype Allele))
    (offspring : Haplotype Allele × Haplotype Allele) :
    (FiniteReproductiveKernel.independentMating
          (gametePool migration parentalLaw maskLaw transmission)).mass offspring =
      (gametePool migration parentalLaw maskLaw transmission).mass offspring.1 *
        (gametePool migration parentalLaw maskLaw transmission).mass offspring.2 := rfl

/-- NOTE2 (6): conditionally independent offspring give the exact multinomial census law of
the next generation, with the diploid offspring probabilities of NOTE2 (5) as its cell
probabilities. -/
theorem censusTransition_mass (population : ℕ) (pool : FiniteReportLaw (Haplotype Allele))
    (counts : FiniteReproductiveKernel.Counts
      (Haplotype Allele × Haplotype Allele) population) :
    (FiniteReproductiveKernel.multinomialLaw
          (FiniteReproductiveKernel.independentMating pool) population).mass counts =
      (Nat.factorial population : ℝ) /
        (∏ genotype, (Nat.factorial (counts.val genotype) : ℝ)) *
        ∏ genotype, (pool.mass genotype.1 * pool.mass genotype.2) ^ counts.val genotype :=
  FiniteReproductiveKernel.multinomialLaw_mass _ population counts

/-- The census transition of NOTE2 (6) is a probability law on census vectors, derived from
the construction rather than imposed. -/
theorem censusTransition_sum_one (population : ℕ)
    (pool : FiniteReportLaw (Haplotype Allele)) :
    ∑ counts, (FiniteReproductiveKernel.multinomialLaw
      (FiniteReproductiveKernel.independentMating pool) population).mass counts = 1 :=
  (FiniteReproductiveKernel.multinomialLaw
    (FiniteReproductiveKernel.independentMating pool) population).mass_sum

end

end Descent.Portability.MeiosisGameteLaw
