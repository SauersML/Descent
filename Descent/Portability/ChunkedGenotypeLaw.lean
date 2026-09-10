/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.SimulationDemographyLaw
import Descent.Portability.SamplingDesignLaw

assert_below Descent.Decision Descent.Program

/-!
Independent chunk ancestry simulations share the already chosen training source.
The product is formed before flattening chunks and filtering the ordered genome
stream. Each chunk retains its full linked joint genotype law. Independence here
is the specified mathematical random-stream model, not a statement about the
implementation of finitely seeded pseudorandom generators.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.ChunkedGenotypeLaw

open FiniteReportLaw StoppedGenotypeLaw ReservoirSamplingLaw SamplingDesignLaw

variable {chunks loci chromosomes : ℕ}

abbrev ChunkedGenome (chunks loci chromosomes : ℕ) :=
  Fin chunks → WholeGenome loci chromosomes

/-- Chunk ancestry is reset at every boundary. Dependence within each chunk
is retained by taking a product of whole-chunk laws, not of individual sites. -/
noncomputable def chunkLaw (laws : Fin chunks → FiniteReportLaw (WholeGenome loci chromosomes)) :
    FiniteReportLaw (ChunkedGenome chunks loci chromosomes) where
  mass := fun genome ↦ ∏ chunk, (laws chunk).mass (genome chunk)
  mass_nonneg := fun genome ↦ Finset.prod_nonneg (fun chunk _ ↦
    (laws chunk).mass_nonneg (genome chunk))
  mass_sum := by
    rw [← Fintype.prod_sum]
    simp only [FiniteReportLaw.mass_sum, Finset.prod_const_one]

def flatten (genome : ChunkedGenome chunks loci chromosomes) :
    WholeGenome (chunks * loci) chromosomes := fun site ↦
  genome (finProdFinEquiv.symm site).1 (finProdFinEquiv.symm site).2

theorem flatten_pair (genome : ChunkedGenome chunks loci chromosomes)
    (chunk : Fin chunks) (locus : Fin loci) :
    flatten genome (finProdFinEquiv (chunk, locus)) = genome chunk locus := by
  simp [flatten]

def flattenEquiv : ChunkedGenome chunks loci chromosomes ≃
    WholeGenome (chunks * loci) chromosomes where
  toFun := flatten
  invFun := fun genome chunk locus ↦ genome (finProdFinEquiv (chunk, locus))
  left_inv := by intro genome; funext chunk locus; exact flatten_pair genome chunk locus
  right_inv := by
    intro genome
    funext site
    change genome (finProdFinEquiv (finProdFinEquiv.symm site)) = genome site
    rw [Equiv.apply_symm_apply]

noncomputable def genomeLaw
    (laws : Fin chunks → FiniteReportLaw (WholeGenome loci chromosomes)) :
    FiniteReportLaw (WholeGenome (chunks * loci) chromosomes) :=
  (chunkLaw laws).pushforward flatten

/-- Exact nonlinear readouts act on the concatenated whole genome. -/
theorem genomeLaw_expectation
    (laws : Fin chunks → FiniteReportLaw (WholeGenome loci chromosomes))
    (readout : WholeGenome (chunks * loci) chromosomes → ℝ) :
    (genomeLaw laws).expectation readout =
      ∑ genome, (∏ chunk, (laws chunk).mass (genome chunk)) * readout (flatten genome) := by
  rw [genomeLaw, expectation_pushforward]
  rfl

/-- Source choice precedes every chunk simulation; averaging source laws first
would erase the dependence induced by oversampling the chosen source. -/
noncomputable def sourceGenomeLaw {Source : Type*} [Fintype Source]
    (source : FiniteReportLaw Source)
    (laws : Source → Fin chunks → FiniteReportLaw (WholeGenome loci chromosomes)) :
    FiniteReportLaw (Source × WholeGenome (chunks * loci) chromosomes) :=
  source.joint (fun trainingSource ↦ genomeLaw (laws trainingSource))

theorem sourceGenome_expectation {Source : Type*} [Fintype Source]
    (source : FiniteReportLaw Source)
    (laws : Source → Fin chunks → FiniteReportLaw (WholeGenome loci chromosomes))
    (readout : Source × WholeGenome (chunks * loci) chromosomes → ℝ) :
    (sourceGenomeLaw source laws).expectation readout =
      ∑ trainingSource, source.mass trainingSource *
        (∑ genome, (∏ chunk, (laws trainingSource chunk).mass (genome chunk)) *
          readout (trainingSource, flatten genome)) := by
  rw [sourceGenomeLaw, expectation_joint]
  simp_rw [genomeLaw_expectation]
  rfl

section Stream

variable {individuals length : ℕ}
  (cohort : FiniteReportLaw (Fin individuals)) (genome : WholeGenome length (2 * individuals))

/-- MAF is computed from raw allele-index dosages, exactly as in the stream
filter. The subsequent BED clipping is not substituted into this calculation. -/
noncomputable def minorAlleleFrequency (site : Fin length) : ℝ :=
  let frequency := cohort.expectation (fun individual ↦
    (rawDiploidDosage genome site individual : ℝ)) / 2
  min frequency (1 - frequency)

noncomputable def eligibleSites (threshold : ℝ) : Finset (Fin length) :=
  (retainedSites genome).filter (fun site ↦ threshold ≤ minorAlleleFrequency cohort genome site)

theorem mem_eligibleSites (threshold : ℝ) (site : Fin length) :
    site ∈ eligibleSites cohort genome threshold ↔
      (genome site).2.2 = true ∧ threshold ≤ minorAlleleFrequency cohort genome site := by
  simp [eligibleSites, mem_retainedSites]

noncomputable def eligibleOrder (threshold : ℝ) :
    Fin (eligibleSites cohort genome threshold).card ↪ Fin length :=
  ((eligibleSites cohort genome threshold).orderEmbOfFin rfl).toEmbedding

theorem eligibleOrder_mem (threshold : ℝ)
    (index : Fin (eligibleSites cohort genome threshold).card) :
    eligibleOrder cohort genome threshold index ∈ eligibleSites cohort genome threshold :=
  Finset.orderEmbOfFin_mem (eligibleSites cohort genome threshold) rfl index

theorem eligibleOrder_strictMono (threshold : ℝ) :
    StrictMono (eligibleOrder cohort genome threshold) :=
  ((eligibleSites cohort genome threshold).orderEmbOfFin rfl).strictMono

/-- The exact ordered reservoir law receives the genotype-derived eligible
stream, including its random length and increasing physical site order. Its
output indices retain access to every raw dosage in the fixed whole genome. -/
noncomputable def eligibleReservoir (threshold : ℝ) (requested : ℕ) :
    FiniteReportLaw (Slots (min requested (eligibleSites cohort genome threshold).card) length) :=
  (completeLaw requested (eligibleSites cohort genome threshold).card).pushforward
    (fun slots ↦ slots.trans (eligibleOrder cohort genome threshold))

theorem eligibleReservoir_expectation (threshold : ℝ) (requested : ℕ)
    (readout : Slots (min requested (eligibleSites cohort genome threshold).card) length → ℝ) :
    (eligibleReservoir cohort genome threshold requested).expectation readout =
      (completeLaw requested (eligibleSites cohort genome threshold).card).expectation
        (fun slots ↦ readout (slots.trans (eligibleOrder cohort genome threshold))) := by
  exact expectation_pushforward _ _ _

/-- Raw causal/PCA columns and clipped BED columns are decoded separately
from the same selected physical site, retaining the simulator's two encodings. -/
def selectedRawDosage {kept : ℕ} (slots : Slots kept length)
    (slot : Fin kept) (individual : Fin individuals) : ℕ :=
  rawDiploidDosage genome (slots slot) individual

def selectedBedDosage {kept : ℕ} (slots : Slots kept length)
    (slot : Fin kept) (individual : Fin individuals) : ℕ :=
  bedDiploidDosage genome (slots slot) individual

theorem selectedBedDosage_eq_clip {kept : ℕ} (slots : Slots kept length)
    (slot : Fin kept) (individual : Fin individuals) :
    selectedBedDosage genome slots slot individual =
      min (selectedRawDosage genome slots slot individual) 2 := rfl

end Stream


/-- A finite dependent joint law retains random reservoir lengths instead of
assuming that every simulated genome supplies the requested number of sites. -/
noncomputable def dependentJoint {A : Type*} [Fintype A] {B : A → Type*}
    [∀ a, Fintype (B a)] (law : FiniteReportLaw A) (kernel : ∀ a, FiniteReportLaw (B a)) :
    FiniteReportLaw (Sigma B) where
  mass := fun output ↦ law.mass output.1 * (kernel output.1).mass output.2
  mass_nonneg := fun output ↦ mul_nonneg (law.mass_nonneg output.1)
    ((kernel output.1).mass_nonneg output.2)
  mass_sum := by
    rw [Fintype.sum_sigma]
    simp only [← Finset.mul_sum, FiniteReportLaw.mass_sum, mul_one]

/-- The genotype distribution and the conditional ordered sampling law both
remain inside the readout used for subsequent training and accuracy. -/
theorem dependentJoint_expectation {A : Type*} [Fintype A] {B : A → Type*}
    [∀ a, Fintype (B a)] (law : FiniteReportLaw A) (kernel : ∀ a, FiniteReportLaw (B a))
    (readout : Sigma B → ℝ) :
    (dependentJoint law kernel).expectation readout =
      law.expectation (fun a ↦ (kernel a).expectation (fun b ↦ readout ⟨a, b⟩)) := by
  unfold expectation dependentJoint
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  ring

section PairedReservoirs

variable {individuals length : ℕ} (cohort : FiniteReportLaw (Fin individuals))

abbrev ReservoirPair (genome : WholeGenome length (2 * individuals)) (causalCount : ℕ) :=
  Slots (min 5000 (eligibleSites cohort genome (1 / 20)).card) length ×
    Slots (min (max (causalCount * 8) 2000)
      (eligibleSites cohort genome (1 / 100)).card) length

/-- Separate PCA and causal random streams are independent conditional on the
same realized genome. They share its MAF filtering and may retain common sites. -/
noncomputable def reservoirPairLaw (genome : WholeGenome length (2 * individuals))
    (causalCount : ℕ) : FiniteReportLaw (ReservoirPair cohort genome causalCount) :=
  (eligibleReservoir cohort genome (1 / 20) 5000).joint (fun _ ↦
    eligibleReservoir cohort genome (1 / 100) (max (causalCount * 8) 2000))

theorem reservoirPair_expectation (genome : WholeGenome length (2 * individuals))
    (causalCount : ℕ) (readout : ReservoirPair cohort genome causalCount → ℝ) :
    (reservoirPairLaw cohort genome causalCount).expectation readout =
      (eligibleReservoir cohort genome (1 / 20) 5000).expectation (fun pca ↦
        (eligibleReservoir cohort genome (1 / 100) (max (causalCount * 8) 2000)).expectation
          (fun causal ↦ readout (pca, causal))) :=
  expectation_joint _ _ _

/-- The chosen source is retained together with its genome and both ordered
reservoirs. Reservoir cardinalities depend on that genome, so this joint state
uses a dependent pair rather than a fixed-size placeholder. -/
noncomputable def sourceGenomeReservoirLaw {Source : Type*} [Fintype Source]
    (genomes : FiniteReportLaw (Source × WholeGenome length (2 * individuals)))
    (causalCount : ℕ) :
    FiniteReportLaw ((base : Source × WholeGenome length (2 * individuals)) ×
      ReservoirPair cohort base.2 causalCount) :=
  dependentJoint genomes (fun base ↦ reservoirPairLaw cohort base.2 causalCount)

theorem sourceGenomeReservoir_expectation {Source : Type*} [Fintype Source]
    (genomes : FiniteReportLaw (Source × WholeGenome length (2 * individuals))) (causalCount : ℕ)
    (readout : ((base : Source × WholeGenome length (2 * individuals)) ×
      ReservoirPair cohort base.2 causalCount) → ℝ) :
    (sourceGenomeReservoirLaw cohort genomes causalCount).expectation readout =
      genomes.expectation (fun base ↦
        (eligibleReservoir cohort base.2 (1 / 20) 5000).expectation (fun pca ↦
          (eligibleReservoir cohort base.2 (1 / 100) (max (causalCount * 8) 2000)).expectation
            (fun causal ↦ readout ⟨base, pca, causal⟩))) := by
  rw [sourceGenomeReservoirLaw, dependentJoint_expectation]
  simp_rw [reservoirPair_expectation]

end PairedReservoirs

/-- Actual default geometry: twenty independent five-megabase chunk laws with
one common uniformly drawn source, preserving the source-dependent sample size. -/
noncomputable def defaultSerialGenomeLaw :
    FiniteReportLaw (Fin 10 × WholeGenome 100000000
      (SimulationDemographyLaw.cohortSize 10 * 2)) :=
  sourceGenomeLaw (chunks := 20) (SourceDesignLaw.sourceLaw 10 (by decide))
    (fun source _ ↦ SimulationDemographyLaw.serialGenomeLaw 5000000 (by decide) source)

noncomputable def defaultGridGenomeLaw :
    FiniteReportLaw (Fin 36 × WholeGenome 100000000
      (SimulationDemographyLaw.cohortSize 36 * 2)) :=
  sourceGenomeLaw (chunks := 20) (SourceDesignLaw.sourceLaw 36 (by decide))
    (fun source _ ↦ SimulationDemographyLaw.gridGenomeLaw 5000000 (by decide) source)

/-- The default complete genotype-to-reservoir input law for the serial model. -/
noncomputable def defaultSerialReservoirLaw (causalCount : ℕ) :
    FiniteReportLaw ((base : Fin 10 × WholeGenome 100000000 14500) ×
      ReservoirPair (uniform (Fin 7250)) base.2 causalCount) :=
  sourceGenomeReservoirLaw (uniform (Fin 7250)) defaultSerialGenomeLaw causalCount

/-- The default complete genotype-to-reservoir input law for the grid model. -/
noncomputable def defaultGridReservoirLaw (causalCount : ℕ) :
    FiniteReportLaw ((base : Fin 36 × WholeGenome 100000000 27500) ×
      ReservoirPair (uniform (Fin 13750)) base.2 causalCount) :=
  sourceGenomeReservoirLaw (uniform (Fin 13750)) defaultGridGenomeLaw causalCount

end Descent.Portability.ChunkedGenotypeLaw
