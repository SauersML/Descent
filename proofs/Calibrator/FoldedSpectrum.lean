import Calibrator.BundleRigidity
import Calibrator.EffectSizeSurgery
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Fin.VecNotation

namespace Calibrator

open scoped BigOperators

/-!
# The folded spectrum, ascertainment ties, and what a matched spectrum does not explain

This file is about **one bundle family** — the standardized diploid genotype at allele
frequency `q` — read through the modulus map of `Calibrator.BundleRigidity`. Everything
here is a statement about allele-frequency spectra of marker panels and about which
summary statistics can see them.

## The objects, spelled out

At frequency `q` a locus contributes three atoms. Atom `j ∈ {0,1,2}` is the standardized
dosage `a_j(q) = (j - 2q) / √(2q(1-q))` and carries the Hardy-Weinberg mass
`((1-q)², 2q(1-q), q²)`. The three atoms move together under one parameter — that is
what makes the family a *bundle*, and it is the only reason anything below is true. The
modulus curve is `m_j(q) = |a_j(q)² - 1|`, the value taken by `|U|` for `U = X² - 1` the
centered squared standardized dosage. `spectrumModulusLaw` sends a panel's
allele-frequency spectrum to the law of `|U|` across the panel.

*Naming discipline.* The functional named here is the law of `|U|`, and the scalar named
below is the **mean inverse heterozygosity** `E_q[1/(2q(1-q))]`. No statement here is
about "F_ST": estimators of differentiation differ in their denominators and disagree by
large factors away from the symmetric point, so an identifiability claim is meaningful
only relative to a named functional. (`Conventions.hudsonFst`, whatever its name says,
computes Nei's `G_ST`; nothing in this file depends on it.)

## THE STANDING HYPOTHESIS: INDEPENDENT LOCI. IT IS IN THE SIGNATURES.

`spectrumModulusLaw` is a *mixture over loci*: it treats a panel as a bag of independent
one-locus laws. Reading it as "what LD-score regression, variance-component heritability
or a heterozygosity summary sees" requires the panel to be in **linkage equilibrium**,
which is stated here as `InLinkageEquilibrium` and carried as an explicit hypothesis of
the headline theorems rather than mentioned in a remark.

This is a **structural limitation of the method, not a gap to be filled later.** The
surrounding theory factors a panel's characteristic function as a product over loci, and
dependence destroys that factorization outright. Every claim below is therefore a claim
about a linkage-equilibrium idealization of a panel, and real panels are not that.
Extending any of it to linked loci is open and is not attempted here.

## What is new here and what is not

Almost nothing in the machinery is new, and the docstrings are written to that
calibration.

* The kernel statement of §1 is **the polarization problem**: from unpolarized data one
  recovers the **folded** site frequency spectrum and no more. Population genetics has
  known this for decades. It appears here as a *validation* that the formalism reproduces
  a known fact, not as a discovery.
* The peeling argument of `BundleRigidity` is the classical lightning-bolt argument for
  sums of weighted compositions (Diliberto–Straus, Marshall–O'Farrell), on the measure
  side.

What is not standard is that the *same* peeling machinery that yields the folded-spectrum
fact then decides identifiability of the folded spectrum itself, and that it does so for
tied weights with moving analytic atoms.
-/

/-! ## 0. The standing independence hypothesis -/

/-- **Linkage equilibrium**: the panel's joint genotype law is the product of its
per-locus Hardy-Weinberg laws.

This is the hypothesis under which a panel may be read as a mixture over loci, which is
what `spectrumModulusLaw` computes. It is carried explicitly by the headline theorems
below. Under linkage disequilibrium the joint law is not of this form, the factorization
the surrounding theory relies on fails, and none of the statements below are claimed. -/
def InLinkageEquilibrium {k n : ℕ} (family : BundleFamily k) (panel : Panel n)
    (joint : (Fin n → Fin k) → ℝ) : Prop :=
  ∀ g : Fin n → Fin k, joint g = ∏ i : Fin n, family.atomMass (g i) (panel.support i)

/-! ## 1. The diploid bundle family -/

/-- The genotype standard deviation `√(2q(1-q))` at frequency `q`. -/
noncomputable def diploidStdev (q : ℝ) : ℝ := Real.sqrt (2 * q * (1 - q))

/-- The standardized dosage of genotype `j ∈ {0,1,2}` at frequency `q`:
`(j - 2q)/√(2q(1-q))`. -/
noncomputable def diploidAtomValue (j : Fin 3) (q : ℝ) : ℝ :=
  ((j : ℝ) - 2 * q) / diploidStdev q

/-- The Hardy-Weinberg mass of genotype `j` at frequency `q`. The three masses are locked
to one parameter; this is what makes the family a bundle. -/
noncomputable def diploidAtomMass (j : Fin 3) (q : ℝ) : ℝ :=
  if j = 0 then (1 - q) ^ 2 else if j = 1 then 2 * q * (1 - q) else q ^ 2

/-- **The diploid bundle family**: standardized genotypes with Hardy-Weinberg masses. -/
noncomputable def diploidFamily : BundleFamily 3 :=
  { atomValue := diploidAtomValue, atomMass := diploidAtomMass }

/-- Relabelling which allele is called the alternate one: genotype `j ↦ 2 - j`. -/
def genotypeFlip3 : Fin 3 → Fin 3 := ![2, 1, 0]

theorem genotypeFlip3_involutive : Function.Involutive genotypeFlip3 := by
  intro j
  fin_cases j <;> rfl

theorem genotypeFlip3_cast (j : Fin 3) : ((genotypeFlip3 j : Fin 3) : ℝ) = 2 - (j : ℝ) := by
  fin_cases j <;> norm_num [genotypeFlip3]

/-! ## 2. The allele-label gauge: this is the folded spectrum

The reflection `τ(q) = 1 - q` is the choice of which allele is called the alternate one.
It is not a biological degree of freedom. The theorems here say that modulus data cannot
see it, which is the statement that unpolarized data determines the **folded** site
frequency spectrum and nothing beyond it.
-/

theorem diploidStdev_reflect (q : ℝ) : diploidStdev (1 - q) = diploidStdev q := by
  unfold diploidStdev
  congr 1
  ring

/-- **Reflection negates the standardized dosage after relabelling the genotype.**
`a_j(1-q) = -a_{2-j}(q)`. -/
theorem diploidAtomValue_reflect (j : Fin 3) (q : ℝ) :
    diploidAtomValue j (1 - q) = -diploidAtomValue (genotypeFlip3 j) q := by
  unfold diploidAtomValue
  rw [diploidStdev_reflect, ← neg_div, genotypeFlip3_cast]
  congr 1
  ring

/-- **Reflection swaps the two homozygote masses and fixes the heterozygote.** -/
theorem diploidAtomMass_reflect (j : Fin 3) (q : ℝ) :
    diploidAtomMass j (1 - q) = diploidAtomMass (genotypeFlip3 j) q := by
  fin_cases j <;> · simp only [diploidAtomMass, genotypeFlip3, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
                   norm_num
                   ring

/-- **The modulus curve is reflection-invariant up to relabelling**: `m_j(1-q) = m_{2-j}(q)`.

This is the step that must be checked rather than assumed. The corpus proves that the
standardized dosage *negates* under reflection; what is needed for modulus data is that
the *squared* dosage is unchanged, which is a strictly weaker statement and is what holds
here. -/
theorem diploid_modulus_reflect (j : Fin 3) (q : ℝ) :
    diploidFamily.modulus j (1 - q) = diploidFamily.modulus (genotypeFlip3 j) q := by
  unfold BundleFamily.modulus diploidFamily
  simp only
  rw [diploidAtomValue_reflect, neg_pow, neg_one_sq, one_mul]

/-- **A locus and its reflection put the same mass on every modulus value.**

Values and masses are permuted together by the same genotype relabelling, so the whole
per-locus law of `|U|` is invariant — not merely its moments. -/
theorem diploid_massAt_reflect (q v : ℝ) :
    diploidFamily.massAt (1 - q) v = diploidFamily.massAt q v := by
  unfold BundleFamily.massAt
  refine Fintype.sum_equiv genotypeFlip3_involutive.toPerm _ _ (fun j => ?_)
  have hmod : diploidFamily.modulus j (1 - q) = diploidFamily.modulus (genotypeFlip3 j) q :=
    diploid_modulus_reflect j q
  have hmass : diploidFamily.atomMass j (1 - q) = diploidFamily.atomMass (genotypeFlip3 j) q :=
    diploidAtomMass_reflect j q
  simp only [Function.Involutive.coe_toPerm]
  rw [hmod, hmass]

/-- The panel with every frequency reflected: `q ↦ 1 - q` at every locus. -/
def Panel.reflect {n : ℕ} (panel : Panel n) : Panel n :=
  { support := fun i => 1 - panel.support i, weight := panel.weight }

/-- **THE ALLELE-LABEL GAUGE THEOREM (the folded spectrum).**

A panel and its reflection have the *same* modulus law. Modulus data therefore determines
an allele-frequency spectrum at best up to `q ↔ 1 - q` at every locus.

**This is the polarization problem and it is not new.** Without an outgroup to polarize
ancestral against derived alleles, the site frequency spectrum is recoverable only in its
folded form; that has been standard population genetics for decades. Its role here is as
a positive control: a framework that failed to produce this kernel would be wrong. That
it appears as the exact kernel direction predicted by the abstract theory is evidence the
formalism is wired up correctly.

**It is a gauge, not a non-identifiability.** Which allele is labelled "alternate" changes
no biology. So the identifiability question worth asking is about the *folded* spectrum,
on `q ∈ (0, 1/2]`, which is where minor allele frequency lives and which `Panel.fold`
below constructs. -/
theorem foldedSpectrum_gauge {n : ℕ} (panel : Panel n) (v : ℝ) :
    spectrumModulusLaw diploidFamily panel.reflect v =
      spectrumModulusLaw diploidFamily panel v := by
  unfold spectrumModulusLaw Panel.reflect
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp only
  rw [diploid_massAt_reflect]

/-- **The reflection-odd part of a spectrum lies in the kernel of the modulus map.**

`L(ν - τ_*ν) = 0` for every panel `ν`, with `τ(q) = 1 - q`. This is the abstract
statement of the same fact: the odd part in the polarization coordinate is invisible. -/
theorem reflection_odd_in_kernel {n : ℕ} (panel : Panel n) (v : ℝ) :
    spectrumModulusLaw diploidFamily panel v -
      spectrumModulusLaw diploidFamily panel.reflect v = 0 := by
  rw [foldedSpectrum_gauge, sub_self]

/-! ## 3. Folding to minor allele frequency -/

/-- The folded panel: every locus moved to `min q (1-q)`, its minor allele frequency. -/
noncomputable def Panel.fold {n : ℕ} (panel : Panel n) : Panel n :=
  { support := fun i => min (panel.support i) (1 - panel.support i),
    weight := panel.weight }

theorem diploid_massAt_fold (q v : ℝ) :
    diploidFamily.massAt (min q (1 - q)) v = diploidFamily.massAt q v := by
  rcases le_total q (1 - q) with h | h
  · rw [min_eq_left h]
  · rw [min_eq_right h, diploid_massAt_reflect]

/-- **Folding changes no modulus statistic.** Every panel is modulus-equivalent to a panel
supported on minor allele frequencies, so nothing is lost by asking the identifiability
question on `(0, 1/2]`. -/
theorem fold_preserves_modulusLaw {n : ℕ} (panel : Panel n) (v : ℝ) :
    spectrumModulusLaw diploidFamily panel.fold v =
      spectrumModulusLaw diploidFamily panel v := by
  unfold spectrumModulusLaw Panel.fold
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp only
  rw [diploid_massAt_fold]

/-- The folded panel really is a minor-allele-frequency panel. -/
theorem fold_support_le_half {n : ℕ} (panel : Panel n) (i : Fin n) :
    panel.fold.support i ≤ 1 / 2 := by
  unfold Panel.fold
  simp only
  rcases le_total (panel.support i) (1 - panel.support i) with h | h
  · rw [min_eq_left h]; linarith
  · rw [min_eq_right h]; linarith

theorem fold_support_nonneg {n : ℕ} (panel : Panel n) (i : Fin n)
    (h0 : 0 ≤ panel.support i) (h1 : panel.support i ≤ 1) :
    0 ≤ panel.fold.support i := by
  unfold Panel.fold
  simp only
  exact le_min h0 (by linarith)

/-! ## 4. Ascertainment ties: the checkable warning

The abstract failure mode is a modulus curve that is *constant on a set of positive
measure*. Biologically that is a panel carrying many markers at the **same** allele
frequency: a fixed-MAF simulation grid, or an ascertained genotyping array whose markers
were selected to sit in a narrow frequency band. The theorems here say exactly what goes
wrong, and they are checkable on a real panel by looking at its frequency column.
-/

/-- A panel has an **ascertainment tie** when two distinct loci sit at the same
frequency. -/
def HasFrequencyTie {k n : ℕ} (_family : BundleFamily k) (panel : Panel n) : Prop :=
  ∃ i l : Fin n, i ≠ l ∧ panel.support i = panel.support l

/-- **A tie destroys separation, for every bundle family.**

Peeling needs each locus to own a modulus value outright. Two loci at the same frequency
own exactly the same values, so neither owns anything, and the peeling route to
identifiability is unavailable on such a panel. This is a hypothesis check a
methodologist can run: duplicate entries in the frequency column void the rigidity
theorem. -/
theorem not_separating_of_frequencyTie {k n : ℕ} (family : BundleFamily k)
    (panel : Panel n) (i l : Fin n) (hne : i ≠ l)
    (htie : panel.support i = panel.support l) :
    ¬ Separating family panel := by
  intro hsep
  obtain ⟨v, hcover, hothers⟩ := hsep i
  exact hcover (by rw [htie]; exact hothers l hne)

/-- **A tie is not merely an obstruction to the proof: it is a genuine non-identifiability.**

Move weight `c` from one tied locus to the other. The modulus law does not change — the
two loci are the same locus as far as `|U|` is concerned — so no moment-based or
LD-score-based statistic can tell the panels apart. On an ascertained array, the *split*
of weight among markers sharing a frequency is not estimable at all, and any procedure
reporting it is reporting its prior. -/
theorem frequencyTie_gives_kernel {n : ℕ} (panel : Panel n) (i l : Fin n) (hne : i ≠ l)
    (htie : panel.support i = panel.support l) (c v : ℝ) :
    spectrumModulusLaw diploidFamily
      { support := panel.support,
        weight := fun m => if m = i then c else if m = l then -c else 0 } v = 0 := by
  unfold spectrumModulusLaw
  simp only
  rw [Finset.sum_eq_add_of_mem i l (Finset.mem_univ i) (Finset.mem_univ l) hne]
  · simp only [if_pos rfl, if_neg hne.symm, if_pos rfl]
    rw [htie]
    ring
  · intro m _ hm
    rw [if_neg hm.1, if_neg hm.2, zero_mul]

/-- The same statement in its smallest concrete instance: two markers at frequency `q`,
weights `c` and `-c`, produce no modulus signal at any value. A fixed-MAF grid is this
configuration repeated. -/
theorem tied_pair_invisible (q c v : ℝ) :
    spectrumModulusLaw diploidFamily { support := ![q, q], weight := ![c, -c] } v = 0 := by
  unfold spectrumModulusLaw
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  ring

/-! ## 5. The three-level hierarchy, each level with its escaping quantity -/

/-- **Mean inverse heterozygosity**, `1/(2q(1-q))` at a locus. Averaged over a panel this
is the fourth moment of the standardized dosage — the first thing any moment-based method
learns about a frequency spectrum. -/
noncomputable def invHeterozygosity (q : ℝ) : ℝ := 1 / (2 * q * (1 - q))

/-- **Level one, what is determined**: the fourth moment of the standardized dosage at a
locus is exactly its inverse heterozygosity. Averaged over a panel in linkage
equilibrium, low-order moment data delivers `E_q[1/(2q(1-q))]` and that is a genuine,
recoverable functional of the spectrum. -/
theorem diploid_fourth_moment (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1) :
    ∑ j : Fin 3, diploidAtomMass j q * diploidAtomValue j q ^ 4 = invHeterozygosity q := by
  have hs : (0 : ℝ) < 2 * q * (1 - q) := by nlinarith
  have hsq : Real.sqrt (2 * q * (1 - q)) ^ 2 = 2 * q * (1 - q) := Real.sq_sqrt hs.le
  have h4 : ∀ j : Fin 3,
      diploidAtomValue j q ^ 4 = ((j : ℝ) - 2 * q) ^ 4 / (2 * q * (1 - q)) ^ 2 := by
    intro j
    unfold diploidAtomValue diploidStdev
    rw [div_pow]
    congr 1
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hsq]
  simp only [Fin.sum_univ_three, h4, diploidAtomMass, invHeterozygosity]
  norm_num
  field_simp
  ring

/-- **Level one, what escapes: the dispersion.**

Two panels can agree exactly in mean inverse heterozygosity and differ in its variance
across loci. The escaping quantity is a **between-locus** quantity, and the mixture has
already integrated over `q` before any low-order moment is taken, so no amount of
low-order moment data recovers it.

Stated as: matching the mean forces the second moments apart whenever the two loci differ.
The hypothesis is the matched mean; the conclusion is that the dispersion is not
matched. -/
theorem dispersion_escapes_low_moments (q₁ q₂ q₃ : ℝ)
    (hmean : invHeterozygosity q₁ + invHeterozygosity q₂
      = invHeterozygosity q₃ + invHeterozygosity q₃)
    (hne : invHeterozygosity q₁ ≠ invHeterozygosity q₂) :
    invHeterozygosity q₁ ^ 2 + invHeterozygosity q₂ ^ 2
      ≠ invHeterozygosity q₃ ^ 2 + invHeterozygosity q₃ ^ 2 := by
  set a := invHeterozygosity q₁
  set b := invHeterozygosity q₂
  set c := invHeterozygosity q₃
  have hpos : 0 < (a - b) ^ 2 :=
    lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 (sub_ne_zero.mpr hne)))
  intro hcontra
  nlinarith [hpos, hmean, hcontra]

/-- **Level two: full modulus data on a separating panel pins the whole spectrum.**

This is `spectrum_determined_of_separating` restated for the diploid family with its
standing hypotheses visible: finitely many loci, linkage equilibrium, no ascertainment
tie (which `Separating` already excludes, by `not_separating_of_frequencyTie`).

Note what is and is not claimed. **A realized panel is finite** — `n` loci, `n`
frequencies — and finiteness is in the hypothesis, doing real work: `Separating` asks each
locus to own a value, which needs a list to pick a minimum from. The continuum
idealization of the same spectrum has full core for this family (every modulus value is
covered at least four times on `(0,1)` and twice above), so the peeling criterion does not
apply there and identifiability of a continuous spectrum from modulus data is **open**. -/
theorem folded_spectrum_identifiable_on_finite_panel {n : ℕ} (panel : Panel n)
    (joint : (Fin n → Fin 3) → ℝ)
    (_hLinkageEquilibrium : InLinkageEquilibrium diploidFamily panel joint)
    (hsep : Separating diploidFamily panel)
    (hkernel : ∀ v : ℝ, spectrumModulusLaw diploidFamily panel v = 0) (i : Fin n) :
    panel.weight i = 0 :=
  spectrum_determined_of_separating diploidFamily panel hsep hkernel i

/-! ## 6. Matched low-order functionals, and what portability loss cannot be blamed on -/

/-- An estimator **reads through a finite list of spectrum functionals** when it is a
fixed linear combination of the panel averages of finitely many test functions. Most
summary-statistic methods are of this shape by construction. -/
def ReadsThroughFunctionals {n m : ℕ} (T : Panel n → ℝ) (φ : Fin m → ℝ → ℝ) : Prop :=
  ∃ c : Fin m → ℝ, ∀ panel : Panel n,
    T panel = ∑ a : Fin m, c a * ∑ i : Fin n, panel.weight i * φ a (panel.support i)

/-- **No leakage: matching finitely many functionals matches every estimator built from
them.** -/
theorem matched_functionals_give_equal_estimates {n m : ℕ} (T : Panel n → ℝ)
    (φ : Fin m → ℝ → ℝ) (hT : ReadsThroughFunctionals T φ) (panel other : Panel n)
    (hmatch : ∀ a : Fin m,
      ∑ i : Fin n, panel.weight i * φ a (panel.support i)
        = ∑ i : Fin n, other.weight i * φ a (other.support i)) :
    T panel = T other := by
  obtain ⟨c, hc⟩ := hT
  rw [hc, hc]
  exact Finset.sum_congr rfl (fun a _ => by rw [hmatch a])

/-- **THE PORTABILITY DECOMPOSITION.**

Two populations whose panels agree on the matched functional produce identical values of
*every* estimator that reads through it, even though their spectra differ — by
`dispersion_escapes_low_moments` the two panels here differ in the dispersion of inverse
heterozygosity, which is a real difference in the site frequency spectrum.

The consequence is a decomposition with teeth: **portability loss between two such
populations cannot be attributed to spectrum shape alone**, because the spectra differ
while the matched summaries do not. Whatever portability gap is observed must come from
outside the matched family — causal effect-size differences, ascertainment, gene-environment
interplay, or linkage disequilibrium. It is falsifiable by simulation: match the
functional, simulate both spectra, and any residual gap localizes the cause.

**The tension, not papered over.** This decomposition inherits the standing independent-loci
hypothesis, and linkage disequilibrium is one of the very residual terms it pushes the
explanation into. So the argument narrows the candidates only within a class of models
that excludes one of the candidates it names. That is a real weakness of the statement
and it is the same open problem flagged at the top of this file. -/
theorem portability_gap_not_attributable_to_spectrum (q₁ q₂ q₃ : ℝ)
    (hmean : invHeterozygosity q₁ + invHeterozygosity q₂
      = invHeterozygosity q₃ + invHeterozygosity q₃)
    (T : Panel 2 → ℝ) (hT : ReadsThroughFunctionals T ![invHeterozygosity]) :
    T { support := ![q₁, q₂], weight := ![1 / 2, 1 / 2] }
      = T { support := ![q₃, q₃], weight := ![1 / 2, 1 / 2] } := by
  refine matched_functionals_give_equal_estimates T _ hT _ _ (fun a => ?_)
  fin_cases a
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.head_fin_const]
  linarith [hmean]

/-! ## 7. The pair theorem -/

/-- **THE PAIR THEOREM. The frequency spectrum is recoverable from summary statistics and
the effect-size architecture is not.**

Two verdicts from the same data, in one statement:

* *(left)* On a finite, linkage-equilibrium, separating panel, modulus data determines the
  allele-frequency spectrum completely — no per-locus frequency information supplied.
* *(right)* On the effect-size side, every **even** summary — heritability `E[β²]`,
  LD-score regression on squared z-scores, stratified heritability, method-of-moments
  polygenicity — is constant on the fibers of the magnitude map, so a redistribution of
  effect mass between `+s` and `-s` is invisible to all of them at once.

**The reason for the difference is structural, and it is worth saying without any of the
machinery.** Genotype atoms come in *bundles*: the three genotype values and their three
Hardy-Weinberg masses are locked to a single parameter `q`, so moving mass in the spectrum
moves values and masses together and cannot be hidden. Effect sizes carry no such lock:
mass at `+s` and mass at `-s` are free to trade, and even summaries read only their sum.
Hardy-Weinberg is what makes frequency spectra rigid, and effect-size distributions have
no analogue of it.

Practical reading: frequency-spectrum inference from summary statistics is on firmer
ground than usually assumed, and effect-size asymmetry should not be inferred from
moment-based summaries at all — the signs are in the data, and the summaries in use
discard them (`odd_summary_detects_transfer` says which statistics recover them). -/
theorem spectrum_recoverable_architecture_not {n : ℕ} (panel : Panel n)
    (joint : (Fin n → Fin 3) → ℝ)
    (_hLinkageEquilibrium : InLinkageEquilibrium diploidFamily panel joint)
    (hsep : Separating diploidFamily panel)
    (hkernel : ∀ v : ℝ, spectrumModulusLaw diploidFamily panel v = 0)
    (F : Fiber) (shift : ℝ) {summary : ℝ → ℝ} (heven : IsEvenSummary summary) :
    (∀ i : Fin n, panel.weight i = 0) ∧
      (F.transfer shift).contribution summary = F.contribution summary :=
  ⟨fun i => spectrum_determined_of_separating diploidFamily panel hsep hkernel i,
    F.even_summary_blind_to_transfer heven shift⟩

/-!
## What is left open, plainly

* **Linkage disequilibrium.** Every statement above assumes independent loci, and the
  factorization the method rests on does not survive dependence. This is the named
  limitation, not a to-do.
* **The continuum spectrum.** The diploid family's core is full, so the peeling criterion
  says nothing about a continuously distributed spectrum. Whether the folded continuum
  spectrum is identifiable from modulus data is open.
* **The tail regime.** The exponentially tilted versions of these statements are the ones
  that govern large deviations — polygenic score tails and quadratic-form statistics such
  as heritability estimators and GRM spectra, which is the regime clinical risk
  stratification actually runs in. Nothing here is proved in the tilted setting.
-/

end Calibrator
