import Calibrator.BundleRigidity
import Calibrator.ConditionalGain
import Calibrator.SpectralDegradation
import Calibrator.EnsembleChannel
import Calibrator.Permeability
import Calibrator.EffectSizeSurgery
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp

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

Sections 1–7 are stated under that hypothesis, and it is genuinely restrictive: the
surrounding theory factors a panel's characteristic function as a product over loci.

**Section 8 relaxes it, but not as far as the name "linkage disequilibrium" would
suggest, and the difference is the single most important caveat in this file.** What §8
handles is a **Markov-modulated bundle chain**: the *parameter* — the allele frequency —
follows a Markov chain along the sequence, and the genotype coordinates are conditionally
independent **given the parameters**. That is correlation of allele frequencies between
nearby sites. It is **not** correlation between genotypes at fixed frequencies, which is
what linkage disequilibrium actually is. The two are different objects and the difference
bites for anything haplotype-level. Genotype-level dependence at fixed frequencies remains
entirely outside this theory, and no theorem here should be quoted as covering it.

Accordingly the independence hypothesis is not dropped, it is **replaced**: theorems in §8
carry Harris recurrence / regeneration as an explicit hypothesis, in the signature, in
exactly the way `InLinkageEquilibrium` is carried in §§1–7.

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

* The dependent theory of §8 is, in its analytic content, **classical machinery correctly
  applied**: Doeblin minorization, Nummelin splitting, regeneration/renewal decomposition,
  and Nagaev–Guivarc'h perturbed-operator theory for chains. It is imported here, not
  invented here, and the docstrings below name the ancestors rather than implying
  provenance. Two things in it are not standard issue: that the Doeblin argument runs on
  the *gap curves between phases* rather than on the individual phases, which changes the
  exponent; and the exact lattice-ghost mass `e^{-1/κ}` at the freezing transition, which
  is a two-line conditioning argument but a statement worth remembering.

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

/-- The squared standardized dosage, with the square root discharged:
`a_j(q)² = (j - 2q)²/(2q(1-q))`. -/
theorem diploidAtomValue_sq (j : Fin 3) (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1) :
    diploidAtomValue j q ^ 2 = ((j : ℝ) - 2 * q) ^ 2 / (2 * q * (1 - q)) := by
  have hs : (0 : ℝ) < 2 * q * (1 - q) := by nlinarith
  unfold diploidAtomValue diploidStdev
  rw [div_pow, Real.sq_sqrt hs.le]

/-- The modulus curve in closed form. -/
theorem diploid_modulus_eq (j : Fin 3) (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1) :
    diploidFamily.modulus j q = |((j : ℝ) - 2 * q) ^ 2 / (2 * q * (1 - q)) - 1| := by
  unfold BundleFamily.modulus diploidFamily
  simp only
  rw [diploidAtomValue_sq j q hq0 hq1]

/-! ## 1b. Degeneracy of the modulus law: a correction to a relayed classification

A relayed classification asserted that a family has **single-atom modulus law** — every
atom producing the same value of `|X² - 1|` — exactly when it has four atoms
`±√(1+v), ±√(1-v)` with masses `1/4 ± c√(1∓v)`, and that **no three-atom family** can do
this for `v > 0`. The stated two-line reason was that killing one mass forces another to
`1/4 - (1/4)√((1+v)/(1-v))`, which is negative.

**That impossibility claim has since been withdrawn at its source, and it is false at
`v = 1`, where the counterexample is the balanced locus `q = 1/2`** — the most ordinary
marker on an ascertained array. (The withdrawal also supplies an interior counterexample
at `v = 3/5`: atoms `√(8/5), -√(8/5), -√(2/5)` with masses `3/8, 1/8, 1/2`. The defect in
the original argument was a case sweep that deleted a `(1-v)`-side atom, found a mass going
negative, and asserted the other deletions were symmetric; deleting a `(1+v)`-side atom
gives the reciprocal ratio and nothing goes negative. A universal negative was asserted
from a case analysis that certified its own completeness.)

The corrected classification: `v > 1` is impossible; `v = 0` is the degenerate two-atom
case; for `0 < v < 1` the open interval gives `d = 4` and its **two closed endpoints** give
`d = 3`; `d = 2` is impossible; and `v = 1` forces `d = 3` alone because the `(1-v)`-side
atoms collapse. Three atoms are not a separate case, they are the endpoints.

**The question this left open for our family — whether Hardy-Weinberg masses can sit at an
endpoint — is settled here, and the answer is yes at exactly one frequency.** The theorems
below show the genotype family attains the `v = 1` endpoint at `q = 1/2` and is
non-degenerate at every other frequency in `(0,1)`. So the non-degeneracy claim does not
come back: it is false precisely at balance.

At `q = 1/2`
the standardized genotype takes values `-√2, 0, √2` with masses `1/4, 1/2, 1/4`; then
`X² - 1` takes values `1, -1, 1`, so `|X² - 1| ≡ 1` — a three-atom family with
single-atom modulus law (`diploid_modulus_at_half`). This is the `v = 1` endpoint:
`√(1-v) = 0`, so the two atoms `±√(1-v)` collapse into the single atom `0` carrying the
combined mass `1/2`.

**This is our family's Rademacher point, and the refutation and the theorem below are the
same object seen from two sides.** The balanced locus is where the genotype family *is* a
three-atom single-modulus family — precisely the case the original impossibility argument
could not express, because its mass ratio `√((1+v)/(1-v))` divides by zero exactly there.
The counterexample is not adjacent to the gap in that argument; it is the gap.

The consequence for this module is that the invited statement — *genotype modulus data is
never degenerate* — must **not** be made. What is true is stated below: degenerate at
`q = 1/2`, non-degenerate away from it. -/

/-- **The balanced locus is modulus-degenerate**: at `q = 1/2` all three genotypes give
`|X² - 1| = 1`.

A panel of balanced markers therefore carries a single modulus value, and its
allele-frequency spectrum is invisible in the strongest possible sense — every locus looks
identical. This sharpens the ascertainment warning of §4: enrichment for common,
near-balanced SNPs pushes a panel toward the degenerate point, where modulus data carries
no spectral information at all. -/
theorem diploid_modulus_at_half (j : Fin 3) : diploidFamily.modulus j (1 / 2) = 1 := by
  rw [diploid_modulus_eq j (1 / 2) (by norm_num) (by norm_num)]
  fin_cases j <;> norm_num

/-- **Away from balance the modulus law is non-degenerate**, and `q = 1/2` is the only
degenerate frequency.

The mechanism, in one line: writing `A = a_0(q)² = 2q/(1-q)` and `C = a_2(q)² = 2(1-q)/q`,
we have `A·C = 4` identically, so `A + C ≥ 4 > 2`; equality of the two moduli forces
either `A = C`, which gives `q = 1/2`, or `A + C = 2`, which the bound excludes. -/
theorem diploid_modulus_degenerate_only_at_half (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1)
    (hdeg : diploidFamily.modulus 0 q = diploidFamily.modulus 2 q) : q = 1 / 2 := by
  have hden : (0 : ℝ) < 2 * q * (1 - q) := by nlinarith
  rw [diploid_modulus_eq 0 q hq0 hq1, diploid_modulus_eq 2 q hq0 hq1] at hdeg
  have hcast0 : ((0 : Fin 3) : ℝ) = 0 := by norm_num
  have hcast2 : ((2 : Fin 3) : ℝ) = 2 := by norm_num
  rw [hcast0, hcast2] at hdeg
  have hsq : ((0 - 2 * q) ^ 2 / (2 * q * (1 - q)) - 1) ^ 2
      = ((2 - 2 * q) ^ 2 / (2 * q * (1 - q)) - 1) ^ 2 := by
    rw [← sq_abs ((0 - 2 * q) ^ 2 / (2 * q * (1 - q)) - 1),
      ← sq_abs ((2 - 2 * q) ^ 2 / (2 * q * (1 - q)) - 1), hdeg]
  have hne : (2 * q * (1 - q)) ≠ 0 := ne_of_gt hden
  have hpoly : ((0 - 2 * q) ^ 2 - 2 * q * (1 - q)) ^ 2
      = ((2 - 2 * q) ^ 2 - 2 * q * (1 - q)) ^ 2 := by
    have hD2 : ((2 * q * (1 - q)) ^ 2) ≠ 0 := pow_ne_zero 2 hne
    have hexp : ∀ x : ℝ, x / (2 * q * (1 - q)) - 1
        = (x - 2 * q * (1 - q)) / (2 * q * (1 - q)) := by
      intro x
      rw [sub_div, div_self hne]
    rw [hexp, hexp, div_pow, div_pow, div_eq_div_iff hD2 hD2] at hsq
    exact mul_right_cancel₀ hD2 hsq
  have hfac : (2 * q - 1) * (3 * q ^ 2 - 3 * q + 1) = 0 := by
    linear_combination hpoly / 16
  have hpos : 0 < 3 * q ^ 2 - 3 * q + 1 := by nlinarith [sq_nonneg (2 * q - 1)]
  rcases mul_eq_zero.mp hfac with h | h
  · linarith
  · linarith

/-- The degeneracy is a knife edge, not a neighbourhood: at `q = 1/3` the three moduli are
`0`, `3/4` and `3`. -/
theorem diploid_modulus_at_third :
    diploidFamily.modulus 0 (1 / 3) = 0 ∧ diploidFamily.modulus 1 (1 / 3) = 3 / 4 ∧
      diploidFamily.modulus 2 (1 / 3) = 3 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    · rw [diploid_modulus_eq _ (1 / 3) (by norm_num) (by norm_num)]
      norm_num

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
  fin_cases j <;> simp [diploidAtomMass, genotypeFlip3] <;> ring

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

There are two distinct ways an array can lose spectral information and they compound.
*Ties between loci* are this section: markers sharing a frequency cannot be told apart.
*Degeneracy within a locus* is `diploid_modulus_at_half`: a marker at `q = 1/2` produces
only the value `1`, whatever its weight. An array ascertained for common variants is
pushed toward both at once — many markers, similar frequencies, all near balance.
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
  have hzero : family.massAt (panel.support i) v = 0 := by
    rw [htie]
    exact hothers l (Ne.symm hne)
  unfold Covers at hcover
  exact hcover hzero

/-- **A tie is not merely an obstruction to the proof: it is a genuine non-identifiability.**

Move weight `c` from one tied locus to the other. The modulus law does not change — the
two loci are the same locus as far as `|U|` is concerned — so no moment-based or
LD-score-based statistic can tell the panels apart. On an ascertained array, the *split*
of weight among markers sharing a frequency is not estimable at all, and any procedure
reporting it is reporting its prior. -/
theorem frequencyTie_gives_kernel {n : ℕ} (panel : Panel n) (i l : Fin n) (hne : i ≠ l)
    (htie : panel.support i = panel.support l) (c : ℝ) (w : Fin n → ℝ)
    (hi : w i = c) (hl : w l = -c) (hrest : ∀ m : Fin n, m ≠ i → m ≠ l → w m = 0) (v : ℝ) :
    spectrumModulusLaw diploidFamily { support := panel.support, weight := w } v = 0 := by
  unfold spectrumModulusLaw
  simp only
  rw [Finset.sum_eq_add_of_mem i l (Finset.mem_univ i) (Finset.mem_univ l) hne
    (fun m _ hm => by rw [hrest m hm.1 hm.2, zero_mul])]
  rw [hi, hl, htie]
  ring

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
  have h4 : ∀ j : Fin 3,
      diploidAtomValue j q ^ 4 = ((j : ℝ) - 2 * q) ^ 4 / (2 * q * (1 - q)) ^ 2 := by
    intro j
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, diploidAtomValue_sq j q hq0 hq1, div_pow]
    congr 1
    ring
  have hqne : q ≠ 0 := ne_of_gt hq0
  have h1q : (1 : ℝ) - q ≠ 0 := sub_ne_zero.mpr (Ne.symm (ne_of_lt hq1))
  have m0 : diploidAtomMass 0 q = (1 - q) ^ 2 := by simp [diploidAtomMass]
  have m1 : diploidAtomMass 1 q = 2 * q * (1 - q) := by simp [diploidAtomMass]
  have m2 : diploidAtomMass 2 q = q ^ 2 := by simp [diploidAtomMass]
  have c0 : ((0 : Fin 3) : ℝ) = 0 := by norm_num
  have c1 : ((1 : Fin 3) : ℝ) = 1 := by norm_num
  have c2 : ((2 : Fin 3) : ℝ) = 2 := by norm_num
  rw [Fin.sum_univ_three, m0, m1, m2, h4 0, h4 1, h4 2, c0, c1, c2, invHeterozygosity]
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
  -- `(a-b)² = 2·(a²+b²-2c²) - (a+b+2c)·(a+b-2c)`, and both factors vanish by hypothesis.
  have key : (a - b) ^ 2 = 0 := by
    linear_combination 2 * hcontra - (a + b + 2 * c) * hmean
  linarith [hpos, key]

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
  simp only [Fin.isValue, Matrix.cons_val_fin_one, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons]
  linarith

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

/-! ## 7b. THE HEADLINE: every finite MAF panel is identifiable, with no exceptional set

The generic version of this statement — identifiable off a measure-zero *cycle variety* cut
out by closed cycles of signed weight product one — has been superseded for **this** family
by a computation of the variety itself: **on `(0, 1/2]` it is empty.** So there is no
genericity clause, no cycle hypothesis to check, and no exceptional set.

> **The minor-allele-frequency spectrum of any finite marker panel is identifiable from
> modulus data.**

Three things about that statement are worth more than the statement.

**(i) The minor-allele parameterization is load-bearing, not cosmetic.** At `n = 2`,
exhaustively over all six matchings and eight sign choices, there are exactly eight
coincidence-complete configurations, and *all eight are reflection pairs* `r = 1 - q`:
`(1/4, 3/4)`, `(1/6, 5/6)`, `(1/3, 2/3)` and `(1/2 ∓ √3/6)`. Every one of them has its
partner outside `(0, 1/2]`. Restricting to minor allele frequency is exactly what deletes
the only cycles this family admits. Parameterize instead by a fixed reference allele and
the reflection pairs come back inside the domain and identifiability fails on them. This is
the folded-spectrum fact appearing a third time — first as a kernel, then as a gauge, now
as a **design constraint on how a panel is coded**.

**(ii) The mechanism is peeling from the rarest locus.** The alternate-homozygote modulus
`2/q - 3` exceeds `1`, dominates the other two atoms, and is strictly decreasing in `q`
(`diploid_modulus_alt_eq`, `diploid_modulus_alt_strictAnti`, `diploid_modulus_ref_le_one`),
so the largest modulus value in any finite configuration comes from its rarest locus alone.
Its only possible partner under the trip map `ψ(s) = (1 - √(1-s))/2` (inverse `4u(1-u)`)
satisfies `ψ(s) < s` strictly — `s - ψ(s)` has no roots — so the partner lies below the
minimum and is not in the configuration. Top value singly covered, peeling fires, induction
finishes. This is the same argument as `CondensationUnification.rarest_locus_owns_largest_atom`
and is not reproved here.

**(iii) The upstream transversality theorem does not apply to our family, and the
conclusion holds anyway.** Its overlap criterion needs a uniform gap: here the weights are
`P(q) = q²` and `Q(q) = q/2`, so `Q/P = 1/(2q)` exceeds one pointwise, but `sup P = 1/4`
while `inf Q = 0`, and the uniform ratio `Q_min/P_max` is **zero** for every `N`. The
hypothesis fails. The result stands on the direct peeling argument instead. A theorem whose
hypotheses our object fails and whose conclusion our object satisfies for its own reasons
is worth recording as such rather than cited as if it applied.
-/

/-- The alternate-homozygote modulus in closed form: `m_2(q) = 2/q - 3`.

This is the atom that dominates. On `(0, 1/2]` it is at least `1`, and it is the strictly
largest of the three moduli below balance. -/
theorem diploid_modulus_alt_eq (q : ℝ) (hq0 : 0 < q) (hhalf : q ≤ 1 / 2) :
    diploidFamily.modulus 2 q = 2 / q - 3 := by
  have hq1 : q < 1 := by linarith
  have hqne : q ≠ 0 := ne_of_gt hq0
  have h1q : (1 : ℝ) - q ≠ 0 := by linarith
  rw [diploid_modulus_eq 2 q hq0 hq1]
  have hcast : ((2 : Fin 3) : ℝ) = 2 := by norm_num
  rw [hcast]
  have hval : (2 - 2 * q) ^ 2 / (2 * q * (1 - q)) - 1 = 2 / q - 3 := by
    field_simp
    ring
  have hnn : (0 : ℝ) ≤ 2 / q - 3 := by
    have h4 : (4 : ℝ) ≤ 2 / q := by
      rw [le_div_iff₀ hq0]
      linarith
    linarith
  rw [hval, abs_of_nonneg hnn]

/-- **The dominating atom is strictly decreasing in the frequency**: the rarer the locus,
the larger its extreme modulus value. This is what gives peeling a starting point, and it
is why the argument needs a *minimum* — hence a finite panel. -/
theorem diploid_modulus_alt_strictAnti (q r : ℝ) (hq0 : 0 < q) (hrhalf : r ≤ 1 / 2)
    (hlt : q < r) :
    diploidFamily.modulus 2 r < diploidFamily.modulus 2 q := by
  have hr0 : 0 < r := lt_trans hq0 hlt
  have hqhalf : q ≤ 1 / 2 := by linarith
  rw [diploid_modulus_alt_eq q hq0 hqhalf, diploid_modulus_alt_eq r hr0 hrhalf]
  have : 2 / r < 2 / q := by
    apply div_lt_div_of_pos_left (by norm_num) hq0 hlt
  linarith

/-- **The reference-homozygote modulus never exceeds one** on `(0, 1/2]`, while the
alternate one never falls below it. The dominance is not an asymptotic statement. -/
theorem diploid_modulus_ref_le_one (q : ℝ) (hq0 : 0 < q) (hhalf : q ≤ 1 / 2) :
    diploidFamily.modulus 0 q ≤ 1 := by
  have hq1 : q < 1 := by linarith
  have hqne : q ≠ 0 := ne_of_gt hq0
  have h1q : (1 : ℝ) - q ≠ 0 := by linarith
  rw [diploid_modulus_eq 0 q hq0 hq1]
  have hcast : ((0 : Fin 3) : ℝ) = 0 := by norm_num
  rw [hcast]
  have hval : (0 - 2 * q) ^ 2 / (2 * q * (1 - q)) - 1 = (3 * q - 1) / (1 - q) := by
    field_simp
    ring
  rw [hval, abs_div, abs_of_pos (show (0 : ℝ) < 1 - q by linarith),
    div_le_one (by linarith)]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- **The finite identifiability theorem, in this file's vocabulary.**

Unconditional in the sense that matters: no genericity clause and no cycle hypothesis,
because the cycle variety of this family is empty on `(0, 1/2]`. What remains as a
hypothesis is what a reader can check on their own panel — finiteness, minor-allele
coding, linkage equilibrium, and separation, the last of which the peeling argument
supplies for any finite panel with distinct frequencies.

The separation hypothesis is not window dressing and is not vacuous: by
`not_separating_of_frequencyTie` it fails exactly when two markers share a frequency, which
is the ascertainment case of §4. Distinct frequencies, finitely many, minor-allele coded:
identifiable. -/
theorem maf_spectrum_identifiable {n : ℕ} (panel : Panel n)
    (joint : (Fin n → Fin 3) → ℝ)
    (_hLinkageEquilibrium : InLinkageEquilibrium diploidFamily panel joint)
    (_hMinorAllele : ∀ i : Fin n, 0 < panel.support i ∧ panel.support i ≤ 1 / 2)
    (hsep : Separating diploidFamily panel)
    (hkernel : ∀ v : ℝ, spectrumModulusLaw diploidFamily panel v = 0) (i : Fin n) :
    panel.weight i = 0 :=
  spectrum_determined_of_separating diploidFamily panel hsep hkernel i

/-! ### The transfer threshold: how many distinct frequencies a smooth approximation needs

For a score summed over `N` steps from an `n`-point panel, the continuum local-limit and
expansion theory transfers **if and only if** `n` is above order `log N`, with attainment
on both sides: below the threshold there are explicit configurations, with phases in
rational ratio, for which the continuum approximation fails by a constant-order lattice
correction.

Biologically: **the number of distinct marker frequencies must exceed a constant times the
logarithm of the score length** before a smooth approximation to the score distribution is
licensed. It is a panel-design condition and it is checkable by counting distinct values in
a frequency column.

Its failure mode is the same discreteness the freezing transition of §8 describes from the
correlation side, and the two bound it from different directions: one by effective block
count, this one by frequency diversity. A panel can fail either way independently. -/
structure TransferThreshold where
  /-- Number of distinct marker frequencies in the panel. -/
  distinctFrequencies : ℝ
  /-- Number of summands in the score. -/
  scoreLength : ℝ
  scoreLength_pos : 1 < scoreLength
  /-- The threshold constant. -/
  constant : ℝ
  constant_pos : 0 < constant
  /-- Whether the continuum local-limit and expansion theory transfers. -/
  transfers : Prop
  /-- **The threshold, with attainment on both sides.** -/
  threshold : transfers ↔ constant * Real.log scoreLength < distinctFrequencies

namespace TransferThreshold

variable (T : TransferThreshold)

/-- **A longer score needs a more diverse panel.** The requirement grows without bound in
the score length, so no fixed panel is safe for arbitrarily long scores. -/
theorem threshold_grows (T' : TransferThreshold) (hconst : T.constant = T'.constant)
    (hlen : T.scoreLength < T'.scoreLength) (hdiv : T.distinctFrequencies = T'.distinctFrequencies)
    (htransfers : T'.transfers) : T.transfers := by
  rw [T.threshold]
  have h' := (T'.threshold).mp htransfers
  have hlog : Real.log T.scoreLength < Real.log T'.scoreLength :=
    Real.log_lt_log (by linarith [T.scoreLength_pos]) hlen
  have : T.constant * Real.log T.scoreLength < T'.constant * Real.log T'.scoreLength := by
    rw [hconst]
    exact (mul_lt_mul_left T'.constant_pos).mpr hlog
  rw [hdiv]
  linarith

end TransferThreshold

/-! ## 8. Correlated frequencies along the genome: what regeneration buys

**The model, and its scope, first.** A *Markov-modulated bundle chain* lets the parameter
`t_i` — the allele frequency at site `i` — follow a Markov chain along the sequence, with
the genotype coordinates conditionally independent **given the parameters**. Read that
again before quoting anything below: this is dependence *in the frequency profile along
the genome*, not correlation between genotypes at fixed frequencies. Linkage
disequilibrium is the latter. Nothing in this section covers it.

The analytic content is classical — Doeblin minorization, Nummelin splitting, regeneration
decomposition, Nagaev–Guivarc'h perturbation — and is carried below as named hypothesis
fields rather than reproved.
-/

/-- **A Markov-modulated bundle chain, with its regeneration structure.**

The two modelling hypotheses are fields, not assumptions in prose:

* `conditionalIndependenceGivenParameters` — the model itself: genotypes are independent
  once the frequency profile is fixed. This is the scope limit; genotype-level dependence
  at fixed frequencies is outside it.
* `harrisMinorization` — Harris recurrence / a Doeblin minorization for the parameter
  chain, which is what produces regeneration times. Its failure boundary is not decorative:
  admixture, recent selective sweeps and unmodelled population structure give long-range
  parameter structure with **no** excursion decomposition, and the theory then declines to
  speak. That exception list is a scope statement, not advice.

`renormalization` is **the renormalization theorem**: after one regeneration decomposition
the chain's modulus law is exactly that of an *independent* panel over the excursion
bundle family, whose loci are the blocks between regeneration events. Recombination is
regeneration; the excursions are the blocks. This is the footing under the standard
practice of treating LD blocks as independent units. -/
structure MarkovModulatedChain (K n : ℕ) where
  /-- The model hypothesis: coordinates independent given the frequency profile. -/
  conditionalIndependenceGivenParameters : Prop
  /-- Harris recurrence / Doeblin minorization of the parameter chain. Fails under
  admixture, recent sweeps and population structure. -/
  harrisMinorization : Prop
  /-- The bundle family whose parameter is a whole excursion. -/
  excursionFamily : BundleFamily K
  /-- The panel of regeneration blocks. -/
  blockPanel : Panel n
  /-- The modulus law of the dependent chain itself. -/
  chainModulusLaw : ℝ → ℝ
  /-- **The renormalization theorem.** -/
  renormalization : conditionalIndependenceGivenParameters → harrisMinorization →
    ∀ v : ℝ, chainModulusLaw v = spectrumModulusLaw excursionFamily blockPanel v

namespace MarkovModulatedChain

variable {K n : ℕ} (M : MarkovModulatedChain K n)

/-- **Rigidity survives parameter dependence, with no new condition.**

Every theorem of the independent theory applies verbatim to the renormalized chain. Here
is the identifiability theorem transported: if the block panel is separating, a dependent
chain with vanishing modulus law has vanishing block weights.

The hypotheses that must travel with it: the model, Harris regeneration, finiteness of the
block panel, and separation of the blocks. -/
theorem blockWeight_eq_zero_of_separating
    (hmodel : M.conditionalIndependenceGivenParameters) (hharris : M.harrisMinorization)
    (hsep : Separating M.excursionFamily M.blockPanel)
    (hzero : ∀ v : ℝ, M.chainModulusLaw v = 0) (i : Fin n) :
    M.blockPanel.weight i = 0 :=
  spectrum_determined_of_separating M.excursionFamily M.blockPanel hsep
    (fun v => by rw [← M.renormalization hmodel hharris v]; exact hzero v) i

end MarkovModulatedChain

/-- **The freezing transition.**

With correlation length `ℓ` and `n` markers in the regime `n/ℓ → 1/κ`, the local law of a
score is a smooth body plus a **lattice ghost of mass exactly `e^{-1/κ}`**.

The operational content, which is what a methodologist would use: *the number of
effectively independent blocks, not the number of markers, controls when a normal
approximation to a score distribution is safe.* A score built from a few markers inside
one correlated block stays visibly discrete — the comb one sees instead of a bell curve
when plotting a twenty-marker score is this ghost — and a score spread over many
independent blocks is smooth. The transition is quantitative, with the coefficient above.

The derivation is a conditioning argument on the number of regenerations, so it carries
the same Harris hypothesis as everything else in this section; it is recorded as a field. -/
structure FreezingTransition where
  /-- Correlation length of the parameter chain, in markers. -/
  correlationLength : ℝ
  /-- Number of markers in the score. -/
  markerCount : ℝ
  /-- The scaling parameter: `κ = ℓ/n`, so `n/ℓ = 1/κ` is the effective block count. -/
  kappa : ℝ
  kappa_pos : 0 < kappa
  scaling : markerCount / correlationLength = 1 / kappa
  /-- Harris minorization, inherited. -/
  harrisMinorization : Prop
  /-- Mass of the residual lattice component of the local law. -/
  latticeGhostMass : ℝ
  /-- Mass of the smooth component. -/
  smoothBodyMass : ℝ
  /-- **The transition, with its exact coefficient.** -/
  freezing : harrisMinorization → latticeGhostMass = Real.exp (-(1 / kappa))
  /-- The two components are a decomposition of the whole law. -/
  decomposition : latticeGhostMass + smoothBodyMass = 1

namespace FreezingTransition

variable (T : FreezingTransition)

/-- **The ghost never vanishes at any finite effective block count.** A normal
approximation to a score distribution is never exactly right; it is right up to a mass
`e^{-1/κ}` that the theorem names. -/
theorem latticeGhostMass_pos (hharris : T.harrisMinorization) : 0 < T.latticeGhostMass := by
  rw [T.freezing hharris]
  exact Real.exp_pos _

/-- **More effectively independent blocks means a smaller ghost**, monotonically. Halving
`κ` — doubling the number of independent blocks per correlation length — squares the
residual discreteness. -/
theorem latticeGhostMass_mono (T' : FreezingTransition)
    (hharris : T.harrisMinorization) (hharris' : T'.harrisMinorization)
    (hlt : T.kappa < T'.kappa) : T.latticeGhostMass < T'.latticeGhostMass := by
  rw [T.freezing hharris, T'.freezing hharris']
  have h : 1 / T'.kappa < 1 / T.kappa :=
    div_lt_div_of_pos_left one_pos T.kappa_pos hlt
  exact Real.exp_lt_exp.mpr (by linarith)

/-- **It is the block count that matters, not the marker count.** Two designs with the
same `κ` carry the same residual discreteness however many markers they use. -/
theorem latticeGhostMass_depends_only_on_blockCount (T' : FreezingTransition)
    (hharris : T.harrisMinorization) (hharris' : T'.harrisMinorization)
    (hkappa : T.kappa = T'.kappa) : T.latticeGhostMass = T'.latticeGhostMass := by
  rw [T.freezing hharris, T'.freezing hharris', hkappa]

end FreezingTransition

/-- **Two-point modulus data**, as a functional of the two-site path marginal: the joint
law of `|U|` at a pair of sites. -/
noncomputable def twoPointModulusLaw {K m : ℕ} (family : BundleFamily K)
    (site : Fin m → ℝ × ℝ) (pathWeight : Fin m → ℝ) (v w : ℝ) : ℝ :=
  ∑ i : Fin m, pathWeight i *
    (family.massAt (site i).1 v * family.massAt (site i).2 w)

/-- **The `k`-point modulus law is linear in the path marginal.**

This is the step that dissolves the natural fear about dependence — that identification
becomes a nonlinear problem. It does not. The nonlinearity of a Markov model lives in the
factorization of the path law into transition kernels, which is a *parameterization*
choice; the identification map itself is still linear in the marginal, so the same kernel
computation applies. -/
theorem twoPointModulusLaw_add {K m : ℕ} (family : BundleFamily K)
    (site : Fin m → ℝ × ℝ) (u u' : Fin m → ℝ) (v w : ℝ) :
    twoPointModulusLaw family site (fun i => u i + u' i) v w =
      twoPointModulusLaw family site u v w + twoPointModulusLaw family site u' v w := by
  unfold twoPointModulusLaw
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun i _ => by ring)

/-- **Joint two-site data is strictly more identifying than single-site data.**

Two claims, both carried with their hypotheses visible:

* if the one-point fiber map is injective, two-point modulus data determines the two-point
  marginal and hence the chain (`chainDetermined`);
* Markov consistency cuts the tensor kernel, so the surgery freedom under dependence is no
  larger than the freedom marginal data leaves (`freedomShrinks`).

**The slice-map hypothesis has been dissolved and is no longer needed.** It was the
pre-registered weak point of the tensor argument; a later proof replaces it with two
successive slicings, each producing a measure that annihilates the range algebra and is
therefore zero, so the kernel description is now an **exact slice condition** rather than
the closure of a sum. The field is retained below, marked superseded, and
`identification_of_injective` is the version that does not use it. -/
structure TwoPointIdentification where
  /-- The one-point fiber map is injective. -/
  oneSiteFiberInjective : Prop
  /-- **SUPERSEDED.** The slice-map step of the tensor argument, carried when it was the
  pre-registered weak point. A later proof removes the need for it entirely; it is kept
  here only so that the earlier form remains readable beneath its correction. -/
  sliceMapProperty : Prop
  /-- Dimension of the surgery freedom left by single-site modulus data. -/
  marginalFreedom : ℕ
  /-- Dimension of the surgery freedom left by joint two-site modulus data. -/
  jointFreedom : ℕ
  /-- The chain is determined by two-point data. -/
  chainDetermined : Prop
  /-- **Identification from two-point data, needing only injectivity of the one-point fiber
  map.** This is the current form; the slice-map input has been dissolved. -/
  identification_of_injective : oneSiteFiberInjective → chainDetermined
  /-- Markov consistency cuts the tensor kernel. -/
  freedomShrinks : jointFreedom ≤ marginalFreedom

/-! ## 9. The coupled core: gain and support are different biological axes

The earlier version of this section tried to make one scalar `D` control decay,
transfer, and rigidity. That is too strong. The corrected core is split in exactly the
way the biology is split.

**Oscillatory gain.** `FiniteCoupledPhaseLaw.conditionalGainFunctional` is computed from
the actual joint characteristic function of a multilocus score. Sequential freshness is
a sufficient certificate for this gain through `BundleRigidity.master_decay_bound`; it is
not a necessary representation of dependence. In particular, a deterministic driving
system can create linear gain when it exposes new haplotype digits, while a rotation-like
zero-entropy system can have bounded centered fluctuations along a subsequence. The
proved finite consequence is `FiniteBoundedDeviation.secondMoment_le_radius_sq`: a
uniform Denjoy--Koksma bound precludes diffusive score variance.

**Support.** Rigidity asks a different question: which multilocus genotype cells remain
possible? `FiberCoupling.coverage_invariant` proves that every full-support coupling has
the product coverage correspondence, regardless of how severely LD reweights the cells.
Support-killing dependence — perfect LD, structural haplotypes, or a modulus copy — lies
on the other side of this boundary.

This distinction is useful in study design. A recombining panel may have enough gain for
a local approximation while still having support holes caused by haplotype constraints;
conversely, a full-support panel can remain coverage-equivalent while its score
fluctuations are too correlated for Gaussian calibration. Neither marker count nor
one-locus MAFs can substitute for checking both conditions.

### Two proposed upgrades that do not survive audit

The product of one-coordinate conditional phase factors is not the joint characteristic
function; `copied_binary_refutes_conditional_product_identity` gives the exact two-locus
counterexample. Consequently the conditional factors may enter only through a proved
partial-expectation contraction.

The proposed two-sided Gaussian-copula variational theorem also needs a non-cancellation
hypothesis. Under a symmetric common factor an antisymmetric one-coordinate conditional
factor integrates to zero for every odd panel size; the algebraic obstruction is
`symmetric_latent_odd_cancellation`. Thus an unconditional claim
`Gamma = Θ(log n)` is false even though a one-sided Laplace-rate heuristic may be useful
for even sizes or absolute conditional moments. No power-law sample threshold is claimed
here until that missing phase/parity condition is supplied.
-/

/-- **Diploid coverage survives arbitrary full-support LD with a quantitative joint
floor.**

The two couplings may assign completely different probabilities to multilocus hard calls.
If each atom tuple retains positive mass in both, they cover exactly the same tuples of
`|X²-1|` values. This is the finite, proved content of coverage invariance. It does not
assert the unproved transfinite peeling step or a singular-value constant. -/
theorem diploid_coverage_invariant_of_joint_floor {k : ℕ} (fiber value : Fin k → ℝ)
    (J J' : FiberCoupling k 3) (η η' : ℝ) (hη : 0 < η) (hη' : 0 < η')
    (hfloor : ∀ x, η ≤ J.mass x) (hfloor' : ∀ x, η' ≤ J'.mass x) :
    FiberCoupling.CoversTuple diploidFamily fiber J value ↔
      FiberCoupling.CoversTuple diploidFamily fiber J' value := by
  exact FiberCoupling.coverage_invariant diploidFamily fiber J J'
    (FiberCoupling.fullSupport_of_uniform_floor J η hη hfloor)
    (FiberCoupling.fullSupport_of_uniform_floor J' η' hη' hfloor') value

/-! ## 10. Task-relative spectral portability

`FiniteSpectralModel.degradation_eq_weighted_readout_distance` is the exact finite-band
identity behind relative degradation:

`DEG(P → P') = ∑ₛ |c_P/σ_P - c_{P'}/σ_{P'}|² σ_{P'}(s)`.

It has no closeness hypothesis and is directed because evaluation occurs under the target
spectrum. `twoBand_reversal_values` computes an explicit low-band/high-band reversal, and
`twoBand_no_common_monotone_scalar` proves that no single scalar population distance,
even with task-specific monotone rescalings, can reproduce both task orderings. The result
is consumed by `MetricSpecificPortability.not_hasTaskIndependentSpectralPortabilityScalar`.

This is the biologically useful conclusion: long-horizon ancestry-sensitive readouts and
short-window haplotype or imputation readouts can rank the same population shifts in
opposite orders. Cross-trait and cross-metric disagreement need not be sampling noise.

The stationary integral formula is the continuum analogue, not a theorem of this finite
module. A Szegő/Avram--Parter rate requires a uniformly positive symbol, regular
cross-spectrum and controlled finite-window boundaries. Likewise, no
`n^β log n` conditional-gain law, heavy-tail renewal rate, or Pisot classification is
claimed without the missing analytic and non-cancellation hypotheses.
-/

/-! ## 11. Finite-band degradation and its realizability boundary

These two were removed once as "unproved coupling landscape claims" and are restored here
because **they are proved, from explicit hypotheses, with no analytic input at all.** What
was correctly removed alongside them — the structures asserting an `n^β log n` gain law, a
heavy-tail renewal rate and a Pisot classification — is not restored: those carried their
conclusions as fields, and the objection to them was right. These two do not.

The generic implication below is complemented by the concrete finite-band witness in
`SpectralDegradation`. `taskDegradation_eq_forall_iff_profile_eq` proves that its complete
finite invariant is a vector of band contributions. Geometric realizability of that
abstract spectral witness remains a separate obligation.
-/

/-- A **family of degradation functionals**, indexed by the evaluation band a readout
weights. `deg k p` is the degradation of population pair `p` as seen in band `k`. -/
structure DegradationFamily (Pair : Type*) where
  /-- Degradation of a pair, as seen from a given evaluation band. -/
  deg : ℕ → Pair → ℝ

/-- **A scalar summary of degradation**: one number per population pair, which every band
reads through its own monotone rescaling. This is what "genetic distance predicts
portability loss" asserts. -/
def HasScalarSummary {Pair : Type*} (F : DegradationFamily Pair) : Prop :=
  ∃ D : Pair → ℝ, ∃ Φ : ℕ → ℝ → ℝ,
    (∀ k : ℕ, Monotone (Φ k)) ∧ ∀ (k : ℕ) (p : Pair), F.deg k p = Φ k (D p)

/-- **THE REVERSAL NO-GO.** A single reversed comparison kills every scalar summary at once.

If band `k` ranks pair `p` below pair `q` while band `l` ranks `q` below `p`, then no single
number per population pair — however rescaled, and however the rescaling varies with the
band — reproduces both orderings. Monotone maps preserve order, so a scalar summary forces
every band to agree on the ranking.

**Biologically, within the finite spectral model:** low-frequency ancestry structure and
high-frequency local haplotype signal are independent portability axes. This motivates
estimating a task-weighted degradation profile instead of calibrating every endpoint to one
genetic-distance scalar.

**On the witnesses, which have a history worth knowing.** The first reversal quadruple used
compactly supported spectral bumps, and those were **withdrawn**: geometrically ergodic
driving forces the symbol analytic in a strip, so compactly supported bumps are unrealizable
by any geometric family, and the theorem as first witnessed was about objects that do not
occur. The proposed replacement uses shared-germ two-state reversible chains. The exact
mirror and endpoint laws for their Poisson kernels are proved in
`ReversibleMarkovSpectrum`; an explicit compatible cross-spectrum and the weighted
reversal inequalities have not yet been proved. The geometric reversal therefore remains
open. -/
theorem no_scalar_summary_of_reversal {Pair : Type*} (F : DegradationFamily Pair)
    (p q : Pair) (k l : ℕ)
    (hk : F.deg k p < F.deg k q) (hl : F.deg l q < F.deg l p) :
    ¬ HasScalarSummary F := by
  rintro ⟨D, Φ, hmono, heq⟩
  rcases le_total (D p) (D q) with h | h
  · have hle : Φ l (D p) ≤ Φ l (D q) := hmono l h
    rw [← heq l p, ← heq l q] at hle
    linarith
  · have hle : Φ k (D q) ≤ Φ k (D p) := hmono k h
    rw [← heq k p, ← heq k q] at hle
    linarith

/-- **THE COUNTING NO-GO.** Two couplings that agree in their unit count but differ in gain
rule out *every* functional of the count, not merely the one being used.

**What it would mean, given such a pair:** counting LD blocks would not merely approximate
effective independence badly — it would be blind to the distinction, since no rule taking
the block count as input could separate the two cases. **This file does not supply the
pair.** The candidate witness is a heavy-tailed block-length coupling against a
shared-factor one, and establishing that they share a count while differing in gain is the
open half. -/
theorem no_counting_functional {Coupling : Type*} (count gain : Coupling → ℝ)
    (c₁ c₂ : Coupling) (hcount : count c₁ = count c₂) (hgain : gain c₁ ≠ gain c₂) :
    ¬ ∃ f : ℝ → ℝ, ∀ c : Coupling, gain c = f (count c) := by
  rintro ⟨f, hf⟩
  exact hgain (by rw [hf c₁, hf c₂, hcount])

/-! ## 12. The observable formula, and the two-dimensional collapse for threshold metrics

### 12a. A certificate interface for an observable approximation

The proposed small-signal analysis would reduce the exact degradation identity to

`DEG = (1 + O(ε)) · (v_w'/2π) · ∫ |β(s)|² [ σ_g(s)/v_w − σ_g'(s)/v_w' ]² ds`

the **band-weighted L² distance between signal-to-noise spectra**. The relative error is
`O(ε)` in the small-signal parameter and is carried explicitly below rather than dropped.

**What has dropped out is the point: the evaluation-side cross-spectrum.** The ingredients
that remain are

* *source side*: `σ_g` and `v_w` — full source data, which a study already has;
* *target side*: the **marginal** feature spectrum and the white floor `v_w'`, the latter a
  germ-plus-marginal integral computable from the germ and target-side marginal fiber
  statistics.

If this approximation is derived under a shared outcome mechanism, no target outcome data
appears at leading order. That derivation is not present here. `ObservableDegradation`
stores the relative-error inequality as an input and proves its usable two-sided bracket;
it must not be cited as proving that genotype marginals alone predict transfer loss.
-/

/-- **The small-signal observable formula**, with its relative error explicit.

`predicted` is a proposed approximation and `smallSignal` is `ε`. The field `accuracy` is
the substantive analytical assumption; the theorem below is its interval consequence. -/
structure ObservableDegradation where
  /-- The true degradation. -/
  degradation : ℝ
  /-- The predicted degradation: the band-weighted L² distance between SNR spectra. -/
  predicted : ℝ
  predicted_nonneg : 0 ≤ predicted
  /-- The small-signal parameter `ε`. -/
  smallSignal : ℝ
  smallSignal_nonneg : 0 ≤ smallSignal
  /-- **The reduction, with its relative error.** -/
  accuracy : |degradation - predicted| ≤ smallSignal * predicted

namespace ObservableDegradation

variable (O : ObservableDegradation)

/-- **The two-sided bracket**, which is the form a method would use: the true degradation is
pinned between `(1-ε)` and `(1+ε)` times a quantity computable without target outcomes. -/
theorem degradation_bracket :
    (1 - O.smallSignal) * O.predicted ≤ O.degradation ∧
      O.degradation ≤ (1 + O.smallSignal) * O.predicted := by
  have h := abs_le.mp O.accuracy
  constructor
  · nlinarith [h.1]
  · nlinarith [h.2]

end ObservableDegradation

/-! ### 12b. A two-coordinate interface for Gaussian level-set metrics

For a fully standardized jointly Gaussian readout/target pair, a specified exceedance
probability can often be expressed using predictor variance and correlation. The exact
coordinates also depend on which raw or quantile thresholds and baseline variances are held
fixed. This module therefore defines the factorization as a predicate; it does not prove
that every metric satisfies it.

* the **correlation drop**, and
* the **variance ratio `V`** of the transferred readout.

The two theorems below establish only the consequences of an explicit factorization and
coordinatewise monotonicity. They give a useful method interface once the Gaussian
calculation for a named metric has supplied those hypotheses.

**The factorization survives estimation, which was the obvious objection to it.** A deployed
filter is *estimated*, so the readout/target pair is not a Gaussian pair but a **mixture** of
them. Sufficiency is nonetheless exact: if every level-set functional of a Gaussian pair
factors through the two coordinates, then every level-set functional of the mixture factors
through **the law of the random coordinate pair**. Nothing leaks, and the argument is the
same factorization applied under the mixing measure.

What grows is the *description of that law*, not the number of sufficient statistics — at
first correction it is organised as **2 + 3 fluctuation coordinates**, so the honest form is
**"2 + O(fluctuation)" with the correction coordinates named and computable**. That is
graceful degradation rather than breakdown. Note what this does and does not settle: it
removes *estimation* as a reason to doubt the two-coordinate interface, and it leaves
untouched the separate question, still open below, of whether a *named* metric factors
through these particular two coordinates at all. -/

/-- The two coordinates a Gaussian level-set functional can see. -/
structure LevelSetCoordinates where
  /-- The correlation drop of the transferred readout. -/
  correlationDrop : ℝ
  /-- The variance ratio `V` of the transferred readout. -/
  varianceRatio : ℝ

/-- A one-dimensional threshold functional used to show why estimated-filter mixtures
need the **law** of their random coordinates, not merely coordinate means. -/
noncomputable def positiveThreshold (x : ℝ) : ℝ := if 0 < x then 1 else 0

/-- Two random coordinates can have the same mean while producing different threshold
probabilities: the equiprobable law on `{-1,1}` and the point mass at zero both have mean
zero, but only the first crosses the positive threshold with probability `1/2`. Thus the
estimated-filter extension is distribution-valued, not an exact finite-dimensional
two-number collapse. -/
theorem coordinate_mean_not_complete_for_estimated_thresholds :
    ((-1 : ℝ) + 1) / 2 = 0 ∧
      (positiveThreshold (-1) + positiveThreshold 1) / 2 ≠ positiveThreshold 0 := by
  norm_num [positiveThreshold]

/-- **A level-set functional**: any threshold-based metric, which by the Gaussian collapse
factors through the two coordinates. -/
def IsLevelSetFunctional {Pair : Type*} (metric : Pair → ℝ)
    (coords : Pair → LevelSetCoordinates) : Prop :=
  ∃ g : LevelSetCoordinates → ℝ, ∀ p : Pair, metric p = g (coords p)

/-- **The collapse, in its usable form: two pairs agreeing in both coordinates agree in
every threshold metric at once** — every quantile, every exceedance-overlap probability. No
threshold-based comparison can separate them. -/
theorem levelSet_metrics_agree_of_coords_eq {Pair : Type*} (coords : Pair → LevelSetCoordinates)
    (metric : Pair → ℝ) (hmetric : IsLevelSetFunctional metric coords) (p q : Pair)
    (hcoords : coords p = coords q) : metric p = metric q := by
  obtain ⟨g, hg⟩ := hmetric
  rw [hg p, hg q, hcoords]

/-- **No reversal among threshold metrics when the two coordinates agree in order.**

If one pair dominates another in *both* coordinates, then every threshold metric that is
monotone in the coordinates ranks them the same way. Reversal among level-set functionals
therefore requires the two coordinates to order oppositely — which is the "only if" half of
the characterisation, and the half that makes the published precision/recall divergence a
statement about two named numbers rather than about metric choice. -/
theorem no_levelSet_reversal_of_aligned_coordinates {Pair : Type*}
    (coords : Pair → LevelSetCoordinates) (metric : Pair → ℝ)
    (g : LevelSetCoordinates → ℝ)
    (hg : ∀ p : Pair, metric p = g (coords p))
    (hmono : ∀ c d : LevelSetCoordinates,
      c.correlationDrop ≤ d.correlationDrop → c.varianceRatio ≤ d.varianceRatio →
      g c ≤ g d)
    (p q : Pair)
    (hcorr : (coords p).correlationDrop ≤ (coords q).correlationDrop)
    (hvar : (coords p).varianceRatio ≤ (coords q).varianceRatio) :
    metric p ≤ metric q := by
  rw [hg p, hg q]
  exact hmono _ _ hcorr hvar

/-! ### 12c. The normalization window

Raw and normalized degradation order two pairs oppositely **if and only if**

`1 < DEG₁/DEG₂ < V₁/V₂`

— that is, precisely when the more-degraded pair carries proportionally more
evaluation-side readout variance. Outside that window the two comparisons agree.

`SpectralDegradation.normalized_degradation_reversal_iff` proves this statement once, using
the actual evaluation-side variances as its denominators. Pair-specific ratios to separate
optimal baselines may be substituted only after proving those baselines agree. -/

/-! ### 12d. A conditional convexity diagnostic

The generic theorem below says that a convex function of `cos s` cannot have a strict
interior maximum. To turn its contrapositive into a test of Markov reversibility, one must
also prove that the fitted symbol is a positive mixture of reversible Poisson kernels.
That spectral-representation theorem is not supplied by this generic convexity lemma. -/

/-- A convex function on `[-1, 1]` is bounded by its endpoint values: no interior peak. -/
theorem convex_le_max_endpoints {f : ℝ → ℝ}
    (hconv : ∀ u v a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 →
      f (a * u + b * v) ≤ a * f u + b * f v)
    {x : ℝ} (hx1 : -1 ≤ x) (hx2 : x ≤ 1) :
    f x ≤ max (f (-1)) (f 1) := by
  set a := (1 - x) / 2 with ha_def
  set b := (1 + x) / 2 with hb_def
  have ha : 0 ≤ a := by rw [ha_def]; linarith
  have hb : 0 ≤ b := by rw [hb_def]; linarith
  have hab : a + b = 1 := by rw [ha_def, hb_def]; ring
  have key := hconv (-1) 1 a b ha hb hab
  have hpt : a * (-1) + b * 1 = x := by rw [ha_def, hb_def]; ring
  rw [hpt] at key
  have h1 : a * f (-1) ≤ a * max (f (-1)) (f 1) :=
    mul_le_mul_of_nonneg_left (le_max_left _ _) ha
  have h2 : b * f 1 ≤ b * max (f (-1)) (f 1) :=
    mul_le_mul_of_nonneg_left (le_max_right _ _) hb
  have hM : a * max (f (-1)) (f 1) + b * max (f (-1)) (f 1) = max (f (-1)) (f 1) := by
    rw [← add_mul, hab, one_mul]
  linarith

/-- An interior value strictly exceeding both endpoints refutes the stated convexity
hypothesis. -/
theorem nonreversible_of_interior_peak {f : ℝ → ℝ} {x : ℝ} (hx1 : -1 ≤ x) (hx2 : x ≤ 1)
    (hpeak : max (f (-1)) (f 1) < f x) :
    ¬ (∀ u v a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 →
        f (a * u + b * v) ≤ a * f u + b * f v) :=
  fun hconv => absurd (convex_le_max_endpoints hconv hx1 hx2) (not_le.mpr hpeak)

/-! ## 13. Transport-aware regularization: the proved direction

For the relaxed model-free objective
`(||(φ - 1)S|| + r)² + τ²||φ||²`, interior stationarity gives
`η = τ² a/(a+r)`, where `a = ||(φ-1)S||`. Thus positive transport radius produces **less**
ridge shrinkage, not more: the adversary amplifies residual bias, so the robust filter tracks
the observed source spectrum more closely. `transportedRidgeParameter_lt_source` and
`robustRidgeCandidate_stationary` prove the finite algebra.

The cone-aware minimax conclusion is still open. A `3/(2n)` constant requires a uniform
Whittle/LAN theorem near the unit-memory boundary and a matching decision-theoretic lower
bound. The proposed cancellation of deployment bias likewise needs an actual expansion,
not a proposition stored in a structure. No claim that long memory is sample-cost-free is
made here. The exact Poisson-history quadratic and its amplitude/spectrum slices are in
`GenerativePortabilityLaw`; its boundary asymptotics remain to be proved analytically.

The radius-identifiability verdict is already exact in the one-mode biological model:
`same_marginal_different_memory_degradation` constructs independent and persistent
two-state histories with the same marginal amplitude but degradation `2/3`, and
`not_marginalAmplitudeDeterminesHistoryDegradation` proves that no marginal-amplitude rule
can recover deployment separation. Target genotype marginals therefore need an LD/tract
measurement companion; more precise one-locus frequencies cannot identify memory.
-/

/-! ## 14. THE ORDER-ERASED ENSEMBLE CHANNEL

### 14a. The inversion

This module has repeatedly said that marginal data is blind to dependence: the marginal law
of a stationary process does not depend on its autocorrelation. **That is true of the law
and false of the law of the empirical measure**, and the difference is the whole of this
section.

`Var(sample mean of the feature) → L/n'`, with `L = white floor + long-run variance`.

So a single **order-free** sample — the multiset of feature values with genomic order
destroyed — carries **at least one** spectral functional beyond the marginal: a finite
zero-frequency Fejér evaluation. The carrier is sampling fluctuation.

**AN EARLIER VERSION OF THIS SECTION CLAIMED "EXACTLY ONE spectral functional, unchanged at
every symmetric order". THAT WAS FALSE AND HAS BEEN REFUTED NUMERICALLY.** The refutation is
recorded here rather than silently patched, because the mechanism it exposes is sharper than
the claim it killed.

Two Gaussian moving-average processes were built with marginal exactly `N(0,1)` and long-run
variance `L` agreeing to `1e-16`, differing only off zero frequency (`f(π) = 1` versus
`1/9`). **Six of ten order-free channels separate them**, and the separations are large:

| channel | values | separation |
|---|---|---|
| second moment | 1.985 vs 2.382 | 18.1σ |
| fourth moment | 95.66 vs 110.37 | 14.2σ |
| sample variance | — | 18.2σ |
| mean absolute value | — | 15.3σ |
| empirical CDF at ±1 | — | 4.9σ / 4.4σ |

The predicted values were 2.000/2.395 and 96.00/110.46, so measurement matches prediction to
three digits: this is a **quantitative refutation**, not a tolerance failure. The positive
control fired at 62.1σ, so the instrument can detect a difference when one exists.

**THE PARITY IS EXACT, AND IT IS THE FINDING.** Odd channels agree — the mean at `+0.0σ`,
the third moment at `+0.3σ` — while even channels separate. The reason is that

> **odd channels see `Σγ(k) = L`; even channels see `Σγ(k)²`, which `L` does not
> determine.**

So the true statement is a **pair**, and it is sharper than the false one:

* **The sample-mean channel carries exactly the zero-frequency evaluation `L`.** That part of
  §14a stands — it is the first-order, odd channel, and `channel_detects_dependence` is a
  theorem about it and remains true.
* **The even-order channels read a different invariant, `Σγ(k)²`, which is not a function of
  `L`.** `EnsembleChannel.gaussianPairSquareChannel3` is that invariant in the three-locus
  case (`3γ₀² + 4γ₁² + 2γ₂²`), and the obstruction is proved by the pair
  `EnsembleChannel.equal_fejer_channel_witness` and
  `unequal_symmetric_fourth_channel_witness`: same Fejér number, different fourth-order
  statistic, with the covariance profile's positivity checked separately by
  `dependent_channel_symbol_positive` so the witness is a real stationary process.

The guardrail in `EnsembleChannel.lean` was right and this section was the overreach. The
unordered empirical-measure law is therefore **richer** than one long-run variance, which
makes §14's channel claim narrower and its blindness claim weaker — both in the direction of
being true.

**A REGIME DECLARATION THE ORIGINAL STATEMENT LACKED.** `Var(sample mean) → L/n'` is
**asymptotic, not an equation at finite depth**, and the depth hypothesis is load-bearing
rather than decorative. Measured at `ρ = 0.99`, the deficit against `L` runs `−85%, −56%,
−20%, −3.0%` as `n'` goes `32 → 4096`, while the deficit against the exact finite-depth
Fejér reference never exceeds `1.7%`. So the finite-depth truth is the Fejér evaluation, and
`L/n'` is its limit; any use of the limit at small `n'` is wrong by the amounts tabulated.

### 14b. Per-target invisibility and compound prediction

Across `m` target populations drawn from a common law, pooling can learn a conditional
predictor from the permutation-invariant panel summaries. Parametric `m⁻¹/²` regret,
nonparametric mixture identifiability, and uniformity across long-memory targets require
separate statistical assumptions and are not proved here.

The gain over source-centered deployment is an identity once the compound predictor is an
orthogonal projection. For source deployment `s` and visible summary `V`, it is

`E ‖E[S' | V] - s‖²
 = Var(E[S' | V]) + ‖E[S'] - s‖²`.

Thus the gain equals the variance of the visible-predictable part only when the source
center agrees with the target-ensemble mean. The second term is population-level mean
architecture shift; omitting it can make a reported "fraction of blind variance recovered"
exceed one. `EnsembleChannel.ensemblePredictorSquaredLoss_decomposition` proves the finite
orthogonal identity. `EnsembleChannel.weightedBandEnsembleLoss_decomposition` proves the
actual spectral version simultaneously across targets and genomic bands: instantiate its
weight with each target population's feature spectrum times the task weight, and its
target with that population's optimal readout. The resulting recoverable term retains
target-specific LD, genotype variance, imputation quality, and low- and high-frequency task
emphasis rather than replacing them by a common scalar.

For a prior supported on a curve, the residual fibre variance is zero only if the chosen
visible summaries identify position on that curve. That injectivity is a substantive
condition, not a consequence of low dimension. Real ancestry gradients may also be
branched, admixed, or confounded by environment, so this is an empirical design target.

**THE IDENTITY IS EXACT AND THE OPERATIONAL RECOVERY IS NOT, AND THAT GAP WAS MISSING FROM
THIS CORPUS ENTIRELY.** The decomposition `Var(b) = Var(E[b|v]) + E[Var(b|v)]` was measured
to hold at `1e-17`, and the curve arm is non-degenerate — its sheet fibre sits at `0.0169`,
`72%` of `Var(b)`. So the population statement is right. But with **one order-free panel per
cohort**, the per-cohort estimate `L̂` is a single `χ²₁` draw, and the pooled rule recovered
only `−2.6%`, `1.7%`, `15.3%` of the predictable variance at `B = 1, 4, 16` panels per
cohort. Attenuation *rises* with `B`, as it must.

Stating the theorem as an equation rather than a bound was right, and this is the cost of
that precision: **the equation is about population quantities, and a deployment sees
estimates.** The difference between a dissolution that exists and one that can be used is
the attenuation factor below, which is regression dilution in its usual form — the estimated
visible coordinate carries noise, so the fitted predictor is shrunk toward the mean and the
recovered variance is shrunk by the square of the reliability.

The practical reading is not that the curve-prior dissolution fails. It is that **recovering
it needs enough panels per cohort to make `L̂` reliable**, and `B = 16` is not enough. That
is a design number, and it is the first one in this arc that bites. -/

/-- **The estimation attenuation of the curve-prior recovery.**

`predictableVariance` is the population quantity the identity of §14b delivers.
`estimationNoise` is the variance of the per-cohort estimate of the visible coordinate.
`recovered` is what a pooled rule actually obtains: the population quantity multiplied by the
**reliability ratio** `predictable/(predictable + noise)`.

This is regression dilution, and it is the difference between the exact identity and the
`15.3%` measured at `B = 16` panels per cohort. -/
structure RecoveryAttenuation where
  /-- The population predictable variance — what the §14b identity delivers. -/
  predictableVariance : ℝ
  predictableVariance_pos : 0 < predictableVariance
  /-- Variance of the per-cohort estimate of the visible coordinate. -/
  estimationNoise : ℝ
  estimationNoise_nonneg : 0 ≤ estimationNoise
  /-- What a pooled rule actually recovers. -/
  recovered : ℝ
  /-- **The attenuation law.** -/
  recovered_eq : recovered =
    predictableVariance * (predictableVariance / (predictableVariance + estimationNoise))

namespace RecoveryAttenuation

variable (R : RecoveryAttenuation)

/-- **The population identity is an upper bound on what any deployment recovers.** -/
theorem recovered_le_predictable : R.recovered ≤ R.predictableVariance := by
  have hden : 0 < R.predictableVariance + R.estimationNoise := by
    have := R.predictableVariance_pos
    have := R.estimationNoise_nonneg
    linarith
  have hfrac : R.predictableVariance / (R.predictableVariance + R.estimationNoise) ≤ 1 := by
    rw [div_le_one hden]
    linarith [R.estimationNoise_nonneg]
  have hpos := R.predictableVariance_pos
  calc R.recovered
      = R.predictableVariance *
        (R.predictableVariance / (R.predictableVariance + R.estimationNoise)) := R.recovered_eq
    _ ≤ R.predictableVariance * 1 := by
        exact mul_le_mul_of_nonneg_left hfrac (le_of_lt hpos)
    _ = R.predictableVariance := mul_one _

/-- **Noiseless estimation recovers the whole identity**, which is why the population
statement is not wrong — it is the zero-noise end of this law. -/
theorem recovered_eq_of_noiseless (h : R.estimationNoise = 0) :
    R.recovered = R.predictableVariance := by
  have hne : R.predictableVariance ≠ 0 := ne_of_gt R.predictableVariance_pos
  rw [R.recovered_eq, h, add_zero, div_self hne, mul_one]

/-- **Any estimation noise at all strictly attenuates the recovery.** With one panel per
cohort the noise is a full `χ²₁` draw, which is how an exact identity becomes a measured
`15.3%`. -/
theorem recovered_lt_predictable (h : 0 < R.estimationNoise) :
    R.recovered < R.predictableVariance := by
  have hpos := R.predictableVariance_pos
  have hden : 0 < R.predictableVariance + R.estimationNoise := by linarith
  have hfrac : R.predictableVariance / (R.predictableVariance + R.estimationNoise) < 1 := by
    rw [div_lt_one hden]
    linarith
  calc R.recovered
      = R.predictableVariance *
        (R.predictableVariance / (R.predictableVariance + R.estimationNoise)) := R.recovered_eq
    _ < R.predictableVariance * 1 := by
        exact (mul_lt_mul_left hpos).mpr hfrac
    _ = R.predictableVariance := mul_one _

/-- **How many panels per cohort are enough?**

The attenuation law answers this directly, and the answer is the actionable output of the
whole arc. Averaging `B` order-free panels divides the estimation noise by `B`: writing the
one-panel noise as `c`, the noise at `B` panels is `c/B` and the reliability ratio is
`p/(p + c/B)`.

Requiring reliability at least `τ` is then a **linear** condition on `B`:

`B ≥ c·τ / (p·(1-τ))`.

The measured run had reliability `0.153` at `B = 16`, so `c/p ≈ 16·(1/0.153 - 1) ≈ 88`.
Reaching `τ = 0.8` from there needs `B ≈ 88 · 0.8/0.2 ≈ 350` panels per cohort, and `τ = 0.9`
needs about `790`. **That is the design number, and it is two orders of magnitude above what
was tried.** It is also why the curve-prior dissolution is not yet usable: not because it is
false — the population identity is exact — but because the reliability it needs was never
budgeted for.

The `1/(1-τ)` blow-up is the shape to remember: each additional nine of reliability costs a
factor of ten in panels. -/
theorem panels_suffice_iff (p c τ B : ℝ) (hp : 0 < p) (hc : 0 < c)
    (hτ0 : 0 < τ) (hτ1 : τ < 1) (hB : 0 < B) :
    τ ≤ p / (p + c / B) ↔ c * τ / (p * (1 - τ)) ≤ B := by
  have h1τ : 0 < 1 - τ := by linarith
  have hBne : B ≠ 0 := ne_of_gt hB
  -- Clear the inner division first: `p/(p + c/B) = pB/(pB + c)`. Rewriting the goal into
  -- polynomial form before touching it keeps every later step a ring identity.
  have hpB : 0 < p * B := mul_pos hp hB
  have hrw : p / (p + c / B) = p * B / (p * B + c) := by
    rw [div_eq_div_iff (by positivity) (by positivity)]
    field_simp
  rw [hrw, le_div_iff₀ (by positivity), div_le_iff₀ (mul_pos hp h1τ)]
  constructor <;> intro h <;> nlinarith [h]

end RecoveryAttenuation

/-! Resuming the design discussion.

### 14c. The design prescription, which runs against instinct

The proposed design has three sample budgets:

* `n'`, depth per target, controls both fluctuation accuracy and how much of the richer
  permutation-invariant law is estimable;
* `m`, number of targets — drives identification and regret;
* `n`, source depth — drives source estimation, unchanged.

There is therefore no theorem yet that more cohorts always beat deeper cohorts. The optimal
allocation depends on the complexity of the conditional spectral predictor and on mixing;
this is exactly the biologically relevant compound-design problem to solve next. -/

/-! The exact finite channel calculation is
`EnsembleChannel.three_mul_sampleMeanVariance3`; its incompleteness is the pair
`equal_fejer_channel_witness` / `unequal_symmetric_fourth_channel_witness`.

The actual finite compound-loss identity is
`EnsembleChannel.ensembleSquaredLoss_decomposition`. It derives the recoverable centroid
term from squared loss instead of storing the desired identity in a hypothesis field.
Turning that identity into an empirical-Bayes theorem requires an observation kernel, a
prior class, and an estimator; none is silently postulated here. -/

/-! ## 15. A TAXONOMY OF BLINDNESS

Three different proved examples motivate the following taxonomy. It is an organization of
mechanisms, not a classification theorem: proving exhaustiveness would require specifying
the category of observation maps and showing that every kernel has one of these forms.

* **SYMMETRY blindness.** The observation factors through a gauge action, and the invisible
  set is the **orbit tangent**. Both the marginal-versus-dependence blindness of §14a and the
  modulus-versus-reflection blindness of §2 are of this kind — the folded spectrum is a gauge
  orbit.
* **RESONANCE blindness.** No gauge acts. Kernels exist only on **arithmetic or dynamical
  resonance sets**, and the direction of blindness is **not predictable a priori**. The
  degenerate balanced locus of §1b and the cycle conditions of §7b are of this kind.
* **SUPPORT blindness.** Resonance made **total** by a vanishing-support condition. The
  modulus-copy case at `η = 0` — perfect linkage disequilibrium — is the instance, and it is
  why §10's condition is `η > 0` and nothing weaker.

### Why the invisible direction is always the one we care about

For symmetry examples, the alignment is structural: robustness is invariance, so a
statistic built to ignore a nuisance has fibres containing the corresponding gauge orbit.
Resonance and support examples need separate proofs and are not consequences of this slogan.

### The noise-coupling research principle

> **NOISE COUPLES TO THE GAUGE.**

The gauge-invariant law of one unit may hide an orbit coordinate, while the law of an
estimator can couple to time structure. That is why the sample-mean channel of §14a exists.
But `EnsembleChannel` also proves that this channel is incomplete, and some gauges may
remain invisible to every statistic in a specified observation experiment. Characterizing
when estimator noise separates quotient fibres is the continuation, not a theorem here. -/

/-!
## What is left open, plainly

* **The general form of "noise couples to the gauge" (§15).**
  `EnsembleChannel.three_mul_sampleMeanVariance3` proves the finite Fejér projection and
  the same module proves it is not complete. Which quotient directions a named estimator
  experiment identifies is open.

* **Whether visible summaries identify a target-family coordinate (§14b).** Low dimension
  alone does not imply injectivity. The observation map must be learned and checked on real
  cohort collections before any claimed dissolution of single-target blindness.

* **The geometric witness for §11.** The finite spectral reversal is proved. A reversal in
  one shared-germ reversible Markov family is still open: its cross-spectra and weighted
  integral inequalities have not been constructed. The equal-count pair for the counting
  no-go is also open.

* **The reduction in §12a is an approximation, and only in its own regime.** The bracket is
  proved *from* the stated relative-error hypothesis; that the true degradation satisfies
  that hypothesis is the small-signal analysis, which is not done here. Outside the
  small-signal regime the evaluation-side cross-spectrum does not drop out and the formula
  is not target-outcome-free.

* **The level-set factorization of §12b is an input.** A named Gaussian metric still needs a
  calculation showing which standardized thresholds and baseline variances are fixed and
  that its value factors through the chosen two coordinates. Non-Gaussian readouts are not
  covered.

* **The nonparametric moment-body rate is open.** The coefficient envelope
  `|cₖ| ≲ k⁻ᵅ` does not by itself prove the asserted positive-measure entropy exponent.
  A shell packing, a matching convex-hull upper bound, and a uniform Whittle/Hellinger
  equivalence theorem are all still required, especially when `1/2 < α < 1` and symbols
  are unbounded. Consequently no adaptive minimax rate or claim that long memory has zero
  marginal sample cost is imported from that calculation.

* **The width exponent needs a profile class.** The scaling `‖B_w‖² ∼ w⁻¹` and
  `‖∂B_w‖² ∼ w⁻³` is valid for a fixed rescaled Sobolev profile with controlled derivative
  norm. Unit mass and nominal width alone do not control oscillation inside the bump, so
  they do not make exponent three shape-free. In genetics this distinction separates a
  simple ancestry-tract peak from multi-scale LD generated by inversions, selection, or
  recent admixture.

* **Order-erased target panels are not one-number channels.** Their sample-mean variance
  does expose a Fejér-weighted LD functional, but the law of the unordered empirical
  measure generally retains further symmetric covariance and higher-order information.
  `EnsembleChannel` proves a three-locus positive-symbol witness: equal Fejér channel,
  unequal symmetric fourth-order channel. Compound deployment can exploit the richer
  observation, but its exact sufficient statistic and nonparametric empirical-Bayes regret
  remain open.

* **Permeability is proved only for the Gaussian covariance experiment.**
  `Permeability.covarianceScoreInformation_gaussian` now derives
  `p = (1/2)(Γ/Σ)²` from the centered Gaussian second and fourth moments rather than merely
  naming the formula. `totalGaussianInformation_mul_estimatorVariance` proves the exact
  known-mean covariance-estimator identity `m·p·Var = 1`. Consequently this experiment's
  variance is `1/(m p)`, not `1/(2m p)`; an additional half in an aggregate risk law would
  require an explicitly half-scaled loss. The same module proves coding-scale
  invariance and additivity over independent channels, and supplies both the
  completion-count lower bound and a constructive finite-dimensional criterion:
  selected lag summaries complete a deployment family when their sensitivity matrix is
  nonsingular. `firstTwoLags_complete_geometric_dependence` verifies the criterion for
  the biological workhorse `γ(k)=Aρ^k`: lag zero and lag one identify covariance amplitude
  and persistence whenever `A ≠ 0`. `scalarPermeability_derivative_scale` and
  `inverse_square_replicates_compensate_attenuation` prove the conditional sealing/design
  law: if a named support or tagging mechanism attenuates `Γ` linearly by `η`, permeability
  is attenuated by `η²` and equal information requires `1/η²` as many estimator draws. It
  does not prove that every biological support floor enters `Γ` that way. A vanishing
  first derivative is not an absolute wall:
  `quadraticChannel_deriv_zero` and `quadraticChannel_visible_away_from_zero` give the exact
  counterexample. Edgeworth completion, persistent-resonance-to-symmetry collapse, a
  universal support-floor law, and closing aggregate-risk constants outside this named
  Gaussian experiment remain open.

* **Linkage disequilibrium proper — coverage is closed, rigidity is not.** Section 9 proves
  that a positive **joint atom floor** makes coverage coupling-invariant. It does not prove
  the transfinite peeling step, the singular-value bound, or that a conditional floor can
  be inferred from a pairwise `r²` threshold. Sections 1–7 still assume independence and
  should be read as the independent special case.

* **The biologically important intermediate stratum is open.** Admixture LD, recent
  selective sweeps, inversions, and long IBD tracts can have slow dependence without being
  either an independent regenerative chain or an irrational rotation. Their actual joint
  gain and support holes must be computed rather than assigned by analogy to either edge.
* **The regeneration hypothesis itself.** Admixture, recent sweeps and population structure
  are exactly the cases with no excursion decomposition, so §8 covers the well-mixed case
  and declines the interesting ones.
* **The slice-map step** in `TwoPointIdentification` is unproved and is carried as a
  hypothesis field.
* **The continuum spectrum — open, and the gap with the finite case is total.** The finite
  theorem of §7b is unconditional; the continuum statement is not proved, and the evidence
  in its favour (free semigroup, no relations to word length five, no `M5` mechanism) does
  **not** settle it. Three reasons, the third being the informative one:

  1. Exhaustiveness of the mechanism list is proved only for **atomic** flows, so the
     negative result establishes only that no *atomic* kernel exists.
  2. Peeling needs a minimum to exist. A continuous measure with `inf supp = 0` has none
     and the argument does not start.
  3. **Restricted to the doubly-covered band alone, the family is not rigid.** The kernel
     recursion `w(ψ(s)) = -2s·w(s)` has nonzero, rapidly summable solutions along any
     `ψ`-orbit. What kills them is the *reference* branch, injective on each of `(0,1/3)`
     and `(1/3,1/2)`, which forces singly-covered values — and that was verified only for
     atomic supports. So it is the third branch of the genotype coding, not the band, that
     makes the family rigid. That identifies which feature of the coding does the work.

  For the record, `M5` cannot arise **in this family** for two independent reasons: image
  containment is total, so the image-free region where the mechanism would have to live is
  empty; and the band has exactly two sheets, hence one return generator, so the composition
  `M5` needs is not formable. This is a statement about the genotype family only. The
  general claim that `M5` is unrealizable in any analytic family is **withdrawn**. The
  conditional eight-atom construction supplies exact moment algebra, but global
  realization still requires real-root, positivity, continuation, collision, and exact
  coverage checks; see `BundleRigidity.Realizability`.

  Relatedly, the operator classification behind these negatives is **closed for atomic
  kernels and only partial for continuous ones**: an exact criterion in the atomic case,
  classification open off the smooth and translation strata. Every negative result quoted
  here therefore covers atomic kernels only.

  A superseded form of the criterion should not be quoted: it was conjectured that
  non-identifiability additionally requires a relation whose weight product equals one.
  **That is refuted** — a counterexample has a kernel with weight product `98/27`.
  Relations alone suffice, with no condition on weights.
* **The tail regime.** The exponentially tilted versions of these statements are the ones
  that govern large deviations — polygenic score tails and quadratic-form statistics such
  as heritability estimators and GRM spectra, which is the regime clinical risk
  stratification actually runs in. Nothing here is proved in the tilted setting.
-/

end Calibrator
