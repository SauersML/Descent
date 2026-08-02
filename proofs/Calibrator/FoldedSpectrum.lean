import Calibrator.BundleRigidity
import Calibrator.EffectSizeSurgery
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Fin

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
    have hexp : ∀ x : ℝ, x / (2 * q * (1 - q)) - 1
        = (x - 2 * q * (1 - q)) / (2 * q * (1 - q)) := by
      intro x
      field_simp
    rw [hexp, hexp, div_pow, div_pow, div_eq_div_iff (by positivity) (by positivity)] at hsq
    have hD2 : ((2 * q * (1 - q)) ^ 2) ≠ 0 := pow_ne_zero 2 hne
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
  exact hcover (by rw [htie]; exact hothers l hne)

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
theorem diploid_modulus_alt_eq (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1) :
    diploidFamily.modulus 2 q = 2 / q - 3 := by
  have hden : (0 : ℝ) < 2 * q * (1 - q) := by nlinarith
  rw [diploid_modulus_eq 2 q hq0 hq1]
  have hcast : ((2 : Fin 3) : ℝ) = 2 := by norm_num
  rw [hcast]
  have hval : (2 - 2 * q) ^ 2 / (2 * q * (1 - q)) - 1 = 2 / q - 3 := by
    field_simp
    ring
  rw [hval, abs_of_nonneg]
  nlinarith

/-- **The dominating atom is strictly decreasing in the frequency**: the rarer the locus,
the larger its extreme modulus value. This is what gives peeling a starting point, and it
is why the argument needs a *minimum* — hence a finite panel. -/
theorem diploid_modulus_alt_strictAnti (q r : ℝ) (hq0 : 0 < q) (hq1 : q < 1)
    (hr1 : r < 1) (hlt : q < r) :
    diploidFamily.modulus 2 r < diploidFamily.modulus 2 q := by
  have hr0 : 0 < r := lt_trans hq0 hlt
  rw [diploid_modulus_alt_eq q hq0 hq1, diploid_modulus_alt_eq r hr0 hr1]
  have : 2 / r < 2 / q := by
    apply div_lt_div_of_pos_left (by norm_num) hq0 hlt
  linarith

/-- **The reference-homozygote modulus never exceeds one** on `(0, 1/2]`, while the
alternate one never falls below it. The dominance is not an asymptotic statement. -/
theorem diploid_modulus_ref_le_one (q : ℝ) (hq0 : 0 < q) (hhalf : q ≤ 1 / 2) :
    diploidFamily.modulus 0 q ≤ 1 := by
  have hq1 : q < 1 := by linarith
  have hden : (0 : ℝ) < 2 * q * (1 - q) := by nlinarith
  rw [diploid_modulus_eq 0 q hq0 hq1]
  have hcast : ((0 : Fin 3) : ℝ) = 0 := by norm_num
  rw [hcast]
  have hval : (0 - 2 * q) ^ 2 / (2 * q * (1 - q)) - 1 = (3 * q - 1) / (1 - q) := by
    field_simp
    ring
  rw [hval, abs_le]
  constructor
  · rw [le_div_iff (by linarith)]
    linarith
  · rw [div_le_one (by linarith)]
    linarith

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
  apply Real.exp_lt_exp.mpr
  have h : 1 / T'.kappa < 1 / T.kappa :=
    one_div_lt_one_div_of_lt T.kappa_pos hlt
  linarith

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

/-! ## 9. The effective-independence dimension `D`, and why it is the effective marker count

Everything above threshold-like is controlled by the same scalar, and it is defined for an
**arbitrary** coupling — no conditional independence, no regeneration.

*Sequential freshness.* Order the coordinates. The freshness `εᵢ` of coordinate `i` is the
largest `ε` with `Law(Xᵢ | earlier coordinates) ≥ ε ·` (fiber reference), almost surely.
Then `D = max over orderings of Σᵢ εᵢ`.

Evaluations, all computable from the coupling data:

| coupling | `D` |
|---|---|
| independent | `n` |
| Harris chain, correlation length `ℓ` | `≈ n/ℓ`, the regeneration count |
| block-copy, blocks of size `ℓ` | `n/ℓ` **exactly** — one fresh unit per block |
| Gaussian copula, precision `J` | `≥ c Σᵢ 1/(Jᵢᵢ σᵢ²)` |
| Gibbs density `e^{-H}` | `≥ Σᵢ e^{-2 osc_i(H)}` |

**The Gaussian-copula line is the one that matters here**: `D` is a spectral functional of
the *precision matrix*, so it is computable directly from a marker correlation matrix. It
is a defined invariant with a formula, not a rule of thumb.

**The claim of this section.** The effective number of independent markers is `D`; it is
computable from the correlation structure; and the effective-test-count estimators
currently in use do not compute it. The second half is measured, not asserted: two marker
panels that the standard estimators rated at ratio `0.995`–`1.000` had true separation
`1.84`, `1.97` and `1.99`, against a certificate demanding a factor of two. The estimators
were tracking something other than the quantity the theory needs.

What `D` has that those estimators do not is three theorems attached to it: the decay
exponent is `γ(s)·D` with a matched lower bound; the transfer threshold is `D` against
`log N`; and the usable slot count in `k`-point data is `min(k, D)`.
-/

/-- **The effective-independence dimension**, with its consequences as named fields.

`D` is defined for an arbitrary coupling via sequential freshness, so this structure
carries no independence or regeneration hypothesis at all — which is the point of it. The
three consequences are fields rather than theorems because their proofs are the upstream
analytic work, not reproduced here. -/
structure EffectiveIndependence (n : ℕ) where
  /-- The dimension `D = max over orderings of Σ εᵢ`. -/
  D : ℝ
  D_nonneg : 0 ≤ D
  /-- `D` never exceeds the coordinate count, with equality exactly for independence. -/
  D_le_count : D ≤ (n : ℝ)
  /-- Whether the coordinates are independent. -/
  independent : Prop
  independent_iff : independent ↔ D = (n : ℝ)
  /-- The number of usable slots in `k`-point data. -/
  usableSlots : ℕ → ℝ
  /-- **Slot count.** Coupled `k`-point data carries `min(k, D)` usable slots, not `k`. -/
  usableSlots_eq : ∀ k : ℕ, usableSlots k = min (k : ℝ) D

namespace EffectiveIndependence

variable {n : ℕ} (E : EffectiveIndependence n)

/-- **Adding perfectly correlated markers adds no usable slots.** Once `k` exceeds `D`, the
slot count stops growing: it is pinned at `D` however many more coordinates are added. -/
theorem usableSlots_saturates (k : ℕ) (hk : E.D ≤ (k : ℝ)) : E.usableSlots k = E.D := by
  rw [E.usableSlots_eq k]
  exact min_eq_right hk

end EffectiveIndependence

/-- **THE MERGED THRESHOLD.** The panel-design condition of §7b and the dependence
condition of §8 are one condition:

> local theory applies `↔ min(panel dimension, D) ≳ log N`.

The panel needs enough distinct frequencies **and** enough effective independence, and it
is the *minimum* that binds. Both faces are attained by explicit constructions, so neither
half is slack: a panel can fail by having too few distinct frequencies at full independence,
or by having ample frequency diversity in one correlated block. -/
structure MergedThreshold (n : ℕ) where
  /-- The panel's dimension — its count of distinct marker frequencies. -/
  panelDimension : ℝ
  /-- The effective-independence dimension of the coupling. -/
  effective : EffectiveIndependence n
  /-- Score length. -/
  scoreLength : ℝ
  scoreLength_pos : 1 < scoreLength
  constant : ℝ
  constant_pos : 0 < constant
  /-- Whether local-limit and expansion theory transfers. -/
  transfers : Prop
  /-- **The merged criterion.** -/
  criterion : transfers ↔
    constant * Real.log scoreLength < min panelDimension effective.D

namespace MergedThreshold

variable {n : ℕ} (M : MergedThreshold n)

/-- **Either face alone can fail the criterion.** Frequency diversity does not rescue a
correlated panel, and independence does not rescue a monotonous one. -/
theorem transfers_needs_both (h : M.transfers) :
    M.constant * Real.log M.scoreLength < M.panelDimension ∧
      M.constant * Real.log M.scoreLength < M.effective.D := by
  have hmin := (M.criterion).mp h
  exact ⟨lt_of_lt_of_le hmin (min_le_left _ _), lt_of_lt_of_le hmin (min_le_right _ _)⟩

end MergedThreshold

/-- **THE FALSIFIER, AND THE DESIGN CONSEQUENCE: modulus-copy coupling.**

Take two slots at equal fibers with the second an **exact modulus copy** of the first. The
two-point modulus law collapses onto a diagonal, and its kernel then contains *every*
perturbation that fixes the first marginal — an infinite-dimensional kernel, present even
when the one-point map is injective.

So **coupled `k`-point data can be strictly blinder than `k` independent one-point
observations**, and the deficit is exactly the freshness deficit `k - D`.

In panel terms, and this is the useful sentence: **perfectly correlated markers contribute
nothing, and adding them does not merely fail to help — it can destroy identifiability that
the same markers would have had independently.** That is why adding correlated markers adds
no information, stated with a mechanism rather than as folklore, and it is what makes `D` a
design criterion rather than a diagnostic. -/
structure ModulusCopyCoupling (K : ℕ) where
  /-- The bundle family the two slots draw from. -/
  family : BundleFamily K
  /-- The shared fiber parameter of the two slots. -/
  fiber : ℝ
  /-- The one-point modulus map is injective — the copy blindness is not inherited from a
  defect at one point. -/
  oneSiteInjective : Prop
  /-- The two-point kernel contains every perturbation fixing the first marginal. -/
  kernelContainsMarginalFixing : Prop
  /-- **The collapse.** -/
  collapse : oneSiteInjective → kernelContainsMarginalFixing

/-!
## What is left open, plainly

* **Linkage disequilibrium proper.** §8 buys dependence *in the allele frequencies along
  the genome*, via regeneration. It does **not** buy correlation between genotypes at
  fixed frequencies, which is what LD is. That remains outside the theory, and it is the
  named limitation, not a to-do. Sections 1–7 assume outright independence.
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
  general claim that `M5` is unrealizable in any analytic family is **withdrawn**: an
  explicit eight-atom recipe realizes it. The reason the earlier obstruction looked general
  is worth keeping, because the principle is: *continuation kills identities, not
  inequalities.* It forbids exact operator identities across sheets of one analytic curve,
  while `M5` needs only open conditions — strict containment, a fixed point in an open gap,
  a strict inequality — and open conditions survive continuation.

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
