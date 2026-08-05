/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Calibrator.ConditionalGain
import Calibrator.Permeability
import Calibrator.EffectSizeSurgery

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
only relative to a named functional. `Conventions.neiGst` computes Nei's `G_ST`;
nothing in this file depends on it.

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
the surrounding theory relies on fails, and none of the statements below are claimed.

    Empirical status: UNTESTED. -/
def InLinkageEquilibrium {k n : ℕ} (family : BundleFamily k) (panel : Panel n)
    (joint : (Fin n → Fin k) → ℝ) : Prop :=
  ∀ g : Fin n → Fin k, joint g = ∏ i : Fin n, family.atomMass (g i) (panel.support i)

/-! ## 1. The diploid bundle family -/

/-- The genotype standard deviation `√(2q(1-q))` at frequency `q`. -/
noncomputable def diploidStdev (q : ℝ) : ℝ := Real.sqrt (2 * q * (1 - q))

/-- **diploidStdev at its junk point, named.** Outside `[0, 1]` the variance `2 q (1 - q)` is
negative and `Real.sqrt` is junk-zero, so an inadmissible allele frequency reports a standard
deviation of zero -- the value for a monomorphic locus. A caller passing an out-of-range
frequency gets a plausible number instead of an error. Consumers must exclude the argument that
makes the guard vanish. -/
theorem diploidStdev_out_of_range_frequency_is_junk :
    diploidStdev 2 = 0 := by
  unfold diploidStdev
  rw [show (2 : ℝ) * 2 * (1 - 2) = -4 by norm_num]
  exact Real.sqrt_eq_zero_of_nonpos (by norm_num)

/-- The standardized dosage of genotype `j ∈ {0,1,2}` at frequency `q`:
`(j - 2q)/√(2q(1-q))`. -/
noncomputable def diploidAtomValue (j : Fin 3) (q : ℝ) : ℝ :=
  ((j : ℝ) - 2 * q) / diploidStdev q

/-- **diploidAtomValue at its junk point, named.** At a monomorphic locus the standardising
denominator is zero, so every genotype's standardised dosage is junk-zero -- all three genotypes
collapse to the same value, and the atom structure the quantity exists to expose disappears.
Consumers must exclude the argument that makes the guard vanish. -/
theorem diploidAtomValue_monomorphic_is_junk (j : Fin 3) :
    diploidAtomValue j 0 = 0 := by
  unfold diploidAtomValue diploidStdev
  simp

/-- The Hardy-Weinberg mass of genotype `j` at frequency `q`. The three masses are locked
to one parameter; this is what makes the family a bundle. -/
noncomputable def diploidAtomMass (j : Fin 3) (q : ℝ) : ℝ :=
  if j = 0 then (1 - q) ^ 2 else if j = 1 then 2 * q * (1 - q) else q ^ 2

/-- **The diploid bundle family**: standardized genotypes with Hardy-Weinberg masses. -/
noncomputable def diploidFamily : BundleFamily 3 :=
  { atomValue := diploidAtomValue, atomMass := diploidAtomMass }

/-- Relabelling which allele is called the alternate one: genotype `j ↦ 2 - j`.

    Empirical status: NOT AN EMPIRICAL CLAIM -- the permutation `![2, 1, 0]`
    on `Fin 3`. A relabelling of genotype indices. -/
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
  fin_cases j
  · simp [diploidAtomMass, genotypeFlip3]
  · simp [diploidAtomMass, genotypeFlip3]
    ring
  · simp [diploidAtomMass, genotypeFlip3]

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
  refine Fintype.sum_equiv genotypeFlip3_involutive.toPerm _ _ (fun j ↦ ?_)
  have hmod : diploidFamily.modulus j (1 - q) = diploidFamily.modulus (genotypeFlip3 j) q :=
    diploid_modulus_reflect j q
  have hmass : diploidFamily.atomMass j (1 - q) = diploidFamily.atomMass (genotypeFlip3 j) q :=
    diploidAtomMass_reflect j q
  simp only [Function.Involutive.coe_toPerm]
  rw [hmod, hmass]

/-- The panel with every frequency reflected: `q ↦ 1 - q` at every locus. -/
def Panel.reflect {n : ℕ} (panel : Panel n) : Panel n :=
  { support := fun i ↦ 1 - panel.support i, weight := panel.weight }

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
  refine Finset.sum_congr rfl (fun i _ ↦ ?_)
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
  { support := fun i ↦ min (panel.support i) (1 - panel.support i),
    weight := panel.weight }

/-- Folding chooses the same canonical representative from both allele-label orientations. -/
theorem Panel.reflect_fold {n : ℕ} (panel : Panel n) :
    panel.reflect.fold = panel.fold := by
  cases panel with
  | mk support weight =>
      simp only [Panel.reflect, Panel.fold]
      congr 1
      funext i
      simp [min_comm]

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
  refine Finset.sum_congr rfl (fun i _ ↦ ?_)
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

/-- **Folding is a projection on admissible allele-frequency panels.** Once every locus has been
moved to minor-allele frequency, folding again changes neither its support nor its weights. -/
theorem Panel.fold_idempotent {n : ℕ} (panel : Panel n)
    (h0 : ∀ i, 0 ≤ panel.support i) (h1 : ∀ i, panel.support i ≤ 1) :
    panel.fold.fold = panel.fold := by
  cases panel with
  | mk support weight =>
      simp only [Panel.fold] at h0 h1 ⊢
      congr 1
      funext i
      have hminor0 : 0 ≤ min (support i) (1 - support i) :=
        le_min (h0 i) (by linarith [h1 i])
      have hminorHalf : min (support i) (1 - support i) ≤ 1 / 2 := by
        rcases le_total (support i) (1 - support i) with h | h
        · rw [min_eq_left h]
          linarith
        · rw [min_eq_right h]
          linarith
      rw [min_eq_left]
      linarith

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
    (fun m _ hm ↦ by rw [hrest m hm.1 hm.2, zero_mul])]
  rw [hi, hl, htie]
  ring

/-- The same statement in its smallest concrete instance: two markers at frequency `q`,
weights `c` and `-c`, produce no modulus signal at any value. A fixed-MAF grid is this
configuration repeated. -/
theorem tied_pair_invisible (q c v : ℝ) :
    spectrumModulusLaw diploidFamily { support := ![q, q], weight := ![c, -c] } v = 0 := by
  unfold spectrumModulusLaw
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

/-! ## 5. The three-level hierarchy, each level with its escaping quantity -/

/-- **Mean inverse heterozygosity**, `1/(2q(1-q))` at a locus. Averaged over a panel this
is the fourth moment of the standardized dosage — the first thing any moment-based method
learns about a frequency spectrum. -/
noncomputable def invHeterozygosity (q : ℝ) : ℝ := 1 / (2 * q * (1 - q))

/-- **The inverse heterozygosity at a monomorphic locus, named.** A locus fixed for either allele
has zero heterozygosity, so its inverse diverges -- that is the whole point of the quantity as a
weight. Lean returns `0`, the SMALLEST possible weight, so a monomorphic locus enters a weighted
sum as negligible rather than as inadmissible. Consumers must require `q ≠ 0` and `q ≠ 1`. -/
theorem invHeterozygosity_monomorphic_is_junk :
    invHeterozygosity 0 = 0 := by
  unfold invHeterozygosity
  simp

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

/-- Every interior Hardy--Weinberg locus has inverse heterozygosity strictly greater than
one. Equivalently, the squared standardized dosage has positive sampling variance. -/
theorem invHeterozygosity_gt_one (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1) :
    1 < invHeterozygosity q := by
  have hden : 0 < 2 * q * (1 - q) := by nlinarith
  unfold invHeterozygosity
  apply (lt_div_iff₀ hden).2
  nlinarith [sq_nonneg (q - 1 / 2)]

/-- **Exact rare-variant sample-cost correction for a covariance channel.** The
standardized Hardy--Weinberg dosage at allele frequency `q` has variance one and fourth
moment `1/[2q(1-q)]`. Therefore a known-mean covariance-tangent estimator has variance

`(1/[2q(1-q)] - 1)/2`

times the Gaussian calculation with the same covariance response. The multiplier equals
one only at the Gaussian fourth-moment frequencies and diverges toward the rare-variant
boundary. This is a direct portability-design law: target-panel depth for LD or
haplotype-covariance completion must be budgeted using allele-frequency kurtosis, not a
Gaussian constant. -/
theorem diploid_covariance_estimator_variance_eq_gaussian_factor
    (q m covarianceDerivative : ℝ) (hq0 : 0 < q) (hq1 : q < 1) :
    covarianceTangentEstimatorVarianceFromMoments m covarianceDerivative 1
        (∑ j : Fin 3, diploidAtomMass j q * diploidAtomValue j q ^ 4) =
      ((invHeterozygosity q - 1) / 2) *
        gaussianCovarianceTangentEstimatorVariance m 1 covarianceDerivative := by
  rw [diploid_fourth_moment q hq0 hq1]
  simpa using covarianceTangentEstimatorVariance_kurtosis_eq_gaussian_factor
    m 1 covarianceDerivative (invHeterozygosity q)

/-- Inverse heterozygosity is bounded below by `1/(2q)`. Hence the covariance-estimation
penalty cannot remain bounded as the minor-allele frequency approaches zero. -/
theorem invHeterozygosity_ge_rare_boundary (q : ℝ)
    (hq0 : 0 < q) (hq1 : q < 1) :
    1 / (2 * q) ≤ invHeterozygosity q := by
  unfold invHeterozygosity
  have h1q : 0 < 1 - q := by linarith
  apply one_div_le_one_div_of_le
  · positivity
  · nlinarith [sq_nonneg q]

/-- The fourth-moment covariance-variance multiplier is at least
`(1/(2q)-1)/2`, an explicit divergent rare-variant lower envelope. -/
theorem diploid_covariance_variance_factor_rare_lower_bound (q : ℝ)
    (hq0 : 0 < q) (hq1 : q < 1) :
    (1 / (2 * q) - 1) / 2 ≤ (invHeterozygosity q - 1) / 2 := by
  linarith [invHeterozygosity_ge_rare_boundary q hq0 hq1]

/-- **One-percent MAF design constant.** At `q=0.01`, the exact covariance-estimation
variance multiplier relative to a Gaussian feature is `4901/198 ≈ 24.75`. Thus a
Gaussian study-design calculation can understate the independent target-panel budget by
nearly twenty-five-fold even before LD, imputation, or support attenuation is applied. -/
theorem onePercentMaf_covariance_estimator_variance
    (m covarianceDerivative : ℝ) :
    covarianceTangentEstimatorVarianceFromMoments m covarianceDerivative 1
        (∑ j : Fin 3,
          diploidAtomMass j (1 / 100) * diploidAtomValue j (1 / 100) ^ 4) =
      (4901 / 198 : ℝ) *
        gaussianCovarianceTangentEstimatorVariance m 1 covarianceDerivative := by
  rw [diploid_covariance_estimator_variance_eq_gaussian_factor
    (1 / 100) m covarianceDerivative (by norm_num) (by norm_num)]
  norm_num [invHeterozygosity]

/-- **Joint rare-variant and incomplete-tagging design constant.** At one-percent MAF,
if the observed marker or assay retains only half of the covariance response of the
deployment-relevant variant, the exact known-mean covariance-estimation variance is

`9802/99 ≈ 99.01`

times the Gaussian calculation for a perfectly tagged coordinate.  The approximately
`24.75×` Hardy--Weinberg fourth-moment cost and the `4×` inverse-square tagging cost
multiply.  Thus MAF and tagging quality cannot be entered as additive corrections in a
cross-population panel or polygenic-score portability budget. -/
theorem onePercentMaf_halfResponse_covariance_estimator_variance
    (m covarianceDerivative : ℝ) (hm : m ≠ 0)
    (hderivative : covarianceDerivative ≠ 0) :
    covarianceTangentEstimatorVarianceFromMoments m
        ((1 / 2) * covarianceDerivative) 1
        (∑ j : Fin 3,
          diploidAtomMass j (1 / 100) * diploidAtomValue j (1 / 100) ^ 4) =
      (9802 / 99 : ℝ) *
        gaussianCovarianceTangentEstimatorVariance m 1 covarianceDerivative := by
  rw [diploid_fourth_moment (1 / 100) (by norm_num) (by norm_num)]
  calc
    _ = ((invHeterozygosity (1 / 100) - 1) / (2 * (1 / 2) ^ 2)) *
        gaussianCovarianceTangentEstimatorVariance m 1 covarianceDerivative := by
      simpa using covarianceTangentEstimatorVariance_kurtosis_attenuation
        m 1 covarianceDerivative (invHeterozygosity (1 / 100)) (1 / 2)
        hm hderivative (by norm_num)
    _ = (9802 / 99 : ℝ) *
        gaussianCovarianceTangentEstimatorVariance m 1 covarianceDerivative := by
      norm_num [invHeterozygosity]

/-- **The same joint law on the information scale.**  A one-percent-MAF covariance
channel retaining half the deployment-relevant response has exactly `99/9802 ≈ 0.0101`
times the order-two information of a perfectly tagged Gaussian channel with the same
unattenuated response.  Thus the approximately `99×` sample-cost law above is not a
Gaussian-score heuristic: it is the reciprocal information of the named non-Gaussian
covariance-moment experiment. -/
theorem onePercentMaf_halfResponse_covariance_moment_permeability
    (covarianceDerivative : ℝ) :
    covarianceMomentPermeability ((1 / 2) * covarianceDerivative) 1
        (∑ j : Fin 3,
          diploidAtomMass j (1 / 100) * diploidAtomValue j (1 / 100) ^ 4) =
      (99 / 9802 : ℝ) * scalarPermeability 1 covarianceDerivative := by
  rw [diploid_fourth_moment (1 / 100) (by norm_num) (by norm_num)]
  calc
    _ = (1 / 2) ^ 2 * covarianceMomentPermeability covarianceDerivative 1
        (invHeterozygosity (1 / 100)) :=
      covarianceMomentPermeability_derivative_scale covarianceDerivative 1
        (invHeterozygosity (1 / 100)) (1 / 2)
    _ = (1 / 2) ^ 2 * (2 / (invHeterozygosity (1 / 100) - 1)) *
        scalarPermeability 1 covarianceDerivative := by
      have hkurtosis : covarianceMomentPermeability covarianceDerivative 1
          (invHeterozygosity (1 / 100)) =
          (2 / (invHeterozygosity (1 / 100) - 1)) *
            scalarPermeability 1 covarianceDerivative := by
        simpa using covarianceMomentPermeability_kurtosis_eq_gaussian_factor
          1 covarianceDerivative (invHeterozygosity (1 / 100))
          (by norm_num) (by norm_num [invHeterozygosity])
      rw [hkurtosis]
      ring
    _ = (99 / 9802 : ℝ) * scalarPermeability 1 covarianceDerivative := by
      norm_num [invHeterozygosity]

/-! ### Independent Hardy--Weinberg panel permeability -/

/-- Order-two covariance-moment information contributed by one standardized
Hardy--Weinberg locus.  This is a covariance-summary experiment, not the raw-dosage
linear-regression information of `AncestrySpecificPower`: standardization fixes the
second moment at one, while the MAF dependence enters through the fourth moment. -/
noncomputable def diploidCovarianceMomentPermeability
    (q covarianceDerivative : ℝ) : ℝ :=
  covarianceMomentPermeability covarianceDerivative 1
    (∑ j : Fin 3, diploidAtomMass j q * diploidAtomValue j q ^ 4)

/-- **Single-locus Hardy--Weinberg information law.**  At an interior MAF, a standardized
locus with covariance response `Γ` contributes

`Γ² / (1/[2q(1-q)] - 1)`.

The denominator is the variance of the squared standardized dosage.  It diverges at the
rare-variant boundary, so equal standardized covariance responses do not imply equal
information across the allele-frequency spectrum. -/
theorem diploidCovarianceMomentPermeability_eq
    (q covarianceDerivative : ℝ) (hq0 : 0 < q) (hq1 : q < 1) :
    diploidCovarianceMomentPermeability q covarianceDerivative =
      covarianceDerivative ^ 2 / (invHeterozygosity q - 1) := by
  unfold diploidCovarianceMomentPermeability covarianceMomentPermeability
    centeredSquareVarianceFromMoments
  rw [diploid_fourth_moment q hq0 hq1]
  ring

/-- Independent panel information with locus-specific MAF, covariance response, and
correlation-scale tagging response `η`.  The definition is deliberately diagonal:
genotype LD between loci invalidates the sum and requires the full covariance of the
quadratic summaries. -/
noncomputable def diploidPanelCovarianceMomentPermeability {n : ℕ}
    (q covarianceDerivative taggingResponse : Fin n → ℝ) : ℝ :=
  diagonalCovarianceMomentPermeability
    (fun i ↦ taggingResponse i * covarianceDerivative i)
    (fun _ ↦ 1)
    (fun i ↦ ∑ j : Fin 3,
      diploidAtomMass j (q i) * diploidAtomValue j (q i) ^ 4)

/-- The independent Hardy--Weinberg panel is exactly the diagonal-precision face of the
correlated covariance-moment theory.  Replacing this diagonal precision by an estimated
full inverse noise covariance is therefore a principled LD/haplotype completion, not a
different objective. -/
theorem diploidPanelCovarianceMomentPermeability_eq_diagonal_precision {n : ℕ}
    (q covarianceDerivative taggingResponse : Fin n → ℝ) :
    diploidPanelCovarianceMomentPermeability q covarianceDerivative taggingResponse =
      covarianceMomentPermeabilityWithPrecision
        (diagonalSquareNoisePrecision (fun _ ↦ 1)
          (fun i ↦ ∑ j : Fin 3,
            diploidAtomMass j (q i) * diploidAtomValue j (q i) ^ 4))
        (fun i ↦ taggingResponse i * covarianceDerivative i) := by
  unfold diploidPanelCovarianceMomentPermeability
  rw [covarianceMomentPermeabilityWithPrecision_diagonal]

/-- Interior Hardy--Weinberg MAFs give a positive-definite diagonal precision for the
independent squared-genotype summary experiment. -/
theorem diploidPanelDiagonalPrecision_posDef {n : ℕ}
    (q : Fin n → ℝ) (hq0 : ∀ i, 0 < q i) (hq1 : ∀ i, q i < 1) :
    (diagonalSquareNoisePrecision (fun _ ↦ 1)
      (fun i ↦ ∑ j : Fin 3,
        diploidAtomMass j (q i) * diploidAtomValue j (q i) ^ 4)).PosDef := by
  apply diagonalSquareNoisePrecision_posDef
  intro i
  rw [diploid_fourth_moment (q i) (hq0 i) (hq1 i)]
  unfold centeredSquareVarianceFromMoments
  have h := invHeterozygosity_gt_one (q i) (hq0 i) (hq1 i)
  norm_num at ⊢
  linarith

/-- **Panel identifiability at order two.** Under locus independence and interior MAFs,
the Hardy--Weinberg panel has zero covariance-moment information exactly when every
tagged covariance response `ηᵢΓᵢ` is zero. -/
theorem diploidPanelCovarianceMomentPermeability_eq_zero_iff {n : ℕ}
    (q covarianceDerivative taggingResponse : Fin n → ℝ)
    (hq0 : ∀ i, 0 < q i) (hq1 : ∀ i, q i < 1) :
    diploidPanelCovarianceMomentPermeability q covarianceDerivative taggingResponse = 0 ↔
      (fun i ↦ taggingResponse i * covarianceDerivative i) = 0 := by
  rw [diploidPanelCovarianceMomentPermeability_eq_diagonal_precision]
  apply covarianceMomentPermeabilityWithPrecision_eq_zero_iff
  exact diploidPanelDiagonalPrecision_posDef q hq0 hq1

/-- **Exact multi-locus design law.** Under independent loci, the panel information is
the sum of per-locus contributions

`ηᵢ² Γᵢ² / (1/[2qᵢ(1-qᵢ)] - 1)`.

Thus MAF, tagging, and biological covariance response interact multiplicatively at each
locus and add only after forming the correctly normalized information contributions. -/
theorem diploidPanelCovarianceMomentPermeability_eq {n : ℕ}
    (q covarianceDerivative taggingResponse : Fin n → ℝ)
    (hq0 : ∀ i, 0 < q i) (hq1 : ∀ i, q i < 1) :
    diploidPanelCovarianceMomentPermeability q covarianceDerivative taggingResponse =
      ∑ i, (taggingResponse i * covarianceDerivative i) ^ 2 /
        (invHeterozygosity (q i) - 1) := by
  unfold diploidPanelCovarianceMomentPermeability
    diagonalCovarianceMomentPermeability
  apply Finset.sum_congr rfl
  intro i _
  simpa [diploidCovarianceMomentPermeability] using
    diploidCovarianceMomentPermeability_eq
      (q i) (taggingResponse i * covarianceDerivative i) (hq0 i) (hq1 i)

/-- **Rare/tagged versus balanced information ratio.**  For the same unattenuated
standardized covariance response, a one-percent-MAF locus observed at half response has
exactly `99/19604 ≈ 0.00505` times the covariance-moment information of a balanced
`q=1/2` locus observed perfectly.  Equivalently, matching the balanced locus requires
`19604/99 ≈ 198.02` times as many independent observations in this named experiment. -/
theorem onePercentMaf_halfResponse_vs_balanced_permeability
    (covarianceDerivative : ℝ) :
    diploidCovarianceMomentPermeability
        (1 / 100) ((1 / 2) * covarianceDerivative) =
      (99 / 19604 : ℝ) *
        diploidCovarianceMomentPermeability (1 / 2) covarianceDerivative := by
  rw [diploidCovarianceMomentPermeability_eq
      (1 / 100) ((1 / 2) * covarianceDerivative) (by norm_num) (by norm_num),
    diploidCovarianceMomentPermeability_eq
      (1 / 2) covarianceDerivative (by norm_num) (by norm_num)]
  norm_num [invHeterozygosity]
  ring

/-- Total covariance-moment information from `m` independent observations of one
standardized Hardy--Weinberg locus. -/
noncomputable def totalDiploidCovarianceMomentInformation
    (m q covarianceDerivative : ℝ) : ℝ :=
  m * diploidCovarianceMomentPermeability q covarianceDerivative

/-- Reference evaluation: no samples, no information. -/
theorem totalDiploidCovarianceMomentInformation_at_reference_point
    (q covarianceDerivative : ℝ) :
    totalDiploidCovarianceMomentInformation 0 q covarianceDerivative = 0 := by
  unfold totalDiploidCovarianceMomentInformation
  ring


/-- **Exact rare/tagged cohort multiplier.** For a nonzero covariance response, matching
the information of `m` balanced, perfectly observed standardized genotypes with a
one-percent-MAF, half-response channel requires exactly `(19604/99)·m` observations. -/
theorem onePercentMaf_halfResponse_required_replicates
    (m covarianceDerivative : ℝ) (hderivative : covarianceDerivative ≠ 0) :
    replicatesForEqualPermeability m
        (diploidCovarianceMomentPermeability (1 / 2) covarianceDerivative)
        (diploidCovarianceMomentPermeability
          (1 / 100) ((1 / 2) * covarianceDerivative)) =
      (19604 / 99 : ℝ) * m := by
  unfold replicatesForEqualPermeability
  rw [diploidCovarianceMomentPermeability_eq
      (1 / 2) covarianceDerivative (by norm_num) (by norm_num),
    diploidCovarianceMomentPermeability_eq
      (1 / 100) ((1 / 2) * covarianceDerivative) (by norm_num) (by norm_num)]
  norm_num [invHeterozygosity]
  field_simp [hderivative]
  ring

/-- The cohort multiplier attains its design target exactly: the enlarged rare/tagged
experiment and the balanced source experiment have identical total moment information. -/
theorem onePercentMaf_halfResponse_equal_total_information
    (m covarianceDerivative : ℝ) :
    totalDiploidCovarianceMomentInformation
        ((19604 / 99 : ℝ) * m) (1 / 100) ((1 / 2) * covarianceDerivative) =
      totalDiploidCovarianceMomentInformation m (1 / 2) covarianceDerivative := by
  unfold totalDiploidCovarianceMomentInformation
  rw [onePercentMaf_halfResponse_vs_balanced_permeability]
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

/-! **Level two, and where it now lives.**

This section used to restate `spectrum_determined_of_separating` for the diploid family
as `folded_spectrum_identifiable_on_finite_panel`, under an
`InLinkageEquilibrium diploidFamily panel joint` premise and a `joint` parameter that
existed only to state it. A scan of the kernel-accepted proof terms found the premise
occurring nowhere in the proof, and it cannot: `spectrumModulusLaw` and `Separating` are
functions of the panel's frequencies and weights alone, so the statement never sees a
joint genotype distribution and holds whether or not the panel is in equilibrium.
Deleting the dead premise left the statement character-for-character identical to
`maf_spectrum_identifiable` in §7b, whose own linkage-equilibrium and minor-allele
premises were dead for the same reason, so the two have been merged there. -/

/-! ## 6. Matched low-order functionals, and what portability loss cannot be blamed on -/

/-- An estimator **reads through a finite list of spectrum functionals** when it is a
fixed linear combination of the panel averages of finitely many test functions. Most
summary-statistic methods are of this shape by construction. -/
def ReadsThroughFunctionals {n m : ℕ} (T : Panel n → ℝ) (φ : Fin m → ℝ → ℝ) : Prop :=
  ∃ c : Fin m → ℝ, ∀ panel : Panel n,
    T panel = ∑ a : Fin m, c a * ∑ i : Fin n, panel.weight i * φ a (panel.support i)

/-- Every fixed linear combination of panel averages reads through its functionals.

    The docstring above says most summary-statistic methods are of this shape by
    construction; this is that sentence as a theorem, and it is what puts the two
    "no leakage" results over a nonempty estimator family. -/
theorem readsThroughFunctionals_of_linearCombination {n m : ℕ} (c : Fin m → ℝ)
    (φ : Fin m → ℝ → ℝ) :
    ReadsThroughFunctionals
      (fun panel : Panel n ↦
        ∑ a : Fin m, c a * ∑ i : Fin n, panel.weight i * φ a (panel.support i)) φ :=
  ⟨c, fun _ ↦ rfl⟩

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
  exact Finset.sum_congr rfl (fun a _ ↦ by rw [hmatch a])

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
  refine matched_functionals_give_equal_estimates T _ hT _ _ (fun a ↦ ?_)
  fin_cases a
  simp only [Matrix.cons_val_fin_one, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  linarith

/-! ## 7. The pair theorem -/

/-- **THE PAIR THEOREM. The frequency spectrum is recoverable from summary statistics and
the effect-size architecture is not.**

Two verdicts from the same data, in one statement:

* *(left)* On a finite separating panel, modulus data determines the allele-frequency
  spectrum completely — no per-locus frequency information supplied, and no linkage
  equilibrium required (see `folded_spectrum_identifiable_on_finite_panel` for why the
  equilibrium premise this statement used to carry was doing nothing).
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
    (hsep : Separating diploidFamily panel)
    (hkernel : ∀ v : ℝ, spectrumModulusLaw diploidFamily panel v = 0)
    (F : Fiber) (shift : ℝ) {summary : ℝ → ℝ} (heven : IsEvenSummary summary) :
    (∀ i : Fin n, panel.weight i = 0) ∧
      (F.transfer shift).contribution summary = F.contribution summary :=
  ⟨fun i ↦ spectrum_determined_of_separating diploidFamily panel hsep hkernel i,
    F.even_summary_blind_to_transfer heven shift⟩

/-! ## 7b. CONJECTURE (NOT FORMALIZED): every finite MAF panel is identifiable

**This section proves nothing of the kind its title used to assert.** Read this paragraph
before anything below it.

The generic version of the statement puts identifiability off a measure-zero *cycle
variety*, cut out by closed cycles of signed weight product one. For **this** family the
variety itself is computed: **on `(0, 1/2]` it is empty** — so the genericity clause and
the cycle hypothesis are genuinely discharged, and that much is real.

> **The minor-allele-frequency spectrum of any finite marker panel is identifiable from
> modulus data.**

**That sentence is the section's thesis, and no theorem in this corpus establishes it.**
The only formal result here, `maf_spectrum_identifiable`, *assumes* `Separating`.
**No lemma anywhere in this corpus produces a `Separating` panel** — the predicate is only
ever hypothesised, never constructed — so nothing below concludes that any particular
panel, or any described class of panels, is identifiable. The missing step is peeling: from
"finite, minor-allele coded, pairwise distinct frequencies" to `Separating`. It is argued
in (ii) below in prose and it is not formalized. Until it is, the display above is a
conjecture this file supports and does not discharge, and quoting it as a result of this
development is a misreading.

**Why the usual checks do not catch this, which is the reason it is written out at
length.** There is no `sorry` here, no custom axiom, and every declaration below has a
clean `#print axioms`. The axiom scan in `proofs/validation/code/Check.lean` is therefore
silent, and correctly so: the gap is not an admitted debt inside a proof, it is a claim
made in prose that no proof was ever written for. A reader who verifies the kernel closure
of this file and concludes the headline is established has checked something real and
learned nothing about the headline. The two dead premises this section used to carry — an
`InLinkageEquilibrium` hypothesis and a minor-allele-coding hypothesis, neither of which
occurred in the proof term — are what led here: a statement decorated with the conditions
its title advertises, none of which the argument consults, is the visible symptom of a
title that outruns its theorem.

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

`spectrum_determined_of_separating` for the diploid family: on a finite separating panel,
modulus data determines every weight.

**One hypothesis carries this result, and it is `Separating`.** The statement used to
carry three more — a `joint` parameter, `InLinkageEquilibrium diploidFamily panel joint`,
and a minor-allele-coding premise `∀ i, 0 < support i ∧ support i ≤ 1/2` — and a scan of
the kernel-accepted proof terms found that none of the three occurs anywhere in the proof.
They cannot: `spectrumModulusLaw` and `Separating` are functions of the panel's
frequencies and weights alone, so the theorem never sees a joint genotype distribution,
and it never inspects where in `(0,1)` a frequency lies. The premises have been removed.

**What that costs the section heading above, and it is worth stating plainly.** The
minor-allele restriction is what empties the cycle variety, and that is why the §7b
narrative is not idle — but the emptiness is established by the `n = 2` enumeration in
prose, not consumed by this theorem, and **no lemma in this corpus produces a
`Separating` panel**. `Separating` is only ever assumed. So "every finite MAF panel is
identifiable, with no exceptional set" is not what is formalized here; what is formalized
is "every finite *separating* panel is identifiable", and the step from distinct
minor-allele-coded frequencies to `Separating` — the peeling argument — remains an
unformalized gap. Do not quote the headline as a theorem.

The separation hypothesis is not window dressing and is not vacuous: by
`not_separating_of_frequencyTie` it fails exactly when two markers share a frequency, which
is the ascertainment case of §4. -/
theorem maf_spectrum_identifiable {n : ℕ} (panel : Panel n)
    (hsep : Separating diploidFamily panel)
    (hkernel : ∀ v : ℝ, spectrumModulusLaw diploidFamily panel v = 0) (i : Fin n) :
    panel.weight i = 0 :=
  spectrum_determined_of_separating diploidFamily panel hsep hkernel i

/-! ## 8. Correlated frequencies along the genome: what regeneration buys

**The model, and its scope, first.** A *Markov-modulated bundle chain* lets the parameter
`t_i` — the allele frequency at site `i` — follow a Markov chain along the sequence, with
the genotype coordinates conditionally independent **given the parameters**. Read that
again before quoting anything below: this is dependence *in the frequency profile along
the genome*, not correlation between genotypes at fixed frequencies. Linkage
disequilibrium is the latter. Nothing in this section covers it.

The analytic content would require Doeblin minorization, Nummelin splitting, regeneration
decomposition, and Nagaev–Guivarc'h perturbation. It is not exported below without proofs.
-/

/-! **The removed Markov-modulated bundle-chain interface.**

The two modelling hypotheses are fields, not assumptions in prose:

* `conditionalIndependenceGivenParameters` — the model itself: genotypes are independent
  once the frequency profile is fixed. This is the scope limit; genotype-level dependence
  at fixed frequencies is outside it.
* `harrisMinorization` — Harris recurrence / a Doeblin minorization for the parameter
  chain, which is what produces regeneration times. Its failure boundary is not decorative:
  admixture, recent selective sweeps and unmodelled population structure give long-range
  parameter structure with **no** excursion decomposition, and the theory then declines to
  speak. That exception list is a scope statement, not advice.

The regeneration identity and the exact freezing coefficient were formerly exported by
placing those conclusions in structure fields.  They are not established in this corpus,
so the interfaces and their projection theorems have been removed.  A future restoration
must construct the split chain and prove the modulus-law identity from it. -/

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
    twoPointModulusLaw family site (fun i ↦ u i + u' i) v w =
      twoPointModulusLaw family site u v w + twoPointModulusLaw family site u' v w := by
  unfold twoPointModulusLaw
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun i _ ↦ by ring)

/-! ## 9. The coupled core: gain and support are different biological axes

No single scalar `D` controls decay, transfer and rigidity at once. That is too strong a
demand on one number. The core below is split in exactly the way the biology is split.

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

The separation is now a theorem rather than only an interpretation:
`FiniteCoupledPhaseLaw.same_full_support_coverage_different_gain` constructs balanced and
biased binary genotype laws with the same positive support and the same phase coding. They
have identical coverage for every bundle family, yet the balanced law has exact phase
cancellation while the biased law has finite gain. Thus even a perfect support audit does
not determine the anti-concentration input needed by a PGS calibration theorem.

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
      FiberCoupling.CoversTuple diploidFamily fiber J' value :=
  FiberCoupling.coverage_invariant diploidFamily fiber J J'
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

/-- **The family generated by one scalar**: every band reports the same number.

`DegradationFamily` had no exhibited inhabitant, which matters more here than it
usually does. The headline result below is a NO-GO -- no scalar summary can
reproduce a reversed pair of band rankings -- and a no-go is only informative
about a property that something satisfies. This is the family that does satisfy
it (`hasScalarSummary_ofScalar`), so the no-go rules out a real possibility
rather than an empty one.

    Empirical status: NOT AN EMPIRICAL CLAIM -- a scalar promoted to a
    band-indexed family by ignoring the band. The claim with content is that
    REAL portability degradation has this shape, which is what the reversal
    theorem denies. -/
def DegradationFamily.ofScalar {Pair : Type*} (D : Pair → ℝ) : DegradationFamily Pair where
  deg := fun _band pair ↦ D pair

instance DegradationFamily.instNonempty (Pair : Type*) :
    Nonempty (DegradationFamily Pair) :=
  ⟨DegradationFamily.ofScalar (fun _ ↦ 0)⟩

/-- **A scalar summary of degradation**: one number per population pair, which every band
reads through its own monotone rescaling. This is what "genetic distance predicts
portability loss" asserts. -/
def HasScalarSummary {Pair : Type*} (F : DegradationFamily Pair) : Prop :=
  ∃ D : Pair → ℝ, ∃ Φ : ℕ → ℝ → ℝ,
    (∀ k : ℕ, Monotone (Φ k)) ∧ ∀ (k : ℕ) (p : Pair), F.deg k p = Φ k (D p)

/-- **The scalar-summary property is satisfiable.** The family generated by one
scalar has that scalar as its summary, with the identity as every band's
rescaling.

This is what stops the reversal theorem below from being a no-go about nothing:
`HasScalarSummary` is a real constraint, met by real families and violated by
others, and the theorem separates the two. -/
theorem hasScalarSummary_ofScalar {Pair : Type*} (D : Pair → ℝ) :
    HasScalarSummary (DegradationFamily.ofScalar D) :=
  ⟨D, fun _band ↦ id, fun _band ↦ monotone_id, fun _band _pair ↦ rfl⟩

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
appears at leading order. That derivation is not present here.  The former
`ObservableDegradation` structure merely stored the desired relative-error theorem as a
field; it and its projection lemma have therefore been removed. -/

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

/-- **The undegraded readout**: no correlation drop and unit variance ratio, the
point every degradation statement is measured from.

`LevelSetCoordinates` had no exhibited inhabitant, so the collapse results --
which say every Gaussian level-set functional factors through these two numbers
-- were stated over a class with nothing in it. Naming the undegraded point in
particular fixes the orientation of both coordinates: a drop of zero and a ratio
of one is transfer with no loss, so a nonzero drop is loss rather than gain.

    Empirical status: NOT AN EMPIRICAL CLAIM -- the origin of a coordinate
    system. -/
def LevelSetCoordinates.undegraded : LevelSetCoordinates where
  correlationDrop := 0
  varianceRatio := 1

instance LevelSetCoordinates.instNonempty : Nonempty LevelSetCoordinates :=
  ⟨LevelSetCoordinates.undegraded⟩

/-- A one-dimensional threshold functional used to show why estimated-filter mixtures
need the **law** of their random coordinates, not merely coordinate means. -/
noncomputable def positiveThreshold (x : ℝ) : ℝ := if 0 < x then 1 else 0

/-- **The threshold reads only the sign, and reads it exactly.** Two values, taken at the two
sides and at the boundary: the indicator is `0` at zero, not `1`, so the convention is strict
positivity rather than nonnegativity, and that choice is visible here rather than left in the
`if`. -/
theorem positiveThreshold_values :
    positiveThreshold 1 = 1 ∧ positiveThreshold 0 = 0 ∧ positiveThreshold (-1) = 0 := by
  refine ⟨?_, ?_, ?_⟩ <;> unfold positiveThreshold <;> norm_num

/-- The indicator is scale invariant under positive rescaling: it is a property of the sign. -/
theorem positiveThreshold_pos_smul (x c : ℝ) (hc : 0 < c) :
    positiveThreshold (c * x) = positiveThreshold x := by
  unfold positiveThreshold
  have hiff : 0 < c * x ↔ 0 < x := by
    constructor
    · intro h; nlinarith
    · intro h; nlinarith
  by_cases hx : 0 < x <;> simp [hx, hiff]

/-- **The two sides of zero partition the indicator.** Sign invariance leaves the height free and
the tabulated values are a conjunction rather than one relation; this is a single equation that
holds only at height one, away from the boundary the convention excludes. -/
theorem positiveThreshold_add_neg (x : ℝ) (hx : x ≠ 0) :
    positiveThreshold x + positiveThreshold (-x) = 1 := by
  unfold positiveThreshold
  rcases lt_or_gt_of_ne hx with h | h
  · rw [if_neg (by linarith), if_pos (by linarith)]
    norm_num
  · rw [if_pos h, if_neg (by linarith)]
    norm_num

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

/-- Anything computed from the two coordinates is a level-set functional.

    This is the converse direction of the collapse, and it is what makes the
    three theorems below statements about a nonempty class. The witness is not
    degenerate: it says precisely which metrics qualify, namely every metric that
    factors through `coords`, which is what "threshold-based" means
    operationally. -/
theorem isLevelSetFunctional_comp {Pair : Type*} (coords : Pair → LevelSetCoordinates)
    (g : LevelSetCoordinates → ℝ) :
    IsLevelSetFunctional (fun p ↦ g (coords p)) coords :=
  ⟨g, fun _ ↦ rfl⟩

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
  fun hconv ↦ absurd (convex_le_max_endpoints hconv hx1 hx2) (not_le.mpr hpeak)

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

**THERE IS NOT "EXACTLY ONE spectral functional, unchanged at every symmetric order", AND
THAT CLAIM IS REFUTED NUMERICALLY.** The refutation is recorded here because the mechanism
it exposes is sharper than the claim it kills.

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

There is nevertheless one exact quotient that no nonlinear symmetric channel can remove.
`EnsembleChannel.orderFreeStatistic_reverse` proves that every statistic constant on panel
permutations is invariant under reversal.  `orderFreeStatistic_pair_swap` specializes the
wall to two units.  Conversely, `twoUnitArrow_swap`, `twoUnitArrow_diagonal`, and
`twoUnitArrow_distinguishes_orientation` prove that a single ordered adjacent pair carries
a reversal-odd transition determinant, while one repeated unit carries none.  In biological
terms, an unordered bag of genotypes can reveal symmetric LD fingerprints but cannot decide
the direction of a haplotype or ancestry-tract transition; retaining one ordered pair is the
minimal carrier for a one-dimensional arrow probe.  The stronger Gaussian finite-atom claim
that all remaining spectral information is visible modulo reversal still requires its
Mehler/diagram and phase-pinning proof and is not asserted by these finite theorems.

**A REGIME DECLARATION THE ORIGINAL STATEMENT LACKED.** `Var(sample mean) → L/n'` is
**asymptotic, not an equation at finite depth**, and the depth hypothesis is load-bearing
rather than decorative. Measured at `ρ = 0.99`, the deficit against `L` runs `−85%, −56%,
−20%, −3.0%` as `n'` goes `32 → 4096`, while the deficit against the exact finite-depth
Fejér reference never exceeds `1.7%`. So the finite-depth truth is the Fejér evaluation, and
`L/n'` is its limit; any use of the limit at small `n'` is wrong by the amounts tabulated.

### 14a′. The Gaussian Arrow reconstruction target

The terminal synthesis proposes the following stronger statement for finite-atom
Gaussian-latent families:

> **The order-free visible algebra is the symbol MODULO TIME REVERSAL, and the invisible
> tangent is EXACTLY the reversal-odd directions** — the sign of `Im λ`, the odd part of the
> spectral measure.
>
> *Destroying the order of a sample destroys the arrow of time and nothing else.*

The negative half is now a theorem: `EnsembleChannel.orderFreeStatistic_reverse` proves
that reversal is invisible to every order-free statistic.  The positive reconstruction
half is not yet proved.  It requires showing that the Hermite/Mehler cyclic diagrams recover
the joint spectral system and that their common rearrangement ambiguity is reduced to
`s ↦ -s` by phase pinning.  Until those two steps are formalized, the displayed statement
is the **Gaussian Arrow conjecture**, not an API guarantee.

**TWO INDEPENDENT DERIVATIONS REACHED THE SAME FOURTH-ORDER INVARIANT.** This corpus refuted
the one-number invisibility claim
*numerically* — two moving-average processes with `L` agreeing to `1e-16`, six of ten
order-free channels separating at up to `18.1σ`, predictions matching measurement to three
digits — and identified `Σγ(k)²` as the even-channel invariant. The analytical refutation
arrived afterwards and independently, by Hermite expansion:

`Σ_k Cov(f(F₀), f(F_k)) = Σ_r (c_r(f)²/r!) · π_r`,  with  `π_r := Σ_{k≥1} ρ(k)^r`,

and varying the test function `f` is expected to expose the power family `{π_r}` under the
required summability and identifiability hypotheses. **The measured `Σγ(k)²` is literally
their `π₂`.** This validates the failure of the Fejér-only model; it does not by itself prove
completeness of the entire order-free algebra.

**SCOPE, AND IT IS NOT DECORATIVE.** Even the positive Gaussian reconstruction is open in
this formal corpus. The non-Gaussian extension is a further conjecture via cumulant graphs.
The definitions below isolate only the proved algebra of an abstract involution. -/

/-- **Time reversal acting on spectral symbols.** The gauge of §15's symmetry class, here in
the form the Arrow Theorem needs. -/
structure TimeReversal (Symbol : Type*) where
  /-- The reversal map `s ↦ -s` on frequency, acting on symbols. -/
  rev : Symbol → Symbol
  /-- Reversal is an involution. -/
  rev_involutive : Function.Involutive rev

namespace TimeReversal

variable {Symbol : Type*} (T : TimeReversal Symbol)

/-- A statistic is **reversal-even** when it cannot tell a symbol from its time reverse. -/
def ReversalEven (φ : Symbol → ℝ) : Prop := ∀ s : Symbol, φ (T.rev s) = φ s

/-- A statistic is **reversal-odd** when reversal flips its sign. -/
def ReversalOdd (φ : Symbol → ℝ) : Prop := ∀ s : Symbol, φ (T.rev s) = -φ s

/-- A symbol is **reversible** when it is its own time reverse. -/
def Reversible (s : Symbol) : Prop := T.rev s = s

/-- Constant statistics are reversal-even, and the zero statistic is reversal-odd.

    Both witnesses are degenerate, and for an ABSTRACT involution `T` nothing
    richer is available: a reversal-odd statistic that is not identically zero
    exists only once `rev` is known to have a free orbit, which is a property of
    the particular `T` and belongs to the caller. The algebra below is real, and
    it is thin. -/
theorem reversalEven_const (c : ℝ) : T.ReversalEven (fun _ ↦ c) := fun _ ↦ rfl

theorem reversalOdd_zero : T.ReversalOdd (fun _ ↦ (0 : ℝ)) := fun _ ↦ (neg_zero).symm

/-- The trivial time reversal: the involution that reverses nothing. -/
def idReversal (Symbol : Type*) : TimeReversal Symbol where
  rev := id
  rev_involutive := fun _ ↦ rfl

/-- Under the trivial reversal every symbol is its own reverse, so `Reversible` is
    inhabited and `odd_vanishes_on_reversible` is not a theorem about nothing.

    This is also the sharpest reading of that theorem: when reversal is trivial,
    every reversal-odd statistic vanishes everywhere. The arrow of time is not
    detectable because there is no arrow, which is the degenerate end of the
    scale the Arrow Theorem measures. -/
theorem reversible_idReversal {Symbol : Type*} (s : Symbol) :
    (idReversal Symbol).Reversible s := rfl

/-- Every reversal-odd statistic vanishes on a reversible symbol.  This algebraic fact does
not assert that a selected order-free experiment identifies every other model coordinate. -/
theorem odd_vanishes_on_reversible {φ : Symbol → ℝ} (h : T.ReversalOdd φ)
    {s : Symbol} (hs : T.Reversible s) : φ s = 0 := by
  have hrev := h s
  rw [hs] at hrev
  linarith

/-- A reversal-odd statistic separates a symbol from its reverse wherever it is nonzero.
For a model known a priori to have exactly this two-element ambiguity, one ordered bit
completes that ambiguity.  Completeness for a larger spectral family requires a separate
identifiability theorem. -/
theorem odd_statistic_separates {φ : Symbol → ℝ} (h : T.ReversalOdd φ)
    {s : Symbol} (hs : φ s ≠ 0) : φ (T.rev s) ≠ φ s := by
  rw [h s]
  intro hcontra
  exact hs (by linarith)

/-- Reversal-even statistics are blind to reversal, which is the negative half of the
theorem and the reason Corollary 2 is needed at all. -/
theorem even_blind_to_reversal {φ : Symbol → ℝ} (h : T.ReversalEven φ) (s : Symbol) :
    φ (T.rev s) = φ s := h s

end TimeReversal

/-! ### 14a‴. COROLLARY 2 IS VACUOUS HERE, AND THAT IS THE RESULT

The two corollaries above are correct. In **this corpus's actual setting** the second one has
an **empty hypothesis**, and proving that is worth more than the corollary was.

For a real scalar stationary process, `γ(-k) = E[X₀X₋ₖ] = E[XₖX₀] = γ(k)` **by stationarity
alone** — no extra assumption, no Gaussianity, nothing about the model. So the spectral
measure is real and even, its odd part is identically zero, and in the Gaussian-latent layer
`Fᵢ = f(Zᵢ)` inherits reversibility pointwise from `Z`. **Every process in the Arrow
Theorem's stated setting is time-reversible.** `odd_vanishes_on_reversible` therefore does
not describe a special case; it describes everything here, and `odd_statistic_separates` has
nothing to separate.

**THE PHYSICAL REASON, which is what makes this robust rather than a technicality: genomic
position has no arrow.** Reading a chromosome 5'→3' versus 3'→5' is not a dynamical
asymmetry. The reversal-odd tangent is not merely unrealizable in the Gaussian scalar layer —
it is **absent from this application**.

**WHERE THE CONTENT RETURNS**, because the Arrow Theorem is empty *here*, not in general:

* **vector-valued observables**, where `Γ(-k) = Γ(k)ᵀ` rather than `Γ(k)`, so the quadrature
  cross-spectrum can be genuinely reversal-odd even in the Gaussian case.
  `EnsembleChannel.threeCycle_crossFeatureArrow_witness` supplies a stationary finite
  positive control with cross-feature arrow `1/3`;
* **real scalar non-Gaussian**, where asymmetry appears at third order as the imaginary part
  of the bispectrum — which is filed as *Conjecture A.1*, a "generalization", when for
  scalars it is precisely where the only content lives. -/

/-- Second moments of a real scalar process, indexed by position pairs along the genome. -/
structure ScalarSecondMoments where
  /-- `moment i j = E[Xᵢ Xⱼ]`. -/
  moment : ℤ → ℤ → ℝ
  /-- `E[XᵢXⱼ] = E[XⱼXᵢ]`. This is commutativity of multiplication, not a modelling
  assumption. -/
  moment_comm : ∀ i j : ℤ, moment i j = moment j i
  /-- Stationarity: second moments depend only on the lag. -/
  stationary : ∀ i j d : ℤ, moment (i + d) (j + d) = moment i j

/-- **The class is inhabited.**  A theorem quantified over an uninhabited structure is
true and empty: kernel-checked, clean axiom report, no content.  This is the witness that
makes the theorems below statements about something. -/
noncomputable def ScalarSecondMoments.witness : ScalarSecondMoments where
  moment := fun _ _ ↦ 0
  moment_comm := fun _ _ ↦ rfl
  stationary := fun _ _ _ ↦ rfl

namespace ScalarSecondMoments

variable (S : ScalarSecondMoments)

/-- The autocovariance at lag `k`. -/
def gamma (k : ℤ) : ℝ := S.moment 0 k

/-- **`γ(-k) = γ(k)`, FROM STATIONARITY ALONE.** Shift the pair `(0, -k)` by `k`, then
commute. No hypothesis beyond the definition of a stationary second moment is used. -/
theorem gamma_symmetric_of_stationary (k : ℤ) : S.gamma (-k) = S.gamma k := by
  unfold gamma
  calc S.moment 0 (-k)
      = S.moment (0 + k) (-k + k) := (S.stationary 0 (-k) k).symm
    _ = S.moment k 0 := by norm_num
    _ = S.moment 0 k := S.moment_comm k 0

/-- **Every real scalar stationary process is its own time reverse.** -/
theorem gamma_reversible : (fun k ↦ S.gamma (-k)) = S.gamma := by
  funext k
  exact S.gamma_symmetric_of_stationary k

/-- **The reversal-odd part of a real scalar stationary symbol is identically zero.**

This is the emptiness of Corollary 2's hypothesis, written as the vanishing of the odd part
itself. There is no arrow to carry, so there is no bit to spend on carrying it. -/
theorem reversalOdd_eq_zero_of_real_scalar (k : ℤ) :
    (S.gamma (-k) - S.gamma k) / 2 = 0 := by
  rw [S.gamma_symmetric_of_stationary k]
  ring

end ScalarSecondMoments

/-! ### 14a⁗. The conditional ceiling model and the support wall

The boxed characterization of the deployment ceiling is

`r⊥ = 0  ⟺  (η > 0) ∧ (reversible ∨ arrow bit)`.

If a named deployment experiment proves this characterization, then
`reversalOdd_eq_zero_of_real_scalar` makes the second conjunct a tautology in the scalar
stationary setting, and the characterization collapses to

> **`r⊥ = 0 ⟺ η > 0`**

The reduction is exact.  The boxed characterization itself is **not** proved by the
reversal calculation: it requires a separate identifiability theorem showing that positive
conditional support removes every remaining deployment-blind direction.

**THE CONDITIONAL BIOLOGICAL CONSEQUENCE.** In any experiment satisfying that missing
identifiability theorem, pruning perfect LD removes the information-theoretic floor and
leaves a sample-size problem.  This must not be quoted for arbitrary PGS deployment merely
from pairwise `r²`, a positive MAF floor, or the algebraic reversal result.

Within the same conditional model, the floor is replaced by a cost rather than nothing.
If the named experiment separately establishes permeability proportional to `η²`, its
sample term is proportional to `1/(mη²)`, and the trade-off is

`m ≥ d / (2·c₋·η²·R_target)`.

This makes LD-pruning threshold and cohort diversity conjugate **inside the verified support
model**.  The proportionality constant and the link between biological support and `η`
must be measured or proved for the assay being designed. -/

/-- Cohorts required for a target aggregate risk: `m ≥ d/(2 c₋ η² R)`. -/
noncomputable def requiredCohorts (d cMinus eta R : ℝ) : ℝ :=
  d / (2 * cMinus * eta ^ 2 * R)

/-- **requiredCohorts at zero cMinus, named.** A zero lower spectral constant means no number of
cohorts suffices to resolve the spectrum. Lean returns `0`: no cohorts required at all, the exact
inversion of an impossible design. Consumers must require `cMinus ≠ 0`. -/
theorem requiredCohorts_zero_cminus_is_junk (d : ℝ) (eta : ℝ) (R : ℝ) :
    requiredCohorts d 0 eta R = 0 := by
  unfold requiredCohorts
  simp

/-- **Strict inverse-square monotonicity.** In the conditional cost formula, smaller positive
`η` requires strictly more cohorts.  A separate limit theorem would be needed to formalize
divergence as `η → 0`; this result proves the exact finite comparison used by design. -/
theorem requiredCohorts_strictAnti_eta
    (d cMinus R e₁ e₂ : ℝ) (hd : 0 < d) (hc : 0 < cMinus) (hR : 0 < R)
    (he₁ : 0 < e₁) (hlt : e₁ < e₂) :
    requiredCohorts d cMinus e₂ R < requiredCohorts d cMinus e₁ R := by
  unfold requiredCohorts
  have h1 : 0 < 2 * cMinus * e₁ ^ 2 * R := by positivity
  have hsq : e₁ ^ 2 < e₂ ^ 2 := by nlinarith
  have h2 : 2 * cMinus * e₁ ^ 2 * R < 2 * cMinus * e₂ ^ 2 * R := by nlinarith
  exact div_lt_div_of_pos_left hd h1 h2

/-! ### 14a″. The two-unit arrow carrier and a conditional information model

`EnsembleChannel.twoUnitArrow_diagonal` proves that one repeated unit carries no value of the
named antisymmetric arrow, while `twoUnitArrow_distinguishes_orientation` proves that two
ordered units can carry it.  This is an algebraic observability threshold.  It does **not**
derive Fisher information or prove that every possible one-unit scheme is blind to every
dependence parameter.

**Two units are qualitatively different from one; the second unit is the arrow's minimal
carrier for this named probe.**

**A UNIT CORRECTION THAT CHANGES HOW THIS SHOULD BE READ: `n'` IS LOCI PER TARGET, NOT
INDIVIDUALS.** The index runs along the genome, so `n'` is in the millions and the mixing
time is the **LD decay length**. So `n' = 1` is a regime nobody occupies, and the `n' ≫
mixing` condition the budget decoupling requires is satisfied by about six orders of
magnitude rather than being a condition anyone needs to check.

`depth_one_cannot_be_bought` stays true and is worth keeping as the boundary case that shows
the axes are independent — but it must **not** be quoted as a live constraint on study
design. The breadth constraint of `RecoveryAttenuation` (`B ≈ 350`) is live; this one is not.

This sits directly beside `RecoveryAttenuation`, and the two constrain *different axes*:

* `panels_suffice_iff` says `B ≈ 350` panels per cohort are needed for reliability `0.8` —
  a statement about **breadth**;
* the arrow lemmas say depth `n' ≥ 2` is necessary for this ordered antisymmetric probe — a
  statement about **depth**, not yet a universal information bound.

No generic information-threshold model is exported from this discussion.  The concrete
binary-orientation experiment below supplies the proved positive control. -/

/-! The binary orientation experiment supplies one fully derived **directed-transition
positive control** for this design logic. `EnsembleChannel.binaryOrientation_orderFree_mean`
proves that **every** order-free
readout has mean independent of the forward/reverse imbalance `θ`, while
`binaryOrientation_arrow_mean` gives the ordered determinant mean `θ` and
`binaryOrientationArrowVariance_pos` gives variance `1 - θ² > 0` for `|θ| < 1`.
`Permeability.binaryOrientationArrowPermeability_eq` therefore yields the exact per-pair
law `p(θ) = 1/(1-θ²)`, with one information unit at the reversible center and `m`-pair
information `m/(1-θ²)`. `binaryOrientationArrowAssay_moreEfficient_iff` then gives the
fixed-budget assay rule: retain the ordered transition exactly when this arrow information
per added cost exceeds the baseline design's information per cost.
`threeCycle_crossFeatureArrow_witness` realizes a nonzero arrow in a stationary
two-annotation process, and `threeCycleOrientationArrowPermeability_eq_binary` proves that
its `1/3` coding scale leaves the information law unchanged.  These theorems apply when the
assay has a genuine directional label—multiple feature channels, parent-of-origin,
longitudinal state, or a non-Gaussian higher-order transition.  They do **not** assign an
arrow to ordinary real scalar LD merely because loci have a reference-coordinate order. -/

/-! ### 14b. Per-target invisibility and compound prediction

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

/-! **The estimation attenuation of curve-prior recovery.**

The earlier `RecoveryAttenuation` structure accepted the attenuation law itself as a field.
The recovered variance is instead defined by that algebraic model, so its bounds are actual
theorems about a term rather than projections from a caller-supplied equality. -/

namespace RecoveryAttenuation

noncomputable def recoveredVariance (predictableVariance estimationNoise : ℝ) : ℝ :=
  predictableVariance * (predictableVariance / (predictableVariance + estimationNoise))

/-- **recoveredVariance at no variance at all, named.** With neither predictable variance nor
estimation noise the shrinkage factor is undefined. Numerator and denominator vanish together,
the factor is junk-zero, and the recovered variance is `0` -- which is also the honest answer
when there is no signal, so the degenerate case hides inside the legitimate one. Consumers must
exclude it by hypothesis. -/
theorem recoveredVariance_no_variance_is_junk :
    recoveredVariance 0 0 = 0 := by
  unfold recoveredVariance
  simp

/-- **The population identity is an upper bound on what any deployment recovers.** -/
theorem recoveredVariance_le_predictable (predictableVariance estimationNoise : ℝ)
    (hp : 0 < predictableVariance) (hn : 0 ≤ estimationNoise) :
    recoveredVariance predictableVariance estimationNoise ≤ predictableVariance := by
  have hden : 0 < predictableVariance + estimationNoise := by
    linarith
  have hfrac : predictableVariance / (predictableVariance + estimationNoise) ≤ 1 := by
    rw [div_le_one hden]
    linarith
  unfold recoveredVariance
  calc predictableVariance * (predictableVariance / (predictableVariance + estimationNoise))
      ≤ predictableVariance * 1 := mul_le_mul_of_nonneg_left hfrac hp.le
    _ = predictableVariance := mul_one _

/-- **Noiseless estimation recovers the whole identity**, which is why the population
statement is not wrong — it is the zero-noise end of this law. -/
@[simp] theorem recoveredVariance_zero_noise (predictableVariance : ℝ)
    (hp : predictableVariance ≠ 0) :
    recoveredVariance predictableVariance 0 = predictableVariance := by
  simp [recoveredVariance, hp]

/-- **Any estimation noise at all strictly attenuates the recovery.** With one panel per
cohort the noise is a full `χ²₁` draw, which is how an exact identity becomes a measured
`15.3%`. -/
theorem recoveredVariance_lt_predictable (predictableVariance estimationNoise : ℝ)
    (hp : 0 < predictableVariance) (hn : 0 < estimationNoise) :
    recoveredVariance predictableVariance estimationNoise < predictableVariance := by
  have hden : 0 < predictableVariance + estimationNoise := by linarith
  have hfrac : predictableVariance / (predictableVariance + estimationNoise) < 1 := by
    rw [div_lt_one hden]
    linarith
  unfold recoveredVariance
  calc predictableVariance * (predictableVariance / (predictableVariance + estimationNoise))
      < predictableVariance * 1 := (mul_lt_mul_iff_right₀ hp).mpr hfrac
    _ = predictableVariance := mul_one _

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
    (hτ1 : τ < 1) (hB : 0 < B) :
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
`ObservationalCeiling.identical_observable_law_implies_identical_statistic_law` proves the
absolute side precisely: equality of the retained observable laws propagates through every
measurable downstream statistic, so an algorithm cannot complete a sigma-algebra that the
assay discarded.  `GenerativePortabilityLaw.no_marginal_only_history_degradation_criterion`
instantiates the deterministic probe form on a realizable independent/persistent Markov
pair: one-locus marginals cannot decide its nonzero history degradation.  But
`EnsembleChannel` also proves that estimator fluctuations expose some dependence and that
the sample-mean channel is incomplete. Characterizing exactly when estimator noise
separates quotient fibres remains the continuation. -/

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
  unequal symmetric fourth-order channel. It also proves the exact finite wall: every
  order-free statistic is reversal-invariant, and a two-unit antisymmetric transition probe
  changes sign under reversal. Compound deployment can exploit the richer symmetric
  observation, but the claimed full visible algebra modulo reversal, its Gaussian diagram
  reconstruction, and nonparametric empirical-Bayes regret remain open.

* **The arrow channel now has one exact experiment-specific information law.** In the
  two-orientation binary transition model, all order-free means are independent of `θ`, the
  ordered arrow has response one and variance `1-θ²`, and its permeability is exactly
  `1/(1-θ²)`. This validates the one-versus-two-unit design threshold for that named model.
  The stationary three-cycle witness proves that such an arrow can occur for multiple
  feature channels without contradicting scalar autocovariance symmetry. It does not prove
  a universal one-bit completion theorem or make ordinary scalar LD directional.

* **Permeability is experiment-specific, not a universal cumulant slogan.**
  `Permeability.covarianceScoreInformation_gaussian` now derives
  `p = (1/2)(Γ/Σ)²` from the centered Gaussian second and fourth moments rather than merely
  naming the formula. `totalGaussianInformation_mul_estimatorVariance` proves the exact
  known-mean covariance-estimator identity `m·p·Var = 1`. Consequently this experiment's
  variance is `1/(m p)`, not `1/(2m p)`; an additional half in an aggregate risk law would
  require an explicitly half-scaled loss.
  `gaussianCovarianceHalfSquaredRisk_eq` now proves that convention separately and yields
  exactly `1/(2mp)`, matching the permeability simulator's unit-Hessian loss
  `½‖error‖²`. Outside Gaussianity,
  `covarianceScoreInformation_kurtosis` gives the fourth-moment correction and labels it a
  quasi-score variance rather than silently calling it likelihood information.  The
  distribution-robust replacement is now explicit:
  `covarianceMomentPermeability = Γ²/Var(X²)`, and
  `totalCovarianceMomentInformation_mul_estimatorVariance` proves exact reciprocal
  variance for the named covariance-moment experiment without a Gaussian likelihood.
  `diploid_covariance_estimator_variance_eq_gaussian_factor` specializes the corresponding
  sampling law to standardized Hardy--Weinberg dosage: its covariance-estimation variance
  is inflated by exactly `(1/[2q(1-q)]-1)/2`, which diverges at the rare-variant boundary.
  `covarianceTangentEstimatorVariance_kurtosis_attenuation` proves that this tail cost and
  an attenuated covariance response multiply rather than add.  The concrete theorem
  `onePercentMaf_halfResponse_covariance_estimator_variance` gives the portability-design
  consequence: one-percent MAF with half-strength tagging costs exactly
  `9802/99 ≈ 99.01` times the Gaussian, perfectly tagged covariance experiment.  This is
  equivalently an information retention of exactly `99/9802`, proved by
  `onePercentMaf_halfResponse_covariance_moment_permeability`.  This is
  a conditional law for a named response attenuation, not a claim that MAF alone fixes
  tagging quality or that every LD proxy induces the same scalar attenuation.
  For an independent panel,
  `diploidPanelCovarianceMomentPermeability_eq` gives the complete locus-wise law
  `Σᵢ ηᵢ²Γᵢ²/(1/[2qᵢ(1-qᵢ)]-1)`.  Relative to a balanced, perfectly observed standardized
  genotype, a one-percent-MAF half-response channel retains exactly `99/19604` of the
  information, requiring `19604/99 ≈ 198.02` times the observations.  This stronger
  comparison is to a balanced **genotype moment experiment**, not to Gaussian data and
  not to raw-dosage regression.  `onePercentMaf_halfResponse_required_replicates` derives
  that cohort multiplier from the general `replicatesForEqualPermeability` design law,
  and `onePercentMaf_halfResponse_equal_total_information` proves that it exactly matches
  total information.  Genotype LD invalidates the diagonal sum and requires the
  covariance matrix of the quadratic summaries.  The unified replacement is
  `covarianceMomentPermeabilityWithPrecision = ΓᵀΩ⁻¹Γ`:
  `diploidPanelCovarianceMomentPermeability_eq_diagonal_precision` proves the independent
  formula is exactly its diagonal face, while
  `twoChannelMomentPermeabilityWithPrecision` exposes the cross term for two correlated
  summaries.  In a real LD block, `Ω` depends on joint genotype fourth moments; MAFs and
  pairwise `r²` alone do not generally determine it.  Under a positive-definite supplied
  precision, `covarianceMomentPermeabilityWithPrecision_eq_zero_iff` proves that zero
  information is equivalent to a zero retained response vector.  For independent
  interior-MAF genotypes, `diploidPanelDiagonalPrecision_posDef` discharges that premise
  and `diploidPanelCovarianceMomentPermeability_eq_zero_iff` gives the corresponding panel
  identifiability theorem.  The method-design consequence is the Schur-complement law
  `twoChannelMomentInformation_eq_base_add_innovation`: a new LD, haplotype,
  ancestry-tract, or longitudinal probe adds exactly its squared response innovation
  divided by its conditional noise.  It never reduces optimal information
  (`twoChannelMomentInformation_ge_first`), improves it strictly for a nonzero innovation,
  and is exactly redundant under `twoChannelMomentInformation_eq_first_iff`.  Thus probe
  selection should maximize **conditional response-to-noise**, not marginal association,
  locus count, or raw tagging alone.  With acquisition cost included,
  `twoChannelAugmentedAssay_moreEfficient_iff` gives the exact assay-versus-cohort rule:
  retain the richer probe iff its conditional information per added cost exceeds the
  baseline design's information per cost.  By
  `informationAtBudget_lt_iff_informationPerUnitCost_lt`, this is also exactly the rule
  maximizing information at every positive fixed budget.
  `AncestrySpecificPower.ld_r2_matches_covariance_response_retention` fixes the convention
  bridge: a tag retaining correlation-scale response `η` has conventional LD
  `r² = η²`, so regression information and covariance permeability retain the same
  fraction.  Treating a reported `r²` as `η` would incorrectly square the tagging loss
  twice.
  Correlated probes are now handled by
  `multivariateGaussianPermeability = (1/2)‖Σ⁻¹ᐟ²ΓΣ⁻¹ᐟ²‖²_F` once the named model supplies
  the whitening. `multivariateGaussianPermeability_diagonal` proves that the earlier
  independent-channel sum is exactly its diagonal face, while
  `twoChannelWhitenedDerivative_permeability` shows that a shared whitened response adds
  `shared²` information beyond the diagonal terms. Thus overlapping LD, haplotype, tract,
  or longitudinal probes are not silently counted as independent. The same module proves
  coding-scale invariance and supplies both the
  completion-count lower bound and a constructive finite-dimensional criterion:
  selected lag summaries complete a deployment family when their sensitivity matrix is
  nonsingular. `firstTwoLags_injective_of_amplitude_ne_zero` verifies the criterion for
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
* **The slice-map step** from the earlier two-point-identification sketch remains unproved;
  no theorem depending on it is exported.
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

  Do not quote a form of the criterion in which non-identifiability additionally requires
  a relation whose weight product equals one. **That is refuted** — a counterexample has a
  kernel with weight product `98/27`. Relations alone suffice, with no condition on
  weights.
* **The tail regime.** The exponentially tilted versions of these statements are the ones
  that govern large deviations — polygenic score tails and quadratic-form statistics such
  as heritability estimators and GRM spectra, which is the regime clinical risk
  stratification actually runs in. Nothing here is proved in the tilted setting.
-/

end Calibrator
