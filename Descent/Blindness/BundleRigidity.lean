/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Descent.Layer

assert_below Descent.Conditionals Descent.Portability Descent.Decision Descent.Program

namespace Descent.Blindness

open scoped BigOperators

/-!
# When summary statistics determine an allele-frequency spectrum

This file is self-contained: it imports only Mathlib and can be read without any other
part of this development.

## What the objects are

A **marker panel** is a finite list of loci. Locus `i` sits at a parameter value
`support i` — its minor allele frequency — and carries weight `weight i`. The list of
those frequencies, with their weights, is the panel's **allele-frequency spectrum**.

A **bundle family** says what one locus contributes. At parameter `t` it has finitely
many atoms; atom `j` takes value `atomValue j t` with mass `atomMass j t`. For diploid
genotypes there are three atoms and the masses are the Hardy-Weinberg proportions, which
is the sense in which a locus is an indivisible *bundle*: its atoms cannot be reweighted
independently, because one number `t` fixes all of them.

The **modulus curve** is `modulus j t = |atomValue j t ^ 2 - 1|`. Writing `U = X² - 1`
for the centered squared standardized dosage, these are the values `|U|` takes.

## What this map is, biologically

`spectrumModulusLaw` sends a panel's frequency spectrum to the distribution of `|U|`
across the panel. **That is what second-moment and heterozygosity-weighted statistics
read.** A regression of squared association statistics on a linkage-disequilibrium score
reads squared quantities; a variance-component heritability estimate is a second moment;
a within-population heterozygosity summary is a functional of `2q(1-q)`. All of them
factor through modulus data, so all of them see the panel only through this map.

The question this file is about is therefore an identifiability question with a concrete
reading: **can two panels with different allele-frequency spectra produce identical
modulus statistics?**

*A naming caution, because it has already caused one defect elsewhere in this corpus.*
Nothing here is stated for "F-statistics" unqualified. Different estimators of population
differentiation use different denominators and disagree by large factors off the
symmetric point, so an identifiability claim is meaningful only relative to a named
functional. What is named here is the law of `|U|` and nothing else.

## The result

The map is **linear** in the weights (`spectrumModulusLaw_add`,
`spectrumModulusLaw_smul`), so identifiability is the triviality of its kernel on
differences of spectra. That single observation converts the question from an argument
about atoms into a computation about one operator, and it is what makes everything below
short.

The mechanism is **coverage**. The coverers of a modulus value are the loci that produce
it. If a value is produced by exactly one locus, the balance at that value involves that
locus alone, so its weight difference is forced to zero (`kernel_vanishes_at_singly_covered`).
A panel every locus of which owns such a value is rigid: its spectrum is determined
(`spectrum_determined_of_separating`).

## The scope, which is the whole point and is in the hypotheses

**These are theorems about realized panels, not about mixing measures**, and the
distinction is not cosmetic. The argument needs a locus that owns a value, which needs a
finite list to pick it from. Over a continuous mixing measure the same modulus value is
generally produced at several distinct parameter points at once, single coverage never
occurs, and the argument does not start.

For the diploid family this is not hypothetical: over the continuum every modulus value
is covered at least twice, so the sufficient condition below fails there, while a finite
panel is rigid. A realized panel is finite — `n` loci, `n` frequencies — so the
biological claim lands on the object of interest and the idealization is the thing it
does not cover. Anyone quoting a rigidity statement about a continuous spectrum is
quoting something this file does not prove and which is currently open.
-/

/-- A **bundle family**: what one locus contributes, as a function of its parameter.

`atomValue j t` is the value of atom `j` at parameter `t` and `atomMass j t` its mass.
For diploid genotypes `atomCount = 3`, the parameter is the allele frequency, and the
masses are the Hardy-Weinberg proportions — so the atoms move together and cannot be
reweighted one at a time. -/
structure BundleFamily (atomCount : ℕ) where
  /-- The value of each atom at a given parameter. -/
  atomValue : Fin atomCount → ℝ → ℝ
  /-- The mass of each atom at a given parameter. -/
  atomMass : Fin atomCount → ℝ → ℝ

/-- The modulus curve of an atom: `|value² - 1|`, the value taken by `|U|`. -/
noncomputable def BundleFamily.modulus {k : ℕ} (family : BundleFamily k)
    (j : Fin k) (t : ℝ) : ℝ :=
  |family.atomValue j t ^ 2 - 1|

/-- The mass a single locus at parameter `t` places on the modulus value `v`. -/
noncomputable def BundleFamily.massAt {k : ℕ} (family : BundleFamily k)
    (t v : ℝ) : ℝ :=
  ∑ j : Fin k, if family.modulus j t = v then family.atomMass j t else 0

/-- A **locus spectrum**: finitely many loci, each at a parameter value, each with a weight.

NOT `Descent.Core.Panel`, which this was called until the two names met. That one is a
genotype matrix -- `nSamples` individuals each CALLED at `nLoci` sites -- and it is the
object the empirical claims are about. This one has no individuals in it at all: a locus
here is an allele frequency and a weight, which is what remains of a genotype matrix after
the samples have been summed away. The traffic runs one way, from that panel to this
spectrum, and never back, because the individuals are not recoverable from the summary.
Everything below is a statement about what survives that summing, so taking a genotype
matrix here would claim a resolution these theorems do not have.

The weights are unconstrained here — nothing below needs them non-negative or summing to
one, because the statements are about *differences* of spectra, where those constraints
do not survive anyway. -/
structure LocusSpectrum (locusCount : ℕ) where
  /-- The parameter — the allele frequency — of each locus. -/
  support : Fin locusCount → ℝ
  /-- The weight of each locus. -/
  weight : Fin locusCount → ℝ

/-- **The modulus law of a panel**, evaluated at one modulus value.

This is the map from a panel's allele-frequency spectrum to what second-moment and
heterozygosity-weighted statistics can read. -/
noncomputable def spectrumModulusLaw {k n : ℕ} (family : BundleFamily k)
    (panel : LocusSpectrum n) (v : ℝ) : ℝ :=
  ∑ i : Fin n, panel.weight i * family.massAt (panel.support i) v

/-- Two panels on the same loci, with weights added. -/
def LocusSpectrum.addWeights {n : ℕ} (panel other : LocusSpectrum n) : LocusSpectrum n :=
  { support := panel.support, weight := fun i ↦ panel.weight i + other.weight i }

/-- A panel with its weights rescaled. -/
def LocusSpectrum.smulWeights {n : ℕ} (c : ℝ) (panel : LocusSpectrum n) : LocusSpectrum n :=
  { support := panel.support, weight := fun i ↦ c * panel.weight i }

/-- **The modulus law is additive in the weights.** -/
theorem spectrumModulusLaw_add {k n : ℕ} (family : BundleFamily k)
    (panel other : LocusSpectrum n) (hsupport : panel.support = other.support) (v : ℝ) :
    spectrumModulusLaw family (panel.addWeights other) v =
      spectrumModulusLaw family panel v + spectrumModulusLaw family other v := by
  unfold spectrumModulusLaw LocusSpectrum.addWeights
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ ↦ ?_)
  rw [hsupport]
  ring

/-- **The modulus law is homogeneous in the weights.** -/
theorem spectrumModulusLaw_smul {k n : ℕ} (family : BundleFamily k)
    (c : ℝ) (panel : LocusSpectrum n) (v : ℝ) :
    spectrumModulusLaw family (LocusSpectrum.smulWeights c panel) v =
      c * spectrumModulusLaw family panel v := by
  unfold spectrumModulusLaw LocusSpectrum.smulWeights
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ ↦ ?_)
  ring

/-- **Locus `i` covers the modulus value `v`** when one of its atoms lands there with non-zero mass.
-/
def Covers {k n : ℕ} (family : BundleFamily k) (panel : LocusSpectrum n) (i : Fin n)
    (v : ℝ) : Prop :=
  family.massAt (panel.support i) v ≠ 0

/-- **The value `v` is singly covered by locus `i`**: `i` covers it and no other locus
contributes anything there.

This is the condition the peeling argument runs on, and for a diploid panel the largest
modulus value is singly covered by the rarest locus — the extreme atom has nobody to
trade with. -/
def SinglyCoveredBy {k n : ℕ} (family : BundleFamily k) (panel : LocusSpectrum n) (i : Fin n)
    (v : ℝ) : Prop :=
  Covers family panel i v ∧
    ∀ l : Fin n, l ≠ i → family.massAt (panel.support l) v = 0

/-- One atom of unit mass, whose value `0` puts its modulus at `|0² - 1| = 1`. -/
noncomputable def singleAtomFamily : BundleFamily 1 where
  atomValue := fun _ _ ↦ 0
  atomMass := fun _ _ ↦ 1

/-- One locus of unit weight. -/
noncomputable def singleLocusSpectrum : LocusSpectrum 1 where
  support := fun _ ↦ 0
  weight := fun _ ↦ 1

/-- **Single coverage is inhabited**, on the one-atom, one-locus panel at modulus `1`.

    The witness is minimal in a way that is worth being explicit about: with a
    single locus the second clause is vacuous, because there is no other locus
    to trade with. That is the degenerate end of exactly the phenomenon the
    docstring describes, where for a diploid panel the largest modulus value is
    singly covered by the rarest locus. It establishes non-vacuity; it does not
    establish that single coverage occurs on a panel with competitors, which is
    the case the peeling argument is actually for. -/
theorem singlyCoveredBy_singleAtom :
    SinglyCoveredBy singleAtomFamily singleLocusSpectrum 0 1 := by
  refine ⟨?_, fun l hl ↦ absurd (Subsingleton.elim l 0) hl⟩
  norm_num [Covers, BundleFamily.massAt, BundleFamily.modulus, singleAtomFamily,
    singleLocusSpectrum]

/-- **The forcing step, which is the whole mechanism.**

If a modulus value is produced by exactly one locus, then the modulus law at that value
is that locus's weight times its mass there. So a difference of spectra that produces no
modulus signal at all must give that locus weight zero: there is nobody to trade with.

This is the collapse of trades in its finite form. A cancellation would need a second
locus contributing at the same value, and single coverage says there is none — so the
question of whether some reparametrisation could move mass between two branches never
arises, because there is only one branch. -/
theorem kernel_vanishes_at_singly_covered {k n : ℕ} (family : BundleFamily k)
    (panel : LocusSpectrum n) (i : Fin n) (v : ℝ)
    (hsingle : SinglyCoveredBy family panel i v)
    (hkernel : spectrumModulusLaw family panel v = 0) :
    panel.weight i = 0 := by
  obtain ⟨hcover, hothers⟩ := hsingle
  have hsum : spectrumModulusLaw family panel v =
      panel.weight i * family.massAt (panel.support i) v := by
    unfold spectrumModulusLaw
    refine Finset.sum_eq_single i (fun l _ hl ↦ ?_) (fun hcontra ↦ ?_)
    · rw [hothers l hl, mul_zero]
    · exact absurd (Finset.mem_univ i) hcontra
  rw [hsum] at hkernel
  rcases mul_eq_zero.mp hkernel with hweight | hmass
  · exact hweight
  · exact absurd hmass hcover

/-- A panel is **separating** when every locus owns a modulus value that no other locus
reaches.

For diploid genotypes the rarest locus owns the largest modulus value outright, and
peeling it off leaves a smaller panel in which the next rarest does the same. This
condition is the simultaneous form of that, and it is what the theorem below consumes. -/
def Separating {k n : ℕ} (family : BundleFamily k) (panel : LocusSpectrum n) : Prop :=
  ∀ i : Fin n, ∃ v : ℝ, SinglyCoveredBy family panel i v

/-- **Rigidity: a separating panel's spectrum is determined by its modulus law.**

If a difference of spectra produces no modulus signal at any value, every weight in it is
zero — so two panels on the same loci with the same modulus law have the same weights.

**Biologically: the allele-frequency spectrum of a realized panel is identifiable from
modulus data alone.** Second-moment and heterozygosity-weighted summaries, which see the
panel only through this map, nevertheless determine the spectrum completely, with no
per-locus frequency information supplied.

The finiteness is in the hypothesis rather than in a remark, and it is doing real work:
`Separating` requires each locus to own a value, which is a statement about a finite list.
The continuum idealization of the same panel need not be separating — for the diploid
family it is not — and this theorem says nothing about it. -/
theorem spectrum_determined_of_separating {k n : ℕ} (family : BundleFamily k)
    (panel : LocusSpectrum n) (hsep : Separating family panel)
    (hkernel : ∀ v : ℝ, spectrumModulusLaw family panel v = 0) (i : Fin n) :
    panel.weight i = 0 := by
  obtain ⟨v, hv⟩ := hsep i
  exact kernel_vanishes_at_singly_covered family panel i v hv (hkernel v)

/-- The same statement as a comparison of two panels: same loci, same modulus law, hence
the same spectrum. -/
theorem panels_agree_of_modulus_law_agree {k n : ℕ} (family : BundleFamily k)
    (panel other : LocusSpectrum n) (hsupport : panel.support = other.support)
    (hdiff : Separating family
      { support := panel.support, weight := fun i ↦ panel.weight i - other.weight i })
    (hlaw : ∀ v : ℝ, spectrumModulusLaw family panel v =
      spectrumModulusLaw family other v) (i : Fin n) :
    panel.weight i = other.weight i := by
  have hzero : ∀ v : ℝ, spectrumModulusLaw family
      { support := panel.support, weight := fun i ↦ panel.weight i - other.weight i } v
        = 0 := by
    intro v
    have hexpand : spectrumModulusLaw family
        { support := panel.support,
          weight := fun i ↦ panel.weight i - other.weight i } v =
        spectrumModulusLaw family panel v - spectrumModulusLaw family other v := by
      unfold spectrumModulusLaw
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun l _ ↦ ?_)
      rw [hsupport]
      ring
    rw [hexpand, hlaw v, sub_self]
  have := spectrum_determined_of_separating family _ hdiff hzero i
  simp only at this
  linarith [this]

/-!
## The dichotomy, and what is not proved here

Peeling is a *sufficient* condition. The general criterion is a dichotomy: the kernel is
trivial exactly when the **core** — the maximal set of parameters from which every
covered value interval is covered at least twice from within — supports no
holonomy-consistent non-zero section. An empty core is the checkable sufficient condition
and is what `Separating` captures in the finite case.

Two analytic inputs are needed for the general statement and neither is proved here. No
general dichotomy theorem is exported until those inputs are formalized.
-/

/-!
## Where this sits, in one paragraph

Three regimes on one axis, each with a named quantity that escapes.

*Few moments.* Floor-one data determines only the mean of `1/(2q(1-q))` across the panel.
What escapes is its **dispersion** — a between-locus quantity, already integrated away.

*Full modulus data, separating panel.* The spectrum is pinned; nothing escapes. That is
`spectrum_determined_of_separating`.

*Full modulus data, non-separating family.* Everything is pinned except freedom confined
to a band of parameter values, and in the folded case that freedom is exactly the odd part
in the fold coordinate — a local, explicitly parameterized non-identifiability rather than
a global one.

Read against the companion result on effect-size distributions, where every even summary
is constant on the fibers of the magnitude map: **modulus data determines the frequency
spectrum and is blind to effect-size asymmetry.** Same summaries, opposite verdicts, and
the reason is structural — genotype atoms come in bundles with masses locked by
Hardy-Weinberg, and effect sizes do not. The practical reading is that frequency-spectrum
inference from summary statistics is on firmer ground than usually assumed, and that
effect-size asymmetry should not be inferred from moment-based summaries at all.
-/

end Descent.Blindness
