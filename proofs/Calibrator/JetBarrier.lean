/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Calibrator.CumulantBlindness

namespace Calibrator

/-!
# Lattice arithmetic from the withdrawn Jet Barrier program

This file proves the lattice-inflation arithmetic used by the Jet Barrier program. The
nonlattice completeness theorem is not formalized here, and no `ChaosSpectroscopy` record
accepts Stone/local-limit conclusions from the caller.

## Why the trichotomy, and not a 2-jet

The observable algebra of independent low-influence chaos over a symmetric product law is
**not** the Mellin 2-jet `(c, v) = (E[x² log x²], Var_tilde(log x²))` and nothing else: that
is **false as stated**, because lattice laws are a live counterexample class. Working the
lattice case out shows it is not an exception to be excluded but a *third observable*.
The historical conjecture was:

> Independent low-influence chaos over a symmetric product law observes exactly the
> triple `(c, v, lattice datum of log x²)` — and nothing else.

* `(c, v)` via the location of the condensation threshold and the window profile
  (`Calibrator.Condensation`);
* the **lattice datum** via the Poisson-intensity oscillation of Theorem 1b below;
* nothing else, by the nonlattice barrier, Theorem 1a.

This corpus does not prove the “nothing else” clause, so it does not export the claimed
classification or a chameleon-completeness theorem.  It retains only directly proved
arithmetic and explicitly conditional finite implications.

Two distinct research questions remain: what a disjoint design can observe and whether a
candidate observable tuple determines the coordinate law.  Neither completeness direction
is exported from this file.  The proved lattice formulas below are positive separation
tools, not a classification of all observations.

## Status labels

* Theorem 1a (nonlattice barrier) is absent pending a repository proof of the required
  uniform local limit theorem.
* Theorem 1b (lattice detection) is likewise absent. What is proved below is the
  arithmetic inequality `h / (1 - exp (-h)) > 1` and its bracket. Identifying that
  ratio with a ratio of exceedance intensities needs two local limit theorems, and
  converting an intensity gap into a limit-law gap needs Gnedenko-Kolmogorov; all three
  are hypotheses of `inflated_intensity_ne_of_injective`, never conclusions.
* To our knowledge the *completeness* formulation — quantifying over designs rather
  than fixing a test law — is not stated in the Ben Arous-Bogachev-Molchanov /
  Bovier-Kurkova-Loewe / Huang-Austern-Orbanz literature, whose theorems fix the test
  law. That is a checked statement about those sources, not a claim of priority over
  the mechanism, which is theirs (see `Calibrator.Condensation` for the ledger).

## Why a polygenic-score development needs this

The lattice factor is a *calibration instrument*: a proposed Gaussian approximation for a
hard-called epistatic score must account for threshold alignment.  This is a necessary
diagnostic, not a complete criterion for Gaussianity.

And the lattice observable is not a technicality in genetics — it is the whole
difference between two data types. **Hard-called genotypes are lattice**: the
standardized dosage takes three values, so `log x²` has finite support. **Imputed
dosages are nonlattice**: they have a density. Neither of those two sentences is proved
here either — they are read off the support of the respective coordinate laws. The
*conjecture* they feed is that hard calls and imputed dosages stay distinguishable by
high-degree epistatic aggregates even after matching every moment; what this file
contributes to it is the inflation factor's arithmetic and nothing else. See
`Calibrator.PolygenicSpectroscopy`.

## Which half of this file applies to genotypes, and where

The file splits cleanly along the symmetry hypothesis, and the split is worth
stating once because it decides what may be quoted about real data.

* **Symmetry-gated.** Any completeness claim requires symmetric coordinate laws. A
  standardized Hardy-Weinberg genotype is symmetric only at `q = 1/2`; no completeness
  claim is exported even there.
* **Symmetry-free.** The lattice arithmetic (`one_lt_latticeInflation`,
  `latticeBracket_antitone`, `latticeInflation_normalization`) never mentions
  symmetry, and neither does the drift theory
  of `Calibrator.Condensation`. These are the parts that apply to genotypes at
  every allele frequency — and they are the parts
  `Calibrator.PolygenicSpectroscopy` actually instantiates.

`Calibrator.PolygenicSpectroscopy` instantiates the symmetry-free side only. The split is
stated so that the symmetry-gated statements are not quoted about genotypes at frequencies
where their hypothesis is false.

## A second gate: disjointness of the tested locus-sets

The title of this file says "independent chaos designs", and independence there
means *disjoint variable supports*. That condition would have to be an explicit hypothesis
of any future barrier theorem, because it is not a technical convenience:

* on disjoint designs the achievable limits are the Gaussian segment
  `{N(0, s²) : 0 ≤ s² ≤ 1}`, so the trichotomy has something to be complete
  *about*;
* on designs whose tested locus-sets share variants the achievable limits are
  weakly dense in the entire moment body — every centered law with second moment
  at most one — uniformly over the coordinate law. See
  the corresponding maximal-spectrum conjecture (also not exported as a theorem here).

Genetically this is the difference between burden or kernel statistics over
non-overlapping genes and partitioned windows (gated in), and sliding windows,
overlapping gene-set panels, and any recurrently tested pleiotropic variant
(gated out). Nothing in this file may be quoted about the second class.
-/

open scoped BigOperators

/-!
## 1. The lattice datum
-/

/-- The lattice structure of the increment `l = log x²`. `nonlattice` when `l` has no
arithmetic-progression support; `lattice h α` when `l` is supported on `α + h * ℤ`
with maximal span `h > 0`.

Note that the size-biased tilt has the same support as the original law, so the
lattice datum is tilt-invariant — which is why it survives to the limit. -/
inductive LatticeDatum where
  | nonlattice : LatticeDatum
  | lattice (span offset : ℝ) : LatticeDatum

/-- **What a lattice datum claims about an actual law.**

    `IsLatticeLaw μ span offset` says `μ` puts no mass outside the arithmetic progression
    `offset + span * ℤ`, with `span > 0`. This is the content a `LatticeDatum` asserts; the
    datum by itself is a constructor and asserts nothing.

    A record carrying a lattice datum has to agree with an actual law, which is what
    `LatticeDatum.Describes` below demands of it. -/
def IsLatticeLaw (μ : MeasureTheory.Measure ℝ) (span offset : ℝ) : Prop :=
  0 < span ∧ μ {x : ℝ | ∀ k : ℤ, x ≠ offset + span * k} = 0

/-- **`IsLatticeLaw` is satisfied by an actual measure**, namely a point mass.

    All the mass of `Measure.dirac a` sits at `a`, which is the `k = 0` element of the
    progression `a + 1 * ℤ`, so the set of points off that progression is null. The example
    is degenerate, and that is its whole job: without it `IsLatticeLaw` is a predicate no
    measure in this corpus is shown to satisfy, and only the nonlattice branch of
    `LatticeDatum.Describes` would have anything to be checked against. It is not evidence
    that the lattice branch is *interesting*, only that it is not empty. -/
theorem dirac_isLatticeLaw (a : ℝ) :
    IsLatticeLaw (MeasureTheory.Measure.dirac a) 1 a := by
  refine ⟨one_pos, ?_⟩
  have hsub : {x : ℝ | ∀ k : ℤ, x ≠ a + 1 * k} ⊆ ({a} : Set ℝ)ᶜ := by
    intro x hx
    simpa using hx 0
  exact MeasureTheory.measure_mono_null hsub (by simp)

/-- A law is **nonlattice** when no span and offset make it a lattice law. -/
def IsNonlatticeLaw (μ : MeasureTheory.Measure ℝ) : Prop :=
  ∀ span offset : ℝ, ¬ IsLatticeLaw μ span offset

/-- The proposition a `LatticeDatum` makes about a law, so the datum can be checked
    against something rather than asserted. -/
def LatticeDatum.Describes : LatticeDatum → MeasureTheory.Measure ℝ → Prop
  | .nonlattice, μ => IsNonlatticeLaw μ
  | .lattice span offset, μ => IsLatticeLaw μ span offset

/-- The law of the increment `log g²` for a standard Gaussian `g`. -/
noncomputable def logSqGaussianLaw : MeasureTheory.Measure ℝ :=
  stdGaussianMeasure.map (fun x ↦ Real.log (x ^ 2))

/-- The pushforward map sends `0` to Mathlib's junk `Real.log 0 = 0`.  The law is unaffected:
the standard Gaussian gives `{0}` measure zero, so the junk point carries no mass and no
statement about `logSqGaussianLaw` depends on the value there. -/
theorem logSqGaussianLaw_at_zero_is_junk : Real.log ((0 : ℝ) ^ 2) = 0 := by
  norm_num


/-- **`log g²` is nonlattice.**

    Every arithmetic progression is countable. Its preimage under `x ↦ log (x²)` is
    contained in zero together with the positive and negative square roots of the
    progression's exponentials, hence is countable as well. The atomless Gaussian measure
    assigns that preimage measure zero, whereas a lattice law would assign its complement
    measure zero. -/
theorem logSqGaussian_nonlattice : IsNonlatticeLaw logSqGaussianLaw := by
  intro span offset hlattice
  let progression : Set ℝ := Set.range fun k : ℤ ↦ offset + span * k
  let logSquare : ℝ → ℝ := fun x ↦ Real.log (x ^ 2)
  have hprogression : progression.Countable := Set.countable_range _
  have hprogressionMeasurable : MeasurableSet progression :=
    hprogression.measurableSet
  let positiveRoot : ℤ → ℝ := fun k ↦ Real.sqrt (Real.exp (offset + span * k))
  have hpreimage : logSquare ⁻¹' progression ⊆
      ({0} : Set ℝ) ∪ Set.range positiveRoot ∪ Set.range (fun k ↦ -positiveRoot k) := by
    intro x hx
    rcases hx with ⟨k, hk⟩
    by_cases hx0 : x = 0
    · exact Or.inl (Or.inl (by simp [hx0]))
    · have hsqpos : 0 < x ^ 2 := sq_pos_of_ne_zero hx0
      have hsquare : x ^ 2 = Real.exp (offset + span * k) := by
        have hexp := congrArg Real.exp hk
        have hleft : Real.exp (logSquare x) = x ^ 2 := by
          change Real.exp (Real.log (x ^ 2)) = x ^ 2
          exact Real.exp_log hsqpos
        calc
          x ^ 2 = Real.exp (logSquare x) := hleft.symm
          _ = Real.exp (offset + span * k) := hexp.symm
      have hrootSquare : positiveRoot k ^ 2 = Real.exp (offset + span * k) := by
        exact Real.sq_sqrt (Real.exp_nonneg _)
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp (hsquare.trans hrootSquare.symm) with hpos | hneg
      · exact Or.inl (Or.inr ⟨k, hpos.symm⟩)
      · exact Or.inr ⟨k, hneg.symm⟩
  have hpreimageCountable : (logSquare ⁻¹' progression).Countable :=
    ((Set.countable_singleton 0).union (Set.countable_range positiveRoot) |>.union
      (Set.countable_range fun k ↦ -positiveRoot k)).mono hpreimage
  letI : MeasureTheory.NoAtoms stdGaussianMeasure := by
    unfold stdGaussianMeasure
    exact ProbabilityTheory.noAtoms_gaussianReal (by norm_num)
  have hpreimageZero : stdGaussianMeasure (logSquare ⁻¹' progression) = 0 :=
    hpreimageCountable.measure_zero stdGaussianMeasure
  have hprogressionZero : logSqGaussianLaw progression = 0 := by
    unfold logSqGaussianLaw
    rw [MeasureTheory.Measure.map_apply (by fun_prop) hprogressionMeasurable]
    exact hpreimageZero
  have hoffProgression :
      {x : ℝ | ∀ k : ℤ, x ≠ offset + span * k} = progressionᶜ := by
    ext x
    simp only [progression, Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_range,
      not_exists, ne_eq]
    constructor
    · intro h k hk
      exact h k hk.symm
    · intro h k hk
      exact h k hk.symm
  have hcomplementZero : logSqGaussianLaw progressionᶜ = 0 := by
    rw [← hoffProgression]
    exact hlattice.2
  have hcomplementOne : logSqGaussianLaw progressionᶜ = 1 := by
    have hfinite : logSqGaussianLaw progression ≠ ⊤ := by
      rw [hprogressionZero]
      exact ENNReal.zero_ne_top
    have huniv : logSqGaussianLaw Set.univ = 1 := by
      unfold logSqGaussianLaw
      rw [MeasureTheory.Measure.map_apply (by fun_prop) MeasurableSet.univ]
      simp [stdGaussianMeasure]
    rw [MeasureTheory.measure_compl hprogressionMeasurable hfinite, huniv,
      hprogressionZero]
    simp
  rw [hcomplementZero] at hcomplementOne
  exact (zero_ne_one : (0 : ENNReal) ≠ 1) hcomplementOne

/-- A triple of Mellin data for a coordinate law: drift, jet variance, lattice datum.

It is a record for carrying those three numbers together, and nothing here shows it is
*complete* — that an independent design observes these and nothing else is exactly the
clause this file does not prove (see the header). Two laws with equal triples are not
thereby shown to be indistinguishable. -/
structure MellinObservables where
  /-- `c = E[x² log x²] = psi'(1)`, the size-biased drift. -/
  drift : ℝ
  /-- `v = psi''(1)`, the size-biased increment variance. -/
  jetVariance : ℝ
  /-- The lattice datum of `log x²`. -/
  latticeDatum : LatticeDatum

/-- **Poisson-intensity inflation factor of a lattice law**, `h / (1 - exp (-h))`.

At a threshold placed exactly on the lattice (`delta = 0`), the exceedance intensity of
a lattice law exceeds the nonlattice/Gaussian intensity by this factor. -/
noncomputable def latticeInflation (h : ℝ) : ℝ := h / (1 - Real.exp (-h))

/-- **The lattice inflation factor at zero spacing, named, and a removable singularity missed.**
As `h` tends to zero the ratio `h / (1 - exp (-h))` tends to `1`: the inflation factor is
continuous there and the continuum limit is the identity. Lean returns `0` instead, because the
divisor is junk-zero -- so the one point where the answer is known exactly is the one point the
definition gets wrong, and it gets it wrong by the whole factor. Consumers must require
`h ≠ 0`. -/
theorem latticeInflation_zero_spacing_is_junk :
    latticeInflation 0 = 0 := by
  unfold latticeInflation
  simp

/-- The general bracket `rho(delta) = h * exp (-delta) / (1 - exp (-h))`, where
`delta ∈ [0, h)` is the distance from the threshold up to the next lattice point.
`latticeInflation h = latticeBracket h 0`. -/
noncomputable def latticeBracket (h δ : ℝ) : ℝ :=
  h * Real.exp (-δ) / (1 - Real.exp (-h))

/-- **The lattice bracket at zero spacing, named.** The same divisor as `latticeInflation`, and
the same removable singularity: the true limit is `exp (-δ)`, and Lean returns `0` for every
`δ`. Consumers must require `h ≠ 0`. -/
theorem latticeBracket_zero_spacing_is_junk (δ : ℝ) :
    latticeBracket 0 δ = 0 := by
  unfold latticeBracket
  simp

@[simp] theorem latticeBracket_zero (h : ℝ) : latticeBracket h 0 = latticeInflation h := by
  unfold latticeBracket latticeInflation
  simp

/-- The denominator is strictly positive for `h > 0`. -/
theorem one_sub_exp_neg_pos {h : ℝ} (hh : 0 < h) : 0 < 1 - Real.exp (-h) :=
  sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))

/-- **The lattice inflation factor is strictly greater than one.**

This is the quantitative heart of Theorem 1b: a lattice law with span `h > 0`, matched
to the Gaussian in the full 2-jet `(c, v)`, still produces a **strictly larger**
Poisson exceedance intensity at a lattice-aligned threshold. Strictly different jump
intensities give strictly different compound-Poisson limits, so the law is separated
from the Gaussian. -/
theorem one_lt_latticeInflation {h : ℝ} (hh : 0 < h) : 1 < latticeInflation h := by
  have hden : 0 < 1 - Real.exp (-h) := one_sub_exp_neg_pos hh
  have hlt : 1 - Real.exp (-h) < h := by
    have := Real.one_sub_lt_exp_neg hh.ne'
    linarith
  unfold latticeInflation
  rw [lt_div_iff₀ hden]
  linarith

/-- **The bracket is normalized: it averages to one across the lattice cell.**

Stated algebraically: `(1 - exp (-h))` times the inflation factor is exactly `h`,
which is the statement that `(1/h) * ∫_0^h rho(delta) d delta = 1`, since
`∫_0^h exp (-delta) d delta = 1 - exp (-h)`.

The content is that the lattice effect is a *phase* effect, invisible on average and
maximal exactly on the lattice — which is why the design in Theorem 1b spends its one
real degree of freedom on aligning the threshold. -/
theorem latticeInflation_normalization {h : ℝ} (hh : 0 < h) :
    (1 - Real.exp (-h)) * latticeInflation h = h := by
  have hden : (1 : ℝ) - Real.exp (-h) ≠ 0 := ne_of_gt (one_sub_exp_neg_pos hh)
  unfold latticeInflation
  field_simp

/-- The bracket decreases as the threshold moves off the lattice: alignment is
optimal. -/
theorem latticeBracket_antitone {h : ℝ} (hh : 0 < h) :
    ∀ ⦃δ₁ δ₂ : ℝ⦄,
      δ₁ ≤ δ₂ → latticeBracket h δ₂ ≤ latticeBracket h δ₁ := by
  intro δ₁ δ₂ hδ
  have hden : 0 < 1 - Real.exp (-h) := one_sub_exp_neg_pos hh
  have hexp : Real.exp (-δ₂) ≤ Real.exp (-δ₁) := Real.exp_le_exp.mpr (by linarith)
  have key : h * Real.exp (-δ₂) ≤ h * Real.exp (-δ₁) :=
    mul_le_mul_of_nonneg_left hexp hh.le
  unfold latticeBracket
  rw [div_eq_mul_inv, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right key (inv_nonneg.mpr hden.le)

/-!
## 2. The barrier is absent

No `ChaosSpectroscopy` record is exported. Holding Stone's local CLT, the lattice local
CLT and Gnedenko-Kolmogorov triangular-array convergence as *fields*, with a `barrier`
field carrying the central indistinguishability claim, would let projection theorems close
by `exact S.barrier`. There is no such record and nothing replaces it — no barrier, no
factorization, no chameleon-completeness
theorem is exported by this file.

Two conditions any future barrier statement must carry explicitly, recorded because
both once lived only in prose:

* **disjoint variable supports**, i.e.
  `Calibrator.EpistaticChaos.GenotypeDesign.VariantDisjoint` — non-overlapping genes,
  disjoint LD blocks, partitioned windows, and not sliding windows or overlapping
  pathway panels;
* **sign symmetry of the coordinate law**, which for a standardized Hardy-Weinberg
  genotype holds at `q = 1/2` and nowhere else in the polymorphic range
  (`EpistaticChaos.standardizedGenotype_symmetric_iff`), and where
  `Calibrator.PolygenicSpectroscopy.hweMellinJetVariance_half` gives `v(1/2) = 0`, so
  the symmetric branch meets the genotypes only at a jet-variance-free point. The
  drift does not degenerate there: `c(1/2) = log 2`.

The results that do apply to genotypes across the whole frequency spectrum are the ones
that never invoke symmetry: the lattice arithmetic of Section 1 and the
drift/condensation machinery of `Calibrator.Condensation`.
-/

/-!
## 3. The inflation factor transported through an injection

The only analytic content available here is `one_lt_latticeInflation`. The statement
below carries it into an abstract limit space and is recorded for what it is: an
arithmetic transport, not a detection theorem.
-/

/-- Given an injection `limitOfIntensity` from intensities to limit laws, an intensity
`μ₀ > 0` and a span `h > 0`, the images of `μ₀` and of `latticeInflation h * μ₀` differ.
The proof is `1 < latticeInflation h` (`one_lt_latticeInflation`) transported through
the injection; the remaining hypotheses merely name the two images.

**This is not lattice detection and must not be cited as such.** The three facts that
would make it one — that a lattice law's exceedance intensity at an aligned threshold is
`latticeInflation h` times the nonlattice one (the two local CLTs), and that distinct
intensities give distinct compound-Poisson limits (Gnedenko-Kolmogorov) — are the
hypotheses `hIntensityLattice`, `hIntensityGauss` and `hInjective`. None is proved in
this corpus, and supplying them is the whole difficulty. -/
theorem inflated_intensity_ne_of_injective
    {Limit : Type*} (limitOfIntensity : ℝ → Limit)
    (hInjective : Function.Injective limitOfIntensity)
    (μ₀ h : ℝ) (hμ : 0 < μ₀) (hh : 0 < h)
    (gaussianLimit latticeLimit : Limit)
    (hIntensityGauss : gaussianLimit = limitOfIntensity μ₀)
    (hIntensityLattice : latticeLimit = limitOfIntensity (latticeInflation h * μ₀)) :
    latticeLimit ≠ gaussianLimit := by
  rw [hIntensityGauss, hIntensityLattice]
  intro hEq
  have h1 : latticeInflation h * μ₀ = μ₀ := hInjective hEq
  have h2 : 1 < latticeInflation h := one_lt_latticeInflation hh
  nlinarith [h1, h2, hμ]

/-- The Gaussian's Mellin triple. The drift and jet variance are the constants proved in
`Calibrator.Condensation`.

The `nonlattice` datum is not stipulated: it is checked against the law of `log g²` by
`gaussianObservables_describes_logSqGaussianLaw` below. -/
noncomputable def gaussianObservables : MellinObservables where
  drift := condensationConstant
  jetVariance := gaussianJetVariance
  latticeDatum := LatticeDatum.nonlattice

/-- The Gaussian triple's lattice datum says something true about the actual law of
    `log g²`, rather than being a field set by hand.

    The `Describes` predicate ensures that the record agrees with the underlying law rather
    than merely carrying a constructor chosen by hand. -/
theorem gaussianObservables_describes_logSqGaussianLaw :
    gaussianObservables.latticeDatum.Describes logSqGaussianLaw :=
  logSqGaussian_nonlattice

/-- A triple with a `lattice` datum is not the Gaussian triple, whatever its 2-jet.

The content is constructor disjointness on the `latticeDatum` field. It says two records
differ, not that two *laws* are distinguishable by any experiment: both lattice data
here are stipulated by the definitions being compared. -/
theorem lattice_observables_ne_gaussian (c v span offset : ℝ) :
    (⟨c, v, LatticeDatum.lattice span offset⟩ : MellinObservables) ≠ gaussianObservables := by
  intro h
  have h2 : LatticeDatum.lattice span offset = LatticeDatum.nonlattice := by
    simpa [gaussianObservables] using congrArg MellinObservables.latticeDatum h
  exact LatticeDatum.noConfusion h2

/-- Nonlattice triples matching the Gaussian 2-jet. With the barrier gone this predicate
carries no experimental meaning — nothing here says a law with this triple is
indistinguishable from the Gaussian — and `isChameleonObservable_iff` shows it is just
record equality spelled out field by field. It is kept only because
`Calibrator.PolygenicSpectroscopy` states its hard-call comparison in this vocabulary. -/
def IsChameleonObservable (O : MellinObservables) : Prop :=
  O.drift = condensationConstant ∧
  O.jetVariance = gaussianJetVariance ∧
  O.latticeDatum = LatticeDatum.nonlattice

/-- A chameleon observable triple *is* the Gaussian triple: that is the whole point. -/
theorem isChameleonObservable_iff (O : MellinObservables) :
    IsChameleonObservable O ↔ O = gaussianObservables := by
  constructor
  · rintro ⟨h1, h2, h3⟩
    cases O
    simp_all [gaussianObservables]
  · rintro rfl
    exact ⟨rfl, rfl, rfl⟩

end Calibrator
