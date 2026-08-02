import Calibrator.Condensation
import Calibrator.CumulantBlindness
import Calibrator.ObservationalCeiling
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.Linarith

namespace Calibrator

/-!
# The Jet Barrier trichotomy: exactly what independent chaos designs can measure

This file formalizes the **completeness-of-blindness** statement for independent
(disjoint-support) monomial designs, in its corrected trichotomy form.

## The correction that produced the trichotomy

An earlier form of this result claimed that the observable algebra of independent
low-influence chaos over a symmetric product law is the **Mellin 2-jet**
`(c, v) = (E[x² log x²], Var_tilde(log x²))` and nothing else. That statement is
**false as stated**: lattice laws are a live counterexample class. Working the lattice
case out shows it is not an exception to be excluded but a *third observable*.
The corrected statement:

> Independent low-influence chaos over a symmetric product law observes exactly the
> triple `(c, v, lattice datum of log x²)` — and nothing else.

* `(c, v)` via the location of the condensation threshold and the window profile
  (`Calibrator.Condensation`);
* the **lattice datum** via the Poisson-intensity oscillation of Theorem 1b below;
* nothing else, by the nonlattice barrier, Theorem 1a.

The chameleon stratum — laws that pass *every* independent-design experiment — is
therefore the **nonlattice, 2-jet-matched** class. The chameleon construction (an
exponential-family perturbation of a continuous log-density) lives there, so the
calibration object survives with its domain corrected.

## Status labels

* Theorem 1a (nonlattice barrier): the slab-comparison step is discharged by **Stone's
  local CLT** for nonlattice sums with finite variance. That analytic input is carried
  here as a named hypothesis field, not hidden inside a proof.
* Theorem 1b (lattice detection): the intensity-inflation factor
  `h / (1 - exp (-h)) > 1` is proved outright below; the local-CLT and
  Gnedenko-Kolmogorov inputs are again named hypotheses.
* To our knowledge the *completeness* formulation — quantifying over designs rather
  than fixing a test law — is not stated in the Ben Arous-Bogachev-Molchanov /
  Bovier-Kurkova-Loewe / Huang-Austern-Orbanz literature, whose theorems fix the test
  law. That is a checked statement about those sources, not a claim of priority over
  the mechanism, which is theirs (see `Calibrator.Condensation` for the ledger).

## Why a polygenic-score development needs this

The trichotomy is a *calibration instrument*. Any proposed criterion for "is this
genotype/score model Gaussian enough?" can be evaluated on a chameleon: if it
certifies the chameleon, the criterion carries at most 2-jet information and the
barrier bounds its power exactly.

And the lattice observable is not a technicality in genetics — it is the whole
difference between two data types. **Hard-called genotypes are lattice**: the
standardized dosage takes three values, so `log x²` has finite support. **Imputed
dosages are nonlattice**: they have a density. Theorem 1b therefore says that hard
calls and imputed dosages are distinguishable by high-degree epistatic aggregates
*even after matching every moment*, with an explicit inflation factor. See
`Calibrator.PolygenicSpectroscopy`.
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

/-- The complete observable triple of an independent-design chaos experiment. -/
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

/-- The general bracket `rho(delta) = h * exp (-delta) / (1 - exp (-h))`, where
`delta ∈ [0, h)` is the distance from the threshold up to the next lattice point.
`latticeInflation h = latticeBracket h 0`. -/
noncomputable def latticeBracket (h δ : ℝ) : ℝ :=
  h * Real.exp (-δ) / (1 - Real.exp (-h))

@[simp] theorem latticeBracket_zero (h : ℝ) : latticeBracket h 0 = latticeInflation h := by
  unfold latticeBracket latticeInflation
  simp

/-- The denominator is strictly positive for `h > 0`. -/
theorem one_sub_exp_neg_pos {h : ℝ} (hh : 0 < h) : 0 < 1 - Real.exp (-h) := by
  have hlt : Real.exp (-h) < Real.exp 0 := Real.exp_lt_exp.mpr (by linarith)
  rw [Real.exp_zero] at hlt
  linarith

/-- The strict inequality `1 - h < exp (-h)` for `h > 0`, from strict convexity of
`exp`. This is the entire analytic content of the inflation factor. -/
theorem one_sub_lt_exp_neg {h : ℝ} (hh : 0 < h) : 1 - h < Real.exp (-h) := by
  have hne : (-h : ℝ) ≠ 0 := by linarith
  have := Real.add_one_lt_exp hne
  linarith

/-- **The lattice inflation factor is strictly greater than one.**

This is the quantitative heart of Theorem 1b: a lattice law with span `h > 0`, matched
to the Gaussian in the full 2-jet `(c, v)`, still produces a **strictly larger**
Poisson exceedance intensity at a lattice-aligned threshold. Strictly different jump
intensities give strictly different compound-Poisson limits, so the law is separated
from the Gaussian. -/
theorem one_lt_latticeInflation {h : ℝ} (hh : 0 < h) : 1 < latticeInflation h := by
  have hden : 0 < 1 - Real.exp (-h) := one_sub_exp_neg_pos hh
  have hlt : 1 - Real.exp (-h) < h := by
    have := one_sub_lt_exp_neg hh
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
    ∀ ⦃δ₁ δ₂ : ℝ⦄, δ₁ ≤ δ₂ → latticeBracket h δ₂ ≤ latticeBracket h δ₁ := by
  intro δ₁ δ₂ hδ
  have hden : 0 < 1 - Real.exp (-h) := one_sub_exp_neg_pos hh
  have hexp : Real.exp (-δ₂) ≤ Real.exp (-δ₁) := Real.exp_le_exp.mpr (by linarith)
  have key : h * Real.exp (-δ₂) ≤ h * Real.exp (-δ₁) :=
    mul_le_mul_of_nonneg_left hexp hh.le
  unfold latticeBracket
  rw [div_eq_mul_inv, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right key (inv_nonneg.mpr hden.le)

/-!
## 2. The barrier, as a spectroscopy structure

We package the analytic content — Stone's local CLT for nonlattice sums, the lattice
local CLT, and Gnedenko-Kolmogorov triangular-array convergence — as *fields* of a
structure, and prove the consequences. This keeps the unproved analytic inputs visible
at the type level rather than buried, matching the convention in
`Calibrator.Identification`.
-/

/-- An independent-design chaos spectroscopy over a class of coordinate laws.

`Law` ranges over symmetric unit-variance coordinate laws with all moments finite;
`Design` over admissible disjoint-support multilinear designs (arbitrary degrees,
arbitrary coefficients with unit `L2` norm and vanishing max coefficient);
`Limit` over limit laws. -/
structure ChaosSpectroscopy (Law Design Limit : Type*) where
  /-- The observable triple of a coordinate law. -/
  observables : Law → MellinObservables
  /-- The limit law of a design under a coordinate law, when it exists. -/
  limitLaw : Law → Design → Limit
  /-- **Theorem 1a, nonlattice barrier (analytic input).** Two laws agreeing in the
  full observable triple are indistinguishable by every independent design.
  Discharged for nonlattice laws by Stone's local CLT via the unit-slab decomposition
  of the exact tilt identity `P(L > y) = Etilde[exp(-(Ltilde - y)); Ltilde > y]`. -/
  barrier : ∀ ν ν' : Law, observables ν = observables ν' →
    ∀ D : Design, limitLaw ν D = limitLaw ν' D

namespace ChaosSpectroscopy

variable {Law Design Limit : Type*} (S : ChaosSpectroscopy Law Design Limit)

/-- **The observable algebra is exactly three-dimensional: nothing beyond the triple
is measurable.** Any experiment that reports a function of the design limits is a
function of the observable triple alone. -/
theorem experiment_factors_through_observables
    {Report : Type*} (experiment : (Design → Limit) → Report)
    (ν ν' : Law) (h : S.observables ν = S.observables ν') :
    experiment (S.limitLaw ν) = experiment (S.limitLaw ν') := by
  congr 1
  funext D
  exact S.barrier ν ν' h D

/-- **Chameleon calibration.** A *chameleon* is a coordinate law that is not the
Gaussian but has the Gaussian's observable triple. Every independent-design criterion
that certifies the Gaussian also certifies the chameleon — so any criterion in this
family carries at most `(c, v, lattice)` information, and the barrier bounds its power
exactly.

This is the calibration instrument: feed a candidate criterion a chameleon. -/
theorem chameleon_passes_every_independent_criterion
    {Report : Type*} (experiment : (Design → Limit) → Report)
    (accept : Report → Prop)
    (gaussianLaw chameleon : Law)
    (hjet : S.observables chameleon = S.observables gaussianLaw)
    (hgauss : accept (experiment (S.limitLaw gaussianLaw))) :
    accept (experiment (S.limitLaw chameleon)) := by
  rwa [S.experiment_factors_through_observables experiment chameleon gaussianLaw hjet]

/-- **No independent-design criterion decides Gaussianity.** If a chameleon exists
(non-Gaussian, matched triple) then no decision rule built from independent-design
limits can have "is the Gaussian" as its acceptance set. -/
theorem no_independent_design_criterion_decides_gaussianity
    {Report : Type*} (experiment : (Design → Limit) → Report)
    (gaussianLaw chameleon : Law)
    (hne : chameleon ≠ gaussianLaw)
    (hjet : S.observables chameleon = S.observables gaussianLaw) :
    ¬ ∃ accept : Report → Prop,
        ∀ ν : Law, ν = gaussianLaw ↔ accept (experiment (S.limitLaw ν)) :=
  ({ positive := gaussianLaw
     negative := chameleon
     same_data :=
       (S.experiment_factors_through_observables experiment chameleon gaussianLaw hjet).symm
     holds := rfl
     fails := hne } :
      ProbeBlindness (fun ν => experiment (S.limitLaw ν)) (fun ν => ν = gaussianLaw)).no_criterion

end ChaosSpectroscopy

/-!
## 3. Theorem 1b: lattice detection

The lattice case is not covered by the barrier because the lattice datum differs.
The separation is quantitative, and this is where `one_lt_latticeInflation` is used.
-/

/-- **Theorem 1b (lattice detection), separation form.**

Suppose a coordinate law `ν` has lattice increments with span `h > 0` and matches the
Gaussian in the full 2-jet `(c, v)`. Choose the equal-coefficient one-degree design
with the exceedance threshold placed *on* the lattice, and tune `N` so that the
Gaussian exceedance intensity converges to `mu₀ > 0`. Then the `ν`-intensity converges
to `latticeInflation h * mu₀`, which is strictly larger. Distinct nondegenerate
compound-Poisson components with different total rates give distinct laws.

The hypotheses `hIntensityGauss`/`hIntensityLattice` are the local-CLT inputs; the
hypothesis `hInjective` is Gnedenko-Kolmogorov (distinct intensities ⇒ distinct
limits). The strict inequality is proved. -/
theorem lattice_detection
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

/-- The Gaussian's own lattice datum: `log g²` has a density, so the Gaussian is
nonlattice. Recorded as the definitional fact it is. -/
noncomputable def gaussianObservables : MellinObservables where
  drift := condensationConstant
  jetVariance := gaussianJetVariance
  latticeDatum := LatticeDatum.nonlattice

/-- A lattice law is never observationally equal to the Gaussian, whatever its 2-jet:
the third observable already separates them. This is the corrected barrier boundary. -/
theorem lattice_observables_ne_gaussian (c v span offset : ℝ) :
    (⟨c, v, LatticeDatum.lattice span offset⟩ : MellinObservables) ≠ gaussianObservables := by
  intro h
  have h2 : LatticeDatum.lattice span offset = LatticeDatum.nonlattice := by
    simpa [gaussianObservables] using congrArg MellinObservables.latticeDatum h
  exact LatticeDatum.noConfusion h2

/-- The **chameleon stratum**, corrected: nonlattice laws matching the Gaussian 2-jet.
Membership is exactly the condition under which the barrier applies and the law is
certified Gaussian by every independent-design experiment. -/
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
