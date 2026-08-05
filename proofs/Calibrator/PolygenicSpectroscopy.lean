/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Calibrator.CramerStratum
import Calibrator.JetBarrier
import Calibrator.LocalToGlobalCoherence
import Calibrator.HiddenConeAmbiguity

namespace Calibrator

/-!
# Polygenic spectroscopy: the Mellin drift of a genotype, and what it costs

This file carries the condensation theory into population genetics, and it does so by
computing a genuinely new population-genetic quantity in closed form rather than by
analogy.

## The quantity

For a biallelic locus in Hardy-Weinberg equilibrium with alternative-allele frequency
`q`, let `x` be the standardized genotype (centered dosage divided by
`sqrt (2 q (1 - q))`). Its **Mellin drift** is

  `c(q) = E[x ^ 2 * log (x ^ 2)]`,

the mean of `log x ^ 2` under the size-biased law `x ^ 2 dP`. `mellinDrift_eq` below
proves the closed form

  `c(q) = (1 - 2q) ^ 2 * log ((1 - 2q) ^ 2 / (2 q (1 - q))) + 4 q (1 - q) * log 2`.

This is not a moment and not a cumulant; it is the derivative of the Mellin exponent
at the size-bias point, and by `Calibrator.Condensation` it is exactly the quantity
that sets the degree at which the Gaussian genotype surrogate stops being valid.

## The biological claim, stated so it can be falsified

Consider a score that aggregates `N` disjoint epistatic terms, each a product of `m`
standardized genotypes at distinct loci. Every variant has influence `1 / N`, so the
score is as polygenic as any theory could ask, and the additive apparatus of
`Calibrator.ScoreDistribution` applies at `m = 1`. Define

  `maxSafeEpistaticOrder N q = log N / c(q)`.

The claim attached to that quantity was: below it the two score laws agree, above it
the Gaussian surrogate condenses onto a point mass while the true genotype chaos does
not.

**Read the MEASURED block on `maxSafeEpistaticOrder` before quoting any of this.** That
claim has been simulated and is falsified in two of its three parts. The common-variant
column is optimistic by up to `2.64x` — the true genotype chaos leaves the Gaussian
limit at `log N / log(1/V)`, below `log N / c(q)` everywhere except `q = 1/2` — and the
direction is backwards: participation ratio says the **surrogate** condenses first at
`q = 0.2764` and the **genotype** first at `q = 0.5`, with the side set by the sign of
`c(q) - c_G`, which flips inside the common range. What survives is the rare-variant
tail, where the gap falls to `0.0035` and the boundary is correct to `0.4%`.

Because `c(q)` is not constant across the frequency spectrum, the safe order is
frequency-dependent. The rare-variant asymptotic is now pinned from both sides:
`rare_variant_drift_sharp_lower_bound` and `rare_variant_drift_upper_bound` sandwich
`c(q)` between `(1 - 4q) log (1/(2q)) - 6q` and `log (1/(2q)) + 4q log 2`, so

  `c(q) = log (1 / (2q)) + O(q log (1/q))`,

and the drift diverges as `q → 0` at exactly that rate. The mechanism is the
**heterozygote**, whose probability `2q(1-q)` and squared standardized value
`(1-2q)^2 / (2q(1-q))` multiply to `(1-2q)^2 → 1` — it carries the entire second
moment at a diverging log-value. It is *not* the rare homozygote: that has a large
standardized value `≈ sqrt (2/q)` but contributes only
`q^2 * (2/q) * log (2/q) ≈ 2q log (1/q) → 0`. Numerically (see
`proofs/validation/empirical/condensation/check_condensation.py`, which recomputes all of this
by direct summation over the three genotypes):

| alt-allele frequency `q` | `c(q)`  | safe order at `N = 10^6` |
|--------------------------|---------|--------------------------|
| 0.50                     | 0.6931  | 19.9                     |
| 0.2764                   | 0.4159  | 33.2                     |
| 0.20                     | 0.4860  | 28.4                     |
| 0.14                     | 0.7313  | 18.9                     |
| 0.05                     | 1.8676  | 7.4                      |
| 0.01                     | 3.7554  | 3.7                      |
| 0.001                    | 6.1896  | 2.2                      |
| 0.0001                   | 8.5138  | 1.6                      |

The last row is the claim worth arguing about: **at MAF `10 ^ (-4)`, pairwise
interaction terms already exceed the safe order.** A pairwise-epistasis model over
ultra-rare variants is past the condensation boundary, so its Gaussian-surrogate
null distribution — the one used to calibrate interaction tests and to set score
percentiles — is converging to the wrong limit, and no amount of sample size repairs
it. This is a statement about the *surrogate*, not about the biology: the true
genotype aggregate is perfectly well behaved. It is the Gaussian stand-in that fails.

The direction of the effect is **not** the one this section used to assert. "The
Gaussian side condenses, so the surrogate under-disperses" holds in one of the two
regimes measured and reverses in the other; see the MEASURED block on
`maxSafeEpistaticOrder`. What is not in doubt is that a surrogate converging to a
different limit is a calibration problem in exactly the regime — rare variants, high
interaction order — where the literature is least able to check it empirically.

## The drift is non-monotone, and it crosses the Gaussian constant

The table is not monotone, and the non-monotonicity is the most informative thing in
it. `c(q)` *falls* from `log 2 = 0.6931` at `q = 1/2` to a minimum of about `0.4159`
near `q ≈ 0.2764`, then rises without bound as `q → 0`. Two exact points are proved
below:

* `hweMellinDrift_at_sqrt5_point`: at `q = (5 - sqrt 5) / 10 = 0.27639...` the drift
  is **exactly** `(3/5) log 2`, because at that frequency `(1 - 2q) ^ 2 = q (1 - q)`
  and the heterozygote ratio is exactly `1/2`. This is below the Gaussian constant.
* `condensationConstant_lt_drift_of_rare`: at `q = 1 / 256` the drift already exceeds
  the Gaussian constant.

So the genotype drift **crosses** `c_G = 2 - gamma - log 2` somewhere in the ordinary
common-variant range (numerically near `q ≈ 0.140`). At that crossing frequency the
*first* observable is blind: `Calibrator.Condensation`'s drift-separation theorem has
nothing to say, and the genotype law is distinguished from its Gaussian surrogate only
by the second observable (the jet variance, through the condensation-window profile)
and the third (the lattice datum).

That is the motivation for looking past the drift at all: there is a band of allele
frequencies — squarely inside the range that dominates real polygenic scores — where
the leading-order diagnostic cannot see the difference. That the remaining two channels
*do* see it is the trichotomy conjecture of `Calibrator.JetBarrier`, which that file
does not prove and this one does not use.

## The second biological claim: hard calls are lattice, dosages are not

Hard-called genotypes take three values, so `log x ^ 2`
has **finite support** and the coordinate law is not absolutely continuous; imputed
dosages have a density and are nonlattice. `hardCall_arithmeticProgression_at_critical_maf`
below exhibits an explicit allele frequency,

  `q* = (2 - sqrt 2) / 4 = 0.146447...`,

at which the three values of `log x ^ 2` form an **exact arithmetic progression** with
span `h = log ((1 - q*) / q*) = log (3 + 2 sqrt 2) = 1.7627...`, so the hard-call law
is lattice with that span. `Calibrator.JetBarrier.one_lt_latticeInflation` gives
`h / (1 - exp (-h)) = 2.128... > 1` for that span — an inequality about a real function,
which is all it is. Reading it as a *Poisson exceedance intensity* inflated relative to
a nonlattice law with the same 2-jet is the conjectured interpretation and requires two
local limit theorems that are not proved anywhere in this corpus.

Under that interpretation the consequence would be that hard calls and imputed dosages
are not exchangeable at high epistatic order even after matching every moment — a
distinct mechanism from the `r ^ 2`-attenuation of
`Calibrator.ImputationPortability`, which is an additive second-moment effect fully
repaired by rescaling, whereas support is invariant under rescaling
(`CondensationUnification.standardizedSquare_scale_invariant`). The rescaling-invariance
is proved; the intensity reading is not.

## The third claim: the loading-decay convention is irreducible

`Calibrator.HiddenConeAmbiguity` shows that the decay profile of latent loadings is
absent from the complete second-order observables, and that identifiability holds
exactly when the mixing is bounded below. In the genotype setting the "complete
second-order observable" is the noiseless infinite-sample LD/covariance operator, and
the hidden decay profile is the ancestry-loading spectrum. So the choice of how many
principal components to include is a convention in the exact sense of
`Calibrator.Conventions`, and `Calibrator.PCCorrectability` quantifies what correction
achieves *given* that convention — which is the right division of labour.
-/

open scoped BigOperators

/-!
## 0. Summation over the three genotypes

The expansion of a genotype sum into its three terms is `sum_over_genotypes` in
`Calibrator.Probability`, which this module imports transitively.  A second copy
of it lived here under a second name, with the same statement and
the same proof, and nothing in the corpus said the two were one theorem: a repair
to either reached half the call sites.
-/

/-!
## 1. The standardized genotype and its Mellin drift
-/

namespace HardyWeinbergModel

/-- The squared standardized genotype `x ^ 2 = (dosage - 2q) ^ 2 / (2 q (1 - q))`.
This is the multiplicative coordinate: a degree-`m` epistatic monomial has squared
value equal to the product of `m` independent copies of this variable. -/
noncomputable def standardizedSquare (h : HardyWeinbergModel) (g : DiploidGenotype) : ℝ :=
  (h.centeredAltAlleleCount g) ^ 2 / h.genotypeVariance

/-- The **Mellin drift** `c(q) = E[x ^ 2 log x ^ 2]` of a Hardy-Weinberg locus: the
mean of `log x ^ 2` under the size-biased law. By `Calibrator.Condensation` this is
the reciprocal slope of the condensation boundary, i.e. the quantity that fixes the
maximum epistatic order at which the Gaussian genotype surrogate is valid.

It is *not* a moment or a cumulant of the genotype, and no bounded-order moment
diagnostic determines it.

Empirical status: DERIVED from `HardyWeinbergModel.genotypeProb` and
`HardyWeinbergModel.standardizedSquare` by direct summation over the three
genotypes; no free parameter and nothing fitted. Recomputed independently by
`proofs/validation/empirical/condensation/check_condensation.py`, which evaluates this sum
numerically and checks it against `hweMellinDrift` across the frequency
spectrum. -/
noncomputable def mellinDrift (h : HardyWeinbergModel) : ℝ :=
  ∑ g : DiploidGenotype,
    h.genotypeProb g * h.standardizedSquare g * Real.log (h.standardizedSquare g)

end HardyWeinbergModel

/-- Closed form of the Hardy-Weinberg Mellin drift as a function of the
alternative-allele frequency.

Empirical status: DERIVED. Equal to `HardyWeinbergModel.mellinDrift` by
`HardyWeinbergModel.mellinDrift_eq`, which is a proof, not a fit; the two are
also checked against each other numerically across the frequency spectrum by
`proofs/validation/empirical/condensation/check_condensation.py`. No free parameter. -/
noncomputable def hweMellinDrift (q : ℝ) : ℝ :=
  (1 - 2 * q) ^ 2 * Real.log ((1 - 2 * q) ^ 2 / (2 * q * (1 - q))) +
    4 * q * (1 - q) * Real.log 2

/-- **hweMellinDrift at a balanced allele frequency, named.** At `q = 1/2` the leading factor `(1
- 2q)²` vanishes, and it multiplies a logarithm whose argument is `0 / (2q(1-q))` -- junk-zero,
so `Real.log 0` is junk-zero too. The product is zero for two independent reasons and the drift
reduces to its mutation term alone. A balanced frequency is the most common case in a panel, so
this branch is not a corner. Consumers must exclude it by hypothesis. -/
theorem hweMellinDrift_balanced_frequency_is_junk :
    hweMellinDrift (1/2) = 4 * (1/2) * (1 - 1/2) * Real.log 2 := by
  unfold hweMellinDrift
  norm_num

section ClosedForm

variable {h : HardyWeinbergModel}

private theorem hwe_variance_eq (h : HardyWeinbergModel) :
    h.genotypeVariance = 2 * h.altFreq * (1 - h.altFreq) := by
  rw [h.genotypeVariance_eq]
  unfold HardyWeinbergModel.refFreq
  ring

private theorem hwe_centered (h : HardyWeinbergModel) (g : DiploidGenotype) :
    h.centeredAltAlleleCount g = altAlleleCount g - 2 * h.altFreq := by
  unfold HardyWeinbergModel.centeredAltAlleleCount
  rw [h.expectedAltAlleleCount_eq]

/-- The three squared standardized genotype values. -/
theorem standardizedSquare_values (h : HardyWeinbergModel)
    (hq0 : 0 < h.altFreq) (hq1 : h.altFreq < 1) :
    h.standardizedSquare DiploidGenotype.homRef = 2 * h.altFreq / (1 - h.altFreq) ∧
    h.standardizedSquare DiploidGenotype.het =
      (1 - 2 * h.altFreq) ^ 2 / (2 * h.altFreq * (1 - h.altFreq)) ∧
    h.standardizedSquare DiploidGenotype.homAlt = 2 * (1 - h.altFreq) / h.altFreq := by
  have hqne : h.altFreq ≠ 0 := ne_of_gt hq0
  have hpne : (1 : ℝ) - h.altFreq ≠ 0 := by intro hc; apply absurd hq1; linarith [hc]
  -- The three cases need different endgames, so they are split rather than run
  -- through one `<;>` block: the heterozygote goal closes at `simp only`, and a
  -- `field_simp` chained after it would run on an empty goal list.
  refine ⟨?_, ?_, ?_⟩
  · -- homRef: `(0 - 2q)² / (2q(1-q)) = 2q / (1-q)`
    unfold HardyWeinbergModel.standardizedSquare
    rw [hwe_centered, hwe_variance_eq]
    simp only [altAlleleCount]
    field_simp
    ring
  · -- het: `(1 - 2q)² / (2q(1-q))` is already the target, up to `altAlleleCount het = 1`
    unfold HardyWeinbergModel.standardizedSquare
    rw [hwe_centered, hwe_variance_eq]
    simp only [altAlleleCount]
  · -- homAlt: `(2 - 2q)² / (2q(1-q)) = 2(1-q) / q`
    unfold HardyWeinbergModel.standardizedSquare
    rw [hwe_centered, hwe_variance_eq]
    simp only [altAlleleCount]
    field_simp

/-- The three Hardy-Weinberg genotype probabilities in terms of `q`. -/
theorem genotypeProb_values (h : HardyWeinbergModel) :
    h.genotypeProb DiploidGenotype.homRef = (1 - h.altFreq) ^ 2 ∧
    h.genotypeProb DiploidGenotype.het = 2 * (1 - h.altFreq) * h.altFreq ∧
    h.genotypeProb DiploidGenotype.homAlt = h.altFreq ^ 2 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    · unfold HardyWeinbergModel.genotypeProb HardyWeinbergModel.refFreq
      ring

/-- **The closed form of the Hardy-Weinberg Mellin drift.**

`E[x ^ 2 log x ^ 2] = (1 - 2q) ^ 2 log ((1 - 2q) ^ 2 / (2q(1-q))) + 4q(1-q) log 2`.

The proof is a three-term expansion plus the identity
`log (2q / (1-q)) + log (2(1-q) / q) = log 4`, which is what collapses the two
homozygote contributions into a single frequency-weighted `log 2`. -/
theorem HardyWeinbergModel.mellinDrift_eq (h : HardyWeinbergModel)
    (hq0 : 0 < h.altFreq) (hq1 : h.altFreq < 1) :
    h.mellinDrift = hweMellinDrift h.altFreq := by
  set q := h.altFreq with hq
  have hqne : q ≠ 0 := ne_of_gt hq0
  have hpne : (1 : ℝ) - q ≠ 0 := by intro hc; apply absurd hq1; linarith [hc]
  obtain ⟨hX0, hX1, hX2⟩ := standardizedSquare_values h hq0 hq1
  obtain ⟨hP0, hP1, hP2⟩ := genotypeProb_values h
  -- the two homozygote log-terms combine into `log 4 = 2 log 2`
  have hne0 : (2 * q / (1 - q)) ≠ 0 := by
    apply div_ne_zero
    · simpa using hqne
    · exact hpne
  have hne2 : (2 * (1 - q) / q) ≠ 0 := by
    apply div_ne_zero
    · intro hc; exact hpne (by linarith [hc])
    · exact hqne
  have hprod : (2 * q / (1 - q)) * (2 * (1 - q) / q) = 4 := by
    field_simp
    ring
  have hL : Real.log (2 * q / (1 - q)) + Real.log (2 * (1 - q) / q) = 2 * Real.log 2 := by
    rw [← Real.log_mul hne0 hne2, hprod]
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  -- coefficient collapses
  have hA : (1 - q) ^ 2 * (2 * q / (1 - q)) = 2 * q * (1 - q) := by
    field_simp
  have hB : 2 * (1 - q) * q * ((1 - 2 * q) ^ 2 / (2 * q * (1 - q))) = (1 - 2 * q) ^ 2 := by
    field_simp
  have hC : q ^ 2 * (2 * (1 - q) / q) = 2 * q * (1 - q) := by
    field_simp
  unfold HardyWeinbergModel.mellinDrift hweMellinDrift
  rw [sum_over_genotypes, hX0, hX1, hX2, hP0, hP1, hP2, hA, hB, hC]
  linear_combination (2 * q * (1 - q)) * hL

end ClosedForm

/-!
## 2. Two anchor values, and the rare-variant divergence
-/

/-- At an equal-frequency locus the Mellin drift is exactly `log 2 = 0.6931...`.

Compare the Gaussian value `c_G = 2 - gamma - log 2 = 0.7296...`: the two differ, so
`Calibrator.Condensation` already separates a balanced hard-called locus from its
Gaussian surrogate. The drift mismatch at the most benign possible allele frequency is
about `5%` — small, but the separation is a statement about limits, not about size.

That comparison is proved, not merely asserted: see
`hweMellinDrift_half_lt_condensationConstant`, which rests on
`Calibrator.Condensation.log_two_lt_condensationConstant`. It was for a long time stated
here in prose while being underivable, because `condensationConstant_bounds` brackets
`c_G` in `(0.640, 0.807)` and that interval straddles `log 2`. -/
@[simp] theorem hweMellinDrift_half : hweMellinDrift (1 / 2) = Real.log 2 := by
  unfold hweMellinDrift
  norm_num

/-- **An exactly solvable interior point.** At `q = (5 - sqrt 5) / 10 = 0.27639...`
the closed form degenerates: `(1 - 2q) ^ 2 = q (1 - q) = 1/5`, so the heterozygote's
squared standardized value is exactly `1/2` and the drift is exactly `(3/5) log 2`.

This is below the drift at `q = 1/2`, which is what makes the drift non-monotone
across the frequency spectrum: it dips through a minimum in the common-variant range
before diverging for rare variants. -/
theorem hweMellinDrift_at_sqrt5_point :
    hweMellinDrift ((5 - Real.sqrt 5) / 10) = (3 / 5) * Real.log 2 := by
  have hsq : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hnum : (1 - 2 * ((5 - Real.sqrt 5) / 10)) ^ 2 = 1 / 5 := by
    linear_combination (1 / 25 : ℝ) * hsq
  have hden : 2 * ((5 - Real.sqrt 5) / 10) * (1 - (5 - Real.sqrt 5) / 10) = 2 / 5 := by
    linear_combination (-1 / 50 : ℝ) * hsq
  have h4 : 4 * ((5 - Real.sqrt 5) / 10) * (1 - (5 - Real.sqrt 5) / 10) = 4 / 5 := by
    linear_combination (-1 / 25 : ℝ) * hsq
  unfold hweMellinDrift
  rw [hnum, hden, h4]
  have hratio : (1 / 5 : ℝ) / (2 / 5) = 1 / 2 := by norm_num
  rw [hratio, show (1 / 2 : ℝ) = 2⁻¹ by norm_num, Real.log_inv]
  ring

/-- **Rare-variant lower bound.** For `0 < q ≤ 1/8` the Mellin drift is at least
`(1/4) * log (1 / (8q))`, hence grows without bound as the allele frequency falls.

The mechanism is transparent in the closed form: the heterozygote carries squared
standardized value `(1 - 2q) ^ 2 / (2q(1-q)) ≈ 1 / (2q)`, which diverges, and it
carries essentially all of the second moment. A rare variant is a *large* multiplicative
coordinate that occurs *rarely* — exactly the configuration the condensation mechanism
punishes. -/
theorem rare_variant_drift_lower_bound {q : ℝ} (hq0 : 0 < q) (hq : q ≤ 1 / 8) :
    (1 / 4) * Real.log (1 / (8 * q)) ≤ hweMellinDrift q := by
  have hqlt : q < 1 := by linarith
  have hpne : (0 : ℝ) < 1 - q := by linarith
  -- the argument of the heterozygote logarithm dominates `1 / (8q)`
  have hden : (0 : ℝ) < 2 * q * (1 - q) := by positivity
  have h8 : (0 : ℝ) < 8 * q := by linarith
  have hkey : 1 / (8 * q) ≤ (1 - 2 * q) ^ 2 / (2 * q * (1 - q)) := by
    -- The difference factors as `2 q (3 - 15 q + 16 q^2)` over a positive denominator,
    -- and `3 - 15 q ≥ 9/8` on `q ≤ 1/8`.
    rw [← sub_nonneg]
    have hfac : (1 - 2 * q) ^ 2 / (2 * q * (1 - q)) - 1 / (8 * q)
        = (2 * q * (3 - 15 * q + 16 * q ^ 2)) / ((8 * q) * (2 * q * (1 - q))) := by
      field_simp
      ring
    rw [hfac]
    refine div_nonneg ?_ (by positivity)
    have hbracket : (0 : ℝ) ≤ 3 - 15 * q + 16 * q ^ 2 := by
      nlinarith [hq0, hq, sq_nonneg q]
    nlinarith [hq0, hbracket]
  have hlog : Real.log (1 / (8 * q)) ≤ Real.log ((1 - 2 * q) ^ 2 / (2 * q * (1 - q))) :=
    Real.log_le_log (by positivity) hkey
  -- the log is nonnegative because `8 q ≤ 1`
  have hlognn : 0 ≤ Real.log (1 / (8 * q)) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ (by positivity)]
    linarith
  have hcoef : (1 : ℝ) / 4 ≤ (1 - 2 * q) ^ 2 := by nlinarith [hq0, hq]
  have hmain : (1 / 4) * Real.log (1 / (8 * q))
      ≤ (1 - 2 * q) ^ 2 * Real.log ((1 - 2 * q) ^ 2 / (2 * q * (1 - q))) := by
    calc (1 / 4) * Real.log (1 / (8 * q))
        ≤ (1 - 2 * q) ^ 2 * Real.log (1 / (8 * q)) := by
          exact mul_le_mul_of_nonneg_right hcoef hlognn
      _ ≤ (1 - 2 * q) ^ 2 * Real.log ((1 - 2 * q) ^ 2 / (2 * q * (1 - q))) := by
          exact mul_le_mul_of_nonneg_left hlog (by positivity)
  have htail : 0 ≤ 4 * q * (1 - q) * Real.log 2 := by
    have : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    positivity
  unfold hweMellinDrift
  linarith

/-- **Rare-variant upper bound.** For `0 < q ≤ 1/8`,
`c(q) ≤ log (1 / (2q)) + 4 q log 2`.

The two ingredients are that the heterozygote's squared standardized value
`(1 - 2q) ^ 2 / (2q(1-q))` never exceeds `1 / (2q)` on this range — because
`(1 - 2q) ^ 2 ≤ 1 - q` — and that the two homozygote contributions together
supply only `4q(1-q) log 2`, which is `O(q)`.

This is the missing half of the rare-variant asymptotic. `rare_variant_drift_lower_bound`
shows the drift diverges; this shows it diverges no faster than `log (1 / (2q))`,
and `rare_variant_drift_sharp_lower_bound` matches the same leading term from
below. -/
theorem rare_variant_drift_upper_bound {q : ℝ} (hq0 : 0 < q) (hq : q ≤ 1 / 8) :
    hweMellinDrift q ≤ Real.log (1 / (2 * q)) + 4 * q * Real.log 2 := by
  have hqlt : q < 1 := by linarith
  have hp : (0 : ℝ) < 1 - q := by linarith
  have h2q : (0 : ℝ) < 1 - 2 * q := by linarith
  have hqne : q ≠ 0 := ne_of_gt hq0
  have hpne : (1 : ℝ) - q ≠ 0 := ne_of_gt hp
  have hden : (0 : ℝ) < 2 * q * (1 - q) := by positivity
  -- The heterozygote's log argument never exceeds `1 / (2q)`: the difference
  -- factors as `q (3 - 4q)` over a positive denominator.
  have hkey : (1 - 2 * q) ^ 2 / (2 * q * (1 - q)) ≤ 1 / (2 * q) := by
    rw [← sub_nonneg]
    have hfac : 1 / (2 * q) - (1 - 2 * q) ^ 2 / (2 * q * (1 - q))
        = (q * (3 - 4 * q)) / (2 * q * (1 - q)) := by
      field_simp
      ring
    rw [hfac]
    refine div_nonneg ?_ hden.le
    exact mul_nonneg hq0.le (by linarith : (0 : ℝ) ≤ 3 - 4 * q)
  have harg0 : (0 : ℝ) < (1 - 2 * q) ^ 2 / (2 * q * (1 - q)) :=
    div_pos (pow_pos h2q 2) hden
  -- The log is nonnegative because the argument is at least `1` on `q ≤ 1/8`.
  have hlognn : 0 ≤ Real.log ((1 - 2 * q) ^ 2 / (2 * q * (1 - q))) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ hden]
    nlinarith [hq0, hq, sq_nonneg q]
  have hlogle : Real.log ((1 - 2 * q) ^ 2 / (2 * q * (1 - q)))
      ≤ Real.log (1 / (2 * q)) := Real.log_le_log harg0 hkey
  have hcoef : (1 - 2 * q) ^ 2 ≤ 1 := by nlinarith [mul_pos hq0 hp, hq0, hq]
  have hterm1 : (1 - 2 * q) ^ 2 * Real.log ((1 - 2 * q) ^ 2 / (2 * q * (1 - q)))
      ≤ Real.log (1 / (2 * q)) := by
    calc (1 - 2 * q) ^ 2 * Real.log ((1 - 2 * q) ^ 2 / (2 * q * (1 - q)))
        ≤ 1 * Real.log ((1 - 2 * q) ^ 2 / (2 * q * (1 - q))) :=
          mul_le_mul_of_nonneg_right hcoef hlognn
      _ = Real.log ((1 - 2 * q) ^ 2 / (2 * q * (1 - q))) := one_mul _
      _ ≤ Real.log (1 / (2 * q)) := hlogle
  have hterm2 : 4 * q * (1 - q) * Real.log 2 ≤ 4 * q * Real.log 2 := by
    have hl2 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have hgap : 4 * q * Real.log 2 - 4 * q * (1 - q) * Real.log 2
        = (4 * q ^ 2) * Real.log 2 := by ring
    have hnn : 0 ≤ (4 * q ^ 2) * Real.log 2 := mul_nonneg (by positivity) hl2
    linarith
  unfold hweMellinDrift
  linarith

/-- **Rare-variant sharp lower bound.** For `0 < q ≤ 1/8`,
`(1 - 4q) log (1 / (2q)) - 6q ≤ c(q)`.

Paired with `rare_variant_drift_upper_bound` this sandwiches the drift between
`(1 - 4q) log (1/(2q)) - 6q` and `log (1/(2q)) + 4q log 2`, so

  `c(q) = log (1 / (2q)) + O(q log (1/q))`,

and in particular `c(q) / log (1 / (2q)) → 1` as `q → 0`. The sandwich is tight
in practice: at `q = 10 ^ (-5)` the two sides agree to four decimal places.

**Where the divergence comes from, since it is easy to get wrong.** It is the
**heterozygote**, not the rare homozygote. The heterozygote has probability
`2q(1-q)` and squared standardized value `(1-2q)^2 / (2q(1-q))`, and those
multiply to `(1-2q)^2 → 1`: it carries essentially the entire second moment, at
a log-value `≈ log (1/(2q))` that diverges. The rare homozygote is the tempting
culprit because its standardized value is large, `≈ sqrt (2/q)`, but its
contribution is `q^2 * (2/q) * log (2/q) ≈ 2q log (1/q) → 0` — it is *too rare
to matter*. This is why the leading constant is `log (1/(2q))` and not
`log (1/q)` or `log (2/q)`: the `2` is the heterozygote's `2q(1-q)`
denominator.

The proof splits the heterozygote logarithm as
`log (1/(2q)) + log ((1-2q)^2 / (1-q))` and bounds the second piece below by
`-6q`, via `(1-2q)^2 / (1-q) ≥ 1 - 3q ≥ exp (-6q)`. -/
theorem rare_variant_drift_sharp_lower_bound {q : ℝ} (hq0 : 0 < q) (hq : q ≤ 1 / 8) :
    (1 - 4 * q) * Real.log (1 / (2 * q)) - 6 * q ≤ hweMellinDrift q := by
  have hp : (0 : ℝ) < 1 - q := by linarith
  have h2q : (0 : ℝ) < 1 - 2 * q := by linarith
  have h3q : (0 : ℝ) < 1 - 3 * q := by linarith
  have hqne : q ≠ 0 := ne_of_gt hq0
  have hpne : (1 : ℝ) - q ≠ 0 := ne_of_gt hp
  have hden : (0 : ℝ) < 2 * q * (1 - q) := by positivity
  have hBpos : (0 : ℝ) < 1 / (2 * q) := by positivity
  have hRpos : (0 : ℝ) < (1 - 2 * q) ^ 2 / (1 - q) := div_pos (pow_pos h2q 2) hp
  -- Split the heterozygote logarithm into the leading term and a remainder.
  have hsplit : (1 - 2 * q) ^ 2 / (2 * q * (1 - q))
      = (1 / (2 * q)) * ((1 - 2 * q) ^ 2 / (1 - q)) := by
    field_simp
  have hlogsplit : Real.log ((1 - 2 * q) ^ 2 / (2 * q * (1 - q)))
      = Real.log (1 / (2 * q)) + Real.log ((1 - 2 * q) ^ 2 / (1 - q)) := by
    rw [hsplit, Real.log_mul (ne_of_gt hBpos) (ne_of_gt hRpos)]
  -- The remainder is at least `1 - 3q`, since `(1-2q)^2 - (1-3q)(1-q) = q^2 ≥ 0`.
  have hR : (1 : ℝ) - 3 * q ≤ (1 - 2 * q) ^ 2 / (1 - q) := by
    rw [le_div_iff₀ hp]
    nlinarith [sq_nonneg q]
  -- and `1 - 3q ≥ exp (-6q)` on this range, from `exp (6q) ≥ 1 + 6q`.
  have hexp : Real.exp (-(6 * q)) ≤ 1 - 3 * q := by
    have hlin : 6 * q + 1 ≤ Real.exp (6 * q) := Real.add_one_le_exp _
    have hEpos : (0 : ℝ) < Real.exp (6 * q) := Real.exp_pos _
    have hprod : (1 : ℝ) ≤ (1 - 3 * q) * Real.exp (6 * q) := by
      nlinarith [mul_nonneg h3q.le (by linarith : (0 : ℝ) ≤ Real.exp (6 * q) - (6 * q + 1)),
        mul_nonneg hq0.le (by linarith : (0 : ℝ) ≤ 1 - 6 * q)]
    have hmul : Real.exp (-(6 * q)) * Real.exp (6 * q) = 1 := by
      rw [← Real.exp_add]
      simp
    have hcancel : Real.exp (-(6 * q)) * Real.exp (6 * q)
        ≤ (1 - 3 * q) * Real.exp (6 * q) := by
      rw [hmul]
      exact hprod
    exact le_of_mul_le_mul_right hcancel hEpos
  have hlogR : -(6 * q) ≤ Real.log ((1 - 2 * q) ^ 2 / (1 - q)) := by
    have hchain : Real.exp (-(6 * q)) ≤ (1 - 2 * q) ^ 2 / (1 - q) := le_trans hexp hR
    have hmono := Real.log_le_log (Real.exp_pos _) hchain
    rwa [Real.log_exp] at hmono
  -- The leading term is at least `log 4`, comfortably above `6q`.
  have hlogB : Real.log 4 ≤ Real.log (1 / (2 * q)) := by
    refine Real.log_le_log (by norm_num) ?_
    rw [le_div_iff₀ (by positivity)]
    linarith
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
    norm_num
  have hl2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hBnn : 6 * q ≤ Real.log (1 / (2 * q)) := by
    have hsmall : 6 * q ≤ 3 / 4 := by linarith
    linarith [hlogB, hlog4, hl2]
  have hLlow : Real.log (1 / (2 * q)) - 6 * q
      ≤ Real.log ((1 - 2 * q) ^ 2 / (2 * q * (1 - q))) := by
    rw [hlogsplit]
    linarith [hlogR]
  have hcoef : 1 - 4 * q ≤ (1 - 2 * q) ^ 2 := by nlinarith [sq_nonneg q]
  have hmain : (1 - 4 * q) * (Real.log (1 / (2 * q)) - 6 * q)
      ≤ (1 - 2 * q) ^ 2 * Real.log ((1 - 2 * q) ^ 2 / (2 * q * (1 - q))) := by
    have hnn : (0 : ℝ) ≤ Real.log (1 / (2 * q)) - 6 * q := by linarith [hBnn]
    calc (1 - 4 * q) * (Real.log (1 / (2 * q)) - 6 * q)
        ≤ (1 - 2 * q) ^ 2 * (Real.log (1 / (2 * q)) - 6 * q) :=
          mul_le_mul_of_nonneg_right hcoef hnn
      _ ≤ (1 - 2 * q) ^ 2 * Real.log ((1 - 2 * q) ^ 2 / (2 * q * (1 - q))) :=
          mul_le_mul_of_nonneg_left hLlow (by positivity)
  have htail : 0 ≤ 4 * q * (1 - q) * Real.log 2 := by
    have : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    positivity
  have hfinal : (1 - 4 * q) * Real.log (1 / (2 * q)) - 6 * q
      ≤ (1 - 4 * q) * (Real.log (1 / (2 * q)) - 6 * q) := by
    nlinarith [sq_nonneg q, hq0]
  unfold hweMellinDrift
  linarith [hmain, htail, hfinal]

/-- **The genotype drift exceeds the Gaussian condensation constant for rare
variants.** Already at `q = 1 / 256` the drift is above `c_G`.

Together with `hweMellinDrift_at_sqrt5_point` — which gives a drift of
`(3/5) log 2 = 0.4159...`, strictly *below* `c_G = 0.7296...` — this proves the drift
**crosses** the Gaussian constant somewhere in the ordinary allele-frequency range.
At the crossing frequency (numerically `q ≈ 0.140`) drift separation is blind, and the
genotype law is distinguished from its Gaussian surrogate only by the jet variance and
the lattice datum. -/
theorem condensationConstant_lt_drift_of_rare :
    condensationConstant < hweMellinDrift (1 / 256) := by
  have hlb := rare_variant_drift_lower_bound (q := 1 / 256) (by norm_num) (by norm_num)
  have harg : (1 : ℝ) / (8 * (1 / 256)) = 32 := by norm_num
  rw [harg] at hlb
  have h32 : Real.log 32 = 5 * Real.log 2 := by
    rw [show (32 : ℝ) = 2 ^ (5 : ℕ) by norm_num, Real.log_pow]
    norm_num
  rw [h32] at hlb
  have hl2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hcc : condensationConstant < 0.807 := condensationConstant_bounds.2
  linarith

/-- **The drift-blind frequency band exists.** There are allele frequencies on both
sides of the Gaussian constant, so the first observable of the trichotomy fails to
separate somewhere strictly inside the common-variant range. -/
theorem drift_straddles_condensationConstant :
    hweMellinDrift ((5 - Real.sqrt 5) / 10) < condensationConstant ∧
    condensationConstant < hweMellinDrift (1 / 256) := by
  refine ⟨?_, condensationConstant_lt_drift_of_rare⟩
  rw [hweMellinDrift_at_sqrt5_point]
  have hl2 : Real.log 2 < (0.6931471808 : ℝ) := Real.log_two_lt_d9
  have hcc : (0.640 : ℝ) < condensationConstant := condensationConstant_bounds.1
  linarith

/-!
## 3. The safe epistatic order, and its collapse for rare variants
-/

/-- The largest epistatic order at which the Gaussian genotype surrogate is still
valid for an aggregate of `N` disjoint monomials at loci of allele frequency `q`:
`m*(N, q) = log N / c(q)`.

Note that this is a function of the allele frequency, not of the Gaussian
constant: it is `criticalDegree N (hweMellinDrift q)`, so the frequency argument
is carried and the Gaussian value `criticalDegree N condensationConstant` is a
different number, recovered only when `c(q) = c_G`. The gap between them at rare
frequencies is `maxSafeEpistaticOrder_collapse_at_rare_maf`.

**MEASURED, and the common-variant column is optimistic by up to 2.64×.**

`p ↦ log E[(x²)^p]` vanishes at `p = 1`; `c(q)` is its tangent slope there while `log(1/V)`
is its secant slope on `[1,2]`, so by convexity `c(q) ≤ log(1/V)` always, with equality only
at `q = 1/2`. Since `κ₄(S_N) = ((1/V)^m - 3)/N`, the true genotype chaos leaves the Gaussian
limit at `log N / log(1/V)` — **below** this definition's `log N / c(q)` at every polymorphic
frequency except `1/2`. At `N = 10⁶`:

| `q` | this definition | true 4th-moment | surrogate condenses | ratio |
|---|---|---|---|---|
| 0.2764 | 33.22 | 15.08 | 18.93 | **2.64×** |
| 0.25 | 33.01 | 14.09 | 18.93 | 2.63× |
| 0.20 | 28.43 | 12.12 | 18.93 | 2.34× |
| 0.05 | 7.40 | 5.87 | 18.93 | 1.26× |
| 1e-4 | 1.62 | 1.62 | 18.93 | 1.00× |

**The gap is worst exactly where the largest safe order is advertised.** Simulation agrees:
at `q = 0.2764`, `N = 2048`, 4000 replicates per cell, the KS distance between true-genotype
and surrogate score laws sits at null level through `m = 8` and goes significant at `m = 9`–`10`
(`0.034`, `0.059`), reaching `0.306` by `m = 22` — the two laws are demonstrably different
from about **half** the claimed safe order. At `q = 0.05` onset falls between `m = 2` and
`m = 4` against a threshold of `4.08`, where this definition is nearly right.

**There is an internal inconsistency using only committed theorems.** At `q = 0.2764` the
corpus's own `drift_straddles_condensationConstant` proves `c(q) < c_G`, so the surrogate
condenses at order `18.9` while this gate still reads "safe" to `33.2`.

**And the direction claim is backwards.** The prose says that above `m*` the Gaussian
surrogate condenses onto a point mass while the true genotype chaos does not. Participation
ratio says the opposite in both regimes tested: at `q = 0.2764` the **surrogate** condenses
faster at every `m` (`0.661` vs `0.383` at `m = 22`, already `0.61` at the claimed boundary),
while at `q = 0.5` the **genotype** does (`1.000` vs `0.614` at `m = 18`). Which side condenses
first is set by the sign of `c(q) - c_G`, which flips inside the common range — a fact this
corpus proves and then does not use.

**What survives is the rare-variant tail**, and it is the row the corpus calls "the claim
worth arguing about": the convexity gap falls to `0.0035` at `q = 1e-4`, so pairwise
interaction already exceeding the safe order at MAF `1e-4`, `N = 10⁶`, is correct to 0.4%.

Controls: the module docstring table reproduces to all quoted digits (`c(0.2764) = 0.4159`,
safe order `33.22` vs `33.2`); at `m = 1` the genotype and surrogate laws are indistinguishable
(KS `0.019`–`0.025` against a split-half null of `0.024`–`0.035`), confirming
`additive_score_is_subcritical`.

Empirical status: **MIXED** -- FALSIFIED on the common-variant column and on the condensation
direction, VALIDATED on the rare-variant tail (`proofs/validation/empirical/safe_order/`). The
head was `FALSIFIED` and reported only one of the two verdicts the same measurement returned; the
tables above are unchanged and are what says which part carries which. Power, for the validated
part: the convexity gap between `c(q)` and `log(1/V)` spans 0.0035 at `q = 1e-4` to the factor
2.64 at `q = 0.2764`, so the rare-variant agreement is a place the design could have rejected this
body and did not. Scope:
HWE,
unlinked loci, disjoint monomials as defined — no LD, no real genotypes, no structure. -/
noncomputable def maxSafeEpistaticOrder (N q : ℝ) : ℝ :=
  Real.log N / hweMellinDrift q

/-- **maxSafeEpistaticOrder at a monomorphic locus, named.** The order divides by
`hweMellinDrift`, which vanishes at a monomorphic locus. Lean returns `0`: no epistatic order is
safe, where in fact the constraint is vacuous because the locus carries no information. The guard
is invisible here -- it lives inside the called definition. Consumers must exclude it by
hypothesis. -/
theorem maxSafeEpistaticOrder_vanishing_drift_is_junk (N : ℝ) :
    maxSafeEpistaticOrder N 0 = 0 := by
  unfold maxSafeEpistaticOrder hweMellinDrift
  norm_num

theorem maxSafeEpistaticOrder_eq_criticalDegree (N q : ℝ) :
    maxSafeEpistaticOrder N q = criticalDegree N (hweMellinDrift q) := rfl

/-- **The Hardy-Weinberg Mellin drift is strictly positive at every polymorphic
frequency.**

Write `A = (1 - 2q)²`, `B = 2q(1-q)`, and `x = A/B`.  Since `B > 0`, the
closed form factors as

`B * (x log x + 2 log 2)`.

For `x > 0`, Mathlib's elementary inequality `1 - x⁻¹ ≤ log x` gives
`x log x ≥ x - 1 ≥ -1`, while the certified numerical bound on `log 2`
gives `2 log 2 > 1`.  At `x = 0` the logarithmic term vanishes directly.
Thus the factor in parentheses and `B` are both strictly positive. -/
theorem hweMellinDrift_pos (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1) :
    0 < hweMellinDrift q := by
  let A : ℝ := (1 - 2 * q) ^ 2
  let B : ℝ := 2 * q * (1 - q)
  let x : ℝ := A / B
  have hqComplement : 0 < 1 - q := by linarith
  have hB : 0 < B := by
    dsimp [B]
    exact mul_pos (mul_pos (by norm_num) hq0) hqComplement
  have hBne : B ≠ 0 := ne_of_gt hB
  have hx : 0 ≤ x := div_nonneg (sq_nonneg (1 - 2 * q)) hB.le
  have hBx : B * x = A := by
    dsimp [x]
    field_simp [hBne]
  have hfactor :
      hweMellinDrift q = B * (x * Real.log x + 2 * Real.log 2) := by
    calc
      hweMellinDrift q = A * Real.log x + 2 * B * Real.log 2 := by
        dsimp [hweMellinDrift, A, B, x]
        ring
      _ = B * (x * Real.log x + 2 * Real.log 2) := by
        rw [← hBx]
        ring
  have htwo : 1 < 2 * Real.log 2 := by
    nlinarith [Real.log_two_gt_d9]
  have hinner : 0 < x * Real.log x + 2 * Real.log 2 := by
    by_cases hx0 : x = 0
    · simp [hx0]
      linarith
    · have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
      have hlog := Real.one_sub_inv_le_log_of_pos hxpos
      have hmul : x * (1 - x⁻¹) ≤ x * Real.log x :=
        mul_le_mul_of_nonneg_left hlog hx
      have hxinv : x * x⁻¹ = 1 := mul_inv_cancel₀ hx0
      have hlower : -1 ≤ x * Real.log x := by
        nlinarith
      linarith
  rw [hfactor]
  exact mul_pos hB hinner

/-- Subcriticality (the Gaussian surrogate is valid) is exactly `m * c(q) < log N`. -/
theorem epistatic_order_safe_iff {N q m : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    m < maxSafeEpistaticOrder N q ↔ hweMellinDrift q * m < Real.log N :=
  subcritical_iff (hweMellinDrift_pos q hq0 hq1)

/-- **A drift above the Gaussian constant is a safe order below the Gaussian value.**

`maxSafeEpistaticOrder` is `log N / c(q)` and the Gaussian calculation is
`log N / c_G`; both share the numerator, so the comparison is entirely a
comparison of drifts. Stated separately because it is the step at which the
frequency-dependence of `c(q)` becomes an actionable statement about a study
design rather than a fact about a function. -/
theorem maxSafeEpistaticOrder_lt_gaussian_of_drift_excess
    {N q : ℝ} (hN : 0 < Real.log N)
    (hlt : condensationConstant < hweMellinDrift q) :
    maxSafeEpistaticOrder N q < criticalDegree N condensationConstant := by
  unfold maxSafeEpistaticOrder criticalDegree
  exact div_lt_div_of_pos_left hN condensationConstant_pos hlt

/-- **The rare-variant drift is more than seven times the Gaussian constant.**

At `q = 1 / 1024 = 0.00098`, essentially the `q = 0.001` row of the table in the
module docstring, `rare_variant_drift_sharp_lower_bound` gives
`c(q) ≥ (1 - 4/1024) * 9 log 2 - 6/1024 = 6.2081...`, while
`condensationConstant_bounds` gives `c_G < 0.807`. So `c(q) > 7 c_G`.

The crude `rare_variant_drift_lower_bound` cannot reach this: it would only give
`c(q) ≥ (1/4) log (128) = 1.213`, a factor of `1.5`. Recovering the true factor
— numerically `8.5` — is what the sharp bound buys. -/
theorem sevenfold_drift_excess_at_rare_maf :
    7 * condensationConstant < hweMellinDrift (1 / 1024) := by
  have hlb := rare_variant_drift_sharp_lower_bound (q := 1 / 1024) (by norm_num) (by norm_num)
  have harg : (1 : ℝ) / (2 * (1 / 1024)) = 512 := by norm_num
  rw [harg] at hlb
  have h512 : Real.log 512 = 9 * Real.log 2 := by
    rw [show (512 : ℝ) = 2 ^ (9 : ℕ) by norm_num, Real.log_pow]
    norm_num
  rw [h512] at hlb
  have hl2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hcc : condensationConstant < 0.807 := condensationConstant_bounds.2
  linarith

/-- **The safe epistatic order collapses by more than sevenfold at MAF `10 ^ (-3)`.**

`7 * maxSafeEpistaticOrder N (1/1024) < criticalDegree N c_G`: a design calibrated
by the Gaussian condensation constant overstates the safe interaction order at a
rare-variant panel by more than a factor of seven.

The number that matters downstream: at `N = 10 ^ 6` disjoint terms
(`log N = 13.8`) the Gaussian calculation gives a safe order near `19`, and the
genotype drift at this frequency gives a safe order near `2`. Pairwise
interaction statistics on standardized rare variants therefore sit *at* the
condensation boundary, not two decades below it, and the Gaussian-surrogate null
used to calibrate them is converging to a different limit. -/
theorem maxSafeEpistaticOrder_collapse_at_rare_maf {N : ℝ} (hN : 0 < Real.log N) :
    7 * maxSafeEpistaticOrder N (1 / 1024) < criticalDegree N condensationConstant := by
  have hd : 7 * condensationConstant < hweMellinDrift (1 / 1024) :=
    sevenfold_drift_excess_at_rare_maf
  have hgpos : 0 < condensationConstant := condensationConstant_pos
  have hdpos : 0 < hweMellinDrift (1 / 1024) := by linarith
  have hcross : 7 * Real.log N * condensationConstant
      < Real.log N * hweMellinDrift (1 / 1024) := by nlinarith [hN, hd]
  unfold maxSafeEpistaticOrder criticalDegree
  have hrw : 7 * (Real.log N / hweMellinDrift (1 / 1024))
      = 7 * Real.log N / hweMellinDrift (1 / 1024) := by ring
  rw [hrw]
  rw [div_lt_div_iff₀ hdpos hgpos]
  linarith

/-- **Supercriticality from a small allele frequency, in usable form.**

If the frequency is low enough that `(m/4) * log (1 / (8q))` already exceeds `log N`,
then order-`m` epistatic aggregates at that frequency are past the condensation
boundary: the Gaussian surrogate converges to a different limit than the genotypes do.

At `N = 10 ^ 6` and `m = 2` the hypothesis holds for `q` below roughly `10 ^ (-11)`
through this (deliberately crude) bound; the exact drift, which is about four times
larger than the bound at such frequencies, puts the true crossing near
`q ≈ 10 ^ (-4)`. The bound is stated in the weak form because it is the form that is
proved. -/
theorem supercritical_of_small_maf {N m q : ℝ}
    (hq0 : 0 < q) (hq : q ≤ 1 / 8) (hm : 0 < m)
    (hsmall : Real.log N < (m / 4) * Real.log (1 / (8 * q))) :
    Real.log N < m * hweMellinDrift q := by
  have hlb := rare_variant_drift_lower_bound hq0 hq
  have : m * ((1 / 4) * Real.log (1 / (8 * q))) ≤ m * hweMellinDrift q :=
    mul_le_mul_of_nonneg_left hlb hm.le
  nlinarith [hsmall, this]

/-- **There is always a frequency below which even order-`m` aggregates condense.**

Explicitly: for `N ≥ 1` and any order `m > 0`, the frequency
`q = exp (-(4 log N / m + 1)) / 8` is supercritical. Taking `m = 2` this says that
pairwise epistasis among sufficiently rare variants is *always* past the boundary, at
every fixed number of terms `N`. -/
theorem exists_maf_supercritical {N m : ℝ} (hm : 0 < m) (hN : 1 ≤ N) :
    ∃ q : ℝ, 0 < q ∧ q ≤ 1 / 8 ∧ Real.log N < m * hweMellinDrift q := by
  set t : ℝ := 4 * Real.log N / m + 1 with ht
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg hN
  have htpos : 0 < t := by
    have : 0 ≤ 4 * Real.log N / m := by positivity
    rw [ht]; linarith
  refine ⟨Real.exp (-t) / 8, by positivity, ?_, ?_⟩
  · have hle : Real.exp (-t) ≤ 1 := by
      have : Real.exp (-t) < Real.exp 0 := Real.exp_lt_exp.mpr (by linarith)
      rw [Real.exp_zero] at this
      linarith
    linarith
  · have hq0 : 0 < Real.exp (-t) / 8 := by positivity
    have hq : Real.exp (-t) / 8 ≤ 1 / 8 := by
      have hle : Real.exp (-t) ≤ 1 := by
        have : Real.exp (-t) < Real.exp 0 := Real.exp_lt_exp.mpr (by linarith)
        rw [Real.exp_zero] at this
        linarith
      linarith
    refine supercritical_of_small_maf hq0 hq hm ?_
    have hmne : m ≠ 0 := ne_of_gt hm
    have harg : 1 / (8 * (Real.exp (-t) / 8)) = Real.exp t := by
      rw [show 8 * (Real.exp (-t) / 8) = Real.exp (-t) by ring, Real.exp_neg]
      simp
    rw [harg, Real.log_exp, ht]
    have : m / 4 * (4 * Real.log N / m + 1) = Real.log N + m / 4 := by
      field_simp
    rw [this]
    linarith

/-!
## 4. Hard calls are lattice: an exact allele frequency where the span is explicit

The lattice datum of `log x ^ 2` is the third slot of the Mellin triple that
`Calibrator.JetBarrier` conjectures to be observable. A hard-called genotype has
three-point support, so its
`log x ^ 2` is finitely supported; it is a lattice law precisely when the two log-gaps
are commensurable. The cleanest such point is where they are *equal*.
-/

/-- The three log-values of `x ^ 2` are in arithmetic progression exactly when the
heterozygote's squared standardized value is the geometric mean of the two
homozygotes', i.e. when `(1 - 2q) ^ 2 = 4 q (1 - q)`. -/
def hweLatticeCondition (q : ℝ) : Prop := (1 - 2 * q) ^ 2 = 4 * q * (1 - q)

/-- The critical allele frequency `q* = (2 - sqrt 2) / 4 = 0.146447...`. -/
noncomputable def latticeCriticalMaf : ℝ := (2 - Real.sqrt 2) / 4

/-- Reference evaluation: the lattice-critical minor allele frequency in closed form. -/
theorem latticeCriticalMaf_at_reference_point :
    latticeCriticalMaf = (2 - Real.sqrt 2) / 4 := rfl


/-- **The critical frequency is below a quarter.** Positivity alone is shared by the sign-flipped
constant, which sits above one half; this bound is not. -/
theorem latticeCriticalMaf_lt_quarter : latticeCriticalMaf < 1 / 4 := by
  have h2 : (1 : ℝ) < Real.sqrt 2 := by
    have h : Real.sqrt 1 < Real.sqrt 2 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    rwa [Real.sqrt_one] at h
  unfold latticeCriticalMaf
  linarith

theorem latticeCriticalMaf_pos : 0 < latticeCriticalMaf := by
  have h : Real.sqrt 2 < 2 := by
    have : (2 : ℝ) < 2 ^ 2 := by norm_num
    exact (Real.sqrt_lt' (by norm_num)).mpr this
  unfold latticeCriticalMaf
  linarith

theorem latticeCriticalMaf_lt_one : latticeCriticalMaf < 1 := by
  have h : (1 : ℝ) < Real.sqrt 2 := by
    have : (1 : ℝ) ^ 2 < 2 := by norm_num
    exact (Real.lt_sqrt (by norm_num)).mpr this
  unfold latticeCriticalMaf
  linarith

/-- **The hard-call lattice point.** At `q* = (2 - sqrt 2) / 4` the three values of
`log x ^ 2` for a hard-called Hardy-Weinberg locus form an exact arithmetic
progression: the coordinate law is *lattice*.

This is an identity among three real numbers. It does not by itself separate the locus
from a nonlattice law with the same Mellin 2-jet: that step is
`Calibrator.JetBarrier.inflated_intensity_ne_of_injective`, whose local-limit and
Gnedenko-Kolmogorov inputs are hypotheses rather than theorems of this corpus. What is
proved is the progression, and that the associated inflation factor exceeds one. -/
theorem hardCall_arithmeticProgression_at_critical_maf :
    hweLatticeCondition latticeCriticalMaf := by
  have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  unfold hweLatticeCondition latticeCriticalMaf
  nlinarith [hsq]

/-!
### The second Mellin observable of a genotype, and the full triple

The first component of the Mellin triple is `hweMellinDrift`; this section supplies the
second in the same closed form, so the **whole triple of a hard-called locus is
computable from the allele frequency alone**. Computability of the triple is what is
established. Whether the triple is what a design observes — and whether it is all a
design observes — is the `Calibrator.JetBarrier` conjecture, which is not proved.
-/

namespace HardyWeinbergModel

/-- The second Mellin observable: `v(q) = Var(log x^2)` under the size-biased law. -/
noncomputable def mellinJetVariance (h : HardyWeinbergModel) : ℝ :=
  (∑ g : DiploidGenotype,
      h.genotypeProb g * h.standardizedSquare g * (Real.log (h.standardizedSquare g)) ^ 2)
    - h.mellinDrift ^ 2

end HardyWeinbergModel

/-- Closed form of the Hardy-Weinberg jet variance. The coefficient collapse is the
same one that produces `hweMellinDrift`; only the logarithm is squared. -/
noncomputable def hweMellinJetVariance (q : ℝ) : ℝ :=
  2 * q * (1 - q) * (Real.log (2 * q / (1 - q))) ^ 2 +
      (1 - 2 * q) ^ 2 * (Real.log ((1 - 2 * q) ^ 2 / (2 * q * (1 - q)))) ^ 2 +
      2 * q * (1 - q) * (Real.log (2 * (1 - q) / q)) ^ 2 -
    hweMellinDrift q ^ 2

/-- At fixation every logarithm argument collapses to Mathlib's junk `0` and every prefactor
vanishes with it, so the jet variance reports minus the squared drift.  A monomorphic locus has
no Mellin jet at all; the biological range is `0 < q < 1`. -/
theorem hweMellinJetVariance_at_fixation_is_junk :
    hweMellinJetVariance 1 = -(hweMellinDrift 1 ^ 2) := by
  unfold hweMellinJetVariance
  norm_num


/-- **The jet variance of a Hardy-Weinberg locus in closed form.** -/
theorem HardyWeinbergModel.mellinJetVariance_eq (h : HardyWeinbergModel)
    (hq0 : 0 < h.altFreq) (hq1 : h.altFreq < 1) :
    h.mellinJetVariance = hweMellinJetVariance h.altFreq := by
  set q := h.altFreq with hq
  have hqne : q ≠ 0 := ne_of_gt hq0
  have hpne : (1 : ℝ) - q ≠ 0 := by intro hc; apply absurd hq1; linarith [hc]
  obtain ⟨hX0, hX1, hX2⟩ := standardizedSquare_values h hq0 hq1
  obtain ⟨hP0, hP1, hP2⟩ := genotypeProb_values h
  have hA : (1 - q) ^ 2 * (2 * q / (1 - q)) = 2 * q * (1 - q) := by
    field_simp
  have hB : 2 * (1 - q) * q * ((1 - 2 * q) ^ 2 / (2 * q * (1 - q))) = (1 - 2 * q) ^ 2 := by
    field_simp
  have hC : q ^ 2 * (2 * (1 - q) / q) = 2 * q * (1 - q) := by
    field_simp
  have hdrift : h.mellinDrift = hweMellinDrift q := h.mellinDrift_eq hq0 hq1
  unfold HardyWeinbergModel.mellinJetVariance hweMellinJetVariance
  rw [sum_over_genotypes, hX0, hX1, hX2, hP0, hP1, hP2, hA, hB, hC, hdrift]

/-- The lattice span at `q*` is `h = log ((1 - q*) / q*) = log (3 + 2 sqrt 2)`, which
is strictly positive; hence the inflation factor `h / (1 - exp (-h))` is strictly
greater than one and the separation of `hardCall_arithmeticProgression_at_critical_maf`
is quantitative. -/
noncomputable def hardCallLatticeSpan : ℝ :=
  Real.log ((1 - latticeCriticalMaf) / latticeCriticalMaf)

/-- Reference evaluation: the span is the log-odds of the lattice-critical frequency. -/
theorem hardCallLatticeSpan_at_reference_point :
    hardCallLatticeSpan = Real.log ((2 + Real.sqrt 2) / (2 - Real.sqrt 2)) := by
  unfold hardCallLatticeSpan latticeCriticalMaf
  congr 1
  have h : Real.sqrt 2 < 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), Real.sqrt_nonneg 2]
  have hne : (2 : ℝ) - Real.sqrt 2 ≠ 0 := by linarith
  field_simp
  ring


theorem hardCallLatticeSpan_pos : 0 < hardCallLatticeSpan := by
  have h0 : 0 < latticeCriticalMaf := latticeCriticalMaf_pos
  have h1 : latticeCriticalMaf < 1 := latticeCriticalMaf_lt_one
  have hhalf : latticeCriticalMaf < 1 / 2 := by
    have h : (1 : ℝ) < Real.sqrt 2 := by
      have : (1 : ℝ) ^ 2 < 2 := by norm_num
      exact (Real.lt_sqrt (by norm_num)).mpr this
    unfold latticeCriticalMaf
    linarith
  have hgt : 1 < (1 - latticeCriticalMaf) / latticeCriticalMaf := by
    rw [lt_div_iff₀ h0]
    linarith
  unfold hardCallLatticeSpan
  exact Real.log_pos hgt

/-- **The second observable degenerates at the balanced locus.** `v(1/2) = 0`.

At `q = 1/2` the standardized square takes only the two values `2` (both homozygotes)
and `0` (the heterozygote), so `log x ^ 2` is confined to a single point and its
size-biased variance vanishes. This is the same degeneracy that
`Calibrator.EpistaticChaos.centeredDosageSquare_two_valued_at_half` records from the
coding side, reached here from the Mellin side; the two computations agree.

**And `q = 1/2` is the only frequency at which the symmetry hypothesis holds.**
`Calibrator.EpistaticChaos.standardizedGenotype_symmetric_iff` proves that a
standardized Hardy-Weinberg genotype is sign-symmetric exactly at `q = 1/2`. So the
one frequency where the symmetric-law results of `Calibrator.JetBarrier` may be
instantiated at a genotype is the one frequency where the second observable they
speak about is identically zero. The drift is *not* degenerate there — `c(1/2) = log 2`
by `hweMellinDrift_half`, not zero, since the standardized coordinate takes the values
`-sqrt 2, 0, sqrt 2` and is not Rademacher — so drift separation survives; it is the
window theory and the barrier that have nothing to work with.

The consequence is a genuine caveat on the spectroscopy, and it is worth stating
plainly: the proposed positive-jet regime **fails** at exactly `q = 1/2`. The
condensation-window theory of `Calibrator.Condensation` — which needs a non-degenerate
size-biased increment to have a window at all — does not apply at a perfectly balanced
locus. Drift separation still does, since `hweMellinDrift_half` gives `log 2 ≠ c_G`.

So the balanced locus is the one frequency at which the *second* observable carries no
information. Combined with the drift-blind band near `q ≈ 0.140`, the picture is that
each of the three observables has its own blind frequency, and only the trichotomy as a
whole separates genotypes from their Gaussian surrogate across the spectrum. -/
@[simp] theorem hweMellinJetVariance_half : hweMellinJetVariance (1 / 2) = 0 := by
  unfold hweMellinJetVariance
  rw [hweMellinDrift_half]
  norm_num
  ring

/-- **The Mellin triple of a hard-called locus at the lattice frequency.**

The first two components are the closed forms proved above. The third is `lattice`
because the three values of `log x ^ 2` form an exact arithmetic progression there
(`hardCall_arithmeticProgression_at_critical_maf`) — but note the record *stipulates*
that constructor rather than deriving it, so the tie to that theorem is by inspection,
not by proof. Nothing here claims the triple is a complete observable. -/
noncomputable def hardCallObservables : MellinObservables where
  drift := hweMellinDrift latticeCriticalMaf
  jetVariance := hweMellinJetVariance latticeCriticalMaf
  latticeDatum :=
    LatticeDatum.lattice hardCallLatticeSpan
      (Real.log (2 * latticeCriticalMaf / (1 - latticeCriticalMaf)))

/-- The hard-call triple at `q*` is not the Gaussian triple.

The proof is constructor disjointness on the third slot, and both slots are stipulated
in the definitions being compared, so what this establishes is that the corpus files a
hard-called locus at `q*` in the lattice stratum and the Gaussian in the nonlattice one.
"Observationally distinct" would need the barrier, which is absent. -/
theorem hardCallObservables_ne_gaussian : hardCallObservables ≠ gaussianObservables :=
  lattice_observables_ne_gaussian _ _ _ _

/-- Equivalently: a hard-called locus at the lattice frequency is **not** a chameleon.
The chameleon stratum is nonlattice, so no hard call can hide there — the blind spot of
the additive apparatus is populated by imputed dosages, not by genotypes.

**Applicability note.** This theorem is a comparison of observable triples and needs no
symmetry: it holds at `q* = 0.1464...`, where the genotype law is *not* sign-symmetric.
The surrounding *completeness* reading — "and nothing else is observable" — has been
withdrawn because its analytic barrier was supplied as a structure field.  The licensed
claim here is only the proved positive one: this observable triple differs from the
Gaussian triple. -/
theorem hardCall_not_chameleon : ¬ IsChameleonObservable hardCallObservables := by
  rw [isChameleonObservable_iff]
  exact hardCallObservables_ne_gaussian


/-- The inflation factor at `q*` is strictly above one.

That is the entire statement: `one_lt_latticeInflation` at `hardCallLatticeSpan`. The
step from "the factor exceeds one" to "the exceedance intensities differ" to "the
compound-Poisson limits differ" is two unproved local limit theorems and
Gnedenko-Kolmogorov, so this is not a separation of hard calls from dosage
surrogates. -/
theorem hardCall_intensity_inflated :
    1 < latticeInflation hardCallLatticeSpan :=
  one_lt_latticeInflation hardCallLatticeSpan_pos

/-!
## 4a. The lattice frequency is outside the Cramér stratum

`Calibrator.CramerStratum` proves that a lattice coordinate law violates Cramér's
condition (C) outright — `not_cramer_of_lattice`, no Diophantine input — and its
`hwe_not_cramer_of_lattice` specialises that to a Hardy-Weinberg locus. But that
specialisation carries the **gap condition** as a hypothesis, and its docstring says in
so many words that deriving the hypothesis for the coordinate `log x ^ 2` at `q*` "is
*not* done here ... the connection is a route, not a discharged hypothesis".

This section discharges it. The reason it was left open is a real gap and not an
oversight: `hardCall_arithmeticProgression_at_critical_maf` is an identity among the
three *squared standardized values*, while (C) is a condition on the three *logarithms*,
and `CramerStratum` deliberately does not compute logarithms of genotype quantities.
The passage between them is the computation below, and it needs the closed forms
`standardizedSquare_values`, which live here.

At `q*` the lattice identity `(1 - 2q) ^ 2 = 4 q (1 - q)` forces the heterozygote's
squared standardized value to be exactly `2` — the geometric mean of the two homozygote
values `2q/(1-q)` and `2(1-q)/q`, whose product is `4`. Writing
`h = hardCallLatticeSpan = log ((1 - q*) / q*)`, the three logarithms are therefore

  `log 2 - h`,  `log 2`,  `log 2 + h`,

so every gap `log x_u ^ 2 - log x_v ^ 2` lies in `h ℤ` with index difference in
`{-2, -1, 0, 1, 2}`. That is exactly the hypothesis `not_cramer_of_lattice` consumes,
and the conclusion is the scope statement `CramerStratum` was written to support:
**at `q*` a hard-called locus is outside the Cramér stratum**, so every Edgeworth /
Insertion-Lemma result in this development scoped to (C) is unavailable for hard calls
and available for imputed dosages, which are continuous per locus.

Note what is and is not proved. The lattice route gives the failure of (C) at *this*
frequency, unconditionally. The claim that a hard call is outside the stratum at *every*
polymorphic frequency is stronger and is not exported until its simultaneous-approximation
argument is formalized.
-/

/-- The integer position of each genotype in the arithmetic progression that
`log x ^ 2` forms at a lattice frequency. The heterozygote sits at the centre, because
the lattice condition says exactly that its squared standardized value is the geometric
mean of the two homozygotes'. -/
def hardCallLatticeIndex : DiploidGenotype → ℤ
  | DiploidGenotype.homRef => -1
  | DiploidGenotype.het => 0
  | DiploidGenotype.homAlt => 1

/-- **The heterozygote's squared standardized value is exactly `2` at a lattice frequency.**

This is the referent of the literal `2` in the conclusion of
`hardCall_logSquare_eq_of_latticeCondition` below, and it is stated rather than left buried
inside that proof on the `_uses_ploidy` reasoning: a literal that no theorem ties to the
quantity it stands for silently stops tracking when the quantity changes, and no inspection
of the proof term distinguishes "true today" from "load-bearing tomorrow".

Note what the `2` is and is not. It is **not** the ploidy convention `Calibrator.ploidy`
restated: it is `4q(1-q) / (2q(1-q))`, the ratio the lattice condition forces, where the
denominator is `HardyWeinbergModel.genotypeVariance` -- itself a sum over `DiploidGenotype`
rather than an inlined constant, and pinned to the convention by
`Calibrator.mellinDrift_uses_ploidy`. So the chain from this `2` down to `ploidy` is
guarded at exactly one place, which is where it should be.

What this lemma buys is the other half: if the heterozygote's standardized square ever
stops being `2` -- a different genotype coding, a polyploid generalisation -- this breaks
here, loudly, instead of the arithmetic progression quietly ceasing to be one. -/
theorem hweLatticeCondition_het_standardizedSquare (h : HardyWeinbergModel)
    (hq0 : 0 < h.altFreq) (hq1 : h.altFreq < 1)
    (hlat : hweLatticeCondition h.altFreq) :
    h.standardizedSquare DiploidGenotype.het = 2 := by
  have hqne : h.altFreq ≠ 0 := ne_of_gt hq0
  have hpne : (1 : ℝ) - h.altFreq ≠ 0 := by intro hc; exact absurd hq1 (by linarith)
  have hlat' : (1 - 2 * h.altFreq) ^ 2 = 4 * h.altFreq * (1 - h.altFreq) := hlat
  obtain ⟨_, hX1, _⟩ := standardizedSquare_values h hq0 hq1
  rw [hX1, hlat']
  field_simp
  ring

/-- **The three logarithms, in closed form, at any lattice frequency.**

`log x_g ^ 2 = log 2 + log ((1 - q) / q) * index g`, whenever `hweLatticeCondition q`
holds. Stated for a general `q` satisfying the condition rather than only at `q*`,
because the proof uses the condition and nothing else about `q*`; the `q*` instance is
below and is obtained by discharging the hypothesis with
`hardCall_arithmeticProgression_at_critical_maf`. -/
theorem hardCall_logSquare_eq_of_latticeCondition (h : HardyWeinbergModel)
    (hq0 : 0 < h.altFreq) (hq1 : h.altFreq < 1)
    (hlat : hweLatticeCondition h.altFreq) (g : DiploidGenotype) :
    Real.log (h.standardizedSquare g)
      = Real.log 2 + Real.log ((1 - h.altFreq) / h.altFreq)
          * (hardCallLatticeIndex g : ℝ) := by
  have hqne : h.altFreq ≠ 0 := ne_of_gt hq0
  have hppos : (0 : ℝ) < 1 - h.altFreq := by linarith
  have hpne : (1 : ℝ) - h.altFreq ≠ 0 := ne_of_gt hppos
  have h2q : (2 : ℝ) * h.altFreq ≠ 0 := by positivity
  have h2p : (2 : ℝ) * (1 - h.altFreq) ≠ 0 := by positivity
  have hlat' : (1 - 2 * h.altFreq) ^ 2 = 4 * h.altFreq * (1 - h.altFreq) := hlat
  obtain ⟨hX0, hX1, hX2⟩ := standardizedSquare_values h hq0 hq1
  have hspan : Real.log ((1 - h.altFreq) / h.altFreq)
      = Real.log (1 - h.altFreq) - Real.log h.altFreq := Real.log_div hpne hqne
  cases g with
  | homRef =>
    rw [hX0, Real.log_div h2q hpne, Real.log_mul two_ne_zero hqne, hspan]
    simp only [hardCallLatticeIndex]
    push_cast
    ring
  | het =>
    -- The lattice condition is precisely `x_het ^ 2 = 2`: the numerator becomes
    -- `4 q (1 - q)` and the denominator is `2 q (1 - q)`.
    rw [hweLatticeCondition_het_standardizedSquare h hq0 hq1 hlat]
    simp only [hardCallLatticeIndex]
    push_cast
    ring
  | homAlt =>
    rw [hX2, Real.log_div h2p hqne, Real.log_mul two_ne_zero hpne, hspan]
    simp only [hardCallLatticeIndex]
    push_cast
    ring

/-- **The gap condition of `CramerStratum.not_cramer_of_lattice`, discharged at `q*`.**

Every difference of two log-squared-standardized values is an integer multiple of
`hardCallLatticeSpan`. This is the hypothesis that `hwe_not_cramer_of_lattice` carries
abstractly; supplying it here is what turns that theorem from a conditional into a
statement about genotypes. -/
theorem hardCall_logSquare_lattice_at_critical_maf (h : HardyWeinbergModel)
    (hq : h.altFreq = latticeCriticalMaf) (u v : DiploidGenotype) :
    ∃ k : ℤ, Real.log (h.standardizedSquare u) - Real.log (h.standardizedSquare v)
      = hardCallLatticeSpan * k := by
  have hq0 : 0 < h.altFreq := by rw [hq]; exact latticeCriticalMaf_pos
  have hq1 : h.altFreq < 1 := by rw [hq]; exact latticeCriticalMaf_lt_one
  have hlat : hweLatticeCondition h.altFreq := by
    rw [hq]; exact hardCall_arithmeticProgression_at_critical_maf
  have hspan : hardCallLatticeSpan = Real.log ((1 - h.altFreq) / h.altFreq) := by
    unfold hardCallLatticeSpan; rw [hq]
  refine ⟨hardCallLatticeIndex u - hardCallLatticeIndex v, ?_⟩
  rw [hardCall_logSquare_eq_of_latticeCondition h hq0 hq1 hlat u,
    hardCall_logSquare_eq_of_latticeCondition h hq0 hq1 hlat v, hspan]
  push_cast
  ring

/-- **A hard-called locus at `q*` is outside the Cramér stratum.**

The load-bearing consequence, and the reason `Calibrator.CramerStratum` is imported by
this file rather than merely cited by it: this statement is *not provable here*. Its
content is `CramerStratum.not_cramer_of_lattice`, an argument about characteristic
functions returning to modulus one at the lattice frequencies `2 pi n / h`, which has no
counterpart anywhere in the spectroscopy machinery. What this file supplies is the
genotype input — the three logarithms and their common span.

Scope consequence, stated plainly because it constrains the rest of the corpus: results
proved on the Cramér stratum transfer to imputed dosages and **do not** transfer to hard
calls at this frequency. -/
theorem hardCall_not_cramer_at_critical_maf (h : HardyWeinbergModel)
    (hq : h.altFreq = latticeCriticalMaf) :
    ¬ CramerCondition h.genotypeProb (fun g ↦ Real.log (h.standardizedSquare g)) :=
  hwe_not_cramer_of_lattice h (fun g ↦ Real.log (h.standardizedSquare g))
    hardCallLatticeSpan hardCallLatticeSpan_pos
    (hardCall_logSquare_lattice_at_critical_maf h hq)

/-!
## 4b. The proposed invariant list of a genotype coding, and what of it is proved

Nothing in this section establishes that any list of invariants is complete. What is
proved is that four named quantities are computable in closed form from `q`. The
completeness framing below is the *proposal* it came from, retained because the reader
needs it to know why these four and not others.

The proposed Vertex-Weight Law says that in the diagram expansion of a truncated
joint cumulant of an admissible design, the coordinate law enters only through window
factors (functions of the Mellin 2-jet and the arithmetic type of `log x ^ 2`), even
vertex weights (polynomials in the cumulants of `x ^ 2`), and odd vertex weights
(sign-couplings, vanishing exactly when the law is symmetric). So the complete list of
transmissible invariants is

  `(c, v)`, the arithmetic type of `log x ^ 2`, symmetry, and the cumulants of `x ^ 2`.

This upgrades the status of what this file computes. The drift `hweMellinDrift`, the jet
variance `hweMellinJetVariance`, and the symmetry verdict
`Calibrator.EpistaticChaos.standardizedGenotype_symmetric_iff` were three quantities that
happened to be computable in closed form.  The exhaustive observability conclusion is not
exported until its proof is present in Lean.

### Complete, but not minimal — and the distinction is not academic

The four-item list is **complete and redundant**, not complete and minimal, and the
corpus should say which is which. The Tower Rigidity Theorem — an external claim, not
proved in this development; see §4c — gives a strictly smaller
sufficient set: a symmetric unit-variance law with `E[x ^ 4] = 3` whose floor-two and
floor-three laws carry the Gaussian's odd parts *is* the Gaussian. Four data — symmetry,
`sigma_1 = sqrt 2`, and two odd parts — then determine every Mellin jet, every arithmetic
type, every higher floor and every cumulant of every iterated square. The load is carried
by the odd part of the *squared* law, which no moment list mentions, and that is why four
successive finite lists failed before it.

So: the redundant data is what is **computable**, and the minimal data is what is
**decisive**. Nothing here is deleted, because closed forms are what let the condensation
boundary be located at a given allele frequency, and rigidity does not supply those.

**But the redundancy is a statement about the Gaussian fiber only, and no genotype is on
it.** Rigidity collapses the list where its hypotheses hold. Off that fiber the four data
determine nothing, and a polymorphic hard-called locus is never on it: symmetry forces
`q = 1/2` (`Calibrator.EpistaticChaos.standardizedGenotype_symmetric_iff`), while
`q = 1/2` forces `E[x ^ 4] = 2` against the Gaussian's `3`
(`standardizedFourthMoment_ne_gaussian_at_half`). The two hypotheses are jointly
unsatisfiable for a genotype. Hence for the objects this file is about, `hweMellinDrift`
and `hweMellinJetVariance` remain independently informative and the critical-degree
results are untouched — the redundancy never gets a chance to bite.

A converse reading was asserted here and is **false**. It said that
`Calibrator.CondensationUnification.standardizedSquare_never_symmetric` shows the odd part
of the floor-two law nonzero at every polymorphic frequency including `q = 1/2`, hence
that symmetry fails one floor up, always. That theorem is about the *uncentered* square
`x²`, which is non-negative and so trivially never symmetric; its own docstring says in
terms that it does not settle the floor-two question. The tower's floor-two coordinate is
the *centered* square `u = (x² - 1)/σ₁`, and at `q = 1/2` that is Rademacher, which **is**
symmetric (`Calibrator.EpistaticChaos.centeredSquare_rademacher_at_half`,
`centeredSquare_third_moment_zero_iff_balanced`). So the balanced locus is symmetric at
both floors, and floor two supplies no separation there either. The gap that leaves at
`q = 1/2` is filled by the drift instead: `hweMellinDrift_half_lt_condensationConstant`.

### The horizon problem dissolves for rigidity

The statistical-reachability limit formalized in this development — a `log log n` cutoff on
how far up the tower a finite sample can see — costs the rigidity theorem nothing.
Rigidity needs floors two and three only, with `sigma_2 = sqrt 14`, comfortably inside any
sample-size horizon. The floors that are statistically unreachable are exactly the ones
rigidity has already shown to be redundant, so the obstruction and the theorem never meet.
The cutoff remains a real limit on what is *computable* from data; it is not a limit on
what is *decisive*. If the reachability computation later fixes where the tower truncates,
that answer bears on computability alone.

### Two consequences, stated carefully

Both are more delicate than they first appear, and the careless versions are wrong.

**At the balanced locus.** It is tempting to say that at `q = 1/2` the drift is the only
surviving channel. That is false. Of the four invariants, only *symmetry* fails to
separate a balanced genotype from a Gaussian there — both are symmetric. The other three
all still differ: `c(1/2) = log 2 = 0.6931` against `c_G = 0.7296`; `v(1/2) = 0` against
`v_G = pi ^ 2 / 2 - 4 = 0.9348`; and `Var(x ^ 2) = 1` against the Gaussian's `2`. What is
true is narrower and is about *usability*, not information: `v(1/2) = 0` means the
condensation-window machinery, which needs a nondegenerate size-biased increment, cannot
be run at that frequency even though the value `0` is itself distinguishing.

**In the rare regime.** The drift diverges like `log (1 / (2q))`
(`rare_variant_drift_sharp_lower_bound`, `rare_variant_drift_upper_bound`), and the jet
variance does *not* — numerically `v` peaks near `q ≈ 0.1` and decays back toward zero
(`v = 1.81` at `q = 0.1`, `0.31` at `q = 0.001`, `0.0094` at `q = 10 ^ (-5)`), so between
the two Mellin invariants the drift is indeed the dominant rare-variant channel and the
critical-degree collapse is governed by it alone. But it is *not* true that no invariant
grows faster: the second cumulant of `x ^ 2` is `Var(x ^ 2) ~ 1 / (2q)`, which diverges
polynomially rather than logarithmically and dwarfs the drift. That does not disturb the
critical-degree result, because `criticalDegree` is a function of the drift by
definition — but the completeness list does not license "the drift is the fastest-growing
invariant", only "the drift is the one that sets the condensation boundary".
-/

/-- Four invariants of a coordinate law, the ones the proposed Vertex-Weight Law
nominates. It is a record for carrying them together; no theorem here says they are
complete, observable, or independent.

`squareCumulant n` is the `n`-th cumulant of `x ^ 2`; `symmetric` is the sign-coupling
datum, which by `Calibrator.EpistaticChaos.standardizedGenotype_symmetric_iff` holds for a
polymorphic Hardy-Weinberg genotype exactly at `q = 1/2`. -/
structure CodingInvariants where
  /-- `c = E[x ^ 2 log x ^ 2]`, the size-biased drift. -/
  drift : ℝ
  /-- `v`, the size-biased increment variance. -/
  jetVariance : ℝ
  /-- The arithmetic type (lattice datum) of `log x ^ 2`. -/
  arithmeticType : LatticeDatum
  /-- Data-valued indicator of sign symmetry; this is not a theorem field. -/
  symmetric : Bool
  /-- The cumulant sequence of `x ^ 2`. -/
  squareCumulant : ℕ → ℝ

/-! The proposed Vertex-Weight completeness law is not represented by a theorem-valued
record.  The numerical invariants remain available, but exhaustive observability will be
exported only after its diagram argument is formalized in this repository. -/

/-- The invariant quadruple of a hard-called Hardy-Weinberg locus.

The drift and the jet variance are supplied from the closed forms proved in this file;
the arithmetic type and the square-cumulant sequence are taken as *arguments*, because
neither has a closed form here — the arithmetic type is only pinned at the explicit
frequency `latticeCriticalMaf`, and the cumulant sequence is not computed anywhere in
this development. Keeping them as arguments is deliberate: the signature then says
exactly which two of the four this file establishes and which two it assumes.

Empirical status: DERIVED in its first two components, from `hweMellinDrift` and
`hweMellinJetVariance`, both of which are proved equal to direct sums over the three
genotypes and recomputed numerically by
`proofs/validation/empirical/condensation/check_condensation.py`. The third and fourth components
are inputs, not claims. No free parameter. -/
noncomputable def hweCodingInvariants (h : HardyWeinbergModel)
    (arithmeticType : LatticeDatum) (squareCumulant : ℕ → ℝ) : CodingInvariants where
  drift := hweMellinDrift h.altFreq
  jetVariance := hweMellinJetVariance h.altFreq
  arithmeticType := arithmeticType
  symmetric := if h.altFreq = 1 / 2 then true else false
  squareCumulant := squareCumulant

/-- **At the balanced locus, symmetry is the invariant that stops separating.**

`q = 1/2` is the unique polymorphic frequency at which the genotype coding is
sign-symmetric, so it is the unique frequency at which the sign-coupling channel agrees
with the Gaussian's. This is the precise form of the "coincidence": not that the drift
degenerates — it does not, `c(1/2) = log 2` — but that the one invariant which does match
the Gaussian matches it exactly where the jet variance is unusable. -/
theorem balanced_locus_symmetric_component
    (h : HardyWeinbergModel) (hhalf : h.altFreq = 1 / 2)
    (arithmeticType : LatticeDatum) (squareCumulant : ℕ → ℝ) :
    (hweCodingInvariants h arithmeticType squareCumulant).symmetric = true ∧
      (hweCodingInvariants h arithmeticType squareCumulant).drift = Real.log 2 ∧
      (hweCodingInvariants h arithmeticType squareCumulant).jetVariance = 0 := by
  refine ⟨by simp [hweCodingInvariants, hhalf], ?_, ?_⟩
  · show hweMellinDrift h.altFreq = Real.log 2
    rw [hhalf]
    exact hweMellinDrift_half
  · show hweMellinJetVariance h.altFreq = 0
    rw [hhalf]
    exact hweMellinJetVariance_half

/-- **Drift separation at the balanced locus, now proved outright.**

`c(1/2) = log 2 = 0.69315` and `c_G = 2 - gamma - log 2 = 0.72964` differ, so the drift
does separate a balanced hard-called locus from its Gaussian surrogate — and separates it
strictly downward, `c(1/2) < c_G`, so a balanced locus is *more* condensation-prone than
its Gaussian surrogate, with a slightly larger critical degree.

This was asserted in prose at `hweMellinDrift_half` long before it was provable:
`condensationConstant_bounds` gives only `0.640 < c_G < 0.807`, an interval that
straddles `log 2`, so nothing in the development established it. The gap is now closed by
`Calibrator.Condensation.log_two_lt_condensationConstant`, which takes the
Euler-Mascheroni bound out to `H_16 - log 16` and lands at `c_G > 0.69871`. -/
theorem hweMellinDrift_half_lt_condensationConstant :
    hweMellinDrift (1 / 2) < condensationConstant := by
  rw [hweMellinDrift_half]
  exact log_two_lt_condensationConstant

/-- The same fact in the form the separation argument uses: the balanced locus is not
observationally equal to its Gaussian surrogate in the drift. -/
theorem balanced_locus_drift_separates :
    hweMellinDrift (1 / 2) ≠ condensationConstant :=
  ne_of_lt hweMellinDrift_half_lt_condensationConstant

/-!
## 4c. The fourth moment, and why no genotype sits at the Gaussian fiber

The Tower Rigidity Theorem says a symmetric unit-variance law with `E[x ^ 4] = 3` whose
floor-two and floor-three laws carry the Gaussian's odd parts *is* the Gaussian. **It is
not proved in this development** — there is no such theorem anywhere in
`proofs/Calibrator`, so no text may cite it as proved here. It is cited only to say
which hypotheses are being ruled out.

Nothing below depends on it. This section computes the fourth moment of a standardized
genotype from scratch and shows that symmetry and `E[x ^ 4] = 3` are jointly
unsatisfiable for a genotype — a statement about genotypes alone, true whatever becomes
of the rigidity claim.
-/

/-- The fourth moment `E[x ^ 4]` of the standardized genotype. Equivalently `1 + Var(x²)`,
since `E[x ^ 2] = 1`.

Empirical status: DERIVED from `HardyWeinbergModel.genotypeProb` and
`HardyWeinbergModel.standardizedSquare` by direct summation over the three genotypes;
closed form in `standardizedFourthMoment_eq`. No free parameter. -/
noncomputable def HardyWeinbergModel.standardizedFourthMoment (h : HardyWeinbergModel) : ℝ :=
  ∑ g : DiploidGenotype, h.genotypeProb g * h.standardizedSquare g ^ 2

/-- **The fourth moment in closed form: `E[x ^ 4] = 1 / (2q(1-q))`.**

The three contributions are `4q²`, `(1-2q)⁴ / (2q(1-q))` and `4(1-q)²`, and they collapse
by the polynomial identity `2q(1-q)(4q² + 4(1-q)²) + (1-2q)⁴ = 1`. Note this is the
reciprocal of the genotype variance `2q(1-q)`, which is a coincidence of the biallelic
three-point law and not a general fact. -/
theorem HardyWeinbergModel.standardizedFourthMoment_eq (h : HardyWeinbergModel)
    (hq0 : 0 < h.altFreq) (hq1 : h.altFreq < 1) :
    h.standardizedFourthMoment = 1 / (2 * h.altFreq * (1 - h.altFreq)) := by
  have hqne : h.altFreq ≠ 0 := ne_of_gt hq0
  have hpne : (1 : ℝ) - h.altFreq ≠ 0 := by intro hc; apply absurd hq1; linarith [hc]
  obtain ⟨hX0, hX1, hX2⟩ := standardizedSquare_values h hq0 hq1
  obtain ⟨hP0, hP1, hP2⟩ := genotypeProb_values h
  unfold HardyWeinbergModel.standardizedFourthMoment
  rw [sum_over_genotypes, hX0, hX1, hX2, hP0, hP1, hP2]
  field_simp
  ring

/-- **Every polymorphic locus has `E[x ^ 4] ≥ 2`,** because `4q(1-q) ≤ 1`. The bound is
the standardized restatement of the fact that a three-point law cannot be less
leptokurtic than the balanced one. -/
theorem standardizedFourthMoment_ge_two (h : HardyWeinbergModel)
    (hq0 : 0 < h.altFreq) (hq1 : h.altFreq < 1) :
    2 ≤ h.standardizedFourthMoment := by
  have hcomp : (0 : ℝ) < 1 - h.altFreq := by linarith
  have hden : (0 : ℝ) < 2 * h.altFreq * (1 - h.altFreq) := by nlinarith [hq0, hcomp]
  rw [h.standardizedFourthMoment_eq hq0 hq1, le_div_iff₀ hden]
  nlinarith [sq_nonneg (1 - 2 * h.altFreq)]

/-- **Equality holds exactly at the balanced locus.** `E[x ^ 4] = 2` iff `q = 1/2`, since
`(1 - 2q) ^ 2 = 1 - 4q(1-q)`.

This is the *second* independent reason `q = 1/2` is distinguished, the first being
symmetry (`Calibrator.EpistaticChaos.standardizedGenotype_symmetric_iff`). The two are not
a coincidence: both descend from `Binomial(2, q)` being a symmetric law exactly at
`q = 1/2`, so the right framing is common cause. -/
theorem standardizedFourthMoment_eq_two_iff_half (h : HardyWeinbergModel)
    (hq0 : 0 < h.altFreq) (hq1 : h.altFreq < 1) :
    h.standardizedFourthMoment = 2 ↔ h.altFreq = 1 / 2 := by
  have hcomp : (0 : ℝ) < 1 - h.altFreq := by linarith
  have hden : (0 : ℝ) < 2 * h.altFreq * (1 - h.altFreq) := by nlinarith [hq0, hcomp]
  rw [h.standardizedFourthMoment_eq hq0 hq1]
  constructor
  · intro heq
    rw [div_eq_iff (ne_of_gt hden)] at heq
    have hsq : (1 - 2 * h.altFreq) ^ 2 = 0 := by nlinarith [heq]
    have hzero : 1 - 2 * h.altFreq = 0 := by
      exact sq_eq_zero_iff.mp hsq
    linarith
  · intro hhalf
    rw [hhalf]
    norm_num

/-- **The balanced locus is not on the Gaussian fiber either.**

At `q = 1/2` the standardized genotype has `E[x ^ 4] = 2`, against the Gaussian's `3`. So
the one frequency at which the symmetry hypothesis of Tower Rigidity is satisfied is a
frequency at which its fourth-moment hypothesis fails.

Combined with `Calibrator.EpistaticChaos.standardizedGenotype_symmetric_iff` — symmetry
holds only at `q = 1/2` — this says **no polymorphic hard-called locus lies on the
Gaussian fiber at all**: symmetry forces `q = 1/2`, and `q = 1/2` forces `E[x ^ 4] = 2`.
The two hypotheses of the rigidity theorem are jointly unsatisfiable for a genotype. (The
frequency at which `E[x ^ 4] = 3` alone would hold is `q = (3 - sqrt 3) / 6 = 0.21132...`,
where symmetry fails.)

The consequence matters for how the redundancy statement of section 4b is read. Tower
Rigidity makes the computed Mellin invariants redundant *at the Gaussian fiber*, where
four data already pin the law down completely. A genotype is never at that fiber, so for
the objects this file is about, `hweMellinDrift` and `hweMellinJetVariance` are **not**
redundant: nothing in the rigidity data determines them off the fiber. -/
theorem standardizedFourthMoment_ne_gaussian_at_half (h : HardyWeinbergModel)
    (hq0 : 0 < h.altFreq) (hq1 : h.altFreq < 1) (hhalf : h.altFreq = 1 / 2) :
    h.standardizedFourthMoment ≠ 3 := by
  rw [h.standardizedFourthMoment_eq hq0 hq1, hhalf]
  norm_num

/-!
## 5. Where each earlier module now sits

* `Calibrator.ScoreDistribution` and the Berry-Esseen certificates of
  `Calibrator.Probability` are **untouched**: they concern degree-one aggregates,
  which are deeply subcritical (`1 < maxSafeEpistaticOrder N q` for any realistic `N`
  and `q`). The condensation theory does not weaken the additive PGS apparatus; it
  bounds the regime in which that apparatus may be extrapolated.
* `Calibrator.EpistasisAndNonAdditivity` is where the boundary bites. Its
  `pairwiseModel` and `epistaticVariance` are second-moment objects and remain valid;
  what fails above `maxSafeEpistaticOrder` is the *distributional* Gaussian surrogate
  used to calibrate interaction tests.
* `Calibrator.ImputationPortability` gains a second, non-additive mechanism: beyond
  the `r ^ 2` attenuation it already models, hard calls and dosages differ in the
  lattice observable, and that difference survives moment matching.
* `Calibrator.PCCorrectability` is unaffected in content and sharpened in status: it
  answers "what does correction achieve given a convention", and
  `Calibrator.HiddenConeAmbiguity` proves the convention cannot be replaced by an
  inference.
* Summary-statistic coherence checks are bounded-radius audits, and
  `Calibrator.LocalToGlobalCoherence` proves no such audit certifies joint
  realizability at any radius.

## Honest status

Proved here: the closed form of the Mellin drift, its value at `q = 1/2`, the
rare-variant bounds in both directions (hence the asymptotic
`c(q) = log (1/(2q)) + O(q log (1/q))`), the supercriticality criteria, the sevenfold
drift excess and safe-order collapse at `q = 1/1024`, the arithmetic-progression
identity at `q*`, and the strict inflation factor. The local-CLT and
Gnedenko-Kolmogorov inputs that would convert an intensity gap into a limit-law gap are
not exported as results. Not proved anywhere in this development: that the
same conclusions survive linkage disequilibrium between the loci entering one monomial.
Every design here uses disjoint variant sets, which is the independent-design regime;
overlapping designs are the open direction, and in the genetics reading overlap is
exactly LD.

## Symmetry, and which results here depend on it

None of the quantitative results in this file depend on the coordinate law being
sign-symmetric: the Mellin drift, the jet variance, the lattice datum and the
condensation boundary are all computed by direct summation over the three genotypes,
and the direct formulas in `Calibrator.Condensation` require no symmetry field. That is
deliberate and it is what makes them quotable at any allele frequency.

The withdrawn completeness claim required symmetry. A standardized Hardy-Weinberg
genotype is sign-symmetric **iff `q = 1/2`**
(`EpistaticChaos.standardizedGenotype_symmetric_iff`), and
`hweMellinJetVariance_half` shows that the second observable vanishes there.  Thus no
"and nothing else is observable" statement is licensed by this corpus.  The proved
positive comparisons — explicit drift, arithmetic progression, and inflation — remain
valid at their displayed allele frequencies.  Extension to overlapping LD designs is
still open.
-/

end Calibrator
