import Calibrator.Condensation
import Calibrator.CumulantBlindness
import Calibrator.JetBarrier
import Calibrator.LocalToGlobalCoherence
import Calibrator.HiddenConeAmbiguity
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.LinearCombination

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

* **Below it** the score's law is the same whether one models genotypes by their true
  discrete law or by the Gaussian surrogate. The infinitesimal approximation is valid
  uniformly over coefficient patterns.
* **Above it** the Gaussian surrogate's chaos condenses onto a point mass while the
  true genotype chaos does not. The surrogate does not mis-estimate a tail; it
  converges to a *different limit*.

Because `c(q)` is not constant across the frequency spectrum, the safe order is
frequency-dependent, and `rare_variant_drift_lower_bound` shows `c(q)` grows like
`log (1 / q)` as `q → 0`. Numerically (see
`proofs/validation/condensation/check_condensation.py`, which recomputes all of this
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

Note the direction of the effect: the Gaussian side condenses, so the surrogate
*under*-disperses relative to truth. Interaction statistics calibrated against it will
be anticonservative in exactly the regime — rare variants, high interaction order —
where the literature is least able to check them empirically.

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

That is why the trichotomy of `Calibrator.JetBarrier` is a biological necessity rather
than a technical refinement. There is a band of allele frequencies — squarely inside
the frequency range that dominates real polygenic scores — where the leading-order
diagnostic cannot see the difference at all, and the only remaining separations are
the two that no moment-based or cumulant-based method can compute.

## The second biological claim: hard calls are lattice, dosages are not

`Calibrator.JetBarrier` shows that independent-design chaos observes exactly the
triple `(c, v, lattice datum)`. Hard-called genotypes take three values, so `log x ^ 2`
has **finite support** and the coordinate law is not absolutely continuous; imputed
dosages have a density and are nonlattice. `hardCall_arithmeticProgression_at_critical_maf`
below exhibits an explicit allele frequency,

  `q* = (2 - sqrt 2) / 4 = 0.146447...`,

at which the three values of `log x ^ 2` form an **exact arithmetic progression** with
span `h = log ((1 - q*) / q*) = log (3 + 2 sqrt 2) = 1.7627...`, so the hard-call law
is lattice with that span. By `Calibrator.JetBarrier.one_lt_latticeInflation` the
Poisson exceedance intensity is then inflated by `h / (1 - exp (-h)) = 2.128...`
relative to any nonlattice law with the same 2-jet.

Consequence: **hard calls and imputed dosages are not exchangeable at high epistatic
order, even after matching every moment.** This is a distinct mechanism from the
`r ^ 2`-attenuation of `Calibrator.ImputationPortability`, which is an additive,
second-moment effect and is fully repaired by rescaling. Lattice detection is not
repairable by rescaling: it is a property of the support, and moment matching cannot
remove it.

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
-/

/-- Expand a sum over diploid genotypes into its three terms. -/
theorem sum_diploidGenotype (f : DiploidGenotype → ℝ) :
    (∑ g : DiploidGenotype, f g) =
      f DiploidGenotype.homRef + f DiploidGenotype.het + f DiploidGenotype.homAlt := by
  have hrewrite :
      (∑ g : DiploidGenotype, f g) =
        ∑ i : Fin 3, f (DiploidGenotype.equivFin3.symm i) := by
    exact Fintype.sum_equiv DiploidGenotype.equivFin3 _ _ (by
      intro x
      rw [DiploidGenotype.equivFin3_symm_apply_apply])
  rw [hrewrite, Fin.sum_univ_three]
  rfl

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
diagnostic determines it. -/
noncomputable def mellinDrift (h : HardyWeinbergModel) : ℝ :=
  ∑ g : DiploidGenotype,
    h.genotypeProb g * h.standardizedSquare g * Real.log (h.standardizedSquare g)

end HardyWeinbergModel

/-- Closed form of the Hardy-Weinberg Mellin drift as a function of the
alternative-allele frequency. -/
noncomputable def hweMellinDrift (q : ℝ) : ℝ :=
  (1 - 2 * q) ^ 2 * Real.log ((1 - 2 * q) ^ 2 / (2 * q * (1 - q))) +
    4 * q * (1 - q) * Real.log 2

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
  refine ⟨?_, ?_, ?_⟩ <;>
    · unfold HardyWeinbergModel.standardizedSquare
      rw [hwe_centered, hwe_variance_eq]
      simp only [altAlleleCount]
      field_simp
      try ring

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
    first
      | (field_simp; ring)
      | field_simp
  have hL : Real.log (2 * q / (1 - q)) + Real.log (2 * (1 - q) / q) = 2 * Real.log 2 := by
    rw [← Real.log_mul hne0 hne2, hprod]
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  -- coefficient collapses
  have hA : (1 - q) ^ 2 * (2 * q / (1 - q)) = 2 * q * (1 - q) := by
    first
      | (field_simp; ring)
      | field_simp
  have hB : 2 * (1 - q) * q * ((1 - 2 * q) ^ 2 / (2 * q * (1 - q))) = (1 - 2 * q) ^ 2 := by
    first
      | (field_simp; ring)
      | field_simp
  have hC : q ^ 2 * (2 * (1 - q) / q) = 2 * q * (1 - q) := by
    first
      | (field_simp; ring)
      | field_simp
  unfold HardyWeinbergModel.mellinDrift hweMellinDrift
  rw [sum_diploidGenotype, hX0, hX1, hX2, hP0, hP1, hP2, hA, hB, hC]
  linear_combination (2 * q * (1 - q)) * hL

end ClosedForm

/-!
## 2. Two anchor values, and the rare-variant divergence
-/

/-- At an equal-frequency locus the Mellin drift is exactly `log 2 = 0.6931...`.

Compare the Gaussian value `c_G = 2 - gamma - log 2 = 0.7296...`: the two differ, so
`Calibrator.Condensation` already separates a balanced hard-called locus from its
Gaussian surrogate. The drift mismatch at the most benign possible allele frequency is
about `5%` — small, but the separation is a statement about limits, not about size. -/
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
      first
        | (field_simp; ring)
        | field_simp
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
  have hden : (0 : ℝ) < 2 * q * (1 - q) := by positivity
  -- The heterozygote's log argument never exceeds `1 / (2q)`: the difference
  -- factors as `q (3 - 4q)` over a positive denominator.
  have hkey : (1 - 2 * q) ^ 2 / (2 * q * (1 - q)) ≤ 1 / (2 * q) := by
    rw [← sub_nonneg]
    have hfac : 1 / (2 * q) - (1 - 2 * q) ^ 2 / (2 * q * (1 - q))
        = (q * (3 - 4 * q)) / (2 * q * (1 - q)) := by
      first
        | (field_simp; ring)
        | field_simp
    rw [hfac]
    refine div_nonneg ?_ hden.le
    nlinarith [hq0, hq]
  have harg0 : (0 : ℝ) < (1 - 2 * q) ^ 2 / (2 * q * (1 - q)) :=
    div_pos (pow_pos h2q 2) hden
  -- The log is nonnegative because the argument is at least `1` on `q ≤ 1/8`.
  have hlognn : 0 ≤ Real.log ((1 - 2 * q) ^ 2 / (2 * q * (1 - q))) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ hden]
    nlinarith [hq0, hq, sq_nonneg q]
  have hlogle : Real.log ((1 - 2 * q) ^ 2 / (2 * q * (1 - q)))
      ≤ Real.log (1 / (2 * q)) := Real.log_le_log harg0 hkey
  have hcoef : (1 - 2 * q) ^ 2 ≤ 1 := by nlinarith [hq0, hq]
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
  have hden : (0 : ℝ) < 2 * q * (1 - q) := by positivity
  have hBpos : (0 : ℝ) < 1 / (2 * q) := by positivity
  have hRpos : (0 : ℝ) < (1 - 2 * q) ^ 2 / (1 - q) := div_pos (pow_pos h2q 2) hp
  -- Split the heterozygote logarithm into the leading term and a remainder.
  have hsplit : (1 - 2 * q) ^ 2 / (2 * q * (1 - q))
      = (1 / (2 * q)) * ((1 - 2 * q) ^ 2 / (1 - q)) := by
    first
      | (field_simp; ring)
      | field_simp
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
    nlinarith [hEpos, hprod, hmul]
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
`m*(N, q) = log N / c(q)`. -/
noncomputable def maxSafeEpistaticOrder (N q : ℝ) : ℝ :=
  Real.log N / hweMellinDrift q

theorem maxSafeEpistaticOrder_eq_criticalDegree (N q : ℝ) :
    maxSafeEpistaticOrder N q = criticalDegree N (hweMellinDrift q) := rfl

/-- Subcriticality (the Gaussian surrogate is valid) is exactly `m * c(q) < log N`. -/
theorem epistatic_order_safe_iff {N q m : ℝ} (hc : 0 < hweMellinDrift q) :
    m < maxSafeEpistaticOrder N q ↔ hweMellinDrift q * m < Real.log N :=
  subcritical_iff hc

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
  first
    | exact div_lt_div_of_pos_left hN condensationConstant_pos hlt
    | exact div_lt_div_of_lt_left hN condensationConstant_pos hlt

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
      first
        | (field_simp; ring)
        | field_simp
    rw [this]
    linarith

/-!
## 4. Hard calls are lattice: an exact allele frequency where the span is explicit

`Calibrator.JetBarrier` shows the third observable of independent-design chaos is the
lattice datum of `log x ^ 2`. A hard-called genotype has three-point support, so its
`log x ^ 2` is finitely supported; it is a lattice law precisely when the two log-gaps
are commensurable. The cleanest such point is where they are *equal*.
-/

/-- The three log-values of `x ^ 2` are in arithmetic progression exactly when the
heterozygote's squared standardized value is the geometric mean of the two
homozygotes', i.e. when `(1 - 2q) ^ 2 = 4 q (1 - q)`. -/
def hweLatticeCondition (q : ℝ) : Prop := (1 - 2 * q) ^ 2 = 4 * q * (1 - q)

/-- The critical allele frequency `q* = (2 - sqrt 2) / 4 = 0.146447...`. -/
noncomputable def latticeCriticalMaf : ℝ := (2 - Real.sqrt 2) / 4

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

By `Calibrator.JetBarrier.lattice_detection` this locus is therefore separated from
every nonlattice law with the same Mellin 2-jet — in particular from any imputed-dosage
or Gaussian surrogate — by an explicit high-degree design, with Poisson intensity
inflated by `latticeInflation h > 1`. Moment matching cannot remove the effect, because
it is a property of the support. -/
theorem hardCall_arithmeticProgression_at_critical_maf :
    hweLatticeCondition latticeCriticalMaf := by
  have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  unfold hweLatticeCondition latticeCriticalMaf
  nlinarith [hsq]

/-!
### The second Mellin observable of a genotype, and the full triple

`Calibrator.JetBarrier` says independent designs observe exactly `(c, v, lattice)`. The
first component is `hweMellinDrift`; this section supplies the second in the same closed
form, so the **entire observable triple of a hard-called locus is computable from the
allele frequency alone**. That is what makes the abstract trichotomy an instrument here
rather than a classification scheme with no instances.
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
    first
      | (field_simp; ring)
      | field_simp
  have hB : 2 * (1 - q) * q * ((1 - 2 * q) ^ 2 / (2 * q * (1 - q))) = (1 - 2 * q) ^ 2 := by
    first
      | (field_simp; ring)
      | field_simp
  have hC : q ^ 2 * (2 * (1 - q) / q) = 2 * q * (1 - q) := by
    first
      | (field_simp; ring)
      | field_simp
  have hdrift : h.mellinDrift = hweMellinDrift q := h.mellinDrift_eq hq0 hq1
  unfold HardyWeinbergModel.mellinJetVariance hweMellinJetVariance
  rw [sum_diploidGenotype, hX0, hX1, hX2, hP0, hP1, hP2, hA, hB, hC, hdrift]

/-- The lattice span at `q*` is `h = log ((1 - q*) / q*) = log (3 + 2 sqrt 2)`, which
is strictly positive; hence the inflation factor `h / (1 - exp (-h))` is strictly
greater than one and the separation of `hardCall_arithmeticProgression_at_critical_maf`
is quantitative. -/
noncomputable def hardCallLatticeSpan : ℝ :=
  Real.log ((1 - latticeCriticalMaf) / latticeCriticalMaf)

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
`Calibrator.EpistaticChaos.standardizedSquare_two_valued_at_half` records from the
coding side, reached here from the Mellin side; the two computations agree.

The consequence is a genuine caveat on the spectroscopy, and it is worth stating
plainly: `MellinProfile.jetVariance_pos` **fails** at exactly `q = 1/2`. The
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
  first
    | (norm_num; ring)
    | norm_num

/-- **The complete observable triple of a hard-called locus at the lattice frequency.**

Every component is a closed-form function of the allele frequency, and the third
component is `lattice` because the three values of `log x ^ 2` form an exact arithmetic
progression there (`hardCall_arithmeticProgression_at_critical_maf`). -/
noncomputable def hardCallObservables : MellinObservables where
  drift := hweMellinDrift latticeCriticalMaf
  jetVariance := hweMellinJetVariance latticeCriticalMaf
  latticeDatum :=
    LatticeDatum.lattice hardCallLatticeSpan
      (Real.log (2 * latticeCriticalMaf / (1 - latticeCriticalMaf)))

/-- **A hard-called locus is observationally distinct from the Gaussian, whatever its
2-jet.** The third observable separates them outright — no moment computation, no
window tuning, and nothing a cumulant can see.

This is the instantiation that makes `Calibrator.JetBarrier` bite: the abstract
trichotomy is not merely a classification, it has a concrete genotype in the lattice
stratum. -/
theorem hardCallObservables_ne_gaussian : hardCallObservables ≠ gaussianObservables :=
  lattice_observables_ne_gaussian _ _ _ _

/-- Equivalently: a hard-called locus at the lattice frequency is **not** a chameleon.
The chameleon stratum is nonlattice, so no hard call can hide there — the blind spot of
the additive apparatus is populated by imputed dosages, not by genotypes. -/
theorem hardCall_not_chameleon : ¬ IsChameleonObservable hardCallObservables := by
  rw [isChameleonObservable_iff]
  exact hardCallObservables_ne_gaussian


/-- **Hard calls are separated from dosage surrogates at high epistatic order.**
The inflation factor at `q*` is strictly above one, so the Poisson exceedance
intensities differ and the compound-Poisson limits differ. -/
theorem hardCall_intensity_inflated :
    1 < latticeInflation hardCallLatticeSpan :=
  one_lt_latticeInflation hardCallLatticeSpan_pos

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
rare-variant lower bound, the supercriticality criteria, the arithmetic-progression
identity at `q*`, and the strict inflation factor. Carried as named hypotheses in
`Calibrator.JetBarrier`: the local-CLT and Gnedenko-Kolmogorov inputs that convert an
intensity gap into a limit-law gap. Not proved anywhere in this development: that the
same conclusions survive linkage disequilibrium between the loci entering one monomial.
Every design here uses disjoint variant sets, which is the independent-design regime;
overlapping designs are the open direction, and in the genetics reading overlap is
exactly LD.
-/

end Calibrator
