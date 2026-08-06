/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Coalescent.Law
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Tactic

assert_below Descent.Pangenome Descent.PopGen Descent.Spectral Descent.Blindness Descent.Conditionals Descent.Portability Descent.Decision Descent.Program

namespace Descent

/-!
# The holding-time law, `d_k e^{-d_k t}`

`Descent.Coalescent.Law` couples the jump chain to a clock, leaving the clock's law as an
argument.  Kingman's clock is fixed: K-C (1.7) gives the sojourn time in a state with `k`
blocks the density

  `d_k e^{-d_k t}` for `t > 0`,   `d_k = ½ k(k-1)`,

"depending only on `|ξ|`", which is the observation that makes the block count a Markov
chain in its own right (K-C (1.8)-(1.9)).  This file supplies that law and the one integral
it needs, closing the parameter `Law.coalescentLaw` left open.

The integral is `∫_0^∞ d e^{-dt} dt = 1`, done by rescaling to `∫_0^∞ e^{-x} dx = 1`.  It is
the only genuine analysis in the coalescent group -- everything else is counting, algebra, or
telescoping -- which is worth recording, because it locates precisely where the group stops
being combinatorial.

What this does NOT do is prove the mean is `d_k⁻¹`.  `Descent.Coalescent.Rates` sums those
means to get `E(T_n) = 2 - 2/n`, and takes `E(τ_r) = d_r⁻¹` from K-G (5.6) rather than
deriving it; that second integral is not done here either.

## Main results

- `holdDensity`, `holdMeasure`: K-C (1.7).
- `integral_holdDensity`: the mass is one.
- `holdMeasure_isProbabilityMeasure`: so it is a probability measure.
- `coalescentLawExp`: `Law.coalescentLaw` with Kingman's clock supplied.
-/

namespace Coalescent

open MeasureTheory Set Nat

/-- K-C (1.7): the sojourn density in a state with death rate `d`, as a density against
Lebesgue measure.  Zero on `t ≤ 0` -- a sojourn is positive. -/
noncomputable def holdDensity (d : ℝ) (t : ℝ) : ENNReal :=
  if 0 < t then ENNReal.ofReal (d * Real.exp (-(d * t))) else 0

/-- **The mass of K-C (1.7) is one.**  The single integral the coalescent group needs:
rescaling `x = d t` turns it into `∫_0^∞ e^{-x} dx = 1`. -/
theorem integral_holdDensity {d : ℝ} (hd : 0 < d) :
    ∫ t in Ioi (0 : ℝ), d * Real.exp (-(d * t)) = 1 := by
  have hscale : ∫ t in Ioi (0 : ℝ), Real.exp (-(d * t))
      = d⁻¹ • ∫ x in Ioi (d * (0 : ℝ)), Real.exp (-x) :=
    integral_comp_mul_left_Ioi (fun x ↦ Real.exp (-x)) 0 hd
  rw [integral_const_mul, hscale, mul_zero, integral_exp_neg_Ioi, smul_eq_mul]
  simp
  field_simp

theorem holdDensity_integrable {d : ℝ} (hd : 0 < d) :
    IntegrableOn (fun t ↦ d * Real.exp (-(d * t))) (Ioi (0 : ℝ)) := by
  have hbase : IntegrableOn (fun t : ℝ ↦ Real.exp (-(d * t))) (Ioi (0 : ℝ)) := by
    simpa using exp_neg_integrableOn_Ioi (0 : ℝ) hd
  exact hbase.const_mul d

theorem holdDensity_nonneg {d : ℝ} (hd : 0 < d) (t : ℝ) : 0 ≤ d * Real.exp (-(d * t)) := by
  positivity

/-- K-C (1.7) as a measure. -/
noncomputable def holdMeasure (d : ℝ) : Measure ℝ := volume.withDensity (holdDensity d)

/-- **The holding-time law is a probability measure.** -/
instance holdMeasure_isProbabilityMeasure {d : ℝ} (hd : 0 < d) :
    IsProbabilityMeasure (holdMeasure d) := by
  constructor
  have hdens : ∫⁻ t, holdDensity d t = 1 := by
    have hind : ∀ t : ℝ, holdDensity d t
        = (Ioi (0 : ℝ)).indicator (fun t ↦ ENNReal.ofReal (d * Real.exp (-(d * t)))) t := by
      intro t
      unfold holdDensity
      by_cases ht : 0 < t
      · rw [if_pos ht, Set.indicator_of_mem (mem_Ioi.mpr ht)]
      · rw [if_neg ht, Set.indicator_of_not_mem (by simpa using le_of_not_lt ht)]
    calc ∫⁻ t, holdDensity d t
        = ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (d * Real.exp (-(d * t))) := by
          simp only [hind]
          rw [lintegral_indicator measurableSet_Ioi]
      _ = ENNReal.ofReal (∫ t in Ioi (0 : ℝ), d * Real.exp (-(d * t))) := by
          rw [← ofReal_integral_eq_lintegral_ofReal (holdDensity_integrable hd)
            (Filter.Eventually.of_forall fun t ↦ holdDensity_nonneg hd t)]
      _ = 1 := by
          rw [integral_holdDensity hd, ENNReal.ofReal_one]
  rw [holdMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  exact hdens

/-! ### The mean sojourn, `E(τ_r) = d_r⁻¹`

K-G (5.6) states `E(τ_r) = d_r⁻¹`, and `Descent.Coalescent.Rates` sums those means to get
`E(T_n) = 2 - 2/n`.  Until now the corpus took the mean from the paper.  It is a second
integral against the same density, and rescaling turns it into `Γ(2) = 1`. -/

/-- `∫_0^∞ x e^{-x} dx = 1`, which is `Γ(2) = 1! = 1`. -/
theorem integral_id_mul_exp_neg : ∫ x in Ioi (0 : ℝ), x * Real.exp (-x) = 1 := by
  have hgamma : Real.Gamma 2 = ∫ x in Ioi (0 : ℝ), Real.exp (-x) * x ^ ((2 : ℝ) - 1) :=
    Real.Gamma_eq_integral (by norm_num)
  have hone : Real.Gamma 2 = 1 := by
    have h : Real.Gamma ((1 : ℕ) + 1) = ((Nat.factorial 1 : ℕ) : ℝ) :=
      Real.Gamma_nat_eq_factorial 1
    simpa using h
  rw [hone] at hgamma
  rw [hgamma]
  refine setIntegral_congr_fun measurableSet_Ioi fun x hx ↦ ?_
  rw [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one]
  ring

/-- **K-G (5.6): the mean sojourn in a state with death rate `d` is `d⁻¹`.**

`Descent.Coalescent.Rates.meanTransitTime` sums exactly these, so `E(T_n) = 2 - 2/n` now
rests on the density K-C (1.7) rather than on K-G's assertion of its mean. -/
theorem integral_id_mul_holdDensity {d : ℝ} (hd : 0 < d) :
    ∫ t in Ioi (0 : ℝ), t * (d * Real.exp (-(d * t))) = 1 / d := by
  have hpt : ∀ t : ℝ, t * (d * Real.exp (-(d * t)))
      = (fun x : ℝ ↦ x * Real.exp (-x)) (d * t) := by
    intro t
    simp only
    ring
  have hcomp : ∫ t in Ioi (0 : ℝ), (fun x : ℝ ↦ x * Real.exp (-x)) (d * t)
      = d⁻¹ • ∫ x in Ioi (d * (0 : ℝ)), x * Real.exp (-x) :=
    integral_comp_mul_left_Ioi (fun x : ℝ ↦ x * Real.exp (-x)) 0 hd
  calc ∫ t in Ioi (0 : ℝ), t * (d * Real.exp (-(d * t)))
      = ∫ t in Ioi (0 : ℝ), (fun x : ℝ ↦ x * Real.exp (-x)) (d * t) := by
        exact setIntegral_congr_fun measurableSet_Ioi fun t _ ↦ hpt t
    _ = d⁻¹ • ∫ x in Ioi (d * (0 : ℝ)), x * Real.exp (-x) := hcomp
    _ = 1 / d := by
        rw [mul_zero, integral_id_mul_exp_neg, smul_eq_mul, mul_one, one_div]

/-- **The mean sojourn at `k` blocks is the summand of `meanTransitTime`.**  With this, the
chain `E(T_n) = Σ_r d_r⁻¹ = 2 - 2/n` of `Descent.Coalescent.Rates` runs from K-C (1.7)'s
density rather than from a cited mean, and `Rates.meanTransitTime_eq_two_sub` becomes a
statement about the mechanism. -/
theorem integral_id_mul_holdDensity_deathRate {k : ℕ} (hk : 2 ≤ k) :
    ∫ t in Ioi (0 : ℝ), t * (deathRate k * Real.exp (-(deathRate k * t)))
      = 1 / deathRate k :=
  integral_id_mul_holdDensity (deathRate_pos hk)

/-- **Kingman's clock, at the rate a `k`-block state carries.**  K-C (1.7)'s `d_k` is
`Descent.Coalescent.Rates.deathRate`, which `Descent.Coalescent.StateSpace.card_covers`
identifies as the number of covers -- so the clock's rate is the number of pairs of lineages
that could merge, which is the whole content of the coalescent's timing. -/
noncomputable def blockHoldMeasure (k : ℕ) : Measure ℝ := holdMeasure (deathRate k)

instance blockHoldMeasure_isProbabilityMeasure {k : ℕ} (hk : 2 ≤ k) :
    IsProbabilityMeasure (blockHoldMeasure k) :=
  holdMeasure_isProbabilityMeasure (deathRate_pos hk)

/-- **K-G section 6's temporal coupling at finite `n`, with nothing left as a parameter.**
The jump chain of `Descent.Coalescent.Trajectory`, coupled to independent copies of
Kingman's own clock.  Independence is arranged, as it is in K-C Theorem 3 -- see
`Descent.Coalescent.Law` for why that is the honest description and what it does not
settle.

Empirical status: NOT AN EMPIRICAL CLAIM.  It is a coupling: `Descent.Coalescent.Trajectory`'s
jump chain paired with independent copies of `blockHoldMeasure`.  Constructing a joint law
whose marginals are two given objects asserts nothing about a population -- what it asserts
is about the two objects, and `Descent.Coalescent.Law` states exactly what the independence
does and does not settle. -/
noncomputable def coalescentLawExp (n k m : ℕ) (rate : ℕ) :
    Measure (List (ER n) × (Fin m → ℝ)) :=
  coalescentLaw n k m (blockHoldMeasure rate)

/-- **The exponential holding-time law is the general law at an exponential block hold.**

`coalescentLawExp` is `coalescentLaw` with one argument fixed, so it inherits everything
the general law states and asserts nothing further. Recorded because the docstring above
is careful that a product measure asserts something about its two marginals and not about
a population -- and a definition with no theorem about it cannot be held to even that. -/
theorem coalescentLawExp_eq (n k m : ℕ) (rate : ℕ) :
    coalescentLawExp n k m rate = coalescentLaw n k m (blockHoldMeasure rate) := rfl

end Coalescent

end Descent
