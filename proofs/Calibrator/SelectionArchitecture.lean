/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Calibrator.AncestrySpecificPower
import Calibrator.OpenQuestions
import Calibrator.PortabilityDrift
import Calibrator.Probability

namespace Calibrator

open MeasureTheory

/-!
# Selection Pressure, Trait Architecture, and Portability

This file formalizes how different modes of natural selection shape
trait genetic architecture and consequently affect PGS portability.
The key insight from Wang et al. is that trait-specific portability
patterns are explained by selection regime differences.

Key results:
1. Stabilizing selection maintains genetic architecture → better portability
2. Diversifying/balancing selection changes architecture → worse portability
3. Polygenic adaptation creates coordinated allele frequency shifts
4. Rapidly varying selection regimes have fastest portability decay
5. Relationship between GWAS effect sizes and selection coefficients

Reference: Wang et al. (2026), Nature Communications 17:942.
-/


/-!
## Stabilizing Selection and Architecture Conservation

Under stabilizing selection, the trait optimum is the same across
populations. Selection maintains effects near the optimum, so genetic
architecture is conserved → good portability.
-/

section StabilizingSelection

/-- **Stabilizing selection constraint on effect sizes.**
    Under stabilizing selection with strength s and optimum μ,
    large-effect alleles are rare because they're selected against.
    The equilibrium effect size distribution has variance ∝ 1/s.

    Empirical status: **VALIDATED**
    (`proofs/validation/empirical/simcov/battery_bulk3.py`,
    `test_effect_variance_recurrence`). It is the fixed point of
    `effectVarianceRecurrence`, and iterating that recurrence 200000 times from
    `V = 5.0` -- far above every equilibrium in the design -- reproduces it to
    every digit carried: 0.20000, 0.10000 and 0.50000 at `(v_mut, s)` of
    (0.010, 0.05), (0.020, 0.20) and (0.005, 0.01).

    Power: the prediction spans 0.10000 to 0.50000 across the design. -/
noncomputable def equilibriumEffectVariance (v_mutation s : ℝ) : ℝ :=
  v_mutation / s

/-- **equilibriumEffectVariance at zero s, named.** Without selection there is no equilibrium:
mutational input accumulates without bound. Lean returns `0`, reporting no standing variance where
the truth is unbounded standing variance. Consumers must require `s ≠ 0`. -/
theorem equilibriumEffectVariance_zero_s_is_junk (v_mutation : ℝ) :
    equilibriumEffectVariance v_mutation 0 = 0 := by
  unfold equilibriumEffectVariance
  simp

/-- **Selection removes exactly the standing variance it is charged with.**

Multiplying the equilibrium by the selection strength returns the per-generation mutational input,
which is what balance means: what selection takes each generation equals what mutation supplies.
The recurrence below is a fixed-point statement and is satisfied by the equilibrium of any body of
the form `c · v_mutation / s`, whatever `c` is, because the same `c` appears on both sides. This
identity fixes it at one. -/
theorem equilibriumEffectVariance_mul_selection (v_mutation s : ℝ) (h : s ≠ 0) :
    equilibriumEffectVariance v_mutation s * s = v_mutation := by
  unfold equilibriumEffectVariance
  field_simp

/-- The algebraic equilibrium vanishes exactly when mutational input or selection strength
vanishes. The `s = 0` branch is the named junk boundary above, not a biological equilibrium. -/
theorem equilibriumEffectVariance_eq_zero_iff (v_mutation s : ℝ) :
    equilibriumEffectVariance v_mutation s = 0 ↔ v_mutation = 0 ∨ s = 0 := by
  unfold equilibriumEffectVariance
  constructor
  · intro h
    by_cases h_s : s = 0
    · exact Or.inr h_s
    · left
      calc
        v_mutation = v_mutation / s * s := (div_mul_cancel₀ v_mutation h_s).symm
        _ = 0 := by rw [h]; norm_num
  · rintro (rfl | rfl) <;> norm_num

/-- **Mutation-selection balance recurrence.**
    Each generation, new mutational variance v_mut is added and selection
    of strength s removes a fraction s of the standing variance V.
    The recurrence is: V(t+1) = (1 - s) × V(t) + v_mut.

    Empirical status: **NOT TESTED BY THE DESIGN THAT LOOKED LIKE IT WAS**
    (`proofs/validation/empirical/simcov/battery_bulk9.py`). The oracle was one
    step of this same recurrence applied to a state fifty iterations in, which is
    this expression evaluated twice; the harness returns SELF-TEST. What would
    test it is a simulated population under stabilising selection and recurrent
    mutation, with the realised effect variance measured from generation to
    generation. -/
noncomputable def effectVarianceRecurrence (V v_mut s : ℝ) : ℝ :=
  (1 - s) * V + v_mut

/-- **The equilibrium variance is the unique fixed point of the recurrence.**
    Solving V* = (1 - s) × V* + v_mut gives V* = v_mut / s.
    The reverse implication rules out every other alleged balance point. -/
theorem effectVarianceRecurrence_eq_self_iff
    (V v_mut s : ℝ) (hs : s ≠ 0) :
    effectVarianceRecurrence V v_mut s = V ↔ V = equilibriumEffectVariance v_mut s := by
  unfold effectVarianceRecurrence equilibriumEffectVariance
  rw [eq_div_iff hs]
  constructor <;> intro h <;> nlinarith

/-- Stronger stabilizing selection → smaller effect sizes. -/
theorem equilibriumEffectVariance_lt_of_selection_lt
    (v_mutation s₁ s₂ : ℝ)
    (h_vm : 0 < v_mutation)
    (h_s₁ : 0 < s₁)
    (h_stronger : s₁ < s₂) :
    equilibriumEffectVariance v_mutation s₂ < equilibriumEffectVariance v_mutation s₁ := by
  unfold equilibriumEffectVariance
  exact div_lt_div_of_pos_left h_vm h_s₁ h_stronger

/-- **Effect correlation under stabilizing selection.**
    When both populations are under the same stabilizing selection,
    effect sizes are pulled toward the same optimum.
    ρ(effects) ≈ 1 - O(1/2Ns) where Ns is selection × drift balance.

    Empirical status: UNTESTED. -/
noncomputable def effectCorrelationStabilizing (Ns : ℝ) : ℝ :=
  1 - 1 / (2 * Ns)

/-- **The stabilizing effect correlation at zero selection, named.** With `Ns = 0` the effect
sizes are governed by drift alone and the cross-population correlation decays to zero. Lean
returns `1`: PERFECTLY preserved effects, the strongest portability claim the corpus can make,
produced exactly where portability is weakest. Its inverse map
`stabilizingNsFromObservedCorrelation` is junk at the same value from the other side. Consumers
must require `Ns ≠ 0`. -/
theorem effectCorrelationStabilizing_zero_selection_is_junk :
    effectCorrelationStabilizing 0 = 1 := by
  unfold effectCorrelationStabilizing
  simp

/-- Effect correlation increases with stronger selection (relative to drift). -/
theorem effectCorrelationStabilizing_lt_of_Ns_lt
    (Ns₁ Ns₂ : ℝ)
    (h₁ : 0 < Ns₁) (h_more : Ns₁ < Ns₂) :
    effectCorrelationStabilizing Ns₁ < effectCorrelationStabilizing Ns₂ := by
  unfold effectCorrelationStabilizing
  rw [sub_lt_sub_iff_left]
  exact div_lt_div_of_pos_left one_pos (by linarith) (by linarith)

/-- Per-locus contribution obtained by spreading a positive architecture-scale variance
equally over `locusCount` causal loci. -/
noncomputable def polygenicAveragingVariance (architectureVariance : ℝ)
    (locusCount : ℕ) : ℝ :=
  architectureVariance / locusCount

/-- The polygenic averaging scale is pinned at four equal loci. -/
theorem polygenicAveragingVariance_at_reference_point :
    polygenicAveragingVariance 1 4 = 1 / 4 := by
  norm_num [polygenicAveragingVariance]

/-- A positive architecture variance contributes strictly less per locus when spread over
strictly more nonzero causal loci. -/
theorem polygenicAveragingVariance_lt_of_locusCount_lt
    (m₁ m₂ : ℕ) (architectureVariance : ℝ)
    (h_m₁ : 0 < m₁) (h_more : m₁ < m₂)
    (h_var : 0 < architectureVariance) :
    polygenicAveragingVariance architectureVariance m₂ <
      polygenicAveragingVariance architectureVariance m₁ :=
  div_lt_div_of_pos_left h_var (Nat.cast_pos.mpr h_m₁) (Nat.cast_lt.mpr h_more)

/-- Equal per-locus heritability when total heritability is spread over a specified count. -/
noncomputable def equalPerLocusHeritability (locusCount : ℕ) (totalHeritability : ℝ) : ℝ :=
  totalHeritability / locusCount

/-- **Highly polygenic architecture: total heritability sums from small effects.**
    With M causal loci each contributing h²/M, the total heritability
    is recovered as M × (h²/M) = h². -/
theorem equalPerLocusHeritability_sum (locusCount : ℕ) (totalHeritability : ℝ)
    (h_count : 0 < locusCount) :
    (locusCount : ℝ) * equalPerLocusHeritability locusCount totalHeritability =
      totalHeritability := by
  unfold equalPerLocusHeritability
  exact mul_div_cancel₀ totalHeritability (Nat.cast_ne_zero.mpr (ne_of_gt h_count))

end StabilizingSelection


/-!
## Diversifying and Fluctuating Selection

Under diversifying selection, the trait optimum differs across populations.
Effects that are beneficial in one population may be neutral or deleterious
in another → allelic turnover → poor portability.
-/

section DiversifyingSelection

/-- **Fluctuating selection accelerates effect turnover.**
    Under fluctuating selection with autocorrelation time τ,
    the effect correlation decays as ρ(t) = exp(-t/τ).

    This models the selection environment as an Ornstein-Uhlenbeck (OU) process:
    the fitness optimum θ(t) satisfies dθ = -θ/τ dt + σ dW, where τ is the
    relaxation time and W is a Wiener process. The autocorrelation function of
    an OU process is Cov(θ(t), θ(t+Δ)) = (σ²τ/2) exp(-Δ/τ), which after
    normalization gives the correlation exp(-Δ/τ). The parameter τ controls
    how quickly the selective landscape decorrelates: small τ means rapid
    turnover, while τ → ∞ recovers stabilizing selection with a fixed
    optimum.

    Empirical status: **VALIDATED**
    (`proofs/validation/empirical/simcov/battery_bulk9.py`,
    `test_ou_effect_correlation`). Lag-`t` autocorrelation of a stationary
    Ornstein-Uhlenbeck process across 20000 independent replicates, with `tau`
    and `t` varied separately:

      tau    t     this def   measured             sems
       5     10     0.13534   0.13220±0.00695      0.45
       5     40     0.00034   0.00607±0.00707      0.81
      20     10     0.60653   0.60511±0.00448      0.32
      20     40     0.13534   0.13904±0.00693      0.53
      60     10     0.84648   0.85097±0.00195      2.30
      60     40     0.51342   0.51808±0.00517      0.90

    The autocorrelation is produced by the process, not by the formula.

    Power: the prediction spans 0.00034 to 0.84648, and the two cells that share
    a predicted 0.13534 at different `(tau, t)` check that only the ratio
    matters. -/
noncomputable def fluctuatingEffectCorrelation (t τ : ℝ) : ℝ :=
  Real.exp (-t / τ)

/-- **fluctuatingEffectCorrelation at its junk point, named.** A zero autocorrelation time means
effects decorrelate instantly, so the correlation should be zero at any positive separation. The
divisor is zero, the exponent is junk-zero, and `exp 0 = 1`: PERFECTLY preserved effects. This
is the forward map's version of the inversion `tauFromObservedEffectCorrelation_perfect_is_junk`
records on the way back. Consumers must exclude the argument that makes the guard vanish. -/
theorem fluctuatingEffectCorrelation_zero_autocorrelation_is_junk (t : ℝ) :
    fluctuatingEffectCorrelation t 0 = 1 := by
  unfold fluctuatingEffectCorrelation
  simp

/-- **Effects are perfectly correlated at zero divergence.**

The decay theorem below is satisfied by every decreasing function of `t`, so it fixes the
direction and leaves both the scale and the starting value free. At zero divergence time two
populations have not diverged and the correlation must be exactly one; a body carrying a leading
factor, or an offset, would still decay and would fail here. It is also the normalisation that
makes `τ` a time constant rather than an arbitrary rate parameter. -/
theorem fluctuatingEffectCorrelation_at_zero (τ : ℝ) :
    fluctuatingEffectCorrelation 0 τ = 1 := by
  unfold fluctuatingEffectCorrelation
  norm_num

/-- Effect correlation decays with divergence time. -/
theorem fluctuating_correlation_decays
    (t₁ t₂ τ : ℝ)
    (h_τ : 0 < τ) (h_more : t₁ < t₂) :
    fluctuatingEffectCorrelation t₂ τ < fluctuatingEffectCorrelation t₁ τ := by
  unfold fluctuatingEffectCorrelation
  apply Real.exp_lt_exp.mpr
  rw [neg_div, neg_div, neg_lt_neg_iff]
  exact div_lt_div_of_pos_right h_more h_τ

/-- Shorter autocorrelation time → faster decay. -/
theorem shorter_autocorrelation_faster_decay
    (t τ₁ τ₂ : ℝ)
    (h_τ₂ : 0 < τ₂)
    (h_shorter : τ₂ < τ₁)
    (h_t : 0 < t) :
    fluctuatingEffectCorrelation t τ₂ < fluctuatingEffectCorrelation t τ₁ := by
  unfold fluctuatingEffectCorrelation
  apply Real.exp_lt_exp.mpr
  rw [neg_div, neg_div, neg_lt_neg_iff]
  exact div_lt_div_of_pos_left h_t (by linarith) h_shorter

/-- **Shorter autocorrelation times imply lower cross-population effect
    correlation.** -/
theorem short_autocorrelation_lower_correlation
    (τ_short τ_long t : ℝ)
    (h_short : 0 < τ_short)
    (h_shorter : τ_short < τ_long)
    (h_t : 0 < t) :
    fluctuatingEffectCorrelation t τ_short < fluctuatingEffectCorrelation t τ_long :=
  shorter_autocorrelation_faster_decay t τ_long τ_short h_short h_shorter h_t

/-- Selected-architecture variance under stabilizing selection. -/
noncomputable def stabilizingSelectedArchitectureVariance (v_mutation s : ℝ) : ℝ :=
  equilibriumEffectVariance v_mutation s

/-- Reference evaluation.  The value is computed through the definitions this body calls, but
the theorem states a number: an inequality or an invariance leaves a family of bodies
satisfying it, and a value does not. -/
theorem stabilizingSelectedArchitectureVariance_at_reference_point :
    stabilizingSelectedArchitectureVariance 1 1 = 1 := by
  norm_num [stabilizingSelectedArchitectureVariance, equilibriumEffectVariance]



/-- Stationary variance of a fluctuating optimum under the OU model. -/
noncomputable def optimumOUVariance (sigmaTheta tau : ℝ) : ℝ :=
  sigmaTheta ^ 2 * tau / 2

/-- **optimumOUVariance pinned at a reference point.** No theorem in the corpus evaluated this
definition, so every body agreeing with it in sign and monotonicity was indistinguishable from
it. At all arguments equal to `1 / 2` it is `1 / 16`, which fixes the coefficients a one-sided
bound or an invariance leaves free. -/
theorem optimumOUVariance_at_reference_point :
    optimumOUVariance (1 / 2) (1 / 2) = 1 / 16 := by
  unfold optimumOUVariance
  norm_num

/-- **The stationary optimum variance is quadratic in the driving amplitude.**
Halving the amplitude quarters the variance. -/
theorem optimumOUVariance_amplitude_scaling (sigmaTheta tau c : ℝ) :
    optimumOUVariance (c * sigmaTheta) tau = c ^ 2 * optimumOUVariance sigmaTheta tau := by
  unfold optimumOUVariance
  ring

/-- **The stationary optimum variance is linear in autocorrelation time.**
Halving the correlation time halves the variance. -/
theorem optimumOUVariance_time_scaling (sigmaTheta tau c : ℝ) :
    optimumOUVariance sigmaTheta (c * tau) = c * optimumOUVariance sigmaTheta tau := by
  unfold optimumOUVariance
  ring

/-- Selected-architecture variance under fluctuating selection: the baseline
    mutation-selection variance plus the variance induced by a moving optimum. -/
noncomputable def fluctuatingSelectedArchitectureVariance
    (v_mutation s sigmaTheta tau : ℝ) : ℝ :=
  equilibriumEffectVariance v_mutation s + optimumOUVariance sigmaTheta tau

/-- Reference evaluation.  The value is computed through the definitions this body calls, but
the theorem states a number: an inequality or an invariance leaves a family of bodies
satisfying it, and a value does not. -/
theorem fluctuatingSelectedArchitectureVariance_at_reference_point :
    fluctuatingSelectedArchitectureVariance 1 1 1 1 = 3 / 2 := by
  norm_num [fluctuatingSelectedArchitectureVariance, equilibriumEffectVariance, optimumOUVariance]


theorem effectCorrelationStabilizing_pos_iff
    (Ns : ℝ) (hNs : 0 < Ns) :
    0 < effectCorrelationStabilizing Ns ↔ 1 / 2 < Ns := by
  unfold effectCorrelationStabilizing
  have hden_pos : 0 < 2 * Ns := by linarith
  rw [sub_pos, div_lt_one hden_pos]
  constructor <;> intro h <;> linarith

theorem effectCorrelationStabilizing_lt_one_iff (Ns : ℝ) :
    effectCorrelationStabilizing Ns < 1 ↔ 0 < Ns := by
  unfold effectCorrelationStabilizing
  rw [sub_lt_self_iff, one_div_pos]
  constructor <;> intro h <;> nlinarith

theorem fluctuatingSelectedArchitectureVariance_gt_stabilizing
    (v_mutation s sigmaTheta tau : ℝ)
    (h_sigma : 0 < sigmaTheta) (h_tau : 0 < tau) :
    stabilizingSelectedArchitectureVariance v_mutation s <
      fluctuatingSelectedArchitectureVariance v_mutation s sigmaTheta tau := by
  unfold stabilizingSelectedArchitectureVariance
    fluctuatingSelectedArchitectureVariance optimumOUVariance
    equilibriumEffectVariance
  have h_extra : 0 < sigmaTheta ^ 2 * tau / 2 := by
    have hsq : 0 < sigmaTheta ^ 2 := sq_pos_of_pos h_sigma
    nlinarith
  linarith

/-- The fluctuating correlation drops below the stabilizing correlation once the
    fluctuating autocorrelation time is below the exact threshold obtained by
    matching `exp(-t/τ)` to `1 - 1/(2Ns)`. -/
theorem fluctuatingCorrelation_lt_stabilizing_of_tau_lt_threshold
    (t tau Ns : ℝ)
    (h_tau : 0 < tau) (hNs : 1 / 2 < Ns)
    (h_tau_lt : tau < t / (-Real.log (effectCorrelationStabilizing Ns))) :
    fluctuatingEffectCorrelation t tau < effectCorrelationStabilizing Ns := by
  have h_rho_pos : 0 < effectCorrelationStabilizing Ns :=
    (effectCorrelationStabilizing_pos_iff Ns (by linarith)).2 hNs
  have h_rho_lt_one : effectCorrelationStabilizing Ns < 1 :=
    (effectCorrelationStabilizing_lt_one_iff Ns).2 (by linarith)
  have h_log_neg : Real.log (effectCorrelationStabilizing Ns) < 0 := by
    have h_log_lt : Real.log (effectCorrelationStabilizing Ns) < Real.log 1 :=
      Real.log_lt_log h_rho_pos h_rho_lt_one
    simpa using h_log_lt
  have h_neglog_pos : 0 < -Real.log (effectCorrelationStabilizing Ns) := by
    linarith
  have h_mul_lt : tau * (-Real.log (effectCorrelationStabilizing Ns)) < t :=
    (lt_div_iff₀ h_neglog_pos).mp h_tau_lt
  have h_neglog_lt_div : -Real.log (effectCorrelationStabilizing Ns) < t / tau :=
    (lt_div_iff₀ h_tau).2 (by simpa [mul_comm] using h_mul_lt)
  have h_exp_lt_log' : -(t / tau) < Real.log (effectCorrelationStabilizing Ns) := by
    linarith
  have h_exp_lt_log : -t / tau < Real.log (effectCorrelationStabilizing Ns) := by
    simpa [neg_div] using h_exp_lt_log'
  unfold fluctuatingEffectCorrelation
  have h_exp_lt := Real.exp_lt_exp.mpr h_exp_lt_log
  simpa [Real.exp_log h_rho_pos] using h_exp_lt

/-- Recover the stabilizing `Ns` parameter from an observed cross-population
    effect correlation.

    Empirical status: UNTESTED. -/
noncomputable def stabilizingNsFromObservedCorrelation (rho : ℝ) : ℝ :=
  1 / (2 * (1 - rho))

/-- **The recovered selection strength's junk branch, named.** At a perfectly preserved
correlation the implied `Ns` diverges and Lean returns `0`, reporting no selection where the
data imply unbounded selection. Consumers must require `rho ≠ 1`. -/
theorem stabilizingNsFromObservedCorrelation_perfect_is_junk :
    stabilizingNsFromObservedCorrelation 1 = 0 := by
  unfold stabilizingNsFromObservedCorrelation; norm_num

/-- Below perfect correlation, the recovered stabilizing-selection scale lies in the
positive-correlation regime `Ns > 1/2` exactly when the observation itself is positive. -/
theorem stabilizingNsFromObservedCorrelation_gt_half_iff
    (rho : ℝ) (h_rho_lt : rho < 1) :
    1 / 2 < stabilizingNsFromObservedCorrelation rho ↔ 0 < rho := by
  unfold stabilizingNsFromObservedCorrelation
  have h_denom : 0 < 2 * (1 - rho) := by linarith
  rw [div_lt_div_iff₀ (by norm_num : (0 : ℝ) < 2) h_denom]
  constructor <;> intro h <;> nlinarith

/-- The inverse map for the stabilizing effect-correlation formula is exact on
    the biologically relevant region `ρ < 1`. -/
theorem effectCorrelationStabilizing_eq_observedCorrelation_of_recoveredNs
    (rho : ℝ) (h_rho_lt : rho < 1) :
    effectCorrelationStabilizing (stabilizingNsFromObservedCorrelation rho) = rho := by
  unfold effectCorrelationStabilizing stabilizingNsFromObservedCorrelation
  have h_one_minus_ne : 1 - rho ≠ 0 := by linarith
  field_simp [h_one_minus_ne]
  ring

/-- Recover the fluctuating-selection autocorrelation time `τ` from an observed
    cross-population effect correlation measured at divergence time `t`.

    Empirical status: **VALIDATED where `rho` is measurable, and
    ILL-CONDITIONED as `rho` approaches zero
    (`proofs/validation/empirical/simcov/battery_bulk9.py`,
    `test_ou_effect_correlation`). Recovering `tau` from the measured
    autocorrelation of an Ornstein-Uhlenbeck process built with a known `tau`:

      tau    t     recovered   built with   sems
       5     10      4.94210     5.00000     0.39
      20     10     19.90689    20.00000     0.16
      20     40     20.27384    20.00000     0.46
      60     10     61.96429    60.00000     1.09
      60     40     60.82545    60.00000     0.46
       5     40      7.83521     5.00000    18.90

    The last row is the regime, not a defect. At `tau = 5` and `t = 40` the true
    correlation is `exp(-8) = 0.00034`, and the measurement returns
    `0.00607 ± 0.00707` -- consistent with zero. Taking a logarithm of a
    quantity indistinguishable from zero amplifies its error without bound, so
    `-t / log(rho)` inherits that: a 0.006 measurement gives 7.8 where the truth
    is 5. The inverse is usable only while `rho` is separated from zero by more
    than its own error bar, which the first five rows satisfy and the sixth does
    not. -/
noncomputable def tauFromObservedEffectCorrelation (t rho : ℝ) : ℝ :=
  -t / Real.log rho

/-- **The recovered autocorrelation time's junk branch, named.** At `rho = 1` the logarithm is
zero and Lean returns `0`, reporting instantaneous decorrelation where a perfectly preserved
correlation implies an infinite autocorrelation time — the reverse of the truth. `Real.log` is
also junk at `rho ≤ 0`. Consumers must require `0 < rho` and `rho ≠ 1`. -/
theorem tauFromObservedEffectCorrelation_perfect_is_junk (t : ℝ) :
    tauFromObservedEffectCorrelation t 1 = 0 := by
  unfold tauFromObservedEffectCorrelation; simp

/-- The recovered OU autocorrelation time is positive for a genuine observed
    effect correlation in `(0, 1)`. -/
theorem tauFromObservedEffectCorrelation_pos
    (t rho : ℝ)
    (h_t : 0 < t) (h_rho : 0 < rho) (h_rho_lt : rho < 1) :
    0 < tauFromObservedEffectCorrelation t rho := by
  have h_log_neg : Real.log rho < 0 := by
    have h_log_lt : Real.log rho < Real.log 1 :=
      Real.log_lt_log h_rho h_rho_lt
    simpa using h_log_lt
  unfold tauFromObservedEffectCorrelation
  exact div_pos_of_neg_of_neg (by linarith) h_log_neg

/-- **The recovered autocorrelation time's scale, pinned.** The junk-branch and positivity
theorems fix where the recovery breaks and its sign, and both hold for `-2 * t / log ρ`. At the
observed correlation `exp (-1)` the divergence time has fallen by exactly one autocorrelation
time, so the recovered `τ` equals `t` — which fixes the constant. -/
theorem tauFromObservedEffectCorrelation_at_one_efold (t : ℝ) :
    tauFromObservedEffectCorrelation t (Real.exp (-1)) = t := by
  unfold tauFromObservedEffectCorrelation
  rw [Real.log_exp]
  norm_num

/-- The inverse map for the fluctuating-selection effect-correlation formula is
    exact on the biologically relevant region `ρ ∈ (0, 1)`. -/
theorem fluctuatingEffectCorrelation_eq_observedCorrelation_of_recoveredTau
    (t rho : ℝ)
    (h_t : 0 < t) (h_rho : 0 < rho) (h_rho_lt : rho < 1) :
    fluctuatingEffectCorrelation t (tauFromObservedEffectCorrelation t rho) = rho := by
  have h_t_ne : t ≠ 0 := ne_of_gt h_t
  have h_log_neg : Real.log rho < 0 := by
    have h_log_lt : Real.log rho < Real.log 1 :=
      Real.log_lt_log h_rho h_rho_lt
    simpa using h_log_lt
  have h_log_ne : Real.log rho ≠ 0 := ne_of_lt h_log_neg
  unfold fluctuatingEffectCorrelation tauFromObservedEffectCorrelation
  have h_ratio : -t / (-t / Real.log rho) = Real.log rho := by
    field_simp [h_t_ne, h_log_ne]
  rw [h_ratio, Real.exp_log h_rho]

/-- Recover the fluctuating-selection optimum-diffusion scale `σ_θ` from an
    observed selected-architecture variance once the fluctuation time scale has
    been recovered from the effect correlation.

    Empirical status: UNTESTED. -/
noncomputable def sigmaThetaFromObservedSelectedVariance
    (v_selected v_mutation s t rho : ℝ) : ℝ :=
  Real.sqrt
    (2 * (v_selected - stabilizingSelectedArchitectureVariance v_mutation s) /
      tauFromObservedEffectCorrelation t rho)

/-- A nonpositive radicand sends `Real.sqrt` to Mathlib's junk `0`, so an observed variance
below the mutation-selection floor reports zero effect-size scale rather than an inconsistent
model.  Zero scale is a value the architecture can also take, so it cannot be read as a flag. -/
theorem sigmaThetaFromObservedSelectedVariance_at_nonpositive_radicand_is_junk
    (v_selected v_mutation s t rho : ℝ)
    (hnonpos : 2 * (v_selected - stabilizingSelectedArchitectureVariance v_mutation s) /
      tauFromObservedEffectCorrelation t rho ≤ 0) :
    sigmaThetaFromObservedSelectedVariance v_selected v_mutation s t rho = 0 := by
  unfold sigmaThetaFromObservedSelectedVariance
  exact Real.sqrt_eq_zero_of_nonpos hnonpos


/-- The recovered optimum-diffusion scale is positive whenever the observed
    selected-architecture variance strictly exceeds the stabilizing baseline. -/
theorem sigmaThetaFromObservedSelectedVariance_pos
    (v_selected v_mutation s t rho : ℝ)
    (h_t : 0 < t) (h_rho : 0 < rho) (h_rho_lt : rho < 1)
    (h_var_gap : stabilizingSelectedArchitectureVariance v_mutation s < v_selected) :
    0 < sigmaThetaFromObservedSelectedVariance v_selected v_mutation s t rho := by
  have h_tau_pos : 0 < tauFromObservedEffectCorrelation t rho :=
    tauFromObservedEffectCorrelation_pos t rho h_t h_rho h_rho_lt
  unfold sigmaThetaFromObservedSelectedVariance
  apply Real.sqrt_pos.mpr
  apply div_pos
  · nlinarith
  · exact h_tau_pos

/-- The inverse map for the fluctuating selected-architecture variance is exact
    once the observed effect correlation and observed selected variance are
    plugged into the recovered OU parameters. -/
theorem fluctuatingSelectedArchitectureVariance_eq_observed_of_recoveredSigmaTheta
    (v_selected v_mutation s t rho : ℝ)
    (h_t : 0 < t) (h_rho : 0 < rho) (h_rho_lt : rho < 1)
    (h_var_gap : stabilizingSelectedArchitectureVariance v_mutation s < v_selected) :
    fluctuatingSelectedArchitectureVariance v_mutation s
        (sigmaThetaFromObservedSelectedVariance v_selected v_mutation s t rho)
        (tauFromObservedEffectCorrelation t rho) =
      v_selected := by
  have h_tau_pos : 0 < tauFromObservedEffectCorrelation t rho :=
    tauFromObservedEffectCorrelation_pos t rho h_t h_rho h_rho_lt
  have h_arg_nonneg :
      0 ≤
        2 * (v_selected - stabilizingSelectedArchitectureVariance v_mutation s) /
          tauFromObservedEffectCorrelation t rho := by
    apply div_nonneg
    · nlinarith
    · exact le_of_lt h_tau_pos
  unfold fluctuatingSelectedArchitectureVariance optimumOUVariance
    sigmaThetaFromObservedSelectedVariance
  rw [Real.sq_sqrt h_arg_nonneg]
  field_simp [ne_of_gt h_tau_pos]
  unfold stabilizingSelectedArchitectureVariance
  ring_nf

/-- **Observed summary statistics identify a fluctuating regime and exclude all
    stabilizing regimes.**

    If an observed trait-level summary exhibits:
    1. a cross-population effect correlation `ρ_obs` strictly between `0` and `1`,
       and
    2. a selected-architecture variance strictly above the stabilizing
       mutation-selection baseline,

    then there is an exact fluctuating-selection regime matching both observed
    summaries, obtained by recovering `τ` from `ρ_obs` and `σ_θ` from the
    selected-variance excess. At the same time, no stabilizing regime can match
    the same joint summary, because under stabilizing selection the selected
    variance is fixed at the baseline `v_mutation / s` independently of `Ns`. -/
theorem observedSummary_identifies_fluctuating_not_stabilizing
    (v_mutation s t rho_obs v_selected_obs : ℝ)
    (h_t : 0 < t)
    (h_rho : 0 < rho_obs) (h_rho_lt : rho_obs < 1)
    (h_var_gap : stabilizingSelectedArchitectureVariance v_mutation s < v_selected_obs) :
    let tau_hat := tauFromObservedEffectCorrelation t rho_obs
    let sigma_hat :=
      sigmaThetaFromObservedSelectedVariance v_selected_obs v_mutation s t rho_obs
    (0 < tau_hat ∧
      0 < sigma_hat ∧
      fluctuatingEffectCorrelation t tau_hat = rho_obs ∧
      fluctuatingSelectedArchitectureVariance v_mutation s sigma_hat tau_hat =
        v_selected_obs) ∧
    ¬ ∃ Ns,
        effectCorrelationStabilizing Ns = rho_obs ∧
          stabilizingSelectedArchitectureVariance v_mutation s = v_selected_obs := by
  dsimp
  have h_tau_pos : 0 < tauFromObservedEffectCorrelation t rho_obs :=
    tauFromObservedEffectCorrelation_pos t rho_obs h_t h_rho h_rho_lt
  have h_sigma_pos :
      0 <
        sigmaThetaFromObservedSelectedVariance
          v_selected_obs v_mutation s t rho_obs :=
    sigmaThetaFromObservedSelectedVariance_pos
      v_selected_obs v_mutation s t rho_obs h_t h_rho h_rho_lt h_var_gap
  constructor
  · exact ⟨h_tau_pos, h_sigma_pos,
      fluctuatingEffectCorrelation_eq_observedCorrelation_of_recoveredTau
        t rho_obs h_t h_rho h_rho_lt,
      fluctuatingSelectedArchitectureVariance_eq_observed_of_recoveredSigmaTheta
        v_selected_obs v_mutation s t rho_obs h_t h_rho h_rho_lt h_var_gap⟩
  · intro h_stab
    rcases h_stab with ⟨Ns, _, h_var_eq⟩
    linarith

/-- **Balancing selection maintains intermediate allele frequencies.**
    Under balancing selection (e.g., heterozygote advantage in HLA),
    allele frequencies are maintained near 0.5 → high heterozygosity.
    This increases PGS variance even as accuracy drops. -/
theorem two_mul_one_sub_lt_of_lt_of_lt_half
    (p_neutral p_balanced lo hi : ℝ)
    (h_neutral_low : p_neutral < lo)
    (h_balanced : hi < p_balanced) (h_balanced_lt : p_balanced < 1/2)
    (h_lo_le_hi : lo ≤ hi) :
    2 * p_neutral * (1 - p_neutral) < 2 * p_balanced * (1 - p_balanced) :=
  two_mul_one_sub_strictMono_le_half p_neutral p_balanced
    (by linarith) (le_of_lt h_balanced_lt)

end DiversifyingSelection


/-!
## Polygenic Adaptation

Polygenic adaptation occurs when many alleles of small effect shift
in frequency in a coordinated direction. This creates a mean shift
in PGS without changing individual-variant effects.
-/

section PolygenicAdaptation

/-- **Polygenic adaptation score shift.**
    Under polygenic adaptation, the mean PGS shifts by
    Δμ = Σᵢ βᵢ · 2 · Δpᵢ where Δpᵢ are coordinated frequency changes. The `2` is
    `Conventions.ploidy`, written as a literal only because importing
    `Conventions` here closes an import cycle;
    `ScoreDistribution.pgsMeanShift` carries the same factor.

    **The ploidy factor was missing and the body has been corrected.** The mean
    score is `Σᵢ βᵢ · ploidy · pᵢ`, because a diploid carries two copies, so its
    shift carries the same factor. Without it the definition returns exactly
    half the quantity its own docstring names.

    Measured (`proofs/validation/empirical/simcov/battery_linalg.py`,
    `test_shift_fork`) as the difference in mean score between two simulated
    diploid panels of 6000 individuals, tested both in linkage equilibrium and
    on a recombining coalescent panel:

      panel                  without ploidy   with ploidy   simulated
      linkage equilibrium           0.83286       1.66572   1.78945±0.10279
      coalescent LD                -1.83130      -3.66260  -3.66260±0.12035

    The uncorrected form sits 9.3 and 15.2 sems away and is 50 percent low in
    both; the corrected form is `ScoreDistribution.pgsMeanShift`, which matched
    the same runs to 1.2 sems. Two definitions of one quantity, and the
    simulation says which.

    Empirical status: **VALIDATED** after correction, worst 1.2 sems on the runs
    above; the superseded body **FALSIFIED** at 15.2 sems.

    Power: the measured shift spans 1.78945 to -3.66260 across the two panels,
    and the two candidate bodies differ by a factor of two everywhere. -/
noncomputable def polygenicAdaptationShift
    {m : ℕ} (β : Fin m → ℝ) (Δp : Fin m → ℝ) : ℝ :=
  ∑ i, β i * 2 * Δp i

/-- **Under neutral drift, expected shift is zero.**
    E[Δpᵢ] = 0 under drift, so E[Δμ] = 0. -/
theorem neutral_expected_shift_zero
    {m : ℕ} (β : Fin m → ℝ) :
    polygenicAdaptationShift β (fun _ ↦ 0) = 0 := by
  unfold polygenicAdaptationShift
  simp

/-- **Under selection, shift is nonzero and directional.**
    If selection favors higher trait values, Δpᵢ > 0 for positive-effect
    alleles and Δpᵢ < 0 for negative-effect alleles.
    The shift Σ βᵢ · 2 · Δpᵢ > 0. -/
theorem selected_shift_positive
    {m : ℕ} (β : Fin m → ℝ) (Δp : Fin m → ℝ)
    (h_concordant : ∀ i, 0 ≤ β i * Δp i)
    (h_exists_pos : ∃ i, 0 < β i * Δp i) :
    0 < polygenicAdaptationShift β Δp := by
  unfold polygenicAdaptationShift
  obtain ⟨i₀, hi₀⟩ := h_exists_pos
  have hterm : ∀ i, 0 ≤ β i * 2 * Δp i := by
    intro i; have := h_concordant i; nlinarith [this]
  have hpos : 0 < β i₀ * 2 * Δp i₀ := by nlinarith [hi₀]
  exact Finset.sum_pos' (fun i _ ↦ hterm i) ⟨i₀, Finset.mem_univ _, hpos⟩

/-- **Polygenic adaptation creates PGS mean shift but not R² loss.**
    The mean shift is recoverable by recalibration (intercept adjustment).

    We prove the key statistical claim: if the PGS has variance V and the
    adaptation shift μ is a constant (same for all individuals), then the
    R² of (PGS + μ) for predicting the phenotype equals R² of PGS alone.
    This is because R² = Var(predictor) × corr² / Var(outcome), and adding
    a constant does not change variance or correlation.

    Formally: for any set of n individual scores, the sample variance is
    invariant under translation by a constant shift. -/
theorem adaptation_shift_recoverable
    {n : ℕ} (scores : Fin n → ℝ) (μ_shift : ℝ) :
    let shifted := fun i ↦ scores i + μ_shift
    let mean_orig := (∑ i, scores i) / n
    let mean_shifted := (∑ i, shifted i) / n
    (∑ i, (shifted i - mean_shifted) ^ 2) =
      ∑ i, (scores i - mean_orig) ^ 2 := by
  by_cases hzero : n = 0
  · subst hzero
    simp
  simp only
  congr 1
  ext i
  have : (∑ j : Fin n, (scores j + μ_shift)) / ↑n =
    (∑ j, scores j) / ↑n + μ_shift := by
    rw [show (∑ j : Fin n, (scores j + μ_shift)) =
      (∑ j, scores j) + n * μ_shift by
      simp [Finset.sum_add_distrib]]
    have hn : (n : ℝ) ≠ 0 := by
      exact_mod_cast hzero
    field_simp [hn]
  rw [this]
  ring_nf

/- **QST-FST comparison detects polygenic adaptation.**
    Q_ST = Var(between-pop trait means) / Var(total).
    Under neutrality, Q_ST ≈ F_ST.
    Q_ST >> F_ST indicates directional selection.
    Q_ST << F_ST indicates stabilizing selection. -/
/-- **The directional QST/FST diagnostic is exact.** For positive `F_ST`, the ratio exceeds
one if and only if `Q_ST` exceeds `F_ST`; no positivity assumption on `Q_ST` is needed. -/
theorem one_lt_qst_div_fst_iff (qst fst : ℝ) (h_fst : 0 < fst) :
    1 < qst / fst ↔ fst < qst := by
  rw [lt_div_iff₀ h_fst]
  simp

/-- **The stabilizing QST/FST diagnostic is exact.** For positive `F_ST`, the ratio is below
one if and only if `Q_ST` is below `F_ST`. -/
theorem qst_div_fst_lt_one_iff (qst fst : ℝ) (h_fst : 0 < fst) :
    qst / fst < 1 ↔ qst < fst := by
  exact div_lt_one h_fst

theorem qst_fst_comparison_directional
    (qst fst : ℝ)
    (h_fst : 0 < fst)
    (h_directional : fst < qst) :
    -- Q_ST / F_ST > 1 indicates directional selection
    1 < qst / fst :=
  (one_lt_qst_div_fst_iff qst fst h_fst).2 h_directional

theorem qst_fst_comparison_stabilizing
    (qst fst : ℝ)
    (h_fst : 0 < fst)
    (h_stabilizing : qst < fst) :
    -- Q_ST / F_ST < 1 indicates stabilizing selection
    qst / fst < 1 :=
  (qst_div_fst_lt_one_iff qst fst h_fst).2 h_stabilizing

end PolygenicAdaptation


/-!
## GWAS Power and Minor Allele Frequency

The power to detect a causal variant in GWAS depends on its minor
allele frequency (MAF). MAF spectra differ across populations,
creating ascertainment-like portability effects.
-/

section GWASPowerMAF

/-- **GWAS non-centrality parameter.**
    NCP = n × β² × 2p(1-p) where n is sample size, β is effect, p is MAF.
    Larger NCP → more power to detect the variant.

    Empirical status: **VALIDATED**
    (`proofs/validation/empirical/simcov/battery_bulk3.py`,
    `test_gwas_ncp_fork`). Chi-square noncentrality measured as the mean
    realised Wald statistic minus one over 3000 replicate studies, worst 1.55
    sems over a prediction spanning 4.20000 to 8.40000.

    This is defined through the canonical `ncp` and `effectiveFisherInformation`
    declarations, so the ancestry-power and selection APIs share one implementation. -/
noncomputable def gwasNCP (n : ℕ) (β p : ℝ) : ℝ :=
  ncp (effectiveFisherInformation n p 1) β

/-- Reference evaluation.  The value is computed through the definitions this body calls, but
the theorem states a number: an inequality or an invariance leaves a family of bodies
satisfying it, and a value does not. -/
theorem gwasNCP_at_reference_point :
    gwasNCP 1 1 (1 / 2) = 1 / 2 := by
  norm_num [gwasNCP, ncp, effectiveFisherInformation, fisherInformation, genotypeVarianceHWE]


/-- GWAS non-centrality vanishes exactly for an empty study, null effect, or
monomorphic locus. -/
theorem gwasNCP_eq_zero_iff (n : ℕ) (β p : ℝ) :
    gwasNCP n β p = 0 ↔ n = 0 ∨ β = 0 ∨ p = 0 ∨ p = 1 := by
  unfold gwasNCP
  constructor
  · intro h
    rcases (ncp_eq_zero_iff _ _).1 h with h_information | h_effect
    · rcases (effectiveFisherInformation_eq_zero_iff n p 1).1 h_information with
        h_n | h_p_zero | h_p_one | h_impossible
      · exact Or.inl h_n
      · exact Or.inr (Or.inr (Or.inl h_p_zero))
      · exact Or.inr (Or.inr (Or.inr h_p_one))
      · norm_num at h_impossible
    · exact Or.inr (Or.inl h_effect)
  · rintro (h_n | h_effect | h_p_zero | h_p_one)
    · exact (ncp_eq_zero_iff _ _).2 <| Or.inl <|
        (effectiveFisherInformation_eq_zero_iff n p 1).2 (Or.inl h_n)
    · exact (ncp_eq_zero_iff _ _).2 (Or.inr h_effect)
    · exact (ncp_eq_zero_iff _ _).2 <| Or.inl <|
        (effectiveFisherInformation_eq_zero_iff n p 1).2 (Or.inr (Or.inl h_p_zero))
    · exact (ncp_eq_zero_iff _ _).2 <| Or.inl <|
        (effectiveFisherInformation_eq_zero_iff n p 1).2 (Or.inr (Or.inr (Or.inl h_p_one)))

/-- GWAS non-centrality is positive exactly for a nonempty study, nonzero effect,
and polymorphic locus. -/
theorem gwasNCP_pos_iff (n : ℕ) (β p : ℝ) :
    0 < gwasNCP n β p ↔ 0 < n ∧ β ≠ 0 ∧ 0 < p ∧ p < 1 := by
  unfold gwasNCP ncp
  constructor
  · intro h
    rcases mul_pos_iff.mp h with ⟨h_information, h_effect⟩ | ⟨_, h_effect⟩
    · rcases (fullyTaggedFisherInformation_pos_iff n p).1 h_information with ⟨h_n, hp0, hp1⟩
      refine ⟨h_n, ?_, hp0, hp1⟩
      intro h_zero
      rw [h_zero] at h_effect
      norm_num at h_effect
    · nlinarith [sq_nonneg β]
  · rintro ⟨h_n, h_effect, hp0, hp1⟩
    exact mul_pos ((fullyTaggedFisherInformation_pos_iff n p).2 ⟨h_n, hp0, hp1⟩)
      (sq_pos_of_ne_zero h_effect)

/-- **NCP depends on population-specific MAF.**
    A variant with MAF 0.3 in Europeans may have MAF 0.05 in
    East Asians. The NCP ratio is proportional to the heterozygosity ratio. -/
theorem ncp_ratio_from_maf
    (n : ℕ) (β p₁ p₂ : ℝ)
    (hn : 0 < n) (hβ : 0 < β)
    (h_maf : p₁ < p₂) (h_half : p₂ ≤ 1/2) :
    gwasNCP n β p₁ < gwasNCP n β p₂ := by
  unfold gwasNCP
  unfold ncp effectiveFisherInformation fisherInformation genotypeVarianceHWE
  simp only [mul_one]
  apply mul_lt_mul_of_pos_right _ (sq_pos_of_pos hβ)
  apply mul_lt_mul_of_pos_left _ (Nat.cast_pos.mpr hn)
  -- 2p₁(1-p₁) < 2p₂(1-p₂) when p₁ < p₂ ≤ 1/2
  nlinarith [sq_nonneg (p₂ - p₁), sq_nonneg (1/2 - p₂)]


end GWASPowerMAF


/-!
## Genetic Architecture Parameters and Portability Predictions

We derive concrete portability predictions from genetic architecture
parameters for different trait classes.
-/

section ArchitecturePredictions

/-- Characteristic generation timescale `1/(2s)` for selection-driven portability decay. -/
noncomputable def selectionPortabilityTimescale (selectionCoefficient : ℝ) : ℝ :=
  1 / (2 * selectionCoefficient)

/-- The selection-decay timescale is pinned at `s = 1/2`. -/
theorem selectionPortabilityTimescale_at_reference_point :
    selectionPortabilityTimescale (1 / 2) = 1 := by
  norm_num [selectionPortabilityTimescale]

/-- **Selection coefficient determines portability timescale.**
    The characteristic timescale for portability decay is 1/(2s) generations,
    where s is the selection coefficient.
    Smaller `s` gives slower change; larger `s` gives faster change. -/
theorem selectionPortabilityTimescale_lt_of_selection_lt
    (s₁ s₂ : ℝ) (h₁ : 0 < s₁)
    (h_stronger : s₁ < s₂) :
    selectionPortabilityTimescale s₂ < selectionPortabilityTimescale s₁ := by
  unfold selectionPortabilityTimescale
  apply div_lt_div_of_pos_left one_pos (by linarith) (by linarith)

/-- **Number of independent loci matters more than heritability for portability.**
    Two traits with the same h² but different architecture have different portability:
    - Trait A: h² = 0.5 from 10 loci (oligogenic)
    - Trait B: h² = 0.5 from 10000 loci (highly polygenic)
    Trait B has better portability because each locus contributes less. -/
theorem polygenic_more_portable_than_oligogenic
    (h2 : ℝ) (m_oligo m_poly : ℕ)
    (h_h2 : 0 < h2)
    (h_oligo : 0 < m_oligo)
    (h_more_loci : m_oligo < m_poly) :
    polygenicAveragingVariance h2 m_poly < polygenicAveragingVariance h2 m_oligo :=
  polygenicAveragingVariance_lt_of_locusCount_lt m_oligo m_poly h2
    h_oligo h_more_loci h_h2

end ArchitecturePredictions


/-!
## Pleiotropy and Cross-Trait Portability

Pleiotropic loci affect multiple traits. The portability of a PGS
for one trait may be correlated with portability of related traits
through shared pleiotropic architecture.
-/

section Pleiotropy

/-- Target R² after a shared pleiotropic component undergoes trait-specific turnover. -/
noncomputable def pleiotropicTargetR2
    (sourceR2 sharedFraction turnover : ℝ) : ℝ :=
  sourceR2 * (1 - sharedFraction * turnover)

/-- The pleiotropic loss model is pinned at an interior reference point. -/
theorem pleiotropicTargetR2_at_reference_point :
    pleiotropicTargetR2 1 (1 / 2) (1 / 2) = 3 / 4 := by
  norm_num [pleiotropicTargetR2]

/-- **Shared portability through pleiotropy.**
    If two traits share many pleiotropic loci, their portability
    patterns are correlated. Specifically, if turnover affects
    the shared loci, both traits suffer. -/
theorem pleiotropicTargetR2_lt_source
    (sourceR2 sharedFraction turnover : ℝ)
    (h_source : 0 < sourceR2) (h_shared : 0 < sharedFraction)
    (h_turnover : 0 < turnover) :
    pleiotropicTargetR2 sourceR2 sharedFraction turnover < sourceR2 := by
  unfold pleiotropicTargetR2
  have h_retention : 1 - sharedFraction * turnover < 1 := by nlinarith
  exact mul_lt_of_lt_one_right h_source h_retention

/-- For a nonzero source signal, pleiotropic transfer preserves source R² exactly when
there is no shared component or no turnover on that component. -/
theorem pleiotropicTargetR2_eq_source_iff
    (sourceR2 sharedFraction turnover : ℝ) (h_source : sourceR2 ≠ 0) :
    pleiotropicTargetR2 sourceR2 sharedFraction turnover = sourceR2 ↔
      sharedFraction = 0 ∨ turnover = 0 := by
  unfold pleiotropicTargetR2
  constructor
  · intro h
    have h_retention : 1 - sharedFraction * turnover = 1 := by
      apply mul_left_cancel₀ h_source
      simpa using h
    have h_product : sharedFraction * turnover = 0 := by linarith
    exact mul_eq_zero.mp h_product
  · rintro (rfl | rfl) <;> ring

/-- **Cross-trait portability prediction.**
    The portability ratio of trait 1's PGS for predicting trait 2 in
    population T is bounded by the product of:
    (1) genetic correlation between traits
    (2) portability of each trait individually -/
theorem cross_trait_portability_bound
    (rg port₁ port₂ : ℝ)
    (h_rg_le : rg ≤ 1)
    (h_p₁ : 0 ≤ port₁) (h_p₁_le : port₁ ≤ 1)
    (h_p₂ : 0 ≤ port₂) (h_p₂_le : port₂ ≤ 1) :
    rg * port₁ * port₂ ≤ 1 := by
  calc rg * port₁ * port₂ ≤ 1 * 1 * 1 := by
        apply mul_le_mul
        · exact mul_le_mul h_rg_le h_p₁_le h_p₁ (by linarith)
        · exact h_p₂_le
        · exact h_p₂
        · exact mul_nonneg (by linarith) (by linarith)
    _ = 1 := by ring

end Pleiotropy

end Calibrator
