/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Calibrator.MultipleMergerBlindness
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.PSeries
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.Tactic

namespace Calibrator

/-!
# What the frequency spectrum cannot determine

`FrequencySpectrumStability` proves the sharp inverse exponent `1 / (2K - 3)` for histories
restricted to at most `K` epochs.  That exponent is a statement about a finite-dimensional
sieve, and this file is the reason the restriction is not a technicality: without it there is
no exponent at all, because the inverse is not a function.

The mechanism is one convergent series.  Writing the history in coalescent time, the expected
time to the first coalescence among `m` lineages is the Laplace transform of the rescaled
history at the Kingman rate `a m = m (m - 1) / 2`, and the whole expected spectrum at every
sample size is a linear encoding of those values.  So the spectrum sees a history only through
`(L N (a m))` for `m ≥ 2`.  After the substitution `x = exp (-τ)` that family is a Müntz
system with exponents `a m - 1`, and the full Müntz theorem on an interval bounded away from
zero says its span is dense exactly when `∑ 1 / a m` diverges.  For Kingman rates the sum
converges — to exactly `2` — so on any interval there is a nonzero function orthogonal to
every exponential the spectrum can test.  Smoothing it keeps it smooth, keeps it supported in
the prescribed epoch, and keeps every Laplace zero.

Three consequences, each formalised below in the general form it actually has.

* **Localisation.** The interval was arbitrary, so an invisible change can be confined to any
  prescribed epoch.  No positive universal resolution kernel exists over an unrestricted
  smoothness class.
* **A constant minimax floor.** Two histories with the same expected spectrum induce the same
  data law at every sample size and every genome length, so no estimator separates them:
  `twoPoint_risk_lower_bound` is that argument, and it is not asymptotic.
* **Fixed sample size is worse still.** For a fixed `n` the spectrum imposes `n` linear
  conditions, so any `n + 1`-parameter family already contains a nonzero invisible direction,
  analyticity included: `exists_invisible_perturbation`.

What survives is stated too.  Ancient perturbations are attenuated at least geometrically in
cumulative coalescent time (`spectrumAttenuation_le_geometric`), which is the operator reading
of the bottleneck phenomenon; and after a finite-dimensional restriction the Laplace core is
exponentially ill-conditioned, so the stable sieve dimension grows like `log L / κ`
(`stableSieveDimension_of_scaled`).  The numerical value `κ = 2.4103951…`, its maximiser
`θ⋆ = 0.7340955…`, and the resulting genome-size multiplier `exp κ = 11.1383…` per additional
stable dimension come from maximising the Cauchy-matrix profile below; only the profile and
the scaling law are asserted formally, since the maximisation is a numerical claim.

The companion blindness is in `MultipleMergerBlindness`, which reaches the same conclusion
from the other side of the ladder: after normalisation every Λ-coalescent has the same pairwise
merger rate, so heterozygosity and mean pairwise coalescence time cannot see a multiple-merger
regime at any sample size, while the three-lineage rate identifies it exactly.  That file also
records the divergent reciprocal ladder of the Bolthausen--Sznitman total rate, which is the
precise contrast to `summable_one_div_coalescentRate` here: the Kingman ladder is quadratic and
its reciprocals converge, so the null directions exist; the linear ladder's do not.

Not formalised, and not asserted anywhere: the Müntz density theorem itself, the smoothing
construction, the Denjoy–Carleman threshold (all-sample injectivity holds exactly on
quasianalytic classes), and the asymptotics of the Cauchy Gram matrix.  Those are the analytic
steps; what is here is the algebra they consume and the statistical conclusions they support.

There are three distinct stability regimes, and none supersedes another.  On a fixed linear
span of `r` exponentials the inverse is linear with condition number exponential in `r`.  On
the nonlinear `K`-epoch sieve, colliding boundaries create the sharp Hölder exponent
`1 / (2K - 3)` recorded in `FrequencySpectrumStability`.  On unrestricted ordinary
smoothness classes, the Müntz nullspace makes the model exactly nonidentifiable.  These are,
respectively, linear conditioning, nonlinear collision geometry, and failure of injectivity.
-/

namespace SpectrumIdentifiability

open scoped BigOperators
open Filter

/-! ## The Kingman rate ladder and its reciprocal sum -/

/-- Kingman pair-coalescence rate for `m` lineages, `m (m - 1) / 2`.

    Empirical status: **VALIDATED**
    (`proofs/validation/empirical/simcov/battery_bulk9.py`,
    `test_coalescent_rate_by_ratio`). Measured as a RATIO of waiting times,
    which no time-unit convention can enter:

      ratio        this def   measured             sems
      T(2)/T(3)     3.00000   2.96490±0.02614      1.34
      T(2)/T(4)     6.00000   5.92983±0.04946      1.42
      T(2)/T(6)    15.00000  14.87823±0.11851      1.03
      T(2)/T(8)    28.00000  27.78241±0.21343      1.02

    30000 independent genealogies per lineage count, first-coalescence time
    only. The absolute value of `T(2)` against `Ne` generations is the positive
    control and it passes.

    The ratio form is deliberate. A first attempt compared the absolute rate and
    reported a clean factor of two, which was `ploidy = 1` with
    `population_size = Ne` making msprime measure time in units of `Ne` rather
    than `2 Ne`. A ratio of two quantities measured the same way removes the
    convention rather than requiring it to be got right -- the same move that
    settled the stepping-stone exponent.

    Power: the prediction spans 3 to 28, a factor of nine.

    What is validated is the RATE LADDER, against genealogies simulated under the
    Kingman model. Whether a given real population's genealogy is Kingman at all is a
    different question, and it is the one the identifiability results below leave open. -/
noncomputable def coalescentRate (m : ℕ) : ℝ :=
  (m : ℝ) * ((m : ℝ) - 1) / 2

@[simp] theorem coalescentRate_two : coalescentRate 2 = 1 := by
  norm_num [coalescentRate]

@[simp] theorem coalescentRate_three : coalescentRate 3 = 3 := by
  norm_num [coalescentRate]

/-- The rate ladder, indexed from the smallest informative sample. -/
theorem coalescentRate_add_two (k : ℕ) :
    coalescentRate (k + 2) = ((k : ℝ) + 2) * ((k : ℝ) + 1) / 2 := by
  unfold coalescentRate
  push_cast
  ring

theorem coalescentRate_add_two_pos (k : ℕ) : 0 < coalescentRate (k + 2) := by
  rw [coalescentRate_add_two]
  positivity

/-- The reciprocal rate telescopes.  This is the whole obstruction: the Müntz sum for the
Kingman ladder is a telescoping series, hence finite. -/
theorem one_div_coalescentRate_add_two (k : ℕ) :
    1 / coalescentRate (k + 2) = 2 * (1 / ((k : ℝ) + 1) - 1 / ((k : ℝ) + 2)) := by
  have h1 : ((k : ℝ) + 1) ≠ 0 := by positivity
  have h2 : ((k : ℝ) + 2) ≠ 0 := by positivity
  rw [coalescentRate_add_two]
  field_simp
  ring

/-- Exact partial sums of the Müntz series for the Kingman ladder. -/
theorem muntzPartialSum (n : ℕ) :
    ∑ k ∈ Finset.range n, 1 / coalescentRate (k + 2) = 2 - 2 / ((n : ℝ) + 1) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      have h1 : ((n : ℝ) + 1) ≠ 0 := by positivity
      have h2 : ((n : ℝ) + 2) ≠ 0 := by positivity
      rw [Finset.sum_range_succ, ih, one_div_coalescentRate_add_two]
      push_cast
      field_simp
      ring

theorem muntzPartialSum_lt_two (n : ℕ) :
    ∑ k ∈ Finset.range n, 1 / coalescentRate (k + 2) < 2 := by
  rw [muntzPartialSum]
  have : 0 < 2 / ((n : ℝ) + 1) := by positivity
  linarith

/-- **Exact Kingman Müntz mass.**  The reciprocal rate ladder does not merely converge: its
total mass is exactly two. -/
theorem hasSum_one_div_coalescentRate :
    HasSum (fun k : ℕ ↦ 1 / coalescentRate (k + 2)) 2 := by
  rw [hasSum_iff_tendsto_nat_of_nonneg
    (fun k ↦ one_div_nonneg.mpr (coalescentRate_add_two_pos k).le)]
  have hzero : Tendsto (fun n : ℕ ↦ 2 / ((n : ℝ) + 1)) atTop (nhds 0) := by
    simpa [div_eq_mul_inv] using
      tendsto_one_div_add_atTop_nhds_zero_nat.const_mul 2
  simpa only [muntzPartialSum, sub_zero] using tendsto_const_nhds.sub hzero

/-- **The Müntz criterion fails for Kingman rates.**  The reciprocal rate sum converges, so the
exponential family the spectrum tests is not dense, and a nonzero function orthogonal to all of
it exists on any interval bounded away from zero. -/
theorem summable_one_div_coalescentRate :
    Summable fun k : ℕ ↦ 1 / coalescentRate (k + 2) :=
  hasSum_one_div_coalescentRate.summable

/-- Exact value of the Kingman reciprocal-rate series. -/
theorem tsum_one_div_coalescentRate :
    ∑' k : ℕ, 1 / coalescentRate (k + 2) = 2 :=
  hasSum_one_div_coalescentRate.tsum_eq

/-- The contrast that makes the criterion a criterion rather than an accident of this proof: a
ladder growing linearly has a divergent reciprocal sum, and no such nullspace. -/
theorem not_summable_one_div_linearRate :
    ¬ Summable fun k : ℕ ↦ 1 / ((k : ℝ) + 1) :=
  -- The linear ladder is the extreme case of the merger-rate criterion, so this reads off
  -- the scale-invariant comparison theorem rather than repeating its plumbing.
  not_summable_reciprocal_of_rate_le_scaled_natSucc _ 1
    (fun _ ↦ by positivity) (fun _ ↦ by simp)

/-- **Scale-invariant superlinear polynomial Müntz boundary.** Any rate ladder bounded below
by `scale * (n + 1) ^ power`, with positive `scale` and `power > 1`, has a summable reciprocal
spectrum. Combined with `not_summable_reciprocal_of_rate_le_scaled_natSucc`, this turns the
Kingman-versus-Bolthausen--Sznitman contrast into a reusable growth criterion. -/
theorem summable_one_div_of_scaled_natSucc_rpow_le_rate
    (rate : ℕ → ℝ) (scale power : ℝ) (hscale : 0 < scale) (hpower : 1 < power)
    (hgrowth : ∀ n : ℕ, scale * ((n : ℝ) + 1) ^ power ≤ rate n) :
    Summable fun n ↦ 1 / rate n := by
  have hpowerBase : Summable fun n : ℕ ↦ 1 / (n : ℝ) ^ power :=
    Real.summable_one_div_nat_rpow.mpr hpower
  have hpowerShift : Summable fun n : ℕ ↦ 1 / (((n : ℝ) + 1) ^ power) := by
    have hshift := (summable_nat_add_iff
      (f := fun n : ℕ ↦ 1 / (n : ℝ) ^ power) 1).2 hpowerBase
    simpa only [Nat.cast_add, Nat.cast_one] using hshift
  have hscaled :
      Summable fun n : ℕ ↦ 1 / (scale * ((n : ℝ) + 1) ^ power) := by
    refine (hpowerShift.mul_left (1 / scale)).congr ?_
    intro n
    have hbase : 0 < ((n : ℝ) + 1) ^ power :=
      Real.rpow_pos_of_pos (by positivity) power
    field_simp [hscale.ne', hbase.ne']
  refine Summable.of_nonneg_of_le ?_ ?_ hscaled
  · intro n
    have hgrowthPos : 0 < scale * ((n : ℝ) + 1) ^ power :=
      mul_pos hscale (Real.rpow_pos_of_pos (by positivity) power)
    have hrate : 0 < rate n := hgrowthPos.trans_le (hgrowth n)
    exact one_div_nonneg.mpr hrate.le
  · intro n
    exact one_div_le_one_div_of_le
      (mul_pos hscale (Real.rpow_pos_of_pos (by positivity) power)) (hgrowth n)

/-! ## Fixed sample size: a linear count, and analyticity does not help -/

/-- **At a fixed sample size the spectrum imposes only `n` linear conditions.**  Any family with
`n + 1` free parameters therefore contains a nonzero perturbation the spectrum cannot see,
whatever regularity the family has — the polynomial-times-exponential construction is the
instance where the family is real analytic.

Stated for an arbitrary linear observation map, because the count is the entire argument. -/
theorem exists_invisible_perturbation {n : ℕ}
    (obs : (Fin (n + 1) → ℝ) →ₗ[ℝ] (Fin n → ℝ)) :
    ∃ v : Fin (n + 1) → ℝ, v ≠ 0 ∧ obs v = 0 := by
  by_contra hcon
  push_neg at hcon
  have hinj : Function.Injective obs := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro v hv
    by_contra hv0
    exact hcon v hv0 hv
  have hle := LinearMap.finrank_le_finrank_of_injective hinj
  simp only [Module.finrank_fin_fun] at hle
  omega

/-! ## The constant minimax floor -/

/-- **Two histories with the same expected spectrum are the same statistical experiment.**  If
they are separated by `Δ`, no estimator has worst-case risk below `Δ / 2` — at any sample size,
at any genome length, for any loss satisfying a triangle inequality.

This is why the failure above is not a rate statement.  A rate says the risk goes to zero
slowly; this says it does not go to zero.  The hypotheses are deliberately weak: `p` is the one
data law both histories induce, `est` is an arbitrary estimator, and `d` need only satisfy the
triangle inequality. -/
theorem twoPoint_risk_lower_bound {ι Θ : Type*} [Fintype ι]
    (d : Θ → Θ → ℝ) (htri : ∀ a b c, d a c ≤ d a b + d b c)
    (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1)
    (hi lo : Θ) (est : ι → Θ) :
    d hi lo / 2 ≤ max (∑ i, p i * d hi (est i)) (∑ i, p i * d (est i) lo) := by
  have key : d hi lo ≤ (∑ i, p i * d hi (est i)) + ∑ i, p i * d (est i) lo := by
    have hbound : ∑ i, p i * d hi lo
        ≤ (∑ i, p i * d hi (est i)) + ∑ i, p i * d (est i) lo := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun i _ ↦ ?_
      rw [← mul_add]
      exact mul_le_mul_of_nonneg_left (htri _ _ _) (hp i)
    calc d hi lo = (∑ i, p i) * d hi lo := by rw [hsum, one_mul]
      _ = ∑ i, p i * d hi lo := by rw [Finset.sum_mul]
      _ ≤ _ := hbound
  have h1 := le_max_left (∑ i, p i * d hi (est i)) (∑ i, p i * d (est i) lo)
  have h2 := le_max_right (∑ i, p i * d hi (est i)) (∑ i, p i * d (est i) lo)
  linarith

/-- **The genuine squared-loss floor.**  This bounds expected squared loss, not merely the
square of expected metric loss. -/
theorem twoPoint_risk_lower_bound_sq {ι Θ : Type*} [Fintype ι]
    (d : Θ → Θ → ℝ) (htri : ∀ a b c, d a c ≤ d a b + d b c) (hd : ∀ a b, 0 ≤ d a b)
    (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1)
    (hi lo : Θ) (est : ι → Θ) :
    (d hi lo / 2) ^ 2
      ≤ max (∑ i, p i * d hi (est i) ^ 2) (∑ i, p i * d (est i) lo ^ 2) := by
  have hpoint (i : ι) :
      d hi lo ^ 2 ≤ 2 * (d hi (est i) ^ 2 + d (est i) lo ^ 2) := by
    have hgap : 0 ≤
        (d hi (est i) + d (est i) lo - d hi lo) *
          (d hi (est i) + d (est i) lo + d hi lo) := by
      apply mul_nonneg
      · linarith [htri hi (est i) lo]
      · exact add_nonneg (add_nonneg (hd hi (est i)) (hd (est i) lo)) (hd hi lo)
    nlinarith [sq_nonneg (d hi (est i) - d (est i) lo)]
  have hbound :
      ∑ i, p i * d hi lo ^ 2 ≤
        ∑ i, p i * (2 * (d hi (est i) ^ 2 + d (est i) lo ^ 2)) := by
    exact Finset.sum_le_sum fun i _ ↦ mul_le_mul_of_nonneg_left (hpoint i) (hp i)
  have htotal : d hi lo ^ 2 ≤
      2 * ((∑ i, p i * d hi (est i) ^ 2) + ∑ i, p i * d (est i) lo ^ 2) := by
    calc
      d hi lo ^ 2 = (∑ i, p i) * d hi lo ^ 2 := by rw [hsum, one_mul]
      _ = ∑ i, p i * d hi lo ^ 2 := by rw [Finset.sum_mul]
      _ ≤ ∑ i, p i * (2 * (d hi (est i) ^ 2 + d (est i) lo ^ 2)) := hbound
      _ = ∑ i, (2 * (p i * d hi (est i) ^ 2) +
          2 * (p i * d (est i) lo ^ 2)) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = (∑ i, 2 * (p i * d hi (est i) ^ 2)) +
          ∑ i, 2 * (p i * d (est i) lo ^ 2) := Finset.sum_add_distrib
      _ = 2 * (∑ i, p i * d hi (est i) ^ 2) +
          2 * (∑ i, p i * d (est i) lo ^ 2) := by
        rw [Finset.mul_sum, Finset.mul_sum]
      _ = 2 * ((∑ i, p i * d hi (est i) ^ 2) +
          ∑ i, p i * d (est i) lo ^ 2) := by ring
  have hleft := le_max_left (∑ i, p i * d hi (est i) ^ 2)
    (∑ i, p i * d (est i) lo ^ 2)
  have hright := le_max_right (∑ i, p i * d hi (est i) ^ 2)
    (∑ i, p i * d (est i) lo ^ 2)
  nlinarith

/-! ## What does survive: geometric attenuation of ancient perturbations -/

/-- Squared spectral energy an epoch-localised perturbation can still deposit, when it is
supported after cumulative coalescent time `τ`. -/
noncomputable def spectrumAttenuation (n : ℕ) (τ : ℝ) : ℝ :=
  ∑ k ∈ Finset.range n, Real.exp (-(2 * coalescentRate (k + 2) * τ))

/-- The Kingman ladder outruns an arithmetic progression of step two. -/
theorem two_mul_add_one_le_coalescentRate (k : ℕ) :
    2 * (k : ℝ) + 1 ≤ coalescentRate (k + 2) := by
  have h : (k : ℝ) ≤ (k : ℝ) ^ 2 := by
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · norm_num
    · have h1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
      nlinarith
  rw [coalescentRate_add_two]
  nlinarith

/-- **Ancient perturbations are attenuated at least geometrically.**  Every rung past the first
costs a further factor `exp (-4τ)`, so the total is the first rung times a geometric series —
the operator statement of why a bottleneck erases what precedes it. -/
theorem spectrumAttenuation_le_geometric (n : ℕ) (τ : ℝ) (hτ : 0 ≤ τ) :
    spectrumAttenuation n τ
      ≤ Real.exp (-(2 * τ)) * ∑ k ∈ Finset.range n, Real.exp (-(4 * τ)) ^ k := by
  unfold spectrumAttenuation
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun k _ ↦ ?_
  rw [← Real.exp_nat_mul, ← Real.exp_add]
  refine Real.exp_le_exp.mpr ?_
  have h := two_mul_add_one_le_coalescentRate k
  nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) k) hτ]

/-! ## After a finite-dimensional restriction: an exponential conditioning law -/

/-- Cauchy-matrix conditioning profile, in the form whose singularities cancel.

The literal integrand `log ((θ² + x²) / |θ² - x²|)` integrates to
`2 [log ((1 + θ²) / (1 - θ²)) + 2θ arctan (1/θ) - θ log ((1 + θ) / (1 - θ))]`, where the two
divergent logarithms cancel as `θ → 1`.  The regrouping below performs that cancellation
symbolically, so the profile is finite on all of `[0, 1]`.

Empirical status: UNTESTED, and not the kind of thing a dataset tests: this is the closed
form of an integral, checked by the theorems below rather than by measurement. It is named
here because it carries the conditioning of a Cauchy matrix, which a numerical experiment
COULD measure. -/
noncomputable def cauchyConditioningProfile (θ : ℝ) : ℝ :=
  2 * (Real.log (1 + θ ^ 2) + (θ - 1) * Real.log (1 - θ)
    - (1 + θ) * Real.log (1 + θ) + 2 * θ * Real.arctan (1 / θ))

/-- `Real.log (1 - θ)` at `θ = 1` is Mathlib's junk value `0`.  The profile is still correct
there: the junk is multiplied by `θ - 1`, which also vanishes, and the true limit of that
product is likewise `0`. -/
theorem cauchyConditioningProfile_log_at_one_is_junk :
    Real.log (1 - (1 : ℝ)) = 0 := by
  norm_num

/-- `Real.arctan (1 / θ)` at `θ = 0` uses Mathlib's junk `1 / 0 = 0`.  The profile is again
unaffected: that term carries a factor `θ`. -/
theorem cauchyConditioningProfile_arctan_at_zero_is_junk :
    Real.arctan (1 / (0 : ℝ)) = 0 := by
  norm_num

@[simp] theorem cauchyConditioningProfile_zero : cauchyConditioningProfile 0 = 0 := by
  norm_num [cauchyConditioningProfile]

/-- Exact value at the right endpoint, after the cancellation.  It is strictly below the
numerical maximum `2.4103951…` attained near `θ⋆ = 0.7340955…`, which is why the maximiser is
interior. -/
theorem cauchyConditioningProfile_one :
    cauchyConditioningProfile 1 = Real.pi - 2 * Real.log 2 := by
  have harc : Real.arctan (1 / (1 : ℝ)) = Real.pi / 4 := by
    norm_num [Real.arctan_one]
  norm_num [cauchyConditioningProfile, harc]
  ring

/-- Exact transcendental stationarity equation for the Cauchy conditioning profile.  Its
right side is `artanh θ`, written in logarithmic form because Mathlib has no separate real
inverse-hyperbolic-tangent API. -/
def CauchyConditioningStationary (θ : ℝ) : Prop :=
  Real.arctan (1 / θ) = (1 / 2) * Real.log ((1 + θ) / (1 - θ))

/-- On the interior of the unit interval, the cancellation-safe profile agrees with the
closed form obtained by integrating the Cauchy kernel. -/
theorem cauchyConditioningProfile_eq_integral_closedForm
    (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    cauchyConditioningProfile θ =
      2 * (Real.log ((1 + θ ^ 2) / (1 - θ ^ 2)) +
        2 * θ * Real.arctan (1 / θ) -
        θ * Real.log ((1 + θ) / (1 - θ))) := by
  have hp : 1 + θ ≠ 0 := by linarith
  have hm : 1 - θ ≠ 0 := by linarith
  have hsq : 1 - θ ^ 2 ≠ 0 := by nlinarith
  rw [Real.log_div (by positivity : 1 + θ ^ 2 ≠ 0) hsq,
    Real.log_div hp hm]
  have hfactor : 1 - θ ^ 2 = (1 - θ) * (1 + θ) := by ring
  rw [hfactor, Real.log_mul hm hp]
  unfold cauchyConditioningProfile
  ring

/-- **Derivative cancellation.**  Every algebraic derivative term cancels; only the
inverse-trigonometric and logarithmic terms remain. -/
theorem hasDerivAt_cauchyConditioningProfile
    (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    HasDerivAt cauchyConditioningProfile
      (2 * (2 * Real.arctan (1 / θ) - Real.log ((1 + θ) / (1 - θ)))) θ := by
  have hθ : θ ≠ 0 := ne_of_gt hθ0
  have hm : 1 - θ ≠ 0 := by linarith
  have hp : 1 + θ ≠ 0 := by linarith
  have hAinner : HasDerivAt (fun x : ℝ ↦ 1 + x ^ 2) (2 * θ) θ := by
    convert (hasDerivAt_const θ (1 : ℝ)).add ((hasDerivAt_id θ).pow 2) using 1
    all_goals simp [id_eq]
  have hA := (Real.hasDerivAt_log (by positivity : 1 + θ ^ 2 ≠ 0)).comp θ hAinner
  have hminus : HasDerivAt (fun x : ℝ ↦ 1 - x) (-1) θ := by
    convert (hasDerivAt_const θ (1 : ℝ)).sub (hasDerivAt_id θ) using 1
    all_goals simp
  have hplus : HasDerivAt (fun x : ℝ ↦ 1 + x) 1 θ := by
    convert (hasDerivAt_const θ (1 : ℝ)).add (hasDerivAt_id θ) using 1
    all_goals simp
  have hlogminus := (Real.hasDerivAt_log hm).comp θ hminus
  have hlogplus := (Real.hasDerivAt_log hp).comp θ hplus
  have hB := ((hasDerivAt_id θ).sub_const 1).mul hlogminus
  have hC := hplus.mul hlogplus
  have hinv := (hasDerivAt_id θ).inv hθ
  have hinv' : HasDerivAt (fun x : ℝ ↦ 1 / x) (-1 / θ ^ 2) θ := by
    convert hinv using 1
    funext x
    simp [one_div, Pi.inv_apply]
  have hatan := (Real.hasDerivAt_arctan (1 / θ)).comp θ hinv'
  have hD := ((hasDerivAt_id θ).mul hatan).const_mul 2
  have htotal := ((hA.add hB).sub hC).add hD |>.const_mul 2
  convert htotal using 1
  · funext x
    simp [cauchyConditioningProfile, Function.comp_apply, id_eq]
    ring
  · simp only [Function.comp_apply, id_eq]
    rw [Real.log_div hp hm]
    field_simp
    ring

/-- Vanishing of the certified derivative is exactly the two-line transcendental equation. -/
theorem cauchyConditioningProfile_derivative_zero_iff_stationary
    (θ : ℝ) :
    2 * (2 * Real.arctan (1 / θ) - Real.log ((1 + θ) / (1 - θ))) = 0 ↔
      CauchyConditioningStationary θ := by
  unfold CauchyConditioningStationary
  constructor <;> intro h <;> linarith

/-- **Stationary-point cancellation.**  At a solution of
`arctan (1 / θ) = artanh θ`, the middle terms cancel and the conditioning exponent is one
logarithmic ratio. -/
theorem cauchyConditioningProfile_at_stationary
    (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hstationary : CauchyConditioningStationary θ) :
    cauchyConditioningProfile θ =
      2 * Real.log ((1 + θ ^ 2) / (1 - θ ^ 2)) := by
  rw [cauchyConditioningProfile_eq_integral_closedForm θ hθ0 hθ1]
  unfold CauchyConditioningStationary at hstationary
  rw [hstationary]
  ring

/-- **Exact exponential base.**  At the maximizing stationary root, the inverse
singular-value base is the elementary ratio `(1 + θ²) / (1 - θ²)`, not an unevaluated
integral. -/
theorem exp_half_cauchyConditioningProfile_at_stationary
    (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hstationary : CauchyConditioningStationary θ) :
    Real.exp (cauchyConditioningProfile θ / 2) =
      (1 + θ ^ 2) / (1 - θ ^ 2) := by
  rw [cauchyConditioningProfile_at_stationary θ hθ0 hθ1 hstationary]
  have hratio : 0 < (1 + θ ^ 2) / (1 - θ ^ 2) := by
    apply div_pos
    · positivity
    · nlinarith
  rw [show 2 * Real.log ((1 + θ ^ 2) / (1 - θ ^ 2)) / 2 =
    Real.log ((1 + θ ^ 2) / (1 - θ ^ 2)) by ring]
  exact Real.exp_log hratio

/-- Largest sieve dimension whose spectral direction is still resolvable at genome length `L`,
when the Laplace core's smallest singular value decays like `exp (-κ r / 2)`. -/
noncomputable def stableSieveDimension (kappa L : ℝ) : ℝ :=
  Real.log L / kappa

/-- **The actionable form of severe ill-posedness.** Buying `added` further stable coordinates
costs the exact genome multiplier `exp (κ * added)`. With the Cauchy exponent
`κ = 2.4103951…`, every single additional coordinate costs `11.1383…` times as much independent
data, and the stable dimension grows like `0.4148697… log L`. -/
theorem stableSieveDimension_of_scaled
    (kappa L added : ℝ) (hk : kappa ≠ 0) (hL : 0 < L) :
    stableSieveDimension kappa (Real.exp (kappa * added) * L) =
      stableSieveDimension kappa L + added := by
  unfold stableSieveDimension
  rw [Real.log_mul (Real.exp_ne_zero (kappa * added)) (ne_of_gt hL), Real.log_exp]
  field_simp
  ring

/-! ## Reference evaluations and junk-value boundaries -/

/-- At zero cumulative coalescent time nothing is attenuated: every rung contributes one. -/
@[simp] theorem spectrumAttenuation_at_zero (n : ℕ) :
    spectrumAttenuation n 0 = n := by
  simp [spectrumAttenuation]

/-- An empty ladder deposits nothing. -/
@[simp] theorem spectrumAttenuation_empty (tau : ℝ) : spectrumAttenuation 0 tau = 0 := by
  simp [spectrumAttenuation]

/-- Reference value: the first rung alone attenuates as `exp (-2 tau)`, since `a 2 = 1`. -/
theorem spectrumAttenuation_one (tau : ℝ) :
    spectrumAttenuation 1 tau = Real.exp (-(2 * tau)) := by
  simp [spectrumAttenuation]

/-- At unit genome length no sieve dimension is resolvable, whatever the exponent. -/
@[simp] theorem stableSieveDimension_at_one (kappa : ℝ) :
    stableSieveDimension kappa 1 = 0 := by
  simp [stableSieveDimension]

/-- Reference value: at genome length `exp kappa` exactly one dimension is resolvable. -/
theorem stableSieveDimension_at_exp (kappa : ℝ) (hk : kappa ≠ 0) :
    stableSieveDimension kappa (Real.exp kappa) = 1 := by
  unfold stableSieveDimension
  rw [Real.log_exp, div_self hk]

/-- Division by `kappa` at `kappa = 0` is Mathlib's junk `0`, so a vanishing conditioning
exponent reports that no dimension is stable.  The true reading is the opposite -- a zero
exponent means no ill-conditioning, hence unbounded stable dimension -- so this is a junk
value that inverts the meaning, and `stableSieveDimension_of_scaled` excludes it. -/
theorem stableSieveDimension_at_zero_exponent_is_junk (L : ℝ) :
    stableSieveDimension 0 L = 0 := by
  simp [stableSieveDimension]


end SpectrumIdentifiability

end Calibrator
