/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
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

/-! ## The Kingman rate ladder and its reciprocal sum -/

/-- Kingman pair-coalescence rate for `m` lineages, `m (m - 1) / 2`. -/
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

/-- **The Müntz criterion fails for Kingman rates.**  The reciprocal rate sum converges, so the
exponential family the spectrum tests is not dense, and a nonzero function orthogonal to all of
it exists on any interval bounded away from zero. -/
theorem summable_one_div_coalescentRate :
    Summable fun k : ℕ ↦ 1 / coalescentRate (k + 2) := by
  refine summable_of_sum_range_le (c := 2) (fun k ↦ ?_) (fun n ↦ ?_)
  · exact one_div_nonneg.mpr (coalescentRate_add_two_pos k).le
  · exact (muntzPartialSum_lt_two n).le

theorem tsum_one_div_coalescentRate_le_two :
    ∑' k : ℕ, 1 / coalescentRate (k + 2) ≤ 2 := by
  refine Real.tsum_le_of_sum_range_le (fun k ↦ ?_) (fun n ↦ (muntzPartialSum_lt_two n).le)
  exact one_div_nonneg.mpr (coalescentRate_add_two_pos k).le

/-- The contrast that makes the criterion a criterion rather than an accident of this proof: a
ladder growing linearly has a divergent reciprocal sum, and no such nullspace. -/
theorem not_summable_one_div_linearRate :
    ¬ Summable fun k : ℕ ↦ 1 / ((k : ℝ) + 1) := by
  intro h
  refine Real.not_summable_one_div_natCast ?_
  refine (summable_nat_add_iff 1).mp ?_
  simpa using h

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

/-- The squared-loss reading of the same floor. -/
theorem twoPoint_risk_lower_bound_sq {ι Θ : Type*} [Fintype ι]
    (d : Θ → Θ → ℝ) (htri : ∀ a b c, d a c ≤ d a b + d b c) (hd : ∀ a b, 0 ≤ d a b)
    (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1)
    (hi lo : Θ) (est : ι → Θ) :
    (d hi lo / 2) ^ 2
      ≤ max (∑ i, p i * d hi (est i)) (∑ i, p i * d (est i) lo) ^ 2 := by
  have hnn : 0 ≤ d hi lo / 2 := by have := hd hi lo; linarith
  exact pow_le_pow_left₀ hnn (twoPoint_risk_lower_bound d htri p hp hsum hi lo est) 2

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
symbolically, so the profile is finite on all of `[0, 1]`. -/
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

/-- **The actionable form of severe ill-posedness: one more resolvable epoch dimension costs a
fixed multiplicative factor `exp κ` of genome.**  With the Cauchy exponent `κ = 2.4103951…`
that factor is `11.1383…`, and the stable dimension grows like `0.4148697… log L`. -/
theorem stableSieveDimension_of_scaled (kappa L : ℝ) (hk : kappa ≠ 0) (hL : 0 < L) :
    stableSieveDimension kappa (Real.exp kappa * L) = stableSieveDimension kappa L + 1 := by
  unfold stableSieveDimension
  rw [Real.log_mul (Real.exp_ne_zero kappa) (ne_of_gt hL), Real.log_exp]
  field_simp
  ring

end SpectrumIdentifiability

end Calibrator
