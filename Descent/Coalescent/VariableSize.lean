/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Coalescent.Rates
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic

assert_below Descent.Pangenome Descent.PopGen Descent.Spectral Descent.Blindness
assert_below Descent.Conditionals Descent.Portability Descent.Decision Descent.Program

namespace Descent

/-!
# A population that changes size: the coalescent as a deterministic time change

Everything in `Descent.Coalescent` up to here holds the population size constant.  Real
histories do not, and the corpus's own `Descent.PopGen.HumanDemography` is a catalogue of
bottlenecks and expansions.  The standard device -- Griffiths and Tavaré (1994) -- is that a
varying size does not need a new coalescent: it is the SAME coalescent run on a different
clock.

If `λ(t)` is the population size `t` units back, relative to its present value, then a pair
of lineages coalesces at instantaneous rate `1/λ(t)` rather than `1`, because coalescence is
faster in a smaller population.  Define

  `τ(t) = ∫₀ᵗ ds/λ(s)`,

and the process on the `τ` clock is a standard coalescent.  All the constant-size results
transfer verbatim -- the ladder `d_k`, `E(T_n) = 2 - 2/n`, `E(L_n) = 2a_{n-1}` -- provided
the answers are read in `τ` and converted back through `τ⁻¹`.

This file does the exponential case, which is the one demography actually uses and the only
one whose time change has a closed form.  A population growing forwards at rate `β` was
smaller in the past, `λ(t) = e^{-βt}`, and

  `τ(t) = (e^{βt} - 1)/β`.

The defining property is `deriv_timeChange`: `τ'(t) = 1/λ(t)`, proved through Mathlib's
`deriv` rather than asserted, so `τ` is the time change and not a formula resembling one.

## What growth does, proved

`timeChange_ge` is `τ(t) ≥ t` for `β ≥ 0`, which is `e^u ≥ 1 + u`.  Everything demographers
say about expansions follows from that one inequality read through
`pairSurvival_le_constant`:

  a growing population's lineages coalesce SOONER than a constant one's, at every time,
  uniformly.

Sooner coalescence means a shallower, more star-like tree; a star-like tree puts almost all
its length in terminal branches; terminal branches carry singletons.  So an expansion
inflates the singleton class relative to
`Descent.Coalescent.SiteFrequencySpectrum.expectedSpectrum`'s neutral `θ/i`, which is a
negative Tajima's `D` -- the departure that
`Descent.Coalescent.SegregatingSites.expectedTajimaNumerator_eq_zero` makes a test.  The
chain from "the population grew" to "the statistic goes negative" is here as far as the
survival function; the branch-length consequence needs the tree under a time change and is
not proved.

## Main results

- `relativeSize`, `timeChange`: `λ(t) = e^{-βt}` and `τ(t) = (e^{βt} - 1)/β`.
- `deriv_timeChange`: **`τ'(t) = 1/λ(t)`**, the defining ODE, through `deriv`.
- `timeChange_zero`, `timeChange_strictMono`: it is a clock.
- `timeChange_ge`: `τ(t) ≥ t` under growth.
- `pairSurvival_le_constant`: **growth never delays coalescence**, uniformly in `t`.
- `timeChange_tendsto_atTop`: coalescence is still certain -- growth compresses the tree, it
  does not prevent the tree.
-/

namespace Coalescent

open Filter Topology

/-! ### The mechanism: a size history, and the clock it induces -/

/-- `λ(t)`, the population size `t` coalescent units in the past relative to the present, for
a population growing forwards at exponential rate `β`.

Empirical status: THIS IS THE MODEL.  Exponential growth is a modelling choice about a
history, not a derivation; `Descent.PopGen.HumanDemography` is where the corpus records
which histories have been measured. -/
noncomputable def relativeSize (β t : ℝ) : ℝ := Real.exp (-(β * t))

@[simp] theorem relativeSize_zero (β : ℝ) : relativeSize β 0 = 1 := by
  simp [relativeSize]

theorem relativeSize_pos (β t : ℝ) : 0 < relativeSize β t := Real.exp_pos _

/-- A growing population is smaller in the past. -/
theorem relativeSize_le_one {β t : ℝ} (hβ : 0 ≤ β) (ht : 0 ≤ t) : relativeSize β t ≤ 1 := by
  unfold relativeSize
  rw [Real.exp_le_one_iff]
  have : 0 ≤ β * t := mul_nonneg hβ ht
  linarith

/-- `τ(t) = ∫₀ᵗ ds/λ(s)`, evaluated for the exponential history: the amount of standard
coalescent time that has elapsed by real time `t`.

Empirical status: DERIVED given `relativeSize` -- `deriv_timeChange` is the statement that
this function has the derivative the integral definition requires, and the integral of a
continuous function is determined by its derivative and its value at zero, both of which are
proved below. -/
noncomputable def timeChange (β t : ℝ) : ℝ := (Real.exp (β * t) - 1) / β

@[simp] theorem timeChange_zero (β : ℝ) : timeChange β 0 = 0 := by
  simp [timeChange]

/-- **The defining property: `τ'(t) = 1/λ(t)`.**  This is what makes `timeChange` the time
change rather than an expression with the right shape, and it is the only place the
exponential form is used. -/
theorem deriv_timeChange {β : ℝ} (hβ : β ≠ 0) (t : ℝ) :
    deriv (timeChange β) t = 1 / relativeSize β t := by
  have hf : HasDerivAt (fun s : ℝ ↦ β * s) β t := by
    simpa using (hasDerivAt_id t).const_mul β
  have hexp : HasDerivAt (fun s : ℝ ↦ Real.exp (β * s)) (Real.exp (β * t) * β) t := hf.exp
  have hd : HasDerivAt (timeChange β) (Real.exp (β * t) * β / β) t :=
    (hexp.sub_const 1).div_const β
  rw [hd.deriv]
  unfold relativeSize
  rw [Real.exp_neg, one_div, inv_inv, mul_div_assoc, div_self hβ, mul_one]

/-- **The rate the clock encodes is the corpus's own ladder, divided by the size.**  A pair
of lineages coalesces at `d_2/λ(t)` rather than `d_2`, and `Rates.deathRate_two` is the
statement that `d_2 = 1`.  Recorded so that the time change is tied to the rate ladder the
rest of the group derives, rather than to a `1` that happens to appear in `deriv_timeChange`.

The `k`-lineage version needs no separate proof: every rate in the ladder is multiplied by
the same `1/λ(t)`, which is exactly why a varying size is a time change and not a different
process. -/
theorem deriv_timeChange_eq_deathRate_div {β : ℝ} (hβ : β ≠ 0) (t : ℝ) :
    deriv (timeChange β) t = deathRate 2 / relativeSize β t := by
  rw [deriv_timeChange hβ, deathRate_two]

/-- The whole ladder, time-changed: `d_k` becomes `d_k/λ(t)` for every `k` at once. -/
theorem deathRate_mul_deriv_timeChange {β : ℝ} (hβ : β ≠ 0) (t : ℝ) (k : ℕ) :
    deathRate k * deriv (timeChange β) t = deathRate k / relativeSize β t := by
  rw [deriv_timeChange hβ]
  ring

/-- The clock runs forwards. -/
theorem timeChange_strictMono {β : ℝ} (hβ : 0 < β) : StrictMono (timeChange β) := by
  intro a b hab
  have hexp : Real.exp (β * a) < Real.exp (β * b) :=
    Real.exp_lt_exp.mpr ((mul_lt_mul_left hβ).mpr hab)
  have hdiff : 0 < (Real.exp (β * b) - Real.exp (β * a)) / β :=
    div_pos (by linarith) hβ
  have heq : (Real.exp (β * b) - Real.exp (β * a)) / β
      = timeChange β b - timeChange β a := by
    unfold timeChange
    simp only [sub_div]
    ring
  rw [heq] at hdiff
  linarith

/-! ### What growth does -/

/-- **`τ(t) ≥ t`: growth speeds the clock.**  The whole of the demographic story is this
inequality, and the inequality is `e^u ≥ 1 + u`. -/
theorem timeChange_ge {β : ℝ} (hβ : 0 < β) (t : ℝ) : t ≤ timeChange β t := by
  have hβ0 : β ≠ 0 := ne_of_gt hβ
  have hexp : β * t + 1 ≤ Real.exp (β * t) := Real.add_one_le_exp (β * t)
  have heq : (Real.exp (β * t) - 1 - t * β) / β = timeChange β t - t := by
    unfold timeChange
    rw [sub_div, mul_div_assoc, div_self hβ0, mul_one]
  have hnn : 0 ≤ (Real.exp (β * t) - 1 - t * β) / β :=
    div_nonneg (by linarith) hβ.le
  rw [heq] at hnn
  linarith

/-- The probability that two lineages have not yet coalesced by real time `t`: the standard
`e^{-s}` read on the `τ` clock.

Empirical status: DERIVED given the time change -- it is `Descent.Coalescent.HoldingTime`'s
exponential survival at `d_2 = 1`, composed with `timeChange`. -/
noncomputable def pairSurvival (β t : ℝ) : ℝ := Real.exp (-(timeChange β t))

@[simp] theorem pairSurvival_zero (β : ℝ) : pairSurvival β 0 = 1 := by
  simp [pairSurvival]

/-- **Growth never delays coalescence.**  At every time in the past, a pair of lineages from
an expanding population is less likely to be still separate than a pair from a constant one.
Uniformly in `t`, with no asymptotics and no approximation.

This is why expansions produce shallow, star-like genealogies, and hence an excess of
singletons over `SiteFrequencySpectrum`'s neutral profile -- the mechanism behind every
negative Tajima's `D` ever attributed to population growth. -/
theorem pairSurvival_le_constant {β : ℝ} (hβ : 0 < β) (t : ℝ) :
    pairSurvival β t ≤ Real.exp (-t) := by
  unfold pairSurvival
  rw [Real.exp_le_exp]
  have := timeChange_ge hβ t
  linarith

/-- Coalescence remains certain: the clock runs to infinity, so growth compresses the tree
rather than preventing it.  A population that grew fast enough for lineages to escape
coalescence entirely would need `τ` to be bounded, which the exponential history is not. -/
theorem timeChange_tendsto_atTop {β : ℝ} (hβ : 0 < β) :
    Tendsto (timeChange β) atTop atTop := by
  exact tendsto_atTop_mono (fun t ↦ timeChange_ge hβ t) tendsto_id

/-- The constant-size coalescent is the `β → 0` boundary of this family, in the only sense
available without a limit: the clock's derivative at the present is `1` for every `β`, so no
finite growth rate changes the rate at which lineages coalesce TODAY.  Growth is visible only
in the past, which is why it is a statement about tree shape and not about the pair
coalescence rate. -/
theorem deriv_timeChange_at_zero {β : ℝ} (hβ : β ≠ 0) :
    deriv (timeChange β) 0 = 1 := by
  rw [deriv_timeChange hβ, relativeSize_zero]
  norm_num

end Coalescent

end Descent
