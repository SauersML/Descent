import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Counting invariants are blind to the quantity that sets the rate

This module is **self-contained: it imports only Mathlib.**

## The moral, and why it is recorded as a theorem rather than as a remark

Two results in this development reach the same conclusion from unrelated directions.

* **The `m_eff` prohibition** (`Calibrator.ImitationCapacity`, proved and simulated): no
  weakly continuous functional of the spectral law determines a detection threshold, so
  Cheverud–Nyholt and Li–Ji effective-marker counts cannot supply one, while `tr K⁻¹` can —
  and for exactly the reason those cannot, namely that it is edge-sensitive and not weakly
  continuous.

* **The heavy-tail ghost**: renewal sharing with tail index `α` has conditional gain
  `Θ(α log n)` rather than `n^α`, because a single-big-block event of mass `n^{-α}` caps
  it. Two couplings with **identical effective-unit counts** therefore differ by a logarithm
  versus a power.

Different objects, different arguments, one conclusion: *an "effective number of
independent things" is a counting invariant, and counting invariants do not see the
quantity that sets the rate.* Two independent derivations of one moral is the reason to
give the moral its own statement instead of leaving it as a shared intuition in two files.

The genetics reach of this is wide, because the pattern is everywhere in the field:
effective number of markers, effective number of independent tests, effective sample size,
effective population size used as a stand-in for a rate. Each is a map from a configuration
to a number, and the theorem below says what such a map can and cannot be asked to do.

## What is proved, and what is assumed

What is proved is the blindness itself, and a quantitative form of it: given two
configurations agreeing in the invariant and disagreeing in the rate, **no** function of the
invariant reproduces the rate, and any predictor built from the invariant is off by at
least half the separation at one of the two. That is the transferable content and it is
unconditional.

What is **not** proved here is either rate. The heavy-tail instance below takes `α log n`
and `n^α` as *given* values, exactly as the upstream statement supplies them; deriving them
needs the renewal and one-big-jump estimates, which are not in this corpus. So the instance
establishes the blindness *conditional on the two rates*, and says so. The separation's
divergence, on the other hand, is proved outright.

Empirical status: UNTESTED. The `m_eff` instance referred to above is separately SIMULATED
in `proofs/validation/meff_prohibition/`; nothing in this module is a numerical claim.
-/

namespace Calibrator.CountingInvariantBlindness

/-! ## The abstract witness -/

/-- **A blindness witness for a counting invariant.**

    `count` is the invariant — an effective-marker count, an effective sample size, any map
    from a configuration to a summary. `rate` is the quantity one wants it to determine.
    The two configurations `left` and `right` agree in the invariant and disagree in the
    rate, and that pair of facts is the entire hypothesis. -/
structure Witness (Config : Type*) (Inv : Type*) where
  /-- The counting invariant. -/
  count : Config → Inv
  /-- The quantity that actually sets the rate. -/
  rate : Config → ℝ
  /-- One configuration. -/
  left : Config
  /-- Another, with the same count. -/
  right : Config
  /-- The invariant does not separate them. -/
  count_eq : count left = count right
  /-- The rate does. -/
  rate_ne : rate left ≠ rate right

variable {Config Inv : Type*}

/-- **No function of a counting invariant determines the rate.**

    Not "no known function", and not "no continuous function": no function whatsoever. Once
    two configurations share the invariant and differ in the rate, the invariant has
    discarded the distinction and nothing downstream can recover it. This is the reason the
    prohibition cannot be escaped by proposing a better formula for the effective count —
    the defect is in what the count retains, not in how it is used. -/
theorem no_function_of_count_determines_rate (W : Witness Config Inv) :
    ¬ ∃ f : Inv → ℝ, ∀ cfg, f (W.count cfg) = W.rate cfg := by
  rintro ⟨f, hf⟩
  apply W.rate_ne
  rw [← hf W.left, ← hf W.right, W.count_eq]

/-- **The quantitative form: every count-based predictor is off by half the separation.**

    For any `f` built from the invariant, the larger of its two errors is at least half the
    gap between the rates. So the failure is not a knife-edge that a tie-breaking convention
    could dispose of — it is bounded below by a quantity one can compute from the two
    configurations, and it degrades exactly as the two rates diverge. -/
theorem count_predictor_error_ge (W : Witness Config Inv) (f : Inv → ℝ) :
    |W.rate W.left - W.rate W.right| / 2
      ≤ max |f (W.count W.left) - W.rate W.left| |f (W.count W.right) - W.rate W.right| := by
  set a := f (W.count W.left) with ha
  have hb : f (W.count W.right) = a := by rw [ha, W.count_eq]
  set L := W.rate W.left
  set R := W.rate W.right
  have htri : |L - R| ≤ |a - L| + |a - R| := by
    have h := abs_sub_le L a R
    rwa [abs_sub_comm L a] at h
  have h1 : |a - L| ≤ max |a - L| |a - R| := le_max_left _ _
  have h2 : |a - R| ≤ max |a - L| |a - R| := le_max_right _ _
  rw [hb]
  linarith

/-! ## The heavy-tail instance

Two renewal couplings sharing an effective-unit count, one with conditional gain
`α · log n` and the other with `n ^ α`. Both values are **inputs**, supplied at the value
the upstream statement gives them; nothing here derives either. What is proved is that the
pair is a blindness witness, and that the separation between the two rates grows without
bound in `n` — so the blindness is not a small-`n` artifact that averages away. -/

/-- The conditional gain of the renewal-sharing coupling: logarithmic in `n`, with the tail
    index entering as a multiplier and not as an exponent. Supplied as a value. -/
noncomputable def ghostGain (α n : ℝ) : ℝ := α * Real.log n

/-- The gain the effective-unit count would predict: a power of `n`. Supplied as a value. -/
noncomputable def countPredictedGain (α n : ℝ) : ℝ := n ^ α

/-- **The two gains separate without bound.**

    For every tail index `α > 0`, past some `n` the power exceeds the logarithm by any
    prescribed factor. This is `isLittleO_log_rpow_atTop` and nothing about renewal
    processes enters; it is recorded because it is what makes the witness below
    non-degenerate at every scale rather than at one. -/
theorem gains_separate (α D : ℝ) (hα : 0 < α) (hD : 0 < D) :
    ∀ᶠ n : ℝ in Filter.atTop, D * ghostGain α n ≤ countPredictedGain α n := by
  have hbound := (isLittleO_log_rpow_atTop hα).bound (inv_pos.mpr (mul_pos hD hα))
  filter_upwards [hbound, Filter.eventually_ge_atTop (2 : ℝ)] with n hn hn2
  have hn0 : (0 : ℝ) < n := by linarith
  have hlog : 0 < Real.log n := Real.log_pos (by linarith)
  have hrpow : 0 < n ^ α := Real.rpow_pos_of_pos hn0 α
  have hle : Real.log n ≤ (D * α)⁻¹ * n ^ α := by
    rw [Real.norm_of_nonneg (le_of_lt hlog), Real.norm_of_nonneg (le_of_lt hrpow)] at hn
    exact hn
  have hmul := mul_le_mul_of_nonneg_left hle (le_of_lt (mul_pos hD hα))
  rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt (mul_pos hD hα)), one_mul] at hmul
  unfold ghostGain countPredictedGain
  calc D * (α * Real.log n) = D * α * Real.log n := by ring
    _ ≤ n ^ α := hmul

/-- **The heavy-tail ghost as a blindness witness.**

    Two configurations, distinguished only by a label, carrying the same effective-unit
    count `u` and the two gains. The hypothesis `hne` is where the upstream content sits:
    the two rates genuinely differ at the scale in question. Everything the abstract
    theorems then say applies — in particular no function of `u` reproduces the gain, at
    any level of ingenuity in the choice of function. -/
noncomputable def ghostWitness (α n u : ℝ)
    (hne : ghostGain α n ≠ countPredictedGain α n) : Witness Bool ℝ where
  count := fun _ => u
  rate := fun b => if b then ghostGain α n else countPredictedGain α n
  left := true
  right := false
  count_eq := rfl
  rate_ne := by simpa using hne

end Calibrator.CountingInvariantBlindness
