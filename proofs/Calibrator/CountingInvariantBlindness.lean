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

/-! ## Approximate blindness, and why the exact form is not enough

The exact witness above covers the heavy-tail ghost, where two couplings carry *identical*
effective-unit counts. It does **not** cover the `m_eff` prohibition, and the difference is
worth stating rather than papering over.

In `Calibrator.ImitationCapacity` the two spectra do not share their moments exactly; they
agree to within `1/(n+1)` in every moment the functional consults, while the certificate
values differ by `n/(n+1)`. The blindness there is a statement about *continuity* — a
functional with a modulus of continuity in the moment metric cannot separate them — not
about an exact coincidence. Instantiating that as an exact `Witness` would require an
equality that is false.

So the general object is the approximate one below, and the exact witness is its
`countGap = 0` case (`ApproxWitness.ofWitness`). The theorem then reads: a predictor that
is Lipschitz in the invariant is off by at least half of *the rate separation less what its
own Lipschitz constant can explain*. The `m_eff` prohibition is the case where that residue
is positive once `n` exceeds the modulus, which is exactly how the corpus's own proof of
`certificate_not_momentContinuous` concludes. -/

/-- **An approximate blindness witness.**

    Two configurations whose invariants are within `countGap` and whose rates are at least
    `rateGap` apart. `dist` is the metric the invariant is compared in — the moment metric
    for `m_eff`, the discrete metric for an exact coincidence. -/
structure ApproxWitness (Config : Type*) (Inv : Type*) where
  /-- The counting invariant. -/
  count : Config → Inv
  /-- The metric in which the invariant is compared. -/
  dist : Inv → Inv → ℝ
  /-- The quantity that actually sets the rate. -/
  rate : Config → ℝ
  /-- One configuration. -/
  left : Config
  /-- Another, with a nearby count. -/
  right : Config
  /-- How far apart the two invariants are. -/
  countGap : ℝ
  /-- The invariants are within `countGap`. -/
  count_close : dist (count left) (count right) ≤ countGap
  /-- How far apart the two rates are, at least. -/
  rateGap : ℝ
  /-- The rates are separated by at least `rateGap`. -/
  rate_sep : rateGap ≤ |rate left - rate right|

/-- An exact witness is the `countGap = 0` case, in any metric that vanishes on the
    diagonal. This is what makes the two blindness results instances of one theorem rather
    than two results with a shared moral. -/
noncomputable def ApproxWitness.ofWitness (W : Witness Config Inv) (d : Inv → Inv → ℝ)
    (hd : ∀ x, d x x = 0) : ApproxWitness Config Inv where
  count := W.count
  dist := d
  rate := W.rate
  left := W.left
  right := W.right
  countGap := 0
  count_close := le_of_eq (by rw [W.count_eq, hd])
  rateGap := |W.rate W.left - W.rate W.right|
  rate_sep := le_refl _

/-- **A Lipschitz predictor built from the invariant is off by at least half the residue.**

    Any `f` with Lipschitz constant `L` in the invariant's metric incurs, at one of the two
    configurations, an error of at least `(rateGap - L · countGap) / 2`. The subtracted term
    is exactly what the predictor's own continuity can account for; whatever separation
    remains is separation the invariant did not carry, and no choice of `f` recovers it.

    Setting `countGap = 0` recovers `count_predictor_error_ge`. Taking `L` to be the modulus
    of a moment-continuous functional, `countGap = 1/(n+1)` and `rateGap = n/(n+1)` gives the
    `m_eff` prohibition's arithmetic: the residue is positive as soon as `n > L`.

    **The Lipschitz hypothesis is local, at the two witness points only.** A first version
    quantified it over all of `Inv`, which is a condition no effective-marker formula in the
    literature satisfies — Cheverud–Nyholt is quadratic in the first moment and has unbounded
    secants, and Li–Ji jumps by exactly one at every integer eigenvalue. The proof never used
    more than the two points, so nothing is lost and the theorem now applies to functionals
    that are merely locally controlled. -/
theorem lipschitz_predictor_error_ge (W : ApproxWitness Config Inv)
    (f : Inv → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hf : |f (W.count W.left) - f (W.count W.right)|
            ≤ L * W.dist (W.count W.left) (W.count W.right)) :
    (W.rateGap - L * W.countGap) / 2
      ≤ max |f (W.count W.left) - W.rate W.left|
            |f (W.count W.right) - W.rate W.right| := by
  set a := f (W.count W.left) with hadef
  set b := f (W.count W.right) with hbdef
  set RL := W.rate W.left with hRL
  set RR := W.rate W.right with hRR
  have hab : |a - b| ≤ L * W.countGap :=
    le_trans hf (mul_le_mul_of_nonneg_left W.count_close hL)
  have t1 := abs_sub_le RL a RR
  have t2 := abs_sub_le a b RR
  have e1 : |RL - a| = |a - RL| := abs_sub_comm RL a
  have m1 : |a - RL| ≤ max |a - RL| |b - RR| := le_max_left _ _
  have m2 : |b - RR| ≤ max |a - RL| |b - RR| := le_max_right _ _
  have hsep := W.rate_sep
  rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
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

/-- The separation hypothesis of `ghostWitness` is satisfiable, so the witness type is
    inhabited and the blindness theorems applied to it are not conditioned on an empty
    hypothesis.

    The scale used here is degenerate — at `n = 1` the logarithm vanishes while the power is
    one — and it is offered as a **consistency witness only**. The substantive statement,
    that the two gains separate without bound at every tail index, is `gains_separate`; this
    lemma establishes only that there is something to separate. -/
theorem ghostGain_ne_countPredicted_at_one :
    ghostGain 1 1 ≠ countPredictedGain 1 1 := by
  unfold ghostGain countPredictedGain
  simp

/-- `ghostWitness` is inhabited. -/
noncomputable def ghostWitnessExample (u : ℝ) : Witness Bool ℝ :=
  ghostWitness 1 1 u ghostGain_ne_countPredicted_at_one

end Calibrator.CountingInvariantBlindness
