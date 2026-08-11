/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent

/-!
# Stepping-stone non-identifiability

WHY THIS IS NOT IN `Descent/`. The declaration below is deliberately wrong. It is the
QUADRATIC stepping-stone form, whose exponent three independent instruments reject, and it
exists so that two theorems can say what `F_ST` data cannot distinguish. A body that asserts
nothing about the world does not belong in a corpus of laws, however its head is worded, and
a reader who meets it there has to be told twice not to fix it. Mathlib keeps its
counterexamples in a separate library for the same reason; this follows that precedent.

WHAT SURVIVES BY BEING HERE. `demoSteppingStoneFst d Nₑ m σ²` and
`steppingStoneFstQuadratic d Nₑ m √(σ²/m)` are equal everywhere. So with `σ²` free, no amount
of `F_ST` data separates the linear form from the quadratic one: a fit constrains the product
`m·σ²` and nothing else, and evidence for the FUNCTIONAL FORM requires `σ²` held at an
independently determined dispersal scale while `m` varies. That is a true statement about the
limits of measurement, and stating it requires naming the rejected form. The second theorem
carries the same identity through the coalescent meeting time, so the meeting time carries the
regime rather than borrowing it from a theorem three declarations away.

WHY THE FORM IS REJECTED, in three instruments that could each have said otherwise. A 16-deme
1D stepping stone at `Nₑ = 500`, interior demes only, gives a log-log slope of `K = d(1-F)/F`
against `m` of `0.959 ± 0.010`; a separate 20-deme lattice on different seeds and a different
separation gives `0.974 ± 0.042`. The linear form predicts 1 and this one predicts 2, so the
measurements sit 4.0 and 0.62 sems from linear against 101 and 24.4 sems from quadratic.
Independently of any simulation, the form is not dimensionally homogeneous: replacing `m·σ²`
by `σ²²·m²` multiplies the denominator's second term by one extra factor of `m`, leaving a
per-generation rate added to a distance, and no choice of units rescues it.

These declarations are built and type-checked like the rest of the corpus. They are outside
the reach of `validation/code/check.py`, which scans `Descent/` only, and that is intended:
the guards enforce properties of production laws, and none of them should be asked to hold
of a body kept precisely because it is false.
-/

namespace Descent.Counterexamples

open Descent.PopGen

/-- **The quadratic stepping-stone form: the wrong exponent, on purpose.**

`d / (d + 4·Nₑ·σ⁴·m²)`, differing from `PopGen.demoSteppingStoneFst` only in carrying `σ²·m`
squared where the surviving body carries it linearly. It is not a candidate law and is not to
be corrected: replacing it with the linear denominator makes it literally
`demoSteppingStoneFst`, collapses both theorems below to `x = x`, and deletes the
non-identifiability result they exist to state.

The file header records what rejects the exponent and what the two theorems buy. -/
noncomputable def steppingStoneFstQuadratic (d Ne m σ_sq : ℝ) : ℝ :=
  d / (d + 4 * Ne * σ_sq ^ 2 * m ^ 2)

/-- **steppingStoneFstQuadratic where its denominator vanishes, named.** The guard `d + 4 * Ne *
σ_sq ^ 2 * m ^ 2` is zero at `d = 0`, `Ne = 0`, `m = 0`, `σ_sq = 0`. Lean returns `0` there
rather than the value the modelled quantity takes, and no type error marks the point. Consumers
must require `d + 4 * Ne * σ_sq ^ 2 * m ^ 2 ≠ 0`. -/
theorem steppingStoneFstQuadratic_at_d0ne0m0sq0_is_junk :
    steppingStoneFstQuadratic 0 0 0 0 = 0 := by
  unfold steppingStoneFstQuadratic
  norm_num

/-- **A freely fitted dispersal variance cannot tell the two forms apart.**

The note on `demoSteppingStoneFst` says a refitted `σ²` absorbs the extra power exactly,
and that the fit therefore constrains the product `m·σ²` and nothing else. This is that
claim, proved: at `σ' = √(σ²/m)` the quadratic form takes the same value everywhere, so no
amount of `F_ST` data with `σ²` free can distinguish them.

The consequence is the regime, and it is now enforceable: evidence for the *functional
form* requires `σ²` held at an independently measured dispersal variance while `m` varies.
Evidence gathered with `σ²` free is evidence about `m·σ²`, whatever the fit quality — the
±11% agreement quoted in the note included. -/
theorem demoSteppingStoneFst_indistinguishable_from_quadratic
    (d Ne m σ_sq : ℝ) (hm : 0 < m) (hσ : 0 ≤ σ_sq) :
    demoSteppingStoneFst d Ne m σ_sq
      = steppingStoneFstQuadratic d Ne m (Real.sqrt (σ_sq / m)) := by
  unfold demoSteppingStoneFst steppingStoneFstQuadratic
  have hnn : (0 : ℝ) ≤ σ_sq / m := div_nonneg hσ (le_of_lt hm)
  rw [Real.sq_sqrt hnn]
  have hm' : m ≠ 0 := ne_of_gt hm
  congr 2
  field_simp

/-- **The meeting time inherits the indistinguishability of the `F_ST` it produces.**

`steppingStoneDiffusionTimescale` is the only route by which `demoSteppingStoneFst` acquires
its dispersal variance, so the freedom that makes the `F_ST` unidentifiable is freedom in
this quantity. Stated so the meeting time carries the regime rather than borrowing it
silently from a theorem three declarations away: a refitted `σ²` changes the meeting time
and leaves the observable `F_ST` fixed, which is what it means for the data to constrain
`m·σ²` and not the dispersal variance itself. -/
theorem steppingStoneCoalescenceTime_indistinguishable_through_coalFst
    (d Ne m σ_sq : ℝ) (hd : 0 < d) (hNe : 0 < Ne) (hm : 0 < m) (hσ : 0 < σ_sq) :
    coalFst (steppingStoneDiffusionTimescale d σ_sq m) Ne =
      steppingStoneFstQuadratic d Ne m (Real.sqrt (σ_sq / m)) := by
  rw [steppingStoneFst_from_coalescence_time d Ne m σ_sq hd hNe hm hσ]
  exact demoSteppingStoneFst_indistinguishable_from_quadratic d Ne m σ_sq hm (le_of_lt hσ)

/-- **The four in the quadratic stepping-stone form is twice the ploidy**, the same
`4 Nₑ` scaling as every other migration-drift denominator in the corpus. Only the powers of
`m` and `σ²` distinguish this form from `demoSteppingStoneFst`; the constant does not. -/
theorem steppingStoneFstQuadratic_uses_ploidy (d Ne m σ_sq : ℝ) :
    steppingStoneFstQuadratic d Ne m σ_sq
      = d / (d + 2 * Descent.Core.ploidy * Ne * σ_sq ^ 2 * m ^ 2) := by
  unfold steppingStoneFstQuadratic Descent.Core.ploidy; ring

end Descent.Counterexamples
