/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Coalescent.Structured
import Mathlib.Tactic

assert_below Descent.Pangenome Descent.PopGen Descent.Spectral Descent.Blindness Descent.Conditionals Descent.Portability Descent.Decision Descent.Program

namespace Descent

/-!
# The seed-bank coalescent, and where Strobeck's invariance fails

Blath, González Casanova, Kurt and Spanò, *The ancestral process of long-range seed bank
models* (J. Appl. Prob. 50, 741-759, 2013), add dormancy: a lineage may be inactive, and an
inactive lineage neither reproduces nor coalesces.  Going backwards, a pair of lineages
coalesces only while both are active, and lineages switch between active and dormant.

Structurally this is `Descent.Coalescent.Structured` with "deme" replaced by "active or
dormant".  The first-step system has the same shape -- and the answer does not, which is the
point of putting them side by side.

**Migration leaves the coalescence time alone; dormancy does not.**
`Structured.meanTimeSame_eq_two` is Strobeck's invariance: however slow the migration, two
lineages from one deme coalesce in mean time `2`, the panmictic answer.  Here, with `c` the
rate at which an active lineage goes dormant and `r` the rate at which a dormant one wakes,

  `E[T] = 1 + 2c/r`,

which exceeds the no-dormancy answer `1` for every positive `c` (`meanTimeActive_gt_one`).
A seed bank inflates coalescence times, in the exact ratio of the two switching rates, and
the inflation does not wash out however fast the switching is -- only the RATIO matters
(`meanTimeActive_eq_of_ratio`).

The asymmetry has a cause worth naming.  Migration moves a lineage between places where it
can still coalesce; dormancy moves it somewhere it cannot.  Structure that preserves the
opportunity to coalesce is invisible to coalescence times; structure that removes it is not.

## Main results

- `meanTimeActive`, `meanTimeDormant`: the solutions of the first-step system.
- `firstStep_active`, `firstStep_dormant`: they satisfy the equations the rates dictate.
- `meanTimeActive_eq`: **`E[T] = 1 + 2c/r`.**
- `meanTimeActive_gt_one`: **so dormancy strictly inflates** -- Strobeck's invariance fails.
- `meanTimeActive_eq_of_ratio`: and only the ratio `c/r` matters, not the speed.
-/

namespace Coalescent

/-- Mean time to the common ancestor of two lineages that are both ACTIVE, with dormancy
rate `c` and resuscitation rate `r`.

Empirical status: DERIVED from the seed-bank coalescent's rates by first-step analysis --
`firstStep_active` and `firstStep_dormant` check that this pair solves the system.  Whether
a population has a seed bank at all is the empirical question; `Descent.PopGen.DriftRegime`
is where the corpus keeps the regime distinctions this feeds. -/
noncomputable def meanTimeActive (c r : ℝ) : ℝ := 1 + 2 * c / r

/-- Mean time when one lineage is dormant: it must wake before anything can happen. -/
noncomputable def meanTimeDormant (c r : ℝ) : ℝ := 1 / r + meanTimeActive c r

/-- **The both-active equation.**  Either the pair coalesces, at rate `1`, or one of the two
goes dormant, at rate `2c`. -/
theorem firstStep_active {c r : ℝ} (hc : 0 < c) (hr : 0 < r) :
    meanTimeActive c r
      = 1 / (1 + 2 * c) + (2 * c / (1 + 2 * c)) * meanTimeDormant c r := by
  have h1 : (1 : ℝ) + 2 * c ≠ 0 := by linarith
  have hr' : r ≠ 0 := ne_of_gt hr
  unfold meanTimeActive meanTimeDormant meanTimeActive
  field_simp
  ring

/-- **The one-dormant equation.**  Nothing can happen until the dormant lineage wakes, at
rate `r`; a dormant lineage cannot coalesce, which is the whole difference from migration. -/
theorem firstStep_dormant (c r : ℝ) :
    meanTimeDormant c r = 1 / r + meanTimeActive c r := rfl

/-- **`E[T] = 1 + 2c/r`.** -/
@[simp] theorem meanTimeActive_eq (c r : ℝ) : meanTimeActive c r = 1 + 2 * c / r := rfl

/-- **Strobeck's invariance fails for seed banks.**  With any positive dormancy rate the
mean coalescence time strictly exceeds the no-dormancy answer `1`.

Set against `Structured.meanTimeSame_eq_two`, where migration leaves the time exactly at the
panmictic value, this is the substantive difference between the two kinds of structure:
migration moves a lineage somewhere it can still coalesce, dormancy moves it somewhere it
cannot. -/
theorem meanTimeActive_gt_one {c r : ℝ} (hc : 0 < c) (hr : 0 < r) :
    1 < meanTimeActive c r := by
  have hpos : 0 < 2 * c / r := by positivity
  rw [meanTimeActive_eq]
  linarith

/-- With no dormancy the seed-bank answer is the panmictic one: `c = 0` returns the
coalescent this group started from. -/
@[simp] theorem meanTimeActive_zero_dormancy (r : ℝ) : meanTimeActive 0 r = 1 := by
  rw [meanTimeActive_eq]
  simp

/-- **Only the ratio matters.**  Doubling both switching rates leaves the coalescence time
unchanged: a fast seed bank and a slow one with the same `c/r` are indistinguishable by
coalescence times, so the inflation cannot be made to vanish by speeding the switching up. -/
theorem meanTimeActive_eq_of_ratio {c r c' r' : ℝ} (hr : 0 < r) (hr' : 0 < r')
    (h : c / r = c' / r') : meanTimeActive c r = meanTimeActive c' r' := by
  rw [meanTimeActive_eq, meanTimeActive_eq]
  have h2 : 2 * c / r = 2 * (c / r) := by ring
  have h2' : 2 * c' / r' = 2 * (c' / r') := by ring
  rw [h2, h2', h]

/-- The dormant-state time exceeds the active-state time by the mean wait to wake, which is
the only thing that can happen from there. -/
theorem meanTimeDormant_sub_meanTimeActive (c r : ℝ) :
    meanTimeDormant c r - meanTimeActive c r = 1 / r := by
  unfold meanTimeDormant
  ring

end Coalescent

end Descent
