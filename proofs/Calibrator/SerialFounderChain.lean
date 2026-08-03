/-
Copyright (c) 2026 Sauers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sauers
-/
import Mathlib

namespace Calibrator

/-!
# The serial founder chain

The `sims/` study runs two demographies. `grid2d` is a 2-D stepping stone and the corpus
covers it (`steppingStoneFst` in `PortabilityDrift`, `demoSteppingStoneFst` in
`DemographicHistory`). `serial1d` is a **serial founder chain** and had no definition
anywhere, so half the study could not be predicted from demography forward.

This file records what a measurement established about that family, including the reason it
is a **recurrence** and not a closed form.

## What was measured

`proofs/validation/differential/cluster/fam_serial_founder.py` solves the demography of
`gen_real_pt.py::dem_serial1d` exactly, as a piecewise-constant structured coalescent on a
56-state pair chain — no simulation, no fitted quantity. For `D = 10`, `N = 3000`,
`N_anc = 10000`, `m = 1e-3`, `splitStep = 400`, `T0 = 200`:

* `E[T₀₀] = 17371.5`, `E[T₉₉] = 15056.8`, `E[T₀₉] = 20079.0` generations;
* far-deme `F_ST = 0.1925`, against `gen_real_pt.py`'s own comment that this configuration
  "already gives far-Fst ~0.21" — an independent corroboration from the study's text;
* the existing stepping-stone form is off by a factor of **7.5**, so this family genuinely
  needs its own definition and this is not a relabelling.

## The mechanism, which is the finding

Three candidate closed forms were tried and all three failed for **one shared reason**: each
compounds a per-founder-event term, and that mechanism is not present.

In a serial founder chain deme `k` splits from deme `k-1` at `t_k = T0 + (D-1-k)·splitStep`,
so **backwards in time a lineage sampled in deme `k` walks back through `k-1, k-2, …` and
reaches deme 0 at `t₁`, whatever `k` is**. Founder events therefore fix a **ceiling** and
contribute **no distance dependence at all**. `serialFounderJoinTime_const` states exactly
that, and `joinTime_pushforward_not_lt` turns it into the
obstruction: any `F_ST` that were a function of the founder history alone would be constant
across all non-source demes, contradicting the measured strictly increasing curve.

All of the distance decay is **migration closing the gap before the forced merge**.

## Why a recurrence, and not an algebraic form

The forced merges make the separation process **time-inhomogeneous**: the deme labels
available to a lineage change at every `t_k`. A meeting problem with a moving state space has
no stationary random-walk solution, so an algebraic function of `k` is wrong *in principle*
and not merely inaccurate. `driftLDStep` is the precedent in this corpus for recording such a
family as a step.

**The validated part and the missing part are recorded separately**, because naming what the
closed form cannot do is what stops the next reader re-deriving it:

* the **ceiling** is predicted to `3.9%` with zero free parameters (`0.18497` against the
  exact `0.19248`) — `serialFounderCeilingFst` below;
* the **approach** to it is missed by `95%` at `k = 1`, and that is what the recurrence has
  to supply. The diffusion/reflection meeting time overestimates how long two *adjacent*
  demes stay unmixed, which is exactly where a continuum approximation to a rate-`2m`
  nearest-neighbour walk is worst.
-/

open scoped BigOperators

/-- Time at which a lineage sampled in deme `k` of a serial founder chain has walked back to
the source deme. Deme `k` splits from deme `k-1` at `T0 + (D-1-k)·splitStep`, so a lineage
steps back one deme at a time and arrives at deme 0 at `T0 + (D-2)·splitStep` — **for every
`k ≥ 1`**. The source deme itself is at time `0` by convention. -/
noncomputable def serialFounderJoinTime (T0 splitStep : ℝ) (D k : ℕ) : ℝ :=
  if k = 0 then 0 else T0 + splitStep * ((D : ℝ) - 2)

/-- **The founder ceiling carries no distance information.** Every non-source deme reaches
the source at the same time, so the founder history alone cannot distinguish a near deme from
a far one. This is the measured mechanism, and it is why three candidate closed forms that
each compounded a per-founder-event term all failed. -/
theorem serialFounderJoinTime_const (T0 splitStep : ℝ) (D j k : ℕ)
    (hj : j ≠ 0) (hk : k ≠ 0) :
    serialFounderJoinTime T0 splitStep D j = serialFounderJoinTime T0 splitStep D k := by
  unfold serialFounderJoinTime
  simp [hj, hk]

/-- **The obstruction, stated as a theorem.** If `F` were a function of the founder history
alone — that is, of the join time — then it would be constant across all non-source demes.
A measured `F_ST` that strictly increases with distance therefore rules out every model of
that shape, which is precisely what the three failing candidates had in common. -/
theorem joinTime_pushforward_not_lt
    (T0 splitStep : ℝ) (D : ℕ) (F : ℕ → ℝ) (g : ℝ → ℝ)
    (hfounder : ∀ k, k ≠ 0 → F k = g (serialFounderJoinTime T0 splitStep D k))
    (j k : ℕ) (hj : j ≠ 0) (hk : k ≠ 0) (hlt : F j < F k) : False := by
  have h := serialFounderJoinTime_const T0 splitStep D j k hj hk
  rw [hfounder j hj, hfounder k hk, h] at hlt
  exact lt_irrefl _ hlt

/-- Expected within-deme coalescence time for the chain: a pair either coalesces inside the
chain, whose total age is `tAnc`, or survives into the ancestral population and waits a
further `2·N_anc`.

    Empirical status: UNTESTED. -/
noncomputable def serialFounderWithinTime (N Nanc tAnc : ℝ) : ℝ :=
  2 * N * (1 - Real.exp (-tAnc / (2 * N)))
    + Real.exp (-tAnc / (2 * N)) * (tAnc + 2 * Nanc)

/-- **The validated half.** The saturated far-deme `F_ST` is the ratio of the ceiling waiting
time to the total, `τ / (T_w + τ)`, with `τ` the founder ceiling and `T_w` the within-deme
time. Measured: `0.18497` against an exact `0.19248`, a `3.9%` error with no free parameter.

This is the part a closed form gets right. The approach to it is not, and
`serialFounderFstApproach` is the field that has to supply it.

    Empirical status: MEASURED at one design point -- `0.18497` against the
    analytic `0.19248`, a `3.9%` error with no free parameter. Power is not
    established: a single configuration cannot reject a wrong functional form,
    so this is not recorded as VALIDATED. -/
noncomputable def serialFounderCeilingFst (N Nanc tAnc τ : ℝ) : ℝ :=
  τ / (serialFounderWithinTime N Nanc tAnc + τ)

/-- The ceiling `F_ST` is a genuine variance ratio: nonnegative, and below one whenever the
within-deme time is positive. -/
theorem serialFounderCeilingFst_lt_one (N Nanc tAnc τ : ℝ)
    (hτ : 0 ≤ τ) (hw : 0 < serialFounderWithinTime N Nanc tAnc) :
    serialFounderCeilingFst N Nanc tAnc τ < 1 := by
  unfold serialFounderCeilingFst
  rw [div_lt_one (by linarith)]
  linarith

theorem serialFounderCeilingFst_nonneg (N Nanc tAnc τ : ℝ)
    (hτ : 0 ≤ τ) (hw : 0 < serialFounderWithinTime N Nanc tAnc) :
    0 ≤ serialFounderCeilingFst N Nanc tAnc τ := by
  unfold serialFounderCeilingFst
  exact div_nonneg hτ (by linarith)

/-- **The serial founder chain as a recurrence**, in the style of `driftLDStep`.

The separation process between two lineages is **time-inhomogeneous**: the set of demes a
lineage can occupy shrinks at every founder time `t_k`, so the meeting problem has no
stationary solution and no algebraic function of `k` can be correct. The family is therefore
recorded as a step plus the two quantities the measurement settled.

`ceilingValidated` and `approachOpen` are separate fields on purpose: the first is the part
with a checked closed form, the second is the part that is not, and collapsing them would
lose exactly the information that stops the next reader re-deriving a form that cannot work.
-/
structure SerialFounderChain where
  /-- Number of demes in the chain. -/
  demeCount : ℕ
  /-- Deme size. -/
  demeSize : ℝ
  /-- Ancestral population size. -/
  ancestralSize : ℝ
  /-- Symmetric migration rate between adjacent demes. -/
  migration : ℝ
  /-- Generations between consecutive founder events. -/
  splitStep : ℝ
  /-- Age of the most recent founder event. -/
  founderOffset : ℝ
  /-- One generation of the separation recurrence: the un-met probability at each separation,
  advanced by migration and by whatever forced merge falls at this time. This is the object
  that has no closed form. -/
  separationStep : ℝ → (ℕ → ℝ) → (ℕ → ℝ)
  /-- The founder ceiling, the expected waiting time imposed by the forced merges. -/
  ceiling : ℝ
  /-- **Audit point, VALIDATED.** The saturated `F_ST` equals `serialFounderCeilingFst` at
  this ceiling, measured to `3.9%` with no free parameter. -/
  ceilingValidated : Bool
  /-- **Audit point, OPEN.** The approach to the ceiling at small separation. The
  diffusion/reflection meeting time misses it by `95%` at `k = 1`; only the recurrence
  supplies it. -/
  approachOpen : Bool

namespace SerialFounderChain

variable (C : SerialFounderChain)

/-- The join time of every non-source deme in the chain, which is the ceiling's origin. -/
noncomputable def joinTime (k : ℕ) : ℝ :=
  serialFounderJoinTime C.founderOffset C.splitStep C.demeCount k

/-- **Restatement in the structure**: the chain's own join times carry no distance
information, so any `F_ST` for this family must come from the migration side of the
recurrence. -/
theorem joinTime_const (j k : ℕ) (hj : j ≠ 0) (hk : k ≠ 0) :
    C.joinTime j = C.joinTime k :=
  serialFounderJoinTime_const _ _ _ _ _ hj hk

end SerialFounderChain

end Calibrator
