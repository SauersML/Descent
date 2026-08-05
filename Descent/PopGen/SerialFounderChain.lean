/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

import Descent.Core.Scaling

namespace Descent.PopGen

/-!
# The serial founder chain

The `sims/` study runs two demographies. `grid2d` is a 2-D stepping stone and the corpus
covers it (`steppingStoneFst` in `PortabilityDrift`, `demoSteppingStoneFst` in
`DemographicHistory`). `serial1d` is a **serial founder chain** and had no definition
anywhere, so half the study could not be predicted from demography forward.

This file records what a measurement established about that family, including the reason it
is a **recurrence** and not a closed form.

## What was measured

`validation/empirical/differential/cluster/fam_serial_founder.py` solves the demography of
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

/-- **Two demes leave no room for a serial step.** At `D = 2` the chain has a source and one
descendant, the step count is zero, and the join time is the base time alone. The constancy
theorem below says the join time does not depend on `k`; this says what the constant is, which
constancy alone leaves free. -/
theorem serialFounderJoinTime_two_demes (T0 splitStep : ℝ) (k : ℕ) (hk : k ≠ 0) :
    serialFounderJoinTime T0 splitStep 2 k = T0 := by
  unfold serialFounderJoinTime
  rw [if_neg hk]
  norm_num

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

    Empirical status: **VALIDATED**
    (`validation/empirical/simcov/battery_falsrepair_e.py`), the body
    having been corrected first and measured second. Mean pairwise TMRCA in a
    two-epoch history under msprime, 60000 independent genealogies per cell,
    `N = 400`, `Nanc = 4000`:

      tAnc    this body   superseded   measured           sems(this)  sems(sup.)
       200      6407.37     6563.13    6391.08±31.72         0.51         5.42
       800      3448.73     3743.04    3438.09±25.84         0.41        11.80
      3000       969.33     1039.88     970.81± 8.38         0.18         8.24

    Worst cell 0.51 sems where the superseded body reaches 11.80. A third form
    with the sign of the `tAnc` term flipped, `2N(1-e^-a) + e^-a (2 Nanc - tAnc)`,
    rides the same cells and is excluded at 10.98 sems, so the measurement picks
    the coefficient of `tAnc` as zero rather than merely rejecting one sign of it.

    Control: with `Nanc = N` the history is single-epoch and the mean pairwise
    TMRCA must be `2N = 800` whatever `tAnc` is. Measured 798.00 ± 3.27, passing
    at 0.61 sems. **The earlier record had no control that could fail** -- it
    compared the constant `2·Nanc` against itself and was correctly recorded as
    a LEAD rather than a verdict, which is why the correction below was carried
    in prose for a while with a FALSIFIED marker describing the superseded body.

    The error is a double-counted `tAnc`. Decomposing on whether the pair
    coalesces before the size change,

      E[T] = ∫₀^tAnc t f(t) dt + P(not yet) · (tAnc + 2 Nanc),

    and the second term is right: a pair still uncoalesced at `tAnc` waits a
    further `2 Nanc` on average, so `tAnc + 2 Nanc` from the present. What was
    wrong is the FIRST term. The truncated integral is
    `2N - e^(-a) (2N + tAnc)`, not `2N (1 - e^(-a))`, and the missing
    `-e^(-a) tAnc` is exactly what cancels the `tAnc` carried by the second
    term. The two forms differ by `tAnc · e^(-tAnc/(2N))`, which is 294 of the
    3743 at `tAnc = 800`.

    After cancellation the expectation is simply `2N` weighted by the
    probability of coalescing in the recent epoch and `2 Nanc` by its
    complement, which is the body now.

    Power: the prediction spans 969.33 to 6407.37, a factor of six and a half,
    and `tAnc` crosses the epoch boundary in both directions -- most pairs
    coalesce after it at `tAnc = 200` and before it at `tAnc = 3000`. This form
    holds across that whole range at 0.51 sems; the superseded one fails hardest
    in the middle, where `e^(-a) tAnc` is largest. -/
noncomputable def serialFounderWithinTime (N Nanc tAnc : ℝ) : ℝ :=
  2 * N * (1 - Real.exp (-tAnc / (2 * N)))
    + Real.exp (-tAnc / (2 * N)) * (2 * Nanc)

/-- A zero effective size sends `-tAnc / (2 * N)` to Mathlib's junk `0`, hence the exponential
to one, and the body reports the ancestral term alone.  The true limit is the opposite: with no
population there is no within-chain coalescent time to accumulate.

The junk value is now `2 * Nanc` rather than `tAnc + 2 * Nanc`, because the body no longer
double-counts `tAnc`; the correction is recorded on the definition above. The branch is still
junk and still has to be excluded by hypothesis -- what changed is only which wrong number it
returns. -/
theorem serialFounderWithinTime_at_zero_size_is_junk (Nanc tAnc : ℝ) :
    serialFounderWithinTime 0 Nanc tAnc = 2 * Nanc := by
  unfold serialFounderWithinTime
  simp


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

/-- **serialFounderCeilingFst at zero between-population coalescent time, named.** With the
between-population time set to zero the ratio has a vanishing numerator, and the
within-population time can vanish with it. Lean returns `0`: no ceiling on differentiation along
a serial founder chain, which is the value for populations that never separated. Consumers must
exclude it by hypothesis. -/
theorem serialFounderCeilingFst_no_coalescent_time_is_junk (N Nanc tAnc : ℝ) :
    serialFounderCeilingFst N Nanc tAnc 0 = 0 := by
  unfold serialFounderCeilingFst
  norm_num

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

/-- **The chain is inhabited**, at a five-deme serial founder expansion: demes of a
thousand from an ancestral ten thousand, migration `10⁻³` between neighbours, a founder
event every two thousand generations with the most recent one two thousand generations
back, and the separation recurrence advanced by neighbour migration alone.

A theorem quantified over an uninhabited structure is true and empty. The two audit
flags are set to the values the docstrings above record -- the ceiling VALIDATED, the
approach OPEN -- rather than both to `true`, because a witness that asserted the open
question was settled would be the one thing this record exists to prevent. -/
noncomputable def SerialFounderChain.witness : SerialFounderChain where
  demeCount := 5
  demeSize := 1000
  ancestralSize := 10000
  migration := 1 / 1000
  splitStep := 2000
  founderOffset := 2000
  separationStep := fun m u k ↦ (1 - m) * u k
  ceiling := 2000
  ceilingValidated := true
  approachOpen := true

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

/-- **The chain's own within-deme coalescent time**, `serialFounderWithinTime`
evaluated at the chain's deme size and ancestral size.

`demeSize` and `ancestralSize` are the two sizes the corrected two-epoch
expectation is a function of, and until this definition existed the structure
carried them without ever feeding them to it -- so the recorded model and the
validated law referred to the same population only by the reader's assumption.
`ancestralEpoch` stays a parameter because the structure records a chain, not an
epoch boundary.

    Empirical status: DERIVED. An instantiation of `serialFounderWithinTime` at
    the chain's own two sizes, introducing no free parameter of its own. The
    evidence is the one recorded there, and this definition neither adds to it
    nor weakens it. -/
noncomputable def withinTime (ancestralEpoch : ℝ) : ℝ :=
  serialFounderWithinTime C.demeSize C.ancestralSize ancestralEpoch

/-- **The chain's own saturated far-deme `F_ST`**: the ratio the audit field
`ceilingValidated` is a flag about, now written where the flag can point at it.
Measured `0.18497` against the analytic `0.19248` at the recorded design point;
the status of that measurement is the one carried by `serialFounderCeilingFst`,
which this only instantiates and does not strengthen.

    Empirical status: DERIVED. An instantiation of `serialFounderCeilingFst` at
    the chain's own fields, with no free parameter of its own. That definition
    is MEASURED at one design point and its power is NOT established -- a single
    configuration cannot reject a wrong functional form -- and instantiating it
    here does not improve that standing. -/
noncomputable def ceilingFst (ancestralEpoch : ℝ) : ℝ :=
  serialFounderCeilingFst C.demeSize C.ancestralSize ancestralEpoch C.ceiling

/-- The chain's ceiling `F_ST` is a genuine variance ratio: in `[0, 1)` whenever
the ceiling is nonnegative and the within-deme time is positive. Both hypotheses
are needed and neither is automatic -- `demeSize = 0` sends the within-deme time
to the junk branch named at
`serialFounderWithinTime_at_zero_size_is_junk`. -/
theorem ceilingFst_mem_Ico (ancestralEpoch : ℝ) (hceiling : 0 ≤ C.ceiling)
    (hwithin : 0 < C.withinTime ancestralEpoch) :
    C.ceilingFst ancestralEpoch ∈ Set.Ico (0 : ℝ) 1 := by
  refine ⟨serialFounderCeilingFst_nonneg _ _ _ _ hceiling ?_,
    serialFounderCeilingFst_lt_one _ _ _ _ hceiling ?_⟩ <;> exact hwithin

/-- **The approach is not a function of the closed-form fields.** Two chains can
agree on every field that has a closed form -- deme count, both sizes, migration,
the split schedule, the founder offset, the ceiling, and both audit flags -- and
still disagree on `separationStep`.

This is the module's thesis stated where it can be checked. The header argues
that the meeting problem is time-inhomogeneous and that no algebraic function of
`k` can supply the approach; the corresponding formal fact is that the approach
is genuinely extra information, so a chain cannot be reconstructed from its
demographic parameters. Without it, `separationStep` is a field nothing reads,
and the claim that it is irreducible rests on prose alone. -/
theorem separationStep_not_determined_by_closedForm_fields :
    ∃ C₁ C₂ : SerialFounderChain,
      C₁.demeCount = C₂.demeCount ∧ C₁.demeSize = C₂.demeSize ∧
        C₁.ancestralSize = C₂.ancestralSize ∧ C₁.migration = C₂.migration ∧
        C₁.splitStep = C₂.splitStep ∧ C₁.founderOffset = C₂.founderOffset ∧
        C₁.ceiling = C₂.ceiling ∧ C₁.ceilingValidated = C₂.ceilingValidated ∧
        C₁.approachOpen = C₂.approachOpen ∧
        C₁.separationStep ≠ C₂.separationStep := by
  refine ⟨{ demeCount := 0, demeSize := 0, ancestralSize := 0, migration := 0,
            splitStep := 0, founderOffset := 0,
            separationStep := fun _ separation ↦ separation,
            ceiling := 0, ceilingValidated := false, approachOpen := true },
          { demeCount := 0, demeSize := 0, ancestralSize := 0, migration := 0,
            splitStep := 0, founderOffset := 0,
            separationStep := fun _ _ ↦ fun _ ↦ 0,
            ceiling := 0, ceilingValidated := false, approachOpen := true },
          rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  intro hstep
  have hpoint := congrFun (congrFun (congrFun hstep 0) (fun _ ↦ (1 : ℝ))) 0
  norm_num at hpoint

end SerialFounderChain

/-- **All three twos in the serial-founder within-deme time are coalescent time scales.**
A pair either coalesces inside the chain, on the scale `Descent.Core.coalescentTimeScale N`, or survives
into the ancestral population and waits a further `Descent.Core.coalescentTimeScale Nanc`. Three literal
twos in one body is exactly the shape in which one of them gets changed alone.

There is no `tAnc` term, and that absence is the whole content of the correction this
body carries. Conditional on surviving to `tAnc` the pair waits `tAnc + 2 Nanc`, so the
survival branch does look like it should contribute one; but the coalesce-early branch is
a PARTIAL expectation, `∫₀^tAnc t (1/2N) e^{-t/2N} dt = 2N (1 - e^{-a}) - tAnc e^{-a}`,
whose `- tAnc e^{-a}` cancels it exactly. Writing `2N (1 - e^{-a})` for the early branch
and `e^{-a} (tAnc + 2 Nanc)` for the late one counts `tAnc e^{-a}` once too often, which
is what this body used to do. -/
theorem serialFounderWithinTime_uses_coalescentTimeScale (N Nanc tAnc : ℝ) :
    PopGen.serialFounderWithinTime N Nanc tAnc
      = Descent.Core.coalescentTimeScale N * (1 - Real.exp (-tAnc / Descent.Core.coalescentTimeScale N))
          + Real.exp (-tAnc / Descent.Core.coalescentTimeScale N) * Descent.Core.coalescentTimeScale Nanc := by
  unfold PopGen.serialFounderWithinTime Descent.Core.coalescentTimeScale Descent.Core.ploidy; ring

end Descent.PopGen
