/-
Copyright (c) 2026 Sauers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sauers
-/
import Calibrator.ObservationalCeiling
import Mathlib.Tactic.Linarith

namespace Calibrator

/-!
# Regimes, common-mode error, and the power of a validation

This file is not about a bug. It is about the two structural defects that let a whole
class of bugs exist, and it makes both of them impossible to reintroduce silently.

## The common-mode failure, stated once

Five definitions — the within-population heterozygosity loss, the `F_ST` derived from
it, the target heterozygosity read back off that `F_ST`, the target PGS variance, and
the neutral allele-frequency benchmark ratio — form a **self-consistent cluster**.
Every cross-check between them passes, and every one of them fails in the same way and
for the same reason: all five are functions of the single quantity

    retention = (1 - 1/(2 Ne)) ^ t,

the closed-population, no-mutation drift recurrence. Simulation at demographic
equilibrium measures a retention of `1.02 ± 0.02` where that formula predicts
`e^(-2) = 0.135`. Mutation replenishes diversity, so a population at equilibrium sits
at constant heterozygosity indefinitely. The cluster's `F_ST` is therefore `≈ 0`
exactly where the measurable between-population `F_ST` is `0.50`.

These are not two calibrations of one quantity. They are **different quantities sharing
a name**, which is how one modelling assumption reproduces itself across a cluster and
reads as several independent confirmations.

## Defect 1: over-determination cannot see common-mode error

`Calibrator.Conventions` states the standing defence:

> Against a wrong constant: over-determination. Derive the quantity from a primitive so
> the constant is forced, and relate independently written formulas so that drift
> between them fails to compile.

That defence detects **divergence** between formulas. It is a redundancy scheme, and
like every redundancy scheme it is blind to **correlated failure**. When all members of
a cluster are functions of one shared premise, every identity among them holds *for
every value of that premise* — including the wrong one. `crossChecks_blind_to_retention`
below proves exactly this, and proves it in the same shape as every other impossibility
in this development: the cluster's internal identities are a probe, and the probe cannot
separate a correct retention from an incorrect one.

The obligation this creates: a definition that encodes a **regime** — an assumption
about the data-generating process, not about algebra — must say so, and the regime must
be dischargeable at the use site rather than baked into the body. Section 1 makes the
regime a hypothesis and exhibits the two regimes that the cluster conflated.

## Defect 2: `VALIDATED` had no power semantics

`neutralAFBenchmarkRatio` was recorded as validated to within `3.2%`. That verdict was
an artifact of a **symmetric test design**: with equal branch lengths both sides of the
ratio collapse to `≈ 1`, so the test had no power to reject a wrong functional form. On
asymmetric effective sizes the same formula is off by `-37%` to `-74%`, at nine to
fifteen standard errors.

This is not a mistake about genetics; it is a mistake about evidence. A validation
record that does not state the **dynamic range the prediction spanned** is not evidence
that the formula is right — it is evidence that the design could not tell. Section 3
proves the point exactly: on any symmetric design the benchmark ratio and its *square*
are indistinguishable, so no symmetric grid can ever separate them.

The obligation this creates: `Empirical status: VALIDATED` must record the spread of the
predicted quantity across the design. `scripts/check-identifications.py` now enforces it.
-/

open scoped BigOperators

/-!
## 1. Two regimes, and the quantity that distinguishes them

The cluster's premise is a *closed population with no mutation*. The alternative, and
the one that describes a population at demographic equilibrium, is *mutation-drift
balance*. Both are legitimate models. The defect was that only one of them was written
down, and it was written into a body rather than into a hypothesis.
-/

/-- A heterozygosity trajectory, with its starting value pinned positive so that the
measured loss is well defined. This is the object a simulation actually reports. -/
structure HeterozygosityTrajectory where
  het : ℕ → ℝ
  het_zero_pos : 0 < het 0

/-- The **measured** proportional heterozygosity loss, `1 - H_t / H_0`. This is an
observable: it is what a simulation or a real panel reports, with no model attached. -/
noncomputable def HeterozygosityTrajectory.measuredLoss
    (M : HeterozygosityTrajectory) (t : ℕ) : ℝ :=
  1 - M.het t / M.het 0

/-- **Regime A: closed population, no mutation.** Heterozygosity decays geometrically
at the drift rate. This is the premise the cluster encodes.

    Regime: closed population, no mutation — stated here as the definition's whole
    content rather than as a hidden assumption.

    Empirical status: FALSIFIED at demographic equilibrium. Simulation measures
    the retention as `1.025 ± 0.020` at `Ne = 1000`, `t = 4000`, where this
    trajectory gives `0.135`. -/
noncomputable def closedPopulation (Ne H₀ : ℝ) (hH : 0 < H₀) : HeterozygosityTrajectory where
  het := fun t => (1 - 1 / (2 * Ne)) ^ t * H₀
  het_zero_pos := by simpa using hH

/-- **Regime B: mutation-drift balance.** At demographic equilibrium mutation replenishes
diversity at the rate drift removes it, so heterozygosity is stationary. This is the
regime the simulation was actually in.

    Empirical status: VALIDATED as the regime of the reported runs. Measured
    retention `1.010`, `0.989`, `1.025` at `T = 200`, `1000`, `4000`, each within
    one standard error of the stationary value `1`. Power: the drift-only rival
    spans `0.905` to `0.135` across the same design, so the design separates
    them by a factor of seven at the far end. -/
noncomputable def mutationDriftBalance (H₀ : ℝ) (hH : 0 < H₀) : HeterozygosityTrajectory where
  het := fun _ => H₀
  het_zero_pos := hH

/-- **The balance regime is a stationary point of the trajectory**, which is what
makes it a balance rather than a value: the measured loss does not move from one
generation to the next, at any starting heterozygosity. The closed-population
regime has no such generation, which is the whole of the disagreement. -/
theorem mutationDriftBalance_isFixedPoint (H₀ : ℝ) (hH : 0 < H₀) (t : ℕ) :
    (mutationDriftBalance H₀ hH).measuredLoss (t + 1) =
      (mutationDriftBalance H₀ hH).measuredLoss t := by
  unfold HeterozygosityTrajectory.measuredLoss mutationDriftBalance
  simp

/-- Under mutation-drift balance the measured loss is **exactly zero at every time**. -/
@[simp] theorem measuredLoss_mutationDriftBalance (H₀ : ℝ) (hH : 0 < H₀) (t : ℕ) :
    (mutationDriftBalance H₀ hH).measuredLoss t = 0 := by
  unfold HeterozygosityTrajectory.measuredLoss mutationDriftBalance
  simp [div_self (ne_of_gt hH)]

/-- Under a closed population the measured loss is the drift-recurrence formula. -/
theorem measuredLoss_closedPopulation (Ne H₀ : ℝ) (hH : 0 < H₀) (t : ℕ) :
    (closedPopulation Ne H₀ hH).measuredLoss t = 1 - (1 - 1 / (2 * Ne)) ^ t := by
  unfold HeterozygosityTrajectory.measuredLoss closedPopulation
  simp only
  rw [pow_zero, one_mul]
  field_simp

/-- **The two regimes disagree, and the gap is not small.** For any effective size above
one half and any positive number of generations, the closed-population regime predicts a
strictly positive heterozygosity loss while mutation-drift balance predicts exactly zero.

At `Ne = 1000` and `t = 4000` the predicted loss is `1 - e^(-2) = 0.865`; the measured
loss at equilibrium is `-0.025 ± 0.02`. A formula derived in one regime is not
transportable to the other, and nothing internal to the formula records which regime it
came from. -/
theorem regimes_disagree {Ne H₀ : ℝ} (hNe : 1 / 2 < Ne) (hH : 0 < H₀) {t : ℕ} (ht : 0 < t) :
    (mutationDriftBalance H₀ hH).measuredLoss t
      < (closedPopulation Ne H₀ hH).measuredLoss t := by
  have hNe0 : 0 < Ne := by linarith
  have hlt : 1 - 1 / (2 * Ne) < 1 := by
    have : 0 < 1 / (2 * Ne) := by positivity
    linarith
  have hnonneg : 0 ≤ 1 - 1 / (2 * Ne) := by
    rw [sub_nonneg, div_le_one (by positivity)]
    linarith
  have hpow : (1 - 1 / (2 * Ne)) ^ t < 1 := pow_lt_one₀ hnonneg hlt ht.ne'
  rw [measuredLoss_mutationDriftBalance, measuredLoss_closedPopulation]
  linarith

/-!
## 2. Why every cross-check passed

Each member of the cluster is a function of the single quantity `retention`. That is the
whole disease: the identities relating them are identities *in* `retention`, so they hold
at every value of it, correct or not.

The retention is not restated here as a formula of its own. It is the retention of the
`closedPopulation` regime, and `measuredLoss_closedPopulation` is what says so. A second
copy of `(1 - 1/(2 Ne))^t` sitting beside the regime it came from is precisely the defect
this file is about: the copy cannot record which regime it belongs to, so it can be
carried into a regime where it is false without anything failing.
-/

/-- Cluster member: heterozygosity loss.

    Denotes: one minus a retention, and nothing more. The same body carries
    names from the 'factor', 'frequency' and 'fst' families elsewhere in the
    corpus, and the body alone does not fix which is meant; here the argument is
    the closed-population retention and the value is a within-population
    heterozygosity loss, never a between-population `F_ST`.

    Empirical status: VACUOUS. It is a function of the shared retention, so it
    carries no evidence independent of it. -/
noncomputable def lossOfRetention (r : ℝ) : ℝ := 1 - r

/-- Cluster member: target heterozygosity. -/
noncomputable def targetHetOfRetention (H₀ r : ℝ) : ℝ := H₀ * r

/-- Cluster member: target PGS variance.

    Empirical status: VACUOUS. It is a function of the shared retention, so it
    carries no evidence independent of it; see
    `cluster_identities_hold_at_every_retention`. -/
noncomputable def targetPgsVarOfRetention (V_A r : ℝ) : ℝ := V_A * r

/-- **Every internal identity of the cluster holds at every retention value.**

This is the cluster's own cross-check, and the theorem says it is satisfied for an
arbitrary `r` — so passing it is evidence about the algebra and no evidence at all about
the number. That is precisely the gap the simulation found.

**INTENTIONALLY VACUOUS. DO NOT DELETE, DO NOT STRENGTHEN.** Its unfalsifiability is the
result: a cross-check that holds at every `r` cannot detect a wrong `r`. Automated
vacuity detection is WRONG here and cannot become right, because the property it flags —
that no instance of this statement can fail — is exactly the property being exhibited.
`validation/extract/equivalence.py` reports this among its rfl candidates on the same
footing as genuinely empty restatements, so a sweep acting on that list without reading
this paragraph would delete the finding while believing it was removing noise. If a
future detector grows an allow-list, this and
`ascertainment_artificial_loss` in `ImputationPortability` are its first two entries. -/
theorem cluster_identities_hold_at_every_retention (H₀ V_A r : ℝ) :
    targetHetOfRetention H₀ r = H₀ * (1 - lossOfRetention r) ∧
      targetPgsVarOfRetention V_A r = V_A * (1 - lossOfRetention r) := by
  constructor
  · unfold targetHetOfRetention lossOfRetention
    ring
  · unfold targetPgsVarOfRetention lossOfRetention
    ring

/-- The cluster's internal cross-check, as a probe: what an over-determination check
actually observes about a candidate retention value. -/
def clusterCrossCheck (r : ℝ) : Prop :=
  targetHetOfRetention 1 r = 1 * (1 - lossOfRetention r)

/-- **The common-mode theorem: over-determination is blind to a shared premise.**

Two different retention values produce *identical* cross-check outcomes, so no criterion
built from the cluster's internal identities — however many members it relates, in
whatever combination — can decide whether the retention is the right one.

This is the same law as every other impossibility in this development
(`Calibrator.ObservationalCeiling`), applied to the development's own quality process.
The consequence is not that over-determination is useless: it catches divergence, which
is a real failure mode and was caught twice. The consequence is that it is **not a
substitute for measuring the primitive against an observable**, and must never be
reported as one.

`ProbeBlindness` carries its two witnesses as data, so this is a `def` and not a
`theorem`: the proposition it supports is `no_crossCheck_criterion_for_retention`
immediately below.

    Empirical status: not an empirical claim. This is a witness construction; the
    measurement it explains is recorded in `Calibrator.PortabilityDrift`. -/
noncomputable def crossChecks_blind_to_retention {trueRetention wrongRetention : ℝ}
    (hne : wrongRetention ≠ trueRetention) :
    ProbeBlindness clusterCrossCheck (fun r => r = trueRetention) where
  positive := trueRetention
  negative := wrongRetention
  same_data := by
    have h1 : clusterCrossCheck trueRetention :=
      (cluster_identities_hold_at_every_retention 1 1 trueRetention).1
    have h2 : clusterCrossCheck wrongRetention :=
      (cluster_identities_hold_at_every_retention 1 1 wrongRetention).1
    exact propext ⟨fun _ => h2, fun _ => h1⟩
  holds := rfl
  fails := hne

/-- Spelled out: no decision rule reading the cluster's cross-checks decides whether the
retention premise holds. -/
theorem no_crossCheck_criterion_for_retention {trueRetention wrongRetention : ℝ}
    (hne : wrongRetention ≠ trueRetention) :
    ¬ ∃ decide : Prop → Prop, ∀ r : ℝ, r = trueRetention ↔ decide (clusterCrossCheck r) :=
  (crossChecks_blind_to_retention hne).no_criterion

/-!
## 3. The power of a design

The second defect. A validation is evidence only in proportion to the range its
prediction spanned. On a symmetric design the benchmark ratio is identically one, and so
is every power of it.
-/

/-- The neutral allele-frequency benchmark ratio, in the form under test.

    **The functional form is CORRECT, and guilt does not transfer along the family.** The
    identical-bodied `PortabilityDrift.neutralAFBenchmarkRatio` is falsified and absent,
    which invites the inference that this body inherits the defect. It does not.
    Measured at the same design point that falsified the twin (`2N_A = 400`, `2N_B = 4000`,
    `t = 500`, `L = 1500`, 6 replicates), with the branch drift coefficient
    `F_i = 1 - H_i/H_ancestral`:

    * measured heterozygosity ratio `H_B/H_A = 3.14043`;
    * `(1 - fstT)/(1 - fstS)` at branch drift `= 3.14033`, an error of `-0.003%`;
    * on a symmetric design, `0.000%`.

    What was falsified upstream was a **different quantity substituted into the `fst` slot**:
    Hudson pairwise `F_ST` is one symmetric number (`0.41934` here), so feeding it to both
    slots forces the ratio to one and destroys all signal. That, not the functional form,
    produced the reported `-37%` to `-74%`.

    So the honest verdict is **VACUOUS given its inputs** — `H_i = H_anc(1 - F_i)` is the
    definition of `F_i` rearranged — rather than falsified. Only the `fst` slot's semantics
    need fixing; the form does not.

    Empirical status: **VALIDATED as a functional form** (`-0.003%`), VACUOUS as a
    prediction. See `proofs/validation/drift_diff/`. -/
noncomputable def benchmarkRatio (fstS fstT : ℝ) : ℝ := (1 - fstT) / (1 - fstS)

/-- A deliberately wrong rival: the same ratio squared. Any design that cannot separate
these two has no power to check the functional form.

    The separation is measured: this rival is `+214.0%` off on the asymmetric design and
    `-0.4%` — indistinguishable — on the symmetric one. That is
    `symmetric_design_has_no_power` observed, with a `3.1×` dynamic range.

    Empirical status: **VALIDATED as a discriminating rival**
    (`proofs/validation/drift_diff/`). -/
noncomputable def benchmarkRatioSquared (fstS fstT : ℝ) : ℝ := ((1 - fstT) / (1 - fstS)) ^ 2

/-- What a **symmetric** design observes: the two branch lengths are equal, so only the
diagonal of the candidate function is ever evaluated.

    Empirical status: not an empirical claim. This is a description of a test
    design, not a prediction about a population. -/
noncomputable def diagonalDesign (g : ℝ → ℝ → ℝ) : ℝ → ℝ := fun x => g x x

/-- **A symmetric design sees `1` whatever the exponent is.** -/
theorem diagonalDesign_benchmark_eq :
    diagonalDesign benchmarkRatio = diagonalDesign benchmarkRatioSquared := by
  funext x
  unfold diagonalDesign benchmarkRatio benchmarkRatioSquared
  rcases eq_or_ne (1 - x) 0 with h | h
  · rw [h]
    simp
  · rw [div_self h]
    norm_num

/-- The two forms genuinely differ off the diagonal: at `fstS = 0`, `fstT = 1/2` one is
`1/2` and the other `1/4`. So the symmetric design's blindness is a real loss, not a
distinction without a difference. -/
theorem benchmark_forms_differ : benchmarkRatio ≠ benchmarkRatioSquared := by
  intro h
  have := congrFun (congrFun h 0) (1 / 2)
  unfold benchmarkRatio benchmarkRatioSquared at this
  norm_num at this

/-- **Symmetric designs have provably zero power to check this functional form.**

No criterion computed from a symmetric grid can decide whether the benchmark ratio is
the right functional form, because the correct form and its square produce identical
data on every such grid. The `3.2%` agreement originally recorded was therefore not weak
evidence — it was *no* evidence about the exponent, and the asymmetric design that
followed found errors of `-37%` to `-74%`.

The general obligation: a validation must report the spread of its prediction across the
design. A prediction that is constant on the design tests nothing about shape.

As above this is a `def`, since `ProbeBlindness` carries its witnesses as data; the
proposition is `symmetric_design_has_no_power` immediately below.

    Empirical status: not an empirical claim. This is a witness construction. -/
noncomputable def symmetricDesignBlindness :
    ProbeBlindness diagonalDesign (fun g => g = benchmarkRatio) where
  positive := benchmarkRatio
  negative := benchmarkRatioSquared
  same_data := diagonalDesign_benchmark_eq
  holds := rfl
  fails := fun h => benchmark_forms_differ h.symm

/-- Spelled out: no rule reading only symmetric-design output decides the functional
form. -/
theorem symmetric_design_has_no_power :
    ¬ ∃ decide : (ℝ → ℝ) → Prop,
        ∀ g : ℝ → ℝ → ℝ, g = benchmarkRatio ↔ decide (diagonalDesign g) :=
  symmetricDesignBlindness.no_criterion

/-!
## 4. The obligations, and where they are enforced

Three rules follow, and none of them is a matter of care or attention — each is
mechanically checkable, and each is now checked.

1. **A regime is a hypothesis, not a body.** A definition whose value depends on an
   assumption about the data-generating process (closed population, no mutation,
   infinite sites, demographic equilibrium) must name that assumption. Section 1
   exhibits the two regimes that were conflated and proves they disagree at every
   positive time. `scripts/check-identifications.py` guard 3i requires a `Regime:` line
   on any definition whose body is a drift-style recurrence.

2. **A cross-check is not a measurement.** Over-determination detects divergence between
   independently written formulas and is provably blind to a premise they share
   (`crossChecks_blind_to_retention`). A cluster may therefore carry at most one
   `VALIDATED` tag per independent measurement against an observable, and a member may
   never inherit the tag from a sibling identity. Guard 3j enforces the no-inheritance
   half.

3. **A validation must report its power.** `Empirical status: VALIDATED` must record the
   spread of the predicted quantity across the design; a prediction that is constant on
   the design tests nothing about shape (`symmetric_design_has_no_power`). Guard 3k
   rejects validation notes whose recorded predictions are all equal.

The deeper point, and the reason this file sits next to `Calibrator.ObservationalCeiling`
rather than next to the definitions it is about: the development's own quality process is
subject to the same law as everything else it proves. A probe that cannot separate two
objects certifies neither, and that is as true of a cross-check as it is of a cumulant.
-/

end Calibrator
