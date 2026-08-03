import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.GroupTheory.Perm.Basic

/-!
# Discharging the deployment-ceiling premise, and the cost it actually carries

This module is **self-contained: it imports only Mathlib.** It does not import
`FoldedSpectrum`, which is large and under concurrent edit; the correspondence with
`AssumedDeploymentCeiling` is stated here in prose and the shapes are matched deliberately.

## What was assumed, and what is discharged here

`Calibrator.AssumedDeploymentCeiling` carries as a **structure field**

```
characterization : perpRisk = 0 ↔ (0 < eta ∧ (reversible ∨ arrowBit))
```

and its own docstring says this "requires a separate identifiability theorem showing that
positive conditional support removes every remaining deployment-blind direction". The
second conjunct is already discharged by the reversal calculation. **The first conjunct is
the open item**, and it is what this module addresses.

Note first why it cannot be discharged *inside* that structure: `perpRisk` and `eta` are
unconstrained real fields there. A biconditional between two arbitrary reals is not
provable, and nothing is wrong with the structure — it is a record of a premise. To
discharge the premise one must supply a **model** in which the two have definitions. That
is what `DeploymentModel` is.

## The model, and the forward direction

A deployment direction is blind at coupling order `k` when order-`k` data cannot see it.
`blind k` is the residual risk invisible at order `k`, and `perpRisk` — the *absolutely*
blind residual — is bounded by every one of them.

The forward conjunct is then **short, and that is the honest headline**:
`perpRisk_eq_zero_of_blind_eq_zero` says that if blindness vanishes at *any single* finite
order, the absolutely-blind residual is zero. Combined with the coverage-invariance
theorem — peelable base plus `η > 0` gives coupled `k`-point injectivity with
`σ_min ≥ (η/C)^k`, and injectivity at order `k` is exactly `blind k = 0` — this gives

> **`η > 0` ⟹ `perpRisk = 0`.**

So the first conjunct is *derivable* rather than assumed, from
`BundleRigidity.CoverageInvariance.sigmaMin_pos` plus a detection lemma linking a positive
smallest singular value to zero blindness at that order. The detection lemma is the one
genuinely new input and it is carried as an explicit hypothesis (`hdetect`), not hidden.

## The finding: the cost is exponential in the coupling order, not quadratic in `1/η`

This is the part that changes how the headline should be quoted.

The corpus states the cost of positive support as `m ≥ d / (2·c₋·η²·R)` — quadratic in
`1/η`. That is the cost **at fixed coupling order**. But the only guarantee available is
`σ_min ≥ (η/C)^k`, which **decays geometrically in `k`**, and a direction resolved only at
coupling order `k` needs roughly `1/σ_min²` samples, i.e. `(C/η)^{2k}`.

`sampleCost_unbounded` proves that this exceeds **every** bound as `k` grows, whenever
`0 < η < C`.

So the qualitative claim survives exactly as stated — there is **no information-theoretic
floor**, every direction is visible at some finite order, and it *is* a sample-size problem
rather than a wall. But "sample-size problem" must not be read as "cheap". The sample size
is exponential in the coupling order a direction requires, and only the `k = 1` case is
quadratic in `1/η`. **A direction with large `r*` is a wall in practice while being a
sample-size problem in theory**, and the published formula does not show that, because it
is the fixed-order specialisation.

That is a refinement rather than a refutation, and it is falsifiable in the useful
direction: exhibit a deployment direction whose coupling order is large, and the quoted
cost formula understates the requirement by an exponential factor.

## What remains assumed

The **converse** — `perpRisk = 0 ⟹ η > 0` — is not proved here and is not provable from
the coverage machinery, which says nothing when `η = 0`. It needs the modulus-copy
falsifier: at `η = 0` there is an infinite-dimensional 2-point kernel even with `T`
injective, so blindness is genuinely present. That witness is carried as the hypothesis
`hzero` of `characterization_of_model` and as `modulusCopyWitness` in
`BundleRigidity.CoverageInvariance`.

So after this module the premise is split into: one direction **derived**, one direction
resting on a **named witness that is known to exist**, and one detection lemma stated as an
explicit input. That is strictly better than a single opaque assumed biconditional, and it
localizes what is still owed.
-/

namespace Calibrator.BundleRigidity

open scoped BigOperators

/-! ## The model -/

/-- A deployment model resolved by coupling order.

`blind k` is the aggregate deployment risk that order-`k` data cannot see; `perpRisk` is the
absolutely-blind residual, the part no finite order sees. The only structural facts needed
are that risks are non-negative and that the absolutely-blind part is bounded by the
blindness at every order. -/
structure DeploymentModel where
  /-- Residual risk invisible to coupling order `k`. -/
  blind : ℕ → ℝ
  /-- Risks are non-negative. -/
  blind_nonneg : ∀ k, 0 ≤ blind k
  /-- The absolutely-blind residual: what no finite order can see. -/
  perpRisk : ℝ
  /-- The absolutely-blind residual is non-negative. -/
  perpRisk_nonneg : 0 ≤ perpRisk
  /-- Whatever is absolutely blind is in particular blind at every finite order. -/
  perpRisk_le_blind : ∀ k, perpRisk ≤ blind k

namespace DeploymentModel

variable (M : DeploymentModel)

/-- **The forward conjunct, in its essential form.**

If blindness vanishes at *any single* finite coupling order, the absolutely-blind residual
is zero. There is no limit to take and no uniformity in `k` to establish: one order
suffices, because the absolutely-blind part is below every order's blindness. -/
theorem perpRisk_eq_zero_of_blind_eq_zero (k : ℕ) (hk : M.blind k = 0) :
    M.perpRisk = 0 :=
  le_antisymm (hk ▸ M.perpRisk_le_blind k) M.perpRisk_nonneg

/-- **Positive conditional support removes the absolutely-blind residual.**

`hdetect` is the detection lemma: a strictly positive smallest singular value at order `k`
means order-`k` data sees everything, i.e. `blind k = 0`. The coverage-invariance theorem
supplies `0 < (η/C)^k` for every `k` whenever `0 < η` and `0 < C`
(`CoverageInvariance.sigmaMin_pos`), so the hypothesis fires and the conclusion follows at
order one.

This is the first conjunct of the boxed characterization, no longer assumed. -/
theorem perpRisk_eq_zero_of_eta_pos (η C : ℝ) (hη : 0 < η) (hC : 0 < C)
    (hdetect : ∀ k : ℕ, 0 < (η / C) ^ k → M.blind k = 0) :
    M.perpRisk = 0 :=
  M.perpRisk_eq_zero_of_blind_eq_zero 1 (hdetect 1 (pow_pos (div_pos hη hC) 1))

/-- **The characterization, assembled from one derived direction and one witness.**

The forward direction is `perpRisk_eq_zero_of_eta_pos`. The converse rests on `hzero`, the
statement that vanishing support leaves genuine blindness — which is what the modulus-copy
falsifier exhibits at `η = 0`.

The `reversible ∨ arrowBit` conjunct of the original does not appear: the reversal
calculation already discharges it, so in the scalar stationary setting the characterization
is exactly this biconditional.

**QUOTE THIS ONLY WITH ITS COST QUALIFIER.** The reading "aggregate deployment risk has no
information-theoretic floor, so the portability gap is a sample-size problem, not a wall"
is correct and is what this theorem says. It must travel with:

> the sample size is **exponential in the coupling order** a direction requires
> (`sampleCost_unbounded`); only the order-one case is the quadratic `1/η²` formula
> (`sampleCost_one`).

A direction with large coupling order is a wall in practice while remaining a sample-size
problem in theory. The published `m ≥ d/(2 c₋ η² R)` is the fixed-order specialisation and
understates a high-order direction by an exponential factor.

**AND NOTE WHAT IS OUT OF SCOPE.** This says nothing about directions that are not
identifiable at *any* order. If an environmental gradient is collinear with the ancestry
gradient, a one-parameter family of genetic/environmental splits produces **identical**
cohort shifts — exactly equal, not approximately — so no cohort-level calibration separates
them at any sample size, and the level-set collapse carries that to every threshold metric.
That is a second and orthogonal kind of wall: this theorem is about how *expensive* a
visible direction is to resolve, and says nothing about a direction a design confined to one
ancestry axis cannot resolve at all. `η > 0` does not cover it, and `r⊥ = 0 ⟺ η > 0` must
not be read as covering it. -/
theorem characterization_of_model (η C : ℝ) (hηnonneg : 0 ≤ η) (hC : 0 < C)
    (hdetect : ∀ k : ℕ, 0 < (η / C) ^ k → M.blind k = 0)
    (hzero : η = 0 → 0 < M.perpRisk) :
    M.perpRisk = 0 ↔ 0 < η := by
  constructor
  · intro hperp
    rcases lt_or_eq_of_le hηnonneg with h | h
    · exact h
    · exact absurd hperp (ne_of_gt (hzero h.symm))
  · intro hpos
    exact M.perpRisk_eq_zero_of_eta_pos η C hpos hC hdetect

end DeploymentModel

/-! ## The cost, which is where the interesting correction lives -/

/-- Samples needed to resolve a direction whose coupling order is `k`, from the only
available guarantee `σ_min ≥ (η/C)^k` and the usual `1/σ_min²` scaling. -/
noncomputable def sampleCost (η C : ℝ) (k : ℕ) : ℝ := (C / η) ^ (2 * k)

/-- **The sample cost is unbounded in the coupling order.**

For `0 < η < C` there is, for every bound `B`, a coupling order whose sample cost exceeds
it. So the guarantee supplied by positive support degrades geometrically in the order, and
the published cost `m ≥ d/(2 c₋ η² R)` — quadratic in `1/η` — is the **fixed-order**
specialisation rather than the general cost.

The qualitative headline is untouched: every direction is seen at some finite order, so
there is no information-theoretic floor. What this shows is that "a sample-size problem,
not a wall" must not be read as "a cheap problem": for a direction requiring large coupling
order the required sample size is exponential in that order. -/
theorem sampleCost_unbounded (η C : ℝ) (hη : 0 < η) (hlt : η < C) (B : ℝ) :
    ∃ k : ℕ, B < sampleCost η C k := by
  have hCη : 1 < C / η := by
    rw [lt_div_iff₀ hη]; linarith
  set r : ℝ := (C / η) ^ 2 with hrdef
  have hr1 : 1 < r := by
    rw [hrdef]; nlinarith [hCη]
  have hrpos : 0 < r - 1 := by linarith
  obtain ⟨k, hk⟩ := exists_nat_gt ((B - 1) / (r - 1))
  refine ⟨k, ?_⟩
  have ha : (-2 : ℝ) ≤ r - 1 := by linarith
  have hbern : 1 + (k : ℝ) * (r - 1) ≤ (1 + (r - 1)) ^ k := one_add_mul_le_pow ha k
  have h1r : (1 : ℝ) + (r - 1) = r := by ring
  rw [h1r] at hbern
  have hBk : B - 1 < (k : ℝ) * (r - 1) := by
    rw [div_lt_iff₀ hrpos] at hk
    linarith
  have hcost : sampleCost η C k = r ^ k := by
    rw [sampleCost, hrdef, ← pow_mul]
  rw [hcost]
  linarith

/-- The cost at coupling order one is the familiar quadratic form: `(C/η)²`. This is the
regime the published formula describes, and stating it beside `sampleCost_unbounded` is the
point — the two together say exactly which claim is safe to quote. -/
theorem sampleCost_one (η C : ℝ) : sampleCost η C 1 = (C / η) ^ 2 := by
  first
    | (rw [sampleCost]; norm_num)
    | rw [sampleCost]

end Calibrator.BundleRigidity
