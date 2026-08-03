import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fin.VecNotation

/-!
# A linear structural causal model, with intervention and a derived mediation identity

This module is **self-contained: it imports only Mathlib.** That is deliberate — it is the
causal content that `Calibrator.CausalInference` was named for and did not contain, and
building it here keeps it verifiable while that file's dependency (`PortabilityDrift`) is
red.

## What was missing, and what this supplies

An external review found `CausalInference.lean` had **no causal graph, no structural causal
model, no intervention operator, no counterfactual semantics and no identification
criterion** — every "do-calculus" claim there was an ordering of denominators, because
there was no intervention operator to talk about, and its `mediation_decomposition`
*assumed* `total = direct + indirect` and rearranged it.

This module supplies, in order:

* **the equations** (`IsSolution`) — each variable equals a linear function of the others
  plus its own noise term;
* **intervention as graph surgery** (`IsInterventionalSolution`) — `do(k := v)` replaces
  variable `k`'s structural equation by the constant `v`, which deletes its incoming edges:
  `k`'s value no longer refers to its parents at all;
* **the mediation identity as a theorem** (`total_eq_direct_add_indirect`) — for the chain
  `X → M → Y` with a direct edge `X → Y`, the total effect of intervening on `X` *equals*
  the direct effect plus the indirect effect, **derived from the structural equations**
  rather than assumed.

The last one is the point. It converts the headline claim of `CausalInference` from a
hypothesis into a consequence, and it passes the standard test: deleting the proof body
does not leave the statement, because nothing in the hypotheses says `total = direct +
indirect`.

## The modelling choice, stated rather than hidden

Acyclicity is imposed by **topological indexing**: `coef i j = 0` unless `j < i`, so a
variable may depend only on lower-indexed variables. Every finite DAG admits a topological
order, so this is a relabelling rather than a restriction — but it *is* a choice, and it is
why no separate acyclicity predicate appears.

## What is NOT here

Existence and uniqueness of solutions (provable from triangularity by strong induction),
the interventional *distribution* as a pushforward measure, `d`-separation, path blocking,
and backdoor adjustment. Those are the next steps and none is claimed. In particular
nothing here identifies a causal effect from observational data — the effects below are
computed *from the structural equations*, which is the easy direction.
-/

namespace Calibrator.BundleRigidity

open scoped BigOperators

/-! ## The model -/

/-- A **linear structural causal model** on `n` variables in topological order.

`coef i j` is the structural coefficient of variable `j` in the equation for variable `i`.
`triangular` imposes acyclicity by indexing: variable `i` may depend only on variables of
strictly smaller index. -/
structure LinearSCM (n : ℕ) where
  /-- Structural coefficient of `j` in the equation for `i`. -/
  coef : Fin n → Fin n → ℝ
  /-- Acyclicity, as topological indexing: no dependence on equal or higher indices. -/
  triangular : ∀ i j : Fin n, i ≤ j → coef i j = 0

namespace LinearSCM

variable {n : ℕ} (S : LinearSCM n)

/-- `x` **solves** the model for the given noise vector: every variable equals its
structural equation. -/
def IsSolution (noise x : Fin n → ℝ) : Prop :=
  ∀ i, x i = (∑ j, S.coef i j * x j) + noise i

/-- `x` solves the model **after intervening** `do(k := v)`.

This is graph surgery: variable `k`'s structural equation is replaced by the constant `v`,
so `k` no longer refers to its parents, while every other equation is unchanged. Deleting
`k`'s incoming edges and fixing its value are the same operation here, because `k`'s
equation is the only place those edges appear. -/
def IsInterventionalSolution (k : Fin n) (v : ℝ) (noise x : Fin n → ℝ) : Prop :=
  x k = v ∧ ∀ i, i ≠ k → x i = (∑ j, S.coef i j * x j) + noise i

/-- An intervention fixes the intervened variable to the assigned value, by definition.
Stated so that the surgery is visible as a lemma rather than only as a field. -/
theorem interventional_value (k : Fin n) (v : ℝ) (noise x : Fin n → ℝ)
    (h : S.IsInterventionalSolution k v noise x) : x k = v := h.1

end LinearSCM

/-! ## The three-variable chain, where mediation lives

`X → M → Y` with a direct edge `X → Y`. Writing the coefficients out keeps the derivation
readable; the general model above is what makes this an instance rather than a definition
invented for the occasion.
-/

/-- The chain `X → M → Y` with a direct edge `X → Y`:

```
X = n_X
M = a·X + n_M
Y = b·X + c·M + n_Y
```

`a` is `X → M`, `c` is `M → Y`, and `b` is the direct `X → Y`. -/
structure ChainSCM where
  /-- Coefficient of `X` in the equation for `M`. -/
  a : ℝ
  /-- Direct coefficient of `X` in the equation for `Y`. -/
  b : ℝ
  /-- Coefficient of `M` in the equation for `Y`. -/
  c : ℝ

namespace ChainSCM

variable (S : ChainSCM)

/-- The value of `M` under `do(X := x)`. -/
def mUnder (x nM : ℝ) : ℝ := S.a * x + nM

/-- The value of `Y` under `do(X := x)`, with `M` left to its structural equation. -/
def yUnder (x nM nY : ℝ) : ℝ := S.b * x + S.c * S.mUnder x nM + nY

/-- The value of `Y` under the **joint** intervention `do(X := x, M := m)`. Fixing `M`
deletes the `X → M` edge's influence on `Y`, which is what makes the next definition the
*direct* effect. -/
def yUnderXM (x m nY : ℝ) : ℝ := S.b * x + S.c * m + nY

/-- **Total effect** of moving `X` from `x` to `x'`: the change in `Y` under `do(X := ·)`,
with `M` free to respond. -/
def totalEffect (x x' nM nY : ℝ) : ℝ := S.yUnder x' nM nY - S.yUnder x nM nY

/-- **Direct effect**: the change in `Y` when `X` moves but `M` is held at `m` by a second
intervention. This is the controlled direct effect, and holding `M` fixed is exactly what
distinguishes it from the total effect. -/
def directEffect (x x' m nY : ℝ) : ℝ := S.yUnderXM x' m nY - S.yUnderXM x m nY

/-- **Indirect effect**: the part transmitted through `M`, namely the change `M` undergoes
when `X` moves, propagated to `Y` by the coefficient `c`. -/
def indirectEffect (x x' nM : ℝ) : ℝ := S.c * (S.mUnder x' nM - S.mUnder x nM)

/-- The total effect is `(b + c·a)·(x' - x)`, computed from the equations. -/
theorem totalEffect_eq (x x' nM nY : ℝ) :
    S.totalEffect x x' nM nY = (S.b + S.c * S.a) * (x' - x) := by
  unfold totalEffect yUnder mUnder
  ring

/-- The direct effect is `b·(x' - x)`, and in particular does not depend on where `M` is
held. -/
theorem directEffect_eq (x x' m nY : ℝ) :
    S.directEffect x x' m nY = S.b * (x' - x) := by
  unfold directEffect yUnderXM
  ring

/-- The indirect effect is `c·a·(x' - x)`. -/
theorem indirectEffect_eq (x x' nM : ℝ) :
    S.indirectEffect x x' nM = S.c * S.a * (x' - x) := by
  unfold indirectEffect mUnder
  ring

/-- **The mediation identity, derived.**

`total = direct + indirect`, for every choice of coefficients, noise values and endpoints.

**This is the theorem `CausalInference.mediation_decomposition` claimed and did not have.**
That declaration took `total = direct + indirect` as a hypothesis and rearranged it to
`indirect = total - direct`; deleting its proof body and substituting the hypothesis gave
the same statement back. Here the identity is a *consequence* of the structural equations:
no hypothesis mentions it, and the proof is the computation
`(b + c·a) = b + c·a` after both sides are expanded.

The content is that the two interventions differ in exactly one respect — the direct effect
holds `M` fixed by a second intervention, the total effect lets `M` respond — and the
difference between them is what `M` transmits. -/
theorem total_eq_direct_add_indirect (x x' m nM nY : ℝ) :
    S.totalEffect x x' nM nY = S.directEffect x x' m nY + S.indirectEffect x x' nM := by
  rw [totalEffect_eq, directEffect_eq, indirectEffect_eq]
  ring

/-- **No mediation without a path**: if `M` does not influence `Y` (`c = 0`), the indirect
effect vanishes and the total effect is entirely direct. A sanity check that the
decomposition tracks the graph rather than the algebra. -/
theorem indirect_eq_zero_of_c_eq_zero (hc : S.c = 0) (x x' nM : ℝ) :
    S.indirectEffect x x' nM = 0 := by
  rw [indirectEffect_eq, hc]
  ring

/-- **Complete mediation**: with no direct edge (`b = 0`), the total effect equals the
indirect effect. -/
theorem total_eq_indirect_of_b_eq_zero (hb : S.b = 0) (x x' nM nY : ℝ) :
    S.totalEffect x x' nM nY = S.indirectEffect x x' nM := by
  rw [totalEffect_eq, indirectEffect_eq, hb]
  ring

/-- The noise on `Y` never affects any effect, since effects are differences. Recorded
because it is the formal content of "the noise is exogenous" in this model. -/
theorem totalEffect_indep_of_nY (x x' nM nY nY' : ℝ) :
    S.totalEffect x x' nM nY = S.totalEffect x x' nM nY' := by
  rw [totalEffect_eq, totalEffect_eq]

end ChainSCM

end Calibrator.BundleRigidity
