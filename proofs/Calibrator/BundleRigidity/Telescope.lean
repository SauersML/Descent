/-
Copyright (c) 2026 Sauers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sauers
-/
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
# The telescoping word identity

This module is **self-contained: it imports only Mathlib**.

## The identity

Let `Φ i` be pushforward operators in a ring `R` of operators, let `P i` and `Q i` be
real weights, and let

```
A i  =  Q i • Φ i  +  P i • 1
```

be the associated one-step operators. For a **word** `w = (w₁, …, w_l)` write `P^w` and
`Q^w` for the products of the weights along the word and `Φ_w = Φ_{w₁} ⋯ Φ_{w_l}` for the
composed pushforward, in word order. Then

```
∑_{k=1}^{l} (-1)^{k-1} P^{w_{<k}} A_{w_k} Q^{w_{>k}} Φ_{w_{>k}}
      =  Q^w Φ_w  +  (-1)^{l-1} P^w · 1.
```

## Why it is true

Set `H k = P^{w_{<k}} Q^{w_{≥k}} Φ_{w_{≥k}}`, so that `H 1 = Q^w Φ_w` and
`H (l+1) = P^w · 1`. Substituting `A_{w_k} = Q_{w_k} Φ_{w_k} + P_{w_k}` splits the `k`-th
summand into exactly

```
summand k  =  H k  +  H (k+1),
```

the first piece absorbing `Q_{w_k} Φ_{w_k}` into the suffix and the second absorbing
`P_{w_k}` into the prefix. The alternating sum of `H k + H (k+1)` telescopes, leaving
`H 1 + (-1)^{l-1} H (l+1)`. That is the whole proof: no analysis, no convergence, no
hypothesis on the weights.

## How it is formalized

The alternating sum is defined by the recursion it satisfies,

```
altSum []       = 0
altSum (i :: u) = A i * (Q^u • Φ_u)  -  P i • altSum u,
```

which is the same object: peeling the first letter takes the `k = 1` term out and turns
every later term into `-P i` times the corresponding term for the shorter word. Induction
on the word then proves the identity directly, and the telescoping is what makes the
inductive step close by `ring`-style rewriting alone.

The exponent is written `(-1) ^ (l + 1)` rather than `(-1) ^ (l - 1)`. The two agree for
every `l ≥ 1`, and the former also makes the empty word come out right — both sides are
zero — where truncated natural subtraction would not.

## Attribution

This is a telescoping sum. It is stated here because it is the engine that the
closed-path and Neumann-series arguments run on, and because both of its small cases were
asserted in the source and are worth having as checked lemmas rather than as remarks.
-/

namespace Calibrator.BundleRigidity

variable {ι : Type*} {R : Type*} [Ring R]

/-- The product of the `P`-weights along a word. -/
def prodWeight (P : ι → ℝ) (w : List ι) : ℝ := (w.map P).prod

/-- The composed pushforward along a word, in word order. -/
def prodOp (Φ : ι → R) (w : List ι) : R := (w.map Φ).prod

@[simp] theorem prodWeight_nil (P : ι → ℝ) : prodWeight P ([] : List ι) = 1 := rfl

@[simp] theorem prodWeight_cons (P : ι → ℝ) (i : ι) (u : List ι) :
    prodWeight P (i :: u) = P i * prodWeight P u := rfl

@[simp] theorem prodOp_nil (Φ : ι → R) : prodOp Φ ([] : List ι) = 1 := rfl

@[simp] theorem prodOp_cons (Φ : ι → R) (i : ι) (u : List ι) :
    prodOp Φ (i :: u) = Φ i * prodOp Φ u := rfl

variable [Algebra ℝ R]

/-- **The alternating sum of the identity**, defined by the recursion it satisfies.

Peeling the first letter of the word extracts the `k = 1` term `A i * (Q^u • Φ_u)` and
rescales every later term by `-P i`, which is exactly the recursion below. -/
noncomputable def altSum (P Q : ι → ℝ) (Φ A : ι → R) : List ι → R
  | [] => 0
  | i :: u => A i * (prodWeight Q u • prodOp Φ u) - P i • altSum P Q Φ A u

@[simp] theorem altSum_nil (P Q : ι → ℝ) (Φ A : ι → R) :
    altSum P Q Φ A ([] : List ι) = 0 := rfl

@[simp] theorem altSum_cons (P Q : ι → ℝ) (Φ A : ι → R) (i : ι) (u : List ι) :
    altSum P Q Φ A (i :: u)
      = A i * (prodWeight Q u • prodOp Φ u) - P i • altSum P Q Φ A u := rfl

/-- **Lemma 2: the telescoping word identity.**

```
∑_k (-1)^{k-1} P^{w_{<k}} A_{w_k} Q^{w_{>k}} Φ_{w_{>k}}  =  Q^w Φ_w + (-1)^{l-1} P^w
```

Proved by induction on the word. No hypothesis on the weights: they may be any reals, of
any sign, and nothing is assumed about the operators `Φ` beyond living in a ring. -/
theorem altSum_eq (P Q : ι → ℝ) (Φ A : ι → R)
    (hA : ∀ i, A i = Q i • Φ i + P i • (1 : R)) (w : List ι) :
    altSum P Q Φ A w
      = prodWeight Q w • prodOp Φ w
        + ((-1 : ℝ) ^ (w.length + 1) * prodWeight P w) • (1 : R) := by
  induction w with
  | nil => simp
  | cons i u ih =>
    rw [altSum_cons, ih, hA i]
    have hexpand :
        (Q i • Φ i + P i • (1 : R)) * (prodWeight Q u • prodOp Φ u)
          = (Q i * prodWeight Q u) • (Φ i * prodOp Φ u)
            + (P i * prodWeight Q u) • prodOp Φ u := by
      -- Explicit and ordered, rather than a `simp only` set: each step is named where it
      -- fires, so a failure points at the step that failed instead of silently leaving
      -- the goal untouched for a later tactic to trip over.
      rw [add_mul, smul_mul_assoc, smul_mul_assoc, one_mul, mul_smul_comm, smul_smul,
        smul_smul]
    rw [hexpand]
    have hsplit :
        P i • (prodWeight Q u • prodOp Φ u
            + ((-1 : ℝ) ^ (u.length + 1) * prodWeight P u) • (1 : R))
          = (P i * prodWeight Q u) • prodOp Φ u
            + (P i * ((-1 : ℝ) ^ (u.length + 1) * prodWeight P u)) • (1 : R) := by
      rw [smul_add, smul_smul, smul_smul]
    rw [hsplit]
    rw [prodWeight_cons, prodOp_cons, prodWeight_cons, List.length_cons]
    have hsign : (-1 : ℝ) ^ (u.length + 1 + 1) * (P i * prodWeight P u)
        = -(P i * ((-1 : ℝ) ^ (u.length + 1) * prodWeight P u)) := by
      rw [pow_succ]
      ring
    -- `neg_smul` is not optional here: `abel` reasons additively and does not know that
    -- the real scalar `-Z` acting on `1` is the negation of `Z` acting on `1`. Without
    -- it the two sides differ only by that identity and `abel` reports unsolved goals.
    rw [hsign, neg_smul]
    abel

/-! ## The two small cases, which were asserted in the source and are checked here -/

/-- **Length one.** The identity reduces to the defining relation `A i = Q i Φ i + P i`. -/
theorem altSum_singleton (P Q : ι → ℝ) (Φ A : ι → R)
    (hA : ∀ i, A i = Q i • Φ i + P i • (1 : R)) (i : ι) :
    altSum P Q Φ A [i] = Q i • Φ i + P i • (1 : R) := by
  rw [altSum_cons, altSum_nil, smul_zero, sub_zero, hA i]
  simp [prodWeight, prodOp]

/-- **Length two, the word `i j`.**

`A i (Q j Φ j) - P i A j = Q i Q j Φ i Φ j - P i P j`. The cross terms `P i Q j Φ j`
cancel, which is the telescoping in its smallest instance. -/
theorem altSum_pair (P Q : ι → ℝ) (Φ A : ι → R)
    (hA : ∀ i, A i = Q i • Φ i + P i • (1 : R)) (i j : ι) :
    A i * (Q j • Φ j) - P i • A j
      = (Q i * Q j) • (Φ i * Φ j) - (P i * P j) • (1 : R) := by
  rw [hA i, hA j, add_mul, smul_mul_assoc, smul_mul_assoc, one_mul, mul_smul_comm,
    smul_smul, smul_smul, smul_add, smul_smul, smul_smul]
  abel

end Calibrator.BundleRigidity
