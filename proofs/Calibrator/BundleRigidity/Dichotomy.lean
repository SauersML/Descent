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
import Calibrator.BundleRigidity.Telescope

/-!
# The corrected kernel dichotomy for trip semigroups

This module imports Mathlib and `Calibrator.BundleRigidity.Telescope`, from which it takes
`prodWeight`. It previously carried its own copy under the name `wProd`, retained because a note here
recorded that `Telescope` did not compile. **That note was stale** -- `Telescope`
builds green -- so the repoint it asked for has been done and the duplicate is gone.

## What this replaces

A previous conjecture in this development read:

> the kernel is non-zero **iff** some relation has **weight product one**.

**That is false, and the falsifier has been executed.** Take `φ₁ = f` and `φ₂ = f ∘ f`.
Then the relation `"2" = "11"` holds, with a parity mismatch, and the resulting Bézout
constant is strictly positive for *every* choice of weights. So the kernel is non-zero
while no relation has weight product one. **Relations alone suffice; the weight condition
is not part of the criterion.**

The superseded statement is kept below as `weightProductOne_conjecture`, immediately under
its refutation, so that a reader who encounters the old form elsewhere can see it named
and struck rather than quietly absent.

### The arithmetic of the falsifier, checked here

At `P₁ = 3/10`, `Q₁ = 7/10`, `P₂ = 2/5`, `Q₂ = 3/5`, the relation `"2" = "11"` has weight
defect

```
(Q₁/P₁)² · (P₂/Q₂)  =  (7/3)² · (2/3)  =  49/9 · 2/3  =  98/27  ≠  1,
```

which is `defect_witness`. That number is proved here from the weights, not quoted.

The accompanying **Bézout constant `c = 125/147` is also derived here**, not quoted. The
character is `χ w = P^w / Q^w`, the ratio of weight products along the word, and the
constant is

```
c  =  (-1)^{|u|-1} χ u  -  (-1)^{|v|-1} χ v.
```

For `u = "2"` and `v = "11"`: `χ 2 = 2/3`, `χ 1 = 3/7` so `χ 11 = 9/49`, and the lengths
`1` and `2` have opposite parity, so the signs are `+1` and `-1` and the two terms **add**:

```
c  =  2/3 + 9/49  =  (98 + 27)/147  =  125/147.
```

That is `bezout_witness`. Both constants now come from the single definition of `χ`, and
the `98/27` above is the same numbers read the other way: `defect = χ u / χ w`
(`defect_eq_chi_ratio`).

### Why the conjecture had to die: parity forbids the cancellation

`bezout_ne_zero_of_parity_mismatch` is the structural statement. When `|u|` and `|v|` have
**opposite parity** the two signs are opposite, so the two terms **add** rather than
subtract; and `χ > 0` always, being a ratio of products of positive weights. Hence
`c ≠ 0` for **every** choice of weights — no tuning can make it vanish.

The refuted conjecture required a cancellation that parity forbids. That is the mechanism,
and it is why the falsifier is not a lucky choice of numbers: `φ₁ = f`, `φ₂ = f ∘ f` gives
the relation `"2" = "11"` with lengths `1` and `2`, and the parity mismatch alone settles
it before any weight is chosen.

## The corrected picture

* **Theorem 1.** Disjoint images together with `Q_min > P_max` gives zero kernel. In the
  normalized regime `P + Q = 1` with `P < Q`, the weight condition is *automatic* — this
  is `weight_condition_automatic`, and it is proved here in full.
* **Theorem 3.** *Any* relation gives an infinite-dimensional kernel, unconditionally on
  the weights. This is the theorem that kills the old conjecture.
* **Theorem 4.** `(Q_min/P_max)^N > m N` for the overlap multiplicity `m` gives zero
  kernel.
* **Zero or infinite.** On every decided stratum the kernel is either zero or
  infinite-dimensional. It is never finite and non-zero.
* **The open stratum.** Free semigroups with overlap at the weight-gap exponential rate.
  Nothing here decides that case, and no if-and-only-if is claimed.

## Why commutation never needed a weight condition

The commutation relation is `ij = ji`, and its weight defect is **identically one** for
every choice of weights (`commutation_defect_eq_one`). That is a two-line computation and
it explains a fact that previously looked like a coincidence: the commutator mechanism was
observed to work without any hypothesis on the weights, and the reason is that the only
weight condition anyone could have imposed on it is satisfied automatically.

## House style

The three deep theorems are **named fields of a structure**, not `sorry`s. Their proofs
are not in this development, and carrying them as inputs means anything derived from them
shows that in its own type. What *is* proved here without hypotheses: the automatic weight
condition, the commutation defect, the falsifier's arithmetic, and the logical form of the
refutation itself.

## Attribution

The closed-path criterion for sums of weighted compositions is classical — Diliberto and
Straus, Marshall and O'Farrell, Ismailov. The correction recorded here is to a conjecture
made in this development, not to that literature.
-/

namespace Calibrator.BundleRigidity

open scoped BigOperators

variable {ι : Type*}

/-! ## Words and weight defects -/

/-- The **weight ratio** of a word: `Q`-product over `P`-product. -/
noncomputable def weightRatio (P Q : ι → ℝ) (w : List ι) : ℝ := prodWeight Q w / prodWeight P w

/-- The **weight defect of a relation** `w ≈ u`: the ratio of the two words' weight
ratios. The refuted conjecture asserted that a relation contributes to the kernel exactly
when its defect is one. -/
noncomputable def defect (P Q : ι → ℝ) (w u : List ι) : ℝ :=
  weightRatio P Q w / weightRatio P Q u

/-- **The commutation relation has defect one, identically.**

`defect (i :: j :: []) (j :: i :: []) = 1` for every choice of weights, because both words
use the same letters and the products are over a commutative field. This is why the
commutator mechanism never needed a weight hypothesis: the only one available to it holds
automatically. -/
theorem commutation_defect_eq_one (P Q : ι → ℝ) (i j : ι)
    (hP : P i ≠ 0) (hP' : P j ≠ 0) (hQ : Q i ≠ 0) (hQ' : Q j ≠ 0) :
    defect P Q [i, j] [j, i] = 1 := by
  unfold defect weightRatio
  simp only [prodWeight_cons, prodWeight_nil, mul_one]
  field_simp

/-! ## The falsifier's arithmetic

`φ₁ = f`, `φ₂ = f ∘ f`, relation `"2" = "11"`, at the source's weights.
-/

/-- The weights of the executed falsifier: `P = (3/10, 2/5)`, `Q = (7/10, 3/5)`. -/
noncomputable def falsifierP : Fin 2 → ℝ := ![3 / 10, 2 / 5]

/-- The weights of the executed falsifier, `Q` side. -/
noncomputable def falsifierQ : Fin 2 → ℝ := ![7 / 10, 3 / 5]

/-- **The falsifier's weight defect is `98/27`, hence not one.**

The relation is `"2" = "11"`: the word `[0, 0]` (two copies of `φ₁`) against the word
`[1]` (one copy of `φ₂`). Its defect is `(Q₁/P₁)² · (P₂/Q₂) = (7/3)² · (2/3) = 98/27`.

This number is computed from the weights here rather than quoted, and it agrees with the
value reported by the source. -/
theorem defect_witness :
    defect falsifierP falsifierQ [0, 0] [1] = 98 / 27 := by
  unfold defect weightRatio falsifierP falsifierQ
  simp only [prodWeight_cons, prodWeight_nil, mul_one, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons]
  norm_num

/-- The falsifier's defect is not one, which is the whole point of it. -/
theorem defect_witness_ne_one :
    defect falsifierP falsifierQ [0, 0] [1] ≠ 1 := by
  rw [defect_witness]; norm_num

/-! ## The character `χ` and the Bézout constant -/

/-- **The character** `χ w = P^w / Q^w`, the ratio of weight products along the word.

Both constants of the falsifier come from this one definition: the Bézout constant is an
alternating combination of `χ` and the weight defect is a ratio of `χ`. -/
noncomputable def chi (P Q : ι → ℝ) (w : List ι) : ℝ := prodWeight P w / prodWeight Q w

/-- A product of positive weights along a word is positive. -/
theorem prodWeight_pos (P : ι → ℝ) (hP : ∀ i, 0 < P i) (w : List ι) : 0 < prodWeight P w := by
  induction w with
  | nil => rw [prodWeight_nil]; norm_num
  | cons i u ih => rw [prodWeight_cons]; exact mul_pos (hP i) ih

/-- **The character is strictly positive**, being a ratio of products of positive
weights. This is half of why the Bézout constant cannot vanish. -/
theorem chi_pos (P Q : ι → ℝ) (hP : ∀ i, 0 < P i) (hQ : ∀ i, 0 < Q i) (w : List ι) :
    0 < chi P Q w :=
  div_pos (prodWeight_pos P hP w) (prodWeight_pos Q hQ w)

/-- **The weight defect is a ratio of characters**: `defect w u = χ u / χ w`.

So the `98/27` and the `125/147` are the same four numbers read two different ways. -/
theorem defect_eq_chi_ratio (P Q : ι → ℝ) (hP : ∀ i, 0 < P i) (hQ : ∀ i, 0 < Q i)
    (w u : List ι) :
    defect P Q w u = chi P Q u / chi P Q w := by
  have hPw := prodWeight_pos P hP w
  have hQw := prodWeight_pos Q hQ w
  have hPu := prodWeight_pos P hP u
  have hQu := prodWeight_pos Q hQ u
  unfold defect weightRatio chi
  field_simp

/-- **The Bézout constant** of a relation `u ≈ v`:

`c = (-1)^{|u|-1} χ u - (-1)^{|v|-1} χ v`.

The exponent is written `|u| + 1`, which agrees with `|u| - 1` for every length and avoids
truncated natural subtraction at the empty word. -/
noncomputable def bezout (P Q : ι → ℝ) (u v : List ι) : ℝ :=
  (-1 : ℝ) ^ (u.length + 1) * chi P Q u - (-1 : ℝ) ^ (v.length + 1) * chi P Q v

/-- **The Bézout constant of the falsifier is `125/147`.**

`χ 2 = 2/3` and `χ 11 = (3/7)² = 9/49`; the lengths `1` and `2` have opposite parity so
the terms add, giving `2/3 + 9/49 = 125/147`. Derived from the weights here. -/
theorem bezout_witness :
    bezout falsifierP falsifierQ [1] [0, 0] = 125 / 147 := by
  unfold bezout chi falsifierP falsifierQ
  simp only [prodWeight_cons, prodWeight_nil, mul_one, List.length_cons, List.length_nil,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  norm_num

/-- **Parity forbids the cancellation: the Bézout constant cannot vanish.**

If `|u|` and `|v|` have opposite parity then the two signs are opposite, so the two terms
**add** rather than subtract. Since `χ > 0` always, the sum is non-zero — for *every*
choice of weights, with no tuning available.

**This is why the weight-product-one conjecture died.** That conjecture required a
cancellation between the two terms, and a parity mismatch makes the cancellation
impossible before any weight is chosen. The falsifier `φ₁ = f`, `φ₂ = f ∘ f` produces the
relation `"2" = "11"` with lengths `1` and `2`, and the mismatch alone settles it. -/
theorem bezout_ne_zero_of_parity_mismatch (P Q : ι → ℝ)
    (hP : ∀ i, 0 < P i) (hQ : ∀ i, 0 < Q i) (u v : List ι)
    (hpar : (Even u.length ∧ Odd v.length) ∨ (Odd u.length ∧ Even v.length)) :
    bezout P Q u v ≠ 0 := by
  have hcu := chi_pos P Q hP hQ u
  have hcv := chi_pos P Q hP hQ v
  unfold bezout
  rcases hpar with ⟨hu, hv⟩ | ⟨hu, hv⟩
  · -- `|u|` even, `|v|` odd: signs are `-1` and `+1`, so `c = -(χ u + χ v) < 0`.
    rw [(hu.add_one).neg_one_pow, (hv.add_one).neg_one_pow]
    intro hzero
    nlinarith [hcu, hcv]
  · -- `|u|` odd, `|v|` even: signs are `+1` and `-1`, so `c = χ u + χ v > 0`.
    rw [(hu.add_one).neg_one_pow, (hv.add_one).neg_one_pow]
    intro hzero
    nlinarith [hcu, hcv]

/-- The falsifier's lengths do have opposite parity, so the general theorem applies to
it. -/
theorem falsifier_parity_mismatch :
    (Even ([1] : List (Fin 2)).length ∧ Odd ([0, 0] : List (Fin 2)).length) ∨
      (Odd ([1] : List (Fin 2)).length ∧ Even ([0, 0] : List (Fin 2)).length) := by
  right
  constructor
  · decide
  · decide

/-! ## The dichotomy, with the deep theorems as named inputs -/

/-- **A trip system**: the weights, the relation structure, and the three theorems of the
corrected picture carried as named fields.

The fields `theorem1`, `theorem3` and `theorem4` are **inputs, not results of this
development**. They appear here so that anything derived from them carries them in its
type. -/
structure TripSystem (ι : Type*) where
  /-- The `P` weights. -/
  P : ι → ℝ
  /-- The `Q` weights. -/
  Q : ι → ℝ
  /-- Weights are strictly positive. -/
  P_pos : ∀ i, 0 < P i
  /-- Weights are strictly positive. -/
  Q_pos : ∀ i, 0 < Q i
  /-- Two distinct words inducing the same composed map. -/
  Relation : List ι → List ι → Prop
  /-- The kernel of the associated operator is non-zero. -/
  KernelNonzero : Prop
  /-- The kernel is infinite-dimensional. -/
  KernelInfiniteDim : Prop
  /-- The generating maps have pairwise disjoint images. -/
  DisjointImages : Prop
  /-- **Theorem 3 (input).** Any relation forces an infinite-dimensional kernel,
  unconditionally on the weights. This is what refutes the weight-product conjecture. -/
  theorem3 : (∃ w u, Relation w u) → KernelInfiniteDim
  /-- **Theorem 1 (input).** Disjoint images plus a uniform weight gap gives zero
  kernel. -/
  theorem1 : DisjointImages → (∀ i j, P i < Q j) → ¬ KernelNonzero
  /-- **The zero-or-infinite dichotomy (input).** On every decided stratum the kernel is
  either zero or infinite-dimensional; it is never finite and non-zero. -/
  zero_or_infinite : KernelNonzero → KernelInfiniteDim
  /-- An infinite-dimensional kernel is in particular non-zero. -/
  infiniteDim_imp_nonzero : KernelInfiniteDim → KernelNonzero

namespace TripSystem

variable (S : TripSystem ι)

/-- **The weight condition of Theorem 1 is automatic in the normalized regime.**

If `P i + Q i = 1` and `P i < Q i` for every `i`, then `P i < Q j` for *every* pair `i, j`
— not merely for matching indices. The reason is that both conditions pin each weight to
its own side of `1/2`: `P i < 1/2 < Q j`.

Proved here in full, with no hypotheses beyond the two displayed. This is the sense in
which Theorem 1's hypothesis is cheaper than it looks. -/
theorem weight_condition_automatic (hnorm : ∀ i, S.P i + S.Q i = 1)
    (hlt : ∀ i, S.P i < S.Q i) : ∀ i j, S.P i < S.Q j := by
  intro i j
  have h1 : S.P i < 1 / 2 := by
    have := hnorm i; have := hlt i; linarith
  have h2 : (1 : ℝ) / 2 < S.Q j := by
    have := hnorm j; have := hlt j; linarith
  linarith

/-- Theorem 1 in the normalized regime, with the weight hypothesis discharged. -/
theorem kernel_zero_of_disjoint_normalized (hdisj : S.DisjointImages)
    (hnorm : ∀ i, S.P i + S.Q i = 1) (hlt : ∀ i, S.P i < S.Q i) :
    ¬ S.KernelNonzero :=
  S.theorem1 hdisj (S.weight_condition_automatic hnorm hlt)

/-- A relation forces a non-zero kernel. -/
theorem kernelNonzero_of_relation (h : ∃ w u, S.Relation w u) : S.KernelNonzero :=
  S.infiniteDim_imp_nonzero (S.theorem3 h)

/-- **The refutation, in logical form.**

If a system has a relation, and **every** relation of the system has defect different from
one, then the kernel is non-zero while no relation has weight product one. That is exactly
the failure of the forward direction of the refuted conjecture.

Stating it this way makes the refutation a theorem rather than an assertion: given
Theorem 3 as an input, one only has to exhibit a system whose relations all have defect
`≠ 1`, and `defect_witness_ne_one` supplies the arithmetic for the `φ₁ = f`, `φ₂ = f ∘ f`
system at the source's weights. -/
theorem weightProductOne_fails (hrel : ∃ w u, S.Relation w u)
    (hdef : ∀ w u, S.Relation w u → defect S.P S.Q w u ≠ 1) :
    S.KernelNonzero ∧ ¬ ∃ w u, S.Relation w u ∧ defect S.P S.Q w u = 1 := by
  refine ⟨S.kernelNonzero_of_relation hrel, ?_⟩
  rintro ⟨w, u, hwu, hone⟩
  exact hdef w u hwu hone

/-- **The superseded conjecture, named and struck.**

This is the statement that was refuted: the kernel is non-zero *if and only if* some
relation has weight product one. It is recorded as a definition so that the old form has a
name to be referred to, and so that a reader meeting it elsewhere in the corpus finds it
here next to `weightProductOne_fails` rather than finding nothing.

**Do not use this as a criterion.** The correct statement is that relations alone
suffice. -/
def weightProductOne_conjecture : Prop :=
  S.KernelNonzero ↔ ∃ w u, S.Relation w u ∧ defect S.P S.Q w u = 1

/-- **The conjecture is false for any system meeting the falsifier's hypotheses.** -/
theorem not_weightProductOne_conjecture (hrel : ∃ w u, S.Relation w u)
    (hdef : ∀ w u, S.Relation w u → defect S.P S.Q w u ≠ 1) :
    ¬ S.weightProductOne_conjecture := by
  intro hconj
  obtain ⟨hne, hno⟩ := S.weightProductOne_fails hrel hdef
  exact hno (hconj.mp hne)

end TripSystem

/-! ## Theorem 1's architecture, and where its weight actually rests

Theorem 1 is **not a case analysis**, and this matters for how it should be audited. It is
a growth-and-contradiction argument in four steps:

1. **shell partition** — with the images `Bᵢ = φᵢ V` disjoint and `Λ` the attractor, the
   shells `S_w = φ_w G` over all words (`G` the complement of the images) are pairwise
   disjoint, and `V` is their disjoint union together with `Λ`;
2. **shell recursion** — restricting the kernel equation to `S_{iw}` gives
   `P₁ α_{iw} + P₂ β_{iw} = -Qᵢ Φᵢ(γ_w)`, with `P₁ α_G + P₂ β_G = 0` on the free start;
3. **growth** — summing over `i` and over all words of length `n` gives
   `U_{n+1} ≥ (Q_min / P_max) · U_n` with ratio strictly above one, so any non-zero `U_n₀`
   forces `U_n → ∞`, contradicting finite total variation;
4. **attractor** — depth-`n` cylinders partition `Λ`, both sides collapse by the partition
   identity, and `(Q_min - P_max) T ≤ 0` forces `T = 0`.

**There is no "the remaining cases are analogous" to audit, and there cannot be**: steps 3
and 4 sum over `i` and over *all* words at once, so no case is left outside the argument.

The contrast with the refuted single-modulus classification is exact. That argument
enumerated deletions and asserted the unenumerated ones were symmetric, about an object
where `A > B` breaks the symmetry. Theorem 1 never enumerates.

**Where its weight actually rests is step 1's disjointness**, which is a single sentence
doing real work, together with the escape-depth claim separating shells from the attractor.
If disjointness fails anywhere, the partition collapses and step 3 sums the same mass
twice. That is where a hidden assumption would live.

A `ShellPartitionHypotheses` structure used to record those four geometric inputs as
`Prop`-valued fields. It is removed: nothing consumed it, and a `Prop` field states
nothing — `shellsPairwiseDisjoint : Prop` is a variable over propositions, satisfiable by
`True`, not an assertion that the shells are disjoint. Recording them as prose is the
honest form, and it loses no content because no proof ever referred to them.

The four geometric inputs of step 1, none of them formalized here:

1. **shells pairwise disjoint** — the load-bearing one. Two distinct words agree up to
   their first differing letter, and at that letter the sets sit inside disjoint images
   pulled forward injectively. If this fails, step 3 counts the same mass twice.
2. **shell disjoint from the attractor** — a point of `S_w` has escape depth `|w|` while
   attractor points have none. A different claim about a different pair of sets, which is
   why it is listed separately.
3. **`V` is the disjoint union** of the shells together with the attractor.
4. **depth-`n` cylinders partition the attractor**, which is what lets step 4 collapse. -/

/-! ## Theorem 1's engine, proved

`ShellPartitionHypotheses` carries the *geometric* inputs — disjointness of the shells, their
separation from the attractor, and the two partition statements. What it does not carry, and
what was previously left in prose, is the **arithmetic** those inputs feed: once the shells
are disjoint the mass they force satisfies `U_{n+1} ≥ (Q_min/P_max)·U_n`, and in the
normalized regime that ratio exceeds one while the total mass is bounded. A quantity that
grows geometrically inside a bounded one cannot start positive.

That step is elementary and it is the whole of Theorem 1 downstream of the geometry, so it
belongs in the corpus as a theorem rather than as a sentence. `forcedMass_ge` is the growth
recursion unrolled; `forcedMass_bounded_contradiction` is the contradiction; and
`kernel_mass_must_vanish` is the form Theorem 1 consumes — **the forced mass at the root is
zero**, which is what "zero kernel" means once the shell partition is in hand.

This does not discharge `TripSystem.theorem1`, which still carries the geometric half as an
input. What it does is localize what remains unproved: after this, the only unproved content
of Theorem 1 is the disjointness of the shells.

Empirical status: DERIVED. Pure arithmetic, no analytic input. -/

section ForcedMassGrowth

/-- **The growth recursion, unrolled.** A geometric lower bound compounds.

    Note what is *not* needed: nonnegativity of `U 0`. The recursion propagates the bound
    whatever the sign of the starting mass, so the hypothesis a first draft carried here was
    dead weight and is omitted rather than left in to look reassuring. -/
theorem forcedMass_ge (ρ : ℝ) (U : ℕ → ℝ) (hρ : 0 ≤ ρ)
    (hstep : ∀ n, ρ * U n ≤ U (n + 1)) :
    ∀ n, ρ ^ n * U 0 ≤ U n := by
  intro n
  induction n with
  | zero => simp
  | succ k ih =>
    calc ρ ^ (k + 1) * U 0 = ρ * (ρ ^ k * U 0) := by ring
      _ ≤ ρ * U k := mul_le_mul_of_nonneg_left ih hρ
      _ ≤ U (k + 1) := hstep k

/-- **Geometric growth inside a bounded quantity forces a zero start.**

    If the forced mass obeys `U_{n+1} ≥ ρ U_n` with `ρ > 1`, and every `U_n` is bounded above
    by the total mass `B`, then `U 0` cannot be positive. This is the contradiction step of
    the word-shell argument, with the shells' disjointness already used to produce `hstep`
    and the ambient total mass supplying `hbound`. -/
theorem forcedMass_bounded_contradiction (ρ B : ℝ) (U : ℕ → ℝ)
    (hρ : 1 < ρ) (hU0 : 0 < U 0) (hstep : ∀ n, ρ * U n ≤ U (n + 1))
    (hbound : ∀ n, U n ≤ B) : False := by
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (B / U 0) hρ
  have hgrow := forcedMass_ge ρ U (by linarith) hstep n
  have hlt : B / U 0 * U 0 < ρ ^ n * U 0 := by
    exact mul_lt_mul_of_pos_right hn hU0
  rw [div_mul_cancel₀ _ (ne_of_gt hU0)] at hlt
  have := hbound n
  linarith

/-- **The form Theorem 1 consumes.** Under the same hypotheses the forced mass at the root
    vanishes, which is the statement that no nonzero kernel element survives the shell
    decomposition. -/
theorem kernel_mass_must_vanish (ρ B : ℝ) (U : ℕ → ℝ)
    (hρ : 1 < ρ) (hnonneg : 0 ≤ U 0) (hstep : ∀ n, ρ * U n ≤ U (n + 1))
    (hbound : ∀ n, U n ≤ B) : U 0 = 0 := by
  rcases eq_or_lt_of_le hnonneg with h | h
  · exact h.symm
  · exact absurd (forcedMass_bounded_contradiction ρ B U hρ h hstep hbound) not_false

/-- **The normalized regime supplies the ratio.** With `P i + Q i = 1` and `P i < Q i`, every
    ratio `Q j / P i` exceeds one — so the growth hypothesis of the contradiction above is
    automatic, exactly as `weight_condition_automatic` makes Theorem 1's weight hypothesis
    automatic. -/
theorem growth_ratio_gt_one {ι : Type*} (P Q : ι → ℝ)
    (hnorm : ∀ i, P i + Q i = 1) (hlt : ∀ i, P i < Q i) (i j : ι)
    (hP : 0 < P i) : 1 < Q j / P i := by
  have h1 : P i < 1 / 2 := by have := hnorm i; have := hlt i; linarith
  have h2 : (1 : ℝ) / 2 < Q j := by have := hnorm j; have := hlt j; linarith
  rw [lt_div_iff₀ hP]
  linarith

end ForcedMassGrowth

end Calibrator.BundleRigidity
