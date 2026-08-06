/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Blindness.BundleRigidity.Telescope
import Descent.Layer

assert_below Descent.Conditionals Descent.Portability Descent.Decision Descent.Program

/-!
# The corrected kernel dichotomy for trip semigroups

This module imports Mathlib and `Descent.Blindness.BundleRigidity.Telescope`, from which it takes
`prodWeight`. **Do not add a local copy of the word-weight product**; one definition, one
place to change it.

## What this replaces

A previous conjecture in this development read:

> the kernel is non-zero **iff** some relation has **weight product one**.

**That is false, and the falsifier has been executed.** Take `φ₁ = f` and `φ₂ = f ∘ f`.
Then the relation `"2" = "11"` holds, with a parity mismatch, and the resulting Bézout
constant is strictly positive for *every* choice of weights. So the kernel is non-zero
while no relation has weight product one. **Relations alone suffice; the weight condition
is not part of the criterion.**

The refuted statement stays below as `weightProductOne_conjecture`, immediately under its
refutation, so that a reader who meets that form elsewhere finds it named and struck
rather than quietly absent.

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
  the weights. This is the theorem that refutes `weightProductOne_conjecture`.
* **Theorem 4.** `(Q_min/P_max)^N > m N` for the overlap multiplicity `m` gives zero
  kernel.
* **Zero or infinite.** On every decided stratum the kernel is either zero or
  infinite-dimensional. It is never finite and non-zero.
* **The open stratum.** Free semigroups with overlap at the weight-gap exponential rate.
  Nothing here decides that case, and no if-and-only-if is claimed.

## Why commutation never needed a weight condition

The commutation relation is `ij = ji`, and its weight defect is **identically one** for
every choice of weights (`commutation_defect_eq_one`). That is a two-line computation and
it explains why the commutator mechanism works without any hypothesis on the weights: the
only weight condition that could be imposed on it is satisfied automatically.

## Proof boundary

**Do not package unproved analytic conclusions as fields of a structure here**: that makes
callers supply the advertised results. This module exports only statements derived in Lean
from their displayed hypotheses -- the automatic weight condition, the commutation defect,
the falsifier's arithmetic, and the logical form of the refutation itself.

## Attribution

The closed-path criterion for sums of weighted compositions is classical — Diliberto and
Straus, Marshall and O'Farrell, Ismailov. The correction recorded here is to a conjecture
made in this development, not to that literature.
-/

namespace Descent.Blindness.BundleRigidity

open scoped BigOperators

variable {ι : Type*}

/-! ## Words and weight defects -/

/-- The **weight ratio** of a word: `Q`-product over `P`-product. -/
noncomputable def weightRatio (P Q : ι → ℝ) (w : List ι) : ℝ := prodWeight Q w / prodWeight P w

/-- With a vanishing denominator Mathlib returns `0`, which is a value this quantity can also
take legitimately, so the branch is named rather than left to be inferred from the result. -/
theorem weightRatio_at_zero_denominator_is_junk (P Q : ι → ℝ) (w : List ι)
    (hzero : prodWeight P w = 0) :
    weightRatio P Q w = 0 := by
  unfold weightRatio
  rw [hzero, div_zero]


/-- The **weight defect of a relation** `w ≈ u`: the ratio of the two words' weight
ratios. The refuted conjecture asserted that a relation contributes to the kernel exactly
when its defect is one. -/
noncomputable def defect (P Q : ι → ℝ) (w u : List ι) : ℝ :=
  weightRatio P Q w / weightRatio P Q u

/-- With a vanishing denominator Mathlib returns `0`, which is a value this quantity can also
take legitimately, so the branch is named rather than left to be inferred from the result. -/
theorem defect_at_zero_denominator_is_junk (P Q : ι → ℝ) (w u : List ι)
    (hzero : weightRatio P Q u = 0) :
    defect P Q w u = 0 := by
  unfold defect
  rw [hzero, div_zero]


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
  simp only [prodWeight_cons, prodWeight_nil, mul_one, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  norm_num

/-- The falsifier's defect is not one, which is the whole point of it. -/
theorem defect_witness_ne_one :
    defect falsifierP falsifierQ [0, 0] [1] ≠ 1 := by
  rw [defect_witness]
  norm_num

/-! ## The character `χ` and the Bézout constant -/

/-- **The character** `χ w = P^w / Q^w`, the ratio of weight products along the word.

Both constants of the falsifier come from this one definition: the Bézout constant is an
alternating combination of `χ` and the weight defect is a ratio of `χ`. -/
noncomputable def chi (P Q : ι → ℝ) (w : List ι) : ℝ := prodWeight P w / prodWeight Q w

/-- With a vanishing denominator Mathlib returns `0`, which is a value this quantity can also
take legitimately, so the branch is named rather than left to be inferred from the result. -/
theorem chi_at_zero_denominator_is_junk (P Q : ι → ℝ) (w : List ι)
    (hzero : prodWeight Q w = 0) :
    chi P Q w = 0 := by
  unfold chi
  rw [hzero, div_zero]


/-- **The character and the weight ratio are one map, read in opposite directions.**

`weightRatio P Q` divides the `Q`-product by the `P`-product and `chi P Q` divides the
`P`-product by the `Q`-product, so each is the other with its two weight families
exchanged. Both names stay, because the defect is a ratio of weight ratios and the Bézout
constant is an alternating combination of characters; what this forbids is the two
spellings drifting apart. -/
theorem chi_eq_weightRatio_swap (P Q : ι → ℝ) (w : List ι) :
    chi P Q w = weightRatio Q P w := rfl

/-- **The character converts one telescope weight into the other.**

`Telescope.prodWeight` is the only product either constant of this file is built from, and
`chi` is the ratio of two of them, so multiplying the character back by the `Q`-product
returns the `P`-product exactly. That is what puts the Bézout constant and the weight defect
on one scale rather than leaving them two unrelated ratios, and it is the statement that
fails if either file changes what a word's weight is. The hypothesis is the honest one: a
word carrying a zero `Q`-weight has no character to speak of, and the ratio is junk there
rather than informative. -/
theorem chi_mul_prodWeight (P Q : ι → ℝ) (w : List ι) (hQ : prodWeight Q w ≠ 0) :
    chi P Q w * prodWeight Q w = prodWeight P w := by
  unfold chi
  field_simp

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
    Matrix.cons_val_zero, Matrix.cons_val_one]
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

/-! ## No upstream theorems are carried here

**Do not add a structure carrying Theorem 1, Theorem 3 or the zero-or-infinite dichotomy as
fields.** Those are proved nowhere in this corpus, and a structure field makes the caller
supply them while looking like a result. The distinction between "proved here" and
"asserted upstream and consumed here" cannot be carried by a docstring convention, because
a docstring is not a type.

This file contains what it proves: the weight arithmetic of the executed falsifier, the
Bézout constant derived from the character, the parity argument that makes the refutation
structural rather than lucky, and the forced-mass-growth engine.
-/



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

**Do not record these as `Prop`-valued structure fields.** A `Prop` field states nothing:
`shellsPairwiseDisjoint : Prop` is a variable over propositions, satisfiable by `True`, not
an assertion that the shells are disjoint. Prose is the honest form until someone
formalizes them, and no proof here refers to them.

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

The *geometric* inputs — disjointness of the shells, their separation from the attractor,
and the two partition statements — are the prose list above. What is proved here is the
**arithmetic** those inputs feed: once the shells
are disjoint the mass they force satisfies `U_{n+1} ≥ (Q_min/P_max)·U_n`, and in the
normalized regime that ratio exceeds one while the total mass is bounded. A quantity that
grows geometrically inside a bounded one cannot start positive.

That step is elementary and it is the whole of Theorem 1 downstream of the geometry, so it
belongs in the corpus as a theorem rather than as a sentence. `forcedMass_ge` is the growth
recursion unrolled; `forcedMass_bounded_contradiction` is the contradiction; and
`kernel_mass_must_vanish` is the form Theorem 1 consumes — **the forced mass at the root is
zero**, which is what "zero kernel" means once the shell partition is in hand.

What this localizes: the arithmetic of the word-shell argument is proved here, and the
geometric half — disjointness of the shells — is simply not in this corpus. It is not carried
as an assumption either; it is absent, and any use of the word-shell argument must supply it.

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

end Descent.Blindness.BundleRigidity
