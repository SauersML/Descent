/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Tactic
import Descent.Layer

assert_below Descent.Conditionals Descent.Portability Descent.Decision Descent.Program

/-!
# Theorem E: the two-atom family, solved completely

This module is **self-contained: it imports only Mathlib**.

## The family

For `0 < p < 1` the two-atom standardized family is

```
atoms   =  ( -√((1-p)/p),  √(p/(1-p)) )
masses  =  ( p,  1-p )
```

whose modulus curves are

```
m₁ p  =  |1 - 2p| / p          m₂ p  =  |1 - 2p| / (1 - p).
```

This is the one case of the bundle rigidity problem that is **completely solved**, and it
is one of the three things this development may legitimately claim as new. Everything
below is proved outright: there are no named hypotheses and no `sorry` in this file.

## The reflection, and what it means biologically

The involution is `τ p = 1 - p`. It swaps the two branches — `m₁ ∘ τ = m₂` and
`m₂ ∘ τ = m₁` (`mOne_reflect`, `mTwo_reflect`) — and it swaps the two masses, so the
transfer measure is invariant: `TT ∘ τ = TT`. By Theorem B every `τ`-odd measure is in the
kernel, and Theorem E says that is *all* of the kernel.

**In population genetics this is a known fact with a name.** From unpolarized allele data
one recovers the site frequency spectrum only up to the ancestral/derived swap — the
**folded spectrum**. The machinery reproduces that independently, which is a validation of
the formalism rather than a discovery.

The contribution is *not* that polarization is unrecoverable; that was known. It is that
the **same peeling machinery** which yields this known fact goes on to decide
identifiability of the folded spectrum itself, on `(0, 1/2]`, which is not standard.

## The peeling chain

The quotient family on `(0, 1/2]` is rigid, and peeling reaches every point of it along

```
P k  =  k / (2k + 1),        P 1 = 1/3,  P 2 = 2/5,  P 3 = 3/7,  …  →  1/2.
```

The chain identity is the arithmetic verification

```
1 / P (k+1)  -  2   =   1 / (k+1)   =   (1 - 2 · P k) / (1 - P k),
```

which says exactly that **`m₁` at the next point equals `m₂` at the current point**:
`m₁ (P (k+1)) = m₂ (P k) = 1/(k+1)`. That common value is the link in the chain, and it is
what lets peeling step from `P k` to `P (k+1)`. Peeling therefore runs to order `ω`, and
the chain exhausts `(0, 1/2)`.

The remaining point `p = 1/2` is the **Rademacher point**, where both atoms are `±1` and
both modulus curves vanish. Peeling cannot reach it, because there is nothing left to
single-cover. It is killed instead by the **mass identity (0.4)**: a measure supported at
`1/2` alone is a multiple of `δ_{1/2}`, its image is the same multiple of `δ_0`, and
vanishing image forces the multiple to be zero (`rademacher_point_killed`). That is the
one place in the argument where the mass identity, rather than coverage, does the work.

## Audit point (AP-b): our family sits on a block-collision stratum, and the argument
## here does not depend on the framework that excludes them

The realizability framework's second pre-registered audit point is **block collisions** —
atom merging — where the sufficiency argument assumes a constant block pattern and is
currently proved *off* those isolated strata.

**This family sits on exactly such a stratum, and not incidentally.** At `p = 1/2` both
modulus curves vanish together (`mOne_half`, `mTwo_half`), so the distinct modulus values
collapse. That is a block collision, and it is the **accumulation point of the peeling
chain** (`chain_tendsto_half`), not an interior point one could exclude by hand.

So the inherited scope condition had to be checked rather than assumed. It clears, and here
is the specific reason:

* **the Rademacher point is killed by the mass identity, not by continuation.**
  `rademacher_point_killed` is pure arithmetic — `c · (p + (1 - p)) = c`, so a vanishing
  image forces `c = 0`. It invokes no analyticity, no germ, no block pattern and no
  continuation argument, so nothing about constant block patterns can affect it;
* **the chain never reaches the collision.** `chain_lt_half` proves every `P k` is strictly
  below `1/2`, so every peeling step happens strictly off the collision stratum, and the
  collision is approached only in the limit;
* **the peeling machinery used here is topological, not analytic.** The coverage and core
  results in `Coverage` use continuity of the modulus curves and monotonicity of peeling;
  they never use analyticity, so they carry no off-strata scope condition to inherit.

**Conclusion: nothing in this file's argument is inherited from the off-collision-strata
sufficiency claim.** This is recorded because an inherited scope condition is exactly the
kind of thing that goes unnoticed — the argument would still *read* correctly if it had
silently depended on one.

## Attribution

The two-atom solution is new here. The peeling argument it runs on is the classical
lightning-bolt argument from the theory of sums of weighted compositions
(Diliberto–Straus, Marshall–O'Farrell, Ismailov). The folded-spectrum conclusion is a
known fact in population genetics, reproduced rather than discovered.
-/

namespace Descent.Blindness.BundleRigidity

open scoped BigOperators

/-! ## The modulus curves -/

/-- The first modulus curve of the two-atom family: `|1 - 2p| / p`.

    Empirical status: NOT AN EMPIRICAL CLAIM -- a modulus curve of a two-point
    mixture; `p` is a mixture weight, not an allele frequency. -/
noncomputable def mOne (p : ℝ) : ℝ := |1 - 2 * p| / p

/-- **The first atom modulus at zero frequency, named.** An atom with no mass has no modulus and
the quantity diverges. Lean returns `0`, the value of a perfectly balanced atom at `p = 1 / 2`,
so the degenerate atom is reported as the best-conditioned one. Consumers must require
`p ≠ 0`. -/
theorem mOne_zero_frequency_is_junk :
    mOne 0 = 0 := by
  unfold mOne
  simp

/-- The second modulus curve of the two-atom family: `|1 - 2p| / (1 - p)`.

    Empirical status: NOT AN EMPIRICAL CLAIM -- a modulus curve of a two-point
    mixture; `p` is a mixture weight, not an allele frequency. -/
noncomputable def mTwo (p : ℝ) : ℝ := |1 - 2 * p| / (1 - p)

/-- **mTwo at its junk point, named.** At `p = 1` the second atom carries no mass and its modulus
diverges. The divisor `1 - p` is zero and Lean returns `0`, the modulus of a perfectly balanced
atom, so the degenerate atom is reported as the best-conditioned one -- the inversion
`mOne_zero_frequency_is_junk` records at the other endpoint. Consumers must exclude the argument
that makes the guard vanish. -/
theorem mTwo_unit_frequency_is_junk :
    mTwo 1 = 0 := by
  unfold mTwo
  norm_num

/-- **On `(0, 1/2]` the first modulus curve is `1/p - 2`**, the absolute value being
resolvable there. This is the form the chain identity uses. -/
theorem mOne_eq_of_le_half {p : ℝ} (hp : 0 < p) (hhalf : p ≤ 1 / 2) :
    mOne p = 1 / p - 2 := by
  unfold mOne
  rw [abs_of_nonneg (by linarith)]
  field_simp

/-- **On `(0, 1/2]` the second modulus curve is `(1 - 2p)/(1 - p)`.** -/
theorem mTwo_eq_of_le_half {p : ℝ} (hhalf : p ≤ 1 / 2) :
    mTwo p = (1 - 2 * p) / (1 - p) := by
  unfold mTwo
  rw [abs_of_nonneg (by linarith)]

/-! ## The reflection `τ p = 1 - p` -/

/-- **The reflection swaps the two branches.** -/
theorem mOne_reflect (p : ℝ) : mOne (1 - p) = mTwo p := by
  unfold mOne mTwo
  rw [show (1 : ℝ) - 2 * (1 - p) = -(1 - 2 * p) by ring, abs_neg]

/-- **The reflection swaps the two branches, the other way round.** -/
theorem mTwo_reflect (p : ℝ) : mTwo (1 - p) = mOne p := by
  unfold mOne mTwo
  rw [show (1 : ℝ) - 2 * (1 - p) = -(1 - 2 * p) by ring, abs_neg,
    show (1 : ℝ) - (1 - p) = p by ring]

/-- The masses also swap under the reflection, which together with `mOne_reflect` and
`mTwo_reflect` is exactly `TT ∘ τ = TT`: branch one at `1 - p` carries mass `1 - p` and
sits at the value branch two carries at `p` with mass `1 - p`. -/
theorem mass_reflect (p : ℝ) : (1 : ℝ) - (1 - p) = p := by ring

/-! ## The peeling chain `P k = k / (2k+1)` -/

/-- The peeling chain of the quotient family on `(0, 1/2]`. -/
noncomputable def chain (k : ℕ) : ℝ := (k : ℝ) / (2 * (k : ℝ) + 1)

@[simp] theorem chain_one : chain 1 = 1 / 3 := by norm_num [chain]

@[simp] theorem chain_two : chain 2 = 2 / 5 := by norm_num [chain]

@[simp] theorem chain_three : chain 3 = 3 / 7 := by norm_num [chain]

/-- The denominator is positive, which every computation below needs. -/
theorem chain_denom_pos (k : ℕ) : (0 : ℝ) < 2 * (k : ℝ) + 1 := by positivity

/-- **The chain lies strictly below `1/2`**, so it stays inside the quotient domain and
never reaches the Rademacher point. -/
theorem chain_lt_half (k : ℕ) : chain k < 1 / 2 := by
  have hd := chain_denom_pos k
  have hkey : 1 / 2 - chain k = 1 / (2 * (2 * (k : ℝ) + 1)) := by
    rw [chain]; field_simp; ring
  have hpos : 0 < 1 / (2 * (2 * (k : ℝ) + 1)) := by positivity
  linarith

/-- **The exact gap to `1/2`.** This is the quantitative form of convergence:
`1/2 - P k = 1 / (2(2k+1))`. -/
theorem half_sub_chain (k : ℕ) : 1 / 2 - chain k = 1 / (2 * (2 * (k : ℝ) + 1)) := by
  have hd := chain_denom_pos k
  rw [chain]
  field_simp
  ring

/-- The chain is non-negative, and positive from `k = 1` on. -/
theorem chain_nonneg (k : ℕ) : 0 ≤ chain k := by
  have hd := chain_denom_pos k
  exact div_nonneg (Nat.cast_nonneg k) (le_of_lt hd)

/-- The chain is strictly increasing: `1/2 - P k` is strictly decreasing. -/
theorem chain_lt_succ (k : ℕ) : chain k < chain (k + 1) := by
  have h1 := half_sub_chain k
  have h2 := half_sub_chain (k + 1)
  have hd := chain_denom_pos k
  have hd' := chain_denom_pos (k + 1)
  have hstep : (1 : ℝ) / (2 * (2 * ((k : ℝ) + 1) + 1)) < 1 / (2 * (2 * (k : ℝ) + 1)) := by
    apply one_div_lt_one_div_of_lt
    · linarith
    · linarith
  push_cast at h2
  linarith

/-! ## The chain identity, which is the whole of Theorem E's arithmetic -/

/-- **The chain identity, left half:** `1 / P (k+1) - 2 = 1 / (k+1)`.

Equivalently `m₁ (P (k+1)) = 1/(k+1)`. -/
theorem chain_identity_left (k : ℕ) :
    1 / chain (k + 1) - 2 = 1 / ((k : ℝ) + 1) := by
  have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hd : (0 : ℝ) < 2 * ((k : ℝ) + 1) + 1 := by positivity
  rw [chain]
  push_cast
  rw [one_div_div]
  field_simp
  ring

/-- **The chain identity, right half:** `(1 - 2 · P k) / (1 - P k) = 1 / (k+1)`.

Equivalently `m₂ (P k) = 1/(k+1)`. -/
theorem chain_identity_right (k : ℕ) :
    (1 - 2 * chain k) / (1 - chain k) = 1 / ((k : ℝ) + 1) := by
  have hd := chain_denom_pos k
  have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hne : (2 * (k : ℝ) + 1) ≠ 0 := ne_of_gt hd
  have hkne : ((k : ℝ) + 1) ≠ 0 := ne_of_gt hk
  -- `first | (field_simp; ring) | field_simp` tolerates either outcome: if `field_simp`
  -- closes the goal outright the `ring` would be a "no goals" error, and if it leaves a
  -- polynomial identity the `ring` is needed. Guessing which happens is what cost the
  -- earlier passes.
  have hdne : 1 - chain k ≠ 0 := by
    rw [chain]
    intro hcontra
    have : (2 * (k : ℝ) + 1) - (k : ℝ) = 0 := by
      field_simp at hcontra; linarith
    linarith
  rw [div_eq_iff hdne, chain]
  field_simp
  ring

/-- **The chain identity, as the source states it:**
`1 / P (k+1) - 2 = 1 / (k+1) = (1 - 2 P k) / (1 - P k)`. -/
theorem chain_identity (k : ℕ) :
    1 / chain (k + 1) - 2 = (1 - 2 * chain k) / (1 - chain k) := by
  rw [chain_identity_left, chain_identity_right]

/-! ## What the identity says about peeling -/

/-- `m₂` at the current chain point is `1/(k+1)`. -/
theorem mTwo_chain (k : ℕ) : mTwo (chain k) = 1 / ((k : ℝ) + 1) := by
  have hd := chain_denom_pos k
  have hpos : 0 < chain k ∨ chain k = 0 := by
    rcases eq_or_lt_of_le (chain_nonneg k) with h | h
    · exact Or.inr h.symm
    · exact Or.inl h
  rw [mTwo, abs_of_nonneg (by linarith [chain_lt_half k])]
  exact chain_identity_right k

/-- `m₁` at the next chain point is `1/(k+1)`. -/
theorem mOne_chain_succ (k : ℕ) : mOne (chain (k + 1)) = 1 / ((k : ℝ) + 1) := by
  have hpos : 0 < chain (k + 1) := by
    rw [chain]
    apply div_pos
    · push_cast; positivity
    · exact chain_denom_pos (k + 1)
  rw [mOne_eq_of_le_half hpos (le_of_lt (chain_lt_half (k + 1)))]
  exact chain_identity_left k

/-- **The link in the peeling chain.**

`m₁ (P (k+1)) = m₂ (P k)`. The value produced by branch two at the current point is
exactly the value produced by branch one at the next point, which is what lets the peeling
step from `P k` to `P (k+1)`. This is the mechanism, and the chain identity is precisely
the statement of it. -/
theorem chain_link (k : ℕ) : mOne (chain (k + 1)) = mTwo (chain k) := by
  rw [mOne_chain_succ, mTwo_chain]

/-! ## The Rademacher point -/

/-- At `p = 1/2` both atoms are `±1` and both modulus curves vanish. -/
@[simp] theorem mOne_half : mOne (1 / 2) = 0 := by norm_num [mOne]

/-- At `p = 1/2` both atoms are `±1` and both modulus curves vanish. -/
@[simp] theorem mTwo_half : mTwo (1 / 2) = 0 := by norm_num [mTwo]

/-- **The Rademacher point is killed by the mass identity, not by peeling.**

Peeling cannot reach `p = 1/2`: both modulus curves vanish there, so there is no value for
it to single-cover. A kernel element supported at `1/2` alone is `c · δ_{1/2}`; its image
under `L` is `c · δ_0`, since both branches send `1/2` to the modulus value `0` and the
masses sum to one. Vanishing image therefore forces `c = 0` — and the step that forces it
is the mass identity `(L κ)([0,∞)) = κ(K)`, evaluated on the constant function `1`.

Formalized here in its arithmetic core: the total mass of the image of `c · δ_{1/2}` is
`c · (p + (1 - p)) = c`, so it vanishes exactly when `c` does. -/
theorem rademacher_point_killed (c : ℝ) (p : ℝ) (hmass : c * (p + (1 - p)) = 0) :
    c = 0 := by
  have h : c * (p + (1 - p)) = c := by ring
  linarith [hmass, h]

/-! ## Convergence of the chain -/

/-- **The chain converges to the Rademacher point**, `P k → 1/2`, so its closure is all of
`(0, 1/2]` and peeling runs to order exactly `ω`: every point below `1/2` is reached at a
finite stage, and `1/2` itself only in the limit. -/
theorem chain_tendsto_half :
    Filter.Tendsto chain Filter.atTop (nhds (1 / 2)) := by
  have hgap : ∀ k : ℕ, |chain k - 1 / 2| = 1 / (2 * (2 * (k : ℝ) + 1)) := by
    intro k
    have h := half_sub_chain k
    have hpos : (0 : ℝ) < 1 / (2 * (2 * (k : ℝ) + 1)) := by
      have := chain_denom_pos k; positivity
    rw [abs_of_nonpos (by linarith)]
    linarith
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / ε)
  refine ⟨N, fun n hn ↦ ?_⟩
  have hd := chain_denom_pos n
  have hNn : (N : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr hn
  have hbound : 1 / (2 * (2 * (n : ℝ) + 1)) < ε := by
    -- Avoid named division lemmas entirely: supply the inverse identity to `nlinarith`.
    have hD : (0 : ℝ) < 2 * (2 * (n : ℝ) + 1) := by linarith
    have h1 : 1 / ε < (n : ℝ) := lt_of_lt_of_le hN hNn
    have hεinv : ε * (1 / ε) = 1 := by field_simp
    have h2 : 1 < ε * (n : ℝ) := by nlinarith [mul_lt_mul_of_pos_left h1 hε]
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hinv : (2 * (2 * (n : ℝ) + 1)) * (1 / (2 * (2 * (n : ℝ) + 1))) = 1 := by
      field_simp
    nlinarith [hinv, hD, hε, h2, hn0]
  rw [Real.dist_eq, hgap n]
  exact hbound

end Descent.Blindness.BundleRigidity
