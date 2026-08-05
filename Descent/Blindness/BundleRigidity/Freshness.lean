/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Blindness.BundleRigidity.Realizability

/-!
# Effective independence dimension and the master decay bound

This module imports targeted Mathlib modules **and** `Descent.Blindness.BundleRigidity.Realizability`.
It is therefore **not self-contained**: it does not rest on Mathlib alone, and any claim
that it does contradicts the import block above.

*On the import style.* A module that begins `import Mathlib` pulls in the whole library
and so requires the root `Mathlib.olean`, which is **absent** from the cluster build. Such
a module cannot be built there at all, while every other module in the corpus can. The
imports here are targeted for that reason, matching the rest of `Descent`, which
needs no root olean. Keep them targeted.

## What this replaces

Everywhere else in this development, oscillatory decay was bought by factoring a
characteristic function as a **product over coordinates**. That step needs independence,
and under linkage disequilibrium it is false. The master bound below replaces it once a
genuine contraction of the partial joint expectation has been established.

## The right object is the actual joint amplitude

The object controlling decay is the modulus of the **joint** characteristic function.
A conditional-gain functional may be defined as its negative logarithm; the finite,
zero-safe definition is `Descent.FiniteCoupledPhaseLaw.conditionalGainFunctional`.

One must not replace the joint characteristic function by a product of one-coordinate
conditional expectations. That identity is false under dependence; the copied binary
counterexample is formalized in `Descent.copied_binary_refutes_conditional_product_identity`.
The telescope below therefore begins with `hstep`, an explicit contraction hypothesis on
the actual partial expectation.

`D` is only a sufficient bookkeeping device for a family of such contractions:

```
|E_n| ≤ exp (-θ γ D).
```

It is neither a necessary invariant of a coupling nor an evaluation of the joint gain.
No Gaussian-copula or deterministic-driving evaluation is asserted in this module.

## The quantity `D`

Fix an ordering of the coordinates. Write `ε i` for the per-coordinate contraction
available at step `i` in the conditional-gain sense above, and let `D` be the maximum over
orderings of `∑ i, ε i`. For independent coordinates every `ε i = 1` and `D` is the number
of coordinates; under strong dependence `D` collapses. It is a **lower-bound parameter**,
not a characterization.

## The master theorem

```
| E ∏ᵢ χ_s(t i, X i) |  ≤  exp( - θ · γ(s) · D )
```

with `θ = 1/2` in the current proof.

## The proof is a telescope, and that is why it formalizes cleanly

Condition on the past. The freshness bound splits the conditional law into an `ε` piece
that sees the reference measure and a `1 - ε` piece about which nothing is known, giving

```
|E(χ_s(X n) | past)|  ≤  (1 - ε n) + ε n · |∫ χ_s|  ≤  1 - ε n · γ n(s).
```

Iterating multiplies these, and `1 - x ≤ e^{-x}` converts the product into the
exponential. Both halves are proved here without hypotheses:

* `abs_le_prod_of_step` — the telescope itself, by induction;
* `prod_one_sub_le_exp_neg_sum` — the product-to-exponential conversion.

`master_decay_bound` composes them.

## The audit points, carried honestly

**(AP-α) — the constant is a parameter, not a baked-in `1/2`.** Sequential freshness is
**order-dependent**, and the factor `θ` absorbs the step where the worst half of the fibers
is discarded by Markov to obtain an average `γ`. Whether an order-free simultaneous
splitting improves `θ` beyond `1/2` is open. Because a failure there **weakens constants,
not statements**, `θ` appears as an explicit argument of `master_decay_bound`: any
improved discard constant is substituted without restating the theorem, and any collapse
of the argument shows up as a worse `θ` rather than as a false conclusion.

**(AP-β) — the band hypothesis.** The passage from a *pointwise kernel band* to an
*operator-norm bound on measures*, in the coupled slice theorem, is carried as the named
field `bandToOperatorNorm` of `CoupledSliceHypotheses`. It is not proved here.

The conditional step bound itself is likewise an input (`stepBound`): deriving it from a
genuine conditional law requires the disintegration machinery, which this module does not
carry. What the module *does* prove is that the step bound implies the master bound —
which is the whole of the telescope, and the part that was worth checking.

## Analytic realization is a separate obligation

The former slogan “continuation kills identities, not inequalities” is too coarse.
Analytic continuation constrains the entire labelled configuration wherever a connected
extension exists. It supplies uniqueness, not global existence: positivity, real-root
bounds, collision-free labelling, and exact window coverage must still be checked.

`symmetric_block_moments` proves the finite moment cancellation behind the
four-atom-per-block construction, while `symmetric_atoms_have_modulus` exposes its actual
domain `0 ≤ w ≤ 1`. Those synthetic atoms provide a useful operator stress test, but are
not automatically a Hardy--Weinberg genotype family.

**This does not reopen our own case.** The genotype family has more than two modulus
values, its cycle variety is empty, and M5 is unavailable for two independent reasons: the
image-free region the mechanism needs is empty, and the band has a single return generator
so the required composition cannot be formed.
-/

namespace Descent.Blindness.BundleRigidity

open scoped BigOperators
open Finset

/-! ## The two proved halves of the telescope -/

/-- **The telescope.**

If each conditioning step contracts the partial expectation by a factor `1 - a k`, and the
initial expectation is bounded by one, then the `n`-th partial expectation is bounded by
the product of the contraction factors.

This is the entire iteration of the master theorem, proved by induction. The only sign
condition needed here is `a k ≤ 1`, which makes every contraction factor non-negative. -/
theorem abs_le_prod_of_step (E : ℕ → ℝ) (a : ℕ → ℝ)
    (ha1 : ∀ k, a k ≤ 1)
    (h0 : |E 0| ≤ 1)
    (hstep : ∀ k, |E (k + 1)| ≤ (1 - a k) * |E k|) (n : ℕ) :
    |E n| ≤ ∏ k ∈ range n, (1 - a k) := by
  induction n with
  | zero => simpa using h0
  | succ n ih =>
    have hfac : (0 : ℝ) ≤ 1 - a n := by linarith [ha1 n]
    calc |E (n + 1)| ≤ (1 - a n) * |E n| := hstep n
      _ ≤ (1 - a n) * ∏ k ∈ range n, (1 - a k) := by
          exact mul_le_mul_of_nonneg_left ih hfac
      _ = ∏ k ∈ range (n + 1), (1 - a k) := by
          rw [Finset.prod_range_succ]
          ring

/-- **Product to exponential**: `∏ (1 - a k) ≤ exp (- ∑ a k)`.

Each factor obeys `1 - x ≤ e^{-x}`, and the factors are non-negative, so the products
compare. This is the step that turns the telescope into a decay rate. -/
theorem prod_one_sub_le_exp_neg_sum (a : ℕ → ℝ)
    (ha1 : ∀ k, a k ≤ 1) (n : ℕ) :
    ∏ k ∈ range n, (1 - a k) ≤ Real.exp (-(∑ k ∈ range n, a k)) := by
  have hterm : ∀ k ∈ range n, (1 - a k) ≤ Real.exp (-(a k)) :=
    fun k _ ↦ Real.one_sub_le_exp_neg (a k)
  have hnonneg : ∀ k ∈ range n, (0 : ℝ) ≤ 1 - a k := by
    intro k _
    linarith [ha1 k]
  calc ∏ k ∈ range n, (1 - a k)
      ≤ ∏ k ∈ range n, Real.exp (-(a k)) :=
        Finset.prod_le_prod hnonneg hterm
    _ = Real.exp (∑ k ∈ range n, -(a k)) := (Real.exp_sum _ _).symm
    _ = Real.exp (-(∑ k ∈ range n, a k)) := by rw [Finset.sum_neg_distrib]

/-! ## The master decay bound -/

/-- **The master decay bound.**

`|E ∏ χ| ≤ exp(- ∑ θ · ε k · γ k)`, where `ε k` is the sequential freshness of coordinate
`k` and `γ k` the oscillation gain there.

**The discard constant `θ` is a parameter.** In the current proof `θ = 1/2`, coming from
the Markov step that throws away the worst half of the fibers to obtain an average `γ`.
Audit point AP-α asks whether an order-free simultaneous splitting improves it. Because it
is an argument rather than a literal, a better constant is substituted without restating
the theorem, and a failure of that argument degrades `θ` rather than falsifying anything.

The per-step contraction is the hypothesis `hstep`; deriving it from a genuine conditional
law needs disintegration, which this module does not carry. What is proved here is that
the step bound gives the exponential bound, for **any coupling whatsoever** — which is the
point of the theorem, and the step that replaces the product-of-characteristic-functions
argument everywhere downstream. -/
theorem master_decay_bound (E : ℕ → ℝ) (θ : ℝ) (ε γ : ℕ → ℝ)
    (hle : ∀ k, θ * ε k * γ k ≤ 1)
    (h0 : |E 0| ≤ 1)
    (hstep : ∀ k, |E (k + 1)| ≤ (1 - θ * ε k * γ k) * |E k|) (n : ℕ) :
    |E n| ≤ Real.exp (-(∑ k ∈ range n, θ * ε k * γ k)) := by
  exact le_trans (abs_le_prod_of_step E _ hle h0 hstep n)
    (prod_one_sub_le_exp_neg_sum _ hle n)

/-- **The master bound in terms of the freshness floor `D`.**

If the oscillation gain is uniform, `γ k = γ`, then the exponent is `θ · γ · D` with `D = ∑ ε k` the freshness floor along the chosen ordering. Taking the
maximum over orderings gives `D` and hence the sharpest form of the bound.

For independent coordinates every `ε k = 1`, so `D = n` and the bound recovers the
classical product decay. Under dependence `D` collapses gracefully — which is exactly the
behaviour the product-of-characteristic-functions step could not express. -/
theorem master_decay_bound_uniform (E : ℕ → ℝ) (θ γ : ℝ) (ε : ℕ → ℝ)
    (hle : ∀ k, θ * ε k * γ ≤ 1)
    (h0 : |E 0| ≤ 1)
    (hstep : ∀ k, |E (k + 1)| ≤ (1 - θ * ε k * γ) * |E k|) (n : ℕ) :
    |E n| ≤ Real.exp (-(θ * γ * ∑ k ∈ range n, ε k)) := by
  have hmain := master_decay_bound E θ ε (fun _ ↦ γ) hle h0 hstep n
  have hrw : ∑ k ∈ range n, θ * ε k * γ = θ * γ * ∑ k ∈ range n, ε k := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ ↦ by ring
  rwa [hrw] at hmain

/-! ## The freshness floor `D`

Sequential freshness is **order-dependent**, so `D` is defined as the maximum of the total
freshness over all orderings of the coordinates. Orderings are permutations of `Fin n`;
the coordinate index stays a natural number so that these definitions plug directly into
the telescope above with no re-indexing.
-/

variable {n : ℕ}

/-- There is always at least one ordering, namely the identity. -/
theorem orderings_nonempty :
    (Finset.univ : Finset (Equiv.Perm (Fin n))).Nonempty :=
  ⟨1, Finset.mem_univ _⟩

/-- The **total freshness along one ordering**: `∑ᵢ εᵢ` for that order. -/
def dimSum (fresh : Equiv.Perm (Fin n) → ℕ → ℝ) (σ : Equiv.Perm (Fin n)) : ℝ :=
  ∑ k ∈ range n, fresh σ k

/-- **The freshness floor** `D`: the maximum of total freshness over all orderings of the
coordinates.

It is a lower-bound parameter for the bound proved below, **not** a characterization of any
coupling invariant and **not** an "effective dimension". In particular it must not be cited
as an evaluation of the joint gain: the zero-safe conditional gain functional lives in
`Descent.Conditionals.ConditionalGain`, and the conditional-product identity that would have related
the two is false under dependence, refuted there by the copied-binary counterexample.

For independent coordinates every freshness is `1` and `D = n`. Under dependence `D`
collapses gracefully — it is the number of coordinates' worth of genuinely new randomness
the coupling still carries, and it is exactly the quantity the master bound decays in. -/
noncomputable def effDim (fresh : Equiv.Perm (Fin n) → ℕ → ℝ) : ℝ :=
  Finset.univ.sup' orderings_nonempty (dimSum fresh)

/-- **The maximum is attained**: some ordering realizes `D`. This is what lets the master
bound be stated at `D` rather than at an infimum that might not be achieved — the set of
orderings is finite. -/
theorem effDim_attained (fresh : Equiv.Perm (Fin n) → ℕ → ℝ) :
    ∃ σ : Equiv.Perm (Fin n), dimSum fresh σ = effDim fresh := by
  obtain ⟨σ, _, hσ⟩ :=
    Finset.exists_mem_eq_sup' (orderings_nonempty (n := n)) (dimSum fresh)
  exact ⟨σ, hσ.symm⟩

/-- Every ordering's total freshness is at most `D`. -/
theorem dimSum_le_effDim (fresh : Equiv.Perm (Fin n) → ℕ → ℝ) (σ : Equiv.Perm (Fin n)) :
    dimSum fresh σ ≤ effDim fresh :=
  Finset.le_sup' (dimSum fresh) (Finset.mem_univ σ)

/-- **`D ≤ n`**: freshness is a proportion, so the dimension never exceeds the number of
coordinates. -/
theorem effDim_le_card (fresh : Equiv.Perm (Fin n) → ℕ → ℝ)
    (hle : ∀ σ k, fresh σ k ≤ 1) : effDim fresh ≤ n := by
  refine Finset.sup'_le _ _ fun σ _ ↦ ?_
  calc dimSum fresh σ = ∑ k ∈ range n, fresh σ k := rfl
    _ ≤ ∑ _k ∈ range n, (1 : ℝ) := Finset.sum_le_sum fun k _ ↦ hle σ k
    _ = n := by simp

/-- **`D ≥ 0`**, since freshness is non-negative. -/
theorem effDim_nonneg (fresh : Equiv.Perm (Fin n) → ℕ → ℝ)
    (h0 : ∀ σ k, 0 ≤ fresh σ k) : 0 ≤ effDim fresh := by
  refine le_trans ?_ (dimSum_le_effDim fresh 1)
  exact Finset.sum_nonneg fun k _ ↦ h0 1 k

/-- **The positive control: independent coordinates give `D = n`.**

If every coordinate is fully fresh under every ordering — which is what independence says —
then `D` is exactly the number of coordinates, and the master bound below reduces to the
classical product decay `exp(-θγn)`.

This matters because the definition is otherwise only ever used to prove *upper* bounds on
decay. A quantity that can only shrink is informative only if it is known to attain its
maximum in the case where the classical argument applies, and this is that check. -/
theorem effDim_eq_of_independent (fresh : Equiv.Perm (Fin n) → ℕ → ℝ)
    (hone : ∀ σ k, fresh σ k = 1) : effDim fresh = n := by
  have hconst : ∀ σ : Equiv.Perm (Fin n), dimSum fresh σ = (n : ℝ) := by
    intro σ
    calc dimSum fresh σ = ∑ k ∈ range n, fresh σ k := rfl
      _ = ∑ _k ∈ range n, (1 : ℝ) := Finset.sum_congr rfl fun k _ ↦ hone σ k
      _ = n := by simp
  refine le_antisymm (Finset.sup'_le _ _ fun σ _ ↦ le_of_eq (hconst σ)) ?_
  rw [← hconst 1]
  exact dimSum_le_effDim fresh 1

/-- **The master decay bound, stated at the freshness floor.**

`|E ∏ χ| ≤ exp(-θ · γ · D)`, where `D` is the maximum total freshness over orderings and
`θ` is the discard constant (`1/2` in the current proof). Equivalently `θγD ≤ Γ_s`: a
floor on the conditional gain, sufficient and not necessary.

The hypotheses are taken along an **optimizing ordering** `σ`, which exists by
`effDim_attained`. No independence or regeneration is used in the telescope, but the
coupling must separately discharge the per-step contraction `hstep`; what is proved here
is that those contractions deliver exponential decay in `D`. -/
theorem master_decay_bound_effDim (E : ℕ → ℝ) (θ γ : ℝ)
    (fresh : Equiv.Perm (Fin n) → ℕ → ℝ) (σ : Equiv.Perm (Fin n))
    (hopt : dimSum fresh σ = effDim fresh)
    (hle : ∀ k, θ * fresh σ k * γ ≤ 1)
    (h0 : |E 0| ≤ 1)
    (hstep : ∀ k, |E (k + 1)| ≤ (1 - θ * fresh σ k * γ) * |E k|) :
    |E n| ≤ Real.exp (-(θ * γ * effDim fresh)) := by
  have hmain := master_decay_bound_uniform E θ γ (fresh σ) hle h0 hstep n
  have hsum : ∑ k ∈ range n, fresh σ k = effDim fresh := hopt
  rwa [hsum] at hmain

/-! ## The named inputs

House style: what this development does not prove appears as a named field, so anything
derived from it carries the input in its own type.
-/

/-! A `CoupledSliceHypotheses` structure used to record the unproved inputs as
`Prop`-valued fields. It is removed — nothing consumed it, and a `Prop` field asserts
nothing, being satisfiable by `True`. The inputs, in prose:

* **AP-β.** The passage from a pointwise kernel band to an operator-norm bound on measures,
  in the coupled slice theorem. Not proved here.
* **The per-step contraction** derived from a genuine conditional law by disintegration.
  This is the hypothesis `hstep` of `master_decay_bound`, which is where it belongs: an
  explicit argument of the theorem that uses it, visible in the signature, rather than a
  field of a record nothing reads.
* **AP-α.** Whether an order-free simultaneous splitting improves the discard constant
  beyond `1/2`. Open; a failure weakens constants rather than statements, which is why `θ`
  is an argument of `master_decay_bound` and not a literal.

The contrast between the second item and the other two is the point of this whole edit. A
genuinely used hypothesis appears as a typed argument of the theorem that needs it and
cannot be forgotten; an unused one in a record is decoration. -/

end Descent.Blindness.BundleRigidity
