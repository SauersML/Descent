/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Blindness.BundleRigidity.Coverage

/-!
# Support-level coverage invariance and slotwise bookkeeping

This module imports targeted Mathlib modules **and** `Descent.BundleRigidity.Coverage`,
whose one-parameter coverage sets are the one-slot case of the charged tuples defined here
(`chargedTuples_one_eq_coverers`).

This module proves three finite/set-theoretic ingredients. It does not prove coupled
injectivity or a singular-value bound.

## Coverage is a property of supports

**Coverage — which value cells are charged from which fiber tuples — is determined by the
supports alone.** It does not see the coupling's probabilities, only which tuples are
possible. And the charging floor says exactly that every product tuple is possible. So the
support is the full product, and therefore

> **the coverage structure of an arbitrary coupling with `η > 0` is identical to the
> coverage structure of the independent product.**

That is `charged_eq_of_support_eq` together with `support_eq_product`. Neither is deep —
the first is a congruence and the second is an extensionality — and their shallowness *is*
the result: coupling-invariance of coverage is not an estimate that could degrade, it is an
identity that either holds or fails with the support.

`slot_uniform` shows that single coverage in one coordinate is uniform over spectator
coordinates when the support is a product. `sigmaMin_pow_le` is only the algebraic
iteration of an explicitly assumed per-slot inequality. The missing mathematical bridge
is still substantial: a support identity does not itself supply a peeling estimate,
conditional recursion, transfinite exhaustion, or a smallest-singular-value statement.

In genetics this separates two questions that LD summaries often conflate. A positive
joint genotype-cell floor preserves which multilocus configurations are possible; it does
not quantify how stably their frequencies can be recovered. Pairwise `r²` alone implies
neither a joint floor nor stable inversion.
-/

namespace Descent.Blindness.BundleRigidity

open scoped BigOperators

variable {T : Type*} {d k : ℕ}

/-! ## Coverage depends only on the support -/

/-- The tuples of a support that **charge** the value tuple `v`: every slot has some branch
landing on that slot's value. -/
def chargedTuples (curve : Fin d → T → ℝ) (Sup : Set (Fin k → T)) (v : Fin k → ℝ) :
    Set (Fin k → T) :=
  {t | t ∈ Sup ∧ ∀ i, ∃ j, curve j (t i) = v i}

/-- **One slot of the charged tuples is exactly the coverage set of `Coverage`.**

`ModulusFamily.coverers S v` collects the parameters of `S` at which some branch takes the
value `v`; `chargedTuples` collects the tuples of a support every slot of which is covered.
At `k = 1` the two are the same set, transported along the projection `t ↦ t 0`. That is
what licenses reading the slotwise results here as statements about the peeling machinery:
`slot_uniform` says a value singly covered *in the sense of `Coverage`* pins its slot in
every charging tuple. Should either side change which branches count as covering, this
stops compiling. -/
theorem chargedTuples_one_eq_coverers [TopologicalSpace T] (F : ModulusFamily T d)
    (S : Set T) (v : Fin 1 → ℝ) :
    (fun t : Fin 1 → T ↦ t 0) ''
        chargedTuples (fun j t ↦ F.curve j t) {u : Fin 1 → T | ∀ l, u l ∈ S} v
      = F.coverers S (v 0) := by
  ext x
  constructor
  · rintro ⟨t, ⟨hmem, hcov⟩, rfl⟩
    exact ⟨hmem 0, hcov 0⟩
  · rintro ⟨hxS, j, hj⟩
    refine ⟨fun _ ↦ x, ⟨fun _ ↦ hxS, fun i ↦ ⟨j, ?_⟩⟩, rfl⟩
    rw [Subsingleton.elim i 0]
    exact hj

/-- **Coverage is a function of the support alone.**

Two couplings with the same support have literally the same charged tuples, for every
value tuple. This is a congruence, and that is the point: coupling-invariance of coverage
is an identity, not an estimate that could degrade under a bad coupling. -/
theorem charged_eq_of_support_eq (curve : Fin d → T → ℝ) {Sup Sup' : Set (Fin k → T)}
    (h : Sup = Sup') (v : Fin k → ℝ) :
    chargedTuples curve Sup v = chargedTuples curve Sup' v := by
  rw [chargedTuples, chargedTuples, h]

/-- Full product inclusion together with the obvious reverse inclusion identifies support.

For a concrete finite probability mass function, a uniform positive cell floor is one way
to prove `hfull`; this set-theoretic theorem does not infer it from a conditional law. -/
theorem support_eq_product {Sup : Set (Fin k → T)} {S : Fin k → Set T}
    (hsub : ∀ t ∈ Sup, ∀ i, t i ∈ S i)
    (hfull : ∀ t : Fin k → T, (∀ i, t i ∈ S i) → t ∈ Sup) :
    Sup = {t : Fin k → T | ∀ i, t i ∈ S i} := by
  ext t
  constructor
  · intro ht
    exact hsub t ht
  · intro ht
    exact hfull t ht

/-! ## Uniformity across spectator slots is free -/

/-- **The uniformity the transfinite step was asked to assume, proved.**

If the value `v i` is singly covered within slot `i`'s own support, then **every** tuple
charging `v` has the same slot-`i` coordinate — whatever the other slots do. The spectator
slots impose constraints only on their own coordinates, so they cannot create a second
slot-`i` coverer.

This is why the pre-registered concern about "uniformity across the other slots" does not
bite: under a product support it is not a hypothesis to be verified stage by stage, it is a
one-line consequence of single coverage in the slot. -/
theorem slot_uniform (curve : Fin d → T → ℝ) {S : Fin k → Set T} {v : Fin k → ℝ}
    (i : Fin k)
    (hsingle : {t : T | t ∈ S i ∧ ∃ j, curve j t = v i}.Subsingleton)
    {t t' : Fin k → T}
    (ht : t ∈ chargedTuples curve {u : Fin k → T | ∀ l, u l ∈ S l} v)
    (ht' : t' ∈ chargedTuples curve {u : Fin k → T | ∀ l, u l ∈ S l} v) :
    t i = t' i := by
  obtain ⟨hmem, hcov⟩ := ht
  obtain ⟨hmem', hcov'⟩ := ht'
  exact hsingle ⟨hmem i, hcov i⟩ ⟨hmem' i, hcov' i⟩

/-- The same statement packaged as single coverage of the whole charged set in slot `i`:
the slot-`i` projection of the charged tuples is a subsingleton. -/
theorem chargedTuples_slot_subsingleton (curve : Fin d → T → ℝ) {S : Fin k → Set T}
    {v : Fin k → ℝ} (i : Fin k)
    (hsingle : {t : T | t ∈ S i ∧ ∃ j, curve j t = v i}.Subsingleton) :
    ((fun t : Fin k → T ↦ t i) ''
      chargedTuples curve {u : Fin k → T | ∀ l, u l ∈ S l} v).Subsingleton := by
  rintro x ⟨t, ht, rfl⟩ y ⟨t', ht', rfl⟩
  exact slot_uniform curve i hsingle ht ht'

/-! ## The slotwise constant compounds -/

/-- An explicitly assumed per-slot recurrence compounds to a `k`-fold product.

Each peeled slot degrades the quantitative constant by one factor, so after `k` slots the
smallest singular value is bounded below by `(η / C_*)^k`. Proved by induction on the
number of slots; `hstep` is the per-slot degradation and `hbase` the normalization.

No claim is made here that coverage supplies `hstep`; it is a separate analytic input. -/
theorem sigmaMin_pow_le (η C : ℝ) (hη : 0 < η) (hC : 0 < C) (σ : ℕ → ℝ)
    (hbase : 1 ≤ σ 0) (hstep : ∀ n, (η / C) * σ n ≤ σ (n + 1)) (m : ℕ) :
    (η / C) ^ m ≤ σ m := by
  have hr : 0 < η / C := div_pos hη hC
  induction m with | zero => simpa using hbase
  | succ n ih =>
    calc (η / C) ^ (n + 1) = (η / C) * (η / C) ^ n := by ring
      _ ≤ (η / C) * σ n := mul_le_mul_of_nonneg_left ih (le_of_lt hr)
      _ ≤ σ (n + 1) := hstep n

/-- The numerical lower-bound expression is positive when both constants are positive. -/
theorem sigmaMin_pos (η C : ℝ) (hη : 0 < η) (hC : 0 < C) (m : ℕ) :
    0 < (η / C) ^ m :=
  pow_pos (div_pos hη hC) m

end Descent.Blindness.BundleRigidity
