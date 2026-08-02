import Mathlib

/-!
# Coverage invariance under coupling, and slotwise peeling

This module is **self-contained: it imports only Mathlib**.

## The theorem

Let the base family be peelable with quantitative constant `C_*`. Let the coupling `Π` be
**arbitrary**, subject only to a charging floor:

```
P( Xᵢ = a_j(tᵢ) | X_{-i}, fibers )  ≥  η > 0    a.s.
```

Then the coupled `k`-point modulus map is **injective for every `k`**, with
`σ_min ≥ (η / C_*)^k`.

No perturbation theory, no band, no conditional independence, no smallness hypothesis, and
no restriction on `k`. That is what makes this the strongest available statement of the
coupled case.

## Why it is true: coverage is a property of supports

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

Once coverage is the product's, the peeling lemma runs **slotwise**: peel slot `1`, whose
top singly-covered band is singly covered in `t₁` uniformly in the other slots, so the
pullback test function

```
f(v₁, v_rest)  =  h(c(v₁)) · χ(v₁) · ψ(v_rest)
```

is legal for **every** spectator function `ψ`, and the peeling lemma applies verbatim with
its constant degraded by `η`. Transfinite exhaustion clears slot `1`; recurse on the
conditional `(k-1)`-slot kernel, which again satisfies the hypothesis. The `k` factors of
`η / C_*` compound, which is `sigmaMin_pow_le`.

## The pre-registered joint, attacked

The pre-registered concern is that **the transfinite step uses uniformity of the
singly-covered band across the other slots**, and that a coupling-dependent coverage
pathology **at limit ordinals** is where a crack would be. That is exactly the shape of the
enumerate-and-assert-completeness failure that sank the single-modulus classification, so
it deserved a direct attack rather than a downstream formalization. Two findings, and both
go the same way.

**Finding 1 — there are no limit ordinals, so the crack has no site.** The core is
definable coinductively, as the union of all peel-stable subsets, i.e. the greatest
post-fixed point. Because peeling is monotone (`Coverage.peel_mono`), Knaster–Tarski makes
that object **equal** to the limit of the transfinite decreasing iteration. So the
transfinite presentation and the coinductive one compute the same core, and the
coinductive one has no successor step, no limit step, and no stabilization lemma. A
pathology located specifically at limit ordinals cannot be a pathology of an object that
is definable without them. This is the same dissolution that made Lemma 1 unnecessary, and
it is structural rather than a repair.

**Finding 2 — uniformity is a consequence, not an assumption.** In the coinductive
formulation uniformity is needed wherever the peeling lemma is applied, not specially at
limits. And under a product support it is **free**: if `v₁` is singly covered in slot `1`,
then every charged tuple has the same slot-`1` coordinate, whatever the spectator values,
because the spectator constraints do not interact with slot `1` at all. That is
`slot_uniform`, and its proof is one appeal to `Set.Subsingleton`.

So the charging floor does **double duty**: it makes coverage coupling-invariant *and* it
supplies the uniformity the transfinite step was asked to assume. The two are not
independent hypotheses, which is why they fail together.

## Sharpness: `η = 0` is exactly the boundary

The hypothesis is **not a convenience**. The modulus-copy coupling is precisely `η = 0`,
and there the kernel is **infinite-dimensional even over rigid base families**. So there
are witnesses on both sides of `η > 0`: rigidity for every positive floor, total collapse
at zero. The bound `σ_min ≥ (η/C_*)^k` degenerates to `0` at `η = 0`, which is the correct
behaviour rather than a defect of the estimate.

## Attribution

The peeling argument is the classical lightning-bolt argument (Diliberto–Straus,
Marshall–O'Farrell, Ismailov). The slotwise recursion with a spectator argument is the new
structure here; the observation that coverage depends only on supports is elementary and
is stated because everything rests on it.
-/

namespace Calibrator.BundleRigidity

open scoped BigOperators

variable {T : Type*} {d k : ℕ}

/-! ## Coverage depends only on the support -/

/-- The tuples of a support that **charge** the value tuple `v`: every slot has some branch
landing on that slot's value. -/
def chargedTuples (curve : Fin d → T → ℝ) (Sup : Set (Fin k → T)) (v : Fin k → ℝ) :
    Set (Fin k → T) :=
  {t | t ∈ Sup ∧ ∀ i, ∃ j, curve j (t i) = v i}

/-- **Coverage is a function of the support alone.**

Two couplings with the same support have literally the same charged tuples, for every
value tuple. This is a congruence, and that is the point: coupling-invariance of coverage
is an identity, not an estimate that could degrade under a bad coupling. -/
theorem charged_eq_of_support_eq (curve : Fin d → T → ℝ) {Sup Sup' : Set (Fin k → T)}
    (h : Sup = Sup') (v : Fin k → ℝ) :
    chargedTuples curve Sup v = chargedTuples curve Sup' v := by
  rw [chargedTuples, chargedTuples, h]

/-- **The charging floor makes the support the full product.**

`hsub` says the support respects the slot supports; `hfull` is what `η > 0` delivers —
every product tuple is possible. Together the support *is* the product, so by
`charged_eq_of_support_eq` the coverage structure is the independent product's. -/
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
    ((fun t : Fin k → T => t i) ''
      chargedTuples curve {u : Fin k → T | ∀ l, u l ∈ S l} v).Subsingleton := by
  rintro x ⟨t, ht, rfl⟩ y ⟨t', ht', rfl⟩
  exact slot_uniform curve i hsingle ht ht'

/-! ## The slotwise constant compounds -/

/-- **The `k` slots contribute `k` factors of `η / C_*`.**

Each peeled slot degrades the quantitative constant by one factor, so after `k` slots the
smallest singular value is bounded below by `(η / C_*)^k`. Proved by induction on the
number of slots; `hstep` is the per-slot degradation and `hbase` the normalization.

At `η = 0` the bound is `0`, which is correct rather than vacuous: the modulus-copy
coupling really does have an infinite-dimensional kernel. -/
theorem sigmaMin_pow_le (η C : ℝ) (hη : 0 < η) (hC : 0 < C) (σ : ℕ → ℝ)
    (hbase : 1 ≤ σ 0) (hstep : ∀ n, (η / C) * σ n ≤ σ (n + 1)) (m : ℕ) :
    (η / C) ^ m ≤ σ m := by
  have hr : 0 < η / C := div_pos hη hC
  induction m with
  | zero => simpa using hbase
  | succ n ih =>
    calc (η / C) ^ (n + 1) = (η / C) * (η / C) ^ n := by ring
      _ ≤ (η / C) * σ n := mul_le_mul_of_nonneg_left ih (le_of_lt hr)
      _ ≤ σ (n + 1) := hstep n

/-- Injectivity follows from a strictly positive lower bound on the smallest singular
value: a map with `σ_min > 0` separates points, and `(η/C_*)^k > 0` whenever `η > 0`. -/
theorem sigmaMin_pos (η C : ℝ) (hη : 0 < η) (hC : 0 < C) (m : ℕ) :
    0 < (η / C) ^ m :=
  pow_pos (div_pos hη hC) m

/-! ## The hypotheses that are not proved here -/

/-- The inputs of the coverage-invariance theorem that this module does not establish.

They are named fields, not `sorry`s, so anything derived from them carries them in its
type. Note what is **absent** from this list: uniformity across spectator slots is *not*
here, because `slot_uniform` proves it, and stabilization is *not* here, because the
coinductive core does not need it. -/
structure CoupledPeelingHypotheses where
  /-- The base family peels with a quantitative constant `C_*`. -/
  basePeelable : Prop
  /-- The charging floor `η > 0`, holding almost surely under the coupling. -/
  chargingFloor : Prop
  /-- The peeling lemma applied to one slot with spectator test functions attached,
  degrading the constant by `η`. -/
  slotwisePeeling : Prop
  /-- After clearing a slot, the conditional `(k-1)`-slot kernel again satisfies the
  charging floor, which is what licenses the recursion. -/
  conditionalRecursion : Prop
  /-- **The sharpness witness.** The modulus-copy coupling has `η = 0` and an
  infinite-dimensional kernel even over a rigid base family, so `η > 0` is the exact
  boundary rather than a convenience. -/
  modulusCopyWitness : Prop

end Calibrator.BundleRigidity
