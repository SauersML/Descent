/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.PCCorrectability.Geometry
import Descent.HiddenConeAmbiguity

namespace Descent

/-!
# Non-identifiability from aggregate differentiation
-/

/-- Aggregate differentiation alone cannot determine PC correctability: at
fixed positive differentiation, sample size, and marker count, two valid
subgroup sizes lie on opposite sides of the spectral threshold whenever the
balanced contrast is detectable. -/
theorem fst_does_not_determine_pc_correctability
    (n M F : ℝ) (hn : 0 < n) (hM : 0 < M) (hF : 0 < F) :
    bbpProxyThreshold n M < F * n →
      ∃ mBelow mAbove : ℝ,
        0 < mBelow ∧ mBelow < n ∧
        0 < mAbove ∧ mAbove < n ∧
        demographicSpike n F mBelow < bbpProxyThreshold n M ∧
        bbpProxyThreshold n M < demographicSpike n F mAbove := by
  intro hdetectable
  let t := bbpProxyThreshold n M
  have ht : 0 < t := by
    unfold t bbpProxyThreshold
    exact Real.sqrt_pos.2 (div_pos hn hM)
  let mBelow := t / (4 * F)
  let mAbove := n / 2
  have hmBelow_pos : 0 < mBelow := by
    exact div_pos ht (mul_pos (by norm_num) hF)
  have hmBelow_lt : mBelow < n := by
    unfold mBelow
    rw [div_lt_iff₀ (mul_pos (by norm_num) hF)]
    nlinarith [hdetectable]
  have hmAbove_pos : 0 < mAbove := by
    unfold mAbove
    linarith
  have hmAbove_lt : mAbove < n := by
    unfold mAbove
    linarith
  have heffective_below_lt : effectiveSubgroupSize n mBelow < mBelow := by
    unfold effectiveSubgroupSize
    rw [div_lt_iff₀ hn]
    nlinarith
  have hfour_below : 4 * F * mBelow = t := by
    unfold mBelow
    field_simp [hF.ne']
  have hspike_below : demographicSpike n F mBelow < t := by
    unfold demographicSpike
    calc
      4 * F * effectiveSubgroupSize n mBelow < 4 * F * mBelow :=
        mul_lt_mul_of_pos_left heffective_below_lt (mul_pos (by norm_num) hF)
      _ = t := hfour_below
  have hspike_above : t < demographicSpike n F mAbove := by
    have hidentity : demographicSpike n F mAbove = F * n := by
      unfold demographicSpike effectiveSubgroupSize mAbove
      field_simp [hn.ne']
      ring
    rw [hidentity]
    exact hdetectable
  exact ⟨mBelow, mAbove, hmBelow_pos, hmBelow_lt, hmAbove_pos, hmAbove_lt,
    hspike_below, hspike_above⟩

/-!
## The second non-identifiability, and where its boundary sits

The theorem above says one *summary* of the design -- aggregate differentiation -- does
not determine correctability. `Descent.HiddenConeAmbiguity` says something stronger and
about a different object: even the **complete noiseless second-moment content** of the
data does not determine the hidden mixing, and it locates exactly when it does.

Read a decay profile `t : ℕ → ℝ` as the sequence of ancestry mixing scales -- the singular
values of the latent-to-observed map, in the order a PC decomposition returns them.
`BoundedLogDistortion t t'` is the relation "these two hidden explanations differ by a
bounded change of hidden coordinates", which is exactly the ambiguity a PC basis cannot
resolve. The dichotomy below is sharp and has nothing in between:

* **Bounded condition number is rigidity.** If both profiles are trapped between positive
  constants -- finitely many ancestry components, mixing bounded away from zero -- they are
  always equivalent, so nothing is lost by fixing a basis. The class is inhabited by
  constant profiles (`boundedBelowAbove_const`), so this side is not vacuous.
* **Losing the lower bound is total.** Once the mixing decays without a positive floor,
  profiles with identical second-moment observables become inequivalent, and the fiber over
  one observable carries a faithful copy of the universal sigma-compact relation.

For PC correction this is the statement that the number of PCs retained is not the binding
constraint. What binds is whether the retained mixing scales stay above a positive floor.
Below the floor, no amount of second-moment data -- not more markers, not more samples --
distinguishes the hidden structures, because they have the same second moments exactly.
-/

/-- **The identifiability dichotomy for ancestry mixing profiles.**

Both halves at once, at a fixed pair of bounds. The first conjunct is rigidity: any two
mixing profiles confined to `[a, b]` with `a > 0` are related by a bounded change of hidden
coordinates. The second exhibits, over any gap sequence `B`, two coded profiles that are
*not* so related -- an explicit inequivalent pair, taking the coding sequences to be `0`
and `n`, whose `ℓ∞` separation is unbounded by the Archimedean property.

The two conjuncts are stated together because either alone reads as the whole answer and
neither is: the content is that the boundary between them is exactly the positive lower
bound on the mixing, with no intermediate regime.

    Empirical status: NOT AN EMPIRICAL CLAIM -- a statement about which hidden models
    share second-order observables, carrying no assertion about any dataset. -/
theorem ancestryProfile_rigidity_dichotomy (B : ℕ → ℝ) (a b : ℝ) :
    (∀ t t' : ℕ → ℝ, BoundedBelowAbove t a b → BoundedBelowAbove t' a b →
        BoundedLogDistortion t t')
      ∧ ∃ x y : ℕ → ℝ,
          ¬ BoundedLogDistortion (codedDecayProfile B x) (codedDecayProfile B y) := by
  refine ⟨fun t t' ht ht' ↦ rigidity_of_boundedBelowAbove ht ht', ?_⟩
  refine ⟨fun _ ↦ 0, fun n ↦ (n : ℝ), inequivalent_of_unbounded_coding B _ _ ?_⟩
  intro C
  obtain ⟨n, hn⟩ := exists_nat_gt C
  refine ⟨n, ?_⟩
  rwa [zero_sub, abs_neg, abs_of_nonneg (Nat.cast_nonneg n)]

end Descent
