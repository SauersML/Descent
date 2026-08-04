/-
Released under Apache 2.0 license as described in the file LICENSE.
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
import Calibrator.BundleRigidity.SingleModulus

/-!
# Realizability: a conditional symmetric lift and a fold obstruction

This module imports targeted Mathlib modules **and**
`Calibrator.BundleRigidity.SingleModulus`, whose atoms are the `B = 1` case of the lift
built here (`atom_sq_eq_symmetric_atom_sq`, `symmetric_atoms_realize_fourAtom`).

This file isolates the finite algebra that is valid inside the proposed monodromy
picture.  It does **not** assert the global analytic assembly theorem.  Analytic
continuation gives uniqueness only after one has supplied a collision-free labelled
configuration on a connected domain; it does not ensure that an arbitrary germ extends
through the proposed visit pattern while retaining positive weights and real atoms.

## The conditional symmetric lift

Split block `b` into four atoms `±√(1 + w b)` and `±√(1 - w b)`, each at mass `q b / 4`.
Then the mean vanishes by symmetry (`block_mean_zero`) and the variance is

```
∑_b (q b / 4)·[ (1 + w b) + (1 + w b) + (1 - w b) + (1 - w b) ]  =  ∑_b q b  =  1
```

The cancellation is exact, but the lift exists over the reals only when `0 ≤ w b ≤ 1`,
and it is a probability law only when the pooled weights are positive and sum to one.
Those conditions are explicit below.  Thus moments create no *additional* obstruction
inside this admissible symmetric construction; they are not vacuous for an arbitrary
family.

This generalizes to all `B` the `B = 1` identity already recorded in `SingleModulus`
(`fourAtom`), where the same cancellation appears as the fact that the mean identity holds
for *every* `c` and the variance is insensitive to `c`.

## A local fold obstruction

At a fold the two laps are the two branches of one square-root germ. With `τ = √(v₁ - v)`,
the **difference** `(dataᵢ - dataᵢ₊₁)/(2τ)` must stay analytic at `v₁`, so in particular
bounded. A constant numerator divided by `τ` blows up unless the numerator is zero
(`eq_zero_of_bounded_by_linear`). Hence:

> **two constant branches directly paired at a fold must carry the same value.**

That is an earlier obstruction — originally found the hard way, by three failed hand
constructions — reduced to a two-line corollary of boundedness. It is recorded here as a
corollary precisely because a wall discovered empirically and a wall derived from a
criterion are very different objects, and only the second tells you where the next wall is.

Finally, `sin_has_many_zeros` supplies the elementary oscillation witness underlying a
possible fixed-atom/unbounded-visit construction.  Turning those zeros into an exact
eight-atom visit family still requires window, positivity, and no-extra-coverer checks;
the theorem is deliberately named for what it proves.

Biologically, the construction is a synthetic standardized atomic phenotype law.  It is
useful as a stress test for modulus identifiability, but it is not an HWE genotype fiber:
Hardy--Weinberg has three dosage atoms whose probabilities are fixed by allele frequency.
The distinction prevents an abstract realization from being reported as a realizable
genetic panel.
-/

namespace Calibrator.BundleRigidity

open scoped BigOperators
open Finset

/-! ## Item 1: the general-`B` moment identities -/

variable {B : ℕ}

/-- **The mean vanishes identically**, for every block decomposition.

Each block contributes `A - A + C - C = 0` before any summation, so the identity needs no
hypothesis on the weights, the defining values, or `B`. -/
theorem block_mean_zero (q A C : Fin B → ℝ) :
    ∑ b, (q b / 4) * (A b + (-A b) + C b + (-C b)) = 0 := by
  apply Finset.sum_eq_zero
  intro b _
  ring

/-- **The variance identity, for every `B`.**

With `A b ^ 2 = 1 + w b` and `C b ^ 2 = 1 - w b`, each block contributes exactly `q b`,
because the `w b` cancel in pairs *within* the block. So the total is `∑ q b = 1` whatever
the defining values are. -/
theorem block_variance_one (q w A C : Fin B → ℝ)
    (hA : ∀ b, A b ^ 2 = 1 + w b) (hC : ∀ b, C b ^ 2 = 1 - w b)
    (hq : ∑ b, q b = 1) :
    ∑ b, (q b / 4) * (A b ^ 2 + (-A b) ^ 2 + C b ^ 2 + (-C b) ^ 2) = 1 := by
  have hterm : ∀ b ∈ (univ : Finset (Fin B)),
      (q b / 4) * (A b ^ 2 + (-A b) ^ 2 + C b ^ 2 + (-C b) ^ 2) = q b := by
    intro b _
    have h1 : (-A b) ^ 2 = A b ^ 2 := by ring
    have h2 : (-C b) ^ 2 = C b ^ 2 := by ring
    rw [h1, h2, hA b, hC b]
    ring
  rw [Finset.sum_congr rfl hterm]
  exact hq

/-- Four copies of mass `q b / 4` have total mass one when the pooled weights do. -/
theorem block_mass_one (q : Fin B → ℝ) (hq : ∑ b, q b = 1) :
    ∑ b, 4 * (q b / 4) = 1 := by
  convert hq using 1
  refine Finset.sum_congr rfl fun b _ ↦ ?_
  ring

/-- Outer and inner atom magnitudes used by the symmetric lift. -/
noncomputable def outerAtom (w : ℝ) : ℝ := Real.sqrt (1 + w)
noncomputable def innerAtom (w : ℝ) : ℝ := Real.sqrt (1 - w)

/-- Below the admissible range the radicand is nonpositive and Mathlib's square root is `0`, so
the outer atom reports zero amplitude rather than an inadmissible weight. -/
theorem outerAtom_at_inadmissible_weight_is_junk (w : ℝ) (hw : w ≤ -1) :
    outerAtom w = 0 := by
  unfold outerAtom
  exact Real.sqrt_eq_zero_of_nonpos (by linarith)


theorem outerAtom_sq {w : ℝ} (hw : 0 ≤ w) : outerAtom w ^ 2 = 1 + w := by
  exact Real.sq_sqrt (by linarith)

theorem innerAtom_sq {w : ℝ} (hw : w ≤ 1) : innerAtom w ^ 2 = 1 - w := by
  exact Real.sq_sqrt (by linarith)

/-- Both atom pairs induce the intended modulus `|X² - 1| = w`. -/
theorem symmetric_atoms_have_modulus {w : ℝ} (hw0 : 0 ≤ w) (hw1 : w ≤ 1) :
    |outerAtom w ^ 2 - 1| = w ∧ |innerAtom w ^ 2 - 1| = w := by
  rw [outerAtom_sq hw0, innerAtom_sq hw1]
  constructor <;> simp [abs_of_nonneg hw0]

/-! ### The `B = 1` case is the single-modulus family

The two magnitudes above are not a second construction: they are the atom magnitudes a
single-modulus family is forced to use, and the four-atom line of `SingleModulus` is the
one-block case of the lift. -/

/-- **Every atom of a single-modulus family squares to one of these two.**

`SingleModulus.sq_cases` says an atom squares to `1 + v` or to `1 - v`; those are exactly
`outerAtom v ^ 2` and `innerAtom v ^ 2`. So the symmetric lift is not making a choice of
magnitudes — at modulus `v` there is no other pair available, whatever the atom count. -/
theorem atom_sq_eq_symmetric_atom_sq {d : ℕ} {v : ℝ} (hv0 : 0 ≤ v) (hv1 : v ≤ 1)
    (S : SingleModulus d v) (j : Fin d) :
    S.atom j ^ 2 = outerAtom v ^ 2 ∨ S.atom j ^ 2 = innerAtom v ^ 2 := by
  rw [outerAtom_sq hv0, innerAtom_sq hv1]
  exact S.sq_cases j

/-- **Both magnitudes are attained: the one-block lift is the four-atom family.**

`fourAtom` at `c = 0` puts mass `1/4` on each of `±A, ±B` with `A² = 1 + v` and
`B² = 1 - v`. Taking `A = outerAtom v` and `B = innerAtom v` is legitimate exactly on
`0 < v < 1`, where the real-root conditions of `outerAtom_sq` and `innerAtom_sq` and the
strict ordering `innerAtom v < outerAtom v` all hold, and the result is a genuine
`SingleModulus 4 v` whose outer and inner atoms are the ones defined here.

This is the `B = 1` case of `symmetric_block_moments`: one block, four atoms, mean zero and
variance one. The general-`B` statement above is its extension, and the two must agree on
this overlap or one of them has the wrong atoms. -/
theorem symmetric_atoms_realize_fourAtom (v : ℝ) (hv0 : 0 < v) (hv1 : v < 1) :
    ∃ S : SingleModulus 4 v, S.atom 0 = outerAtom v ∧ S.atom 2 = innerAtom v := by
  have hApos : 0 < outerAtom v := by
    unfold outerAtom
    exact Real.sqrt_pos.mpr (by linarith)
  have hBpos : 0 < innerAtom v := by
    unfold innerAtom
    exact Real.sqrt_pos.mpr (by linarith)
  have hBA : innerAtom v < outerAtom v := by
    unfold innerAtom outerAtom
    exact Real.sqrt_lt_sqrt (by linarith) (by linarith)
  exact ⟨fourAtom v (outerAtom v) (innerAtom v) 0 hv0.le (outerAtom_sq hv0.le)
    (innerAtom_sq hv1.le) hApos hBpos hBA (by norm_num), rfl, rfl⟩

/-- Positive pooled weights give positive mass to every one of the four split atoms. -/
theorem split_atom_mass_pos (q : Fin B → ℝ) (hq : ∀ b, 0 < q b) (b : Fin B) :
    0 < q b / 4 := div_pos (hq b) (by norm_num)

/-- **The symmetric block lift satisfies both moment identities.**

Both standardization identities hold *simultaneously and identically*: for every block
count `B`, every vector of defining values `w`, and every weight vector `q` summing to one,
the four-atom-per-block configuration has mean zero and variance one.

The hypotheses state the real-root conditions explicitly. Positivity of masses is a
separate hypothesis when this algebra is packaged as a probability law. -/
theorem symmetric_block_moments (q w A C : Fin B → ℝ)
    (hA : ∀ b, A b ^ 2 = 1 + w b) (hC : ∀ b, C b ^ 2 = 1 - w b)
    (hq : ∑ b, q b = 1) :
    (∑ b, (q b / 4) * (A b + (-A b) + C b + (-C b)) = 0) ∧
      (∑ b, (q b / 4) * (A b ^ 2 + (-A b) ^ 2 + C b ^ 2 + (-C b) ^ 2) = 1) :=
  ⟨block_mean_zero q A C, block_variance_one q w A C hA hC hq⟩

/-! ## Item 3: folds fix constants -/

/-- **A quantity dominated by `M · τ` for all small positive `τ` is zero.**

This is the boundedness step of the fold relation, isolated: `(dataᵢ - dataᵢ₊₁)/(2τ)` stays
analytic, hence bounded, near the fold, which says the numerator is `O(τ)`. -/
theorem eq_zero_of_bounded_by_linear (k M δ : ℝ) (hM : 0 ≤ M) (hδ : 0 < δ)
    (hbound : ∀ τ : ℝ, 0 < τ → τ < δ → |k| ≤ M * τ) : k = 0 := by
  by_contra hk
  have habs : 0 < |k| := abs_pos.mpr hk
  set τ := min (δ / 2) (|k| / (2 * (M + 1))) with hτdef
  have hMpos : (0 : ℝ) < M + 1 := by linarith
  have hτpos : 0 < τ := by
    apply lt_min
    · linarith
    · positivity
  have hτlt : τ < δ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hle := hbound τ hτpos hτlt
  have hτle : τ ≤ |k| / (2 * (M + 1)) := min_le_right _ _
  have hchain : M * τ ≤ M * (|k| / (2 * (M + 1))) :=
    mul_le_mul_of_nonneg_left hτle hM
  have hfrac : M * (|k| / (2 * (M + 1))) < |k| := by
    rw [mul_div_assoc'] at *
    rw [div_lt_iff₀ (by linarith : (0:ℝ) < 2 * (M + 1))]
    nlinarith [habs, hM]
  linarith

/-- **Folds fix constants.**

If two sheets carry constant data `c₁` and `c₂`, the fold relation forces
`|c₁ - c₂| = O(τ)` near the fold, and a constant that is `O(τ)` is zero. So the two
constants agree.

Two directly fold-paired constant branches therefore cannot have different weights. -/
theorem folds_fix_constants (c₁ c₂ M δ : ℝ) (hM : 0 ≤ M) (hδ : 0 < δ)
    (hfold : ∀ τ : ℝ, 0 < τ → τ < δ → |c₁ - c₂| ≤ M * τ) : c₁ = c₂ := by
  have := eq_zero_of_bounded_by_linear (c₁ - c₂) M δ hM hδ hfold
  linarith [sub_eq_zero.mp this]

/-! ## The oscillation ingredient for visit-count witnesses -/

/-- `sin (N t)` has at least `N + 1` explicitly exhibited distinct zeros.

The witness family has a fixed atom count (`8`) and defining value `v* + ε·sin(N t)`, whose
level crossings grow without bound in `N`. This lemma records the counting half: `sin(N t)`
has at least `N + 1` distinct zeros, exhibited explicitly at `t = kπ/N`.

This is the counting ingredient of a high-oscillation analytic construction, not by
itself a theorem about exact coverage blocks. -/
theorem sin_has_many_zeros (N : ℕ) (hN : 0 < N) :
    ∃ f : Fin (N + 1) → ℝ, Function.Injective f ∧
      ∀ k : Fin (N + 1), Real.sin ((N : ℝ) * f k) = 0 := by
  have hNne : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN)
  refine ⟨fun k ↦ (k : ℕ) * Real.pi / (N : ℝ), ?_, ?_⟩
  · intro k k' hkk'
    have hc : Real.pi / (N : ℝ) ≠ 0 := div_ne_zero Real.pi_ne_zero hNne
    have hkreal : (k : ℝ) = (k' : ℝ) := by
      apply mul_right_cancel₀ hc
      calc
        (k : ℝ) * (Real.pi / (N : ℝ)) = (k : ℝ) * Real.pi / (N : ℝ) := by ring
        _ = (k' : ℝ) * Real.pi / (N : ℝ) := hkk'
        _ = (k' : ℝ) * (Real.pi / (N : ℝ)) := by ring
    exact Fin.ext (by exact_mod_cast hkreal)
  · intro k
    have : (N : ℝ) * ((k : ℕ) * Real.pi / (N : ℝ)) = (k : ℕ) * Real.pi := by
      field_simp
    rw [this]
    exact Real.sin_nat_mul_pi _

end Calibrator.BundleRigidity
