/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.AncestralLocality.CompatibilityNeutrality

assert_below Descent.PopGen Descent.Spectral Descent.Blindness Descent.Conditionals
assert_below Descent.Portability Descent.Decision Descent.Program

/-!
# Joint non-autonomy: autonomous observations are not closed under joins

The spec is `ANCESTRAL_LOCALITY.md` §3.2, from the research note "Ancestral locality" of
11 September 2026: two observations can each be hereditarily autonomous (2.2) while their joint
observation is not. `CompatibilityNeutrality` has both halves, on the eight-state witness of §5.2.

Take `witnessGraph`, the single rule "exchange `a` only when the parents agree at `h`" on the
features `(a, b, h) = (0, 1, 2)` of `Fin 3`. The observation `z ↦ z_a` is autonomous, with the
observed kernel `K̄(u, v; o) = 1{u = o}/2 + 1{v = o}/2` that Theorem 3 (4.4) gives through
`compatibilityKernel_marginal`, and so is `z ↦ z_b`, with the same kernel. Their joint
observation `z ↦ (z_a, z_b)` has no observed kernel, `witness_not_autonomous`: the parental pairs
`(000, 110)` and `(000, 111)` are both observed as `(00, 11)`, yet the offspring shows `11` with
probability zero from the first and `1/2` from the second.
`autonomous_features_joint_not_autonomous` states the three facts as one theorem.

Autonomy is written out as `witness_not_autonomous` writes it: the existence of `K̄` with
`K_G(x,y; π⁻¹(o)) = K̄(πx, πy; o)` for all `x, y, o`. This is the smallest instance of the remark
of §5.1 that autonomous coordinate observations are not closed under joins.

## Empirical status

None. The statement is an identity and a non-existence between finite sums of kernel weights on
Boolean genomes, so no measurement can bear on it.
-/

namespace Descent.Pangenome.AncestralLocality

open Finset

/-- **§3.2: two autonomous observations whose joint observation is not autonomous.** Under the
witness rule `witnessGraph`, the observations of the features `a = 0` and `b = 1` each satisfy
the autonomy equation (2.2), with the kernel `K̄(u, v; o) = 1{u = o}/2 + 1{v = o}/2`, while their
joint observation `z ↦ (z_a, z_b)` admits no kernel on observed states. -/
theorem autonomous_features_joint_not_autonomous :
    (∃ Kbar : Bool → Bool → Bool → ℝ, ∀ x y o,
      ∑ z ∈ univ.filter (fun z : Fin 3 → Bool ↦ z 0 = o),
          compatibilityKernel witnessGraph x y z =
        Kbar (x 0) (y 0) o) ∧
      (∃ Kbar : Bool → Bool → Bool → ℝ, ∀ x y o,
        ∑ z ∈ univ.filter (fun z : Fin 3 → Bool ↦ z 1 = o),
            compatibilityKernel witnessGraph x y z =
          Kbar (x 1) (y 1) o) ∧
      ¬ ∃ Kbar : (Bool × Bool) → (Bool × Bool) → (Bool × Bool) → ℝ, ∀ x y o,
        ∑ z ∈ univ.filter (fun z : Fin 3 → Bool ↦ (z 0, z 1) = o),
            compatibilityKernel witnessGraph x y z =
          Kbar (x 0, x 1) (y 0, y 1) o := by
  refine ⟨⟨fun u v o ↦ (if u = o then 1 else 0) / 2 + (if v = o then 1 else 0) / 2,
      fun x y o ↦ compatibilityKernel_marginal witnessGraph 0 o x y⟩,
    ⟨fun u v o ↦ (if u = o then 1 else 0) / 2 + (if v = o then 1 else 0) / 2,
      fun x y o ↦ compatibilityKernel_marginal witnessGraph 1 o x y⟩, ?_⟩
  exact witness_not_autonomous

end Descent.Pangenome.AncestralLocality
