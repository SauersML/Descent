/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Coalescent.Infinite
import Descent.Coalescent.Kernel
import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Mathlib.Tactic

assert_below Descent.Pangenome Descent.PopGen Descent.Spectral Descent.Blindness
assert_below Descent.Conditionals Descent.Portability Descent.Decision Descent.Program

namespace Descent

/-!
# `𝓔` as a subset of `2^{ℕ×ℕ}`, and the measurable structure that comes with it

K-C section 3 opens by saying an equivalence relation on `ℕ` "is of course a subset of
`ℕ × ℕ`, and so `𝓔` can be regarded as a subset of `2^{ℕ×ℕ}`.  If we give `2^{ℕ×ℕ}` its
product topology, `𝓔` is closed."  That sentence is doing real work: it is what gives `𝓔` a
compact metrisable topology and hence the measurable structure in which K-C Theorem 3 and
K-G section 7 build a measure by projective limit.

`Descent.Coalescent.Infinite` proves the set-level statement -- `𝓔` is the projective limit
of the `𝓔ₙ`.  The measure-level statement needs the encoding as well, because Mathlib's
projective-limit machinery is built for product spaces `∀ i, X i` with projections to finite
index sets, and `𝓔ₙ` is not a product.  Kingman's encoding is the translation, and this file
supplies it: `encode` embeds `𝓔` in `ℕ × ℕ → Bool`, injectively, and the σ-algebra pulled
back along it makes every restriction map measurable.

That is the setup step, not the extension theorem.  What is still missing for `n = ∞` is the
extension of a consistent family of measures, and `Descent.Coalescent.Program` continues to
list it.  But it is now missing for a stated reason -- a theorem about measures -- rather
than because the state space had no measurable structure to state it in.

## Main results

- `encode`, `encode_injective`: `𝓔 ↪ 2^{ℕ×ℕ}`, K-C section 3.
- `measurableSpace_EInf`: the σ-algebra `𝓔` inherits.
- `measurable_rel`: each coordinate `R ↦ (i ~ j)` is measurable, which is what "product
  σ-algebra" means here.
- `measurable_restrictInf`: **every `ρ_n` is measurable**, so the finite-dimensional laws of
  a process on `𝓔` are well defined -- the hypothesis a projective limit argument needs.
-/

namespace Coalescent

open MeasureTheory
open scoped Classical

/-- **K-C section 3: `𝓔` as a subset of `2^{ℕ×ℕ}`.** -/
noncomputable def encode (R : EInf) : ℕ × ℕ → Bool := fun p ↦ decide (R.r p.1 p.2)

theorem encode_injective : Function.Injective encode := by
  intro R S h
  refine Setoid.ext fun i j ↦ ?_
  have hij : decide (R.r i j) = decide (S.r i j) := congrFun h (i, j)
  by_cases hR : R.r i j
  · have hS : S.r i j := by
      by_contra hS
      rw [decide_eq_true hR, decide_eq_false hS] at hij
      exact Bool.noConfusion hij
    exact ⟨fun _ ↦ hS, fun _ ↦ hR⟩
  · have hS : ¬ S.r i j := by
      intro hS
      rw [decide_eq_false hR, decide_eq_true hS] at hij
      exact Bool.noConfusion hij
    exact ⟨fun h' ↦ absurd h' hR, fun h' ↦ absurd h' hS⟩

/-- The σ-algebra `𝓔` inherits from `2^{ℕ×ℕ}` -- the one K-C's topology induces, and the one
a projective limit argument would produce a measure on. -/
scoped instance measurableSpace_EInf : MeasurableSpace EInf :=
  MeasurableSpace.comap encode inferInstance

/-- Each coordinate is measurable: whether `i` and `j` are related is a measurable event. -/
theorem measurable_rel (i j : ℕ) : MeasurableSet {R : EInf | R.r i j} := by
  refine ⟨(fun f : ℕ × ℕ → Bool ↦ f (i, j)) ⁻¹' {true}, ?_, ?_⟩
  · exact (measurable_pi_apply (i, j)) (measurableSet_singleton true)
  · ext R
    simp [encode]

/-- Its complement, likewise -- stated because the restriction preimages below are built from
both. -/
theorem measurable_not_rel (i j : ℕ) : MeasurableSet {R : EInf | ¬ R.r i j} := by
  have h := (measurable_rel i j).compl
  have hset : {R : EInf | R.r i j}ᶜ = {R : EInf | ¬ R.r i j} := rfl
  rwa [hset] at h

/-- **Every restriction map is measurable.**

`ρ_n` sends `R` to its restriction to `{1, …, n}`, and the preimage of a single state is the
finitely many coordinate conditions that define it.  With `𝓔ₙ` finite -- and discrete, since
`Descent.Coalescent.Kernel` gives it the top σ-algebra -- that is all measurability requires.

This is the hypothesis Kingman's projective limit needs: without it, "the finite-dimensional
distributions of a process on `𝓔`" is not a well-formed phrase. -/
theorem measurable_restrictInf (n : ℕ) : Measurable (restrictInf n) := by
  refine measurable_to_countable' fun ξ ↦ ?_
  have hpre : (restrictInf n) ⁻¹' {ξ}
      = ⋂ (p : Fin n × Fin n),
          (if ξ.r p.1 p.2 then {R : EInf | R.r (p.1 : ℕ) (p.2 : ℕ)}
            else {R : EInf | ¬ R.r (p.1 : ℕ) (p.2 : ℕ)}) := by
    ext R
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iInter]
    constructor
    · intro hR p
      subst hR
      by_cases hp : (restrictInf n R).r p.1 p.2
      · rw [if_pos hp]
        exact hp
      · rw [if_neg hp]
        exact hp
    · intro hR
      refine Setoid.ext fun x y ↦ ?_
      have hxy := hR (x, y)
      by_cases hp : ξ.r x y
      · rw [if_pos hp] at hxy
        exact ⟨fun _ ↦ hp, fun _ ↦ hxy⟩
      · rw [if_neg hp] at hxy
        exact ⟨fun h ↦ absurd h hxy, fun h ↦ absurd h hp⟩
  rw [hpre]
  refine MeasurableSet.iInter fun p ↦ ?_
  by_cases hp : ξ.r p.1 p.2
  · rw [if_pos hp]
    exact measurable_rel _ _
  · rw [if_neg hp]
    exact measurable_not_rel _ _

/-- **The encoding determines every finite marginal.**

`encode_injective` is the sentence K-C leans on, and `measurable_restrictInf` is what the
projective-limit argument needs, but nothing said the two were about the same object: the
restrictions could have collapsed information the encoding keeps, and the σ-algebra pulled
back along `encode` would then be finer than the one the finite-dimensional laws live in.
This says they agree -- two relations with the same encoding have the same `ρ_n` for every
`n`, so a finite-dimensional law is a function of the encoding and the setup step really is
a setup step. -/
theorem restrictInf_eq_of_encode_eq {R S : EInf} (h : encode R = encode S) (n : ℕ) :
    restrictInf n R = restrictInf n S := by
  rw [encode_injective h]

end Coalescent

end Descent
