/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Coalescent.Process
import Mathlib.Probability.Kernel.Basic
import Mathlib.Tactic

namespace Descent

/-!
# `𝓔ₙ` is finite, and the jump chain is a Markov kernel

Kingman opens K-C section 1 with "Because `𝓔ₙ` is finite, such chains exist and all have the
same finite-dimensional distributions".  The finiteness is used and not proved -- it is
obvious -- but a formalisation cannot use what it has not got, and every counting argument
in this group has so far had to obtain finiteness of the pieces it needed by hand.
`instFiniteER` proves it once: a relation on `Fin n` is determined by the family of its
classes, and there are finitely many such families.

With that in place the jump chain becomes an object of Mathlib's probability library rather
than a family of hand-rolled mass functions: `jumpKernel` is a `ProbabilityTheory.Kernel`
on `𝓔ₙ`, and it is a Markov kernel.  The corpus had no kernel of any kind before this; every
genealogical claim in it was a claim about a scalar summary of a process that was never
written down.

The kernel is total, which requires deciding what an absorbed chain does.  K-C (1.10) makes
`Θ` absorbing for the continuous-time chain, and the jump chain "terminates on reaching a
state with `q_ξ = 0`".  A total kernel cannot terminate, so it holds: at a state with one
block the kernel is the point mass there.  That is a modelling choice about a convention,
not about biology, and `jumpKernel_absorbing` states it explicitly rather than leaving it to
be discovered in the definition.

## Main results

- `instFiniteER`: `𝓔ₙ` is finite -- K-C section 1's opening remark, proved.
- `jumpKernel`: the jump chain as a `ProbabilityTheory.Kernel`.
- `jumpKernel_isMarkovKernel`: it is a Markov kernel.
- `jumpKernel_absorbing`: at one block it is the point mass, the convention K-C (1.10)
  needs a total kernel to make.
- `jumpKernel_apply_cover`: its mass on each cover is K-C (2.2).
-/

namespace Coalescent

open MeasureTheory ProbabilityTheory

/-- **`𝓔ₙ` is finite.**  K-C section 1 asserts this in passing; here it is, from the
observation that a relation is determined by the family of sets `{y ; y ~ x}`. -/
instance instFiniteER (n : ℕ) : Finite (ER n) := by
  classical
  refine Finite.of_injective
    (fun ξ : ER n => fun y => Finset.univ.filter (fun z => ξ.r z y)) ?_
  intro ξ η h
  refine Setoid.ext fun x y => ?_
  have hxy : Finset.univ.filter (fun z => ξ.r z y) = Finset.univ.filter (fun z => η.r z y) :=
    congrFun h y
  constructor
  · intro hr
    have hmem : x ∈ Finset.univ.filter (fun z => ξ.r z y) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ x, hr⟩
    rw [hxy] at hmem
    exact (Finset.mem_filter.mp hmem).2
  · intro hr
    have hmem : x ∈ Finset.univ.filter (fun z => η.r z y) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ x, hr⟩
    rw [← hxy] at hmem
    exact (Finset.mem_filter.mp hmem).2

noncomputable instance instFintypeER (n : ℕ) : Fintype (ER n) := Fintype.ofFinite _

/-- The state space is discrete: every set of relations is measurable.  Nothing is lost by
this -- the space is finite -- and it is what lets the kernel below be a kernel without a
measurability argument. -/
instance instMeasurableSpaceER (n : ℕ) : MeasurableSpace (ER n) := ⊤

/-- The one-step law of the jump chain as a mass function on the whole state space: uniform
on the covers when there is anywhere to go, and the point mass otherwise. -/
noncomputable def jumpLaw {n : ℕ} (ξ : ER n) : PMF (ER n) :=
  if h : 2 ≤ blocks ξ then (jumpStep ξ h).map Subtype.val else PMF.pure ξ

/-- **The jump chain of the `n`-coalescent as a Markov kernel on `𝓔ₙ`.**

Empirical status: NOT AN EMPIRICAL CLAIM.  The transition law is forced by K-C (1.3)'s unit
rates and the cover count (`jumpStep_apply_eq_jumpProb`); the only free choice is what an
absorbed chain does, and `jumpKernel_absorbing` records the convention taken. -/
noncomputable def jumpKernel (n : ℕ) : Kernel (ER n) (ER n) where
  toFun ξ := (jumpLaw ξ).toMeasure
  measurable' := measurable_from_top

@[simp] theorem jumpKernel_apply {n : ℕ} (ξ : ER n) :
    jumpKernel n ξ = (jumpLaw ξ).toMeasure := rfl

/-- Every row is a probability measure, so the jump chain loses no mass: it is a Markov
kernel. -/
instance jumpKernel_isMarkovKernel (n : ℕ) : IsMarkovKernel (jumpKernel n) :=
  ⟨fun ξ => by
    rw [jumpKernel_apply]
    exact (jumpLaw ξ).toMeasure.isProbabilityMeasure⟩

/-- **The absorbing convention, stated.**  At a state with one block -- `Θ` when the sample
is nonempty, K-C (1.10) -- there is no cover to move to, and the total kernel holds where it
is.  Kingman's chain terminates instead; the two agree on everything before absorption, and
differ only in whether "after absorption" is a thing that exists. -/
theorem jumpKernel_absorbing {n : ℕ} (ξ : ER n) (h : blocks ξ < 2) :
    jumpKernel n ξ = Measure.dirac ξ := by
  rw [jumpKernel_apply, jumpLaw, dif_neg (by omega)]
  exact PMF.toMeasure_pure ξ

/-- **The weight the trajectory law puts on one step.**  Pushing the uniform choice of cover
forward into the whole state space keeps its value: each cover of a `k`-block state gets
`1/C(k,2)`, and every other state gets nothing.  This is what makes the weights in
`Descent.Coalescent.Trajectory.chainLaw` explicit rather than implicit in a `bind`. -/
theorem jumpLaw_apply_cover {n : ℕ} {ξ η : ER n} (hk : 2 ≤ blocks ξ) (h : Covers ξ η) :
    jumpLaw ξ η = (((blocks ξ).choose 2 : ℕ) : ENNReal)⁻¹ := by
  classical
  rw [jumpLaw, dif_pos hk, PMF.map_apply]
  rw [tsum_eq_single ⟨η, h⟩ ?_]
  · rw [if_pos rfl, jumpStep_apply]
  · rintro ⟨ζ, hζ⟩ hne
    rw [if_neg]
    intro heq
    exact hne (Subtype.ext heq.symm)

/-- The mass the kernel puts on a single cover is Kingman's `2/(k(k-1))`.  The kernel is not
a new model: it is `Descent.Coalescent.Process.jumpStep` with its values placed in the state
space they belong to. -/
theorem jumpKernel_apply_cover {n : ℕ} (ξ : ER n) (hk : 2 ≤ blocks ξ)
    (η : {η : ER n // Covers ξ η}) :
    ((jumpStep ξ hk) η).toReal = jumpProb (blocks ξ) :=
  jumpStep_apply_eq_jumpProb ξ hk η

end Coalescent

end Descent
