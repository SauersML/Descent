/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.RealizationBody
import Descent.Portability.EulerInvariantSet

assert_below Descent.Decision Descent.Program

/-!
# The realization body is preserved by a positively approximated semigroup

This module joins the two halves of NOTE1 §2: the abstract invariance theorem of
`Descent.Portability.EulerInvariantSet` and the probabilistic meaning of the body given in
`Descent.Portability.RealizationBody`. The main result `exp_mulVec_mem_realizationBody` is
NOTE1 Theorem 1 in the form actually wanted: if the feature map `φ` admits a microscopic
approximation of the generator `A` by genuine finite mixture kernels, and the realization
body of `φ` is closed, then `exp(tA)` carries the body into itself for every `t ≥ 0`.

The step map required by the abstract theorem is built here. For a point `v` of the body,
`mem_realizationBody_iff` supplies a finitely supported law realizing `v`; pushing that law
through the kernel `K_h` gives a finitely supported law again, whose feature vector is the
image point. The map is not canonical -- it depends on the realizing law chosen, and the
choice is made once by `choose` -- but the abstract theorem only needs a function with the
two stated properties, so nothing depends on the choice. The uniform first-order estimate
is checked coordinatewise: the difference between the pushforward feature vector and the
Euler step is the law's average of the per-state expansion errors, so the bound of the
approximation passes through the average unchanged, by `abs_law_average_le`.

`propagator_mulVec_mem_realizationBody` specialises this to a corpus epoch: whenever a
microscopic approximation of `LowOrderLDEpoch.generator` exists, `LowOrderLDEpoch.propagator`
maps the corpus body into itself. `split_mulVec_mem_realizationBody` is the instantaneous
half, and it needs no approximation at all: a split copies a haplotype vector, so the corpus
construction `LowOrderLDHaplotypeRealization.split` already relabels the realizing law.
`propagate_mem_realizationBody` is the list induction over `LowOrderLDInstruction` lists,
taking body preservation of each instruction as the hypothesis those two lemmas discharge.

`dd_quadraticForm_nonneg_of_mem`, `dd_cauchySchwarz_of_mem` and `dd_diagonal_nonneg_of_mem`
are NOTE1 Corollary 2.1 for a point of the corpus body. They are not reproved here: the
point of the body carries a haplotype realization, whose derived Gram witness already
satisfies the corpus theorems `LowOrderLDDDRealization.dd_quadraticForm_nonneg` and
`dd_cauchySchwarz`. Combined with `LowOrderLDHaplotypeRealization.toLDPairDomain`, a point of
the body with positive `DD` diagonals therefore reaches the normalised portability domain.

`enlargedLowOrderLDFeature` is the enlarged coordinate family of NOTE1 (6), carrying the
right-locus heterozygosities `H^R` alongside the stored coordinates, on the coordinate type
`Option (LowOrderLDCoordinate D ⊕ (Fin D × Fin D))`. `locusExchangeableRealizationOfLaw`
is the point of NOTE1 (12): a law whose enlarged feature vector identifies `H` with `H^R`
realizes the stored state locus-exchangeably, which is the hypothesis the closed mutation
row of the corpus generator needs.

What is NOT proved here: the closedness of the corpus body (a hypothesis throughout), the
existence of a microscopic approximation for the corpus generator (NOTE1 §2.3, built
elsewhere), the invariance of the subspace (12) under the enlarged generator (NOTE1 Theorem
2), and the time-varying case NOTE1 §2.4.

## Empirical status

None. The bodies here are algebra: averages of polynomial coordinates against a finitely
supported probability vector, and a limit of matrix products. No measurement can bear on
whether a convex hull is mapped into itself.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.KernelRealizationPreservation

open Descent.Portability.FiniteMixtureKernel
open Descent.Portability.RealizationBody
open Descent.Coalescent

noncomputable section

/-- A law's average of uniformly bounded quantities obeys the same bound. This is the
law-side companion of `FiniteMixtureKernel.apply_le_of_le`, which is the kernel-side one. -/
theorem abs_law_average_le {Ω : Type*} [Fintype Ω] (p : Ω → ℝ) (hp : ∀ ω, 0 ≤ p ω)
    (hsum : ∑ ω, p ω = 1) (g : Ω → ℝ) (M : ℝ) (hg : ∀ ω, |g ω| ≤ M) :
    |∑ ω, p ω * g ω| ≤ M := by
  calc |∑ ω, p ω * g ω| ≤ ∑ ω, |p ω * g ω| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ ω, p ω * M := by
        refine Finset.sum_le_sum fun ω _ ↦ ?_
        rw [abs_mul, abs_of_nonneg (hp ω)]
        exact mul_le_mul_of_nonneg_left (hg ω) (hp ω)
    _ = M := by rw [← Finset.sum_mul, hsum, one_mul]

/-- A matrix applied to a law's feature vector is the law's average of the matrix applied to
each atom's feature vector. -/
theorem mulVec_featureVector {Ω X ι : Type*} [Fintype Ω] [Fintype ι] (A : Matrix ι ι ℝ)
    (p : Ω → ℝ) (point : Ω → X) (φ : X → ι → ℝ) (i : ι) :
    (A.mulVec (featureVector p point φ)) i = ∑ ω, p ω * (A.mulVec (φ (point ω))) i := by
  simp only [Matrix.mulVec, dotProduct, featureVector_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun ω _ ↦ Finset.sum_congr rfl fun j _ ↦ by ring

/-- **NOTE1 Theorem 1 for realization bodies.** If the feature map admits a microscopic
approximation of `A` by genuine finite mixture kernels and its realization body is closed,
then the semigroup generated by `A` carries the body into itself at every nonnegative time.
Assumes: the body is closed; the approximation is supplied as data. -/
theorem exp_mulVec_mem_realizationBody {ι B X : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype B] (φ : X → ι → ℝ) (A : Matrix ι ι ℝ)
    (approx : MicroscopicApproximation (B := B) φ A)
    (hclosed : IsClosed (realizationBody φ)) (t : ℝ) (ht : 0 ≤ t) (v : ι → ℝ)
    (hv : v ∈ realizationBody φ) :
    (matrixExponential A t).mulVec v ∈ realizationBody φ := by
  classical
  have hstep : ∀ h : ℝ, ∀ u : ι → ℝ, ∃ w : ι → ℝ,
      0 < h → u ∈ realizationBody φ →
        w ∈ realizationBody φ ∧
          ‖w - (u + h • A.mulVec u)‖ ≤ h * approx.error h := by
    intro h u
    by_cases hcond : 0 < h ∧ u ∈ realizationBody φ
    · obtain ⟨hh, huu⟩ := hcond
      obtain ⟨Ω, hΩ, p, point, hp, hsum, hfeat⟩ := (mem_realizationBody_iff φ u).mp huu
      refine ⟨featureVector ((approx.kernel h).pushforwardMass p point)
        ((approx.kernel h).pushforwardPoint point) φ, fun _ _ ↦ ⟨?_, ?_⟩⟩
      · exact featureVector_mem_convexHull _
          ((approx.kernel h).pushforwardMass_nonneg p hp point)
          ((approx.kernel h).pushforwardMass_sum p hsum point) _ φ
      · have hnn : 0 ≤ h * approx.error h :=
          mul_nonneg hh.le (approx.error_nonneg h)
        rw [pi_norm_le_iff_of_nonneg hnn]
        intro i
        have hwi : featureVector ((approx.kernel h).pushforwardMass p point)
              ((approx.kernel h).pushforwardPoint point) φ i
            = ∑ ω, p ω * (approx.kernel h).apply (fun y ↦ φ y i) (point ω) := by
          rw [(approx.kernel h).featureVector_pushforward p point φ]
          simp [Finset.sum_apply]
        have hui : u i = ∑ ω, p ω * φ (point ω) i := by
          rw [← hfeat, featureVector_apply]
        have hAi : (A.mulVec u) i = ∑ ω, p ω * (A.mulVec (φ (point ω))) i := by
          rw [← hfeat, mulVec_featureVector]
        have hsumeq : ∑ ω, p ω * ((approx.kernel h).apply (fun y ↦ φ y i) (point ω)
              - φ (point ω) i - h * (A.mulVec (φ (point ω))) i)
            = (featureVector ((approx.kernel h).pushforwardMass p point)
                ((approx.kernel h).pushforwardPoint point) φ
                - (u + h • A.mulVec u)) i := by
          simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hwi, hui, hAi,
            Finset.mul_sum]
          rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
          exact Finset.sum_congr rfl fun ω _ ↦ by ring
        rw [Real.norm_eq_abs, ← hsumeq]
        exact abs_law_average_le p hp hsum _ (h * approx.error h)
          (fun ω ↦ approx.expansion h hh (point ω) i)
    · exact ⟨u, fun hh huu ↦ absurd ⟨hh, huu⟩ hcond⟩
  choose step hstepspec using hstep
  refine EulerInvariantSet.exp_mulVec_mem_of_euler_approx (realizationBody φ) hclosed A step
    ?_ approx.error approx.error_tendsto ?_ t ht v hv
  · intro h hh u hu
    exact (hstepspec h u hh hu).1
  · intro h hh u hu
    exact (hstepspec h u hh hu).2

/-- **NOTE1 Theorem 1 for a corpus epoch.** An epoch whose generator admits a microscopic
approximation propagates every haplotype-realizable low-order state to a
haplotype-realizable one. Assumes: the corpus body is closed. -/
theorem propagator_mulVec_mem_realizationBody {D : ℕ} {B : Type*} [Fintype B]
    (hclosed : IsClosed (realizationBody (lowOrderLDFeature D)))
    (epoch : LowOrderLDEpoch D)
    (approx : MicroscopicApproximation (B := B) (lowOrderLDFeature D) epoch.generator)
    (v : AffineLowOrderLDCoordinate D → ℝ)
    (hv : v ∈ realizationBody (lowOrderLDFeature D)) :
    epoch.propagator.mulVec v ∈ realizationBody (lowOrderLDFeature D) := by
  rw [LowOrderLDEpoch.propagator]
  exact exp_mulVec_mem_realizationBody (lowOrderLDFeature D) epoch.generator approx hclosed
    epoch.duration epoch.duration_nonneg v hv

/-- A split preserves the corpus realization body with no approximation and no limit: the
corpus split of a haplotype realization relabels the very same probability law.
Assumes: the corpus body is closed. -/
theorem split_mulVec_mem_realizationBody {D : ℕ}
    (hclosed : IsClosed (realizationBody (lowOrderLDFeature D)))
    {v : AffineLowOrderLDCoordinate D → ℝ}
    (hv : v ∈ realizationBody (lowOrderLDFeature D)) (parent child : Fin D) :
    (lowOrderLDSplitTransform parent child).mulVec v
      ∈ realizationBody (lowOrderLDFeature D) := by
  obtain ⟨realization⟩ := nonempty_lowOrderLDRealization_of_mem hv
  exact lowOrderLDState_mem_realizationBody hclosed (realization.split parent child)

/-- A whole piecewise-constant demographic history preserves the corpus realization body as
soon as each of its instructions does. This is NOTE1 §2.4 for the corpus's
`LowOrderLDInstruction` lists; the two preceding lemmas discharge the hypothesis for evolve
epochs with an approximation and for splits. -/
theorem propagate_mem_realizationBody {D : ℕ}
    (instructions : List (LowOrderLDInstruction D))
    (hpreserve : ∀ instruction ∈ instructions,
      ∀ w ∈ realizationBody (lowOrderLDFeature D),
        instruction.apply w ∈ realizationBody (lowOrderLDFeature D))
    (initial : AffineLowOrderLDCoordinate D → ℝ)
    (hinitial : initial ∈ realizationBody (lowOrderLDFeature D)) :
    propagateLowOrderLDInstructions instructions initial
      ∈ realizationBody (lowOrderLDFeature D) := by
  induction instructions generalizing initial with
  | nil => simpa [propagateLowOrderLDInstructions] using hinitial
  | cons head rest ih =>
    have hhead : head.apply initial ∈ realizationBody (lowOrderLDFeature D) :=
      hpreserve head (List.mem_cons_self ..) initial hinitial
    have hrest : ∀ instruction ∈ rest, ∀ w ∈ realizationBody (lowOrderLDFeature D),
        instruction.apply w ∈ realizationBody (lowOrderLDFeature D) :=
      fun instruction hmem ↦ hpreserve instruction (List.mem_cons_of_mem head hmem)
    have hfold : propagateLowOrderLDInstructions (head :: rest) initial
        = propagateLowOrderLDInstructions rest (head.apply initial) := rfl
    rw [hfold]
    exact ih hrest (head.apply initial) hhead

/-- NOTE1 Corollary 2.1: the propagated `DD` block of any point of the corpus realization
body is positive semidefinite. Derived from the common haplotype law, not assumed. -/
theorem dd_quadraticForm_nonneg_of_mem {D : ℕ}
    {v : AffineLowOrderLDCoordinate D → ℝ}
    (hv : v ∈ realizationBody (lowOrderLDFeature D)) (weight : Fin D → ℝ) :
    0 ≤ ∑ first, ∑ second, weight first * v (some (.DD first second)) * weight second := by
  obtain ⟨realization⟩ := nonempty_lowOrderLDRealization_of_mem hv
  exact realization.toDDDRealization.dd_quadraticForm_nonneg weight

/-- NOTE1 (13): every `DD` diagonal of a point of the corpus realization body is
nonnegative. -/
theorem dd_diagonal_nonneg_of_mem {D : ℕ}
    {v : AffineLowOrderLDCoordinate D → ℝ}
    (hv : v ∈ realizationBody (lowOrderLDFeature D)) (deme : Fin D) :
    0 ≤ v (some (.DD deme deme)) := by
  obtain ⟨realization⟩ := nonempty_lowOrderLDRealization_of_mem hv
  exact realization.toDDDRealization.dd_diagonal_nonneg deme

/-- NOTE1 (13): the Cauchy--Schwarz inequality on the `DD` block of a point of the corpus
realization body. Valid without strict positivity of the diagonal. -/
theorem dd_cauchySchwarz_of_mem {D : ℕ}
    {v : AffineLowOrderLDCoordinate D → ℝ}
    (hv : v ∈ realizationBody (lowOrderLDFeature D)) (first second : Fin D) :
    v (some (.DD first second)) ^ 2
      ≤ v (some (.DD first first)) * v (some (.DD second second)) := by
  obtain ⟨realization⟩ := nonempty_lowOrderLDRealization_of_mem hv
  exact realization.toDDDRealization.dd_cauchySchwarz first second

/-- The enlarged observable family of NOTE1 (6): the stored low-order coordinates together
with the right-locus heterozygosities `H^R`, on the coordinate type
`Option (LowOrderLDCoordinate D ⊕ (Fin D × Fin D))`. The enlargement matters because the
stored model identifies expected left and right heterozygosities rather than the frequencies
pointwise, so the two families must be carried separately before the generator acts. -/
def enlargedLowOrderLDFeature (D : ℕ) :
    (Fin D → TwoLocusHaplotypeFrequencies) →
      Option (LowOrderLDCoordinate D ⊕ (Fin D × Fin D)) → ℝ :=
  fun state coordinate ↦
    match coordinate with
    | none => 1
    | some (Sum.inl c) => twoLocusJetMoment state c
    | some (Sum.inr pair) =>
        twoLocusRightHeterozygosity (state pair.1) (state pair.2)

/-- The affine coordinate of the enlarged family is identically one. -/
@[simp] theorem enlargedLowOrderLDFeature_none (D : ℕ)
    (state : Fin D → TwoLocusHaplotypeFrequencies) :
    enlargedLowOrderLDFeature D state none = 1 := rfl

/-- On the stored coordinates the enlarged family is the corpus feature map. -/
@[simp] theorem enlargedLowOrderLDFeature_inl (D : ℕ)
    (state : Fin D → TwoLocusHaplotypeFrequencies) (c : LowOrderLDCoordinate D) :
    enlargedLowOrderLDFeature D state (some (Sum.inl c))
      = lowOrderLDFeature D state (some c) := rfl

/-- On the new coordinates the enlarged family is the right-locus heterozygosity. -/
@[simp] theorem enlargedLowOrderLDFeature_inr (D : ℕ)
    (state : Fin D → TwoLocusHaplotypeFrequencies) (first second : Fin D) :
    enlargedLowOrderLDFeature D state (some (Sum.inr (first, second)))
      = twoLocusRightHeterozygosity (state first) (state second) := rfl

/-- NOTE1 (12). A finitely supported law whose enlarged feature vector identifies the left-
and right-locus heterozygosity coordinates realizes its stored low-order state
locus-exchangeably, which is exactly what the closed mutation row of the corpus generator
requires. The law is taken as data, so this is a construction and not an existence claim. -/
def locusExchangeableRealizationOfLaw {D : ℕ} {Ω : Type} [Fintype Ω] (p : Ω → ℝ)
    (hp : ∀ ω, 0 ≤ p ω) (hsum : ∑ ω, p ω = 1)
    (point : Ω → Fin D → TwoLocusHaplotypeFrequencies)
    (hexchange : ∀ first second,
      featureVector p point (enlargedLowOrderLDFeature D)
          (some (Sum.inl (.H first second)))
        = featureVector p point (enlargedLowOrderLDFeature D)
            (some (Sum.inr (first, second)))) :
    LocusExchangeableLowOrderLDHaplotypeRealization
      (featureVector p point (lowOrderLDFeature D)) where
  toLowOrderLDHaplotypeRealization := lowOrderLDRealizationOfLaw p hp hsum point
  H_right_eq first second := by
    have hleft := hexchange first second
    rw [featureVector_apply, featureVector_apply] at hleft
    rw [featureVector_apply]
    simpa only [enlargedLowOrderLDFeature_inl, enlargedLowOrderLDFeature_inr,
      weightedExp_apply] using hleft

end

end Descent.Portability.KernelRealizationPreservation
