/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.ReplicaMomentCompleteness

assert_below Descent.Decision Descent.Program

/-!
# The tagged source/target mixture and completeness for the joint population law

NOTE 2 section 4 handles a source population law `Q_s` and a target population law `Q_t` that
vary jointly with shared context through one tagged probability vector
`Q_* = ½ δ_s ⊗ Q_s + ½ δ_t ⊗ Q_t` on the disjoint union of the two observation alphabets, and
claims that the replica laws of `Q_*` determine the joint law of the pair, not merely its two
marginal mixing laws. `ReplicaMomentCompleteness` proves completeness on one alphabet and
supplies the tagging map `taggedPair`; this module forms the tagged mixture and derives the
joint completeness from it.

`taggedObservationLaw` is `Q_*` for one fixed pair, as a finite report law on
`Fin ms ⊕ Fin mt`, and `taggedObservationLaw_expectation` is its mixture form: every
expectation under `Q_*` is half the source expectation of the source letters plus half the
target expectation of the target letters. `taggedPoint` is the same vector as a point of the
simplex on the `ms + mt` letters, for a pair of simplex points; it is continuous
(`continuous_taggedPoint`) and injective (`taggedPoint_injective`). For a joint law `joint` of
the pair on the product of the two simplices, `taggedMixture` is the law of `Q_*`, the
pushforward of `joint` by `taggedPoint`, and `replicaLaw_taggedMixture` shows that its replica
probability at a listing of tagged letters is `∫ ∏ᵢ Q_*(zᵢ) d joint`, the probability that
conditionally independent tagged draws read out those letters.

`jointLaw_eq_of_taggedReplicaLaw_eq` is the corollary the note claims: two finite joint laws of
the source/target pair with the same tagged replica laws at every cohort size are equal. The
proof applies `ReplicaMomentCompleteness.measure_eq_of_replicaLaw_eq` to the two tagged
mixtures and then cancels the pushforward, because a continuous injection of a compact space
into a Hausdorff space is a closed embedding and hence a measurable embedding.

Scope: the two alphabets are finite and a population law is a point of a simplex. Retained
context outside the alphabets, which the note says must be kept alongside the replica tests, is
not modelled here.

## Empirical status

None. The bodies here are measure theory on compact simplices: `taggedMixture` is a stipulated
pushforward and every claim is an identity between measures or integrals, so no measurement can
bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.TaggedMixtureCompleteness

open MeasureTheory ReplicaMomentCompleteness

noncomputable section

/-- **NOTE 2 section 4.** The tagged observation law `Q_* = ½ δ_s ⊗ Q_s + ½ δ_t ⊗ Q_t` of one
source law and one target law, as a finite report law on the disjoint union of the two
alphabets. -/
def taggedObservationLaw {ms mt : ℕ} (source : FiniteReportLaw (Fin ms))
    (target : FiniteReportLaw (Fin mt)) : FiniteReportLaw (Fin ms ⊕ Fin mt) where
  mass := taggedPair ms mt source.mass target.mass
  mass_nonneg := (taggedPair_mem ms mt source.mass target.mass
    ⟨source.mass_nonneg, source.mass_sum⟩ ⟨target.mass_nonneg, target.mass_sum⟩).1
  mass_sum := (taggedPair_mem ms mt source.mass target.mass
    ⟨source.mass_nonneg, source.mass_sum⟩ ⟨target.mass_nonneg, target.mass_sum⟩).2

/-- **NOTE 2 section 4, mixture form.** Every expectation under the tagged observation law is
half the source expectation of the source letters plus half the target expectation of the
target letters. -/
theorem taggedObservationLaw_expectation {ms mt : ℕ} (source : FiniteReportLaw (Fin ms))
    (target : FiniteReportLaw (Fin mt)) (metric : Fin ms ⊕ Fin mt → ℝ) :
    (taggedObservationLaw source target).expectation metric =
      source.expectation (fun letter ↦ metric (Sum.inl letter)) / 2 +
        target.expectation (fun letter ↦ metric (Sum.inr letter)) / 2 := by
  simp only [FiniteReportLaw.expectation, taggedObservationLaw, taggedPair,
    Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Finset.sum_div]
  congr 1
  · exact Finset.sum_congr rfl fun letter _ ↦ by ring
  · exact Finset.sum_congr rfl fun letter _ ↦ by ring

/-- The tagged vector of a pair of simplex points, as a point of the simplex on the `ms + mt`
letters of the disjoint union. -/
def taggedPoint (ms mt : ℕ)
    (pair : ↥(stdSimplex ℝ (Fin ms)) × ↥(stdSimplex ℝ (Fin mt))) :
    ↥(stdSimplex ℝ (Fin (ms + mt))) :=
  ⟨fun letter ↦ taggedPair ms mt pair.1 pair.2 (finSumFinEquiv.symm letter),
    ⟨fun letter ↦ (taggedPair_mem ms mt pair.1 pair.2 pair.1.2 pair.2.2).1 _,
      (Equiv.sum_comp finSumFinEquiv.symm (taggedPair ms mt pair.1 pair.2)).trans
        (taggedPair_mem ms mt pair.1 pair.2 pair.1.2 pair.2.2).2⟩⟩

/-- The tagged point depends continuously on the pair. -/
theorem continuous_taggedPoint (ms mt : ℕ) : Continuous (taggedPoint ms mt) := by
  have hvalues : Continuous fun pair : ↥(stdSimplex ℝ (Fin ms)) × ↥(stdSimplex ℝ (Fin mt)) ↦
      fun letter : Fin (ms + mt) ↦ taggedPair ms mt pair.1 pair.2 (finSumFinEquiv.symm letter) :=
    continuous_pi fun letter ↦ (continuous_apply (finSumFinEquiv.symm letter)).comp
      ((continuous_taggedPair ms mt).comp
        (continuous_subtype_val.prodMap continuous_subtype_val))
  exact hvalues.subtype_mk (p := fun point ↦ point ∈ stdSimplex ℝ (Fin (ms + mt)))
    fun pair ↦ (taggedPoint ms mt pair).2

/-- The tagged point determines the pair: tagging is injective on pairs of simplex points. -/
theorem taggedPoint_injective (ms mt : ℕ) : Function.Injective (taggedPoint ms mt) := by
  intro first second hequal
  have hvalues : taggedPair ms mt first.1 first.2 = taggedPair ms mt second.1 second.2 := by
    funext letter
    have hletter := congrArg
      (fun point : ↥(stdSimplex ℝ (Fin (ms + mt))) ↦
        (point : Fin (ms + mt) → ℝ) (finSumFinEquiv letter)) hequal
    simpa only [taggedPoint, Equiv.symm_apply_apply] using hletter
  have hpair : ((first.1 : Fin ms → ℝ), (first.2 : Fin mt → ℝ)) =
      ((second.1 : Fin ms → ℝ), (second.2 : Fin mt → ℝ)) :=
    taggedPair_injective ms mt hvalues
  exact Prod.ext (Subtype.ext (congrArg Prod.fst hpair))
    (Subtype.ext (congrArg Prod.snd hpair))

/-- **NOTE 2 section 4.** The law of the tagged vector `Q_*` when the source/target pair has
joint law `joint`: the pushforward of `joint` by the tagging map. -/
def taggedMixture (ms mt : ℕ)
    (joint : Measure (↥(stdSimplex ℝ (Fin ms)) × ↥(stdSimplex ℝ (Fin mt)))) :
    Measure ↥(stdSimplex ℝ (Fin (ms + mt))) :=
  joint.map (taggedPoint ms mt)

/-- The tagged mixture of a finite joint law is a finite measure. -/
instance taggedMixture_isFiniteMeasure (ms mt : ℕ)
    (joint : Measure (↥(stdSimplex ℝ (Fin ms)) × ↥(stdSimplex ℝ (Fin mt))))
    [IsFiniteMeasure joint] : IsFiniteMeasure (taggedMixture ms mt joint) :=
  Measure.isFiniteMeasure_map joint (taggedPoint ms mt)

/-- The tagged mixture of a joint probability law is a probability law. -/
instance taggedMixture_isProbabilityMeasure (ms mt : ℕ)
    (joint : Measure (↥(stdSimplex ℝ (Fin ms)) × ↥(stdSimplex ℝ (Fin mt))))
    [IsProbabilityMeasure joint] : IsProbabilityMeasure (taggedMixture ms mt joint) :=
  Measure.isProbabilityMeasure_map (continuous_taggedPoint ms mt).measurable.aemeasurable

/-- **NOTE 2 (11) for the tagged mixture.** The replica probability of `Q_*` at a listing of
tagged letters is `∫ ∏ᵢ Q_*(zᵢ) d joint`: the probability that conditionally independent tagged
draws read out those letters, under the joint law of the source/target pair. -/
theorem replicaLaw_taggedMixture (ms mt : ℕ)
    (joint : Measure (↥(stdSimplex ℝ (Fin ms)) × ↥(stdSimplex ℝ (Fin mt))))
    {slots : Type} [Fintype slots] (letters : slots → Fin ms ⊕ Fin mt) :
    replicaLaw (ms + mt) (taggedMixture ms mt joint)
        (fun slot ↦ finSumFinEquiv (letters slot)) =
      ∫ pair, ∏ slot, taggedPair ms mt pair.1 pair.2 (letters slot) ∂joint := by
  have hreadout : Continuous fun point : ↥(stdSimplex ℝ (Fin (ms + mt))) ↦
      ∏ slot, (point : Fin (ms + mt) → ℝ) (finSumFinEquiv (letters slot)) :=
    continuous_finset_prod _ fun slot _ ↦
      (continuous_apply (finSumFinEquiv (letters slot))).comp continuous_subtype_val
  rw [replicaLaw, taggedMixture,
    integral_map (continuous_taggedPoint ms mt).measurable.aemeasurable
      hreadout.measurable.aestronglyMeasurable]
  simp only [taggedPoint, Equiv.symm_apply_apply]

/-- **NOTE 2 section 4, completeness for the joint source/target law.** Two finite joint laws
of the source/target pair with the same tagged replica laws at every cohort size are equal. The
tagged mixtures then have the same replica laws, so they are equal by
`ReplicaMomentCompleteness.measure_eq_of_replicaLaw_eq`, and the tagging map is a measurable
embedding, so the pushforward cancels. -/
theorem jointLaw_eq_of_taggedReplicaLaw_eq (ms mt : ℕ)
    (joint other : Measure (↥(stdSimplex ℝ (Fin ms)) × ↥(stdSimplex ℝ (Fin mt))))
    [IsFiniteMeasure joint] [IsFiniteMeasure other]
    (hreplica : ∀ (n : ℕ) (letters : Fin n → Fin ms ⊕ Fin mt),
      ∫ pair, ∏ slot, taggedPair ms mt pair.1 pair.2 (letters slot) ∂joint =
        ∫ pair, ∏ slot, taggedPair ms mt pair.1 pair.2 (letters slot) ∂other) :
    joint = other := by
  have hembedding : MeasurableEmbedding (taggedPoint ms mt) :=
    ((continuous_taggedPoint ms mt).isClosedEmbedding
      (taggedPoint_injective ms mt)).measurableEmbedding
  have hmixture : taggedMixture ms mt joint = taggedMixture ms mt other := by
    refine measure_eq_of_replicaLaw_eq (ms + mt) _ _ fun n listing ↦ ?_
    have hlisting :
        listing = fun slot ↦ finSumFinEquiv (finSumFinEquiv.symm (listing slot)) :=
      funext fun slot ↦ (finSumFinEquiv.apply_symm_apply (listing slot)).symm
    rw [hlisting, replicaLaw_taggedMixture, replicaLaw_taggedMixture]
    exact hreplica n fun slot ↦ finSumFinEquiv.symm (listing slot)
  rw [← hembedding.comap_map joint, ← hembedding.comap_map other]
  exact congrArg (Measure.comap (taggedPoint ms mt)) hmixture

end

end Descent.Portability.TaggedMixtureCompleteness
