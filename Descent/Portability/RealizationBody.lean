/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.FiniteMixtureKernel
import Descent.Portability.PortabilityMasterTheorem
import Descent.Coalescent.TwoLocusHistory
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.NormedSpace.HahnBanach.Separation
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

assert_below Descent.Decision Descent.Program

/-!
# The realization body of a feature map

The realization body of a feature map `φ : X → ι → ℝ` is the convex hull of its range,
equation (2) of NOTE1 §2.1. This module gives the body its exact probabilistic meaning and
connects it to the haplotype-realization structures of `Descent.Coalescent.TwoLocusHistory`.

`mem_realizationBody_iff` is the characterisation both ways: a vector lies in the body
exactly when it is the feature vector of some finitely supported probability law on `X`.
The forward direction is Carathéodory in the form of Mathlib's
`mem_convexHull_iff_exists_fintype` together with a choice of preimages under `φ`; the
backward direction is the convexity of the hull. `constant_coordinate_eq` records the
normalisation used throughout: if some coordinate of `φ` is identically one, every point of
the body has that coordinate equal to one.

`expFunctional_feature_mem` is the separation argument of NOTE1 §2.1 in its exact form. A
`Descent.Foundations.ExpFunctional` is a normalised positive linear functional with no
countable additivity, so its feature vector need not come from a finitely supported law;
nonetheless, if the body is closed, the feature vector lies in it. The proof separates the
point from the body with `geometric_hahn_banach_point_closed`, expands the separating
continuous functional over the standard basis of `ι → ℝ`, moves the finite sum through the
functional with `ExpFunctional.eval_sum`, and contradicts the strict separation by
monotonicity. Closedness is taken as a hypothesis rather than proved here.

`lowOrderLDFeature D` is the corpus feature map: the affine low-order LD coordinate family
of `AffineLowOrderLDCoordinate D`, with the constant coordinate `none` sent to one and every
other coordinate to the corresponding `twoLocusJetMoment` polynomial of the multi-deme
haplotype-frequency state. `haplotypeLowOrderLDState_eq_eval_lowOrderLDFeature` identifies
the corpus semantic map with evaluation of this feature map under an expectation, which is
what lets the two directions of the realizability correspondence be stated in corpus terms:
`lowOrderLDRealizationOfLaw` builds a `LowOrderLDHaplotypeRealization` from an explicit
finitely supported law using `weightedExp`, and `lowOrderLDState_mem_realizationBody` sends
the state vector of an arbitrary realization back into the body whenever it is closed.

`exists_law_of_mem_realizationBody` is Carathéodory with the ambient dimension: every point of
the body is the feature vector of a law on `Fin (Fintype.card ι + 1)`, obtained from Mathlib's
`eq_pos_convex_span_of_mem_convexHull` together with the affine-independence bound
`AffineIndependent.card_le_finrank_succ` and padding by zero weights.
`isCompact_realizationBody` then gives NOTE1 §2.1's compactness: for a compact space `X` and a
continuous `φ`, the body is the image of the compact set
`stdSimplex ℝ (Fin (card ι + 1)) ×ˢ univ` under the continuous map that reads a law's feature
vector, hence compact, hence closed. That discharges the `IsClosed` hypothesis above whenever
the feature map is continuous on a compact space.

What is NOT proved in this module: the sharpened Carathéodory count of NOTE1 §2.1 (at most
`Fintype.card ι` atoms when a coordinate is constant, rather than the `card ι + 1` proved
here), and the compactness of the corpus body. The latter is not a gap in the argument above
but a missing structure: `Coalescent.TwoLocusHaplotypeFrequencies` carries no topology in the
corpus, so `lowOrderLDFeature` is not yet a continuous map on a compact space and
`isCompact_realizationBody` cannot be applied to it. Supplying that topology, by identifying
the range of the corpus feature map with the image of a product of standard simplices under
the polynomial coordinate formulas, is the remaining step.

## Empirical status

None. The bodies here are algebra and point-set topology: a convex hull, a separating
functional, and a finite sum of polynomial coordinates. No measurement on any population
bears on whether a convex hull contains a point.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.RealizationBody

open Descent.Portability.FiniteMixtureKernel
open Descent.Coalescent

noncomputable section

/-- The realization body of a feature map, NOTE1 (2): the convex hull of the range of `φ`.
Its points are exactly the feature vectors attainable by probability laws on `X`. -/
def realizationBody {X ι : Type*} (φ : X → ι → ℝ) : Set (ι → ℝ) :=
  convexHull ℝ (Set.range φ)

/-- The realization body is convex, being a convex hull. -/
theorem convex_realizationBody {X ι : Type*} (φ : X → ι → ℝ) :
    Convex ℝ (realizationBody φ) :=
  convex_convexHull ℝ (Set.range φ)

/-- Every attainable feature value is in the body. -/
theorem mem_realizationBody_of_range {X ι : Type*} (φ : X → ι → ℝ) (x : X) :
    φ x ∈ realizationBody φ :=
  subset_convexHull ℝ (Set.range φ) (Set.mem_range_self x)

/-- A vector lies in the realization body exactly when it is the feature vector of some
finitely supported probability law on `X`. This is the exact content of NOTE1 (2): the body
is the set of attainable feature vectors, not merely a convex set containing them. -/
theorem mem_realizationBody_iff {X ι : Type*} (φ : X → ι → ℝ) (v : ι → ℝ) :
    v ∈ realizationBody φ ↔
      ∃ (Ω : Type) (_ : Fintype Ω) (p : Ω → ℝ) (point : Ω → X),
        (∀ ω, 0 ≤ p ω) ∧ ∑ ω, p ω = 1 ∧ featureVector p point φ = v := by
  constructor
  · intro hv
    obtain ⟨Ω, hΩ, w, z, hw₀, hw₁, hz, hcomb⟩ :=
      mem_convexHull_iff_exists_fintype.mp hv
    choose point hpoint using hz
    refine ⟨Ω, hΩ, w, point, hw₀, hw₁, ?_⟩
    rw [featureVector, ← hcomb]
    exact Finset.sum_congr rfl fun ω _ ↦ by rw [hpoint ω]
  · rintro ⟨Ω, hΩ, p, point, hp, hsum, rfl⟩
    exact featureVector_mem_convexHull p hp hsum point φ

/-- If one coordinate of the feature map is identically one, then every point of the body
has that coordinate equal to one. This is the affine confinement used in NOTE1 §2.1. -/
theorem constant_coordinate_eq {X ι : Type*} (φ : X → ι → ℝ) (i₀ : ι)
    (hconst : ∀ x, φ x i₀ = 1) (v : ι → ℝ) (hv : v ∈ realizationBody φ) : v i₀ = 1 := by
  have hsubset : realizationBody φ ⊆ {w : ι → ℝ | w i₀ = 1} := by
    refine convexHull_min ?_ ?_
    · rintro _ ⟨x, rfl⟩
      exact hconst x
    · intro a ha b hb s t hs ht hst
      simp only [Set.mem_setOf_eq] at ha hb ⊢
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, ha, hb, mul_one]
      exact hst
  exact hsubset hv

/-- NOTE1 §2.1, the separation argument. A normalised positive linear expectation
functional composed with the feature map lands inside the realization body whenever the
body is closed, even though the functional is not assumed countably additive and need not
be a finitely supported law. Assumes: the body is closed. -/
theorem expFunctional_feature_mem {Ω X ι : Type*} [Fintype ι] (φ : X → ι → ℝ)
    (hclosed : IsClosed (realizationBody φ)) (E : Foundations.ExpFunctional Ω)
    (hap : Ω → X) :
    (fun i ↦ E (fun ω ↦ φ (hap ω) i)) ∈ realizationBody φ := by
  classical
  by_contra hv
  obtain ⟨sep, u, hsepv, hsepb⟩ :=
    geometric_hahn_banach_point_closed (convex_realizationBody φ) hclosed hv
  have hsingle : ∀ (i : ι) (a : ℝ),
      (Pi.single i a : ι → ℝ) = a • (Pi.single i (1 : ℝ) : ι → ℝ) := by
    intro i a
    funext j
    by_cases hj : j = i
    · subst hj
      simp
    · simp [Pi.single_eq_of_ne hj]
  have hrep : ∀ w : ι → ℝ, sep w = ∑ i, w i * sep (Pi.single i (1 : ℝ)) := by
    intro w
    have hw : (∑ i, (Pi.single i (w i) : ι → ℝ)) = w := Finset.univ_sum_single w
    conv_lhs => rw [← hw]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [hsingle i (w i), map_smul, smul_eq_mul]
  have hscale : ∀ (a : ℝ) (g : Ω → ℝ), E (fun ω ↦ g ω * a) = E g * a := by
    intro a g
    have hcomm : (fun ω ↦ g ω * a) = a • g := by
      funext ω
      simp [Pi.smul_apply, smul_eq_mul, mul_comm]
    rw [hcomm, E.smul_eval, mul_comm]
  have hfeval : sep (fun i ↦ E (fun ω ↦ φ (hap ω) i))
      = E (fun ω ↦ sep (φ (hap ω))) := by
    rw [hrep]
    have hswap : (fun ω ↦ sep (φ (hap ω)))
        = Finset.sum Finset.univ
            (fun i ω ↦ φ (hap ω) i * sep (Pi.single i (1 : ℝ))) := by
      funext ω
      rw [hrep (φ (hap ω))]
      simp
    rw [hswap, Foundations.ExpFunctional.eval_sum]
    exact Finset.sum_congr rfl fun i _ ↦ (hscale _ _).symm
  have hge : u ≤ E (fun ω ↦ sep (φ (hap ω))) := by
    have hmono : E (fun _ : Ω ↦ u) ≤ E (fun ω ↦ sep (φ (hap ω))) :=
      Foundations.ExpFunctional.eval_mono E
        (fun ω ↦ (hsepb _ (mem_realizationBody_of_range φ (hap ω))).le)
    simpa using hmono
  rw [hfeval] at hsepv
  exact absurd hsepv (not_lt.mpr hge)

/-- The corpus feature map for `D` demes: the constant coordinate is one and every other
coordinate is the corresponding low-order LD moment polynomial read off a multi-deme
haplotype-frequency state. -/
def lowOrderLDFeature (D : ℕ) :
    (Fin D → TwoLocusHaplotypeFrequencies) → AffineLowOrderLDCoordinate D → ℝ :=
  fun state coordinate ↦
    match coordinate with
    | none => 1
    | some c => twoLocusJetMoment state c

/-- The affine coordinate of the corpus feature map is identically one. -/
@[simp] theorem lowOrderLDFeature_none (D : ℕ)
    (state : Fin D → TwoLocusHaplotypeFrequencies) :
    lowOrderLDFeature D state none = 1 := rfl

/-- Away from the affine coordinate the corpus feature map is the jet moment. -/
@[simp] theorem lowOrderLDFeature_some (D : ℕ)
    (state : Fin D → TwoLocusHaplotypeFrequencies) (c : LowOrderLDCoordinate D) :
    lowOrderLDFeature D state (some c) = twoLocusJetMoment state c := rfl

/-- The corpus semantic moment map is exactly the expectation of the corpus feature map.
This identification is what makes a point of the realization body the same thing as a
haplotype-realizable low-order state. -/
theorem haplotypeLowOrderLDState_eq_eval_lowOrderLDFeature {D : ℕ} {Ω : Type}
    (E : Foundations.ExpFunctional Ω)
    (hap : Ω → Fin D → TwoLocusHaplotypeFrequencies)
    (c : AffineLowOrderLDCoordinate D) :
    haplotypeLowOrderLDState E hap c = E (fun ω ↦ lowOrderLDFeature D (hap ω) c) := by
  match c with
  | none => simp [haplotypeLowOrderLDState]
  | some (.H first second) =>
    simp only [haplotypeLowOrderLDState, lowOrderLDFeature_some, twoLocusJetMoment,
      twoLocusCoordinateJet, twoLocusHJet_value]
  | some (.DD first second) =>
    simp only [haplotypeLowOrderLDState, lowOrderLDFeature_some, twoLocusJetMoment,
      twoLocusCoordinateJet, twoLocusDDJet_value]
  | some (.Dz first second third) =>
    simp only [haplotypeLowOrderLDState, lowOrderLDFeature_some, twoLocusJetMoment,
      twoLocusCoordinateJet, twoLocusDzJet_value]
  | some (.pi2 first second third fourth) =>
    simp only [haplotypeLowOrderLDState, lowOrderLDFeature_some, twoLocusJetMoment,
      twoLocusCoordinateJet, twoLocusPi2Jet_value]

/-- The haplotype realization carried by an explicit finitely supported law: its common
probability law is `weightedExp`, its haplotype random variable is the law's atoms, and its
low-order state is the law's feature vector. The law is taken as data, so no choice is used
and the realization is an honest construction rather than an existence claim. -/
def lowOrderLDRealizationOfLaw {D : ℕ} {Ω : Type} [Fintype Ω] (p : Ω → ℝ)
    (hp : ∀ ω, 0 ≤ p ω) (hsum : ∑ ω, p ω = 1)
    (point : Ω → Fin D → TwoLocusHaplotypeFrequencies) :
    LowOrderLDHaplotypeRealization (featureVector p point (lowOrderLDFeature D)) where
  sampleSpace := Ω
  expectation := weightedExp p hp hsum
  haplotype := point
  constant_eq := by
    rw [featureVector_apply]
    simpa using hsum
  H_eq := fun first second ↦ by
    rw [featureVector_apply]
    simp only [weightedExp_apply, lowOrderLDFeature_some, twoLocusJetMoment,
      twoLocusCoordinateJet, twoLocusHJet_value]
  DD_eq := fun first second ↦ by
    rw [featureVector_apply]
    simp only [weightedExp_apply, lowOrderLDFeature_some, twoLocusJetMoment,
      twoLocusCoordinateJet, twoLocusDDJet_value]
  Dz_eq := fun first second third ↦ by
    rw [featureVector_apply]
    simp only [weightedExp_apply, lowOrderLDFeature_some, twoLocusJetMoment,
      twoLocusCoordinateJet, twoLocusDzJet_value]
  pi2_eq := fun first second third fourth ↦ by
    rw [featureVector_apply]
    simp only [weightedExp_apply, lowOrderLDFeature_some, twoLocusJetMoment,
      twoLocusCoordinateJet, twoLocusPi2Jet_value]

/-- Every point of the corpus realization body carries a genuine common haplotype law: the
finitely supported law supplied by `mem_realizationBody_iff`, read through `weightedExp`.
This is the converse half of NOTE1 §2.1 for the corpus coordinates, and the existential is
only a corollary of the construction above. -/
theorem nonempty_lowOrderLDRealization_of_mem {D : ℕ}
    {v : AffineLowOrderLDCoordinate D → ℝ}
    (hv : v ∈ realizationBody (lowOrderLDFeature D)) :
    Nonempty (LowOrderLDHaplotypeRealization v) := by
  obtain ⟨Ω, hΩ, p, point, hp, hsum, hfeat⟩ :=
    (mem_realizationBody_iff (lowOrderLDFeature D) v).mp hv
  exact ⟨hfeat ▸ lowOrderLDRealizationOfLaw p hp hsum point⟩

/-- The state vector of any haplotype realization lies in the corpus realization body, no
matter how large or how badly behaved its sample space, provided the body is closed. This
is NOTE1 §2.1 applied to the corpus coordinates; together with the realization built above
it says the body is exactly the set of haplotype-realizable low-order states.
Assumes: the body is closed. -/
theorem lowOrderLDState_mem_realizationBody {D : ℕ}
    (hclosed : IsClosed (realizationBody (lowOrderLDFeature D)))
    {v : AffineLowOrderLDCoordinate D → ℝ}
    (realization : LowOrderLDHaplotypeRealization v) :
    v ∈ realizationBody (lowOrderLDFeature D) := by
  have hv : v = fun c ↦ realization.expectation
      (fun ω ↦ lowOrderLDFeature D (realization.haplotype ω) c) := by
    funext c
    match c with
    | none => simpa using realization.constant_eq
    | some (.H first second) =>
      rw [realization.H_eq first second]
      simp only [lowOrderLDFeature_some, twoLocusJetMoment, twoLocusCoordinateJet,
        twoLocusHJet_value]
    | some (.DD first second) =>
      rw [realization.DD_eq first second]
      simp only [lowOrderLDFeature_some, twoLocusJetMoment, twoLocusCoordinateJet,
        twoLocusDDJet_value]
    | some (.Dz first second third) =>
      rw [realization.Dz_eq first second third]
      simp only [lowOrderLDFeature_some, twoLocusJetMoment, twoLocusCoordinateJet,
        twoLocusDzJet_value]
    | some (.pi2 first second third fourth) =>
      rw [realization.pi2_eq first second third fourth]
      simp only [lowOrderLDFeature_some, twoLocusJetMoment, twoLocusCoordinateJet,
        twoLocusPi2Jet_value]
  rw [hv]
  exact expFunctional_feature_mem (lowOrderLDFeature D) hclosed _ _

/-- **Carathéodory with the ambient dimension.** Every point of the realization body is the
feature vector of a finitely supported law with at most `Fintype.card ι + 1` atoms, indexed
by `Fin (Fintype.card ι + 1)`. The affinely independent family supplied by Carathéodory has
at most that many members because the ambient space has dimension `Fintype.card ι`; the
remaining indices are padded with zero weight. -/
theorem exists_law_of_mem_realizationBody {X ι : Type*} [Fintype ι] (φ : X → ι → ℝ)
    (v : ι → ℝ) (hv : v ∈ realizationBody φ) :
    ∃ p : Fin (Fintype.card ι + 1) → ℝ, ∃ point : Fin (Fintype.card ι + 1) → X,
      (∀ k, 0 ≤ p k) ∧ ∑ k, p k = 1 ∧ featureVector p point φ = v := by
  classical
  obtain ⟨J, hJ, z, weight, hzrange, haff, hpos, hwsum, hcomb⟩ :=
    eq_pos_convex_span_of_mem_convexHull hv
  have hcard : Fintype.card J ≤ Fintype.card ι + 1 := by
    refine haff.card_le_finrank_succ.trans (Nat.add_le_add_right ?_ 1)
    have hle : Module.finrank ℝ (vectorSpan ℝ (Set.range z))
        ≤ Module.finrank ℝ (ι → ℝ) := Submodule.finrank_le _
    simpa [Module.finrank_pi] using hle
  have hJne : Nonempty J := by
    by_contra hempty
    rw [not_nonempty_iff] at hempty
    simp at hwsum
  choose point₀ hpoint₀ using fun j : J ↦ hzrange (Set.mem_range_self j)
  obtain ⟨j₀⟩ := hJne
  have hcastinj : Function.Injective (Fin.castLE hcard) :=
    fun a b hab ↦ Fin.val_injective (congrArg Fin.val hab)
  have hinj : Function.Injective fun j : J ↦ Fin.castLE hcard (Fintype.equivFin J j) :=
    hcastinj.comp (Fintype.equivFin J).injective
  refine ⟨Function.extend (fun j : J ↦ Fin.castLE hcard (Fintype.equivFin J j)) weight 0,
    Function.extend (fun j : J ↦ Fin.castLE hcard (Fintype.equivFin J j)) point₀
      (fun _ ↦ point₀ j₀), ?_, ?_, ?_⟩
  · intro k
    by_cases hk : ∃ j, (fun j : J ↦ Fin.castLE hcard (Fintype.equivFin J j)) j = k
    · obtain ⟨j, rfl⟩ := hk
      rw [hinj.extend_apply]
      exact (hpos j).le
    · rw [Function.extend_apply' _ _ _ hk]
      exact le_rfl
  · have hvanish : ∀ k ∈ Finset.univ,
        k ∉ Finset.univ.map ⟨_, hinj⟩ →
        Function.extend (fun j : J ↦ Fin.castLE hcard (Fintype.equivFin J j)) weight 0 k
          = 0 := by
      intro k _ hk
      refine Function.extend_apply' _ _ _ ?_
      rintro ⟨j, rfl⟩
      exact hk (Finset.mem_map_of_mem _ (Finset.mem_univ j))
    rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.map ⟨_, hinj⟩)) hvanish,
      Finset.sum_map]
    rw [← hwsum]
    exact Finset.sum_congr rfl fun j _ ↦ hinj.extend_apply weight 0 j
  · have hvanish : ∀ k ∈ Finset.univ,
        k ∉ Finset.univ.map ⟨_, hinj⟩ →
        Function.extend (fun j : J ↦ Fin.castLE hcard (Fintype.equivFin J j)) weight 0 k •
            φ (Function.extend (fun j : J ↦ Fin.castLE hcard (Fintype.equivFin J j)) point₀
              (fun _ ↦ point₀ j₀) k) = 0 := by
      intro k _ hk
      have hzero : Function.extend
          (fun j : J ↦ Fin.castLE hcard (Fintype.equivFin J j)) weight 0 k = 0 := by
        refine Function.extend_apply' _ _ _ ?_
        rintro ⟨j, rfl⟩
        exact hk (Finset.mem_map_of_mem _ (Finset.mem_univ j))
      rw [hzero, zero_smul]
    rw [featureVector,
      ← Finset.sum_subset (Finset.subset_univ (Finset.univ.map ⟨_, hinj⟩)) hvanish,
      Finset.sum_map, ← hcomb]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [Function.Embedding.coeFn_mk, hinj.extend_apply, hinj.extend_apply, hpoint₀]

/-- **NOTE1 §2.1, compactness of the realization body.** For a compact space `X` and a
continuous feature map, the body is compact: it is the image of the compact set
`stdSimplex ℝ (Fin (card ι + 1)) ×ˢ univ` under the continuous map sending a law to its
feature vector, by Carathéodory. Compactness gives closedness, which is the hypothesis the
invariance theorem needs. -/
theorem isCompact_realizationBody {X ι : Type*} [Fintype ι] [TopologicalSpace X]
    [CompactSpace X] (φ : X → ι → ℝ) (hφ : Continuous φ) :
    IsCompact (realizationBody φ) := by
  have himage : realizationBody φ
      = (fun q : (Fin (Fintype.card ι + 1) → ℝ) × (Fin (Fintype.card ι + 1) → X) ↦
          featureVector q.1 q.2 φ) ''
        (stdSimplex ℝ (Fin (Fintype.card ι + 1)) ×ˢ (Set.univ : Set (Fin _ → X))) := by
    apply Set.Subset.antisymm
    · intro v hv
      obtain ⟨p, point, hp, hsum, hfeat⟩ := exists_law_of_mem_realizationBody φ v hv
      exact ⟨(p, point), ⟨⟨hp, hsum⟩, Set.mem_univ _⟩, hfeat⟩
    · rintro _ ⟨⟨p, point⟩, ⟨hp, -⟩, rfl⟩
      exact featureVector_mem_convexHull p hp.1 hp.2 point φ
  have hcont : Continuous
      fun q : (Fin (Fintype.card ι + 1) → ℝ) × (Fin (Fintype.card ι + 1) → X) ↦
        featureVector q.1 q.2 φ := by
    simp only [featureVector]
    exact continuous_finset_sum Finset.univ fun k _ ↦
      ((continuous_apply k).comp continuous_fst).smul
        (hφ.comp ((continuous_apply k).comp continuous_snd))
  rw [himage]
  exact (isCompact_stdSimplex _ |>.prod isCompact_univ).image hcont

/-- The realization body of a continuous feature map on a compact space is closed, which is
what the invariance theorem of NOTE1 Theorem 1 requires of it. -/
theorem isClosed_realizationBody {X ι : Type*} [Fintype ι] [TopologicalSpace X]
    [CompactSpace X] (φ : X → ι → ℝ) (hφ : Continuous φ) :
    IsClosed (realizationBody φ) :=
  (isCompact_realizationBody φ hφ).isClosed

end

end Descent.Portability.RealizationBody
