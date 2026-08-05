/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Blindness.TrafficInvariantSeparation.SpectralSDPSeparation

namespace Descent.Blindness
namespace TrafficInvariantSeparation

open scoped Matrix Topology

/-!
# `TrafficInvariantSeparation.PolynomialTraffic`

Part of the split of `Descent/Blindness/TrafficInvariantSeparation.lean`, which was 6,618 lines.

The parts are a CHAIN: each imports the one before, in the order the original was written.
That is the conservative choice, deliberately. A monolith's declarations depend on each
other in whatever order they happen to appear, and cutting it into modules that import only
what they use means discovering that order first -- worth doing, and not what this does.
The chain preserves every resolution the single file had, so the split cannot change what
any proof sees.

Where a cut falls inside a section, the section is reopened and reclosed by name. A section
scopes `variable`s and this file declares none at that level, so the reopening is exact.
-/


section PolynomialTraffic

/-- Two endpoint-label assignments have the same equality pattern exactly when
they induce the same partition of the endpoint slots.  This relation is the
precise combinatorial content of having the same directed multigraph shape. -/
def SameEqualityPattern {Slot Label : Type*}
    (left right : Slot → Label) : Prop :=
  ∀ first second, left first = left second ↔ right first = right second

/-- Every endpoint-label assignment establishes its own equality pattern. -/
theorem sameEqualityPattern_refl
    {Slot Label : Type*} (assignment : Slot → Label) :
    SameEqualityPattern assignment assignment := by
  intro first second
  rfl

/-- Equality-pattern equivalence is symmetric. -/
theorem sameEqualityPattern_symm
    {Slot Label : Type*} {left right : Slot → Label}
    (hpattern : SameEqualityPattern left right) :
    SameEqualityPattern right left := by
  intro first second
  exact (hpattern first second).symm

/-- Equality-pattern equivalence is transitive. -/
theorem sameEqualityPattern_trans
    {Slot Label : Type*} {left middle right : Slot → Label}
    (hleft : SameEqualityPattern left middle)
    (hright : SameEqualityPattern middle right) :
    SameEqualityPattern left right := by
  intro first second
  exact (hleft first second).trans (hright first second)

/-- The canonical orbit relation on endpoint-label assignments. -/
def sameEqualityPatternSetoid (Slot Label : Type*) : Setoid (Slot → Label) where
  r := SameEqualityPattern
  iseqv := ⟨sameEqualityPattern_refl, @sameEqualityPattern_symm Slot Label,
    @sameEqualityPattern_trans Slot Label⟩

/-- The canonical finite traffic-graph shape is the quotient of endpoint
assignments by equality pattern.  It records precisely a directed multigraph
with its ordered endpoint slots, and nothing about the particular labels. -/
def EqualityPattern (Slot Label : Type*) :=
  Quotient (sameEqualityPatternSetoid Slot Label)

noncomputable instance equalityPatternFintype
    (Slot Label : Type*) [Fintype Slot] [Fintype Label] :
    Fintype (EqualityPattern Slot Label) := by
  letI : DecidableEq (EqualityPattern Slot Label) := Classical.decEq _
  letI : DecidableEq Slot := Classical.decEq _
  exact Fintype.ofSurjective (Quotient.mk (sameEqualityPatternSetoid Slot Label))
    Quotient.mk_surjective

noncomputable instance equalityPatternDecidableEq
    (Slot Label : Type*) : DecidableEq (EqualityPattern Slot Label) :=
  Classical.decEq _

/-- Send an assignment to its canonical equality-pattern traffic shape. -/
def equalityPatternShape {Slot Label : Type*}
    (assignment : Slot → Label) : EqualityPattern Slot Label :=
  Quotient.mk (sameEqualityPatternSetoid Slot Label) assignment

/-- Equality of canonical traffic shapes is exactly equality of endpoint
partitions. -/
theorem equalityPatternShape_eq_iff
    {Slot Label : Type*} (left right : Slot → Label) :
    equalityPatternShape left = equalityPatternShape right ↔
      SameEqualityPattern left right := by
  exact Quotient.eq

/-- The occupied labels of two assignments with the same equality pattern are
equivalent: send the label at a slot on the left to the label at
the same slot on the right.  Choice only selects a representative slot; the
equality-pattern hypothesis proves the result independent of that choice. -/
noncomputable def equalityPatternRangeEquiv
    {Slot Label : Type*} (left right : Slot → Label)
    (hpattern : SameEqualityPattern left right) :
    Set.range left ≃ Set.range right where
  toFun value :=
    ⟨right (Classical.choose value.property),
      ⟨Classical.choose value.property, rfl⟩⟩
  invFun value :=
    ⟨left (Classical.choose value.property),
      ⟨Classical.choose value.property, rfl⟩⟩
  left_inv value := by
    apply Subtype.ext
    have hleft := Classical.choose_spec value.property
    have hright := Classical.choose_spec
      ((⟨right (Classical.choose value.property),
        ⟨Classical.choose value.property, rfl⟩⟩ : Set.range right).property)
    exact (hpattern _ _).mpr (hright.trans rfl) |>.trans hleft
  right_inv value := by
    apply Subtype.ext
    have hright := Classical.choose_spec value.property
    have hleft := Classical.choose_spec
      ((⟨left (Classical.choose value.property),
        ⟨Classical.choose value.property, rfl⟩⟩ : Set.range left).property)
    exact (hpattern _ _).mp (hleft.trans rfl) |>.trans hright

/-- On a finite label set, the equivalence between occupied labels extends to
a permutation of the entire label set.

Empirical status: NOT AN EMPIRICAL CLAIM. -/
noncomputable def equalityPatternPermutation
    {Slot Label : Type*} [Finite Label] (left right : Slot → Label)
    (hpattern : SameEqualityPattern left right) : Equiv.Perm Label := by
  classical
  exact Equiv.extendSubtype (equalityPatternRangeEquiv left right hpattern)

/-- The extended permutation sends every label used by the first monomial to
the corresponding label used by the second monomial. -/
theorem equalityPatternPermutation_apply
    {Slot Label : Type*} [Finite Label] (left right : Slot → Label)
    (hpattern : SameEqualityPattern left right) (slot : Slot) :
    equalityPatternPermutation left right hpattern (left slot) = right slot := by
  classical
  change Equiv.extendSubtype (equalityPatternRangeEquiv left right hpattern) (left slot) =
    right slot
  rw [Equiv.extendSubtype_apply_of_mem _ _ (Set.mem_range_self slot)]
  change right (Classical.choose (Set.mem_range_self slot)) = right slot
  apply (hpattern _ _).mp
  exact Classical.choose_spec (Set.mem_range_self slot)

/-- Permutation invariance forces coefficients to be constant on equality
patterns.  This discharges the representation-theoretic step that the raw
orbit-sum identity alone cannot prove. -/
theorem coefficient_eq_of_sameEqualityPattern
    {Slot Label : Type*} [Finite Label]
    (coefficient : (Slot → Label) → ℝ)
    (hinvariant : ∀ (permutation : Equiv.Perm Label) monomial,
      coefficient (permutation ∘ monomial) = coefficient monomial)
    (left right : Slot → Label) (hpattern : SameEqualityPattern left right) :
    coefficient left = coefficient right := by
  let permutation := equalityPatternPermutation left right hpattern
  have hmap : permutation ∘ left = right := by
    funext slot
    exact equalityPatternPermutation_apply left right hpattern slot
  rw [← hmap, hinvariant]

/-- **Orbit sums are graph polynomials.**  `shape` records the equality pattern of the endpoint
indices of a monomial—equivalently its directed multigraph.  Once permutation invariance makes
the coefficient depend only on this shape, regrouping monomials gives an exact finite graph-sum
factorization.  The same statement covers rooted shapes by including the output slot in `Graph`. -/
theorem polynomial_orbitSum_factorization
    {Monomial Graph : Type*} [Fintype Monomial] [Fintype Graph] [DecidableEq Graph]
    (shape : Monomial → Graph) (coefficient : Graph → ℝ) (value : Monomial → ℝ) :
    (∑ monomial, coefficient (shape monomial) * value monomial) =
      ∑ graph, coefficient graph *
        ∑ monomial, if shape monomial = graph then value monomial else 0 := by
  classical
  simp_rw [Finset.mul_sum, mul_ite, mul_zero]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro monomial _
  simp

/-- Coefficient assigned to an equality-pattern graph by choosing any monomial of that shape. -/
noncomputable def graphShapeCoefficient
    {Monomial Graph : Type*} (shape : Monomial → Graph) (coefficient : Monomial → ℝ)
    (graph : Graph) : ℝ := by
  classical
  exact if h : ∃ monomial, shape monomial = graph then
    coefficient (Classical.choose h) else 0

/-- Shape-invariant monomial coefficients factor through the graph shape. -/
theorem graphShapeCoefficient_comp_of_shapeInvariant
    {Monomial Graph : Type*} (shape : Monomial → Graph) (coefficient : Monomial → ℝ)
    (hinvariant : ∀ left right, shape left = shape right →
      coefficient left = coefficient right) (monomial : Monomial) :
    graphShapeCoefficient shape coefficient (shape monomial) = coefficient monomial := by
  let h : ∃ candidate, shape candidate = shape monomial := ⟨monomial, rfl⟩
  rw [graphShapeCoefficient, dif_pos h]
  exact hinvariant _ _ (Classical.choose_spec h)

/-- **Permutation-invariant polynomial factorization, after equality patterns are identified with
graphs.**  Invariance makes each monomial coefficient constant on its shape class; the resulting
polynomial is exactly a linear combination of the corresponding graph sums.  Taking `Graph` to
be rooted equality patterns gives the equivariant vector version without changing the proof. -/
theorem invariantPolynomial_graphSum_factorization_of_shapeInvariant
    {Monomial Graph : Type*} [Fintype Monomial] [Fintype Graph] [DecidableEq Graph]
    (shape : Monomial → Graph) (coefficient value : Monomial → ℝ)
    (hinvariant : ∀ left right, shape left = shape right →
      coefficient left = coefficient right) :
    (∑ monomial, coefficient monomial * value monomial) =
      ∑ graph, graphShapeCoefficient shape coefficient graph *
        ∑ monomial, if shape monomial = graph then value monomial else 0 := by
  calc
    (∑ monomial, coefficient monomial * value monomial) =
        ∑ monomial, graphShapeCoefficient shape coefficient (shape monomial) * value monomial := by
      apply Finset.sum_congr rfl
      intro monomial _
      rw [graphShapeCoefficient_comp_of_shapeInvariant shape coefficient hinvariant]
    _ = _ := polynomial_orbitSum_factorization shape
      (graphShapeCoefficient shape coefficient) value

/-- **Exact finite permutation-invariant polynomial/traffic factorization.**
Monomials are endpoint-label assignments.  If `shape` completely records their
equality pattern, permutation invariance of the polynomial coefficients implies
shape invariance, and the polynomial factors through the corresponding graph
sums.  Rooted equivariant polynomials use the same theorem after including the
distinguished output slot in `Slot`. -/
theorem invariantPolynomial_graphSum_factorization
    {Slot Label Graph : Type*} [Fintype Slot] [DecidableEq Slot] [Fintype Label]
    [Fintype Graph] [DecidableEq Graph]
    (shape : (Slot → Label) → Graph)
    (coefficient value : (Slot → Label) → ℝ)
    (hshape : ∀ left right, shape left = shape right →
      SameEqualityPattern left right)
    (hinvariant : ∀ (permutation : Equiv.Perm Label) monomial,
      coefficient (permutation ∘ monomial) = coefficient monomial) :
    (∑ monomial, coefficient monomial * value monomial) =
      ∑ graph, graphShapeCoefficient shape coefficient graph *
        ∑ monomial, if shape monomial = graph then value monomial else 0 := by
  apply invariantPolynomial_graphSum_factorization_of_shapeInvariant
  intro left right hsame
  exact coefficient_eq_of_sameEqualityPattern coefficient hinvariant left right
    (hshape left right hsame)

/-- The equality asserted by canonical finite traffic factorization. -/
noncomputable def CanonicalTrafficFactorizationStatement
    {Slot Label : Type*} [Fintype Slot] [DecidableEq Slot] [Fintype Label]
    (coefficient value : (Slot → Label) → ℝ) : Prop :=
  (∑ monomial, coefficient monomial * value monomial) =
    ∑ graph : EqualityPattern Slot Label,
      graphShapeCoefficient equalityPatternShape coefficient graph *
        ∑ monomial,
          if equalityPatternShape monomial = graph then value monomial else 0

/-- The equality asserted by the rooted canonical finite traffic factorization. -/
noncomputable def RootedCanonicalTrafficFactorizationStatement
    {Slot Label : Type*} [Fintype Slot] [DecidableEq Slot] [Fintype Label]
    (coefficient value : (Option Slot → Label) → ℝ) : Prop :=
  (∑ monomial, coefficient monomial * value monomial) =
    ∑ graph : EqualityPattern (Option Slot) Label,
      graphShapeCoefficient equalityPatternShape coefficient graph *
        ∑ monomial,
          if equalityPatternShape monomial = graph then value monomial else 0

/-- **Canonical invariant-polynomial/traffic factorization.**  The graph index
is now the actual quotient by endpoint equality pattern, so no external shape
map or shape-completeness hypothesis remains.  Permutation invariance of the
formal monomial coefficients alone yields exact finite factorization. -/
theorem invariantPolynomial_canonicalTraffic_factorization
    {Slot Label : Type*} [Fintype Slot] [DecidableEq Slot] [Fintype Label]
    (coefficient value : (Slot → Label) → ℝ)
    (hinvariant : ∀ (permutation : Equiv.Perm Label) monomial,
      coefficient (permutation ∘ monomial) = coefficient monomial) :
    CanonicalTrafficFactorizationStatement coefficient value := by
  apply invariantPolynomial_graphSum_factorization equalityPatternShape
    coefficient value
  · intro left right hshape
    exact (equalityPatternShape_eq_iff left right).mp hshape
  · exact hinvariant

/-- **Canonical rooted factorization.**  `none` is the distinguished output
slot and `some slot` are matrix-entry endpoint slots.  Hence this is the exact
finite rooted-traffic form used for permutation-equivariant vector outputs. -/
theorem rootedInvariantPolynomial_canonicalTraffic_factorization
    {Slot Label : Type*} [Fintype Slot] [DecidableEq Slot] [Fintype Label]
    (coefficient value : (Option Slot → Label) → ℝ)
    (hinvariant : ∀ (permutation : Equiv.Perm Label) monomial,
      coefficient (permutation ∘ monomial) = coefficient monomial) :
    RootedCanonicalTrafficFactorizationStatement coefficient value :=
  invariantPolynomial_canonicalTraffic_factorization coefficient value hinvariant

/-- The exact scalar degree-bounded traffic factorization statement.

Convention: `D` is polynomial edge degree, not linkage-disequilibrium `D`. -/
noncomputable def DegreeAtMostTrafficFactorizationStatement
    {D : ℕ} {Label : Type*} [Fintype Label]
    (coefficient value : (degree : Fin (D + 1)) →
      ((Fin (degree : ℕ) × Bool → Label) → ℝ)) : Prop :=
  (∑ degree : Fin (D + 1),
    ∑ monomial, coefficient degree monomial * value degree monomial) =
    ∑ degree : Fin (D + 1),
      ∑ graph : EqualityPattern (Fin (degree : ℕ) × Bool) Label,
        graphShapeCoefficient equalityPatternShape (coefficient degree) graph *
          ∑ monomial,
            if equalityPatternShape monomial = graph then value degree monomial else 0

/-- The exact rooted degree-bounded traffic factorization statement.

Convention: `D` is polynomial edge degree, not linkage-disequilibrium `D`. -/
noncomputable def DegreeAtMostRootedTrafficFactorizationStatement
    {D : ℕ} {Label : Type*} [Fintype Label]
    (coefficient value : (degree : Fin (D + 1)) →
      ((Option (Fin (degree : ℕ) × Bool) → Label) → ℝ)) : Prop :=
  (∑ degree : Fin (D + 1),
    ∑ monomial, coefficient degree monomial * value degree monomial) =
    ∑ degree : Fin (D + 1),
      ∑ graph : EqualityPattern (Option (Fin (degree : ℕ) × Bool)) Label,
        graphShapeCoefficient equalityPatternShape (coefficient degree) graph *
          ∑ monomial,
            if equalityPatternShape monomial = graph then value degree monomial else 0

/-- **Exact degree-at-most-`D` traffic factorization.**  The homogeneous
degree `d` component uses endpoint slots `Fin d × Bool`, namely the ordered
tail and head of each of its `d` matrix-entry factors.  Summing over
`d : Fin (D + 1)` therefore proves factorization through canonical traffic
graphs with at most `D` edges, rather than leaving the edge bound implicit. -/
theorem degreeAtMostInvariantPolynomial_canonicalTraffic_factorization
    {D : ℕ} {Label : Type*} [Fintype Label]
    (coefficient value : (degree : Fin (D + 1)) →
      ((Fin (degree : ℕ) × Bool → Label) → ℝ))
    (hinvariant : ∀ degree (permutation : Equiv.Perm Label) monomial,
      coefficient degree (permutation ∘ monomial) = coefficient degree monomial) :
    DegreeAtMostTrafficFactorizationStatement coefficient value := by
  apply Finset.sum_congr rfl
  intro degree _hdegree
  exact invariantPolynomial_canonicalTraffic_factorization
    (coefficient degree) (value degree) (hinvariant degree)

/-- **Rooted degree-at-most-`D` factorization.**  Adding one `Option` slot to
each degree-`d` endpoint family marks the output coordinate, so the same exact
edge bound holds for permutation-equivariant vector-polynomial coordinates. -/
theorem degreeAtMostRootedInvariantPolynomial_canonicalTraffic_factorization
    {D : ℕ} {Label : Type*} [Fintype Label]
    (coefficient value : (degree : Fin (D + 1)) →
      ((Option (Fin (degree : ℕ) × Bool) → Label) → ℝ))
    (hinvariant : ∀ degree (permutation : Equiv.Perm Label) monomial,
      coefficient degree (permutation ∘ monomial) = coefficient degree monomial) :
    DegreeAtMostRootedTrafficFactorizationStatement coefficient value := by
  apply Finset.sum_congr rfl
  intro degree _hdegree
  exact rootedInvariantPolynomial_canonicalTraffic_factorization
    (coefficient degree) (value degree) (hinvariant degree)

/-- The complete canonical traffic profile seen by scalar polynomials of total
degree at most `D`.  At homogeneous degree `d`, it stores every graph sum on
the equality-pattern quotient of the `2d` ordered matrix endpoints.

Convention: `D` is polynomial edge degree, not linkage-disequilibrium `D`. -/
def DegreeAtMostCanonicalTrafficProfile (D : ℕ) (Label : Type*) :=
  (degree : Fin (D + 1)) →
    EqualityPattern (Fin (degree : ℕ) × Bool) Label → ℝ

/-- The equality-pattern sum common to scalar and rooted traffic profiles. -/
noncomputable def equalityPatternProfile
    {Slot Label : Type*} [Fintype Slot] [DecidableEq Slot] [Fintype Label]
    (value : (Slot → Label) → ℝ) (graph : EqualityPattern Slot Label) : ℝ :=
  ∑ monomial,
    if equalityPatternShape monomial = graph then value monomial else 0

/-- Evaluate the canonical degree-limited traffic profile of a family of
monomial values.

Convention: `D` is polynomial edge degree, not linkage-disequilibrium `D`. -/
noncomputable def degreeAtMostCanonicalTrafficProfile
    {D : ℕ} {Label : Type*} [Fintype Label]
    (value : (degree : Fin (D + 1)) →
      ((Fin (degree : ℕ) × Bool → Label) → ℝ)) :
    DegreeAtMostCanonicalTrafficProfile D Label :=
  fun degree graph ↦ equalityPatternProfile (value degree) graph

/-- The rooted profile seen by degree-limited equivariant vector-polynomial
coordinates.  The additional `Option` slot marks the output label.

Convention: `D` is polynomial edge degree, not linkage-disequilibrium `D`. -/
def DegreeAtMostRootedCanonicalTrafficProfile (D : ℕ) (Label : Type*) :=
  (degree : Fin (D + 1)) →
    EqualityPattern (Option (Fin (degree : ℕ) × Bool)) Label → ℝ

/-- Evaluate the rooted canonical traffic profile of a family of rooted
monomial values.

Convention: `D` is polynomial edge degree, not linkage-disequilibrium `D`. -/
noncomputable def degreeAtMostRootedCanonicalTrafficProfile
    {D : ℕ} {Label : Type*} [Fintype Label]
    (value : (degree : Fin (D + 1)) →
      ((Option (Fin (degree : ℕ) × Bool) → Label) → ℝ)) :
    DegreeAtMostRootedCanonicalTrafficProfile D Label :=
  fun degree graph ↦ equalityPatternProfile (value degree) graph

/-- Scalar and rooted degree-limited profiles are the two endpoint-slot
specializations of the same equality-pattern sum. -/
theorem degreeAtMostTrafficProfiles_are_equalityPatternProfiles
    {D : ℕ} {Label : Type*} [Fintype Label]
    (value : (degree : Fin (D + 1)) →
      ((Fin (degree : ℕ) × Bool → Label) → ℝ))
    (rootedValue : (degree : Fin (D + 1)) →
      ((Option (Fin (degree : ℕ) × Bool) → Label) → ℝ)) :
    (∀ degree graph,
      degreeAtMostCanonicalTrafficProfile value degree graph =
        equalityPatternProfile (value degree) graph) ∧
    (∀ degree graph,
      degreeAtMostRootedCanonicalTrafficProfile rootedValue degree graph =
        equalityPatternProfile (rootedValue degree) graph) := by
  exact ⟨fun _degree _graph ↦ rfl, fun _degree _graph ↦ rfl⟩

/-- The scalar factorization theorem expressed as literal factorization
through the canonical profile map. -/
theorem degreeAtMostInvariantPolynomial_factorsThroughCanonicalTrafficProfile
    {D : ℕ} {Label : Type*} [Fintype Label]
    (coefficient value : (degree : Fin (D + 1)) →
      ((Fin (degree : ℕ) × Bool → Label) → ℝ))
    (hinvariant : ∀ degree (permutation : Equiv.Perm Label) monomial,
      coefficient degree (permutation ∘ monomial) = coefficient degree monomial) :
    (∑ degree : Fin (D + 1),
      ∑ monomial, coefficient degree monomial * value degree monomial) =
      ∑ degree : Fin (D + 1),
        ∑ graph : EqualityPattern (Fin (degree : ℕ) × Bool) Label,
          graphShapeCoefficient equalityPatternShape (coefficient degree) graph *
            degreeAtMostCanonicalTrafficProfile value degree graph := by
  simpa only [degreeAtMostCanonicalTrafficProfile, equalityPatternProfile] using
    degreeAtMostInvariantPolynomial_canonicalTraffic_factorization
      coefficient value hinvariant

/-- Equal canonical traffic profiles make every invariant scalar polynomial
of degree at most `D` exactly equal.  This is the finite algorithmic
indistinguishability statement, not only an expansion formula. -/
theorem degreeAtMostInvariantPolynomial_eq_of_canonicalTrafficProfile_eq
    {D : ℕ} {Label : Type*} [Fintype Label]
    (coefficient leftValue rightValue : (degree : Fin (D + 1)) →
      ((Fin (degree : ℕ) × Bool → Label) → ℝ))
    (hinvariant : ∀ degree (permutation : Equiv.Perm Label) monomial,
      coefficient degree (permutation ∘ monomial) = coefficient degree monomial)
    (htraffic : degreeAtMostCanonicalTrafficProfile leftValue =
      degreeAtMostCanonicalTrafficProfile rightValue) :
    (∑ degree : Fin (D + 1),
      ∑ monomial, coefficient degree monomial * leftValue degree monomial) =
      ∑ degree : Fin (D + 1),
        ∑ monomial, coefficient degree monomial * rightValue degree monomial := by
  rw [degreeAtMostInvariantPolynomial_factorsThroughCanonicalTrafficProfile
      coefficient leftValue hinvariant,
    degreeAtMostInvariantPolynomial_factorsThroughCanonicalTrafficProfile
      coefficient rightValue hinvariant,
    htraffic]

/-- Equal rooted profiles likewise make every rooted equivariant-polynomial
coordinate of degree at most `D` exactly equal. -/
theorem degreeAtMostRootedInvariantPolynomial_eq_of_canonicalTrafficProfile_eq
    {D : ℕ} {Label : Type*} [Fintype Label]
    (coefficient leftValue rightValue : (degree : Fin (D + 1)) →
      ((Option (Fin (degree : ℕ) × Bool) → Label) → ℝ))
    (hinvariant : ∀ degree (permutation : Equiv.Perm Label) monomial,
      coefficient degree (permutation ∘ monomial) = coefficient degree monomial)
    (htraffic : degreeAtMostRootedCanonicalTrafficProfile leftValue =
      degreeAtMostRootedCanonicalTrafficProfile rightValue) :
    (∑ degree : Fin (D + 1),
      ∑ monomial, coefficient degree monomial * leftValue degree monomial) =
      ∑ degree : Fin (D + 1),
        ∑ monomial, coefficient degree monomial * rightValue degree monomial := by
  have hleft := degreeAtMostRootedInvariantPolynomial_canonicalTraffic_factorization
    coefficient leftValue hinvariant
  have hright := degreeAtMostRootedInvariantPolynomial_canonicalTraffic_factorization
    coefficient rightValue hinvariant
  rw [hleft, hright]
  apply Finset.sum_congr rfl
  intro degree _hdegree
  apply Finset.sum_congr rfl
  intro graph _hgraph
  have hcomponent := congrFun (congrFun htraffic degree) graph
  dsimp only [degreeAtMostRootedCanonicalTrafficProfile] at hcomponent
  simp only [equalityPatternProfile] at hcomponent
  rw [hcomponent]

/-- **Direct fixed-degree invariant-separation hardness theorem.**  A single
pair of equal canonical traffic profiles equalizes the risk of every uniform
permutation-invariant degree-`D` polynomial procedure.  If the right Bayes risk
is optimal there, the entire Bayes gap lower-bounds every procedure's excess
risk on the left, with no factor loss and no prepackaged risk-factorization
assumption. -/
theorem degreeAtMostInvariantPolynomial_hardness_of_canonicalTrafficProfile_eq
    {Algorithm : Type*} {D : ℕ} {Label : Type*} [Fintype Label]
    (coefficient : Algorithm → (degree : Fin (D + 1)) →
      ((Fin (degree : ℕ) × Bool → Label) → ℝ))
    (leftValue rightValue : (degree : Fin (D + 1)) →
      ((Fin (degree : ℕ) × Bool → Label) → ℝ))
    (hinvariant : ∀ algorithm degree (permutation : Equiv.Perm Label) monomial,
      coefficient algorithm degree (permutation ∘ monomial) =
        coefficient algorithm degree monomial)
    (htraffic : degreeAtMostCanonicalTrafficProfile leftValue =
      degreeAtMostCanonicalTrafficProfile rightValue)
    (bayesLeft bayesRight : ℝ)
    (hoptimalRight : ∀ algorithm,
      bayesRight ≤ ∑ degree : Fin (D + 1),
        ∑ monomial,
          coefficient algorithm degree monomial * rightValue degree monomial)
    (algorithm : Algorithm) :
    bayesRight - bayesLeft ≤
      (∑ degree : Fin (D + 1),
        ∑ monomial,
          coefficient algorithm degree monomial * leftValue degree monomial) -
        bayesLeft := by
  apply suboptimal_of_invariant_separation
    (fun candidate ↦ ∑ degree : Fin (D + 1),
      ∑ monomial,
        coefficient candidate degree monomial * leftValue degree monomial)
    (fun candidate ↦ ∑ degree : Fin (D + 1),
      ∑ monomial,
        coefficient candidate degree monomial * rightValue degree monomial)
    bayesLeft bayesRight
  · intro candidate
    exact degreeAtMostInvariantPolynomial_eq_of_canonicalTrafficProfile_eq
      (coefficient candidate) leftValue rightValue (hinvariant candidate) htraffic
  · exact hoptimalRight

/-- A scalar risk that has access only to traffic coordinates with at most `D` edges. -/
structure TruncatedTrafficRisk (D : ℕ) where
  coefficient : Fin (D + 1) → ℝ

/-- Evaluation of a truncated-traffic risk functional.

Convention: `D` is polynomial/edge degree, not the population-genetic
linkage-disequilibrium coefficient traditionally also denoted `D`. -/
noncomputable def TruncatedTrafficRisk.evaluate
    {D : ℕ} (risk : TruncatedTrafficRisk D) (traffic : Fin (D + 1) → ℝ) : ℝ :=
  ∑ graph, risk.coefficient graph * traffic graph

/-- **The total-traffic functional**: unit weight on every retained graph
coordinate.

`TruncatedTrafficRisk` had no exhibited inhabitant, so the stability bound below
was stated over an empty-for-all-we-knew class. This member also fixes the
orientation of the bound: its coefficient `ℓ¹` mass is the number of retained
coordinates, so the bound reads "degree controls the number of coordinates, and
therefore the amplification" on a functional where that is visible.

Convention: `D` is polynomial/edge degree, not the population-genetic
linkage-disequilibrium coefficient traditionally also denoted `D`. The two differ
by ploidy and nothing here is about haplotype frequencies; the same note is
carried by `TruncatedTrafficRisk.evaluate` above, and it is repeated rather than
cross-referenced because this definition takes the argument on its own. -/
def TruncatedTrafficRisk.totalTraffic (D : ℕ) : TruncatedTrafficRisk D where
  coefficient := fun _graph ↦ 1

instance TruncatedTrafficRisk.instNonempty (D : ℕ) :
    Nonempty (TruncatedTrafficRisk D) :=
  ⟨TruncatedTrafficRisk.totalTraffic D⟩

/-- The total-traffic functional evaluates to the traffic sum, which is what
makes it the one whose amplification is exactly the coordinate count. -/
theorem TruncatedTrafficRisk.evaluate_totalTraffic {D : ℕ}
    (traffic : Fin (D + 1) → ℝ) :
    (TruncatedTrafficRisk.totalTraffic D).evaluate traffic = ∑ graph, traffic graph := by
  unfold TruncatedTrafficRisk.evaluate TruncatedTrafficRisk.totalTraffic
  simp

/-- **Quantitative finite-traffic stability.**  If every retained graph
coordinate changes by at most `epsilon`, the value of a graph polynomial
changes by at most `epsilon` times the coefficient `ℓ¹` mass.  This is the
missing hypothesis when exact finite factorization is passed to a limiting
traffic statement: fixed degree controls the number of coordinates, but not
the size-dependent coefficients multiplying them. -/
theorem truncatedTrafficRisk_abs_sub_le_coefficientMass_mul
    {D : ℕ} (risk : TruncatedTrafficRisk D)
    (left right : Fin (D + 1) → ℝ) (epsilon : ℝ)
    (hcoordinate : ∀ graph, |left graph - right graph| ≤ epsilon) :
    |risk.evaluate left - risk.evaluate right| ≤
      (∑ graph, |risk.coefficient graph|) * epsilon := by
  rw [TruncatedTrafficRisk.evaluate, TruncatedTrafficRisk.evaluate,
    ← Finset.sum_sub_distrib]
  calc
    |∑ graph, (risk.coefficient graph * left graph -
        risk.coefficient graph * right graph)| =
        |∑ graph, risk.coefficient graph * (left graph - right graph)| := by
          congr 1
          apply Finset.sum_congr rfl
          intro graph _hgraph
          ring
    _ ≤ ∑ graph, |risk.coefficient graph * (left graph - right graph)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ graph, |risk.coefficient graph| * |left graph - right graph| := by
      apply Finset.sum_congr rfl
      intro graph _hgraph
      rw [abs_mul]
    _ ≤ ∑ graph, |risk.coefficient graph| * epsilon := by
      apply Finset.sum_le_sum
      intro graph _hgraph
      exact mul_le_mul_of_nonneg_left (hcoordinate graph) (abs_nonneg _)
    _ = (∑ graph, |risk.coefficient graph|) * epsilon := by
      rw [Finset.sum_mul]

/-- A uniform coefficient-mass bound converts quantitative convergence of a
fixed truncated traffic profile into convergence of every stable polynomial
evaluation. -/
theorem truncatedTrafficRisk_tendsto_zero_of_boundedCoefficientMass
    {D : ℕ} (risk : ℕ → TruncatedTrafficRisk D)
    (left right : ℕ → Fin (D + 1) → ℝ)
    (discrepancy coefficientBound : ℝ)
    (hdiscrepancy : ∀ index graph,
      |left index graph - right index graph| ≤
        discrepancy * (1 / 2 : ℝ) ^ index)
    (hcoefficient : ∀ index,
      (∑ graph, |(risk index).coefficient graph|) ≤ coefficientBound)
    (hdiscrepancyNonneg : 0 ≤ discrepancy) :
    Filter.Tendsto
      (fun index ↦ (risk index).evaluate (left index) -
        (risk index).evaluate (right index))
      Filter.atTop (nhds 0) := by
  apply (tendsto_zero_iff_abs_tendsto_zero _).mpr
  apply squeeze_zero (fun index ↦ abs_nonneg _)
  · intro index
    calc
      |(risk index).evaluate (left index) -
          (risk index).evaluate (right index)| ≤
          (∑ graph, |(risk index).coefficient graph|) *
            (discrepancy * (1 / 2 : ℝ) ^ index) :=
        truncatedTrafficRisk_abs_sub_le_coefficientMass_mul
          (risk index) (left index) (right index)
          (discrepancy * (1 / 2 : ℝ) ^ index) (hdiscrepancy index)
      _ ≤ coefficientBound * (discrepancy * (1 / 2 : ℝ) ^ index) := by
        exact mul_le_mul_of_nonneg_right (hcoefficient index)
          (mul_nonneg hdiscrepancyNonneg (by positivity))
  · have hpow : Filter.Tendsto (fun index : ℕ ↦ (1 / 2 : ℝ) ^ index)
        Filter.atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_abs_lt_one (by norm_num)
    simpa [mul_assoc] using
      hpow.const_mul (coefficientBound * discrepancy)

/-! ### Certified high-temperature passage from traffic to pressure -/

/-- **High-temperature traffic sufficiency from an absolutely convergent
truncation certificate.**  Suppose both limiting pressures are approximated
by the same depth-`D` traffic polynomial and both tails obey the uniform
polymer bound `C q^(D+1)/(1-q)` with `0 ≤ q < 1`.  Then the two limiting
pressures are equal.

This theorem formalizes the analytic passage after a cluster expansion has
supplied its certificate.  It deliberately does not assert that a biological
posterior satisfies a Dobrushin or polymer condition; that model-specific
step remains an explicit hypothesis rather than an imported axiom. -/
theorem highTemperatureTrafficLimit_eq_of_geometricTruncation
    (leftLimit rightLimit C q : ℝ) (commonTruncation : ℕ → ℝ)
    (hqNonneg : 0 ≤ q) (hq : q < 1)
    (hleft : ∀ depth,
      |leftLimit - commonTruncation depth| ≤
        C * q ^ (depth + 1) / (1 - q))
    (hright : ∀ depth,
      |rightLimit - commonTruncation depth| ≤
        C * q ^ (depth + 1) / (1 - q)) :
    leftLimit = rightLimit := by
  have hbound : ∀ depth,
      |leftLimit - rightLimit| ≤
        2 * (C * q ^ (depth + 1) / (1 - q)) := by
    intro depth
    have htriangle : |leftLimit - rightLimit| ≤
        |leftLimit - commonTruncation depth| +
          |rightLimit - commonTruncation depth| := by
      have h := abs_sub_le leftLimit (commonTruncation depth) rightLimit
      rwa [abs_sub_comm (commonTruncation depth) rightLimit] at h
    linarith [hleft depth, hright depth]
  have hqAbs : |q| < 1 := by
    rw [abs_of_nonneg hqNonneg]
    exact hq
  have hpow : Filter.Tendsto (fun depth : ℕ ↦ q ^ depth)
      Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_abs_lt_one hqAbs
  have htail : Filter.Tendsto
      (fun depth : ℕ ↦ 2 * (C * q ^ (depth + 1) / (1 - q)))
      Filter.atTop (nhds 0) := by
    convert hpow.const_mul (2 * C * q / (1 - q)) using 1
    · funext depth
      rw [pow_succ]
      ring
    · simp
  have hconstant : Filter.Tendsto (fun _depth : ℕ ↦ |leftLimit - rightLimit|)
      Filter.atTop (nhds 0) :=
    squeeze_zero (fun _depth ↦ abs_nonneg _) hbound htail
  have hzero : |leftLimit - rightLimit| = 0 :=
    tendsto_nhds_unique tendsto_const_nhds hconstant
  exact sub_eq_zero.mp (abs_eq_zero.mp hzero)

/-- Equal traffic through degree `D` makes every degree-`D` graph-polynomial risk identical. -/
theorem truncatedTrafficRisk_eq_of_profile_eq
    {D : ℕ} (risk : TruncatedTrafficRisk D) (left right : Fin (D + 1) → ℝ)
    (htraffic : left = right) :
    risk.evaluate left = risk.evaluate right := by
  rw [htraffic]

/-- The invariant-separation lower bound specialized to any class whose risks factor through one
truncated traffic profile. -/
theorem truncatedTraffic_hardness
    {Algorithm : Type*} {D : ℕ} (risk : Algorithm → TruncatedTrafficRisk D)
    (left right : Fin (D + 1) → ℝ) (htraffic : left = right)
    (bayesLeft bayesRight : ℝ)
    (hoptimalRight : ∀ algorithm, bayesRight ≤ (risk algorithm).evaluate right)
    (algorithm : Algorithm) :
    bayesRight - bayesLeft ≤ (risk algorithm).evaluate left - bayesLeft := by
  apply suboptimal_of_invariant_separation
    (fun candidate ↦ (risk candidate).evaluate left)
    (fun candidate ↦ (risk candidate).evaluate right)
    bayesLeft bayesRight
  · intro candidate
    exact truncatedTrafficRisk_eq_of_profile_eq (risk candidate) left right htraffic
  · exact hoptimalRight

/-! ### Strictness of every truncated moment/traffic level -/

/-- `D + 2` distinct positive nodes in `[1,2]`.  They support a signed
annihilator of moments through degree `D`.

Convention: `D` is moment degree, not linkage-disequilibrium `D`. -/
noncomputable def momentSeparationNode (D : ℕ) (index : Fin (D + 2)) : ℝ :=
  1 + (index : ℝ) / (D + 1 : ℝ)

/-- The node divisor is `D + 1` for `D : ℕ`, which is at least one, so this quotient has no
junk point.  Recorded here rather than left for the scanner to re-derive each run. -/
theorem momentSeparationNode_divisor_ne_zero (D : ℕ) : ((D : ℝ) + 1) ≠ 0 := by
  positivity


/-- Rectangular Vandermonde map taking weights on `D + 2` nodes to moments of
degrees `0,…,D`.

Convention: `D` is moment degree, not linkage-disequilibrium `D`. -/
noncomputable def truncatedMomentMap (D : ℕ) :
    (Fin (D + 2) → ℝ) →ₗ[ℝ] (Fin (D + 1) → ℝ) :=
  (Matrix.rectVandermonde (momentSeparationNode D) (fun _ ↦ 1) (D + 1)).vecMulLinear

/-- The moment-separation nodes are injectively indexed. -/
theorem momentSeparationNode_injective (D : ℕ) :
    Function.Injective (momentSeparationNode D) := by
  intro left right heq
  have hden : (D + 1 : ℝ) ≠ 0 := by positivity
  have hfrac : (left : ℝ) / (D + 1 : ℝ) =
      (right : ℝ) / (D + 1 : ℝ) := by
    unfold momentSeparationNode at heq
    linarith
  have hcast : (left : ℝ) = (right : ℝ) := (div_left_inj' hden).mp hfrac
  apply Fin.ext
  exact_mod_cast hcast

/-- Every node lies in the uniformly well-conditioned interval `[1,2]`. -/
theorem momentSeparationNode_mem_Icc (D : ℕ) (index : Fin (D + 2)) :
    momentSeparationNode D index ∈ Set.Icc (1 : ℝ) 2 := by
  have hden : (0 : ℝ) < D + 1 := by positivity
  have hindex0 : (0 : ℝ) ≤ index := by positivity
  have hindex1 : (index : ℝ) ≤ D + 1 := by
    exact_mod_cast Nat.le_of_lt_succ index.isLt
  constructor
  · unfold momentSeparationNode
    have hfrac0 : (0 : ℝ) ≤ (index : ℝ) / (D + 1 : ℝ) :=
      div_nonneg hindex0 hden.le
    linarith
  · unfold momentSeparationNode
    have := (div_le_one hden).2 hindex1
    linarith

/-- **Every truncated moment hierarchy has a nontrivial next-order
direction.**  For every `D` there is a nonzero signed weight vector whose
moments of degrees `0,…,D` vanish but whose degree-`D+1` moment is nonzero.

The existence is dimension-theoretic (`D+2` weights and `D+1` constraints).
The final nonvanishing is not assumed: if it also vanished, invertibility of
the square Vandermonde matrix on the distinct nodes would force the weight
vector to be zero. -/
theorem exists_truncatedMoment_annihilator (D : ℕ) :
    ∃ weight : Fin (D + 2) → ℝ,
      weight ≠ 0 ∧
        (∀ degree : Fin (D + 1),
          ∑ index : Fin (D + 2),
            weight index * momentSeparationNode D index ^ (degree : ℕ) = 0) ∧
        ∑ index : Fin (D + 2),
          weight index * momentSeparationNode D index ^ (D + 1) ≠ 0 := by
  have hdim :
      Module.finrank ℝ (Fin (D + 1) → ℝ) <
        Module.finrank ℝ (Fin (D + 2) → ℝ) := by
    simp
  have hker : LinearMap.ker (truncatedMomentMap D) ≠ ⊥ :=
    LinearMap.ker_ne_bot_of_finrank_lt hdim
  obtain ⟨weight, hweightKernel, hweightNe⟩ :=
    Submodule.exists_mem_ne_zero_of_ne_bot hker
  have hmapZero : truncatedMomentMap D weight = 0 :=
    LinearMap.mem_ker.mp hweightKernel
  have hlow : ∀ degree : Fin (D + 1),
      ∑ index : Fin (D + 2),
        weight index * momentSeparationNode D index ^ (degree : ℕ) = 0 := by
    intro degree
    have hcoordinate := congrFun hmapZero degree
    simpa [truncatedMomentMap, Matrix.vecMul, dotProduct,
      Matrix.rectVandermonde_apply] using hcoordinate
  refine ⟨weight, hweightNe, hlow, ?_⟩
  intro hhigh
  apply hweightNe
  apply Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero
    (momentSeparationNode_injective D)
  intro degree
  refine Fin.lastCases ?_ (fun lowDegree ↦ ?_) degree
  · simpa using hhigh
  · simpa using hlow lowDegree

/-- Uniform reference mass on the `D + 2` nodes.

Convention: `D` is moment degree, not linkage-disequilibrium `D`. -/
noncomputable def momentUniformWeight (D : ℕ) : ℝ :=
  1 / (D + 2 : ℝ)

/-- Reference evaluation; see `Descent.Core.Ratios` for what these pin and why. -/
theorem momentUniformWeight_at_reference_point :
    momentUniformWeight 1 = 1 / 3 := by
  norm_num [momentUniformWeight]



/-- A strictly positive scale small enough that perturbing the uniform law by
any signed weight vector preserves positivity coordinatewise.

Convention: `D` is moment degree, not linkage-disequilibrium `D`. -/
noncomputable def momentPerturbationScale
    (D : ℕ) (weight : Fin (D + 2) → ℝ) : ℝ :=
  1 / ((D + 2 : ℝ) * (1 + ∑ index, |weight index|))

/-- The perturbed member of the moment-matched pair.

Convention: `D` is moment degree, not linkage-disequilibrium `D`. -/
noncomputable def perturbedMomentWeight
    (D : ℕ) (weight : Fin (D + 2) → ℝ) (index : Fin (D + 2)) : ℝ :=
  momentUniformWeight D + momentPerturbationScale D weight * weight index

/-- The reference member of the moment-matched pair.

Convention: `D` is moment degree, not linkage-disequilibrium `D`. -/
noncomputable def referenceMomentWeight
    (D : ℕ) (_index : Fin (D + 2)) : ℝ :=
  momentUniformWeight D

theorem momentPerturbationScale_pos
    (D : ℕ) (weight : Fin (D + 2) → ℝ) :
    0 < momentPerturbationScale D weight := by
  unfold momentPerturbationScale
  positivity

/-- The perturbation at any coordinate is strictly smaller than the uniform
mass at that coordinate. -/
theorem momentPerturbation_abs_lt_uniform
    (D : ℕ) (weight : Fin (D + 2) → ℝ) (index : Fin (D + 2)) :
    momentPerturbationScale D weight * |weight index| < momentUniformWeight D := by
  have hcard : (0 : ℝ) < D + 2 := by positivity
  have hsum0 : (0 : ℝ) ≤ ∑ candidate, |weight candidate| := by positivity
  have hsumPos : (0 : ℝ) < 1 + ∑ candidate, |weight candidate| := by linarith
  have hsingle : |weight index| ≤ ∑ candidate, |weight candidate| := by
    exact Finset.single_le_sum (fun candidate _ ↦ abs_nonneg (weight candidate))
      (Finset.mem_univ index)
  have hstrict : |weight index| < 1 + ∑ candidate, |weight candidate| := by
    linarith
  unfold momentPerturbationScale momentUniformWeight
  calc
    1 / ((D + 2 : ℝ) * (1 + ∑ candidate, |weight candidate|)) * |weight index| =
        |weight index| / ((D + 2 : ℝ) *
          (1 + ∑ candidate, |weight candidate|)) := by ring
    _ < (1 + ∑ candidate, |weight candidate|) /
        ((D + 2 : ℝ) * (1 + ∑ candidate, |weight candidate|)) :=
      div_lt_div_of_pos_right hstrict (mul_pos hcard hsumPos)
    _ = 1 / (D + 2 : ℝ) := by field_simp

/-- The perturbed weights are strictly positive, hence nonnegative. -/
theorem perturbedMomentWeight_pos
    (D : ℕ) (weight : Fin (D + 2) → ℝ) (index : Fin (D + 2)) :
    0 < perturbedMomentWeight D weight index := by
  have hscale := momentPerturbationScale_pos D weight
  have hsmall := momentPerturbation_abs_lt_uniform D weight index
  have hlower : -|weight index| ≤ weight index := neg_abs_le (weight index)
  have hscaled :
      -(momentPerturbationScale D weight * |weight index|) ≤
        momentPerturbationScale D weight * weight index := by
    nlinarith
  unfold perturbedMomentWeight
  linarith

/-- The reference weights sum to one. -/
theorem referenceMomentWeight_sum_one (D : ℕ) :
    ∑ index : Fin (D + 2), referenceMomentWeight D index = 1 := by
  simp [referenceMomentWeight, momentUniformWeight]
  field_simp

/-- A zero-total-mass signed direction preserves normalization. -/
theorem perturbedMomentWeight_sum_one
    (D : ℕ) (weight : Fin (D + 2) → ℝ)
    (hzero : ∑ index, weight index = 0) :
    ∑ index, perturbedMomentWeight D weight index = 1 := by
  simp_rw [perturbedMomentWeight]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, hzero, mul_zero, add_zero]
  exact referenceMomentWeight_sum_one D

/-- Vanishing of a signed moment makes the two probability laws agree at that
degree. -/
theorem perturbedMoment_eq_referenceMoment
    (D degree : ℕ) (weight : Fin (D + 2) → ℝ)
    (hvanish : ∑ index,
      weight index * momentSeparationNode D index ^ degree = 0) :
    (∑ index, perturbedMomentWeight D weight index *
        momentSeparationNode D index ^ degree) =
      ∑ index, referenceMomentWeight D index *
        momentSeparationNode D index ^ degree := by
  simp_rw [perturbedMomentWeight, referenceMomentWeight, add_mul]
  rw [Finset.sum_add_distrib]
  have hscaled :
      (∑ index : Fin (D + 2),
        momentPerturbationScale D weight * weight index *
          momentSeparationNode D index ^ degree) = 0 := by
    simp_rw [mul_assoc]
    rw [← Finset.mul_sum]
    simpa [mul_assoc] using congrArg (momentPerturbationScale D weight * ·) hvanish
  rw [hscaled, add_zero]

/-- A nonzero signed moment remains different after the positive
normalization. -/
theorem perturbedMoment_ne_referenceMoment
    (D degree : ℕ) (weight : Fin (D + 2) → ℝ)
    (hnonzero : ∑ index,
      weight index * momentSeparationNode D index ^ degree ≠ 0) :
    (∑ index, perturbedMomentWeight D weight index *
        momentSeparationNode D index ^ degree) ≠
      ∑ index, referenceMomentWeight D index *
        momentSeparationNode D index ^ degree := by
  intro hequal
  have hscaleNe : momentPerturbationScale D weight ≠ 0 :=
    ne_of_gt (momentPerturbationScale_pos D weight)
  have hscaled : momentPerturbationScale D weight *
      (∑ index, weight index * momentSeparationNode D index ^ degree) = 0 := by
    have hdifference := sub_eq_zero.mpr hequal
    simpa [perturbedMomentWeight, referenceMomentWeight, add_mul,
      Finset.sum_add_distrib, ← Finset.mul_sum, mul_assoc] using hdifference
  exact hnonzero ((mul_eq_zero.mp hscaled).resolve_left hscaleNe)

/-- The diagonal traffic profile through `D` edges generated by a finite
spectral probability law.

Convention: `D` is graph edge depth, not linkage-disequilibrium `D`. -/
noncomputable def finiteDiagonalTrafficProfile
    (D : ℕ) (weight : Fin (D + 2) → ℝ) : Fin (D + 1) → ℝ :=
  fun degree ↦ ∑ index,
    weight index * momentSeparationNode D index ^ (degree : ℕ)

/-- Its first coordinate beyond the truncation.

Convention: `D` is graph edge depth, not linkage-disequilibrium `D`. -/
noncomputable def finiteDiagonalNextTrafficCoordinate
    (D : ℕ) (weight : Fin (D + 2) → ℝ) : ℝ :=
  ∑ index, weight index * momentSeparationNode D index ^ (D + 1)

/-- The complete finite probability-pair contract used by strictness of the
diagonal traffic hierarchy.

Convention: `D` is graph edge depth, not linkage-disequilibrium `D`. -/
def IsMomentMatchedProbabilityPair
    (D : ℕ) (left right : Fin (D + 2) → ℝ) : Prop :=
  (∀ index, momentSeparationNode D index ∈ Set.Icc (1 : ℝ) 2) ∧
    (∀ index, 0 ≤ left index) ∧
    (∀ index, 0 ≤ right index) ∧
    (∑ index, left index = 1) ∧
    (∑ index, right index = 1) ∧
    finiteDiagonalTrafficProfile D left = finiteDiagonalTrafficProfile D right

/-- The next diagonal coordinate distinguishes a moment-matched pair.

Convention: `D` is graph edge depth, not linkage-disequilibrium `D`. -/
def SeparatesAtNextDiagonalTraffic
    (D : ℕ) (left right : Fin (D + 2) → ℝ) : Prop :=
  finiteDiagonalNextTrafficCoordinate D left ≠
    finiteDiagonalNextTrafficCoordinate D right

/-- One pair is simultaneously invisible to every truncated traffic risk and
visible at the next traffic coordinate.

Convention: `D` is graph edge depth, not linkage-disequilibrium `D`. -/
def IsBlindPairForEveryTruncatedTrafficRisk
    (D : ℕ) (left right : Fin (D + 2) → ℝ) : Prop :=
  IsMomentMatchedProbabilityPair D left right ∧
    (∀ risk : TruncatedTrafficRisk D,
      risk.evaluate (finiteDiagonalTrafficProfile D left) =
        risk.evaluate (finiteDiagonalTrafficProfile D right)) ∧
    SeparatesAtNextDiagonalTraffic D left right

/-- **Strictness of the truncated traffic hierarchy at every degree.**  There
are two probability laws supported on `D + 2` points in `[1,2]` whose moments
agree through degree `D` and differ at degree `D+1`.  For diagonal covariance
sequences these moments are exactly the connected traffic coordinates indexed
by edge count. -/
theorem exists_probabilityWeights_matchingMoments_through_degree (D : ℕ) :
    ∃ left right : Fin (D + 2) → ℝ,
      IsMomentMatchedProbabilityPair D left right ∧
        SeparatesAtNextDiagonalTraffic D left right := by
  obtain ⟨weight, _hweightNe, hlow, hhigh⟩ := exists_truncatedMoment_annihilator D
  have hzero : ∑ index, weight index = 0 := by
    simpa using hlow (0 : Fin (D + 1))
  let left := perturbedMomentWeight D weight
  let right := referenceMomentWeight D
  have hprofile : finiteDiagonalTrafficProfile D left =
      finiteDiagonalTrafficProfile D right := by
    funext degree
    exact perturbedMoment_eq_referenceMoment D degree weight (hlow degree)
  refine ⟨left, right, ?_, ?_⟩
  · exact ⟨momentSeparationNode_mem_Icc D,
      fun index ↦ (perturbedMomentWeight_pos D weight index).le,
      fun _index ↦ by unfold right referenceMomentWeight momentUniformWeight; positivity,
      perturbedMomentWeight_sum_one D weight hzero,
      referenceMomentWeight_sum_one D, hprofile⟩
  · exact perturbedMoment_ne_referenceMoment D (D + 1) weight hhigh

/-- **A common hard pair for the entire degree-`D` graph-polynomial class.**
The two laws are genuine probability laws on `[1,2]`; every truncated traffic
risk gives exactly the same value on them, while their next diagonal traffic
coordinate differs. -/
theorem exists_probabilityPair_blindToEveryTruncatedTrafficRisk (D : ℕ) :
    ∃ left right : Fin (D + 2) → ℝ,
      IsBlindPairForEveryTruncatedTrafficRisk D left right := by
  obtain ⟨left, right, hpair, hnext⟩ :=
    exists_probabilityWeights_matchingMoments_through_degree D
  rcases hpair with ⟨hnodes, hleft, hright, hleftSum, hrightSum, hprofile⟩
  refine ⟨left, right,
    ⟨⟨hnodes, hleft, hright, hleftSum, hrightSum, hprofile⟩, ?_, hnext⟩⟩
  intro risk
  exact truncatedTrafficRisk_eq_of_profile_eq risk _ _ hprofile

end PolynomialTraffic

end TrafficInvariantSeparation
end Descent.Blindness
