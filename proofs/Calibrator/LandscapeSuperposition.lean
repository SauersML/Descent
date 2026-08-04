/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace Calibrator

/-!
# Near-optimal geometry under landscape superposition

This file formalizes the exact level-resolved decomposition that governs overlap-gap
persistence under a positive superposition of finite landscapes.  It deliberately separates
the easy direction from the hard one:

* `nearOptimal_superposition_iff_exists_levels` is an equality of configuration sets;
* `superposedAchievableOverlap_subset_levelResolved` is the induced one-sided inclusion for
  achievable overlaps;
* `forbiddenOverlap_of_levelResolved_cover` and
  `forbiddenInterval_of_levelResolved_cover` certify persistence of a forbidden overlap or
  interval;
* no converse is asserted.  Dissolution requires constructing common configurations and does
  not follow from this set calculus.

The final section checks the polynomial arithmetic behind the spherical calibration example.
It proves that each idiosyncratic tail has a negative endpoint certificate while their
half-weight covariance mixture has a strictly positive certificate throughout `[0, 1]`.
No external spin-glass criterion is accepted as a theorem parameter; only the polynomial fact
that such a criterion would consume is formalized here.
-/

open scoped BigOperators Matrix

section LevelResolvedCalculus

variable {Index Config Overlap R : Type*} [Ring R] [LinearOrder R]

/-- Finite-support positive linear superposition of component landscapes.  The ambient index
type need not be finite; `active` records the components actually used. -/
def superposedLandscape
    (active : Finset Index) (weight : Index → R) (energy : Index → Config → R)
    (config : Config) : R :=
  ∑ k ∈ active, weight k * energy k config

/-- Configurations above an energy level. -/
def NearOptimalSet (energy : Config → R) (level : R) : Set Config :=
  {config | level ≤ energy config}

/-- A vector of component levels whose weighted value reaches the superposed target. -/
def AdmissibleLevels
    (active : Finset Index) (weight : Index → R) (target : R) (level : Index → R) : Prop :=
  target ≤ ∑ k ∈ active, weight k * level k

/-- **Exact near-optimal-set decomposition.**  A configuration is superposed-near-optimal iff
it lies above some admissible vector of component levels.  Nonnegative weights are precisely
what makes the reverse implication valid. -/
theorem nearOptimal_superposition_iff_exists_levels
    [IsStrictOrderedRing R]
    (active : Finset Index) (weight : Index → R) (energy : Index → Config → R)
    (target : R) (hweight : ∀ k ∈ active, 0 ≤ weight k) (config : Config) :
    config ∈ NearOptimalSet (superposedLandscape active weight energy) target ↔
      ∃ level : Index → R,
        AdmissibleLevels active weight target level ∧
          ∀ k ∈ active, config ∈ NearOptimalSet (energy k) (level k) := by
  constructor
  · intro hconfig
    refine ⟨fun k ↦ energy k config, hconfig, ?_⟩
    intro k hk
    change energy k config ≤ energy k config
    exact le_rfl
  · rintro ⟨level, hadmissible, hlevel⟩
    exact hadmissible.trans <| Finset.sum_le_sum fun k hk ↦
      mul_le_mul_of_nonneg_left
        (show level k ≤ energy k config from hlevel k hk) (hweight k hk)

/-- Set-level form of the exact decomposition. -/
theorem nearOptimalSet_superposition_eq_levelResolvedUnion
    [IsStrictOrderedRing R]
    (active : Finset Index) (weight : Index → R) (energy : Index → Config → R)
    (target : R) (hweight : ∀ k ∈ active, 0 ≤ weight k) :
    NearOptimalSet (superposedLandscape active weight energy) target =
      {config | ∃ level : Index → R,
        AdmissibleLevels active weight target level ∧
          ∀ k ∈ active, config ∈ NearOptimalSet (energy k) (level k)} := by
  ext config
  exact nearOptimal_superposition_iff_exists_levels active weight energy target hweight config

/-- Overlaps achieved by a common pair of configurations above two component-level vectors. -/
def ComponentAchievableOverlaps
    (energy : Index → Config → R) (overlap : Config → Config → Overlap)
    (leftLevel rightLevel : Index → R) (k : Index) : Set Overlap :=
  {q | ∃ left right : Config,
    left ∈ NearOptimalSet (energy k) (leftLevel k) ∧
      right ∈ NearOptimalSet (energy k) (rightLevel k) ∧ overlap left right = q}

/-- Overlaps achieved by pairs above the superposed target. -/
def SuperposedAchievableOverlaps
    (active : Finset Index) (weight : Index → R) (energy : Index → Config → R)
    (overlap : Config → Config → Overlap) (target : R) : Set Overlap :=
  {q | ∃ left right : Config,
    left ∈ NearOptimalSet (superposedLandscape active weight energy) target ∧
      right ∈ NearOptimalSet (superposedLandscape active weight energy) target ∧
      overlap left right = q}

/-- The level-resolved outer approximation to the superposed achievable-overlap set. -/
def LevelResolvedAchievableEnvelope
    (active : Finset Index) (weight : Index → R) (energy : Index → Config → R)
    (overlap : Config → Config → Overlap) (target : R) : Set Overlap :=
  {q | ∃ leftLevel rightLevel : Index → R,
    AdmissibleLevels active weight target leftLevel ∧
      AdmissibleLevels active weight target rightLevel ∧
        ∀ k ∈ active,
          q ∈ ComponentAchievableOverlaps energy overlap leftLevel rightLevel k}

/-- The dual level-resolved forbidden core: every admissible pair of level vectors is blocked
by at least one active component. -/
def LevelResolvedForbiddenCore
    (active : Finset Index) (weight : Index → R) (energy : Index → Config → R)
    (overlap : Config → Config → Overlap) (target : R) : Set Overlap :=
  {q | ∀ leftLevel rightLevel : Index → R,
    AdmissibleLevels active weight target leftLevel →
      AdmissibleLevels active weight target rightLevel →
        ∃ k ∈ active,
          q ∉ ComponentAchievableOverlaps energy overlap leftLevel rightLevel k}

/-- The forbidden core is exactly the complement of the achievable envelope.  This is the
quantifier duality behind the unions-of-bands-inside-an-intersection formula. -/
theorem levelResolvedForbiddenCore_eq_compl_envelope
    (active : Finset Index) (weight : Index → R) (energy : Index → Config → R)
    (overlap : Config → Config → Overlap) (target : R) :
    LevelResolvedForbiddenCore active weight energy overlap target =
      (LevelResolvedAchievableEnvelope active weight energy overlap target)ᶜ := by
  ext q
  constructor
  · intro hcore henvelope
    rcases henvelope with ⟨leftLevel, rightLevel, hleft, hright, hall⟩
    rcases hcore leftLevel rightLevel hleft hright with ⟨k, hk, hforbidden⟩
    exact hforbidden (hall k hk)
  · intro houtside leftLevel rightLevel hleft hright
    by_contra hnone
    apply houtside
    refine ⟨leftLevel, rightLevel, hleft, hright, ?_⟩
    intro k hk
    by_contra hforbidden
    exact hnone ⟨k, hk, hforbidden⟩

/-- **Universal inclusion for achievable overlaps.**  Every overlap of a superposed-near-optimal
pair belongs simultaneously to every component's achievable set at some two admissible level
vectors.  The component witnesses on the right may differ, so this is only an inclusion. -/
theorem superposedAchievableOverlap_subset_levelResolved
    [IsStrictOrderedRing R]
    (active : Finset Index) (weight : Index → R) (energy : Index → Config → R)
    (overlap : Config → Config → Overlap) (target : R)
    (hweight : ∀ k ∈ active, 0 ≤ weight k) (q : Overlap)
    (hq : q ∈ SuperposedAchievableOverlaps active weight energy overlap target) :
    q ∈ LevelResolvedAchievableEnvelope active weight energy overlap target := by
  rcases hq with ⟨left, right, hleft, hright, hoverlap⟩
  rw [nearOptimal_superposition_iff_exists_levels active weight energy target hweight left] at hleft
  rw [nearOptimal_superposition_iff_exists_levels active weight energy target hweight right]
    at hright
  rcases hleft with ⟨leftLevel, hleftAdmissible, hleftLevel⟩
  rcases hright with ⟨rightLevel, hrightAdmissible, hrightLevel⟩
  refine ⟨leftLevel, rightLevel, hleftAdmissible, hrightAdmissible, ?_⟩
  intro k hk
  exact ⟨left, right, hleftLevel k hk, hrightLevel k hk, hoverlap⟩

/-- Set-level universal inclusion for achievable overlaps. -/
theorem superposedAchievableOverlaps_subset_levelResolvedEnvelope
    [IsStrictOrderedRing R]
    (active : Finset Index) (weight : Index → R) (energy : Index → Config → R)
    (overlap : Config → Config → Overlap) (target : R)
    (hweight : ∀ k ∈ active, 0 ≤ weight k) :
    SuperposedAchievableOverlaps active weight energy overlap target ⊆
      LevelResolvedAchievableEnvelope active weight energy overlap target := by
  intro q hq
  exact superposedAchievableOverlap_subset_levelResolved
    active weight energy overlap target hweight q hq

/-- A level-resolved cover by component forbidden sets certifies a forbidden overlap for the
superposition.  This is the rigorous persistence direction. -/
theorem forbiddenOverlap_of_levelResolved_cover
    [IsStrictOrderedRing R]
    (active : Finset Index) (weight : Index → R) (energy : Index → Config → R)
    (overlap : Config → Config → Overlap) (target : R)
    (hweight : ∀ k ∈ active, 0 ≤ weight k) (q : Overlap)
    (hcover : q ∈ LevelResolvedForbiddenCore active weight energy overlap target) :
    q ∉ SuperposedAchievableOverlaps active weight energy overlap target := by
  intro hq
  rcases superposedAchievableOverlap_subset_levelResolved
      active weight energy overlap target hweight q hq with
    ⟨leftLevel, rightLevel, hleft, hright, hall⟩
  rcases hcover leftLevel rightLevel hleft hright with ⟨k, hk⟩
  exact hk.2 (hall k hk.1)

/-- Set-level dual inclusion: the level-resolved forbidden core is genuinely forbidden by the
superposition. -/
theorem levelResolvedForbiddenCore_subset_superposedComplement
    [IsStrictOrderedRing R]
    (active : Finset Index) (weight : Index → R) (energy : Index → Config → R)
    (overlap : Config → Config → Overlap) (target : R)
    (hweight : ∀ k ∈ active, 0 ≤ weight k) :
    LevelResolvedForbiddenCore active weight energy overlap target ⊆
      (SuperposedAchievableOverlaps active weight energy overlap target)ᶜ := by
  intro q hq
  exact forbiddenOverlap_of_levelResolved_cover
    active weight energy overlap target hweight q hq

/-- Interval version of the persistence theorem.  The order on overlaps is used only to name the
candidate interval; the proof is pointwise. -/
theorem forbiddenInterval_of_levelResolved_cover
    [IsStrictOrderedRing R] [LinearOrder Overlap]
    (active : Finset Index) (weight : Index → R) (energy : Index → Config → R)
    (overlap : Config → Config → Overlap) (target : R)
    (hweight : ∀ k ∈ active, 0 ≤ weight k) (lower upper : Overlap)
    (hcover : Set.Ioo lower upper ⊆
      LevelResolvedForbiddenCore active weight energy overlap target) :
    Set.Ioo lower upper ⊆
      (SuperposedAchievableOverlaps active weight energy overlap target)ᶜ := by
  intro q hq
  exact forbiddenOverlap_of_levelResolved_cover active weight energy overlap target hweight q
    (hcover hq)

end LevelResolvedCalculus

/-! ## Boundary of the simplex -/

section SimplexBoundary

variable {Index Config R : Type*} [Ring R] [DecidableEq Index]

/-- A simplex vertex selecting one component landscape. -/
def oneHotWeight (selected : Index) (k : Index) : R :=
  if k = selected then 1 else 0

/-- At a simplex vertex the superposition is exactly the selected landscape. -/
theorem superposedLandscape_oneHot
    (active : Finset Index) (energy : Index → Config → R) (selected : Index)
    (hselected : selected ∈ active) (config : Config) :
    superposedLandscape active (oneHotWeight selected) energy config =
      energy selected config := by
  simp [superposedLandscape, oneHotWeight, hselected]

/-- Consequently the near-optimal set at a simplex vertex is the component near-optimal set.
Any statement claiming uniform destruction up to the boundary must therefore fail. -/
theorem nearOptimalSet_superposition_oneHot
    [LinearOrder R] [IsStrictOrderedRing R]
    (active : Finset Index) (energy : Index → Config → R) (selected : Index)
    (hselected : selected ∈ active) (target : R) :
    NearOptimalSet (superposedLandscape active (oneHotWeight selected) energy) target =
      NearOptimalSet (energy selected) target := by
  ext config
  simp only [NearOptimalSet, Set.mem_setOf_eq,
    superposedLandscape_oneHot active energy selected hselected]

end SimplexBoundary

/-! ## Band migration is compatible with disjoint endpoints -/

/-- An open forbidden band with fixed width whose left endpoint moves affinely in `mix`. -/
def translatedForbiddenBand (start velocity width mix : ℝ) : Set ℝ :=
  Set.Ioo (start + velocity * mix) (start + velocity * mix + width)

/-- Positive width is exactly what supplies a canonical point in every translated band. -/
theorem translatedForbiddenBand_nonempty
    (start velocity width mix : ℝ) (hwidth : 0 < width) :
    (translatedForbiddenBand start velocity width mix).Nonempty := by
  refine ⟨start + velocity * mix + width / 2, ?_⟩
  constructor <;> linarith

/-- If the one-step displacement dominates the width, the endpoint bands are disjoint. -/
theorem translatedForbiddenBand_endpoints_disjoint
    (start velocity width : ℝ) (hseparated : width ≤ velocity) :
    Disjoint (translatedForbiddenBand start velocity width 0)
      (translatedForbiddenBand start velocity width 1) := by
  rw [Set.disjoint_left]
  intro q hleft hright
  rcases hleft with ⟨hleftLower, hleftUpper⟩
  rcases hright with ⟨hrightLower, hrightUpper⟩
  linarith

/-- Both endpoints move with the same exact affine displacement. -/
theorem translatedForbiddenBand_endpoint_displacement
    (start velocity width leftMix rightMix : ℝ) :
    ((start + velocity * rightMix) - (start + velocity * leftMix) =
        velocity * (rightMix - leftMix)) ∧
      ((start + velocity * rightMix + width) -
          (start + velocity * leftMix + width) = velocity * (rightMix - leftMix)) := by
  constructor <;> ring

/-- The concrete unit-width band used to refute the endpoint-disjointness heuristic. -/
def migratingForbiddenBand (mix : ℝ) : Set ℝ :=
  translatedForbiddenBand 0 2 1 mix

/-- The endpoint bands are disjoint. -/
theorem migratingForbiddenBand_endpoints_disjoint :
    Disjoint (migratingForbiddenBand 0) (migratingForbiddenBand 1) := by
  exact translatedForbiddenBand_endpoints_disjoint 0 2 1 (by norm_num)

/-- Nevertheless every point of the interpolation path has a nonempty forbidden band.  Thus
endpoint disjointness and continuity alone cannot imply gap dissolution: a band may migrate. -/
theorem migratingForbiddenBand_nonempty (mix : ℝ) :
    (migratingForbiddenBand mix).Nonempty := by
  exact translatedForbiddenBand_nonempty 0 2 1 mix (by norm_num)

/-! ## Spherical covariance calibration arithmetic -/

/-- Even mixed spherical covariance with a shared quadratic component and two tail terms. -/
noncomputable def mixedSphericalCovariance (alpha beta q : ℝ) : ℝ :=
  q ^ 2 + alpha * q ^ 4 + beta * q ^ 6

/-- **mixedSphericalCovariance pinned at a reference point.** No theorem in the corpus evaluated
this definition, so every body agreeing with it in sign and monotonicity was indistinguishable
from it. At all arguments equal to `1 / 2` it is `37 / 128`, which fixes the coefficients a
one-sided bound or an invariance leaves free. -/
theorem mixedSphericalCovariance_at_reference_point :
    mixedSphericalCovariance (1 / 2) (1 / 2) (1 / 2) = 37 / 128 := by
  unfold mixedSphericalCovariance
  norm_num

/-- Convex covariance mixing preserves the shared quadratic component and averages every
idiosyncratic tail coefficient. -/
theorem mixedSphericalCovariance_weighted_add
    (firstWeight secondWeight firstAlpha secondAlpha firstBeta secondBeta q : ℝ)
    (hweight : firstWeight + secondWeight = 1) :
    firstWeight * mixedSphericalCovariance firstAlpha firstBeta q +
        secondWeight * mixedSphericalCovariance secondAlpha secondBeta q =
      mixedSphericalCovariance
        (firstWeight * firstAlpha + secondWeight * secondAlpha)
        (firstWeight * firstBeta + secondWeight * secondBeta) q := by
  unfold mixedSphericalCovariance
  calc
    firstWeight * (q ^ 2 + firstAlpha * q ^ 4 + firstBeta * q ^ 6) +
        secondWeight * (q ^ 2 + secondAlpha * q ^ 4 + secondBeta * q ^ 6) =
      (firstWeight + secondWeight) * q ^ 2 +
        (firstWeight * firstAlpha + secondWeight * secondAlpha) * q ^ 4 +
          (firstWeight * firstBeta + secondWeight * secondBeta) * q ^ 6 := by ring
    _ = q ^ 2 +
        (firstWeight * firstAlpha + secondWeight * secondAlpha) * q ^ 4 +
          (firstWeight * firstBeta + secondWeight * secondBeta) * q ^ 6 := by rw [hweight, one_mul]

/-- Independent half-weight superposition adds covariances with squared weights.  The shared
quadratic component is retained, whereas the two idiosyncratic tails are each diluted by one
half. -/
theorem halfWeight_quartic_sextic_covariance (q : ℝ) :
    (1 / 2 : ℝ) * mixedSphericalCovariance (1 / 10) 0 q +
        (1 / 2 : ℝ) * mixedSphericalCovariance 0 (1 / 14) q =
      mixedSphericalCovariance (1 / 20) (1 / 28) q := by
  convert mixedSphericalCovariance_weighted_add
    (1 / 2) (1 / 2) (1 / 10) 0 0 (1 / 14) q (by norm_num) using 1
  all_goals norm_num

/-- The polynomial certificate `2 ξ'' ξ'''' - 3 (ξ''')²` for
`ξ(q) = q² + alpha q⁴ + beta q⁶`. -/
noncomputable def sphericalGaplessnessCertificate (alpha beta q : ℝ) : ℝ :=
  2 * (2 + 12 * alpha * q ^ 2 + 30 * beta * q ^ 4) *
      (24 * alpha + 360 * beta * q ^ 2) -
    3 * (24 * alpha * q + 120 * beta * q ^ 3) ^ 2

/-- Expanded certificate.  It isolates the positive shared-curvature contribution and the
three tail-interaction penalties used by the robust positivity criterion below. -/
theorem sphericalGaplessnessCertificate_eq
    (alpha beta q : ℝ) :
    sphericalGaplessnessCertificate alpha beta q =
      96 * alpha + (1440 * beta - 1152 * alpha ^ 2) * q ^ 2 -
        7200 * alpha * beta * q ^ 4 - 21600 * beta ^ 2 * q ^ 6 := by
  unfold sphericalGaplessnessCertificate
  ring

/-- For a nonnegative pure quartic tail, endpoint failure is equivalent to crossing the
classical `1 / 12` threshold. -/
theorem quarticTail_certificate_at_one_neg_iff
    (alpha : ℝ) (halpha : 0 ≤ alpha) :
    sphericalGaplessnessCertificate alpha 0 1 < 0 ↔ 1 / 12 < alpha := by
  have hfactor : sphericalGaplessnessCertificate alpha 0 1 =
      96 * alpha * (1 - 12 * alpha) := by
    rw [sphericalGaplessnessCertificate_eq]
    ring
  rw [hfactor]
  constructor
  · intro hnegative
    by_contra hthreshold
    have hupper : alpha ≤ 1 / 12 := le_of_not_gt hthreshold
    have hnonnegative : 0 ≤ 96 * alpha * (1 - 12 * alpha) :=
      mul_nonneg (mul_nonneg (by norm_num) halpha) (by linarith)
    linarith
  · intro hthreshold
    exact mul_neg_of_pos_of_neg (mul_pos (by norm_num) (by linarith)) (by linarith)

/-- One-way form convenient when the coefficient is already known to exceed the threshold. -/
theorem quarticTail_certificate_at_one_neg_of_gt
    (alpha : ℝ) (halpha : 1 / 12 < alpha) :
    sphericalGaplessnessCertificate alpha 0 1 < 0 := by
  exact (quarticTail_certificate_at_one_neg_iff alpha (by linarith)).2 halpha

/-- For a nonnegative pure sextic tail, endpoint failure is equivalent to crossing the
`1 / 15` threshold. -/
theorem sexticTail_certificate_at_one_neg_iff
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    sphericalGaplessnessCertificate 0 beta 1 < 0 ↔ 1 / 15 < beta := by
  have hfactor : sphericalGaplessnessCertificate 0 beta 1 =
      1440 * beta * (1 - 15 * beta) := by
    rw [sphericalGaplessnessCertificate_eq]
    ring
  rw [hfactor]
  constructor
  · intro hnegative
    by_contra hthreshold
    have hupper : beta ≤ 1 / 15 := le_of_not_gt hthreshold
    have hnonnegative : 0 ≤ 1440 * beta * (1 - 15 * beta) :=
      mul_nonneg (mul_nonneg (by norm_num) hbeta) (by linarith)
    linarith
  · intro hthreshold
    exact mul_neg_of_pos_of_neg (mul_pos (by norm_num) (by linarith)) (by linarith)

/-- One-way form convenient when the coefficient is already known to exceed the threshold. -/
theorem sexticTail_certificate_at_one_neg_of_gt
    (beta : ℝ) (hbeta : 1 / 15 < beta) :
    sphericalGaplessnessCertificate 0 beta 1 < 0 := by
  exact (sexticTail_certificate_at_one_neg_iff beta (by linarith)).2 hbeta

/-- The `q⁴` summand's endpoint certificate is negative. -/
theorem quarticTail_certificate_at_one_neg :
    sphericalGaplessnessCertificate (1 / 10) 0 1 < 0 := by
  exact quarticTail_certificate_at_one_neg_of_gt (1 / 10) (by norm_num)

/-- The `q⁶` summand's endpoint certificate is negative. -/
theorem sexticTail_certificate_at_one_neg :
    sphericalGaplessnessCertificate 0 (1 / 14) 1 < 0 := by
  exact sexticTail_certificate_at_one_neg_of_gt (1 / 14) (by norm_num)

/-- A reusable sufficient condition for strict positivity on the full overlap interval.  It
quantifies when shared quartic curvature dominates both its self-interaction and every sextic
tail penalty. -/
theorem sphericalGaplessnessCertificate_pos_of_tail_condition
    (alpha beta q : ℝ) (halpha : 0 < alpha) (hbeta : 0 ≤ beta)
    (htail : 0 ≤ 1440 * beta - 1152 * alpha ^ 2 -
      7200 * alpha * beta - 21600 * beta ^ 2)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    0 < sphericalGaplessnessCertificate alpha beta q := by
  have hq2 : 0 ≤ q ^ 2 := sq_nonneg q
  have hq2le : q ^ 2 ≤ 1 := by nlinarith
  have hq4le : q ^ 4 ≤ q ^ 2 := by nlinarith [sq_nonneg (q ^ 2)]
  have hq6le : q ^ 6 ≤ q ^ 2 := by
    have hq4nonneg : 0 ≤ q ^ 4 := by nlinarith [sq_nonneg (q ^ 2)]
    calc
      q ^ 6 = q ^ 4 * q ^ 2 := by ring
      _ ≤ q ^ 4 * 1 := mul_le_mul_of_nonneg_left hq2le hq4nonneg
      _ ≤ q ^ 2 := by simpa using hq4le
  have hab : 0 ≤ alpha * beta := mul_nonneg halpha.le hbeta
  have hquartic := mul_le_mul_of_nonneg_left hq4le
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 7200) hab)
  have hsextic := mul_le_mul_of_nonneg_left hq6le
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 21600) (sq_nonneg beta))
  have htailTerm : 0 ≤
      (1440 * beta - 1152 * alpha ^ 2 - 7200 * alpha * beta -
        21600 * beta ^ 2) * q ^ 2 := mul_nonneg htail hq2
  rw [sphericalGaplessnessCertificate_eq]
  nlinarith

/-- After half-weight covariance superposition, the common quadratic component retains full
strength while each idiosyncratic tail is halved.  The resulting certificate is strictly
positive on the full overlap interval. -/
theorem dilutedTails_certificate_pos (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    0 < sphericalGaplessnessCertificate (1 / 20) (1 / 28) q := by
  apply sphericalGaplessnessCertificate_pos_of_tail_condition
  · norm_num
  · norm_num
  · norm_num
  · exact hq0
  · exact hq1

/-! ## Anisotropy separates Euclidean overlap from covariance energy -/

abbrev TwoCoordinateConfiguration := Fin 2 → ℝ

/-- Euclidean overlap, the coordinate used by the classical isotropic band calculation. -/
noncomputable def configurationOverlap
    (left right : TwoCoordinateConfiguration) : ℝ :=
  dotProduct left right

/-- Energy scale of the displacement from a planted configuration under covariance `sigma`. -/
noncomputable def covarianceDisplacementEnergy
    (sigma : Matrix (Fin 2) (Fin 2) ℝ)
    (candidate truth : TwoCoordinateConfiguration) : ℝ :=
  dotProduct (candidate - truth) (sigma.mulVec (candidate - truth))

/-- General symmetric two-coordinate covariance. -/
noncomputable def symmetricTwoCoordinateCovariance
    (firstVariance secondVariance correlation : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![firstVariance, correlation; correlation, secondVariance]

/-- Its quadratic form in coordinates. -/
theorem symmetricTwoCoordinateCovariance_energy_eq
    (firstVariance secondVariance correlation : ℝ)
    (vector : TwoCoordinateConfiguration) :
    dotProduct vector
        ((symmetricTwoCoordinateCovariance firstVariance secondVariance correlation).mulVec
          vector) =
      firstVariance * vector 0 ^ 2 + 2 * correlation * vector 0 * vector 1 +
        secondVariance * vector 1 ^ 2 := by
  simp [symmetricTwoCoordinateCovariance, dotProduct, Matrix.mulVec, Fin.sum_univ_two]
  ring

/-- The familiar positive-principal-minor conditions imply strict positivity of the full
quadratic form. -/
theorem symmetricTwoCoordinateCovariance_pos
    (firstVariance secondVariance correlation : ℝ)
    (hfirst : 0 < firstVariance)
    (hdeterminant : correlation ^ 2 < firstVariance * secondVariance)
    (vector : TwoCoordinateConfiguration) (hvector : vector ≠ 0) :
    0 < dotProduct vector
      ((symmetricTwoCoordinateCovariance firstVariance secondVariance correlation).mulVec
        vector) := by
  rw [symmetricTwoCoordinateCovariance_energy_eq]
  by_cases hsecond : vector 1 = 0
  · have hfirstCoordinate : vector 0 ≠ 0 := by
      intro hzero
      apply hvector
      funext i
      fin_cases i
      · exact hzero
      · exact hsecond
    rw [hsecond]
    norm_num
    exact mul_pos hfirst (sq_pos_of_ne_zero hfirstCoordinate)
  · have hdetPositive : 0 < firstVariance * secondVariance - correlation ^ 2 :=
      sub_pos.mpr hdeterminant
    have hcompletion :
        firstVariance *
            (firstVariance * vector 0 ^ 2 + 2 * correlation * vector 0 * vector 1 +
              secondVariance * vector 1 ^ 2) =
          (firstVariance * vector 0 + correlation * vector 1) ^ 2 +
            (firstVariance * secondVariance - correlation ^ 2) * vector 1 ^ 2 := by
      ring
    have hright : 0 <
        (firstVariance * vector 0 + correlation * vector 1) ^ 2 +
          (firstVariance * secondVariance - correlation ^ 2) * vector 1 ^ 2 := by
      exact add_pos_of_nonneg_of_pos (sq_nonneg _)
        (mul_pos hdetPositive (sq_pos_of_ne_zero hsecond))
    have hproduct : 0 < firstVariance *
        (firstVariance * vector 0 ^ 2 + 2 * correlation * vector 0 * vector 1 +
          secondVariance * vector 1 ^ 2) := by
      rw [hcompletion]
      exact hright
    rw [mul_comm] at hproduct
    exact pos_of_mul_pos_left hproduct hfirst.le

/-- A positive anisotropic covariance with eigen-directions rotated relative to coordinates. -/
noncomputable def overlapEnergyWitnessCovariance : Matrix (Fin 2) (Fin 2) ℝ :=
  symmetricTwoCoordinateCovariance 2 2 1

/-- The covariance energy is a sum of three squares. -/
theorem overlapEnergyWitnessCovariance_energy_eq (vector : TwoCoordinateConfiguration) :
    dotProduct vector (overlapEnergyWitnessCovariance.mulVec vector) =
      vector 0 ^ 2 + vector 1 ^ 2 + (vector 0 + vector 1) ^ 2 := by
  simp [overlapEnergyWitnessCovariance, symmetricTwoCoordinateCovariance, dotProduct,
    Matrix.mulVec, Fin.sum_univ_two]
  ring

/-- The witness covariance is strictly positive on every nonzero configuration. -/
theorem overlapEnergyWitnessCovariance_pos
    (vector : TwoCoordinateConfiguration) (hvector : vector ≠ 0) :
    0 < dotProduct vector (overlapEnergyWitnessCovariance.mulVec vector) := by
  exact symmetricTwoCoordinateCovariance_pos 2 2 1 (by norm_num) (by norm_num)
    vector hvector

noncomputable def overlapEnergyTruth : TwoCoordinateConfiguration := ![1, 0]
noncomputable def overlapEnergyPositive : TwoCoordinateConfiguration := ![0, 1]
noncomputable def overlapEnergyNegative : TwoCoordinateConfiguration := ![0, -1]

/-- The two antipodal candidates have identical planted overlap and Euclidean norm. -/
theorem overlapEnergyCandidates_same_overlap_and_norm :
    configurationOverlap overlapEnergyPositive overlapEnergyTruth = 0 ∧
      configurationOverlap overlapEnergyNegative overlapEnergyTruth = 0 ∧
      configurationOverlap overlapEnergyPositive overlapEnergyPositive = 1 ∧
      configurationOverlap overlapEnergyNegative overlapEnergyNegative = 1 := by
  norm_num [configurationOverlap, overlapEnergyTruth, overlapEnergyPositive,
    overlapEnergyNegative, dotProduct, Fin.sum_univ_two]

/-- For a general symmetric covariance, the same-overlap candidates have energies differing by
exactly four times the off-diagonal correlation. -/
theorem overlapEnergyCandidates_covariance_energy
    (firstVariance secondVariance correlation : ℝ) :
    covarianceDisplacementEnergy
        (symmetricTwoCoordinateCovariance firstVariance secondVariance correlation)
        overlapEnergyPositive overlapEnergyTruth =
          firstVariance + secondVariance - 2 * correlation ∧
      covarianceDisplacementEnergy
        (symmetricTwoCoordinateCovariance firstVariance secondVariance correlation)
        overlapEnergyNegative overlapEnergyTruth =
          firstVariance + secondVariance + 2 * correlation := by
  norm_num [covarianceDisplacementEnergy, symmetricTwoCoordinateCovariance,
    overlapEnergyTruth, overlapEnergyPositive, overlapEnergyNegative, dotProduct,
    Matrix.mulVec, Fin.sum_univ_two]
  constructor <;> ring

/-- The covariance-energy gap is therefore exactly `4 * correlation`. -/
theorem overlapEnergyCandidates_energy_gap
    (firstVariance secondVariance correlation : ℝ) :
    covarianceDisplacementEnergy
        (symmetricTwoCoordinateCovariance firstVariance secondVariance correlation)
        overlapEnergyNegative overlapEnergyTruth -
      covarianceDisplacementEnergy
        (symmetricTwoCoordinateCovariance firstVariance secondVariance correlation)
        overlapEnergyPositive overlapEnergyTruth = 4 * correlation := by
  rw [(overlapEnergyCandidates_covariance_energy firstVariance secondVariance correlation).1,
    (overlapEnergyCandidates_covariance_energy firstVariance secondVariance correlation).2]
  ring

/-- The same-overlap candidates are separated by covariance energy exactly when the covariance
has a nonzero off-diagonal entry in the configuration basis. -/
theorem overlapEnergyCandidates_energy_ne_iff
    (firstVariance secondVariance correlation : ℝ) :
    covarianceDisplacementEnergy
        (symmetricTwoCoordinateCovariance firstVariance secondVariance correlation)
        overlapEnergyNegative overlapEnergyTruth ≠
      covarianceDisplacementEnergy
        (symmetricTwoCoordinateCovariance firstVariance secondVariance correlation)
        overlapEnergyPositive overlapEnergyTruth ↔ correlation ≠ 0 := by
  constructor
  · intro henergy hzero
    apply henergy
    rw [(overlapEnergyCandidates_covariance_energy firstVariance secondVariance correlation).1,
      (overlapEnergyCandidates_covariance_energy firstVariance secondVariance correlation).2,
      hzero]
    ring
  · intro hcorrelation henergy
    apply hcorrelation
    have hgap := overlapEnergyCandidates_energy_gap firstVariance secondVariance correlation
    rw [henergy, sub_self] at hgap
    linarith

/-- The two candidates have the same Euclidean norm and the same overlap with the planted
configuration, but different covariance energies.  Thus an anisotropic first-moment theory
cannot project to overlap alone; its state space must retain both `(ρ, r)`. -/
theorem equal_overlap_different_covariance_energy :
    configurationOverlap overlapEnergyPositive overlapEnergyTruth = 0 ∧
      configurationOverlap overlapEnergyNegative overlapEnergyTruth = 0 ∧
      configurationOverlap overlapEnergyPositive overlapEnergyPositive = 1 ∧
      configurationOverlap overlapEnergyNegative overlapEnergyNegative = 1 ∧
      covarianceDisplacementEnergy overlapEnergyWitnessCovariance
          overlapEnergyPositive overlapEnergyTruth = 2 ∧
      covarianceDisplacementEnergy overlapEnergyWitnessCovariance
          overlapEnergyNegative overlapEnergyTruth = 6 := by
  refine ⟨overlapEnergyCandidates_same_overlap_and_norm.1,
    overlapEnergyCandidates_same_overlap_and_norm.2.1,
    overlapEnergyCandidates_same_overlap_and_norm.2.2.1,
    overlapEnergyCandidates_same_overlap_and_norm.2.2.2, ?_⟩
  have henergy := overlapEnergyCandidates_covariance_energy 2 2 1
  norm_num [overlapEnergyWitnessCovariance] at henergy ⊢
  exact henergy

end Calibrator
