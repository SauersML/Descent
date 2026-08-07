/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Descent.Core.Ratios

assert_below Descent.Conditionals Descent.Portability Descent.Decision Descent.Program

namespace Descent.Blindness

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
      active weight energy overlap target hweight q hq with ⟨leftLevel, rightLevel, hleft, hright,
        hall⟩
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

/-- **The simplex vertex is the Kronecker delta.** Over `ℝ` this weight is
`Descent.Core.kronecker` with its arguments in the other order, so the two names denote one
function and a divergence in either spelling fails this equation.

They are not written in terms of each other because they cannot be: `kronecker` is real-valued,
while the superposition calculus below needs a weight in an arbitrary `Ring R` and uses it at
`R` ordered by `LinearOrder R`. Collapsing the definitions would specialise that calculus to
`ℝ` to remove a duplication the equation already removes. -/
theorem oneHotWeight_eq_kronecker (selected k : Index) :
    (oneHotWeight selected k : ℝ) = Descent.Core.kronecker k selected :=
  rfl

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
    [LinearOrder R]
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

/-- The concrete unit-width band used to refute the endpoint-disjointness heuristic.

    Empirical status: NOT AN EMPIRICAL CLAIM. This is a counterexample, chosen
    for its arithmetic and not offered as a description of any migrating
    population. Its job is to show that a heuristic fails, which one instance
    suffices to do -- and a measurement finding no real population shaped like
    this would leave the refutation untouched, which is what makes it a
    counterexample rather than a claim. -/
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

/-- Reference evaluation; see `Descent.Core.Ratios` for what these pin and why. -/
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

/-! ## Exact population transition for a two-environment covariance mixture -/

/-- The positive root of `r² + r - 1 = 0`.  It is the correlation threshold at which the
two-block population overlap profile changes from monotone to gapped. -/
noncomputable def goldenCorrelationThreshold : ℝ :=
  (Real.sqrt 5 - 1) / 2

/-- The threshold lies strictly inside the correlation interval. -/
theorem goldenCorrelationThreshold_mem_Ioo :
    goldenCorrelationThreshold ∈ Set.Ioo (0 : ℝ) 1 := by
  have hsqrt : (Real.sqrt 5) ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hsqrtNonneg : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
  unfold goldenCorrelationThreshold
  constructor <;> nlinarith

/-- Golden-ratio identity used by every threshold calculation below. -/
theorem goldenCorrelationThreshold_sq_add_self :
    goldenCorrelationThreshold ^ 2 + goldenCorrelationThreshold = 1 := by
  have hsqrt : (Real.sqrt 5) ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  unfold goldenCorrelationThreshold
  nlinarith

/-- Population overlap profile for the rank-two correlated sparse-design witness.  Here `x`
is the missed-support fraction and `q` is the squared active correlation. -/
noncomputable def populationOverlapProfile (q x : ℝ) : ℝ :=
  Descent.Core.overlapProfile q x

/-- With a vanishing denominator Mathlib returns `0`, which is a value this quantity can also
take legitimately, so the branch is named rather than left to be inferred from the result. -/
theorem populationOverlapProfile_at_zero_denominator_is_junk (q x : ℝ)
    (hzero : (1 - q * x * (1 - x)) = 0) :
    populationOverlapProfile q x = 0 := by
  exact Descent.Core.overlapProfile_at_zero_denominator_is_junk q x hzero


/-- The far, disjoint candidate has normalized loss `1 - q`. -/
@[simp] theorem populationOverlapProfile_one (q : ℝ) :
    populationOverlapProfile q 1 = 1 - q := by
  exact Descent.Core.overlapProfile_at_one q

/-- The planted support has zero excess population loss. -/
@[simp] theorem populationOverlapProfile_zero (q : ℝ) :
    populationOverlapProfile q 0 = 0 := by
  exact Descent.Core.overlapProfile_at_zero_mass q

/-- Endpoint derivative numerator of the overlap profile.  Its sign detects whether the
profile turns down before reaching the disjoint-support endpoint. -/
noncomputable def populationGapCertificate (correlation : ℝ) : ℝ :=
  1 - 3 * correlation ^ 2 + correlation ^ 4

/-- Difference factorization for the population gap certificate. -/
theorem populationGapCertificate_sub_eq_mul (left right : ℝ) :
    populationGapCertificate left - populationGapCertificate right =
      (left ^ 2 - right ^ 2) * (left ^ 2 + right ^ 2 - 3) := by
  unfold populationGapCertificate
  ring

/-- The golden threshold is exactly the zero of the population gap certificate. -/
theorem populationGapCertificate_goldenCorrelationThreshold :
    populationGapCertificate goldenCorrelationThreshold = 0 := by
  have hgold : goldenCorrelationThreshold ^ 2 = 1 - goldenCorrelationThreshold := by
    linarith [goldenCorrelationThreshold_sq_add_self]
  unfold populationGapCertificate
  calc
    1 - 3 * goldenCorrelationThreshold ^ 2 + goldenCorrelationThreshold ^ 4 =
        1 - 3 * goldenCorrelationThreshold ^ 2 +
          (goldenCorrelationThreshold ^ 2) ^ 2 := by ring
    _ = 0 := by nlinarith [hgold]

/-- On squared correlations in `[0,1]`, the certificate is nonnegative below the golden
threshold. -/
theorem populationGapCertificate_nonneg_of_abs_le_golden
    (correlation : ℝ) (hcorrelation : |correlation| ≤ goldenCorrelationThreshold) :
    0 ≤ populationGapCertificate correlation := by
  have hthreshold := goldenCorrelationThreshold_mem_Ioo
  have hsq : correlation ^ 2 ≤ goldenCorrelationThreshold ^ 2 := by
    rw [sq_le_sq, abs_of_pos hthreshold.1]
    exact hcorrelation
  have hq0 : 0 ≤ correlation ^ 2 := sq_nonneg correlation
  have hq1 : correlation ^ 2 ≤ 1 := by
    exact (sq_le_one_iff_abs_le_one correlation).mpr (hcorrelation.trans hthreshold.2.le)
  have hroot : populationGapCertificate goldenCorrelationThreshold = 0 :=
    populationGapCertificate_goldenCorrelationThreshold
  have hfactor := populationGapCertificate_sub_eq_mul
    correlation goldenCorrelationThreshold
  have hsecond : correlation ^ 2 + goldenCorrelationThreshold ^ 2 - 3 ≤ 0 := by
    have hthresholdSq : goldenCorrelationThreshold ^ 2 ≤ 1 := by
      exact (sq_le_one_iff_abs_le_one goldenCorrelationThreshold).mpr (by
        rw [abs_of_pos hthreshold.1]
        exact hthreshold.2.le)
    nlinarith
  have hproduct : 0 ≤
      (correlation ^ 2 - goldenCorrelationThreshold ^ 2) *
        (correlation ^ 2 + goldenCorrelationThreshold ^ 2 - 3) :=
    mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr hsq) hsecond
  rw [hroot, sub_zero] at hfactor
  linarith

/-- On the admissible correlation interval, crossing the golden threshold makes the endpoint
certificate strictly negative and hence forces an interior turn of the population profile. -/
theorem populationGapCertificate_neg_of_golden_lt_abs
    (correlation : ℝ) (hcorrelation : |correlation| ≤ 1)
    (hgolden : goldenCorrelationThreshold < |correlation|) :
    populationGapCertificate correlation < 0 := by
  have hthreshold := goldenCorrelationThreshold_mem_Ioo
  have hsq : goldenCorrelationThreshold ^ 2 < correlation ^ 2 := by
    rw [sq_lt_sq, abs_of_pos hthreshold.1]
    exact hgolden
  have hq1 : correlation ^ 2 ≤ 1 := by
    exact (sq_le_one_iff_abs_le_one correlation).mpr hcorrelation
  have hroot : populationGapCertificate goldenCorrelationThreshold = 0 :=
    populationGapCertificate_goldenCorrelationThreshold
  have hfactor := populationGapCertificate_sub_eq_mul
    correlation goldenCorrelationThreshold
  have hsecond : correlation ^ 2 + goldenCorrelationThreshold ^ 2 - 3 < 0 := by
    have hthresholdSq : goldenCorrelationThreshold ^ 2 < 1 := by
      exact (sq_lt_one_iff_abs_lt_one goldenCorrelationThreshold).mpr (by
        rw [abs_of_pos hthreshold.1]
        exact hthreshold.2)
    nlinarith
  have hproduct :
      (correlation ^ 2 - goldenCorrelationThreshold ^ 2) *
          (correlation ^ 2 + goldenCorrelationThreshold ^ 2 - 3) < 0 :=
    mul_neg_of_pos_of_neg (sub_pos.mpr hsq) hsecond
  rw [hroot, sub_zero] at hfactor
  linarith

/-! ### Arbitrary finite environment mixtures -/

/-- Effective active correlation of a finite collection of environments. -/
noncomputable def pooledEnvironmentCorrelations
    {Environment : Type*} (active : Finset Environment)
    (mass correlation : Environment → ℝ) : ℝ :=
  ∑ environment ∈ active, mass environment * correlation environment

/-- Vanishing identity: with no active environments there is nothing to pool. -/
theorem pooledEnvironmentCorrelations_empty_eq_zero {Environment : Type*}
    (mass correlation : Environment → ℝ) :
    pooledEnvironmentCorrelations (∅ : Finset Environment) mass correlation = 0 := by
  unfold pooledEnvironmentCorrelations
  simp


/-- A normalized nonnegative environment mixture remains inside the component correlation
interval.  This is the general convex-hull law behind every two-environment calculation. -/
theorem pooledEnvironmentCorrelations_mem_Icc
    {Environment : Type*} (active : Finset Environment)
    (mass correlation : Environment → ℝ) (lower upper : ℝ)
    (hmass : ∀ environment ∈ active, 0 ≤ mass environment)
    (hsum : ∑ environment ∈ active, mass environment = 1)
    (hcorrelation : ∀ environment ∈ active,
      correlation environment ∈ Set.Icc lower upper) :
    pooledEnvironmentCorrelations active mass correlation ∈ Set.Icc lower upper := by
  constructor
  · calc
      lower = ∑ environment ∈ active, mass environment * lower := by
        rw [← Finset.sum_mul, hsum, one_mul]
      _ ≤ ∑ environment ∈ active, mass environment * correlation environment := by
        exact Finset.sum_le_sum fun environment hactive ↦
          mul_le_mul_of_nonneg_left (hcorrelation environment hactive).1
            (hmass environment hactive)
      _ = pooledEnvironmentCorrelations active mass correlation := rfl
  · calc
      pooledEnvironmentCorrelations active mass correlation =
          ∑ environment ∈ active, mass environment * correlation environment := rfl
      _ ≤ ∑ environment ∈ active, mass environment * upper := by
        exact Finset.sum_le_sum fun environment hactive ↦
          mul_le_mul_of_nonneg_left (hcorrelation environment hactive).2
            (hmass environment hactive)
      _ = upper := by rw [← Finset.sum_mul, hsum, one_mul]

/-- A strictly better component with positive mass makes the pooled correlation strictly
larger than a common lower bound. -/
theorem pooledEnvironmentCorrelations_gt
    {Environment : Type*} (active : Finset Environment)
    (mass correlation : Environment → ℝ) (lower : ℝ)
    (hmass : ∀ environment ∈ active, 0 ≤ mass environment)
    (hsum : ∑ environment ∈ active, mass environment = 1)
    (hlower : ∀ environment ∈ active, lower ≤ correlation environment)
    (witness : Environment) (hwitness : witness ∈ active)
    (hwitnessMass : 0 < mass witness)
    (hwitnessCorrelation : lower < correlation witness) :
    lower < pooledEnvironmentCorrelations active mass correlation := by
  have hstrict :
      ∑ environment ∈ active, mass environment * lower <
        ∑ environment ∈ active, mass environment * correlation environment := by
    apply Finset.sum_lt_sum
    · intro environment hactive
      exact mul_le_mul_of_nonneg_left (hlower environment hactive)
        (hmass environment hactive)
    · exact ⟨witness, hwitness,
        mul_lt_mul_of_pos_left hwitnessCorrelation hwitnessMass⟩
  calc
    lower = ∑ environment ∈ active, mass environment * lower := by
      rw [← Finset.sum_mul, hsum, one_mul]
    _ < ∑ environment ∈ active, mass environment * correlation environment := hstrict
    _ = pooledEnvironmentCorrelations active mass correlation := rfl

/-- **Same-sign, magnitude-varying environments cannot close this population gap.**  If every
positively weighted pure environment lies on the positive gapped side of the golden threshold,
then so does their pooled correlation. -/
theorem pooledEnvironmentCorrelations_golden_lt
    {Environment : Type*} (active : Finset Environment)
    (mass correlation : Environment → ℝ)
    (hmass : ∀ environment ∈ active, 0 ≤ mass environment)
    (hsum : ∑ environment ∈ active, mass environment = 1)
    (hgolden : ∀ environment ∈ active,
      goldenCorrelationThreshold < correlation environment)
    (witness : Environment) (hwitness : witness ∈ active)
    (hwitnessMass : 0 < mass witness) :
    goldenCorrelationThreshold < pooledEnvironmentCorrelations active mass correlation :=
  pooledEnvironmentCorrelations_gt active mass correlation goldenCorrelationThreshold
    hmass hsum (fun environment hactive ↦ (hgolden environment hactive).le)
    witness hwitness hwitnessMass (hgolden witness hwitness)

/-- Therefore a normalized same-sign mixture of individually gapped admissible correlations
retains a negative population gap certificate.  Magnitude heterogeneity alone cannot close the
gap in this rank-two witness family. -/
theorem pooledEnvironmentGapCertificate_neg_of_same_sign
    {Environment : Type*} (active : Finset Environment)
    (mass correlation : Environment → ℝ)
    (hmass : ∀ environment ∈ active, 0 ≤ mass environment)
    (hsum : ∑ environment ∈ active, mass environment = 1)
    (hgolden : ∀ environment ∈ active,
      goldenCorrelationThreshold < correlation environment)
    (hupper : ∀ environment ∈ active, correlation environment ≤ 1)
    (witness : Environment) (hwitness : witness ∈ active)
    (hwitnessMass : 0 < mass witness) :
    populationGapCertificate (pooledEnvironmentCorrelations active mass correlation) < 0 := by
  have hpooledGolden : goldenCorrelationThreshold <
      pooledEnvironmentCorrelations active mass correlation :=
    pooledEnvironmentCorrelations_golden_lt active mass correlation hmass hsum hgolden
      witness hwitness hwitnessMass
  have hpooledBounds := pooledEnvironmentCorrelations_mem_Icc active mass correlation
    goldenCorrelationThreshold 1 hmass hsum
      (fun environment hactive ↦ ⟨(hgolden environment hactive).le, hupper environment hactive⟩)
  have hpooledPos : 0 < pooledEnvironmentCorrelations active mass correlation :=
    goldenCorrelationThreshold_mem_Ioo.1.trans hpooledGolden
  apply populationGapCertificate_neg_of_golden_lt_abs
  · rw [abs_of_pos hpooledPos]
    exact hpooledBounds.2
  · rw [abs_of_pos hpooledPos]
    exact hpooledGolden

/-- Effective active correlation obtained by pooling arbitrary left and right environments. -/
noncomputable def pooledEnvironmentCorrelation
    (left right leftMass : ℝ) : ℝ :=
  Descent.Core.convexCombination leftMass left right

/-- Opposite-sign, equal-magnitude environments reduce to the cancellation parameter used
below. -/
theorem pooledEnvironmentCorrelation_opposite
    (rho mix : ℝ) :
    pooledEnvironmentCorrelation rho (-rho) mix = rho * (2 * mix - 1) := by
  unfold pooledEnvironmentCorrelation Descent.Core.convexCombination
  ring

/-- **Same-sign caveat.**  Pooling two equal active correlations does not change the landscape
parameter at all.  Thus the explicit gap-closing example is a sign-cancellation mechanism,
not a theorem that arbitrary ancestry heterogeneity helps. -/
@[simp] theorem pooledEnvironmentCorrelation_same
    (rho mix : ℝ) :
    pooledEnvironmentCorrelation rho rho mix = rho := by
  unfold pooledEnvironmentCorrelation Descent.Core.convexCombination
  ring

/-- Effective active correlation when the `+rho` environment has mass `mix` and the `-rho`
environment has mass `1 - mix`.

    Empirical status: VALIDATED. Battery `gap01` draws 1e5 pairs per block, 20 blocks
    per cell, from two environments with correlations `+rho` and `-rho` pooled at mass
    `mix`, and measures the realised Pearson correlation of the pooled sample. This body
    matches at 2.06 sems.

Power: the check separates this equation from the reading that counts only the positive
environment. `rho * mix` is the natural mistake here -- it is what "mass `mix` of the
`+rho` environment" sounds like -- and the battery rejects it at 473 sems, with the
positive control (pooled marginal variance, known to be 1) passing at 1.55. The margin
is the sign cancellation: at `mix = 1/2` this body is 0 and the rival is `rho/2`, so the
two cannot both survive a balanced mixture. See `mixedEnvironmentCorrelation_half`. -/
noncomputable def mixedEnvironmentCorrelation (rho mix : ℝ) : ℝ :=
  rho * (2 * mix - 1)

/-- Exact cancellation at a balanced mixture. -/
@[simp] theorem mixedEnvironmentCorrelation_half (rho : ℝ) :
    mixedEnvironmentCorrelation rho (1 / 2) = 0 := by
  unfold mixedEnvironmentCorrelation
  ring

/-- If the effective correlation lies below the golden threshold, the mixture is on the
non-gapped side of the exact population certificate. -/
theorem mixedEnvironmentGapCertificate_nonneg
    (rho mix : ℝ)
    (hmix : |mixedEnvironmentCorrelation rho mix| ≤ goldenCorrelationThreshold) :
    0 ≤ populationGapCertificate (mixedEnvironmentCorrelation rho mix) :=
  populationGapCertificate_nonneg_of_abs_le_golden _ hmix

/-- Critical minority-environment fraction for a positive pure-environment correlation. -/
noncomputable def criticalMinorityProportion (rho : ℝ) : ℝ :=
  (1 - goldenCorrelationThreshold / rho) / 2

/-- At zero correlation the threshold ratio divides by zero and Mathlib returns `0`, so the
critical minority share reads as one half.  The true reading is that no mixture closes the gap
when there is no correlation to cancel. -/
theorem criticalMinorityProportion_at_zero_correlation_is_junk :
    criticalMinorityProportion 0 = 1 / 2 := by
  norm_num [criticalMinorityProportion]

/-- **Exact maximal-correlation diversity threshold.**  When the two pure environments have
unit-magnitude opposite correlations, the minimum minority share that reaches the non-gapped
population phase is `(3 - √5) / 4`, approximately nineteen percent. -/
theorem criticalMinorityProportion_one :
    criticalMinorityProportion 1 = (3 - Real.sqrt 5) / 4 := by
  unfold criticalMinorityProportion goldenCorrelationThreshold
  ring

/-- For positive correlation, the critical minority share is the lower endpoint
`(rho - rho_c) / (2 rho)` of the exact gap-closing interval. -/
theorem criticalMinorityProportion_eq_ratio
    (rho : ℝ) (hrho : 0 < rho) :
    criticalMinorityProportion rho =
      (rho - goldenCorrelationThreshold) / (2 * rho) := by
  unfold criticalMinorityProportion
  field_simp [hrho.ne']

/-- The symmetric upper endpoint is `(rho + rho_c) / (2 rho)`. -/
theorem one_sub_criticalMinorityProportion_eq_ratio
    (rho : ℝ) (hrho : 0 < rho) :
    1 - criticalMinorityProportion rho =
      (rho + goldenCorrelationThreshold) / (2 * rho) := by
  unfold criticalMinorityProportion
  field_simp [hrho.ne']
  ring

/-- **Exact cancellation interval.**  For a positive pure-environment correlation, the pooled
correlation lies on the non-gapped side exactly when the positive-environment mass lies between
the two critical proportions. -/
theorem mixedEnvironmentCorrelation_abs_le_golden_iff
    (rho mix : ℝ) (hrho : 0 < rho) :
    |mixedEnvironmentCorrelation rho mix| ≤ goldenCorrelationThreshold ↔
      criticalMinorityProportion rho ≤ mix ∧
        mix ≤ 1 - criticalMinorityProportion rho := by
  rw [one_sub_criticalMinorityProportion_eq_ratio rho hrho,
    criticalMinorityProportion_eq_ratio rho hrho, abs_le]
  have htwoRho : 0 < 2 * rho := mul_pos (by norm_num) hrho
  constructor
  · rintro ⟨hlower, hupper⟩
    constructor
    · apply (div_le_iff₀ htwoRho).2
      unfold mixedEnvironmentCorrelation at hlower
      nlinarith
    · apply (le_div_iff₀ htwoRho).2
      unfold mixedEnvironmentCorrelation at hupper
      nlinarith
  · rintro ⟨hlower, hupper⟩
    have hlower' := (div_le_iff₀ htwoRho).1 hlower
    have hupper' := (le_div_iff₀ htwoRho).1 hupper
    unfold mixedEnvironmentCorrelation
    constructor <;> nlinarith


/-- At the critical minority fraction, the effective correlation is exactly the golden
threshold. -/
theorem mixedEnvironmentCorrelation_at_criticalMinority
    (rho : ℝ) (hrho : rho ≠ 0) :
    mixedEnvironmentCorrelation rho (1 - criticalMinorityProportion rho) =
      goldenCorrelationThreshold := by
  unfold mixedEnvironmentCorrelation criticalMinorityProportion
  field_simp [hrho]
  ring

/-- Consequently the exact gap certificate vanishes at the computed mixing proportion. -/
theorem mixedEnvironmentGapCertificate_at_criticalMinority
    (rho : ℝ) (hrho : rho ≠ 0) :
    populationGapCertificate
        (mixedEnvironmentCorrelation rho (1 - criticalMinorityProportion rho)) = 0 := by
  rw [mixedEnvironmentCorrelation_at_criticalMinority rho hrho]
  exact populationGapCertificate_goldenCorrelationThreshold

/-- Any minority fraction between the critical value and one half closes the population
certificate, provided each pure environment is itself inside the correlation interval. -/
theorem mixedEnvironmentGapCertificate_nonneg_of_minority_ge_critical
    (rho minority : ℝ)
    (hrhoGolden : goldenCorrelationThreshold < rho)
    (hminority : criticalMinorityProportion rho ≤ minority)
    (hminorityHalf : minority ≤ 1 / 2) :
    0 ≤ populationGapCertificate
      (mixedEnvironmentCorrelation rho (1 - minority)) := by
  have hrho : 0 < rho := lt_trans goldenCorrelationThreshold_mem_Ioo.1 hrhoGolden
  have heffectiveNonneg : 0 ≤ mixedEnvironmentCorrelation rho (1 - minority) := by
    unfold mixedEnvironmentCorrelation
    exact mul_nonneg hrho.le (by linarith)
  have heffectiveLe :
      mixedEnvironmentCorrelation rho (1 - minority) ≤ goldenCorrelationThreshold := by
    have hcritical := mixedEnvironmentCorrelation_at_criticalMinority rho hrho.ne'
    unfold mixedEnvironmentCorrelation at hcritical ⊢
    nlinarith
  apply populationGapCertificate_nonneg_of_abs_le_golden
  rw [abs_of_nonneg heffectiveNonneg]
  exact heffectiveLe

/-- **Complete two-environment population phase diagram.**  Inside the biological mixture and
correlation ranges, the population gap certificate is nonnegative exactly on the symmetric
critical interval.  Outside that interval each pure-sign side has a strictly negative
certificate. -/
theorem mixedEnvironmentGapCertificate_nonneg_iff
    (rho mix : ℝ) (hrho : 0 < rho) (hrhoUpper : rho ≤ 1)
    (hmix : mix ∈ Set.Icc (0 : ℝ) 1) :
    0 ≤ populationGapCertificate (mixedEnvironmentCorrelation rho mix) ↔
      criticalMinorityProportion rho ≤ mix ∧
        mix ≤ 1 - criticalMinorityProportion rho := by
  rw [← mixedEnvironmentCorrelation_abs_le_golden_iff rho mix hrho]
  constructor
  · intro hcertificate
    have hcentered : |2 * mix - 1| ≤ 1 := by
      rw [abs_le]
      constructor <;> linarith [hmix.1, hmix.2]
    have heffectiveBound : |mixedEnvironmentCorrelation rho mix| ≤ 1 := by
      rw [mixedEnvironmentCorrelation, abs_mul, abs_of_pos hrho]
      calc
        rho * |2 * mix - 1| ≤ rho * 1 :=
          mul_le_mul_of_nonneg_left hcentered hrho.le
        _ ≤ 1 := by simpa using hrhoUpper
    by_contra houtside
    have hgolden : goldenCorrelationThreshold <
        |mixedEnvironmentCorrelation rho mix| := lt_of_not_ge houtside
    have hnegative := populationGapCertificate_neg_of_golden_lt_abs
      (mixedEnvironmentCorrelation rho mix) heffectiveBound hgolden
    linarith
  · exact mixedEnvironmentGapCertificate_nonneg rho mix

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

/-- Vanishing identity: a candidate at the truth carries no displacement energy. -/
theorem covarianceDisplacementEnergy_self_eq_zero
    (sigma : Matrix (Fin 2) (Fin 2) ℝ) (truth : TwoCoordinateConfiguration) :
    covarianceDisplacementEnergy sigma truth truth = 0 := by
  unfold covarianceDisplacementEnergy
  simp


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

end Descent.Blindness
