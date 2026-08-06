/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Blindness.TrafficInvariantSeparation.InvariantSeparation
import Descent.Layer

assert_below Descent.Conditionals Descent.Portability Descent.Decision Descent.Program

namespace Descent.Blindness
namespace TrafficInvariantSeparation

open scoped Matrix Topology

/-!
# `TrafficInvariantSeparation.ExponentialProfileCompactness`

Part of the split of `Descent/Blindness/TrafficInvariantSeparation.lean`, which was 6,618 lines.

The parts are a FAN: each imports the parts that declare the symbols it names, and nothing
else. The split first made them a CHAIN -- each importing the one before, in the order the
original text ran -- which preserved every resolution the single file had and charged every
part a dependency on everything written above it, used or not. Recovering the real order is
the work that chain deferred: each part's identifiers were resolved against its siblings'
declarations, and the imports above are the answer, so what a part rests on is readable
from its header instead of inherited from its position in a file that no longer exists.

Where a cut falls inside a section, the section is reopened and reclosed by name. A section
scopes `variable`s and this file declares none at that level, so the reopening is exact.
-/


section ExponentialProfileCompactness

/-! ### Countable LD/right-convergence compactification

The nonperturbative profile is a countable collection of normalized pressure
coordinates.  Uniform operator and support bounds place every coordinate in a
fixed compact interval.  The product below is therefore the exact compact
state space behind the diagonal-subsequence argument; unlike a prose appeal to
"diagonalization", the theorem returns one common subsequence on which every
coordinate converges.
-/

/-- **Quantitative dense-parameter control for pressure profiles.**  If a set
of enumerated parameters is a `radius`-net, two uniformly `K`-Lipschitz
profiles that differ there by at most `coordinateError` differ everywhere by
at most `2 K radius + coordinateError`.  This is the finite-resolution theorem
behind extending rational tilt coordinates to all tilts. -/
theorem lipschitzPressureProfiles_dist_le_of_net
    {Parameter : Type*} [PseudoMetricSpace Parameter]
    (K : NNReal) (left right : Parameter → ℝ)
    (hleft : LipschitzWith K left) (hright : LipschitzWith K right)
    (net : Set Parameter) (radius coordinateError : ℝ)
    (hnet : ∀ parameter, ∃ representative ∈ net,
      dist parameter representative ≤ radius)
    (hagrees : ∀ representative ∈ net,
      dist (left representative) (right representative) ≤ coordinateError) :
    ∀ parameter,
      dist (left parameter) (right parameter) ≤
        2 * (K : ℝ) * radius + coordinateError := by
  intro parameter
  obtain ⟨representative, hrepresentative, hdistance⟩ := hnet parameter
  have hleftBound :
      dist (left parameter) (left representative) ≤ (K : ℝ) * radius :=
    hleft.dist_le_mul_of_le hdistance
  have hrightBound :
      dist (right representative) (right parameter) ≤ (K : ℝ) * radius := by
    apply hright.dist_le_mul_of_le
    simpa [dist_comm] using hdistance
  have hmiddle := hagrees representative hrepresentative
  calc
    dist (left parameter) (right parameter) ≤
        dist (left parameter) (left representative) +
          dist (left representative) (right parameter) :=
      dist_triangle _ _ _
    _ ≤ dist (left parameter) (left representative) +
        (dist (left representative) (right representative) +
          dist (right representative) (right parameter)) := by
      gcongr
      exact dist_triangle _ _ _
    _ ≤ 2 * (K : ℝ) * radius + coordinateError := by
      linarith

/-- **Dense rational pressure coordinates determine the full Lipschitz
profile uniquely.**  This is the zero-resolution limit of the preceding net
bound and is the exact uniqueness statement used by the countable
right-convergence compactification. -/
theorem lipschitzPressureProfiles_eq_of_eqOn_dense
    {Parameter : Type*} [PseudoMetricSpace Parameter]
    (K : NNReal) (left right : Parameter → ℝ)
    (hleft : LipschitzWith K left) (hright : LipschitzWith K right)
    (parameters : Set Parameter) (hdense : Dense parameters)
    (hagrees : Set.EqOn left right parameters) :
    left = right :=
  Continuous.ext_on hdense hleft.continuous hright.continuous hagrees

/-- **Dense rational convergence extends to every tilt.**  A sequence of
uniformly `K`-Lipschitz pressure profiles that converges pointwise on a dense
parameter family to a `K`-Lipschitz limit converges pointwise everywhere.  The
proof uses one nearby dense parameter and a three-term metric bound, so no
unproved Arzelà--Ascoli step is hidden. -/
theorem lipschitzPressureProfiles_tendsto_of_tendstoOn_dense
    {Parameter : Type*} [PseudoMetricSpace Parameter]
    (K : NNReal) (profiles : ℕ → Parameter → ℝ) (limit : Parameter → ℝ)
    (hprofiles : ∀ index, LipschitzWith K (profiles index))
    (hlimit : LipschitzWith K limit)
    (parameters : Set Parameter) (hdense : Dense parameters)
    (hconverges : ∀ parameter ∈ parameters,
      Filter.Tendsto (fun index ↦ profiles index parameter)
        Filter.atTop (nhds (limit parameter))) :
    ∀ parameter,
      Filter.Tendsto (fun index ↦ profiles index parameter)
        Filter.atTop (nhds (limit parameter)) := by
  intro parameter
  rw [Metric.tendsto_nhds]
  intro epsilon hepsilon
  have hscale : 0 < 3 * ((K : ℝ) + 1) := by positivity
  obtain ⟨representative, hrepresentative, hdistance⟩ :=
    hdense.exists_dist_lt parameter (div_pos hepsilon hscale)
  have hlocal : (K : ℝ) * dist parameter representative < epsilon / 3 := by
    calc
      (K : ℝ) * dist parameter representative ≤
          ((K : ℝ) + 1) * dist parameter representative := by
        exact mul_le_mul_of_nonneg_right (by linarith) dist_nonneg
      _ < ((K : ℝ) + 1) * (epsilon / (3 * ((K : ℝ) + 1))) :=
        mul_lt_mul_of_pos_left hdistance (by positivity)
      _ = epsilon / 3 := by
        field_simp
  have hmiddle := (Metric.tendsto_nhds.mp
    (hconverges representative hrepresentative)) (epsilon / 3) (by positivity)
  filter_upwards [hmiddle] with index hmiddleIndex
  have hleftLocal :
      dist (profiles index parameter) (profiles index representative) < epsilon / 3 :=
    (hprofiles index).dist_le_mul parameter representative |>.trans_lt hlocal
  have hrightLocal :
      dist (limit representative) (limit parameter) < epsilon / 3 := by
    have := hlimit.dist_le_mul representative parameter
    rw [dist_comm representative parameter] at this
    exact this.trans_lt hlocal
  calc
    dist (profiles index parameter) (limit parameter) ≤
        dist (profiles index parameter) (profiles index representative) +
          dist (profiles index representative) (limit parameter) :=
      dist_triangle _ _ _
    _ ≤ dist (profiles index parameter) (profiles index representative) +
        (dist (profiles index representative) (limit representative) +
          dist (limit representative) (limit parameter)) := by
      gcongr
      exact dist_triangle _ _ _
    _ < epsilon := by linarith

/-- **Compact tilt domains upgrade dense convergence to uniform convergence.**
Uniform `K`-Lipschitz control supplies equicontinuity; compactness supplies a
finite radius net; convergence at its finitely many points supplies one common
index.  The resulting conclusion is `TendstoUniformly`, not merely pointwise
convergence at each tilt. -/
theorem lipschitzPressureProfiles_tendstoUniformly_of_tendstoOn_dense
    {Parameter : Type*} [PseudoMetricSpace Parameter] [CompactSpace Parameter]
    (K : NNReal) (profiles : ℕ → Parameter → ℝ) (limit : Parameter → ℝ)
    (hprofiles : ∀ index, LipschitzWith K (profiles index))
    (hlimit : LipschitzWith K limit)
    (parameters : Set Parameter) (hdense : Dense parameters)
    (hconverges : ∀ parameter ∈ parameters,
      Filter.Tendsto (fun index ↦ profiles index parameter)
        Filter.atTop (nhds (limit parameter))) :
    TendstoUniformly profiles limit Filter.atTop := by
  have hpointwise := lipschitzPressureProfiles_tendsto_of_tendstoOn_dense
    K profiles limit hprofiles hlimit parameters hdense hconverges
  rw [Metric.tendstoUniformly_iff]
  intro epsilon hepsilon
  let radius : ℝ := epsilon / (6 * ((K : ℝ) + 1))
  have hradius : 0 < radius := by
    dsimp [radius]
    positivity
  have htotallyBounded : TotallyBounded (Set.univ : Set Parameter) :=
    CompactSpace.isCompact_univ.totallyBounded
  obtain ⟨net, _hnetUniv, hnetFinite, hcover⟩ :=
    Metric.finite_approx_of_totallyBounded htotallyBounded radius hradius
  have heventually : ∀ᶠ index in Filter.atTop,
      ∀ representative ∈ hnetFinite.toFinset,
        dist (profiles index representative) (limit representative) < epsilon / 3 := by
    rw [Finset.eventually_all]
    intro representative _hrepresentative
    exact (Metric.tendsto_nhds.mp (hpointwise representative))
      (epsilon / 3) (by positivity)
  filter_upwards [heventually] with index hindex
  intro parameter
  have hnetApprox : ∀ candidate, ∃ representative ∈ net,
      dist candidate representative ≤ radius := by
    intro candidate
    have hcandidate := hcover (Set.mem_univ candidate)
    simp only [Set.mem_iUnion, Metric.mem_ball] at hcandidate
    obtain ⟨nearby, hnearby, hnearbyDistance⟩ := hcandidate
    exact ⟨nearby, hnearby, hnearbyDistance.le⟩
  have hagrees : ∀ candidate ∈ net,
      dist (profiles index candidate) (limit candidate) ≤ epsilon / 3 := by
    intro candidate hcandidate
    exact (hindex candidate (hnetFinite.mem_toFinset.mpr hcandidate)).le
  have hbound := lipschitzPressureProfiles_dist_le_of_net
    K (profiles index) limit (hprofiles index) hlimit net radius (epsilon / 3)
      hnetApprox hagrees parameter
  have hradiusNonneg : 0 ≤ radius := hradius.le
  have hspatial : 2 * (K : ℝ) * radius ≤ epsilon / 3 := by
    calc
      2 * (K : ℝ) * radius ≤ 2 * ((K : ℝ) + 1) * radius := by
        gcongr
        linarith
      _ = epsilon / 3 := by
        dsimp [radius]
        field_simp
        norm_num
  rw [dist_comm]
  exact hbound.trans_lt (by linarith)

/-- Bounded continuous pressure functions with one common Lipschitz constant
and one common range interval.  This is the functional, rather than merely
coordinatewise, right-profile family used by Arzelà--Ascoli. -/
def boundedLipschitzPressureFamily
    {Parameter : Type*} [PseudoMetricSpace Parameter]
    (K : NNReal) (bound : ℝ) :
    Set (BoundedContinuousFunction Parameter ℝ) :=
  {profile | LipschitzWith K profile ∧
    ∀ parameter, profile parameter ∈ Set.Icc (-bound) bound}

/-- The bounded common-Lipschitz pressure family is closed in the uniform
metric on bounded continuous functions. -/
theorem isClosed_boundedLipschitzPressureFamily
    {Parameter : Type*} [PseudoMetricSpace Parameter]
    (K : NNReal) (bound : ℝ) :
    IsClosed (boundedLipschitzPressureFamily (Parameter := Parameter) K bound) := by
  rw [show boundedLipschitzPressureFamily (Parameter := Parameter) K bound =
      {profile | ∀ x y,
        dist (profile x) (profile y) ≤ (K : ℝ) * dist x y} ∩
      {profile | ∀ x, profile x ∈ Set.Icc (-bound) bound} by
    ext profile
    simp only [boundedLipschitzPressureFamily, Set.mem_setOf_eq, Set.mem_inter_iff]
    rw [lipschitzWith_iff_dist_le_mul]]
  apply IsClosed.inter
  · simp only [Set.setOf_forall]
    exact isClosed_iInter fun x ↦ isClosed_iInter fun y ↦
      isClosed_le
        (BoundedContinuousFunction.continuous_eval_const.dist
          BoundedContinuousFunction.continuous_eval_const)
        continuous_const
  · simp only [Set.setOf_forall]
    exact isClosed_iInter fun x ↦
      isClosed_Icc.preimage BoundedContinuousFunction.continuous_eval_const

/-- **Functional right-profile compactness (Arzelà--Ascoli).**  On a compact
tilt domain, uniformly bounded pressure functions sharing one Lipschitz
constant form a compact set in the uniform metric. -/
theorem isCompact_boundedLipschitzPressureFamily
    {Parameter : Type*} [PseudoMetricSpace Parameter] [CompactSpace Parameter]
    (K : NNReal) (bound : ℝ) :
    IsCompact (boundedLipschitzPressureFamily (Parameter := Parameter) K bound) := by
  let family := boundedLipschitzPressureFamily (Parameter := Parameter) K bound
  have hclosed : IsClosed family := isClosed_boundedLipschitzPressureFamily K bound
  have hrange : ∀ (profile : BoundedContinuousFunction Parameter ℝ)
      (parameter : Parameter),
      profile ∈ family → profile parameter ∈ Set.Icc (-bound) bound := by
    intro profile parameter hprofile
    exact hprofile.2 parameter
  have hequicontinuous : Equicontinuous ((↑) : family → Parameter → ℝ) := by
    exact (LipschitzWith.uniformEquicontinuous
      ((↑) : family → Parameter → ℝ) K
      (fun profile ↦ profile.property.1)).equicontinuous
  have hclosure := BoundedContinuousFunction.arzela_ascoli
    (Set.Icc (-bound) bound) isCompact_Icc family hrange hequicontinuous
  simpa [hclosed.closure_eq] using hclosure

/-- Every bounded equi-Lipschitz pressure sequence on a compact tilt domain
has a uniformly convergent subsequence whose limit remains in the same family. -/
theorem boundedLipschitzPressureFamily_tendsto_subseq
    {Parameter : Type*} [PseudoMetricSpace Parameter] [CompactSpace Parameter]
    (K : NNReal) (bound : ℝ)
    (profiles : ℕ → BoundedContinuousFunction Parameter ℝ)
    (hprofiles : ∀ index,
      profiles index ∈ boundedLipschitzPressureFamily K bound) :
    ∃ limit ∈ boundedLipschitzPressureFamily (Parameter := Parameter) K bound,
      ∃ subsequence : ℕ → ℕ,
        StrictMono subsequence ∧
          Filter.Tendsto (profiles ∘ subsequence) Filter.atTop (nhds limit) :=
  (isCompact_boundedLipschitzPressureFamily K bound).tendsto_subseq hprofiles

/-- A bounded countable exponential/LD profile.  Coordinate `j` packages one
choice of prior, replica number, and rational tilt from the fixed countable
dense family. -/
abbrev BoundedExponentialProfile (bound : ℝ) :=
  ℕ → Set.Icc (-bound) bound

/-- A dedicated carrier for the explicit exponential/right-profile metric.
It is definitionally the same bounded coordinate family, but unlike the raw
function type it receives the weighted product metric rather than an unrelated
function-space metric instance. -/
def ExponentialProfilePoint (bound : ℝ) := BoundedExponentialProfile bound

/-- Mathlib's metric on a countable product of metric spaces, transported to
the dedicated profile carrier:

    dist x y = ∑' j, min (2⁻ʲ) (dist (x j) (y j)).

`PiCountable.metricSpace` fixes `toUniformSpace := Pi.uniformSpace _`, so this
distance carries the product uniformity *by construction* rather than by a
separate argument.  That is what makes distance convergence and simultaneous
coordinate convergence the same statement below, and it is why this file no
longer carries its own capped-coordinate metric: the whole construction, and
the Tannery/coercivity argument that it induces the product topology, is
`Mathlib.Topology.MetricSpace.PiNat`.

The earlier bespoke formula was `∑' j, 2⁻ʲ · min 1 |x j - y j|`.  Mathlib's
caps the weight rather than the discrepancy; both are separating, both have
total mass two, and both metrize the product topology, so every downstream
statement is unchanged. -/
noncomputable instance exponentialProfilePointMetricSpace (bound : ℝ) :
    MetricSpace (ExponentialProfilePoint bound) :=
  PiCountable.metricSpace

/-- The explicit weighted distance on the countable exponential/LD profile.

Convention: the index is the enumeration position of a prior/replica/tilt
coordinate, not a biological locus. -/
noncomputable def exponentialProfileDistance
    {bound : ℝ} (left right : BoundedExponentialProfile bound) : ℝ :=
  dist (show ExponentialProfilePoint bound from left)
    (show ExponentialProfilePoint bound from right)

/-- Distance in the bundled right-profile metric is exactly the weighted
capped-coordinate formula, not merely topologically equivalent to it. -/
@[simp] theorem exponentialProfilePoint_dist_eq
    {bound : ℝ} (left right : ExponentialProfilePoint bound) :
    dist left right = exponentialProfileDistance left right := rfl

/-- The explicit series form of the profile distance.  `Encodable.encode` on
`ℕ` is the identity, so the weight at coordinate `j` is exactly `2⁻ʲ`. -/
theorem exponentialProfileDistance_eq_tsum
    {bound : ℝ} (left right : BoundedExponentialProfile bound) :
    exponentialProfileDistance left right =
      ∑' coordinate : ℕ,
        min ((1 / 2 : ℝ) ^ coordinate)
          (dist (left coordinate) (right coordinate)) :=
  PiCountable.dist_eq_tsum (F := fun _ : ℕ ↦ Set.Icc (-bound) bound) left right

theorem exponentialProfileDistance_summable
    {bound : ℝ} (left right : BoundedExponentialProfile bound) :
    Summable (fun coordinate : ℕ ↦
      min ((1 / 2 : ℝ) ^ coordinate)
        (dist (left coordinate) (right coordinate))) :=
  PiCountable.dist_summable (F := fun _ : ℕ ↦ Set.Icc (-bound) bound) left right

theorem exponentialProfileDistance_nonneg
    {bound : ℝ} (left right : BoundedExponentialProfile bound) :
    0 ≤ exponentialProfileDistance left right :=
  dist_nonneg

@[simp] theorem exponentialProfileDistance_self
    {bound : ℝ} (profile : BoundedExponentialProfile bound) :
    exponentialProfileDistance profile profile = 0 :=
  dist_self (show ExponentialProfilePoint bound from profile)

theorem exponentialProfileDistance_comm
    {bound : ℝ} (left right : BoundedExponentialProfile bound) :
    exponentialProfileDistance left right = exponentialProfileDistance right left :=
  dist_comm (show ExponentialProfilePoint bound from left)
    (show ExponentialProfilePoint bound from right)

theorem exponentialProfileDistance_triangle
    {bound : ℝ} (left middle right : BoundedExponentialProfile bound) :
    exponentialProfileDistance left right ≤
      exponentialProfileDistance left middle + exponentialProfileDistance middle right :=
  dist_triangle (show ExponentialProfilePoint bound from left)
    (show ExponentialProfilePoint bound from middle)
    (show ExponentialProfilePoint bound from right)

theorem exponentialProfileDistance_eq_zero_iff
    {bound : ℝ} (left right : BoundedExponentialProfile bound) :
    exponentialProfileDistance left right = 0 ↔ left = right :=
  dist_eq_zero (x := show ExponentialProfilePoint bound from left)
    (y := show ExponentialProfilePoint bound from right)

/-- The explicit right-profile metric has uniform diameter at most two.  The
constant is exact for the zero-based weights `2⁻ʲ`: their total mass is two,
and every coordinate term is capped by its weight. -/
theorem exponentialProfileDistance_le_two
    {bound : ℝ} (left right : BoundedExponentialProfile bound) :
    exponentialProfileDistance left right ≤ 2 := by
  rw [exponentialProfileDistance_eq_tsum]
  calc
    ∑' coordinate : ℕ,
        min ((1 / 2 : ℝ) ^ coordinate)
          (dist (left coordinate) (right coordinate)) ≤
        ∑' coordinate : ℕ, (1 / 2 : ℝ) ^ coordinate :=
      (exponentialProfileDistance_summable left right).tsum_le_tsum
        (fun _ ↦ min_le_left _ _) summable_geometric_two
    _ = 2 := tsum_geometric_two

/-- Agreement on the first `prefixLength` pressure coordinates controls the
entire nonperturbative profile with the exact remaining geometric tail.  This
is the quantitative finite-coordinate approximation property behind the
countable right-convergence compactification. -/
theorem exponentialProfileDistance_le_geometricTail_of_prefix_eq
    {bound : ℝ} (left right : BoundedExponentialProfile bound)
    (prefixLength : ℕ)
    (hprefix : ∀ coordinate < prefixLength, left coordinate = right coordinate) :
    exponentialProfileDistance left right ≤
      2 * (1 / 2 : ℝ) ^ prefixLength := by
  have hsummable := exponentialProfileDistance_summable left right
  have hprefixSum :
      ∑ coordinate ∈ Finset.range prefixLength,
        min ((1 / 2 : ℝ) ^ coordinate)
          (dist (left coordinate) (right coordinate)) = 0 := by
    refine Finset.sum_eq_zero fun coordinate hcoordinate ↦ ?_
    rw [hprefix coordinate (Finset.mem_range.mp hcoordinate), dist_self]
    exact min_eq_right (by positivity)
  have hsplit := hsummable.sum_add_tsum_nat_add prefixLength
  rw [hprefixSum, zero_add] at hsplit
  rw [exponentialProfileDistance_eq_tsum, ← hsplit]
  calc
    ∑' coordinate : ℕ,
        min ((1 / 2 : ℝ) ^ (coordinate + prefixLength))
          (dist (left (coordinate + prefixLength))
            (right (coordinate + prefixLength))) ≤
        ∑' coordinate : ℕ, (1 / 2 : ℝ) ^ (coordinate + prefixLength) :=
      ((summable_nat_add_iff prefixLength).mpr hsummable).tsum_le_tsum
        (fun _ ↦ min_le_left _ _)
        ((summable_nat_add_iff prefixLength).mpr summable_geometric_two)
    _ = 2 * (1 / 2 : ℝ) ^ prefixLength := by
      simp_rw [pow_add]
      rw [tsum_mul_right, tsum_geometric_two]

/-- Every coordinate discrepancy is controlled by the complete weighted
profile distance.  This is the coercive half of the metric construction: no
fixed pressure coordinate can move without paying its strictly positive
geometric weight in the global distance. -/
theorem exponentialProfileDistance_coordinateTerm_le
    {bound : ℝ} (left right : BoundedExponentialProfile bound)
    (coordinate : ℕ) :
    min ((1 / 2 : ℝ) ^ coordinate)
        (dist (left coordinate) (right coordinate)) ≤
      exponentialProfileDistance left right :=
  PiCountable.min_dist_le_dist_pi (F := fun _ : ℕ ↦ Set.Icc (-bound) bound)
    left right coordinate

/-- **Compactness of the countable exponential profile.**  Every sequence of
bounded profiles has one strictly increasing subsequence converging in the
product topology.  Product convergence is exactly coordinatewise convergence,
so the same subsequence works for every enumerated pressure coordinate. -/
theorem boundedExponentialProfile_compact_subsequence
    (bound : ℝ) (profiles : ℕ → BoundedExponentialProfile bound) :
    ∃ limit : BoundedExponentialProfile bound, ∃ subsequence : ℕ → ℕ,
      StrictMono subsequence ∧
        Filter.Tendsto (profiles ∘ subsequence) Filter.atTop (nhds limit) :=
  CompactSpace.tendsto_subseq profiles

/-- Product convergence of bounded exponential profiles gives convergence of
every individual pressure coordinate along the same subsequence. -/
theorem boundedExponentialProfile_coordinatewise
    {bound : ℝ} {profiles : ℕ → BoundedExponentialProfile bound}
    {limit : BoundedExponentialProfile bound} {subsequence : ℕ → ℕ}
    (hprofiles :
      Filter.Tendsto (profiles ∘ subsequence) Filter.atTop (nhds limit)) :
    ∀ coordinate : ℕ,
      Filter.Tendsto (fun n ↦ profiles (subsequence n) coordinate)
        Filter.atTop (nhds (limit coordinate)) :=
  fun coordinate ↦ (tendsto_pi_nhds.mp hprofiles) coordinate

theorem boundedExponentialProfile_common_coordinatewise_subsequence
    (bound : ℝ) (profiles : ℕ → BoundedExponentialProfile bound) :
    ∃ limit : BoundedExponentialProfile bound, ∃ subsequence : ℕ → ℕ,
      StrictMono subsequence ∧
        ∀ coordinate : ℕ,
          Filter.Tendsto (fun n ↦ profiles (subsequence n) coordinate)
            Filter.atTop (nhds (limit coordinate)) := by
  obtain ⟨limit, subsequence, hmono, hprofiles⟩ :=
    boundedExponentialProfile_compact_subsequence bound profiles
  exact ⟨limit, subsequence, hmono,
    boundedExponentialProfile_coordinatewise hprofiles⟩

/-- Standard convergence in the bundled right-profile metric is equivalent to
simultaneous convergence of every enumerated pressure coordinate.  This is
immediate from `PiCountable.metricSpace` carrying the product uniformity; the
former hand-rolled Tannery argument and its coercive converse are gone. -/
theorem exponentialProfilePoint_tendsto_iff_coordinatewise
    {bound : ℝ} {profiles : ℕ → ExponentialProfilePoint bound}
    {limit : ExponentialProfilePoint bound} :
    Filter.Tendsto profiles Filter.atTop (nhds limit) ↔
      ∀ coordinate : ℕ,
        Filter.Tendsto (fun n ↦ profiles n coordinate)
          Filter.atTop (nhds (limit coordinate)) :=
  tendsto_pi_nhds

/-- **Exact sequential characterization of the right-profile metric.**
Weighted-distance convergence is equivalent to simultaneous convergence of
all enumerated prior/replica/tilt pressure coordinates. -/
theorem exponentialProfileDistance_tendsto_zero_iff_coordinatewise
    {bound : ℝ} {profiles : ℕ → BoundedExponentialProfile bound}
    {limit : BoundedExponentialProfile bound} :
    Filter.Tendsto (fun n ↦ exponentialProfileDistance (profiles n) limit)
        Filter.atTop (nhds 0) ↔
      ∀ coordinate : ℕ,
        Filter.Tendsto (fun n ↦ profiles n coordinate)
          Filter.atTop (nhds (limit coordinate)) :=
  (tendsto_iff_dist_tendsto_zero
      (f := fun n ↦ show ExponentialProfilePoint bound from profiles n)
      (a := show ExponentialProfilePoint bound from limit)).symm.trans
    exponentialProfilePoint_tendsto_iff_coordinatewise

theorem exponentialProfileDistance_tendsto_zero_of_coordinatewise
    {bound : ℝ} {profiles : ℕ → BoundedExponentialProfile bound}
    {limit : BoundedExponentialProfile bound}
    (hcoordinate : ∀ coordinate : ℕ,
      Filter.Tendsto (fun n ↦ profiles n coordinate)
        Filter.atTop (nhds (limit coordinate))) :
    Filter.Tendsto (fun n ↦ exponentialProfileDistance (profiles n) limit)
      Filter.atTop (nhds 0) :=
  exponentialProfileDistance_tendsto_zero_iff_coordinatewise.mpr hcoordinate

theorem exponentialProfileDistance_coordinatewise_of_tendsto_zero
    {bound : ℝ} {profiles : ℕ → BoundedExponentialProfile bound}
    {limit : BoundedExponentialProfile bound}
    (hdistance :
      Filter.Tendsto (fun n ↦ exponentialProfileDistance (profiles n) limit)
        Filter.atTop (nhds 0)) :
    ∀ coordinate : ℕ,
      Filter.Tendsto (fun n ↦ profiles n coordinate)
        Filter.atTop (nhds (limit coordinate)) :=
  exponentialProfileDistance_tendsto_zero_iff_coordinatewise.mp hdistance

/-- **Sequential compactness in the explicit distance.**  Every bounded
profile sequence has one common subsequence whose weighted exponential-profile
distance to a limiting profile tends to zero. -/
theorem boundedExponentialProfile_compact_subsequence_in_distance
    (bound : ℝ) (profiles : ℕ → BoundedExponentialProfile bound) :
    ∃ limit : BoundedExponentialProfile bound, ∃ subsequence : ℕ → ℕ,
      StrictMono subsequence ∧
        Filter.Tendsto
          (fun n ↦ exponentialProfileDistance (profiles (subsequence n)) limit)
          Filter.atTop (nhds 0) := by
  obtain ⟨limit, subsequence, hmono, hcoordinate⟩ :=
    boundedExponentialProfile_common_coordinatewise_subsequence bound profiles
  exact ⟨limit, subsequence, hmono,
    exponentialProfileDistance_tendsto_zero_of_coordinatewise hcoordinate⟩

/-- The bounded explicit right-profile metric space is compact in Mathlib's
ordinary topological sense, not only sequentially compact in a bespoke
statement. -/
instance exponentialProfilePointCompactSpace (bound : ℝ) :
    CompactSpace (ExponentialProfilePoint bound) :=
  Pi.compactSpace

/-- Every sequence in the bundled explicit metric has a conventionally
convergent subsequence. -/
theorem exponentialProfilePoint_isSeqCompact_univ (bound : ℝ) :
    IsSeqCompact (Set.univ : Set (ExponentialProfilePoint bound)) :=
  isCompact_univ.isSeqCompact

end ExponentialProfileCompactness

end TrafficInvariantSeparation
end Descent.Blindness
