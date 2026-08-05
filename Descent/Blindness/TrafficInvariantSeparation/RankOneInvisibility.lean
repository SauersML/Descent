/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Real.StarOrdered
import Mathlib.Logic.Equiv.Fintype
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Topology.Sequences
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Topology.MetricSpace.PiNat
import Mathlib.Topology.MetricSpace.UniformConvergence
import Mathlib.Topology.Order.LeftRight
import Mathlib.Tactic
import Descent.Blindness.ObservationalCeiling
import Descent.Blindness.TrafficInvariantSeparation.InvariantSeparation

namespace Descent.Blindness
namespace TrafficInvariantSeparation

open scoped Matrix Topology

/-!
# `TrafficInvariantSeparation.RankOneInvisibility`

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


section RankOneInvisibility

/-- **The rank-one spike's normalised graph sum, bounded.**

    For a balanced sign vector scaled by `p^(-1/2)`, a connected test graph with every vertex degree even contributes `p ^ (|V| - |E| - 1)`. Such a graph has
    `|E| ≥ |V|`, so the exponent is at most `-1`.

    The graph-theoretic input is the hypothesis `hev : v ≤ e`; what is proved is
    that it forces the bound. Odd-degree graphs contribute zero by balancedness
    and need no bound. -/
theorem rankOneGraphSum_le_inv
    (p : ℝ) (v e : ℕ) (hp : 1 ≤ p) (hev : v ≤ e) :
    p ^ v / p ^ (e + 1) ≤ 1 / p := by
  have hp0 : (0 : ℝ) < p := lt_of_lt_of_le zero_lt_one hp
  have hmono : p ^ v ≤ p ^ e := pow_le_pow_right₀ hp hev
  have hpe : (0 : ℝ) < p ^ e := pow_pos hp0 e
  rw [pow_succ, div_le_div_iff₀ (by positivity) hp0]
  calc p ^ v * p = p ^ v * p := rfl
    _ ≤ p ^ e * p := by nlinarith [hpe]
    _ = 1 * (p ^ e * p) := by ring

/-- **The graph-count input follows from handshaking.**  A finite contracted
graph in which every surviving vertex has degree at least two and whose degree
sum is twice its edge count satisfies `|V| ≤ |E|`.  Connected all-even graphs
with a nonempty edge set supply the minimum-degree premise automatically. -/
theorem vertices_le_edges_of_minDegree_two_of_handshake
    {Vertex : Type*} [Fintype Vertex]
    (degree : Vertex → ℕ) (edges : ℕ)
    (hminimum : ∀ vertex, 2 ≤ degree vertex)
    (hhandshake : ∑ vertex, degree vertex = 2 * edges) :
    Fintype.card Vertex ≤ edges := by
  classical
  have hsum : ∑ _vertex : Vertex, 2 ≤ ∑ vertex, degree vertex := by
    apply Finset.sum_le_sum
    intro vertex _hvertex
    exact hminimum vertex
  have htwice : 2 * Fintype.card Vertex ≤ 2 * edges := by
    calc
      2 * Fintype.card Vertex = ∑ _vertex : Vertex, 2 := by simp [mul_comm]
      _ ≤ ∑ vertex, degree vertex := hsum
      _ = 2 * edges := hhandshake
  exact Nat.le_of_mul_le_mul_left htwice (by omega)

/-- A positive even natural-number degree is at least two.  This is the local
arithmetic that turns “connected/non-isolated and Eulerian” into the minimum
degree premise used by the handshaking bound. -/
theorem two_le_degree_of_positive_even
    (degree : ℕ) (hpositive : 0 < degree) (heven : Even degree) :
    2 ≤ degree := by
  obtain ⟨half, hdegree⟩ := heven
  omega

/-- A finite graph with positive even degree at every surviving vertex and the
handshaking identity satisfies `|V| ≤ |E|`.  Positivity is the only connectivity
consequence needed by the count; evenness upgrades it to minimum degree two. -/
theorem vertices_le_edges_of_positive_evenDegrees_of_handshake
    {Vertex : Type*} [Fintype Vertex]
    (degree : Vertex → ℕ) (edges : ℕ)
    (hpositive : ∀ vertex, 0 < degree vertex)
    (heven : ∀ vertex, Even (degree vertex))
    (hhandshake : ∑ vertex, degree vertex = 2 * edges) :
    Fintype.card Vertex ≤ edges := by
  apply vertices_le_edges_of_minDegree_two_of_handshake degree edges
  · intro vertex
    exact two_le_degree_of_positive_even
      (degree vertex) (hpositive vertex) (heven vertex)
  · exact hhandshake

/-- Closed evaluation of a balanced rank-one kernel on an all-even connected test graph after
the vertex sums in the graph homomorphism count have factorized. -/
noncomputable def balancedRankOneGraphSum (p : ℕ) (vertices edges : ℕ) : ℝ :=
  (p : ℝ) ^ vertices / (p : ℝ) ^ (edges + 1)

/-- At `p = 0` the denominator is `0 ^ (edges + 1) = 0`, so Mathlib returns `0` for the whole
ratio.  A zero-dimensional traffic sum has no balanced value; the biological range is `p ≥ 1`. -/
theorem balancedRankOneGraphSum_at_zero_dimension_is_junk (vertices edges : ℕ) :
    balancedRankOneGraphSum 0 vertices edges = 0 := by
  simp [balancedRankOneGraphSum]


/-- The closed rank-one graph coordinate obeys the universal `1/p` bound. -/
theorem balancedRankOneGraphSum_le_inv
    (p vertices edges : ℕ) (hp : 1 ≤ p) (hev : vertices ≤ edges) :
    balancedRankOneGraphSum p vertices edges ≤ 1 / (p : ℝ) := by
  apply rankOneGraphSum_le_inv (p : ℝ) vertices edges
  · exact_mod_cast hp
  · exact hev

/-- A positive rank-one spike can leave every fixed connected traffic coordinate unchanged in
the limit: every nonzero all-even contribution is squeezed by `1/p`, while an odd-degree
coordinate is exactly zero by balancedness. -/
theorem balancedRankOneGraphSum_tendsto_zero (vertices edges : ℕ) (hev : vertices ≤ edges) :
    Filter.Tendsto (fun p : ℕ ↦ balancedRankOneGraphSum (p + 1) vertices edges)
      Filter.atTop (nhds 0) := by
  have hnonneg : ∀ p : ℕ, 0 ≤ balancedRankOneGraphSum (p + 1) vertices edges := by
    intro p
    unfold balancedRankOneGraphSum
    positivity
  have hupper : ∀ p : ℕ,
      balancedRankOneGraphSum (p + 1) vertices edges ≤ 1 / ((p + 1 : ℕ) : ℝ) := by
    intro p
    exact balancedRankOneGraphSum_le_inv (p + 1) vertices edges (Nat.succ_le_succ (Nat.zero_le p))
      hev
  have hdenom : Filter.Tendsto (fun p : ℕ ↦ ((p + 1 : ℕ) : ℝ))
      Filter.atTop Filter.atTop := by
    convert (tendsto_natCast_atTop_atTop (R := ℝ)).comp
      (Filter.tendsto_add_atTop_nat 1) using 1
  have hinv : Filter.Tendsto (fun p : ℕ ↦ 1 / ((p + 1 : ℕ) : ℝ))
      Filter.atTop (nhds 0) := by
    simpa only [one_div] using hdenom.inv_tendsto_atTop
  exact squeeze_zero hnonneg hupper hinv

/-- Closed balanced-spike coordinate for an arbitrary connected test graph: odd-degree graphs
vanish exactly, while all-even graphs use the factorized rank-one graph sum. -/
noncomputable def balancedRankOneTrafficCoordinate
    (hasOddDegree : Bool) (p vertices edges : ℕ) : ℝ :=
  if hasOddDegree then 0 else balancedRankOneGraphSum p vertices edges

/-- Reference evaluation; see `Descent.Core.Ratios` for what these pin and why. -/
theorem balancedRankOneTrafficCoordinate_at_reference_point (p vertices edges : ℕ) :
    balancedRankOneTrafficCoordinate true p vertices edges = 0 ∧
      balancedRankOneTrafficCoordinate false p vertices edges
        = balancedRankOneGraphSum p vertices edges := by
  constructor <;> simp [balancedRankOneTrafficCoordinate]


/-- Every fixed connected graph coordinate of the balanced positive rank-one
spike vanishes.  Odd-degree coordinates vanish identically; the edge bound is
therefore required only in the all-even branch. -/
theorem balancedRankOneTrafficCoordinate_tendsto_zero
    (hasOddDegree : Bool) (vertices edges : ℕ)
    (hev : hasOddDegree = false → vertices ≤ edges) :
    Filter.Tendsto
      (fun p : ℕ ↦ balancedRankOneTrafficCoordinate hasOddDegree (p + 1) vertices edges)
      Filter.atTop (nhds 0) := by
  cases hodd : hasOddDegree with
  | false =>
      simpa [balancedRankOneTrafficCoordinate, hodd] using
        balancedRankOneGraphSum_tendsto_zero vertices edges (hev hodd)
  | true =>
      simp [balancedRankOneTrafficCoordinate]

/-- A fixed graph expansion contains only finitely many nonempty choices of
rank-one spike edges.  After contracting its identity edges, each choice has a
coefficient and one balanced rank-one coordinate.  This definition records the
complete correction obtained by summing those contracted terms. -/
noncomputable def finiteRankOneTrafficCorrection
    {Term : Type*} [Fintype Term]
    (coefficient : Term → ℝ) (hasOddDegree : Term → Bool)
    (vertices edges : Term → ℕ) (population : ℕ) : ℝ :=
  ∑ term,
    coefficient term *
      balancedRankOneTrafficCoordinate (hasOddDegree term) population
        (vertices term) (edges term)

/-- **Finite expansion closes rank-one traffic invisibility.**  If every
contracted nonempty spike graph satisfies the connected all-even edge bound
`|V| ≤ |E|` whenever it is nonzero, then their entire fixed-graph correction
vanishes.  This is the analytic step from one contracted term to the expansion
of `(aI + λP)`; the graph contraction supplies `hconnected`. -/
theorem finiteRankOneTrafficCorrection_tendsto_zero
    {Term : Type*} [Fintype Term]
    (coefficient : Term → ℝ) (hasOddDegree : Term → Bool)
    (vertices edges : Term → ℕ)
    (hconnected : ∀ term, hasOddDegree term = false → vertices term ≤ edges term) :
    Filter.Tendsto
      (fun population : ℕ ↦
        finiteRankOneTrafficCorrection coefficient hasOddDegree vertices edges
          (population + 1))
      Filter.atTop (nhds 0) := by
  classical
  have hterm : ∀ term : Term,
      Filter.Tendsto
        (fun population : ℕ ↦ coefficient term *
          balancedRankOneTrafficCoordinate (hasOddDegree term) (population + 1)
            (vertices term) (edges term))
        Filter.atTop (nhds 0) := by
    intro term
    simpa using
      (balancedRankOneTrafficCoordinate_tendsto_zero
        (hasOddDegree term) (vertices term) (edges term) (hconnected term)).const_mul
          (coefficient term)
  have hsum := tendsto_finset_sum Finset.univ
    (fun term _hterm ↦ hterm term)
  simpa [finiteRankOneTrafficCorrection] using hsum

/-- The finite traffic correction vanishes from graph-local degree data, with no pre-assumed cardinal inequality.  Each all-even contracted term supplies
its degree function, minimum degree two, and handshaking identity; odd-degree
terms require no graph bound because balancedness kills them exactly. -/
theorem finiteRankOneTrafficCorrection_tendsto_zero_of_degreeData
    {Term : Type*} [Fintype Term]
    (coefficient : Term → ℝ) (hasOddDegree : Term → Bool)
    (vertices edges : Term → ℕ)
    (degree : ∀ term, Fin (vertices term) → ℕ)
    (hminimum : ∀ term, hasOddDegree term = false →
      ∀ vertex, 2 ≤ degree term vertex)
    (hhandshake : ∀ term, hasOddDegree term = false →
      ∑ vertex, degree term vertex = 2 * edges term) :
    Filter.Tendsto
      (fun population : ℕ ↦
        finiteRankOneTrafficCorrection coefficient hasOddDegree vertices edges
          (population + 1))
      Filter.atTop (nhds 0) := by
  apply finiteRankOneTrafficCorrection_tendsto_zero
  intro term heven
  have hbound := vertices_le_edges_of_minDegree_two_of_handshake
    (degree term) (edges term) (hminimum term heven) (hhandshake term heven)
  simpa using hbound

/-- **Connected-Eulerian degree data suffice for finite traffic
invisibility.**  On every all-even contracted term, positive degrees exclude
isolated vertices, degree parity supplies the minimum-degree-two bound, and
handshaking supplies `|V| ≤ |E|`.  Odd-degree terms still vanish without any of
these hypotheses. -/
theorem finiteRankOneTrafficCorrection_tendsto_zero_of_positiveEvenDegreeData
    {Term : Type*} [Fintype Term]
    (coefficient : Term → ℝ) (hasOddDegree : Term → Bool)
    (vertices edges : Term → ℕ)
    (degree : ∀ term, Fin (vertices term) → ℕ)
    (hpositive : ∀ term, hasOddDegree term = false →
      ∀ vertex, 0 < degree term vertex)
    (heven : ∀ term, hasOddDegree term = false →
      ∀ vertex, Even (degree term vertex))
    (hhandshake : ∀ term, hasOddDegree term = false →
      ∑ vertex, degree term vertex = 2 * edges term) :
    Filter.Tendsto
      (fun population : ℕ ↦
        finiteRankOneTrafficCorrection coefficient hasOddDegree vertices edges
          (population + 1))
      Filter.atTop (nhds 0) := by
  apply finiteRankOneTrafficCorrection_tendsto_zero_of_degreeData
    coefficient hasOddDegree vertices edges degree
  · intro term hallEven vertex
    exact two_le_degree_of_positive_even
      (degree term vertex) (hpositive term hallEven vertex) (heven term hallEven vertex)
  · exact hhandshake

/-! ### Positive-cone and ground-state certificates -/

/-- Balanced finite coordinates: `p` positive-sign and `p` negative-sign
locations. -/
abbrev BalancedRankOneCoordinate (population : ℕ) :=
  Sum (Fin population) (Fin population)

/-- The balanced hidden sign vector. -/
def balancedRankOneSign (population : ℕ) :
    BalancedRankOneCoordinate population → ℝ
  | Sum.inl _coordinate => 1
  | Sum.inr _coordinate => -1

/-- The hidden sign vector has exactly zero coordinate sum. -/
theorem balancedRankOneSign_sum_eq_zero (population : ℕ) :
    ∑ coordinate, balancedRankOneSign population coordinate = 0 := by
  simp [balancedRankOneSign]

/-- Its squared Euclidean norm is exactly the ambient dimension `2p`. -/
theorem balancedRankOneSign_dot_self (population : ℕ) :
    balancedRankOneSign population ⬝ᵥ balancedRankOneSign population =
      (2 * population : ℕ) := by
  simp [dotProduct, balancedRankOneSign]
  ring

/-- The normalized outer-product projector onto the balanced hidden
direction.  The positive-population premise is imposed on the theorems that
use its normalization. -/
noncomputable def balancedRankOneProjector (population : ℕ) :
    Matrix (BalancedRankOneCoordinate population)
      (BalancedRankOneCoordinate population) ℝ :=
  (((2 * population : ℕ) : ℝ)⁻¹) •
    Matrix.vecMulVec (balancedRankOneSign population) (balancedRankOneSign population)

/-- The normalized balanced outer product is positive semidefinite. -/
theorem balancedRankOneProjector_posSemidef (population : ℕ) :
    (balancedRankOneProjector population).PosSemidef := by
  apply Matrix.PosSemidef.smul
  · simpa using Matrix.posSemidef_vecMulVec_self_star
      (balancedRankOneSign population)
  · positivity

/-- The concrete finite covariance witness `aI + λP`. -/
noncomputable def balancedRankOneCovariance
    (baseline spikeStrength : ℝ) (population : ℕ) :
    Matrix (BalancedRankOneCoordinate population)
      (BalancedRankOneCoordinate population) ℝ :=
  Matrix.diagonal (fun _coordinate ↦ baseline) +
    spikeStrength • balancedRankOneProjector population

/-- For nonnegative baseline and spike strength, the concrete covariance lies
in the positive-semidefinite cone. -/
theorem balancedRankOneCovariance_posSemidef
    (baseline spikeStrength : ℝ) (population : ℕ)
    (hbaseline : 0 ≤ baseline) (hspike : 0 ≤ spikeStrength) :
    (balancedRankOneCovariance baseline spikeStrength population).PosSemidef := by
  apply Matrix.PosSemidef.add
  · exact Matrix.PosSemidef.diagonal (fun _coordinate ↦ hbaseline)
  · exact (balancedRankOneProjector_posSemidef population).smul hspike

/-- Quadratic form of a real finite covariance matrix. -/
noncomputable def finiteMatrixQuadraticForm
    {Coordinate : Type*} [Fintype Coordinate]
    (matrix : Matrix Coordinate Coordinate ℝ) (vector : Coordinate → ℝ) : ℝ :=
  vector ⬝ᵥ (matrix *ᵥ vector)

/-- The concrete rank-one covariance has exactly the baseline energy plus the
squared hidden-direction alignment. -/
theorem balancedRankOneCovariance_quadraticForm
    (baseline spikeStrength : ℝ) (population : ℕ)
    (vector : BalancedRankOneCoordinate population → ℝ) :
    finiteMatrixQuadraticForm
        (balancedRankOneCovariance baseline spikeStrength population) vector =
      baseline * (∑ coordinate, vector coordinate ^ 2) +
        spikeStrength * (((2 * population : ℕ) : ℝ)⁻¹) *
          (balancedRankOneSign population ⬝ᵥ vector) ^ 2 := by
  classical
  have hdiagonalMulVec :
      Matrix.diagonal (fun _coordinate ↦ baseline) *ᵥ vector =
        baseline • vector := by
    ext coordinate
    simp [Matrix.mulVec]
  have hdiagonal :
      vector ⬝ᵥ
          (Matrix.diagonal (fun _coordinate ↦ baseline) *ᵥ vector) =
        baseline * ∑ coordinate, vector coordinate ^ 2 := by
    rw [hdiagonalMulVec]
    simp only [dotProduct, Pi.smul_apply, smul_eq_mul, pow_two]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro coordinate _hcoordinate
    ring
  rw [finiteMatrixQuadraticForm, balancedRankOneCovariance,
    Matrix.add_mulVec, dotProduct_add, hdiagonal]
  simp only [balancedRankOneProjector, Matrix.smul_mulVec,
    Matrix.vecMulVec_mulVec, dotProduct_smul]
  simp
  rw [dotProduct_comm vector (balancedRankOneSign population)]
  ring

/-- A Rademacher-valued vector has squared norm equal to the ambient
dimension `2p`. -/
theorem balancedRademacher_squaredNorm
    (population : ℕ) (vector : BalancedRankOneCoordinate population → ℝ)
    (hrademacher : ∀ coordinate, vector coordinate ^ 2 = 1) :
    ∑ coordinate, vector coordinate ^ 2 = (2 * population : ℕ) := by
  calc
    (∑ coordinate, vector coordinate ^ 2) = ∑ _coordinate, (1 : ℝ) := by
      apply Finset.sum_congr rfl
      intro coordinate _hcoordinate
      exact hrademacher coordinate
    _ = (2 * population : ℕ) := by
      simp [BalancedRankOneCoordinate]
      ring

/-- On Rademacher vectors, the concrete covariance energy is exactly the
baseline extensive term plus the normalized Curie--Weiss alignment energy. -/
theorem balancedRankOneCovariance_rademacherEnergy
    (baseline spikeStrength : ℝ) (population : ℕ)
    (vector : BalancedRankOneCoordinate population → ℝ)
    (hrademacher : ∀ coordinate, vector coordinate ^ 2 = 1) :
    finiteMatrixQuadraticForm
        (balancedRankOneCovariance baseline spikeStrength population) vector =
      baseline * (2 * population : ℕ) +
        spikeStrength * (((2 * population : ℕ) : ℝ)⁻¹) *
          (balancedRankOneSign population ⬝ᵥ vector) ^ 2 := by
  rw [balancedRankOneCovariance_quadraticForm,
    balancedRademacher_squaredNorm population vector hrademacher]

/-- **Hamiltonian bridge to finite Curie--Weiss pressure.**  After subtracting
the baseline covariance energy and multiplying by `temperature/2`, the matrix
Hamiltonian is exactly `tλ/(2N) * alignment²` with `N=2p`, the exponent used
by `finiteCWPartition`. -/
theorem balancedRankOneCovariance_rademacherExponent_eq_finiteCW
    (baseline spikeStrength temperature : ℝ) (population : ℕ)
    (vector : BalancedRankOneCoordinate population → ℝ)
    (hrademacher : ∀ coordinate, vector coordinate ^ 2 = 1) :
    temperature / 2 *
        (finiteMatrixQuadraticForm
            (balancedRankOneCovariance baseline spikeStrength population) vector -
          baseline * (2 * population : ℕ)) =
      (temperature * spikeStrength) /
          (2 * ((2 * population : ℕ) : ℝ)) *
        (balancedRankOneSign population ⬝ᵥ vector) ^ 2 := by
  rw [balancedRankOneCovariance_rademacherEnergy
    baseline spikeStrength population vector hrademacher]
  ring

/-- The constant-one vector on an arbitrary coordinate type. -/
def constantOneVector {Coordinate : Type*} : Coordinate → ℝ :=
  fun _coordinate ↦ 1

@[simp] theorem constantOneVector_apply {Coordinate : Type*}
    (coordinate : Coordinate) : constantOneVector coordinate = 1 := rfl

/-- The all-one Rademacher vector is orthogonal to the balanced hidden
direction. -/
def balancedRankOneOrthogonalSpin (population : ℕ) :
    BalancedRankOneCoordinate population → ℝ :=
  constantOneVector

/-- The explicit orthogonal spin is genuinely Rademacher-valued. -/
theorem balancedRankOneOrthogonalSpin_isRademacher (population : ℕ) :
    ∀ coordinate, balancedRankOneOrthogonalSpin population coordinate ^ 2 = 1 := by
  intro coordinate
  simp [balancedRankOneOrthogonalSpin]

/-- Balancedness makes the all-one spin exactly orthogonal to the hidden
direction, at every finite population. -/
theorem balancedRankOneOrthogonalSpin_alignment_eq_zero (population : ℕ) :
    balancedRankOneSign population ⬝ᵥ
        balancedRankOneOrthogonalSpin population = 0 := by
  simpa [dotProduct, balancedRankOneOrthogonalSpin] using
    balancedRankOneSign_sum_eq_zero population

/-- The hidden sign vector itself is an explicit aligned Rademacher spin. -/
theorem balancedRankOneSign_isRademacher (population : ℕ) :
    ∀ coordinate, balancedRankOneSign population coordinate ^ 2 = 1 := by
  intro coordinate
  cases coordinate <;> simp [balancedRankOneSign]

/-- **Concrete matrix-level ground-state certificate.**  Every Rademacher
spin has energy at least the unspiked baseline, the explicit all-one spin
attains it, and the explicit hidden-sign spin has strictly larger energy when
the spike and population are positive.  Thus the lower ground state is
unchanged even though the same covariance has a supercritical pressure
transition. -/
theorem balancedRankOneCovariance_groundState_certificate
    (baseline spikeStrength : ℝ) (population : ℕ)
    (hspike : 0 < spikeStrength) (hpopulation : 0 < population) :
    (∀ vector : BalancedRankOneCoordinate population → ℝ,
      (∀ coordinate, vector coordinate ^ 2 = 1) →
        baseline * (2 * population : ℕ) ≤
          finiteMatrixQuadraticForm
            (balancedRankOneCovariance baseline spikeStrength population) vector) ∧
      finiteMatrixQuadraticForm
          (balancedRankOneCovariance baseline spikeStrength population)
          (balancedRankOneOrthogonalSpin population) =
        baseline * (2 * population : ℕ) ∧
      baseline * (2 * population : ℕ) <
        finiteMatrixQuadraticForm
          (balancedRankOneCovariance baseline spikeStrength population)
          (balancedRankOneSign population) := by
  have hdimension : 0 < (((2 * population : ℕ) : ℝ)) := by
    exact_mod_cast Nat.mul_pos (by norm_num : 0 < 2) hpopulation
  constructor
  · intro vector hrademacher
    rw [balancedRankOneCovariance_rademacherEnergy
      baseline spikeStrength population vector hrademacher]
    have hcorrection : 0 ≤
        spikeStrength * (((2 * population : ℕ) : ℝ)⁻¹) *
          (balancedRankOneSign population ⬝ᵥ vector) ^ 2 := by
      positivity
    linarith
  constructor
  · rw [balancedRankOneCovariance_rademacherEnergy
      baseline spikeStrength population (balancedRankOneOrthogonalSpin population)
      (balancedRankOneOrthogonalSpin_isRademacher population),
      balancedRankOneOrthogonalSpin_alignment_eq_zero]
    ring
  · rw [balancedRankOneCovariance_rademacherEnergy
      baseline spikeStrength population (balancedRankOneSign population)
      (balancedRankOneSign_isRademacher population),
      balancedRankOneSign_dot_self]
    have hcorrection : 0 <
        spikeStrength * (((2 * population : ℕ) : ℝ)⁻¹) *
          (((2 * population : ℕ) : ℝ)) ^ 2 := by
      positivity
    linarith

/-- Per-coordinate quadratic energy of a rank-one positive spike, expressed through the spin's
alignment with the hidden direction. -/
noncomputable def rankOneEnergyDensity (baseline spikeStrength population alignment : ℝ) : ℝ :=
  baseline + spikeStrength * (alignment / population) ^ 2

/-- With no population the alignment share divides by zero and Mathlib returns `0`, so the
density reports the baseline alone: the spike contributes nothing where the true reading is
that the share is undefined. -/
theorem rankOneEnergyDensity_at_zero_population_is_junk
    (baseline spikeStrength alignment : ℝ) :
    rankOneEnergyDensity baseline spikeStrength 0 alignment = baseline := by
  simp [rankOneEnergyDensity]


/-- A positive-semidefinite rank-one spike can only raise the energy. -/
theorem rankOneEnergyDensity_ge_baseline
    (baseline spikeStrength population alignment : ℝ) (hspike : 0 ≤ spikeStrength) :
    baseline ≤ rankOneEnergyDensity baseline spikeStrength population alignment := by
  unfold rankOneEnergyDensity
  have : 0 ≤ spikeStrength * (alignment / population) ^ 2 := by positivity
  linarith

/-- An orthogonal spin has exactly the unspiked ground-state energy. -/
@[simp] theorem rankOneEnergyDensity_orthogonal
    (baseline spikeStrength population : ℝ) :
    rankOneEnergyDensity baseline spikeStrength population 0 = baseline := by
  simp [rankOneEnergyDensity]

/-- A fully aligned spin exposes the complete spike strength. -/
theorem rankOneEnergyDensity_aligned
    (baseline spikeStrength population : ℝ) (hpopulation : population ≠ 0) :
    rankOneEnergyDensity baseline spikeStrength population population =
      baseline + spikeStrength := by
  simp [rankOneEnergyDensity, hpopulation]

/-- **Ground-state dichotomy failure, as an exact certificate.**  If the spin class contains one
configuration orthogonal to the hidden direction, every spiked energy is at least the baseline
and that configuration attains it.  Yet an aligned configuration has larger energy when the
spike is positive.  Thus identical lower ground-state energy does not control the upper tail. -/
theorem rankOne_groundState_certificate
    {Spin : Type*} (alignment : Spin → ℝ) (orthogonal : Spin)
    (baseline spikeStrength population : ℝ) (hspike : 0 ≤ spikeStrength)
    (horthogonal : alignment orthogonal = 0) :
    (∀ spin, baseline ≤
        rankOneEnergyDensity baseline spikeStrength population (alignment spin)) ∧
      rankOneEnergyDensity baseline spikeStrength population (alignment orthogonal) = baseline := by
  constructor
  · intro spin
    exact rankOneEnergyDensity_ge_baseline baseline spikeStrength population (alignment spin)
      hspike
  · rw [horthogonal, rankOneEnergyDensity_orthogonal]

end RankOneInvisibility

end TrafficInvariantSeparation
end Descent.Blindness
