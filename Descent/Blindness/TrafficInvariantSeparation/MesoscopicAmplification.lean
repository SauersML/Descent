/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Blindness.TrafficInvariantSeparation.RankOneInvisibility

assert_below Descent.Conditionals Descent.Portability Descent.Decision Descent.Program

namespace Descent.Blindness
namespace TrafficInvariantSeparation

open scoped Matrix Topology

/-!
# `TrafficInvariantSeparation.MesoscopicAmplification`

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


section MesoscopicAmplification

/-- Difference between the diagonal traffic coordinate of `aI` and that of a diagonal matrix
whose exceptional fraction is `4⁻ᵏ` and exceptional value is `a + 2`. -/
noncomputable def diagonalTrafficCorrection (baseline : ℝ) (edges iteration : ℕ) : ℝ :=
  (1 / 4 : ℝ) ^ iteration * ((baseline + 2) ^ edges - baseline ^ edges)

/-- Reference evaluation; see `Descent.Core.Ratios` for what these pin and why. -/
theorem diagonalTrafficCorrection_at_reference_point :
    diagonalTrafficCorrection 1 1 1 = 1 / 2 := by
  norm_num [diagonalTrafficCorrection]


/-- Every fixed traffic coordinate misses the exceptional diagonal block. -/
theorem diagonalTrafficCorrection_tendsto_zero (baseline : ℝ) (edges : ℕ) :
    Filter.Tendsto (fun iteration ↦ diagonalTrafficCorrection baseline edges iteration)
      Filter.atTop (nhds 0) := by
  have hpow : Filter.Tendsto (fun iteration : ℕ ↦ (1 / 4 : ℝ) ^ iteration)
      Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_abs_lt_one (by norm_num)
  simpa [diagonalTrafficCorrection] using
    hpow.mul_const ((baseline + 2) ^ edges - baseline ^ edges)

/-- A concrete `16^k`-coordinate realization of the mesoscopic example.  The
second coordinate indexes `4^k` blocks; the exceptional subspace is the slice
whose second coordinate has value zero and therefore has exactly `4^k`
coordinates. -/
abbrev MesoscopicGFOMCoordinate (iteration : ℕ) :=
  Fin (4 ^ iteration) × Fin (4 ^ iteration)

/-- The exceptional coordinate slice supporting the amplified output. -/
abbrev MesoscopicGFOMExceptionalCoordinate (iteration : ℕ) :=
  {coordinate : MesoscopicGFOMCoordinate iteration // coordinate.2.val = 0}

/-- The concrete ambient dimension is exactly `16^k`. -/
theorem mesoscopicGFOM_dimension (iteration : ℕ) :
    Fintype.card (MesoscopicGFOMCoordinate iteration) = 16 ^ iteration := by
  simp [MesoscopicGFOMCoordinate, ← mul_pow]

/-- The concrete exceptional rank is exactly `4^k`. -/
theorem mesoscopicGFOM_exceptionalRank (iteration : ℕ) :
    Fintype.card (MesoscopicGFOMExceptionalCoordinate iteration) = 4 ^ iteration := by
  classical
  let equivalence : MesoscopicGFOMExceptionalCoordinate iteration ≃ Fin (4 ^ iteration) :=
    { toFun := fun coordinate ↦ coordinate.1.1
      invFun := fun coordinate ↦
        ⟨(coordinate, ⟨0, pow_pos (by norm_num) iteration⟩), rfl⟩
      left_inv := by
        intro coordinate
        apply Subtype.ext
        apply Prod.ext
        · rfl
        · apply Fin.ext
          exact coordinate.property.symm
      right_inv := fun _coordinate ↦ rfl }
  simpa using Fintype.card_congr equivalence

/-- The actual diagonal GFOM step `(M-aI)x`: multiply the exceptional slice
by two and annihilate the bulk. -/
def mesoscopicGFOMStep (iteration : ℕ)
    (vector : MesoscopicGFOMCoordinate iteration → ℝ) :
    MesoscopicGFOMCoordinate iteration → ℝ :=
  fun coordinate ↦ if coordinate.2.val = 0 then 2 * vector coordinate else 0

/-- Repeated application of the concrete diagonal step. -/
def mesoscopicGFOMIterate (iteration : ℕ) :
    ℕ → (MesoscopicGFOMCoordinate iteration → ℝ) →
      MesoscopicGFOMCoordinate iteration → ℝ
  | 0, vector => vector
  | runtime + 1, vector =>
      mesoscopicGFOMStep iteration (mesoscopicGFOMIterate iteration runtime vector)

/-- Every positive-time iterate has the exact expected coordinate formula:
the exceptional slice is multiplied by `2^t` and every bulk coordinate is
zero. -/
theorem mesoscopicGFOMIterate_succ_apply
    (iteration runtime : ℕ)
    (vector : MesoscopicGFOMCoordinate iteration → ℝ)
    (coordinate : MesoscopicGFOMCoordinate iteration) :
    mesoscopicGFOMIterate iteration (runtime + 1) vector coordinate =
      if coordinate.2.val = 0 then
        (2 : ℝ) ^ (runtime + 1) * vector coordinate else 0 := by
  induction runtime with
  | zero =>
      simp [mesoscopicGFOMIterate, mesoscopicGFOMStep]
  | succ runtime ih =>
      by_cases hexceptional : coordinate.2.val = 0
      · rw [mesoscopicGFOMIterate]
        simp only [mesoscopicGFOMStep, hexceptional, ↓reduceIte, ih, pow_succ]
        ring
      · rw [mesoscopicGFOMIterate]
        simp only [mesoscopicGFOMStep, hexceptional, ↓reduceIte]

/-- Deterministic unit input used to expose the exact normalized amplification
without adding an unnecessary probabilistic layer. -/
def mesoscopicGFOMUnitInput (iteration : ℕ) :
    MesoscopicGFOMCoordinate iteration → ℝ :=
  constantOneVector

/-- Both deterministic inputs are restrictions of the same constant-one
vector, despite living on different finite coordinate spaces. -/
theorem balancedRankOneOrthogonalSpin_eq_mesoscopicGFOMUnitInput
    (population iteration : ℕ)
    (balancedCoordinate : BalancedRankOneCoordinate population)
    (mesoscopicCoordinate : MesoscopicGFOMCoordinate iteration) :
    balancedRankOneOrthogonalSpin population balancedCoordinate =
      mesoscopicGFOMUnitInput iteration mesoscopicCoordinate := by
  rfl

/-- Normalized squared output of the genuine finite diagonal iteration. -/
noncomputable def mesoscopicGFOMActualEnergy (iteration runtime : ℕ) : ℝ :=
  (∑ coordinate : MesoscopicGFOMCoordinate iteration,
    mesoscopicGFOMIterate iteration runtime
      (mesoscopicGFOMUnitInput iteration) coordinate ^ 2) /
    (16 : ℝ) ^ iteration

/-- Exactly `4^k` coordinates lie in the exceptional slice. -/
theorem mesoscopicGFOM_sum_exceptionalSlice
    (iteration : ℕ) (value : ℝ) :
    (∑ coordinate : MesoscopicGFOMCoordinate iteration,
      if coordinate.2.val = 0 then value else 0) =
      (4 : ℝ) ^ iteration * value := by
  classical
  have hsize : 0 < 4 ^ iteration := pow_pos (by norm_num) iteration
  have hinner : ∀ first : Fin (4 ^ iteration),
      (∑ second : Fin (4 ^ iteration),
        if second.val = 0 then value else 0) = value := by
    intro first
    let zero : Fin (4 ^ iteration) := ⟨0, hsize⟩
    rw [Finset.sum_eq_single zero]
    · simp [zero]
    · intro second _hsecond hne
      have hnonzero : second.val ≠ 0 := by
        intro hzero
        apply hne
        apply Fin.ext
        exact hzero
      simp [hnonzero]
    · simp
  rw [Fintype.sum_prod_type]
  calc
    (∑ first : Fin (4 ^ iteration),
      ∑ second : Fin (4 ^ iteration),
        if second.val = 0 then value else 0) =
        ∑ _first : Fin (4 ^ iteration), value := by
      apply Finset.sum_congr rfl
      intro first _hfirst
      exact hinner first
    _ = (4 : ℝ) ^ iteration * value := by simp

/-- Normalized squared output of the diagonal power iteration: the exceptional mass `4⁻ᵏ` is
amplified by `4ᵗ`. -/
noncomputable def mesoscopicGFOMEnergy (iteration runtime : ℕ) : ℝ :=
  (4 : ℝ) ^ runtime * (1 / 4 : ℝ) ^ iteration

/-- At every positive runtime, the energy of the concrete `16^k`-dimensional
iteration is exactly the scalar amplification ledger. -/
theorem mesoscopicGFOMActualEnergy_succ_eq_proxy
    (iteration runtime : ℕ) :
    mesoscopicGFOMActualEnergy iteration (runtime + 1) =
      mesoscopicGFOMEnergy iteration (runtime + 1) := by
  have hsum :
      (∑ coordinate : MesoscopicGFOMCoordinate iteration,
        mesoscopicGFOMIterate iteration (runtime + 1)
          (mesoscopicGFOMUnitInput iteration) coordinate ^ 2) =
        (4 : ℝ) ^ iteration * ((2 : ℝ) ^ (runtime + 1)) ^ 2 := by
    simpa [mesoscopicGFOMIterate_succ_apply, mesoscopicGFOMUnitInput] using
      mesoscopicGFOM_sum_exceptionalSlice iteration
        (((2 : ℝ) ^ (runtime + 1)) ^ 2)
  have hamplification : ((2 : ℝ) ^ (runtime + 1)) ^ 2 =
      (4 : ℝ) ^ (runtime + 1) := by
    rw [pow_two, ← mul_pow]
    norm_num
  have hmass : (4 : ℝ) ^ iteration / (16 : ℝ) ^ iteration =
      (1 / 4 : ℝ) ^ iteration := by
    rw [← div_pow]
    norm_num
  rw [mesoscopicGFOMActualEnergy, hsum, hamplification, mesoscopicGFOMEnergy]
  calc
    (4 : ℝ) ^ iteration * (4 : ℝ) ^ (runtime + 1) /
        (16 : ℝ) ^ iteration =
      (4 : ℝ) ^ (runtime + 1) *
        ((4 : ℝ) ^ iteration / (16 : ℝ) ^ iteration) := by ring
    _ = (4 : ℝ) ^ (runtime + 1) * (1 / 4 : ℝ) ^ iteration := by rw [hmass]

/-- At logarithmic runtime `t = k`, the vanishing mass and amplification cancel exactly. -/
@[simp] theorem mesoscopicGFOMEnergy_logRuntime (iteration : ℕ) :
    mesoscopicGFOMEnergy iteration iteration = 1 := by
  rw [mesoscopicGFOMEnergy, ← mul_pow]
  norm_num

/-- At every fixed runtime, the same normalized output vanishes. -/
theorem mesoscopicGFOMEnergy_fixedRuntime_tendsto_zero (runtime : ℕ) :
    Filter.Tendsto (fun iteration ↦ mesoscopicGFOMEnergy iteration runtime)
      Filter.atTop (nhds 0) := by
  have hpow : Filter.Tendsto (fun iteration : ℕ ↦ (1 / 4 : ℝ) ^ iteration)
      Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_abs_lt_one (by norm_num)
  simpa [mesoscopicGFOMEnergy] using hpow.const_mul ((4 : ℝ) ^ runtime)

/-- Every fixed positive runtime of the actual finite diagonal iteration has
vanishing normalized output energy. -/
theorem mesoscopicGFOMActualEnergy_fixedPositiveRuntime_tendsto_zero
    (runtime : ℕ) :
    Filter.Tendsto
      (fun iteration ↦ mesoscopicGFOMActualEnergy iteration (runtime + 1))
      Filter.atTop (nhds 0) := by
  simpa only [mesoscopicGFOMActualEnergy_succ_eq_proxy] using
    mesoscopicGFOMEnergy_fixedRuntime_tendsto_zero (runtime + 1)

/-- At the genuine logarithmic runtime `t=k`, for every positive `k`, the
actual normalized squared output is exactly one. -/
theorem mesoscopicGFOMActualEnergy_logRuntime (iteration : ℕ)
    (hiteration : 0 < iteration) :
    mesoscopicGFOMActualEnergy iteration iteration = 1 := by
  obtain ⟨runtime, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hiteration)
  rw [mesoscopicGFOMActualEnergy_succ_eq_proxy]
  exact mesoscopicGFOMEnergy_logRuntime (runtime + 1)

/-- The dimensions `pₖ = 16ᵏ` and exceptional ranks `rₖ = 4ᵏ` have mass exactly `4⁻ᵏ`. -/
theorem mesoscopic_rank_fraction (iteration : ℕ) :
    (4 : ℝ) ^ iteration / (16 : ℝ) ^ iteration = (1 / 4 : ℝ) ^ iteration := by
  rw [← div_pow]
  norm_num

/-- Fixed traffic and logarithmic-time iteration therefore have incompatible limits. -/
theorem limitingTraffic_does_not_control_logarithmicIteration (runtime : ℕ) :
    Filter.Tendsto (fun iteration ↦ diagonalTrafficCorrection 1 runtime iteration)
        Filter.atTop (nhds 0) ∧
      mesoscopicGFOMEnergy runtime runtime = 1 :=
  ⟨diagonalTrafficCorrection_tendsto_zero 1 runtime,
    mesoscopicGFOMEnergy_logRuntime runtime⟩

/-- The fixed-coordinate/logarithmic-runtime separation contract. -/
def FixedTrafficLogRuntimeSeparation : Prop :=
    (∀ edges : ℕ,
      Filter.Tendsto (fun iteration ↦ diagonalTrafficCorrection 1 edges iteration)
        Filter.atTop (nhds 0)) ∧
      ∀ iteration : ℕ, mesoscopicGFOMEnergy iteration iteration = 1

/-- The complete fixed-coordinate/logarithmic-runtime separation in one statement. -/
theorem fixedTraffic_invisible_logRuntime_visible : FixedTrafficLogRuntimeSeparation :=
  ⟨diagonalTrafficCorrection_tendsto_zero 1, mesoscopicGFOMEnergy_logRuntime⟩

/-- The concrete finite-matrix version of the logarithmic-runtime separation. -/
def ConcreteGFOMLogRuntimeSeparation : Prop :=
  (∀ iteration : ℕ,
    Fintype.card (MesoscopicGFOMCoordinate iteration) = 16 ^ iteration ∧
      Fintype.card (MesoscopicGFOMExceptionalCoordinate iteration) = 4 ^ iteration) ∧
  (∀ edges : ℕ,
    Filter.Tendsto (fun iteration ↦ diagonalTrafficCorrection 1 edges iteration)
      Filter.atTop (nhds 0)) ∧
  (∀ runtime : ℕ,
    Filter.Tendsto
      (fun iteration ↦ mesoscopicGFOMActualEnergy iteration (runtime + 1))
      Filter.atTop (nhds 0)) ∧
  ∀ iteration : ℕ, 0 < iteration →
    mesoscopicGFOMActualEnergy iteration iteration = 1

/-- **Concrete matrix-iteration counterexample.**  The actual finite diagonal
operator has dimension `16^k` and exceptional rank `4^k`; every fixed traffic
coordinate and every fixed positive-time output energy vanish, while the
positive logarithmic-time output energy is exactly one. -/
theorem concreteGFOM_fixedTrafficInvisible_logRuntimeVisible :
    ConcreteGFOMLogRuntimeSeparation :=
  ⟨fun iteration ↦
      ⟨mesoscopicGFOM_dimension iteration, mesoscopicGFOM_exceptionalRank iteration⟩,
    diagonalTrafficCorrection_tendsto_zero 1,
    mesoscopicGFOMActualEnergy_fixedPositiveRuntime_tendsto_zero,
    mesoscopicGFOMActualEnergy_logRuntime⟩

/-! ### Coefficient amplification already breaks limiting traffic at degree one -/

/-- A degree-one invariant polynomial may multiply its normalized trace
coordinate by a size-dependent coefficient.  On the `16^k`-dimensional
diagonal witness, the coefficient `4^k = p_k / r_k` exactly resolves the
exceptional block of relative mass `4⁻ᵏ`. -/
noncomputable def amplifiedDegreeOneTrafficDifference
    (baseline : ℝ) (iteration : ℕ) : ℝ :=
  (4 : ℝ) ^ iteration * diagonalTrafficCorrection baseline 1 iteration

/-- The unamplified degree-one traffic discrepancy vanishes. -/
theorem degreeOneTrafficDifference_tendsto_zero (baseline : ℝ) :
    Filter.Tendsto
      (fun iteration ↦ diagonalTrafficCorrection baseline 1 iteration)
      Filter.atTop (nhds 0) :=
  diagonalTrafficCorrection_tendsto_zero baseline 1

/-- The growing coefficient recovers the spike height exactly at every size.
This is the finite statement behind the correction that fixed degree alone
does not imply factorization through *limiting* traffic. -/
@[simp] theorem amplifiedDegreeOneTrafficDifference_eq_two
    (baseline : ℝ) (iteration : ℕ) :
    amplifiedDegreeOneTrafficDifference baseline iteration = 2 := by
  rw [amplifiedDegreeOneTrafficDifference, diagonalTrafficCorrection]
  rw [show (baseline + 2) ^ 1 - baseline ^ 1 = 2 by ring]
  rw [← mul_assoc, ← mul_pow]
  norm_num

/-- **Unrestricted degree-one polynomials do not factor through limiting
traffic.**  The normalized degree-one coordinate tends to zero, while the
same coordinate with coefficient growth `4^k` remains equal to two. -/
theorem limitingTraffic_insufficient_for_unstableDegreeOne (baseline : ℝ) :
    Filter.Tendsto
        (fun iteration ↦ diagonalTrafficCorrection baseline 1 iteration)
        Filter.atTop (nhds 0) ∧
      ∀ iteration,
        amplifiedDegreeOneTrafficDifference baseline iteration = 2 :=
  ⟨degreeOneTrafficDifference_tendsto_zero baseline,
    amplifiedDegreeOneTrafficDifference_eq_two baseline⟩

end MesoscopicAmplification

end TrafficInvariantSeparation
end Descent.Blindness
