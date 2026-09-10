/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.EvolutionaryObservability

assert_below Descent.Decision Descent.Program

/-!
Permanent blindness for known finite linear dynamics. The complete continuous
time observation vanishes exactly when the first state-dimension many Krylov
observations vanish. This concerns a known generator and unknown initial state;
it makes no claim to identify an unknown generator jointly with that state.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
open scoped Matrix Matrix.Norms.Operator

namespace Descent.Portability.DynamicBlindness

open MinimalObservableLaw
variable {S I : Type*} [Fintype S] [DecidableEq S] [Nonempty S] [Fintype I]

noncomputable def observation (readout : Matrix I S ℝ) (generator : Matrix S S ℝ)
    (direction : S → ℝ) (time : ℝ) : I → ℝ :=
  readout *ᵥ (NormedSpace.exp ℝ (time • generator)) *ᵥ direction

noncomputable def readoutLinear (readout : Matrix I S ℝ) (direction : S → ℝ) :
    Matrix S S ℝ →ₗ[ℝ] (I → ℝ) where
  toFun matrix := readout *ᵥ matrix *ᵥ direction
  map_add' first second := by simp [Matrix.add_mulVec, Matrix.mulVec_add]
  map_smul' scalar matrix := by simp [Matrix.smul_mulVec, Matrix.mulVec_smul]

omit [Nonempty S] in
/-- Differentiation advances the hidden direction by one generator application. -/
theorem observation_hasDerivAt (readout : Matrix I S ℝ) (generator : Matrix S S ℝ)
    (direction : S → ℝ) (time : ℝ) :
    HasDerivAt (observation readout generator direction)
      (observation readout generator (generator *ᵥ direction) time) time := by
  let linear : Matrix S S ℝ →L[ℝ] (I → ℝ) :=
    LinearMap.toContinuousLinearMap (readoutLinear readout direction)
  have hd := linear.hasFDerivAt.comp_hasDerivAt time (hasDerivAt_exp_smul_const generator time)
  change HasDerivAt (fun t : ℝ ↦ readout *ᵥ
    (NormedSpace.exp ℝ (t • generator)) *ᵥ direction) _ time
  simpa only [linear, LinearMap.coe_toContinuousLinearMap', Function.comp_def,
    readoutLinear, LinearMap.coe_mk, AddHom.coe_mk, observation,
    Matrix.mulVec_mulVec] using hd

omit [Fintype I] in
/-- Cayley–Hamilton turns the finite blindness test into every discrete derivative order. -/
theorem finite_powers_iff_all (readout : Matrix I S ℝ) (generator : Matrix S S ℝ)
    (direction : S → ℝ) :
    (∀ time < Fintype.card S, readout *ᵥ (generator ^ time) *ᵥ direction = 0) ↔
      ∀ time : ℕ, readout *ᵥ (generator ^ time) *ᵥ direction = 0 := by
  constructor
  · intro hfinite time
    rw [power_remainder generator time, Matrix.sum_mulVec, Matrix.mulVec_sum]
    apply Finset.sum_eq_zero
    intro earlier hearlier
    rw [Matrix.smul_mulVec, Matrix.mulVec_smul,
      hfinite earlier (Finset.mem_range.mp hearlier), smul_zero]
  · intro hall time _
    exact hall time

omit [Nonempty S] [Fintype I] in
/-- Vanishing power observations annihilate the convergent matrix exponential series. -/
theorem observation_zero_of_powers (readout : Matrix I S ℝ) (generator : Matrix S S ℝ)
    (direction : S → ℝ)
    (hblind : ∀ order : ℕ, readout *ᵥ (generator ^ order) *ᵥ direction = 0) (time : ℝ) :
    observation readout generator direction time = 0 := by
  let linear : Matrix S S ℝ →L[ℝ] (I → ℝ) :=
    LinearMap.toContinuousLinearMap (readoutLinear readout direction)
  have hs : Summable (fun order : ℕ ↦
      ((order.factorial : ℝ)⁻¹) • ((time • generator) ^ order)) :=
    NormedSpace.expSeries_summable' (time • generator)
  change linear (NormedSpace.exp ℝ (time • generator)) = 0
  rw [NormedSpace.exp_eq_tsum]
  dsimp only
  rw [linear.map_tsum hs]
  have hterm (order : ℕ) : linear
      (((order.factorial : ℝ)⁻¹) • ((time • generator) ^ order)) = 0 := by
    simp only [smul_pow, map_smul]
    have hz : linear (generator ^ order) = 0 := hblind order
    rw [hz, smul_zero, smul_zero]
  simp only [hterm, tsum_zero]

omit [Nonempty S] in
/-- A permanently zero observation has every derivative order equal to zero. -/
theorem powers_zero_of_observation (readout : Matrix I S ℝ) (generator : Matrix S S ℝ)
    (direction : S → ℝ)
    (hblind : ∀ time : ℝ, observation readout generator direction time = 0) :
    ∀ order : ℕ, readout *ᵥ (generator ^ order) *ᵥ direction = 0 := by
  have hpowers : ∀ order : ℕ, ∀ time : ℝ,
      observation readout generator ((generator ^ order) *ᵥ direction) time = 0 := by
    intro order
    induction order with
    | zero => simpa using hblind
    | succ order ih =>
        intro time
        have hd := observation_hasDerivAt readout generator ((generator ^ order) *ᵥ direction) time
        have hfun : observation readout generator ((generator ^ order) *ᵥ direction) =
            fun _ ↦ (0 : I → ℝ) := funext ih
        rw [hfun] at hd
        have hz := hd.unique (hasDerivAt_const time (0 : I → ℝ))
        simpa only [pow_succ', ← Matrix.mulVec_mulVec] using hz
  intro order
  simpa [observation] using hpowers order 0

/-- The exact finite-dimensional permanent-blindness criterion in new report Theorem 11. -/
theorem permanent_blindness_iff (readout : Matrix I S ℝ) (generator : Matrix S S ℝ)
    (direction : S → ℝ) :
    (∀ time : ℝ, observation readout generator direction time = 0) ↔
      ∀ order < Fintype.card S, readout *ᵥ (generator ^ order) *ᵥ direction = 0 := by
  rw [finite_powers_iff_all]
  exact ⟨powers_zero_of_observation _ _ _, observation_zero_of_powers _ _ _⟩

end Descent.Portability.DynamicBlindness
