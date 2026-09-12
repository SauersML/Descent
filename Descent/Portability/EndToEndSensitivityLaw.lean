/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.EndToEndPortabilityLaw
import Descent.Portability.MechanismReportDerivative
import Descent.Portability.TwoLocusPortabilityDecay
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.MeasureTheory.Integral.DominatedConvergence

assert_below Descent.Decision Descent.Program

/-!
# The exact sensitivity of a history propagator to a demographic parameter

`EndToEndPortabilityLaw` writes every expected metric numerator and denominator of a score as a
coefficient vector dotted with `U · H_K(x₀)`, where `U` is the chronological product of epoch
exponentials `e^{τQ}` and pulse substitution kernels.  `EndToEndPortabilityLipschitz` bounds how
far `U` moves when the rates move.  This module computes the exact derivative instead.

The epoch.  If the generator `Q(θ)` of an epoch has derivative `Q'` at `θ₀`, the propagator
`e^{τQ(θ)}` has derivative `∫₀^τ e^{sQ} Q' e^{(τ - s)Q} ds` there (`duhamelDerivative`,
`hasDerivAt_matrixExponential_of_hasDerivAt`, entrywise `hasDerivAt_matrixExponential_apply`).
The proof is Duhamel's formula along the path: `e^{tA} - e^{tB}` is the integral of
`e^{sA} (A - B) e^{(t - s)B}` by the fundamental theorem of calculus
(`exp_smul_sub_exp_smul_eq_integral`), so the slope of the propagator is a parametric integral
of the generator slope, continuous in the pair (generator, slope), and the derivative is its value
at `(Q(θ₀), Q')`, a limit taken in coordinates (`hasDerivAt_exp_smul_apply`, then
`hasDerivAt_of_hasDerivAt_apply` and `hasDerivAt_apply`).  Mathlib has no Fréchet derivative of
the exponential of a noncommuting algebra at a general point; this is the substitute.  Paired
with a coefficient vector and a moment vector it reads `∫₀^τ (c e^{sQ}) · Q' · (e^{(τ - s)Q} v) ds`,
forward law times generator derivative times backward value (`dotProduct_duhamelDerivative_mulVec`).
When `Q'` commutes with `Q` it is `τ Q' e^{τQ}` (`duhamelDerivative_of_commute`), and for the
scalar decay generator `-r` it recovers `∂_r e^{-rT} = -T e^{-rT}` of
`TwoLocusPortabilityDecay.portabilityDecay` (`hasDerivAt_portabilityDecay_rate`).

The history.  A parametrized history is a list of event families `θ ↦ event`, epochs or pulses.
Its propagator `historyEventPropagator (history.map (· θ))` applied to a moment vector is the
backward value of `MechanismReportDerivative` for the stages `historyStage`, the latest event
first (`historyEventPropagator_mulVec_eq_backValue`, using `backValue_succ_eq` and
`backValue_congr`).  So TQ (6.4) applies unchanged: when every event propagator has derivative
`derivative event` at `θ₀`, `c · U(θ) v` has derivative the stagewise sum `historySensitivity` of
forward law, event derivative and backward value (`hasDerivAt_dotProduct_historyEventPropagator`).
An epoch whose dual generator is differentiable in `θ` supplies the Duhamel derivative
(`hasDerivAt_eventPropagator_epoch`); a fixed pulse supplies zero
(`hasDerivAt_eventPropagator_pulse`).

Scope.  The parameter enters through the event propagators: the dual generator of an epoch, or a
pulse kernel supplied with its derivative.  Durations are fixed.  That the dual generator is
differentiable in a rate coordinate is a hypothesis here, as continuity is in
`NeutralRateHistoryKernel`; its entries are finite sums of rate coordinates, but that linearity is
not proved.  The derivative of the propagator of a time-varying rate path, a variation of constants
for the fundamental matrix, is not covered.

## Empirical status

None.  The bodies here are derivatives and integrals of matrix exponentials of supplied
generators and finite products of supplied matrices, so no measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.EndToEndSensitivityLaw

open Descent.Coalescent PartialHaplotypeDualGenerator PartialHaplotypeDualSemigroup
  PartialHaplotypePulseKernel NeutralPulseHistoryKernel MechanismReportDerivative
  TwoLocusPortabilityDecay
open scoped Matrix NNReal

noncomputable section

/-! ## Duhamel's formula along a parameter -/

section Duhamel

open scoped Matrix.Norms.Operator

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `s ↦ e^{sA} M e^{(t - s)B}` is continuous. -/
theorem continuous_exp_smul_mul_exp_smul (A M B : Matrix ι ι ℝ) (t : ℝ) :
    Continuous fun s : ℝ ↦
      NormedSpace.exp ℝ (s • A) * M * NormedSpace.exp ℝ ((t - s) • B) :=
  (((NormedSpace.exp_continuous (𝕂 := ℝ)).comp (continuous_id.smul continuous_const)).mul
    continuous_const).mul
    ((NormedSpace.exp_continuous (𝕂 := ℝ)).comp
      ((continuous_const.sub continuous_id).smul continuous_const))

/-- Along `s ↦ e^{sA} e^{(t - s)B}` the derivative is `e^{sA} (A - B) e^{(t - s)B}`. -/
theorem hasDerivAt_exp_smul_mul_exp_smul (A B : Matrix ι ι ℝ) (t s : ℝ) :
    HasDerivAt (fun u ↦ NormedSpace.exp ℝ (u • A) * NormedSpace.exp ℝ ((t - u) • B))
      (NormedSpace.exp ℝ (s • A) * (A - B) * NormedSpace.exp ℝ ((t - s) • B)) s := by
  have hleft := hasDerivAt_exp_smul_const (𝕂 := ℝ) A s
  have hright : HasDerivAt (fun u ↦ NormedSpace.exp ℝ ((t - u) • B))
      ((-1 : ℝ) • (B * NormedSpace.exp ℝ ((t - s) • B))) s :=
    HasDerivAt.scomp (x := s) (hasDerivAt_exp_smul_const' (𝕂 := ℝ) B (t - s))
      ((hasDerivAt_id (x := s)).const_sub t)
  refine (hleft.fun_mul hright).congr_deriv ?_
  simp only [neg_one_smul]
  noncomm_ring

/-- **Duhamel's formula for a change of generator.**  `e^{tA} - e^{tB}` is the integral over
`s ∈ [0, t]` of `e^{sA} (A - B) e^{(t - s)B}`. -/
theorem exp_smul_sub_exp_smul_eq_integral (A B : Matrix ι ι ℝ) (t : ℝ) :
    NormedSpace.exp ℝ (t • A) - NormedSpace.exp ℝ (t • B)
      = ∫ s in (0 : ℝ)..t,
          NormedSpace.exp ℝ (s • A) * (A - B) * NormedSpace.exp ℝ ((t - s) • B) := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s _ ↦ hasDerivAt_exp_smul_mul_exp_smul A B t s)
    ((continuous_exp_smul_mul_exp_smul A (A - B) B t).intervalIntegrable 0 t)]
  simp only [sub_self, zero_smul, sub_zero, NormedSpace.exp_zero, mul_one, one_mul]

/-- The Duhamel integral `∫₀^τ e^{sM} N e^{(τ - s)B} ds` is continuous in the pair `(M, N)`. -/
theorem continuous_duhamelIntegral (B : Matrix ι ι ℝ) (τ : ℝ) :
    Continuous fun p : Matrix ι ι ℝ × Matrix ι ι ℝ ↦
      ∫ s in (0 : ℝ)..τ, NormedSpace.exp ℝ (s • p.1) * p.2 * NormedSpace.exp ℝ ((τ - s) • B) := by
  have hjoint : Continuous fun q : (Matrix ι ι ℝ × Matrix ι ι ℝ) × ℝ ↦
      NormedSpace.exp ℝ (q.2 • q.1.1) * q.1.2 * NormedSpace.exp ℝ ((τ - q.2) • B) :=
    (((NormedSpace.exp_continuous (𝕂 := ℝ)).comp (continuous_snd.smul continuous_fst.fst)).mul
      continuous_fst.snd).mul
      ((NormedSpace.exp_continuous (𝕂 := ℝ)).comp
        ((continuous_const.sub continuous_snd).smul continuous_const))
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (f := fun (p : Matrix ι ι ℝ × Matrix ι ι ℝ) (s : ℝ) ↦
      NormedSpace.exp ℝ (s • p.1) * p.2 * NormedSpace.exp ℝ ((τ - s) • B))
    hjoint 0 τ

/-- Each coordinate of the Duhamel integral is continuous in the coordinates of `M` and `N`. -/
theorem continuous_duhamelIntegral_apply (B : Matrix ι ι ℝ) (τ : ℝ) (i j : ι) :
    Continuous fun p : (ι → ι → ℝ) × (ι → ι → ℝ) ↦
      (∫ s in (0 : ℝ)..τ, NormedSpace.exp ℝ (s • Matrix.of p.1) * Matrix.of p.2
        * NormedSpace.exp ℝ ((τ - s) • B)) i j := by
  have hentry := LinearMap.continuous_of_finiteDimensional
    ({ toFun := fun N ↦ N i j, map_add' := fun _ _ ↦ rfl, map_smul' := fun _ _ ↦ rfl } :
      Matrix ι ι ℝ →ₗ[ℝ] ℝ)
  have hof := LinearMap.continuous_of_finiteDimensional
    ({ toFun := fun p ↦ Matrix.of p, map_add' := fun _ _ ↦ rfl, map_smul' := fun _ _ ↦ rfl } :
      (ι → ι → ℝ) →ₗ[ℝ] Matrix ι ι ℝ)
  exact hentry.comp ((continuous_duhamelIntegral B τ).comp
    ((hof.comp continuous_fst).prodMk (hof.comp continuous_snd)))

omit [Fintype ι] [DecidableEq ι] in
/-- The coordinates of a generator path and of its slope converge together at a point where
every coordinate of the path is differentiable. -/
theorem tendsto_coordinates_slope {Q : ℝ → Matrix ι ι ℝ} {Q' : Matrix ι ι ℝ} {θ₀ : ℝ}
    (hQ : ∀ k l, HasDerivAt (fun θ ↦ Q θ k l) (Q' k l) θ₀) :
    Filter.Tendsto
      (fun θ ↦ ((fun k l ↦ Q θ k l : ι → ι → ℝ), (fun k l ↦ slope Q θ₀ θ k l : ι → ι → ℝ)))
      (nhdsWithin θ₀ {θ₀}ᶜ)
      (nhds ((fun k l ↦ Q θ₀ k l : ι → ι → ℝ), (fun k l ↦ Q' k l : ι → ι → ℝ))) :=
  (tendsto_pi_nhds.mpr fun k ↦ tendsto_pi_nhds.mpr fun l ↦
      (hQ k l).continuousAt.tendsto.mono_left nhdsWithin_le_nhds).prodMk_nhds
    (tendsto_pi_nhds.mpr fun k ↦ tendsto_pi_nhds.mpr fun l ↦
      hasDerivAt_iff_tendsto_slope.mp (hQ k l))

/-- **The slope of a propagator is a Duhamel integral of the generator slope.** -/
theorem slope_exp_smul_eq_integral (Q : ℝ → Matrix ι ι ℝ) (τ θ₀ θ : ℝ) :
    slope (fun θ ↦ NormedSpace.exp ℝ (τ • Q θ)) θ₀ θ
      = ∫ s in (0 : ℝ)..τ, NormedSpace.exp ℝ (s • Q θ) * slope Q θ₀ θ
          * NormedSpace.exp ℝ ((τ - s) • Q θ₀) := by
  simp only [slope, vsub_eq_sub]
  rw [exp_smul_sub_exp_smul_eq_integral, ← intervalIntegral.integral_smul]
  refine intervalIntegral.integral_congr fun s _ ↦ ?_
  simp only [mul_smul_comm, smul_mul_assoc]

/-- **Duhamel's formula for the derivative of a propagator in a parameter, entrywise.**  If every
entry of the generator path `Q` has derivative `Q' k l` at `θ₀`, then every entry of
`θ ↦ e^{τQ(θ)}` has as derivative at `θ₀` the corresponding entry of
`∫₀^τ e^{sQ(θ₀)} Q' e^{(τ - s)Q(θ₀)} ds`.  The limit is taken in the coordinates of the generator
and of its slope, so that only coordinate and real topologies meet. -/
theorem hasDerivAt_exp_smul_apply {Q : ℝ → Matrix ι ι ℝ} {Q' : Matrix ι ι ℝ} {θ₀ : ℝ}
    (hQ : ∀ k l, HasDerivAt (fun θ ↦ Q θ k l) (Q' k l) θ₀) (τ : ℝ) (i j : ι) :
    HasDerivAt (fun θ ↦ NormedSpace.exp ℝ (τ • Q θ) i j)
      ((∫ s in (0 : ℝ)..τ,
        NormedSpace.exp ℝ (s • Q θ₀) * Q' * NormedSpace.exp ℝ ((τ - s) • Q θ₀)) i j) θ₀ := by
  rw [hasDerivAt_iff_tendsto_slope]
  exact (((continuous_duhamelIntegral_apply (Q θ₀) τ i j).tendsto _).comp
    (tendsto_coordinates_slope hQ)).congr fun θ ↦
      (congrFun (congrFun (slope_exp_smul_eq_integral Q τ θ₀ θ) i) j).symm

/-- A matrix path whose entries are differentiable is differentiable. -/
theorem hasDerivAt_of_hasDerivAt_apply {Q : ℝ → Matrix ι ι ℝ} {Q' : Matrix ι ι ℝ} {θ₀ : ℝ}
    (hQ : ∀ i j, HasDerivAt (fun θ ↦ Q θ i j) (Q' i j) θ₀) : HasDerivAt Q Q' θ₀ := by
  have hentry : ∀ i j, HasDerivAt (fun θ ↦ Matrix.single i j (Q θ i j))
      (Matrix.single i j (Q' i j)) θ₀ := by
    intro i j
    simpa only [Matrix.smul_single, smul_eq_mul, mul_one] using
      (hQ i j).smul_const (Matrix.single i j (1 : ℝ))
  have hsum : HasDerivAt (fun θ ↦ ∑ i, ∑ j, Matrix.single i j (Q θ i j))
      (∑ i, ∑ j, Matrix.single i j (Q' i j)) θ₀ :=
    HasDerivAt.fun_sum fun i _ ↦ HasDerivAt.fun_sum fun j _ ↦ hentry i j
  exact (hsum.congr_deriv (Matrix.matrix_eq_sum_single Q').symm).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun θ ↦ Matrix.matrix_eq_sum_single (Q θ))

omit [DecidableEq ι] in
/-- A differentiable matrix path has differentiable entries. -/
theorem hasDerivAt_apply {M : ℝ → Matrix ι ι ℝ} {M' : Matrix ι ι ℝ} {θ₀ : ℝ}
    (hM : HasDerivAt M M' θ₀) (i j : ι) : HasDerivAt (fun θ ↦ M θ i j) (M' i j) θ₀ :=
  (LinearMap.toContinuousLinearMap
    ({ toFun := fun N ↦ N i j, map_add' := fun _ _ ↦ rfl, map_smul' := fun _ _ ↦ rfl } :
      Matrix ι ι ℝ →ₗ[ℝ] ℝ)).hasFDerivAt.comp_hasDerivAt θ₀ hM

/-- **The Duhamel derivative** of the propagator `e^{τQ}` in the generator direction `Q'`:
`∫₀^τ e^{sQ} Q' e^{(τ - s)Q} ds`. -/
def duhamelDerivative (Q Q' : Matrix ι ι ℝ) (τ : ℝ) : Matrix ι ι ℝ :=
  ∫ s in (0 : ℝ)..τ, matrixExponential Q s * Q' * matrixExponential Q (τ - s)

/-- **The propagator derivative, entrywise.**  If every generator entry is differentiable at `θ₀`,
every propagator entry is, with the entries of the Duhamel derivative as derivatives. -/
theorem hasDerivAt_matrixExponential_apply {Q : ℝ → Matrix ι ι ℝ} {Q' : Matrix ι ι ℝ} {θ₀ : ℝ}
    (hQ : ∀ i j, HasDerivAt (fun θ ↦ Q θ i j) (Q' i j) θ₀) (τ : ℝ) (i j : ι) :
    HasDerivAt (fun θ ↦ matrixExponential (Q θ) τ i j) (duhamelDerivative (Q θ₀) Q' τ i j) θ₀ := by
  simp only [matrixExponential_eq_normedSpace_exp, duhamelDerivative]
  exact hasDerivAt_exp_smul_apply hQ τ i j

/-- **The propagator derivative in corpus form.**  If the generator path `Q` has derivative `Q'`
at `θ₀`, the exact propagator `matrixExponential (Q θ) τ` has derivative
`duhamelDerivative (Q θ₀) Q' τ` there. -/
theorem hasDerivAt_matrixExponential_of_hasDerivAt {Q : ℝ → Matrix ι ι ℝ} {Q' : Matrix ι ι ℝ}
    {θ₀ : ℝ} (hQ : HasDerivAt Q Q' θ₀) (τ : ℝ) :
    HasDerivAt (fun θ ↦ matrixExponential (Q θ) τ) (duhamelDerivative (Q θ₀) Q' τ) θ₀ :=
  hasDerivAt_of_hasDerivAt_apply fun i j ↦
    hasDerivAt_matrixExponential_apply (hasDerivAt_apply hQ) τ i j

/-- **The Duhamel derivative as forward law, generator derivative and backward value.**  Paired
with a coefficient vector `c` and a moment vector `v` it is the integral over the epoch of the
forward law `c e^{sQ}` against `Q'` applied to the backward value `e^{(τ - s)Q} v`. -/
theorem dotProduct_duhamelDerivative_mulVec (Q Q' : Matrix ι ι ℝ) (τ : ℝ) (c v : ι → ℝ) :
    c ⬝ᵥ (duhamelDerivative Q Q' τ *ᵥ v)
      = ∫ s in (0 : ℝ)..τ,
          (c ᵥ* matrixExponential Q s) ⬝ᵥ (Q' *ᵥ (matrixExponential Q (τ - s) *ᵥ v)) := by
  let pairing : Matrix ι ι ℝ →ₗ[ℝ] ℝ :=
    { toFun := fun N ↦ c ⬝ᵥ (N *ᵥ v)
      map_add' := fun N₁ N₂ ↦ by simp only [Matrix.add_mulVec, dotProduct_add]
      map_smul' := fun r N ↦ by
        simp only [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, RingHom.id_apply] }
  have hcontinuous : Continuous fun s : ℝ ↦
      matrixExponential Q s * Q' * matrixExponential Q (τ - s) := by
    simp only [matrixExponential_eq_normedSpace_exp]
    exact continuous_exp_smul_mul_exp_smul Q Q' Q τ
  have hcomm := (LinearMap.toContinuousLinearMap pairing).intervalIntegral_comp_comm
    (hcontinuous.intervalIntegrable (μ := MeasureTheory.volume) 0 τ)
  have hpoint : ∀ s : ℝ,
      c ⬝ᵥ ((matrixExponential Q s * Q' * matrixExponential Q (τ - s)) *ᵥ v)
        = (c ᵥ* matrixExponential Q s) ⬝ᵥ (Q' *ᵥ (matrixExponential Q (τ - s) *ᵥ v)) := by
    intro s
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec]
  calc c ⬝ᵥ (duhamelDerivative Q Q' τ *ᵥ v)
      = LinearMap.toContinuousLinearMap pairing (duhamelDerivative Q Q' τ) := rfl
    _ = ∫ s in (0 : ℝ)..τ, LinearMap.toContinuousLinearMap pairing
          (matrixExponential Q s * Q' * matrixExponential Q (τ - s)) := hcomm.symm
    _ = _ := intervalIntegral.integral_congr fun s _ ↦ hpoint s

/-- **The commuting case.**  When the generator derivative commutes with the generator, the
Duhamel derivative is `τ Q' e^{τQ}`. -/
theorem duhamelDerivative_of_commute {Q Q' : Matrix ι ι ℝ} (hcommute : Commute Q Q') (τ : ℝ) :
    duhamelDerivative Q Q' τ = τ • (Q' * matrixExponential Q τ) := by
  have hpoint : ∀ s : ℝ, matrixExponential Q s * Q' * matrixExponential Q (τ - s)
      = Q' * matrixExponential Q τ := by
    intro s
    have hleft : Commute (NormedSpace.exp ℝ (s • Q)) Q' := (hcommute.smul_left s).exp_left ℝ
    have hsum : s • Q + (τ - s) • Q = τ • Q := by
      rw [← add_smul]
      congr 1
      ring
    have hsplit : NormedSpace.exp ℝ (τ • Q)
        = NormedSpace.exp ℝ (s • Q) * NormedSpace.exp ℝ ((τ - s) • Q) := by
      rw [← NormedSpace.exp_add_of_commute (((Commute.refl Q).smul_left s).smul_right (τ - s)),
        hsum]
    simp only [matrixExponential_eq_normedSpace_exp]
    rw [hleft.eq, mul_assoc, ← hsplit]
  have hconstant : ∫ s in (0 : ℝ)..τ, matrixExponential Q s * Q' * matrixExponential Q (τ - s)
      = ∫ _ in (0 : ℝ)..τ, Q' * matrixExponential Q τ :=
    intervalIntegral.integral_congr fun s _ ↦ hpoint s
  rw [duhamelDerivative, hconstant, intervalIntegral.integral_const, sub_zero]

/-- The exponential of the scalar generator `-r` at time `τ` is `e^{-rτ}` times the identity. -/
theorem matrixExponential_neg_smul_one (r τ : ℝ) :
    matrixExponential (-r • (1 : Matrix ι ι ℝ)) τ = portabilityDecay r τ • 1 := by
  have hscalar : τ • (-r • (1 : Matrix ι ι ℝ)) = algebraMap ℝ (Matrix ι ι ℝ) (-(r * τ)) := by
    rw [Algebra.algebraMap_eq_smul_one, smul_smul]
    congr 1
    ring
  have hexp : NormedSpace.exp ℝ (algebraMap ℝ (Matrix ι ι ℝ) (-(r * τ)))
      = algebraMap ℝ (Matrix ι ι ℝ) (Real.exp (-(r * τ))) := by
    rw [Real.exp_eq_exp_ℝ]
    exact (NormedSpace.algebraMap_exp_comm (𝕂 := ℝ) (-(r * τ))).symm
  rw [matrixExponential_eq_normedSpace_exp, hscalar, hexp, Algebra.algebraMap_eq_smul_one,
    portabilityDecay]

/-- **Agreement with the two-locus decay law.**  The Duhamel law for the scalar generator `-r`,
whose derivative `-1` commutes with it, recovers `∂_r e^{-rT} = -T e^{-rT}` for the closed-form
portability decay of `TwoLocusPortabilityDecay`. -/
theorem hasDerivAt_portabilityDecay_rate (τ r₀ : ℝ) :
    HasDerivAt (fun r ↦ portabilityDecay r τ) (-τ * portabilityDecay r₀ τ) r₀ := by
  have hpath : HasDerivAt (fun r : ℝ ↦ -r • (1 : Matrix Unit Unit ℝ)) (-1) r₀ := by
    simpa only [neg_one_smul, id_eq] using
      (hasDerivAt_id r₀).neg.smul_const (1 : Matrix Unit Unit ℝ)
  have hlaw := hasDerivAt_apply (hasDerivAt_matrixExponential_of_hasDerivAt hpath τ) () ()
  have hfun : ∀ r : ℝ,
      portabilityDecay r τ = matrixExponential (-r • (1 : Matrix Unit Unit ℝ)) τ () () := by
    intro r
    rw [matrixExponential_neg_smul_one, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul,
      mul_one]
  have hvalue : -τ * portabilityDecay r₀ τ
      = duhamelDerivative (-r₀ • (1 : Matrix Unit Unit ℝ)) (-1) τ () () := by
    rw [duhamelDerivative_of_commute (Commute.one_right _).neg_right,
      matrixExponential_neg_smul_one]
    simp only [Matrix.smul_apply, Matrix.neg_apply, Matrix.one_apply_eq, smul_eq_mul,
      neg_one_mul, mul_one]
    ring
  exact (hlaw.congr_deriv hvalue.symm).congr_of_eventuallyEq
    (Filter.Eventually.of_forall hfun)

end Duhamel

/-! ## The stagewise derivative along a history -/

section Stages

variable {S : Type*} [Fintype S]

/-- One more stage at the end of a backward value is one more transition applied to the
terminal value. -/
theorem backValue_succ_eq (kernel : ℕ → ℝ → Matrix S S ℝ) (terminal : S → ℝ) (θ : ℝ) :
    ∀ (remaining stage : ℕ), backValue kernel terminal stage (remaining + 1) θ
      = backValue kernel (kernel (stage + remaining) θ *ᵥ terminal) stage remaining θ := by
  intro remaining
  induction remaining with
  | zero => intro stage; rfl
  | succ remaining ih =>
    intro stage
    show kernel stage θ *ᵥ backValue kernel terminal (stage + 1) (remaining + 1) θ
      = kernel stage θ *ᵥ
          backValue kernel (kernel (stage + (remaining + 1)) θ *ᵥ terminal) (stage + 1) remaining θ
    rw [ih (stage + 1), show stage + 1 + remaining = stage + (remaining + 1) by omega]

/-- A backward value reads the kernel only at the stages it runs through. -/
theorem backValue_congr {first second : ℕ → ℝ → Matrix S S ℝ} (terminal : S → ℝ) (θ : ℝ) :
    ∀ (remaining stage : ℕ),
      (∀ k, stage ≤ k → k < stage + remaining → first k θ = second k θ) →
      backValue first terminal stage remaining θ = backValue second terminal stage remaining θ := by
  intro remaining
  induction remaining with
  | zero => intro stage _; rfl
  | succ remaining ih =>
    intro stage hagree
    show first stage θ *ᵥ backValue first terminal (stage + 1) remaining θ
      = second stage θ *ᵥ backValue second terminal (stage + 1) remaining θ
    rw [hagree stage le_rfl (by omega),
      ih (stage + 1) fun k hk hk' ↦ hagree k (by omega) (by omega)]

end Stages

section History

variable {Deme Locus : Type*} {Allele : Locus → Type*}
variable [Fintype Deme] [DecidableEq Deme] [Fintype Locus] [DecidableEq Locus]
  [∀ ℓ, Fintype (Allele ℓ)] [∀ ℓ, DecidableEq (Allele ℓ)]

/-- **The stages of a parametrized history** around the base parameter `θ₀`, latest event
first: stage `k` at `θ` is the moment matrix at `θ + θ₀` of the event `k` places before the end,
and stages before the start of the history are the identity. -/
def historyStage (capacity : Locus → ℕ) (θ₀ : ℝ) :
    List (ℝ → ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme)) → ℕ → ℝ →
      Matrix (BudgetConfiguration Deme Locus Allele capacity)
        (BudgetConfiguration Deme Locus Allele capacity) ℝ
  | [], _, _ => 1
  | event :: rest, k, θ =>
      if k = rest.length then eventPropagator capacity (event (θ + θ₀))
      else historyStage capacity θ₀ rest k θ

/-- The derivatives of the stages of a parametrized history, latest event first, from a
derivative matrix for each event family. -/
def historyStageDerivative (capacity : Locus → ℕ)
    (derivative : (ℝ → ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme)) →
      Matrix (BudgetConfiguration Deme Locus Allele capacity)
        (BudgetConfiguration Deme Locus Allele capacity) ℝ) :
    List (ℝ → ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme)) → ℕ →
      Matrix (BudgetConfiguration Deme Locus Allele capacity)
        (BudgetConfiguration Deme Locus Allele capacity) ℝ
  | [], _ => 0
  | event :: rest, k =>
      if k = rest.length then derivative event
      else historyStageDerivative capacity derivative rest k

/-- Every stage of a parametrized history is differentiable at the base parameter when every
event propagator is. -/
theorem hasDerivAt_historyStage (capacity : Locus → ℕ) {θ₀ : ℝ}
    (derivative : (ℝ → ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme)) →
      Matrix (BudgetConfiguration Deme Locus Allele capacity)
        (BudgetConfiguration Deme Locus Allele capacity) ℝ) :
    ∀ history : List (ℝ → ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme)),
      (∀ event ∈ history, ∀ ξ η,
        HasDerivAt (fun θ ↦ eventPropagator capacity (event θ) ξ η) (derivative event ξ η) θ₀) →
      ∀ k ξ η, HasDerivAt (fun θ ↦ historyStage capacity θ₀ history k θ ξ η)
        (historyStageDerivative capacity derivative history k ξ η) 0
  | [], _, k, ξ, η => by
    simp only [historyStage, historyStageDerivative, Matrix.zero_apply]
    exact hasDerivAt_const _ _
  | event :: rest, hderivative, k, ξ, η => by
    by_cases hk : k = rest.length
    · simp only [historyStage, historyStageDerivative, if_pos hk]
      have hevent := hderivative event (List.mem_cons.mpr (Or.inl rfl)) ξ η
      exact HasDerivAt.comp_add_const (f := fun θ ↦ eventPropagator capacity (event θ) ξ η)
        0 θ₀ (by rwa [zero_add])
    · simp only [historyStage, historyStageDerivative, if_neg hk]
      exact hasDerivAt_historyStage capacity derivative rest
        (fun e he ↦ hderivative e (List.mem_cons.mpr (Or.inr he))) k ξ η

/-- **The history propagator is a backward value.**  Applied to a moment vector, the propagator of
a parametrized history at `θ + θ₀` is the backward value of its stages at `θ`. -/
theorem historyEventPropagator_mulVec_eq_backValue (capacity : Locus → ℕ) (θ₀ θ : ℝ) :
    ∀ (history : List (ℝ → ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme)))
      (v : BudgetConfiguration Deme Locus Allele capacity → ℝ),
      historyEventPropagator capacity (history.map fun event ↦ event (θ + θ₀)) *ᵥ v
        = backValue (historyStage capacity θ₀ history) v 0 history.length θ
  | [], v => by
    simp only [List.map_nil, historyEventPropagator, List.length_nil, backValue,
      Matrix.one_mulVec]
  | event :: rest, v => by
    have hrest := historyEventPropagator_mulVec_eq_backValue capacity θ₀ θ rest
      (eventPropagator capacity (event (θ + θ₀)) *ᵥ v)
    have hlast : historyStage capacity θ₀ (event :: rest) rest.length θ
        = eventPropagator capacity (event (θ + θ₀)) := by
      simp [historyStage]
    have hagree : backValue (historyStage capacity θ₀ (event :: rest))
          (eventPropagator capacity (event (θ + θ₀)) *ᵥ v) 0 rest.length θ
        = backValue (historyStage capacity θ₀ rest)
          (eventPropagator capacity (event (θ + θ₀)) *ᵥ v) 0 rest.length θ :=
      backValue_congr _ θ rest.length 0 fun k _ hk ↦ by
        simp only [historyStage]
        exact if_neg (by omega)
    have hsplit : historyEventPropagator capacity ((event :: rest).map fun event ↦ event (θ + θ₀))
        = historyEventPropagator capacity (rest.map fun event ↦ event (θ + θ₀))
          * eventPropagator capacity (event (θ + θ₀)) := rfl
    rw [hsplit, ← Matrix.mulVec_mulVec, hrest, List.length_cons, backValue_succ_eq, zero_add,
      hlast, hagree]

/-- **The stagewise sensitivity of a history**: TQ (6.4) for the stages of a parametrized history
around `θ₀`, the sum over stages of the forward law of `c`, the event derivative there, and the
backward value of `v` afterwards. -/
def historySensitivity (capacity : Locus → ℕ) (θ₀ : ℝ)
    (history : List (ℝ → ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme)))
    (derivative : (ℝ → ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme)) →
      Matrix (BudgetConfiguration Deme Locus Allele capacity)
        (BudgetConfiguration Deme Locus Allele capacity) ℝ)
    (c v : BudgetConfiguration Deme Locus Allele capacity → ℝ) : ℝ :=
  ∑ step ∈ Finset.range history.length,
    (forwardLaw (historyStage capacity θ₀ history) c 0 step
        ᵥ* historyStageDerivative capacity derivative history (0 + step))
      ⬝ᵥ backValue (historyStage capacity θ₀ history) v (0 + step + 1)
        (history.length - (step + 1)) 0

/-- **The exact sensitivity law of a history of epochs, splits and pulses.**  If every event
propagator of a parametrized history has derivative `derivative event` at `θ₀`, then
`c · U(θ) v`, with `U(θ)` the chronological propagator of the history at `θ`, has derivative
`historySensitivity` at `θ₀`: the stagewise sum of forward law, event derivative and backward
value of `MechanismReportDerivative.mechanism_to_report_derivative`. -/
theorem hasDerivAt_dotProduct_historyEventPropagator (capacity : Locus → ℕ) {θ₀ : ℝ}
    (history : List (ℝ → ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme)))
    (derivative : (ℝ → ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme)) →
      Matrix (BudgetConfiguration Deme Locus Allele capacity)
        (BudgetConfiguration Deme Locus Allele capacity) ℝ)
    (hderivative : ∀ event ∈ history, ∀ ξ η,
      HasDerivAt (fun θ ↦ eventPropagator capacity (event θ) ξ η) (derivative event ξ η) θ₀)
    (c v : BudgetConfiguration Deme Locus Allele capacity → ℝ) :
    HasDerivAt
      (fun θ ↦ c ⬝ᵥ (historyEventPropagator capacity (history.map fun event ↦ event θ) *ᵥ v))
      (historySensitivity capacity θ₀ history derivative c v) θ₀ := by
  have hshifted := mechanism_to_report_derivative (historyStage capacity θ₀ history)
    (historyStageDerivative capacity derivative history) v c
    (hasDerivAt_historyStage capacity derivative history hderivative) history.length
  have hfun : (fun θ ↦ c ⬝ᵥ backValue (historyStage capacity θ₀ history) v 0 history.length θ)
      = fun θ ↦ c ⬝ᵥ
          (historyEventPropagator capacity (history.map fun event ↦ event (θ + θ₀)) *ᵥ v) := by
    funext θ
    rw [historyEventPropagator_mulVec_eq_backValue]
  rw [hfun] at hshifted
  have hback := HasDerivAt.comp_sub_const θ₀ θ₀ (by rwa [sub_self])
    (f := fun θ ↦ c ⬝ᵥ
      (historyEventPropagator capacity (history.map fun event ↦ event (θ + θ₀)) *ᵥ v))
  simpa only [sub_add_cancel] using hback

/-- An epoch whose dual generator is differentiable in the parameter has the Duhamel derivative
of its propagator. -/
theorem hasDerivAt_eventPropagator_epoch (capacity : Locus → ℕ)
    {rates : ℝ → NeutralRates Deme Locus Allele}
    {generatorDerivative : Matrix (BudgetConfiguration Deme Locus Allele capacity)
      (BudgetConfiguration Deme Locus Allele capacity) ℝ} {θ₀ : ℝ}
    (hrates : ∀ ξ η, HasDerivAt (fun θ ↦ dualGenerator (rates θ) capacity ξ η)
      (generatorDerivative ξ η) θ₀)
    (duration : ℝ≥0) (ξ η : BudgetConfiguration Deme Locus Allele capacity) :
    HasDerivAt (fun θ ↦ eventPropagator capacity
        (Sum.inl (rates θ, duration) : (NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme)
        ξ η)
      (duhamelDerivative (dualGenerator (rates θ₀) capacity) generatorDerivative duration ξ η)
      θ₀ :=
  hasDerivAt_matrixExponential_apply hrates duration ξ η

/-- A fixed pulse has derivative zero. -/
theorem hasDerivAt_eventPropagator_pulse (capacity : Locus → ℕ) (pulse : PulseMatrix Deme)
    (θ₀ : ℝ) (ξ η : BudgetConfiguration Deme Locus Allele capacity) :
    HasDerivAt (fun _ : ℝ ↦ eventPropagator capacity
        (Sum.inr pulse : (NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme) ξ η) 0 θ₀ :=
  hasDerivAt_const θ₀ _

end History

end

end Descent.Portability.EndToEndSensitivityLaw
