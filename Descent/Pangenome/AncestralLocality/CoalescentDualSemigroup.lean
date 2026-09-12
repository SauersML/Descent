/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.AncestralLocality.SamplingDuality
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Topology.Algebra.Module.FiniteDimension

assert_below Descent.PopGen Descent.Spectral Descent.Blindness Descent.Conditionals
assert_below Descent.Portability Descent.Decision Descent.Program

/-!
# The coalescent dual semigroup: the backward equation without decisions

Without decisions (`r = 0`) the forward generator (7.1) of the research note "Ancestral locality"
is the resampling generator of the neutral multi-type Wright-Fisher diffusion, and the backward
circuit of `Descent.Pangenome.AncestralLocality.SamplingDuality` only coalesces. Coalescence keeps
the arity of an observation, so the backward generator is a linear operator
`L_c f = c ∑_{a<b} (C_ab f - f)` on the finite-dimensional space `(Fin n → H) → ℝ`
(`coalescenceOperator`). It has an exact exponential `S_t = e^{t L_c}` (`dualSemigroup`), which
is a semigroup (`dualSemigroup_zero`, `dualSemigroup_add`) and moves every observation along the
generator (`hasDerivAt_dualSemigroup_apply`).

The sampling functional `f ↦ H_f(p)` (`samplingFunctional`) turns `L_c` into the resampling
generator: on a vector of total mass one, `H_{L_c f}(p) = resamplingGenerator c H_f (p)`
(`samplingFunctional_coalescenceOperator`), which is Theorem 6 for `r = 0` as an operator
identity. Along the semigroup this is the backward equation: `t ↦ H_{S_t f}(p)` has derivative
`resamplingGenerator c H_{S_t f} (p)` (`hasDerivAt_samplingObservable_dualSemigroup`), with
`H_{S_0 f}(p) = H_f(p)` (`samplingObservable_dualSemigroup_zero`). So `u(t, p) = H_{S_t f}(p)`,
the right-hand side `E_f[H_{f_t}(p)]` of the note's (7.5), solves `∂_t u = L u` on the simplex.

Scope. Only the pure-resampling case `r = 0` is treated. Decision branching raises the arity, the
span of sampling observables of bounded arity is not closed under it, and no finite-dimensional
exponential exists for the full circuit. The forward diffusion on `P(H)` is not constructed, so
the identification of `H_{S_t f}(p)` with `E_p[H_f(P_t)]`, which needs uniqueness for the forward
equation, is not proved.

## Empirical status

None. The bodies here are linear operators and their exponentials over a supplied state space,
rate and vector, so no measurement can bear on them.
-/

namespace Descent.Pangenome.AncestralLocality

open Finset

variable {H : Type*} [Fintype H] [DecidableEq H] {n : ℕ}

/-! ### The coalescence generator as an operator -/

/-- **The sampling functional** `f ↦ H_f(p)` at a vector `p`. -/
def samplingFunctional (p : H → ℝ) : ((Fin n → H) → ℝ) →ₗ[ℝ] ℝ where
  toFun f := samplingObservable f p
  map_add' f g := by
    simp only [samplingObservable, Pi.add_apply, add_mul, sum_add_distrib]
  map_smul' d f := by
    simp only [samplingObservable, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_sum,
      mul_assoc]

/-- The sampling functional is the sampling observable. -/
theorem samplingFunctional_apply (p : H → ℝ) (f : (Fin n → H) → ℝ) :
    samplingFunctional p f = samplingObservable f p :=
  rfl

/-- **The coalescence generator on observations of arity `n`**, `L_c f = c ∑_{a<b} (C_ab f - f)`:
the backward circuit with no decisions, as a linear operator. -/
def coalescenceOperator (c : ℝ) : ((Fin n → H) → ℝ) →ₗ[ℝ] ((Fin n → H) → ℝ) where
  toFun f := c • ∑ b, ∑ a ∈ Iio b, (coalesceArguments a b f - f)
  map_add' f g := by
    have hadd : ∀ a b : Fin n, coalesceArguments a b (f + g) =
        coalesceArguments a b f + coalesceArguments a b g := fun _ _ ↦ rfl
    simp only [hadd, add_sub_add_comm, sum_add_distrib, smul_add]
  map_smul' d f := by
    have hsmul : ∀ a b : Fin n, coalesceArguments a b (d • f) = d • coalesceArguments a b f :=
      fun _ _ ↦ rfl
    simp only [hsmul, ← smul_sub, ← smul_sum, RingHom.id_apply, smul_comm c d]

/-- The coalescence generator applied to an observation. -/
theorem coalescenceOperator_apply (c : ℝ) (f : (Fin n → H) → ℝ) :
    coalescenceOperator c f = c • ∑ b, ∑ a ∈ Iio b, (coalesceArguments a b f - f) :=
  rfl

/-- **Theorem 6 without decisions, as an operator identity.** On a vector of total mass one the
sampling functional turns the coalescence generator into the resampling generator (7.1):
`H_{L_c f}(p) = resamplingGenerator c H_f (p)`. -/
theorem samplingFunctional_coalescenceOperator (c : ℝ) (f : (Fin n → H) → ℝ) {p : H → ℝ}
    (hp : ∑ h, p h = 1) :
    samplingFunctional p (coalescenceOperator c f) =
      resamplingGenerator c (samplingObservable f) p := by
  rw [resamplingGenerator_samplingObservable c f hp, coalescenceOperator_apply]
  simp only [map_smul, map_sum, map_sub, smul_eq_mul, samplingFunctional_apply]

/-! ### The dual semigroup -/

/-- **The dual semigroup `S_t = e^{t L_c}`** of the coalescence generator, on the
finite-dimensional space of observations of arity `n`. -/
noncomputable def dualSemigroup (c t : ℝ) : ((Fin n → H) → ℝ) →L[ℝ] ((Fin n → H) → ℝ) :=
  NormedSpace.exp ℝ (t • LinearMap.toContinuousLinearMap (coalescenceOperator c))

/-- The semigroup starts at the identity. -/
theorem dualSemigroup_zero (c : ℝ) : dualSemigroup (H := H) (n := n) c 0 = 1 := by
  rw [dualSemigroup, zero_smul, NormedSpace.exp_zero]

/-- **The semigroup law** `S_{s+t} = S_s S_t`. -/
theorem dualSemigroup_add (c s t : ℝ) :
    dualSemigroup (H := H) (n := n) c (s + t) = dualSemigroup c s * dualSemigroup c t := by
  have hcomm : Commute
      (s • LinearMap.toContinuousLinearMap (coalescenceOperator (H := H) (n := n) c))
      (t • LinearMap.toContinuousLinearMap (coalescenceOperator (H := H) (n := n) c)) := by
    show s • _ * t • _ = t • _ * s • _
    rw [smul_mul_smul_comm, smul_mul_smul_comm, mul_comm s t]
  rw [dualSemigroup, dualSemigroup, dualSemigroup, add_smul, NormedSpace.exp_add_of_commute hcomm]

/-- **The semigroup moves an observation along the coalescence generator**,
`d/dt S_t f = L_c S_t f`. -/
theorem hasDerivAt_dualSemigroup_apply (c t : ℝ) (f : (Fin n → H) → ℝ) :
    HasDerivAt (fun s ↦ dualSemigroup c s f) (coalescenceOperator c (dualSemigroup c t f)) t := by
  have h := (hasDerivAt_exp_smul_const' (LinearMap.toContinuousLinearMap
    (coalescenceOperator (H := H) (n := n) c)) t).clm_apply (hasDerivAt_const (x := t) (c := f))
  rw [ContinuousLinearMap.map_zero, add_zero] at h
  exact h

/-- The dual semigroup at time zero leaves every sampling observable unchanged. -/
theorem samplingObservable_dualSemigroup_zero (c : ℝ) (f : (Fin n → H) → ℝ) (p : H → ℝ) :
    samplingObservable (dualSemigroup c 0 f) p = samplingObservable f p := by
  rw [dualSemigroup_zero, ContinuousLinearMap.one_apply]

/-- **The backward equation (7.5) without decisions.** On a vector of total mass one,
`t ↦ H_{S_t f}(p)` has derivative `resamplingGenerator c H_{S_t f} (p)`: the dual semigroup solves
the backward equation of the neutral multi-type diffusion, observable by observable. -/
theorem hasDerivAt_samplingObservable_dualSemigroup (c t : ℝ) (f : (Fin n → H) → ℝ)
    {p : H → ℝ} (hp : ∑ h, p h = 1) :
    HasDerivAt (fun s ↦ samplingObservable (dualSemigroup c s f) p)
      (resamplingGenerator c (samplingObservable (dualSemigroup c t f)) p) t := by
  rw [← samplingFunctional_coalescenceOperator c _ hp]
  exact HasFDerivAt.comp_hasDerivAt
    (hl := (LinearMap.toContinuousLinearMap (samplingFunctional (n := n) p)).hasFDerivAt)
    (hf := hasDerivAt_dualSemigroup_apply c t f)

end Descent.Pangenome.AncestralLocality
