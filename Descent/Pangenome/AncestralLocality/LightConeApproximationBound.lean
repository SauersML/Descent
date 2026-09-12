/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.AncestralLocality.InfiniteGenomeLimit
import Descent.Pangenome.AncestralLocality.LocalityCouplingBounds
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Topology.ContinuousMap.Compact

assert_below Descent.PopGen Descent.Spectral Descent.Blindness Descent.Conditionals
assert_below Descent.Portability Descent.Decision Descent.Program

/-!
# The light-cone approximation bound for finite-genome truncations

`ANCESTRAL_LOCALITY.md` §10, Theorem 9. `InfiniteGenomeLimit` builds the infinite-genome semigroup
from an exhaustion satisfying `LightConeApproximation S A`, which it takes as a named hypothesis.
This module discharges that hypothesis for exhaustions represented through the sampling duality,
from the coupling of Corollary 8.1 and the escape bound (9.1) of Theorem 8.

Two bounded evaluations on one probability law that coincide off an escape set have integrals
within `2B` times the probability of escape (`abs_integral_sub_le_of_eqOn_compl`). That is the
error term `2 ‖f‖_∞ Pr(E_{ℓ,T})` of the proof of Theorem 9. The escape bound (9.1) grows with the
horizon (`escapeBound_mono_time`). Under the hypotheses listed below, the finite-genome operators
satisfy the approximation bound with the escape function `lightConeEscape`
(`norm_operator_sub_le_lightConeEscape`). Along an exhaustion whose radius grows without bound
they therefore form a `LightConeApproximation` (`LightConeApproximation.ofDuality`), from which
`InfiniteGenomeLimit` builds the limit.

The hypotheses that still enter, named precisely:
* the sampling duality (7.5) of Theorem 6, at every exhaustion index `m`, observable `f` of the
  subalgebra, genome law `p` and time `t`: `(S m).operator t f p` is the integral of an evaluation
  of the circuit state against the marginal law of that state, with the evaluation integrable and
  bounded by `‖f‖`;
* agreement until escape: on a circuit state that has not escaped the ball of radius `radius m`
  around the observation set of `f`, the evaluations of `S m` and of every later `S m'` coincide.
  For the support tags this is `runCircuit_truncatedStep_eq`: the full and the truncated circuits
  coincide until the first outside-checking event;
* the marginal laws of the circuit state are probability laws that start at `n |A|` arguments
  carrying the observation set and obey Dynkin's formula for the light-cone count at base `a` at
  every time, with integrability and continuity, as in `measureReal_escapeSet_le_exp`.

The finite-genome semigroups themselves are data, as in `InfiniteGenomeLimit`.

## Empirical status

None. The bodies here are integrals of bounded functions, sup-norm bounds and a chain of stated
bounds: the semigroups, the laws and the evaluations are supplied, and no measurement enters any
statement.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Pangenome.AncestralLocality

open Finset MeasureTheory Filter Topology InfiniteGenomeLimit
open scoped NNReal

noncomputable section

/-- Spec §10, the error term of Theorem 9. Assumes: a probability law `ν`, two integrable
evaluations bounded in absolute value by `B`, and an escape set off which the evaluations coincide.
Their integrals differ by at most `2 B ν(escape)`. -/
theorem abs_integral_sub_le_of_eqOn_compl {σ : Type*} [MeasurableSpace σ] (ν : Measure σ)
    [IsProbabilityMeasure ν] (F G : σ → ℝ) (hF : Integrable F ν) (hG : Integrable G ν) {B : ℝ}
    (hFB : ∀ x, |F x| ≤ B) (hGB : ∀ x, |G x| ≤ B) {escape : Set σ}
    (hagree : ∀ x ∉ escape, F x = G x) :
    |∫ x, F x ∂ν - ∫ x, G x ∂ν| ≤ 2 * B * ν.real escape := by
  have hvanish : ∀ x, x ∉ escape → F x - G x = 0 := fun x hx ↦ by rw [hagree x hx, sub_self]
  have hdifference : IntegrableOn (fun x ↦ ‖F x - G x‖) escape ν := (hF.sub hG).norm.integrableOn
  have hconstant : IntegrableOn (fun _ ↦ 2 * B) escape ν := (integrable_const (2 * B)).integrableOn
  rw [← integral_sub hF hG, ← setIntegral_eq_integral_of_forall_compl_eq_zero hvanish,
    ← Real.norm_eq_abs]
  refine (norm_integral_le_integral_norm _).trans
    ((setIntegral_mono hdifference hconstant fun x ↦ ?_).trans ?_)
  · simp only [Real.norm_eq_abs]
    obtain ⟨hFlow, hFhigh⟩ := abs_le.mp (hFB x)
    obtain ⟨hGlow, hGhigh⟩ := abs_le.mp (hGB x)
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  · rw [setIntegral_const, smul_eq_mul]
    exact le_of_eq (mul_comm _ _)

/-- The escape bound (9.1) grows with the horizon. Assumes: a nonnegative number of arguments `N`,
a nonnegative rate bound `D`, a base `a ≥ 1` and `t ≤ T`. -/
theorem escapeBound_mono_time {N D a : ℝ} {ℓ : ℕ} (hN : 0 ≤ N) (hD : 0 ≤ D) (ha : 1 ≤ a)
    {t T : ℝ} (htT : t ≤ T) :
    min 1 (N * Real.exp (D * (1 + 2 * a) * t) / a ^ ℓ) ≤
      min 1 (N * Real.exp (D * (1 + 2 * a) * T) / a ^ ℓ) := by
  have hexp : Real.exp (D * (1 + 2 * a) * t) ≤ Real.exp (D * (1 + 2 * a) * T) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left htT (mul_nonneg hD (by linarith)))
  have hpositive : 0 < a ^ ℓ := pow_pos (by linarith) ℓ
  refine min_le_min le_rfl ?_
  rw [div_eq_mul_inv, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hexp hN)
    (inv_nonneg.mpr hpositive.le)

/-- Spec §10, the operator bound of Theorem 9 for finite-genome truncations. Assumes: nonnegative
rates with row sums at most `D ≥ 0`, a coalescence rate `c ≥ 0`, a base `a ≥ 1`, and for every
observable `f` of the subalgebra an observation set and a number of sampled arguments; the
sampling duality `hduality` of the operators `S m` through bounded integrable evaluations of the
circuit state against its marginal laws `law f p t`; agreement `hagree` of the evaluations of
`S m` and every later `S m'` on every state that has not escaped the ball of radius `radius m`;
and the hypotheses of `measureReal_escapeSet_le_exp` for the marginal laws at every time. Then later members of the
exhaustion stay within `2 ‖f‖` times the escape bound (9.1) at the horizon. -/
theorem norm_operator_sub_le_lightConeEscape {X V : Type*} [TopologicalSpace X] [CompactSpace X]
    [DecidableEq V] [Fintype V] [MeasurableSpace (Multiset (Finset V))]
    [MeasurableSingletonClass (Multiset (Finset V))] {S : ℕ → FellerSemigroup X}
    {A : Subalgebra ℝ C(X, ℝ)} {r : V → V → ℝ} {c D a : ℝ} (hr : ∀ i j, 0 ≤ r i j)
    (hD : ∀ i, ∑ j, r i j ≤ D) (hDnonneg : 0 ≤ D) (hc : 0 ≤ c) (ha : 1 ≤ a) (radius : ℕ → ℕ)
    (observationSet : C(X, ℝ) → Finset V) (sampleSize : C(X, ℝ) → ℕ)
    (law : C(X, ℝ) → X → ℝ → Measure (Multiset (Finset V)))
    [∀ f p t, IsProbabilityMeasure (law f p t)]
    (evaluation : ℕ → C(X, ℝ) → X → ℝ → Multiset (Finset V) → ℝ)
    (hintegrable : ∀ m f p t, Integrable (evaluation m f p t) (law f p t))
    (hbounded : ∀ m f p t s, |evaluation m f p t s| ≤ ‖f‖)
    (hduality : ∀ f ∈ A, ∀ m p (t : ℝ≥0),
      (S m).operator t f p = ∫ s, evaluation m f p t s ∂law f p t)
    (hagree : ∀ f ∈ A, ∀ m m', m ≤ m' → ∀ p t s,
      s ∉ escapeSet r (observationSet f) (radius m) → evaluation m f p t s = evaluation m' f p t s)
    (hstart : ∀ f p,
      law f p 0 = Measure.dirac (Multiset.replicate (sampleSize f) (observationSet f)))
    (hint : ∀ f p m, ∀ t ∈ Set.Ici (0 : ℝ),
      Integrable (weightedCount (lightWeight r (observationSet f) (radius m) a)) (law f p t))
    (hintL : ∀ f p m, ∀ t ∈ Set.Ici (0 : ℝ),
      Integrable
        (supportGenerator r c (weightedCount (lightWeight r (observationSet f) (radius m) a)))
        (law f p t))
    (hcont : ∀ f p m, ContinuousOn
      (fun t ↦ ∫ s, weightedCount (lightWeight r (observationSet f) (radius m) a) s ∂law f p t)
      (Set.Ici 0))
    (hdynkin : ∀ f p m, ∀ t ∈ Set.Ici (0 : ℝ),
      HasDerivWithinAt
        (fun t ↦ ∫ s, weightedCount (lightWeight r (observationSet f) (radius m) a) s ∂law f p t)
        (∫ s, supportGenerator r c (weightedCount (lightWeight r (observationSet f) (radius m) a)) s
          ∂law f p t) (Set.Ici t) t) :
    ∀ f ∈ A, ∀ T t, t ≤ T → ∀ m m', m ≤ m' →
      ‖(S m).operator t f - (S m').operator t f‖ ≤
        2 * ‖f‖ *
          lightConeEscape ((sampleSize f : ℝ) * (observationSet f).card) D a radius T m := by
  intro f hf T t htT m m' hmm'
  have hnumber : (0 : ℝ) ≤ (sampleSize f : ℝ) * (observationSet f).card := by positivity
  have hescapeNonneg : 0 ≤ lightConeEscape ((sampleSize f : ℝ) * (observationSet f).card) D a
      radius T m :=
    le_min zero_le_one
      (div_nonneg (mul_nonneg hnumber (Real.exp_pos _).le) (pow_nonneg (by linarith) _))
  rw [ContinuousMap.norm_le (C0 := mul_nonneg (by positivity) hescapeNonneg)]
  intro p
  rw [ContinuousMap.sub_apply, hduality f hf m p t, hduality f hf m' p t, Real.norm_eq_abs]
  have hcoupling := abs_integral_sub_le_of_eqOn_compl (law f p t) _ _ (hintegrable m f p t)
    (hintegrable m' f p t) (hbounded m f p t) (hbounded m' f p t) (hagree f hf m m' hmm' p t)
  have hbound := measureReal_escapeSet_le_exp hr hD hc ha t.coe_nonneg (μ := law f p) (hstart f p)
    (fun u hu ↦ hint f p m u hu.1) (fun u hu ↦ hintL f p m u hu.1)
    ((hcont f p m).mono Set.Icc_subset_Ici_self) (fun u hu ↦ hdynkin f p m u hu.1)
  calc |∫ s, evaluation m f p t s ∂law f p t - ∫ s, evaluation m' f p t s ∂law f p t|
      ≤ 2 * ‖f‖ * (law f p t).real (escapeSet r (observationSet f) (radius m)) := hcoupling
    _ ≤ 2 * ‖f‖ * min 1 ((sampleSize f : ℝ) * (observationSet f).card *
          Real.exp (D * (1 + 2 * a) * t) / a ^ radius m) :=
        mul_le_mul_of_nonneg_left hbound (by positivity)
    _ ≤ 2 * ‖f‖ * lightConeEscape ((sampleSize f : ℝ) * (observationSet f).card) D a radius T m :=
        mul_le_mul_of_nonneg_left
          (escapeBound_mono_time hnumber hDnonneg ha (NNReal.coe_le_coe.mpr htT)) (by positivity)

/-- Spec §10, Theorem 9's approximation hypothesis discharged. Assumes: a base `a > 1`, an
exhaustion radius growing without bound, and the hypotheses of
`norm_operator_sub_le_lightConeEscape`. The finite-genome semigroups form a
`LightConeApproximation` with the escape function (9.1). -/
def InfiniteGenomeLimit.LightConeApproximation.ofDuality {X V : Type*} [TopologicalSpace X]
    [CompactSpace X] [DecidableEq V] [Fintype V] [MeasurableSpace (Multiset (Finset V))]
    [MeasurableSingletonClass (Multiset (Finset V))] {S : ℕ → FellerSemigroup X}
    {A : Subalgebra ℝ C(X, ℝ)} {r : V → V → ℝ} {c D a : ℝ} (hr : ∀ i j, 0 ≤ r i j)
    (hD : ∀ i, ∑ j, r i j ≤ D) (hDnonneg : 0 ≤ D) (hc : 0 ≤ c) (ha : 1 < a) (radius : ℕ → ℕ)
    (hradius : Tendsto radius atTop atTop)
    (observationSet : C(X, ℝ) → Finset V) (sampleSize : C(X, ℝ) → ℕ)
    (law : C(X, ℝ) → X → ℝ → Measure (Multiset (Finset V)))
    [∀ f p t, IsProbabilityMeasure (law f p t)]
    (evaluation : ℕ → C(X, ℝ) → X → ℝ → Multiset (Finset V) → ℝ)
    (hintegrable : ∀ m f p t, Integrable (evaluation m f p t) (law f p t))
    (hbounded : ∀ m f p t s, |evaluation m f p t s| ≤ ‖f‖)
    (hduality : ∀ f ∈ A, ∀ m p (t : ℝ≥0),
      (S m).operator t f p = ∫ s, evaluation m f p t s ∂law f p t)
    (hagree : ∀ f ∈ A, ∀ m m', m ≤ m' → ∀ p t s,
      s ∉ escapeSet r (observationSet f) (radius m) → evaluation m f p t s = evaluation m' f p t s)
    (hstart : ∀ f p,
      law f p 0 = Measure.dirac (Multiset.replicate (sampleSize f) (observationSet f)))
    (hint : ∀ f p m, ∀ t ∈ Set.Ici (0 : ℝ),
      Integrable (weightedCount (lightWeight r (observationSet f) (radius m) a)) (law f p t))
    (hintL : ∀ f p m, ∀ t ∈ Set.Ici (0 : ℝ),
      Integrable
        (supportGenerator r c (weightedCount (lightWeight r (observationSet f) (radius m) a)))
        (law f p t))
    (hcont : ∀ f p m, ContinuousOn
      (fun t ↦ ∫ s, weightedCount (lightWeight r (observationSet f) (radius m) a) s ∂law f p t)
      (Set.Ici 0))
    (hdynkin : ∀ f p m, ∀ t ∈ Set.Ici (0 : ℝ),
      HasDerivWithinAt
        (fun t ↦ ∫ s, weightedCount (lightWeight r (observationSet f) (radius m) a) s ∂law f p t)
        (∫ s, supportGenerator r c (weightedCount (lightWeight r (observationSet f) (radius m) a)) s
          ∂law f p t) (Set.Ici t) t) :
    LightConeApproximation S A :=
  LightConeApproximation.ofEscapeBound (fun f ↦ (sampleSize f : ℝ) * (observationSet f).card) D ha
    radius hradius
    (norm_operator_sub_le_lightConeEscape hr hD hDnonneg hc ha.le radius observationSet sampleSize
      law evaluation hintegrable hbounded hduality hagree hstart hint hintL hcont hdynkin)

end

end Descent.Pangenome.AncestralLocality
