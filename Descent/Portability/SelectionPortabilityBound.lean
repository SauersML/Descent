/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.AncestralLocality.SelectionSemigroupPerturbation
import Descent.Portability.MixingLawReplicaBias
import Descent.Portability.PortabilityMetricCompilation

assert_below Descent.Decision Descent.Program

/-!
# Portability under weak selection: an explicit error bar

`Descent.Pangenome.AncestralLocality.SelectionSemigroupPerturbation` bounds how far events at total
rate `R` move the forward semigroup of a finite window from the neutral semigroup of the same
window: `‖T^r_t H_f - T^0_t H_f‖ ≤ 2 n R t ‖f‖` on the sampling observable of every observation `f`
of `n` genomes. This module works out which portability metric that bound reaches, and with which
constant.

Which metric. The dual acts on sampling observables, the expectations of observations of finitely
many sampled genomes, so the metrics it reaches are polynomials in the window frequencies. For a
score `S` and an outcome `Y` of the genome type, the corpus metrics of NOTE2 (21) at the law `p` of
the window, `ReplicaMetricInstances.correlationNumerator` `N = 16 C_{S,Y}²` and
`ReplicaMetricInstances.correlationDenominator` `D = 16 V_S V_Y`, are sampling observables of four
genomes. The covariance kernel `c_{S,Y}(u) = (S(u_0) - S(u_1)) (Y(u_0) - Y(u_1)) / 2` of two genomes
samples the covariance (`samplingObservable_covarianceObservation`), independent samples multiply
(`tensorObservation`, `samplingObservable_tensorObservation`), and so `N = H_{16 c_{S,Y} ⊗ c_{S,Y}}`
and `D = H_{16 c_{S,S} ⊗ c_{Y,Y}}` (`windowNumerator_apply`, `windowDenominator_apply`). The metric
the dual reaches is therefore the portability of expected accuracies, the ratio NOTE2 (27) of
`E N_t / E D_t` at a target time `t` to `E N_s / E D_s` at a source time `s`, along the window
started at a law `p₀` (`windowPortability`, the cross form `windowPortability_eq_cross`). The
expected squared correlation `E[N/D]` is not a sampling observable, and the bound does not reach
it.

Which constant. For a score and an outcome in the unit interval each covariance kernel is at most
`1/2` (`norm_covarianceObservation_le`), so both observations have sup norm at most `4`
(`norm_numeratorObservation_le`, `norm_denominatorObservation_le`). With `n = 4`, every expected
numerator and denominator moves by at most `2 · 4 · R t · 4 = 32 R t`
(`abs_windowNumerator_sub_neutral_le`, `abs_windowDenominator_sub_neutral_le`). A Feller semigroup
keeps `0 ≤ E N ≤ E D ≤ 1` (`operator_apply_mem_unit`), so the four expectations lie in the unit
box, the realization body of its own coordinates (`unitBoxFeature`, `portabilityExpectations`,
`abs_portabilityExpectations_le`), and the portability is a cross ratio of their coordinates
(`windowPortability_eq_dotProduct`). The rest is the corpus analysis of that cross ratio,
`PortabilityMetricCompilation.abs_crossRatio_sub_le`, the route
`EndToEndPortabilityRateLipschitz` takes for rate histories: with feature bound `B = 1` and unit
coefficient vectors it moves by at most `4 / δ⁴` times the sup distance of the expectations. So
for `s ≤ t`, `|P_r - P_0| ≤ 4 · 32 R t / δ⁴ = 128 R t / δ⁴`
(`abs_windowPortability_sub_neutral_le`), and `128 σ t / δ⁴` for a total selective rate at most `σ`
(`abs_windowPortability_sub_neutral_le_of_sum_le`).

Significance. The portability of expected accuracies computed by the neutral window semigroup,
whose action on sampling observables is the killed coalescence semigroup, survives weak selection
to first order in `σ t`, with the explicit constant `128 / δ⁴`.

Scope. One finite window with deterministic decision events at constant rates. The window is one
panmictic population, so source and target are two times of the same process, not two demes. The
bound is local: the guard `δ` has to hold under both semigroups.

## Empirical status

None. The bodies here are finite sums over sampled genomes, sup-norm bounds and elementary
inequalities for quotients, so no measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.SelectionPortabilityBound

open Finset ReplicaMetricInstances
open Descent.Pangenome.AncestralLocality (samplingObservable samplingFunctional
  samplingFunctional_apply)
open Descent.Pangenome.AncestralLocality.InfiniteGenomeLimit (FellerSemigroup)
open Descent.Pangenome.AncestralLocality.DecisionWindowJumps (SimplexLaw samplingFunction)
open Descent.Pangenome.AncestralLocality.DecisionWindowSemigroup (decisionWindowSemigroup)
open Descent.Pangenome.AncestralLocality.SelectionSemigroupPerturbation (neutralWindowSemigroup
  norm_decisionWindowSemigroup_sub_neutral_le)
open scoped NNReal

noncomputable section

/-! ## Independent samples -/

section Sampling

variable {H : Type*} [Fintype H]

/-- **Two independent samples.** `tensorObservation f g` reads the first `n` of `n + m` sampled
genomes with `f` and the last `m` with `g`. -/
def tensorObservation {n m : ℕ} (f : (Fin n → H) → ℝ) (g : (Fin m → H) → ℝ) :
    (Fin (n + m) → H) → ℝ :=
  fun u ↦ f (fun i ↦ u (Fin.castAdd m i)) * g (fun j ↦ u (Fin.natAdd n j))

/-- **Independent samples multiply**: `H_{f ⊗ g}(p) = H_f(p) H_g(p)` at every vector `p`. -/
theorem samplingObservable_tensorObservation {n m : ℕ} (f : (Fin n → H) → ℝ)
    (g : (Fin m → H) → ℝ) (p : H → ℝ) :
    samplingObservable (tensorObservation f g) p =
      samplingObservable f p * samplingObservable g p := by
  simp only [samplingObservable]
  calc ∑ u, tensorObservation f g u * ∏ a, p (u a)
      = ∑ x : (Fin n → H) × (Fin m → H),
          (f x.1 * ∏ a, p (x.1 a)) * (g x.2 * ∏ a, p (x.2 a)) :=
        Fintype.sum_equiv (Fin.appendEquiv n m).symm _ _ fun u ↦ by
          show f (fun i ↦ u (Fin.castAdd m i)) * g (fun j ↦ u (Fin.natAdd n j)) *
              ∏ a, p (u a) =
            (f (fun i ↦ u (Fin.castAdd m i)) * ∏ a, p (u (Fin.castAdd m a))) *
              (g (fun j ↦ u (Fin.natAdd n j)) * ∏ a, p (u (Fin.natAdd n a)))
          rw [Fin.prod_univ_add]
          ring
    _ = ∑ x, ∑ y, (f x * ∏ a, p (x a)) * (g y * ∏ a, p (y a)) := Fintype.sum_prod_type _
    _ = (∑ x, f x * ∏ a, p (x a)) * ∑ y, g y * ∏ a, p (y a) := (Fintype.sum_mul_sum _ _).symm

/-- **One sampled genome read through `φ`** has sampling observable `∑_h p_h φ(h)`. -/
theorem samplingObservable_unary (φ : H → ℝ) (p : H → ℝ) :
    samplingObservable (fun w : Fin 1 → H ↦ φ (w 0)) p = ∑ h, p h * φ h := by
  simp only [samplingObservable, Fin.prod_univ_one]
  exact Fintype.sum_equiv (Equiv.funUnique (Fin 1) H) _ _ fun w ↦ mul_comm _ _

/-- **Independent samples multiply sup norms**: `‖f ⊗ g‖ ≤ ‖f‖ ‖g‖`. -/
theorem norm_tensorObservation_le {n m : ℕ} (f : (Fin n → H) → ℝ) (g : (Fin m → H) → ℝ) :
    ‖tensorObservation f g‖ ≤ ‖f‖ * ‖g‖ :=
  (pi_norm_le_iff_of_nonneg (mul_nonneg (norm_nonneg f) (norm_nonneg g))).mpr fun u ↦ by
    show ‖f (fun i ↦ u (Fin.castAdd m i)) * g (fun j ↦ u (Fin.natAdd n j))‖ ≤ ‖f‖ * ‖g‖
    rw [norm_mul]
    exact mul_le_mul (norm_le_pi_norm f _) (norm_le_pi_norm g _) (norm_nonneg _) (norm_nonneg f)

/-! ## The squared correlation as a sampling observable -/

/-- **The covariance kernel on two sampled genomes**,
`c_{S,Y}(u) = (S(u_0) - S(u_1)) (Y(u_0) - Y(u_1)) / 2`. -/
def covarianceObservation (S Y : H → ℝ) : (Fin (1 + 1) → H) → ℝ :=
  fun u ↦ (S (u (Fin.castAdd 1 0)) - S (u (Fin.natAdd 1 0))) *
    (Y (u (Fin.castAdd 1 0)) - Y (u (Fin.natAdd 1 0))) / 2

/-- **The covariance kernel samples the covariance**: at every law `p` of the window,
`H_{c_{S,Y}}(p) = C_{S,Y}(p)`. -/
theorem samplingObservable_covarianceObservation (S Y : H → ℝ) (p : SimplexLaw H) :
    samplingObservable (covarianceObservation S Y) p.1 =
      (MixingLawReplicaBias.simplexLaw p).covariance S Y := by
  have hsplit : covarianceObservation S Y = (1 / 2 : ℝ) •
      (tensorObservation (fun w : Fin 1 → H ↦ S (w 0) * Y (w 0)) (fun _ : Fin 1 → H ↦ 1) +
          tensorObservation (fun _ : Fin 1 → H ↦ 1) (fun w : Fin 1 → H ↦ S (w 0) * Y (w 0)) -
        tensorObservation (fun w : Fin 1 → H ↦ S (w 0)) (fun w : Fin 1 → H ↦ Y (w 0)) -
        tensorObservation (fun w : Fin 1 → H ↦ Y (w 0)) (fun w : Fin 1 → H ↦ S (w 0))) := by
    funext u
    simp only [covarianceObservation, tensorObservation, Pi.smul_apply, Pi.add_apply,
      Pi.sub_apply, smul_eq_mul]
    ring
  have hSY : samplingObservable (fun w : Fin 1 → H ↦ S (w 0) * Y (w 0)) p.1 =
      ∑ h, p.1 h * (S h * Y h) :=
    samplingObservable_unary (fun h ↦ S h * Y h) p.1
  have hS : samplingObservable (fun w : Fin 1 → H ↦ S (w 0)) p.1 = ∑ h, p.1 h * S h :=
    samplingObservable_unary S p.1
  have hY : samplingObservable (fun w : Fin 1 → H ↦ Y (w 0)) p.1 = ∑ h, p.1 h * Y h :=
    samplingObservable_unary Y p.1
  have hone : samplingObservable (fun _ : Fin 1 → H ↦ (1 : ℝ)) p.1 = 1 := by
    have h := samplingObservable_unary (fun _ : H ↦ (1 : ℝ)) p.1
    simp only [mul_one, p.2.2] at h
    exact h
  have hmean : ∀ φ : H → ℝ,
      (MixingLawReplicaBias.simplexLaw p).expectation φ = ∑ h, p.1 h * φ h := fun _ ↦ rfl
  rw [FiniteReportLaw.covariance_eq_rawMoments, hmean, hmean, hmean, hsplit,
    ← samplingFunctional_apply, map_smul, map_sub, map_sub, map_add]
  simp only [samplingFunctional_apply, samplingObservable_tensorObservation, hSY, hS, hY, hone,
    smul_eq_mul]
  ring

/-- **The correlation numerator as an observation of four genomes**, `16 c_{S,Y} ⊗ c_{S,Y}`. -/
def numeratorObservation (S Y : H → ℝ) : (Fin (1 + 1 + (1 + 1)) → H) → ℝ :=
  (16 : ℝ) • tensorObservation (covarianceObservation S Y) (covarianceObservation S Y)

/-- **The correlation denominator as an observation of four genomes**,
`16 c_{S,S} ⊗ c_{Y,Y}`. -/
def denominatorObservation (S Y : H → ℝ) : (Fin (1 + 1 + (1 + 1)) → H) → ℝ :=
  (16 : ℝ) • tensorObservation (covarianceObservation S S) (covarianceObservation Y Y)

/-- The numerator observation samples the corpus correlation numerator `16 C_{S,Y}²`. -/
theorem samplingObservable_numeratorObservation (S Y : H → ℝ) (p : SimplexLaw H) :
    samplingObservable (numeratorObservation S Y) p.1 =
      correlationNumerator (MixingLawReplicaBias.simplexLaw p) S Y := by
  rw [numeratorObservation, ← samplingFunctional_apply, map_smul, samplingFunctional_apply,
    samplingObservable_tensorObservation, samplingObservable_covarianceObservation, smul_eq_mul,
    correlationNumerator, sq]

/-- The denominator observation samples the corpus correlation denominator `16 V_S V_Y`. -/
theorem samplingObservable_denominatorObservation (S Y : H → ℝ) (p : SimplexLaw H) :
    samplingObservable (denominatorObservation S Y) p.1 =
      correlationDenominator (MixingLawReplicaBias.simplexLaw p) S Y := by
  rw [denominatorObservation, ← samplingFunctional_apply, map_smul, samplingFunctional_apply,
    samplingObservable_tensorObservation, samplingObservable_covarianceObservation,
    samplingObservable_covarianceObservation, smul_eq_mul]
  rfl

/-- For a score and an outcome in the unit interval the covariance kernel is at most `1/2`. -/
theorem norm_covarianceObservation_le {S Y : H → ℝ} (hS0 : ∀ h, 0 ≤ S h) (hS1 : ∀ h, S h ≤ 1)
    (hY0 : ∀ h, 0 ≤ Y h) (hY1 : ∀ h, Y h ≤ 1) : ‖covarianceObservation S Y‖ ≤ 1 / 2 :=
  (pi_norm_le_iff_of_nonneg (by norm_num)).mpr fun u ↦ by
    have hS : |S (u (Fin.castAdd 1 0)) - S (u (Fin.natAdd 1 0))| ≤ 1 :=
      abs_le.mpr ⟨by linarith [hS0 (u (Fin.castAdd 1 0)), hS1 (u (Fin.natAdd 1 0))],
        by linarith [hS0 (u (Fin.natAdd 1 0)), hS1 (u (Fin.castAdd 1 0))]⟩
    have hY : |Y (u (Fin.castAdd 1 0)) - Y (u (Fin.natAdd 1 0))| ≤ 1 :=
      abs_le.mpr ⟨by linarith [hY0 (u (Fin.castAdd 1 0)), hY1 (u (Fin.natAdd 1 0))],
        by linarith [hY0 (u (Fin.natAdd 1 0)), hY1 (u (Fin.castAdd 1 0))]⟩
    show ‖(S (u (Fin.castAdd 1 0)) - S (u (Fin.natAdd 1 0))) *
      (Y (u (Fin.castAdd 1 0)) - Y (u (Fin.natAdd 1 0))) / 2‖ ≤ 1 / 2
    rw [Real.norm_eq_abs, abs_div, abs_mul, abs_two]
    have hprod := mul_le_mul hS hY (abs_nonneg _) zero_le_one
    linarith

/-- For a score and an outcome in the unit interval the numerator observation is at most `4`. -/
theorem norm_numeratorObservation_le {S Y : H → ℝ} (hS0 : ∀ h, 0 ≤ S h) (hS1 : ∀ h, S h ≤ 1)
    (hY0 : ∀ h, 0 ≤ Y h) (hY1 : ∀ h, Y h ≤ 1) : ‖numeratorObservation S Y‖ ≤ 4 := by
  have hc := norm_covarianceObservation_le hS0 hS1 hY0 hY1
  have hcc : ‖covarianceObservation S Y‖ * ‖covarianceObservation S Y‖ ≤ 1 / 2 * (1 / 2) :=
    mul_le_mul hc hc (norm_nonneg _) (by norm_num)
  have ht := norm_tensorObservation_le (covarianceObservation S Y) (covarianceObservation S Y)
  rw [numeratorObservation, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 16)]
  linarith

/-- For a score and an outcome in the unit interval the denominator observation is at most `4`. -/
theorem norm_denominatorObservation_le {S Y : H → ℝ} (hS0 : ∀ h, 0 ≤ S h) (hS1 : ∀ h, S h ≤ 1)
    (hY0 : ∀ h, 0 ≤ Y h) (hY1 : ∀ h, Y h ≤ 1) : ‖denominatorObservation S Y‖ ≤ 4 := by
  have hS := norm_covarianceObservation_le hS0 hS1 hS0 hS1
  have hY := norm_covarianceObservation_le hY0 hY1 hY0 hY1
  have hprod : ‖covarianceObservation S S‖ * ‖covarianceObservation Y Y‖ ≤ 1 / 2 * (1 / 2) :=
    mul_le_mul hS hY (norm_nonneg _) (by norm_num)
  have ht := norm_tensorObservation_le (covarianceObservation S S) (covarianceObservation Y Y)
  rw [denominatorObservation, norm_smul, Real.norm_eq_abs,
    abs_of_pos (by norm_num : (0 : ℝ) < 16)]
  linarith

/-! ## The window metrics -/

/-- **The correlation numerator of the window**, `p ↦ 16 C_{S,Y}(p)²`, as the sampling function of
`numeratorObservation`. -/
def windowNumerator (S Y : H → ℝ) : C(SimplexLaw H, ℝ) :=
  samplingFunction (numeratorObservation S Y)

/-- **The correlation denominator of the window**, `p ↦ 16 V_S(p) V_Y(p)`, as the sampling function
of `denominatorObservation`. -/
def windowDenominator (S Y : H → ℝ) : C(SimplexLaw H, ℝ) :=
  samplingFunction (denominatorObservation S Y)

/-- **The window numerator is the corpus correlation numerator** at every law. -/
theorem windowNumerator_apply (S Y : H → ℝ) (p : SimplexLaw H) :
    windowNumerator S Y p = correlationNumerator (MixingLawReplicaBias.simplexLaw p) S Y :=
  samplingObservable_numeratorObservation S Y p

/-- **The window denominator is the corpus correlation denominator** at every law. -/
theorem windowDenominator_apply (S Y : H → ℝ) (p : SimplexLaw H) :
    windowDenominator S Y p = correlationDenominator (MixingLawReplicaBias.simplexLaw p) S Y :=
  samplingObservable_denominatorObservation S Y p

/-- The window numerator is nonnegative. -/
theorem windowNumerator_nonneg (S Y : H → ℝ) (p : SimplexLaw H) : 0 ≤ windowNumerator S Y p := by
  rw [windowNumerator_apply]
  exact correlationNumerator_nonneg _ S Y

/-- The window numerator is at most the window denominator. -/
theorem windowNumerator_le_windowDenominator (S Y : H → ℝ) (p : SimplexLaw H) :
    windowNumerator S Y p ≤ windowDenominator S Y p := by
  rw [windowNumerator_apply, windowDenominator_apply]
  exact correlationNumerator_le_denominator _ S Y

/-- For a score and an outcome in the unit interval the window denominator is at most one. -/
theorem windowDenominator_le_one {S Y : H → ℝ} (hS0 : ∀ h, 0 ≤ S h) (hS1 : ∀ h, S h ≤ 1)
    (hY0 : ∀ h, 0 ≤ Y h) (hY1 : ∀ h, Y h ≤ 1) (p : SimplexLaw H) :
    windowDenominator S Y p ≤ 1 := by
  rw [windowDenominator_apply]
  exact correlationDenominator_le_one _ S Y hS0 hS1 hY0 hY1

/-- **The expected portability of the window** from a source time `s` to a target time `t`: the
ratio NOTE2 (27) of the expected accuracy `E N_t / E D_t` at the target to `E N_s / E D_s` at the
source, for a Feller semigroup of the window started at `p₀`. -/
def windowPortability (semigroup : FellerSemigroup (SimplexLaw H)) (p₀ : SimplexLaw H)
    (s t : ℝ≥0) (S Y : H → ℝ) : ℝ :=
  PortabilityRatioQueries.portabilityRatio
    (fun _ : Unit ↦ semigroup.operator s (windowNumerator S Y) p₀)
    (fun _ ↦ semigroup.operator s (windowDenominator S Y) p₀)
    (fun _ ↦ semigroup.operator t (windowNumerator S Y) p₀)
    (fun _ ↦ semigroup.operator t (windowDenominator S Y) p₀) ()

/-- **The window portability is the cross ratio** `(E N_t · E D_s) / (E D_t · E N_s)`. -/
theorem windowPortability_eq_cross (semigroup : FellerSemigroup (SimplexLaw H))
    (p₀ : SimplexLaw H) (s t : ℝ≥0) (S Y : H → ℝ) :
    windowPortability semigroup p₀ s t S Y =
      semigroup.operator t (windowNumerator S Y) p₀ *
          semigroup.operator s (windowDenominator S Y) p₀ /
        (semigroup.operator t (windowDenominator S Y) p₀ *
          semigroup.operator s (windowNumerator S Y) p₀) :=
  div_div_div_eq _ _ _ _

end Sampling

/-! ## Feller semigroups keep the unit interval -/

/-- **A Feller semigroup keeps ordered observables in the unit interval**: if `0 ≤ F ≤ G ≤ 1`
pointwise, then `0 ≤ T_t F(x) ≤ T_t G(x) ≤ 1`. -/
theorem operator_apply_mem_unit {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (semigroup : FellerSemigroup X) (t : ℝ≥0) {F G : C(X, ℝ)} (hF : ∀ x, 0 ≤ F x)
    (hFG : ∀ x, F x ≤ G x) (hG : ∀ x, G x ≤ 1) (x : X) :
    0 ≤ semigroup.operator t F x ∧ semigroup.operator t F x ≤ semigroup.operator t G x ∧
      semigroup.operator t G x ≤ 1 := by
  have hpos : ∀ g : C(X, ℝ), (∀ y, 0 ≤ g y) → 0 ≤ semigroup.operator t g x := fun g hg ↦
    ContinuousMap.le_def.mp (semigroup.nonneg t g (ContinuousMap.le_def.mpr hg)) x
  have hGF := hpos (G - F) fun y ↦ by
    rw [ContinuousMap.sub_apply]
    linarith [hFG y]
  have hOneG := hpos (1 - G) fun y ↦ by
    rw [ContinuousMap.sub_apply, ContinuousMap.one_apply]
    linarith [hG y]
  rw [map_sub, ContinuousMap.sub_apply] at hGF hOneG
  rw [semigroup.map_one t, ContinuousMap.one_apply] at hOneG
  exact ⟨hpos F hF, by linarith, by linarith⟩

/-! ## The expectations on the unit box -/

section Box

variable {H : Type*} [Fintype H]

/-- **The unit box of four coordinates, read through its own coordinates.** Its realization body is
the box of vectors with every coordinate in `[-1, 1]`. -/
def unitBoxFeature : {v : Bool × Bool → ℝ // ∀ i, |v i| ≤ 1} → Bool × Bool → ℝ :=
  Subtype.val

/-- **The four expectations of the window portability**: the expected correlation numerator at
`(true, true)` and denominator at `(true, false)` at the target time `t`, and the numerator at
`(false, true)` and denominator at `(false, false)` at the source time `s`. -/
def portabilityExpectations (semigroup : FellerSemigroup (SimplexLaw H)) (p₀ : SimplexLaw H)
    (s t : ℝ≥0) (S Y : H → ℝ) : Bool × Bool → ℝ :=
  fun i ↦ semigroup.operator (if i.1 then t else s)
    (if i.2 then windowNumerator S Y else windowDenominator S Y) p₀

/-- **The window portability is a cross ratio of coordinates** of the four expectations. -/
theorem windowPortability_eq_dotProduct (semigroup : FellerSemigroup (SimplexLaw H))
    (p₀ : SimplexLaw H) (s t : ℝ≥0) (S Y : H → ℝ) :
    windowPortability semigroup p₀ s t S Y =
      (Pi.single (true, true) 1 ⬝ᵥ portabilityExpectations semigroup p₀ s t S Y) *
          (Pi.single (false, false) 1 ⬝ᵥ portabilityExpectations semigroup p₀ s t S Y) /
        ((Pi.single (true, false) 1 ⬝ᵥ portabilityExpectations semigroup p₀ s t S Y) *
          (Pi.single (false, true) 1 ⬝ᵥ portabilityExpectations semigroup p₀ s t S Y)) := by
  rw [windowPortability_eq_cross]
  simp only [single_dotProduct, one_mul]
  rfl

/-- **The four expectations lie in the unit box** for a score and an outcome in the unit
interval. -/
theorem abs_portabilityExpectations_le (semigroup : FellerSemigroup (SimplexLaw H))
    (p₀ : SimplexLaw H) (s t : ℝ≥0) {S Y : H → ℝ} (hS0 : ∀ h, 0 ≤ S h) (hS1 : ∀ h, S h ≤ 1)
    (hY0 : ∀ h, 0 ≤ Y h) (hY1 : ∀ h, Y h ≤ 1) (i : Bool × Bool) :
    |portabilityExpectations semigroup p₀ s t S Y i| ≤ 1 := by
  rcases i with ⟨b₁, b₂⟩
  obtain ⟨hN0, hND, hD1⟩ := operator_apply_mem_unit semigroup (if b₁ then t else s)
    (windowNumerator_nonneg S Y) (windowNumerator_le_windowDenominator S Y)
    (windowDenominator_le_one hS0 hS1 hY0 hY1) p₀
  cases b₂
  · show |semigroup.operator (if b₁ then t else s) (windowDenominator S Y) p₀| ≤ 1
    exact abs_le.mpr ⟨by linarith, hD1⟩
  · show |semigroup.operator (if b₁ then t else s) (windowNumerator S Y) p₀| ≤ 1
    exact abs_le.mpr ⟨by linarith, by linarith⟩

end Box

/-! ## The error bar -/

section Window

variable {H : Type*} [Fintype H] [DecidableEq H] {E : Type*} [Fintype E]

/-- **The expected correlation numerator moves by at most `32 R t`.** For a score and an outcome in
the unit interval, events at rates `r_e ≥ 0` with total `R = ∑_e r_e`, and every initial law `p₀`,
`|E^r N_t - E^0 N_t| ≤ 32 R t`. -/
theorem abs_windowNumerator_sub_neutral_le {c : ℝ} (hc : 0 ≤ c) {r : E → ℝ}
    (hr : ∀ e, 0 ≤ r e) (T : E → H → H → H) (t : ℝ≥0) {S Y : H → ℝ} (hS0 : ∀ h, 0 ≤ S h)
    (hS1 : ∀ h, S h ≤ 1) (hY0 : ∀ h, 0 ≤ Y h) (hY1 : ∀ h, Y h ≤ 1) (p₀ : SimplexLaw H) :
    |(decisionWindowSemigroup hc hr T).operator t (windowNumerator S Y) p₀ -
        (neutralWindowSemigroup hc T).operator t (windowNumerator S Y) p₀| ≤
      32 * (∑ e, r e) * (t : ℝ) := by
  have hmove := norm_decisionWindowSemigroup_sub_neutral_le hc hr T t (numeratorObservation S Y)
  have hf := norm_numeratorObservation_le hS0 hS1 hY0 hY1
  have hpoint := ContinuousMap.norm_coe_le_norm
    ((decisionWindowSemigroup hc hr T).operator t (windowNumerator S Y) -
      (neutralWindowSemigroup hc T).operator t (windowNumerator S Y)) p₀
  rw [ContinuousMap.sub_apply, Real.norm_eq_abs] at hpoint
  have hX : 0 ≤ 2 * ((1 + 1 + (1 + 1) : ℕ) : ℝ) * (∑ e, r e) * (t : ℝ) :=
    mul_nonneg (mul_nonneg (by positivity) (sum_nonneg fun e _ ↦ hr e)) (NNReal.coe_nonneg t)
  calc _ ≤ _ := hpoint
    _ ≤ 2 * ((1 + 1 + (1 + 1) : ℕ) : ℝ) * (∑ e, r e) * (t : ℝ) * ‖numeratorObservation S Y‖ :=
        hmove
    _ ≤ 2 * ((1 + 1 + (1 + 1) : ℕ) : ℝ) * (∑ e, r e) * (t : ℝ) * 4 :=
        mul_le_mul_of_nonneg_left hf hX
    _ = 32 * (∑ e, r e) * (t : ℝ) := by
        push_cast
        ring

/-- **The expected correlation denominator moves by at most `32 R t`.** For a score and an outcome
in the unit interval, events at rates `r_e ≥ 0` with total `R = ∑_e r_e`, and every initial law
`p₀`, `|E^r D_t - E^0 D_t| ≤ 32 R t`. -/
theorem abs_windowDenominator_sub_neutral_le {c : ℝ} (hc : 0 ≤ c) {r : E → ℝ}
    (hr : ∀ e, 0 ≤ r e) (T : E → H → H → H) (t : ℝ≥0) {S Y : H → ℝ} (hS0 : ∀ h, 0 ≤ S h)
    (hS1 : ∀ h, S h ≤ 1) (hY0 : ∀ h, 0 ≤ Y h) (hY1 : ∀ h, Y h ≤ 1) (p₀ : SimplexLaw H) :
    |(decisionWindowSemigroup hc hr T).operator t (windowDenominator S Y) p₀ -
        (neutralWindowSemigroup hc T).operator t (windowDenominator S Y) p₀| ≤
      32 * (∑ e, r e) * (t : ℝ) := by
  have hmove :=
    norm_decisionWindowSemigroup_sub_neutral_le hc hr T t (denominatorObservation S Y)
  have hf := norm_denominatorObservation_le hS0 hS1 hY0 hY1
  have hpoint := ContinuousMap.norm_coe_le_norm
    ((decisionWindowSemigroup hc hr T).operator t (windowDenominator S Y) -
      (neutralWindowSemigroup hc T).operator t (windowDenominator S Y)) p₀
  rw [ContinuousMap.sub_apply, Real.norm_eq_abs] at hpoint
  have hX : 0 ≤ 2 * ((1 + 1 + (1 + 1) : ℕ) : ℝ) * (∑ e, r e) * (t : ℝ) :=
    mul_nonneg (mul_nonneg (by positivity) (sum_nonneg fun e _ ↦ hr e)) (NNReal.coe_nonneg t)
  calc _ ≤ _ := hpoint
    _ ≤ 2 * ((1 + 1 + (1 + 1) : ℕ) : ℝ) * (∑ e, r e) * (t : ℝ) * ‖denominatorObservation S Y‖ :=
        hmove
    _ ≤ 2 * ((1 + 1 + (1 + 1) : ℕ) : ℝ) * (∑ e, r e) * (t : ℝ) * 4 :=
        mul_le_mul_of_nonneg_left hf hX
    _ = 32 * (∑ e, r e) * (t : ℝ) := by
        push_cast
        ring

/-- **Portability survives weak selection, with an explicit error bar.** For a score and an
outcome in the unit interval, events at rates `r_e ≥ 0` with total `R = ∑_e r_e`, an initial law
`p₀` and source and target times `s ≤ t`, if the expected target denominator and source numerator
are at least `δ > 0` under both semigroups, the expected portabilities with and without the events
differ by at most `128 R t / δ⁴`. -/
theorem abs_windowPortability_sub_neutral_le {c : ℝ} (hc : 0 ≤ c) {r : E → ℝ}
    (hr : ∀ e, 0 ≤ r e) (T : E → H → H → H) (p₀ : SimplexLaw H) {s t : ℝ≥0} (hst : s ≤ t)
    {S Y : H → ℝ} (hS0 : ∀ h, 0 ≤ S h) (hS1 : ∀ h, S h ≤ 1) (hY0 : ∀ h, 0 ≤ Y h)
    (hY1 : ∀ h, Y h ≤ 1) {δ : ℝ} (hδ : 0 < δ)
    (htarget : δ ≤ (decisionWindowSemigroup hc hr T).operator t (windowDenominator S Y) p₀)
    (hsource : δ ≤ (decisionWindowSemigroup hc hr T).operator s (windowNumerator S Y) p₀)
    (htarget₀ : δ ≤ (neutralWindowSemigroup hc T).operator t (windowDenominator S Y) p₀)
    (hsource₀ : δ ≤ (neutralWindowSemigroup hc T).operator s (windowNumerator S Y) p₀) :
    |windowPortability (decisionWindowSemigroup hc hr T) p₀ s t S Y -
        windowPortability (neutralWindowSemigroup hc T) p₀ s t S Y| ≤
      128 * (∑ e, r e) * (t : ℝ) / δ ^ 4 := by
  have hR : 0 ≤ ∑ e, r e := sum_nonneg fun e _ ↦ hr e
  have hmono : 32 * (∑ e, r e) * (s : ℝ) ≤ 32 * (∑ e, r e) * (t : ℝ) :=
    mul_le_mul_of_nonneg_left (NNReal.coe_le_coe.mpr hst) (mul_nonneg (by norm_num) hR)
  have hmove : ‖portabilityExpectations (decisionWindowSemigroup hc hr T) p₀ s t S Y -
      portabilityExpectations (neutralWindowSemigroup hc T) p₀ s t S Y‖ ≤
        32 * (∑ e, r e) * (t : ℝ) := by
    refine (pi_norm_le_iff_of_nonneg (mul_nonneg (mul_nonneg (by norm_num) hR)
      (NNReal.coe_nonneg t))).mpr fun i ↦ ?_
    rcases i with ⟨b₁, b₂⟩
    have htime : 32 * (∑ e, r e) * ((if b₁ then t else s : ℝ≥0) : ℝ) ≤
        32 * (∑ e, r e) * (t : ℝ) := by
      cases b₁
      · exact hmono
      · exact le_rfl
    rw [Pi.sub_apply, Real.norm_eq_abs]
    cases b₂
    · exact (abs_windowDenominator_sub_neutral_le hc hr T (if b₁ then t else s) hS0 hS1 hY0 hY1
        p₀).trans htime
    · exact (abs_windowNumerator_sub_neutral_le hc hr T (if b₁ then t else s) hS0 hS1 hY0 hY1
        p₀).trans htime
  have hv : portabilityExpectations (decisionWindowSemigroup hc hr T) p₀ s t S Y ∈
      RealizationBody.realizationBody unitBoxFeature :=
    RealizationBody.mem_realizationBody_of_range unitBoxFeature
      ⟨portabilityExpectations (decisionWindowSemigroup hc hr T) p₀ s t S Y,
        abs_portabilityExpectations_le (decisionWindowSemigroup hc hr T) p₀ s t hS0 hS1 hY0 hY1⟩
  have hv₀ : portabilityExpectations (neutralWindowSemigroup hc T) p₀ s t S Y ∈
      RealizationBody.realizationBody unitBoxFeature :=
    RealizationBody.mem_realizationBody_of_range unitBoxFeature
      ⟨portabilityExpectations (neutralWindowSemigroup hc T) p₀ s t S Y,
        abs_portabilityExpectations_le (neutralWindowSemigroup hc T) p₀ s t hS0 hS1 hY0 hY1⟩
  have hDt : δ ≤ Pi.single (true, false) 1 ⬝ᵥ
      portabilityExpectations (decisionWindowSemigroup hc hr T) p₀ s t S Y := by
    rw [single_dotProduct, one_mul]
    exact htarget
  have hNs : δ ≤ Pi.single (false, true) 1 ⬝ᵥ
      portabilityExpectations (decisionWindowSemigroup hc hr T) p₀ s t S Y := by
    rw [single_dotProduct, one_mul]
    exact hsource
  have hDt₀ : δ ≤ Pi.single (true, false) 1 ⬝ᵥ
      portabilityExpectations (neutralWindowSemigroup hc T) p₀ s t S Y := by
    rw [single_dotProduct, one_mul]
    exact htarget₀
  have hNs₀ : δ ≤ Pi.single (false, true) 1 ⬝ᵥ
      portabilityExpectations (neutralWindowSemigroup hc T) p₀ s t S Y := by
    rw [single_dotProduct, one_mul]
    exact hsource₀
  have hcross := PortabilityMetricCompilation.abs_crossRatio_sub_le unitBoxFeature hδ
    (fun x i ↦ x.2 i) (Pi.single (true, true) 1) (Pi.single (false, false) 1)
    (Pi.single (true, false) 1) (Pi.single (false, true) 1) hv hv₀ hDt hNs hDt₀ hNs₀
  have hsum : ∀ k : Bool × Bool, ∑ i, |(Pi.single k (1 : ℝ) : Bool × Bool → ℝ) i| = 1 :=
    fun k ↦ by
      rw [Finset.sum_eq_single k (fun i _ hik ↦ by rw [Pi.single_eq_of_ne hik, abs_zero])
        (fun hk ↦ absurd (Finset.mem_univ k) hk), Pi.single_eq_same, abs_one]
  rw [hsum, hsum, hsum, hsum] at hcross
  rw [windowPortability_eq_dotProduct, windowPortability_eq_dotProduct]
  calc _ ≤ _ := hcross
    _ ≤ 4 * 1 ^ 3 * 1 * 1 * 1 * 1 / δ ^ 4 * (32 * (∑ e, r e) * (t : ℝ)) :=
        mul_le_mul_of_nonneg_left hmove (by positivity)
    _ = 128 * (∑ e, r e) * (t : ℝ) / δ ^ 4 := by ring

/-- **The error bar for a total selective rate at most `σ`**: under the hypotheses of
`abs_windowPortability_sub_neutral_le` and `∑_e r_e ≤ σ`, the expected portabilities differ by at
most `128 σ t / δ⁴`. -/
theorem abs_windowPortability_sub_neutral_le_of_sum_le {c σ : ℝ} (hc : 0 ≤ c) {r : E → ℝ}
    (hr : ∀ e, 0 ≤ r e) (hRσ : ∑ e, r e ≤ σ) (T : E → H → H → H) (p₀ : SimplexLaw H)
    {s t : ℝ≥0} (hst : s ≤ t) {S Y : H → ℝ} (hS0 : ∀ h, 0 ≤ S h) (hS1 : ∀ h, S h ≤ 1)
    (hY0 : ∀ h, 0 ≤ Y h) (hY1 : ∀ h, Y h ≤ 1) {δ : ℝ} (hδ : 0 < δ)
    (htarget : δ ≤ (decisionWindowSemigroup hc hr T).operator t (windowDenominator S Y) p₀)
    (hsource : δ ≤ (decisionWindowSemigroup hc hr T).operator s (windowNumerator S Y) p₀)
    (htarget₀ : δ ≤ (neutralWindowSemigroup hc T).operator t (windowDenominator S Y) p₀)
    (hsource₀ : δ ≤ (neutralWindowSemigroup hc T).operator s (windowNumerator S Y) p₀) :
    |windowPortability (decisionWindowSemigroup hc hr T) p₀ s t S Y -
        windowPortability (neutralWindowSemigroup hc T) p₀ s t S Y| ≤
      128 * σ * (t : ℝ) / δ ^ 4 := by
  refine (abs_windowPortability_sub_neutral_le hc hr T p₀ hst hS0 hS1 hY0 hY1 hδ htarget hsource
    htarget₀ hsource₀).trans (div_le_div_of_nonneg_right ?_ (by positivity))
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hRσ (by norm_num))
    (NNReal.coe_nonneg t)

end Window

end

end Descent.Portability.SelectionPortabilityBound
