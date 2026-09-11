/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.IntegrableGeneratorPropagator
import Descent.Portability.IntegrableRateHistoryRealization
import Descent.Portability.RateGeneratorLipschitz

assert_below Descent.Decision Descent.Program

/-!
# Locus-exchangeable realizability under rate histories with integrable rates

NOTE1 section 2.4: for finitely many demes on a finite horizon, nonnegative measurable rates with
integrable norm give a fundamental matrix solving `U(t) = 1 + ∫₀ᵗ A(s) U(s) ds`, and the
propagator carries realizable states to realizable states.
`Descent.Portability.IntegrableRateHistoryRealization` proves the realizability theorem when the
corpus generator depends continuously on time.  This module removes that restriction.

The rates are approximated, not the generators.  `floorRates` turns a signed coordinate tuple
into a rate law by clipping negative rates at zero and adding a small floor to coalescence, and
`norm_rateCoordinates_floorRates_sub_le` shows this moves it at most the floor farther from any
rate law.  Combined with the density of continuous functions in `L¹`,
`exists_continuous_rates_integral_norm_sub_le` gives, for every `ε`, a rate history with
continuous coordinates within `ε (1 + T)` of the given one in `L¹([0, T])`.  By
`RateGeneratorLipschitz.exists_generator_lipschitz` their generators are within a fixed multiple
of that.

`exists_integral_solution_of_continuous_approximation` is the limit step, stated for any generator
path with integrable norm and any continuous paths within `scale / (k + 1)` of it in `L¹`: the
fundamental matrices of the approximating paths converge uniformly on the horizon, by the
integrated-norm variation of constants estimate of `IntegrableGeneratorPropagator`, and the limit
is a continuous solution of the integral equation.  `eq_of_integral_eq` shows that the integral
equation has at most one continuous solution: the difference of two solutions solves the
homogeneous equation, and comparing it with a continuous approximation of the generator and
applying Gronwall's inequality bounds it by an arbitrarily small multiple of the approximation
error.

`integrableRateHistory_preserves_locusExchangeable_realization` is NOTE1 section 2.4.  For every
rate history whose rate coordinates are integrable on `[0, T]`, there is a continuous solution of
the integral equation with the corpus generator of the rate law at each time; every continuous
solution agrees with it on the horizon; and its value at `T` carries every locus-exchangeably
realizable stored state to a locus-exchangeably realizable one.  The approximating histories
preserve realizability by the continuous theorem, their propagators converge, and the realizable
states form a closed set.

Scope.  Integrability is assumed for the rate coordinates; by the Lipschitz bound this makes the
generator norm integrable, and the converse is not used.  The fundamental matrix is characterized
by the integral equation, the Carathéodory form of `U' = A(t) U`; its almost-everywhere
derivative is not stated.  The approximating histories have continuous rates rather than the
step functions of the note; the continuous theorem reduces them to epoch products in turn.

## Empirical status

None.  The bodies here are calculus and point-set topology: integral inequalities, uniform
limits in a finite-dimensional space, and membership in a closed set, so no measurement can bear
on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.IntegrableRateRealization

open Coalescent
open MeasureTheory Filter Topology
open Descent.Portability.LinearFundamentalMatrix
open Descent.Portability.IntegrableGeneratorPropagator
open Descent.Portability.IntegrableRateHistoryRealization
open Descent.Portability.RateGeneratorLipschitz
open scoped Matrix.Norms.Operator

noncomputable section

/-! ## Rate laws from signed coordinates with a coalescence floor -/

/-- The rate law obtained from a signed coordinate tuple by clipping negative rates at zero,
dropping self-migration and adding `floor` to every coalescence rate. -/
def floorRates {D : ℕ} (floor : ℝ) (hfloor : 0 < floor) (x : RateCoordinates D) :
    ManyDemeLDRates D where
  coalescence i := max (x.1 i) 0 + floor
  migration i j := if i = j then 0 else max (x.2.1 i j) 0
  mutation i := max (x.2.2.1 i) 0
  recombination i := max (x.2.2.2 i) 0
  coalescence_pos i := add_pos_of_nonneg_of_pos (le_max_right _ _) hfloor
  migration_nonneg i j := by
    split_ifs
    · exact le_rfl
    · exact le_max_right _ _
  migration_self i := if_pos rfl
  mutation_nonneg i := le_max_right _ _
  recombination_nonneg i := le_max_right _ _

/-- The positive-part rate law of `RateGeneratorLipschitz` is the floor rate law at floor one. -/
theorem positivePartRates_eq_floorRates {D : ℕ} (x : RateCoordinates D) :
    positivePartRates x = floorRates 1 one_pos x := rfl

theorem rateCoordinates_fst {D : ℕ} (rates : ManyDemeLDRates D) :
    (rateCoordinates rates).1 = rates.coalescence := rfl

theorem rateCoordinates_snd_fst {D : ℕ} (rates : ManyDemeLDRates D) :
    (rateCoordinates rates).2.1 = rates.migration := rfl

theorem rateCoordinates_snd_snd_fst {D : ℕ} (rates : ManyDemeLDRates D) :
    (rateCoordinates rates).2.2.1 = rates.mutation := rfl

theorem rateCoordinates_snd_snd_snd {D : ℕ} (rates : ManyDemeLDRates D) :
    (rateCoordinates rates).2.2.2 = rates.recombination := rfl

/-- Clipping at zero does not move a real number farther from a nonnegative one. -/
theorem abs_max_zero_sub_le {a r : ℝ} (hr : 0 ≤ r) : |max a 0 - r| ≤ |a - r| := by
  have hmax := abs_max_sub_max_le_abs a r 0
  rwa [max_eq_left hr] at hmax

/-- Clipping at zero and adding a floor moves a real number at most the floor farther from a
nonnegative one. -/
theorem abs_max_zero_add_sub_le {a r floor : ℝ} (hr : 0 ≤ r) (hfloor : 0 ≤ floor) :
    |max a 0 + floor - r| ≤ |a - r| + floor := by
  obtain ⟨hlow, hhigh⟩ := abs_le.mp (abs_max_zero_sub_le (a := a) hr)
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- **The floor rate law stays close to every nearby rate law.** -/
theorem norm_rateCoordinates_floorRates_sub_le {D : ℕ} (floor : ℝ) (hfloor : 0 < floor)
    (x : RateCoordinates D) (rates : ManyDemeLDRates D) :
    ‖rateCoordinates (floorRates floor hfloor x) - rateCoordinates rates‖ ≤
      ‖x - rateCoordinates rates‖ + floor := by
  have hgap : 0 ≤ ‖x - rateCoordinates rates‖ + floor := add_nonneg (norm_nonneg _) hfloor.le
  have hfirst : ‖(x - rateCoordinates rates).1‖ ≤ ‖x - rateCoordinates rates‖ := norm_fst_le _
  have hsecond : ‖(x - rateCoordinates rates).2.1‖ ≤ ‖x - rateCoordinates rates‖ :=
    (norm_fst_le _).trans (norm_snd_le _)
  have hthird : ‖(x - rateCoordinates rates).2.2.1‖ ≤ ‖x - rateCoordinates rates‖ :=
    (norm_fst_le _).trans ((norm_snd_le _).trans (norm_snd_le _))
  have hfourth : ‖(x - rateCoordinates rates).2.2.2‖ ≤ ‖x - rateCoordinates rates‖ :=
    (norm_snd_le _).trans ((norm_snd_le _).trans (norm_snd_le _))
  rw [Prod.norm_def, Prod.norm_def, Prod.norm_def]
  refine max_le ?_ (max_le ?_ (max_le ?_ ?_))
  · refine (pi_norm_le_iff_of_nonneg hgap).mpr fun i ↦ ?_
    have hcomponent := (norm_le_pi_norm (x - rateCoordinates rates).1 i).trans hfirst
    simp only [Prod.fst_sub, Pi.sub_apply, rateCoordinates_fst, Real.norm_eq_abs]
      at hcomponent ⊢
    simp only [floorRates]
    linarith [abs_max_zero_add_sub_le (a := x.1 i) (rates.coalescence_pos i).le hfloor.le]
  · refine (pi_norm_le_iff_of_nonneg hgap).mpr fun i ↦ ?_
    refine (pi_norm_le_iff_of_nonneg hgap).mpr fun j ↦ ?_
    have hcomponent := ((norm_le_pi_norm ((x - rateCoordinates rates).2.1 i) j).trans
      (norm_le_pi_norm (x - rateCoordinates rates).2.1 i)).trans hsecond
    simp only [Prod.fst_sub, Prod.snd_sub, Pi.sub_apply, rateCoordinates_snd_fst,
      Real.norm_eq_abs] at hcomponent ⊢
    simp only [floorRates]
    by_cases hsame : i = j
    · subst hsame
      rw [if_pos rfl, rates.migration_self, sub_zero, abs_zero]
      exact hgap
    · rw [if_neg hsame]
      linarith [abs_max_zero_sub_le (a := x.2.1 i j) (rates.migration_nonneg i j)]
  · refine (pi_norm_le_iff_of_nonneg hgap).mpr fun i ↦ ?_
    have hcomponent := (norm_le_pi_norm (x - rateCoordinates rates).2.2.1 i).trans hthird
    simp only [Prod.fst_sub, Prod.snd_sub, Pi.sub_apply, rateCoordinates_snd_snd_fst,
      Real.norm_eq_abs] at hcomponent ⊢
    simp only [floorRates]
    linarith [abs_max_zero_sub_le (a := x.2.2.1 i) (rates.mutation_nonneg i)]
  · refine (pi_norm_le_iff_of_nonneg hgap).mpr fun i ↦ ?_
    have hcomponent := (norm_le_pi_norm (x - rateCoordinates rates).2.2.2 i).trans hfourth
    simp only [Prod.snd_sub, Pi.sub_apply, rateCoordinates_snd_snd_snd, Real.norm_eq_abs]
      at hcomponent ⊢
    simp only [floorRates]
    linarith [abs_max_zero_sub_le (a := x.2.2.2 i) (rates.recombination_nonneg i)]

/-- The coordinates of the floor rate law depend continuously on the signed tuple. -/
theorem continuous_rateCoordinates_floorRates {D : ℕ} (floor : ℝ) (hfloor : 0 < floor) :
    Continuous fun x : RateCoordinates D ↦ rateCoordinates (floorRates floor hfloor x) := by
  have hcoalescence : Continuous fun x : RateCoordinates D ↦ fun i ↦ max (x.1 i) 0 + floor :=
    continuous_pi fun i ↦ (((continuous_apply i).comp continuous_fst).max continuous_const).add
      continuous_const
  have hmigration : Continuous fun x : RateCoordinates D ↦
      fun i j : Fin D ↦ if i = j then (0 : ℝ) else max (x.2.1 i j) 0 := by
    refine continuous_pi fun i ↦ continuous_pi fun j ↦ ?_
    by_cases hsame : i = j
    · simp only [if_pos hsame]
      exact continuous_const
    · simp only [if_neg hsame]
      exact (((continuous_apply j).comp (continuous_apply i)).comp
        (continuous_fst.comp continuous_snd)).max continuous_const
  have hmutation : Continuous fun x : RateCoordinates D ↦ fun i ↦ max (x.2.2.1 i) 0 :=
    continuous_pi fun i ↦ ((continuous_apply i).comp
      (continuous_fst.comp (continuous_snd.comp continuous_snd))).max continuous_const
  have hrecombination : Continuous fun x : RateCoordinates D ↦ fun i ↦ max (x.2.2.2 i) 0 :=
    continuous_pi fun i ↦ ((continuous_apply i).comp
      (continuous_snd.comp (continuous_snd.comp continuous_snd))).max continuous_const
  exact hcoalescence.prodMk (hmigration.prodMk (hmutation.prodMk hrecombination))

/-! ## Generators of rate histories -/

/-- A rate history with continuous coordinates has a continuous corpus generator. -/
theorem continuous_augmentedLowOrderLDGenerator {D : ℕ} {path : ℝ → ManyDemeLDRates D}
    (hpath : Continuous fun t ↦ rateCoordinates (path t)) :
    Continuous fun t ↦ augmentedLowOrderLDGenerator (path t) := by
  have hlinear : Continuous (generatorLinearMap D) :=
    LinearMap.continuous_of_finiteDimensional _
  simp only [augmentedLowOrderLDGenerator_eq_generatorLinearMap]
  exact hlinear.comp hpath

/-- A rate history with integrable coordinates has an integrable corpus generator. -/
theorem intervalIntegrable_augmentedLowOrderLDGenerator {D : ℕ}
    {rates : ℝ → ManyDemeLDRates D} {T : ℝ}
    (hintegrable : IntervalIntegrable (fun t ↦ rateCoordinates (rates t)) volume 0 T) :
    IntervalIntegrable (fun t ↦ augmentedLowOrderLDGenerator (rates t)) volume 0 T := by
  simp only [augmentedLowOrderLDGenerator_eq_generatorLinearMap]
  let bounded := LinearMap.toContinuousLinearMap (generatorLinearMap D)
  exact ⟨bounded.integrable_comp hintegrable.1, bounded.integrable_comp hintegrable.2⟩

/-- **Continuous rate histories approximate integrable ones in `L¹`.** -/
theorem exists_continuous_rates_integral_norm_sub_le {D : ℕ} {rates : ℝ → ManyDemeLDRates D}
    {T : ℝ} (hT : 0 ≤ T)
    (hintegrable : IntervalIntegrable (fun t ↦ rateCoordinates (rates t)) volume 0 T)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ path : ℝ → ManyDemeLDRates D, Continuous (fun t ↦ rateCoordinates (path t)) ∧
      ∫ t in (0 : ℝ)..T, ‖rateCoordinates (path t) - rateCoordinates (rates t)‖ ≤
        ε * (1 + T) := by
  obtain ⟨g, hg, hclose⟩ := exists_continuous_integral_norm_sub_le hT hintegrable hε
  have hcontinuous : Continuous fun t ↦ rateCoordinates (floorRates ε hε (g t)) :=
    (continuous_rateCoordinates_floorRates ε hε).comp hg
  refine ⟨fun t ↦ floorRates ε hε (g t), hcontinuous, ?_⟩
  have hbound : ∀ t ∈ Set.Icc 0 T,
      ‖rateCoordinates (floorRates ε hε (g t)) - rateCoordinates (rates t)‖ ≤
        ‖rateCoordinates (rates t) - g t‖ + ε := fun t _ ↦ by
    rw [norm_sub_rev (rateCoordinates (rates t)) (g t)]
    exact norm_rateCoordinates_floorRates_sub_le ε hε (g t) (rates t)
  have hdifference :
      IntervalIntegrable (fun t ↦ ‖rateCoordinates (rates t) - g t‖) volume 0 T :=
    (hintegrable.sub (hg.intervalIntegrable 0 T)).norm
  calc ∫ t in (0 : ℝ)..T, ‖rateCoordinates (floorRates ε hε (g t)) - rateCoordinates (rates t)‖
      ≤ ∫ t in (0 : ℝ)..T, (‖rateCoordinates (rates t) - g t‖ + ε) :=
        intervalIntegral.integral_mono_on hT
          ((hcontinuous.intervalIntegrable 0 T).sub hintegrable).norm
          (hdifference.add intervalIntegrable_const) hbound
    _ = (∫ t in (0 : ℝ)..T, ‖rateCoordinates (rates t) - g t‖) + T * ε := by
        rw [intervalIntegral.integral_add hdifference intervalIntegrable_const,
          intervalIntegral.integral_const, smul_eq_mul, sub_zero]
    _ ≤ ε * (1 + T) := by nlinarith [hclose]

/-! ## Uniqueness of the integral equation -/

/-- **The integral equation has at most one continuous solution.**  For a generator path with
integrable norm, two continuous solutions of `U(t) = 1 + ∫₀ᵗ A U` agree on the horizon. -/
theorem eq_of_integral_eq {ι : Type*} [Fintype ι] [DecidableEq ι] {A : ℝ → Matrix ι ι ℝ}
    {T : ℝ} (hT : 0 ≤ T) (hA : IntervalIntegrable A volume 0 T) {V W : ℝ → Matrix ι ι ℝ}
    (hV : Continuous V) (hW : Continuous W)
    (hVeq : ∀ t ∈ Set.Icc 0 T, V t = 1 + ∫ s in (0 : ℝ)..t, A s * V s)
    (hWeq : ∀ t ∈ Set.Icc 0 T, W t = 1 + ∫ s in (0 : ℝ)..t, A s * W s) :
    ∀ t ∈ Set.Icc 0 T, V t = W t := by
  obtain ⟨bound, hboundNonneg, hbound⟩ := exists_bound_of_continuous (hV.sub hW) hT
  have hsubinterval : ∀ t ∈ Set.Icc 0 T, IntervalIntegrable A volume 0 t := fun t ht ↦
    hA.mono_set (Set.uIcc_subset_uIcc_left (Set.mem_uIcc_of_le ht.1 ht.2))
  have hsmall : ∀ t ∈ Set.Icc 0 T, ∀ ε : ℝ, 0 < ε →
      ‖V t - W t‖ ≤ bound * ε * Real.exp ((∫ s in (0 : ℝ)..T, ‖A s‖) + ε) := by
    intro t ht ε hε
    obtain ⟨B, hB, hclose⟩ := exists_continuous_integral_norm_sub_le hT hA hε
    have hstep : ∀ r ∈ Set.Icc 0 T, ‖V r - W r‖ ≤
        bound * ε + ∫ s in (0 : ℝ)..r, ‖B s‖ * ‖V s - W s‖ := by
      intro r hr
      have hAr := hsubinterval r hr
      have hsplit : V r - W r = (∫ s in (0 : ℝ)..r, B s * (V s - W s)) +
          ∫ s in (0 : ℝ)..r, (A s - B s) * (V s - W s) := by
        rw [hVeq r hr, hWeq r hr, add_sub_add_left_eq_sub,
          ← intervalIntegral.integral_sub (hAr.mul_continuousOn hV.continuousOn)
            (hAr.mul_continuousOn hW.continuousOn),
          ← intervalIntegral.integral_add ((hB.mul (hV.sub hW)).intervalIntegrable _ _)
            ((hAr.sub (hB.intervalIntegrable _ _)).mul_continuousOn (hV.sub hW).continuousOn)]
        congr 1
        funext s
        noncomm_ring
      have hfirst : ‖∫ s in (0 : ℝ)..r, B s * (V s - W s)‖ ≤
          ∫ s in (0 : ℝ)..r, ‖B s‖ * ‖V s - W s‖ :=
        (intervalIntegral.norm_integral_le_integral_norm hr.1).trans
          (intervalIntegral.integral_mono_on hr.1
            ((hB.mul (hV.sub hW)).norm.intervalIntegrable _ _)
            ((hB.norm.mul (hV.sub hW).norm).intervalIntegrable _ _) fun s _ ↦ norm_mul_le _ _)
      have hsecond : ‖∫ s in (0 : ℝ)..r, (A s - B s) * (V s - W s)‖ ≤ bound * ε := by
        refine (intervalIntegral.norm_integral_le_integral_norm hr.1).trans ?_
        calc ∫ s in (0 : ℝ)..r, ‖(A s - B s) * (V s - W s)‖
            ≤ ∫ s in (0 : ℝ)..r, ‖A s - B s‖ * bound := by
              refine intervalIntegral.integral_mono_on hr.1
                (((hAr.sub (hB.intervalIntegrable _ _)).mul_continuousOn
                  (hV.sub hW).continuousOn).norm)
                ((hAr.sub (hB.intervalIntegrable _ _)).norm.mul_const _) fun s hs ↦ ?_
              exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left
                (hbound s ⟨hs.1, hs.2.trans hr.2⟩) (norm_nonneg _))
          _ = (∫ s in (0 : ℝ)..r, ‖A s - B s‖) * bound :=
              intervalIntegral.integral_mul_const _ _
          _ ≤ ε * bound := by
              refine mul_le_mul_of_nonneg_right ?_ hboundNonneg
              exact (intervalIntegral.integral_mono_interval le_rfl hr.1 hr.2
                (ae_of_all _ fun _ ↦ norm_nonneg _)
                (hA.sub (hB.intervalIntegrable _ _)).norm).trans hclose
          _ = bound * ε := mul_comm _ _
      rw [hsplit]
      refine (norm_add_le _ _).trans ?_
      linarith [hfirst, hsecond]
    have hgronwall := le_mul_exp_integral_of_le_add_integral (a := fun s ↦ ‖B s‖)
      (u := fun s ↦ ‖V s - W s‖) hB.norm (hV.sub hW).norm (fun s _ ↦ norm_nonneg _) hstep t ht
    have hnormB : (∫ s in (0 : ℝ)..t, ‖B s‖) ≤ (∫ s in (0 : ℝ)..T, ‖A s‖) + ε := by
      have hmono : (∫ s in (0 : ℝ)..t, ‖B s‖) ≤ ∫ s in (0 : ℝ)..T, ‖B s‖ :=
        intervalIntegral.integral_mono_interval le_rfl ht.1 ht.2
          (ae_of_all _ fun _ ↦ norm_nonneg _) (hB.norm.intervalIntegrable _ _)
      have htriangle : (∫ s in (0 : ℝ)..T, ‖B s‖) ≤
          ∫ s in (0 : ℝ)..T, (‖A s‖ + ‖A s - B s‖) :=
        intervalIntegral.integral_mono_on hT (hB.norm.intervalIntegrable _ _)
          (hA.norm.add (hA.sub (hB.intervalIntegrable _ _)).norm) fun s _ ↦
            calc ‖B s‖ = ‖A s - (A s - B s)‖ := by rw [sub_sub_cancel]
              _ ≤ ‖A s‖ + ‖A s - B s‖ := norm_sub_le _ _
      rw [intervalIntegral.integral_add hA.norm (hA.sub (hB.intervalIntegrable _ _)).norm]
        at htriangle
      linarith
    calc ‖V t - W t‖ ≤ bound * ε * Real.exp (∫ s in (0 : ℝ)..t, ‖B s‖) := hgronwall
      _ ≤ bound * ε * Real.exp ((∫ s in (0 : ℝ)..T, ‖A s‖) + ε) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hnormB)
            (mul_nonneg hboundNonneg hε.le)
  intro t ht
  have hlimit : Tendsto (fun n : ℕ ↦ bound * (1 / ((n : ℝ) + 1)) *
      Real.exp ((∫ s in (0 : ℝ)..T, ‖A s‖) + 1)) atTop (𝓝 0) := by
    simpa using (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul bound).mul_const
      (Real.exp ((∫ s in (0 : ℝ)..T, ‖A s‖) + 1))
  have hle : ∀ n : ℕ, ‖V t - W t‖ ≤ bound * (1 / ((n : ℝ) + 1)) *
      Real.exp ((∫ s in (0 : ℝ)..T, ‖A s‖) + 1) := by
    intro n
    have hpositive : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    have hsmallOne : 1 / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    refine (hsmall t ht _ hpositive).trans ?_
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith))
      (mul_nonneg hboundNonneg hpositive.le)
  have hzero : ‖V t - W t‖ ≤ 0 := ge_of_tendsto' hlimit hle
  exact sub_eq_zero.mp (norm_le_zero_iff.mp hzero)

/-! ## The limit of fundamental matrices -/

/-- **The fundamental matrices of continuous approximations converge to a solution.**  For a
generator path with integrable norm and continuous paths within `scale / (k + 1)` of it in
`L¹([0, T])`, the fundamental matrices of the approximations converge at the horizon to the value
of a continuous solution of `U(t) = 1 + ∫₀ᵗ A U`. -/
theorem exists_integral_solution_of_continuous_approximation {ι : Type*} [Fintype ι]
    [DecidableEq ι] {A : ℝ → Matrix ι ι ℝ} {T : ℝ} (hT : 0 ≤ T)
    (hA : IntervalIntegrable A volume 0 T) {scale : ℝ} (hscale : 0 ≤ scale)
    (approximation : ℕ → ℝ → Matrix ι ι ℝ) (hcontinuous : ∀ k, Continuous (approximation k))
    (hclose : ∀ k : ℕ,
      ∫ s in (0 : ℝ)..T, ‖approximation k s - A s‖ ≤ scale * (1 / ((k : ℝ) + 1))) :
    ∃ U : ℝ → Matrix ι ι ℝ, Continuous U ∧
      (∀ t ∈ Set.Icc 0 T, U t = 1 + ∫ s in (0 : ℝ)..t, A s * U s) ∧
      Tendsto (fun k ↦ fundamentalMatrix (approximation k) T T) atTop (𝓝 (U T)) := by
  set mass := (∫ s in (0 : ℝ)..T, ‖A s‖) + scale with hmass
  have hinverse : ∀ {k j : ℕ}, k ≤ j → 1 / ((j : ℝ) + 1) ≤ 1 / ((k : ℝ) + 1) := by
    intro k j hkj
    gcongr
    exact_mod_cast hkj
  have hinverseOne : ∀ k : ℕ, 1 / ((k : ℝ) + 1) ≤ 1 := by
    intro k
    rw [div_le_one (by positivity)]
    linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have hnormA : 0 ≤ ∫ s in (0 : ℝ)..T, ‖A s‖ :=
    intervalIntegral.integral_nonneg hT fun s _ ↦ norm_nonneg (A s)
  have hexpOne : 1 ≤ Real.exp mass := Real.one_le_exp (by rw [hmass]; linarith)
  have hexpPos : 0 < Real.exp mass := Real.exp_pos mass
  have hscaledNonneg : ∀ k : ℕ, 0 ≤ scale * (1 / ((k : ℝ) + 1)) :=
    fun k ↦ mul_nonneg hscale (by positivity)
  have happroxIntegrable : ∀ k, IntervalIntegrable (approximation k) volume 0 T :=
    fun k ↦ (hcontinuous k).intervalIntegrable 0 T
  have hmassBound : ∀ k, (∫ s in (0 : ℝ)..T, ‖approximation k s‖) ≤ mass := by
    intro k
    have hstep : (∫ s in (0 : ℝ)..T, ‖approximation k s‖) ≤
        ∫ s in (0 : ℝ)..T, (‖A s‖ + ‖approximation k s - A s‖) :=
      intervalIntegral.integral_mono_on hT (happroxIntegrable k).norm
        (hA.norm.add ((happroxIntegrable k).sub hA).norm) fun s _ ↦
          calc ‖approximation k s‖ = ‖A s + (approximation k s - A s)‖ := by
                congr 1
                abel
            _ ≤ ‖A s‖ + ‖approximation k s - A s‖ := norm_add_le _ _
    rw [intervalIntegral.integral_add hA.norm ((happroxIntegrable k).sub hA).norm] at hstep
    have hscaled : scale * (1 / ((k : ℝ) + 1)) ≤ scale :=
      mul_le_of_le_one_right hscale (hinverseOne k)
    linarith [hclose k]
  have hpairClose : ∀ k j : ℕ,
      (∫ s in (0 : ℝ)..T, ‖approximation k s - approximation j s‖) ≤
        scale * (1 / ((k : ℝ) + 1)) + scale * (1 / ((j : ℝ) + 1)) := by
    intro k j
    have hstep : (∫ s in (0 : ℝ)..T, ‖approximation k s - approximation j s‖) ≤
        ∫ s in (0 : ℝ)..T, (‖approximation k s - A s‖ + ‖approximation j s - A s‖) :=
      intervalIntegral.integral_mono_on hT
        ((happroxIntegrable k).sub (happroxIntegrable j)).norm
        (((happroxIntegrable k).sub hA).norm.add ((happroxIntegrable j).sub hA).norm)
        fun s _ ↦
          calc ‖approximation k s - approximation j s‖ =
                ‖(approximation k s - A s) - (approximation j s - A s)‖ := by
                congr 1
                abel
            _ ≤ ‖approximation k s - A s‖ + ‖approximation j s - A s‖ := norm_sub_le _ _
    rw [intervalIntegral.integral_add ((happroxIntegrable k).sub hA).norm
      ((happroxIntegrable j).sub hA).norm] at hstep
    linarith [hclose k, hclose j]
  set sequence : ℕ → ℝ → Matrix ι ι ℝ :=
    fun k t ↦ fundamentalMatrix (approximation k) T (clampTime T t) with hsequence
  have hsequenceContinuous : ∀ k, Continuous (sequence k) := by
    intro k
    obtain ⟨K, hK, hbound⟩ := exists_bound_of_continuous (hcontinuous k) hT
    exact (continuous_fundamentalMatrix (hcontinuous k) hT hK hbound).comp
      (continuous_clampTime T)
  have hsequenceBound : ∀ k s, ‖sequence k s‖ ≤ Real.exp mass := by
    intro k s
    have hmem := clampTime_mem hT s
    exact (norm_fundamentalMatrix_le_exp_integral (hcontinuous k) hT (clampTime T s) hmem).trans
      (Real.exp_le_exp.mpr ((intervalIntegral.integral_mono_interval le_rfl hmem.1 hmem.2
        (ae_of_all _ fun _ ↦ norm_nonneg _) (happroxIntegrable k).norm).trans (hmassBound k)))
  have hsequenceClose : ∀ k j t, ‖sequence k t - sequence j t‖ ≤
      (scale * (1 / ((k : ℝ) + 1)) + scale * (1 / ((j : ℝ) + 1))) * Real.exp mass *
        Real.exp mass := by
    intro k j t
    have hmem := clampTime_mem hT t
    have hexpj : Real.exp (∫ s in (0 : ℝ)..T, ‖approximation j s‖) ≤ Real.exp mass :=
      Real.exp_le_exp.mpr (hmassBound j)
    have hexpk : Real.exp (∫ s in (0 : ℝ)..clampTime T t, ‖approximation k s‖) ≤
        Real.exp mass :=
      Real.exp_le_exp.mpr ((intervalIntegral.integral_mono_interval le_rfl hmem.1 hmem.2
        (ae_of_all _ fun _ ↦ norm_nonneg _) (happroxIntegrable k).norm).trans (hmassBound k))
    have hpairNonneg := add_nonneg (hscaledNonneg k) (hscaledNonneg j)
    exact (norm_fundamentalMatrix_sub_le_exp_integral (hcontinuous k) (hcontinuous j) hT
      (clampTime T t) hmem).trans (mul_le_mul (mul_le_mul (hpairClose k j) hexpj
        (Real.exp_pos _).le hpairNonneg) hexpk (Real.exp_pos _).le
        (mul_nonneg hpairNonneg hexpPos.le))
  have hdecay : Tendsto (fun k : ℕ ↦ 2 * (scale * (1 / ((k : ℝ) + 1))) * Real.exp mass *
      Real.exp mass) atTop (𝓝 0) := by
    simpa using (((tendsto_one_div_add_atTop_nhds_zero_nat.const_mul scale).const_mul 2).mul_const
      (Real.exp mass)).mul_const (Real.exp mass)
  have hfactor : ∀ {k j : ℕ}, k ≤ j →
      (scale * (1 / ((j : ℝ) + 1)) + scale * (1 / ((k : ℝ) + 1))) * Real.exp mass *
          Real.exp mass ≤
        2 * (scale * (1 / ((k : ℝ) + 1))) * Real.exp mass * Real.exp mass := by
    intro k j hkj
    have hshrink := mul_le_mul_of_nonneg_left (hinverse hkj) hscale
    have hsum : scale * (1 / ((j : ℝ) + 1)) + scale * (1 / ((k : ℝ) + 1)) ≤
        2 * (scale * (1 / ((k : ℝ) + 1))) := by linarith
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hsum hexpPos.le) hexpPos.le
  have hcauchy : ∀ t, CauchySeq fun k ↦ sequence k t := by
    intro t
    refine Metric.cauchySeq_iff'.mpr fun ε hε ↦ ?_
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hdecay ε hε
    refine ⟨N, fun n hn ↦ ?_⟩
    have hNbound := hN N le_rfl
    rw [Real.dist_eq, sub_zero] at hNbound
    rw [dist_eq_norm]
    exact ((hsequenceClose n N t).trans (hfactor hn)).trans_lt
      ((le_abs_self _).trans_lt hNbound)
  choose U hU using fun t ↦ cauchySeq_tendsto_of_complete (hcauchy t)
  have hlimitClose : ∀ k t, ‖U t - sequence k t‖ ≤
      2 * (scale * (1 / ((k : ℝ) + 1))) * Real.exp mass * Real.exp mass := by
    intro k t
    exact le_of_tendsto ((hU t).sub_const (sequence k t)).norm
      (eventually_atTop.mpr ⟨k, fun j hj ↦ (hsequenceClose j k t).trans (hfactor hj)⟩)
  have huniform : TendstoUniformly sequence U atTop := by
    refine Metric.tendstoUniformly_iff.mpr fun ε hε ↦ ?_
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hdecay ε hε
    refine eventually_atTop.mpr ⟨N, fun k hk t ↦ ?_⟩
    have hkbound := hN k hk
    rw [Real.dist_eq, sub_zero] at hkbound
    rw [dist_eq_norm]
    exact (hlimitClose k t).trans_lt ((le_abs_self _).trans_lt hkbound)
  have hUcontinuous : Continuous U :=
    huniform.continuous (Eventually.of_forall hsequenceContinuous)
  refine ⟨U, hUcontinuous, fun t ht ↦ ?_, ?_⟩
  · have hAt : IntervalIntegrable A volume 0 t :=
      hA.mono_set (Set.uIcc_subset_uIcc_left (Set.mem_uIcc_of_le ht.1 ht.2))
    have hequation : ∀ k, sequence k t =
        1 + ∫ s in (0 : ℝ)..t, approximation k s * sequence k s := by
      intro k
      obtain ⟨K, hK, hbound⟩ := exists_bound_of_continuous (hcontinuous k) hT
      show fundamentalMatrix (approximation k) T (clampTime T t) =
        1 + ∫ s in (0 : ℝ)..t,
          approximation k s * fundamentalMatrix (approximation k) T (clampTime T s)
      rw [clampTime_of_mem ht, fundamentalMatrix_eq_integral (hcontinuous k) hT hK hbound ht]
      congr 1
      refine intervalIntegral.integral_congr fun s hs ↦ ?_
      rw [Set.uIcc_of_le ht.1] at hs
      simp only [clampTime_of_mem ⟨hs.1, hs.2.trans ht.2⟩]
    have hright : Tendsto (fun k ↦ 1 + ∫ s in (0 : ℝ)..t, approximation k s * sequence k s)
        atTop (𝓝 (1 + ∫ s in (0 : ℝ)..t, A s * U s)) := by
      refine tendsto_const_nhds.add ?_
      rw [tendsto_iff_norm_sub_tendsto_zero]
      have hbounding : Tendsto (fun k : ℕ ↦ (Real.exp mass + mass) *
          (2 * (scale * (1 / ((k : ℝ) + 1))) * Real.exp mass * Real.exp mass)) atTop (𝓝 0) := by
        simpa using hdecay.const_mul (Real.exp mass + mass)
      refine squeeze_zero (fun _ ↦ norm_nonneg _) (fun k ↦ ?_) hbounding
      have hsplit : (∫ s in (0 : ℝ)..t, approximation k s * sequence k s) -
          ∫ s in (0 : ℝ)..t, A s * U s =
            (∫ s in (0 : ℝ)..t, (approximation k s - A s) * sequence k s) +
              ∫ s in (0 : ℝ)..t, A s * (sequence k s - U s) := by
        rw [← intervalIntegral.integral_sub
            (((hcontinuous k).mul (hsequenceContinuous k)).intervalIntegrable _ _)
            (hAt.mul_continuousOn hUcontinuous.continuousOn),
          ← intervalIntegral.integral_add
            ((((hcontinuous k).intervalIntegrable _ _).sub hAt).mul_continuousOn
              (hsequenceContinuous k).continuousOn)
            (hAt.mul_continuousOn ((hsequenceContinuous k).sub hUcontinuous).continuousOn)]
        congr 1
        funext s
        noncomm_ring
      rw [hsplit]
      have hfirst : ‖∫ s in (0 : ℝ)..t, (approximation k s - A s) * sequence k s‖ ≤
          Real.exp mass *
            (2 * (scale * (1 / ((k : ℝ) + 1))) * Real.exp mass * Real.exp mass) := by
        refine (intervalIntegral.norm_integral_le_integral_norm ht.1).trans ?_
        calc ∫ s in (0 : ℝ)..t, ‖(approximation k s - A s) * sequence k s‖
            ≤ ∫ s in (0 : ℝ)..t, ‖approximation k s - A s‖ * Real.exp mass := by
              refine intervalIntegral.integral_mono_on ht.1
                ((((hcontinuous k).intervalIntegrable _ _).sub hAt).mul_continuousOn
                  (hsequenceContinuous k).continuousOn).norm
                ((((hcontinuous k).intervalIntegrable _ _).sub hAt).norm.mul_const _)
                fun s _ ↦ ?_
              exact (norm_mul_le _ _).trans
                (mul_le_mul_of_nonneg_left (hsequenceBound k s) (norm_nonneg _))
          _ = (∫ s in (0 : ℝ)..t, ‖approximation k s - A s‖) * Real.exp mass :=
              intervalIntegral.integral_mul_const _ _
          _ ≤ scale * (1 / ((k : ℝ) + 1)) * Real.exp mass := by
              refine mul_le_mul_of_nonneg_right ?_ hexpPos.le
              exact (intervalIntegral.integral_mono_interval le_rfl ht.1 ht.2
                (ae_of_all _ fun _ ↦ norm_nonneg _) ((happroxIntegrable k).sub hA).norm).trans
                (hclose k)
          _ ≤ scale * (1 / ((k : ℝ) + 1)) * Real.exp mass *
                (2 * (Real.exp mass * Real.exp mass)) :=
              le_mul_of_one_le_right (mul_nonneg (hscaledNonneg k) hexpPos.le)
                (by nlinarith [hexpOne])
          _ = Real.exp mass *
                (2 * (scale * (1 / ((k : ℝ) + 1))) * Real.exp mass * Real.exp mass) := by ring
      have hsecond : ‖∫ s in (0 : ℝ)..t, A s * (sequence k s - U s)‖ ≤
          mass * (2 * (scale * (1 / ((k : ℝ) + 1))) * Real.exp mass * Real.exp mass) := by
        have hdecayNonneg : 0 ≤ 2 * (scale * (1 / ((k : ℝ) + 1))) * Real.exp mass *
            Real.exp mass :=
          mul_nonneg (mul_nonneg (mul_nonneg zero_le_two (hscaledNonneg k)) hexpPos.le)
            hexpPos.le
        refine (intervalIntegral.norm_integral_le_integral_norm ht.1).trans ?_
        calc ∫ s in (0 : ℝ)..t, ‖A s * (sequence k s - U s)‖
            ≤ ∫ s in (0 : ℝ)..t, ‖A s‖ *
                (2 * (scale * (1 / ((k : ℝ) + 1))) * Real.exp mass * Real.exp mass) := by
              refine intervalIntegral.integral_mono_on ht.1
                ((hAt.mul_continuousOn ((hsequenceContinuous k).sub hUcontinuous).continuousOn).norm)
                (hAt.norm.mul_const _) fun s _ ↦ ?_
              refine (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
              rw [norm_sub_rev]
              exact hlimitClose k s
          _ = (∫ s in (0 : ℝ)..t, ‖A s‖) *
                (2 * (scale * (1 / ((k : ℝ) + 1))) * Real.exp mass * Real.exp mass) :=
              intervalIntegral.integral_mul_const _ _
          _ ≤ mass * (2 * (scale * (1 / ((k : ℝ) + 1))) * Real.exp mass * Real.exp mass) := by
              refine mul_le_mul_of_nonneg_right ?_ hdecayNonneg
              have hmono := intervalIntegral.integral_mono_interval le_rfl ht.1 ht.2
                (ae_of_all _ fun _ ↦ norm_nonneg _) hA.norm
              rw [hmass]
              linarith
      calc ‖(∫ s in (0 : ℝ)..t, (approximation k s - A s) * sequence k s) +
            ∫ s in (0 : ℝ)..t, A s * (sequence k s - U s)‖
          ≤ Real.exp mass * (2 * (scale * (1 / ((k : ℝ) + 1))) * Real.exp mass * Real.exp mass) +
              mass * (2 * (scale * (1 / ((k : ℝ) + 1))) * Real.exp mass * Real.exp mass) :=
            (norm_add_le _ _).trans (add_le_add hfirst hsecond)
        _ = (Real.exp mass + mass) *
              (2 * (scale * (1 / ((k : ℝ) + 1))) * Real.exp mass * Real.exp mass) := by ring
    exact tendsto_nhds_unique ((hU t).congr fun k ↦ hequation k) hright
  · have hTmem : T ∈ Set.Icc 0 T := ⟨hT, le_rfl⟩
    refine (hU T).congr fun k ↦ ?_
    show fundamentalMatrix (approximation k) T (clampTime T T) =
      fundamentalMatrix (approximation k) T T
    rw [clampTime_of_mem hTmem]

/-! ## NOTE1 section 2.4 -/

/-- **NOTE1 section 2.4: rate histories with integrable rates preserve locus-exchangeable
realizability.**  For a rate history whose rate coordinates are integrable on `[0, T]`, the
integral equation `U(t) = 1 + ∫₀ᵗ A(s) U(s) ds` with the corpus generator of the rate law at
each time has a continuous solution; every continuous solution agrees with it on the horizon; and
its value at `T` carries every locus-exchangeably realizable stored state to a locus-exchangeably
realizable one. -/
theorem integrableRateHistory_preserves_locusExchangeable_realization {D : ℕ}
    (rates : ℝ → ManyDemeLDRates D) {T : ℝ} (hT : 0 ≤ T)
    (hintegrable : IntervalIntegrable (fun t ↦ rateCoordinates (rates t)) volume 0 T) :
    ∃ propagator : ℝ → Matrix (AffineLowOrderLDCoordinate D) (AffineLowOrderLDCoordinate D) ℝ,
      Continuous propagator ∧
      (∀ t ∈ Set.Icc 0 T, propagator t =
        1 + ∫ s in (0 : ℝ)..t, augmentedLowOrderLDGenerator (rates s) * propagator s) ∧
      (∀ other : ℝ → Matrix (AffineLowOrderLDCoordinate D) (AffineLowOrderLDCoordinate D) ℝ,
        Continuous other →
        (∀ t ∈ Set.Icc 0 T, other t =
          1 + ∫ s in (0 : ℝ)..t, augmentedLowOrderLDGenerator (rates s) * other s) →
        ∀ t ∈ Set.Icc 0 T, other t = propagator t) ∧
      ∀ {state : AffineLowOrderLDCoordinate D → ℝ},
        LocusExchangeableLowOrderLDHaplotypeRealization state →
        Nonempty (LocusExchangeableLowOrderLDHaplotypeRealization
          ((propagator T).mulVec state)) := by
  obtain ⟨K, hK, _, hlipschitz⟩ := exists_generator_lipschitz D
  have hgenerator := intervalIntegrable_augmentedLowOrderLDGenerator hintegrable
  have hstep : ∀ k : ℕ, (0 : ℝ) < 1 / ((k : ℝ) + 1) := fun k ↦ by positivity
  choose path hpath hpathClose using fun k : ℕ ↦
    exists_continuous_rates_integral_norm_sub_le hT hintegrable (hstep k)
  have hpathGenerator : ∀ k, Continuous fun t ↦ augmentedLowOrderLDGenerator (path k t) :=
    fun k ↦ continuous_augmentedLowOrderLDGenerator (hpath k)
  have hscale : 0 ≤ K * (1 + T) := mul_nonneg hK (by linarith)
  have happroximation : ∀ k : ℕ,
      ∫ s in (0 : ℝ)..T, ‖generatorPath (path k) T s - augmentedLowOrderLDGenerator (rates s)‖ ≤
        K * (1 + T) * (1 / ((k : ℝ) + 1)) := by
    intro k
    have hsame : (∫ s in (0 : ℝ)..T,
        ‖generatorPath (path k) T s - augmentedLowOrderLDGenerator (rates s)‖) =
          ∫ s in (0 : ℝ)..T,
            ‖augmentedLowOrderLDGenerator (path k s) - augmentedLowOrderLDGenerator (rates s)‖ := by
      refine intervalIntegral.integral_congr fun s hs ↦ ?_
      rw [Set.uIcc_of_le hT] at hs
      simp only [generatorPath_of_mem (path k) hs]
    rw [hsame]
    calc ∫ s in (0 : ℝ)..T,
          ‖augmentedLowOrderLDGenerator (path k s) - augmentedLowOrderLDGenerator (rates s)‖
        ≤ ∫ s in (0 : ℝ)..T, K * ‖rateCoordinates (path k s) - rateCoordinates (rates s)‖ :=
          intervalIntegral.integral_mono_on hT
            (((hpathGenerator k).intervalIntegrable 0 T).sub hgenerator).norm
            ((((hpath k).intervalIntegrable 0 T).sub hintegrable).norm.const_mul K)
            fun s _ ↦ hlipschitz (path k s) (rates s)
      _ = K * ∫ s in (0 : ℝ)..T, ‖rateCoordinates (path k s) - rateCoordinates (rates s)‖ :=
          intervalIntegral.integral_const_mul _ _
      _ ≤ K * (1 / ((k : ℝ) + 1) * (1 + T)) := mul_le_mul_of_nonneg_left (hpathClose k) hK
      _ = K * (1 + T) * (1 / ((k : ℝ) + 1)) := by ring
  obtain ⟨propagator, hcontinuous, hequation, hlimit⟩ :=
    exists_integral_solution_of_continuous_approximation hT hgenerator hscale
      (fun k ↦ generatorPath (path k) T)
      (fun k ↦ continuous_generatorPath hT (hpathGenerator k).continuousOn) happroximation
  refine ⟨propagator, hcontinuous, hequation, fun other hother hotherEq ↦
    eq_of_integral_eq hT hgenerator hother hcontinuous hotherEq hequation, ?_⟩
  intro state realization
  have hsampled : ∀ k : ℕ,
      (fundamentalMatrix (generatorPath (path k) T) T T).mulVec state ∈ exchangeableStates D := by
    intro k
    obtain ⟨propagated⟩ := rateHistory_preserves_locusExchangeable_realization (path k) hT
      (hpathGenerator k).continuousOn realization
    exact (mem_exchangeableStates_iff _).mpr ⟨propagated⟩
  have hmapped : Tendsto
      (fun k ↦ (fundamentalMatrix (generatorPath (path k) T) T T).mulVec state)
      atTop (𝓝 ((propagator T).mulVec state)) :=
    ((EulerInvariantSet.mulVecMap state).continuous_of_finiteDimensional.tendsto _).comp hlimit
  exact (mem_exchangeableStates_iff _).mp
    ((isClosed_exchangeableStates D).mem_of_tendsto hmapped (Eventually.of_forall hsampled))

end

end Descent.Portability.IntegrableRateRealization
