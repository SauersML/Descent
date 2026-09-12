/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.NeutralRateLipschitz
import Descent.Portability.NeutralRateHistoryRealization
import Descent.Portability.IntegrableRateRealization

assert_below Descent.Decision Descent.Program

/-!
# The neutral dual propagator of an integrable rate history

NOTE1 §4.2a asks for the dual semigroup of (20) under measurable rate histories with integrable
norm, by the approximation of §2.4. `NeutralRateHistoryRealization` carries it out when the dual
generator of the history is continuous on the horizon. This module removes that restriction.

The rates are approximated, not the generators, so that every approximation is again the dual
generator of a rate law. `positivePartNeutralRates` turns a signed coordinate tuple into a rate law
by symmetrizing its mutation rates and clipping at zero. Its coordinates depend continuously on the
tuple (`continuous_coordinates_positivePartNeutralRates`), and clipping never moves a tuple farther
from a genuine rate law (`norm_coordinates_positivePartNeutralRates_sub_le`). With the density of
continuous functions in `L¹`, every rate history with integrable coordinates is within any `ε` in
`L¹([0, T])` of a rate history with continuous coordinates (`exists_continuous_neutralRates_near`).
By `NeutralRateLipschitz.exists_dualGenerator_lipschitz` their dual generators are within a fixed
multiple of that, and the generator path is integrable (`intervalIntegrable_dualGenerator`).

`exists_neutralIntegrablePropagator` is the existence half. Along `ε = 1 / (k + 1)` the continuous
approximations give generator paths converging to the dual generator of the history in `L¹`, so
`IntegrableRateRealization.exists_integral_solution_of_continuous_approximation` gives a continuous
solution of `U(t) = 1 + ∫₀ᵗ Q(s) U(s) ds`, and the approximating fundamental matrices converge to it
at the horizon. Every approximating propagator keeps the budget moments of a state in the
realization body of the budget-moment feature by
`NeutralRateHistoryRealization.rateHistoryDualPropagator_mulVec_mem_realizationBody`, and the body
is closed, so the solution does too.

`neutralIntegrablePropagator_mulVec_mem_realizationBody` holds for every continuous solution of the
integral equation, which agrees with the one just built by
`IntegrableRateRealization.eq_of_integral_eq`, and `exists_neutralIntegrableLaw` is the realization
by a finitely supported probability law on frequency states whose budget-respecting configuration
moments are `U(T) H(x₀)`.

Scope. The hypothesis is interval integrability of the rate coordinates on `[0, T]`, that is, a
measurable rate history with integrable norm, NOTE1's hypothesis; the dual generator path is then
integrable by the Lipschitz bound. The propagator is characterized by the integral equation. The
Markov-kernel limit of the time-varying history is not constructed here.

## Empirical status

None. The bodies here are calculus and point-set topology: integral inequalities, a limit of
fundamental matrices, and membership in a closed convex set, so no measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.NeutralIntegrableRateRealization

open MeasureTheory ProbabilityTheory MvPolynomial Filter Topology Descent.Coalescent
  PartialHaplotypeCarrier PartialHaplotypeDualGenerator PartialHaplotypeDualSemigroup
  NeutralFellerGenerator PartialHaplotypeMicroscopicApproximation PartialHaplotypePanelLikelihood
  FiniteMixtureKernel RealizationBody KernelRealizationPreservation LinearFundamentalMatrix
  NeutralMicroscopicEulerLimit NeutralKernelPanelLikelihood NeutralHistoryKernel
  NeutralRateHistoryRealization NeutralRateLipschitz
open IntegrableGeneratorPropagator (exists_continuous_integral_norm_sub_le)
open IntegrableRateRealization (abs_max_zero_sub_le eq_of_integral_eq
  exists_integral_solution_of_continuous_approximation)
open scoped Matrix NNReal Matrix.Norms.Operator

noncomputable section

variable {Deme Locus : Type*} {Allele : Locus → Type*}
variable [Fintype Deme] [DecidableEq Deme] [Fintype Locus] [DecidableEq Locus]
  [∀ ℓ, Fintype (Allele ℓ)] [∀ ℓ, DecidableEq (Allele ℓ)]

/-! ## Clipped rate laws from signed coordinates -/

/-- The coordinates of the clipped rate law depend continuously on the signed tuple. -/
theorem continuous_coordinates_positivePartNeutralRates :
    Continuous fun x : NeutralRateCoordinates Deme Locus Allele ↦
      neutralRateCoordinates (positivePartNeutralRates x) := by
  have hcoalescence : Continuous fun x : NeutralRateCoordinates Deme Locus Allele ↦
      fun i : Deme ↦ max (x.1 i) 0 :=
    continuous_pi fun i ↦ ((continuous_apply i).comp continuous_fst).max continuous_const
  have hmigration : Continuous fun x : NeutralRateCoordinates Deme Locus Allele ↦
      fun i j : Deme ↦ max (x.2.1 i j) 0 :=
    continuous_pi fun i ↦ continuous_pi fun j ↦
      ((continuous_apply j).comp ((continuous_apply i).comp continuous_snd.fst)).max
        continuous_const
  have hrecombination : Continuous fun x : NeutralRateCoordinates Deme Locus Allele ↦
      fun selector : Locus → Bool ↦ max (x.2.2.1 selector) 0 :=
    continuous_pi fun selector ↦ ((continuous_apply selector).comp
      (continuous_fst.comp (continuous_snd.comp continuous_snd))).max continuous_const
  have hlast : Continuous fun x : NeutralRateCoordinates Deme Locus Allele ↦ x.2.2.2 :=
    continuous_snd.comp (continuous_snd.comp continuous_snd)
  have hmutation : Continuous fun x : NeutralRateCoordinates Deme Locus Allele ↦
      fun ℓ (a b : Allele ℓ) ↦ max (symmetrizeMutation x.2.2.2 ℓ a b) 0 := by
    refine continuous_pi fun ℓ ↦ continuous_pi fun a ↦ continuous_pi fun b ↦ ?_
    have hab : Continuous fun x : NeutralRateCoordinates Deme Locus Allele ↦ x.2.2.2 ℓ a b :=
      (continuous_apply b).comp ((continuous_apply a).comp ((continuous_apply ℓ).comp hlast))
    have hba : Continuous fun x : NeutralRateCoordinates Deme Locus Allele ↦ x.2.2.2 ℓ b a :=
      (continuous_apply a).comp ((continuous_apply b).comp ((continuous_apply ℓ).comp hlast))
    exact ((hab.add hba).div_const 2).max continuous_const
  exact hcoalescence.prodMk (hmigration.prodMk (hrecombination.prodMk hmutation))

/-- **Clipping never moves a signed tuple farther from a rate law.** Every clipped coordinate is
within the tuple's distance of a nonnegative rate, and a symmetrized mutation rate is within the
average of two such distances of a symmetric one. -/
theorem norm_coordinates_positivePartNeutralRates_sub_le
    (x : NeutralRateCoordinates Deme Locus Allele) (rates : NeutralRates Deme Locus Allele) :
    ‖neutralRateCoordinates (positivePartNeutralRates x) - neutralRateCoordinates rates‖ ≤
      ‖x - neutralRateCoordinates rates‖ := by
  generalize hgap : ‖x - neutralRateCoordinates rates‖ = gap
  have hgapNonneg : 0 ≤ gap := (norm_nonneg _).trans_eq hgap
  have hfirst : ‖(x - neutralRateCoordinates rates).1‖ ≤ gap :=
    (norm_fst_le (x - neutralRateCoordinates rates)).trans hgap.le
  have hsecond : ‖(x - neutralRateCoordinates rates).2.1‖ ≤ gap :=
    (norm_fst_le (x - neutralRateCoordinates rates).2).trans
      ((norm_snd_le (x - neutralRateCoordinates rates)).trans hgap.le)
  have hthird : ‖(x - neutralRateCoordinates rates).2.2.1‖ ≤ gap :=
    (norm_fst_le (x - neutralRateCoordinates rates).2.2).trans
      ((norm_snd_le (x - neutralRateCoordinates rates).2).trans
        ((norm_snd_le (x - neutralRateCoordinates rates)).trans hgap.le))
  have hfourth : ‖(x - neutralRateCoordinates rates).2.2.2‖ ≤ gap :=
    (norm_snd_le (x - neutralRateCoordinates rates).2.2).trans
      ((norm_snd_le (x - neutralRateCoordinates rates).2).trans
        ((norm_snd_le (x - neutralRateCoordinates rates)).trans hgap.le))
  refine (Prod.norm_def _).trans_le (max_le ?_ ((Prod.norm_def _).trans_le
    (max_le ?_ ((Prod.norm_def _).trans_le (max_le ?_ ?_)))))
  · refine (pi_norm_le_iff_of_nonneg hgapNonneg).mpr fun i ↦ ?_
    have hcomponent := (norm_le_pi_norm (x - neutralRateCoordinates rates).1 i).trans hfirst
    simp only [neutralRateCoordinates, positivePartNeutralRates, Prod.fst_sub, Pi.sub_apply,
      Real.norm_eq_abs] at hcomponent ⊢
    exact (abs_max_zero_sub_le (rates.coalescence_nonneg i)).trans hcomponent
  · refine (pi_norm_le_iff_of_nonneg hgapNonneg).mpr fun i ↦ ?_
    refine (pi_norm_le_iff_of_nonneg hgapNonneg).mpr fun j ↦ ?_
    have hcomponent := (norm_le_pi_norm ((x - neutralRateCoordinates rates).2.1 i) j).trans
      ((norm_le_pi_norm (x - neutralRateCoordinates rates).2.1 i).trans hsecond)
    simp only [neutralRateCoordinates, positivePartNeutralRates, Prod.fst_sub, Prod.snd_sub,
      Pi.sub_apply, Real.norm_eq_abs] at hcomponent ⊢
    exact (abs_max_zero_sub_le (rates.migration_nonneg i j)).trans hcomponent
  · refine (pi_norm_le_iff_of_nonneg hgapNonneg).mpr fun selector ↦ ?_
    have hcomponent :=
      (norm_le_pi_norm (x - neutralRateCoordinates rates).2.2.1 selector).trans hthird
    simp only [neutralRateCoordinates, positivePartNeutralRates, Prod.fst_sub, Prod.snd_sub,
      Pi.sub_apply, Real.norm_eq_abs] at hcomponent ⊢
    exact (abs_max_zero_sub_le (rates.recombination_nonneg selector)).trans hcomponent
  · refine (pi_norm_le_iff_of_nonneg hgapNonneg).mpr fun ℓ ↦ ?_
    refine (pi_norm_le_iff_of_nonneg hgapNonneg).mpr fun a ↦ ?_
    refine (pi_norm_le_iff_of_nonneg hgapNonneg).mpr fun b ↦ ?_
    have hab := (norm_le_pi_norm ((x - neutralRateCoordinates rates).2.2.2 ℓ a) b).trans
      ((norm_le_pi_norm ((x - neutralRateCoordinates rates).2.2.2 ℓ) a).trans
        ((norm_le_pi_norm (x - neutralRateCoordinates rates).2.2.2 ℓ).trans hfourth))
    have hba := (norm_le_pi_norm ((x - neutralRateCoordinates rates).2.2.2 ℓ b) a).trans
      ((norm_le_pi_norm ((x - neutralRateCoordinates rates).2.2.2 ℓ) b).trans
        ((norm_le_pi_norm (x - neutralRateCoordinates rates).2.2.2 ℓ).trans hfourth))
    simp only [neutralRateCoordinates, positivePartNeutralRates, symmetrizeMutation, Prod.snd_sub,
      Pi.sub_apply, Real.norm_eq_abs] at hab hba ⊢
    rw [rates.mutation_symm ℓ b a] at hba
    obtain ⟨hab1, hab2⟩ := abs_le.mp hab
    obtain ⟨hba1, hba2⟩ := abs_le.mp hba
    refine (abs_max_zero_sub_le (rates.mutation_nonneg ℓ a b)).trans
      (abs_le.mpr ⟨?_, ?_⟩) <;> linarith

/-- **Continuous rate histories approximate integrable ones in `L¹`.** -/
theorem exists_continuous_neutralRates_near {rates : ℝ → NeutralRates Deme Locus Allele} {T : ℝ}
    (hT : 0 ≤ T)
    (hintegrable : IntervalIntegrable (fun t ↦ neutralRateCoordinates (rates t)) volume 0 T)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ path : ℝ → NeutralRates Deme Locus Allele,
      Continuous (fun t ↦ neutralRateCoordinates (path t)) ∧
      ∫ t in (0 : ℝ)..T,
        ‖neutralRateCoordinates (path t) - neutralRateCoordinates (rates t)‖ ≤ ε := by
  obtain ⟨g, hg, hclose⟩ := exists_continuous_integral_norm_sub_le hT hintegrable hε
  have hpath : Continuous fun t ↦ neutralRateCoordinates (positivePartNeutralRates (g t)) :=
    continuous_coordinates_positivePartNeutralRates.comp hg
  refine ⟨fun t ↦ positivePartNeutralRates (g t), hpath, le_trans
    (intervalIntegral.integral_mono_on hT
      ((hpath.intervalIntegrable 0 T).sub hintegrable).norm
      (hintegrable.sub (hg.intervalIntegrable 0 T)).norm fun t _ ↦ ?_) hclose⟩
  exact (norm_coordinates_positivePartNeutralRates_sub_le (g t) (rates t)).trans_eq
    (norm_sub_rev _ _)

/-! ## The generator path of a rate history -/

/-- Along any rate history the dual generator is the linear map at the rate coordinates. -/
theorem dualGenerator_comp_eq_linearMap (capacity : Locus → ℕ)
    (path : ℝ → NeutralRates Deme Locus Allele) :
    (fun t ↦ dualGenerator (path t) capacity) =
      fun t ↦ dualGeneratorLinearMap capacity (neutralRateCoordinates (path t)) :=
  funext fun t ↦ dualGenerator_eq_dualGeneratorLinearMap (path t) capacity

/-- A rate history with continuous coordinates has a dual generator continuous on every
horizon. -/
theorem continuousOn_dualGenerator_of_continuous {path : ℝ → NeutralRates Deme Locus Allele}
    (hpath : Continuous fun t ↦ neutralRateCoordinates (path t)) (capacity : Locus → ℕ) (T : ℝ) :
    ContinuousOn (fun t ↦ dualGenerator (path t) capacity) (Set.Icc 0 T) := by
  rw [dualGenerator_comp_eq_linearMap capacity path]
  exact ((dualGeneratorLinearMap (Deme := Deme) (Allele := Allele)
    capacity).continuous_of_finiteDimensional.comp hpath).continuousOn

/-- A rate history with integrable coordinates has an integrable dual generator path. -/
theorem intervalIntegrable_dualGenerator {rates : ℝ → NeutralRates Deme Locus Allele} {T : ℝ}
    (capacity : Locus → ℕ)
    (hintegrable : IntervalIntegrable (fun t ↦ neutralRateCoordinates (rates t)) volume 0 T) :
    IntervalIntegrable (fun t ↦ dualGenerator (rates t) capacity) volume 0 T := by
  rw [dualGenerator_comp_eq_linearMap capacity rates]
  let bounded := LinearMap.toContinuousLinearMap
    (dualGeneratorLinearMap (Deme := Deme) (Allele := Allele) capacity)
  exact ⟨bounded.integrable_comp hintegrable.1, bounded.integrable_comp hintegrable.2⟩

/-! ## NOTE1 §4.2a for integrable rate histories -/

/-- **A realizability-preserving solution of the integral equation.** For a rate history whose
rate coordinates are integrable on `[0, T]`, the integral equation with the dual generator of the
rate law at each time has a continuous solution whose value at `T` carries the budget moments of
every frequency state into the realization body of the budget-moment feature. -/
theorem exists_neutralIntegrablePropagator (rates : ℝ → NeutralRates Deme Locus Allele)
    (capacity : Locus → ℕ) {T : ℝ} (hT : 0 ≤ T)
    (hintegrable : IntervalIntegrable (fun t ↦ neutralRateCoordinates (rates t)) volume 0 T) :
    ∃ propagator : ℝ → Matrix (BudgetConfiguration Deme Locus Allele capacity)
        (BudgetConfiguration Deme Locus Allele capacity) ℝ,
      Continuous propagator ∧
      (∀ t ∈ Set.Icc 0 T,
        propagator t = 1 + ∫ s in (0 : ℝ)..t, dualGenerator (rates s) capacity * propagator s) ∧
      ∀ x0 : FrequencyState Deme Locus Allele,
        propagator T *ᵥ budgetMomentFeature capacity x0 ∈ realizationBody
          (budgetMomentFeature (Deme := Deme) (Locus := Locus) (Allele := Allele) capacity) := by
  obtain ⟨K, hK, hlipschitz⟩ :=
    exists_dualGenerator_lipschitz (Deme := Deme) (Allele := Allele) capacity
  have hgenerator := intervalIntegrable_dualGenerator capacity hintegrable
  have hstep : ∀ k : ℕ, (0 : ℝ) < 1 / ((k : ℝ) + 1) := fun k ↦ by positivity
  choose path hpath hpathClose using fun k : ℕ ↦
    exists_continuous_neutralRates_near hT hintegrable (hstep k)
  have hpathGenerator : ∀ k, ContinuousOn (fun t ↦ dualGenerator (path k t) capacity)
      (Set.Icc 0 T) := fun k ↦ continuousOn_dualGenerator_of_continuous (hpath k) capacity T
  have happroximation : ∀ k : ℕ,
      ∫ s in (0 : ℝ)..T,
          ‖dualGeneratorPath (path k) capacity T s - dualGenerator (rates s) capacity‖ ≤
        K * (1 / ((k : ℝ) + 1)) := by
    intro k
    calc ∫ s in (0 : ℝ)..T,
          ‖dualGeneratorPath (path k) capacity T s - dualGenerator (rates s) capacity‖
        ≤ ∫ s in (0 : ℝ)..T,
            K * ‖neutralRateCoordinates (path k s) - neutralRateCoordinates (rates s)‖ := by
          refine intervalIntegral.integral_mono_on hT
            (((continuous_dualGeneratorPath hT (hpathGenerator k)).intervalIntegrable 0 T).sub
              hgenerator).norm
            ((((hpath k).intervalIntegrable 0 T).sub hintegrable).norm.const_mul K)
            fun s hs ↦ ?_
          simp only [dualGeneratorPath, clampTime_of_mem hs]
          exact hlipschitz (path k s) (rates s)
      _ = K * ∫ s in (0 : ℝ)..T,
            ‖neutralRateCoordinates (path k s) - neutralRateCoordinates (rates s)‖ :=
          intervalIntegral.integral_const_mul _ _
      _ ≤ K * (1 / ((k : ℝ) + 1)) := mul_le_mul_of_nonneg_left (hpathClose k) hK
  obtain ⟨propagator, hcontinuous, hequation, hlimit⟩ :=
    exists_integral_solution_of_continuous_approximation hT hgenerator hK
      (fun k ↦ dualGeneratorPath (path k) capacity T)
      (fun k ↦ continuous_dualGeneratorPath hT (hpathGenerator k)) happroximation
  refine ⟨propagator, hcontinuous, hequation, fun x0 ↦ ?_⟩
  have hmapped : Tendsto
      (fun k ↦ rateHistoryDualPropagator (path k) capacity T *ᵥ budgetMomentFeature capacity x0)
      atTop (𝓝 (propagator T *ᵥ budgetMomentFeature capacity x0)) :=
    ((EulerInvariantSet.mulVecMap
      (budgetMomentFeature capacity x0)).continuous_of_finiteDimensional.tendsto _).comp hlimit
  exact (isClosed_realizationBody _ (continuous_budgetMomentFeature capacity)).mem_of_tendsto
    hmapped (Eventually.of_forall fun k ↦
      rateHistoryDualPropagator_mulVec_mem_realizationBody hT (hpathGenerator k) x0)

/-- **NOTE1 §4.2a for integrable rate histories: the propagator keeps moment vectors realizable.**
Every continuous solution of the integral equation of a rate history with integrable coordinates
carries the budget moments of every frequency state, at the horizon, into the realization body of
the budget-moment feature. -/
theorem neutralIntegrablePropagator_mulVec_mem_realizationBody
    (rates : ℝ → NeutralRates Deme Locus Allele) (capacity : Locus → ℕ) {T : ℝ} (hT : 0 ≤ T)
    (hintegrable : IntervalIntegrable (fun t ↦ neutralRateCoordinates (rates t)) volume 0 T)
    {propagator : ℝ → Matrix (BudgetConfiguration Deme Locus Allele capacity)
      (BudgetConfiguration Deme Locus Allele capacity) ℝ}
    (hcontinuous : Continuous propagator)
    (hequation : ∀ t ∈ Set.Icc 0 T,
      propagator t = 1 + ∫ s in (0 : ℝ)..t, dualGenerator (rates s) capacity * propagator s)
    (x0 : FrequencyState Deme Locus Allele) :
    propagator T *ᵥ budgetMomentFeature capacity x0 ∈ realizationBody
      (budgetMomentFeature (Deme := Deme) (Locus := Locus) (Allele := Allele) capacity) := by
  obtain ⟨solution, hsolution, hsolutionEquation, hbody⟩ :=
    exists_neutralIntegrablePropagator rates capacity hT hintegrable
  rw [eq_of_integral_eq hT (intervalIntegrable_dualGenerator capacity hintegrable) hcontinuous
    hsolution hequation hsolutionEquation T ⟨hT, le_rfl⟩]
  exact hbody x0

/-- **A realizing law for an integrable rate history.** At every initial state there is a finitely
supported probability law on frequency states whose budget-respecting configuration moments are
`U(T) H(x₀)`, for every continuous solution `U` of the integral equation. -/
theorem exists_neutralIntegrableLaw (rates : ℝ → NeutralRates Deme Locus Allele)
    (capacity : Locus → ℕ) {T : ℝ} (hT : 0 ≤ T)
    (hintegrable : IntervalIntegrable (fun t ↦ neutralRateCoordinates (rates t)) volume 0 T)
    {propagator : ℝ → Matrix (BudgetConfiguration Deme Locus Allele capacity)
      (BudgetConfiguration Deme Locus Allele capacity) ℝ}
    (hcontinuous : Continuous propagator)
    (hequation : ∀ t ∈ Set.Icc 0 T,
      propagator t = 1 + ∫ s in (0 : ℝ)..t, dualGenerator (rates s) capacity * propagator s)
    (x0 : FrequencyState Deme Locus Allele) :
    ∃ w : Fin (Fintype.card (BudgetConfiguration Deme Locus Allele capacity) + 1) → ℝ,
      ∃ point : Fin (Fintype.card (BudgetConfiguration Deme Locus Allele capacity) + 1)
          → FrequencyState Deme Locus Allele,
        (∀ k, 0 ≤ w k) ∧ ∑ k, w k = 1
          ∧ featureVector w point (budgetMomentFeature capacity)
            = propagator T *ᵥ budgetMomentFeature capacity x0 :=
  exists_law_of_mem_realizationBody _ _
    (neutralIntegrablePropagator_mulVec_mem_realizationBody rates capacity hT hintegrable
      hcontinuous hequation x0)

end

end Descent.Portability.NeutralIntegrableRateRealization
