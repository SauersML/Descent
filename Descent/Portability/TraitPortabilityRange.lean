/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.MechanismIdentification

assert_below Descent.Decision Descent.Program

/-!
# Exact architecture range under fixed genotype and genetic-variance inputs

Three independent standardized binary coordinates supply two causal loci and
independent phenotype noise. The source can be held at alignment one. Target
alignment varies while the full genotype law, score, genetic variance, and
noise variance remain fixed. The entire accuracy interval [0,heritability] is
attained, not just two endpoints.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.TraitPortabilityRange

open Foundations

noncomputable section

def sign (b : Bool) : ℝ := if b then 1 else -1

def architectureWorld (a b noise : ℝ) :
    DeploymentPopulation (Bool × Bool × Bool) (Fin 1) (Fin 2) where
  E := uniformExp (Bool × Bool × Bool)
  X := fun z _ ↦ sign z.1
  C := fun z ↦ ![sign z.1, sign z.2.1]
  β := ![a, b]
  h := fun z ↦ noise * sign z.2.2

/-- Moment formulas derived from the finite joint law, with no supplied
covariance, outcome-variance, or portability premises. -/
theorem architecture_moments (a b noise : ℝ) :
    (architectureWorld a b noise).scoreVariance (fun _ ↦ 1) = 1 ∧
      (architectureWorld a b noise).predictiveCovariance (fun _ ↦ 1) = a ∧
      (architectureWorld a b noise).outcomeVariance = a ^ 2 + b ^ 2 + noise ^ 2 := by
  norm_num [DeploymentPopulation.scoreVariance, DeploymentPopulation.predictiveCovariance,
    DeploymentPopulation.outcomeVariance, DeploymentPopulation.phenotype,
    DeploymentPopulation.score, variance_eq_expect_sq_sub_sq_mean,
    covariance_eq_expect_mul_sub_means, causalSignal, linScore, dot, Core.innerSum,
    architectureWorld, sign, uniformExp_apply, Fintype.sum_prod_type,
    Fintype.sum_bool, Fin.sum_univ_two]
  constructor <;> ring

def alignedWorld (rho noiseVariance : ℝ) :
    DeploymentPopulation (Bool × Bool × Bool) (Fin 1) (Fin 2) :=
  architectureWorld rho (Real.sqrt (1 - rho ^ 2)) (Real.sqrt noiseVariance)

/-- Genetic observations do not vary anywhere in the family. -/
theorem fixed_genotype_inputs (rho sigma noiseVariance : ℝ) :
    (alignedWorld rho noiseVariance).E = (alignedWorld sigma noiseVariance).E ∧
      (alignedWorld rho noiseVariance).X = (alignedWorld sigma noiseVariance).X ∧
      (alignedWorld rho noiseVariance).C = (alignedWorld sigma noiseVariance).C :=
  ⟨rfl, rfl, rfl⟩

theorem fixed_genetic_signal (rho noiseVariance : ℝ) (hr0 : 0 ≤ rho) (hr1 : rho ≤ 1) :
    ∑ j, (alignedWorld rho noiseVariance).β j ^ 2 = 1 := by
  have hs : 0 ≤ 1 - rho ^ 2 := by nlinarith
  simp [alignedWorld, architectureWorld, Fin.sum_univ_two, Real.sq_sqrt hs]

/-- The fixed signal is the actual genetic variance, not just an effect norm. -/
theorem actual_genetic_variance (rho noiseVariance : ℝ)
    (hr0 : 0 ≤ rho) (hr1 : rho ≤ 1) :
    variance (alignedWorld rho noiseVariance).E
      (causalSignal (alignedWorld rho noiseVariance).β
        (alignedWorld rho noiseVariance).C) = 1 := by
  have hs : 0 ≤ 1 - rho ^ 2 := by nlinarith
  have he : variance (alignedWorld rho noiseVariance).E
      (causalSignal (alignedWorld rho noiseVariance).β
        (alignedWorld rho noiseVariance).C) = rho ^ 2 + Real.sqrt (1 - rho ^ 2) ^ 2 := by
    norm_num [alignedWorld, architectureWorld, causalSignal, dot, Core.innerSum,
      variance_eq_expect_sq_sub_sq_mean, sign, uniformExp_apply,
      Fintype.sum_prod_type, Fintype.sum_bool, Fin.sum_univ_two]
    ring
  rw [he, Real.sq_sqrt hs]
  ring

/-- Exact alignment-to-accuracy law on its full admissible interval. -/
theorem aligned_accuracy (rho noiseVariance : ℝ) (hr0 : 0 ≤ rho) (hr1 : rho ≤ 1)
    (hn : 0 ≤ noiseVariance) :
    (alignedWorld rho noiseVariance).r2 (fun _ ↦ 1) = rho ^ 2 / (1 + noiseVariance) := by
  have hs : 0 ≤ 1 - rho ^ 2 := by nlinarith
  have hm := architecture_moments rho (Real.sqrt (1 - rho ^ 2)) (Real.sqrt noiseVariance)
  unfold DeploymentPopulation.r2 alignedWorld
  rw [hm.1, hm.2.1, hm.2.2, Real.sq_sqrt hs, Real.sq_sqrt hn]
  congr 1
  ring

/-- The full interval is necessary and sufficient at fixed genotype law and
heritability 1/(1+noiseVariance). Source alignment may stay fixed at one. -/
theorem sharp_accuracy_range (noiseVariance q : ℝ) (hn : 0 ≤ noiseVariance) :
    (∃ rho : ℝ, 0 ≤ rho ∧ rho ≤ 1 ∧
      (alignedWorld rho noiseVariance).r2 (fun _ ↦ 1) = q) ↔
      0 ≤ q ∧ q ≤ 1 / (1 + noiseVariance) := by
  have hden : 0 < 1 + noiseVariance := by positivity
  constructor
  · rintro ⟨rho, hr0, hr1, rfl⟩
    rw [aligned_accuracy rho noiseVariance hr0 hr1 hn]
    exact ⟨div_nonneg (sq_nonneg rho) hden.le,
      (div_le_div_iff_of_pos_right hden).mpr (by nlinarith)⟩
  · rintro ⟨hq0, hq1⟩
    let rho := Real.sqrt (q * (1 + noiseVariance))
    have hr0 : 0 ≤ rho := Real.sqrt_nonneg _
    have hsq : rho ^ 2 = q * (1 + noiseVariance) :=
      Real.sq_sqrt (mul_nonneg hq0 hden.le)
    have hr1 : rho ≤ 1 := by
      have h := (le_div_iff₀ hden).mp hq1
      nlinarith
    refine ⟨rho, hr0, hr1, ?_⟩
    rw [aligned_accuracy rho noiseVariance hr0 hr1 hn, hsq]
    field_simp

end

end Descent.Portability.TraitPortabilityRange
