/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.ExactMetricEvaluation

assert_below Descent.Decision Descent.Program

/-!
Finite exact report results: sharp binary-risk ambiguity, conditional calibration
transport, its unchanged-mechanism two-locus witness, prior-odds correction, and
the additive projection of a fixed interaction. Finite conditional transport is
explicitly a finite specialization; arbitrary-measure transport is separate.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.ReportFiniteCalibrationLaw

open FiniteReportLaw

/-- Excess Brier risk at the two equally likely predictor states. -/
noncomputable def excessRisk (fminus fplus delta : ℝ) : ℝ :=
  ((fminus - (1 / 2 - delta)) ^ 2 + (fplus - (1 / 2 + delta)) ^ 2) / 2

/-- The two observationally compatible worlds have this exact average excess risk. -/
theorem ambiguity_average (fminus fplus delta : ℝ) :
    (excessRisk fminus fplus delta + excessRisk fminus fplus (-delta)) / 2 =
      ((fminus - 1 / 2) ^ 2 + (fplus - 1 / 2) ^ 2) / 2 + delta ^ 2 := by
  unfold excessRisk
  ring

/-- The report's sharp minimax excess-risk lower bound. -/
theorem ambiguity_lower_bound (fminus fplus delta : ℝ) :
    delta ^ 2 ≤ max (excessRisk fminus fplus delta) (excessRisk fminus fplus (-delta)) := by
  have ha := ambiguity_average fminus fplus delta
  have h1 := le_max_left (excessRisk fminus fplus delta) (excessRisk fminus fplus (-delta))
  have h2 := le_max_right (excessRisk fminus fplus delta) (excessRisk fminus fplus (-delta))
  nlinarith [sq_nonneg (fminus - 1 / 2), sq_nonneg (fplus - 1 / 2)]

theorem ambiguity_attained (delta : ℝ) :
    excessRisk (1 / 2) (1 / 2) delta = delta ^ 2 := by
  unfold excessRisk
  ring

theorem ambiguity_valid_probabilities (delta : ℝ) (hd : 0 < delta) (hu : delta ≤ 1 / 2) :
    0 ≤ 1 / 2 - delta ∧ 1 / 2 - delta ≤ 1 ∧
      0 ≤ 1 / 2 + delta ∧ 1 / 2 + delta ≤ 1 := by
  constructor <;> first | linarith | constructor
  all_goals first | linarith | constructor <;> linarith

/-- Total Brier risk adds the identical Bernoulli noise in the two worlds. -/
theorem ambiguity_total_minimax (fminus fplus delta : ℝ) :
    1 / 4 ≤ max (excessRisk fminus fplus delta + (1 / 4 - delta ^ 2))
      (excessRisk fminus fplus (-delta) + (1 / 4 - delta ^ 2)) ∧
    excessRisk (1 / 2) (1 / 2) delta + (1 / 4 - delta ^ 2) = 1 / 4 := by
  rw [max_add_add_right, ambiguity_attained]
  constructor
  · linarith [ambiguity_lower_bound fminus fplus delta]
  · ring

variable {X A : Type*} [Fintype X] [DecidableEq A]

noncomputable def fiberSum (p : FiniteReportLaw X) (score : X → A) (a : A)
    (f : X → ℝ) : ℝ := ∑ x, if score x = a then p.mass x * f x else 0

noncomputable def fiberMass (p : FiniteReportLaw X) (score : X → A) (a : A) : ℝ :=
  fiberSum p score a (fun _ ↦ 1)

noncomputable def fiberMean (p : FiniteReportLaw X) (score : X → A) (a : A)
    (f : X → ℝ) : ℝ := fiberSum p score a f / fiberMass p score a

noncomputable def fiberCovariance (p : FiniteReportLaw X) (score : X → A) (a : A)
    (f g : X → ℝ) : ℝ :=
  fiberMean p score a (fun x ↦ f x * g x) - fiberMean p score a f * fiberMean p score a g

private theorem fiberSum_sub (p : FiniteReportLaw X) (score : X → A) (a : A)
    (f g : X → ℝ) :
    fiberSum p score a (fun x ↦ f x - g x) = fiberSum p score a f - fiberSum p score a g := by
  simp only [fiberSum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro x _
  split_ifs <;> ring

/-- Finite conditional change of measure, derived from the pointwise density. -/
theorem fiber_change_of_measure (p q : FiniteReportLaw X) (score : X → A) (a : A)
    (r f : X → ℝ) (hr : ∀ x, q.mass x = p.mass x * r x)
    (hp : fiberMass p score a ≠ 0) :
    fiberMean q score a f =
      fiberMean p score a (fun x ↦ r x * f x) / fiberMean p score a r := by
  have hn : fiberSum q score a f = fiberSum p score a (fun x ↦ r x * f x) := by
    simp only [fiberSum, hr, mul_assoc]
  have hd : fiberMass q score a = fiberSum p score a r := by
    simp [fiberMass, fiberSum, hr]
  simp only [fiberMean, hn, hd]
  field_simp

/-- Theorem 3 on finite predictor spaces, with both support denominators explicit. -/
theorem finite_calibration_transport (p q : FiniteReportLaw X) (score : X → A) (a : A)
    (r etaS etaT : X → ℝ) (hr : ∀ x, q.mass x = p.mass x * r x)
    (hp : fiberMass p score a ≠ 0) (hd : fiberMean p score a r ≠ 0) :
    fiberMean q score a etaT - fiberMean p score a etaS =
      fiberMean p score a (fun x ↦ r x * (etaT x - etaS x)) / fiberMean p score a r +
      fiberCovariance p score a r etaS / fiberMean p score a r := by
  rw [fiber_change_of_measure p q score a r etaT hr hp]
  have hn : fiberMean p score a (fun x ↦ r x * (etaT x - etaS x)) =
      fiberMean p score a (fun x ↦ r x * etaT x) -
        fiberMean p score a (fun x ↦ r x * etaS x) := by
    simp only [mul_sub, fiberMean, fiberSum_sub, sub_div]
  rw [hn, fiberCovariance]
  field_simp
  ring

/-- Gauge freedom is pathwise, so no distributional assumption can remove it. -/
theorem residual_gauge {J : Type*} [Fintype J] (causal beta shift : J → ℝ) (residual : ℝ) :
    (∑ j, causal j * (beta j + shift j)) + (residual - ∑ j, causal j * shift j) =
      (∑ j, causal j * beta j) + residual := by
  simp only [mul_add, Finset.sum_add_distrib]
  ring

/-- Independent Bernoulli two-locus probability law. -/
noncomputable def twoLocusLaw (p1 p2 : ℝ) (h1 : 0 ≤ p1 ∧ p1 ≤ 1)
    (h2 : 0 ≤ p2 ∧ p2 ≤ 1) : FiniteReportLaw (Bool × Bool) where
  mass x := (if x.1 then p1 else 1 - p1) * (if x.2 then p2 else 1 - p2)
  mass_nonneg x := mul_nonneg (by split_ifs <;> linarith [h1.1, h1.2])
    (by split_ifs <;> linarith [h2.1, h2.2])
  mass_sum := by simp [Fintype.sum_prod_type]; ring

def allele (b : Bool) : ℝ := if b then 1 else 0

def interaction (x : Bool × Bool) : ℝ := allele x.1 * allele x.2

def additiveFit (p1 p2 : ℝ) (x : Bool × Bool) : ℝ :=
  -p1 * p2 + p2 * allele x.1 + p1 * allele x.2

/-- The residual identity underlying Proposition 5.1. -/
theorem interaction_residual (p1 p2 : ℝ) (x : Bool × Bool) :
    interaction x - additiveFit p1 p2 x = (allele x.1 - p1) * (allele x.2 - p2) := by
  unfold interaction additiveFit
  ring

/-- Exact risk of every affine competitor. The extra terms certify projection
optimality, not merely a candidate set of regression coefficients. -/
theorem interaction_risk_decomposition (p1 p2 : ℝ) (h1 : 0 ≤ p1 ∧ p1 ≤ 1)
    (h2 : 0 ≤ p2 ∧ p2 ≤ 1) (a b c : ℝ) :
    (twoLocusLaw p1 p2 h1 h2).expectation
      (fun x ↦ (interaction x - (a + b * allele x.1 + c * allele x.2)) ^ 2) =
      p1 * (1 - p1) * p2 * (1 - p2) +
      (a + b * p1 + c * p2 - p1 * p2) ^ 2 +
      (b - p2) ^ 2 * p1 * (1 - p1) + (c - p1) ^ 2 * p2 * (1 - p2) := by
  simp [expectation, twoLocusLaw, interaction, allele, Fintype.sum_prod_type]
  ring

/-- The displayed additive fit attains the exact irreducible interaction variance. -/
theorem interaction_projection_risk (p1 p2 : ℝ) (h1 : 0 ≤ p1 ∧ p1 ≤ 1)
    (h2 : 0 ≤ p2 ∧ p2 ≤ 1) :
    (twoLocusLaw p1 p2 h1 h2).expectation
      (fun x ↦ (interaction x - additiveFit p1 p2 x) ^ 2) =
        p1 * (1 - p1) * p2 * (1 - p2) := by
  simpa [additiveFit, mul_comm] using interaction_risk_decomposition p1 p2 h1 h2 (-p1 * p2) p2 p1

/-- Independent source loci with both frequencies one half. -/
noncomputable def witnessSource : FiniteReportLaw (Bool × Bool) :=
  twoLocusLaw (1 / 2) (1 / 2) (by norm_num) (by norm_num)

/-- Target loci have complete negative association and unchanged marginals. -/
noncomputable def witnessTarget : FiniteReportLaw (Bool × Bool) where
  mass x := if x.1 = x.2 then 0 else 1 / 2
  mass_nonneg x := by split_ifs <;> norm_num
  mass_sum := by norm_num [Fintype.sum_prod_type]

noncomputable def witnessRisk (x : Bool × Bool) : ℝ := (allele x.1 + allele x.2) / 2

noncomputable def witnessScore (b : Bool) : ℝ := 1 / 4 + allele b / 2

/-- Both allele frequencies, both prevalences, and the complete score law agree. -/
theorem witness_matching_observations :
    (∀ i : Bool, witnessSource.expectation (fun x ↦ allele (if i then x.1 else x.2)) = 1 / 2 ∧
      witnessTarget.expectation (fun x ↦ allele (if i then x.1 else x.2)) = 1 / 2) ∧
    witnessSource.expectation witnessRisk = 1 / 2 ∧
    witnessTarget.expectation witnessRisk = 1 / 2 ∧
    (∀ b, fiberMass witnessSource Prod.fst b = 1 / 2 ∧
      fiberMass witnessTarget Prod.fst b = 1 / 2) := by
  constructor
  · intro i
    cases i <;> norm_num [expectation, witnessSource, witnessTarget, twoLocusLaw,
      allele, Fintype.sum_prod_type]
  · constructor
    · norm_num [expectation, witnessSource, twoLocusLaw, witnessRisk, allele,
        Fintype.sum_prod_type]
    · constructor
      · norm_num [expectation, witnessTarget, witnessRisk, allele, Fintype.sum_prod_type]
      · intro b
        cases b <;> norm_num [fiberMass, fiberSum, witnessSource, witnessTarget,
          twoLocusLaw, Fintype.sum_prod_type]

/-- The score is calibrated at source, but target calibration is constant one half. -/
theorem witness_calibration_curves (b : Bool) :
    fiberMean witnessSource Prod.fst b witnessRisk = witnessScore b ∧
      fiberMean witnessTarget Prod.fst b witnessRisk = 1 / 2 := by
  cases b <;> norm_num [fiberMean, fiberMass, fiberSum, witnessSource, witnessTarget,
    twoLocusLaw, witnessRisk, witnessScore, allele, Fintype.sum_prod_type]

/-- Nonzero calibration drift despite all the matching observations above. -/
theorem witness_target_calibration_error :
    witnessTarget.expectation (fun x ↦
      (fiberMean witnessTarget Prod.fst x.1 witnessRisk - witnessScore x.1) ^ 2) = 1 / 16 := by
  simp_rw [(witness_calibration_curves _).2]
  norm_num [expectation, witnessTarget, witnessScore, allele, Fintype.sum_prod_type]

/-- The witness obeys the source-support condition exactly. -/
theorem witness_density (x : Bool × Bool) :
    witnessTarget.mass x = witnessSource.mass x * (if x.1 = x.2 then 0 else 2) := by
  rcases x with ⟨a, b⟩
  cases a <;> cases b <;> norm_num [witnessTarget, witnessSource, twoLocusLaw]

/-- The counterexample's risk mechanism is additive and unchanged, while LD changes. -/
theorem witness_joint_change :
    witnessSource.expectation interaction = 1 / 4 ∧
      witnessTarget.expectation interaction = 0 := by
  norm_num [expectation, witnessSource, witnessTarget, twoLocusLaw, interaction, allele,
    Fintype.sum_prod_type]

noncomputable def posterior (prior likelihood0 likelihood1 : ℝ) : ℝ :=
  prior * likelihood1 / ((1 - prior) * likelihood0 + prior * likelihood1)

noncomputable def priorOddsMultiplier (sourcePrior targetPrior : ℝ) : ℝ :=
  (targetPrior / (1 - targetPrior)) / (sourcePrior / (1 - sourcePrior))

/-- Proposition 4 at a shared-support predictor state. The two class-conditional
likelihoods are shared; a mere prevalence or genotype-law match is insufficient. -/
theorem prior_odds_correction (s t l0 l1 : ℝ) (hs : 0 < s ∧ s < 1)
    (ht : 0 < t ∧ t < 1) (h0 : 0 ≤ l0) (h1 : 0 ≤ l1) (hsupport : 0 < l0 + l1) :
    posterior t l0 l1 =
      priorOddsMultiplier s t * posterior s l0 l1 /
        (1 - posterior s l0 l1 + priorOddsMultiplier s t * posterior s l0 l1) := by
  have hs0 : s ≠ 0 := ne_of_gt hs.1
  have hs1 : 1 - s ≠ 0 := ne_of_gt (sub_pos.mpr hs.2)
  have ht1 : 1 - t ≠ 0 := ne_of_gt (sub_pos.mpr ht.2)
  have ds : 0 < (1 - s) * l0 + s * l1 := by
    by_cases hl : 0 < l0
    · exact add_pos_of_pos_of_nonneg (mul_pos (sub_pos.mpr hs.2) hl) (mul_nonneg hs.1.le h1)
    · have hl1 : 0 < l1 := by linarith
      exact add_pos_of_nonneg_of_pos (mul_nonneg (sub_pos.mpr hs.2).le h0)
        (mul_pos hs.1 hl1)
  have dt : 0 < (1 - t) * l0 + t * l1 := by
    by_cases hl : 0 < l0
    · exact add_pos_of_pos_of_nonneg (mul_pos (sub_pos.mpr ht.2) hl) (mul_nonneg ht.1.le h1)
    · have hl1 : 0 < l1 := by linarith
      exact add_pos_of_nonneg_of_pos (mul_nonneg (sub_pos.mpr ht.2).le h0)
        (mul_pos ht.1 hl1)
  have hd : 1 - posterior s l0 l1 + priorOddsMultiplier s t * posterior s l0 l1 =
      (1 - s) * ((1 - t) * l0 + t * l1) / ((1 - t) * ((1 - s) * l0 + s * l1)) := by
    unfold posterior priorOddsMultiplier
    field_simp
    ring
  rw [hd]
  unfold posterior priorOddsMultiplier
  field_simp [hs0, hs1, ht1, ne_of_gt ds, ne_of_gt dt]
  have ds' : l1 * s + (l0 - l0 * s) ≠ 0 := by nlinarith [ds]
  calc
    t * l1 = t * l1 * ((l1 * s + (l0 - l0 * s)) *
        (l1 * s + (l0 - l0 * s))⁻¹) := by rw [mul_inv_cancel₀ ds', mul_one]
    _ = _ := by ring

/-- Every affine competitor has risk at least the exact interaction residual risk. -/
theorem interaction_projection_minimizes (p1 p2 : ℝ) (h1 : 0 ≤ p1 ∧ p1 ≤ 1)
    (h2 : 0 ≤ p2 ∧ p2 ≤ 1) (a b c : ℝ) :
    (twoLocusLaw p1 p2 h1 h2).expectation
      (fun x ↦ (interaction x - additiveFit p1 p2 x) ^ 2) ≤
    (twoLocusLaw p1 p2 h1 h2).expectation
      (fun x ↦ (interaction x - (a + b * allele x.1 + c * allele x.2)) ^ 2) := by
  rw [interaction_projection_risk, interaction_risk_decomposition]
  have hb := mul_nonneg (mul_nonneg (sq_nonneg (b - p2)) h1.1) (sub_nonneg.mpr h1.2)
  have hc := mul_nonneg (mul_nonneg (sq_nonneg (c - p1)) h2.1) (sub_nonneg.mpr h2.2)
  nlinarith [sq_nonneg (a + b * p1 + c * p2 - p1 * p2)]

/-- A Bernoulli outcome's Brier risk splits into excess risk and Bernoulli noise. -/
theorem bernoulli_brier_split (q f : ℝ) :
    q * (1 - f) ^ 2 + (1 - q) * f ^ 2 = (f - q) ^ 2 + q * (1 - q) := by ring

/-- The ambiguity experiment's actual Brier risk has the asserted common noise. -/
theorem ambiguity_brier_identity (fminus fplus delta : ℝ) :
    (((1 / 2 - delta) * (1 - fminus) ^ 2 + (1 / 2 + delta) * fminus ^ 2) +
      ((1 / 2 + delta) * (1 - fplus) ^ 2 + (1 / 2 - delta) * fplus ^ 2)) / 2 =
        excessRisk fminus fplus delta + (1 / 4 - delta ^ 2) := by
  unfold excessRisk
  ring

/-- The interaction residual is centered, so its MSE is its variance. -/
theorem interaction_residual_mean_zero (p1 p2 : ℝ) (h1 : 0 ≤ p1 ∧ p1 ≤ 1)
    (h2 : 0 ≤ p2 ∧ p2 ≤ 1) :
    (twoLocusLaw p1 p2 h1 h2).expectation
      (fun x ↦ interaction x - additiveFit p1 p2 x) = 0 := by
  simp [expectation, twoLocusLaw, interaction, additiveFit, allele, Fintype.sum_prod_type]
  ring

theorem interaction_residual_variance (p1 p2 : ℝ) (h1 : 0 ≤ p1 ∧ p1 ≤ 1)
    (h2 : 0 ≤ p2 ∧ p2 ≤ 1) :
    (twoLocusLaw p1 p2 h1 h2).variance (fun x ↦ interaction x - additiveFit p1 p2 x) =
      p1 * (1 - p1) * p2 * (1 - p2) := by
  rw [variance_eq_rawMoments, interaction_residual_mean_zero, interaction_projection_risk]
  ring

end Descent.Portability.ReportFiniteCalibrationLaw
