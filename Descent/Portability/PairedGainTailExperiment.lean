/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.DecisionLossContrasts
import Mathlib.MeasureTheory.Integral.Prod

assert_below Descent.Decision Descent.Program

/-!
Decision-Directed Portability, Theorem 3. A fully specified six-outcome
experiment has fixed expected paired improvement and fixed improvement
variance, while the variance of individual squared loss grows without bound.
The parameterization by an amplitude permits exact polynomial moment proofs;
the manuscript's amplitude is the inverse square root of its probability.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.PairedGainTailExperiment

open MeasureTheory ProbabilityTheory

/-- A fair binary context. -/
noncomputable def contextLaw : Measure Bool :=
  ENNReal.ofReal (1 / 2 : ℝ) • Measure.dirac false +
    ENNReal.ofReal (1 / 2 : ℝ) • Measure.dirac true

/-- The sparse symmetric noise chooses zero, the positive atom, or the negative atom. -/
noncomputable def noiseLaw (p : ℝ) : Measure (Fin 3) :=
  ENNReal.ofReal (1 - p) • Measure.dirac 0 +
    ENNReal.ofReal (p / 2) • Measure.dirac 1 +
    ENNReal.ofReal (p / 2) • Measure.dirac 2

/-- The actual context/noise experiment has independent product sampling. -/
noncomputable def jointLaw (p : ℝ) : Measure (Bool × Fin 3) := contextLaw.prod (noiseLaw p)

/-- The context-specific repair is one half or three halves. -/
noncomputable def correction (w : Bool) : ℝ := if w then 3 / 2 else 1 / 2

/-- Noise values at the three atoms. -/
def noiseValue (a : ℝ) : Fin 3 → ℝ := ![0, a, -a]

/-- Baseline squared loss in the explicit experiment. -/
noncomputable def loss (a : ℝ) (z : Bool × Fin 3) : ℝ := (correction z.1 + noiseValue a z.2) ^ 2

/-- Paired loss reduction from deploying the known context correction. -/
noncomputable def improvement (a : ℝ) (z : Bool × Fin 3) : ℝ := loss a z - noiseValue a z.2 ^ 2

/-- The context law is normalized. -/
theorem context_probability : IsProbabilityMeasure contextLaw := by
  constructor
  simp only [contextLaw, Measure.add_apply, Measure.smul_apply, measure_univ,
    smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  norm_num

/-- The noise law is normalized, including the endpoint probability one. -/
theorem noise_probability (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1) :
    IsProbabilityMeasure (noiseLaw p) := by
  constructor
  simp only [noiseLaw, Measure.add_apply, Measure.smul_apply, measure_univ,
    smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add (sub_nonneg.mpr hp.2) (div_nonneg hp.1 (by norm_num)),
    ← ENNReal.ofReal_add (by linarith [hp.1, hp.2]) (div_nonneg hp.1 (by norm_num))]
  norm_num [show 1 - p + p / 2 + p / 2 = 1 by ring]

/-- The six-outcome joint experiment is an actual probability law. -/
theorem joint_probability (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1) :
    IsProbabilityMeasure (jointLaw p) := by
  letI := context_probability
  letI := noise_probability p hp
  unfold jointLaw
  infer_instance

/-- Exact expectation against the two context atoms. -/
theorem context_integral (f : Bool → ℝ) :
    (∫ w, f w ∂contextLaw) = (f false + f true) / 2 := by
  unfold contextLaw
  rw [integral_add_measure]
  · simp only [integral_smul_measure, integral_dirac, smul_eq_mul]
    norm_num
    ring
  all_goals exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top

/-- Exact expectation against the three noise atoms. -/
theorem noise_integral (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1) (f : Fin 3 → ℝ) :
    (∫ n, f n ∂noiseLaw p) = (1 - p) * f 0 + (p / 2) * f 1 + (p / 2) * f 2 := by
  have hi (n : Fin 3) (r : ℝ) : Integrable f (ENNReal.ofReal r • Measure.dirac n) :=
    (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top
  unfold noiseLaw
  rw [integral_add_measure ((hi 0 (1 - p)).add_measure (hi 1 (p / 2))) (hi 2 (p / 2)),
    integral_add_measure (hi 0 (1 - p)) (hi 1 (p / 2))]
  simp only [integral_smul_measure, integral_dirac, smul_eq_mul,
    ENNReal.toReal_ofReal (sub_nonneg.mpr hp.2),
    ENNReal.toReal_ofReal (div_nonneg hp.1 (by norm_num) : 0 ≤ p / 2)]

/-- Exact six-atom integration, derived from the independent product law. -/
theorem joint_integral (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1) (f : Bool × Fin 3 → ℝ) :
    (∫ z, f z ∂jointLaw p) =
      ((1 - p) * f (false, 0) + (p / 2) * f (false, 1) + (p / 2) * f (false, 2) +
       ((1 - p) * f (true, 0) + (p / 2) * f (true, 1) + (p / 2) * f (true, 2))) / 2 := by
  letI := context_probability
  letI := noise_probability p hp
  rw [jointLaw, integral_prod _ Integrable.of_finite, context_integral]
  rw [noise_integral p hp, noise_integral p hp]

/-- The amplitude in the manuscript gives noise variance one and fourth moment one over p. -/
theorem amplitude_moments (p : ℝ) (hp : 0 < p) :
    p * (Real.sqrt p)⁻¹ ^ 2 = 1 ∧ p * (Real.sqrt p)⁻¹ ^ 4 = 1 / p := by
  have hs : Real.sqrt p ^ 2 = p := Real.sq_sqrt hp.le
  have hn : Real.sqrt p ≠ 0 := (Real.sqrt_pos.mpr hp).ne'
  constructor
  · field_simp
    nlinarith
  · field_simp
    nlinarith [sq_nonneg (Real.sqrt p ^ 2 - p)]

/-- The complete noise moment packet comes from its explicit three-atom law. -/
theorem noise_moments (p a : ℝ) (hp : 0 ≤ p ∧ p ≤ 1) :
    (∫ n, noiseValue a n ∂noiseLaw p) = 0 ∧
    (∫ n, noiseValue a n ^ 2 ∂noiseLaw p) = p * a ^ 2 ∧
    (∫ n, noiseValue a n ^ 3 ∂noiseLaw p) = 0 ∧
    (∫ n, noiseValue a n ^ 4 ∂noiseLaw p) = p * a ^ 4 := by
  simp only [noise_integral p hp, noiseValue, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  constructor
  · ring
  constructor
  · ring
  constructor <;> ring

/-- Actual conditional integration of baseline squared loss within either context. -/
theorem conditional_loss (p a : ℝ) (hp : 0 ≤ p ∧ p ≤ 1) (w : Bool) :
    (∫ n, loss a (w, n) ∂noiseLaw p) = correction w ^ 2 + p * a ^ 2 := by
  rw [noise_integral p hp]
  simp only [loss, noiseValue, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val]
  ring

/-- Baseline-loss first and second moments, computed without discarding the rare atoms. -/
theorem loss_moments (p a : ℝ) (hp : 0 ≤ p ∧ p ≤ 1) :
    (∫ z, loss a z ∂jointLaw p) = 5 / 4 + p * a ^ 2 ∧
    (∫ z, loss a z ^ 2 ∂jointLaw p) = 41 / 16 + (15 / 2) * (p * a ^ 2) + p * a ^ 4 := by
  simp only [joint_integral p hp, loss, correction, noiseValue, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val, Bool.false_eq_true, ↓reduceIte]
  constructor <;> ring

/-- Paired gain has no fourth-moment contribution, even in this changing-tail family. -/
theorem improvement_moments (p a : ℝ) (hp : 0 ≤ p ∧ p ≤ 1) :
    (∫ z, improvement a z ∂jointLaw p) = 5 / 4 ∧
    (∫ z, improvement a z ^ 2 ∂jointLaw p) = 41 / 16 + 5 * (p * a ^ 2) := by
  simp only [joint_integral p hp, improvement, loss, correction, noiseValue,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
    Bool.false_eq_true, ↓reduceIte]
  constructor <;> ring

/-- Every observable on the six-atom experiment has a genuine finite second moment. -/
theorem joint_memLp (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1) (f : Bool × Fin 3 → ℝ) :
    MemLp f 2 (jointLaw p) := by
  letI := joint_probability p hp
  exact (memLp_two_iff_integrable_sq (measurable_of_countable f).aestronglyMeasurable).mpr
    Integrable.of_finite

/-- The exact three quantities in the manuscript: loss variance, gain mean, and gain variance. -/
theorem exact_moment_packet (p : ℝ) (hp : 0 < p ∧ p ≤ 1) :
    Var[loss (Real.sqrt p)⁻¹; jointLaw p] = 5 + 1 / p ∧
    (∫ z, improvement (Real.sqrt p)⁻¹ z ∂jointLaw p) = 5 / 4 ∧
    Var[improvement (Real.sqrt p)⁻¹; jointLaw p] = 6 := by
  letI := joint_probability p ⟨hp.1.le, hp.2⟩
  have ha := amplitude_moments p hp.1
  have hL := loss_moments p (Real.sqrt p)⁻¹ ⟨hp.1.le, hp.2⟩
  have hG := improvement_moments p (Real.sqrt p)⁻¹ ⟨hp.1.le, hp.2⟩
  rw [ha.1, ha.2] at hL
  rw [ha.1] at hG
  rw [variance_eq_sub (joint_memLp p ⟨hp.1.le, hp.2⟩ _),
    variance_eq_sub (joint_memLp p ⟨hp.1.le, hp.2⟩ _)]
  simp only [Pi.pow_apply, hL.1, hL.2, hG.1, hG.2]
  constructor
  · ring
  constructor
  · trivial
  · norm_num

/-- Adding a deployed score to both predictions and the outcome preserves both loss contrasts. -/
theorem score_translation (s b z : ℝ) :
    ((s + b + z) - s) ^ 2 = (b + z) ^ 2 ∧
    ((s + b + z) - s) ^ 2 - ((s + b + z) - (s + b)) ^ 2 = (b + z) ^ 2 - z ^ 2 := by
  constructor <;> ring

end Descent.Portability.PairedGainTailExperiment
