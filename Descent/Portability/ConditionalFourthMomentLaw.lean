/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.LossNoiseCompletion

assert_below Descent.Decision Descent.Program

/-!
# The complete conditional fourth-moment law

UPT Lemma 2.2, UPT Theorem 2.3 and PL Theorem 2.2. Fixing a conditional
residual mean `b` and raw second moment `a`, the exact set of achievable
conditional squared-loss variances is `{δ ≥ 0}`, with `δ` forced to vanish
exactly where `a = b²`. Both directions are proved: necessity from positivity
of the expectation functional and Cauchy-Schwarz (`cauchy_schwarz` of the
foundations), sufficiency from the explicit at-most-two-point law
`momentCompletionLaw`, built from the mean-zero family `zeroMeanNoise` of
`LossNoiseCompletion` and evaluated exactly at its first, second and fourth raw
moments. No Gaussianity and no independence between residual shape and genotype
is assumed. The hypotheses are the manuscript's domain conditions `b² ≤ a`,
`δ ≥ 0` and the degeneracy restriction.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.ConditionalFourthMomentLaw

open Foundations IndividualLossMoments LossNoiseCompletion

noncomputable section

variable {D Ω : Type*}

/-- Shifting a mean-zero law by a constant moves the mean by that constant. -/
theorem shifted_law_mean (E : ExpFunctional Ω) (e : Ω → ℝ) (hmean : E e = 0)
    (c : ℝ) : E (fun ω ↦ c + e ω) = c := by
  have hsplit : (fun ω ↦ c + e ω) = (fun _ : Ω ↦ c) + e := rfl
  rw [hsplit, E.add_eval, E.eval_const, hmean]
  ring

/-- A vanishing second central moment forces a vanishing third central moment.
This is Cauchy-Schwarz applied to the centred variable against its square. -/
theorem central_third_of_second_zero (E : ExpFunctional Ω) (X : Ω → ℝ) (b : ℝ)
    (hc2 : E (fun ω ↦ (X ω - b) ^ 2) = 0) : E (fun ω ↦ (X ω - b) ^ 3) = 0 := by
  have hcs := E.cauchy_schwarz (fun ω ↦ X ω - b) (fun ω ↦ (X ω - b) ^ 2)
  have e1 : (fun ω ↦ (X ω - b) * (X ω - b) ^ 2) = fun ω ↦ (X ω - b) ^ 3 := by
    funext ω
    ring
  have e2 : (fun ω ↦ ((X ω - b) ^ 2) ^ 2) = fun ω ↦ (X ω - b) ^ 4 := by
    funext ω
    ring
  rw [e1, e2, hc2, zero_mul] at hcs
  have hzero : E (fun ω ↦ (X ω - b) ^ 3) ^ 2 = 0 := le_antisymm hcs (sq_nonneg _)
  rw [pow_two] at hzero
  exact mul_self_eq_zero.mp hzero

/-- A vanishing second central moment forces a vanishing fourth central moment.
Cauchy-Schwarz is applied to `|X - b|` against `|X - b|³`. -/
theorem central_fourth_of_second_zero (E : ExpFunctional Ω) (X : Ω → ℝ) (b : ℝ)
    (hc2 : E (fun ω ↦ (X ω - b) ^ 2) = 0) : E (fun ω ↦ (X ω - b) ^ 4) = 0 := by
  have hcs := E.cauchy_schwarz (fun ω ↦ |X ω - b|) (fun ω ↦ |X ω - b| ^ 3)
  have e1 : (fun ω ↦ |X ω - b| * |X ω - b| ^ 3) = fun ω ↦ (X ω - b) ^ 4 := by
    funext ω
    have h : |X ω - b| * |X ω - b| ^ 3 = |X ω - b| ^ 4 := by ring
    rw [h, pow_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (X ω - b) ^ 4)]
  have e2 : (fun ω ↦ |X ω - b| ^ 2) = fun ω ↦ (X ω - b) ^ 2 := by
    funext ω
    exact sq_abs _
  have e3 : (fun ω ↦ (|X ω - b| ^ 3) ^ 2) = fun ω ↦ (X ω - b) ^ 6 := by
    funext ω
    have h : (|X ω - b| ^ 3) ^ 2 = |X ω - b| ^ 6 := by ring
    rw [h, pow_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (X ω - b) ^ 6)]
  rw [e1, e2, e3, hc2, zero_mul] at hcs
  have hzero : E (fun ω ↦ (X ω - b) ^ 4) ^ 2 = 0 := le_antisymm hcs (sq_nonneg _)
  rw [pow_two] at hzero
  exact mul_self_eq_zero.mp hzero

/-- A degenerate conditional second moment leaves no fourth-moment freedom: the
squared-loss variance is forced to zero. This is the `a = b²` restriction of
UPT (2.5) and PL (2.3), proved rather than assumed. -/
theorem degenerate_second_moment_forces_zero (E : ExpFunctional Ω) (X : Ω → ℝ)
    (b : ℝ) (hb : E X = b) (ha : E (fun ω ↦ X ω ^ 2) = b ^ 2) :
    variance E (fun ω ↦ X ω ^ 2) = 0 := by
  have hc2 : E (fun ω ↦ (X ω - b) ^ 2) = 0 := by
    have hsplit : (fun ω ↦ (X ω - b) ^ 2)
        = (fun ω ↦ X ω ^ 2) + (-(2 * b)) • X + (fun _ : Ω ↦ b ^ 2) := by
      funext ω
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [hsplit, E.add_eval, E.add_eval, E.smul_eval, E.eval_const, hb, ha]
    ring
  have hc3 := central_third_of_second_zero E X b hc2
  have hc4 := central_fourth_of_second_zero E X b hc2
  have hmean0 : E (fun ω ↦ X ω - b) = 0 := by
    have h := eval_centered_zero E X
    rw [hb] at h
    exact h
  have h4 := noise_shift_fourth_moment E (fun ω ↦ X ω - b) hmean0 b
  have hid : (fun ω ↦ (b + (X ω - b)) ^ 4) = fun ω ↦ X ω ^ 4 := by
    funext ω
    ring
  rw [hid, hc2, hc3, hc4] at h4
  simp only [variance_eq_expect_sq_sub_sq_mean, ← pow_mul]
  rw [h4, ha]
  ring

/-- The at-most-two-point law completing a prescribed mean `b`, raw second
moment `a` and raw fourth moment `a² + δ`: UPT (2.3). Where the prescribed
conditional variance is positive it is the shifted mean-zero two-point law;
on the degenerate region it is the point mass at `b`. -/
def momentCompletionLaw (b a δ : ℝ) : ExpFunctional Bool :=
  if h : b ^ 2 < a then
    zeroMeanNoise (a - b ^ 2) (-2 * b + Real.sqrt (δ / (a - b ^ 2))) (by linarith)
  else ExpFunctional.evalAt true

/-- The support values of `momentCompletionLaw`. -/
def momentCompletionValue (b a δ : ℝ) (x : Bool) : ℝ :=
  if b ^ 2 < a then
    b + zeroMeanNoiseValue (a - b ^ 2) (-2 * b + Real.sqrt (δ / (a - b ^ 2))) x
  else b

/-- On the nondegenerate region the completion law is the shifted mean-zero
two-point family. -/
theorem momentCompletionLaw_pos (b a δ : ℝ) (h : b ^ 2 < a) (hv : 0 < a - b ^ 2) :
    momentCompletionLaw b a δ
      = zeroMeanNoise (a - b ^ 2) (-2 * b + Real.sqrt (δ / (a - b ^ 2))) hv := by
  simp only [momentCompletionLaw, dif_pos h]

/-- On the degenerate region the completion law is the point mass at `b`. -/
theorem momentCompletionLaw_neg (b a δ : ℝ) (h : ¬ b ^ 2 < a) :
    momentCompletionLaw b a δ = ExpFunctional.evalAt true := by
  simp only [momentCompletionLaw, dif_neg h]

/-- The completion's support values on the nondegenerate region. -/
theorem momentCompletionValue_pos (b a δ : ℝ) (h : b ^ 2 < a) :
    momentCompletionValue b a δ = fun x ↦
      b + zeroMeanNoiseValue (a - b ^ 2)
        (-2 * b + Real.sqrt (δ / (a - b ^ 2))) x := by
  funext x
  simp only [momentCompletionValue, if_pos h]

/-- The completion's support values on the degenerate region. -/
theorem momentCompletionValue_neg (b a δ : ℝ) (h : ¬ b ^ 2 < a) :
    momentCompletionValue b a δ = fun _ ↦ b := by
  funext x
  simp only [momentCompletionValue, if_neg h]

/-- UPT Lemma 2.2, sufficiency: the completion realizes the prescribed mean,
raw second moment and raw fourth moment exactly. -/
theorem momentCompletionLaw_moments (b a δ : ℝ) (hba : b ^ 2 ≤ a) (hδ : 0 ≤ δ)
    (hdeg : b ^ 2 = a → δ = 0) :
    momentCompletionLaw b a δ (momentCompletionValue b a δ) = b ∧
      momentCompletionLaw b a δ (fun x ↦ momentCompletionValue b a δ x ^ 2) = a ∧
      momentCompletionLaw b a δ (fun x ↦ momentCompletionValue b a δ x ^ 4)
        = a ^ 2 + δ := by
  by_cases h : b ^ 2 < a
  · have hv : 0 < a - b ^ 2 := by linarith
    have hne : a - b ^ 2 ≠ 0 := ne_of_gt hv
    have hsv : Real.sqrt (δ / (a - b ^ 2)) ^ 2 * (a - b ^ 2) = δ := by
      rw [Real.sq_sqrt (div_nonneg hδ hv.le)]
      field_simp
    simp only [momentCompletionLaw_pos b a δ h hv, momentCompletionValue_pos b a δ h]
    refine ⟨?_, ?_, ?_⟩
    · exact shifted_law_mean _ _ (zeroMeanNoise_mean _ _ hv) b
    · rw [noise_shift_second_moment _ _ (zeroMeanNoise_mean _ _ hv) b,
        zeroMeanNoise_second _ _ hv]
      ring
    · rw [noise_shift_fourth_moment _ _ (zeroMeanNoise_mean _ _ hv) b,
        zeroMeanNoise_second _ _ hv, zeroMeanNoise_third _ _ hv,
        zeroMeanNoise_fourth _ _ hv]
      linear_combination hsv
  · have heq : b ^ 2 = a := le_antisymm hba (not_lt.mp h)
    have hδ0 : δ = 0 := hdeg heq
    simp only [momentCompletionLaw_neg b a δ h, momentCompletionValue_neg b a δ h]
    refine ⟨rfl, heq, ?_⟩
    show b ^ 4 = a ^ 2 + δ
    rw [hδ0, ← heq]
    ring

/-- The squared-loss variance of the completion is exactly the prescribed `δ`. -/
theorem momentCompletionLaw_loss_variance (b a δ : ℝ) (hba : b ^ 2 ≤ a)
    (hδ : 0 ≤ δ) (hdeg : b ^ 2 = a → δ = 0) :
    variance (momentCompletionLaw b a δ)
      (fun x ↦ momentCompletionValue b a δ x ^ 2) = δ := by
  obtain ⟨_, h2, h4⟩ := momentCompletionLaw_moments b a δ hba hδ hdeg
  simp only [variance_eq_expect_sq_sub_sq_mean, ← pow_mul]
  rw [h4, h2]
  ring

/-- UPT Lemma 2.2: a real random variable with mean `b`, raw second moment `a`
and raw fourth moment `a² + δ` exists if and only if either `b² < a` and
`δ ≥ 0`, or `b² = a` and `δ = 0`. Necessity uses only positivity of the
expectation functional; sufficiency is witnessed by a law with at most two
support points. -/
theorem raw_moment_completion_iff (b a δ : ℝ) :
    (∃ (Ω : Type) (E : ExpFunctional Ω) (X : Ω → ℝ), E X = b ∧
        E (fun ω ↦ X ω ^ 2) = a ∧ E (fun ω ↦ X ω ^ 4) = a ^ 2 + δ)
      ↔ (b ^ 2 < a ∧ 0 ≤ δ) ∨ (b ^ 2 = a ∧ δ = 0) := by
  constructor
  · rintro ⟨Ω, E, X, hb, ha, h4⟩
    have hvar : 0 ≤ variance E X := E.nonneg_eval _ (fun _ ↦ sq_nonneg _)
    rw [variance_eq_expect_sq_sub_sq_mean, hb, ha] at hvar
    have hcs := E.cauchy_schwarz (fun ω ↦ X ω ^ 2) (fun _ ↦ (1 : ℝ))
    have e1 : (fun ω ↦ X ω ^ 2 * 1) = fun ω ↦ X ω ^ 2 := by
      funext ω
      ring
    have e2 : (fun ω ↦ (X ω ^ 2) ^ 2) = fun ω ↦ X ω ^ 4 := by
      funext ω
      ring
    have e3 : (fun _ : Ω ↦ (1 : ℝ) ^ 2) = fun _ : Ω ↦ (1 : ℝ) := by
      funext ω
      ring
    rw [e1, e2, e3, E.const_one, ha, h4] at hcs
    rcases lt_or_eq_of_le (by linarith : b ^ 2 ≤ a) with hlt | heq
    · exact Or.inl ⟨hlt, by linarith⟩
    · refine Or.inr ⟨heq, ?_⟩
      have hdeg := degenerate_second_moment_forces_zero E X b hb (by rw [ha, heq])
      simp only [variance_eq_expect_sq_sub_sq_mean, ← pow_mul] at hdeg
      rw [h4, ha] at hdeg
      linarith
  · intro hcond
    have hba : b ^ 2 ≤ a := by
      rcases hcond with ⟨h, _⟩ | ⟨h, _⟩
      · linarith
      · linarith
    have hδ : 0 ≤ δ := by
      rcases hcond with ⟨_, h⟩ | ⟨_, h⟩
      · exact h
      · linarith
    have hdeg : b ^ 2 = a → δ = 0 := by
      intro he
      rcases hcond with ⟨h, _⟩ | ⟨_, h⟩
      · linarith
      · exact h
    obtain ⟨h1, h2, h3⟩ := momentCompletionLaw_moments b a δ hba hδ hdeg
    exact ⟨Bool, momentCompletionLaw b a δ, momentCompletionValue b a δ, h1, h2, h3⟩

/-- UPT Theorem 2.3 / PL Theorem 2.2, necessity: every kernel with the
prescribed conditional first and second moments has a nonnegative conditional
squared-loss variance, which vanishes wherever the conditional variance does. -/
theorem conditional_loss_variance_necessity (K : D → ExpFunctional Ω)
    (r : D × Ω → ℝ) (b a : D → ℝ) (hb : ∀ d, K d (fun ω ↦ r (d, ω)) = b d)
    (ha : ∀ d, K d (fun ω ↦ r (d, ω) ^ 2) = a d) (d : D) :
    b d ^ 2 ≤ a d ∧ 0 ≤ variance (K d) (fun ω ↦ r (d, ω) ^ 2) ∧
      (b d ^ 2 = a d → variance (K d) (fun ω ↦ r (d, ω) ^ 2) = 0) := by
  have hvar : 0 ≤ variance (K d) (fun ω ↦ r (d, ω)) :=
    (K d).nonneg_eval _ (fun _ ↦ sq_nonneg _)
  rw [variance_eq_expect_sq_sub_sq_mean, hb d, ha d] at hvar
  refine ⟨by linarith, (K d).nonneg_eval _ (fun _ ↦ sq_nonneg _), ?_⟩
  intro heq
  exact degenerate_second_moment_forces_zero (K d) (fun ω ↦ r (d, ω)) (b d)
    (hb d) (by rw [ha d, heq])

/-- UPT Theorem 2.3 / PL Theorem 2.2, sufficiency: every admissible `δ` is
realized by a conditional kernel with at most two support points in each cell,
with the prescribed conditional first and second moments unchanged. -/
theorem conditional_loss_variance_attained (b a δ : D → ℝ)
    (hba : ∀ d, b d ^ 2 ≤ a d) (hδ : ∀ d, 0 ≤ δ d)
    (hdeg : ∀ d, b d ^ 2 = a d → δ d = 0) (d : D) :
    momentCompletionLaw (b d) (a d) (δ d)
        (fun x ↦ momentCompletionValue (b d) (a d) (δ d) x) = b d ∧
      momentCompletionLaw (b d) (a d) (δ d)
        (fun x ↦ momentCompletionValue (b d) (a d) (δ d) x ^ 2) = a d ∧
      variance (momentCompletionLaw (b d) (a d) (δ d))
        (fun x ↦ momentCompletionValue (b d) (a d) (δ d) x ^ 2) = δ d := by
  obtain ⟨h1, h2, _⟩ := momentCompletionLaw_moments (b d) (a d) (δ d) (hba d)
    (hδ d) (hdeg d)
  exact ⟨h1, h2, momentCompletionLaw_loss_variance (b d) (a d) (δ d) (hba d)
    (hδ d) (hdeg d)⟩

/-- UPT Theorem 2.3 / PL Theorem 2.2, as an exact identification of the set of
achievable conditional squared-loss variance functions. -/
theorem conditional_loss_variance_exact_set (b a δ : D → ℝ)
    (hba : ∀ d, b d ^ 2 ≤ a d) :
    (∃ (K : D → ExpFunctional Bool) (r : D × Bool → ℝ),
        (∀ d, K d (fun x ↦ r (d, x)) = b d) ∧
        (∀ d, K d (fun x ↦ r (d, x) ^ 2) = a d) ∧
        (∀ d, variance (K d) (fun x ↦ r (d, x) ^ 2) = δ d))
      ↔ (∀ d, 0 ≤ δ d) ∧ ∀ d, b d ^ 2 = a d → δ d = 0 := by
  constructor
  · rintro ⟨K, r, hb, ha, hv⟩
    refine ⟨fun d ↦ ?_, fun d hd ↦ ?_⟩
    · rw [← hv d]
      exact (conditional_loss_variance_necessity K r b a hb ha d).2.1
    · rw [← hv d]
      exact (conditional_loss_variance_necessity K r b a hb ha d).2.2 hd
  · rintro ⟨hδ, hdeg⟩
    refine ⟨fun d ↦ momentCompletionLaw (b d) (a d) (δ d),
      fun z ↦ momentCompletionValue (b z.1) (a z.1) (δ z.1) z.2,
      fun d ↦ ?_, fun d ↦ ?_, fun d ↦ ?_⟩
    · exact (conditional_loss_variance_attained b a δ hba hδ hdeg d).1
    · exact (conditional_loss_variance_attained b a δ hba hδ hdeg d).2.1
    · exact (conditional_loss_variance_attained b a δ hba hδ hdeg d).2.2

end

end Descent.Portability.ConditionalFourthMomentLaw
