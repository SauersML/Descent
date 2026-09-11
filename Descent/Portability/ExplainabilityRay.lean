/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.ConditionalFourthMomentLaw

assert_below Descent.Decision Descent.Program

/-!
# The sharp simultaneous explainability ray

UPT Theorem 2.4 and PL Corollary 2.3. With the full outer law, the conditional
residual mean `b` and the conditional raw second moment `a` held fixed, every
summary's explainable fraction of individual squared loss is its own fixed
numerator `B_C` over one common denominator `A + t`, where `A` is the variance
of `a` and `t` the mean conditional squared-loss variance. A summary is modelled
as a disintegration of the outer law, and two witnesses show the hypothesis is
satisfiable. The exact attainable set for a summary with positive numerator is
the ray `(0, B_C / A]`: every value is attained by the explicit two-point
completion `excessCompletionKernel`, and zero is an infimum only. This builds on
`mixture` and `total_variance` of `IndividualLossMoments` and on
`momentCompletionLaw` and `conditional_loss_variance_attained` of
`ConditionalFourthMomentLaw`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.ExplainabilityRay

open Foundations IndividualLossMoments ConditionalFourthMomentLaw

noncomputable section

variable {D S T Ω : Type*}

/-- UPT (2.6), denominator: the total loss variance is the variance of the
conditional mean loss plus the mean conditional squared-loss variance. -/
theorem total_loss_variance_eq (E : ExpFunctional D) (K : D → ExpFunctional Ω)
    (r : D × Ω → ℝ) (a δ : D → ℝ)
    (ha : ∀ d, K d (fun ω ↦ r (d, ω) ^ 2) = a d)
    (hδ : ∀ d, variance (K d) (fun ω ↦ r (d, ω) ^ 2) = δ d) :
    variance (mixture E K) (fun z ↦ r z ^ 2) = variance E a + E δ := by
  have hfa : (fun d ↦ K d (fun ω ↦ r (d, ω) ^ 2)) = a := by
    funext d
    exact ha d
  have hfδ : (fun d ↦ variance (K d) (fun ω ↦ r (d, ω) ^ 2)) = δ := by
    funext d
    exact hδ d
  rw [total_variance E K (fun z ↦ r z ^ 2)]
  show E (fun d ↦ variance (K d) (fun ω ↦ r (d, ω) ^ 2))
      + variance E (fun d ↦ K d (fun ω ↦ r (d, ω) ^ 2)) = variance E a + E δ
  rw [hfa, hfδ]
  ring

/-- The finest summary, the outer variable itself, is a disintegration. -/
theorem self_disintegration (E : ExpFunctional D) (f : D → ℝ) :
    E f = mixture E (fun _ ↦ ExpFunctional.evalAt PUnit.unit)
      (fun z : D × PUnit ↦ f z.1) := rfl

/-- The trivial summary, which retains nothing, is a disintegration. -/
theorem constant_disintegration (E : ExpFunctional D) (f : D → ℝ) :
    E f = mixture (ExpFunctional.evalAt PUnit.unit) (fun _ ↦ E)
      (fun z : PUnit × D ↦ f z.2) := rfl

/-- The numerator `B_C` of UPT (2.6) is the between-summary variance of the
conditional mean loss. It depends only on the outer law and on `a`, never on
the completion, and the within-summary remainder is nonnegative. -/
theorem summary_between_variance (E : ExpFunctional D) (ES : ExpFunctional S)
    (KT : S → ExpFunctional T) (emb : S × T → D) (a : D → ℝ)
    (hcompat : ∀ f : D → ℝ, E f = mixture ES KT (fun z ↦ f (emb z))) :
    variance E a = ES (fun s ↦ variance (KT s) (fun u ↦ a (emb (s, u))))
      + variance ES (fun s ↦ KT s (fun u ↦ a (emb (s, u)))) := by
  have h1 : E a = mixture ES KT (fun z ↦ a (emb z)) := hcompat a
  have h2 : variance E a = variance (mixture ES KT) (fun z ↦ a (emb z)) := by
    show E (fun d ↦ (a d - E a) ^ 2)
        = mixture ES KT
          (fun z ↦ (a (emb z) - mixture ES KT (fun z ↦ a (emb z))) ^ 2)
    rw [← h1, hcompat (fun d ↦ (a d - E a) ^ 2)]
  rw [h2]
  exact total_variance ES KT (fun z : S × T ↦ a (emb z))

/-- The between-summary numerator never exceeds the variance of the conditional
mean loss, so `B_C ≤ A`. -/
theorem summary_between_variance_le (E : ExpFunctional D) (ES : ExpFunctional S)
    (KT : S → ExpFunctional T) (emb : S × T → D) (a : D → ℝ)
    (hcompat : ∀ f : D → ℝ, E f = mixture ES KT (fun z ↦ f (emb z))) :
    variance ES (fun s ↦ KT s (fun u ↦ a (emb (s, u)))) ≤ variance E a := by
  have hwithin : 0 ≤ ES (fun s ↦ variance (KT s) (fun u ↦ a (emb (s, u)))) :=
    ES.nonneg_eval _ (fun s ↦ (KT s).nonneg_eval _ (fun _ ↦ sq_nonneg _))
  have hd := summary_between_variance E ES KT emb a hcompat
  linarith

/-- UPT (2.8) and PL (2.5): for any family of summaries, every coordinate of the
vector of explainable fractions is its own fixed numerator over the single
common denominator `A + t`. The completion therefore rescales all coordinates by
a common factor and cannot reorder them. -/
theorem simultaneous_explainability_ray {ι : Type*} {Si Ti : ι → Type*}
    (E : ExpFunctional D) (ES : (i : ι) → ExpFunctional (Si i))
    (KT : (i : ι) → Si i → ExpFunctional (Ti i)) (emb : (i : ι) → Si i × Ti i → D)
    (K : D → ExpFunctional Ω) (r : D × Ω → ℝ) (a δ : D → ℝ)
    (hcompat : ∀ (i : ι) (f : D → ℝ),
      E f = mixture (ES i) (KT i) (fun z ↦ f (emb i z)))
    (ha : ∀ d, K d (fun ω ↦ r (d, ω) ^ 2) = a d)
    (hδ : ∀ d, variance (K d) (fun ω ↦ r (d, ω) ^ 2) = δ d) (i : ι) :
    variance (ES i) (fun s ↦ KT i s (fun u ↦ a (emb i (s, u)))) ≤ variance E a ∧
      variance (ES i) (fun s ↦ KT i s (fun u ↦ a (emb i (s, u))))
          / variance (mixture E K) (fun z ↦ r z ^ 2)
        = variance (ES i) (fun s ↦ KT i s (fun u ↦ a (emb i (s, u))))
          / (variance E a + E δ) := by
  refine ⟨summary_between_variance_le E (ES i) (KT i) (emb i) a (hcompat i), ?_⟩
  rw [total_loss_variance_eq E K r a δ ha hδ]

/-- The mass of the nondegenerate region where the conditional variance is
positive. UPT calls this `P(V)`. -/
def nondegenerateMass (E : ExpFunctional D) (b a : D → ℝ) : ℝ :=
  E (fun d ↦ if b d ^ 2 < a d then (1 : ℝ) else 0)

/-- The mass of the nondegenerate region is nonnegative. -/
theorem nondegenerateMass_nonneg (E : ExpFunctional D) (b a : D → ℝ) :
    0 ≤ nondegenerateMass E b a :=
  E.nonneg_eval _ (fun _ ↦ by split <;> norm_num)

/-- The excess profile of the UPT Theorem 2.4 proof: the prescribed total excess
`t` is spread uniformly over the nondegenerate region. -/
def excessProfile (E : ExpFunctional D) (b a : D → ℝ) (t : ℝ) (d : D) : ℝ :=
  t / nondegenerateMass E b a * (if b d ^ 2 < a d then (1 : ℝ) else 0)

/-- The excess profile integrates to the prescribed total excess. -/
theorem excessProfile_total (E : ExpFunctional D) (b a : D → ℝ) (t : ℝ)
    (hp : nondegenerateMass E b a ≠ 0) : E (excessProfile E b a t) = t := by
  have hsplit : excessProfile E b a t = (t / nondegenerateMass E b a) •
      (fun d ↦ if b d ^ 2 < a d then (1 : ℝ) else 0) := rfl
  rw [hsplit, E.smul_eval]
  show t / nondegenerateMass E b a * nondegenerateMass E b a = t
  field_simp

/-- The excess profile is nonnegative. -/
theorem excessProfile_nonneg (E : ExpFunctional D) (b a : D → ℝ) (t : ℝ)
    (ht : 0 ≤ t) (d : D) : 0 ≤ excessProfile E b a t d := by
  have h1 : 0 ≤ t / nondegenerateMass E b a :=
    div_nonneg ht (nondegenerateMass_nonneg E b a)
  have h2 : (0 : ℝ) ≤ if b d ^ 2 < a d then (1 : ℝ) else 0 := by
    split <;> norm_num
  exact mul_nonneg h1 h2

/-- The excess profile vanishes on the degenerate region, as UPT (2.5) requires. -/
theorem excessProfile_degenerate (E : ExpFunctional D) (b a : D → ℝ) (t : ℝ)
    (d : D) (h : b d ^ 2 = a d) : excessProfile E b a t d = 0 := by
  unfold excessProfile
  rw [if_neg (by linarith : ¬ b d ^ 2 < a d)]
  ring

/-- The cell-wise two-point completion realizing total excess `t`. -/
def excessCompletionKernel (E : ExpFunctional D) (b a : D → ℝ) (t : ℝ) (d : D) :
    ExpFunctional Bool :=
  momentCompletionLaw (b d) (a d) (excessProfile E b a t d)

/-- The residual of the cell-wise two-point completion. -/
def excessCompletionResidual (E : ExpFunctional D) (b a : D → ℝ) (t : ℝ)
    (z : D × Bool) : ℝ :=
  momentCompletionValue (b z.1) (a z.1) (excessProfile E b a t z.1) z.2

/-- The completion keeps the prescribed conditional first and second moment
functions and has total loss variance exactly `A + t`. -/
theorem excessCompletion_moments (E : ExpFunctional D) (b a : D → ℝ) (t : ℝ)
    (hba : ∀ d, b d ^ 2 ≤ a d) (ht : 0 ≤ t) (hp : nondegenerateMass E b a ≠ 0) :
    (∀ d, excessCompletionKernel E b a t d
        (fun x ↦ excessCompletionResidual E b a t (d, x)) = b d) ∧
      (∀ d, excessCompletionKernel E b a t d
        (fun x ↦ excessCompletionResidual E b a t (d, x) ^ 2) = a d) ∧
      variance (mixture E (excessCompletionKernel E b a t))
        (fun z ↦ excessCompletionResidual E b a t z ^ 2) = variance E a + t := by
  have hnn : ∀ d, 0 ≤ excessProfile E b a t d := fun d ↦
    excessProfile_nonneg E b a t ht d
  have hdeg : ∀ d, b d ^ 2 = a d → excessProfile E b a t d = 0 := fun d h ↦
    excessProfile_degenerate E b a t d h
  have hall := fun d ↦ conditional_loss_variance_attained b a
    (excessProfile E b a t) hba hnn hdeg d
  refine ⟨fun d ↦ (hall d).1, fun d ↦ (hall d).2.1, ?_⟩
  rw [total_loss_variance_eq E (excessCompletionKernel E b a t)
      (excessCompletionResidual E b a t) a (excessProfile E b a t)
      (fun d ↦ (hall d).2.1) (fun d ↦ (hall d).2.2),
    excessProfile_total E b a t hp]

/-- Solving the ray equation for the excess that realizes a prescribed value. -/
theorem ray_excess (bc a η : ℝ) (hbc : 0 < bc) (ha : 0 < a) (hη : 0 < η)
    (hle : η ≤ bc / a) : 0 ≤ bc / η - a ∧ bc / (a + (bc / η - a)) = η := by
  have h1 : η * a ≤ bc := (le_div_iff₀ ha).mp hle
  have h2 : a ≤ bc / η := (le_div_iff₀ hη).mpr (by nlinarith)
  refine ⟨by linarith, ?_⟩
  have hd : a + (bc / η - a) = bc / η := by ring
  rw [hd, div_div_eq_mul_div, mul_comm, mul_div_assoc, div_self (ne_of_gt hbc),
    mul_one]

/-- UPT Theorem 2.4 and PL Corollary 2.3: with the outer law and the conditional
first and second moment functions held fixed, the exact set of attainable
explainable fractions of a summary with positive numerator is the ray
`(0, B_C / A]`. Every value in it is attained by an explicit conditional
two-point completion; zero is an infimum and is not attained. -/
theorem sharp_explainability_ray (E : ExpFunctional D) (ES : ExpFunctional S)
    (KT : S → ExpFunctional T) (emb : S × T → D) (b a : D → ℝ)
    (hcompat : ∀ f : D → ℝ, E f = mixture ES KT (fun z ↦ f (emb z)))
    (hba : ∀ d, b d ^ 2 ≤ a d) (hp : nondegenerateMass E b a ≠ 0)
    (hB : 0 < variance ES (fun s ↦ KT s (fun u ↦ a (emb (s, u))))) (η : ℝ) :
    (∃ (K : D → ExpFunctional Bool) (r : D × Bool → ℝ),
        (∀ d, K d (fun x ↦ r (d, x)) = b d) ∧
        (∀ d, K d (fun x ↦ r (d, x) ^ 2) = a d) ∧
        variance ES (fun s ↦ KT s (fun u ↦ a (emb (s, u))))
          / variance (mixture E K) (fun z ↦ r z ^ 2) = η)
      ↔ 0 < η ∧
        η ≤ variance ES (fun s ↦ KT s (fun u ↦ a (emb (s, u)))) / variance E a := by
  have hBA := summary_between_variance_le E ES KT emb a hcompat
  have hA : 0 < variance E a := lt_of_lt_of_le hB hBA
  constructor
  · rintro ⟨K, r, _, ha, rfl⟩
    have hδnn : 0 ≤ E (fun d ↦ variance (K d) (fun x ↦ r (d, x) ^ 2)) :=
      E.nonneg_eval _ (fun d ↦ (K d).nonneg_eval _ (fun _ ↦ sq_nonneg _))
    rw [total_loss_variance_eq E K r a
      (fun d ↦ variance (K d) (fun x ↦ r (d, x) ^ 2)) ha (fun _ ↦ rfl)]
    refine ⟨div_pos hB (by linarith), ?_⟩
    rw [div_le_div_iff₀ (by linarith) hA]
    nlinarith
  · rintro ⟨hη, hle⟩
    obtain ⟨ht, hfrac⟩ := ray_excess
      (variance ES (fun s ↦ KT s (fun u ↦ a (emb (s, u))))) (variance E a) η hB hA
      hη hle
    obtain ⟨h1, h2, h3⟩ := excessCompletion_moments E b a _ hba ht hp
    exact ⟨excessCompletionKernel E b a _, excessCompletionResidual E b a _, h1, h2,
      by rw [h3]; exact hfrac⟩

end

end Descent.Portability.ExplainabilityRay
