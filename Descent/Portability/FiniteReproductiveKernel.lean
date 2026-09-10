/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.ExactFiniteHistoryLaw
import Mathlib.Data.Nat.Choose.Multinomial

assert_below Descent.Decision Descent.Program

/-!
A finite reproductive transition law with arbitrary state-dependent mating,
transmission, and environmental feedback. The offspring count law is the exact
multinomial mass function, normalized using the multinomial theorem. Thus census
drift is part of the transition law. Conditional independence of the offspring is
the multinomial reproduction premise, not an additional noise approximation.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.FiniteReproductiveKernel

variable {H E : Type*} [Fintype H] [DecidableEq H] [Fintype E]

/-- Finite census vectors with total population size `population`. -/
abbrev Counts (H : Type*) [Fintype H] [DecidableEq H] (population : ℕ) :=
  ↥(Finset.piAntidiag (Finset.univ : Finset H) population)

theorem counts_sum {population : ℕ} (counts : Counts H population) :
    ∑ reproductiveType, counts.val reproductiveType = population :=
  (Finset.mem_piAntidiag.mp counts.property).1

noncomputable def multinomialLaw (offspring : FiniteReportLaw H) (population : ℕ) :
    FiniteReportLaw (Counts H population) where
  mass counts := (Nat.multinomial Finset.univ counts.val : ℝ) *
    ∏ reproductiveType, offspring.mass reproductiveType ^ counts.val reproductiveType
  mass_nonneg counts := mul_nonneg (Nat.cast_nonneg _)
    (Finset.prod_nonneg fun reproductiveType _ ↦
      pow_nonneg (offspring.mass_nonneg reproductiveType) _)
  mass_sum := by
    rw [Finset.sum_coe_sort]
    rw [← Finset.sum_pow_eq_sum_piAntidiag, offspring.mass_sum, one_pow]

/-- The natural multinomial coefficient equals the real factorial ratio exactly. -/
theorem multinomial_coefficient {population : ℕ} (counts : Counts H population) :
    (Nat.multinomial Finset.univ counts.val : ℝ) =
      (Nat.factorial population : ℝ) /
        ∏ reproductiveType, (Nat.factorial (counts.val reproductiveType) : ℝ) := by
  have hpositive : 0 < ∏ reproductiveType,
      (Nat.factorial (counts.val reproductiveType) : ℝ) := by positivity
  apply (eq_div_iff (ne_of_gt hpositive)).mpr
  have hspec := Nat.multinomial_spec Finset.univ counts.val
  rw [counts_sum counts] at hspec
  have hcast := congrArg (fun value : ℕ ↦ (value : ℝ)) hspec
  norm_cast at hcast ⊢
  simpa only [mul_comm] using hspec

/-- Closed count probabilities retain zero probabilities and zero counts exactly. -/
theorem multinomialLaw_mass (offspring : FiniteReportLaw H) (population : ℕ)
    (counts : Counts H population) :
    (multinomialLaw offspring population).mass counts =
      (Nat.factorial population : ℝ) /
        (∏ reproductiveType, (Nat.factorial (counts.val reproductiveType) : ℝ)) *
          ∏ reproductiveType, offspring.mass reproductiveType ^ counts.val reproductiveType := by
  change (Nat.multinomial Finset.univ counts.val : ℝ) * _ = _
  rw [multinomial_coefficient]

abbrev State (H E : Type*) [Fintype H] [DecidableEq H] (population : ℕ) :=
  Counts H population × E

/-- Inputs may depend on the entire phased reproductive census and environment.
The next environment may additionally depend on the realized offspring census. -/
structure Model (H E : Type*) [Fintype H] [DecidableEq H] [Fintype E] (population : ℕ) where
  mating : State H E population → FiniteReportLaw (H × H)
  transmission : State H E population → H × H → FiniteReportLaw H
  environment : State H E population → Counts H population → FiniteReportLaw E

noncomputable def offspringLaw {population : ℕ} (model : Model H E population)
    (state : State H E population) : FiniteReportLaw H :=
  (model.mating state).bind (model.transmission state)

theorem offspringLaw_mass {population : ℕ} (model : Model H E population)
    (state : State H E population) (offspring : H) :
    (offspringLaw model state).mass offspring =
      ∑ firstParent, ∑ secondParent,
        (model.mating state).mass (firstParent, secondParent) *
          (model.transmission state (firstParent, secondParent)).mass offspring := by
  simp only [offspringLaw, FiniteReportLaw.bind, Fintype.sum_prod_type]

/-- The exact census-and-environment transition, including environmental feedback. -/
noncomputable def transition {population : ℕ} (model : Model H E population)
    (state : State H E population) : FiniteReportLaw (State H E population) where
  mass target := (multinomialLaw (offspringLaw model state) population).mass target.1 *
    (model.environment state target.1).mass target.2
  mass_nonneg target := mul_nonneg
    ((multinomialLaw (offspringLaw model state) population).mass_nonneg target.1)
    ((model.environment state target.1).mass_nonneg target.2)
  mass_sum := by
    rw [Fintype.sum_prod_type]
    simp only [← Finset.mul_sum, FiniteReportLaw.mass_sum, mul_one]

/-- The complete finite evolutionary kernel in factorial-product form. -/
theorem transition_mass {population : ℕ} (model : Model H E population)
    (state target : State H E population) :
    (transition model state).mass target =
      (Nat.factorial population : ℝ) /
        (∏ reproductiveType, (Nat.factorial (target.1.val reproductiveType) : ℝ)) *
          (∏ reproductiveType, (∑ firstParent, ∑ secondParent,
            (model.mating state).mass (firstParent, secondParent) *
              (model.transmission state (firstParent, secondParent)).mass reproductiveType) ^
                target.1.val reproductiveType) *
                  (model.environment state target.1).mass target.2 := by
  unfold transition
  rw [multinomialLaw_mass]
  simp_rw [offspringLaw_mass]

/-- Arbitrarily many generations remain normalized, with time-varying models. -/
noncomputable def historyLaw {population : ℕ} (models : ℕ → Model H E population)
    (initial : FiniteReportLaw (State H E population)) (generations : ℕ) :
    FiniteReportLaw (State H E population) :=
  ExactFiniteHistoryLaw.propagate initial
    (fun generation ↦ transition (models generation)) generations

theorem historyLaw_normalized {population : ℕ} (models : ℕ → Model H E population)
    (initial : FiniteReportLaw (State H E population)) (generations : ℕ) :
    ∑ target, (historyLaw models initial generations).mass target = 1 :=
  (historyLaw models initial generations).mass_sum

end Descent.Portability.FiniteReproductiveKernel
