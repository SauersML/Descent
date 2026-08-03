/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Calibrator.CertificateGrading

/-!
# Finite minimax duality: the ungraded certificate calculus

This file states the genuine finite decision problem behind the slogan
"ungraded mixture certificates are complete by minimax duality".  The problem
contains only an observation kernel and a numerical loss.  In particular, it
does not accept duality, compactness, convexity, or a lower bound as a field.

The sound inequality `mixtureDualRisk ≤ minimaxRisk` is proved from finite loss bounds. The
reverse inequality is the finite minimax theorem and remains an explicit `sorry`: importing a
literature theorem, assuming a duality proposition, or defining the dual value to equal the
primal value would make the file green while deleting its mathematical content.
-/

namespace Calibrator.FiniteMinimax

open scoped BigOperators
open Calibrator.CertificateGrading

/-- A finite statistical decision problem.  All three index types are
nonempty (`Fin (n + 1)`), and every observation law is Mathlib's `PMF`. -/
structure Problem (parameterCount actionCount observationCount : ℕ) where
  observation : Fin (parameterCount + 1) → FinitePrior observationCount
  loss : Fin (parameterCount + 1) → Fin (actionCount + 1) → ℝ

/-- Randomized decision rules, represented without side-condition fields. -/
abbrev Rule (actionCount observationCount : ℕ) :=
  Fin (observationCount + 1) → FinitePrior actionCount

namespace Problem

variable {parameterCount actionCount observationCount : ℕ}
    (E : Problem parameterCount actionCount observationCount)

/-- Forget the action/loss layer while retaining the exact observation kernel
used by the decision problem.  A target and its graded moment probes then make
that same kernel into a genuine mixture-certificate experiment. -/
noncomputable def toMixtureExperiment
    (target : Fin (parameterCount + 1) → ℝ)
    (moment : ℕ → Fin (parameterCount + 1) → ℝ) :
    FiniteMixtureExperiment parameterCount observationCount where
  target := target
  moment := moment
  observation := E.observation

/-- The bridge is law-preserving: the certificate layer and the decision
layer use exactly the same prior-predictive observation law. -/
@[simp] theorem toMixtureExperiment_mixture
    (target : Fin (parameterCount + 1) → ℝ)
    (moment : ℕ → Fin (parameterCount + 1) → ℝ)
    (π : FinitePrior parameterCount) :
    (E.toMixtureExperiment target moment).mixture π =
      π.bind E.observation := rfl

/-- Frequentist risk at one parameter value. -/
noncomputable def risk
    (δ : Rule actionCount observationCount)
    (θ : Fin (parameterCount + 1)) : ℝ :=
  ∑ x, (E.observation θ).probability x *
    ∑ a, (δ x).probability a * E.loss θ a

/-- Worst-case risk of a randomized rule. -/
noncomputable def worstRisk (δ : Rule actionCount observationCount) : ℝ :=
  sSup (Set.range (E.risk δ))

/-- Primal minimax value. -/
noncomputable def minimaxRisk : ℝ :=
  sInf (Set.range E.worstRisk)

/-- Bayes risk of a rule under a finite prior. -/
noncomputable def bayesRisk
    (π : FinitePrior parameterCount)
    (δ : Rule actionCount observationCount) : ℝ :=
  ∑ θ, π.probability θ * E.risk δ θ

/-- Optimal Bayes value at a fixed prior. -/
noncomputable def optimalBayesRisk (π : FinitePrior parameterCount) : ℝ :=
  sInf (Set.range (E.bayesRisk π))

/-- Ungraded mixture-certificate value: optimize over every prior. -/
noncomputable def mixtureDualRisk : ℝ :=
  sSup (Set.range E.optimalBayesRisk)

/-- **Half of duality, proved: a prior-averaged risk never exceeds the worst case.**

    `bayesRisk π δ` is an average of `risk δ θ` against a probability vector, and every
    term is at most `worstRisk δ`, which is the supremum over `θ`. The supremum is attained
    on a finite range, so it is a genuine bound rather than a formal `sSup`.

    This is the inequality that makes the mixture certificate sound: no prior can certify
    more than the minimax value. It is stated separately from the duality below because it
    is true unconditionally and needs no minimax theorem. -/
theorem bayesRisk_le_worstRisk (π : FinitePrior parameterCount)
    (δ : Rule actionCount observationCount) :
    E.bayesRisk π δ ≤ E.worstRisk δ := by
  have hbdd : BddAbove (Set.range (E.risk δ)) := (Set.finite_range _).bddAbove
  have hle : ∀ θ, E.risk δ θ ≤ E.worstRisk δ := fun θ ↦ le_csSup hbdd ⟨θ, rfl⟩
  have hmass : ∑ θ, FinitePrior.probability π θ = 1 :=
    (finitePrior_probability_mem π).2
  calc E.bayesRisk π δ = ∑ θ, FinitePrior.probability π θ * E.risk δ θ := rfl
    _ ≤ ∑ θ, FinitePrior.probability π θ * E.worstRisk δ :=
        Finset.sum_le_sum fun θ _ ↦
          mul_le_mul_of_nonneg_left (hle θ) (FinitePrior.probability_nonneg π θ)
    _ = E.worstRisk δ := by rw [← Finset.sum_mul, hmass, one_mul]

/-- Absolute loss bound at one parameter. The observation index is included in the sum to avoid
using normalization merely to optimize the constant. -/
noncomputable def pointRiskAbsBound (θ : Fin (parameterCount + 1)) : ℝ :=
  ∑ _x : Fin (observationCount + 1), ∑ a, |E.loss θ a|

/-- Uniform absolute risk bound for the whole finite decision problem. -/
noncomputable def riskAbsBound : ℝ := ∑ θ, E.pointRiskAbsBound θ

/-- Every pointwise risk is bounded by the finite absolute loss table. -/
theorem abs_risk_le_pointRiskAbsBound (δ : Rule actionCount observationCount)
    (θ : Fin (parameterCount + 1)) :
    |E.risk δ θ| ≤ E.pointRiskAbsBound θ := by
  have houter := FinitePrior.abs_mean_le_sum_abs (E.observation θ)
    (fun x ↦ FinitePrior.mean (δ x) (E.loss θ))
  have hinner : ∀ x : Fin (observationCount + 1),
      |FinitePrior.mean (δ x) (E.loss θ)| ≤ ∑ a, |E.loss θ a| :=
    fun x ↦ FinitePrior.abs_mean_le_sum_abs (δ x) (E.loss θ)
  calc
    |E.risk δ θ| =
        |FinitePrior.mean (E.observation θ)
          (fun x ↦ FinitePrior.mean (δ x) (E.loss θ))| := by
            rfl
    _ ≤ ∑ x, |FinitePrior.mean (δ x) (E.loss θ)| := houter
    _ ≤ ∑ x, ∑ a, |E.loss θ a| := Finset.sum_le_sum fun x _ ↦ hinner x
    _ = E.pointRiskAbsBound θ := rfl

/-- Bayes risks are uniformly bounded below, so their real-valued infimum is genuine. -/
theorem bayesRisk_bddBelow (π : FinitePrior parameterCount) :
    BddBelow (Set.range (E.bayesRisk π)) := by
  refine ⟨-E.riskAbsBound, ?_⟩
  rintro value ⟨δ, rfl⟩
  have hmean := FinitePrior.abs_mean_le_sum_abs π (E.risk δ)
  have hrisk : ∑ θ, |E.risk δ θ| ≤ E.riskAbsBound := by
    unfold riskAbsBound
    exact Finset.sum_le_sum fun θ _ ↦ E.abs_risk_le_pointRiskAbsBound δ θ
  exact neg_le_of_abs_le (hmean.trans hrisk)

/-- A fixed prior's optimal Bayes value is below every rule's worst-case risk. -/
theorem optimalBayesRisk_le_worstRisk (π : FinitePrior parameterCount)
    (δ : Rule actionCount observationCount) :
    E.optimalBayesRisk π ≤ E.worstRisk δ := by
  exact (csInf_le (E.bayesRisk_bddBelow π) ⟨δ, rfl⟩).trans
    (E.bayesRisk_le_worstRisk π δ)

/-- **The unconditional sound half of finite minimax duality.**

    Optimizing Bayes risk over every finite prior cannot exceed the minimax risk. This closes
    both order-theoretic layers of the earlier pointwise inequality and uses only the explicit
    finite loss bound above. -/
theorem mixtureDualRisk_le_minimaxRisk : E.mixtureDualRisk ≤ E.minimaxRisk := by
  unfold mixtureDualRisk minimaxRisk
  apply csSup_le (Set.range_nonempty E.optimalBayesRisk)
  intro bayesValue hbayes
  rcases hbayes with ⟨π, rfl⟩
  apply le_csInf (Set.range_nonempty E.worstRisk)
  intro worstValue hworst
  rcases hworst with ⟨δ, rfl⟩
  exact E.optimalBayesRisk_le_worstRisk π δ

/-- Every risk is bounded below by the smallest loss value, uniformly in the rule.

    Risk is a double average of loss values against probability vectors, so it cannot fall
    below their minimum. This is what makes the infima below genuine rather than formal:
    the rule space is a continuum, and without a floor `sInf` would carry no information. -/
theorem exists_risk_lower_bound :
    ∃ m : ℝ, ∀ (δ : Rule actionCount observationCount) (θ : Fin (parameterCount + 1)),
      m ≤ E.risk δ θ := by
  obtain ⟨q, -, hq⟩ :=
    (Finset.univ : Finset (Fin (parameterCount + 1) × Fin (actionCount + 1))).exists_min_image
      (fun q ↦ E.loss q.1 q.2) ⟨(0, 0), Finset.mem_univ _⟩
  refine ⟨E.loss q.1 q.2, fun δ θ ↦ ?_⟩
  have hinner : ∀ x : Fin (observationCount + 1),
      E.loss q.1 q.2 ≤ ∑ a, FinitePrior.probability (δ x) a * E.loss θ a := by
    intro x
    have hmass : ∑ a, FinitePrior.probability (δ x) a = 1 :=
      (finitePrior_probability_mem (δ x)).2
    calc E.loss q.1 q.2
        = ∑ a, FinitePrior.probability (δ x) a * E.loss q.1 q.2 := by
          rw [← Finset.sum_mul, hmass, one_mul]
      _ ≤ ∑ a, FinitePrior.probability (δ x) a * E.loss θ a :=
          Finset.sum_le_sum fun a _ ↦
            mul_le_mul_of_nonneg_left (hq (θ, a) (Finset.mem_univ _))
              (FinitePrior.probability_nonneg (δ x) a)
  have hmassObs : ∑ x, FinitePrior.probability (E.observation θ) x = 1 :=
    (finitePrior_probability_mem (E.observation θ)).2
  calc E.loss q.1 q.2
      = ∑ x, FinitePrior.probability (E.observation θ) x * E.loss q.1 q.2 := by
        rw [← Finset.sum_mul, hmassObs, one_mul]
    _ ≤ ∑ x, FinitePrior.probability (E.observation θ) x *
          ∑ a, FinitePrior.probability (δ x) a * E.loss θ a :=
        Finset.sum_le_sum fun x _ ↦
          mul_le_mul_of_nonneg_left (hinner x)
            (FinitePrior.probability_nonneg (E.observation θ) x)
    _ = E.risk δ θ := rfl

/-- Mix two decision rules with weight `t`, as a Bernoulli choice between them.

    The rule space has to be convex for the separation argument that would close duality:
    the set of achievable risk profiles is the image of this space under an affine map, and
    a separating hyperplane needs that image to be convex. -/
noncomputable def mixRule (t : NNReal) (ht : t ≤ 1)
    (δ₁ δ₂ : Rule actionCount observationCount) : Rule actionCount observationCount :=
  fun x ↦ (PMF.bernoulli t ht).bind fun b ↦ if b then δ₁ x else δ₂ x

/-- The mixed rule's action law is the corresponding mixture of the two action laws. -/
theorem mixRule_apply (t : NNReal) (ht : t ≤ 1)
    (δ₁ δ₂ : Rule actionCount observationCount) (x : Fin (observationCount + 1))
    (a : Fin (actionCount + 1)) :
    (mixRule t ht δ₁ δ₂ x) a
      = (t : ENNReal) * (δ₁ x) a + (1 - (t : ENNReal)) * (δ₂ x) a := by
  simp only [mixRule, PMF.bind_apply, PMF.bernoulli_apply, tsum_bool, if_true, if_false]
  exact add_comm _ _

/-- The mixed rule's action probabilities are the real mixture of the two rules'. -/
theorem probability_mixRule (t : NNReal) (ht : t ≤ 1)
    (δ₁ δ₂ : Rule actionCount observationCount) (x : Fin (observationCount + 1))
    (a : Fin (actionCount + 1)) :
    FinitePrior.probability (mixRule t ht δ₁ δ₂ x) a
      = (t : ℝ) * FinitePrior.probability (δ₁ x) a
        + (1 - (t : ℝ)) * FinitePrior.probability (δ₂ x) a := by
  have htle : (t : ENNReal) ≤ 1 := by exact_mod_cast ht
  have h1 : ((t : ENNReal) * (δ₁ x) a) ≠ ⊤ :=
    ENNReal.mul_ne_top (by simp) (PMF.apply_ne_top _ _)
  have h2 : ((1 - (t : ENNReal)) * (δ₂ x) a) ≠ ⊤ :=
    ENNReal.mul_ne_top (by simp) (PMF.apply_ne_top _ _)
  unfold FinitePrior.probability
  rw [mixRule_apply, ENNReal.toReal_add h1 h2, ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_sub_of_le htle (by simp)]
  simp

/-- **Risk is affine in the rule.** Mixing two rules mixes their risks with the same
    weight, at every parameter value.

    This is what makes the set of achievable risk profiles convex, which is the hypothesis
    a separating-hyperplane argument needs. -/
theorem risk_mixRule (t : NNReal) (ht : t ≤ 1)
    (δ₁ δ₂ : Rule actionCount observationCount) (θ : Fin (parameterCount + 1)) :
    E.risk (mixRule t ht δ₁ δ₂) θ
      = (t : ℝ) * E.risk δ₁ θ + (1 - (t : ℝ)) * E.risk δ₂ θ := by
  unfold risk
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  have hinner : ∑ a, FinitePrior.probability (mixRule t ht δ₁ δ₂ x) a * E.loss θ a
      = (t : ℝ) * ∑ a, FinitePrior.probability (δ₁ x) a * E.loss θ a
        + (1 - (t : ℝ)) * ∑ a, FinitePrior.probability (δ₂ x) a * E.loss θ a := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    rw [probability_mixRule]
    ring
  rw [hinner]
  ring

/-- The set of risk profiles achievable by some rule, as a subset of `ℝ^Θ`. -/
def riskProfiles : Set (Fin (parameterCount + 1) → ℝ) :=
  Set.range fun δ : Rule actionCount observationCount ↦ E.risk δ

/-- **The achievable risk profiles form a convex set.**

    Directly from `risk_mixRule`: a convex combination of two profiles is the profile of the
    correspondingly mixed rule. This is the hypothesis a separating-hyperplane argument
    consumes, and it is the reason the rule space had to admit mixtures. -/
theorem convex_riskProfiles : Convex ℝ E.riskProfiles := by
  rintro y₁ ⟨δ₁, rfl⟩ y₂ ⟨δ₂, rfl⟩ p q hp hq hpq
  have hple : p ≤ 1 := by linarith
  refine ⟨mixRule ⟨p, hp⟩ (by exact_mod_cast hple) δ₁ δ₂, ?_⟩
  funext θ
  have hq' : q = 1 - p := by linarith
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [risk_mixRule, hq']
  norm_num

/-- The open half-space of profiles strictly below a given level in every coordinate. -/
def belowLevel (v : ℝ) : Set (Fin (parameterCount + 1) → ℝ) :=
  {y | ∀ θ, y θ < v}

theorem convex_belowLevel (v : ℝ) :
    Convex ℝ (belowLevel (parameterCount := parameterCount) v) := by
  intro y₁ h₁ y₂ h₂ p q hp hq hpq θ
  have hy1 : y₁ θ < v := h₁ θ
  have hy2 : y₂ θ < v := h₂ θ
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rcases lt_or_eq_of_le hp with hp' | hp'
  · have h1 : p * y₁ θ < p * v := mul_lt_mul_of_pos_left hy1 hp'
    have h2 : q * y₂ θ ≤ q * v := mul_le_mul_of_nonneg_left (le_of_lt hy2) hq
    have hsum : p * v + q * v = v := by rw [← add_mul, hpq, one_mul]
    linarith
  · have hp0 : p = 0 := hp'.symm
    have hq1 : q = 1 := by linarith
    rw [hp0, hq1]
    simpa using hy2

/-- A rule whose risk is everywhere below a level has worst-case risk below it.

    The supremum over a finite range is attained, so a strict bound at every parameter is a
    strict bound on the supremum -- which a formal `sSup` would not give. -/
theorem worstRisk_lt_of_forall_lt (δ : Rule actionCount observationCount) (v : ℝ)
    (h : ∀ θ, E.risk δ θ < v) : E.worstRisk δ < v := by
  obtain ⟨θ, hθ⟩ :=
    (Set.range_nonempty (E.risk δ)).csSup_mem (Set.finite_range _)
  unfold worstRisk
  rw [← hθ]
  exact h θ

/-- **The two sets are disjoint at the minimax level.**

    No achievable risk profile lies strictly below the minimax value in every coordinate:
    such a profile would give a rule with worst-case risk below the infimum of worst-case
    risks. This is the emptiness hypothesis the separation theorem needs. -/
theorem disjoint_riskProfiles_belowLevel :
    Disjoint E.riskProfiles (belowLevel E.minimaxRisk) := by
  obtain ⟨m, hm⟩ := E.exists_risk_lower_bound
  have hbdd : BddBelow (Set.range E.worstRisk) := by
    refine ⟨m, ?_⟩
    rintro y ⟨δ, rfl⟩
    exact le_trans (hm δ 0) (le_csSup (Set.finite_range _).bddAbove ⟨0, rfl⟩)
  rw [Set.disjoint_left]
  rintro y ⟨δ, rfl⟩ hy
  have hlt : E.worstRisk δ < E.minimaxRisk := E.worstRisk_lt_of_forall_lt δ _ hy
  have hge : E.minimaxRisk ≤ E.worstRisk δ := csInf_le hbdd ⟨δ, rfl⟩
  linarith

/-- **The equalizer theorem: a constant-risk Bayes rule closes duality.**

    If a rule has the same risk at every parameter value and is Bayes against some prior,
    then the minimax value equals the mixture-certificate value, and that common value is the
    rule's risk. This is the standard sufficient condition, and it is proved here.

    An equalizer is stronger than a general saddle point: a least-favourable prior can be
    supported only on parameters attaining the worst risk, while other parameters have strictly
    smaller risk. Thus this lemma proves a useful sufficient condition but does not reduce the
    general theorem to equalizer existence. General duality still needs a finite-game separation
    argument, which Mathlib's decision-risk development does not currently provide. -/
theorem minimax_eq_of_equalizer (δstar : Rule actionCount observationCount)
    (πstar : FinitePrior parameterCount) (value : ℝ)
    (hconst : ∀ θ, E.risk δstar θ = value)
    (hbayes : E.optimalBayesRisk πstar = E.bayesRisk πstar δstar) :
    E.minimaxRisk = E.mixtureDualRisk ∧ E.minimaxRisk = value := by
  obtain ⟨m, hm⟩ := E.exists_risk_lower_bound
  have hworst : E.worstRisk δstar = value := by
    unfold worstRisk
    have hrange : Set.range (E.risk δstar) = {value} := by
      ext y
      constructor
      · rintro ⟨θ, rfl⟩; exact hconst θ
      · rintro rfl; exact ⟨0, hconst 0⟩
    rw [hrange, csSup_singleton]
  have hbayesValue : E.bayesRisk πstar δstar = value := by
    have hmass : ∑ θ, FinitePrior.probability πstar θ = 1 :=
      (finitePrior_probability_mem πstar).2
    calc E.bayesRisk πstar δstar
        = ∑ θ, FinitePrior.probability πstar θ * E.risk δstar θ := rfl
      _ = ∑ θ, FinitePrior.probability πstar θ * value := by
          exact Finset.sum_congr rfl fun θ _ ↦ by rw [hconst θ]
      _ = value := by rw [← Finset.sum_mul, hmass, one_mul]
  have hworstBdd : BddBelow (Set.range E.worstRisk) := by
    refine ⟨m, ?_⟩
    rintro y ⟨δ, rfl⟩
    exact le_trans (hm δ 0) (le_csSup (Set.finite_range _).bddAbove ⟨0, rfl⟩)
  have hminimax_le : E.minimaxRisk ≤ value := by
    rw [← hworst]
    exact csInf_le hworstBdd ⟨δstar, rfl⟩
  have hdualBdd : BddAbove (Set.range E.optimalBayesRisk) := by
    refine ⟨E.minimaxRisk, ?_⟩
    rintro y ⟨π, rfl⟩
    unfold minimaxRisk
    refine le_csInf (Set.range_nonempty E.worstRisk) ?_
    rintro z ⟨δ, rfl⟩
    exact E.optimalBayesRisk_le_worstRisk π δ
  have hvalue_le : value ≤ E.mixtureDualRisk := by
    rw [← hbayesValue, ← hbayes]
    exact le_csSup hdualBdd ⟨πstar, rfl⟩
  have hweak := E.mixtureDualRisk_le_minimaxRisk
  constructor
  · linarith
  · linarith

/-- **Finite minimax duality.**  Ungraded mixture-versus-mixture reasoning is
complete because the primal minimax value equals the optimization over all
Bayes priors.  This is the real theorem, not a definitional equality and not a
caller-supplied proposition.

    WHAT IS PROVED, AND WHAT IS NOT. `mixtureDualRisk_le_minimaxRisk` proves the sound
    direction unconditionally: finite loss bounds make every real infimum genuine, and an
    average against a prior never exceeds the worst case. The reverse inequality is the minimax
    theorem itself and needs a finite-game separation argument this corpus does not yet carry.

    The `sorry` is the whole equality rather than the missing half, because splitting it
    into a proved inequality plus an assumed one would put the hard direction in a
    hypothesis, where no audit reads it.  Here `AxiomScan` reports it. -/
theorem finite_minimax_duality : E.minimaxRisk = E.mixtureDualRisk := by
  sorry

/-- The program's "vacuous ungraded completeness" statement, now tied to an
actual decision problem rather than to a value defined to equal itself. -/
theorem ungraded_certificate_calculus_complete :
    E.minimaxRisk = E.mixtureDualRisk :=
  E.finite_minimax_duality

end Problem

end Calibrator.FiniteMinimax
