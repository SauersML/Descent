/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Blindness.BlindnessRegistry
import Descent.Decision.FiniteMinimax

/-!
# From blindness witnesses to minimax floors

`ObservationalCeiling` proves a qualitative law: a probe that returns the same data on two
objects certifies neither, so no criterion factoring through it decides any property that
separates them. `FiniteMinimax` proves a quantitative one: two parameters emitting the same
observation law force minimax risk at least half the loss separation, and no downstream
channel repairs it.

Those two files never met. The registry's instances stopped at "no rule reading this probe
decides the property", and the decision-theoretic endpoints stood proved but unconsumed.
This file is the bridge, and it is the reason the bridge is worth building: a blindness
witness is upgraded from *this probe fails* to *every procedure fails, by at least this
much, whatever it does with the data afterwards*.

## The reduction

A `Blindness.ProbeBlindness probe P` supplies two objects with `probe positive = probe negative`.
Turn it into a two-point decision problem by choosing any **readout** of the probe — a
finite, possibly randomized measurement `Data → FinitePrior n`. The observation kernel is
`readout ∘ probe` at the two witnesses, the action set is the binary verdict `P` holds /
`P` fails, and the loss is `0` for the correct verdict and `1` for the wrong one, so risk
*is* error probability (`Blindness.ProbeBlindness.risk_readoutProblem`).

`same_data` then says the two observation laws are equal on the nose, and
`half_separation_le_minimaxRisk_of_observation_eq` gives a floor of `1 / 2`: no rule, at
any sample size, with any randomization, beats a coin flip on the worst of the two
hypotheses. `Blindness.ProbeBlindness.blindReadoutProblem_minimaxRisk` shows the floor is exactly
attained, so the
cost of blindness is a coin flip and not more.

Nothing here restricts the readout. It may be noisy, it may quantize, it may be the whole
downstream pipeline folded into one map;
`Blindness.ProbeBlindness.half_le_garbled_readoutProblem_minimaxRisk`
adds the further channel-monotonicity statement on top. This is the sense in which the
ceiling is a ceiling.

## Instances

The three biological instances of the registry that carry an exact witness pair are pushed
through, and two of them are packaged as `Blindness.ProbeBlindness` witnesses here for the first
time -- previously they existed only as bare equations:

- instance 8, `half_le_averageEffect_minimaxRisk`: no procedure reading the dosage
  regression slope calls additive-versus-dominant right more than half the time at
  `p = 1/2`;
- instance 9, `half_le_normalisedPairwiseSurvival_minimaxRisk`: likewise for the
  coalescent timescale, from the normalised pairwise survival curve;
- instance 10, `half_le_totalFamilyFraction_minimaxRisk`: likewise for sweep origin
  multiplicity, from the total selected-allele frequency.
-/

namespace Descent.Decision

open Descent.Decision.FiniteMinimax

variable {Object Data : Type*} {probe : Object → Data} {P : Object → Prop}

/-- The two-point decision problem a blindness witness induces, given any finite
randomized **readout** of the probe.

Parameter `0` is the object satisfying `P`, parameter `1` the object failing it. Action `0`
is the verdict "`P` holds", action `1` the verdict "`P` fails". The loss is `0` on the
correct verdict and `1` on the wrong one, so the risk of a rule is exactly its error
probability at that hypothesis.

The readout is arbitrary: any map from probe data to a finite distribution over
observations. Quantization, added noise, repeated sampling folded into a summary, or an
entire analysis pipeline are all instances. What it may not do is see anything other than
the probe -- which is what makes the floor below a statement about the probe rather than
about the analyst. -/
noncomputable def _root_.Descent.Blindness.ProbeBlindness.readoutProblem (B : Blindness.ProbeBlindness probe P)
    {observationCount : ℕ} (readout : Data → CertificateGrading.FinitePrior observationCount) :
    Problem 1 1 observationCount where
  observation := fun θ ↦ readout (probe (if θ = 0 then B.positive else B.negative))
  loss := fun θ action ↦ if θ = action then 0 else 1

/-- The readout of the `P`-satisfying witness. -/
@[simp] theorem _root_.Descent.Blindness.ProbeBlindness.readoutProblem_observation_zero (B : Blindness.ProbeBlindness probe P)
    {observationCount : ℕ}
    (readout : Data → CertificateGrading.FinitePrior observationCount) :
    (B.readoutProblem readout).observation 0 = readout (probe B.positive) := by
  show readout (probe (if (0 : Fin (1 + 1)) = 0 then B.positive else B.negative)) = _
  rw [if_pos rfl]

/-- The readout of the `P`-failing witness. -/
@[simp] theorem _root_.Descent.Blindness.ProbeBlindness.readoutProblem_observation_one (B : Blindness.ProbeBlindness probe P)
    {observationCount : ℕ}
    (readout : Data → CertificateGrading.FinitePrior observationCount) :
    (B.readoutProblem readout).observation 1 = readout (probe B.negative) := by
  show readout (probe (if (1 : Fin (1 + 1)) = 0 then B.positive else B.negative)) = _
  rw [if_neg (by decide)]

/-- **Blindness is exact observational equivalence.** The two hypotheses emit literally the
same observation law under every readout of the probe. This is the hypothesis that the
finite Le Cam theorems consume, and `same_data` is the whole of its content. -/
theorem _root_.Descent.Blindness.ProbeBlindness.readoutProblem_observation_eq (B : Blindness.ProbeBlindness probe P)
    {observationCount : ℕ}
    (readout : Data → CertificateGrading.FinitePrior observationCount) :
    (B.readoutProblem readout).observation 0 = (B.readoutProblem readout).observation 1 := by
  rw [Blindness.ProbeBlindness.readoutProblem_observation_zero, Blindness.ProbeBlindness.readoutProblem_observation_one, B.same_data]

/-- The zero-one loss separates the two hypotheses by one at every action: whichever verdict
is returned, it is wrong at one of them. -/
theorem _root_.Descent.Blindness.ProbeBlindness.readoutProblem_loss_add (B : Blindness.ProbeBlindness probe P)
    {observationCount : ℕ}
    (readout : Data → CertificateGrading.FinitePrior observationCount)
    (action : Fin (1 + 1)) :
    (1 : ℝ) ≤ (B.readoutProblem readout).loss 0 action
      + (B.readoutProblem readout).loss 1 action := by
  fin_cases action <;> simp [Blindness.ProbeBlindness.readoutProblem]

/-- **Risk is error probability.** With the zero-one verdict loss, the risk of a rule at a
hypothesis is one minus the chance it returns that hypothesis' own verdict. Stated so that
the floor below reads as a misclassification rate and not as an abstract loss. -/
theorem _root_.Descent.Blindness.ProbeBlindness.risk_readoutProblem (B : Blindness.ProbeBlindness probe P)
    {observationCount : ℕ}
    (readout : Data → CertificateGrading.FinitePrior observationCount)
    (rule : Rule 1 observationCount) (θ : Fin (1 + 1)) :
    (B.readoutProblem readout).risk rule θ =
      1 - ∑ x, ((B.readoutProblem readout).observation θ).probability x *
        (rule x).probability θ := by
  have hinner : ∀ x : Fin (observationCount + 1),
      ∑ action, (rule x).probability action * (B.readoutProblem readout).loss θ action
        = 1 - (rule x).probability θ := by
    intro x
    have hsplit : ∀ action : Fin (1 + 1),
        (rule x).probability action * (B.readoutProblem readout).loss θ action
          = (rule x).probability action
            - (if θ = action then (rule x).probability action else 0) := by
      intro action
      by_cases haction : θ = action <;> simp [Blindness.ProbeBlindness.readoutProblem, haction]
    rw [Finset.sum_congr rfl fun action _ ↦ hsplit action, Finset.sum_sub_distrib,
      (CertificateGrading.finitePrior_probability_mem (rule x)).2]
    simp
  have hmass : ∑ x, ((B.readoutProblem readout).observation θ).probability x = 1 :=
    (CertificateGrading.finitePrior_probability_mem _).2
  calc (B.readoutProblem readout).risk rule θ
      = ∑ x, ((B.readoutProblem readout).observation θ).probability x *
          ∑ action, (rule x).probability action *
            (B.readoutProblem readout).loss θ action := rfl
    _ = ∑ x, ((B.readoutProblem readout).observation θ).probability x *
          (1 - (rule x).probability θ) := by
        exact Finset.sum_congr rfl fun x _ ↦ by rw [hinner x]
    _ = 1 - ∑ x, ((B.readoutProblem readout).observation θ).probability x *
          (rule x).probability θ := by
        simp only [mul_sub, mul_one]
        rw [Finset.sum_sub_distrib, hmass]

/-- **Every rule is at coin-flip error on the worse hypothesis.** No randomized decision
rule reading any finite readout of a blind probe has worst-case error probability below
one half. -/
theorem _root_.Descent.Blindness.ProbeBlindness.half_le_readoutProblem_worstRisk (B : Blindness.ProbeBlindness probe P)
    {observationCount : ℕ}
    (readout : Data → CertificateGrading.FinitePrior observationCount)
    (rule : Rule 1 observationCount) :
    (1 : ℝ) / 2 ≤ (B.readoutProblem readout).worstRisk rule :=
  (B.readoutProblem readout).half_separation_le_worstRisk_of_observation_eq 0 1 1
    (B.readoutProblem_observation_eq readout) (B.readoutProblem_loss_add readout) rule

/-- **The quantitative ceiling.** A blindness witness forces minimax error probability at
least one half, at every sample size, for every randomized rule, under every finite readout
of the probe.

This is the quantitative form of `no_criterion_of_factors`. That theorem says no criterion
*decides* the property; this one says every criterion is wrong at least half the time at
one of the two witnesses, which is what an empirical claim about a blind probe actually
costs. -/
theorem _root_.Descent.Blindness.ProbeBlindness.half_le_readoutProblem_minimaxRisk (B : Blindness.ProbeBlindness probe P)
    {observationCount : ℕ}
    (readout : Data → CertificateGrading.FinitePrior observationCount) :
    (1 : ℝ) / 2 ≤ (B.readoutProblem readout).minimaxRisk :=
  (B.readoutProblem readout).half_separation_le_minimaxRisk_of_observation_eq 0 1 1
    (B.readoutProblem_observation_eq readout) (B.readoutProblem_loss_add readout)

/-- **Downstream processing does not help.** Passing the readout through any further
parameter-independent stochastic channel -- binning, compression, feature extraction, a
second-stage model -- leaves the same floor. -/
theorem _root_.Descent.Blindness.ProbeBlindness.half_le_garbled_readoutProblem_minimaxRisk (B : Blindness.ProbeBlindness probe P)
    {observationCount summaryCount : ℕ}
    (readout : Data → CertificateGrading.FinitePrior observationCount)
    (channel : Fin (observationCount + 1) → CertificateGrading.FinitePrior summaryCount) :
    (1 : ℝ) / 2 ≤
      ((B.readoutProblem readout).garbleObservations summaryCount channel).minimaxRisk :=
  (B.readoutProblem readout).half_separation_le_garbled_minimaxRisk_of_observation_eq
    summaryCount channel 0 1 1
    (B.readoutProblem_observation_eq readout) (B.readoutProblem_loss_add readout)

/-- The readout that records nothing is the corpus's canonical uninformative experiment.
Definitional: a constant observation kernel with the zero-one verdict loss *is*
`indistinguishableBinaryProblem 1`. -/
theorem _root_.Descent.Blindness.ProbeBlindness.uninformativeReadoutProblem_eq (B : Blindness.ProbeBlindness probe P) :
    B.readoutProblem (fun _ ↦ (PMF.pure 0 : CertificateGrading.FinitePrior 0)) =
      Problem.indistinguishableBinaryProblem 1 :=
  rfl

/-- **The floor is exactly a coin flip, not more.** Sharpness matters here: without it the
bound would be compatible with the blindness being arbitrarily worse than a coin flip, and
the registry's instances would carry no calibrated cost. The fair rule attains it. -/
theorem _root_.Descent.Blindness.ProbeBlindness.blindReadoutProblem_minimaxRisk (B : Blindness.ProbeBlindness probe P) :
    (B.readoutProblem (fun _ ↦ (PMF.pure 0 : CertificateGrading.FinitePrior 0))).minimaxRisk
      = 1 / 2 := by
  rw [B.uninformativeReadoutProblem_eq, Problem.indistinguishableBinaryProblem_minimaxRisk]



/-! ## Instance 8: the dominance blind spot costs a coin flip -/

/-- **No procedure reading the dosage-regression slope beats a coin flip on additivity.**

`averageEffect_blind_to_dominance` is the witness and `averageEffect_eq_regression_slope`
identifies the probe with the least-squares slope of genotypic value on allele dosage. So
the object bounded here is the coefficient a polygenic score actually fits: at `p = 1/2`,
every rule reading any finite readout of that coefficient misclassifies additive versus
dominant with probability at least one half at one of the two loci. -/
theorem half_le_averageEffect_minimaxRisk {δ : ℝ} (hδ : δ ≠ 0) (a : ℝ)
    {observationCount : ℕ}
    (readout : ℝ → CertificateGrading.FinitePrior observationCount) :
    (1 : ℝ) / 2 ≤ ((Blindness.averageEffect_blind_to_dominance hδ a).readoutProblem readout).minimaxRisk :=
  (Blindness.averageEffect_blind_to_dominance hδ a).half_le_readoutProblem_minimaxRisk readout

/-! ## Instance 9: the coalescent timescale blind spot -/

/-- **Instance 9 as a witness pair.** The registry proved the equation
`normalised_pairwise_blind_to_rate` and stopped there; the blindness was stated in prose.
This packages it in the registry's own standard form, so it can be consumed by the
`Blindness.ProbeBlindness` law and by the minimax floor below.

Objects are nonzero coalescence rates, the probe is the entire normalised pairwise survival
curve `x ↦ exp(-x)` -- not a summary of it, the whole function -- and the property is being
the first of the two rates. -/
noncomputable def normalisedPairwiseSurvival_blind_to_rate
    {rate₁ rate₂ : ℝ} (h₁ : rate₁ ≠ 0) (h₂ : rate₂ ≠ 0) (hne : rate₁ ≠ rate₂) :
    Blindness.ProbeBlindness
      (fun r : {r : ℝ // r ≠ 0} ↦ fun x : ℝ ↦ Blindness.pairwiseCoalescentSurvival r.1 (x / r.1))
      (fun r : {r : ℝ // r ≠ 0} ↦ r.1 = rate₁) where
  positive := ⟨rate₁, h₁⟩
  negative := ⟨rate₂, h₂⟩
  same_data := funext fun x ↦ Blindness.normalised_pairwise_blind_to_rate rate₁ rate₂ x h₁ h₂
  holds := rfl
  fails := hne.symm

/-- **No criterion reading the normalised pairwise survival curve decides the rate.** The
qualitative half, stated because a witness no criterion theorem consumes proves nothing. -/
theorem no_normalisedPairwiseSurvival_criterion_for_rate
    {rate₁ rate₂ : ℝ} (h₁ : rate₁ ≠ 0) (h₂ : rate₂ ≠ 0) (hne : rate₁ ≠ rate₂)
    {Verdict : Type*} (combine : (ℝ → ℝ) → Verdict) :
    ¬ ∃ accept : Verdict → Prop, ∀ r : {r : ℝ // r ≠ 0},
        r.1 = rate₁ ↔ accept (combine (fun x ↦ Blindness.pairwiseCoalescentSurvival r.1 (x / r.1))) :=
  (normalisedPairwiseSurvival_blind_to_rate h₁ h₂ hne).no_criterion_of_factors combine

/-- **The coalescent timescale blind spot costs a coin flip.** Two `Λ`-coalescents whose raw
timescales differ by any factor are misidentified with probability at least one half by
every rule reading any finite readout of the normalised pairwise law -- which is what the
measured five-model table in the registry is a picture of. -/
theorem half_le_normalisedPairwiseSurvival_minimaxRisk
    {rate₁ rate₂ : ℝ} (h₁ : rate₁ ≠ 0) (h₂ : rate₂ ≠ 0) (hne : rate₁ ≠ rate₂)
    {observationCount : ℕ}
    (readout : (ℝ → ℝ) → CertificateGrading.FinitePrior observationCount) :
    (1 : ℝ) / 2 ≤
      ((normalisedPairwiseSurvival_blind_to_rate h₁ h₂ hne).readoutProblem readout).minimaxRisk :=
  (normalisedPairwiseSurvival_blind_to_rate h₁ h₂ hne).half_le_readoutProblem_minimaxRisk readout

/-! ## Instance 10: the sweep-origin blind spot -/

/-- **Instance 10 as a witness pair.** Objects are marked breakout configurations of any
family count, the probe is the total selected-allele frequency, and the property is having
a single origin. The underlying content is `XiFromMarks`'s own theorem; what is new is the
`Blindness.ProbeBlindness` packaging, which is what the law and the minimax floor consume. -/
noncomputable def totalFamilyFraction_blind_to_originMultiplicity {finalFrequency : ℝ}
    (hfrequency : 0 < finalFrequency) :
    Blindness.ProbeBlindness
      (fun c : (k : ℕ) × (Fin k → ℝ) ↦ Blindness.XiFromMarks.totalFamilyFraction c.2)
      (fun c : (k : ℕ) × (Fin k → ℝ) ↦ ¬ Blindness.XiFromMarks.HasTwoPositiveFamilies c.2) where
  positive := ⟨1, ![finalFrequency]⟩
  negative := ⟨2, ![finalFrequency / 2, finalFrequency / 2]⟩
  same_data :=
    (Blindness.XiFromMarks.totalFamilyFraction_does_not_determine_multiplicity finalFrequency hfrequency).1
  holds :=
    (Blindness.XiFromMarks.totalFamilyFraction_does_not_determine_multiplicity finalFrequency hfrequency).2.1
  fails := not_not_intro
    (Blindness.XiFromMarks.totalFamilyFraction_does_not_determine_multiplicity
      finalFrequency hfrequency).2.2

/-- **No criterion reading the total selected-allele frequency decides origin
multiplicity.** -/
theorem no_totalFamilyFraction_criterion_for_originMultiplicity {finalFrequency : ℝ}
    (hfrequency : 0 < finalFrequency) {Verdict : Type*} (combine : ℝ → Verdict) :
    ¬ ∃ accept : Verdict → Prop, ∀ c : (k : ℕ) × (Fin k → ℝ),
        ¬ Blindness.XiFromMarks.HasTwoPositiveFamilies c.2 ↔
          accept (combine (Blindness.XiFromMarks.totalFamilyFraction c.2)) :=
  (totalFamilyFraction_blind_to_originMultiplicity hfrequency).no_criterion_of_factors combine

/-- **The sweep-origin blind spot costs a coin flip.** Every rule reading any finite readout
of the total selected-allele frequency calls one-origin versus two-origin wrong with probability at
least one half at one of the two sweeps. The registry's identification of
the escape route is unchanged and now quantified: the missing half of the information is
ancestry from four lineages, and no amount of extra precision on the frequency trajectory
substitutes for it. -/
theorem half_le_totalFamilyFraction_minimaxRisk {finalFrequency : ℝ}
    (hfrequency : 0 < finalFrequency)
    {observationCount : ℕ}
    (readout : ℝ → CertificateGrading.FinitePrior observationCount) :
    (1 : ℝ) / 2 ≤
      ((totalFamilyFraction_blind_to_originMultiplicity hfrequency).readoutProblem
        readout).minimaxRisk :=
  (totalFamilyFraction_blind_to_originMultiplicity hfrequency).half_le_readoutProblem_minimaxRisk
    readout

end Descent.Decision
