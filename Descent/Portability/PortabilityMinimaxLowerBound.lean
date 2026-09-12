/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.AttainableChronologyCurve
import Descent.Portability.ChronologyReportLaw
import Descent.Portability.ConditionalErrorCertificate
import Descent.Portability.FourCellCohortLaw
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Data.Real.Sqrt

assert_below Descent.Decision Descent.Program

/-!
# What source data cannot tell you about the target: a minimax lower bound for portability

A source experiment is observed through `n` independent replicas of a finite report law `P_h`
fixed by the demographic history `h` (`FourCellCohortLaw.cohortLaw`). The target quantity of
interest, for instance the squared correlation of a fixed score in the target population, is a
number `τ(h)`. An estimator is any function of the `n` replicas.

## Statement

**Two-point minimax lower bound.** For two histories with source laws `P`, `Q` and target values
`τ_P`, `τ_Q`, every estimator `T` of the target value from `n` source replicas satisfies

`max (E_{P^n} |T - τ_P|, E_{Q^n} |T - τ_Q|) ≥ (|τ_P - τ_Q| / 2) (1 - TV(P, Q))^n`
`≥ (|τ_P - τ_Q| / 2) max (0, 1 - n TV(P, Q))`

(`lowerBound_cohortLaw_pow`, `lowerBound_cohortLaw_totalVariation`), and in Hellinger form

`max (E_{P^n} |T - τ_P|, E_{Q^n} |T - τ_Q|) ≥ (|τ_P - τ_Q| / 4) ρ(P, Q)^{2n}`,

with `ρ(P, Q) = ∑ √(P Q) = 1 - H²(P, Q)` the Hellinger affinity
(`lowerBound_cohortLaw_hellingerAffinity`). The proof is Le Cam's two-point method. For one
observation the two errors add up to at least `|τ_P - τ_Q|` times the overlap `∑ min (P, Q)`
(`abs_sub_div_two_mul_lawOverlap_le`), and the overlap is `1 - TV(P, Q)`
(`lawOverlap_eq_one_sub_totalVariation`, from `ConditionalErrorCertificate.totalVariation_overlap`).
Over replicas the overlap is super-multiplicative (`pow_lawOverlap_le_lawOverlap_cohortLaw`), the
affinity is multiplicative (`hellingerAffinity_cohortLaw`), and `ρ² ≤ 2 ∑ min (P, Q)` by
Cauchy-Schwarz (`hellingerAffinity_sq_le_two_mul_lawOverlap`).

**Demographic instance: NOTE1 section 6, Theorem 5.** The three-block chronology of
`AttainableChronologyCurve` applies recombination exposure `R - b`, migration total `M` and then
recombination exposure `b`. Its totals are `M` and `R` whatever `b` is
(`migrationTotal_threeBlockHistory`, `recombinationTotal_threeBlockHistory`). Its final donor
fraction is `p = 1 - e^{-M}` and its coupling is `C = e^{-b}`. An admixed record then has the
chronology law of `(p, C)` (`threeBlockRecordLaw_mass`), whose squared correlation is `C²`
(`squaredCorrelation_threeBlockRecordLaw`). A source cohort mixes a report law that does not
depend on the chronology with admixed records at fraction `ε` (`sourceCohortLaw`). Two
chronologies `b₀`, `b₁` give source laws within total variation
`ε · 2p(1 - p) · |e^{-b₀} - e^{-b₁}|` (`totalVariation_sourceCohortLaw`), while their target squared
correlations are `e^{-2b₀}` and `e^{-2b₁}`. Every estimator of the target squared correlation from
`n` source replicas therefore has worst-case error at least
`(|e^{-2b₀} - e^{-2b₁}| / 2) max (0, 1 - n ε 2p(1 - p) |e^{-b₀} - e^{-b₁}|)`
(`sourceCohort_lowerBound`). At `b₀ = R`, `b₁ = 0` the two targets are the ends `e^{-2R}` and `1`
of the attainable range of Theorem 5. In NOTE1's worked example `M = R = log 2`, with target
squared correlations `1/4` and `1`, the bound is `(3/8) max (0, 1 - n ε / 4)`
(`logTwo_sourceCohort_lowerBound`). At `ε = 0` it is `3/8` for every `n`.

## Significance

Source data identify at most the source report law. When a portability quantity moves by `Δ`
while the source law moves by `δ` in total variation, no estimator from `n` source replicas has
worst-case error below `(Δ / 2)(1 - δ)^n`. When the source law does not move, no amount of source
data brings the error below `Δ / 2`. In the chronology model the migration and recombination
totals, the final allele frequencies and the fixed score are shared by both histories, and the
target squared correlation ranges over `[e^{-2R}, 1]`. Admixed source records separate the
histories only through `ε · 2p(1 - p)(1 - e^{-R})` per record. The total-variation bound stays
above half its value until `n` reaches `1 / (4 ε p(1 - p)(1 - e^{-R}))`, and the Hellinger form
needs `n` of order `1 / H²`. A claim about target portability therefore needs target-side
information. In this model that information is the exposure law `ν` of NOTE1 (30)-(36), or an
assumption tying the target to the source.

## Scope

Estimators are deterministic functions of the replicas. A randomized estimator is a mixture of
deterministic ones, and its errors are the same mixture, so the bound holds for it too; that step
is not formalized. Report spaces are finite and the replicas are independent and identically
distributed. The mixture model of the source cohort is a stated model, not a claim about any
cohort, and the base law is arbitrary. Adaptive designs, infinite report spaces, and the two-history
instance on the NOTE2 section 9 reference experiment are not covered here.

## Empirical status

None. The theorems are finite-sum inequalities about stated laws, so no measurement on any cohort
can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.PortabilityMinimaxLowerBound

open Finset
open Descent.Portability.FourCellCohortLaw (cohortLaw cohortLaw_mass)

noncomputable section

section TwoPoint

variable {Report : Type*} [Fintype Report]

/-- The overlap `∑ min (p, q)` of two report laws. -/
def lawOverlap (p q : FiniteReportLaw Report) : ℝ :=
  ∑ report, min (p.mass report) (q.mass report)

/-- The overlap is one minus the total variation. -/
theorem lawOverlap_eq_one_sub_totalVariation (p q : FiniteReportLaw Report) :
    lawOverlap p q = 1 - p.totalVariation q := by
  rw [ConditionalErrorCertificate.totalVariation_overlap]
  unfold lawOverlap
  ring

/-- **Le Cam's two-point bound for one observation.** Any estimator of the target value makes,
under one of the two laws, an expected absolute error of at least half the separation of the
targets times the overlap of the laws. -/
theorem abs_sub_div_two_mul_lawOverlap_le (p q : FiniteReportLaw Report) (τp τq : ℝ)
    (estimator : Report → ℝ) :
    |τp - τq| / 2 * lawOverlap p q ≤
      max (p.expectation fun report ↦ |estimator report - τp|)
        (q.expectation fun report ↦ |estimator report - τq|) := by
  have hpoint : ∀ report, |τp - τq| * min (p.mass report) (q.mass report) ≤
      p.mass report * |estimator report - τp| + q.mass report * |estimator report - τq| := by
    intro report
    have htriangle : |τp - τq| ≤ |estimator report - τp| + |estimator report - τq| := by
      have h1 := le_abs_self (estimator report - τp)
      have h2 := neg_abs_le (estimator report - τp)
      have h3 := le_abs_self (estimator report - τq)
      have h4 := neg_abs_le (estimator report - τq)
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    have hmin : 0 ≤ min (p.mass report) (q.mass report) :=
      le_min (p.mass_nonneg report) (q.mass_nonneg report)
    calc |τp - τq| * min (p.mass report) (q.mass report)
        ≤ (|estimator report - τp| + |estimator report - τq|) *
            min (p.mass report) (q.mass report) :=
          mul_le_mul_of_nonneg_right htriangle hmin
      _ = min (p.mass report) (q.mass report) * |estimator report - τp| +
            min (p.mass report) (q.mass report) * |estimator report - τq| := by ring
      _ ≤ p.mass report * |estimator report - τp| + q.mass report * |estimator report - τq| :=
          add_le_add (mul_le_mul_of_nonneg_right (min_le_left _ _) (abs_nonneg _))
            (mul_le_mul_of_nonneg_right (min_le_right _ _) (abs_nonneg _))
  have hsum : |τp - τq| * lawOverlap p q ≤
      p.expectation (fun report ↦ |estimator report - τp|) +
        q.expectation (fun report ↦ |estimator report - τq|) := by
    simp only [lawOverlap, FiniteReportLaw.expectation, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun report _ ↦ hpoint report
  have hleft := le_max_left (p.expectation fun report ↦ |estimator report - τp|)
    (q.expectation fun report ↦ |estimator report - τq|)
  have hright := le_max_right (p.expectation fun report ↦ |estimator report - τp|)
    (q.expectation fun report ↦ |estimator report - τq|)
  linarith

/-- Over independent replicas the overlap is at least the power of the one-record overlap. -/
theorem pow_lawOverlap_le_lawOverlap_cohortLaw (p q : FiniteReportLaw Report) (n : ℕ) :
    lawOverlap p q ^ n ≤ lawOverlap (cohortLaw p n) (cohortLaw q n) := by
  have hpoint : ∀ sample : Fin n → Report,
      ∏ member, min (p.mass (sample member)) (q.mass (sample member)) ≤
        min ((cohortLaw p n).mass sample) ((cohortLaw q n).mass sample) := by
    intro sample
    have hnonneg : ∀ member ∈ (univ : Finset (Fin n)),
        0 ≤ min (p.mass (sample member)) (q.mass (sample member)) := fun member _ ↦
      le_min (p.mass_nonneg _) (q.mass_nonneg _)
    rw [cohortLaw_mass, cohortLaw_mass]
    exact le_min (Finset.prod_le_prod hnonneg fun member _ ↦ min_le_left _ _)
      (Finset.prod_le_prod hnonneg fun member _ ↦ min_le_right _ _)
  calc lawOverlap p q ^ n
      = ∏ _member : Fin n, lawOverlap p q := (Fin.prod_const n _).symm
    _ = ∑ sample : Fin n → Report,
          ∏ member, min (p.mass (sample member)) (q.mass (sample member)) :=
        Fintype.prod_sum fun (_ : Fin n) (report : Report) ↦ min (p.mass report) (q.mass report)
    _ ≤ lawOverlap (cohortLaw p n) (cohortLaw q n) :=
        Finset.sum_le_sum fun sample _ ↦ hpoint sample

/-- Replicas amplify total variation at most as `1 - (1 - TV)^n`. -/
theorem totalVariation_cohortLaw_le_one_sub_pow (p q : FiniteReportLaw Report) (n : ℕ) :
    (cohortLaw p n).totalVariation (cohortLaw q n) ≤ 1 - (1 - p.totalVariation q) ^ n := by
  have h := pow_lawOverlap_le_lawOverlap_cohortLaw p q n
  rw [lawOverlap_eq_one_sub_totalVariation, lawOverlap_eq_one_sub_totalVariation] at h
  linarith

/-- Bernoulli's inequality for the one-record overlap: `1 - n TV ≤ (1 - TV)^n`. -/
theorem one_sub_mul_le_pow_one_sub_totalVariation (p q : FiniteReportLaw Report) (n : ℕ) :
    1 - n * p.totalVariation q ≤ (1 - p.totalVariation q) ^ n := by
  have hbound : -2 ≤ -p.totalVariation q := by
    have hone := FiniteReportLaw.totalVariation_le_one p q
    linarith
  calc 1 - n * p.totalVariation q = 1 + n * -p.totalVariation q := by ring
    _ ≤ (1 + -p.totalVariation q) ^ n := one_add_mul_le_pow hbound n
    _ = (1 - p.totalVariation q) ^ n := by rw [sub_eq_add_neg]

/-- **The minimax lower bound from `n` source replicas, power form.** For every estimator, one
of the two histories forces an expected absolute error of at least
`(|τ_P - τ_Q| / 2)(1 - TV(P, Q))^n`. -/
theorem lowerBound_cohortLaw_pow (p q : FiniteReportLaw Report) (n : ℕ) (τp τq : ℝ)
    (estimator : (Fin n → Report) → ℝ) :
    |τp - τq| / 2 * (1 - p.totalVariation q) ^ n ≤
      max ((cohortLaw p n).expectation fun sample ↦ |estimator sample - τp|)
        ((cohortLaw q n).expectation fun sample ↦ |estimator sample - τq|) := by
  rw [← lawOverlap_eq_one_sub_totalVariation]
  exact (mul_le_mul_of_nonneg_left (pow_lawOverlap_le_lawOverlap_cohortLaw p q n)
    (by positivity)).trans (abs_sub_div_two_mul_lawOverlap_le _ _ τp τq estimator)

/-- **The minimax lower bound from `n` source replicas, total-variation form.** For every
estimator, one of the two histories forces an expected absolute error of at least
`(|τ_P - τ_Q| / 2) max (0, 1 - n TV(P, Q))`. -/
theorem lowerBound_cohortLaw_totalVariation (p q : FiniteReportLaw Report) (n : ℕ) (τp τq : ℝ)
    (estimator : (Fin n → Report) → ℝ) :
    |τp - τq| / 2 * max 0 (1 - n * p.totalVariation q) ≤
      max ((cohortLaw p n).expectation fun sample ↦ |estimator sample - τp|)
        ((cohortLaw q n).expectation fun sample ↦ |estimator sample - τq|) := by
  have hpow : max 0 (1 - n * p.totalVariation q) ≤ (1 - p.totalVariation q) ^ n :=
    max_le (pow_nonneg (sub_nonneg.mpr (FiniteReportLaw.totalVariation_le_one p q)) n)
      (one_sub_mul_le_pow_one_sub_totalVariation p q n)
  exact (mul_le_mul_of_nonneg_left hpow (by positivity)).trans
    (lowerBound_cohortLaw_pow p q n τp τq estimator)

/-- The Hellinger affinity `ρ(p, q) = ∑ √(p q)`, equal to `1 - H²(p, q)`. -/
def hellingerAffinity (p q : FiniteReportLaw Report) : ℝ :=
  ∑ report, Real.sqrt (p.mass report * q.mass report)

/-- Cauchy-Schwarz on `√(p q) = √(min (p, q)) √(max (p, q))`: the squared affinity is at most twice
the overlap. -/
theorem hellingerAffinity_sq_le_two_mul_lawOverlap (p q : FiniteReportLaw Report) :
    hellingerAffinity p q ^ 2 ≤ 2 * lawOverlap p q := by
  have hmin : ∀ report, 0 ≤ min (p.mass report) (q.mass report) := fun report ↦
    le_min (p.mass_nonneg report) (q.mass_nonneg report)
  have hmax : ∀ report, 0 ≤ max (p.mass report) (q.mass report) := fun report ↦
    le_max_of_le_left (p.mass_nonneg report)
  have hsplit : ∀ report, Real.sqrt (p.mass report * q.mass report) =
      Real.sqrt (min (p.mass report) (q.mass report)) *
        Real.sqrt (max (p.mass report) (q.mass report)) := fun report ↦ by
    rw [← Real.sqrt_mul (hmin report), min_mul_max]
  have hminsq : ∀ report, Real.sqrt (min (p.mass report) (q.mass report)) ^ 2 =
      min (p.mass report) (q.mass report) := fun report ↦ Real.sq_sqrt (hmin report)
  have hmaxsq : ∀ report, Real.sqrt (max (p.mass report) (q.mass report)) ^ 2 =
      max (p.mass report) (q.mass report) := fun report ↦ Real.sq_sqrt (hmax report)
  have hschwarz := Finset.sum_mul_sq_le_sq_mul_sq univ
    (fun report ↦ Real.sqrt (min (p.mass report) (q.mass report)))
    (fun report ↦ Real.sqrt (max (p.mass report) (q.mass report)))
  simp only [hminsq, hmaxsq] at hschwarz
  have hsum_max : ∑ report, max (p.mass report) (q.mass report) = 2 - lawOverlap p q := by
    have hpoint : ∀ report, max (p.mass report) (q.mass report) =
        (p.mass report + q.mass report) - min (p.mass report) (q.mass report) := fun report ↦ by
      rw [← min_add_max (p.mass report) (q.mass report)]
      ring
    rw [Finset.sum_congr rfl fun report _ ↦ hpoint report, Finset.sum_sub_distrib,
      Finset.sum_add_distrib, p.mass_sum, q.mass_sum]
    unfold lawOverlap
    ring
  have haffinity : hellingerAffinity p q = ∑ report,
      Real.sqrt (min (p.mass report) (q.mass report)) *
        Real.sqrt (max (p.mass report) (q.mass report)) :=
    Finset.sum_congr rfl fun report _ ↦ hsplit report
  rw [haffinity]
  calc _ ≤ (∑ report, min (p.mass report) (q.mass report)) *
        ∑ report, max (p.mass report) (q.mass report) := hschwarz
    _ = lawOverlap p q * (2 - lawOverlap p q) := by rw [hsum_max]; rfl
    _ ≤ 2 * lawOverlap p q := by nlinarith [sq_nonneg (lawOverlap p q)]

/-- Over independent replicas the Hellinger affinity is the power of the one-record affinity. -/
theorem hellingerAffinity_cohortLaw (p q : FiniteReportLaw Report) (n : ℕ) :
    hellingerAffinity (cohortLaw p n) (cohortLaw q n) = hellingerAffinity p q ^ n := by
  have hsample : ∀ sample : Fin n → Report,
      Real.sqrt ((cohortLaw p n).mass sample * (cohortLaw q n).mass sample) =
        ∏ member, Real.sqrt (p.mass (sample member) * q.mass (sample member)) := by
    intro sample
    have hnonneg : 0 ≤ ∏ member, Real.sqrt (p.mass (sample member) * q.mass (sample member)) :=
      Finset.prod_nonneg fun member _ ↦ Real.sqrt_nonneg _
    rw [cohortLaw_mass, cohortLaw_mass, ← Finset.prod_mul_distrib, ← Real.sqrt_sq hnonneg,
      ← Finset.prod_pow]
    congr 1
    exact Finset.prod_congr rfl fun member _ ↦
      (Real.sq_sqrt (mul_nonneg (p.mass_nonneg _) (q.mass_nonneg _))).symm
  calc hellingerAffinity (cohortLaw p n) (cohortLaw q n)
      = ∑ sample : Fin n → Report,
          ∏ member, Real.sqrt (p.mass (sample member) * q.mass (sample member)) :=
        Finset.sum_congr rfl fun sample _ ↦ hsample sample
    _ = ∏ _member : Fin n, hellingerAffinity p q :=
        (Fintype.prod_sum fun (_ : Fin n) (report : Report) ↦
          Real.sqrt (p.mass report * q.mass report)).symm
    _ = hellingerAffinity p q ^ n := Fin.prod_const n _

/-- **The minimax lower bound from `n` source replicas, Hellinger form.** For every estimator,
one of the two histories forces an expected absolute error of at least
`(|τ_P - τ_Q| / 4) ρ(P, Q)^{2n}`. -/
theorem lowerBound_cohortLaw_hellingerAffinity (p q : FiniteReportLaw Report) (n : ℕ)
    (τp τq : ℝ) (estimator : (Fin n → Report) → ℝ) :
    |τp - τq| / 4 * hellingerAffinity p q ^ (2 * n) ≤
      max ((cohortLaw p n).expectation fun sample ↦ |estimator sample - τp|)
        ((cohortLaw q n).expectation fun sample ↦ |estimator sample - τq|) := by
  have hcohort := hellingerAffinity_sq_le_two_mul_lawOverlap (cohortLaw p n) (cohortLaw q n)
  rw [hellingerAffinity_cohortLaw, ← pow_mul, mul_comm n 2] at hcohort
  calc |τp - τq| / 4 * hellingerAffinity p q ^ (2 * n)
      ≤ |τp - τq| / 4 * (2 * lawOverlap (cohortLaw p n) (cohortLaw q n)) :=
        mul_le_mul_of_nonneg_left hcohort (by positivity)
    _ = |τp - τq| / 2 * lawOverlap (cohortLaw p n) (cohortLaw q n) := by ring
    _ ≤ _ := abs_sub_div_two_mul_lawOverlap_le _ _ τp τq estimator

end TwoPoint

section Chronology

/-- A source cohort record law: a report law `base` that does not depend on the history, mixed
with admixed records at fraction `ε`. -/
def mixtureReportLaw {Report : Type*} [Fintype Report] (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (base admixed : FiniteReportLaw Report) : FiniteReportLaw Report where
  mass := fun report ↦ (1 - ε) * base.mass report + ε * admixed.mass report
  mass_nonneg := fun report ↦ add_nonneg (mul_nonneg (by linarith) (base.mass_nonneg report))
    (mul_nonneg hε0 (admixed.mass_nonneg report))
  mass_sum := by
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, base.mass_sum, admixed.mass_sum]
    ring

/-- Mixing with a common base law scales total variation by the admixed fraction.
Assumes: `0 ≤ ε ≤ 1`. -/
theorem totalVariation_mixtureReportLaw {Report : Type*} [Fintype Report] (ε : ℝ)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (base admixed admixed' : FiniteReportLaw Report) :
    (mixtureReportLaw ε hε0 hε1 base admixed).totalVariation
        (mixtureReportLaw ε hε0 hε1 base admixed') = ε * admixed.totalVariation admixed' := by
  simp only [FiniteReportLaw.totalVariation, Finset.mul_sum]
  refine Finset.sum_congr rfl fun report _ ↦ ?_
  change max ((1 - ε) * base.mass report + ε * admixed.mass report -
      ((1 - ε) * base.mass report + ε * admixed'.mass report)) 0 = _
  rw [show (1 - ε) * base.mass report + ε * admixed.mass report -
      ((1 - ε) * base.mass report + ε * admixed'.mass report) =
        ε * (admixed.mass report - admixed'.mass report) by ring,
    mul_max_of_nonneg _ _ hε0, mul_zero]

/-- Two chronology laws with one donor fraction differ in total variation by
`2 p(1 - p) |C - C'|`. Assumes: `0 ≤ p ≤ 1` and both couplings in `[0, 1]`. -/
theorem totalVariation_chronologyLaw (p C C' : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hC0 : 0 ≤ C)
    (hC1 : C ≤ 1) (hC0' : 0 ≤ C') (hC1' : C' ≤ 1) :
    (ChronologyReportLaw.chronologyLaw p C hp0 hp1 hC0 hC1).totalVariation
        (ChronologyReportLaw.chronologyLaw p C' hp0 hp1 hC0' hC1') =
      2 * (p * (1 - p)) * |C - C'| := by
  have hprod : 0 ≤ p * (1 - p) := mul_nonneg hp0 (by linarith)
  have hplus : |p * (1 - p) * (C - C')| = p * (1 - p) * |C - C'| := by
    rw [abs_mul, abs_of_nonneg hprod]
  have hminus : |-(p * (1 - p) * (C - C'))| = p * (1 - p) * |C - C'| := by
    rw [abs_neg, hplus]
  have hcell : ∀ cell : Bool × Bool,
      |ChronologyReportLaw.chronologyMass p C cell - ChronologyReportLaw.chronologyMass p C' cell| =
        p * (1 - p) * |C - C'| := by
    rintro ⟨_ | _, _ | _⟩ <;>
      simp only [ChronologyReportLaw.chronologyMass_false_false,
        ChronologyReportLaw.chronologyMass_false_true,
        ChronologyReportLaw.chronologyMass_true_false,
        ChronologyReportLaw.chronologyMass_true_true]
    · rw [← hplus]
      congr 1
      ring
    · rw [← hminus]
      congr 1
      ring
    · rw [← hminus]
      congr 1
      ring
    · rw [← hplus]
      congr 1
      ring
  rw [FiniteReportLaw.totalVariation_eq_half_sum_abs]
  change (∑ cell, |ChronologyReportLaw.chronologyMass p C cell -
      ChronologyReportLaw.chronologyMass p C' cell|) / 2 = _
  rw [Finset.sum_congr rfl fun cell _ ↦ hcell cell, Finset.sum_const, Finset.card_univ,
    Fintype.card_prod, Fintype.card_bool, nsmul_eq_mul]
  push_cast
  ring

/-- The report law of one admixed record under the three-block chronology with migration total
`M` and recombination exposure `b` after the migration: the chronology law at donor fraction
`1 - e^{-M}` and coupling `e^{-b}`. Assumes: `0 ≤ b` and `0 ≤ M`. -/
def threeBlockRecordLaw (bexp mtot : ℝ) (hb : 0 ≤ bexp) (hm : 0 ≤ mtot) :
    FiniteReportLaw (Bool × Bool) :=
  ChronologyReportLaw.chronologyLaw (1 - Real.exp (-mtot)) (Real.exp (-bexp))
    (sub_nonneg.mpr ((Real.exp_le_exp.mpr (by linarith)).trans_eq Real.exp_zero))
    (sub_le_self _ (Real.exp_pos _).le) (Real.exp_pos _).le
    ((Real.exp_le_exp.mpr (by linarith)).trans_eq Real.exp_zero)

/-- The record law is the chronology law of the state the three-block history reaches: its donor
fraction and its coupling. Assumes: `0 ≤ b` and `0 < M`. -/
theorem threeBlockRecordLaw_mass (bexp mtot rtot : ℝ) (hb : 0 ≤ bexp) (hm : 0 < mtot)
    (report : Bool × Bool) :
    (threeBlockRecordLaw bexp mtot hb hm.le).mass report =
      ChronologyReportLaw.chronologyMass
        (AdmixtureChronologyLaw.runEvents
          (AttainableChronologyCurve.threeBlockHistory bexp mtot rtot) (0, 0)).1
        (AttainableChronologyCurve.couplingOfState (AdmixtureChronologyLaw.runEvents
          (AttainableChronologyCurve.threeBlockHistory bexp mtot rtot) (0, 0))) report :=
  congrArg₂ (fun donor coupling ↦ ChronologyReportLaw.chronologyMass donor coupling report)
    (congrArg Prod.fst (AttainableChronologyCurve.runEvents_threeBlockHistory bexp mtot rtot)).symm
    (AttainableChronologyCurve.couplingOfState_threeBlockHistory bexp mtot rtot hm).symm

/-- The target squared correlation of an admixed record is the squared coupling `e^{-2b}`.
Assumes: `0 ≤ b` and `0 < M`. -/
theorem squaredCorrelation_threeBlockRecordLaw (bexp mtot : ℝ) (hb : 0 ≤ bexp) (hm : 0 < mtot) :
    (threeBlockRecordLaw bexp mtot hb hm.le).squaredCorrelation ChronologyReportLaw.scoreOf
        ChronologyReportLaw.outcomeOf = some (Real.exp (-bexp) ^ 2) :=
  (ChronologyReportLaw.metric_values_chronologyLaw _ _ _ _ _ _
    (sub_pos.mpr ((Real.exp_lt_exp.mpr (by linarith)).trans_eq Real.exp_zero))
    (sub_lt_self _ (Real.exp_pos _))).1

/-- The source cohort under the three-block chronology with late exposure `b`: the base law mixed
with admixed records at fraction `ε`. Assumes: `0 ≤ ε ≤ 1`, `0 ≤ b` and `0 ≤ M`. -/
def sourceCohortLaw (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (base : FiniteReportLaw (Bool × Bool))
    (bexp mtot : ℝ) (hb : 0 ≤ bexp) (hm : 0 ≤ mtot) : FiniteReportLaw (Bool × Bool) :=
  mixtureReportLaw ε hε0 hε1 base (threeBlockRecordLaw bexp mtot hb hm)

/-- Two chronologies with the same totals give source cohorts within total variation
`ε · 2p(1 - p) · |e^{-b₀} - e^{-b₁}|`, `p = 1 - e^{-M}`. Assumes: `0 ≤ ε ≤ 1`, `0 ≤ b₀`,
`0 ≤ b₁` and `0 ≤ M`. -/
theorem totalVariation_sourceCohortLaw (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (base : FiniteReportLaw (Bool × Bool)) (b₀ b₁ mtot : ℝ) (hb₀ : 0 ≤ b₀) (hb₁ : 0 ≤ b₁)
    (hm : 0 ≤ mtot) :
    (sourceCohortLaw ε hε0 hε1 base b₀ mtot hb₀ hm).totalVariation
        (sourceCohortLaw ε hε0 hε1 base b₁ mtot hb₁ hm) =
      ε * (2 * ((1 - Real.exp (-mtot)) * (1 - (1 - Real.exp (-mtot)))) *
        |Real.exp (-b₀) - Real.exp (-b₁)|) := by
  simp only [sourceCohortLaw, threeBlockRecordLaw]
  rw [totalVariation_mixtureReportLaw, totalVariation_chronologyLaw]

/-- **What a source cohort cannot tell you about the target squared correlation.** Every
estimator of the target squared correlation from `n` source replicas has, under one of two
three-block chronologies with the same totals, an expected absolute error of at least
`(|e^{-2b₀} - e^{-2b₁}| / 2) max (0, 1 - n ε 2p(1 - p) |e^{-b₀} - e^{-b₁}|)`.
Assumes: `0 ≤ ε ≤ 1`, `0 ≤ b₀`, `0 ≤ b₁` and `0 ≤ M`. -/
theorem sourceCohort_lowerBound (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (base : FiniteReportLaw (Bool × Bool)) (b₀ b₁ mtot : ℝ) (hb₀ : 0 ≤ b₀) (hb₁ : 0 ≤ b₁)
    (hm : 0 ≤ mtot) (n : ℕ) (estimator : (Fin n → Bool × Bool) → ℝ) :
    |Real.exp (-b₀) ^ 2 - Real.exp (-b₁) ^ 2| / 2 *
        max 0 (1 - n * (ε * (2 * ((1 - Real.exp (-mtot)) * (1 - (1 - Real.exp (-mtot)))) *
          |Real.exp (-b₀) - Real.exp (-b₁)|))) ≤
      max ((cohortLaw (sourceCohortLaw ε hε0 hε1 base b₀ mtot hb₀ hm) n).expectation
          fun sample ↦ |estimator sample - Real.exp (-b₀) ^ 2|)
        ((cohortLaw (sourceCohortLaw ε hε0 hε1 base b₁ mtot hb₁ hm) n).expectation
          fun sample ↦ |estimator sample - Real.exp (-b₁) ^ 2|) := by
  rw [← totalVariation_sourceCohortLaw ε hε0 hε1 base b₀ b₁ mtot hb₀ hb₁ hm]
  exact lowerBound_cohortLaw_totalVariation _ _ n _ _ estimator

/-- **NOTE1's worked example, `M = R = log 2`.** The migration-first chronology (`b = log 2`,
target squared correlation `1/4`) and the recombination-first chronology (`b = 0`, target squared
correlation `1`) force every estimator from `n` source replicas to an expected absolute error of
at least `(3/8) max (0, 1 - n ε / 4)` under one of them. Assumes: `0 ≤ ε ≤ 1`. -/
theorem logTwo_sourceCohort_lowerBound (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (base : FiniteReportLaw (Bool × Bool)) (n : ℕ) (estimator : (Fin n → Bool × Bool) → ℝ) :
    3 / 8 * max 0 (1 - n * (ε / 4)) ≤
      max ((cohortLaw (sourceCohortLaw ε hε0 hε1 base (Real.log 2) (Real.log 2)
            (Real.log_nonneg one_le_two) (Real.log_nonneg one_le_two)) n).expectation
          fun sample ↦ |estimator sample - 1 / 4|)
        ((cohortLaw (sourceCohortLaw ε hε0 hε1 base 0 (Real.log 2) le_rfl
            (Real.log_nonneg one_le_two)) n).expectation
          fun sample ↦ |estimator sample - 1|) := by
  refine le_trans (le_of_eq ?_) (lowerBound_cohortLaw_totalVariation _ _ n (1 / 4) 1 estimator)
  rw [totalVariation_sourceCohortLaw, AttainableChronologyCurve.exp_neg_log_two, neg_zero,
    Real.exp_zero, abs_of_neg (by norm_num : (1 / 4 : ℝ) - 1 < 0),
    abs_of_neg (by norm_num : (1 / 2 : ℝ) - 1 < 0)]
  congr 1
  · norm_num
  · congr 1
    ring

end Chronology

end

end Descent.Portability.PortabilityMinimaxLowerBound
