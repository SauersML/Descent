/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.ExactMetricEvaluation
import Descent.Portability.FiniteIndependentMoments
import Descent.Portability.FiniteNumericalCertificate
import Descent.Portability.BellmanReportBounds
import Mathlib.Data.Real.Sqrt

assert_below Descent.Decision Descent.Program

/-!
# A replica bound for every Lipschitz functional of a population law

NOTE2 (31) says that a functional of a population law which is Lipschitz for the distance
between category shares can be read off a finite block of conditionally independent replicas,
with an error that shrinks like the square root of the replica count and does not depend on
the functional beyond its Lipschitz constant. This module proves that bound exactly.

The replica block is the independent product law of the corpus
(`HWEInteractionLaw.independentLaw`), and the empirical law of a block is the share of
replicas landing in each category, written with the corpus singleton indicator
`FiniteReportLaw.singletonMetric`. Three exact steps carry the proof. The mean squared
deviation of one category share is the binomial variance divided by the replica count, which
is `FiniteIndependentMoments.independent_sum_second` applied to the centered indicators. The
mean absolute deviation is at most the root of that, which is the nonnegativity of the corpus
variance rather than a general Jensen inequality. The sum of those roots over the categories
is at most the root of the category count times their sum, which is the discrete
Cauchy-Schwarz inequality, and the sum itself is at most the reciprocal category count
subtracted from one, again by Cauchy-Schwarz applied to the population vector itself.

The Lipschitz class is stated as a predicate on a functional together with its constant, and
a coordinate readout is exhibited as an actual member of it, so the hypothesis is inhabited
rather than merely assumed. The final statement mixes over a shared study context carrying
its own finite law, which is the form (31) takes once the population law is itself random.

Not formalized here: the bound is stated for a finite category alphabet and a replica block
indexed by a finite ordinal, not for general Polish spaces; and the Lipschitz constant is a
supplied datum rather than an infimum over admissible constants.

## Empirical status

None. The bodies here are algebra: the replica block is a constructed product of a supplied
population law, and every bound is a consequence of the two Cauchy-Schwarz inequalities and
the exact second moment, so no measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.EmpiricalLawLipschitzBound

open scoped BigOperators

noncomputable section

variable {Category : Type*} [Fintype Category]

/-- The law of a block of conditionally independent replicas drawn from one population law. -/
def replicaLaw (count : ℕ) (q : FiniteReportLaw Category) :
    FiniteReportLaw (Fin count → Category) :=
  HWEInteractionLaw.independentLaw fun _ ↦ q

/-- The empirical law of a finite replica block: the share of replicas in each category. -/
def empiricalMass {count : ℕ} (draw : Fin count → Category) (category : Category) : ℝ :=
  (∑ replica, FiniteReportLaw.singletonMetric category (draw replica)) / count

/-- The centered and scaled indicator contributed by one replica: the deviation of the
empirical share from the population share is exactly the sum of these. -/
def centeredIndicator (q : FiniteReportLaw Category) (category : Category) (count : ℕ)
    (draw : Category) : ℝ :=
  (FiniteReportLaw.singletonMetric category draw - q.mass category) / count

/-- The expectation of any affine function of a category indicator, in closed form. -/
theorem expectation_indicator_affine (q : FiniteReportLaw Category) (category : Category)
    (scale shift : ℝ) :
    q.expectation
        (fun draw ↦ scale * FiniteReportLaw.singletonMetric category draw + shift) =
      scale * q.mass category + shift := by
  have hfirst : (∑ draw, q.mass draw *
      (scale * FiniteReportLaw.singletonMetric category draw)) =
      scale * q.mass category := by
    rw [← FiniteReportLaw.expectation_singletonMetric q category, FiniteReportLaw.expectation,
      Finset.mul_sum]
    exact Finset.sum_congr rfl fun draw _ ↦ by ring
  simp only [FiniteReportLaw.expectation, mul_add, Finset.sum_add_distrib, hfirst,
    ← Finset.sum_mul, q.mass_sum, one_mul]

omit [Fintype Category] in
/-- A category indicator is idempotent: it takes only the values zero and one. -/
theorem singletonMetric_sq (category draw : Category) :
    FiniteReportLaw.singletonMetric category draw ^ 2 =
      FiniteReportLaw.singletonMetric category draw := by
  rcases eq_or_ne draw category with h | h
  · simp [FiniteReportLaw.singletonMetric, h]
  · simp [FiniteReportLaw.singletonMetric, h]

/-- The centered indicator has mean zero, which is what makes the cross terms of the replica
sum vanish. -/
theorem expectation_centeredIndicator (q : FiniteReportLaw Category) (category : Category)
    (count : ℕ) : q.expectation (centeredIndicator q category count) = 0 := by
  have hfun : centeredIndicator q category count =
      fun draw ↦ (1 / (count:ℝ)) * FiniteReportLaw.singletonMetric category draw +
        -(q.mass category) / count := by
    funext draw
    rw [centeredIndicator]
    ring
  rw [hfun, expectation_indicator_affine]
  ring

/-- The second moment of one centered indicator is the binomial variance scaled by the
square of the replica count. -/
theorem expectation_sq_centeredIndicator (q : FiniteReportLaw Category)
    (category : Category) (count : ℕ) :
    q.expectation (fun draw ↦ centeredIndicator q category count draw ^ 2) =
      q.mass category * (1 - q.mass category) / (count:ℝ) ^ 2 := by
  have hfun : (fun draw ↦ centeredIndicator q category count draw ^ 2) =
      fun draw ↦ ((1 - 2 * q.mass category) / (count:ℝ) ^ 2) *
        FiniteReportLaw.singletonMetric category draw +
        q.mass category ^ 2 / (count:ℝ) ^ 2 := by
    funext draw
    rw [centeredIndicator, div_pow]
    linear_combination singletonMetric_sq category draw / (count:ℝ) ^ 2
  rw [hfun, expectation_indicator_affine]
  ring

/-- The empirical deviation of one category share is exactly the sum of the centered
indicators of the replicas. -/
theorem empiricalMass_sub_eq_sum {count : ℕ} (hcount : 0 < count)
    (q : FiniteReportLaw Category) (category : Category) (draw : Fin count → Category) :
    empiricalMass draw category - q.mass category =
      ∑ replica, centeredIndicator q category count (draw replica) := by
  have hne : (count : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hcount.ne'
  simp only [centeredIndicator, empiricalMass, ← Finset.sum_div, Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

/-- NOTE2 (31), first step: the mean squared deviation of one empirical category share is
the exact binomial variance divided by the replica count. -/
theorem expectation_sq_deviation (count : ℕ) (hcount : 0 < count)
    (q : FiniteReportLaw Category) (category : Category) :
    (replicaLaw count q).expectation
        (fun draw ↦ (empiricalMass draw category - q.mass category) ^ 2) =
      q.mass category * (1 - q.mass category) / count := by
  have hne : (count : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hcount.ne'
  have hfun : (fun draw : Fin count → Category ↦
      (empiricalMass draw category - q.mass category) ^ 2) =
      fun draw ↦ (∑ replica, centeredIndicator q category count (draw replica)) ^ 2 := by
    funext draw
    rw [empiricalMass_sub_eq_sum hcount q category draw]
  have hmain : (replicaLaw count q).expectation
      (fun draw ↦ (∑ replica, centeredIndicator q category count (draw replica)) ^ 2) =
      ∑ _replica : Fin count,
        q.expectation (fun a ↦ centeredIndicator q category count a ^ 2) :=
    FiniteIndependentMoments.independent_sum_second (fun _ ↦ q)
      (fun _ ↦ centeredIndicator q category count)
      (fun _ ↦ expectation_centeredIndicator q category count)
  rw [hfun, hmain, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    expectation_sq_centeredIndicator]
  field_simp

/-- NOTE2 (31), second step: the mean absolute deviation of one category share is at most
its binomial standard error. This is the nonnegativity of the corpus variance applied to the
absolute deviation, not a separate convexity argument. -/
theorem expectation_abs_deviation_le (count : ℕ) (hcount : 0 < count)
    (q : FiniteReportLaw Category) (category : Category) :
    (replicaLaw count q).expectation
        (fun draw ↦ |empiricalMass draw category - q.mass category|) ≤
      Real.sqrt (q.mass category * (1 - q.mass category) / count) := by
  have hnn : 0 ≤ (replicaLaw count q).expectation
      (fun draw ↦ |empiricalMass draw category - q.mass category|) :=
    Finset.sum_nonneg fun draw _ ↦
      mul_nonneg ((replicaLaw count q).mass_nonneg draw) (abs_nonneg _)
  have hsq : (replicaLaw count q).expectation
      (fun draw ↦ |empiricalMass draw category - q.mass category| ^ 2) =
      q.mass category * (1 - q.mass category) / count := by
    rw [show (fun draw : Fin count → Category ↦
        |empiricalMass draw category - q.mass category| ^ 2) =
        (fun draw ↦ (empiricalMass draw category - q.mass category) ^ 2) from
      funext fun draw ↦ sq_abs _]
    exact expectation_sq_deviation count hcount q category
  have hvar : 0 ≤ (replicaLaw count q).expectation
      (fun draw ↦ |empiricalMass draw category - q.mass category| ^ 2) -
      ((replicaLaw count q).expectation
        (fun draw ↦ |empiricalMass draw category - q.mass category|)) ^ 2 := by
    have h := FiniteReportLaw.variance_nonneg (replicaLaw count q)
      (fun draw ↦ |empiricalMass draw category - q.mass category|)
    rwa [FiniteReportLaw.variance_eq_rawMoments] at h
  calc (replicaLaw count q).expectation
        (fun draw ↦ |empiricalMass draw category - q.mass category|)
      = Real.sqrt (((replicaLaw count q).expectation
          (fun draw ↦ |empiricalMass draw category - q.mass category|)) ^ 2) :=
        (Real.sqrt_sq hnn).symm
    _ ≤ Real.sqrt (q.mass category * (1 - q.mass category) / count) :=
        Real.sqrt_le_sqrt (by linarith)

/-- NOTE2 (31): the expected total deviation between the empirical law of a replica block
and the population law it was drawn from, in the exact closed form of the note. -/
theorem expectation_deviation_sum_le (count : ℕ) (hcount : 0 < count) (witness : Category)
    (q : FiniteReportLaw Category) :
    (replicaLaw count q).expectation
        (fun draw ↦ ∑ category, |empiricalMass draw category - q.mass category|) ≤
      Real.sqrt (((Fintype.card Category : ℝ) - 1) / count) := by
  have hcountpos : (0:ℝ) < count := by exact_mod_cast hcount
  have hcard : 0 < Fintype.card Category := Fintype.card_pos_iff.mpr ⟨witness⟩
  have hcardpos : (0:ℝ) < (Fintype.card Category : ℝ) := by exact_mod_cast hcard
  have hvnn : ∀ category : Category,
      0 ≤ q.mass category * (1 - q.mass category) / count := by
    intro category
    have h1 : q.mass category ≤ 1 := by
      rw [← q.mass_sum]
      exact Finset.single_le_sum (f := q.mass) (fun x _ ↦ q.mass_nonneg x) (Finset.mem_univ _)
    exact div_nonneg (mul_nonneg (q.mass_nonneg category) (by linarith)) hcountpos.le
  have hsplit : (replicaLaw count q).expectation
      (fun draw ↦ ∑ category, |empiricalMass draw category - q.mass category|) =
      ∑ category, (replicaLaw count q).expectation
        (fun draw ↦ |empiricalMass draw category - q.mass category|) :=
    FiniteIndependentMoments.expectation_sum (replicaLaw count q)
      (fun category draw ↦ |empiricalMass draw category - q.mass category|)
  have hbound : ∑ category, (replicaLaw count q).expectation
      (fun draw ↦ |empiricalMass draw category - q.mass category|) ≤
      ∑ category, Real.sqrt (q.mass category * (1 - q.mass category) / count) :=
    Finset.sum_le_sum fun category _ ↦
      expectation_abs_deviation_le count hcount q category
  have hlower : (1:ℝ) ≤ (Fintype.card Category : ℝ) * ∑ category, q.mass category ^ 2 := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ : Category ↦ (1:ℝ)) q.mass
    simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      mul_one] at h
    rw [q.mass_sum] at h
    simpa using h
  have hsumv : ∑ category, q.mass category * (1 - q.mass category) / count =
      (1 - ∑ category, q.mass category ^ 2) / count := by
    rw [← Finset.sum_div]
    congr 1
    have hterm : ∀ category : Category,
        q.mass category * (1 - q.mass category) =
          q.mass category - q.mass category ^ 2 := fun category ↦ by ring
    simp only [hterm, Finset.sum_sub_distrib, q.mass_sum]
  have hcs : (∑ category, Real.sqrt (q.mass category * (1 - q.mass category) / count)) ^ 2 ≤
      (Fintype.card Category : ℝ) *
        ∑ category, q.mass category * (1 - q.mass category) / count := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ : Category ↦ (1:ℝ))
      (fun category ↦ Real.sqrt (q.mass category * (1 - q.mass category) / count))
    simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      mul_one] at h
    have hsqrt : ∀ category : Category,
        Real.sqrt (q.mass category * (1 - q.mass category) / count) ^ 2 =
          q.mass category * (1 - q.mass category) / count :=
      fun category ↦ Real.sq_sqrt (hvnn category)
    simpa only [hsqrt] using h
  have hkey : (Fintype.card Category : ℝ) * (1 - ∑ category, q.mass category ^ 2) ≤
      (Fintype.card Category : ℝ) - 1 := by nlinarith [hlower]
  have hfinal : (Fintype.card Category : ℝ) *
      (∑ category, q.mass category * (1 - q.mass category) / count) ≤
      ((Fintype.card Category : ℝ) - 1) / count := by
    have hleft : (Fintype.card Category : ℝ) *
        ((1 - ∑ category, q.mass category ^ 2) / (count:ℝ)) =
        ((Fintype.card Category : ℝ) * (1 - ∑ category, q.mass category ^ 2)) *
          (1 / (count:ℝ)) := by ring
    have hright : ((Fintype.card Category : ℝ) - 1) / (count:ℝ) =
        ((Fintype.card Category : ℝ) - 1) * (1 / (count:ℝ)) := by ring
    rw [hsumv, hleft, hright]
    exact mul_le_mul_of_nonneg_right hkey (by positivity)
  have hroot : ∑ category, Real.sqrt (q.mass category * (1 - q.mass category) / count) ≤
      Real.sqrt (((Fintype.card Category : ℝ) - 1) / count) := by
    have hnn : 0 ≤ ∑ category, Real.sqrt (q.mass category * (1 - q.mass category) / count) :=
      Finset.sum_nonneg fun category _ ↦ Real.sqrt_nonneg _
    calc ∑ category, Real.sqrt (q.mass category * (1 - q.mass category) / count)
        = Real.sqrt ((∑ category,
            Real.sqrt (q.mass category * (1 - q.mass category) / count)) ^ 2) :=
          (Real.sqrt_sq hnn).symm
      _ ≤ Real.sqrt (((Fintype.card Category : ℝ) - 1) / count) :=
          Real.sqrt_le_sqrt (le_trans hcs hfinal)
  rw [hsplit]
  exact le_trans hbound hroot

/-- The hypothesis class of NOTE2 section 7.1: a report functional of a population vector
that is Lipschitz for the total deviation between vectors, together with its constant. -/
def LipschitzInL1 (functional : (Category → ℝ) → ℝ) (constant : ℝ) : Prop :=
  ∀ first second : Category → ℝ,
    |functional first - functional second| ≤
      constant * ∑ category, |first category - second category|

/-- Reading off one category share is one-Lipschitz, so the hypothesis class is inhabited by
an explicit functional rather than merely assumed nonempty. -/
theorem lipschitzInL1_coordinate (category : Category) :
    LipschitzInL1 (fun law ↦ law category) 1 := by
  intro first second
  rw [one_mul]
  exact Finset.single_le_sum (f := fun c ↦ |first c - second c|)
    (fun c _ ↦ abs_nonneg _) (Finset.mem_univ category)

/-- The absolute expectation of a report statistic is at most the expectation of its
absolute value. -/
theorem abs_expectation_le_expectation_abs {Ω : Type*} [Fintype Ω] (p : FiniteReportLaw Ω)
    (statistic : Ω → ℝ) :
    |p.expectation statistic| ≤ p.expectation fun state ↦ |statistic state| := by
  rw [FiniteReportLaw.expectation, FiniteReportLaw.expectation]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun state _ ↦ ?_)
  rw [abs_mul, abs_of_nonneg (p.mass_nonneg state)]

/-- NOTE2 (31): every functional that is Lipschitz for the total deviation is read off a
replica block with an error controlled by the Lipschitz constant and the replica count
alone. The bound is uniform over population laws. -/
theorem abs_expectation_functional_sub_le (count : ℕ) (hcount : 0 < count)
    (witness : Category) (q : FiniteReportLaw Category)
    (functional : (Category → ℝ) → ℝ) (constant : ℝ) (hconstant : 0 ≤ constant)
    (hlipschitz : LipschitzInL1 functional constant) :
    |(replicaLaw count q).expectation (fun draw ↦ functional (empiricalMass draw)) -
        functional q.mass| ≤
      constant * Real.sqrt (((Fintype.card Category : ℝ) - 1) / count) := by
  have hdiff : (replicaLaw count q).expectation
      (fun draw ↦ functional (empiricalMass draw)) - functional q.mass =
      (replicaLaw count q).expectation
        (fun draw ↦ functional (empiricalMass draw) - functional q.mass) := by
    rw [FiniteNumericalCertificate.expectation_difference,
      FiniteIndependentMoments.expectation_const]
  have hmono : (replicaLaw count q).expectation
      (fun draw ↦ |functional (empiricalMass draw) - functional q.mass|) ≤
      (replicaLaw count q).expectation
        (fun draw ↦ constant *
          ∑ category, |empiricalMass draw category - q.mass category|) :=
    BellmanReportBounds.expectation_mono _ _ _ fun draw ↦ hlipschitz _ _
  have hscale : (replicaLaw count q).expectation
      (fun draw ↦ constant *
        ∑ category, |empiricalMass draw category - q.mass category|) =
      constant * (replicaLaw count q).expectation
        (fun draw ↦ ∑ category, |empiricalMass draw category - q.mass category|) := by
    simp only [FiniteReportLaw.expectation, Finset.mul_sum]
    exact Finset.sum_congr rfl fun draw _ ↦ by ring
  rw [hdiff]
  refine le_trans (abs_expectation_le_expectation_abs _ _) (le_trans hmono ?_)
  rw [hscale]
  exact mul_le_mul_of_nonneg_left
    (expectation_deviation_sum_le count hcount witness q) hconstant

/-- NOTE2 (31) with a random population law: mixing the bound over a finite law of shared
study contexts leaves the same constant, because the bound does not depend on the population
law it is applied to. -/
theorem abs_mixed_expectation_functional_sub_le {Context : Type*} [Fintype Context]
    (count : ℕ) (hcount : 0 < count) (witness : Category)
    (mixing : FiniteReportLaw Context) (population : Context → FiniteReportLaw Category)
    (functional : (Category → ℝ) → ℝ) (constant : ℝ) (hconstant : 0 ≤ constant)
    (hlipschitz : LipschitzInL1 functional constant) :
    |mixing.expectation (fun context ↦
        (replicaLaw count (population context)).expectation
          (fun draw ↦ functional (empiricalMass draw))) -
      mixing.expectation (fun context ↦ functional (population context).mass)| ≤
      constant * Real.sqrt (((Fintype.card Category : ℝ) - 1) / count) := by
  have hdiff : mixing.expectation (fun context ↦
        (replicaLaw count (population context)).expectation
          (fun draw ↦ functional (empiricalMass draw))) -
      mixing.expectation (fun context ↦ functional (population context).mass) =
      mixing.expectation (fun context ↦
        (replicaLaw count (population context)).expectation
          (fun draw ↦ functional (empiricalMass draw)) -
        functional (population context).mass) :=
    (FiniteNumericalCertificate.expectation_difference mixing _ _).symm
  have hmono : mixing.expectation (fun context ↦
      |(replicaLaw count (population context)).expectation
        (fun draw ↦ functional (empiricalMass draw)) -
        functional (population context).mass|) ≤
      mixing.expectation (fun _ ↦
        constant * Real.sqrt (((Fintype.card Category : ℝ) - 1) / count)) :=
    BellmanReportBounds.expectation_mono _ _ _ fun context ↦
      abs_expectation_functional_sub_le count hcount witness (population context)
        functional constant hconstant hlipschitz
  rw [hdiff]
  refine le_trans (abs_expectation_le_expectation_abs _ _) (le_trans hmono ?_)
  rw [FiniteIndependentMoments.expectation_const]

end

end Descent.Portability.EmpiricalLawLipschitzBound
