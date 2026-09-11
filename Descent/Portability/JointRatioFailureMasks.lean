/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.UniversalMetricIdentification

assert_below Descent.Decision Descent.Program

/-!
# A finite family of bounded ratio metrics shares one domain, and its failure masks expand

Several nonlinear metrics computed on the same cohort are defined on different events, so
their joint law is not determined by their separate laws. NOTE 2 section 6.1 puts the whole
family over one common denominator and then accounts for the definedness pattern by
inclusion and exclusion.

`jointDenominator` is the product of the denominators and `jointNumerator` carries one
numerator against the others, which is NOTE 2 equation (24): `jointNumerator_ratio` shows the
quotient is the original metric wherever every denominator is nonzero, and
`jointNumerator_le_jointDenominator` with the two positivity statements shows the recast pair
is again a bounded ratio, so the replica machinery applies to it unchanged.
`multiIndexNumerator` and `multiIndexDenominator` do the same for an arbitrary multi-index,
which is NOTE 2 equation (25): `multiIndexNumerator_ratio` shows the quotient is the product
of the metrics raised to the multi-index, again a bounded ratio. Joint moments of the family
are therefore readouts of one common domain.

`maskStatistic` is the exact definedness mask of a chosen subfamily, a product over the
chosen metrics of their definedness indicators against a product over the rest of the
complementary indicators. `prod_mask_expansion` is the algebraic heart of NOTE 2 equation
(26): for arbitrary reals, the mask equals the alternating sum over subsets of the complement
of the product over the chosen metrics together with that subset. It is pure ring algebra,
with no probability and no idempotence of indicators used. `expectation_mask_expansion`
transports it through a finite report law, which is the inclusion and exclusion formula for
the probability that exactly the chosen metrics are defined.

Scope: everything here is stated for a finite family indexed by a finite type with decidable
equality, on an arbitrary point type for the algebra and a finite report law for the
probability statement. The exponent bookkeeping of a multi-index uses the NOTE's convention
that a zero entry still contributes one power of its denominator. The portability query
algebra of NOTE 2 equation (27), and the distinction among the four queries listed there, is
formalized in `PortabilityRatioQueries`.

## Empirical status

None. The bodies here are algebra: products and quotients of two given families of real
functionals, and one ring identity between a product and an alternating sum, so no
measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.JointRatioFailureMasks

variable {Metric : Type*} [Fintype Metric] [DecidableEq Metric]
variable {Point : Type*}

/-- **NOTE 2 equation (24).** The common denominator of a finite family of ratio metrics. -/
noncomputable def jointDenominator (den : Metric → Point → ℝ) : Point → ℝ :=
  fun point ↦ ∏ index, den index point

/-- **NOTE 2 equation (24).** The numerator of one member of the family, recast against the
common denominator by carrying the denominators of all the other members. -/
noncomputable def jointNumerator (num den : Metric → Point → ℝ) (chosen : Metric) :
    Point → ℝ :=
  fun point ↦ num chosen point * ∏ index ∈ Finset.univ.erase chosen, den index point

/-- **NOTE 2 equation (24).** Wherever every denominator is nonzero, the recast pair has the
same quotient as the original metric. -/
theorem jointNumerator_ratio (num den : Metric → Point → ℝ) (chosen : Metric) (point : Point)
    (hden : ∀ index, den index point ≠ 0) :
    jointNumerator num den chosen point / jointDenominator den point =
      num chosen point / den chosen point := by
  have hrest : (∏ index ∈ Finset.univ.erase chosen, den index point) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun index _ ↦ hden index
  unfold jointNumerator jointDenominator
  rw [← Finset.mul_prod_erase Finset.univ (fun index ↦ den index point)
      (Finset.mem_univ chosen),
    div_eq_div_iff (mul_ne_zero (hden chosen) hrest) (hden chosen)]
  ring

/-- The common denominator of nonnegative denominators is nonnegative. -/
theorem jointDenominator_nonneg (den : Metric → Point → ℝ)
    (hden : ∀ index point, 0 ≤ den index point) (point : Point) :
    0 ≤ jointDenominator den point :=
  Finset.prod_nonneg fun index _ ↦ hden index point

/-- The common denominator of denominators below one is itself below one. -/
theorem jointDenominator_le_one (den : Metric → Point → ℝ)
    (hden : ∀ index point, 0 ≤ den index point)
    (hone : ∀ index point, den index point ≤ 1) (point : Point) :
    jointDenominator den point ≤ 1 :=
  Finset.prod_le_one (fun index _ ↦ hden index point) fun index _ ↦ hone index point

/-- The recast numerator of a nonnegative family is nonnegative. -/
theorem jointNumerator_nonneg (num den : Metric → Point → ℝ)
    (hnum : ∀ index point, 0 ≤ num index point)
    (hle : ∀ index point, num index point ≤ den index point) (chosen : Metric)
    (point : Point) : 0 ≤ jointNumerator num den chosen point :=
  mul_nonneg (hnum chosen point)
    (Finset.prod_nonneg fun index _ ↦ le_trans (hnum index point) (hle index point))

/-- **NOTE 2 equation (24).** The recast pair is again a dominated pair, so the family shares
one bounded ratio structure over the common domain. -/
theorem jointNumerator_le_jointDenominator (num den : Metric → Point → ℝ)
    (hnum : ∀ index point, 0 ≤ num index point)
    (hle : ∀ index point, num index point ≤ den index point) (chosen : Metric)
    (point : Point) :
    jointNumerator num den chosen point ≤ jointDenominator den point := by
  unfold jointNumerator jointDenominator
  rw [← Finset.mul_prod_erase Finset.univ (fun index ↦ den index point)
    (Finset.mem_univ chosen)]
  exact mul_le_mul_of_nonneg_right (hle chosen point)
    (Finset.prod_nonneg fun index _ ↦ le_trans (hnum index point) (hle index point))

/-- **NOTE 2 equation (25).** The exponent a multi-index puts on each denominator: a metric
absent from the multi-index still contributes one power of its denominator, which is what
keeps the common domain the same for every multi-index. -/
def multiIndexExponent (order : Metric → ℕ) (index : Metric) : ℕ := max 1 (order index)

/-- **NOTE 2 equation (25).** The denominator of a multi-index moment of the family. -/
noncomputable def multiIndexDenominator (den : Metric → Point → ℝ) (order : Metric → ℕ) :
    Point → ℝ :=
  fun point ↦ ∏ index, den index point ^ multiIndexExponent order index

/-- **NOTE 2 equation (25).** The numerator of a multi-index moment of the family. -/
noncomputable def multiIndexNumerator (num den : Metric → Point → ℝ) (order : Metric → ℕ) :
    Point → ℝ :=
  fun point ↦ ∏ index, num index point ^ order index *
    den index point ^ (multiIndexExponent order index - order index)

/-- **NOTE 2 equation (25).** Wherever every denominator is nonzero, the multi-index pair has
as its quotient the product of the original metrics raised to the multi-index. -/
theorem multiIndexNumerator_ratio (num den : Metric → Point → ℝ) (order : Metric → ℕ)
    (point : Point) (hden : ∀ index, den index point ≠ 0) :
    multiIndexNumerator num den order point / multiIndexDenominator den order point =
      ∏ index, (num index point / den index point) ^ order index := by
  unfold multiIndexNumerator multiIndexDenominator
  rw [← Finset.prod_div_distrib]
  refine Finset.prod_congr rfl fun index _ ↦ ?_
  have hexponent : order index ≤ multiIndexExponent order index := le_max_right 1 (order index)
  have hne : den index point ≠ 0 := hden index
  rw [div_pow, div_eq_div_iff (pow_ne_zero _ hne) (pow_ne_zero _ hne), mul_assoc, ← pow_add,
    Nat.sub_add_cancel hexponent]

/-- The multi-index numerator of a nonnegative family is nonnegative. -/
theorem multiIndexNumerator_nonneg (num den : Metric → Point → ℝ)
    (hnum : ∀ index point, 0 ≤ num index point)
    (hle : ∀ index point, num index point ≤ den index point) (order : Metric → ℕ)
    (point : Point) : 0 ≤ multiIndexNumerator num den order point :=
  Finset.prod_nonneg fun index _ ↦
    mul_nonneg (pow_nonneg (hnum index point) _)
      (pow_nonneg (le_trans (hnum index point) (hle index point)) _)

/-- The multi-index denominator stays below one. -/
theorem multiIndexDenominator_le_one (den : Metric → Point → ℝ)
    (hden : ∀ index point, 0 ≤ den index point)
    (hone : ∀ index point, den index point ≤ 1) (order : Metric → ℕ) (point : Point) :
    multiIndexDenominator den order point ≤ 1 :=
  Finset.prod_le_one (fun index _ ↦ pow_nonneg (hden index point) _)
    fun index _ ↦ pow_le_one₀ (hden index point) (hone index point)

/-- **NOTE 2 equation (25).** The multi-index pair is again a dominated pair, so every joint
moment of the family is a bounded ratio on the common domain. -/
theorem multiIndexNumerator_le_multiIndexDenominator (num den : Metric → Point → ℝ)
    (hnum : ∀ index point, 0 ≤ num index point)
    (hle : ∀ index point, num index point ≤ den index point) (order : Metric → ℕ)
    (point : Point) :
    multiIndexNumerator num den order point ≤ multiIndexDenominator den order point := by
  unfold multiIndexNumerator multiIndexDenominator
  refine Finset.prod_le_prod (fun index _ ↦ ?_) fun index _ ↦ ?_
  · exact mul_nonneg (pow_nonneg (hnum index point) _)
      (pow_nonneg (le_trans (hnum index point) (hle index point)) _)
  · have hexponent : order index ≤ multiIndexExponent order index :=
      le_max_right 1 (order index)
    have hsplit : den index point ^ multiIndexExponent order index =
        den index point ^ order index *
          den index point ^ (multiIndexExponent order index - order index) := by
      rw [← pow_add, Nat.add_sub_cancel' hexponent]
    rw [hsplit]
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (hnum index point) (hle index point) _)
      (pow_nonneg (le_trans (hnum index point) (hle index point)) _)

/-- The exact definedness mask of a chosen subfamily: the chosen indicators against the
complementary indicators of every other member. -/
noncomputable def maskStatistic (indicatorOf : Metric → Point → ℝ)
    (selected : Finset Metric) : Point → ℝ :=
  fun point ↦ (∏ index ∈ selected, indicatorOf index point) *
    ∏ index ∈ selectedᶜ, (1 - indicatorOf index point)

/-- The mask reads one where exactly the chosen metrics are defined. -/
theorem maskStatistic_eq_one (indicatorOf : Metric → Point → ℝ) (selected : Finset Metric)
    (point : Point) (hselected : ∀ index ∈ selected, indicatorOf index point = 1)
    (hother : ∀ index ∈ selectedᶜ, indicatorOf index point = 0) :
    maskStatistic indicatorOf selected point = 1 := by
  have hleft : (∏ index ∈ selected, indicatorOf index point) = 1 :=
    Finset.prod_eq_one hselected
  have hright : (∏ index ∈ selectedᶜ, (1 - indicatorOf index point)) = 1 := by
    refine Finset.prod_eq_one fun index hmem ↦ ?_
    rw [hother index hmem, sub_zero]
  unfold maskStatistic
  rw [hleft, hright, mul_one]

/-- The mask reads zero when a chosen metric is undefined. -/
theorem maskStatistic_eq_zero_of_mem (indicatorOf : Metric → Point → ℝ)
    (selected : Finset Metric) (point : Point) (chosen : Metric) (hmem : chosen ∈ selected)
    (hzero : indicatorOf chosen point = 0) :
    maskStatistic indicatorOf selected point = 0 := by
  unfold maskStatistic
  rw [Finset.prod_eq_zero hmem hzero, zero_mul]

/-- The mask reads zero when an unchosen metric is defined. -/
theorem maskStatistic_eq_zero_of_not_mem (indicatorOf : Metric → Point → ℝ)
    (selected : Finset Metric) (point : Point) (chosen : Metric) (hmem : chosen ∈ selectedᶜ)
    (hone : indicatorOf chosen point = 1) :
    maskStatistic indicatorOf selected point = 0 := by
  have hfactor : (1 : ℝ) - indicatorOf chosen point = 0 := by rw [hone, sub_self]
  unfold maskStatistic
  rw [Finset.prod_eq_zero hmem hfactor, mul_zero]

/-- **NOTE 2 equation (26), algebraic form.** The exact mask of a chosen subfamily is the
alternating sum, over subsets of the complementary family, of the product over the chosen
metrics together with that subset. This is a ring identity for arbitrary real values: no
probability and no idempotence of the indicators is used. -/
theorem prod_mask_expansion (value : Metric → ℝ) (selected : Finset Metric) :
    (∏ index ∈ selected, value index) * ∏ index ∈ selectedᶜ, (1 - value index) =
      ∑ subset ∈ selectedᶜ.powerset, (-1 : ℝ) ^ subset.card *
        ∏ index ∈ selected ∪ subset, value index := by
  have hshift : (∏ index ∈ selectedᶜ, (1 - value index)) =
      ∏ index ∈ selectedᶜ, ((-value index) + 1) :=
    Finset.prod_congr rfl fun index _ ↦ by ring
  rw [hshift, Finset.prod_add (fun index ↦ -value index) (fun _ ↦ (1 : ℝ)) selectedᶜ,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun subset hsubset ↦ ?_
  have hsub := Finset.mem_powerset.mp hsubset
  have hdisjoint : Disjoint selected subset := by
    refine Finset.disjoint_left.mpr fun index hin hother ↦ ?_
    exact (Finset.mem_compl.mp (hsub hother)) hin
  rw [Finset.prod_union hdisjoint, Finset.prod_neg, Finset.prod_const_one, mul_one]
  ring

section ReportLaw

variable {Report : Type*} [Fintype Report]

/-- **NOTE 2 equation (26).** The probability that exactly the chosen metrics are defined is
the alternating sum, over subsets of the complementary family, of the probability that every
metric in the chosen family together with that subset is defined. -/
theorem expectation_mask_expansion (law : FiniteReportLaw Report)
    (indicatorOf : Metric → Report → ℝ) (selected : Finset Metric) :
    law.expectation (maskStatistic indicatorOf selected) =
      ∑ subset ∈ selectedᶜ.powerset, (-1 : ℝ) ^ subset.card *
        law.expectation
          (fun report ↦ ∏ index ∈ selected ∪ subset, indicatorOf index report) := by
  have hpoint : ∀ report : Report,
      law.mass report * maskStatistic indicatorOf selected report =
        ∑ subset ∈ selectedᶜ.powerset, (-1 : ℝ) ^ subset.card *
          (law.mass report * ∏ index ∈ selected ∪ subset, indicatorOf index report) := by
    intro report
    unfold maskStatistic
    rw [prod_mask_expansion (fun index ↦ indicatorOf index report) selected, Finset.mul_sum]
    exact Finset.sum_congr rfl fun subset _ ↦ by ring
  simp only [FiniteReportLaw.expectation]
  rw [Finset.sum_congr rfl fun report _ ↦ hpoint report, Finset.sum_comm]
  exact Finset.sum_congr rfl fun subset _ ↦ (Finset.mul_sum _ _ _).symm

end ReportLaw

end Descent.Portability.JointRatioFailureMasks
