/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.UniversalMetricIdentification
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.Order.Field.Basic

assert_below Descent.Decision Descent.Program

/-!
# Four portability questions that are four different numbers

This is NOTE2 §6.2. A report carries four accumulators: the source numerator and denominator
and the target numerator and denominator. On the definedness domain `D_s > 0`, `D_t > 0`,
`N_s > 0` the portability ratio `𝒫 = M_t / M_s` of NOTE2 (27) equals the cross product
`N_t D_s / (D_t N_s)`, which is `portabilityRatio_eq_cross`.

Four summaries of that ratio are then defined against a finite report law and a domain: the
mean of the ratio, the ratio of the two conditional means, the mass on which the target
metric exceeds the source metric, and the probability that the ratio exceeds one given that
it is defined. `massTargetExceeds_eq_definedMass_mul` shows the third and the fourth differ
exactly by the definedness mass, and `exampleQueries` exhibits one explicit three-point law
on which all four take different values: `9/8`, `5/6`, `1/4` and `1/2`.

The example needs three points rather than two. Two defined points are needed to separate the
mean of the ratio from the ratio of the means, since with a single defined point both
collapse to that point's ratio; and one undefined point is needed to separate the unconditional
event mass from the conditional probability, since with a full domain the definedness mass is
one. The domain is supplied to the query definitions as data rather than recovered from a
decision procedure on the reals.

Scope. The accumulators are arbitrary supplied functions on a finite report space; no claim is
made that any particular metric has this shape. NOTE2 (24)-(26), the joint failure masks, are
not formalized here.

## Empirical status

None. The bodies here are algebra: the four accumulators are supplied inputs, and every
statement is an identity between finite sums of them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.PortabilityRatioQueries

noncomputable section

variable {Ω : Type*} [Fintype Ω]

/-! ### The portability ratio and its definedness domain -/

/-- The portability ratio `𝒫 = M_t / M_s` of NOTE2 (27). -/
def portabilityRatio (sourceNum sourceDen targetNum targetDen : Ω → ℝ) (ω : Ω) : ℝ :=
  (targetNum ω / targetDen ω) / (sourceNum ω / sourceDen ω)

/-- **NOTE2 (27), the gating identity.** On the definedness domain the portability ratio is
the cross product of the four accumulators. -/
theorem portabilityRatio_eq_cross (sourceNum sourceDen targetNum targetDen : Ω → ℝ) (ω : Ω)
    (hsd : 0 < sourceDen ω) (htd : 0 < targetDen ω) (hsn : 0 < sourceNum ω) :
    portabilityRatio sourceNum sourceDen targetNum targetDen ω =
      targetNum ω * sourceDen ω / (targetDen ω * sourceNum ω) := by
  have hs : sourceDen ω ≠ 0 := hsd.ne'
  have ht : targetDen ω ≠ 0 := htd.ne'
  have hn : sourceNum ω ≠ 0 := hsn.ne'
  unfold portabilityRatio
  field_simp <;> ring

/-- **The comparison event is the same event either way.** On the definedness domain the
portability ratio exceeds one exactly when the target metric exceeds the source metric: by the
gating identity the ratio is the cross product, and comparing the cross product with one is
comparing the two metrics by cross-multiplication. -/
theorem one_lt_portabilityRatio_iff (sourceNum sourceDen targetNum targetDen : Ω → ℝ) (ω : Ω)
    (hsd : 0 < sourceDen ω) (htd : 0 < targetDen ω) (hsn : 0 < sourceNum ω) :
    1 < portabilityRatio sourceNum sourceDen targetNum targetDen ω ↔
      sourceNum ω / sourceDen ω < targetNum ω / targetDen ω := by
  rw [portabilityRatio_eq_cross sourceNum sourceDen targetNum targetDen ω hsd htd hsn,
    one_lt_div (mul_pos htd hsn), div_lt_div_iff₀ hsd htd,
    mul_comm (targetDen ω) (sourceNum ω)]

/-! ### The four queries -/

/-- The probability that the portability ratio is defined. -/
def definedMass (law : FiniteReportLaw Ω) (domain : Finset Ω) : ℝ :=
  ∑ ω ∈ domain, law.mass ω

/-- The first query of NOTE2 §6.2: the conditional mean of the portability ratio. -/
def meanOfRatio (law : FiniteReportLaw Ω) (domain : Finset Ω)
    (sourceNum sourceDen targetNum targetDen : Ω → ℝ) : ℝ :=
  (∑ ω ∈ domain,
      law.mass ω * portabilityRatio sourceNum sourceDen targetNum targetDen ω) /
    definedMass law domain

/-- The second query of NOTE2 §6.2: the ratio of the two conditional means. -/
def ratioOfMeans (law : FiniteReportLaw Ω) (domain : Finset Ω)
    (sourceNum sourceDen targetNum targetDen : Ω → ℝ) : ℝ :=
  (∑ ω ∈ domain, law.mass ω * (targetNum ω / targetDen ω)) /
    ∑ ω ∈ domain, law.mass ω * (sourceNum ω / sourceDen ω)

/-- The third query of NOTE2 §6.2: the probability that the target metric exceeds the source
metric, not conditioned on definedness. -/
def massTargetExceeds (law : FiniteReportLaw Ω) (domain : Finset Ω)
    (sourceNum sourceDen targetNum targetDen : Ω → ℝ) : ℝ :=
  ∑ ω ∈ domain,
    law.mass ω *
      (if sourceNum ω / sourceDen ω < targetNum ω / targetDen ω then 1 else 0)

/-- The fourth query of NOTE2 §6.2: the probability that the portability ratio exceeds one,
conditioned on definedness. -/
def probRatioExceedsOne (law : FiniteReportLaw Ω) (domain : Finset Ω)
    (sourceNum sourceDen targetNum targetDen : Ω → ℝ) : ℝ :=
  (∑ ω ∈ domain,
      law.mass ω *
        (if 1 < portabilityRatio sourceNum sourceDen targetNum targetDen ω then 1
          else 0)) /
    definedMass law domain

/-- **The third and fourth queries differ exactly by the definedness mass.** On a domain of
defined reports the two comparison events coincide, so the unconditional event mass is the
conditional probability scaled by the definedness mass. -/
theorem massTargetExceeds_eq_definedMass_mul (law : FiniteReportLaw Ω) (domain : Finset Ω)
    (sourceNum sourceDen targetNum targetDen : Ω → ℝ)
    (hdomain : ∀ ω ∈ domain, 0 < sourceDen ω ∧ 0 < targetDen ω ∧ 0 < sourceNum ω)
    (hmass : 0 < definedMass law domain) :
    massTargetExceeds law domain sourceNum sourceDen targetNum targetDen =
      definedMass law domain *
        probRatioExceedsOne law domain sourceNum sourceDen targetNum targetDen := by
  have hsame : ∑ ω ∈ domain,
      law.mass ω *
        (if 1 < portabilityRatio sourceNum sourceDen targetNum targetDen ω then 1
          else 0) =
      massTargetExceeds law domain sourceNum sourceDen targetNum targetDen := by
    refine Finset.sum_congr rfl fun ω hω ↦ ?_
    obtain ⟨hsd, htd, hsn⟩ := hdomain ω hω
    rw [if_congr
      (one_lt_portabilityRatio_iff sourceNum sourceDen targetNum targetDen ω hsd htd hsn)
      rfl rfl]
  rw [probRatioExceedsOne, hsame, mul_div_assoc', mul_comm, mul_div_assoc,
    div_self hmass.ne', mul_one]

/-! ### One law on which all four queries differ -/

/-- The report masses of the separating example: one undefined report of mass one half and
two defined reports of mass one quarter each. -/
def exampleMass : Fin 3 → ℝ := ![1 / 2, 1 / 4, 1 / 4]

/-- The source numerators of the separating example; the first report has numerator zero,
which is what puts it outside the definedness domain. -/
def exampleSourceNum : Fin 3 → ℝ := ![0, 1, 1]

/-- The source denominators of the separating example. -/
def exampleSourceDen : Fin 3 → ℝ := ![1, 2, 1]

/-- The target numerators of the separating example. -/
def exampleTargetNum : Fin 3 → ℝ := ![1, 1, 1]

/-- The target denominators of the separating example. -/
def exampleTargetDen : Fin 3 → ℝ := ![1, 1, 4]

/-- The separating example's masses are nonnegative. -/
theorem exampleMass_nonneg (ω : Fin 3) : 0 ≤ exampleMass ω := by
  fin_cases ω <;> norm_num [exampleMass, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]

/-- The separating example's masses sum to one. -/
theorem exampleMass_sum : ∑ ω, exampleMass ω = 1 := by
  norm_num [Fin.sum_univ_three, exampleMass, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]

/-- The separating example as a finite report law. -/
def exampleLaw : FiniteReportLaw (Fin 3) where
  mass := exampleMass
  mass_nonneg := exampleMass_nonneg
  mass_sum := exampleMass_sum

/-- The definedness domain of the separating example: the second and third reports. -/
def exampleDomain : Finset (Fin 3) := {1, 2}

/-- The first report lies outside the domain, because its source numerator vanishes, and the
other two lie inside it. -/
theorem exampleDomain_membership :
    (0 : Fin 3) ∉ exampleDomain ∧ (1 : Fin 3) ∈ exampleDomain ∧
      (2 : Fin 3) ∈ exampleDomain := by
  refine ⟨by decide, by decide, by decide⟩

/-- The excluded report has source numerator zero, which is the definedness failure of
NOTE2 (27). -/
theorem exampleSourceNum_first : exampleSourceNum 0 = 0 := rfl

/-- Sums over the example domain are two-term sums. -/
theorem exampleDomain_sum (summand : Fin 3 → ℝ) :
    ∑ ω ∈ exampleDomain, summand ω = summand 1 + summand 2 := by
  rw [exampleDomain, Finset.sum_pair (by decide)]

/-- **NOTE2 §6.2, the four queries are four numbers.** On the separating example the mean of
the portability ratio, the ratio of the conditional means, the unconditional mass on which
the target metric exceeds the source metric, and the conditional probability that the
portability ratio exceeds one are `9/8`, `5/6`, `1/4` and `1/2`. -/
theorem exampleQueries :
    meanOfRatio exampleLaw exampleDomain exampleSourceNum exampleSourceDen
        exampleTargetNum exampleTargetDen = 9 / 8 ∧
      ratioOfMeans exampleLaw exampleDomain exampleSourceNum exampleSourceDen
          exampleTargetNum exampleTargetDen = 5 / 6 ∧
      massTargetExceeds exampleLaw exampleDomain exampleSourceNum exampleSourceDen
          exampleTargetNum exampleTargetDen = 1 / 4 ∧
      probRatioExceedsOne exampleLaw exampleDomain exampleSourceNum exampleSourceDen
          exampleTargetNum exampleTargetDen = 1 / 2 := by
  have hmass : definedMass exampleLaw exampleDomain = 1 / 2 := by
    rw [definedMass, exampleDomain_sum]
    norm_num [exampleLaw, exampleMass, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [meanOfRatio, exampleDomain_sum, hmass]
    norm_num [exampleLaw, exampleMass, portabilityRatio, exampleSourceNum, exampleSourceDen,
      exampleTargetNum, exampleTargetDen, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  · rw [ratioOfMeans, exampleDomain_sum, exampleDomain_sum]
    norm_num [exampleLaw, exampleMass, exampleSourceNum, exampleSourceDen,
      exampleTargetNum, exampleTargetDen, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  · rw [massTargetExceeds, exampleDomain_sum]
    norm_num [exampleLaw, exampleMass, exampleSourceNum, exampleSourceDen,
      exampleTargetNum, exampleTargetDen, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  · rw [probRatioExceedsOne, exampleDomain_sum, hmass]
    norm_num [exampleLaw, exampleMass, portabilityRatio, exampleSourceNum, exampleSourceDen,
      exampleTargetNum, exampleTargetDen, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]

/-- The four query values of the separating example are pairwise different. -/
theorem exampleQueries_pairwise_ne :
    meanOfRatio exampleLaw exampleDomain exampleSourceNum exampleSourceDen
        exampleTargetNum exampleTargetDen ≠
      ratioOfMeans exampleLaw exampleDomain exampleSourceNum exampleSourceDen
        exampleTargetNum exampleTargetDen ∧
      massTargetExceeds exampleLaw exampleDomain exampleSourceNum exampleSourceDen
          exampleTargetNum exampleTargetDen ≠
        probRatioExceedsOne exampleLaw exampleDomain exampleSourceNum exampleSourceDen
          exampleTargetNum exampleTargetDen ∧
      ratioOfMeans exampleLaw exampleDomain exampleSourceNum exampleSourceDen
          exampleTargetNum exampleTargetDen ≠
        probRatioExceedsOne exampleLaw exampleDomain exampleSourceNum exampleSourceDen
          exampleTargetNum exampleTargetDen := by
  obtain ⟨h1, h2, h3, h4⟩ := exampleQueries
  refine ⟨?_, ?_, ?_⟩
  · rw [h1, h2]; norm_num
  · rw [h3, h4]; norm_num
  · rw [h2, h4]; norm_num

end

end Descent.Portability.PortabilityRatioQueries
