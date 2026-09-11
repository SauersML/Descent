/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.ExactMetricEvaluation

assert_below Descent.Decision Descent.Program

/-!
# The rational clause of the finite-model completeness theorem

NOTE2 Theorem 1 ends with a computational claim: if every branch probability of a fully
specified finite experiment and every requested report value is rational, then every
probability, every expectation, and every conditional expectation with positive definedness
probability is itself rational, and a finite algorithm computes it exactly. This module
proves that clause.

The first half is the closure of the rational values inside the reals under the operations
the corpus report algebra actually uses: sums, differences, products, quotients, and finite
sums and products over a finite index. The second half transports that closure along the
corpus constructions. A law whose cell masses are rational evaluates every rational metric at
a rational number; `FiniteReportLaw.bind` of a rational law through a rational kernel is
rational; `ExactFiniteHistoryLaw.propagate` over rational kernels stays rational at every
horizon; the chain-rule weight `ExactFiniteHistoryLaw.pathMass` of every complete history is
rational; and the skip-undefined conditional mean `FiniteReportLaw.conditionalMetric` returns
a rational value whenever its definedness mass is nonzero.

The terminating-algorithm clause is made literal by a second law type whose masses are
rationals rather than reals. Its expectation is a finite sum of rationals, which is the
algorithm; casting that law into the corpus real-valued law and evaluating there gives the
cast of the same rational number, so the exact rational computation and the real-valued
theory agree by a theorem rather than by convention. One concrete law and metric are
evaluated by rational arithmetic to exhibit the algorithm running.

Not formalized here: the trace enumeration of NOTE2 (7) itself, which the corpus already
carries in `ExactFiniteHistoryLaw`; and any complexity claim about the algorithm beyond its
finiteness. The value class is named `RationalValue` rather than the note's `IsRat` because
that name is taken in the root namespace by the arithmetic normalizer.

## Empirical status

None. The bodies here are algebra: rationality is a property of supplied inputs, and every
statement transports that property along constructions, so no measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.RationalReportClosure

open scoped BigOperators

/-- The value class of NOTE2 Theorem 1: a real number carried exactly by a rational. -/
def RationalValue (value : ℝ) : Prop := ∃ carrier : ℚ, (carrier : ℝ) = value

/-- Every rational is a rational value, which inhabits the class with actual numbers. -/
theorem rationalValue_ratCast (carrier : ℚ) : RationalValue (carrier : ℝ) := ⟨carrier, rfl⟩

theorem rationalValue_zero : RationalValue 0 := ⟨0, Rat.cast_zero⟩

theorem rationalValue_one : RationalValue 1 := ⟨1, Rat.cast_one⟩

theorem rationalValue_add {first second : ℝ} (hfirst : RationalValue first)
    (hsecond : RationalValue second) : RationalValue (first + second) := by
  obtain ⟨left, hleft⟩ := hfirst
  obtain ⟨right, hright⟩ := hsecond
  exact ⟨left + right, by rw [Rat.cast_add, hleft, hright]⟩

theorem rationalValue_neg {value : ℝ} (hvalue : RationalValue value) :
    RationalValue (-value) := by
  obtain ⟨carrier, hcarrier⟩ := hvalue
  exact ⟨-carrier, by rw [Rat.cast_neg, hcarrier]⟩

theorem rationalValue_sub {first second : ℝ} (hfirst : RationalValue first)
    (hsecond : RationalValue second) : RationalValue (first - second) := by
  obtain ⟨left, hleft⟩ := hfirst
  obtain ⟨right, hright⟩ := hsecond
  exact ⟨left - right, by rw [Rat.cast_sub, hleft, hright]⟩

theorem rationalValue_mul {first second : ℝ} (hfirst : RationalValue first)
    (hsecond : RationalValue second) : RationalValue (first * second) := by
  obtain ⟨left, hleft⟩ := hfirst
  obtain ⟨right, hright⟩ := hsecond
  exact ⟨left * right, by rw [Rat.cast_mul, hleft, hright]⟩

/-- Quotients stay rational, including the vanishing-denominator convention under which a
quotient by zero is zero. -/
theorem rationalValue_div {first second : ℝ} (hfirst : RationalValue first)
    (hsecond : RationalValue second) : RationalValue (first / second) := by
  obtain ⟨left, hleft⟩ := hfirst
  obtain ⟨right, hright⟩ := hsecond
  exact ⟨left / right, by rw [Rat.cast_div, hleft, hright]⟩

theorem rationalValue_sum {Index : Type*} [Fintype Index] (values : Index → ℝ)
    (hvalues : ∀ index, RationalValue (values index)) :
    RationalValue (∑ index, values index) :=
  Finset.sum_induction values RationalValue (fun _ _ ↦ rationalValue_add)
    rationalValue_zero (fun index _ ↦ hvalues index)

theorem rationalValue_prod {Index : Type*} [Fintype Index] (values : Index → ℝ)
    (hvalues : ∀ index, RationalValue (values index)) :
    RationalValue (∏ index, values index) :=
  Finset.prod_induction values RationalValue (fun _ _ ↦ rationalValue_mul)
    rationalValue_one (fun index _ ↦ hvalues index)

/-- A finite report law all of whose cell masses are rational. Assumes: the branch
probabilities supplied by the experiment are exact rationals. -/
def RationalLaw {Report : Type*} [Fintype Report] (law : FiniteReportLaw Report) : Prop :=
  ∀ report, RationalValue (law.mass report)

/-- The corpus point mass is a rational law, so the hypothesis class is inhabited by an
actual law rather than merely assumed. -/
theorem rationalLaw_pointMass {Report : Type*} [Fintype Report] (selected : Report) :
    RationalLaw (FiniteReportLaw.pointMass selected) := by
  classical
  intro report
  by_cases hreport : report = selected
  · exact ⟨1, by simp [FiniteReportLaw.pointMass, hreport]⟩
  · exact ⟨0, by simp [FiniteReportLaw.pointMass, hreport]⟩

/-- NOTE2 Theorem 1: a rational law evaluates every rational metric at a rational number. -/
theorem rationalValue_expectation {Report : Type*} [Fintype Report]
    (law : FiniteReportLaw Report) (hlaw : RationalLaw law) (metric : Report → ℝ)
    (hmetric : ∀ report, RationalValue (metric report)) :
    RationalValue (law.expectation metric) := by
  rw [FiniteReportLaw.expectation]
  exact rationalValue_sum _ fun report ↦ rationalValue_mul (hlaw report) (hmetric report)

/-- Marginalizing a rational law through a rational kernel keeps every cell rational. -/
theorem rationalLaw_bind {State Next : Type*} [Fintype State] [Fintype Next]
    (law : FiniteReportLaw State) (hlaw : RationalLaw law)
    (kernel : State → FiniteReportLaw Next)
    (hkernel : ∀ state, RationalLaw (kernel state)) :
    RationalLaw (law.bind kernel) := by
  intro next
  rw [show (law.bind kernel).mass next =
      ∑ state, law.mass state * (kernel state).mass next from rfl]
  exact rationalValue_sum _ fun state ↦ rationalValue_mul (hlaw state) (hkernel state next)

/-- Forward propagation through rational kernels stays rational at every horizon. -/
theorem rationalLaw_propagate {State : Type*} [Fintype State]
    (initial : FiniteReportLaw State) (hinitial : RationalLaw initial)
    (kernel : ℕ → State → FiniteReportLaw State)
    (hkernel : ∀ step state, RationalLaw (kernel step state)) (horizon : ℕ) :
    RationalLaw (ExactFiniteHistoryLaw.propagate initial kernel horizon) := by
  induction horizon with
  | zero => exact hinitial
  | succ step ih =>
    exact rationalLaw_bind _ ih (kernel step) fun state ↦ hkernel step state

/-- NOTE2 (7): the chain-rule probability of every complete finite history is rational. -/
theorem rationalValue_pathMass {State : Type*} [Fintype State]
    (initial : FiniteReportLaw State) (hinitial : RationalLaw initial)
    (kernel : ℕ → State → FiniteReportLaw State)
    (hkernel : ∀ step state, RationalLaw (kernel step state)) (horizon : ℕ) :
    ∀ path : ExactFiniteHistoryLaw.Path State horizon,
      RationalValue (ExactFiniteHistoryLaw.pathMass initial kernel path) := by
  induction horizon with
  | zero => exact fun path ↦ hinitial path
  | succ step ih =>
    intro path
    exact rationalValue_mul (ih path.1)
      (hkernel step (ExactFiniteHistoryLaw.terminal path.1) path.2)

/-- NOTE2 (2): the skip-undefined conditional mean of a rational partial metric under a
rational law is the named ratio, and that ratio is rational. The definedness hypothesis is
what makes the corpus metric return a value at all. -/
theorem rationalValue_conditionalMetric {Report : Type*} [Fintype Report]
    (law : FiniteReportLaw Report) (hlaw : RationalLaw law) (metric : Report → Option ℝ)
    (hmetric : ∀ report, RationalValue ((metric report).getD 0))
    (hdefined : law.definedMass metric ≠ 0) :
    law.conditionalMetric metric =
        some (law.weightedDefinedMetric metric / law.definedMass metric) ∧
      RationalValue (law.weightedDefinedMetric metric / law.definedMass metric) := by
  classical
  refine ⟨by rw [FiniteReportLaw.conditionalMetric, if_neg hdefined], ?_⟩
  have hnumerator : RationalValue (law.weightedDefinedMetric metric) :=
    rationalValue_expectation law hlaw _ hmetric
  have hmass : RationalValue (law.definedMass metric) := by
    refine rationalValue_expectation law hlaw _ fun report ↦ ?_
    by_cases hsome : (metric report).isSome
    · simpa [hsome] using rationalValue_one
    · simpa [hsome] using rationalValue_zero
  exact rationalValue_div hnumerator hmass

/-- The terminating-algorithm form of NOTE2 Theorem 1: a finite report law whose cell masses
are exact rationals. Assumes: the experiment supplies its branch probabilities as rationals. -/
structure RationalReportLaw (Report : Type*) [Fintype Report] where
  mass : Report → ℚ
  mass_nonneg : ∀ report, 0 ≤ mass report
  mass_sum : ∑ report, mass report = 1

namespace RationalReportLaw

variable {Report : Type*} [Fintype Report]

/-- The exact rational expectation. This finite sum of rationals is the algorithm that
NOTE2 Theorem 1 promises; it runs on the rationals and never touches a real number. -/
def expectation (law : RationalReportLaw Report) (metric : Report → ℚ) : ℚ :=
  ∑ report, law.mass report * metric report

/-- The real-valued corpus law carried by a rational law. -/
noncomputable def toReal (law : RationalReportLaw Report) : FiniteReportLaw Report where
  mass := fun report ↦ (law.mass report : ℝ)
  mass_nonneg := fun report ↦ by exact_mod_cast law.mass_nonneg report
  mass_sum := by
    have hcast : ((∑ report, law.mass report : ℚ) : ℝ) = ((1 : ℚ) : ℝ) := by
      rw [law.mass_sum]
    simpa using hcast

/-- The carried law is rational, which supplies a witness for the hypothesis class. -/
theorem rationalLaw_toReal (law : RationalReportLaw Report) : RationalLaw law.toReal :=
  fun report ↦ ⟨law.mass report, rfl⟩

/-- The real-valued expectation of a carried law at a carried metric is the cast of the
exact rational expectation. The rational computation and the real theory agree by proof. -/
theorem expectation_toReal (law : RationalReportLaw Report) (metric : Report → ℚ) :
    law.toReal.expectation (fun report ↦ (metric report : ℝ)) =
      ((law.expectation metric : ℚ) : ℝ) := by
  simp only [FiniteReportLaw.expectation, toReal, expectation, Rat.cast_sum, Rat.cast_mul]

/-- A concrete two-outcome rational law, which inhabits the structure with actual numbers. -/
def fairBinaryLaw : RationalReportLaw Bool where
  mass := fun _ ↦ 1 / 2
  mass_nonneg := fun _ ↦ by norm_num
  mass_sum := by norm_num [Fintype.sum_bool]

/-- The algorithm running: one concrete law and metric evaluated by rational arithmetic
alone, with the exact value decided rather than approximated. -/
theorem fairBinaryLaw_expectation :
    fairBinaryLaw.expectation (fun outcome ↦ if outcome then 3 / 5 else 1 / 7) = 13 / 35 := by
  norm_num [expectation, fairBinaryLaw, Fintype.sum_bool]

end RationalReportLaw

end Descent.Portability.RationalReportClosure
