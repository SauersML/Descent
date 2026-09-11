/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.FiniteTraceTreeLaw
import Descent.Portability.ArchitectureEnvironmentRegion
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Data.Sign.Defs

assert_below Descent.Decision Descent.Program

/-!
# Rational parameter reports on sign-condition cells

NOTE2 Theorem 2 and equation (8), in their finite-algebraic content. An experiment with a fixed
finite topology and numerical inputs `θ : σ → ℝ` is a `ParametricTree`: the dependent trace tree
of `FiniteTraceTreeLaw` with every branch probability presented, for every sign pattern of a
finite family of guard polynomials, as a quotient of real multivariate polynomials
(`PolynomialQuotient`, over Mathlib's `MvPolynomial`). A branch, domain or tie decision taken by
a Boolean combination of polynomial sign conditions is a function of the sign pattern, so it is
a branch whose presented probability is `0` or `1` on every cell. Report accumulators (the
definedness weight and the zero-extended numerator of a requested quantity) are presented the
same way.

The cells `signCell` of the sign patterns are pairwise disjoint (`disjoint_signCell`), cover the
parameter space (`iUnion_signCell`), and are finitely many (`finite_range_signCell`). Presented
quotients are closed under products, quotients and finite sums through explicit polynomial
presentations (`eval_mul`, `eval_div`, `eval_sum`). On each cell every trace weight is the value
of the explicit presentation `weightQuotient` (`traceWeight_eq_eval_weightQuotient`, with no
hypothesis). Every accumulation, in particular the definedness probability `d_j(θ)` and the
numerator `n_j(θ)`, is the value of the explicit presentation `accumulationQuotient`, whose
denominator does not vanish where the supplied presentations are regular
(`accumulation_eq_eval_accumulationQuotient`). Where `d_j(θ) > 0` the conditional mean
`n_j(θ) / d_j(θ)` is the value of an explicit presentation with nonvanishing denominator
(`conditionalMean_eq_eval_div`). At a valid parameter point the topology is an actual trace tree
(`experimentAt`): its traces are the topology's (`trace_experimentAt`), its backward evaluation
is the parametric trace enumeration (`backwardValue_experimentAt`), and the corpus
`definedMass`, `weightedDefinedMetric` and `conditionalMetric` of a presented partial metric are
the two accumulations and the presented quotient (`conditionalMetric_experimentAt_eq_eval`).

The exact joint attainable region (8), `attainableRegion`, for any finite family of requested
quantities over any admissible parameter set, is the image of the admissible points with every
`d_j > 0` under the report map `θ ↦ (n_j(θ) / d_j(θ))_j` (`attainableRegion_eq_image`). For a
parametric experiment it is the finite union over the cells of images under explicit
polynomial-quotient maps (`attainableRegion_eq_iUnion_image_cells`). One parameter point serves
every metric, so globally shared parameters stay shared. The two-by-two architecture and
environment region of NOTE2 §3.2 is an instance: `architectureTree` enumerates the mixture
averages of `ArchitectureEnvironmentRegion` (`accumulation_architectureTree`), and its attainable
region over the unit square is the corpus region `jointRegion` of NOTE2 (10)
(`attainableRegion_architectureTree_eq_jointRegion`).

Not formalized: semialgebraic sets, the semialgebraicity of the joint input-output graph, and
real quantifier elimination, which the note uses to describe (8), establish sharp bounds, and
decide attainment; none of them is available at this Mathlib pin. The partition here is by the
signs of the supplied guards, and regularity of the presented denominators at a point is a
supplied hypothesis, not a refinement the module computes. Algebraic roots, optimizers and
transcendental primitives are outside the rational conclusion, as the note states.

## Empirical status

None. The bodies here are algebra: parameters, presented probabilities and accumulators are
supplied inputs, and every statement is an identity of polynomial evaluations or of sets.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.RationalParameterReports

open FiniteTraceTreeLaw

noncomputable section

/-! ### Presented quotients of multivariate polynomials -/

/-- A presented quotient of two real multivariate polynomials in the parameter coordinates. -/
structure PolynomialQuotient (σ : Type) where
  numerator : MvPolynomial σ ℝ
  denominator : MvPolynomial σ ℝ

namespace PolynomialQuotient

variable {σ : Type}

/-- The value `P(θ) / Q(θ)` of a presented quotient at a parameter point. -/
def eval (quotient : PolynomialQuotient σ) (θ : σ → ℝ) : ℝ :=
  MvPolynomial.eval θ quotient.numerator / MvPolynomial.eval θ quotient.denominator

/-- A polynomial presented with unit denominator. -/
def ofPolynomial (polynomial : MvPolynomial σ ℝ) : PolynomialQuotient σ :=
  ⟨polynomial, 1⟩

/-- A polynomial with unit denominator evaluates to the polynomial. -/
theorem eval_ofPolynomial (polynomial : MvPolynomial σ ℝ) (θ : σ → ℝ) :
    (ofPolynomial polynomial).eval θ = MvPolynomial.eval θ polynomial := by
  simp only [eval, ofPolynomial, map_one, div_one]

/-- The unit denominator never vanishes. -/
theorem denominator_ofPolynomial_ne_zero (polynomial : MvPolynomial σ ℝ) (θ : σ → ℝ) :
    MvPolynomial.eval θ (ofPolynomial polynomial).denominator ≠ 0 := by
  simp only [ofPolynomial, map_one, ne_eq, one_ne_zero, not_false_eq_true]

/-- The presented product of two quotients. -/
def mul (first second : PolynomialQuotient σ) : PolynomialQuotient σ :=
  ⟨first.numerator * second.numerator, first.denominator * second.denominator⟩

/-- A presented product evaluates to the product of the values, with no hypothesis. -/
theorem eval_mul (first second : PolynomialQuotient σ) (θ : σ → ℝ) :
    (first.mul second).eval θ = first.eval θ * second.eval θ := by
  simp only [eval, mul, map_mul, div_mul_div_comm]

/-- A presented product has a nonvanishing denominator where both factors do. -/
theorem denominator_mul_ne_zero {first second : PolynomialQuotient σ} {θ : σ → ℝ}
    (hfirst : MvPolynomial.eval θ first.denominator ≠ 0)
    (hsecond : MvPolynomial.eval θ second.denominator ≠ 0) :
    MvPolynomial.eval θ (first.mul second).denominator ≠ 0 := by
  simp only [mul, map_mul]
  exact mul_ne_zero hfirst hsecond

/-- The presented quotient of two quotients. -/
def div (first second : PolynomialQuotient σ) : PolynomialQuotient σ :=
  ⟨first.numerator * second.denominator, first.denominator * second.numerator⟩

/-- A presented quotient of quotients evaluates to the quotient of the values. -/
theorem eval_div (first second : PolynomialQuotient σ) (θ : σ → ℝ) :
    (first.div second).eval θ = first.eval θ / second.eval θ := by
  simp only [eval, div, map_mul, div_div_div_eq]

/-- A presented quotient of quotients has a nonvanishing denominator where the dividend's
denominator does not vanish and the divisor's value is nonzero. -/
theorem denominator_div_ne_zero {first second : PolynomialQuotient σ} {θ : σ → ℝ}
    (hfirst : MvPolynomial.eval θ first.denominator ≠ 0) (hsecond : second.eval θ ≠ 0) :
    MvPolynomial.eval θ (first.div second).denominator ≠ 0 := by
  simp only [div, map_mul]
  exact mul_ne_zero hfirst (div_ne_zero_iff.mp hsecond).1

/-- The presented common-denominator sum of a finite family of quotients. -/
def sum {ι : Type} [Fintype ι] (family : ι → PolynomialQuotient σ) : PolynomialQuotient σ := by
  classical
  exact ⟨∑ index, (family index).numerator *
      ∏ other ∈ Finset.univ.erase index, (family other).denominator,
    ∏ index, (family index).denominator⟩

/-- A presented sum has a nonvanishing denominator where every summand does. -/
theorem denominator_sum_ne_zero {ι : Type} [Fintype ι] {family : ι → PolynomialQuotient σ}
    {θ : σ → ℝ} (hfamily : ∀ index, MvPolynomial.eval θ (family index).denominator ≠ 0) :
    MvPolynomial.eval θ (sum family).denominator ≠ 0 := by
  simp only [sum, map_prod]
  exact Finset.prod_ne_zero_iff.mpr fun index _ ↦ hfamily index

/-- With every denominator nonzero, a presented sum evaluates to the sum of the values. -/
theorem eval_sum {ι : Type} [Fintype ι] (family : ι → PolynomialQuotient σ) (θ : σ → ℝ)
    (hfamily : ∀ index, MvPolynomial.eval θ (family index).denominator ≠ 0) :
    (sum family).eval θ = ∑ index, (family index).eval θ := by
  classical
  simp only [eval, sum, map_sum, map_mul, map_prod, Finset.sum_div]
  refine Finset.sum_congr rfl fun index _ ↦ ?_
  rw [← Finset.mul_prod_erase Finset.univ
    (fun other ↦ MvPolynomial.eval θ (family other).denominator) (Finset.mem_univ index)]
  exact mul_div_mul_right _ _ (Finset.prod_ne_zero_iff.mpr fun other _ ↦ hfamily other)

end PolynomialQuotient

/-! ### Sign-condition cells -/

variable {σ Guard Report : Type}

/-- The sign pattern of a finite family of guard polynomials at a parameter point. -/
def signPattern (guard : Guard → MvPolynomial σ ℝ) (θ : σ → ℝ) : Guard → SignType :=
  fun index ↦ SignType.sign (MvPolynomial.eval θ (guard index))

/-- The cell of a sign pattern: the parameters at which every guard has its prescribed sign. A
Boolean combination of polynomial sign conditions is a function of the pattern, hence constant
on every cell. -/
def signCell (guard : Guard → MvPolynomial σ ℝ) (pattern : Guard → SignType) :
    Set (σ → ℝ) :=
  {θ | signPattern guard θ = pattern}

/-- Every parameter point lies in the cell of its own sign pattern. -/
theorem mem_signCell_signPattern (guard : Guard → MvPolynomial σ ℝ) (θ : σ → ℝ) :
    θ ∈ signCell guard (signPattern guard θ) :=
  rfl

/-- The cells of distinct sign patterns are disjoint. -/
theorem disjoint_signCell (guard : Guard → MvPolynomial σ ℝ) {first second : Guard → SignType}
    (hne : first ≠ second) : Disjoint (signCell guard first) (signCell guard second) :=
  Set.disjoint_left.mpr fun _ hfirst hsecond ↦ hne (Eq.trans (Eq.symm hfirst) hsecond)

/-- The cells cover the parameter space. -/
theorem iUnion_signCell (guard : Guard → MvPolynomial σ ℝ) :
    ⋃ pattern, signCell guard pattern = Set.univ :=
  Set.eq_univ_of_forall fun θ ↦ Set.mem_iUnion.mpr ⟨_, mem_signCell_signPattern guard θ⟩

/-- A finite family of guards has finitely many cells. -/
theorem finite_range_signCell [Finite Guard] (guard : Guard → MvPolynomial σ ℝ) :
    (Set.range (signCell guard)).Finite :=
  Set.finite_range _

/-! ### Parametric experiments -/

/-- An experiment with a fixed finite topology and numerical inputs `θ`. A node carries a finite
branch type and, for every sign pattern of the guards, a presented quotient probability for each
branch. A decision by polynomial sign conditions is a branch presented as `0` or `1` per cell. -/
inductive ParametricTree (σ Guard Report : Type) : Type 1
  | leaf (report : Report) : ParametricTree σ Guard Report
  | node (Branch : Type) [Fintype Branch]
      (probability : (Guard → SignType) → Branch → PolynomialQuotient σ)
      (child : Branch → ParametricTree σ Guard Report) : ParametricTree σ Guard Report

namespace ParametricTree

/-- The complete traces of the topology, which do not depend on the parameters. -/
def Trace : ParametricTree σ Guard Report → Type
  | .leaf _ => Unit
  | @ParametricTree.node _ _ _ Branch _ _ child => Σ branch : Branch, Trace (child branch)

/-- A topology has finitely many complete traces. -/
instance traceFintype : (tree : ParametricTree σ Guard Report) → Fintype (Trace tree)
  | .leaf _ => inferInstanceAs (Fintype Unit)
  | @ParametricTree.node _ _ _ Branch _ _ child => by
      letI : ∀ branch, Fintype (Trace (child branch)) :=
        fun branch ↦ traceFintype (child branch)
      exact inferInstanceAs (Fintype (Σ branch : Branch, Trace (child branch)))

/-- The report at the end of a complete trace. -/
def traceReport : (tree : ParametricTree σ Guard Report) → Trace tree → Report
  | .leaf report, _ => report
  | @ParametricTree.node _ _ _ _ _ _ child, trace => traceReport (child trace.1) trace.2

/-- The chain-rule weight of a trace at a parameter point: the product of the branch
probabilities selected by the sign pattern at that point. -/
def traceWeight (guard : Guard → MvPolynomial σ ℝ) (θ : σ → ℝ) :
    (tree : ParametricTree σ Guard Report) → Trace tree → ℝ
  | .leaf _, _ => 1
  | @ParametricTree.node _ _ _ _ _ probability child, trace =>
      (probability (signPattern guard θ) trace.1).eval θ *
        traceWeight guard θ (child trace.1) trace.2

/-- The presented quotient of a trace weight on the cell of a pattern. -/
def weightQuotient (pattern : Guard → SignType) :
    (tree : ParametricTree σ Guard Report) → Trace tree → PolynomialQuotient σ
  | .leaf _, _ => PolynomialQuotient.ofPolynomial 1
  | @ParametricTree.node _ _ _ _ _ probability child, trace =>
      (probability pattern trace.1).mul (weightQuotient pattern (child trace.1) trace.2)

/-- Every branch probability presented for the pattern has a denominator that does not vanish at
θ. -/
def RegularAt (pattern : Guard → SignType) (θ : σ → ℝ) : ParametricTree σ Guard Report → Prop
  | .leaf _ => True
  | @ParametricTree.node _ _ _ _ _ probability child =>
      (∀ branch, MvPolynomial.eval θ (probability pattern branch).denominator ≠ 0) ∧
        ∀ branch, RegularAt pattern θ (child branch)

/-- **NOTE2 Theorem 2, trace weights.** On the cell of a pattern every trace weight is the value
of the explicit presentation `weightQuotient`, a product of presented quotients. -/
theorem traceWeight_eq_eval_weightQuotient (guard : Guard → MvPolynomial σ ℝ)
    (pattern : Guard → SignType) {θ : σ → ℝ} (hcell : θ ∈ signCell guard pattern)
    (tree : ParametricTree σ Guard Report) (trace : Trace tree) :
    traceWeight guard θ tree trace = (weightQuotient pattern tree trace).eval θ := by
  induction tree with
  | leaf _ =>
    change (1 : ℝ) = (PolynomialQuotient.ofPolynomial 1).eval θ
    rw [PolynomialQuotient.eval_ofPolynomial, map_one]
  | node Branch probability child ih =>
    change (probability (signPattern guard θ) trace.1).eval θ *
        traceWeight guard θ (child trace.1) trace.2 =
      ((probability pattern trace.1).mul (weightQuotient pattern (child trace.1) trace.2)).eval θ
    rw [PolynomialQuotient.eval_mul, ← ih trace.1 trace.2,
      show signPattern guard θ = pattern from hcell]

/-- The presentation of a trace weight has a nonvanishing denominator at a regular point.
Assumes: `RegularAt pattern θ tree`. -/
theorem denominator_weightQuotient_ne_zero (pattern : Guard → SignType) {θ : σ → ℝ}
    (tree : ParametricTree σ Guard Report) (hregular : RegularAt pattern θ tree)
    (trace : Trace tree) :
    MvPolynomial.eval θ (weightQuotient pattern tree trace).denominator ≠ 0 := by
  induction tree with
  | leaf _ => exact PolynomialQuotient.denominator_ofPolynomial_ne_zero 1 θ
  | node Branch probability child ih =>
    exact PolynomialQuotient.denominator_mul_ne_zero (hregular.1 trace.1)
      (ih trace.1 (hregular.2 trace.1) trace.2)

/-- The trace enumeration of an accumulator at a parameter point, `Σ_τ w_τ(θ) a(R(τ), θ)`. With
the definedness weight of a requested quantity this is `d_j(θ)`, with its zero-extended numerator
it is `n_j(θ)`. -/
def accumulation (guard : Guard → MvPolynomial σ ℝ) (tree : ParametricTree σ Guard Report)
    (accumulator : Report → (Guard → SignType) → PolynomialQuotient σ) (θ : σ → ℝ) : ℝ :=
  ∑ trace, traceWeight guard θ tree trace *
    (accumulator (traceReport tree trace) (signPattern guard θ)).eval θ

/-- The presented quotient of an accumulation on the cell of a pattern. -/
def accumulationQuotient (tree : ParametricTree σ Guard Report)
    (accumulator : Report → (Guard → SignType) → PolynomialQuotient σ)
    (pattern : Guard → SignType) : PolynomialQuotient σ :=
  PolynomialQuotient.sum fun trace : Trace tree ↦
    (weightQuotient pattern tree trace).mul (accumulator (traceReport tree trace) pattern)

/-- The presentation of an accumulation has a nonvanishing denominator at a regular point.
Assumes: `RegularAt pattern θ tree`. -/
theorem denominator_accumulationQuotient_ne_zero (tree : ParametricTree σ Guard Report)
    (accumulator : Report → (Guard → SignType) → PolynomialQuotient σ)
    (pattern : Guard → SignType) {θ : σ → ℝ} (hregular : RegularAt pattern θ tree)
    (haccumulator : ∀ report, MvPolynomial.eval θ (accumulator report pattern).denominator ≠ 0) :
    MvPolynomial.eval θ (accumulationQuotient tree accumulator pattern).denominator ≠ 0 :=
  PolynomialQuotient.denominator_sum_ne_zero fun trace ↦
    PolynomialQuotient.denominator_mul_ne_zero
      (denominator_weightQuotient_ne_zero pattern tree hregular trace) (haccumulator _)

/-- **NOTE2 Theorem 2, definedness probabilities and numerators.** On the cell of a pattern, at a
regular point, every accumulation is the value of the explicit presentation
`accumulationQuotient`. Assumes: `RegularAt pattern θ tree`. -/
theorem accumulation_eq_eval_accumulationQuotient (guard : Guard → MvPolynomial σ ℝ)
    (pattern : Guard → SignType) {θ : σ → ℝ} (hcell : θ ∈ signCell guard pattern)
    (tree : ParametricTree σ Guard Report)
    (accumulator : Report → (Guard → SignType) → PolynomialQuotient σ)
    (hregular : RegularAt pattern θ tree)
    (haccumulator : ∀ report, MvPolynomial.eval θ (accumulator report pattern).denominator ≠ 0) :
    accumulation guard tree accumulator θ =
      (accumulationQuotient tree accumulator pattern).eval θ := by
  rw [accumulationQuotient, PolynomialQuotient.eval_sum _ _ fun trace ↦
    PolynomialQuotient.denominator_mul_ne_zero
      (denominator_weightQuotient_ne_zero pattern tree hregular trace) (haccumulator _)]
  refine Finset.sum_congr rfl fun trace _ ↦ ?_
  rw [PolynomialQuotient.eval_mul, ← traceWeight_eq_eval_weightQuotient guard pattern hcell,
    show signPattern guard θ = pattern from hcell]

/-- **NOTE2 Theorem 2, conditional means.** On the cell of a pattern, at a regular point where the
definedness accumulation is positive, the conditional mean `n(θ) / d(θ)` is the value of an
explicit presented quotient of polynomials, and that presentation has a nonvanishing denominator.
Assumes: `RegularAt pattern θ tree`. -/
theorem conditionalMean_eq_eval_div (guard : Guard → MvPolynomial σ ℝ)
    (pattern : Guard → SignType) {θ : σ → ℝ} (hcell : θ ∈ signCell guard pattern)
    (tree : ParametricTree σ Guard Report)
    (definedness numerator : Report → (Guard → SignType) → PolynomialQuotient σ)
    (hregular : RegularAt pattern θ tree)
    (hdefinedness : ∀ report, MvPolynomial.eval θ (definedness report pattern).denominator ≠ 0)
    (hnumerator : ∀ report, MvPolynomial.eval θ (numerator report pattern).denominator ≠ 0)
    (hpositive : 0 < accumulation guard tree definedness θ) :
    accumulation guard tree numerator θ / accumulation guard tree definedness θ =
        ((accumulationQuotient tree numerator pattern).div
          (accumulationQuotient tree definedness pattern)).eval θ ∧
      MvPolynomial.eval θ ((accumulationQuotient tree numerator pattern).div
        (accumulationQuotient tree definedness pattern)).denominator ≠ 0 := by
  have hdef := accumulation_eq_eval_accumulationQuotient guard pattern hcell tree definedness
    hregular hdefinedness
  have hnum := accumulation_eq_eval_accumulationQuotient guard pattern hcell tree numerator
    hregular hnumerator
  refine ⟨by rw [PolynomialQuotient.eval_div, ← hdef, ← hnum], ?_⟩
  refine PolynomialQuotient.denominator_div_ne_zero
    (denominator_accumulationQuotient_ne_zero tree numerator pattern hregular hnumerator) ?_
  rw [← hdef]
  exact hpositive.ne'

/-! ### The actual experiment at a valid parameter point -/

/-- At θ, every node's selected branch probabilities are nonnegative and sum to one. -/
def ValidAt (guard : Guard → MvPolynomial σ ℝ) (θ : σ → ℝ) :
    ParametricTree σ Guard Report → Prop
  | .leaf _ => True
  | @ParametricTree.node _ _ _ _ _ probability child =>
      (∀ branch, 0 ≤ (probability (signPattern guard θ) branch).eval θ) ∧
        (∑ branch, (probability (signPattern guard θ) branch).eval θ) = 1 ∧
          ∀ branch, ValidAt guard θ (child branch)

/-- The experiment at a valid parameter point, as a trace tree carrying actual branch laws. -/
def experimentAt (guard : Guard → MvPolynomial σ ℝ) (θ : σ → ℝ) :
    (tree : ParametricTree σ Guard Report) → ValidAt guard θ tree → TraceTree Report
  | .leaf report, _ => .leaf report
  | @ParametricTree.node _ _ _ Branch _ probability child, hvalid =>
      .node Branch
        { mass := fun branch ↦ (probability (signPattern guard θ) branch).eval θ
          mass_nonneg := hvalid.1
          mass_sum := hvalid.2.1 }
        fun branch ↦ experimentAt guard θ (child branch) (hvalid.2.2 branch)

/-- The traces of the actual experiment at a valid point are the traces of the topology.
Assumes: `ValidAt guard θ tree`. -/
theorem trace_experimentAt (guard : Guard → MvPolynomial σ ℝ) (θ : σ → ℝ)
    (tree : ParametricTree σ Guard Report) (hvalid : ValidAt guard θ tree) :
    TraceTree.Trace (experimentAt guard θ tree hvalid) = Trace tree := by
  induction tree with
  | leaf _ => rfl
  | node Branch probability child ih =>
    exact congrArg (@Sigma Branch) (funext fun branch ↦ ih branch (hvalid.2.2 branch))

/-- **The parametric experiment is an experiment.** At a valid parameter point, backward
evaluation of the actual trace tree is the trace enumeration of the topology with the selected
branch probabilities. Assumes: `ValidAt guard θ tree`. -/
theorem backwardValue_experimentAt (guard : Guard → MvPolynomial σ ℝ) (θ : σ → ℝ)
    (tree : ParametricTree σ Guard Report) (hvalid : ValidAt guard θ tree)
    (metric : Report → ℝ) :
    TraceTree.backwardValue (experimentAt guard θ tree hvalid) metric =
      ∑ trace, traceWeight guard θ tree trace * metric (traceReport tree trace) := by
  induction tree with
  | leaf report =>
    change metric report = ∑ _trace : Unit, (1 : ℝ) * metric report
    simp
  | node Branch probability child ih =>
    change ∑ branch, (probability (signPattern guard θ) branch).eval θ *
        TraceTree.backwardValue (experimentAt guard θ (child branch) (hvalid.2.2 branch)) metric =
      ∑ trace : (Σ branch : Branch, Trace (child branch)),
        (probability (signPattern guard θ) trace.1).eval θ *
          traceWeight guard θ (child trace.1) trace.2 *
            metric (traceReport (child trace.1) trace.2)
    rw [Fintype.sum_sigma]
    refine Finset.sum_congr rfl fun branch _ ↦ ?_
    rw [ih branch (hvalid.2.2 branch), Finset.mul_sum]
    exact Finset.sum_congr rfl fun trace _ ↦ (mul_assoc _ _ _).symm

/-- A presented partial metric at a parameter point: defined where its definedness decision holds
on the sign pattern at that point, with the presented value there. -/
def partialMetric (guard : Guard → MvPolynomial σ ℝ)
    (defined : Report → (Guard → SignType) → Bool)
    (value : Report → (Guard → SignType) → PolynomialQuotient σ) (θ : σ → ℝ) :
    Report → Option ℝ :=
  fun report ↦ if defined report (signPattern guard θ) then
    some ((value report (signPattern guard θ)).eval θ) else none

/-- The definedness accumulator of a presented partial metric: `1` where it is defined and `0`
elsewhere. -/
def definednessAccumulator (defined : Report → (Guard → SignType) → Bool) :
    Report → (Guard → SignType) → PolynomialQuotient σ :=
  fun report pattern ↦ if defined report pattern then PolynomialQuotient.ofPolynomial 1
    else PolynomialQuotient.ofPolynomial 0

/-- The zero-extended numerator accumulator of a presented partial metric. -/
def numeratorAccumulator (defined : Report → (Guard → SignType) → Bool)
    (value : Report → (Guard → SignType) → PolynomialQuotient σ) :
    Report → (Guard → SignType) → PolynomialQuotient σ :=
  fun report pattern ↦ if defined report pattern then value report pattern
    else PolynomialQuotient.ofPolynomial 0

/-- **NOTE2 (2) at a parameter point.** Under the actual report law at a valid θ, the corpus
definedness probability of a presented partial metric is its definedness accumulation `d(θ)`.
Assumes: `ValidAt guard θ tree`. -/
theorem definedMass_experimentAt [Fintype Report] (guard : Guard → MvPolynomial σ ℝ)
    (θ : σ → ℝ) (tree : ParametricTree σ Guard Report) (hvalid : ValidAt guard θ tree)
    (defined : Report → (Guard → SignType) → Bool)
    (value : Report → (Guard → SignType) → PolynomialQuotient σ) :
    (TraceTree.reportLaw (experimentAt guard θ tree hvalid)).definedMass
        (partialMetric guard defined value θ) =
      accumulation guard tree (definednessAccumulator defined) θ := by
  rw [FiniteReportLaw.definedMass, TraceTree.expectation_reportLaw, backwardValue_experimentAt]
  refine Finset.sum_congr rfl fun trace _ ↦ ?_
  by_cases hdefined : defined (traceReport tree trace) (signPattern guard θ) = true <;>
    simp [partialMetric, definednessAccumulator, hdefined, PolynomialQuotient.eval_ofPolynomial]

/-- **NOTE2 (2) at a parameter point.** Under the actual report law at a valid θ, the corpus
zero-extended numerator of a presented partial metric is its numerator accumulation `n(θ)`.
Assumes: `ValidAt guard θ tree`. -/
theorem weightedDefinedMetric_experimentAt [Fintype Report] (guard : Guard → MvPolynomial σ ℝ)
    (θ : σ → ℝ) (tree : ParametricTree σ Guard Report) (hvalid : ValidAt guard θ tree)
    (defined : Report → (Guard → SignType) → Bool)
    (value : Report → (Guard → SignType) → PolynomialQuotient σ) :
    (TraceTree.reportLaw (experimentAt guard θ tree hvalid)).weightedDefinedMetric
        (partialMetric guard defined value θ) =
      accumulation guard tree (numeratorAccumulator defined value) θ := by
  rw [FiniteReportLaw.weightedDefinedMetric, TraceTree.expectation_reportLaw,
    backwardValue_experimentAt]
  refine Finset.sum_congr rfl fun trace _ ↦ ?_
  by_cases hdefined : defined (traceReport tree trace) (signPattern guard θ) = true <;>
    simp [partialMetric, numeratorAccumulator, hdefined, PolynomialQuotient.eval_ofPolynomial]

/-- **NOTE2 Theorem 2 for a partial metric.** Let θ be a valid, regular parameter point in the
cell of a pattern. Under the actual report law at θ, whenever the definedness probability is
positive, the corpus conditional mean of a presented partial metric is the value at θ of an
explicit presented quotient of polynomials that depends only on the pattern. Assumes:
`ValidAt guard θ tree` and `RegularAt pattern θ tree`. -/
theorem conditionalMetric_experimentAt_eq_eval [Fintype Report]
    (guard : Guard → MvPolynomial σ ℝ) (pattern : Guard → SignType) {θ : σ → ℝ}
    (hcell : θ ∈ signCell guard pattern) (tree : ParametricTree σ Guard Report)
    (hvalid : ValidAt guard θ tree) (hregular : RegularAt pattern θ tree)
    (defined : Report → (Guard → SignType) → Bool)
    (value : Report → (Guard → SignType) → PolynomialQuotient σ)
    (hvalue : ∀ report, MvPolynomial.eval θ (value report pattern).denominator ≠ 0)
    (hpositive : 0 < (TraceTree.reportLaw (experimentAt guard θ tree hvalid)).definedMass
      (partialMetric guard defined value θ)) :
    (TraceTree.reportLaw (experimentAt guard θ tree hvalid)).conditionalMetric
        (partialMetric guard defined value θ) =
      some (((accumulationQuotient tree (numeratorAccumulator defined value) pattern).div
        (accumulationQuotient tree (definednessAccumulator defined) pattern)).eval θ) := by
  have hdefinedness : ∀ report,
      MvPolynomial.eval θ (definednessAccumulator defined report pattern).denominator ≠ 0 := by
    intro report
    simp only [definednessAccumulator]
    split_ifs <;> exact PolynomialQuotient.denominator_ofPolynomial_ne_zero _ θ
  have hnumerator : ∀ report,
      MvPolynomial.eval θ (numeratorAccumulator defined value report pattern).denominator ≠ 0 := by
    intro report
    simp only [numeratorAccumulator]
    split_ifs
    · exact hvalue report
    · exact PolynomialQuotient.denominator_ofPolynomial_ne_zero _ θ
  have hmass := definedMass_experimentAt guard θ tree hvalid defined value
  rw [FiniteReportLaw.conditionalMetric, if_neg hpositive.ne', hmass,
    weightedDefinedMetric_experimentAt]
  rw [hmass] at hpositive
  exact congrArg some (conditionalMean_eq_eval_div guard pattern hcell tree _ _ hregular
    hdefinedness hnumerator hpositive).1

end ParametricTree

/-! ### The joint attainable region (8) -/

/-- **NOTE2 (8).** The exact joint attainable region: the report vectors `r` for which one
admissible parameter point has every definedness probability positive and `d_j(θ) r_j = n_j(θ)`
for every requested quantity `j`. -/
def attainableRegion {Parameter J : Type} (admissible : Set Parameter)
    (definedness numerator : J → Parameter → ℝ) : Set (J → ℝ) :=
  {report | ∃ θ ∈ admissible, ∀ j, 0 < definedness j θ ∧
    definedness j θ * report j = numerator j θ}

/-- **NOTE2 (8) is an image.** The attainable region is the image, under the report map
`θ ↦ (n_j(θ) / d_j(θ))_j`, of the admissible points at which every definedness probability is
positive. -/
theorem attainableRegion_eq_image {Parameter J : Type} (admissible : Set Parameter)
    (definedness numerator : J → Parameter → ℝ) :
    attainableRegion admissible definedness numerator =
      (fun θ j ↦ numerator j θ / definedness j θ) ''
        {θ | θ ∈ admissible ∧ ∀ j, 0 < definedness j θ} := by
  ext report
  constructor
  · rintro ⟨θ, hθ, hreport⟩
    refine ⟨θ, ⟨hθ, fun j ↦ (hreport j).1⟩, funext fun j ↦ ?_⟩
    show numerator j θ / definedness j θ = report j
    rw [← (hreport j).2, mul_div_cancel_left₀ _ (hreport j).1.ne']
  · rintro ⟨θ, ⟨hθ, hpositive⟩, rfl⟩
    refine ⟨θ, hθ, fun j ↦ ⟨hpositive j, ?_⟩⟩
    show definedness j θ * (numerator j θ / definedness j θ) = numerator j θ
    rw [← mul_div_assoc, mul_div_cancel_left₀ _ (hpositive j).ne']

/-- **NOTE2 Theorem 2, the joint input-output graph.** When the presented probabilities and
accumulators are regular at every admissible point, the attainable region of a finite family of
requested quantities is the finite union, over the sign patterns, of the images of the admissible
points of each cell under an explicit map whose coordinates are presented quotients of
polynomials. Assumes: `RegularAt (signPattern guard θ) θ tree` at every admissible θ. -/
theorem attainableRegion_eq_iUnion_image_cells {J : Type} (guard : Guard → MvPolynomial σ ℝ)
    (tree : ParametricTree σ Guard Report)
    (definedness numerator : J → Report → (Guard → SignType) → PolynomialQuotient σ)
    (admissible : Set (σ → ℝ))
    (hregular : ∀ θ ∈ admissible, ParametricTree.RegularAt (signPattern guard θ) θ tree)
    (haccumulators : ∀ θ ∈ admissible, ∀ j report,
      MvPolynomial.eval θ (definedness j report (signPattern guard θ)).denominator ≠ 0 ∧
        MvPolynomial.eval θ (numerator j report (signPattern guard θ)).denominator ≠ 0) :
    attainableRegion admissible
        (fun j ↦ ParametricTree.accumulation guard tree (definedness j))
        (fun j ↦ ParametricTree.accumulation guard tree (numerator j)) =
      ⋃ pattern, (fun θ j ↦
          ((ParametricTree.accumulationQuotient tree (numerator j) pattern).div
            (ParametricTree.accumulationQuotient tree (definedness j) pattern)).eval θ) ''
        {θ | θ ∈ admissible ∧ θ ∈ signCell guard pattern ∧
          ∀ j, 0 < ParametricTree.accumulation guard tree (definedness j) θ} := by
  have hmean : ∀ θ ∈ admissible,
      (∀ j, 0 < ParametricTree.accumulation guard tree (definedness j) θ) →
        (fun j ↦ ParametricTree.accumulation guard tree (numerator j) θ /
          ParametricTree.accumulation guard tree (definedness j) θ) =
        fun j ↦ ((ParametricTree.accumulationQuotient tree (numerator j)
            (signPattern guard θ)).div (ParametricTree.accumulationQuotient tree (definedness j)
              (signPattern guard θ))).eval θ :=
    fun θ hθ hpositive ↦ funext fun j ↦
      (ParametricTree.conditionalMean_eq_eval_div guard _ (mem_signCell_signPattern guard θ) tree
        _ _ (hregular θ hθ) (fun report ↦ (haccumulators θ hθ j report).1)
        (fun report ↦ (haccumulators θ hθ j report).2) (hpositive j)).1
  rw [attainableRegion_eq_image]
  ext report
  simp only [Set.mem_image, Set.mem_iUnion, Set.mem_setOf_eq]
  constructor
  · rintro ⟨θ, ⟨hθ, hpositive⟩, rfl⟩
    exact ⟨signPattern guard θ, θ, ⟨hθ, mem_signCell_signPattern guard θ, hpositive⟩,
      (hmean θ hθ hpositive).symm⟩
  · rintro ⟨pattern, θ, ⟨hθ, hcell, hpositive⟩, rfl⟩
    have hsign : signPattern guard θ = pattern := hcell
    subst hsign
    exact ⟨θ, ⟨hθ, hpositive⟩, hmean θ hθ hpositive⟩

/-! ### The architecture/environment region of NOTE2 §3.2 is an instance -/

/-- The presented probability of a binary indicator whose mean is the parameter coordinate
`index`. -/
def indicatorQuotient (index : Fin 2) : Bool → PolynomialQuotient (Fin 2)
  | true => PolynomialQuotient.ofPolynomial (MvPolynomial.X index)
  | false => PolynomialQuotient.ofPolynomial (1 - MvPolynomial.X index)

/-- The indicator is on with probability `θ index`. -/
theorem eval_indicatorQuotient_true (index : Fin 2) (θ : Fin 2 → ℝ) :
    (indicatorQuotient index true).eval θ = θ index := by
  simp only [indicatorQuotient, PolynomialQuotient.eval_ofPolynomial, MvPolynomial.eval_X]

/-- The indicator is off with probability `1 - θ index`. -/
theorem eval_indicatorQuotient_false (index : Fin 2) (θ : Fin 2 → ℝ) :
    (indicatorQuotient index false).eval θ = 1 - θ index := by
  simp only [indicatorQuotient, PolynomialQuotient.eval_ofPolynomial, map_sub, map_one,
    MvPolynomial.eval_X]

/-- NOTE2 §3.2 as a parametric experiment with no guards: an architecture indicator of mean
`θ 0`, then an independent environment indicator of mean `θ 1`, reporting the corner. -/
def architectureTree : ParametricTree (Fin 2) Empty (Bool × Bool) :=
  .node Bool (fun _ architecture ↦ indicatorQuotient 0 architecture) fun architecture ↦
    .node Bool (fun _ environment ↦ indicatorQuotient 1 environment) fun environment ↦
      .leaf (architecture, environment)

/-- Corner accumulators presented as constant polynomials. -/
def cornerAccumulator (corner : Bool × Bool → ℝ) :
    Bool × Bool → (Empty → SignType) → PolynomialQuotient (Fin 2) :=
  fun report _ ↦ PolynomialQuotient.ofPolynomial (MvPolynomial.C (corner report))

/-- The architecture tree has polynomial branch probabilities, so it is regular everywhere. -/
theorem regularAt_architectureTree (pattern : Empty → SignType) (θ : Fin 2 → ℝ) :
    ParametricTree.RegularAt pattern θ architectureTree := by
  have hindicator : ∀ (index : Fin 2) (outcome : Bool),
      MvPolynomial.eval θ (indicatorQuotient index outcome).denominator ≠ 0 := by
    intro index outcome
    cases outcome <;> exact PolynomialQuotient.denominator_ofPolynomial_ne_zero _ θ
  exact ⟨fun architecture ↦ hindicator 0 architecture,
    fun _ ↦ ⟨fun environment ↦ hindicator 1 environment, fun _ ↦ trivial⟩⟩

/-- The architecture tree is a valid experiment at every point of the unit square. -/
theorem validAt_architectureTree (guard : Empty → MvPolynomial (Fin 2) ℝ) (θ : Fin 2 → ℝ)
    (h0a : 0 ≤ θ 0) (h1a : θ 0 ≤ 1) (h0e : 0 ≤ θ 1) (h1e : θ 1 ≤ 1) :
    ParametricTree.ValidAt guard θ architectureTree := by
  refine ⟨fun architecture ↦ ?_, ?_, fun _ ↦ ⟨fun environment ↦ ?_, ?_, fun _ ↦ trivial⟩⟩
  · cases architecture <;>
      simp only [eval_indicatorQuotient_true, eval_indicatorQuotient_false] <;> linarith
  · simp only [Fintype.sum_bool, eval_indicatorQuotient_true, eval_indicatorQuotient_false]
    ring
  · cases environment <;>
      simp only [eval_indicatorQuotient_true, eval_indicatorQuotient_false] <;> linarith
  · simp only [Fintype.sum_bool, eval_indicatorQuotient_true, eval_indicatorQuotient_false]
    ring

/-- The trace enumeration of a corner accumulator over the architecture tree is the mixture
average `ArchitectureEnvironmentRegion.mixtureNumerator` of NOTE2 (9). -/
theorem accumulation_architectureTree (guard : Empty → MvPolynomial (Fin 2) ℝ)
    (corner : Bool × Bool → ℝ) (θ : Fin 2 → ℝ) :
    ParametricTree.accumulation guard architectureTree (cornerAccumulator corner) θ =
      ArchitectureEnvironmentRegion.mixtureNumerator corner (θ 0) (θ 1) := by
  change ∑ trace : (Σ _architecture : Bool, Σ _environment : Bool, Unit),
      (indicatorQuotient 0 trace.1).eval θ * ((indicatorQuotient 1 trace.2.1).eval θ * 1) *
        (PolynomialQuotient.ofPolynomial (MvPolynomial.C (corner (trace.1, trace.2.1)))).eval θ =
    ∑ c, ArchitectureEnvironmentRegion.cellWeight (θ 0) (θ 1) c * corner c
  simp only [Fintype.sum_sigma, Fintype.sum_prod_type, Fintype.sum_bool, Finset.univ_unique,
    Finset.sum_singleton, eval_indicatorQuotient_true, eval_indicatorQuotient_false,
    PolynomialQuotient.eval_ofPolynomial, MvPolynomial.eval_C,
    ArchitectureEnvironmentRegion.cellWeight]
  ring

/-- **NOTE2 §3.2 is an instance of (8).** With every corner denominator positive, the attainable
region of the architecture tree over the unit square, for corner accumulators, is the corpus
joint region `ArchitectureEnvironmentRegion.jointRegion` of NOTE2 (10). -/
theorem attainableRegion_architectureTree_eq_jointRegion {J : Type} [Fintype J]
    (guard : Empty → MvPolynomial (Fin 2) ℝ) (num den : J → Bool × Bool → ℝ)
    (hden : ∀ j c, 0 < den j c) :
    attainableRegion {θ : Fin 2 → ℝ | θ 0 ∈ Set.Icc 0 1 ∧ θ 1 ∈ Set.Icc 0 1}
        (fun j ↦ ParametricTree.accumulation guard architectureTree (cornerAccumulator (den j)))
        (fun j ↦ ParametricTree.accumulation guard architectureTree (cornerAccumulator (num j))) =
      ArchitectureEnvironmentRegion.jointRegion num den := by
  rw [attainableRegion_eq_image, ArchitectureEnvironmentRegion.jointRegion_eq_image num den hden]
  simp only [accumulation_architectureTree]
  ext report
  constructor
  · rintro ⟨θ, ⟨⟨hα, hη⟩, _⟩, rfl⟩
    exact ⟨(θ 0, θ 1), ⟨hα, hη⟩, rfl⟩
  · rintro ⟨⟨α, η⟩, ⟨hα, hη⟩, rfl⟩
    refine ⟨![α, η], ⟨⟨hα, hη⟩, fun j ↦ ?_⟩, rfl⟩
    exact ArchitectureEnvironmentRegion.mixtureDenominator_pos (den j) (hden j) α η
      (Set.mem_Icc.mp hα).1 (Set.mem_Icc.mp hα).2 (Set.mem_Icc.mp hη).1 (Set.mem_Icc.mp hη).2

end

end Descent.Portability.RationalParameterReports
