/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.FiniteTraceTreeLaw
import Descent.Portability.ArchitectureEnvironmentRegion
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Data.Sign.Defs
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.Compact

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
parameter space (`iUnion_signCell`), and are finitely many (`finite_range_signCell`); the
partition claim of Theorem 2, that the report map is rational on every cell, is stated in one
theorem as `signCell_partition_rational_reports`. Presented
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
every metric, so globally shared parameters stay shared. The joint input-output graph
`reportGraph`, in the joint coordinates `σ ⊕ J` of parameters and reports, projects onto (8)
(`attainableRegion_eq_image_reportGraph`). Over any admissible set that is a union of guard
cells, the graph is the finite union over those cells of the sets cut out by the explicit
polynomial sign conditions `graphGuard` with signs `graphPattern`: the guards, the positivity
`D_num D_den > 0` of every presented definedness probability, and the polynomial equation
`D_num N_den r_j = N_num D_den` of every report coordinate
(`reportGraph_eq_iUnion_signCell`). This is the defining presentation of a semialgebraic set,
for every finite algebraic experiment, obtained without quantifier elimination. The two-by-two
architecture and environment region of NOTE2 §3.2 is an instance: `architectureTree` enumerates
the mixture averages of `ArchitectureEnvironmentRegion` (`accumulation_architectureTree`), and
its attainable region over the unit square is the corpus region `jointRegion` of NOTE2 (10)
(`attainableRegion_architectureTree_eq_jointRegion`). A non-degenerate instance, with a genuine
quotient probability and a genuine decision guard, is `selectionTree`: it draws the selected type
with the fitness-weighted probability `x w / (x w + 1 - x)` of NOTE2 (4), then takes the
advantage decision on the sign of `w - 1`. The normalizing total is itself a guard, so regularity
on the cells where it is positive is read off the pattern (`regularAt_selectionTree`); the
experiment is valid for `0 ≤ x < 1` and `w ≥ 0` (`validAt_selectionTree`); its selected-type
accumulation is the quotient of NOTE2 (4) whichever way the decision goes
(`accumulation_selectionTree_selected`); and its joint graph over those cells is the explicit
finite union (`reportGraph_selectionTree`).

Sharp bounds without quantifier elimination. When the admissible points with every definedness
probability positive form a compact set on which the report map is continuous, the attainable
region is compact (`isCompact_attainableRegion`) and every requested quantity attains its largest
and smallest attainable values (`exists_attained_bounds_attainableRegion`). The hypothesis sits on
the constrained set, not on the admissible set, as the note requires: excluding a zero-denominator
boundary can make the constrained set open. For a compact admissible set inside one sign cell,
with regular presentations and positive definedness, the report map is a presented quotient with
nonvanishing denominator, hence continuous, and the bounds are attained
(`exists_attained_bounds_of_compact_cell`). Worked instance: over the compact box `0 ≤ x ≤ 1/2`,
`3/2 ≤ w ≤ 2` of the selection experiment, which lies in one cell
(`selectionBox_subset_signCell`), the attainable selected-type probability lies in `[0, 2/3]` and
both bounds are attained, at `x = 0, w = 3/2` and at `x = 1/2, w = 2`
(`selectionRegion_bounds_attained`); the general theorem gives compactness of that region
(`isCompact_selectionRegion`).

Not formalized: Mathlib's notion of a semialgebraic set, and real quantifier elimination, which
the note uses to eliminate the parameters from the graph and so describe (8) without them,
establish sharp bounds, and decide attainment; neither is available at this Mathlib pin. The
partition here is by the signs of the supplied guards, and regularity of the presented
denominators at a point is a supplied hypothesis, not a refinement the module computes.
Algebraic roots, optimizers and transcendental primitives are outside the rational conclusion,
as the note states.

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

/-- Membership in a cell, written out guard by guard. -/
theorem mem_signCell_iff (guard : Guard → MvPolynomial σ ℝ) (pattern : Guard → SignType)
    (θ : σ → ℝ) :
    θ ∈ signCell guard pattern ↔
      ∀ index, SignType.sign (MvPolynomial.eval θ (guard index)) = pattern index :=
  ⟨fun hcell index ↦ congrFun hcell index, fun hsigns ↦ funext hsigns⟩

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

/-! ### The rational partition of parameter space -/

/-- **NOTE2 Theorem 2, the rational partition of parameter space.** The sign-condition cells of the
guards partition the parameter space: they cover it, the cells of distinct patterns are disjoint,
and there are finitely many. On each cell, at every regular point, every trace weight, the
definedness probability `d_j(θ)` and the numerator `n_j(θ)` of every requested quantity, and,
where `d_j(θ) > 0`, its conditional mean `n_j(θ) / d_j(θ)`, are the values of explicit presented
quotients of polynomials that depend only on the cell, with nonvanishing denominators. Assumes:
`RegularAt pattern θ tree` at the points it is applied to. -/
theorem signCell_partition_rational_reports [Finite Guard] {J : Type}
    (guard : Guard → MvPolynomial σ ℝ) (tree : ParametricTree σ Guard Report)
    (definedness numerator : J → Report → (Guard → SignType) → PolynomialQuotient σ) :
    (⋃ pattern, signCell guard pattern) = Set.univ ∧
      (∀ first second : Guard → SignType, first ≠ second →
        Disjoint (signCell guard first) (signCell guard second)) ∧
      (Set.range (signCell guard)).Finite ∧
      ∀ pattern, ∀ θ ∈ signCell guard pattern, ParametricTree.RegularAt pattern θ tree →
        (∀ j report, MvPolynomial.eval θ (definedness j report pattern).denominator ≠ 0 ∧
          MvPolynomial.eval θ (numerator j report pattern).denominator ≠ 0) →
        (∀ trace, ParametricTree.traceWeight guard θ tree trace =
            (ParametricTree.weightQuotient pattern tree trace).eval θ ∧
          MvPolynomial.eval θ (ParametricTree.weightQuotient pattern tree trace).denominator ≠
            0) ∧
        ∀ j, ParametricTree.accumulation guard tree (definedness j) θ =
              (ParametricTree.accumulationQuotient tree (definedness j) pattern).eval θ ∧
            ParametricTree.accumulation guard tree (numerator j) θ =
              (ParametricTree.accumulationQuotient tree (numerator j) pattern).eval θ ∧
            (0 < ParametricTree.accumulation guard tree (definedness j) θ →
              ParametricTree.accumulation guard tree (numerator j) θ /
                  ParametricTree.accumulation guard tree (definedness j) θ =
                ((ParametricTree.accumulationQuotient tree (numerator j) pattern).div
                  (ParametricTree.accumulationQuotient tree (definedness j) pattern)).eval θ ∧
              MvPolynomial.eval θ
                ((ParametricTree.accumulationQuotient tree (numerator j) pattern).div
                  (ParametricTree.accumulationQuotient tree (definedness j) pattern)).denominator ≠
                0) := by
  refine ⟨iUnion_signCell guard, fun _ _ hne ↦ disjoint_signCell guard hne,
    finite_range_signCell guard, fun pattern θ hcell hregular haccumulators ↦ ⟨fun trace ↦
      ⟨ParametricTree.traceWeight_eq_eval_weightQuotient guard pattern hcell tree trace,
        ParametricTree.denominator_weightQuotient_ne_zero pattern tree hregular trace⟩,
      fun j ↦ ⟨ParametricTree.accumulation_eq_eval_accumulationQuotient guard pattern hcell tree
          (definedness j) hregular fun report ↦ (haccumulators j report).1,
        ParametricTree.accumulation_eq_eval_accumulationQuotient guard pattern hcell tree
          (numerator j) hregular fun report ↦ (haccumulators j report).2,
        fun hpositive ↦ ParametricTree.conditionalMean_eq_eval_div guard pattern hcell tree
          (definedness j) (numerator j) hregular (fun report ↦ (haccumulators j report).1)
          (fun report ↦ (haccumulators j report).2) hpositive⟩⟩⟩

/-! ### The joint attainable region (8) -/

/-- **NOTE2 (8).** The exact joint attainable region: the report vectors `r` for which one
admissible parameter point has every definedness probability positive and `d_j(θ) r_j = n_j(θ)`
for every requested quantity `j`. -/
def attainableRegion {Parameter J : Type} (admissible : Set Parameter)
    (definedness numerator : J → Parameter → ℝ) : Set (J → ℝ) :=
  {report | ∃ θ ∈ admissible, ∀ j, 0 < definedness j θ ∧
    definedness j θ * report j = numerator j θ}

/-- The report map of NOTE2 (8): a parameter point's vector of requested conditional means
`θ ↦ (n_j(θ) / d_j(θ))_j`. -/
abbrev attainableReportMap {Parameter J : Type} (definedness numerator : J → Parameter → ℝ)
    (θ : Parameter) : J → ℝ :=
  fun j ↦ numerator j θ / definedness j θ

/-- **NOTE2 (8) is an image.** The attainable region is the image, under the report map
`attainableReportMap`, of the admissible points at which every definedness probability is
positive. -/
theorem attainableRegion_eq_image {Parameter J : Type} (admissible : Set Parameter)
    (definedness numerator : J → Parameter → ℝ) :
    attainableRegion admissible definedness numerator =
      attainableReportMap definedness numerator ''
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

/-! ### The joint input-output graph -/

/-- The joint input-output graph of NOTE2 Theorem 2 in the joint coordinates `σ ⊕ J`: the points
whose parameter part is admissible, with every definedness probability positive and
`d_j(θ) r_j = n_j(θ)` for the report part. -/
def reportGraph {J : Type} (admissible : Set (σ → ℝ))
    (definedness numerator : J → (σ → ℝ) → ℝ) : Set (σ ⊕ J → ℝ) :=
  {point | point ∘ Sum.inl ∈ admissible ∧ ∀ j, 0 < definedness j (point ∘ Sum.inl) ∧
    definedness j (point ∘ Sum.inl) * point (Sum.inr j) = numerator j (point ∘ Sum.inl)}

/-- **NOTE2 (8) is the projection of the graph.** The attainable region is the image of the joint
input-output graph under the projection onto the report coordinates. Describing it without the
parameters is the quantifier elimination this module does not formalize. -/
theorem attainableRegion_eq_image_reportGraph {J : Type} (admissible : Set (σ → ℝ))
    (definedness numerator : J → (σ → ℝ) → ℝ) :
    attainableRegion admissible definedness numerator =
      (fun point j ↦ point (Sum.inr j)) '' reportGraph admissible definedness numerator := by
  ext report
  constructor
  · rintro ⟨θ, hθ, hreport⟩
    exact ⟨Sum.elim θ report, ⟨hθ, hreport⟩, rfl⟩
  · rintro ⟨point, ⟨hθ, hreport⟩, rfl⟩
    exact ⟨point ∘ Sum.inl, hθ, hreport⟩

/-- The polynomial conditions in the joint coordinates that cut out the graph on the cell of one
guard pattern: the guards, the product of the numerator and denominator of every presented
definedness probability, and the defining equation of every report coordinate. -/
def graphGuard {J : Type} (guard : Guard → MvPolynomial σ ℝ)
    (tree : ParametricTree σ Guard Report)
    (definedness numerator : J → Report → (Guard → SignType) → PolynomialQuotient σ)
    (pattern : Guard → SignType) : Guard ⊕ J ⊕ J → MvPolynomial (σ ⊕ J) ℝ
  | Sum.inl index => MvPolynomial.rename Sum.inl (guard index)
  | Sum.inr (Sum.inl j) =>
      MvPolynomial.rename Sum.inl
        ((ParametricTree.accumulationQuotient tree (definedness j) pattern).numerator *
          (ParametricTree.accumulationQuotient tree (definedness j) pattern).denominator)
  | Sum.inr (Sum.inr j) =>
      MvPolynomial.rename Sum.inl
          ((ParametricTree.accumulationQuotient tree (definedness j) pattern).numerator *
            (ParametricTree.accumulationQuotient tree (numerator j) pattern).denominator) *
        MvPolynomial.X (Sum.inr j) -
      MvPolynomial.rename Sum.inl
        ((ParametricTree.accumulationQuotient tree (numerator j) pattern).numerator *
          (ParametricTree.accumulationQuotient tree (definedness j) pattern).denominator)

/-- The prescribed signs of the graph conditions: the pattern on the guards, `+1` on every
definedness product, and `0` on every defining equation. -/
def graphPattern {J : Type} (pattern : Guard → SignType) : Guard ⊕ J ⊕ J → SignType
  | Sum.inl index => pattern index
  | Sum.inr (Sum.inl _) => 1
  | Sum.inr (Sum.inr _) => 0

/-- Membership in the sign-condition set of the graph conditions, written out: the parameter part
lies in the guard cell, every presented definedness product is positive, and every report
coordinate satisfies its polynomial equation. -/
theorem mem_signCell_graphGuard_iff {J : Type} (guard : Guard → MvPolynomial σ ℝ)
    (tree : ParametricTree σ Guard Report)
    (definedness numerator : J → Report → (Guard → SignType) → PolynomialQuotient σ)
    (pattern : Guard → SignType) (point : σ ⊕ J → ℝ) :
    point ∈ signCell (graphGuard guard tree definedness numerator pattern)
        (graphPattern pattern) ↔
      point ∘ Sum.inl ∈ signCell guard pattern ∧
        ∀ j, 0 < MvPolynomial.eval (point ∘ Sum.inl)
              (ParametricTree.accumulationQuotient tree (definedness j) pattern).numerator *
            MvPolynomial.eval (point ∘ Sum.inl)
              (ParametricTree.accumulationQuotient tree (definedness j) pattern).denominator ∧
          MvPolynomial.eval (point ∘ Sum.inl)
                (ParametricTree.accumulationQuotient tree (definedness j) pattern).numerator *
              MvPolynomial.eval (point ∘ Sum.inl)
                (ParametricTree.accumulationQuotient tree (numerator j) pattern).denominator *
              point (Sum.inr j) =
            MvPolynomial.eval (point ∘ Sum.inl)
                (ParametricTree.accumulationQuotient tree (numerator j) pattern).numerator *
              MvPolynomial.eval (point ∘ Sum.inl)
                (ParametricTree.accumulationQuotient tree (definedness j) pattern).denominator := by
  simp only [mem_signCell_iff, Sum.forall, graphGuard, graphPattern, map_sub, map_mul,
    MvPolynomial.eval_rename, MvPolynomial.eval_X, sign_eq_one_iff, sign_eq_zero_iff, sub_eq_zero,
    forall_and]

/-- On the cell of a pattern, at a regular point, a report value satisfies the definedness and
defining equation of one requested quantity exactly when the presented polynomials satisfy the
positivity and the polynomial equation of the graph conditions. Assumes:
`RegularAt pattern θ tree`. -/
theorem accumulation_region_iff_polynomial (guard : Guard → MvPolynomial σ ℝ)
    (pattern : Guard → SignType) {θ : σ → ℝ} (hcell : θ ∈ signCell guard pattern)
    (tree : ParametricTree σ Guard Report)
    (definedness numerator : Report → (Guard → SignType) → PolynomialQuotient σ)
    (hregular : ParametricTree.RegularAt pattern θ tree)
    (hdefinedness : ∀ report, MvPolynomial.eval θ (definedness report pattern).denominator ≠ 0)
    (hnumerator : ∀ report, MvPolynomial.eval θ (numerator report pattern).denominator ≠ 0)
    (value : ℝ) :
    (0 < ParametricTree.accumulation guard tree definedness θ ∧
        ParametricTree.accumulation guard tree definedness θ * value =
          ParametricTree.accumulation guard tree numerator θ) ↔
      (0 < MvPolynomial.eval θ
            (ParametricTree.accumulationQuotient tree definedness pattern).numerator *
          MvPolynomial.eval θ
            (ParametricTree.accumulationQuotient tree definedness pattern).denominator ∧
        MvPolynomial.eval θ
              (ParametricTree.accumulationQuotient tree definedness pattern).numerator *
            MvPolynomial.eval θ
              (ParametricTree.accumulationQuotient tree numerator pattern).denominator * value =
          MvPolynomial.eval θ
              (ParametricTree.accumulationQuotient tree numerator pattern).numerator *
            MvPolynomial.eval θ
              (ParametricTree.accumulationQuotient tree definedness pattern).denominator) := by
  have hD := ParametricTree.accumulation_eq_eval_accumulationQuotient guard pattern hcell tree
    definedness hregular hdefinedness
  have hN := ParametricTree.accumulation_eq_eval_accumulationQuotient guard pattern hcell tree
    numerator hregular hnumerator
  have hDd := ParametricTree.denominator_accumulationQuotient_ne_zero tree definedness pattern
    hregular hdefinedness
  have hNd := ParametricTree.denominator_accumulationQuotient_ne_zero tree numerator pattern
    hregular hnumerator
  rw [hD, hN]
  simp only [PolynomialQuotient.eval]
  constructor
  · rintro ⟨hpositive, hequation⟩
    refine ⟨mul_pos_iff.mpr (div_pos_iff.mp hpositive), ?_⟩
    rw [div_mul_eq_mul_div, div_eq_div_iff hDd hNd] at hequation
    linear_combination hequation
  · rintro ⟨hpositive, hequation⟩
    refine ⟨div_pos_iff.mpr (mul_pos_iff.mp hpositive), ?_⟩
    rw [div_mul_eq_mul_div, div_eq_div_iff hDd hNd]
    linear_combination hequation

/-- **NOTE2 Theorem 2, the joint input-output graph is semialgebraic, by explicit presentation.**
Let the admissible set be the union of the cells of a set of guard patterns, with the presented
probabilities and accumulators regular on those cells. Then the joint input-output graph is the
finite union, over those patterns, of the sets cut out in the joint coordinates by the explicit
polynomial sign conditions `graphGuard` with the signs `graphPattern`. Assumes:
`RegularAt pattern θ tree` on every admissible cell. -/
theorem reportGraph_eq_iUnion_signCell {J : Type} (guard : Guard → MvPolynomial σ ℝ)
    (tree : ParametricTree σ Guard Report)
    (definedness numerator : J → Report → (Guard → SignType) → PolynomialQuotient σ)
    (patterns : Set (Guard → SignType))
    (hregular : ∀ pattern ∈ patterns, ∀ θ ∈ signCell guard pattern,
      ParametricTree.RegularAt pattern θ tree ∧ ∀ j report,
        MvPolynomial.eval θ (definedness j report pattern).denominator ≠ 0 ∧
          MvPolynomial.eval θ (numerator j report pattern).denominator ≠ 0) :
    reportGraph (⋃ pattern ∈ patterns, signCell guard pattern)
        (fun j ↦ ParametricTree.accumulation guard tree (definedness j))
        (fun j ↦ ParametricTree.accumulation guard tree (numerator j)) =
      ⋃ pattern ∈ patterns,
        signCell (graphGuard guard tree definedness numerator pattern) (graphPattern pattern) := by
  ext point
  simp only [reportGraph, Set.mem_setOf_eq, Set.mem_iUnion, exists_prop,
    mem_signCell_graphGuard_iff]
  constructor
  · rintro ⟨⟨pattern, hpattern, hcell⟩, hreport⟩
    obtain ⟨hregularAt, hden⟩ := hregular pattern hpattern _ hcell
    exact ⟨pattern, hpattern, hcell, fun j ↦
      (accumulation_region_iff_polynomial guard pattern hcell tree (definedness j) (numerator j)
        hregularAt (fun report ↦ (hden j report).1) (fun report ↦ (hden j report).2)
        (point (Sum.inr j))).mp (hreport j)⟩
  · rintro ⟨pattern, hpattern, hcell, hgraph⟩
    obtain ⟨hregularAt, hden⟩ := hregular pattern hpattern _ hcell
    exact ⟨⟨pattern, hpattern, hcell⟩, fun j ↦
      (accumulation_region_iff_polynomial guard pattern hcell tree (definedness j) (numerator j)
        hregularAt (fun report ↦ (hden j report).1) (fun report ↦ (hden j report).2)
        (point (Sum.inr j))).mpr (hgraph j)⟩

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
  have hmap : attainableReportMap
      (fun j ↦ ParametricTree.accumulation guard architectureTree (cornerAccumulator (den j)))
      (fun j ↦ ParametricTree.accumulation guard architectureTree (cornerAccumulator (num j))) =
        fun θ j ↦
          ParametricTree.accumulation guard architectureTree (cornerAccumulator (num j)) θ /
            ParametricTree.accumulation guard architectureTree (cornerAccumulator (den j)) θ :=
    rfl
  rw [attainableRegion_eq_image, hmap,
    ArchitectureEnvironmentRegion.jointRegion_eq_image num den hden]
  simp only [accumulation_architectureTree]
  ext report
  constructor
  · rintro ⟨θ, ⟨⟨hα, hη⟩, _⟩, rfl⟩
    exact ⟨(θ 0, θ 1), ⟨hα, hη⟩, rfl⟩
  · rintro ⟨⟨α, η⟩, ⟨hα, hη⟩, rfl⟩
    refine ⟨![α, η], ⟨⟨hα, hη⟩, fun j ↦ ?_⟩, rfl⟩
    exact ArchitectureEnvironmentRegion.mixtureDenominator_pos (den j) (hden j) α η
      (Set.mem_Icc.mp hα).1 (Set.mem_Icc.mp hα).2 (Set.mem_Icc.mp hη).1 (Set.mem_Icc.mp hη).2

/-! ### A non-degenerate instance: fitness-weighted selection with a decision guard -/

/-- The guards of the selection experiment in the coordinates `θ 0 = x`, the frequency of the
selected type, and `θ 1 = w`, its relative fitness. The guard `false` is the normalizing total
`x w + 1 - x` of NOTE2 (4); the guard `true` is the advantage contrast `w - 1`. -/
def selectionGuard : Bool → MvPolynomial (Fin 2) ℝ :=
  fun index ↦ if index then MvPolynomial.X 1 - 1
    else MvPolynomial.X 0 * MvPolynomial.X 1 + 1 - MvPolynomial.X 0

/-- The fitness-weighted selection probabilities of NOTE2 (4) as presented quotients: the
selected type with probability `x w / (x w + 1 - x)`, the other with `(1 - x) / (x w + 1 - x)`. -/
def selectionQuotient : Bool → PolynomialQuotient (Fin 2)
  | true => ⟨MvPolynomial.X 0 * MvPolynomial.X 1,
      MvPolynomial.X 0 * MvPolynomial.X 1 + 1 - MvPolynomial.X 0⟩
  | false => ⟨1 - MvPolynomial.X 0,
      MvPolynomial.X 0 * MvPolynomial.X 1 + 1 - MvPolynomial.X 0⟩

/-- The selected type is drawn with probability `x w / (x w + 1 - x)`. -/
theorem eval_selectionQuotient_true (θ : Fin 2 → ℝ) :
    (selectionQuotient true).eval θ = θ 0 * θ 1 / (θ 0 * θ 1 + 1 - θ 0) := by
  simp only [selectionQuotient, PolynomialQuotient.eval, map_mul, map_add, map_sub, map_one,
    MvPolynomial.eval_X]

/-- The other type is drawn with probability `(1 - x) / (x w + 1 - x)`. -/
theorem eval_selectionQuotient_false (θ : Fin 2 → ℝ) :
    (selectionQuotient false).eval θ = (1 - θ 0) / (θ 0 * θ 1 + 1 - θ 0) := by
  simp only [selectionQuotient, PolynomialQuotient.eval, map_mul, map_add, map_sub, map_one,
    MvPolynomial.eval_X]

/-- A decision taken by a polynomial sign condition, presented per cell: the branch that agrees
with the decision has probability `1` and the other `0`. -/
def decisionQuotient (decision branch : Bool) : PolynomialQuotient (Fin 2) :=
  if branch = decision then PolynomialQuotient.ofPolynomial 1
  else PolynomialQuotient.ofPolynomial 0

/-- A presented decision evaluates to the indicator of agreement. -/
theorem eval_decisionQuotient (decision branch : Bool) (θ : Fin 2 → ℝ) :
    (decisionQuotient decision branch).eval θ = if branch = decision then 1 else 0 := by
  simp only [decisionQuotient]
  split_ifs <;> simp only [PolynomialQuotient.eval_ofPolynomial, map_one, map_zero]

/-- NOTE2 (4) with a decision guard: draw the selected type with the fitness-weighted probability,
then take the advantage decision `w > 1` on the sign of the guard `w - 1`, reporting both. -/
def selectionTree : ParametricTree (Fin 2) Bool (Bool × Bool) :=
  .node Bool (fun _ selected ↦ selectionQuotient selected) fun selected ↦
    .node Bool (fun pattern advantaged ↦ decisionQuotient (decide (pattern true = 1)) advantaged)
      fun advantaged ↦ .leaf (selected, advantaged)

/-- On every cell where the normalizing total is positive the selection experiment is regular:
its only non-unit denominator is that total, whose sign the pattern prescribes. -/
theorem regularAt_selectionTree (pattern : Bool → SignType) (hpattern : pattern false = 1)
    {θ : Fin 2 → ℝ} (hcell : θ ∈ signCell selectionGuard pattern) :
    ParametricTree.RegularAt pattern θ selectionTree := by
  have htotal : 0 < θ 0 * θ 1 + 1 - θ 0 := by
    have h := (mem_signCell_iff selectionGuard pattern θ).mp hcell false
    rw [hpattern, sign_eq_one_iff] at h
    simpa only [selectionGuard, Bool.false_eq_true, if_false, map_sub, map_add, map_mul, map_one,
      MvPolynomial.eval_X] using h
  have hden : MvPolynomial.eval θ (selectionQuotient true).denominator ≠ 0 := by
    simp only [selectionQuotient, map_sub, map_add, map_mul, map_one, MvPolynomial.eval_X]
    exact htotal.ne'
  have hselection : ∀ selected,
      MvPolynomial.eval θ (selectionQuotient selected).denominator ≠ 0 := by
    intro selected
    cases selected <;> exact hden
  have hdecision : ∀ decision branch,
      MvPolynomial.eval θ (decisionQuotient decision branch).denominator ≠ 0 := by
    intro decision branch
    simp only [decisionQuotient]
    split_ifs <;> exact PolynomialQuotient.denominator_ofPolynomial_ne_zero _ θ
  exact ⟨hselection, fun _ ↦ ⟨fun branch ↦ hdecision _ branch, fun _ ↦ trivial⟩⟩

/-- The selection experiment is valid at every point with `0 ≤ x < 1` and `w ≥ 0`. -/
theorem validAt_selectionTree {θ : Fin 2 → ℝ} (h0x : 0 ≤ θ 0) (h1x : θ 0 < 1) (h0w : 0 ≤ θ 1) :
    ParametricTree.ValidAt selectionGuard θ selectionTree := by
  have htotal : 0 < θ 0 * θ 1 + 1 - θ 0 := by nlinarith
  refine ⟨fun selected ↦ ?_, ?_, fun _ ↦ ⟨fun advantaged ↦ ?_, ?_, fun _ ↦ trivial⟩⟩
  · cases selected
    · simp only [eval_selectionQuotient_false]
      exact div_nonneg (by linarith) htotal.le
    · simp only [eval_selectionQuotient_true]
      exact div_nonneg (mul_nonneg h0x h0w) htotal.le
  · simp only [Fintype.sum_bool, eval_selectionQuotient_true, eval_selectionQuotient_false]
    rw [← add_div, div_eq_one_iff_eq htotal.ne']
    ring
  · simp only [eval_decisionQuotient]
    split_ifs <;> norm_num
  · simp only [Fintype.sum_bool, eval_decisionQuotient]
    cases decide (signPattern selectionGuard θ true = 1) <;> simp

/-- The trace enumeration of the selected-type indicator over the selection experiment is the
fitness-weighted probability `x w / (x w + 1 - x)` of NOTE2 (4), whichever way the decision goes. -/
theorem accumulation_selectionTree_selected (θ : Fin 2 → ℝ) :
    ParametricTree.accumulation selectionGuard selectionTree
        (fun report _ ↦ PolynomialQuotient.ofPolynomial (if report.1 then 1 else 0)) θ =
      θ 0 * θ 1 / (θ 0 * θ 1 + 1 - θ 0) := by
  change ∑ trace : (Σ _selected : Bool, Σ _advantaged : Bool, Unit),
      (selectionQuotient trace.1).eval θ *
          ((decisionQuotient (decide (signPattern selectionGuard θ true = 1)) trace.2.1).eval θ *
            1) *
        (PolynomialQuotient.ofPolynomial (if trace.1 then 1 else 0)).eval θ = _
  obtain ⟨decision, hdecision⟩ :
      ∃ decision, decide (signPattern selectionGuard θ true = 1) = decision := ⟨_, rfl⟩
  rw [hdecision]
  cases decision <;>
    simp [Fintype.sum_sigma, Finset.univ_unique, Finset.sum_singleton, eval_decisionQuotient,
      PolynomialQuotient.eval_ofPolynomial, eval_selectionQuotient_true]

/-- **NOTE2 Theorem 2, a non-degenerate instance.** For the selection experiment with its
decision guard and any finite family of requested quantities with polynomial accumulators, the
joint input-output graph over the cells where the normalizing total is positive is the explicit
finite union of polynomial sign-condition sets. -/
theorem reportGraph_selectionTree {J : Type}
    (definedness numerator : J → Bool × Bool → (Bool → SignType) → MvPolynomial (Fin 2) ℝ) :
    reportGraph (⋃ pattern ∈ {pattern : Bool → SignType | pattern false = 1},
          signCell selectionGuard pattern)
        (fun j ↦ ParametricTree.accumulation selectionGuard selectionTree
          (fun report pattern ↦ PolynomialQuotient.ofPolynomial (definedness j report pattern)))
        (fun j ↦ ParametricTree.accumulation selectionGuard selectionTree
          (fun report pattern ↦ PolynomialQuotient.ofPolynomial (numerator j report pattern))) =
      ⋃ pattern ∈ {pattern : Bool → SignType | pattern false = 1},
        signCell (graphGuard selectionGuard selectionTree
            (fun j report pattern ↦ PolynomialQuotient.ofPolynomial (definedness j report pattern))
            (fun j report pattern ↦ PolynomialQuotient.ofPolynomial (numerator j report pattern))
            pattern)
          (graphPattern pattern) :=
  reportGraph_eq_iUnion_signCell selectionGuard selectionTree _ _ _
    fun pattern hpattern θ hcell ↦ ⟨regularAt_selectionTree pattern hpattern hcell, fun _ _ ↦
      ⟨PolynomialQuotient.denominator_ofPolynomial_ne_zero _ θ,
        PolynomialQuotient.denominator_ofPolynomial_ne_zero _ θ⟩⟩

/-! ### Sharp bounds attained on compact constrained sets -/

/-- A presented quotient is continuous on every set where its denominator does not vanish. -/
theorem PolynomialQuotient.continuousOn_eval (quotient : PolynomialQuotient σ)
    (region : Set (σ → ℝ))
    (hden : ∀ θ ∈ region, MvPolynomial.eval θ quotient.denominator ≠ 0) :
    ContinuousOn (fun θ ↦ quotient.eval θ) region :=
  (MvPolynomial.continuous_eval (p := quotient.numerator)).continuousOn.div
    (MvPolynomial.continuous_eval (p := quotient.denominator)).continuousOn hden

/-- **NOTE2 (8) on a compact constrained set.** If the admissible points at which every
definedness probability is positive form a compact set on which the report map is continuous, the
attainable region is compact. The hypothesis is on the constrained set, not on the admissible set:
excluding a zero-denominator boundary can make the constrained set open. -/
theorem isCompact_attainableRegion {Parameter J : Type} [TopologicalSpace Parameter]
    (admissible : Set Parameter) (definedness numerator : J → Parameter → ℝ)
    (hcompact : IsCompact {θ | θ ∈ admissible ∧ ∀ j, 0 < definedness j θ})
    (hcontinuous : ContinuousOn (fun θ j ↦ numerator j θ / definedness j θ)
      {θ | θ ∈ admissible ∧ ∀ j, 0 < definedness j θ}) :
    IsCompact (attainableRegion admissible definedness numerator) := by
  rw [attainableRegion_eq_image]
  exact hcompact.image_of_continuousOn hcontinuous

/-- **Sharp bounds are attained.** Under the same hypotheses, when some admissible point has every
definedness probability positive, every requested quantity attains both its largest and its
smallest attainable value. -/
theorem exists_attained_bounds_attainableRegion {Parameter J : Type} [TopologicalSpace Parameter]
    (admissible : Set Parameter) (definedness numerator : J → Parameter → ℝ)
    (hcompact : IsCompact {θ | θ ∈ admissible ∧ ∀ j, 0 < definedness j θ})
    (hcontinuous : ContinuousOn (fun θ j ↦ numerator j θ / definedness j θ)
      {θ | θ ∈ admissible ∧ ∀ j, 0 < definedness j θ})
    (hnonempty : {θ | θ ∈ admissible ∧ ∀ j, 0 < definedness j θ}.Nonempty) (j : J) :
    (∃ report ∈ attainableRegion admissible definedness numerator,
        ∀ other ∈ attainableRegion admissible definedness numerator, other j ≤ report j) ∧
      ∃ report ∈ attainableRegion admissible definedness numerator,
        ∀ other ∈ attainableRegion admissible definedness numerator, report j ≤ other j := by
  have hregion := isCompact_attainableRegion admissible definedness numerator hcompact
    hcontinuous
  have hne : (attainableRegion admissible definedness numerator).Nonempty := by
    rw [attainableRegion_eq_image]
    exact hnonempty.image _
  obtain ⟨top, htop, hmax⟩ := hregion.exists_isMaxOn hne (continuous_apply j).continuousOn
  obtain ⟨bottom, hbottom, hmin⟩ := hregion.exists_isMinOn hne (continuous_apply j).continuousOn
  exact ⟨⟨top, htop, fun other hother ↦ hmax hother⟩,
    ⟨bottom, hbottom, fun other hother ↦ hmin hother⟩⟩

/-- **Polynomial reports on a compact cell attain their sharp bounds.** Let a nonempty compact
admissible set lie in one sign cell, with the presented probabilities and accumulators regular and
every definedness accumulation positive there. Then the report map is a presented quotient with
nonvanishing denominator, hence continuous; the attainable region is compact; and every requested
quantity attains its largest and smallest attainable values. Assumes: `RegularAt pattern θ tree`
on the admissible set. -/
theorem exists_attained_bounds_of_compact_cell {J : Type} (guard : Guard → MvPolynomial σ ℝ)
    (tree : ParametricTree σ Guard Report)
    (definedness numerator : J → Report → (Guard → SignType) → PolynomialQuotient σ)
    (pattern : Guard → SignType) (admissible : Set (σ → ℝ))
    (hsubset : admissible ⊆ signCell guard pattern) (hcompact : IsCompact admissible)
    (hnonempty : admissible.Nonempty)
    (hregular : ∀ θ ∈ admissible, ParametricTree.RegularAt pattern θ tree ∧ ∀ j report,
      MvPolynomial.eval θ (definedness j report pattern).denominator ≠ 0 ∧
        MvPolynomial.eval θ (numerator j report pattern).denominator ≠ 0)
    (hpositive : ∀ θ ∈ admissible, ∀ j,
      0 < ParametricTree.accumulation guard tree (definedness j) θ) (j : J) :
    IsCompact (attainableRegion admissible
        (fun quantity ↦ ParametricTree.accumulation guard tree (definedness quantity))
        (fun quantity ↦ ParametricTree.accumulation guard tree (numerator quantity))) ∧
      (∃ report ∈ attainableRegion admissible
          (fun quantity ↦ ParametricTree.accumulation guard tree (definedness quantity))
          (fun quantity ↦ ParametricTree.accumulation guard tree (numerator quantity)),
        ∀ other ∈ attainableRegion admissible
          (fun quantity ↦ ParametricTree.accumulation guard tree (definedness quantity))
          (fun quantity ↦ ParametricTree.accumulation guard tree (numerator quantity)),
          other j ≤ report j) ∧
      ∃ report ∈ attainableRegion admissible
          (fun quantity ↦ ParametricTree.accumulation guard tree (definedness quantity))
          (fun quantity ↦ ParametricTree.accumulation guard tree (numerator quantity)),
        ∀ other ∈ attainableRegion admissible
          (fun quantity ↦ ParametricTree.accumulation guard tree (definedness quantity))
          (fun quantity ↦ ParametricTree.accumulation guard tree (numerator quantity)),
          report j ≤ other j := by
  have hconstrained : {θ | θ ∈ admissible ∧
      ∀ quantity, 0 < ParametricTree.accumulation guard tree (definedness quantity) θ} =
        admissible :=
    Set.ext fun θ ↦ ⟨fun hθ ↦ hθ.1, fun hθ ↦ ⟨hθ, hpositive θ hθ⟩⟩
  have hcontinuous : ContinuousOn
      (fun θ quantity ↦ ParametricTree.accumulation guard tree (numerator quantity) θ /
        ParametricTree.accumulation guard tree (definedness quantity) θ) admissible := by
    refine continuousOn_pi.mpr fun quantity ↦ ?_
    have hmean : ∀ θ ∈ admissible,
        ParametricTree.accumulation guard tree (numerator quantity) θ /
            ParametricTree.accumulation guard tree (definedness quantity) θ =
          ((ParametricTree.accumulationQuotient tree (numerator quantity) pattern).div
            (ParametricTree.accumulationQuotient tree (definedness quantity) pattern)).eval θ ∧
        MvPolynomial.eval θ ((ParametricTree.accumulationQuotient tree (numerator quantity)
          pattern).div (ParametricTree.accumulationQuotient tree (definedness quantity)
            pattern)).denominator ≠ 0 :=
      fun θ hθ ↦ ParametricTree.conditionalMean_eq_eval_div guard pattern (hsubset hθ) tree
        (definedness quantity) (numerator quantity) (hregular θ hθ).1
        (fun report ↦ ((hregular θ hθ).2 quantity report).1)
        (fun report ↦ ((hregular θ hθ).2 quantity report).2) (hpositive θ hθ quantity)
    exact (PolynomialQuotient.continuousOn_eval
      ((ParametricTree.accumulationQuotient tree (numerator quantity) pattern).div
        (ParametricTree.accumulationQuotient tree (definedness quantity) pattern))
      admissible fun θ hθ ↦ (hmean θ hθ).2).congr fun θ hθ ↦ (hmean θ hθ).1
  rw [← hconstrained] at hcompact hnonempty hcontinuous
  exact ⟨isCompact_attainableRegion admissible
      (fun quantity ↦ ParametricTree.accumulation guard tree (definedness quantity))
      (fun quantity ↦ ParametricTree.accumulation guard tree (numerator quantity))
      hcompact hcontinuous,
    exists_attained_bounds_attainableRegion admissible
      (fun quantity ↦ ParametricTree.accumulation guard tree (definedness quantity))
      (fun quantity ↦ ParametricTree.accumulation guard tree (numerator quantity))
      hcompact hcontinuous hnonempty j⟩

/-- At a valid point the trace enumeration of the constant accumulator `1` is `1`: the chain-rule
weights sum to one. Assumes: `ValidAt guard θ tree`. -/
theorem ParametricTree.accumulation_const_one (guard : Guard → MvPolynomial σ ℝ) (θ : σ → ℝ)
    (tree : ParametricTree σ Guard Report) (hvalid : ParametricTree.ValidAt guard θ tree) :
    ParametricTree.accumulation guard tree (fun _ _ ↦ PolynomialQuotient.ofPolynomial 1) θ =
      1 := by
  have h := ParametricTree.backwardValue_experimentAt guard θ tree hvalid fun _ ↦ 1
  rw [TraceTree.backwardValue_const] at h
  simp only [ParametricTree.accumulation, PolynomialQuotient.eval_ofPolynomial, map_one]
  exact h.symm

/-- The compact parameter box `0 ≤ x ≤ 1/2`, `3/2 ≤ w ≤ 2` of the selection experiment. -/
def selectionBox : Set (Fin 2 → ℝ) :=
  Set.Icc ![0, 3 / 2] ![1 / 2, 2]

/-- Membership in the box, coordinate by coordinate. -/
theorem mem_selectionBox_iff (θ : Fin 2 → ℝ) :
    θ ∈ selectionBox ↔ (0 ≤ θ 0 ∧ θ 0 ≤ 1 / 2) ∧ 3 / 2 ≤ θ 1 ∧ θ 1 ≤ 2 := by
  simp only [selectionBox, Set.mem_Icc, Pi.le_def, Fin.forall_fin_two, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  constructor
  · rintro ⟨⟨h0x, h0w⟩, h1x, h1w⟩
    exact ⟨⟨h0x, h1x⟩, h0w, h1w⟩
  · rintro ⟨⟨h0x, h1x⟩, h0w, h1w⟩
    exact ⟨⟨h0x, h0w⟩, h1x, h1w⟩

/-- The box is compact. -/
theorem isCompact_selectionBox : IsCompact selectionBox :=
  isCompact_Icc

/-- The lower corner `x = 0`, `w = 3/2` lies in the box. -/
theorem lowerCorner_mem_selectionBox : (![0, 3 / 2] : Fin 2 → ℝ) ∈ selectionBox :=
  (mem_selectionBox_iff _).mpr ⟨⟨by norm_num, by norm_num⟩, by norm_num, by norm_num⟩

/-- The upper corner `x = 1/2`, `w = 2` lies in the box. -/
theorem upperCorner_mem_selectionBox : (![1 / 2, 2] : Fin 2 → ℝ) ∈ selectionBox :=
  (mem_selectionBox_iff _).mpr ⟨⟨by norm_num, by norm_num⟩, by norm_num, by norm_num⟩

/-- The box lies in one cell: the normalizing total and the advantage contrast are both positive
there. -/
theorem selectionBox_subset_signCell : selectionBox ⊆ signCell selectionGuard fun _ ↦ 1 := by
  intro θ hθ
  obtain ⟨⟨h0x, h1x⟩, h0w, h1w⟩ := (mem_selectionBox_iff θ).mp hθ
  refine (mem_signCell_iff selectionGuard _ θ).mpr fun index ↦ sign_pos ?_
  cases index
  · simp only [selectionGuard, Bool.false_eq_true, if_false, map_sub, map_add, map_mul, map_one,
      MvPolynomial.eval_X]
    nlinarith
  · simp only [selectionGuard, if_true, map_sub, map_one, MvPolynomial.eval_X]
    linarith

/-- The selection experiment is valid at every point of the box. -/
theorem validAt_of_mem_selectionBox {θ : Fin 2 → ℝ} (hθ : θ ∈ selectionBox) :
    ParametricTree.ValidAt selectionGuard θ selectionTree := by
  obtain ⟨⟨h0x, h1x⟩, h0w, h1w⟩ := (mem_selectionBox_iff θ).mp hθ
  exact validAt_selectionTree h0x (by linarith) (by linarith)

/-- On the box the selected-type probability lies in `[0, 2/3]`. -/
theorem selectionQuotient_true_mem_Icc {θ : Fin 2 → ℝ} (hθ : θ ∈ selectionBox) :
    (selectionQuotient true).eval θ ∈ Set.Icc 0 (2 / 3) := by
  obtain ⟨⟨h0x, h1x⟩, h0w, h1w⟩ := (mem_selectionBox_iff θ).mp hθ
  have htotal : 0 < θ 0 * θ 1 + 1 - θ 0 := by nlinarith
  rw [eval_selectionQuotient_true]
  refine ⟨div_nonneg (by nlinarith) htotal.le, ?_⟩
  rw [div_le_iff₀ htotal]
  nlinarith

/-- The lower bound `0` is attained at the lower corner. -/
theorem eval_selectionQuotient_true_lowerCorner :
    (selectionQuotient true).eval ![0, 3 / 2] = 0 := by
  rw [eval_selectionQuotient_true]
  norm_num

/-- The upper bound `2/3` is attained at the upper corner. -/
theorem eval_selectionQuotient_true_upperCorner :
    (selectionQuotient true).eval ![1 / 2, 2] = 2 / 3 := by
  rw [eval_selectionQuotient_true]
  norm_num

/-- The attainable region (8) of the selected-type probability of the selection experiment over
the box: one requested quantity, always defined, whose numerator is the selected-type
indicator. -/
def selectionRegion : Set (Unit → ℝ) :=
  attainableRegion selectionBox
    (fun _ ↦ ParametricTree.accumulation selectionGuard selectionTree
      fun _ _ ↦ PolynomialQuotient.ofPolynomial 1)
    (fun _ ↦ ParametricTree.accumulation selectionGuard selectionTree
      fun report _ ↦ PolynomialQuotient.ofPolynomial (if report.1 then 1 else 0))

/-- The selected-type probability at any point of the box is an attainable report. -/
theorem selectionQuotient_true_mem_selectionRegion {θ : Fin 2 → ℝ} (hθ : θ ∈ selectionBox) :
    (fun _ ↦ (selectionQuotient true).eval θ) ∈ selectionRegion := by
  refine ⟨θ, hθ, fun _ ↦ ?_⟩
  dsimp only
  rw [ParametricTree.accumulation_const_one selectionGuard θ selectionTree
    (validAt_of_mem_selectionBox hθ), accumulation_selectionTree_selected,
    eval_selectionQuotient_true]
  exact ⟨one_pos, one_mul _⟩

/-- **A worked instance of attained sharp bounds.** Over the compact box the attainable
selected-type probability lies in `[0, 2/3]`, and both bounds are attained: `0` at `x = 0`,
`w = 3/2`, and `2/3` at `x = 1/2`, `w = 2`. -/
theorem selectionRegion_bounds_attained :
    (∀ report ∈ selectionRegion, report () ∈ Set.Icc 0 (2 / 3)) ∧
      (fun _ ↦ 0) ∈ selectionRegion ∧ (fun _ ↦ 2 / 3) ∈ selectionRegion := by
  refine ⟨?_, ?_, ?_⟩
  · rintro report ⟨θ, hθ, hreport⟩
    obtain ⟨_, hequation⟩ := hreport ()
    dsimp only at hequation
    rw [ParametricTree.accumulation_const_one selectionGuard θ selectionTree
      (validAt_of_mem_selectionBox hθ), one_mul, accumulation_selectionTree_selected,
      ← eval_selectionQuotient_true] at hequation
    rw [hequation]
    exact selectionQuotient_true_mem_Icc hθ
  · have h := selectionQuotient_true_mem_selectionRegion lowerCorner_mem_selectionBox
    rwa [eval_selectionQuotient_true_lowerCorner] at h
  · have h := selectionQuotient_true_mem_selectionRegion upperCorner_mem_selectionBox
    rwa [eval_selectionQuotient_true_upperCorner] at h

/-- The general attainment theorem applies to the worked instance: its attainable region is
compact. -/
theorem isCompact_selectionRegion : IsCompact selectionRegion :=
  (exists_attained_bounds_of_compact_cell selectionGuard selectionTree
    (fun _ _ _ ↦ PolynomialQuotient.ofPolynomial 1)
    (fun _ report _ ↦ PolynomialQuotient.ofPolynomial (if report.1 then 1 else 0))
    (fun _ ↦ 1) selectionBox selectionBox_subset_signCell isCompact_selectionBox
    ⟨_, lowerCorner_mem_selectionBox⟩
    (fun θ hθ ↦ ⟨regularAt_selectionTree _ rfl (selectionBox_subset_signCell hθ), fun _ _ ↦
      ⟨PolynomialQuotient.denominator_ofPolynomial_ne_zero _ θ,
        PolynomialQuotient.denominator_ofPolynomial_ne_zero _ θ⟩⟩)
    (fun θ hθ _ ↦ by
      rw [ParametricTree.accumulation_const_one selectionGuard θ selectionTree
        (validAt_of_mem_selectionBox hθ)]
      exact one_pos) ()).1

end

end Descent.Portability.RationalParameterReports
