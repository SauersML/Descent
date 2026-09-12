/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Layer
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Complex.ExponentialBounds

assert_below Descent.PopGen Descent.Spectral Descent.Blindness Descent.Conditionals
assert_below Descent.Portability Descent.Decision Descent.Program

/-!
# The genomic light cone as a coupling

`ANCESTRAL_LOCALITY.md` §9. The sampling dual of the neutral model with local compatibility
checks is an ancestral decision circuit, and the circuit reads only the coordinates its support
tags have reached. Corollary 8.1 turns that locality into a total-variation bound: two sample laws
obtained by evaluating the same circuit on inputs that agree wherever the circuit reads before it
escapes are within total variation the probability of escape.

The coupling is stated on a common finite probability space. The circuit randomness `ω` carries
nonnegative weights, and on each `ω` the circuit evaluated on an input is a finite law on samples
(`mixtureLaw`). When the evaluations on two inputs coincide off an escape event, the two sample
laws are within total variation (`totalVariation`) the probability of that event
(`totalVariation_mixtureLaw_le`); for deterministic outputs this is the coupling inequality
(`totalVariation_pointLaw_le`). A circuit whose evaluation depends only on the coordinates it has
inspected, run on inputs that agree on a ball, gives the bound with the escape event that some
inspected coordinate lies outside the ball (`totalVariation_local_le`), which is (9.3). For a test
function bounded by `B` the two expectations differ by at most `2 B Pr(escape)`
(`abs_sum_mul_mixtureLaw_sub_le`), the error term of the §10 approximation.

The truncation form is stated for the support-tag circuit of (7.6). A decision along `i → j` on an
argument whose support contains `i` adds `j` to that support and a parent with support `{i, j}`,
and is omitted otherwise; a coalescence unites two supports (`fullStep`). The circuit truncated to
the induced checking graph on a ball keeps every internal edge and drops the edges leaving the
ball (`truncatedStep`); its rates are the internal rates unchanged, with no renormalization
(`truncatedRate_of_mem`, `sum_truncatedRate_le`). Started from supports inside the ball, the full
and truncated circuits execute the same operations and reach the same state along every run with
no outside-checking event (`runCircuit_truncatedStep_eq`), so they coincide until the first
outside-checking event, and every evaluation of the final state satisfies the same bound
(`totalVariation_truncated_le`).

§9.1 certified numbers, with `n = 10`, `|A| = 2`, `D = 1` and `T = 1`: the support bound `20 e³`
lies in `[401.7, 401.72]` (`twenty_mul_exp_three_mem_Icc`), and the escape bound `20 e (2e/20)^20`
at `ℓ = 20` is at most `2.64 × 10⁻¹⁰` (`escapeBound_twenty_le`).

Scope. The escape probability enters as the weight of the escape event; its bound, Theorem 8, is
not proved in this module. The continuous-time circuit and the duality identity (7.5) that makes
the output of the circuit the sample law `S_{n,A,T}(p)` are not constructed: the coupling
statements take the randomness of the circuit as a finite weighted space and its evaluation as
given.

## Empirical status

None. The bodies here are finite sums, list recursions and bounds on `e`: the circuit randomness,
the evaluations and the ball are supplied, and no measurement enters any statement.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Pangenome.AncestralLocality

open Finset

noncomputable section

/-! ### Corollary 8.1 on a common finite probability space -/

section Coupling

variable {Ω S : Type*} [Fintype Ω] [Fintype S]

/-- The total variation distance `d_TV(μ, ν) = ½ ∑_s |μ(s) - ν(s)|` of two finite laws. -/
def totalVariation (μ ν : S → ℝ) : ℝ := (∑ s, |μ s - ν s|) / 2

/-- The law of a finite sample obtained by evaluating a random circuit: the circuit randomness `ω`
has weight `weight ω`, and on `ω` the evaluation is the finite law `evaluation ω` on samples. -/
def mixtureLaw (weight : Ω → ℝ) (evaluation : Ω → S → ℝ) (s : S) : ℝ :=
  ∑ ω, weight ω * evaluation ω s

/-- Spec Corollary 8.1 on a common finite probability space. Assumes: nonnegative weights for the
circuit randomness, and for every `ω` two finite laws on samples, the evaluations of one circuit on
two inputs, which coincide whenever `ω` is not an escape. Then the two sample laws are within total
variation the probability of escape. -/
theorem totalVariation_mixtureLaw_le (weight : Ω → ℝ) (hweight : ∀ ω, 0 ≤ weight ω)
    (evaluationP evaluationQ : Ω → S → ℝ) (hnonnegP : ∀ ω s, 0 ≤ evaluationP ω s)
    (hnonnegQ : ∀ ω s, 0 ≤ evaluationQ ω s) (htotalP : ∀ ω, ∑ s, evaluationP ω s = 1)
    (htotalQ : ∀ ω, ∑ s, evaluationQ ω s = 1) (escape : Ω → Prop) [DecidablePred escape]
    (hagree : ∀ ω, ¬ escape ω → evaluationP ω = evaluationQ ω) :
    totalVariation (mixtureLaw weight evaluationP) (mixtureLaw weight evaluationQ) ≤
      ∑ ω ∈ univ.filter escape, weight ω := by
  have hdifference : ∀ s, mixtureLaw weight evaluationP s - mixtureLaw weight evaluationQ s =
      ∑ ω ∈ univ.filter escape, weight ω * (evaluationP ω s - evaluationQ ω s) := by
    intro s
    unfold mixtureLaw
    rw [← Finset.sum_sub_distrib, ← Finset.sum_filter_add_sum_filter_not univ escape]
    have hzero : ∑ ω ∈ univ.filter (fun ω ↦ ¬ escape ω),
        (weight ω * evaluationP ω s - weight ω * evaluationQ ω s) = 0 := by
      refine Finset.sum_eq_zero fun ω hω ↦ ?_
      rw [hagree ω (Finset.mem_filter.mp hω).2, sub_self]
    rw [hzero, add_zero]
    exact Finset.sum_congr rfl fun ω _ ↦ (mul_sub _ _ _).symm
  have hbound : ∀ s, |mixtureLaw weight evaluationP s - mixtureLaw weight evaluationQ s| ≤
      ∑ ω ∈ univ.filter escape, weight ω * (evaluationP ω s + evaluationQ ω s) := by
    intro s
    rw [hdifference s]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun ω _ ↦ ?_)
    rw [abs_mul, abs_of_nonneg (hweight ω)]
    refine mul_le_mul_of_nonneg_left (abs_le.mpr ⟨?_, ?_⟩) (hweight ω)
    · linarith [hnonnegP ω s, hnonnegQ ω s]
    · linarith [hnonnegP ω s, hnonnegQ ω s]
  have htotal : ∑ s, ∑ ω ∈ univ.filter escape, weight ω * (evaluationP ω s + evaluationQ ω s) =
      2 * ∑ ω ∈ univ.filter escape, weight ω := by
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun ω _ ↦ ?_
    rw [← Finset.mul_sum, Finset.sum_add_distrib, htotalP, htotalQ]
    ring
  unfold totalVariation
  rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
  calc ∑ s, |mixtureLaw weight evaluationP s - mixtureLaw weight evaluationQ s|
      ≤ ∑ s, ∑ ω ∈ univ.filter escape, weight ω * (evaluationP ω s + evaluationQ ω s) :=
        Finset.sum_le_sum fun s _ ↦ hbound s
    _ = (∑ ω ∈ univ.filter escape, weight ω) * 2 := by rw [htotal, mul_comm]

/-- Spec Corollary 8.1 for deterministic outputs, the coupling inequality. Assumes: nonnegative
weights, and two outputs of the circuit randomness that coincide whenever `ω` is not an escape. The
laws of the two outputs are within total variation the probability of escape. -/
theorem totalVariation_pointLaw_le [DecidableEq S] (weight : Ω → ℝ) (hweight : ∀ ω, 0 ≤ weight ω)
    (outputP outputQ : Ω → S) (escape : Ω → Prop) [DecidablePred escape]
    (hagree : ∀ ω, ¬ escape ω → outputP ω = outputQ ω) :
    totalVariation (mixtureLaw weight fun ω s ↦ if outputP ω = s then 1 else 0)
        (mixtureLaw weight fun ω s ↦ if outputQ ω = s then 1 else 0) ≤
      ∑ ω ∈ univ.filter escape, weight ω :=
  totalVariation_mixtureLaw_le weight hweight _ _ (fun ω s ↦ by split_ifs <;> norm_num)
    (fun ω s ↦ by split_ifs <;> norm_num) (fun ω ↦ by simp) (fun ω ↦ by simp) escape
    fun ω hω ↦ by simp only [hagree ω hω]

/-- Spec (9.3). Assumes: nonnegative weights for the circuit randomness; a circuit whose evaluation
on `ω` is a finite law on samples that depends only on the input coordinates it inspects on `ω`;
and two inputs that agree on a ball. The two sample laws are within total variation the probability
that the circuit inspects a coordinate outside the ball. -/
theorem totalVariation_local_le {V X : Type*} [DecidableEq V] (weight : Ω → ℝ)
    (hweight : ∀ ω, 0 ≤ weight ω) (inspected : Ω → Finset V) (ball : Finset V)
    (evaluation : Ω → (V → X) → S → ℝ) (hnonneg : ∀ ω input s, 0 ≤ evaluation ω input s)
    (htotal : ∀ ω input, ∑ s, evaluation ω input s = 1)
    (hlocal : ∀ ω (first second : V → X), (∀ v ∈ inspected ω, first v = second v) →
      evaluation ω first = evaluation ω second)
    (p q : V → X) (hball : ∀ v ∈ ball, p v = q v) :
    totalVariation (mixtureLaw weight fun ω ↦ evaluation ω p)
        (mixtureLaw weight fun ω ↦ evaluation ω q) ≤
      ∑ ω ∈ univ.filter (fun ω ↦ ¬ inspected ω ⊆ ball), weight ω :=
  totalVariation_mixtureLaw_le weight hweight _ _ (fun ω ↦ hnonneg ω p) (fun ω ↦ hnonneg ω q)
    (fun ω ↦ htotal ω p) (fun ω ↦ htotal ω q) (fun ω ↦ ¬ inspected ω ⊆ ball)
    fun ω hω ↦ hlocal ω p q fun v hv ↦ hball v (not_not.mp hω hv)

/-- Spec §10, the error term of the approximation, for expectations of a bounded test function.
Assumes: the hypotheses of `totalVariation_mixtureLaw_le`, and a test function on samples bounded
in absolute value by `bound ≥ 0`. The expectations under the two sample laws differ by at most
`2 · bound · Pr(escape)`. -/
theorem abs_sum_mul_mixtureLaw_sub_le (weight : Ω → ℝ) (hweight : ∀ ω, 0 ≤ weight ω)
    (evaluationP evaluationQ : Ω → S → ℝ) (hnonnegP : ∀ ω s, 0 ≤ evaluationP ω s)
    (hnonnegQ : ∀ ω s, 0 ≤ evaluationQ ω s) (htotalP : ∀ ω, ∑ s, evaluationP ω s = 1)
    (htotalQ : ∀ ω, ∑ s, evaluationQ ω s = 1) (escape : Ω → Prop) [DecidablePred escape]
    (hagree : ∀ ω, ¬ escape ω → evaluationP ω = evaluationQ ω) (test : S → ℝ) (bound : ℝ)
    (hbound : 0 ≤ bound) (htest : ∀ s, |test s| ≤ bound) :
    |∑ s, test s * mixtureLaw weight evaluationP s -
        ∑ s, test s * mixtureLaw weight evaluationQ s| ≤
      2 * bound * ∑ ω ∈ univ.filter escape, weight ω := by
  have hvariation := totalVariation_mixtureLaw_le weight hweight evaluationP evaluationQ hnonnegP
    hnonnegQ htotalP htotalQ escape hagree
  calc |∑ s, test s * mixtureLaw weight evaluationP s -
        ∑ s, test s * mixtureLaw weight evaluationQ s|
      = |∑ s, test s * (mixtureLaw weight evaluationP s - mixtureLaw weight evaluationQ s)| := by
        rw [← Finset.sum_sub_distrib]
        simp only [mul_sub]
    _ ≤ ∑ s, |test s * (mixtureLaw weight evaluationP s - mixtureLaw weight evaluationQ s)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ s, bound * |mixtureLaw weight evaluationP s - mixtureLaw weight evaluationQ s| :=
        Finset.sum_le_sum fun s _ ↦ by
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_right (htest s) (abs_nonneg _)
    _ = bound * (2 * totalVariation (mixtureLaw weight evaluationP)
          (mixtureLaw weight evaluationQ)) := by
        rw [← Finset.mul_sum, totalVariation]
        ring
    _ ≤ bound * (2 * ∑ ω ∈ univ.filter escape, weight ω) :=
        mul_le_mul_of_nonneg_left (by linarith [hvariation]) hbound
    _ = 2 * bound * ∑ ω ∈ univ.filter escape, weight ω := by ring

end Coupling

/-! ### The truncation form -/

/-- An event of the ancestral decision circuit: a decision branching of an argument along the
checking edge `source → target`, or the coalescence of two arguments. -/
inductive CircuitEvent (V : Type*)
  | decision (argument : ℕ) (source target : V)
  | coalescence (first second : ℕ)

/-- The state of a decision circuit: the support tag of every argument, and the operations it has
executed, most recent first. -/
structure CircuitState (V : Type*) where
  supports : List (Finset V)
  executed : List (CircuitEvent V)

section Truncation

variable {V : Type*} [DecidableEq V]

/-- One event of the full circuit, (7.6). A decision along `i → j` on an argument whose support
contains `i` adds `j` to that support and appends a parent with support `{i, j}`, and is omitted
otherwise. A coalescence gives the first argument the union of the two supports and removes the
second argument. -/
def fullStep (state : CircuitState V) : CircuitEvent V → CircuitState V
  | .decision argument source target =>
    if source ∈ state.supports.getD argument ∅ then
      ⟨state.supports.set argument (insert target (state.supports.getD argument ∅)) ++
          [{source, target}], .decision argument source target :: state.executed⟩
    else state
  | .coalescence first second =>
    ⟨(state.supports.set first
        (state.supports.getD first ∅ ∪ state.supports.getD second ∅)).eraseIdx second,
      .coalescence first second :: state.executed⟩

/-- One event of the circuit truncated to the induced checking graph on `ball`: a decision along an
edge leaving the induced graph never happens, and every other event is as in the full circuit. -/
def truncatedStep (ball : Finset V) (state : CircuitState V) : CircuitEvent V → CircuitState V
  | .decision argument source target =>
    if source ∈ ball ∧ target ∈ ball then fullStep state (.decision argument source target)
    else state
  | .coalescence first second => fullStep state (.coalescence first second)

/-- An outside-checking event: a decision on an argument whose support contains the source, along
an edge whose target lies outside `ball`. -/
def ChecksOutside (ball : Finset V) (state : CircuitState V) : CircuitEvent V → Prop
  | .decision argument source target =>
    source ∈ state.supports.getD argument ∅ ∧ target ∉ ball
  | .coalescence _ _ => False

/-- Runs a circuit over a list of events, oldest first. -/
def runCircuit (step : CircuitState V → CircuitEvent V → CircuitState V)
    (state : CircuitState V) (events : List (CircuitEvent V)) : CircuitState V :=
  events.foldl step state

/-- No event along the run of the full circuit checks outside `ball`. -/
def NoOutsideCheck (ball : Finset V) : CircuitState V → List (CircuitEvent V) → Prop
  | _, [] => True
  | state, event :: rest =>
    ¬ ChecksOutside ball state event ∧ NoOutsideCheck ball (fullStep state event) rest

/-- The truncated rates: the rates of the edges of the induced graph on `ball`, unchanged, and zero
on every edge leaving it. -/
def truncatedRate (ball : Finset V) (rate : V → V → ℝ) (source target : V) : ℝ :=
  if source ∈ ball ∧ target ∈ ball then rate source target else 0

/-- A witness that an outside-checking event can occur: from the support `{0}`, a decision along
`0 → 1` checks outside the ball `{0}`. -/
theorem checksOutside_witness :
    ChecksOutside ({0} : Finset ℕ) ⟨[{0}], []⟩ (CircuitEvent.decision 0 0 1) := by
  simp [ChecksOutside]

/-- A witness of a run with no outside-checking event: from the support `{0}`, a decision along
`0 → 1` stays inside the ball `{0, 1}`. -/
theorem noOutsideCheck_witness :
    NoOutsideCheck ({0, 1} : Finset ℕ) ⟨[{0}], []⟩ [CircuitEvent.decision 0 0 1] := by
  simp [NoOutsideCheck, ChecksOutside]

omit [DecidableEq V] in
/-- The support of any argument index lies in `ball` when every listed support does, since an
index past the end reads the empty support. Assumes: every listed support lies in `ball`. -/
theorem getD_subset_of_forall {ball : Finset V} {supports : List (Finset V)}
    (hinside : ∀ support ∈ supports, support ⊆ ball) (index : ℕ) :
    supports.getD index ∅ ⊆ ball := by
  induction supports generalizing index with
  | nil => simp
  | cons head tail ih =>
    cases index with
    | zero => simpa using hinside head (by simp)
    | succ index =>
      simpa using ih (fun support hsupport ↦ hinside support (by simp [hsupport])) index

/-- Assumes: supports inside `ball` and an event that does not check outside `ball`. The truncated
circuit takes the same step as the full circuit. -/
theorem fullStep_eq_truncatedStep {ball : Finset V} {state : CircuitState V}
    (hinside : ∀ support ∈ state.supports, support ⊆ ball) {event : CircuitEvent V}
    (hevent : ¬ ChecksOutside ball state event) :
    truncatedStep ball state event = fullStep state event := by
  cases event with
  | decision argument source target =>
    simp only [ChecksOutside, not_and, not_not] at hevent
    by_cases hsource : source ∈ state.supports.getD argument ∅
    · have hball : source ∈ ball := getD_subset_of_forall hinside argument hsource
      simp only [truncatedStep, if_pos (And.intro hball (hevent hsource))]
    · simp only [truncatedStep, fullStep, if_neg hsource, ite_self]
  | coalescence first second => rfl

/-- Assumes: supports inside `ball` and an event that does not check outside `ball`. After the step
of the full circuit every support still lies in `ball`. -/
theorem fullStep_inside {ball : Finset V} {state : CircuitState V}
    (hinside : ∀ support ∈ state.supports, support ⊆ ball) {event : CircuitEvent V}
    (hevent : ¬ ChecksOutside ball state event) :
    ∀ support ∈ (fullStep state event).supports, support ⊆ ball := by
  cases event with
  | decision argument source target =>
    simp only [ChecksOutside, not_and, not_not] at hevent
    by_cases hsource : source ∈ state.supports.getD argument ∅
    · have hsourceBall := getD_subset_of_forall hinside argument hsource
      have htarget := hevent hsource
      intro support hsupport
      simp only [fullStep, if_pos hsource, List.mem_append, List.mem_singleton] at hsupport
      rcases hsupport with hset | rfl
      · rcases List.mem_or_eq_of_mem_set hset with hold | rfl
        · exact hinside support hold
        · exact Finset.insert_subset htarget (getD_subset_of_forall hinside argument)
      · exact Finset.insert_subset hsourceBall (Finset.singleton_subset_iff.mpr htarget)
    · simpa only [fullStep, if_neg hsource] using hinside
  | coalescence first second =>
    intro support hsupport
    simp only [fullStep] at hsupport
    rcases List.mem_or_eq_of_mem_set (List.mem_of_mem_eraseIdx hsupport) with hold | rfl
    · exact hinside support hold
    · exact Finset.union_subset (getD_subset_of_forall hinside first)
        (getD_subset_of_forall hinside second)

/-- Spec Corollary 8.1, the truncation form. Assumes: a circuit whose supports lie in `ball`, and a
list of events along which the full circuit never checks outside `ball`. Then the full circuit and
the circuit truncated to the induced checking graph on `ball` execute the same operations and reach
the same state. Applied to every prefix of a run, they coincide until the first outside-checking
event. -/
theorem runCircuit_truncatedStep_eq (ball : Finset V) (events : List (CircuitEvent V)) :
    ∀ state : CircuitState V, (∀ support ∈ state.supports, support ⊆ ball) →
      NoOutsideCheck ball state events →
        runCircuit (truncatedStep ball) state events = runCircuit fullStep state events := by
  induction events with
  | nil => intro state _ _; rfl
  | cons event rest ih =>
    intro state hinside hno
    simp only [NoOutsideCheck] at hno
    obtain ⟨hevent, hrest⟩ := hno
    simp only [runCircuit, List.foldl_cons]
    rw [fullStep_eq_truncatedStep hinside hevent]
    exact ih _ (fullStep_inside hinside hevent) hrest

/-- The truncated rates are the internal rates, unchanged. Assumes: an edge of the induced graph. -/
theorem truncatedRate_of_mem {ball : Finset V} {rate : V → V → ℝ} {source target : V}
    (hsource : source ∈ ball) (htarget : target ∈ ball) :
    truncatedRate ball rate source target = rate source target := by
  simp [truncatedRate, hsource, htarget]

/-- No renormalization: truncation never raises the total checking rate out of a coordinate, so
(8.1) holds for the truncated graph with the same bound `D`. Assumes: nonnegative rates. -/
theorem sum_truncatedRate_le [Fintype V] {ball : Finset V} {rate : V → V → ℝ}
    (hrate : ∀ source target, 0 ≤ rate source target) (source : V) :
    ∑ target, truncatedRate ball rate source target ≤ ∑ target, rate source target :=
  Finset.sum_le_sum fun target _ ↦ by
    unfold truncatedRate
    split_ifs
    · exact le_rfl
    · exact hrate source target

open scoped Classical in
/-- Spec Corollary 8.1 for the truncated circuit. Assumes: nonnegative weights for the circuit
randomness, a starting circuit whose supports lie in `ball`, and an evaluation of the final circuit
state as a finite law on samples. The sample laws of the full circuit and of the truncated circuit
are within total variation the probability of an outside-checking event along the run. -/
theorem totalVariation_truncated_le {Ω S : Type*} [Fintype Ω] [Fintype S] (ball : Finset V)
    (weight : Ω → ℝ) (hweight : ∀ ω, 0 ≤ weight ω) (initial : CircuitState V)
    (hinitial : ∀ support ∈ initial.supports, support ⊆ ball)
    (events : Ω → List (CircuitEvent V)) (evaluation : CircuitState V → S → ℝ)
    (hnonneg : ∀ state s, 0 ≤ evaluation state s) (htotal : ∀ state, ∑ s, evaluation state s = 1) :
    totalVariation (mixtureLaw weight fun ω ↦ evaluation (runCircuit fullStep initial (events ω)))
        (mixtureLaw weight fun ω ↦
          evaluation (runCircuit (truncatedStep ball) initial (events ω))) ≤
      ∑ ω ∈ univ.filter (fun ω ↦ ¬ NoOutsideCheck ball initial (events ω)), weight ω :=
  totalVariation_mixtureLaw_le weight hweight _ _ (fun _ ↦ hnonneg _) (fun _ ↦ hnonneg _)
    (fun _ ↦ htotal _) (fun _ ↦ htotal _) (fun ω ↦ ¬ NoOutsideCheck ball initial (events ω))
    fun ω hω ↦ by
      simp only [runCircuit_truncatedStep_eq ball (events ω) initial hinitial (not_not.mp hω)]

end Truncation

/-! ### §9.1 certified numbers -/

/-- Spec §9.1, first number. With `n = 10`, `|A| = 2`, `D = 1` and `T = 1` the support bound (8.2),
`n |A| e^{3DT} = 20 e³`, lies in `[401.7, 401.72]`. -/
theorem twenty_mul_exp_three_mem_Icc : 20 * Real.exp 3 ∈ Set.Icc (401.7 : ℝ) 401.72 := by
  have hcube : Real.exp 3 = Real.exp 1 ^ 3 := by
    rw [← Real.exp_nat_mul]
    norm_num
  have hlow := Real.exp_one_gt_d9
  have hhigh := Real.exp_one_lt_d9
  have hpositive := Real.exp_pos 1
  rw [hcube]
  constructor
  · nlinarith [mul_pos (sub_pos.mpr hlow)
      (by positivity : (0 : ℝ) < Real.exp 1 ^ 2 + Real.exp 1 * 2.7182818283 + 2.7182818283 ^ 2)]
  · nlinarith [mul_pos (sub_pos.mpr hhigh)
      (by positivity : (0 : ℝ) < 2.7182818286 ^ 2 + 2.7182818286 * Real.exp 1 + Real.exp 1 ^ 2)]

/-- Spec §9.1, second number. With the same values and `ℓ = 20` the escape bound (9.2),
`n |A| e^{DT} (2eDT/ℓ)^ℓ = 20 e (2e/20)^20`, is at most `2.64 × 10⁻¹⁰`. -/
theorem escapeBound_twenty_le : 20 * Real.exp 1 * (2 * Real.exp 1 / 20) ^ 20 ≤ 2.64e-10 := by
  have hle : Real.exp 1 ≤ 2.7182818286 := Real.exp_one_lt_d9.le
  calc 20 * Real.exp 1 * (2 * Real.exp 1 / 20) ^ 20
      ≤ 20 * 2.7182818286 * (2 * 2.7182818286 / 20) ^ 20 := by gcongr
    _ ≤ 2.64e-10 := by norm_num

end

end Descent.Pangenome.AncestralLocality
