/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.AncestralLocality.JumpFellerSemigroup
import Descent.Pangenome.AncestralLocality.DecisionJumpExpansion

assert_below Descent.PopGen Descent.Spectral Descent.Blindness Descent.Conditionals
assert_below Descent.Portability Descent.Decision Descent.Program

/-!
# Jump models on the laws of a finite window

Theorem 9 of the research note "Ancestral locality" builds its semigroup from finite windows of
the genome. On a window with genome types `H` the forward population is a law on `H`, a point of
the standard simplex (`SimplexLaw H`, compact by `compactSpace_simplexLaw`). This module sets up
the continuous observables of that simplex and the jump models whose Feller semigroups approach
the forward diffusion (7.1) with decisions.

Sampling functions. A sampling observable `H_f` read on the simplex is a continuous function
(`samplingFunction`), at most `‖f‖` (`norm_samplingFunction_le`), and linear in `f`
(`samplingCLM`). The polynomials in the frequencies, `windowPolynomialAlgebra H`, separate laws
(`windowPolynomialAlgebra_separatesPoints`), and every one of them is a sampling function
(`exists_samplingFunction_eq`): a constant has arity zero, a product with a frequency samples one
more genome (`samplingObservable_extendObservation`), and two arities are made equal by sampling
genomes that are not read (`samplingObservable_padObservation`).

The jump models. `mixtureOperator w φ` averages an observable over finitely many jumps `φ_b` with
weights `w_b`, and it is positive when the weights are (`mixtureOperator_nonneg`). The resampling
jump `resampleLaw` replaces a fraction `ε` of the population by copies of one genome, and the
decision jump `decisionLaw` replaces it by children of a rule. At rate `c/ε²` for resampling and
`r_e/ε` for the decision of event `e`, `jumpGenerator c r T` is positive with total rate
`jumpRate c r ε` (`jumpGenerator_nonneg`, `jumpGenerator_one`), and `jumpApproximation` is its
Feller semigroup, through `JumpFellerSemigroup.jumpSemigroup`. On a sampling function the jump
generator is the backward generator of `SamplingDuality` up to `4 (c + R) ε n³ ‖f‖` at every law,
with `R = ∑_e r_e` (`abs_jumpGenerator_sub_le`), by the expansions of `DecisionJumpExpansion`.

Scope. The jump models, their semigroups and the generator estimate at a fixed step `ε`; the
passage `ε → 0` and the limiting semigroup are not in this module.

## Empirical status

None. The bodies here are continuous functions on a simplex, finite sums and operator bounds, so
no measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Pangenome.AncestralLocality.DecisionWindowJumps

open Finset InfiniteGenomeLimit JumpFellerSemigroup DecisionJumpExpansion
open scoped NNReal

noncomputable section

/-! ## The laws of a window -/

/-- The laws of a finite state space, the standard simplex, as a type. -/
abbrev SimplexLaw (H : Type*) [Fintype H] := ↥(stdSimplex ℝ H)

variable {H : Type*} [Fintype H]

/-- The laws of a finite state space form a compact space. -/
instance compactSpace_simplexLaw : CompactSpace (SimplexLaw H) :=
  isCompact_iff_compactSpace.mp (isCompact_stdSimplex H)

/-- A mixture `ε v + (1 - ε) q` of two laws is a law. -/
theorem mix_mem_stdSimplex {v q : H → ℝ} (hv : v ∈ stdSimplex ℝ H) (hq : q ∈ stdSimplex ℝ H)
    {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) : ε • v + (1 - ε) • q ∈ stdSimplex ℝ H := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact add_nonneg (mul_nonneg hε0 (hv.1 h)) (mul_nonneg (sub_nonneg.mpr hε1) (hq.1 h))
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, sum_add_distrib, ← mul_sum, hv.2, hq.2]
    ring

/-- The frequency of a genome type, as a continuous function of the law. -/
def coordinateFunction (x : H) : C(SimplexLaw H, ℝ) where
  toFun p := p.1 x
  continuous_toFun := (continuous_apply x).comp continuous_subtype_val

/-- The frequency of a genome type at a law. -/
theorem coordinateFunction_apply (x : H) (p : SimplexLaw H) : coordinateFunction x p = p.1 x :=
  rfl

/-- **The polynomials in the frequencies**, as a subalgebra of the continuous observables. -/
def windowPolynomialAlgebra (H : Type*) [Fintype H] : Subalgebra ℝ C(SimplexLaw H, ℝ) :=
  (MvPolynomial.aeval (coordinateFunction (H := H))).range

/-- **The frequencies separate laws.** -/
theorem windowPolynomialAlgebra_separatesPoints :
    (windowPolynomialAlgebra H).SeparatesPoints := by
  intro p q hpq
  have hex : ∃ x, p.1 x ≠ q.1 x := by
    by_contra hc
    push_neg at hc
    exact hpq (Subtype.ext (funext hc))
  obtain ⟨x, hx⟩ := hex
  exact ⟨_, ⟨coordinateFunction x, ⟨MvPolynomial.X x, MvPolynomial.aeval_X _ _⟩, rfl⟩, hx⟩

/-! ## Sampling functions -/

/-- **A sampling observable as a continuous function of the law.** -/
def samplingFunction {n : ℕ} (f : (Fin n → H) → ℝ) : C(SimplexLaw H, ℝ) where
  toFun p := samplingObservable f p.1
  continuous_toFun := by
    unfold samplingObservable
    fun_prop

/-- A sampling function at a law. -/
theorem samplingFunction_apply {n : ℕ} (f : (Fin n → H) → ℝ) (p : SimplexLaw H) :
    samplingFunction f p = samplingObservable f p.1 :=
  rfl

/-- A sampling observable is additive in the observation. -/
theorem samplingObservable_add {n : ℕ} (f g : (Fin n → H) → ℝ) (p : H → ℝ) :
    samplingObservable (f + g) p = samplingObservable f p + samplingObservable g p := by
  simp only [samplingObservable, Pi.add_apply, add_mul, sum_add_distrib]

/-- **One more sampled genome**, read through `g`:
`(extendObservation f g)(u) = f(u_{<n}) g(u_n)`. -/
def extendObservation {n : ℕ} (f : (Fin n → H) → ℝ) (g : H → ℝ) : (Fin (n + 1) → H) → ℝ :=
  fun u ↦ f (Fin.init u) * g (u (Fin.last n))

/-- **Sampling one more genome multiplies by its mean**: `H_{f ⊗ g}(p) = H_f(p) ∑_h g(h) p(h)`. -/
theorem samplingObservable_extendObservation {n : ℕ} (f : (Fin n → H) → ℝ) (g : H → ℝ)
    (p : H → ℝ) :
    samplingObservable (extendObservation f g) p = samplingObservable f p * ∑ h, g h * p h := by
  rw [samplingObservable, sum_tuple_snoc, samplingObservable, sum_mul]
  refine sum_congr rfl fun w _ ↦ ?_
  rw [mul_sum]
  refine sum_congr rfl fun y _ ↦ ?_
  simp only [extendObservation, Fin.init_snoc, Fin.snoc_last, Fin.prod_univ_castSucc,
    Fin.snoc_castSucc]
  ring

/-- **Genomes sampled and not read.** `padObservation f k` reads the first `n` of `n + k` sampled
genomes with `f`. -/
def padObservation {n : ℕ} (f : (Fin n → H) → ℝ) : (k : ℕ) → (Fin (n + k) → H) → ℝ
  | 0 => f
  | k + 1 => extendObservation (padObservation f k) fun _ ↦ 1

/-- On a vector of total mass one, unread genomes do not change a sampling observable. -/
theorem samplingObservable_padObservation {n : ℕ} (f : (Fin n → H) → ℝ) {p : H → ℝ}
    (hp : ∑ h, p h = 1) (k : ℕ) :
    samplingObservable (padObservation f k) p = samplingObservable f p := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [padObservation, samplingObservable_extendObservation, ih]
    simp only [one_mul, hp, mul_one]

/-- An observation read at an equal arity. -/
def castObservation {n n' : ℕ} (h : n = n') (f : (Fin n → H) → ℝ) : (Fin n' → H) → ℝ :=
  h ▸ f

/-- Reading an observation at an equal arity does not change its sampling observable. -/
theorem samplingObservable_castObservation {n n' : ℕ} (h : n = n') (f : (Fin n → H) → ℝ)
    (p : H → ℝ) : samplingObservable (castObservation h f) p = samplingObservable f p := by
  subst h
  rfl

variable [DecidableEq H]

/-- A sampling function is at most `‖f‖`. -/
theorem norm_samplingFunction_le {n : ℕ} (f : (Fin n → H) → ℝ) : ‖samplingFunction f‖ ≤ ‖f‖ :=
  (ContinuousMap.norm_le _ (norm_nonneg f)).mpr fun p ↦ by
    rw [Real.norm_eq_abs, samplingFunction_apply]
    exact abs_samplingObservable_le f p.2

/-- The sampling functions of arity `n`, as a bounded linear map. -/
def samplingCLM (n : ℕ) : ((Fin n → H) → ℝ) →L[ℝ] C(SimplexLaw H, ℝ) :=
  LinearMap.mkContinuous
    { toFun := samplingFunction
      map_add' := fun f g ↦ ContinuousMap.ext fun p ↦ by
        simp only [samplingFunction_apply, ContinuousMap.add_apply, samplingObservable_add]
      map_smul' := fun a f ↦ ContinuousMap.ext fun p ↦ by
        simp only [samplingFunction_apply, ContinuousMap.smul_apply, samplingObservable,
          Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_sum, mul_assoc] }
    1 fun f ↦ by
      rw [one_mul]
      exact norm_samplingFunction_le f

/-- The linear map of sampling functions. -/
theorem samplingCLM_apply {n : ℕ} (f : (Fin n → H) → ℝ) :
    samplingCLM n f = samplingFunction f :=
  rfl

/-- **Every polynomial in the frequencies is a sampling function.** -/
theorem exists_samplingFunction_eq {F : C(SimplexLaw H, ℝ)} (hF : F ∈ windowPolynomialAlgebra H) :
    ∃ (n : ℕ) (f : (Fin n → H) → ℝ), samplingFunction f = F := by
  obtain ⟨P, rfl⟩ := (AlgHom.mem_range _).mp hF
  induction P using MvPolynomial.induction_on with
  | C a =>
    refine ⟨0, fun _ ↦ a, ContinuousMap.ext fun p ↦ ?_⟩
    simp [samplingFunction_apply, samplingObservable, MvPolynomial.aeval_C,
      ContinuousMap.algebraMap_apply]
  | add P Q hP hQ =>
    obtain ⟨n, f, hf⟩ := hP
    obtain ⟨m, g, hg⟩ := hQ
    refine ⟨n + m, padObservation f m + castObservation (Nat.add_comm m n) (padObservation g n),
      ContinuousMap.ext fun p ↦ ?_⟩
    rw [map_add, ← hf, ← hg, ContinuousMap.add_apply, samplingFunction_apply,
      samplingFunction_apply, samplingFunction_apply, samplingObservable_add,
      samplingObservable_castObservation, samplingObservable_padObservation _ p.2.2,
      samplingObservable_padObservation _ p.2.2]
  | mul_X P x hP =>
    obtain ⟨n, f, hf⟩ := hP
    refine ⟨n + 1, extendObservation f fun h ↦ if h = x then 1 else 0,
      ContinuousMap.ext fun p ↦ ?_⟩
    rw [map_mul, ← hf, MvPolynomial.aeval_X, ContinuousMap.mul_apply, samplingFunction_apply,
      samplingFunction_apply, samplingObservable_extendObservation, coordinateFunction_apply]
    simp only [ite_mul, one_mul, zero_mul, sum_ite_eq', mem_univ, if_true]

/-! ## Mixtures of jumps -/

/-- **A finite mixture of jumps**: `(J g)(p) = ∑_b w_b(p) g(φ_b(p))`. -/
def mixtureOperator {B : Type*} [Fintype B] (weight : B → C(SimplexLaw H, ℝ))
    (move : B → C(SimplexLaw H, SimplexLaw H)) : C(SimplexLaw H, ℝ) →L[ℝ] C(SimplexLaw H, ℝ) :=
  LinearMap.mkContinuous
    { toFun := fun g ↦ ∑ b, weight b * g.comp (move b)
      map_add' := fun g₁ g₂ ↦ by
        simp only [ContinuousMap.add_comp, mul_add, sum_add_distrib]
      map_smul' := fun a g ↦ by
        simp only [ContinuousMap.smul_comp, mul_smul_comm, smul_sum, RingHom.id_apply] }
    (∑ b, ‖weight b‖) fun g ↦ by
      refine (norm_sum_le _ _).trans ?_
      rw [sum_mul]
      refine sum_le_sum fun b _ ↦
        (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
      exact (ContinuousMap.norm_le _ (norm_nonneg g)).mpr fun p ↦
        ContinuousMap.norm_coe_le_norm g (move b p)

/-- A mixture of jumps at a law. -/
theorem mixtureOperator_apply {B : Type*} [Fintype B] (weight : B → C(SimplexLaw H, ℝ))
    (move : B → C(SimplexLaw H, SimplexLaw H)) (g : C(SimplexLaw H, ℝ)) (p : SimplexLaw H) :
    mixtureOperator weight move g p = ∑ b, weight b p * g (move b p) := by
  simp only [mixtureOperator, LinearMap.mkContinuous_apply, LinearMap.coe_mk, AddHom.coe_mk,
    ContinuousMap.sum_apply, ContinuousMap.mul_apply, ContinuousMap.comp_apply]

/-- **A mixture with nonnegative weights is positive.** -/
theorem mixtureOperator_nonneg {B : Type*} [Fintype B] {weight : B → C(SimplexLaw H, ℝ)}
    (hw : ∀ b, 0 ≤ weight b) (move : B → C(SimplexLaw H, SimplexLaw H)) {g : C(SimplexLaw H, ℝ)}
    (hg : 0 ≤ g) : 0 ≤ mixtureOperator weight move g :=
  ContinuousMap.le_def.mpr fun p ↦ by
    rw [ContinuousMap.zero_apply, mixtureOperator_apply]
    exact sum_nonneg fun b _ ↦
      mul_nonneg (by simpa using ContinuousMap.le_def.mp (hw b) p)
        (by simpa using ContinuousMap.le_def.mp hg (move b p))

/-- A mixture sends the constant one to the total weight. -/
theorem mixtureOperator_one {B : Type*} [Fintype B] (weight : B → C(SimplexLaw H, ℝ))
    (move : B → C(SimplexLaw H, SimplexLaw H)) : mixtureOperator weight move 1 = ∑ b, weight b :=
  ContinuousMap.ext fun p ↦ by
    rw [mixtureOperator_apply, ContinuousMap.sum_apply]
    simp only [ContinuousMap.one_apply, mul_one]

/-! ## The jump models -/

/-- **The resampling jump** `p ↦ ε δ_x + (1 - ε) p`: a fraction `ε` of the population becomes
copies of the genome `x`. -/
def resampleLaw {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (x : H) : C(SimplexLaw H, SimplexLaw H) where
  toFun p := ⟨ε • (Pi.single x 1 : H → ℝ) + (1 - ε) • p.1,
    mix_mem_stdSimplex (pointMass_mem_stdSimplex x) p.2 hε0 hε1⟩
  continuous_toFun :=
    (continuous_const.add (continuous_const.smul continuous_subtype_val)).subtype_mk _

/-- The law after a resampling jump. -/
theorem resampleLaw_coe {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (x : H) (p : SimplexLaw H) :
    (resampleLaw hε0 hε1 x p).1 = ε • (Pi.single x 1 : H → ℝ) + (1 - ε) • p.1 :=
  rfl

/-- **The decision jump** `p ↦ ε R_{K_T}(p) + (1 - ε) p`: a fraction `ε` of the population becomes
children of the rule `T`. -/
def decisionLaw {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (T : H → H → H) :
    C(SimplexLaw H, SimplexLaw H) where
  toFun p := ⟨ε • reproduce (ruleKernel T) p.1 + (1 - ε) • p.1,
    mix_mem_stdSimplex (reproduce_ruleKernel_mem_stdSimplex T p.2) p.2 hε0 hε1⟩
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    refine (continuous_const.smul ?_).add (continuous_const.smul continuous_subtype_val)
    refine continuous_pi fun z ↦ ?_
    unfold reproduce
    fun_prop

/-- The law after a decision jump. -/
theorem decisionLaw_coe {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (T : H → H → H) (p : SimplexLaw H) :
    (decisionLaw hε0 hε1 T p).1 = ε • reproduce (ruleKernel T) p.1 + (1 - ε) • p.1 :=
  rfl

variable {E : Type*} [Fintype E]

/-- **The jump generator** at step `ε`: resampling at rate `c/ε²`, and the decision of event `e` at
rate `r_e/ε`. -/
def jumpGenerator (c : ℝ) (r : E → ℝ) (T : E → H → H → H) {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    C(SimplexLaw H, ℝ) →L[ℝ] C(SimplexLaw H, ℝ) :=
  mixtureOperator (fun x ↦ (c / ε ^ 2) • coordinateFunction x) (resampleLaw hε0 hε1) +
    mixtureOperator (fun e ↦ ContinuousMap.const _ (r e / ε)) fun e ↦ decisionLaw hε0 hε1 (T e)

/-- The total jump rate `c/ε² + ∑_e r_e/ε`. -/
def jumpRate (c : ℝ) (r : E → ℝ) (ε : ℝ) : ℝ :=
  c / ε ^ 2 + ∑ e, r e / ε

/-- **The jump generator is positive** for nonnegative rates. -/
theorem jumpGenerator_nonneg {c : ℝ} (hc : 0 ≤ c) {r : E → ℝ} (hr : ∀ e, 0 ≤ r e)
    (T : E → H → H → H) {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) {g : C(SimplexLaw H, ℝ)}
    (hg : 0 ≤ g) : 0 ≤ jumpGenerator c r T hε0 hε1 g := by
  rw [jumpGenerator, ContinuousLinearMap.add_apply]
  refine add_nonneg (mixtureOperator_nonneg (fun x ↦ ?_) _ hg)
    (mixtureOperator_nonneg (fun e ↦ ?_) _ hg)
  · refine ContinuousMap.le_def.mpr fun p ↦ ?_
    simp only [ContinuousMap.zero_apply, ContinuousMap.smul_apply, coordinateFunction_apply,
      smul_eq_mul]
    exact mul_nonneg (div_nonneg hc (sq_nonneg ε)) (p.2.1 x)
  · refine ContinuousMap.le_def.mpr fun p ↦ ?_
    simp only [ContinuousMap.zero_apply, ContinuousMap.const_apply]
    exact div_nonneg (hr e) hε0

/-- **The jump generator sends the constant one to the total rate.** -/
theorem jumpGenerator_one (c : ℝ) (r : E → ℝ) (T : E → H → H → H) {ε : ℝ} (hε0 : 0 ≤ ε)
    (hε1 : ε ≤ 1) : jumpGenerator c r T hε0 hε1 1 = jumpRate c r ε • 1 := by
  refine ContinuousMap.ext fun p ↦ ?_
  rw [jumpGenerator, ContinuousLinearMap.add_apply, mixtureOperator_one, mixtureOperator_one]
  simp only [ContinuousMap.add_apply, ContinuousMap.sum_apply, ContinuousMap.smul_apply,
    coordinateFunction_apply, ContinuousMap.const_apply, smul_eq_mul, ContinuousMap.one_apply,
    mul_one, jumpRate, ← mul_sum, p.2.2]

/-- **The jump approximation** at step `ε`: the Feller semigroup of the jump generator. -/
def jumpApproximation {c : ℝ} (hc : 0 ≤ c) {r : E → ℝ} (hr : ∀ e, 0 ≤ r e)
    (T : E → H → H → H) {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) : FellerSemigroup (SimplexLaw H) :=
  jumpSemigroup (jumpGenerator c r T hε0 hε1) (jumpRate c r ε)
    (fun _ hg ↦ jumpGenerator_nonneg hc hr T hε0 hε1 hg) (jumpGenerator_one c r T hε0 hε1)

/-- The operators of the jump approximation are exponentials of the jump generator. -/
theorem jumpApproximation_operator {c : ℝ} (hc : 0 ≤ c) {r : E → ℝ} (hr : ∀ e, 0 ≤ r e)
    (T : E → H → H → H) {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (t : ℝ≥0) :
    (jumpApproximation hc hr T hε0 hε1).operator t =
      jumpOperator (jumpGenerator c r T hε0 hε1) (jumpRate c r ε) t :=
  rfl

/-- **The jump generator against the backward generator.** At every law and for `0 < ε ≤ 1`, on a
sampling function of arity `n`,
`|(J - λ) H_f(p) - backwardGenerator c r T f p| ≤ 4 (c + R) ε n³ ‖f‖`, with `R = ∑_e r_e`. -/
theorem abs_jumpGenerator_sub_le {c : ℝ} (hc : 0 ≤ c) {r : E → ℝ} (hr : ∀ e, 0 ≤ r e)
    (T : E → H → H → H) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) {n : ℕ} (f : (Fin n → H) → ℝ)
    (p : SimplexLaw H) :
    |(jumpGenerator c r T hε0.le hε1 - jumpRate c r ε • 1) (samplingFunction f) p -
        backwardGenerator c r T f p.1| ≤ 4 * (c + ∑ e, r e) * ε * (n : ℝ) ^ 3 * ‖f‖ := by
  have hε : ε ≠ 0 := hε0.ne'
  have hres := abs_resample_sub_le f p.2 hε0.le hε1
  have hdec : ∀ e, |samplingObservable f (ε • reproduce (ruleKernel (T e)) p.1 + (1 - ε) • p.1) -
      samplingObservable f p.1 - ε * ∑ a,
        (samplingObservable (decisionBranch (T e) a f) p.1 - samplingObservable f p.1)| ≤
      4 * ε ^ 2 * (n : ℝ) ^ 2 * ‖f‖ := fun e ↦ abs_decision_sub_le (T e) f p.2 hε0.le hε1
  have hval : (jumpGenerator c r T hε0.le hε1 - jumpRate c r ε • 1) (samplingFunction f) p -
      backwardGenerator c r T f p.1 =
        c / ε ^ 2 * (∑ x, p.1 x * samplingObservable f (ε • (Pi.single x 1 : H → ℝ) +
          (1 - ε) • p.1) - samplingObservable f p.1 - ε ^ 2 * ∑ b, ∑ a ∈ Iio b,
            (samplingObservable (coalesceArguments a b f) p.1 - samplingObservable f p.1)) +
        ∑ e, r e / ε * (samplingObservable f (ε • reproduce (ruleKernel (T e)) p.1 +
          (1 - ε) • p.1) - samplingObservable f p.1 - ε * ∑ a,
            (samplingObservable (decisionBranch (T e) a f) p.1 - samplingObservable f p.1)) := by
    simp only [jumpGenerator, jumpRate, backwardGenerator, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.one_apply, ContinuousMap.sub_apply, ContinuousMap.add_apply,
      ContinuousMap.smul_apply, mixtureOperator_apply, coordinateFunction_apply,
      ContinuousMap.const_apply, samplingFunction_apply, resampleLaw_coe, decisionLaw_coe,
      smul_eq_mul]
    have hx : ∑ x, c / ε ^ 2 * p.1 x *
        samplingObservable f (ε • (Pi.single x 1 : H → ℝ) + (1 - ε) • p.1) =
          c / ε ^ 2 * ∑ x, p.1 x *
            samplingObservable f (ε • (Pi.single x 1 : H → ℝ) + (1 - ε) • p.1) := by
      rw [mul_sum]
      exact sum_congr rfl fun x _ ↦ by ring
    have he : ∑ e, r e / ε * (samplingObservable f (ε • reproduce (ruleKernel (T e)) p.1 +
        (1 - ε) • p.1) - samplingObservable f p.1 - ε * ∑ a,
          (samplingObservable (decisionBranch (T e) a f) p.1 - samplingObservable f p.1)) =
        ∑ e, r e / ε * samplingObservable f (ε • reproduce (ruleKernel (T e)) p.1 +
          (1 - ε) • p.1) - (∑ e, r e / ε) * samplingObservable f p.1 - ∑ e, r e * ∑ a,
            (samplingObservable (decisionBranch (T e) a f) p.1 - samplingObservable f p.1) := by
      rw [sum_mul, ← sum_sub_distrib, ← sum_sub_distrib]
      exact sum_congr rfl fun e _ ↦ by
        field_simp
        ring
    rw [hx, he]
    field_simp
    ring
  rw [hval]
  have hcε : 0 ≤ c / ε ^ 2 := div_nonneg hc (sq_nonneg ε)
  have hn : (n : ℝ) ^ 2 ≤ (n : ℝ) ^ 3 := by
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · simp [h0]
    · exact pow_le_pow_right₀ (by exact_mod_cast hpos) (by norm_num)
  calc |c / ε ^ 2 * (∑ x, p.1 x * samplingObservable f (ε • (Pi.single x 1 : H → ℝ) +
          (1 - ε) • p.1) - samplingObservable f p.1 - ε ^ 2 * ∑ b, ∑ a ∈ Iio b,
            (samplingObservable (coalesceArguments a b f) p.1 - samplingObservable f p.1)) +
        ∑ e, r e / ε * (samplingObservable f (ε • reproduce (ruleKernel (T e)) p.1 +
          (1 - ε) • p.1) - samplingObservable f p.1 - ε * ∑ a,
            (samplingObservable (decisionBranch (T e) a f) p.1 - samplingObservable f p.1))|
      ≤ c / ε ^ 2 * (4 * ε ^ 3 * (n : ℝ) ^ 3 * ‖f‖) +
          ∑ e, r e / ε * (4 * ε ^ 2 * (n : ℝ) ^ 2 * ‖f‖) := by
        refine (abs_add_le _ _).trans (add_le_add ?_ ((abs_sum_le_sum_abs _ _).trans ?_))
        · rw [abs_mul, abs_of_nonneg hcε]
          exact mul_le_mul_of_nonneg_left hres hcε
        · refine sum_le_sum fun e _ ↦ ?_
          rw [abs_mul, abs_of_nonneg (div_nonneg (hr e) hε0.le)]
          exact mul_le_mul_of_nonneg_left (hdec e) (div_nonneg (hr e) hε0.le)
    _ = 4 * c * ε * (n : ℝ) ^ 3 * ‖f‖ + 4 * ε * (n : ℝ) ^ 2 * ‖f‖ * ∑ e, r e := by
        rw [mul_sum]
        congr 1
        · field_simp
          ring
        · exact sum_congr rfl fun e _ ↦ by
            field_simp
            ring
    _ ≤ 4 * (c + ∑ e, r e) * ε * (n : ℝ) ^ 3 * ‖f‖ := by
        have hR : 0 ≤ ∑ e, r e := sum_nonneg fun e _ ↦ hr e
        have hterm := mul_le_mul_of_nonneg_left hn
          (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hε0.le)
            (mul_nonneg (norm_nonneg f) hR))
        nlinarith [hterm]

end

end Descent.Pangenome.AncestralLocality.DecisionWindowJumps
