/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.AncestralLocality.SamplingDuality
import Descent.Portability.AncestralForwardGenerator

assert_below Descent.Decision Descent.Program

/-!
# The finite population converges to the sampling dual

The spec is `ANCESTRAL_LOCALITY.md` §4.1, §7.1 and §7.2.  Two modules state the forward
generator (7.1).  `AncestralForwardGenerator` writes it with formal partial derivatives and proves
that it is the `N`-generation limit of the finite-population chain (4.5) on every polynomial
observable.  `Descent.Pangenome.AncestralLocality.SamplingDuality` writes it with line derivatives
on arbitrary functions of the population and proves the generator form of Theorem 6: on a
sampling observable `H_f` the forward generator is the backward circuit of coalescence and
decision branching.  This module ties the two and composes them.

The derivatives.  A polynomial moves along a line by its formal gradient,
`d/dt F(p + t v)|_{t=0} = Σ_z v_z ∂_z F(p)` (`hasDerivAt_eval_line`), so the line derivatives of a
polynomial function are its formal partial derivatives (`firstPartial_eval`, `secondPartial_eval`).

The generators agree.  With the rate table `edgeRate G` (the rate `r_ij` on an edge of the checking
graph and zero off it) and the ordered children `T_ij` of (4.1), the formal-derivative generator
is the line-derivative generator on every polynomial observable
(`forwardGenerator_eq_samplingDuality`).

The dual limit.  The sampling observable `H_f(p) = Σ_x f(x) Π_a p(x_a)` of (7.2) is the
polynomial `samplingPolynomial f` (`eval_samplingPolynomial`).  Composing the finite-population
limit with the generator identity gives, for every population `p` and every `f`,
`N · E[H_f(P') - H_f(p)] → (backward generator applied to f, read at p)`: one generation of the
finite population, on the `N`-generation scale, is the backward circuit of Theorem 6
(`tendsto_nextGenerationMean_samplingPolynomial`).

Scope.  The resampling rate is `c = 1`, and the statement is the one-generation expansion at a
fixed population; the semigroup duality (7.5) is not proved here.

## Empirical status

None.  The bodies here are derivatives of polynomials and limits of finite census sums in
supplied rates and population frequencies, so no measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.AncestralSamplingLimit

open Filter Topology MvPolynomial
open Descent.Pangenome.AncestralLocality (CheckingGraph orderedChild exchangeKernel reproduce
  firstPartial secondPartial resamplingGenerator decisionGenerator backwardGenerator
  samplingObservable)

noncomputable section

/-! ## Line derivatives of polynomials -/

section Derivatives

variable {H : Type*} [Fintype H] [DecidableEq H]

/-- **A polynomial along a line.**  `t ↦ F(p + t v)` has derivative `Σ_z v_z ∂_z F(p)` at
`t = 0`. -/
theorem hasDerivAt_eval_line (p v : H → ℝ) (F : MvPolynomial H ℝ) :
    HasDerivAt (fun t : ℝ ↦ eval (p + t • v) F) (∑ z, v z * eval p (pderiv z F)) 0 := by
  induction F using MvPolynomial.induction_on with
  | C a =>
    simp only [eval_C, pderiv_C, map_zero, mul_zero, Finset.sum_const_zero]
    exact hasDerivAt_const 0 a
  | add F₁ F₂ h₁ h₂ =>
    simp only [map_add, mul_add, Finset.sum_add_distrib]
    exact h₁.add h₂
  | mul_X F n hF =>
    have hline : HasDerivAt (fun t : ℝ ↦ p n + t * v n) (v n) 0 := by
      have h := ((hasDerivAt_id (0 : ℝ)).mul_const (v n)).const_add (p n)
      simpa only [id_eq, one_mul] using h
    have h := hF.mul hline
    simp only [zero_mul, add_zero, zero_smul] at h
    have hfun : (fun t : ℝ ↦ eval (p + t • v) (F * X n))
        = fun t : ℝ ↦ eval (p + t • v) F * (p n + t * v n) := by
      funext t
      simp only [map_mul, eval_X, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [hfun, AncestralForwardGenerator.sum_mul_eval_pderiv_mul_X]
    exact h

/-- The line derivative of a polynomial function is the formal gradient paired with the
direction. -/
theorem lineDeriv_eval (p v : H → ℝ) (F : MvPolynomial H ℝ) :
    lineDeriv ℝ (fun q ↦ eval q F) p v = ∑ z, v z * eval p (pderiv z F) :=
  (hasDerivAt_eval_line p v F).deriv

/-- **The first partial derivative of a polynomial function is the formal one.** -/
theorem firstPartial_eval (p : H → ℝ) (F : MvPolynomial H ℝ) (z : H) :
    firstPartial (fun q ↦ eval q F) p z = eval p (pderiv z F) := by
  rw [firstPartial, lineDeriv_eval]
  simp only [Pi.single_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
    if_true]

/-- **The second partial derivative of a polynomial function is the formal one.** -/
theorem secondPartial_eval (p : H → ℝ) (F : MvPolynomial H ℝ) (x y : H) :
    secondPartial (fun q ↦ eval q F) p x y = eval p (pderiv x (pderiv y F)) := by
  have hfun : (fun q ↦ lineDeriv ℝ (fun q' ↦ eval q' F) q (Pi.single y 1))
      = fun q ↦ eval q (pderiv y F) :=
    funext fun q ↦ firstPartial_eval q F y
  rw [secondPartial, hfun]
  exact firstPartial_eval p (pderiv y F) x

end Derivatives

/-! ## The two forms of (7.1) and the dual limit -/

section Link

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The rate table of a checking graph on all ordered pairs: the rate `r_ij` on an edge and zero
off it. -/
def edgeRate (G : CheckingGraph V) (e : V × V) : ℝ :=
  if e ∈ G.edges then G.rate e else 0

/-- **The two forms of (7.1) agree.**  On a polynomial observable, the generator of the
finite-population limit, written with formal partial derivatives, is the forward generator of
`SamplingDuality`, written with line derivatives, for the rate table `edgeRate G` and the ordered
children on the edges. -/
theorem forwardGenerator_eq_samplingDuality (G : CheckingGraph V) (c : ℝ)
    (p : (V → Bool) → ℝ) (F : MvPolynomial (V → Bool) ℝ) :
    AncestralForwardGenerator.forwardGenerator G c p F
      = Descent.Pangenome.AncestralLocality.forwardGenerator c (edgeRate G)
          (fun e ↦ orderedChild e.1 e.2) (fun q ↦ eval q F) p := by
  have hresampling : resamplingGenerator c (fun q ↦ eval q F) p
      = c * MultinomialMomentExpansion.resamplingOperator p F := by
    have hterm : ∀ x y, p x * ((if x = y then 1 else 0) - p y) * eval p (pderiv x (pderiv y F))
        = ((if x = y then p x else 0) - p x * p y) * eval p (pderiv x (pderiv y F)) := by
      intro x y
      split_ifs <;> ring
    rw [resamplingGenerator, MultinomialMomentExpansion.resamplingOperator]
    simp only [secondPartial_eval, hterm]
    ring
  have hdecision : decisionGenerator (edgeRate G) (fun e ↦ orderedChild e.1 e.2)
        (fun q ↦ eval q F) p
      = ∑ e ∈ G.edges, G.rate e
          * ∑ z, (reproduce (exchangeKernel e.1 e.2) p z - p z) * eval p (pderiv z F) := by
    rw [decisionGenerator]
    simp only [firstPartial_eval, edgeRate, ite_mul, zero_mul, Finset.sum_ite_mem,
      Finset.univ_inter]
    rfl
  rw [AncestralForwardGenerator.forwardGenerator,
    Descent.Pangenome.AncestralLocality.forwardGenerator, hresampling, hdecision]

/-- The sampling observable `H_f` of (7.2) as a polynomial in the genome frequencies. -/
def samplingPolynomial {n : ℕ} (f : (Fin n → V → Bool) → ℝ) : MvPolynomial (V → Bool) ℝ :=
  ∑ w, C (f w) * ∏ a, X (w a)

/-- The sampling polynomial evaluates to the sampling observable. -/
theorem eval_samplingPolynomial {n : ℕ} (f : (Fin n → V → Bool) → ℝ) (p : (V → Bool) → ℝ) :
    eval p (samplingPolynomial f) = samplingObservable f p := by
  simp only [samplingPolynomial, samplingObservable, map_sum, map_mul, map_prod, eval_C, eval_X]

/-- **One generation of the finite population is the backward circuit.**  For every population
`p` and every sampling observable `H_f`, the census proportions `P'` of `N` offspring from
`Q_N(p)` satisfy `N · E[H_f(P') - H_f(p)] → L_anc f (p)`, where `L_anc` is the backward generator
of Theorem 6 (coalescence of every pair at rate one, branching of every argument along every edge
at its rate), read at `p`. -/
theorem tendsto_nextGenerationMean_samplingPolynomial (G : CheckingGraph V)
    (p : FiniteReportLaw (V → Bool)) {n : ℕ} (f : (Fin n → V → Bool) → ℝ) :
    Tendsto (fun N : ℕ ↦ (N : ℝ)
        * (AncestralForwardGenerator.nextGenerationMean G N p.mass (samplingPolynomial f)
          - samplingObservable f p.mass)) atTop
      (𝓝 (backwardGenerator 1 (edgeRate G) (fun e ↦ orderedChild e.1 e.2) f p.mass)) := by
  have h := AncestralForwardGenerator.tendsto_nextGenerationMean G p (samplingPolynomial f)
  have hfun : (fun q ↦ eval q (samplingPolynomial f)) = samplingObservable f :=
    funext fun q ↦ eval_samplingPolynomial f q
  rw [eval_samplingPolynomial, forwardGenerator_eq_samplingDuality, hfun,
    Descent.Pangenome.AncestralLocality.forwardGenerator_samplingObservable 1 (edgeRate G) _ f
      p.mass_sum] at h
  exact h

end Link

end

end Descent.Portability.AncestralSamplingLimit
