/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.AncestralLocality.CoalescentDualSemigroup
import Descent.Portability.AncestralSamplingLimit
import Descent.Portability.NeutralFellerProperty

assert_below Descent.Decision Descent.Program

/-!
# The resampling semigroup on a finite window of the genome

Theorem 9 of the research note "Ancestral locality" without decisions (`r = 0`) is built from one
finite window of the genome at a time.  This module constructs the semigroup of one window and
identifies its action on sampling observables with the coalescent dual of
`Descent.Pangenome.AncestralLocality.CoalescentDualSemigroup`.

The window.  For a finite set `G` of genome types, the neutral model of NOTE1 §4.2 with one deme,
one locus with alleles `G`, coalescence at rate one, and no migration, recombination or mutation
(`resamplingRates G`) is the pure resampling diffusion on the simplex `P(G)`.  Its extended
semigroup is a Feller semigroup in the sense of `InfiniteGenomeLimit.FellerSemigroup`
(`windowSemigroup`, by `NeutralFellerProperty.neutralFellerSemigroup`).

The moment functional in time.  In every neutral model the moment functional of a polynomial
moves along the neutral generator: `d/du Λ_{u,x}(q) = Λ_{u,x}(L q)` at every real time
(`hasDerivAt_momentFunctional`), because on a budget containing the monomials of `q` and of `L q`
both are coefficient vectors dotted with `e^{uQ} H(x)`, and the dual generator carries the
difference of the two coefficient vectors to a combination vanishing on states.  At time zero the
functional is evaluation (`momentFunctional_zero`).

The generators agree.  A sampling observable `H_f(p) = Σ_x f(x) Π_a p(x_a)` is the polynomial
`windowSamplingPolynomial G f` in the window frequencies (`eval_lift_windowSamplingPolynomial`).
The line derivatives of a polynomial read through the window frequencies are its formal partial
derivatives (`lineDeriv_windowEval`, `secondPartial_windowEval`), so the resampling generator of
`SamplingDuality` is the neutral generator of the resampling rates
(`resamplingGenerator_windowEval`).

The dual.  The moment functionals of the window, read on sampling observables, obey the moment
equation of the coalescence generator: `d/du Λ_u(H_f) = Λ_u(L H_f) = Λ_u(H_{L_c f})`, the last step
being Theorem 6 without decisions
(`CoalescentDualSemigroup.samplingFunctional_coalescenceOperator`).  The moment form of the duality
(`CoalescentDualSemigroup.moments_eq_dualSemigroup`) then gives
`T_t H_f (x) = H_{S_t f}(p(x))` with `S_t = e^{t L_c}`: on sampling observables the window semigroup
is the coalescent dual read at the window frequencies (`windowSemigroup_samplingPolynomial`).  The
dual never raises the arity.

Scope.  One window at a time; the passage to the infinite genome is a separate module.

## Empirical status

None.  The bodies here are derivatives of matrix exponentials of supplied rates and polynomials on
the simplex of a supplied finite type set, so no measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.ResamplingWindowSemigroup

open MvPolynomial Filter Topology Descent.Coalescent PartialHaplotypeCarrier
  PartialHaplotypeDualGenerator PartialHaplotypeDualSemigroup NeutralFellerGenerator
  NeutralStateTangency NeutralMomentSemigroup NeutralPolynomialSemigroup
  NeutralPolynomialPositivity PolynomialFellerExtension NeutralMicroscopicEulerLimit
open Descent.Pangenome.AncestralLocality (samplingObservable samplingFunctional
  samplingFunctional_apply coalescenceOperator dualSemigroup moments_eq_dualSemigroup
  samplingFunctional_coalescenceOperator resamplingGenerator secondPartial)
open scoped Matrix NNReal

noncomputable section

/-! ## The moment functional in time -/

section MomentTime

variable {Deme Locus : Type*} {Allele : Locus → Type*}
variable [Fintype Deme] [DecidableEq Deme] [Fintype Locus] [DecidableEq Locus]
  [∀ ℓ, Fintype (Allele ℓ)] [∀ ℓ, DecidableEq (Allele ℓ)]

/-- At time zero the moment functional evaluates the polynomial at the state. -/
theorem momentFunctional_zero (rates : NeutralRates Deme Locus Allele) (ℓ₀ : Locus)
    (x : FrequencyState Deme Locus Allele) (q : FrequencyPolynomial Deme Locus Allele) :
    momentFunctional rates ℓ₀ 0 x q = eval x.1 q := by
  rw [momentFunctional_eq_dotProduct rates ℓ₀ 0 x _ q (withinBudget_supportBudget ℓ₀ q),
    matrixExponential_zero, Matrix.one_mulVec,
    ← eval_eq_dotProduct ℓ₀ _ q (withinBudget_supportBudget ℓ₀ q) x]

/-- **The moment functional moves along the neutral generator.**  At every real time `s`,
`d/du Λ_{u,x}(q) = Λ_{s,x}(L q)`. -/
theorem hasDerivAt_momentFunctional (rates : NeutralRates Deme Locus Allele) (ℓ₀ : Locus)
    (hap₀ : FullHaplotype Locus Allele) (x : FrequencyState Deme Locus Allele)
    (q : FrequencyPolynomial Deme Locus Allele) (s : ℝ) :
    HasDerivAt (fun u ↦ momentFunctional rates ℓ₀ u x q)
      (momentFunctional rates ℓ₀ s x (neutralGenerator rates q)) s := by
  obtain ⟨capacity, hq, hg⟩ : ∃ capacity : Locus → ℕ,
      (∀ β ∈ q.support, WithinBudget capacity (monomialConfiguration ℓ₀ β))
        ∧ ∀ β ∈ (neutralGenerator rates q).support,
          WithinBudget capacity (monomialConfiguration ℓ₀ β) :=
    ⟨fun ℓ ↦ supportBudget ℓ₀ q ℓ + supportBudget ℓ₀ (neutralGenerator rates q) ℓ,
      fun β hβ ℓ ↦ (withinBudget_supportBudget ℓ₀ q β hβ ℓ).trans (Nat.le_add_right _ _),
      fun β hβ ℓ ↦ (withinBudget_supportBudget ℓ₀ _ β hβ ℓ).trans (Nat.le_add_left _ _)⟩
  obtain ⟨c, hcq, hceval⟩ : ∃ c : BudgetConfiguration Deme Locus Allele capacity → ℝ,
      (∀ u y, momentFunctional rates ℓ₀ u y q
        = c ⬝ᵥ (matrixExponential (dualGenerator rates capacity) u *ᵥ momentVector capacity y))
        ∧ ∀ y, eval y.1 q = c ⬝ᵥ momentVector capacity y :=
    ⟨_, fun u y ↦ momentFunctional_eq_dotProduct rates ℓ₀ u y capacity q hq,
      fun y ↦ eval_eq_dotProduct ℓ₀ capacity q hq y⟩
  obtain ⟨c', hc'q, hc'eval⟩ : ∃ c' : BudgetConfiguration Deme Locus Allele capacity → ℝ,
      (∀ u y, momentFunctional rates ℓ₀ u y (neutralGenerator rates q)
        = c' ⬝ᵥ (matrixExponential (dualGenerator rates capacity) u *ᵥ momentVector capacity y))
        ∧ ∀ y, eval y.1 (neutralGenerator rates q) = c' ⬝ᵥ momentVector capacity y :=
    ⟨_, fun u y ↦ momentFunctional_eq_dotProduct rates ℓ₀ u y capacity _ hg,
      fun y ↦ eval_eq_dotProduct ℓ₀ capacity _ hg y⟩
  have hvanish : c ᵥ* dualGenerator rates capacity - c' ∈ vanishingCombinations capacity := by
    intro y
    have hdiff : ∀ z : FrequencyState Deme Locus Allele,
        eval z.1 ((∑ η, C (c η) * momentPolynomial η.1) - q) = 0 := by
      intro z
      rw [map_sub, map_sum, hceval z]
      simp only [map_mul, eval_C]
      exact sub_eq_zero.mpr rfl
    have h := eval_neutralGenerator_of_vanishing rates hap₀ _ hdiff y
    rw [← neutralGeneratorAddHom_apply, map_sub, neutralGeneratorAddHom_apply,
      neutralGeneratorAddHom_apply, map_sub, sub_eq_zero] at h
    rw [sub_dotProduct, ← eval_neutralGenerator_combination rates capacity c y, ← hc'eval y,
      sub_eq_zero]
    exact h
  have hderiv : HasDerivAt
      (fun u ↦ c ⬝ᵥ (matrixExponential (dualGenerator rates capacity) u *ᵥ momentVector capacity x))
      (c ⬝ᵥ (dualGenerator rates capacity
        *ᵥ (matrixExponential (dualGenerator rates capacity) s *ᵥ momentVector capacity x))) s := by
    have h := hasDerivAt_pi.mp (StationaryHaplotypeRealization.hasDerivAt_matrixExponential_mulVec
      (dualGenerator rates capacity) (momentVector capacity x) s)
    simp only [dotProduct]
    exact HasDerivAt.fun_sum fun η _ ↦ (h η).const_mul (c η)
  have hvalue : c ⬝ᵥ (dualGenerator rates capacity
        *ᵥ (matrixExponential (dualGenerator rates capacity) s *ᵥ momentVector capacity x))
      = momentFunctional rates ℓ₀ s x (neutralGenerator rates q) := by
    have hzero := vecMul_matrixExponential_mem rates hap₀ capacity s _ hvanish x
    rw [← Matrix.dotProduct_mulVec, sub_dotProduct, ← Matrix.dotProduct_mulVec, sub_eq_zero]
      at hzero
    rw [hzero, hc'q s x]
  rw [hvalue] at hderiv
  exact hderiv.congr_of_eventuallyEq (Eventually.of_forall fun u ↦ hcq u x)

end MomentTime

/-! ## The window model -/

section Window

variable (G : Type*) [Fintype G] [DecidableEq G]

/-- **The resampling rates** on one deme and one locus with the genome types `G` as alleles:
coalescence at rate one, and no migration, recombination or mutation. -/
def resamplingRates : NeutralRates Unit Unit (fun _ ↦ G) where
  coalescence _ := 1
  migration _ _ := 0
  recombination _ := 0
  mutation _ _ _ := 0
  coalescence_nonneg _ := zero_le_one
  migration_nonneg _ _ := le_rfl
  recombination_nonneg _ := le_rfl
  mutation_nonneg _ _ _ := le_rfl
  mutation_symm _ _ _ := rfl

/-- **The window semigroup**: the neutral Feller semigroup of the resampling rates on the simplex
of the genome types `G`. -/
def windowSemigroup (hap₀ : FullHaplotype Unit (fun _ ↦ G)) :
    Descent.Pangenome.AncestralLocality.InfiniteGenomeLimit.FellerSemigroup
      (FrequencyState Unit Unit (fun _ ↦ G)) :=
  NeutralFellerProperty.neutralFellerSemigroup (resamplingRates G) () hap₀

/-- The frequency vector of a window state over the genome types. -/
def windowFrequency (y : FrequencyState Unit Unit (fun _ ↦ G)) :
    FullHaplotype Unit (fun _ ↦ G) → ℝ :=
  fun h ↦ y.1 ((), h)

omit [DecidableEq G] in
/-- The window frequencies of a state have total mass one. -/
theorem sum_windowFrequency (y : FrequencyState Unit Unit (fun _ ↦ G)) :
    ∑ h, windowFrequency G y h = 1 :=
  y.2.2 ()

/-- The sampling observable `H_f` as a polynomial in the window frequencies. -/
def windowSamplingPolynomial {n : ℕ} (f : (Fin n → FullHaplotype Unit (fun _ ↦ G)) → ℝ) :
    FrequencyPolynomial Unit Unit (fun _ ↦ G) :=
  ∑ w, C (f w) * ∏ a, X ((), w a)

omit [DecidableEq G] in
/-- The sampling polynomial, read at the frequencies `p`, is the sampling observable. -/
theorem eval_lift_windowSamplingPolynomial {n : ℕ}
    (f : (Fin n → FullHaplotype Unit (fun _ ↦ G)) → ℝ) (p : FullHaplotype Unit (fun _ ↦ G) → ℝ) :
    eval (fun v : FrequencyVariable Unit Unit (fun _ ↦ G) ↦ p v.2) (windowSamplingPolynomial G f)
      = samplingObservable f p := by
  simp only [windowSamplingPolynomial, samplingObservable, map_sum, map_mul, map_prod, eval_C,
    eval_X]

/-- The sampling polynomials of arity `n` as a linear map of the observation. -/
def windowSamplingLinear (n : ℕ) :
    ((Fin n → FullHaplotype Unit (fun _ ↦ G)) → ℝ) →ₗ[ℝ]
      FrequencyPolynomial Unit Unit (fun _ ↦ G) where
  toFun f := windowSamplingPolynomial G f
  map_add' f g := by
    simp only [windowSamplingPolynomial, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]
  map_smul' r f := by
    simp only [windowSamplingPolynomial, Pi.smul_apply, smul_eq_mul, map_mul, RingHom.id_apply,
      Finset.smul_sum, smul_eq_C_mul, mul_assoc]

/-- **Line derivatives through the window frequencies are formal partial derivatives.** -/
theorem lineDeriv_windowEval (q : FrequencyPolynomial Unit Unit (fun _ ↦ G))
    (p : FullHaplotype Unit (fun _ ↦ G) → ℝ) (y : FullHaplotype Unit (fun _ ↦ G)) :
    lineDeriv ℝ (fun p' : FullHaplotype Unit (fun _ ↦ G) → ℝ ↦
        eval (fun v : FrequencyVariable Unit Unit (fun _ ↦ G) ↦ p' v.2) q) p (Pi.single y 1)
      = eval (fun v : FrequencyVariable Unit Unit (fun _ ↦ G) ↦ p v.2) (pderiv ((), y) q) := by
  have hline : (fun t : ℝ ↦ eval (fun v : FrequencyVariable Unit Unit (fun _ ↦ G) ↦
        (p + t • (Pi.single y (1 : ℝ) : FullHaplotype Unit (fun _ ↦ G) → ℝ)) v.2) q)
      = fun t : ℝ ↦ eval ((fun v : FrequencyVariable Unit Unit (fun _ ↦ G) ↦ p v.2)
          + t • (Pi.single ((), y) (1 : ℝ) : FrequencyVariable Unit Unit (fun _ ↦ G) → ℝ)) q := by
    funext t
    refine congrArg (fun z : FrequencyVariable Unit Unit (fun _ ↦ G) → ℝ ↦ eval z q) ?_
    funext v
    rcases v with ⟨⟨⟩, h⟩
    simp [Pi.single_apply]
  have h := AncestralSamplingLimit.hasDerivAt_eval_line
    (fun v : FrequencyVariable Unit Unit (fun _ ↦ G) ↦ p v.2)
    (Pi.single ((), y) (1 : ℝ) : FrequencyVariable Unit Unit (fun _ ↦ G) → ℝ) q
  rw [← hline] at h
  rw [lineDeriv, h.deriv]
  simp [Pi.single_apply]

/-- **Second partial derivatives through the window frequencies are formal ones.** -/
theorem secondPartial_windowEval (q : FrequencyPolynomial Unit Unit (fun _ ↦ G))
    (p : FullHaplotype Unit (fun _ ↦ G) → ℝ) (x y : FullHaplotype Unit (fun _ ↦ G)) :
    secondPartial (fun p' : FullHaplotype Unit (fun _ ↦ G) → ℝ ↦
        eval (fun v : FrequencyVariable Unit Unit (fun _ ↦ G) ↦ p' v.2) q) p x y
      = eval (fun v : FrequencyVariable Unit Unit (fun _ ↦ G) ↦ p v.2)
          (pderiv ((), x) (pderiv ((), y) q)) := by
  have hfun : (fun p' : FullHaplotype Unit (fun _ ↦ G) → ℝ ↦ lineDeriv ℝ
        (fun p'' : FullHaplotype Unit (fun _ ↦ G) → ℝ ↦
          eval (fun v : FrequencyVariable Unit Unit (fun _ ↦ G) ↦ p'' v.2) q) p' (Pi.single y 1))
      = fun p' ↦ eval (fun v : FrequencyVariable Unit Unit (fun _ ↦ G) ↦ p' v.2)
          (pderiv ((), y) q) :=
    funext fun p' ↦ lineDeriv_windowEval G q p' y
  rw [secondPartial, hfun]
  exact lineDeriv_windowEval G (pderiv ((), y) q) p x

/-- **The resampling generator is the neutral generator of the resampling rates.**  Read through
the window frequencies, the resampling generator (7.1) of a polynomial observable is its neutral
generator. -/
theorem resamplingGenerator_windowEval (q : FrequencyPolynomial Unit Unit (fun _ ↦ G))
    (p : FullHaplotype Unit (fun _ ↦ G) → ℝ) :
    resamplingGenerator 1 (fun p' : FullHaplotype Unit (fun _ ↦ G) → ℝ ↦
        eval (fun v : FrequencyVariable Unit Unit (fun _ ↦ G) ↦ p' v.2) q) p
      = eval (fun v : FrequencyVariable Unit Unit (fun _ ↦ G) ↦ p v.2)
          (neutralGenerator (resamplingRates G) q) := by
  have hdrift : ∀ coordinate : FrequencyVariable Unit Unit (fun _ ↦ G),
      driftPolynomial (resamplingRates G) coordinate = 0 := fun coordinate ↦ by
    simp [driftPolynomial, resamplingRates]
  have hterm : ∀ x y : FullHaplotype Unit (fun _ ↦ G),
      p x * ((if x = y then (1 : ℝ) else 0) - p y)
          * eval (fun v : FrequencyVariable Unit Unit (fun _ ↦ G) ↦ p v.2)
            (pderiv ((), x) (pderiv ((), y) q))
        = (if x = y then p x * eval (fun v : FrequencyVariable Unit Unit (fun _ ↦ G) ↦ p v.2)
              (pderiv ((), x) (pderiv ((), x) q)) else 0)
          - p x * p y * eval (fun v : FrequencyVariable Unit Unit (fun _ ↦ G) ↦ p v.2)
            (pderiv ((), x) (pderiv ((), y) q)) := by
    intro x y
    split_ifs with hxy
    · rw [hxy]
      ring
    · ring
  have hcoalescence : ∀ i : Unit, (resamplingRates G).coalescence i = 1 := fun _ ↦ rfl
  rw [resamplingGenerator]
  simp only [secondPartial_windowEval, hterm, Finset.sum_sub_distrib, Finset.sum_ite_eq,
    Finset.mem_univ, if_true, neutralGenerator, hdrift, zero_mul, Finset.sum_const_zero,
    zero_add, Finset.univ_unique, PUnit.default_eq_unit, Finset.sum_singleton, demeSecondOrder,
    map_sub, map_sum, map_mul, eval_C, eval_X, hcoalescence]

/-- **On sampling observables the window semigroup is the coalescent dual.**  For every
observation `f` of arity `n`, `T_t H_f (y) = H_{S_t f}(p(y))`, with `S_t = e^{t L_c}` the dual
semigroup of the coalescence generator and `p(y)` the window frequencies of the state. -/
theorem windowSemigroup_samplingPolynomial (hap₀ : FullHaplotype Unit (fun _ ↦ G)) (t : ℝ≥0)
    {n : ℕ} (f : (Fin n → FullHaplotype Unit (fun _ ↦ G)) → ℝ)
    (y : FrequencyState Unit Unit (fun _ ↦ G)) :
    (windowSemigroup G hap₀).operator t (polynomialFunction (windowSamplingPolynomial G f)) y
      = samplingObservable (dualSemigroup 1 t f) (windowFrequency G y) := by
  have hpoly : (windowSemigroup G hap₀).operator t
        (polynomialFunction (windowSamplingPolynomial G f)) y
      = momentFunctional (resamplingRates G) () t y (windowSamplingPolynomial G f) :=
    (congrArg (fun F : C(FrequencyState Unit Unit (fun _ ↦ G), ℝ) ↦ F y)
      (denseExtension_coe _ dense_polynomialSubspace _
        (norm_neutralPolynomialSemigroup_le (resamplingRates G) () hap₀ t)
        ⟨polynomialFunction (windowSamplingPolynomial G f), polynomialFunction_mem _⟩)).trans
      ((neutralPolynomialSemigroup_apply _ _ _ t _ y).trans
        (momentFunctional_congr _ _ hap₀ t y _ _ (polynomialFunction_representative _)))
  rw [hpoly]
  let m : ℝ → ((Fin n → FullHaplotype Unit (fun _ ↦ G)) → ℝ) →ₗ[ℝ] ℝ :=
    fun u ↦ (momentFunctional (resamplingRates G) () u y).comp (windowSamplingLinear G n)
  have hm : ∀ s g, HasDerivAt (fun u ↦ m u g) (m s (coalescenceOperator 1 g)) s := by
    intro s g
    have h := hasDerivAt_momentFunctional (resamplingRates G) () hap₀ y
      (windowSamplingPolynomial G g) s
    have hgen : momentFunctional (resamplingRates G) () s y
          (neutralGenerator (resamplingRates G) (windowSamplingPolynomial G g))
        = momentFunctional (resamplingRates G) () s y
          (windowSamplingPolynomial G (coalescenceOperator 1 g)) := by
      refine momentFunctional_congr _ _ hap₀ s y _ _ (ContinuousMap.ext fun z ↦ ?_)
      have hfun : samplingObservable g = fun p' : FullHaplotype Unit (fun _ ↦ G) → ℝ ↦
          eval (fun v : FrequencyVariable Unit Unit (fun _ ↦ G) ↦ p' v.2)
            (windowSamplingPolynomial G g) :=
        funext fun p' ↦ (eval_lift_windowSamplingPolynomial G g p').symm
      rw [polynomialFunction_apply, polynomialFunction_apply]
      change eval z.1 _ = eval (fun v : FrequencyVariable Unit Unit (fun _ ↦ G) ↦
        windowFrequency G z v.2) (windowSamplingPolynomial G (coalescenceOperator 1 g))
      rw [eval_lift_windowSamplingPolynomial, ← samplingFunctional_apply,
        samplingFunctional_coalescenceOperator 1 g (sum_windowFrequency G z), hfun,
        resamplingGenerator_windowEval]
      rfl
    rw [hgen] at h
    exact h
  have hdual := moments_eq_dualSemigroup 1 m hm (NNReal.coe_nonneg t) f
  calc momentFunctional (resamplingRates G) () t y (windowSamplingPolynomial G f) = m t f := rfl
    _ = m 0 (dualSemigroup 1 t f) := hdual
    _ = samplingObservable (dualSemigroup 1 t f) (windowFrequency G y) := by
      change momentFunctional (resamplingRates G) () 0 y
        (windowSamplingPolynomial G (dualSemigroup 1 t f)) = _
      rw [momentFunctional_zero]
      exact eval_lift_windowSamplingPolynomial G _ (windowFrequency G y)

end Window

end

end Descent.Portability.ResamplingWindowSemigroup
