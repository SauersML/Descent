/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.ResamplingWindowSemigroup

assert_below Descent.Decision Descent.Program

/-!
# Consistency of the resampling window semigroups

Theorem 9 of the research note "Ancestral locality" without decisions (`r = 0`) glues the
resampling semigroups of finite windows of the genome.  Gluing needs that a larger window, read
through the marginalization onto a smaller one, runs the smaller window's semigroup.  This module
proves it for any map of genome types.

Relabelling.  A map `φ : G' → G` of genome types reads an observation of `n` genomes of types `G`
on genomes of types `G'` (`relabelObservation`).  Coalescence identifies arguments, so it commutes
with relabelling (`coalescenceOperator_relabel`), and sampling a relabelled observation at `p` is
sampling the observation at the pushforward `φ_# p` (`samplingObservable_relabel`).  The moment form
of the duality then carries the commutation to the dual semigroup,
`H_{S_t(f ∘ φ)}(p) = H_{S_t f}(φ_# p)` at every time `t ≥ 0`
(`samplingObservable_dualSemigroup_relabel`).

Windows.  On the states of the window models the pushforward is a continuous map of states
(`windowMarginal`), and a sampling polynomial read at the marginal state is the relabelled sampling
polynomial (`polynomialFunction_comp_windowMarginal`).  With the identification of the window
semigroup with the coalescent dual (`ResamplingWindowSemigroup.windowSemigroup_samplingPolynomial`)
this gives consistency on sampling polynomials
(`windowSemigroup_comp_windowMarginal_samplingPolynomial`).  Every polynomial in the window
frequencies is a combination of sampling polynomials (`mem_samplingSpan`, through
`windowSamplingPolynomial_mul_X`), both sides are continuous in the observable, and the polynomial
observables are dense, so the window semigroups are consistent on every continuous observable:
`T'_t (g ∘ φ_#) = (T_t g) ∘ φ_#` (`windowSemigroup_comp_windowMarginal`).

Scope.  Only the resampling rates of `ResamplingWindowSemigroup` are treated.

## Empirical status

None.  The bodies here are exponentials of linear operators and polynomials over supplied finite
type sets, so no measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.ResamplingWindowConsistency

open MvPolynomial Filter Topology PartialHaplotypeDualGenerator NeutralFellerGenerator
  NeutralPolynomialSemigroup ResamplingWindowSemigroup
open Descent.Pangenome.AncestralLocality (samplingObservable samplingFunctional
  samplingFunctional_apply coalescenceOperator coalescenceOperator_apply coalesceArguments
  dualSemigroup dualSemigroup_zero hasDerivAt_dualSemigroup_apply moments_eq_dualSemigroup
  sum_tuple_snoc)
open scoped NNReal

noncomputable section

/-! ## Relabelling the genome types of an observation -/

section Relabel

variable {H H' : Type*} {n : ℕ}

/-- Reading an observation through a map of genome types, argument by argument. -/
def relabelObservation (φ : H' → H) : ((Fin n → H) → ℝ) →ₗ[ℝ] ((Fin n → H') → ℝ) :=
  LinearMap.funLeft ℝ ℝ fun x : Fin n → H' ↦ φ ∘ x

/-- A relabelled observation reads the relabelled genomes. -/
theorem relabelObservation_apply (φ : H' → H) (f : (Fin n → H) → ℝ) (x : Fin n → H') :
    relabelObservation φ f x = f (φ ∘ x) :=
  rfl

/-- **Coalescence commutes with relabelling the genome types.** -/
theorem coalescenceOperator_relabel (φ : H' → H) (c : ℝ) (f : (Fin n → H) → ℝ) :
    coalescenceOperator c (relabelObservation φ f)
      = relabelObservation φ (coalescenceOperator c f) := by
  funext x
  simp only [coalescenceOperator_apply, relabelObservation_apply, Pi.smul_apply, Finset.sum_apply,
    Pi.sub_apply, coalesceArguments, Function.comp_update, Function.comp_apply]

variable [Fintype H] [Fintype H']

/-- The pushforward of a frequency vector along a map of genome types. -/
def pushVector [DecidableEq H] (φ : H' → H) (p : H' → ℝ) : H → ℝ :=
  fun h ↦ ∑ h' ∈ Finset.univ.filter (fun h' ↦ φ h' = h), p h'

/-- **Sampling a relabelled observation is sampling at the pushforward.** -/
theorem samplingObservable_relabel [DecidableEq H] (φ : H' → H) (f : (Fin n → H) → ℝ)
    (p : H' → ℝ) :
    samplingObservable (relabelObservation φ f) p = samplingObservable f (pushVector φ p) := by
  have hfiber : ∀ w : Fin n → H,
      Fintype.piFinset (fun a ↦ Finset.univ.filter fun h' ↦ φ h' = w a)
        = Finset.univ.filter fun x : Fin n → H' ↦ φ ∘ x = w := by
    intro w
    ext x
    simp only [Fintype.mem_piFinset, Finset.mem_filter, Finset.mem_univ, true_and, funext_iff,
      Function.comp_apply]
  have hinner : ∀ w : Fin n → H,
      ∑ x ∈ Finset.univ.filter (fun x : Fin n → H' ↦ φ ∘ x = w), f (φ ∘ x) * ∏ a, p (x a)
        = f w * ∏ a, pushVector φ p (w a) := by
    intro w
    have hcongr : ∑ x ∈ Finset.univ.filter (fun x : Fin n → H' ↦ φ ∘ x = w),
          f (φ ∘ x) * ∏ a, p (x a)
        = ∑ x ∈ Finset.univ.filter (fun x : Fin n → H' ↦ φ ∘ x = w), f w * ∏ a, p (x a) :=
      Finset.sum_congr rfl fun x hx ↦ by rw [(Finset.mem_filter.mp hx).2]
    unfold pushVector
    rw [hcongr, ← Finset.mul_sum, ← hfiber w, ← Finset.prod_univ_sum]
  rw [samplingObservable, samplingObservable,
    ← Finset.sum_fiberwise Finset.univ (fun x : Fin n → H' ↦ φ ∘ x)]
  exact Finset.sum_congr rfl fun w _ ↦ hinner w

/-- **The dual semigroup commutes with relabelling the genome types.**  Read at any vector `p`,
`H_{S_t(f ∘ φ)}(p) = H_{S_t f}(φ_# p)` at every time `t ≥ 0`. -/
theorem samplingObservable_dualSemigroup_relabel [DecidableEq H] [DecidableEq H'] (φ : H' → H)
    (c : ℝ) {t : ℝ} (ht : 0 ≤ t) (f : (Fin n → H) → ℝ) (p : H' → ℝ) :
    samplingObservable (dualSemigroup c t (relabelObservation φ f)) p
      = samplingObservable (dualSemigroup c t f) (pushVector φ p) := by
  let m : ℝ → ((Fin n → H) → ℝ) →ₗ[ℝ] ℝ := fun u ↦
    (samplingFunctional p).comp ((dualSemigroup (H := H') (n := n) c u).toLinearMap.comp
      (relabelObservation φ))
  have hcommute : ∀ (u : ℝ) (g : (Fin n → H') → ℝ),
      dualSemigroup c u (coalescenceOperator c g)
        = coalescenceOperator c (dualSemigroup c u g) := by
    intro u g
    have h : Commute (LinearMap.toContinuousLinearMap (coalescenceOperator (H := H') (n := n) c))
        (NormedSpace.exp ℝ
          (u • LinearMap.toContinuousLinearMap (coalescenceOperator (H := H') (n := n) c))) :=
      ((Commute.refl _).smul_right u).exp_right (𝕂 := ℝ)
    exact (congrArg (fun L : ((Fin n → H') → ℝ) →L[ℝ] ((Fin n → H') → ℝ) ↦ L g) h.eq).symm
  have hm : ∀ s g, HasDerivAt (fun u ↦ m u g) (m s (coalescenceOperator c g)) s := by
    intro s g
    have h := HasFDerivAt.comp_hasDerivAt
      (hl := (LinearMap.toContinuousLinearMap (samplingFunctional (n := n) p)).hasFDerivAt)
      (hf := hasDerivAt_dualSemigroup_apply c s (relabelObservation φ g))
    change HasDerivAt (fun u ↦ samplingFunctional p (dualSemigroup c u (relabelObservation φ g)))
      (samplingFunctional p (dualSemigroup c s (relabelObservation φ (coalescenceOperator c g)))) s
    rw [← coalescenceOperator_relabel, hcommute]
    exact h
  have hdual := moments_eq_dualSemigroup c m hm ht f
  calc samplingObservable (dualSemigroup c t (relabelObservation φ f)) p = m t f := rfl
    _ = m 0 (dualSemigroup c t f) := hdual
    _ = samplingObservable (dualSemigroup c t f) (pushVector φ p) := by
      change samplingFunctional p (dualSemigroup c 0 (relabelObservation φ (dualSemigroup c t f)))
        = _
      rw [dualSemigroup_zero, ContinuousLinearMap.one_apply, samplingFunctional_apply,
        samplingObservable_relabel]

end Relabel

/-! ## Consistency of the window semigroups -/

section Window

variable {G G' : Type*} [Fintype G] [DecidableEq G] [Fintype G'] [DecidableEq G']

/-- A map of genome types, read on the window haplotypes. -/
def windowTypeMap (φ : G' → G) :
    FullHaplotype Unit (fun _ ↦ G') → FullHaplotype Unit (fun _ ↦ G) :=
  fun h _ ↦ φ (h ())

/-- The window marginal frequencies along a map of genome types. -/
def windowMarginalVector (φ : G' → G) (y : FrequencyState Unit Unit (fun _ ↦ G')) :
    FrequencyVariable Unit Unit (fun _ ↦ G) → ℝ :=
  fun v ↦ pushVector (windowTypeMap φ) (windowFrequency G' y) v.2

omit [DecidableEq G'] in
/-- The window marginal frequencies form a state. -/
theorem windowMarginalVector_mem (φ : G' → G) (y : FrequencyState Unit Unit (fun _ ↦ G')) :
    windowMarginalVector φ y ∈ frequencySimplex Unit Unit (fun _ ↦ G) := by
  refine ⟨fun v ↦ Finset.sum_nonneg fun h' _ ↦ y.2.1 ((), h'), fun _ ↦ ?_⟩
  change ∑ h, pushVector (windowTypeMap φ) (windowFrequency G' y) h = 1
  unfold pushVector
  rw [Finset.sum_fiberwise Finset.univ (windowTypeMap φ) (windowFrequency G' y)]
  exact sum_windowFrequency G' y

/-- **The window marginalization** along a map of genome types, a continuous map of states. -/
def windowMarginal (φ : G' → G) :
    C(FrequencyState Unit Unit (fun _ ↦ G'), FrequencyState Unit Unit (fun _ ↦ G)) where
  toFun y := ⟨windowMarginalVector φ y, windowMarginalVector_mem φ y⟩
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    refine continuous_pi fun v ↦ ?_
    change Continuous fun y : FrequencyState Unit Unit (fun _ ↦ G') ↦
      ∑ h' ∈ Finset.univ.filter (fun h' ↦ windowTypeMap φ h' = v.2), y.1 ((), h')
    exact continuous_finset_sum _ fun h' _ ↦
      (continuous_apply ((), h')).comp continuous_subtype_val

/-- The window frequencies of a marginal state are the pushforward of the window frequencies. -/
theorem windowFrequency_windowMarginal (φ : G' → G) (y : FrequencyState Unit Unit (fun _ ↦ G')) :
    windowFrequency G (windowMarginal φ y) = pushVector (windowTypeMap φ) (windowFrequency G' y) :=
  rfl

/-- A sampling polynomial read at the marginal state is the relabelled sampling polynomial. -/
theorem polynomialFunction_comp_windowMarginal (φ : G' → G) {n : ℕ}
    (f : (Fin n → FullHaplotype Unit (fun _ ↦ G)) → ℝ) :
    (polynomialFunction (windowSamplingPolynomial G f)).comp (windowMarginal φ)
      = polynomialFunction
          (windowSamplingPolynomial G' (relabelObservation (windowTypeMap φ) f)) := by
  ext y
  change eval (fun v : FrequencyVariable Unit Unit (fun _ ↦ G) ↦
      windowFrequency G (windowMarginal φ y) v.2) (windowSamplingPolynomial G f)
    = eval (fun v : FrequencyVariable Unit Unit (fun _ ↦ G') ↦ windowFrequency G' y v.2)
      (windowSamplingPolynomial G' (relabelObservation (windowTypeMap φ) f))
  rw [eval_lift_windowSamplingPolynomial, eval_lift_windowSamplingPolynomial,
    samplingObservable_relabel, windowFrequency_windowMarginal]

/-- **Window consistency on sampling polynomials.**  The larger window's semigroup, applied to a
sampling polynomial read at the marginal state, is the smaller window's semigroup read at the
marginal state. -/
theorem windowSemigroup_comp_windowMarginal_samplingPolynomial (φ : G' → G)
    (hap₀ : FullHaplotype Unit (fun _ ↦ G)) (hap₀' : FullHaplotype Unit (fun _ ↦ G')) (t : ℝ≥0)
    {n : ℕ} (f : (Fin n → FullHaplotype Unit (fun _ ↦ G)) → ℝ) :
    (windowSemigroup G' hap₀').operator t
        ((polynomialFunction (windowSamplingPolynomial G f)).comp (windowMarginal φ))
      = ((windowSemigroup G hap₀).operator t
          (polynomialFunction (windowSamplingPolynomial G f))).comp (windowMarginal φ) := by
  rw [polynomialFunction_comp_windowMarginal]
  ext y
  rw [ContinuousMap.comp_apply, windowSemigroup_samplingPolynomial,
    windowSemigroup_samplingPolynomial,
    samplingObservable_dualSemigroup_relabel _ 1 (NNReal.coe_nonneg t),
    windowFrequency_windowMarginal]

/-- An observation with one more argument, read as the indicator of the genome type `h`. -/
def snocObservation {n : ℕ} (f : (Fin n → FullHaplotype Unit (fun _ ↦ G)) → ℝ)
    (h : FullHaplotype Unit (fun _ ↦ G)) :
    (Fin (n + 1) → FullHaplotype Unit (fun _ ↦ G)) → ℝ :=
  fun x ↦ f (Fin.init x) * if x (Fin.last n) = h then 1 else 0

/-- Multiplying a sampling polynomial by a window frequency appends an indicator argument. -/
theorem windowSamplingPolynomial_mul_X {n : ℕ}
    (f : (Fin n → FullHaplotype Unit (fun _ ↦ G)) → ℝ) (h : FullHaplotype Unit (fun _ ↦ G)) :
    windowSamplingPolynomial G f * X ((), h)
      = windowSamplingPolynomial G (snocObservation f h) := by
  have hterm : ∀ (w : Fin n → FullHaplotype Unit (fun _ ↦ G)) (y : FullHaplotype Unit (fun _ ↦ G)),
      C (snocObservation f h (Fin.snoc w y))
          * ∏ a, X ((), (Fin.snoc w y : Fin (n + 1) → FullHaplotype Unit (fun _ ↦ G)) a)
        = if y = h then C (f w) * (∏ a, X ((), w a)) * X ((), h) else 0 := by
    intro w y
    rw [Fin.prod_univ_castSucc]
    simp only [snocObservation, Fin.init_snoc, Fin.snoc_last, Fin.snoc_castSucc]
    split_ifs with hy
    · rw [hy, mul_one, mul_assoc]
    · rw [mul_zero, map_zero, zero_mul]
  have hsnoc : ∑ u : Fin (n + 1) → FullHaplotype Unit (fun _ ↦ G),
        C (snocObservation f h u) * ∏ a, X ((), u a)
      = ∑ w : Fin n → FullHaplotype Unit (fun _ ↦ G), ∑ y : FullHaplotype Unit (fun _ ↦ G),
          C (snocObservation f h (Fin.snoc w y))
            * ∏ a, X ((), (Fin.snoc w y : Fin (n + 1) → FullHaplotype Unit (fun _ ↦ G)) a) := by
    calc ∑ u : Fin (n + 1) → FullHaplotype Unit (fun _ ↦ G),
          C (snocObservation f h u) * ∏ a, X ((), u a)
        = ∑ x : FullHaplotype Unit (fun _ ↦ G) × (Fin n → FullHaplotype Unit (fun _ ↦ G)),
            C (snocObservation f h (Fin.snoc x.2 x.1))
              * ∏ a, X ((), (Fin.snoc x.2 x.1 : Fin (n + 1) → FullHaplotype Unit (fun _ ↦ G)) a) :=
          (Fintype.sum_equiv (Fin.snocEquiv fun _ ↦ FullHaplotype Unit (fun _ ↦ G)) _ _
            fun _ ↦ rfl).symm
      _ = ∑ y : FullHaplotype Unit (fun _ ↦ G), ∑ w : Fin n → FullHaplotype Unit (fun _ ↦ G),
            C (snocObservation f h (Fin.snoc w y))
              * ∏ a, X ((), (Fin.snoc w y : Fin (n + 1) → FullHaplotype Unit (fun _ ↦ G)) a) :=
          Fintype.sum_prod_type _
      _ = _ := Finset.sum_comm
  rw [windowSamplingPolynomial, windowSamplingPolynomial, Finset.sum_mul, hsnoc]
  refine Finset.sum_congr rfl fun w _ ↦ ?_
  rw [Finset.sum_congr rfl fun y _ ↦ hterm w y, Finset.sum_ite_eq', if_pos (Finset.mem_univ h)]

variable (G) in
/-- The span of the sampling polynomials of every arity in the window frequencies. -/
def samplingSpan : Submodule ℝ (FrequencyPolynomial Unit Unit (fun _ ↦ G)) :=
  Submodule.span ℝ {q | ∃ (n : ℕ) (f : (Fin n → FullHaplotype Unit (fun _ ↦ G)) → ℝ),
    windowSamplingPolynomial G f = q}

/-- **Every polynomial in the window frequencies is a combination of sampling polynomials.** -/
theorem mem_samplingSpan (q : FrequencyPolynomial Unit Unit (fun _ ↦ G)) :
    q ∈ samplingSpan G := by
  induction q using MvPolynomial.induction_on with
  | C a =>
    refine Submodule.subset_span ⟨0, fun _ ↦ a, ?_⟩
    simp [windowSamplingPolynomial]
  | add p q hp hq => exact Submodule.add_mem _ hp hq
  | mul_X p v hp =>
    obtain ⟨⟨⟩, h⟩ := v
    refine Submodule.span_induction (p := fun r _ ↦ r * X ((), h) ∈ samplingSpan G)
      ?_ ?_ ?_ ?_ hp
    · rintro r ⟨n, f, rfl⟩
      exact Submodule.subset_span ⟨n + 1, snocObservation f h,
        (windowSamplingPolynomial_mul_X f h).symm⟩
    · change (0 : FrequencyPolynomial Unit Unit (fun _ ↦ G)) * X ((), h) ∈ samplingSpan G
      rw [zero_mul]
      exact Submodule.zero_mem _
    · intro r s _ _ hr hs
      rw [add_mul]
      exact Submodule.add_mem _ hr hs
    · intro a r _ hr
      rw [smul_mul_assoc]
      exact Submodule.smul_mem _ a hr

/-- **The window semigroups are consistent.**  For every continuous observable `g` of the smaller
window, `T'_t (g ∘ φ_#) = (T_t g) ∘ φ_#`: the larger window, read through the marginalization, runs
the smaller window's semigroup. -/
theorem windowSemigroup_comp_windowMarginal (φ : G' → G)
    (hap₀ : FullHaplotype Unit (fun _ ↦ G)) (hap₀' : FullHaplotype Unit (fun _ ↦ G')) (t : ℝ≥0)
    (g : C(FrequencyState Unit Unit (fun _ ↦ G), ℝ)) :
    (windowSemigroup G' hap₀').operator t (g.comp (windowMarginal φ))
      = ((windowSemigroup G hap₀).operator t g).comp (windowMarginal φ) := by
  have hpoly : ∀ q : FrequencyPolynomial Unit Unit (fun _ ↦ G),
      (windowSemigroup G' hap₀').operator t ((polynomialFunction q).comp (windowMarginal φ))
        = ((windowSemigroup G hap₀).operator t (polynomialFunction q)).comp
            (windowMarginal φ) := by
    intro q
    refine Submodule.span_induction (p := fun r _ ↦
        (windowSemigroup G' hap₀').operator t ((polynomialFunction r).comp (windowMarginal φ))
          = ((windowSemigroup G hap₀).operator t (polynomialFunction r)).comp
              (windowMarginal φ)) ?_ ?_ ?_ ?_ (mem_samplingSpan q)
    · rintro r ⟨n, f, rfl⟩
      exact windowSemigroup_comp_windowMarginal_samplingPolynomial φ hap₀ hap₀' t f
    · have hzero : polynomialFunction (0 : FrequencyPolynomial Unit Unit (fun _ ↦ G)) = 0 :=
        ContinuousMap.ext fun x ↦ by simp [polynomialFunction_apply]
      beta_reduce
      rw [hzero, ContinuousMap.zero_comp, map_zero, map_zero, ContinuousMap.zero_comp]
    · intro r s _ _ hr hs
      rw [polynomialFunction_add, ContinuousMap.add_comp, map_add, map_add, hr, hs,
        ContinuousMap.add_comp]
    · intro a r _ hr
      rw [polynomialFunction_smul, ContinuousMap.smul_comp, map_smul, map_smul, hr,
        ContinuousMap.smul_comp]
  have hcont₁ : Continuous fun g : C(FrequencyState Unit Unit (fun _ ↦ G), ℝ) ↦
      (windowSemigroup G' hap₀').operator t (g.comp (windowMarginal φ)) :=
    ((windowSemigroup G' hap₀').operator t).continuous.comp
      (ContinuousMap.continuous_precomp (windowMarginal φ))
  have hcont₂ : Continuous fun g : C(FrequencyState Unit Unit (fun _ ↦ G), ℝ) ↦
      ((windowSemigroup G hap₀).operator t g).comp (windowMarginal φ) :=
    (ContinuousMap.continuous_precomp (windowMarginal φ)).comp
      ((windowSemigroup G hap₀).operator t).continuous
  have hagree := hcont₁.ext_on dense_polynomialSubspace hcont₂ fun g hg ↦ by
    obtain ⟨q, rfl⟩ := hg
    exact hpoly q
  exact congrFun hagree g

end Window

end

end Descent.Portability.ResamplingWindowConsistency
