/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.AncestralLocality.CoalescentDualSemigroup
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecificLimits.Normed

assert_below Descent.PopGen Descent.Spectral Descent.Blindness Descent.Conditionals
assert_below Descent.Portability Descent.Decision Descent.Program

/-!
# Sampling duality with decisions: the moment equation determines the moments

With decisions (`r > 0`) the backward circuit of the research note "Ancestral locality" raises the
arity of an observation by one at every branching. The moment equations of the forward process do
not close on observations of bounded arity, and the exponential of
`Descent.Pangenome.AncestralLocality.CoalescentDualSemigroup` does not exist for the full
circuit. This file proves the duality (7.5) in moment form anyway: a bounded family of moment
functionals obeying the moment equation is determined by its initial moments.

A moment family is `m : ℝ → (k : ℕ) → ((Fin k → H) → ℝ) →ₗ[ℝ] ℝ`, one linear functional on the
observations of every arity at every time. Its moment equation is
`d/dt m_t(f) = momentGenerator c r T m_t f`, the backward generator of Theorem 6 read through
`m_t` (`momentGenerator`). At a fixed vector the sampling functionals give `backwardGenerator`
(`momentGenerator_samplingFunctional`). The generator splits into the coalescence gain
`P f = c ∑_{a<b} C_ab f` (`coalescenceGain`), the branching gain `G f = ∑_e r_e ∑_a B_{a,e} f`
into arity `n + 1` (`branchingGain`), and the loss `dualExitRate c r n · m_t(f)`
(`momentGenerator_eq`).

The proof is Duhamel's formula along the coalescence gain. The gain semigroup `e^{τP}` grows at most
like `e^{c d_n τ}` in sup norm (`norm_gainSemigroup_le`, by Grönwall), and branching costs at most
`n R` with `R = ∑_e r_e` (`norm_branchingGain_le`). Along `u ↦ e^{-λ(t-u)} m_u(e^{(t-u)P} f)`,
with `λ = c d_n + n R`, coalescence and the loss cancel and only branching remains
(`hasDerivAt_duhamel`). For a family that starts at zero and satisfies `|m_t(f)| ≤ K ‖f‖`, a mean
value bound along this curve and induction on the number `j` of branchings give
`|m_t(f)| ≤ K ‖f‖ C(j + n, n) (R t)^j` for every `j` (`abs_moment_le_choose_mul_pow`). These are
the terms of a convergent series when `R t < 1`, so `m_t = 0` there
(`moment_eq_zero_of_mul_lt_one`), and shifting time extends this to every `t ≥ 0`
(`moment_eq_zero`). Two bounded families obeying the moment equation with the same initial moments
agree at every time (`moments_eq_of_momentEquation`).

Scope. The theorem is uniqueness. The backward jump process `f_t` and its expectation
`E_f[m_0(f_t)]` are not constructed, and neither is the forward diffusion. Any family built from
either side that obeys the moment equation and the sup-norm bound equals every other such family,
which is the content of (7.5) once both sides are constructed. The rates are nonnegative, the bound
`|m_t(f)| ≤ ‖f‖` is a hypothesis (it holds for expectations of sampling observables at probability
vectors), and the moment equation is assumed at every time.

## Empirical status

None. The bodies here are linear operators, exponentials and finite sums over a supplied state
space, rate table, rule family and moment family, so no measurement can bear on them.
-/

namespace Descent.Pangenome.AncestralLocality

open Finset Filter Topology

variable {H : Type*} {n : ℕ}

/-! ### The two gains of the backward generator -/

/-- **The coalescence gain `P f = c ∑_{a<b} C_ab f`**: the coalescence part of the backward
generator without its loss term. -/
def coalescenceGain (c : ℝ) : ((Fin n → H) → ℝ) →ₗ[ℝ] ((Fin n → H) → ℝ) where
  toFun f := c • ∑ b, ∑ a ∈ Iio b, coalesceArguments a b f
  map_add' f g := by
    have hadd : ∀ a b : Fin n, coalesceArguments a b (f + g) =
        coalesceArguments a b f + coalesceArguments a b g := fun _ _ ↦ rfl
    simp only [hadd, sum_add_distrib, smul_add]
  map_smul' d f := by
    have hsmul : ∀ a b : Fin n, coalesceArguments a b (d • f) = d • coalesceArguments a b f :=
      fun _ _ ↦ rfl
    simp only [hsmul, ← smul_sum, RingHom.id_apply, smul_comm c d]

/-- **The branching gain `G f = ∑_e r_e ∑_a B_{a,e} f`**: the decision part of the backward
generator without its loss term. It raises the arity by one. -/
def branchingGain {E : Type*} [Fintype E] (r : E → ℝ) (T : E → H → H → H) :
    ((Fin n → H) → ℝ) →ₗ[ℝ] ((Fin (n + 1) → H) → ℝ) where
  toFun f := ∑ e, r e • ∑ a, decisionBranch (T e) a f
  map_add' f g := by
    have hadd : ∀ (e : E) (a : Fin n), decisionBranch (T e) a (f + g) =
        decisionBranch (T e) a f + decisionBranch (T e) a g := fun _ _ ↦ rfl
    simp only [hadd, sum_add_distrib, smul_add]
  map_smul' d f := by
    have hsmul : ∀ (e : E) (a : Fin n), decisionBranch (T e) a (d • f) =
        d • decisionBranch (T e) a f := fun _ _ ↦ rfl
    have hcomm : ∀ (e : E) (x : (Fin (n + 1) → H) → ℝ), r e • d • x = d • r e • x :=
      fun _ _ ↦ smul_comm _ _ _
    simp only [hsmul, ← smul_sum, hcomm, RingHom.id_apply]

/-- A substitution does not raise the sup norm: coalescence. -/
theorem norm_coalesceArguments_le [Fintype H] (a b : Fin n) (f : (Fin n → H) → ℝ) :
    ‖coalesceArguments a b f‖ ≤ ‖f‖ :=
  (pi_norm_le_iff_of_nonneg (norm_nonneg f)).mpr fun _ ↦ norm_le_pi_norm f _

/-- A substitution does not raise the sup norm: decision branching. -/
theorem norm_decisionBranch_le [Fintype H] (T : H → H → H) (a : Fin n)
    (f : (Fin n → H) → ℝ) : ‖decisionBranch T a f‖ ≤ ‖f‖ :=
  (pi_norm_le_iff_of_nonneg (norm_nonneg f)).mpr fun _ ↦ norm_le_pi_norm f _

/-- **The coalescence gain costs at most `c d_n`** in sup norm. -/
theorem norm_coalescenceGain_le [Fintype H] {c : ℝ} (hc : 0 ≤ c) (f : (Fin n → H) → ℝ) :
    ‖coalescenceGain c f‖ ≤ (c * ∑ b : Fin n, ((Iio b).card : ℝ)) * ‖f‖ := by
  show ‖c • ∑ b, ∑ a ∈ Iio b, coalesceArguments a b f‖ ≤ _
  rw [norm_smul, Real.norm_of_nonneg hc, mul_assoc, sum_mul]
  refine mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (sum_le_sum fun b _ ↦ ?_)) hc
  exact (norm_sum_le _ _).trans ((sum_le_sum fun a _ ↦ norm_coalesceArguments_le a b f).trans_eq
    (by rw [sum_const, nsmul_eq_mul]))

/-- **The branching gain costs at most `n R`**, `R = ∑_e r_e`, in sup norm. -/
theorem norm_branchingGain_le [Fintype H] {E : Type*} [Fintype E] {r : E → ℝ}
    (hr : ∀ e, 0 ≤ r e) (T : E → H → H → H) (f : (Fin n → H) → ℝ) :
    ‖branchingGain r T f‖ ≤ (n * ∑ e, r e) * ‖f‖ := by
  show ‖∑ e, r e • ∑ a, decisionBranch (T e) a f‖ ≤ _
  refine (norm_sum_le _ _).trans ?_
  calc ∑ e, ‖r e • ∑ a, decisionBranch (T e) a f‖ ≤ ∑ e, r e * (n * ‖f‖) := by
        refine sum_le_sum fun e _ ↦ ?_
        rw [norm_smul, Real.norm_of_nonneg (hr e)]
        refine mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans ?_) (hr e)
        exact (sum_le_sum fun a _ ↦ norm_decisionBranch_le (T e) a f).trans_eq
          (by rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul])
    _ = (n * ∑ e, r e) * ‖f‖ := by
        rw [← sum_mul]
        ring

/-! ### Moment families and their generator -/

/-- **The moment generator with decisions.** For a family `m` of linear moment functionals on the
observations of every arity: coalescence of every pair `a < b` at rate `c`, and branching of every
argument by every event `e` at rate `r e`, read through `m`. -/
def momentGenerator {E : Type*} [Fintype E] (c : ℝ) (r : E → ℝ) (T : E → H → H → H)
    (m : (k : ℕ) → ((Fin k → H) → ℝ) →ₗ[ℝ] ℝ) (n : ℕ) (f : (Fin n → H) → ℝ) : ℝ :=
  c * ∑ b, ∑ a ∈ Iio b, (m n (coalesceArguments a b f) - m n f) +
    ∑ e, r e * ∑ a, (m (n + 1) (decisionBranch (T e) a f) - m n f)

/-- **The sampling functionals at a vector are a moment family**, and their moment generator is
the backward generator of Theorem 6. -/
theorem momentGenerator_samplingFunctional [Fintype H] [DecidableEq H] {E : Type*} [Fintype E]
    (c : ℝ) (r : E → ℝ) (T : E → H → H → H) (p : H → ℝ) (n : ℕ) (f : (Fin n → H) → ℝ) :
    momentGenerator c r T (fun k ↦ samplingFunctional (n := k) p) n f =
      backwardGenerator c r T f p :=
  rfl

/-- **The moment generator is gain minus loss**: `m(P f) + m(G f) - (c d_n + n R) m(f)`. -/
theorem momentGenerator_eq {E : Type*} [Fintype E] (c : ℝ) (r : E → ℝ) (T : E → H → H → H)
    (m : (k : ℕ) → ((Fin k → H) → ℝ) →ₗ[ℝ] ℝ) (n : ℕ) (f : (Fin n → H) → ℝ) :
    momentGenerator c r T m n f =
      m n (coalescenceGain c f) + m (n + 1) (branchingGain r T f) - dualExitRate c r n * m n f := by
  have hgain : m n (coalescenceGain c f) =
      c * ∑ b, ∑ a ∈ Iio b, m n (coalesceArguments a b f) := by
    show m n (c • ∑ b, ∑ a ∈ Iio b, coalesceArguments a b f) = _
    simp only [map_smul, map_sum, smul_eq_mul]
  have hbranch : m (n + 1) (branchingGain r T f) =
      ∑ e, r e * ∑ a, m (n + 1) (decisionBranch (T e) a f) := by
    show m (n + 1) (∑ e, r e • ∑ a, decisionBranch (T e) a f) = _
    simp only [map_smul, map_sum, smul_eq_mul]
  have hcoal : ∑ b : Fin n, ∑ a ∈ Iio b, (m n (coalesceArguments a b f) - m n f) =
      ∑ b, ∑ a ∈ Iio b, m n (coalesceArguments a b f) -
        (∑ b : Fin n, ((Iio b).card : ℝ)) * m n f := by
    rw [sum_mul, ← sum_sub_distrib]
    refine sum_congr rfl fun b _ ↦ ?_
    rw [sum_sub_distrib, sum_const, nsmul_eq_mul]
  have hdec : ∑ e, r e * ∑ a : Fin n, (m (n + 1) (decisionBranch (T e) a f) - m n f) =
      ∑ e, r e * ∑ a, m (n + 1) (decisionBranch (T e) a f) - (∑ e, r e) * (n * m n f) := by
    rw [sum_mul, ← sum_sub_distrib]
    refine sum_congr rfl fun e _ ↦ ?_
    rw [sum_sub_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  rw [momentGenerator, hgain, hbranch, hcoal, hdec, dualExitRate]
  ring

/-- The moment generator is linear in the family. -/
theorem momentGenerator_sub {E : Type*} [Fintype E] (c : ℝ) (r : E → ℝ) (T : E → H → H → H)
    (m m' : (k : ℕ) → ((Fin k → H) → ℝ) →ₗ[ℝ] ℝ) (n : ℕ) (f : (Fin n → H) → ℝ) :
    momentGenerator c r T (fun k ↦ m k - m' k) n f =
      momentGenerator c r T m n f - momentGenerator c r T m' n f := by
  simp only [momentGenerator_eq, LinearMap.sub_apply]
  ring

/-! ### The gain semigroup -/

/-- **The gain semigroup `e^{τP}`** of the coalescence gain on observations of arity `n`. -/
noncomputable def gainSemigroup [Fintype H] (c τ : ℝ) :
    ((Fin n → H) → ℝ) →L[ℝ] ((Fin n → H) → ℝ) :=
  NormedSpace.exp ℝ (τ • LinearMap.toContinuousLinearMap (coalescenceGain c))

/-- The gain semigroup starts at the identity. -/
theorem gainSemigroup_zero [Fintype H] (c : ℝ) : gainSemigroup (H := H) (n := n) c 0 = 1 := by
  rw [gainSemigroup, zero_smul, NormedSpace.exp_zero]

/-- The gain semigroup moves an observation along the coalescence gain. -/
theorem hasDerivAt_gainSemigroup_apply [Fintype H] (c τ : ℝ) (f : (Fin n → H) → ℝ) :
    HasDerivAt (fun s ↦ gainSemigroup c s f) (coalescenceGain c (gainSemigroup c τ f)) τ := by
  have h := (hasDerivAt_exp_smul_const' (LinearMap.toContinuousLinearMap
    (coalescenceGain (H := H) (n := n) c)) τ).clm_apply (hasDerivAt_const (x := τ) (c := f))
  rw [ContinuousLinearMap.map_zero, add_zero] at h
  exact h

/-- **The gain semigroup grows at most exponentially**: `‖e^{τP} f‖ ≤ ‖f‖ e^{c d_n τ}` for
`τ ≥ 0`, by Grönwall's inequality. -/
theorem norm_gainSemigroup_le [Fintype H] {c : ℝ} (hc : 0 ≤ c) {τ : ℝ} (hτ : 0 ≤ τ)
    (f : (Fin n → H) → ℝ) :
    ‖gainSemigroup c τ f‖ ≤ ‖f‖ * Real.exp ((c * ∑ b : Fin n, ((Iio b).card : ℝ)) * τ) := by
  have h := norm_le_gronwallBound_of_norm_deriv_right_le (f := fun s ↦ gainSemigroup c s f)
    (f' := fun s ↦ coalescenceGain c (gainSemigroup c s f)) (δ := ‖f‖)
    (K := c * ∑ b : Fin n, ((Iio b).card : ℝ)) (ε := 0) (a := 0) (b := τ)
    (fun s _ ↦ (hasDerivAt_gainSemigroup_apply c s f).continuousAt.continuousWithinAt)
    (fun s _ ↦ (hasDerivAt_gainSemigroup_apply c s f).hasDerivWithinAt)
    (by simp [gainSemigroup_zero])
    (fun s _ ↦ by
      rw [add_zero]
      exact norm_coalescenceGain_le hc _)
    τ (Set.right_mem_Icc.mpr hτ)
  rwa [gronwallBound_ε0, sub_zero] at h

/-! ### Duhamel's formula -/

/-- **Duhamel's formula along the coalescence gain.** For a moment family obeying the moment
equation, `u ↦ e^{-λ(t-u)} m_u(e^{(t-u)P} f)` with `λ = c d_n + n R` has derivative
`e^{-λ(t-u)} m_u(G e^{(t-u)P} f)`: coalescence and the loss cancel, and only branching into arity
`n + 1` remains. -/
theorem hasDerivAt_duhamel [Fintype H] [DecidableEq H] {E : Type*} [Fintype E] (c : ℝ)
    (r : E → ℝ) (T : E → H → H → H) (m : ℝ → (k : ℕ) → ((Fin k → H) → ℝ) →ₗ[ℝ] ℝ)
    (hm : ∀ s k (g : (Fin k → H) → ℝ),
      HasDerivAt (fun u ↦ m u k g) (momentGenerator c r T (m s) k g) s)
    (t s : ℝ) (f : (Fin n → H) → ℝ) :
    HasDerivAt
      (fun u ↦ Real.exp (-dualExitRate c r n * (t - u)) * m u n (gainSemigroup c (t - u) f))
      (Real.exp (-dualExitRate c r n * (t - s)) *
        m s (n + 1) (branchingGain r T (gainSemigroup c (t - s) f))) s := by
  have hdecomp : ∀ (u : ℝ) (x : (Fin n → H) → ℝ),
      m u n x = ∑ w, x w * m u n (fun j ↦ if w = j then 1 else 0) := fun u x ↦ by
    conv_lhs => rw [pi_eq_sum_univ x]
    simp only [map_sum, map_smul, smul_eq_mul]
  have hlinear : ∀ x : (Fin n → H) → ℝ,
      ∑ w, x w * momentGenerator c r T (m s) n (fun j ↦ if w = j then 1 else 0) =
        momentGenerator c r T (m s) n x := fun x ↦ by
    have hP : m s n (coalescenceGain c x) =
        ∑ w, x w * m s n (coalescenceGain c (fun j ↦ if w = j then 1 else 0)) := by
      conv_lhs => rw [pi_eq_sum_univ x]
      simp only [map_sum, map_smul, smul_eq_mul]
    have hG : m s (n + 1) (branchingGain r T x) =
        ∑ w, x w * m s (n + 1) (branchingGain r T (fun j ↦ if w = j then 1 else 0)) := by
      conv_lhs => rw [pi_eq_sum_univ x]
      simp only [map_sum, map_smul, smul_eq_mul]
    simp only [momentGenerator_eq, mul_sub, mul_add, sum_sub_distrib, sum_add_distrib]
    rw [hP, hG, hdecomp s x, mul_sum]
    congr 1
    refine sum_congr rfl fun w _ ↦ ?_
    ring
  have hv : HasDerivAt (fun u ↦ gainSemigroup c (t - u) f)
      ((-1 : ℝ) • coalescenceGain c (gainSemigroup c (t - s) f)) s :=
    HasDerivAt.scomp (hg := hasDerivAt_gainSemigroup_apply c (t - s) f)
      (hh := (hasDerivAt_id (x := s)).const_sub t)
  have hsum : HasDerivAt
      (fun u ↦ ∑ w, gainSemigroup c (t - u) f w * m u n (fun j ↦ if w = j then 1 else 0))
      (∑ w, (((-1 : ℝ) • coalescenceGain c (gainSemigroup c (t - s) f)) w *
          m s n (fun j ↦ if w = j then 1 else 0) +
        gainSemigroup c (t - s) f w *
          momentGenerator c r T (m s) n (fun j ↦ if w = j then 1 else 0))) s :=
    HasDerivAt.fun_sum fun w _ ↦ (HasFDerivAt.comp_hasDerivAt
      (hl := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n → H ↦ ℝ) w).hasFDerivAt)
      (hf := hv)).mul (hm s n _)
  have hvalue : ∑ w, (((-1 : ℝ) • coalescenceGain c (gainSemigroup c (t - s) f)) w *
        m s n (fun j ↦ if w = j then 1 else 0) +
      gainSemigroup c (t - s) f w *
        momentGenerator c r T (m s) n (fun j ↦ if w = j then 1 else 0)) =
      m s (n + 1) (branchingGain r T (gainSemigroup c (t - s) f)) -
        dualExitRate c r n * m s n (gainSemigroup c (t - s) f) := by
    rw [sum_add_distrib, ← hdecomp, hlinear, momentGenerator_eq, map_smul, smul_eq_mul]
    ring
  rw [hvalue] at hsum
  have hψ := hsum.congr_of_eventuallyEq (Filter.Eventually.of_forall fun u ↦ hdecomp u _)
  have hexp : HasDerivAt (fun u ↦ Real.exp (-dualExitRate c r n * (t - u)))
      (Real.exp (-dualExitRate c r n * (t - s)) * (-dualExitRate c r n * -1)) s :=
    (((hasDerivAt_id (x := s)).const_sub t).const_mul (-dualExitRate c r n)).exp
  convert hexp.mul hψ using 1
  ring

/-! ### The branching bound and uniqueness -/

/-- **Every branching costs a factor `R t`.** For a moment family obeying the moment equation, with
`|m_t(f)| ≤ K ‖f‖` and zero initial moments, `|m_t(f)| ≤ K ‖f‖ C(j + n, n) (R t)^j` at every
time `t ≥ 0` and for every number `j` of branchings. -/
theorem abs_moment_le_choose_mul_pow [Fintype H] [DecidableEq H] {E : Type*} [Fintype E]
    {c : ℝ} (hc : 0 ≤ c) {r : E → ℝ} (hr : ∀ e, 0 ≤ r e) (T : E → H → H → H)
    (m : ℝ → (k : ℕ) → ((Fin k → H) → ℝ) →ₗ[ℝ] ℝ) {K : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ s k (g : (Fin k → H) → ℝ), |m s k g| ≤ K * ‖g‖)
    (hm : ∀ s k (g : (Fin k → H) → ℝ),
      HasDerivAt (fun u ↦ m u k g) (momentGenerator c r T (m s) k g) s)
    (h0 : ∀ k (g : (Fin k → H) → ℝ), m 0 k g = 0) (j : ℕ) :
    ∀ (k : ℕ) (g : (Fin k → H) → ℝ) {s : ℝ}, 0 ≤ s →
      |m s k g| ≤ K * ‖g‖ * (((j + k).choose k : ℝ) * ((∑ e, r e) * s) ^ j) := by
  have hR0 : 0 ≤ ∑ e, r e := sum_nonneg fun e _ ↦ hr e
  induction j with
  | zero =>
    intro k g s _
    simpa using hbound s k g
  | succ j ih =>
    intro k g t ht
    have hbnd : ∀ u ∈ Set.Ico (0 : ℝ) t,
        ‖Real.exp (-dualExitRate c r k * (t - u)) *
          m u (k + 1) (branchingGain r T (gainSemigroup c (t - u) g))‖ ≤
        K * ‖g‖ * ((j + 1 + k).choose k : ℝ) * (∑ e, r e) ^ (j + 1) *
          (((j + 1 : ℕ) : ℝ) * u ^ j) := by
      intro u hu
      obtain ⟨hu0, hut⟩ := hu
      have htu : 0 ≤ t - u := sub_nonneg.mpr hut.le
      have hexp_le : Real.exp (-dualExitRate c r k * (t - u)) *
          Real.exp ((c * ∑ b : Fin k, ((Iio b).card : ℝ)) * (t - u)) ≤ 1 := by
        rw [← Real.exp_add, Real.exp_le_one_iff, dualExitRate]
        nlinarith [mul_nonneg (mul_nonneg (Nat.cast_nonneg (α := ℝ) k) hR0) htu]
      have hG : ‖branchingGain r T (gainSemigroup c (t - u) g)‖ ≤
          (k * ∑ e, r e) * (‖g‖ * Real.exp ((c * ∑ b : Fin k, ((Iio b).card : ℝ)) * (t - u))) :=
        (norm_branchingGain_le hr T _).trans
          (mul_le_mul_of_nonneg_left (norm_gainSemigroup_le hc htu g)
            (mul_nonneg (Nat.cast_nonneg _) hR0))
      have hih := ih (k + 1) (branchingGain r T (gainSemigroup c (t - u) g)) hu0
      have hchoose : (k : ℝ) * ((j + (k + 1)).choose (k + 1) : ℝ) ≤
          ((j + 1 + k).choose k : ℝ) * ((j + 1 : ℕ) : ℝ) := by
        have h := Nat.choose_succ_right_eq (j + 1 + k) k
        rw [show j + 1 + k - k = j + 1 by omega] at h
        rw [show j + (k + 1) = j + 1 + k by omega]
        have hcast : ((j + 1 + k).choose (k + 1) : ℝ) * ((k : ℝ) + 1) =
            ((j + 1 + k).choose k : ℝ) * ((j + 1 : ℕ) : ℝ) := by
          exact_mod_cast h
        nlinarith [Nat.cast_nonneg (α := ℝ) ((j + 1 + k).choose (k + 1))]
      have hC1 : 0 ≤ ((j + (k + 1)).choose (k + 1) : ℝ) * ((∑ e, r e) * u) ^ j :=
        mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (mul_nonneg hR0 hu0) j)
      have hX : 0 ≤ K * ‖g‖ * (∑ e, r e) ^ (j + 1) * u ^ j :=
        mul_nonneg (mul_nonneg (mul_nonneg hK (norm_nonneg g)) (pow_nonneg hR0 _))
          (pow_nonneg hu0 _)
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, Real.abs_exp]
      calc Real.exp (-dualExitRate c r k * (t - u)) *
            |m u (k + 1) (branchingGain r T (gainSemigroup c (t - u) g))|
          ≤ Real.exp (-dualExitRate c r k * (t - u)) *
            (K * ((k * ∑ e, r e) *
                (‖g‖ * Real.exp ((c * ∑ b : Fin k, ((Iio b).card : ℝ)) * (t - u)))) *
              (((j + (k + 1)).choose (k + 1) : ℝ) * ((∑ e, r e) * u) ^ j)) :=
            mul_le_mul_of_nonneg_left
              (hih.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hG hK) hC1))
              (Real.exp_pos _).le
        _ = (K * ‖g‖ * (∑ e, r e) ^ (j + 1) * u ^ j) *
              ((k : ℝ) * ((j + (k + 1)).choose (k + 1) : ℝ)) *
              (Real.exp (-dualExitRate c r k * (t - u)) *
                Real.exp ((c * ∑ b : Fin k, ((Iio b).card : ℝ)) * (t - u))) := by
            ring
        _ ≤ (K * ‖g‖ * (∑ e, r e) ^ (j + 1) * u ^ j) *
              ((k : ℝ) * ((j + (k + 1)).choose (k + 1) : ℝ)) * 1 :=
            mul_le_mul_of_nonneg_left hexp_le
              (mul_nonneg hX (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)))
        _ ≤ (K * ‖g‖ * (∑ e, r e) ^ (j + 1) * u ^ j) *
              (((j + 1 + k).choose k : ℝ) * ((j + 1 : ℕ) : ℝ)) := by
            rw [mul_one]
            exact mul_le_mul_of_nonneg_left hchoose hX
        _ = K * ‖g‖ * ((j + 1 + k).choose k : ℝ) * (∑ e, r e) ^ (j + 1) *
              (((j + 1 : ℕ) : ℝ) * u ^ j) := by
            ring
    have hmain := image_norm_le_of_norm_deriv_right_le_deriv_boundary
      (f := fun u ↦ Real.exp (-dualExitRate c r k * (t - u)) *
        m u k (gainSemigroup c (t - u) g))
      (f' := fun u ↦ Real.exp (-dualExitRate c r k * (t - u)) *
        m u (k + 1) (branchingGain r T (gainSemigroup c (t - u) g)))
      (a := 0) (b := t)
      (B := fun u ↦ K * ‖g‖ * ((j + 1 + k).choose k : ℝ) * (∑ e, r e) ^ (j + 1) * u ^ (j + 1))
      (B' := fun u ↦ K * ‖g‖ * ((j + 1 + k).choose k : ℝ) * (∑ e, r e) ^ (j + 1) *
        (((j + 1 : ℕ) : ℝ) * u ^ j))
      (fun u _ ↦ (hasDerivAt_duhamel c r T m hm t u g).continuousAt.continuousWithinAt)
      (fun u _ ↦ (hasDerivAt_duhamel c r T m hm t u g).hasDerivWithinAt)
      (by simp [h0])
      (fun u ↦ by
        simpa using (hasDerivAt_pow (j + 1) u).const_mul
          (K * ‖g‖ * ((j + 1 + k).choose k : ℝ) * (∑ e, r e) ^ (j + 1)))
      hbnd (Set.right_mem_Icc.mpr ht)
    have hφt : Real.exp (-dualExitRate c r k * (t - t)) * m t k (gainSemigroup c (t - t) g) =
        m t k g := by
      rw [sub_self, mul_zero, Real.exp_zero, one_mul, gainSemigroup_zero,
        ContinuousLinearMap.one_apply]
    have h : ‖Real.exp (-dualExitRate c r k * (t - t)) * m t k (gainSemigroup c (t - t) g)‖ ≤
        K * ‖g‖ * ((j + 1 + k).choose k : ℝ) * (∑ e, r e) ^ (j + 1) * t ^ (j + 1) := hmain
    rw [hφt, Real.norm_eq_abs] at h
    calc |m t k g| ≤ K * ‖g‖ * ((j + 1 + k).choose k : ℝ) * (∑ e, r e) ^ (j + 1) * t ^ (j + 1) :=
          h
      _ = K * ‖g‖ * (((j + 1 + k).choose k : ℝ) * ((∑ e, r e) * t) ^ (j + 1)) := by ring

/-- **A family starting at zero stays at zero while `R t < 1`.** -/
theorem moment_eq_zero_of_mul_lt_one [Fintype H] [DecidableEq H] {E : Type*} [Fintype E]
    {c : ℝ} (hc : 0 ≤ c) {r : E → ℝ} (hr : ∀ e, 0 ≤ r e) (T : E → H → H → H)
    (m : ℝ → (k : ℕ) → ((Fin k → H) → ℝ) →ₗ[ℝ] ℝ) {K : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ s k (g : (Fin k → H) → ℝ), |m s k g| ≤ K * ‖g‖)
    (hm : ∀ s k (g : (Fin k → H) → ℝ),
      HasDerivAt (fun u ↦ m u k g) (momentGenerator c r T (m s) k g) s)
    (h0 : ∀ k (g : (Fin k → H) → ℝ), m 0 k g = 0) {s : ℝ} (hs : 0 ≤ s)
    (hRs : (∑ e, r e) * s < 1) (k : ℕ) (g : (Fin k → H) → ℝ) : m s k g = 0 := by
  have hx0 : 0 ≤ (∑ e, r e) * s := mul_nonneg (sum_nonneg fun e _ ↦ hr e) hs
  have hsum := summable_choose_mul_geometric_of_norm_lt_one k (r := (∑ e, r e) * s)
    (by rwa [Real.norm_of_nonneg hx0])
  have htends : Tendsto (fun j : ℕ ↦ K * ‖g‖ * (((j + k).choose k : ℝ) * ((∑ e, r e) * s) ^ j))
      atTop (𝓝 0) := by
    have h := hsum.tendsto_cofinite_zero
    rw [Nat.cofinite_eq_atTop] at h
    simpa using h.const_mul (K * ‖g‖)
  have hle : |m s k g| ≤ 0 := ge_of_tendsto' htends fun j ↦
    abs_moment_le_choose_mul_pow hc hr T m hK hbound hm h0 j k g hs
  exact abs_nonpos_iff.mp hle

/-- **A family starting at zero stays at zero.** Shifting time by multiples of `1/(R + 1)` extends
the short-horizon statement to every `t ≥ 0`. -/
theorem moment_eq_zero [Fintype H] [DecidableEq H] {E : Type*} [Fintype E] {c : ℝ} (hc : 0 ≤ c)
    {r : E → ℝ} (hr : ∀ e, 0 ≤ r e) (T : E → H → H → H)
    (m : ℝ → (k : ℕ) → ((Fin k → H) → ℝ) →ₗ[ℝ] ℝ) {K : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ s k (g : (Fin k → H) → ℝ), |m s k g| ≤ K * ‖g‖)
    (hm : ∀ s k (g : (Fin k → H) → ℝ),
      HasDerivAt (fun u ↦ m u k g) (momentGenerator c r T (m s) k g) s)
    (h0 : ∀ k (g : (Fin k → H) → ℝ), m 0 k g = 0) {t : ℝ} (ht : 0 ≤ t) (k : ℕ)
    (g : (Fin k → H) → ℝ) : m t k g = 0 := by
  have hR0 : 0 ≤ ∑ e, r e := sum_nonneg fun e _ ↦ hr e
  have hτ0 : 0 < 1 / (∑ e, r e + 1) := one_div_pos.mpr (by linarith)
  have hRτ : (∑ e, r e) * (1 / (∑ e, r e + 1)) < 1 := by
    rw [mul_one_div, div_lt_one (by linarith)]
    linarith
  have hshift : ∀ j : ℕ, ∀ s : ℝ, 0 ≤ s → s ≤ j * (1 / (∑ e, r e + 1)) →
      ∀ (k : ℕ) (g : (Fin k → H) → ℝ), m s k g = 0 := by
    intro j
    induction j with
    | zero =>
      intro s hs0 hs k g
      have hs' : s = 0 := le_antisymm (by simpa using hs) hs0
      rw [hs']
      exact h0 k g
    | succ j ih =>
      intro s hs0 hs k g
      by_cases hsj : s ≤ j * (1 / (∑ e, r e + 1))
      · exact ih s hs0 hsj k g
      · push_neg at hsj
        have hj0 : 0 ≤ (j : ℝ) * (1 / (∑ e, r e + 1)) := mul_nonneg (Nat.cast_nonneg j) hτ0.le
        have hmshift : ∀ (u : ℝ) (k : ℕ) (g : (Fin k → H) → ℝ),
            HasDerivAt (fun v ↦ m (j * (1 / (∑ e, r e + 1)) + v) k g)
              (momentGenerator c r T (m (j * (1 / (∑ e, r e + 1)) + u)) k g) u :=
          fun u k g ↦ by
            have h := HasDerivAt.comp (hh₂ := hm (j * (1 / (∑ e, r e + 1)) + u) k g)
              (hh := (hasDerivAt_id (x := u)).const_add ((j : ℝ) * (1 / (∑ e, r e + 1))))
            simpa using h
        have hzero := moment_eq_zero_of_mul_lt_one hc hr T
          (fun u ↦ m (j * (1 / (∑ e, r e + 1)) + u)) hK (fun u k g ↦ hbound _ k g) hmshift
          (fun k g ↦ by simpa using ih _ hj0 le_rfl k g) (sub_nonneg.mpr hsj.le)
          (by
            push_cast at hs
            calc (∑ e, r e) * (s - j * (1 / (∑ e, r e + 1)))
                ≤ (∑ e, r e) * (1 / (∑ e, r e + 1)) :=
                  mul_le_mul_of_nonneg_left (by linarith) hR0
              _ < 1 := hRτ)
          k g
        simpa using hzero
  obtain ⟨j, hj⟩ := exists_nat_ge (t / (1 / (∑ e, r e + 1)))
  exact hshift j t ht (by rwa [div_le_iff₀ hτ0] at hj) k g

/-- **The duality (7.5) with decisions, in moment form.** Two families of moment functionals on the
observations of every arity, bounded by the sup norm and obeying the moment equation of the backward
circuit, that agree at time zero agree at every time `t ≥ 0`. -/
theorem moments_eq_of_momentEquation [Fintype H] [DecidableEq H] {E : Type*} [Fintype E] {c : ℝ}
    (hc : 0 ≤ c) {r : E → ℝ} (hr : ∀ e, 0 ≤ r e) (T : E → H → H → H)
    (m m' : ℝ → (k : ℕ) → ((Fin k → H) → ℝ) →ₗ[ℝ] ℝ)
    (hbound : ∀ s k (g : (Fin k → H) → ℝ), |m s k g| ≤ ‖g‖)
    (hbound' : ∀ s k (g : (Fin k → H) → ℝ), |m' s k g| ≤ ‖g‖)
    (hm : ∀ s k (g : (Fin k → H) → ℝ),
      HasDerivAt (fun u ↦ m u k g) (momentGenerator c r T (m s) k g) s)
    (hm' : ∀ s k (g : (Fin k → H) → ℝ),
      HasDerivAt (fun u ↦ m' u k g) (momentGenerator c r T (m' s) k g) s)
    (h0 : ∀ k (g : (Fin k → H) → ℝ), m 0 k g = m' 0 k g) {t : ℝ} (ht : 0 ≤ t) (k : ℕ)
    (g : (Fin k → H) → ℝ) : m t k g = m' t k g := by
  have hdiff := moment_eq_zero hc hr T (fun s k ↦ m s k - m' s k) (K := 2) (by norm_num)
    (fun s k g ↦ by
      show |m s k g - m' s k g| ≤ 2 * ‖g‖
      have h1 := abs_le.mp (hbound s k g)
      have h2 := abs_le.mp (hbound' s k g)
      exact abs_le.mpr ⟨by linarith [h1.1, h2.2], by linarith [h1.2, h2.1]⟩)
    (fun s k g ↦ by
      have h := (hm s k g).sub (hm' s k g)
      rw [← momentGenerator_sub] at h
      exact h)
    (fun k g ↦ by
      show m 0 k g - m' 0 k g = 0
      rw [h0, sub_self])
    ht k g
  exact sub_eq_zero.mp hdiff

end Descent.Pangenome.AncestralLocality
