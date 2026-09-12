/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Coalescent.StructuredPresentDay
import Descent.Pangenome.AncestralLocality.LocalityBounds
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.Topology.Algebra.Module.FiniteDimension

assert_below Descent.PopGen Descent.Spectral Descent.Blindness Descent.Conditionals
assert_below Descent.Portability Descent.Decision Descent.Program

/-!
# Dynkin's formula for the truncated support chain

`Descent.Pangenome.AncestralLocality.LocalityBounds` proves Theorems 7 and 8 of
`ANCESTRAL_LOCALITY.md` for any marginal laws of the backward circuit that obey Dynkin's formula.
This file builds laws that obey it, the laws of the support circuit truncated after `M` decisions,
and proves the bounds for them with no such hypothesis and with constants that do not depend on
`M`.

## Finite jump chains

`jumpRateGenerator rate` is the generator matrix of a finite chain that jumps from `x` to `y` at
rate `rate x y`. It acts by its jumps (`jumpRateGenerator_mulVec`), is Metzler for nonnegative
rates (`jumpRateGenerator_apply_nonneg`), and its rows sum to zero (`sum_jumpRateGenerator`).
`jumpChainLaw Q x₀ t` is the row `x₀` of the corpus matrix exponential, `μ_t = δ_{x₀} e^{tQ}`.

Dynkin's formula `d/dt ∫ f dμ_t = ∫ Q f dμ_t` is `hasDerivAt_sum_jumpChainLaw_mul`, and its
compensator form `∫ G dμ_T - G(x₀) = ∫_0^T ∫ Q G dμ_t dt` is
`sum_jumpChainLaw_mul_sub_eq_integral`. A Metzler generator gives nonnegative laws
(`jumpChainLaw_nonneg`), a generator whose rows sum to zero gives mass one (`sum_jumpChainLaw`),
and a drift bound `Q F ≤ K F` gives `∫ F dμ_t ≤ F(x₀) e^{K t}` (`sum_jumpChainLaw_mul_le_exp`).

## The support chain truncated after `M` decisions

A state of `SupportChainState V n M` holds the supports of `n + M` argument slots, in the tag form
`A : Fin (n + M) → Finset V` of `Descent.Pangenome.AncestralLocality.AncestralDecision`, and the
number of decisions taken. `supportChainBranch` is the decision (7.6): while fewer than `M`
decisions have been taken, the argument in slot `a` gains `j` and the new parental argument fills
slot `n + k` with `{i, j}`. After `M` decisions no further decision is taken. Coalescence is
`coalesceTags`, at rate `c` per pair of occupied slots. `supportChainRate` collects the rates,
`supportChainGenerator` is the generator, and `supportChainLaw` is the law started from
`supportChainStart`, `n` arguments carrying `A` and no decisions.

A decision raises the tag weight by at most `w i + 2 w j` (`tagWeight_supportChainBranch_le`), so
the generator obeys `Q Z^{(w)} ≤ D (1 + 2κ) Z^{(w)}` (`supportChainGenerator_tagWeight_le`). The
decision count has drift at most `decisionRate r` (`supportChainGenerator_count_le`). For every
truncation `M`:

* (8.2): `E Z_T ≤ n |A| e^{3 D T}`, `sum_supportChainLaw_mul_tagCount_le`;
* (8.3): `E B_T ≤ (n |A| / 3)(e^{3 D T} - 1)`, `sum_supportChainLaw_mul_count_le`;
* the light-cone count `E Z^{(a)}_T ≤ n |A| e^{D (1 + 2a) T}`,
  `sum_supportChainLaw_mul_lightWeight_le`;
* (9.1): `sum_supportChainLaw_escape_le`; (9.2): `sum_supportChainLaw_escape_le_radius`; and no
  escape when `D T = 0`: `sum_supportChainLaw_escape_eq_zero`.

Scope. The chain is the support circuit truncated after `M` decisions: after the `M`-th decision
no further decision is taken, while coalescence continues. It is not proved here that the
truncated laws converge to a law of the untruncated circuit as `M → ∞`, nor that the truncated
and untruncated circuits agree until the `M`-th decision. The circuit records supports only, not
the function `f` of the sampling dual. The genome is finite, and the rates are real with
`r i j ≥ 0` and row sums at most `D`. The laws are rows of the matrix exponential of the
generator, and no path space is constructed.

## Empirical status

None. The bodies here are finite sums, matrix exponentials and calculus on a supplied rate table,
and no measurement can bear on them.
-/

namespace Descent.Pangenome.AncestralLocality

open Finset
open scoped Matrix

noncomputable section

/-! ### Finite jump chains -/

section JumpChain

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

/-- **The generator matrix of a finite jump chain** that moves from `x` to `y` at rate
`rate x y`: the rates, less the total exit rate on the diagonal. -/
def jumpRateGenerator (rate : σ → σ → ℝ) : Matrix σ σ ℝ :=
  fun x y ↦ rate x y - if x = y then ∑ z, rate x z else 0

/-- **The generator acts by jumps**: `(Q f)(x) = Σ_y rate x y (f y - f x)`. -/
theorem jumpRateGenerator_mulVec (rate : σ → σ → ℝ) (f : σ → ℝ) (x : σ) :
    (jumpRateGenerator rate *ᵥ f) x = ∑ y, rate x y * (f y - f x) := by
  have hdiag : ∑ y, (if x = y then ∑ z, rate x z else 0) * f y = ∑ z, rate x z * f x := by
    simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte,
      Finset.sum_mul]
  calc (jumpRateGenerator rate *ᵥ f) x
      = ∑ y, (rate x y * f y - (if x = y then ∑ z, rate x z else 0) * f y) := by
        simp only [Matrix.mulVec, dotProduct, jumpRateGenerator, sub_mul]
    _ = ∑ y, rate x y * (f y - f x) := by
        rw [Finset.sum_sub_distrib, hdiag, ← Finset.sum_sub_distrib]
        simp only [mul_sub]

/-- Nonnegative rates give a Metzler generator. -/
theorem jumpRateGenerator_apply_nonneg {rate : σ → σ → ℝ} (hrate : ∀ x y, 0 ≤ rate x y)
    {x y : σ} (hxy : x ≠ y) : 0 ≤ jumpRateGenerator rate x y := by
  simp only [jumpRateGenerator, if_neg hxy, sub_zero]
  exact hrate x y

/-- The rows of a jump generator sum to zero. -/
theorem sum_jumpRateGenerator (rate : σ → σ → ℝ) (x : σ) :
    ∑ y, jumpRateGenerator rate x y = 0 := by
  simp only [jumpRateGenerator, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ,
    ↓reduceIte, sub_self]

/-- **The law at time `t` of a finite jump chain** with generator `Q` started at `x₀`: the row
`x₀` of the matrix exponential, `μ_t = δ_{x₀} e^{tQ}`. -/
def jumpChainLaw (Q : Matrix σ σ ℝ) (x₀ : σ) (t : ℝ) (y : σ) : ℝ :=
  Coalescent.matrixExponential Q t x₀ y

/-- At time zero the law is the point mass at `x₀`. -/
theorem sum_jumpChainLaw_zero_mul (Q : Matrix σ σ ℝ) (x₀ : σ) (f : σ → ℝ) :
    ∑ y, jumpChainLaw Q x₀ 0 y * f y = f x₀ := by
  simp [jumpChainLaw, Coalescent.matrixExponential_zero, Matrix.one_apply]

/-- **A Metzler generator gives a nonnegative law** at every time `t ≥ 0`. -/
theorem jumpChainLaw_nonneg {Q : Matrix σ σ ℝ} (hQ : ∀ x y, x ≠ y → 0 ≤ Q x y) (x₀ : σ)
    {t : ℝ} (ht : 0 ≤ t) (y : σ) : 0 ≤ jumpChainLaw Q x₀ t y :=
  Coalescent.matrixExponential_apply_nonneg_of_metzler Q hQ t ht x₀ y

/-- **Dynkin's formula for a finite jump chain**: `d/dt ∫ f dμ_t = ∫ Q f dμ_t` for the laws
`μ_t = δ_{x₀} e^{tQ}`, Kolmogorov's forward equation read against an observable. -/
theorem hasDerivAt_sum_jumpChainLaw_mul (Q : Matrix σ σ ℝ) (x₀ : σ) (f : σ → ℝ) (t : ℝ) :
    HasDerivAt (fun u ↦ ∑ y, jumpChainLaw Q x₀ u y * f y)
      (∑ y, jumpChainLaw Q x₀ t y * (Q *ᵥ f) y) t := by
  let evaluation : Matrix σ σ ℝ →ₗ[ℝ] ℝ :=
    { toFun := fun N ↦ ∑ y, N x₀ y * f y
      map_add' := fun N N' ↦ by
        simp only [Matrix.add_apply, add_mul, Finset.sum_add_distrib]
      map_smul' := fun k N ↦ by
        simp only [Matrix.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum, mul_assoc] }
  have hcont : Continuous evaluation := LinearMap.continuous_of_finiteDimensional evaluation
  have key : HasDerivAt (fun u : ℝ ↦ evaluation (NormedSpace.exp ℝ (u • Q)))
      (evaluation (NormedSpace.exp ℝ (t • Q) * Q)) t := by
    open scoped Matrix.Norms.Operator in
    exact (⟨evaluation, hcont⟩ : Matrix σ σ ℝ →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt (x := t)
      (hasDerivAt_exp_smul_const (𝕂 := ℝ) Q t)
  have hlaw : ∀ u y, jumpChainLaw Q x₀ u y = NormedSpace.exp ℝ (u • Q) x₀ y := fun u y ↦ by
    rw [jumpChainLaw, Coalescent.matrixExponential_eq_normedSpace_exp]
  simp only [hlaw]
  refine key.congr_deriv ?_
  show ∑ y, (NormedSpace.exp ℝ (t • Q) * Q) x₀ y * f y =
    ∑ y, NormedSpace.exp ℝ (t • Q) x₀ y * (Q *ᵥ f) y
  simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct, Finset.sum_mul, Finset.mul_sum,
    mul_assoc]
  exact Finset.sum_comm

/-- **A generator whose rows sum to zero keeps total mass one.** -/
theorem sum_jumpChainLaw {Q : Matrix σ σ ℝ} (hrow : ∀ x, ∑ y, Q x y = 0) (x₀ : σ) (t : ℝ) :
    ∑ y, jumpChainLaw Q x₀ t y = 1 := by
  have hone : ∀ x, (Q *ᵥ fun _ ↦ (1 : ℝ)) x = 0 := fun x ↦ by
    simpa only [Matrix.mulVec, dotProduct, mul_one] using hrow x
  have hderiv : ∀ u, HasDerivAt (fun u ↦ ∑ y, jumpChainLaw Q x₀ u y * 1) 0 u := fun u ↦ by
    simpa only [hone, mul_zero, Finset.sum_const_zero] using
      hasDerivAt_sum_jumpChainLaw_mul Q x₀ (fun _ ↦ 1) u
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := t)
    (fun u _ ↦ hderiv u) intervalIntegrable_const
  beta_reduce at hftc
  rw [intervalIntegral.integral_zero, sum_jumpChainLaw_zero_mul] at hftc
  simpa only [mul_one] using (by linarith : ∑ y, jumpChainLaw Q x₀ t y * 1 = 1)

/-- **Grönwall along the chain.** If the generator obeys `Q F ≤ K F` at every state, then
`∫ F dμ_t ≤ F(x₀) e^{K t}` at every time `t ≥ 0`. -/
theorem sum_jumpChainLaw_mul_le_exp {Q : Matrix σ σ ℝ} (hQ : ∀ x y, x ≠ y → 0 ≤ Q x y)
    {F : σ → ℝ} {K : ℝ} (hF : ∀ x, (Q *ᵥ F) x ≤ K * F x) (x₀ : σ) {t : ℝ} (ht : 0 ≤ t) :
    ∑ y, jumpChainLaw Q x₀ t y * F y ≤ F x₀ * Real.exp (K * t) := by
  have hderiv := hasDerivAt_sum_jumpChainLaw_mul Q x₀ F
  refine le_mul_exp_of_hasDerivWithinAt (m := fun u ↦ ∑ y, jumpChainLaw Q x₀ u y * F y)
    (m' := fun u ↦ ∑ y, jumpChainLaw Q x₀ u y * (Q *ᵥ F) y) (T := t)
    (fun u _ ↦ (hderiv u).continuousAt.continuousWithinAt)
    (fun u _ ↦ (hderiv u).hasDerivWithinAt) (fun u hu ↦ ?_)
    (sum_jumpChainLaw_zero_mul Q x₀ F).le t ⟨ht, le_rfl⟩
  calc ∑ y, jumpChainLaw Q x₀ u y * (Q *ᵥ F) y
      ≤ ∑ y, jumpChainLaw Q x₀ u y * (K * F y) :=
        Finset.sum_le_sum fun y _ ↦
          mul_le_mul_of_nonneg_left (hF y) (jumpChainLaw_nonneg hQ x₀ hu.1 y)
    _ = K * ∑ y, jumpChainLaw Q x₀ u y * F y := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun y _ ↦ by ring

/-- **The compensator form of Dynkin's formula**:
`∫ G dμ_T - G(x₀) = ∫_0^T ∫ Q G dμ_t dt`. -/
theorem sum_jumpChainLaw_mul_sub_eq_integral (Q : Matrix σ σ ℝ) (x₀ : σ) (G : σ → ℝ) (T : ℝ) :
    ∑ y, jumpChainLaw Q x₀ T y * G y - G x₀ =
      ∫ t in (0 : ℝ)..T, ∑ y, jumpChainLaw Q x₀ t y * (Q *ᵥ G) y := by
  have hcont : Continuous fun t ↦ ∑ y, jumpChainLaw Q x₀ t y * (Q *ᵥ G) y :=
    continuous_iff_continuousAt.mpr fun t ↦
      (hasDerivAt_sum_jumpChainLaw_mul Q x₀ (Q *ᵥ G) t).continuousAt
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ ↦ hasDerivAt_sum_jumpChainLaw_mul Q x₀ G t) (hcont.intervalIntegrable 0 T),
    sum_jumpChainLaw_zero_mul]

end JumpChain

/-! ### Tag weights of slot updates -/

section Tags

variable {V : Type*}

/-- Replacing the support of one slot changes the tag weight by the difference of the weights. -/
theorem tagWeight_update (w : V → ℝ) {N : ℕ} (A : Fin N → Finset V) (a : Fin N)
    (S : Finset V) :
    tagWeight w (Function.update A a S) = tagWeight w A - ∑ v ∈ A a, w v + ∑ v ∈ S, w v := by
  have hsplit := Finset.sum_eq_add_sum_diff_singleton (Finset.mem_univ a)
    fun c ↦ ∑ v ∈ A c, w v
  have hupdate := Finset.sum_update_of_mem (Finset.mem_univ a) (fun c ↦ ∑ v ∈ A c, w v)
    (∑ v ∈ S, w v)
  have hcomp : ∑ c, ∑ v ∈ Function.update A a S c, w v =
      ∑ c, Function.update (fun c ↦ ∑ v ∈ A c, w v) a (∑ v ∈ S, w v) c :=
    Finset.sum_congr rfl fun c _ ↦
      Function.apply_update (fun (_ : Fin N) (T : Finset V) ↦ ∑ v ∈ T, w v) A a S c
  beta_reduce at hsplit hupdate
  simp only [tagWeight]
  rw [hcomp, hupdate]
  linarith

/-- Replacing one slot raises the tag weight by at most the weight of the new support. -/
theorem tagWeight_update_le {w : V → ℝ} (hw : ∀ v, 0 ≤ w v) {N : ℕ} (A : Fin N → Finset V)
    (a : Fin N) (S : Finset V) :
    tagWeight w (Function.update A a S) ≤ tagWeight w A + ∑ v ∈ S, w v := by
  rw [tagWeight_update]
  linarith [Finset.sum_nonneg fun v (_ : v ∈ A a) ↦ hw v]

/-- A nonnegative weight has a nonnegative tag weight. -/
theorem tagWeight_nonneg {w : V → ℝ} (hw : ∀ v, 0 ≤ w v) {N : ℕ} (A : Fin N → Finset V) :
    0 ≤ tagWeight w A :=
  Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun v _ ↦ hw v

/-- **The state of the support chain truncated after `M` decisions**: the supports of `n + M`
argument slots and the number of decisions taken so far. -/
abbrev SupportChainState (V : Type*) (n M : ℕ) :=
  (Fin (n + M) → Finset V) × Fin (M + 1)

/-- **The initial state**: `n` arguments carrying the observation set `A`, `M` empty slots and
no decisions. -/
def supportChainStart (A : Finset V) (n M : ℕ) : SupportChainState V n M :=
  (Fin.append (fun _ : Fin n ↦ A) (fun _ : Fin M ↦ ∅), 0)

/-- The initial tag weight is `n` times the weight of `A`. -/
theorem tagWeight_supportChainStart (w : V → ℝ) (A : Finset V) (n M : ℕ) :
    tagWeight w (supportChainStart A n M).1 = n * ∑ v ∈ A, w v := by
  simp [supportChainStart, tagWeight, Fin.sum_univ_add]

end Tags

/-! ### The truncated support chain -/

section SupportChain

variable {V : Type*} [DecidableEq V] {n M : ℕ}

/-- **A decision in the truncated chain.** While fewer than `M` decisions have been taken, the
argument in slot `a` checks `i` against `j`: its support gains `j`, and the new parental argument
fills slot `n + k` with support `{i, j}`. After `M` decisions the state is left unchanged. -/
def supportChainBranch (x : SupportChainState V n M) (a : Fin (n + M)) (i j : V) :
    SupportChainState V n M :=
  if h : (x.2 : ℕ) < M then
    (Function.update (Function.update x.1 a (insert j (x.1 a))) ⟨n + (x.2 : ℕ), by omega⟩ {i, j},
      ⟨(x.2 : ℕ) + 1, by omega⟩)
  else x

/-- **A decision raises the tag weight by at most `w i + 2 w j`.** -/
theorem tagWeight_supportChainBranch_le {w : V → ℝ} (hw : ∀ v, 0 ≤ w v)
    (x : SupportChainState V n M) (a : Fin (n + M)) (i j : V) :
    tagWeight w (supportChainBranch x a i j).1 ≤ tagWeight w x.1 + (w i + 2 * w j) := by
  have hwi := hw i
  have hwj := hw j
  unfold supportChainBranch
  split_ifs with h
  · dsimp only
    have hinsert : ∑ v ∈ insert j (x.1 a), w v ≤ w j + ∑ v ∈ x.1 a, w v := by
      have h' := sum_union_le_add hw {j} (x.1 a)
      rwa [← Finset.insert_eq, Finset.sum_singleton] at h'
    have hpair : ∑ v ∈ ({i, j} : Finset V), w v ≤ w i + w j := by
      have h' := sum_union_le_add hw {i} {j}
      rwa [← Finset.insert_eq, Finset.sum_singleton, Finset.sum_singleton] at h'
    refine (tagWeight_update_le hw _ _ _).trans ?_
    rw [tagWeight_update]
    linarith
  · linarith

/-- A decision raises the decision count by at most one. -/
theorem supportChainBranch_count_le (x : SupportChainState V n M) (a : Fin (n + M)) (i j : V) :
    (((supportChainBranch x a i j).2 : ℕ) : ℝ) ≤ ((x.2 : ℕ) : ℝ) + 1 := by
  unfold supportChainBranch
  split_ifs with h
  · simp
  · linarith

variable [Fintype V]

/-- **The jump rates of the truncated support chain.** At rate `r i j` every argument whose
support contains `i` takes a decision along `i → j`, and at rate `c` every pair of occupied slots
coalesces through `coalesceTags`. -/
def supportChainRate (r : V → V → ℝ) (c : ℝ) (x y : SupportChainState V n M) : ℝ :=
  (∑ a, ∑ i ∈ x.1 a, ∑ j, if supportChainBranch x a i j = y then r i j else 0) +
    ∑ a, ∑ b, if (coalesceTags a b x.1, x.2) = y then
      (if a < b ∧ (x.1 a).Nonempty ∧ (x.1 b).Nonempty then c else 0) else 0

/-- **The generator matrix of the truncated support chain.** -/
def supportChainGenerator (r : V → V → ℝ) (c : ℝ) :
    Matrix (SupportChainState V n M) (SupportChainState V n M) ℝ :=
  jumpRateGenerator (supportChainRate r c)

/-- The support chain has nonnegative rates. -/
theorem supportChainRate_nonneg {r : V → V → ℝ} {c : ℝ} (hr : ∀ i j, 0 ≤ r i j) (hc : 0 ≤ c)
    (x y : SupportChainState V n M) : 0 ≤ supportChainRate r c x y := by
  refine add_nonneg (Finset.sum_nonneg fun a _ ↦ Finset.sum_nonneg fun i _ ↦
    Finset.sum_nonneg fun j _ ↦ ?_) (Finset.sum_nonneg fun a _ ↦ Finset.sum_nonneg fun b _ ↦ ?_)
  · split_ifs
    · exact hr i j
    · exact le_rfl
  · split_ifs <;> linarith

/-- The generator of the support chain is Metzler. -/
theorem supportChainGenerator_apply_nonneg {r : V → V → ℝ} {c : ℝ} (hr : ∀ i j, 0 ≤ r i j)
    (hc : 0 ≤ c) {x y : SupportChainState V n M} (hxy : x ≠ y) :
    0 ≤ supportChainGenerator r c x y :=
  jumpRateGenerator_apply_nonneg (supportChainRate_nonneg hr hc) hxy

/-- **The generator of the support chain acts by decisions and coalescences.** -/
theorem supportChainGenerator_mulVec (r : V → V → ℝ) (c : ℝ) (f : SupportChainState V n M → ℝ)
    (x : SupportChainState V n M) :
    (supportChainGenerator r c *ᵥ f) x =
      ∑ a, ∑ i ∈ x.1 a, ∑ j, r i j * (f (supportChainBranch x a i j) - f x) +
        ∑ a, ∑ b, (if a < b ∧ (x.1 a).Nonempty ∧ (x.1 b).Nonempty then c else 0) *
          (f (coalesceTags a b x.1, x.2) - f x) := by
  rw [supportChainGenerator, jumpRateGenerator_mulVec]
  simp only [supportChainRate, add_mul, Finset.sum_add_distrib, Finset.sum_mul]
  congr 1
  · refine Finset.sum_comm.trans (Finset.sum_congr rfl fun a _ ↦ ?_)
    refine Finset.sum_comm.trans (Finset.sum_congr rfl fun i _ ↦ ?_)
    refine Finset.sum_comm.trans (Finset.sum_congr rfl fun j _ ↦ ?_)
    simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  · refine Finset.sum_comm.trans (Finset.sum_congr rfl fun a _ ↦ ?_)
    refine Finset.sum_comm.trans (Finset.sum_congr rfl fun b _ ↦ ?_)
    simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]

/-- **The drift inequality of the truncated chain.** If every row of rates sums to at most `D`
and the weight grows by at most the factor `κ` along every edge of positive rate, then
`Q Z^{(w)} ≤ D (1 + 2κ) Z^{(w)}` for the tag weight, whatever the truncation `M`. -/
theorem supportChainGenerator_tagWeight_le {r : V → V → ℝ} {c D κ : ℝ} {w : V → ℝ}
    (hr : ∀ i j, 0 ≤ r i j) (hD : ∀ i, ∑ j, r i j ≤ D) (hc : 0 ≤ c) (hw : ∀ v, 0 ≤ w v)
    (hκ : 0 ≤ κ) (hedge : ∀ i j, 0 < r i j → w j ≤ κ * w i) (x : SupportChainState V n M) :
    (supportChainGenerator r c *ᵥ fun y ↦ tagWeight w y.1) x ≤
      D * (1 + 2 * κ) * tagWeight w x.1 := by
  rw [supportChainGenerator_mulVec]
  have hright : D * (1 + 2 * κ) * tagWeight w x.1 =
      ∑ a, ∑ i ∈ x.1 a, D * (1 + 2 * κ) * w i := by
    simp only [tagWeight, Finset.mul_sum]
  have hbranch : ∑ a, ∑ i ∈ x.1 a, ∑ j, r i j *
      (tagWeight w (supportChainBranch x a i j).1 - tagWeight w x.1) ≤
        D * (1 + 2 * κ) * tagWeight w x.1 := by
    rw [hright]
    refine Finset.sum_le_sum fun a _ ↦ Finset.sum_le_sum fun i _ ↦ ?_
    have hterm : ∀ j, r i j * (tagWeight w (supportChainBranch x a i j).1 - tagWeight w x.1) ≤
        r i j * ((1 + 2 * κ) * w i) := by
      intro j
      rcases (hr i j).eq_or_lt with hzero | hpos
      · rw [← hzero, zero_mul, zero_mul]
      · refine mul_le_mul_of_nonneg_left ?_ (hr i j)
        linarith [tagWeight_supportChainBranch_le hw x a i j, hedge i j hpos]
    calc ∑ j, r i j * (tagWeight w (supportChainBranch x a i j).1 - tagWeight w x.1)
        ≤ ∑ j, r i j * ((1 + 2 * κ) * w i) := Finset.sum_le_sum fun j _ ↦ hterm j
      _ = (∑ j, r i j) * ((1 + 2 * κ) * w i) := by rw [Finset.sum_mul]
      _ ≤ D * ((1 + 2 * κ) * w i) :=
        mul_le_mul_of_nonneg_right (hD i) (mul_nonneg (by linarith) (hw i))
      _ = D * (1 + 2 * κ) * w i := by ring
  have hcoal : ∑ a, ∑ b, (if a < b ∧ (x.1 a).Nonempty ∧ (x.1 b).Nonempty then c else 0) *
      (tagWeight w (coalesceTags a b x.1, x.2).1 - tagWeight w x.1) ≤ 0 := by
    refine Finset.sum_nonpos fun a _ ↦ Finset.sum_nonpos fun b _ ↦ ?_
    split_ifs with hab
    · exact mul_nonpos_of_nonneg_of_nonpos hc
        (sub_nonpos.mpr (tagWeight_coalesceTags_le hw (ne_of_lt hab.1) x.1))
    · rw [zero_mul]
  linarith

/-- **The decision count has drift at most the decision rate** of the supports. -/
theorem supportChainGenerator_count_le {r : V → V → ℝ} {c : ℝ} (hr : ∀ i j, 0 ≤ r i j)
    (x : SupportChainState V n M) :
    (supportChainGenerator r c *ᵥ fun y ↦ ((y.2 : ℕ) : ℝ)) x ≤ decisionRate r x.1 := by
  rw [supportChainGenerator_mulVec]
  have hbranch : ∑ a, ∑ i ∈ x.1 a, ∑ j, r i j *
      ((((supportChainBranch x a i j).2 : ℕ) : ℝ) - ((x.2 : ℕ) : ℝ)) ≤ decisionRate r x.1 := by
    rw [decisionRate]
    refine Finset.sum_le_sum fun a _ ↦ Finset.sum_le_sum fun i _ ↦
      Finset.sum_le_sum fun j _ ↦ ?_
    exact mul_le_of_le_one_right (hr i j) (by linarith [supportChainBranch_count_le x a i j])
  have hcoal : ∑ a, ∑ b, (if a < b ∧ (x.1 a).Nonempty ∧ (x.1 b).Nonempty then c else 0) *
      ((((coalesceTags a b x.1, x.2).2 : ℕ) : ℝ) - ((x.2 : ℕ) : ℝ)) = 0 := by
    simp
  linarith

/-- **The law at time `t` of the support chain truncated after `M` decisions**, started from `n`
arguments carrying `A`: `μ_t = δ_{x₀} e^{tQ}`. -/
def supportChainLaw (r : V → V → ℝ) (c : ℝ) (A : Finset V) (n M : ℕ) (t : ℝ)
    (y : SupportChainState V n M) : ℝ :=
  jumpChainLaw (supportChainGenerator r c) (supportChainStart A n M) t y

/-- **Dynkin's formula for the truncated support chain**: `d/dt ∫ f dμ_t = ∫ Q f dμ_t`. -/
theorem hasDerivAt_sum_supportChainLaw_mul (r : V → V → ℝ) (c : ℝ) (A : Finset V) (n M : ℕ)
    (f : SupportChainState V n M → ℝ) (t : ℝ) :
    HasDerivAt (fun u ↦ ∑ y, supportChainLaw r c A n M u y * f y)
      (∑ y, supportChainLaw r c A n M t y * (supportChainGenerator r c *ᵥ f) y) t :=
  hasDerivAt_sum_jumpChainLaw_mul _ _ f t

/-- The truncated chain has a nonnegative law at every time `t ≥ 0`. -/
theorem supportChainLaw_nonneg {r : V → V → ℝ} {c : ℝ} (hr : ∀ i j, 0 ≤ r i j) (hc : 0 ≤ c)
    (A : Finset V) (n M : ℕ) {t : ℝ} (ht : 0 ≤ t) (y : SupportChainState V n M) :
    0 ≤ supportChainLaw r c A n M t y :=
  jumpChainLaw_nonneg (fun _ _ hxy ↦ supportChainGenerator_apply_nonneg hr hc hxy) _ ht y

/-- The truncated chain keeps total mass one. -/
theorem sum_supportChainLaw (r : V → V → ℝ) (c : ℝ) (A : Finset V) (n M : ℕ) (t : ℝ) :
    ∑ y, supportChainLaw r c A n M t y = 1 :=
  sum_jumpChainLaw (sum_jumpRateGenerator _) _ t

/-- **Theorem 7, (8.2), with Dynkin's formula proved**: for the support chain truncated after any
number `M` of decisions, `E Z_T ≤ n |A| e^{3 D T}`. -/
theorem sum_supportChainLaw_mul_tagCount_le {r : V → V → ℝ} {c D T : ℝ}
    (hr : ∀ i j, 0 ≤ r i j) (hD : ∀ i, ∑ j, r i j ≤ D) (hc : 0 ≤ c) (A : Finset V) (n M : ℕ)
    (hT : 0 ≤ T) :
    ∑ y, supportChainLaw r c A n M T y * (tagCount y.1 : ℝ) ≤
      n * A.card * Real.exp (3 * D * T) := by
  have hunit : (fun y : SupportChainState V n M ↦ (tagCount y.1 : ℝ)) =
      fun y ↦ tagWeight (fun _ ↦ 1) y.1 := funext fun y ↦ (tagWeight_one y.1).symm
  have hdrift : ∀ x : SupportChainState V n M,
      (supportChainGenerator r c *ᵥ fun y ↦ (tagCount y.1 : ℝ)) x ≤
        3 * D * (tagCount x.1 : ℝ) := by
    intro x
    have h := supportChainGenerator_tagWeight_le (w := fun _ ↦ 1) (κ := 1) hr hD hc
      (fun _ ↦ zero_le_one) zero_le_one (fun _ _ _ ↦ by norm_num) x
    rw [hunit, ← tagWeight_one]
    linarith
  have h := sum_jumpChainLaw_mul_le_exp (Q := supportChainGenerator r c)
    (fun _ _ hxy ↦ supportChainGenerator_apply_nonneg hr hc hxy) hdrift
    (supportChainStart A n M) hT
  have hstart : (tagCount (supportChainStart A n M).1 : ℝ) = n * A.card := by
    rw [← tagWeight_one, tagWeight_supportChainStart]
    simp
  beta_reduce at h
  rw [hstart] at h
  exact h

/-- **Theorem 7, (8.3), with Dynkin's formula proved**: for the support chain truncated after any
number `M` of decisions, the expected number of decisions by time `T` is at most
`(n |A| / 3)(e^{3 D T} - 1)`. -/
theorem sum_supportChainLaw_mul_count_le {r : V → V → ℝ} {c D T : ℝ} (hr : ∀ i j, 0 ≤ r i j)
    (hD : ∀ i, ∑ j, r i j ≤ D) (hD0 : 0 ≤ D) (hc : 0 ≤ c) (A : Finset V) (n M : ℕ)
    (hT : 0 ≤ T) :
    ∑ y, supportChainLaw r c A n M T y * ((y.2 : ℕ) : ℝ) ≤
      n * A.card / 3 * (Real.exp (3 * D * T) - 1) := by
  have hcomp := sum_jumpChainLaw_mul_sub_eq_integral (supportChainGenerator r c)
    (supportChainStart A n M) (fun y ↦ ((y.2 : ℕ) : ℝ)) T
  have hzero : (((supportChainStart A n M).2 : ℕ) : ℝ) = 0 := by
    simp [supportChainStart]
  simp only [hzero, sub_zero] at hcomp
  have hcont : ContinuousOn
      (fun t ↦ ∑ y, supportChainLaw r c A n M t y * (tagCount y.1 : ℝ)) (Set.Icc 0 T) :=
    fun t _ ↦ (hasDerivAt_sum_supportChainLaw_mul r c A n M
      (fun y ↦ (tagCount y.1 : ℝ)) t).continuousAt.continuousWithinAt
  have hrate : Continuous fun t ↦ ∑ y, supportChainLaw r c A n M t y *
      (supportChainGenerator r c *ᵥ fun y ↦ ((y.2 : ℕ) : ℝ)) y :=
    continuous_iff_continuousAt.mpr fun t ↦ (hasDerivAt_sum_supportChainLaw_mul r c A n M
      (supportChainGenerator r c *ᵥ fun y ↦ ((y.2 : ℕ) : ℝ)) t).continuousAt
  refine le_div_three_mul_exp_sub_one hD0 hT hcont
    (fun t ht ↦ sum_supportChainLaw_mul_tagCount_le hr hD hc A n M ht.1) ?_
  calc ∑ y, supportChainLaw r c A n M T y * ((y.2 : ℕ) : ℝ)
      = ∫ t in (0 : ℝ)..T, ∑ y, supportChainLaw r c A n M t y *
          (supportChainGenerator r c *ᵥ fun y ↦ ((y.2 : ℕ) : ℝ)) y := hcomp
    _ ≤ ∫ t in (0 : ℝ)..T, D * ∑ y, supportChainLaw r c A n M t y * (tagCount y.1 : ℝ) := by
        refine intervalIntegral.integral_mono_on hT (hrate.intervalIntegrable 0 T)
          ((hcont.intervalIntegrable_of_Icc hT).const_mul D) fun t ht ↦ ?_
        calc ∑ y, supportChainLaw r c A n M t y *
              (supportChainGenerator r c *ᵥ fun y ↦ ((y.2 : ℕ) : ℝ)) y
            ≤ ∑ y, supportChainLaw r c A n M t y * (D * (tagCount y.1 : ℝ)) :=
              Finset.sum_le_sum fun y _ ↦ mul_le_mul_of_nonneg_left
                ((supportChainGenerator_count_le hr y).trans (decisionRate_le hD y.1))
                (supportChainLaw_nonneg hr hc A n M ht.1 y)
          _ = D * ∑ y, supportChainLaw r c A n M t y * (tagCount y.1 : ℝ) := by
              rw [Finset.mul_sum]
              exact Finset.sum_congr rfl fun y _ ↦ by ring
    _ = D * ∫ t in (0 : ℝ)..T, ∑ y, supportChainLaw r c A n M t y * (tagCount y.1 : ℝ) :=
        intervalIntegral.integral_const_mul _ _

/-- **The light-cone count with Dynkin's formula proved**: for the truncated chain and `a ≥ 1`,
`E Z^{(a)}_T ≤ n |A| e^{D (1 + 2a) T}`. -/
theorem sum_supportChainLaw_mul_lightWeight_le {r : V → V → ℝ} {c D T a : ℝ}
    (hr : ∀ i j, 0 ≤ r i j) (hD : ∀ i, ∑ j, r i j ≤ D) (hc : 0 ≤ c) (ha : 1 ≤ a)
    (A : Finset V) (n M ℓ : ℕ) (hT : 0 ≤ T) :
    ∑ y, supportChainLaw r c A n M T y * tagWeight (lightWeight r A ℓ a) y.1 ≤
      n * A.card * Real.exp (D * (1 + 2 * a) * T) := by
  have h := sum_jumpChainLaw_mul_le_exp (Q := supportChainGenerator r c)
    (fun _ _ hxy ↦ supportChainGenerator_apply_nonneg hr hc hxy)
    (F := fun y ↦ tagWeight (lightWeight r A ℓ a) y.1) (K := D * (1 + 2 * a))
    (supportChainGenerator_tagWeight_le hr hD hc (lightWeight_nonneg (by linarith)) (by linarith)
      fun _ _ hij ↦ lightWeight_le_mul ha hij)
    (supportChainStart A n M) hT
  have hstart : tagWeight (lightWeight r A ℓ a) (supportChainStart A n M).1 = n * A.card := by
    rw [tagWeight_supportChainStart]
    congr 1
    calc ∑ v ∈ A, lightWeight r A ℓ a v = ∑ _v ∈ A, (1 : ℝ) :=
          Finset.sum_congr rfl fun v hv ↦ by rw [lightWeight, lightDepth_eq_zero hv, pow_zero]
      _ = A.card := by simp
  beta_reduce at h
  rw [hstart] at h
  exact h

open scoped Classical in
/-- **Theorem 8, (9.1), with Dynkin's formula proved.** For the support chain truncated after any
number `M` of decisions and every `a ≥ 1`, the probability that the circuit holds a coordinate at
distance at least `ℓ` from `A` at time `T` is at most `min {1, n |A| e^{D (1 + 2a) T} / a^ℓ}`. -/
theorem sum_supportChainLaw_escape_le {r : V → V → ℝ} {c D T a : ℝ} (hr : ∀ i j, 0 ≤ r i j)
    (hD : ∀ i, ∑ j, r i j ≤ D) (hc : 0 ≤ c) (ha : 1 ≤ a) (A : Finset V) (n M ℓ : ℕ)
    (hT : 0 ≤ T) :
    ∑ y, (if univ.val.map y.1 ∈ escapeSet r A ℓ then supportChainLaw r c A n M T y else 0) ≤
      min 1 (n * A.card * Real.exp (D * (1 + 2 * a) * T) / a ^ ℓ) := by
  have hnonneg : ∀ y, 0 ≤ supportChainLaw r c A n M T y := supportChainLaw_nonneg hr hc A n M hT
  have hpos : 0 < a ^ ℓ := pow_pos (by linarith) ℓ
  refine le_min ?_ ?_
  · calc ∑ y, (if univ.val.map y.1 ∈ escapeSet r A ℓ then supportChainLaw r c A n M T y else 0)
        ≤ ∑ y, supportChainLaw r c A n M T y := Finset.sum_le_sum fun y _ ↦ by
          split_ifs
          · exact le_rfl
          · exact hnonneg y
      _ = 1 := sum_supportChainLaw r c A n M T
  · rw [le_div_iff₀ hpos, Finset.sum_mul]
    refine (Finset.sum_le_sum fun y _ ↦ ?_).trans
      (sum_supportChainLaw_mul_lightWeight_le hr hD hc ha A n M ℓ hT)
    split_ifs with hy
    · have h := pow_le_weightedCount_of_mem_escapeSet (by linarith) hy
      rw [weightedCount_map_univ] at h
      exact mul_le_mul_of_nonneg_left h (hnonneg y)
    · rw [zero_mul]
      exact mul_nonneg (hnonneg y) (tagWeight_nonneg (lightWeight_nonneg (by linarith)) y.1)

open scoped Classical in
/-- **Theorem 8, (9.2), with Dynkin's formula proved**: at the radius `a = ℓ / (2 D T) ≥ 1` the
escape bound of the truncated chain is `min {1, n |A| e^{D T} (2 e D T / ℓ)^ℓ}`. -/
theorem sum_supportChainLaw_escape_le_radius {r : V → V → ℝ} {c D T : ℝ}
    (hr : ∀ i j, 0 ≤ r i j) (hD : ∀ i, ∑ j, r i j ≤ D) (hc : 0 ≤ c) (A : Finset V)
    (n M ℓ : ℕ) (hT : 0 ≤ T) (hDT : D * T ≠ 0) (hradius : 1 ≤ (ℓ : ℝ) / (2 * D * T)) :
    ∑ y, (if univ.val.map y.1 ∈ escapeSet r A ℓ then supportChainLaw r c A n M T y else 0) ≤
      min 1 (n * A.card * Real.exp (D * T) * (2 * Real.exp 1 * D * T / ℓ) ^ ℓ) := by
  have h := sum_supportChainLaw_escape_le hr hD hc hradius A n M ℓ hT
  rwa [exp_div_pow_eq_of_radius hDT] at h

open scoped Classical in
/-- **No escape when `D T = 0`**: the truncated chain holds no coordinate at distance `ℓ ≥ 1`. -/
theorem sum_supportChainLaw_escape_eq_zero {r : V → V → ℝ} {c D T : ℝ} (hr : ∀ i j, 0 ≤ r i j)
    (hD : ∀ i, ∑ j, r i j ≤ D) (hc : 0 ≤ c) (A : Finset V) (n M ℓ : ℕ) (hT : 0 ≤ T)
    (hDT : D * T = 0) (hℓ : 1 ≤ ℓ) :
    ∑ y, (if univ.val.map y.1 ∈ escapeSet r A ℓ then supportChainLaw r c A n M T y else 0) = 0 :=
  eq_zero_of_forall_escape_bound hDT hℓ
    (Finset.sum_nonneg fun y _ ↦ by
      split_ifs
      · exact supportChainLaw_nonneg hr hc A n M hT y
      · exact le_rfl)
    fun a ha ↦ sum_supportChainLaw_escape_le hr hD hc ha.le A n M ℓ hT

end SupportChain

end

end Descent.Pangenome.AncestralLocality
