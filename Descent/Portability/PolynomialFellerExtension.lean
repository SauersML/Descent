/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.FiniteMixtureKernel
import Mathlib.Analysis.Normed.Operator.Completeness
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Topology.MetricSpace.UniformConvergence
import Mathlib.Topology.UniformSpace.Equicontinuity

assert_below Descent.Decision Descent.Program

/-!
# Positive polynomial semigroups extend to Feller semigroups

This module proves the operator half of NOTE1 §4.2a ("the complete probability kernel can be
constructed, not assumed"). The note defines `T_t f` for polynomial observables by finite
matrix exponentials on material-bounded invariant spaces, obtains the same operators as the
microscopic limit `T_t f = lim_{h ↓ 0} K_h^{⌊t/h⌋} f`, and concludes that `T_t` extends
uniquely to a positive, constant-preserving, strongly continuous contraction semigroup on
`C(X)`. The abstract steps of that argument are proved here for a compact space `X` and any
dense subspace `V ⊆ C(X, ℝ)` containing the constants. The theorem
`dense_toSubmodule_of_separatesPoints` supplies density for every point-separating subalgebra
by Stone–Weierstrass, which covers the polynomials in haplotype frequencies on the simplex.

Positivity versus contraction. For a linear map into `C(X, ℝ)` that fixes the constant one,
positivity and sup-norm contraction are the same property (`norm_le_of_nonneg_of_map_unit`,
`nonneg_of_norm_le_of_map_unit`, `nonneg_iff_norm_le_of_map_unit`). So the three properties
the note lists reduce to two, and positivity of the extension is inherited from contraction
rather than proved by approximating nonnegative functions from inside `V`.

The extension. `denseExtension V hV T hT` extends a contraction `T : V →ₗ[ℝ] V` along the
isometric inclusion by uniform continuity. It agrees with `T` on `V` (`denseExtension_coe`),
contracts (`denseExtension_norm_le`), fixes constants (`denseExtension_one`), is positive
(`denseExtension_nonneg`), and is the only continuous map agreeing with `T` on `V`
(`denseExtension_unique`; `denseExtension_eq_of_contraction` for linear contractions). For a
family `T : ℝ≥0 → V →ₗ[ℝ] V` the semigroup law passes to the extensions
(`denseExtension_add`), so does the identity at time zero (`denseExtension_eq_id`), and
strong continuity at time zero on `V` gives strong continuity on `C(X, ℝ)` because
contractions are equicontinuous (`denseExtension_tendsto_zero`). The theorem
`exists_unique_extension_semigroup` packages the extension statement of NOTE1 §4.2a.

The microscopic bridge. Iterates of the corpus kernels `FiniteMixtureKernel` preserve
nonnegativity and contract uniform distances (`iterate_apply_nonneg`, `iterate_apply_sub_le`).
If iterates `K_i^{n_i}` converge pointwise to `T f` for every `f ∈ V` along a nontrivial
filter, `T` is positive and fixes the constants (`nonneg_and_map_one_of_iterate_tendsto`);
the uniform Euler limit `K_h^{⌊t/h⌋} f → T f` as `h ↓ 0` gives all three properties of the
note (`markov_of_euler_tendstoUniformly`); and the iterates then converge to the extension on
every continuous observable, not only on `V` (`tendsto_iterate_extension`).

Scope. The finite matrix exponentials of NOTE1 (20), their independence of the chosen
invariant space, and the `O(N^{-2})` remainder of the multinomial expansion at every finite
degree are NOT formalized: the Euler limit enters as a hypothesis on the approximating
kernels, and the two-locus instantiation is not attempted. The representation of the
extended operators by probability kernels is the companion module `FellerKernelRepresentation`.

## Empirical status

None. The bodies here are functional analysis: every statement is an identity or inequality
between operators on continuous functions, proved from linearity, positivity and density, so
no measurement on any population could bear on one.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.PolynomialFellerExtension

open Filter Topology
open scoped NNReal
open FiniteMixtureKernel

noncomputable section

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]

/-! ### Positivity and contraction for maps fixing the constants -/

/-- A positive linear map `S` into `C(X, ℝ)` sending a unit `u` to the constant one contracts
sup norms relative to any readout `ι` with `ι u = 1`: `‖S f‖ ≤ ‖ι f‖`. Positivity applied to
`‖ι f‖ • u ± f`, whose readouts are nonnegative, bounds `S f` pointwise by `‖ι f‖`. -/
theorem norm_le_of_nonneg_of_map_unit {M : Type*} [AddCommGroup M] [Module ℝ M]
    (ι S : M →ₗ[ℝ] C(X, ℝ)) (u : M) (hιu : ι u = 1) (hSu : S u = 1)
    (hpos : ∀ f, 0 ≤ ι f → 0 ≤ S f) (f : M) : ‖S f‖ ≤ ‖ι f‖ := by
  have hplus := hpos (‖ι f‖ • u + f) <| ContinuousMap.le_def.mpr fun x ↦ by
    have hx := ContinuousMap.neg_norm_le_apply (ι f) x
    simp only [map_add, map_smul, hιu, ContinuousMap.add_apply, ContinuousMap.smul_apply,
      ContinuousMap.one_apply, ContinuousMap.zero_apply, smul_eq_mul, mul_one]
    linarith
  have hminus := hpos (‖ι f‖ • u - f) <| ContinuousMap.le_def.mpr fun x ↦ by
    have hx := ContinuousMap.apply_le_norm (ι f) x
    simp only [map_sub, map_smul, hιu, ContinuousMap.sub_apply, ContinuousMap.smul_apply,
      ContinuousMap.one_apply, ContinuousMap.zero_apply, smul_eq_mul, mul_one]
    linarith
  refine (ContinuousMap.norm_le (S f) (norm_nonneg (ι f))).mpr fun x ↦ ?_
  have hp := ContinuousMap.le_def.mp hplus x
  have hm := ContinuousMap.le_def.mp hminus x
  simp only [map_add, map_sub, map_smul, hSu, ContinuousMap.add_apply, ContinuousMap.sub_apply,
    ContinuousMap.smul_apply, ContinuousMap.one_apply, ContinuousMap.zero_apply, smul_eq_mul,
    mul_one] at hp hm
  rw [Real.norm_eq_abs, abs_le]
  constructor <;> linarith

/-- A linear map `S` into `C(X, ℝ)` sending a unit `u` to the constant one and contracting sup
norms relative to a readout `ι` with `ι u = 1` is positive. For `0 ≤ ι g` the readout of
`g - (‖ι g‖ / 2) • u` lies within `‖ι g‖ / 2` of zero, hence so does `S g - ‖ι g‖ / 2`. -/
theorem nonneg_of_norm_le_of_map_unit {M : Type*} [AddCommGroup M] [Module ℝ M]
    (ι S : M →ₗ[ℝ] C(X, ℝ)) (u : M) (hιu : ι u = 1) (hSu : S u = 1)
    (hcontr : ∀ f, ‖S f‖ ≤ ‖ι f‖) (g : M) (hg : 0 ≤ ι g) : 0 ≤ S g := by
  have hhalf : (0 : ℝ) ≤ ‖ι g‖ / 2 := by positivity
  have hbound : ‖ι (g - (‖ι g‖ / 2) • u)‖ ≤ ‖ι g‖ / 2 := by
    refine (ContinuousMap.norm_le (ι (g - (‖ι g‖ / 2) • u)) hhalf).mpr fun x ↦ ?_
    have h0 := ContinuousMap.le_def.mp hg x
    have hle := ContinuousMap.apply_le_norm (ι g) x
    simp only [ContinuousMap.zero_apply] at h0
    simp only [map_sub, map_smul, hιu, ContinuousMap.sub_apply, ContinuousMap.smul_apply,
      ContinuousMap.one_apply, smul_eq_mul, mul_one, Real.norm_eq_abs, abs_le]
    constructor <;> linarith
  refine ContinuousMap.le_def.mpr fun x ↦ ?_
  have hx := (ContinuousMap.norm_coe_le_norm (S (g - (‖ι g‖ / 2) • u)) x).trans
    ((hcontr _).trans hbound)
  simp only [map_sub, map_smul, hSu, ContinuousMap.sub_apply, ContinuousMap.smul_apply,
    ContinuousMap.one_apply, smul_eq_mul, mul_one, Real.norm_eq_abs, abs_le] at hx
  rw [ContinuousMap.zero_apply]
  linarith [hx.1]

/-- For a linear map into `C(X, ℝ)` that fixes the constant one, positivity and sup-norm
contraction are one property. -/
theorem nonneg_iff_norm_le_of_map_unit {M : Type*} [AddCommGroup M] [Module ℝ M]
    (ι S : M →ₗ[ℝ] C(X, ℝ)) (u : M) (hιu : ι u = 1) (hSu : S u = 1) :
    (∀ f, 0 ≤ ι f → 0 ≤ S f) ↔ ∀ f, ‖S f‖ ≤ ‖ι f‖ :=
  ⟨norm_le_of_nonneg_of_map_unit ι S u hιu hSu, nonneg_of_norm_le_of_map_unit ι S u hιu hSu⟩

/-! ### Extension from a dense subspace -/

/-- The extension to all of `C(X, ℝ)` of a sup-norm contraction `T` of a dense subspace `V`:
`T` is read into `C(X, ℝ)` as a bounded operator of norm at most one and extended along the
isometric inclusion `V ⊆ C(X, ℝ)` by uniform continuity. -/
def denseExtension (V : Submodule ℝ C(X, ℝ)) (hV : Dense (V : Set C(X, ℝ))) (T : V →ₗ[ℝ] V)
    (hT : ∀ f : V, ‖(T f : C(X, ℝ))‖ ≤ ‖(f : C(X, ℝ))‖) : C(X, ℝ) →L[ℝ] C(X, ℝ) :=
  (LinearMap.mkContinuous (V.subtype ∘ₗ T) 1 fun f ↦ by rw [one_mul]; exact hT f).extend
    V.subtypeL hV.denseRange_val V.subtypeₗᵢ.isometry.isUniformInducing

/-- On the dense subspace the extension is the operator itself. -/
theorem denseExtension_coe (V : Submodule ℝ C(X, ℝ)) (hV : Dense (V : Set C(X, ℝ)))
    (T : V →ₗ[ℝ] V) (hT : ∀ f : V, ‖(T f : C(X, ℝ))‖ ≤ ‖(f : C(X, ℝ))‖) (f : V) :
    denseExtension V hV T hT f = T f := by
  unfold denseExtension
  exact ContinuousLinearMap.extend_eq _ _ _ _ f

/-- The extension contracts sup norms: the inequality holds on the dense subspace, and the set
of functions where it holds is closed. -/
theorem denseExtension_norm_le (V : Submodule ℝ C(X, ℝ)) (hV : Dense (V : Set C(X, ℝ)))
    (T : V →ₗ[ℝ] V) (hT : ∀ f : V, ‖(T f : C(X, ℝ))‖ ≤ ‖(f : C(X, ℝ))‖) (g : C(X, ℝ)) :
    ‖denseExtension V hV T hT g‖ ≤ ‖g‖ := by
  have hd : DenseRange (Subtype.val : V → C(X, ℝ)) := hV.denseRange_val
  refine hd.induction_on g
    (isClosed_le (denseExtension V hV T hT).continuous.norm continuous_norm) fun f ↦ ?_
  rw [denseExtension_coe]
  exact hT f

/-- The extension fixes the constant one when the operator does. -/
theorem denseExtension_one (V : Submodule ℝ C(X, ℝ)) (hV : Dense (V : Set C(X, ℝ)))
    (T : V →ₗ[ℝ] V) (hT : ∀ f : V, ‖(T f : C(X, ℝ))‖ ≤ ‖(f : C(X, ℝ))‖)
    (h1 : (1 : C(X, ℝ)) ∈ V) (hT1 : (T ⟨1, h1⟩ : C(X, ℝ)) = 1) :
    denseExtension V hV T hT 1 = 1 :=
  (denseExtension_coe V hV T hT ⟨1, h1⟩).trans hT1

/-- The extension is positive when the operator fixes the constants: a contraction of
`C(X, ℝ)` fixing the constant one is positive by `nonneg_of_norm_le_of_map_unit`. -/
theorem denseExtension_nonneg (V : Submodule ℝ C(X, ℝ)) (hV : Dense (V : Set C(X, ℝ)))
    (T : V →ₗ[ℝ] V) (hT : ∀ f : V, ‖(T f : C(X, ℝ))‖ ≤ ‖(f : C(X, ℝ))‖)
    (h1 : (1 : C(X, ℝ)) ∈ V) (hT1 : (T ⟨1, h1⟩ : C(X, ℝ)) = 1) (g : C(X, ℝ)) (hg : 0 ≤ g) :
    0 ≤ denseExtension V hV T hT g :=
  nonneg_of_norm_le_of_map_unit LinearMap.id (denseExtension V hV T hT).toLinearMap 1 rfl
    (denseExtension_one V hV T hT h1 hT1) (denseExtension_norm_le V hV T hT) g hg

/-- The extension is the only continuous map on `C(X, ℝ)` that agrees with the operator on
the dense subspace. -/
theorem denseExtension_unique (V : Submodule ℝ C(X, ℝ)) (hV : Dense (V : Set C(X, ℝ)))
    (T : V →ₗ[ℝ] V) (hT : ∀ f : V, ‖(T f : C(X, ℝ))‖ ≤ ‖(f : C(X, ℝ))‖)
    (S : C(X, ℝ) → C(X, ℝ)) (hS : Continuous S) (hST : ∀ f : V, S f = T f) :
    S = denseExtension V hV T hT := by
  have hd : DenseRange (Subtype.val : V → C(X, ℝ)) := hV.denseRange_val
  refine hd.equalizer hS (denseExtension V hV T hT).continuous (funext fun f ↦ ?_)
  simp only [Function.comp_apply, hST, denseExtension_coe]

/-- A linear sup-norm contraction of `C(X, ℝ)` that agrees with the operator on the dense
subspace is the extension. -/
theorem denseExtension_eq_of_contraction (V : Submodule ℝ C(X, ℝ))
    (hV : Dense (V : Set C(X, ℝ))) (T : V →ₗ[ℝ] V)
    (hT : ∀ f : V, ‖(T f : C(X, ℝ))‖ ≤ ‖(f : C(X, ℝ))‖) (S : C(X, ℝ) →ₗ[ℝ] C(X, ℝ))
    (hS : ∀ g, ‖S g‖ ≤ ‖g‖) (hST : ∀ f : V, S f = T f) (g : C(X, ℝ)) :
    S g = denseExtension V hV T hT g :=
  congr_fun (denseExtension_unique V hV T hT S
    (LinearMap.mkContinuous S 1 fun g ↦ by rw [one_mul]; exact hS g).continuous hST) g

/-- The semigroup law `T (s + t) = T s ∘ T t` on the dense subspace passes to the
extensions. -/
theorem denseExtension_add (V : Submodule ℝ C(X, ℝ)) (hV : Dense (V : Set C(X, ℝ)))
    (T : ℝ≥0 → V →ₗ[ℝ] V) (hT : ∀ t (f : V), ‖(T t f : C(X, ℝ))‖ ≤ ‖(f : C(X, ℝ))‖)
    (hsemi : ∀ s t, T (s + t) = T s ∘ₗ T t) (s t : ℝ≥0) :
    denseExtension V hV (T (s + t)) (hT (s + t))
      = (denseExtension V hV (T s) (hT s)).comp (denseExtension V hV (T t) (hT t)) := by
  refine ContinuousLinearMap.coeFn_injective
    (denseExtension_unique V hV (T (s + t)) (hT (s + t)) _
      ((denseExtension V hV (T s) (hT s)).comp (denseExtension V hV (T t) (hT t))).continuous
      fun f ↦ ?_).symm
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply, denseExtension_coe, hsemi,
    LinearMap.comp_apply]

/-- If the operator is the identity of the dense subspace, its extension is the identity of
`C(X, ℝ)`. -/
theorem denseExtension_eq_id (V : Submodule ℝ C(X, ℝ)) (hV : Dense (V : Set C(X, ℝ)))
    (T : V →ₗ[ℝ] V) (hT : ∀ f : V, ‖(T f : C(X, ℝ))‖ ≤ ‖(f : C(X, ℝ))‖)
    (hid : T = LinearMap.id) : denseExtension V hV T hT = ContinuousLinearMap.id ℝ C(X, ℝ) :=
  ContinuousLinearMap.coeFn_injective
    (denseExtension_unique V hV T hT id continuous_id fun f ↦ by subst hid; rfl).symm

/-- Strong continuity at time zero passes from the dense subspace to `C(X, ℝ)`: the extensions
are contractions, hence equicontinuous, so the set of observables along which they converge
is closed and contains the dense subspace. -/
theorem denseExtension_tendsto_zero (V : Submodule ℝ C(X, ℝ)) (hV : Dense (V : Set C(X, ℝ)))
    (T : ℝ≥0 → V →ₗ[ℝ] V) (hT : ∀ t (f : V), ‖(T t f : C(X, ℝ))‖ ≤ ‖(f : C(X, ℝ))‖)
    (hcont : ∀ f : V, Tendsto (fun t ↦ (T t f : C(X, ℝ))) (𝓝 0) (𝓝 (f : C(X, ℝ))))
    (g : C(X, ℝ)) : Tendsto (fun t ↦ denseExtension V hV (T t) (hT t) g) (𝓝 0) (𝓝 g) := by
  have hd : DenseRange (Subtype.val : V → C(X, ℝ)) := hV.denseRange_val
  have hequi : Equicontinuous fun t ↦ ⇑(denseExtension V hV (T t) (hT t)) := by
    refine (LipschitzWith.uniformEquicontinuous
      (fun t ↦ ⇑(denseExtension V hV (T t) (hT t))) 1 fun t ↦ ?_).equicontinuous
    refine LipschitzWith.of_dist_le_mul fun g₁ g₂ ↦ ?_
    simpa only [NNReal.coe_one, one_mul, dist_eq_norm, map_sub]
      using denseExtension_norm_le V hV (T t) (hT t) (g₁ - g₂)
  refine hd.induction_on g (hequi.isClosed_setOf_tendsto continuous_id) fun f ↦ ?_
  simpa only [denseExtension_coe] using hcont f

/-! ### Point-separating subalgebras -/

/-- Stone–Weierstrass: a point-separating subalgebra of `C(X, ℝ)`, read as a subspace, is
dense, so every such subalgebra (polynomials in haplotype frequencies on the simplex among
them) is a domain for `denseExtension`. -/
theorem dense_toSubmodule_of_separatesPoints (A : Subalgebra ℝ C(X, ℝ))
    (hA : A.SeparatesPoints) : Dense (Subalgebra.toSubmodule A : Set C(X, ℝ)) := by
  rw [Subalgebra.coe_toSubmodule, dense_iff_closure_eq, ← Subalgebra.topologicalClosure_coe,
    ContinuousMap.subalgebra_topologicalClosure_eq_top_of_separatesPoints A hA, Algebra.coe_top]

/-- NOTE1 §4.2a, extension form. A semigroup of linear operators on a dense subspace of
`C(X, ℝ)` containing the constants, each positive and fixing the constants, has exactly one
extension to a family of continuous operators on `C(X, ℝ)` agreeing with it on the subspace,
and that family consists of positive, constant-preserving sup-norm contractions obeying the
semigroup law. -/
theorem exists_unique_extension_semigroup (V : Submodule ℝ C(X, ℝ))
    (hV : Dense (V : Set C(X, ℝ))) (h1 : (1 : C(X, ℝ)) ∈ V) (T : ℝ≥0 → V →ₗ[ℝ] V)
    (hT1 : ∀ t, (T t ⟨1, h1⟩ : C(X, ℝ)) = 1)
    (hpos : ∀ t (f : V), 0 ≤ (f : C(X, ℝ)) → 0 ≤ (T t f : C(X, ℝ)))
    (hsemi : ∀ s t, T (s + t) = T s ∘ₗ T t) :
    ∃! S : ℝ≥0 → C(X, ℝ) →L[ℝ] C(X, ℝ), (∀ t (f : V), S t f = T t f) ∧
      (∀ t g, ‖S t g‖ ≤ ‖g‖) ∧ (∀ t, S t 1 = 1) ∧ (∀ t g, 0 ≤ g → 0 ≤ S t g) ∧
      ∀ s t, S (s + t) = (S s).comp (S t) := by
  have hT : ∀ t (f : V), ‖(T t f : C(X, ℝ))‖ ≤ ‖(f : C(X, ℝ))‖ := fun t ↦
    norm_le_of_nonneg_of_map_unit V.subtype (V.subtype ∘ₗ T t) ⟨1, h1⟩ rfl (hT1 t) (hpos t)
  refine ⟨fun t ↦ denseExtension V hV (T t) (hT t),
    ⟨fun t ↦ denseExtension_coe V hV (T t) (hT t),
      fun t ↦ denseExtension_norm_le V hV (T t) (hT t),
      fun t ↦ denseExtension_one V hV (T t) (hT t) h1 (hT1 t),
      fun t ↦ denseExtension_nonneg V hV (T t) (hT t) h1 (hT1 t),
      denseExtension_add V hV T hT hsemi⟩,
    fun S hS ↦ funext fun t ↦ ContinuousLinearMap.coeFn_injective
      (denseExtension_unique V hV (T t) (hT t) (S t) (S t).continuous (hS.1 t))⟩

/-! ### The microscopic Euler limit -/

/-- Iterating a finite mixture kernel preserves nonnegativity of observables. -/
theorem iterate_apply_nonneg {B Y : Type*} [Fintype B] (K : FiniteMixtureKernel B Y) (n : ℕ)
    (f : Y → ℝ) (hf : ∀ y, 0 ≤ f y) (x : Y) : 0 ≤ K.apply^[n] f x := by
  induction n generalizing x with
  | zero => exact hf x
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact K.apply_nonneg _ ih x

/-- Iterating a finite mixture kernel contracts uniform distances between observables. -/
theorem iterate_apply_sub_le {B Y : Type*} [Fintype B] (K : FiniteMixtureKernel B Y) (n : ℕ)
    (f g : Y → ℝ) (M : ℝ) (hfg : ∀ y, |f y - g y| ≤ M) (x : Y) :
    |K.apply^[n] f x - K.apply^[n] g x| ≤ M := by
  induction n generalizing x with
  | zero => exact hfg x
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    exact K.apply_sub_le _ _ M ih x

/-- The positivity half of NOTE1 §4.2a for the corpus kernels. If iterates `K_i^{n_i}` of
finite mixture kernels converge pointwise to `T f` for every observable `f` of the subspace,
along a nontrivial filter, then `T` is positive and fixes the constants. -/
theorem nonneg_and_map_one_of_iterate_tendsto {ι B : Type*} [Fintype B] {l : Filter ι}
    (hl : l.NeBot) (V : Submodule ℝ C(X, ℝ)) (h1 : (1 : C(X, ℝ)) ∈ V) (T : V →ₗ[ℝ] V)
    (K : ι → FiniteMixtureKernel B X) (n : ι → ℕ)
    (hlim : ∀ (f : V) (x : X),
      Tendsto (fun i ↦ (K i).apply^[n i] ⇑(f : C(X, ℝ)) x) l (𝓝 ((T f : C(X, ℝ)) x))) :
    (∀ f : V, 0 ≤ (f : C(X, ℝ)) → 0 ≤ (T f : C(X, ℝ))) ∧ (T ⟨1, h1⟩ : C(X, ℝ)) = 1 := by
  haveI := hl
  refine ⟨fun f hf ↦ ContinuousMap.le_def.mpr fun x ↦ ?_, ContinuousMap.ext fun x ↦ ?_⟩
  · rw [ContinuousMap.zero_apply]
    refine ge_of_tendsto' (hlim f x) fun i ↦ iterate_apply_nonneg (K i) (n i) _ (fun y ↦ ?_) x
    simpa only [ContinuousMap.zero_apply] using ContinuousMap.le_def.mp hf y
  · refine tendsto_nhds_unique' hl (hlim ⟨1, h1⟩ x) (tendsto_const_nhds.congr fun i ↦ ?_)
    exact (congr_fun (Function.iterate_fixed (funext ((K i).apply_const 1)) (n i)) x).symm

/-- NOTE1 §4.2a, microscopic form. If the Euler iterates `K_h^{⌊t/h⌋}` of finite mixture
kernels converge uniformly to `T f` as `h ↓ 0` for every observable `f` of a subspace
containing the constants, then `T` is positive, fixes the constants and contracts sup norms:
the hypotheses of `denseExtension` and `exists_unique_extension_semigroup`. -/
theorem markov_of_euler_tendstoUniformly {B : Type*} [Fintype B] (V : Submodule ℝ C(X, ℝ))
    (h1 : (1 : C(X, ℝ)) ∈ V) (T : V →ₗ[ℝ] V) (K : ℝ → FiniteMixtureKernel B X) (t : ℝ)
    (hlim : ∀ f : V, TendstoUniformly (fun h ↦ (K h).apply^[⌊t / h⌋₊] ⇑(f : C(X, ℝ)))
      ⇑(T f : C(X, ℝ)) (𝓝[>] 0)) :
    (∀ f : V, 0 ≤ (f : C(X, ℝ)) → 0 ≤ (T f : C(X, ℝ))) ∧ (T ⟨1, h1⟩ : C(X, ℝ)) = 1 ∧
      ∀ f : V, ‖(T f : C(X, ℝ))‖ ≤ ‖(f : C(X, ℝ))‖ := by
  obtain ⟨hpos, hone⟩ := nonneg_and_map_one_of_iterate_tendsto (nhdsGT_neBot (0 : ℝ)) V h1 T K
    (fun h ↦ ⌊t / h⌋₊) fun f x ↦ (hlim f).tendsto_at x
  exact ⟨hpos, hone,
    norm_le_of_nonneg_of_map_unit V.subtype (V.subtype ∘ₗ T) ⟨1, h1⟩ rfl hone hpos⟩

/-- The microscopic approximation reaches every continuous observable. If the iterates
`K_i^{n_i}` converge pointwise to `T f` for every `f` of the dense subspace, they converge
pointwise to the extension on every `g ∈ C(X, ℝ)`: iterates contract uniform distances, so
the family is equicontinuous and the set of convergent observables is closed. -/
theorem tendsto_iterate_extension {ι B : Type*} [Fintype B] {l : Filter ι}
    (V : Submodule ℝ C(X, ℝ)) (hV : Dense (V : Set C(X, ℝ))) (T : V →ₗ[ℝ] V)
    (hT : ∀ f : V, ‖(T f : C(X, ℝ))‖ ≤ ‖(f : C(X, ℝ))‖) (K : ι → FiniteMixtureKernel B X)
    (n : ι → ℕ) (hlim : ∀ (f : V) (x : X),
      Tendsto (fun i ↦ (K i).apply^[n i] ⇑(f : C(X, ℝ)) x) l (𝓝 ((T f : C(X, ℝ)) x)))
    (g : C(X, ℝ)) (x : X) :
    Tendsto (fun i ↦ (K i).apply^[n i] ⇑g x) l (𝓝 (denseExtension V hV T hT g x)) := by
  have hd : DenseRange (Subtype.val : V → C(X, ℝ)) := hV.denseRange_val
  have hequi : Equicontinuous fun i (h : C(X, ℝ)) ↦ (K i).apply^[n i] ⇑h x := by
    refine (LipschitzWith.uniformEquicontinuous
      (fun i (h : C(X, ℝ)) ↦ (K i).apply^[n i] ⇑h x) 1 fun i ↦ ?_).equicontinuous
    refine LipschitzWith.of_dist_le_mul fun h₁ h₂ ↦ ?_
    simp only [NNReal.coe_one, one_mul, Real.dist_eq]
    refine iterate_apply_sub_le (K i) (n i) _ _ _ (fun y ↦ ?_) x
    rw [← Real.dist_eq]
    exact ContinuousMap.dist_apply_le_dist y
  have hev : Continuous fun h : C(X, ℝ) ↦ h x := continuous_eval_const x
  refine hd.induction_on g
    (hequi.isClosed_setOf_tendsto (hev.comp (denseExtension V hV T hT).continuous)) fun f ↦ ?_
  rw [denseExtension_coe]
  exact hlim f x

end

end Descent.Portability.PolynomialFellerExtension
