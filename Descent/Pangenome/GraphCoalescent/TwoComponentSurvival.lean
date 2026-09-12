/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.GraphCoalescent.MinimalRefinement
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.Topology.Algebra.Module.FiniteDimension

assert_below Descent.PopGen Descent.Spectral Descent.Blindness Descent.Conditionals
assert_below Descent.Portability Descent.Decision Descent.Program

/-!
# The survival semigroup of the two-component load chain

With two reported components, Theorem B of the hidden-lineage clock reads the unordered pair of
hidden loads off the survival function `S_{a,b}(t)` of the visible merger.
`Descent.Pangenome.GraphCoalescent.MinimalRefinement` represents that function by the killed
generator `twoComponentGenerator` applied once and twice to the constant one. This module
constructs the survival function as a matrix semigroup and computes its derivatives.

**The killed generator as a matrix.** On the grid of loads `{0, …, A} × {0, …, B}`,
`loadGenerator A B` moves loads `(a, b)` to `(a - 1, b)` at rate `C(a,2)` and to `(a, b - 1)` at
rate `C(b,2)`, and kills at rate `ab`, the visible merger. Its rows act on a function of the loads
as the corpus generator, `(Q g)(a, b) = twoComponentGenerator g a b` (`sum_loadGenerator_mul`), so
its row sums are minus the killing rate (`sum_loadGenerator`) and the rows of its square are the
generator applied twice to the constant one (`sum_loadGenerator_sq`).

**The semigroup.** `gridSurvival A B x t = δ_x e^{tQ} 𝟙`, with Mathlib's `NormedSpace.exp` on
matrices, and `survival a b t = α e^{tQ} 𝟙` with `α` the point mass at loads `(a, b)` on the grid
they span. The transition matrices form a semigroup (`exp_add_smul_loadGenerator`), so the
survival functions satisfy Chapman-Kolmogorov (`gridSurvival_add`, `survival_add`) and start at
one (`gridSurvival_zero`, `survival_zero`). They solve the backward equation `S' = Q S`
(`hasDerivAt_gridSurvival`), which in the loads is `twoComponentGenerator` applied to the survival
functions of the load states (`hasDerivAt_gridSurvival_eq_generator`).

**(B2) as derivatives.** The derivatives of `S_{a,b}` at `0` are the generator applied once and
twice to the constant one (`hasDerivAt_survival_generator_one`,
`hasDerivAt_deriv_survival_generator_twice`), and `MinimalRefinement.twoComponentGenerator_one`
and `MinimalRefinement.twoComponentGenerator_twice_one` evaluate them: `S'(0) = -ab`
(`hasDerivAt_survival_zero`, `deriv_survival_zero`) and
`S''(0) = (ab)² + C(a,2) b + C(b,2) a = (ab)² + ab(a + b - 2)/2`
(`hasDerivAt_deriv_survival_zero`, `deriv_deriv_survival_zero`).

**Theorem B for the survival function.** Positive loads with the same survival function form the
same unordered pair (`unorderedPair_of_survival_eq`). Exchanging the two components conjugates the
generator and its exponential (`loadGenerator_swap`, `exp_smul_loadGenerator_swap`), so the
survival function does not see the order (`survival_swap`): it determines the unordered pair of
loads and nothing more (`survival_eq_iff`).

Scope. The continuous-time load chain is not constructed as a stochastic process: the survival
function is defined as `α e^{tQ} 𝟙` of the killed generator, not as the probability that a process
has not yet connected. The grid is the one spanned by the initial loads; that a larger grid gives
the same survival function is not formalized.

## Empirical status

None. The bodies here are a finite matrix exponential, its derivatives at a point, and binomial
coefficients of supplied natural numbers, so no measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Pangenome.GraphCoalescent.TwoComponentSurvival

open Descent.Pangenome.GraphCoalescent.MinimalRefinement

noncomputable section

/-! ### The killed generator as a matrix -/

/-- Loads after a merger inside the first component: `(a, b) ↦ (a - 1, b)`. -/
def lowerFirst {A B : ℕ} (x : Fin (A + 1) × Fin (B + 1)) : Fin (A + 1) × Fin (B + 1) :=
  (⟨(x.1 : ℕ) - 1, lt_of_le_of_lt (Nat.sub_le _ _) x.1.isLt⟩, x.2)

/-- Loads after a merger inside the second component: `(a, b) ↦ (a, b - 1)`. -/
def lowerSecond {A B : ℕ} (x : Fin (A + 1) × Fin (B + 1)) : Fin (A + 1) × Fin (B + 1) :=
  (x.1, ⟨(x.2 : ℕ) - 1, lt_of_le_of_lt (Nat.sub_le _ _) x.2.isLt⟩)

/-- **The killed generator of the two-component load chain** on the loads at most `(A, B)`. From
loads `(a, b)` the rate into `(a - 1, b)` is `C(a,2)`, the rate into `(a, b - 1)` is `C(b,2)`, and
the killing rate is `ab`, the visible merger; the diagonal entry is minus the total rate. -/
def loadGenerator (A B : ℕ) :
    Matrix (Fin (A + 1) × Fin (B + 1)) (Fin (A + 1) × Fin (B + 1)) ℝ :=
  fun x y ↦
    (if y = lowerFirst x then (Nat.choose x.1 2 : ℝ) else 0) +
      (if y = lowerSecond x then (Nat.choose x.2 2 : ℝ) else 0) -
      (if y = x then (Nat.choose x.1 2 : ℝ) + Nat.choose x.2 2 + (x.1 : ℕ) * (x.2 : ℕ) else 0)

/-- **The rows of the killed generator act as `twoComponentGenerator`**: for a function `g` of the
two loads, `Σ_y Q((a, b), y) g(y) = twoComponentGenerator g a b`. -/
theorem sum_loadGenerator_mul (A B : ℕ) (g : ℕ → ℕ → ℝ) (x : Fin (A + 1) × Fin (B + 1)) :
    ∑ y, loadGenerator A B x y * g y.1 y.2 = twoComponentGenerator g x.1 x.2 := by
  have hsingle : ∀ (z : Fin (A + 1) × Fin (B + 1)) (c : ℝ),
      ∑ y : Fin (A + 1) × Fin (B + 1), (if y = z then c else 0) * g y.1 y.2 =
        c * g z.1 z.2 := by
    intro z c
    rw [Finset.sum_eq_single z (fun y _ hy ↦ by rw [if_neg hy, zero_mul])
      (fun hz ↦ absurd (Finset.mem_univ z) hz), if_pos rfl]
  simp only [loadGenerator, sub_mul, add_mul, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    hsingle]
  simp only [lowerFirst, lowerSecond, twoComponentGenerator]
  ring

/-- The row sums of the killed generator are minus the killing rate `ab`. -/
theorem sum_loadGenerator (A B : ℕ) (x : Fin (A + 1) × Fin (B + 1)) :
    ∑ y, loadGenerator A B x y = -(((x.1 : ℕ) : ℝ) * (x.2 : ℕ)) := by
  have h := sum_loadGenerator_mul A B (fun _ _ ↦ 1) x
  simp only [mul_one] at h
  rw [h, twoComponentGenerator_one]

/-- The rows of the square of the killed generator are the generator applied twice to the
constant one. -/
theorem sum_loadGenerator_sq (A B : ℕ) (x : Fin (A + 1) × Fin (B + 1)) :
    ∑ y, (loadGenerator A B * loadGenerator A B) x y =
      twoComponentGenerator (twoComponentGenerator fun _ _ ↦ 1) x.1 x.2 := by
  rw [← sum_loadGenerator_mul A B _ x]
  simp only [Matrix.mul_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun z _ ↦ ?_
  have hrow := sum_loadGenerator_mul A B (fun _ _ ↦ 1) z
  simp only [mul_one] at hrow
  rw [← hrow, Finset.mul_sum]

/-! ### The survival semigroup -/

/-- **The survival function on the load grid**: `S_x(t) = δ_x e^{tQ} 𝟙`, the row sum from loads
`x` of the transition matrix of the killed chain. -/
def gridSurvival (A B : ℕ) (x : Fin (A + 1) × Fin (B + 1)) (t : ℝ) : ℝ :=
  ∑ y, NormedSpace.exp ℝ (t • loadGenerator A B) x y

/-- **The survival function of the two-component load chain** from loads `(a, b)`:
`S_{a,b}(t) = α e^{tQ} 𝟙` with `α` the point mass at `(a, b)`, on the grid of loads at most
`(a, b)`. -/
def survival (a b : ℕ) (t : ℝ) : ℝ :=
  gridSurvival a b (Fin.last a, Fin.last b) t

/-- **The transition matrices form a semigroup**: `e^{(s+t)Q} = e^{sQ} e^{tQ}`. -/
theorem exp_add_smul_loadGenerator (A B : ℕ) (s t : ℝ) :
    NormedSpace.exp ℝ ((s + t) • loadGenerator A B) =
      NormedSpace.exp ℝ (s • loadGenerator A B) * NormedSpace.exp ℝ (t • loadGenerator A B) := by
  have hcommute : Commute (s • loadGenerator A B) (t • loadGenerator A B) := by
    show s • loadGenerator A B * t • loadGenerator A B =
      t • loadGenerator A B * s • loadGenerator A B
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_comm s t]
  rw [add_smul]
  exact Matrix.exp_add_of_commute (𝕂 := ℝ) _ _ hcommute

/-- The survival functions start at one. -/
theorem gridSurvival_zero (A B : ℕ) (x : Fin (A + 1) × Fin (B + 1)) :
    gridSurvival A B x 0 = 1 := by
  simp [gridSurvival, Matrix.one_apply, NormedSpace.exp_zero]

/-- `S_{a,b}(0) = 1`. -/
theorem survival_zero (a b : ℕ) : survival a b 0 = 1 :=
  gridSurvival_zero a b _

/-- **Chapman-Kolmogorov for the survival functions**: `S_x(s + t) = Σ_y e^{sQ}(x, y) S_y(t)`. -/
theorem gridSurvival_add (A B : ℕ) (x : Fin (A + 1) × Fin (B + 1)) (s t : ℝ) :
    gridSurvival A B x (s + t) =
      ∑ y, NormedSpace.exp ℝ (s • loadGenerator A B) x y * gridSurvival A B y t := by
  simp only [gridSurvival, exp_add_smul_loadGenerator, Matrix.mul_apply, Finset.mul_sum]
  exact Finset.sum_comm

/-- **Chapman-Kolmogorov from loads `(a, b)`.** -/
theorem survival_add (a b : ℕ) (s t : ℝ) :
    survival a b (s + t) =
      ∑ y, NormedSpace.exp ℝ (s • loadGenerator a b) (Fin.last a, Fin.last b) y *
        gridSurvival a b y t :=
  gridSurvival_add a b _ s t

/-! ### The backward equation -/

/-- **The derivative of a row functional of the transition matrices**:
`d/dt Σ_y (M e^{tQ})(x, y) = Σ_y (M Q e^{tQ})(x, y)`. -/
theorem hasDerivAt_sum_mul_exp_smul {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M Q : Matrix ι ι ℝ) (x : ι) (t : ℝ) :
    HasDerivAt (fun u : ℝ ↦ ∑ y, (M * NormedSpace.exp ℝ (u • Q)) x y)
      (∑ y, (M * (Q * NormedSpace.exp ℝ (t • Q))) x y) t := by
  let rowSum : Matrix ι ι ℝ →ₗ[ℝ] ℝ :=
    { toFun := fun N ↦ ∑ y, (M * N) x y
      map_add' := fun N N' ↦ by
        simp only [Matrix.mul_add, Matrix.add_apply, Finset.sum_add_distrib]
      map_smul' := fun c N ↦ by
        simp only [Matrix.mul_smul, Matrix.smul_apply, smul_eq_mul, RingHom.id_apply,
          Finset.mul_sum] }
  have hcont : Continuous rowSum := LinearMap.continuous_of_finiteDimensional rowSum
  have key : HasDerivAt (fun u : ℝ ↦ rowSum (NormedSpace.exp ℝ (u • Q)))
      (rowSum (Q * NormedSpace.exp ℝ (t • Q))) t := by
    open scoped Matrix.Norms.Operator in
    exact (⟨rowSum, hcont⟩ : Matrix ι ι ℝ →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt (x := t)
      (hasDerivAt_exp_smul_const' (𝕂 := ℝ) Q t)
  exact key

/-- **The backward equation** `S' = Q S`: `d/dt S_x(t) = Σ_y Q(x, y) S_y(t)`. -/
theorem hasDerivAt_gridSurvival (A B : ℕ) (x : Fin (A + 1) × Fin (B + 1)) (t : ℝ) :
    HasDerivAt (gridSurvival A B x) (∑ y, loadGenerator A B x y * gridSurvival A B y t) t := by
  have h := hasDerivAt_sum_mul_exp_smul 1 (loadGenerator A B) x t
  simp only [Matrix.one_mul] at h
  have hvalue : ∑ y, (loadGenerator A B * NormedSpace.exp ℝ (t • loadGenerator A B)) x y =
      ∑ y, loadGenerator A B x y * gridSurvival A B y t := by
    simp only [Matrix.mul_apply, gridSurvival, Finset.mul_sum]
    exact Finset.sum_comm
  rw [hvalue] at h
  exact h

/-- A function on the load grid, read as a function of two natural numbers, zero off the grid. -/
def gridExtension (A B : ℕ) (f : Fin (A + 1) × Fin (B + 1) → ℝ) (a b : ℕ) : ℝ :=
  if h : a < A + 1 ∧ b < B + 1 then f (⟨a, h.1⟩, ⟨b, h.2⟩) else 0

/-- On the grid, the extension is the function itself. -/
theorem gridExtension_apply (A B : ℕ) (f : Fin (A + 1) × Fin (B + 1) → ℝ)
    (y : Fin (A + 1) × Fin (B + 1)) : gridExtension A B f y.1 y.2 = f y := by
  rw [gridExtension, dif_pos (show (y.1 : ℕ) < A + 1 ∧ (y.2 : ℕ) < B + 1 from
    ⟨y.1.isLt, y.2.isLt⟩)]

/-- **The backward equation in the loads**: the survival function from loads `x` has derivative
`twoComponentGenerator` applied to the survival functions of the load states. -/
theorem hasDerivAt_gridSurvival_eq_generator (A B : ℕ) (x : Fin (A + 1) × Fin (B + 1)) (t : ℝ) :
    HasDerivAt (gridSurvival A B x)
      (twoComponentGenerator (gridExtension A B fun y ↦ gridSurvival A B y t) x.1 x.2) t := by
  rw [← sum_loadGenerator_mul A B _ x]
  simp only [gridExtension_apply]
  exact hasDerivAt_gridSurvival A B x t

/-! ### The first two derivatives at zero -/

/-- The derivative of the survival function: `S_x'(t) = δ_x Q e^{tQ} 𝟙`. -/
theorem deriv_gridSurvival (A B : ℕ) (x : Fin (A + 1) × Fin (B + 1)) :
    deriv (gridSurvival A B x) =
      fun t ↦ ∑ y, (loadGenerator A B * NormedSpace.exp ℝ (t • loadGenerator A B)) x y := by
  funext t
  have h := hasDerivAt_sum_mul_exp_smul 1 (loadGenerator A B) x t
  simp only [Matrix.one_mul] at h
  exact h.deriv

/-- **The second derivative of the survival function**: `S_x''(t) = δ_x Q² e^{tQ} 𝟙`. -/
theorem hasDerivAt_deriv_gridSurvival (A B : ℕ) (x : Fin (A + 1) × Fin (B + 1)) (t : ℝ) :
    HasDerivAt (deriv (gridSurvival A B x))
      (∑ y, (loadGenerator A B * loadGenerator A B *
        NormedSpace.exp ℝ (t • loadGenerator A B)) x y) t := by
  rw [deriv_gridSurvival, Matrix.mul_assoc]
  exact hasDerivAt_sum_mul_exp_smul (loadGenerator A B) (loadGenerator A B) x t

/-- **The first derivative at zero is the generator applied to the constant one.** -/
theorem hasDerivAt_survival_generator_one (a b : ℕ) :
    HasDerivAt (survival a b) (twoComponentGenerator (fun _ _ ↦ 1) a b) 0 := by
  have hrow := sum_loadGenerator_mul a b (fun _ _ ↦ 1) (Fin.last a, Fin.last b)
  simp only [mul_one, Fin.val_last] at hrow
  have h := hasDerivAt_gridSurvival a b (Fin.last a, Fin.last b) 0
  simp only [gridSurvival_zero, mul_one] at h
  rw [← hrow]
  exact h

/-- **The second derivative at zero is the generator applied twice to the constant one.** -/
theorem hasDerivAt_deriv_survival_generator_twice (a b : ℕ) :
    HasDerivAt (deriv (survival a b))
      (twoComponentGenerator (twoComponentGenerator fun _ _ ↦ 1) a b) 0 := by
  have hsquare := sum_loadGenerator_sq a b (Fin.last a, Fin.last b)
  simp only [Fin.val_last] at hsquare
  have h := hasDerivAt_deriv_gridSurvival a b (Fin.last a, Fin.last b) 0
  simp only [zero_smul, NormedSpace.exp_zero, Matrix.mul_one] at h
  rw [← hsquare]
  exact h

/-- **Spec (B2), first derivative**: `S_{a,b}'(0) = -ab`. -/
theorem hasDerivAt_survival_zero (a b : ℕ) :
    HasDerivAt (survival a b) (-((a : ℝ) * b)) 0 := by
  rw [← twoComponentGenerator_one a b]
  exact hasDerivAt_survival_generator_one a b

/-- **Spec (B2), second derivative**: `S_{a,b}''(0) = (ab)² + ab(a + b - 2)/2`. -/
theorem hasDerivAt_deriv_survival_zero (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    HasDerivAt (deriv (survival a b))
      (((a : ℝ) * b) ^ 2 + (a : ℝ) * b * ((a : ℝ) + b - 2) / 2) 0 := by
  rw [← (twoComponentGenerator_twice_one a b ha hb).2]
  exact hasDerivAt_deriv_survival_generator_twice a b

/-- `S_{a,b}'(0) = -ab`, as the value of `deriv`. -/
theorem deriv_survival_zero (a b : ℕ) : deriv (survival a b) 0 = -((a : ℝ) * b) :=
  (hasDerivAt_survival_zero a b).deriv

/-- `S_{a,b}''(0) = (ab)² + C(a,2) b + C(b,2) a = (ab)² + ab(a + b - 2)/2`, as the value of the
iterated `deriv`. -/
theorem deriv_deriv_survival_zero (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    deriv (deriv (survival a b)) 0 =
        ((a : ℝ) * b) ^ 2 + (Nat.choose a 2 : ℝ) * b + (Nat.choose b 2 : ℝ) * a ∧
      deriv (deriv (survival a b)) 0 =
        ((a : ℝ) * b) ^ 2 + (a : ℝ) * b * ((a : ℝ) + b - 2) / 2 := by
  rw [(hasDerivAt_deriv_survival_generator_twice a b).deriv]
  exact twoComponentGenerator_twice_one a b ha hb

/-! ### Theorem B for the survival function -/

/-- **Theorem B, necessity with two components, for the survival function.** Positive loads with
the same survival function form the same unordered pair. -/
theorem unorderedPair_of_survival_eq (a b a' b' : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) (ha' : 1 ≤ a')
    (hb' : 1 ≤ b') (h : survival a b = survival a' b') :
    (a' = a ∧ b' = b) ∨ (a' = b ∧ b' = a) := by
  have hfirst := (hasDerivAt_survival_generator_one a b).deriv
  have hsecond := (hasDerivAt_deriv_survival_generator_twice a b).deriv
  rw [h] at hfirst hsecond
  exact unorderedPair_of_survivalDerivatives_eq a b a' b' ha hb ha' hb'
    (hfirst.symm.trans (hasDerivAt_survival_generator_one a' b').deriv)
    (hsecond.symm.trans (hasDerivAt_deriv_survival_generator_twice a' b').deriv)

/-- Exchanging the two components conjugates the killed generator. -/
theorem loadGenerator_swap (a b : ℕ) (x y : Fin (b + 1) × Fin (a + 1)) :
    loadGenerator b a x y = loadGenerator a b x.swap y.swap := by
  have hfirst : y.swap = lowerFirst x.swap ↔ y = lowerSecond x := by
    rw [show lowerFirst x.swap = (lowerSecond x).swap from rfl, Prod.swap_injective.eq_iff]
  have hsecond : y.swap = lowerSecond x.swap ↔ y = lowerFirst x := by
    rw [show lowerSecond x.swap = (lowerFirst x).swap from rfl, Prod.swap_injective.eq_iff]
  have hdiagonal : y.swap = x.swap ↔ y = x := Prod.swap_injective.eq_iff
  simp only [loadGenerator, hfirst, hsecond, hdiagonal, Prod.fst_swap, Prod.snd_swap]
  split_ifs <;> ring

/-- Exchanging the two components conjugates the transition matrices. -/
theorem exp_smul_loadGenerator_swap (a b : ℕ) (t : ℝ) (x y : Fin (b + 1) × Fin (a + 1)) :
    NormedSpace.exp ℝ (t • loadGenerator b a) x y =
      NormedSpace.exp ℝ (t • loadGenerator a b) x.swap y.swap := by
  let swapAlgEquiv : Matrix (Fin (a + 1) × Fin (b + 1)) (Fin (a + 1) × Fin (b + 1)) ℝ ≃ₐ[ℝ]
      Matrix (Fin (b + 1) × Fin (a + 1)) (Fin (b + 1) × Fin (a + 1)) ℝ :=
    Matrix.reindexAlgEquiv ℝ ℝ (Equiv.prodComm _ _)
  have hcont : Continuous swapAlgEquiv := by
    show Continuous fun M : Matrix (Fin (a + 1) × Fin (b + 1)) (Fin (a + 1) × Fin (b + 1)) ℝ ↦
      Matrix.reindex (Equiv.prodComm _ _) (Equiv.prodComm _ _) M
    exact continuous_id.matrix_reindex _ _
  have hgenerator : t • loadGenerator b a = swapAlgEquiv (t • loadGenerator a b) := by
    ext x' y'
    show t • loadGenerator b a x' y' = t • loadGenerator a b x'.swap y'.swap
    rw [loadGenerator_swap]
  have hmap : swapAlgEquiv (NormedSpace.exp ℝ (t • loadGenerator a b)) =
      NormedSpace.exp ℝ (t • loadGenerator b a) := by
    rw [hgenerator]
    open scoped Matrix.Norms.Operator in
    exact NormedSpace.map_exp (𝕂 := ℝ) swapAlgEquiv hcont (t • loadGenerator a b)
  calc NormedSpace.exp ℝ (t • loadGenerator b a) x y
      = swapAlgEquiv (NormedSpace.exp ℝ (t • loadGenerator a b)) x y := by rw [hmap]
    _ = NormedSpace.exp ℝ (t • loadGenerator a b) x.swap y.swap := rfl

/-- **Theorem B, sufficiency with two components, for the survival function.** Exchanging the two
loads leaves the survival function unchanged. -/
theorem survival_swap (a b : ℕ) : survival b a = survival a b := by
  funext t
  simp only [survival, gridSurvival]
  rw [← Equiv.sum_comp (Equiv.prodComm (Fin (b + 1)) (Fin (a + 1)))]
  refine Finset.sum_congr rfl fun y _ ↦ ?_
  exact exp_smul_loadGenerator_swap a b t (Fin.last b, Fin.last a) y

/-- **Theorem B with two components, for the survival function.** For positive loads, the survival
function and the unordered pair of loads determine each other. -/
theorem survival_eq_iff (a b a' b' : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) (ha' : 1 ≤ a') (hb' : 1 ≤ b') :
    survival a b = survival a' b' ↔ ((a' = a ∧ b' = b) ∨ (a' = b ∧ b' = a)) := by
  constructor
  · exact unorderedPair_of_survival_eq a b a' b' ha hb ha' hb'
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · rfl
    · exact (survival_swap _ _).symm

end

end Descent.Pangenome.GraphCoalescent.TwoComponentSurvival
