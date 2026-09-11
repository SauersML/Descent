/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.PortabilityMasterTheorem
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

assert_below Descent.Decision Descent.Program

/-!
# Exact transport coordinates and the training leg with a singular second-moment matrix

TQ Proposition 3.1 is already the corpus's exact metric laws; `exact_transport_coordinates`
records the three coordinates of equation (3.1) against
`DeploymentPopulation.scoreVariance_eq`, `predictiveCovariance_eq` and
`outcomeVariance_eq`, and equation (3.2) is
`Deployment.predictiveCovariance_transport`.

The new content here is TQ Theorem 3.2 and UPT Theorem 4.3 in the **singular** case,
which the corpus's `§7` did not cover because it assumed an invertible covariance
matrix.  Mathlib at this pin has no Moore-Penrose pseudo-inverse, so the theorem is
formalized through the normal equations instead, which is what the pseudo-inverse is
there to express:

* `crossMoment_mem_range`: the cross-moment vector `c_X = E[XY]` always lies in the
  range of the second-moment matrix `Σ = E[XXᵀ]`, so some `w*` with `Σ w* = c_X` exists
  whatever the rank of `Σ`.  Proved from the kernel being `E`-null plus a rank-nullity
  splitting, with no positive-definiteness assumption anywhere.
* `excess_risk_law`: for that `w*` and **every** `w`,
  `E[(Y − wᵀX)²] = E[Y²] − c_Xᵀw* + (w − w*)ᵀΣ(w − w*)`, equation (3.4)/(4.5).
* `oracle_value_unique`: `c_Xᵀw*` does not depend on which solution `w*` is taken, which
  is what entitles the manuscript to write it as `c_Xᵀ Σ⁺ c_X`.

Builds on `Foundations.secondMomentMatrix`, `Foundations.secondMoment_quadratic_form`,
`Foundations.mse_transport_decomposition_general`, `Foundations.expMse`,
`Foundations.linScore`, `Foundations.dot` and
`Foundations.ExpFunctional.cauchy_schwarz`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.TransportCoordinates

open Foundations

noncomputable section

variable {Ω : Type*}
variable {J : Type*} [Fintype J] [DecidableEq J]

/-! ### TQ Proposition 3.1, recorded against the corpus's metric laws -/

section Coordinates

variable {L : Type*} [Fintype L] [DecidableEq L]

/-- **TQ Proposition 3.1, equation (3.1): the three exact transport coordinates.**
`u = wᵀΣ_X w`, `c = wᵀKβ + wᵀk_X`, `v = βᵀΣ_Cβ + 2βᵀk_C + Var(h)`.  Each conjunct is
the corpus's own exact metric law; this records the manuscript's labelling of them.
Equation (3.2), the ordered source-to-target decomposition of `c`, is
`Deployment.predictiveCovariance_transport`, and equation (3.3) is the log-derivative
law of `PortabilityCurveClassification`. -/
theorem exact_transport_coordinates (P : DeploymentPopulation Ω J L) (w : J → ℝ) :
    P.scoreVariance w = dot w (P.sigmaX.mulVec w) ∧
      P.predictiveCovariance w = dot w (P.kappa.mulVec P.β) + dot w P.contextX ∧
        P.outcomeVariance = dot P.β (P.sigmaC.mulVec P.β) + 2 * dot P.β P.contextC
          + variance P.E P.h :=
  ⟨P.scoreVariance_eq w, P.predictiveCovariance_eq w, P.outcomeVariance_eq⟩

end Coordinates

/-! ### Uncentered second moments -/

/-- The cross-moment vector `c_X = E[X Y]`.  Unlike `crossCovVector` this subtracts no
means: TQ §3.2 works after a specified exact mean adjustment, so the second moments are
the objects in play. -/
def crossMomentVector (E : ExpFunctional Ω) (X : Ω → J → ℝ) (Y : Ω → ℝ) : J → ℝ :=
  fun i ↦ E (fun ω ↦ X ω i * Y ω)

/-- The outcome second moment `v = E[Y²]`. -/
def outcomeSecondMoment (E : ExpFunctional Ω) (Y : Ω → ℝ) : ℝ := E (fun ω ↦ Y ω ^ 2)

/-- A linear score read against the outcome is the weights read against the
cross-moment vector. -/
theorem crossMoment_dot (E : ExpFunctional Ω) (X : Ω → J → ℝ) (Y : Ω → ℝ) (z : J → ℝ) :
    E (fun ω ↦ dot z (X ω) * Y ω) = dot z (crossMomentVector E X Y) := by
  have hsum : (fun ω ↦ dot z (X ω) * Y ω) = ∑ i, (z i) • (fun ω ↦ X ω i * Y ω) := by
    funext ω
    simp [dot, Finset.sum_mul, smul_eq_mul, mul_assoc, Descent.Core.innerSum]
  rw [hsum, ExpFunctional.eval_sum]
  unfold dot crossMomentVector Descent.Core.innerSum
  exact Finset.sum_congr rfl fun i _ ↦ E.smul_eval (z i) _

/-- A coordinate read against a linear score is the second-moment matrix applied to the
weights. -/
theorem coordinate_secondMoment (E : ExpFunctional Ω) (X : Ω → J → ℝ) (w : J → ℝ)
    (i : J) :
    E (fun ω ↦ X ω i * dot w (X ω)) = ((secondMomentMatrix E X).mulVec w) i := by
  have h_expand : (fun ω ↦ X ω i * dot w (X ω))
      = ∑ j, (w j) • (fun ω ↦ X ω i * X ω j) := by
    funext ω
    simp [dot, Finset.mul_sum, smul_eq_mul, mul_left_comm, mul_comm,
      Descent.Core.innerSum]
  rw [h_expand, ExpFunctional.eval_sum]
  rw [show (∑ j, E ((w j) • fun ω ↦ X ω i * X ω j))
      = ∑ j, w j * E (fun ω ↦ X ω i * X ω j) from
    Finset.sum_congr rfl fun j _ ↦ E.smul_eval (w j) _]
  unfold secondMomentMatrix
  simp only [Matrix.mulVec, dotProduct, Matrix.of_apply]
  exact Finset.sum_congr rfl fun j _ ↦ mul_comm (w j) _

/-- **The normal equations in matrix form.**  A weight vector is a least-squares
solution exactly when the second-moment matrix maps it to the cross-moment vector. -/
theorem normal_equations_iff (E : ExpFunctional Ω) (X : Ω → J → ℝ) (Y : Ω → ℝ)
    (wStar : J → ℝ) :
    (∀ i, E (fun ω ↦ X ω i * (Y ω - dot wStar (X ω))) = 0)
      ↔ (secondMomentMatrix E X).mulVec wStar = crossMomentVector E X Y := by
  have hsub : ∀ i : J, (fun ω ↦ X ω i * (Y ω - dot wStar (X ω)))
      = (fun ω ↦ X ω i * Y ω) - (fun ω ↦ X ω i * dot wStar (X ω)) := by
    intro i
    funext ω
    simp only [Pi.sub_apply]
    ring
  constructor
  · intro h
    funext i
    have hi := h i
    rw [hsub i, E.eval_sub, coordinate_secondMoment] at hi
    have hc : crossMomentVector E X Y i = E (fun ω ↦ X ω i * Y ω) := rfl
    rw [hc]
    linarith
  · intro h i
    rw [hsub i, E.eval_sub, coordinate_secondMoment, h]
    have hc : crossMomentVector E X Y i = E (fun ω ↦ X ω i * Y ω) := rfl
    rw [hc]
    ring

/-! ### The cross-moment vector lies in the range of the second-moment matrix -/

/-- A vector of zero self-inner-product is zero. -/
theorem dot_self_eq_zero (y : J → ℝ) (h : dot y y = 0) : y = 0 := by
  funext j
  have hnn : ∀ i ∈ (Finset.univ : Finset J), 0 ≤ y i * y i :=
    fun i _ ↦ mul_self_nonneg _
  have hle : y j * y j ≤ ∑ i, y i * y i := Finset.single_le_sum hnn (Finset.mem_univ j)
  have hsum : ∑ i, y i * y i = 0 := h
  have hzero : y j * y j = 0 := by
    rw [hsum] at hle
    exact le_antisymm hle (mul_self_nonneg _)
  simpa using mul_self_eq_zero.mp hzero

/-- Addition on the left of an inner sum, in the `Pi` phrasing. -/
theorem dot_add_left_pi (x y z : J → ℝ) : dot (x + y) z = dot x z + dot y z := by
  simp [dot, Descent.Core.innerSum, Pi.add_apply, add_mul, Finset.sum_add_distrib]

/-- An inner sum against the zero vector vanishes. -/
theorem dot_zero_right (x : J → ℝ) : dot x (0 : J → ℝ) = 0 := by
  simp [dot, Descent.Core.innerSum]

/-- **Polarization of the second-moment quadratic form.**  This is what replaces an
explicit symmetry lemma: the right-hand side is visibly symmetric in the two weight
vectors. -/
theorem secondMoment_polarization (E : ExpFunctional Ω) (X : Ω → J → ℝ) (x y : J → ℝ) :
    dot x ((secondMomentMatrix E X).mulVec y) + dot y ((secondMomentMatrix E X).mulVec x)
      = 2 * E (fun ω ↦ dot x (X ω) * dot y (X ω)) := by
  have hsum := secondMoment_quadratic_form E X (x + y)
  have hx := secondMoment_quadratic_form E X x
  have hy := secondMoment_quadratic_form E X y
  have hL : (fun ω ↦ dot (x + y) (X ω) ^ 2)
      = (fun ω ↦ dot x (X ω) ^ 2) + ((2:ℝ) • fun ω ↦ dot x (X ω) * dot y (X ω))
        + (fun ω ↦ dot y (X ω) ^ 2) := by
    funext ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, dot_add_left_pi]
    ring
  have hR : dot (x + y) ((secondMomentMatrix E X).mulVec (x + y))
      = dot x ((secondMomentMatrix E X).mulVec x)
        + dot x ((secondMomentMatrix E X).mulVec y)
        + dot y ((secondMomentMatrix E X).mulVec x)
        + dot y ((secondMomentMatrix E X).mulVec y) := by
    rw [Matrix.mulVec_add, dot_add_left_pi, dot_add_right, dot_add_right]
    ring
  rw [hL, E.add_eval, E.add_eval, E.smul_eval, hR] at hsum
  linarith

/-- A kernel vector of the second-moment matrix gives an `E`-null linear score. -/
theorem kernel_score_null (E : ExpFunctional Ω) (X : Ω → J → ℝ) (z : J → ℝ)
    (hz : (secondMomentMatrix E X).mulVec z = 0) :
    E (fun ω ↦ dot z (X ω) ^ 2) = 0 := by
  rw [secondMoment_quadratic_form, hz, dot_zero_right]

/-- **The kernel of the second-moment matrix is orthogonal to every direction it can
reach.** -/
theorem dot_kernel_range_zero (E : ExpFunctional Ω) (X : Ω → J → ℝ) (z x : J → ℝ)
    (hz : (secondMomentMatrix E X).mulVec z = 0) :
    dot z ((secondMomentMatrix E X).mulVec x) = 0 := by
  have hpol := secondMoment_polarization E X z x
  rw [hz, dot_zero_right] at hpol
  have hcs := ExpFunctional.cauchy_schwarz E (fun ω ↦ dot z (X ω)) (fun ω ↦ dot x (X ω))
  rw [kernel_score_null E X z hz, zero_mul] at hcs
  have hprod : E (fun ω ↦ dot z (X ω) * dot x (X ω)) = 0 := by
    have heq : E (fun ω ↦ dot z (X ω) * dot x (X ω)) ^ 2 = 0 :=
      le_antisymm hcs (sq_nonneg _)
    by_contra hne
    exact absurd heq (pow_ne_zero 2 hne)
  rw [hprod] at hpol
  linarith

/-- **The kernel of the second-moment matrix is orthogonal to the cross-moment
vector.**  This is the manuscript's `zᵀc_X = 0` for `z ∈ ker Σ`, proved from
Cauchy-Schwarz rather than from an almost-sure argument. -/
theorem kernel_orthogonal_crossMoment (E : ExpFunctional Ω) (X : Ω → J → ℝ) (Y : Ω → ℝ)
    (z : J → ℝ) (hz : (secondMomentMatrix E X).mulVec z = 0) :
    dot z (crossMomentVector E X Y) = 0 := by
  have hcs := ExpFunctional.cauchy_schwarz E (fun ω ↦ dot z (X ω)) Y
  rw [kernel_score_null E X z hz, zero_mul] at hcs
  have hprod : E (fun ω ↦ dot z (X ω) * Y ω) = 0 := by
    have heq : E (fun ω ↦ dot z (X ω) * Y ω) ^ 2 = 0 := le_antisymm hcs (sq_nonneg _)
    by_contra hne
    exact absurd heq (pow_ne_zero 2 hne)
  rw [← crossMoment_dot]
  exact hprod

/-- **TQ Theorem 3.2 / UPT Theorem 4.3: `c_X ∈ range(Σ)`.**  Whatever the rank of the
second-moment matrix, the cross-moment vector is in its range, so a least-squares
weight vector exists.  No invertibility, no positive definiteness, no pseudo-inverse:
the kernel is `E`-null, and a symmetric matrix splits its space into kernel and
range. -/
theorem crossMoment_mem_range (E : ExpFunctional Ω) (X : Ω → J → ℝ) (Y : Ω → ℝ) :
    ∃ wStar : J → ℝ,
      (secondMomentMatrix E X).mulVec wStar = crossMomentVector E X Y := by
  classical
  have hdisj : Disjoint (LinearMap.ker (Matrix.mulVecLin (secondMomentMatrix E X)))
      (LinearMap.range (Matrix.mulVecLin (secondMomentMatrix E X))) := by
    rw [Submodule.disjoint_def]
    intro y hy hyr
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hy
    rw [LinearMap.mem_range] at hyr
    obtain ⟨u, hu⟩ := hyr
    rw [Matrix.mulVecLin_apply] at hu
    have hzz : dot y y = 0 := by
      have hd := dot_kernel_range_zero E X y u hy
      rw [hu] at hd
      exact hd
    exact dot_self_eq_zero y hzz
  have htop : LinearMap.ker (Matrix.mulVecLin (secondMomentMatrix E X))
      ⊔ LinearMap.range (Matrix.mulVecLin (secondMomentMatrix E X)) = ⊤ := by
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq
      (LinearMap.ker (Matrix.mulVecLin (secondMomentMatrix E X)))
      (LinearMap.range (Matrix.mulVecLin (secondMomentMatrix E X)))
    have h2 := LinearMap.finrank_range_add_finrank_ker
      (Matrix.mulVecLin (secondMomentMatrix E X))
    rw [disjoint_iff.mp hdisj, finrank_bot] at h1
    refine Submodule.eq_top_of_finrank_eq ?_
    omega
  have hmem : crossMomentVector E X Y
      ∈ LinearMap.ker (Matrix.mulVecLin (secondMomentMatrix E X))
        ⊔ LinearMap.range (Matrix.mulVecLin (secondMomentMatrix E X)) := by
    rw [htop]
    trivial
  rw [Submodule.mem_sup] at hmem
  obtain ⟨k, hk, r, hr, hsum⟩ := hmem
  rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hk
  rw [LinearMap.mem_range] at hr
  obtain ⟨u, hu⟩ := hr
  rw [Matrix.mulVecLin_apply] at hu
  have hkr : dot k r = 0 := by
    rw [← hu]
    exact dot_kernel_range_zero E X k u hk
  have hkc : dot k (crossMomentVector E X Y) = 0 :=
    kernel_orthogonal_crossMoment E X Y k hk
  have hkk : dot k k = 0 := by
    have hexp : dot k (crossMomentVector E X Y) = dot k k + dot k r := by
      rw [← hsum, dot_add_right]
    rw [hkc, hkr] at hexp
    linarith
  have hk0 : k = 0 := dot_self_eq_zero k hkk
  refine ⟨u, ?_⟩
  rw [hu, ← hsum, hk0, zero_add]

/-! ### The exact training decomposition -/

/-- Expansion of a mean squared error into second moments. -/
theorem expMse_expand (E : ExpFunctional Ω) (X : Ω → J → ℝ) (Y : Ω → ℝ) (w : J → ℝ) :
    expMse E Y (linScore w X) = outcomeSecondMoment E Y
        - 2 * E (fun ω ↦ dot w (X ω) * Y ω) + E (fun ω ↦ dot w (X ω) ^ 2) := by
  have hsplit : (fun ω ↦ (Y ω - dot w (X ω)) ^ 2)
      = (fun ω ↦ Y ω ^ 2) + ((-2 : ℝ) • fun ω ↦ dot w (X ω) * Y ω)
        + (fun ω ↦ dot w (X ω) ^ 2) := by
    funext ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  unfold expMse linScore outcomeSecondMoment
  rw [hsplit, E.add_eval, E.add_eval, E.smul_eval]
  ring

/-- **The oracle risk.**  A least-squares weight vector leaves exactly `v − c_Xᵀw*`. -/
theorem oracle_risk_eq (E : ExpFunctional Ω) (X : Ω → J → ℝ) (Y : Ω → ℝ) (wStar : J → ℝ)
    (hstar : (secondMomentMatrix E X).mulVec wStar = crossMomentVector E X Y) :
    expMse E Y (linScore wStar X)
      = outcomeSecondMoment E Y - dot wStar (crossMomentVector E X Y) := by
  have hquad := secondMoment_quadratic_form E X wStar
  rw [hstar] at hquad
  rw [expMse_expand, crossMoment_dot, hquad]
  ring

/-- **The exact excess-risk law with no cross term**, for any least-squares solution. -/
theorem training_risk_decomposition (E : ExpFunctional Ω) (X : Ω → J → ℝ) (Y : Ω → ℝ)
    (wStar w : J → ℝ)
    (hstar : (secondMomentMatrix E X).mulVec wStar = crossMomentVector E X Y) :
    expMse E Y (linScore w X)
      = expMse E Y (linScore wStar X)
        + dot (fun i ↦ w i - wStar i)
            ((secondMomentMatrix E X).mulVec (fun i ↦ w i - wStar i)) := by
  have hnormal := (normal_equations_iff E X Y wStar).mpr hstar
  have hdecomp := mse_transport_decomposition_general E X Y wStar w hnormal
  have hquad := secondMoment_quadratic_form E X (fun i ↦ w i - wStar i)
  unfold expMse linScore
  rw [hdecomp, hquad]

/-- **TQ Theorem 3.2 equation (3.4) / UPT Theorem 4.3 equation (4.5).**
`E[(Y − wᵀX)²] = E[Y²] − c_Xᵀ w* + (w − w*)ᵀ Σ (w − w*)` for every `w`, with `w*` any
solution of the normal equations.  Nothing here requires `Σ` to be invertible. -/
theorem excess_risk_law (E : ExpFunctional Ω) (X : Ω → J → ℝ) (Y : Ω → ℝ)
    (wStar w : J → ℝ)
    (hstar : (secondMomentMatrix E X).mulVec wStar = crossMomentVector E X Y) :
    expMse E Y (linScore w X)
      = outcomeSecondMoment E Y - dot wStar (crossMomentVector E X Y)
        + dot (fun i ↦ w i - wStar i)
            ((secondMomentMatrix E X).mulVec (fun i ↦ w i - wStar i)) := by
  rw [training_risk_decomposition E X Y wStar w hstar, oracle_risk_eq E X Y wStar hstar]

/-! ### The oracle value is well defined -/

/-- Expansion of the mean square of a difference. -/
theorem expand_sq_diff (E : ExpFunctional Ω) (a b : Ω → ℝ) :
    E (fun ω ↦ (a ω - b ω) ^ 2)
      = E (fun ω ↦ a ω ^ 2) - 2 * E (fun ω ↦ a ω * b ω) + E (fun ω ↦ b ω ^ 2) := by
  have hsplit : (fun ω ↦ (a ω - b ω) ^ 2)
      = (fun ω ↦ a ω ^ 2) + ((-2 : ℝ) • fun ω ↦ a ω * b ω) + (fun ω ↦ b ω ^ 2) := by
    funext ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [hsplit, E.add_eval, E.add_eval, E.smul_eval]
  ring

/-- Expansion of a product against a difference. -/
theorem expand_mul_sub (E : ExpFunctional Ω) (a b : Ω → ℝ) :
    E (fun ω ↦ a ω * (a ω - b ω))
      = E (fun ω ↦ a ω ^ 2) - E (fun ω ↦ a ω * b ω) := by
  have hsplit : (fun ω ↦ a ω * (a ω - b ω))
      = (fun ω ↦ a ω ^ 2) + ((-1 : ℝ) • fun ω ↦ a ω * b ω) := by
    funext ω
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [hsplit, E.add_eval, E.smul_eval]
  ring

/-- **The oracle value `c_Xᵀ w*` is the same for every least-squares solution.**  That
is what entitles the manuscript to write it as `c_Xᵀ Σ⁺ c_X`: the number is a function
of the moments, not of the choice of solution. -/
theorem oracle_value_unique (E : ExpFunctional Ω) (X : Ω → J → ℝ) (Y : Ω → ℝ)
    (w1 w2 : J → ℝ)
    (h1 : (secondMomentMatrix E X).mulVec w1 = crossMomentVector E X Y)
    (h2 : (secondMomentMatrix E X).mulVec w2 = crossMomentVector E X Y) :
    dot w1 (crossMomentVector E X Y) = dot w2 (crossMomentVector E X Y) := by
  have hq1 : E (fun ω ↦ dot w1 (X ω) ^ 2) = dot w1 (crossMomentVector E X Y) := by
    rw [secondMoment_quadratic_form, h1]
  have hq2 : E (fun ω ↦ dot w2 (X ω) ^ 2) = dot w2 (crossMomentVector E X Y) := by
    rw [secondMoment_quadratic_form, h2]
  have hpol := secondMoment_polarization E X w1 w2
  rw [h1, h2] at hpol
  have hdiff : E (fun ω ↦ (dot w1 (X ω) - dot w2 (X ω)) ^ 2) = 0 := by
    rw [expand_sq_diff, hq1, hq2]
    linarith
  have hcs1 := ExpFunctional.cauchy_schwarz E (fun ω ↦ dot w1 (X ω))
    (fun ω ↦ dot w1 (X ω) - dot w2 (X ω))
  have hcs2 := ExpFunctional.cauchy_schwarz E (fun ω ↦ dot w2 (X ω))
    (fun ω ↦ dot w1 (X ω) - dot w2 (X ω))
  rw [hdiff, mul_zero] at hcs1 hcs2
  have hz1 : E (fun ω ↦ dot w1 (X ω) * (dot w1 (X ω) - dot w2 (X ω))) = 0 := by
    have heq : E (fun ω ↦ dot w1 (X ω) * (dot w1 (X ω) - dot w2 (X ω))) ^ 2 = 0 :=
      le_antisymm hcs1 (sq_nonneg _)
    by_contra hne
    exact absurd heq (pow_ne_zero 2 hne)
  have hz2 : E (fun ω ↦ dot w2 (X ω) * (dot w1 (X ω) - dot w2 (X ω))) = 0 := by
    have heq : E (fun ω ↦ dot w2 (X ω) * (dot w1 (X ω) - dot w2 (X ω))) ^ 2 = 0 :=
      le_antisymm hcs2 (sq_nonneg _)
    by_contra hne
    exact absurd heq (pow_ne_zero 2 hne)
  rw [expand_mul_sub] at hz1
  have hz2' : E (fun ω ↦ dot w2 (X ω) * dot w1 (X ω))
      - E (fun ω ↦ dot w2 (X ω) ^ 2) = 0 := by
    have hsplit : (fun ω ↦ dot w2 (X ω) * (dot w1 (X ω) - dot w2 (X ω)))
        = (fun ω ↦ dot w2 (X ω) * dot w1 (X ω))
          + ((-1 : ℝ) • fun ω ↦ dot w2 (X ω) ^ 2) := by
      funext ω
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [hsplit, E.add_eval, E.smul_eval] at hz2
    linarith
  have hcomm : E (fun ω ↦ dot w1 (X ω) * dot w2 (X ω))
      = E (fun ω ↦ dot w2 (X ω) * dot w1 (X ω)) := by
    congr 1
    funext ω
    ring
  rw [← hq1, ← hq2]
  linarith [hz1, hz2', hcomm]

/-! ### UPT Theorem 4.3, the centered second-moment metric laws -/

/-- A centered coordinate family gives a mean-zero linear score. -/
theorem linScore_mean_zero (E : ExpFunctional Ω) (X : Ω → J → ℝ) (w : J → ℝ)
    (hcentered : ∀ j, E (fun ω ↦ X ω j) = 0) : E (linScore w X) = 0 := by
  have hzero : (fun j ↦ E (fun ω ↦ X ω j)) = (0 : J → ℝ) := funext hcentered
  rw [eval_linScore, hzero, dot_zero_right]

/-- **UPT equation (4.4), first identity: `Var(wᵀX) = wᵀΣw` on centered features.** -/
theorem centered_score_variance (E : ExpFunctional Ω) (X : Ω → J → ℝ) (w : J → ℝ)
    (hcentered : ∀ j, E (fun ω ↦ X ω j) = 0) :
    variance E (linScore w X) = dot w ((secondMomentMatrix E X).mulVec w) := by
  have hsq : (fun ω ↦ linScore w X ω ^ 2) = fun ω ↦ dot w (X ω) ^ 2 := rfl
  rw [variance_eq_expect_sq_sub_sq_mean, linScore_mean_zero E X w hcentered, hsq,
    secondMoment_quadratic_form]
  ring

/-- **UPT equation (4.4), second identity: `Cov(wᵀX, Y) = wᵀc` on centered features.** -/
theorem centered_predictive_covariance (E : ExpFunctional Ω) (X : Ω → J → ℝ) (Y : Ω → ℝ)
    (w : J → ℝ) (hcentered : ∀ j, E (fun ω ↦ X ω j) = 0) :
    covariance E (linScore w X) Y = dot w (crossMomentVector E X Y) := by
  have hprod : (fun ω ↦ linScore w X ω * Y ω) = fun ω ↦ dot w (X ω) * Y ω := rfl
  rw [covariance_eq_expect_mul_sub_means, linScore_mean_zero E X w hcentered, hprod,
    crossMoment_dot]
  ring

/-- **UPT equation (4.4): the exact squared correlation of a learned score.**
`q(w) = (wᵀc)² / (v · wᵀΣw)` on centered features and a centered outcome. -/
theorem centered_score_r2 (E : ExpFunctional Ω) (X : Ω → J → ℝ) (Y : Ω → ℝ) (w : J → ℝ)
    (hcentered : ∀ j, E (fun ω ↦ X ω j) = 0) (hY : E Y = 0) :
    covariance E (linScore w X) Y ^ 2 / (variance E (linScore w X) * variance E Y)
      = dot w (crossMomentVector E X Y) ^ 2
        / (outcomeSecondMoment E Y * dot w ((secondMomentMatrix E X).mulVec w)) := by
  have hvarY : variance E Y = outcomeSecondMoment E Y := by
    unfold outcomeSecondMoment
    rw [variance_eq_expect_sq_sub_sq_mean, hY]
    ring
  rw [centered_predictive_covariance E X Y w hcentered,
    centered_score_variance E X w hcentered, hvarY, mul_comm]

/-! ### The training leg with a sampling law for the learned weights -/

section LearnedWeights

variable {Θ : Type*}

/-- The mean of a learned weight vector under its own sampling law. -/
def weightMean (W : ExpFunctional Θ) (what : Θ → J → ℝ) : J → ℝ :=
  fun j ↦ W (fun θ ↦ what θ j)

/-- The covariance matrix of a learned weight vector under its own sampling law. -/
def weightCovariance (W : ExpFunctional Θ) (what : Θ → J → ℝ) : Matrix J J ℝ :=
  Matrix.of fun j k ↦
    W (fun θ ↦ (what θ j - weightMean W what j) * (what θ k - weightMean W what k))

/-- The weight covariance matrix is symmetric. -/
theorem weightCovariance_symm (W : ExpFunctional Θ) (what : Θ → J → ℝ) (j k : J) :
    weightCovariance W what j k = weightCovariance W what k j := by
  unfold weightCovariance
  simp only [Matrix.of_apply]
  congr 1
  funext θ
  ring

/-- A quadratic form written as a double sum. -/
theorem quadratic_form_sum (M : Matrix J J ℝ) (u : J → ℝ) :
    dot u (M.mulVec u) = ∑ j, ∑ k, M j k * u j * u k := by
  unfold dot Descent.Core.innerSum
  simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun k _ ↦ by ring

/-- The trace of a product against a symmetric matrix is the entrywise sum. -/
theorem trace_mul_symm (M V : Matrix J J ℝ) (hV : ∀ j k, V j k = V k j) :
    Matrix.trace (M * V) = ∑ j, ∑ k, M j k * V j k := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun k _ ↦ ?_
  rw [hV k j]

/-- The second moment of a weight error splits into a squared bias and a covariance
entry, with no cross term: the sampling fluctuation has mean zero by construction. -/
theorem weight_second_moment (W : ExpFunctional Θ) (what : Θ → J → ℝ) (wStar : J → ℝ)
    (j k : J) :
    W (fun θ ↦ (what θ j - wStar j) * (what θ k - wStar k))
      = (weightMean W what j - wStar j) * (weightMean W what k - wStar k)
        + weightCovariance W what j k := by
  have hmj : W (fun θ ↦ what θ j - weightMean W what j) = 0 :=
    eval_centered_zero W (fun θ ↦ what θ j)
  have hmk : W (fun θ ↦ what θ k - weightMean W what k) = 0 :=
    eval_centered_zero W (fun θ ↦ what θ k)
  have hsplit : (fun θ ↦ (what θ j - wStar j) * (what θ k - wStar k))
      = (fun θ ↦ (what θ j - weightMean W what j) * (what θ k - weightMean W what k))
        + ((weightMean W what k - wStar k) • fun θ ↦ what θ j - weightMean W what j)
        + ((weightMean W what j - wStar j) • fun θ ↦ what θ k - weightMean W what k)
        + (fun _ : Θ ↦ (weightMean W what j - wStar j)
            * (weightMean W what k - wStar k)) := by
    funext θ
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [hsplit, W.add_eval, W.add_eval, W.add_eval, W.smul_eval, W.smul_eval,
    ExpFunctional.eval_const, hmj, hmk]
  unfold weightCovariance
  simp only [Matrix.of_apply]
  ring

/-- **TQ Theorem 3.2 equation (3.5): the expected target risk of a learned score.**
`E R_t(ŵ) = v − c_Xᵀw* + (w̄ − w*)ᵀΣ(w̄ − w*) + tr(Σ V_w)`.  The learned weights carry
their own sampling law on a separate space, which is the manuscript's independence of
the learned weight from the target individual; `§3.2` warns that this independence must
not be inserted after marginalizing shared latent parameters away, and nothing here
does so, because the two expectations are over unrelated spaces by construction. -/
theorem expected_training_risk (E : ExpFunctional Ω) (X : Ω → J → ℝ) (Y : Ω → ℝ)
    (W : ExpFunctional Θ) (what : Θ → J → ℝ) (wStar : J → ℝ)
    (hstar : (secondMomentMatrix E X).mulVec wStar = crossMomentVector E X Y) :
    W (fun θ ↦ expMse E Y (linScore (what θ) X))
      = outcomeSecondMoment E Y - dot wStar (crossMomentVector E X Y)
        + dot (fun j ↦ weightMean W what j - wStar j)
            ((secondMomentMatrix E X).mulVec (fun j ↦ weightMean W what j - wStar j))
        + Matrix.trace (secondMomentMatrix E X * weightCovariance W what) := by
  have hfun : (fun θ ↦ expMse E Y (linScore (what θ) X))
      = (fun _ : Θ ↦ outcomeSecondMoment E Y - dot wStar (crossMomentVector E X Y))
        + ∑ j, ∑ k, ((secondMomentMatrix E X j k)
            • fun θ ↦ (what θ j - wStar j) * (what θ k - wStar k)) := by
    funext θ
    rw [excess_risk_law E X Y wStar (what θ) hstar, quadratic_form_sum]
    simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    congr 1
    exact Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun k _ ↦ by ring
  have hinner : ∀ j : J,
      W (∑ k, ((secondMomentMatrix E X j k)
          • fun θ ↦ (what θ j - wStar j) * (what θ k - wStar k)))
        = ∑ k, secondMomentMatrix E X j k
            * ((weightMean W what j - wStar j) * (weightMean W what k - wStar k)
              + weightCovariance W what j k) := by
    intro j
    rw [ExpFunctional.eval_sum]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [W.smul_eval, weight_second_moment]
  have hsum : (∑ j, W (∑ k, ((secondMomentMatrix E X j k)
        • fun θ ↦ (what θ j - wStar j) * (what θ k - wStar k))))
      = ∑ j, ∑ k, secondMomentMatrix E X j k
          * ((weightMean W what j - wStar j) * (weightMean W what k - wStar k)
            + weightCovariance W what j k) :=
    Finset.sum_congr rfl fun j _ ↦ hinner j
  have hsplit2 : (∑ j, ∑ k, secondMomentMatrix E X j k
        * ((weightMean W what j - wStar j) * (weightMean W what k - wStar k)
          + weightCovariance W what j k))
      = (∑ j, ∑ k, secondMomentMatrix E X j k * (weightMean W what j - wStar j)
          * (weightMean W what k - wStar k))
        + ∑ j, ∑ k, secondMomentMatrix E X j k * weightCovariance W what j k := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ ↦ by ring
  rw [hfun, W.add_eval, ExpFunctional.eval_const, ExpFunctional.eval_sum, hsum, hsplit2,
    quadratic_form_sum, trace_mul_symm (secondMomentMatrix E X) (weightCovariance W what)
      (weightCovariance_symm W what)]
  ring

end LearnedWeights

end

end Descent.Portability.TransportCoordinates
