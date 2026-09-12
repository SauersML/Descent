/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Layer
import Mathlib.Topology.ContinuousMap.StoneWeierstrass

assert_below Descent.PopGen Descent.Spectral Descent.Blindness Descent.Conditionals
assert_below Descent.Portability Descent.Decision Descent.Program

/-!
# The infinite-genome limit as a Feller semigroup

Theorem 9 of the ancestral-locality note takes a countable genome `V` with a locally finite
checking graph of bounded total rate `D`, and concludes that the finite-genome models along an
exhaustion determine one limiting Feller semigroup on `P({0,1}^V)`, independent of the
exhaustion. Its proof outline has four analytic steps: the finite-genome sampling operators
converge uniformly, with error at most `2 ‖f‖_∞ Pr(E_{ℓ,T})` from the light cone of Theorem 8;
the cylinder sampling polynomials are dense in `C(P(H))`; the limiting operators extend to
positive, constant-preserving contractions obeying the semigroup law and strong continuity; and
the limit is unique through the separating algebra. This module proves the operator half of those
steps on any compact space `X` with a point-separating subalgebra `A` of observables.

`FellerSemigroup X` is a family of positive, constant-preserving sup-norm contractions of
`C(X, ℝ)` with the semigroup law and strong continuity at time zero, which gives strong continuity
at every time (`FellerSemigroup.continuous_operator`). `LightConeApproximation S A`
is the uniform approximation bound, taken as a named hypothesis: the semigroups `S m` along the
exhaustion are within `2 ‖f‖ · escape f T m` of every later member on each observable `f ∈ A` at
every time up to `T`, and the escape bound tends to zero along the exhaustion.

The limit. `dense_subalgebra_of_separatesPoints` is Stone–Weierstrass, `norm_operator_sub_le`
moves the observable by a contraction's own bound, and `cauchySeq_operator` combines the two: on
every continuous observable, not only on `A`, the finite-genome operators form a Cauchy sequence.
`limitValue` is its limit, `limitOperator` the resulting bounded linear operator, and
`limitSemigroup` packages the limit as a Feller semigroup: contraction (`norm_limitValue_le`),
positivity (`limitValue_nonneg`), the constant (`limitValue_one`), time zero (`limitValue_zero`),
the semigroup law (`limitValue_add`), and strong continuity (`tendsto_limitValue_zero`), which
uses that the convergence is uniform in time up to any horizon (`norm_limitValue_sub_le`).

Uniqueness. `operator_eq_of_eqOn` shows that two Feller semigroups agreeing on a separating
subalgebra agree everywhere, and `limitSemigroup_eq_of_tendsto` is independence of the exhaustion:
two approximating sequences whose operators approach each other on `A` have the same limit.

Scope. The finite-genome models, their transition semigroups lifted to `C(X, ℝ)`, and the light-cone
bound are hypotheses here: `S` is data and `LightConeApproximation` carries the bound of Theorem 8
as a named hypothesis until the locality bounds are available. The space `P({0,1}^V)`, its
compactness and the cylinder sampling algebra are not constructed in this module; the operator
statements are proved for an arbitrary compact space and separating subalgebra. The sampling duality
of Theorem 6 and the circuit bounds (8.2) and (9.1) are not restated.

## Empirical status

None. The bodies here are functional analysis: limits of contractions on a Banach space of
continuous functions, and density of a subalgebra, so no measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Pangenome.AncestralLocality.InfiniteGenomeLimit

open Filter Topology
open scoped NNReal

noncomputable section

/-! ## Feller semigroups and the uniform approximation bound -/

/-- **A Feller semigroup on `C(X, ℝ)`.** A family of bounded operators indexed by time, each a
positive sup-norm contraction fixing the constant one, with the identity at time zero, the
semigroup law, and strong continuity at time zero.
Assumes: nothing beyond the listed fields; `FellerSemigroup.identity` is a witness. -/
structure FellerSemigroup (X : Type*) [TopologicalSpace X] [CompactSpace X] where
  /-- The transition operator at time `t`. -/
  operator : ℝ≥0 → C(X, ℝ) →L[ℝ] C(X, ℝ)
  /-- Every operator is a sup-norm contraction. -/
  norm_le : ∀ t g, ‖operator t g‖ ≤ ‖g‖
  /-- Every operator fixes the constant one. -/
  map_one : ∀ t, operator t 1 = 1
  /-- Every operator is positive. -/
  nonneg : ∀ t g, 0 ≤ g → 0 ≤ operator t g
  /-- At time zero the operator is the identity. -/
  operator_zero : operator 0 = ContinuousLinearMap.id ℝ C(X, ℝ)
  /-- The semigroup law. -/
  operator_add : ∀ s t, operator (s + t) = (operator s).comp (operator t)
  /-- Strong continuity at time zero. -/
  tendsto_operator_zero : ∀ g, Tendsto (fun t ↦ operator t g) (𝓝 0) (𝓝 g)

/-- The identity semigroup is a Feller semigroup on every compact space. -/
def FellerSemigroup.identity (X : Type*) [TopologicalSpace X] [CompactSpace X] :
    FellerSemigroup X where
  operator _ := ContinuousLinearMap.id ℝ C(X, ℝ)
  norm_le _ _ := le_rfl
  map_one _ := rfl
  nonneg _ _ hg := hg
  operator_zero := rfl
  operator_add _ _ := (ContinuousLinearMap.id_comp _).symm
  tendsto_operator_zero _ := tendsto_const_nhds

/-- **The uniform approximation bound of Theorem 9.** The Feller semigroups `S m` along an
exhaustion are within `2 ‖f‖ · escape f T m` of every later member on each observable `f` of the
subalgebra `A`, at every time up to the horizon `T`, and the escape bound vanishes along the
exhaustion. In the note the escape bound is the light-cone probability `Pr(E_{ℓ,T})` of Theorem 8.
Assumes: the listed fields; `LightConeApproximation.constant` is a witness. -/
structure LightConeApproximation {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (S : ℕ → FellerSemigroup X) (A : Subalgebra ℝ C(X, ℝ)) where
  /-- The escape bound of an observable at a horizon and an exhaustion index. -/
  escape : C(X, ℝ) → ℝ≥0 → ℕ → ℝ
  /-- The escape bound vanishes along the exhaustion. -/
  escape_tendsto : ∀ f ∈ A, ∀ T, Tendsto (escape f T) atTop (𝓝 0)
  /-- Later members stay within `2 ‖f‖` times the escape bound on the subalgebra. -/
  norm_sub_le : ∀ f ∈ A, ∀ T t, t ≤ T → ∀ m m', m ≤ m' →
    ‖(S m).operator t f - (S m').operator t f‖ ≤ 2 * ‖f‖ * escape f T m

/-- The constant sequence of identity semigroups satisfies the bound with no escape. -/
def LightConeApproximation.constant (X : Type*) [TopologicalSpace X] [CompactSpace X] :
    LightConeApproximation (fun _ ↦ FellerSemigroup.identity X) (⊤ : Subalgebra ℝ C(X, ℝ)) where
  escape _ _ _ := 0
  escape_tendsto _ _ _ := tendsto_const_nhds
  norm_sub_le _ _ _ _ _ _ _ _ := by simp

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]

/-- **A Feller semigroup is strongly continuous at every time.** For `s ≤ t` the output at `t` is
the output at `s` of the output at `t - s`, so the contraction bound reduces the difference to
strong continuity at time zero; the case `t ≤ s` is symmetric. -/
theorem FellerSemigroup.continuous_operator (P : FellerSemigroup X) (g : C(X, ℝ)) :
    Continuous fun t ↦ P.operator t g := by
  have hbound : ∀ s t : ℝ≥0, ‖P.operator t g - P.operator s g‖ ≤
      ‖P.operator (t - s) g - g‖ + ‖P.operator (s - t) g - g‖ := by
    intro s t
    rcases le_total s t with hst | hts
    · have hsplit : P.operator t g = P.operator s (P.operator (t - s) g) := by
        have htime : t = s + (t - s) := (add_tsub_cancel_of_le hst).symm
        calc P.operator t g = P.operator (s + (t - s)) g := by rw [← htime]
          _ = P.operator s (P.operator (t - s) g) := by
            rw [P.operator_add, ContinuousLinearMap.comp_apply]
      rw [hsplit, ← map_sub]
      exact (P.norm_le s _).trans (le_add_of_nonneg_right (norm_nonneg _))
    · have hsplit : P.operator s g = P.operator t (P.operator (s - t) g) := by
        have htime : s = t + (s - t) := (add_tsub_cancel_of_le hts).symm
        calc P.operator s g = P.operator (t + (s - t)) g := by rw [← htime]
          _ = P.operator t (P.operator (s - t) g) := by
            rw [P.operator_add, ContinuousLinearMap.comp_apply]
      rw [hsplit, norm_sub_rev, ← map_sub]
      exact (P.norm_le t _).trans (le_add_of_nonneg_left (norm_nonneg _))
  refine continuous_iff_continuousAt.mpr fun s ↦ ?_
  have hzero : Tendsto (fun d : ℝ≥0 ↦ ‖P.operator d g - g‖) (𝓝 0) (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.mp (P.tendsto_operator_zero g)
  have hright : Tendsto (fun t : ℝ≥0 ↦ t - s) (𝓝 s) (𝓝 0) :=
    (continuous_id.sub continuous_const).tendsto' s 0 (tsub_self s)
  have hleft : Tendsto (fun t : ℝ≥0 ↦ s - t) (𝓝 s) (𝓝 0) :=
    (continuous_const.sub continuous_id).tendsto' s 0 (tsub_self s)
  have hsum : Tendsto (fun t : ℝ≥0 ↦ ‖P.operator (t - s) g - g‖ + ‖P.operator (s - t) g - g‖)
      (𝓝 s) (𝓝 0) := by
    simpa using (hzero.comp hright).add (hzero.comp hleft)
  exact tendsto_iff_norm_sub_tendsto_zero.mpr
    (squeeze_zero (fun _ ↦ norm_nonneg _) (fun t ↦ hbound s t) hsum)

/-- Stone–Weierstrass: a point-separating subalgebra of `C(X, ℝ)` is dense. -/
theorem dense_subalgebra_of_separatesPoints (A : Subalgebra ℝ C(X, ℝ))
    (hA : A.SeparatesPoints) : Dense (A : Set C(X, ℝ)) := by
  rw [dense_iff_closure_eq, ← Subalgebra.topologicalClosure_coe,
    ContinuousMap.subalgebra_topologicalClosure_eq_top_of_separatesPoints A hA, Algebra.coe_top]

/-- Replacing the observable `g` by `f` changes the distance between two contractions' outputs by
at most twice the distance between the observables. -/
theorem norm_operator_sub_le (P Q : FellerSemigroup X) (t : ℝ≥0) (f g : C(X, ℝ)) :
    ‖P.operator t g - Q.operator t g‖ ≤ 2 * ‖g - f‖ + ‖P.operator t f - Q.operator t f‖ := by
  have hsplit : P.operator t g - Q.operator t g =
      P.operator t (g - f) + (P.operator t f - Q.operator t f) - Q.operator t (g - f) := by
    simp only [map_sub]
    abel
  rw [hsplit]
  refine (norm_sub_le _ _).trans ?_
  refine (add_le_add_right (norm_add_le _ _) _).trans ?_
  linarith [P.norm_le t (g - f), Q.norm_le t (g - f)]

section Limit

variable {S : ℕ → FellerSemigroup X} {A : Subalgebra ℝ C(X, ℝ)}

/-- On an observable of the subalgebra the escape term eventually falls below any positive
tolerance. -/
theorem eventually_escape_lt (approx : LightConeApproximation S A) {f : C(X, ℝ)} (hf : f ∈ A)
    (T : ℝ≥0) {δ : ℝ} (hδ : 0 < δ) : ∀ᶠ m in atTop, 2 * ‖f‖ * approx.escape f T m < δ := by
  have hlimit := (approx.escape_tendsto f hf T).const_mul (2 * ‖f‖)
  rw [mul_zero] at hlimit
  exact hlimit.eventually (gt_mem_nhds hδ)

/-- **The finite-genome operators converge on every continuous observable.** At each time the
sequence of outputs is Cauchy: approximate the observable within the subalgebra, where the escape
bound controls the sequence, and pay twice the approximation error. -/
theorem cauchySeq_operator (hA : A.SeparatesPoints) (approx : LightConeApproximation S A)
    (t : ℝ≥0) (g : C(X, ℝ)) : CauchySeq fun m ↦ (S m).operator t g := by
  refine Metric.cauchySeq_iff'.mpr fun ε hε ↦ ?_
  obtain ⟨f, hball, hf⟩ :=
    Metric.dense_iff.mp (dense_subalgebra_of_separatesPoints A hA) g (ε / 4) (by positivity)
  have hgf : ‖g - f‖ < ε / 4 := by
    rw [← dist_eq_norm, dist_comm]
    exact hball
  obtain ⟨N, hN⟩ :=
    eventually_atTop.mp (eventually_escape_lt approx hf t (by positivity : 0 < ε / 4))
  refine ⟨N, fun n hn ↦ ?_⟩
  rw [dist_eq_norm]
  have hestimate := norm_operator_sub_le (S n) (S N) t f g
  have hclose := approx.norm_sub_le f hf t t le_rfl N n hn
  rw [norm_sub_rev ((S n).operator t f)] at hestimate
  linarith [hN N le_rfl]

/-- The limiting output at time `t` on the observable `g`. -/
def limitValue (S : ℕ → FellerSemigroup X) (t : ℝ≥0) (g : C(X, ℝ)) : C(X, ℝ) :=
  limUnder atTop fun m ↦ (S m).operator t g

/-- The finite-genome outputs converge to the limiting output. -/
theorem tendsto_limitValue (hA : A.SeparatesPoints) (approx : LightConeApproximation S A)
    (t : ℝ≥0) (g : C(X, ℝ)) :
    Tendsto (fun m ↦ (S m).operator t g) atTop (𝓝 (limitValue S t g)) :=
  (cauchySeq_operator hA approx t g).tendsto_limUnder

/-- The limiting output is linear in the observable. -/
def limitLinear (hA : A.SeparatesPoints) (approx : LightConeApproximation S A) (t : ℝ≥0) :
    C(X, ℝ) →ₗ[ℝ] C(X, ℝ) where
  toFun := limitValue S t
  map_add' g h := tendsto_nhds_unique (tendsto_limitValue hA approx t (g + h)) (by
    simpa only [map_add] using
      (tendsto_limitValue hA approx t g).add (tendsto_limitValue hA approx t h))
  map_smul' c g := tendsto_nhds_unique (tendsto_limitValue hA approx t (c • g)) (by
    simpa only [map_smul, RingHom.id_apply] using (tendsto_limitValue hA approx t g).const_smul c)

/-- The limiting output is a sup-norm contraction of the observable. -/
theorem norm_limitValue_le (hA : A.SeparatesPoints) (approx : LightConeApproximation S A)
    (t : ℝ≥0) (g : C(X, ℝ)) : ‖limitValue S t g‖ ≤ ‖g‖ :=
  le_of_tendsto (tendsto_limitValue hA approx t g).norm
    (Eventually.of_forall fun m ↦ (S m).norm_le t g)

/-- The limiting operator at time `t`, a bounded operator of norm at most one. -/
def limitOperator (hA : A.SeparatesPoints) (approx : LightConeApproximation S A) (t : ℝ≥0) :
    C(X, ℝ) →L[ℝ] C(X, ℝ) :=
  (limitLinear hA approx t).mkContinuous 1 fun g ↦ by
    rw [one_mul]
    exact norm_limitValue_le hA approx t g

/-- The limiting output of a nonnegative observable is nonnegative. -/
theorem limitValue_nonneg (hA : A.SeparatesPoints) (approx : LightConeApproximation S A)
    (t : ℝ≥0) {g : C(X, ℝ)} (hg : 0 ≤ g) : 0 ≤ limitValue S t g := by
  refine ContinuousMap.le_def.mpr fun x ↦ ?_
  have hpoint : Tendsto (fun m ↦ (S m).operator t g x) atTop (𝓝 (limitValue S t g x)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun _ ↦ norm_nonneg _) (fun m ↦ ?_)
      (tendsto_iff_norm_sub_tendsto_zero.mp (tendsto_limitValue hA approx t g))
    exact ContinuousMap.norm_coe_le_norm ((S m).operator t g - limitValue S t g) x
  exact ge_of_tendsto hpoint
    (Eventually.of_forall fun m ↦ ContinuousMap.le_def.mp ((S m).nonneg t g hg) x)

/-- The limiting operators fix the constant one. -/
theorem limitValue_one (hA : A.SeparatesPoints) (approx : LightConeApproximation S A)
    (t : ℝ≥0) : limitValue S t 1 = 1 :=
  tendsto_nhds_unique (tendsto_limitValue hA approx t 1)
    (tendsto_const_nhds.congr fun m ↦ ((S m).map_one t).symm)

/-- At time zero the limiting operator is the identity. -/
theorem limitValue_zero (hA : A.SeparatesPoints) (approx : LightConeApproximation S A)
    (g : C(X, ℝ)) : limitValue S 0 g = g :=
  tendsto_nhds_unique (tendsto_limitValue hA approx 0 g)
    (tendsto_const_nhds.congr fun m ↦ by simp [(S m).operator_zero])

/-- **The semigroup law passes to the limit.** The finite-genome outputs at time `s + t` are the
outputs at `s` of the outputs at `t`, and the contraction bound lets both limits be taken at
once. -/
theorem limitValue_add (hA : A.SeparatesPoints) (approx : LightConeApproximation S A)
    (s t : ℝ≥0) (g : C(X, ℝ)) : limitValue S (s + t) g = limitValue S s (limitValue S t g) := by
  refine tendsto_nhds_unique (tendsto_limitValue hA approx (s + t) g) ?_
  have hcompose : ∀ m, (S m).operator (s + t) g = (S m).operator s ((S m).operator t g) :=
    fun m ↦ by rw [(S m).operator_add, ContinuousLinearMap.comp_apply]
  have hinner := tendsto_iff_norm_sub_tendsto_zero.mp (tendsto_limitValue hA approx t g)
  have houter := tendsto_iff_norm_sub_tendsto_zero.mp
    (tendsto_limitValue hA approx s (limitValue S t g))
  have hsum : Tendsto (fun m ↦ ‖(S m).operator t g - limitValue S t g‖ +
      ‖(S m).operator s (limitValue S t g) - limitValue S s (limitValue S t g)‖) atTop (𝓝 0) := by
    simpa using hinner.add houter
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun _ ↦ norm_nonneg _) (fun m ↦ ?_) hsum
  rw [hcompose m]
  calc ‖(S m).operator s ((S m).operator t g) - limitValue S s (limitValue S t g)‖
      = ‖(S m).operator s ((S m).operator t g - limitValue S t g) +
          ((S m).operator s (limitValue S t g) - limitValue S s (limitValue S t g))‖ := by
        rw [map_sub]
        congr 1
        abel
    _ ≤ ‖(S m).operator t g - limitValue S t g‖ +
          ‖(S m).operator s (limitValue S t g) - limitValue S s (limitValue S t g)‖ :=
        (norm_add_le _ _).trans (add_le_add_right ((S m).norm_le s _) _)

/-- **The convergence is uniform in time up to any horizon.** At every time `t ≤ T` the limiting
output is within twice the approximation error plus the escape term of the `m`-th output. -/
theorem norm_limitValue_sub_le (hA : A.SeparatesPoints) (approx : LightConeApproximation S A)
    {T t : ℝ≥0} (ht : t ≤ T) (m : ℕ) {f : C(X, ℝ)} (hf : f ∈ A) (g : C(X, ℝ)) :
    ‖limitValue S t g - (S m).operator t g‖ ≤ 2 * ‖g - f‖ + 2 * ‖f‖ * approx.escape f T m := by
  have hlimit : Tendsto (fun n ↦ ‖(S n).operator t g - (S m).operator t g‖) atTop
      (𝓝 ‖limitValue S t g - (S m).operator t g‖) :=
    ((tendsto_limitValue hA approx t g).sub_const _).norm
  refine le_of_tendsto hlimit (eventually_atTop.mpr ⟨m, fun n hn ↦ ?_⟩)
  have hestimate := norm_operator_sub_le (S n) (S m) t f g
  have hclose := approx.norm_sub_le f hf T t ht m n hn
  rw [norm_sub_rev ((S n).operator t f)] at hestimate
  linarith

/-- **Strong continuity passes to the limit.** Near time zero the limiting output is within the
uniform approximation error of one finite-genome output, which is itself close to the observable
by the strong continuity of that semigroup. -/
theorem tendsto_limitValue_zero (hA : A.SeparatesPoints) (approx : LightConeApproximation S A)
    (g : C(X, ℝ)) : Tendsto (fun t ↦ limitValue S t g) (𝓝 0) (𝓝 g) := by
  refine Metric.tendsto_nhds.mpr fun ε hε ↦ ?_
  obtain ⟨f, hball, hf⟩ :=
    Metric.dense_iff.mp (dense_subalgebra_of_separatesPoints A hA) g (ε / 8) (by positivity)
  have hgf : ‖g - f‖ < ε / 8 := by
    rw [← dist_eq_norm, dist_comm]
    exact hball
  obtain ⟨m, hm⟩ := (eventually_escape_lt approx hf 1 (by positivity : 0 < ε / 4)).exists
  have hnear : ∀ᶠ t in 𝓝 (0 : ℝ≥0), dist ((S m).operator t g) g < ε / 4 :=
    Metric.tendsto_nhds.mp ((S m).tendsto_operator_zero g) (ε / 4) (by positivity)
  filter_upwards [hnear, eventually_lt_nhds (zero_lt_one : (0 : ℝ≥0) < 1)] with t htnear htone
  have hbound := norm_limitValue_sub_le hA approx htone.le m hf g
  rw [dist_eq_norm] at htnear ⊢
  calc ‖limitValue S t g - g‖
      = ‖(limitValue S t g - (S m).operator t g) + ((S m).operator t g - g)‖ := by
        congr 1
        abel
    _ ≤ ‖limitValue S t g - (S m).operator t g‖ + ‖(S m).operator t g - g‖ := norm_add_le _ _
    _ < ε := by linarith

/-- **The limiting Feller semigroup.** The uniform limit of the finite-genome semigroups along the
exhaustion is a Feller semigroup on `C(X, ℝ)`. -/
def limitSemigroup (hA : A.SeparatesPoints) (approx : LightConeApproximation S A) :
    FellerSemigroup X where
  operator t := limitOperator hA approx t
  norm_le t g := norm_limitValue_le hA approx t g
  map_one t := limitValue_one hA approx t
  nonneg t _ hg := limitValue_nonneg hA approx t hg
  operator_zero := ContinuousLinearMap.ext fun g ↦ limitValue_zero hA approx g
  operator_add s t := ContinuousLinearMap.ext fun g ↦ limitValue_add hA approx s t g
  tendsto_operator_zero g := tendsto_limitValue_zero hA approx g

/-- The finite-genome operators converge to the limiting semigroup on every observable. -/
theorem tendsto_limitSemigroup (hA : A.SeparatesPoints) (approx : LightConeApproximation S A)
    (t : ℝ≥0) (g : C(X, ℝ)) :
    Tendsto (fun m ↦ (S m).operator t g) atTop (𝓝 ((limitSemigroup hA approx).operator t g)) :=
  tendsto_limitValue hA approx t g

end Limit

/-! ## Uniqueness through the separating algebra -/

/-- **Two Feller semigroups agreeing on a separating subalgebra are equal.** The operators are
continuous and the subalgebra is dense. -/
theorem operator_eq_of_eqOn (P Q : FellerSemigroup X) {A : Subalgebra ℝ C(X, ℝ)}
    (hA : A.SeparatesPoints) (h : ∀ t, ∀ f ∈ A, P.operator t f = Q.operator t f) :
    P.operator = Q.operator := by
  funext t
  exact ContinuousLinearMap.coeFn_injective ((P.operator t).continuous.ext_on
    (dense_subalgebra_of_separatesPoints A hA) (Q.operator t).continuous fun f hf ↦ h t f hf)

/-- **The limit does not depend on the exhaustion.** Two approximating sequences whose operators
approach each other on the separating subalgebra have the same limiting semigroup. -/
theorem limitSemigroup_eq_of_tendsto {S S' : ℕ → FellerSemigroup X} {A : Subalgebra ℝ C(X, ℝ)}
    (hA : A.SeparatesPoints) (approx : LightConeApproximation S A)
    (approx' : LightConeApproximation S' A)
    (hclose : ∀ t, ∀ f ∈ A,
      Tendsto (fun m ↦ (S m).operator t f - (S' m).operator t f) atTop (𝓝 0)) :
    (limitSemigroup hA approx).operator = (limitSemigroup hA approx').operator :=
  operator_eq_of_eqOn _ _ hA fun t f hf ↦ sub_eq_zero.mp (tendsto_nhds_unique
    ((tendsto_limitSemigroup hA approx t f).sub (tendsto_limitSemigroup hA approx' t f))
    (hclose t f hf))

end

end Descent.Pangenome.AncestralLocality.InfiniteGenomeLimit
