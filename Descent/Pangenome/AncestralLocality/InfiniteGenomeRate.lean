/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.AncestralLocality.CircuitCoupling
import Descent.Pangenome.AncestralLocality.CylinderWindowProjection
import Descent.Pangenome.AncestralLocality.InfiniteGenomeLimit

assert_below Descent.PopGen Descent.Spectral Descent.Blindness Descent.Conditionals
assert_below Descent.Portability Descent.Decision Descent.Program

/-!
# An explicit rate for the infinite-genome limit

`ANCESTRAL_LOCALITY.md` §10, Theorem 9, with a rate. `InfiniteGenomeLimit` builds the
infinite-genome semigroup `T_t` as the limit of finite-genome semigroups `T^m_t` along an
exhaustion, and `LightConeApproximationBound.norm_operator_sub_le_lightConeEscape` bounds the
distance between members of the exhaustion by the escape bound (9.1), for marginal laws that obey
Dynkin's formula. This module gives the rate of convergence to the limit, in the form (9.2) and
with the escape bound taken from the laws of the support circuit truncated after `M` decisions,
where Dynkin's formula is proved (`SupportChainDynkin`, the bounds used in `CircuitCoupling`).

**Statement.** Let `r` be nonnegative checking rates on a finite genome `V` with row sums at most
`D ≥ 0`, let `c ≥ 0` be the coalescence rate, and let `T^m = S m` be Feller semigroups on a compact
space `X` along an exhaustion with radii `ℓ_m`. Fix an observable `f`, read through `n` sampled
arguments on an observation set `A`, a horizon `T` with `2 D T ≤ ℓ_m` and `1 ≤ ℓ_m` for every `m`,
and a truncation `M` of the backward circuit. Suppose that
* (duality) at every index `m`, genome law `p` and time `t`, `(T^m_t f)(p)` is the expectation of
  an evaluation `F_m(p, t, ·)` of the circuit state under the truncated chain law
  `supportChainLaw r c A n M t`, and every evaluation is bounded by `‖f‖`;
* (agreement until escape) the evaluations of `T^m` and of every later `T^{m'}` coincide on every
  circuit state that holds no coordinate at directed distance `ℓ_m` or more from `A`.
Then for every `m` and `t ≤ T`
`‖T^m_t f - T_t f‖ ≤ 2 ‖f‖ · min {1, n |A| e^{D T} (2 e D T / ℓ_m)^{ℓ_m}}`
(`norm_operator_sub_limitValue_le_radiusEscape`). On the genome laws `P({0,1}^V)` the observables
are the cylinder sampling polynomials of `n` genomes on a window `A`, the pullbacks of window
polynomials (`CylinderWindowProjection.windowPullback_windowPolynomial`), and the limit is
`infiniteGenomeSemigroup` (`norm_operator_sub_infiniteGenomeSemigroup_le`,
`norm_windowPullback_operator_sub_infiniteGenomeSemigroup_le`).

**Proof.** `radiusEscape N D T ℓ` is the bound (9.2), nonnegative and increasing in the horizon
(`radiusEscape_nonneg`, `radiusEscape_mono_time`). The truncated chain escapes the ball of radius
`ℓ` with probability at most `radiusEscape (n |A|) D T ℓ` at every time up to `T`
(`sum_supportChainLaw_escape_le_radiusEscape`), through `sum_supportChainLaw_escape_le_radius`
when `D t ≠ 0` and `sum_supportChainLaw_escape_eq_zero` when `D t = 0`. Two bounded evaluations
agreeing off the escape set differ in expectation by at most twice the bound times the escape
probability (`abs_sum_supportChainLaw_sub_le`), so later members of the exhaustion stay within the
rate (`norm_operator_sub_le_radiusEscape`), and a bound on the tail of a convergent sequence holds
at its limit (`norm_sub_limit_le_of_tail`).

**Choosing the window.** When `ℓ ≥ 2 e² D T` the bound decays like `N e^{D T} e^{-ℓ}`
(`radiusEscape_le_exp_neg`), so `ℓ ≥ max {2 e² D T, D T + log (N / ε)}` gives error at most
`2 ‖f‖ ε` (`radiusEscape_le_of_radius`).

**Named hypotheses.** The sampling duality of Theorem 6 through the truncated chain and agreement
until escape are hypotheses, as in `LightConeApproximationBound`; the escape probability itself is
proved. Scope: the circuit is truncated after `M` decisions, as in `SupportChainDynkin`, and the
rate table is finite; the `M → ∞` limit of the circuit is not proved.

## Empirical status

None. The bodies here are finite sums, sup-norm bounds and limits: the semigroups, the evaluations
and the rate table are supplied, and no measurement enters any statement.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Pangenome.AncestralLocality.InfiniteGenomeRate

open Finset MeasureTheory Filter Topology InfiniteGenomeLimit CylinderSamplingAlgebra
  CylinderSamplingPolynomials CylinderWindowProjection

open scoped NNReal

noncomputable section

/-! ### The escape bound at the radius of (9.2) -/

/-- **The escape bound (9.2)** for `N` sampled arguments on the observation set, rate bound `D`,
horizon `T` and radius `ℓ`: `min {1, N e^{D T} (2 e D T / ℓ)^ℓ}`. -/
def radiusEscape (N D T : ℝ) (ℓ : ℕ) : ℝ :=
  min 1 (N * Real.exp (D * T) * (2 * Real.exp 1 * D * T / ℓ) ^ ℓ)

/-- The escape bound (9.2) is nonnegative. Assumes: `N ≥ 0`, `D ≥ 0` and `T ≥ 0`. -/
theorem radiusEscape_nonneg {N D T : ℝ} (hN : 0 ≤ N) (hD : 0 ≤ D) (hT : 0 ≤ T) (ℓ : ℕ) :
    0 ≤ radiusEscape N D T ℓ :=
  le_min zero_le_one (mul_nonneg (mul_nonneg hN (Real.exp_pos _).le)
    (pow_nonneg (div_nonneg
      (mul_nonneg (mul_nonneg (mul_nonneg zero_le_two (Real.exp_pos 1).le) hD) hT)
      (Nat.cast_nonneg ℓ)) ℓ))

/-- The escape bound (9.2) grows with the horizon. Assumes: `N ≥ 0`, `D ≥ 0` and `0 ≤ t ≤ T`. -/
theorem radiusEscape_mono_time {N D t T : ℝ} (hN : 0 ≤ N) (hD : 0 ≤ D) (ht : 0 ≤ t)
    (htT : t ≤ T) (ℓ : ℕ) : radiusEscape N D t ℓ ≤ radiusEscape N D T ℓ := by
  have hcoefficient : 0 ≤ 2 * Real.exp 1 * D :=
    mul_nonneg (mul_nonneg zero_le_two (Real.exp_pos 1).le) hD
  have hexp : Real.exp (D * t) ≤ Real.exp (D * T) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left htT hD)
  have hbase : 0 ≤ 2 * Real.exp 1 * D * t / ℓ :=
    div_nonneg (mul_nonneg hcoefficient ht) (Nat.cast_nonneg ℓ)
  have hbaseLe : 2 * Real.exp 1 * D * t / ℓ ≤ 2 * Real.exp 1 * D * T / ℓ := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left htT hcoefficient)
      (inv_nonneg.mpr (Nat.cast_nonneg ℓ))
  have hpow : (2 * Real.exp 1 * D * t / ℓ) ^ ℓ ≤ (2 * Real.exp 1 * D * T / ℓ) ^ ℓ :=
    pow_le_pow_left₀ hbase hbaseLe ℓ
  exact min_le_min le_rfl (mul_le_mul (mul_le_mul_of_nonneg_left hexp hN) hpow
    (pow_nonneg hbase ℓ) (mul_nonneg hN (Real.exp_pos _).le))

/-- **Choosing the radius.** When `ℓ ≥ 2 e² D T` the escape bound (9.2) is at most
`N e^{D T} e^{-ℓ}`. Assumes: `N ≥ 0`, `D ≥ 0`, `T ≥ 0`, `ℓ ≥ 1` and `2 e² D T ≤ ℓ`. -/
theorem radiusEscape_le_exp_neg {N D T : ℝ} (hN : 0 ≤ N) (hD : 0 ≤ D) (hT : 0 ≤ T) {ℓ : ℕ}
    (hℓ : 1 ≤ ℓ) (hradius : 2 * Real.exp 1 ^ 2 * D * T ≤ ℓ) :
    radiusEscape N D T ℓ ≤ N * Real.exp (D * T) * Real.exp (-(ℓ : ℝ)) := by
  have hℓpositive : (0 : ℝ) < ℓ := Nat.cast_pos.mpr (by omega)
  have he : 0 < Real.exp 1 := Real.exp_pos 1
  have hbase : 0 ≤ 2 * Real.exp 1 * D * T / ℓ :=
    div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg zero_le_two he.le) hD) hT) hℓpositive.le
  have hbaseLe : 2 * Real.exp 1 * D * T / ℓ ≤ Real.exp (-1) := by
    rw [div_le_iff₀ hℓpositive, Real.exp_neg]
    have hsquare : 2 * Real.exp 1 * D * T * Real.exp 1 = 2 * Real.exp 1 ^ 2 * D * T := by ring
    have hkey : 2 * Real.exp 1 * D * T * Real.exp 1 ≤ ℓ := by linarith
    calc 2 * Real.exp 1 * D * T
        = 2 * Real.exp 1 * D * T * Real.exp 1 * (Real.exp 1)⁻¹ :=
          (mul_inv_cancel_right₀ he.ne' _).symm
      _ ≤ ℓ * (Real.exp 1)⁻¹ := mul_le_mul_of_nonneg_right hkey (inv_nonneg.mpr he.le)
      _ = (Real.exp 1)⁻¹ * ℓ := mul_comm _ _
  have hpow : (2 * Real.exp 1 * D * T / ℓ) ^ ℓ ≤ Real.exp (-(ℓ : ℝ)) :=
    calc (2 * Real.exp 1 * D * T / ℓ) ^ ℓ ≤ Real.exp (-1) ^ ℓ := pow_le_pow_left₀ hbase hbaseLe ℓ
      _ = Real.exp (-(ℓ : ℝ)) := by rw [← Real.exp_nat_mul, mul_neg_one]
  exact (min_le_right _ _).trans
    (mul_le_mul_of_nonneg_left hpow (mul_nonneg hN (Real.exp_pos _).le))

/-- **A window size for a target accuracy.** If `ℓ ≥ 2 e² D T` and `ℓ ≥ D T + log (N / ε)`, the
escape bound (9.2) is at most `ε`. Assumes: `N > 0`, `D ≥ 0`, `T ≥ 0`, `ε > 0` and `ℓ ≥ 1`. -/
theorem radiusEscape_le_of_radius {N D T ε : ℝ} (hN : 0 < N) (hD : 0 ≤ D) (hT : 0 ≤ T)
    (hε : 0 < ε) {ℓ : ℕ} (hℓ : 1 ≤ ℓ) (hradius : 2 * Real.exp 1 ^ 2 * D * T ≤ ℓ)
    (haccuracy : D * T + Real.log (N / ε) ≤ ℓ) : radiusEscape N D T ℓ ≤ ε := by
  refine (radiusEscape_le_exp_neg hN.le hD hT hℓ hradius).trans ?_
  have hexponent : Real.log N + D * T - ℓ ≤ Real.log ε := by
    rw [Real.log_div hN.ne' hε.ne'] at haccuracy
    linarith
  calc N * Real.exp (D * T) * Real.exp (-(ℓ : ℝ)) = Real.exp (Real.log N + D * T - ℓ) := by
        rw [Real.exp_sub, Real.exp_add, Real.exp_log hN, Real.exp_neg]
        ring
    _ ≤ Real.exp (Real.log ε) := Real.exp_le_exp.mpr hexponent
    _ = ε := Real.exp_log hε

/-! ### The truncated circuit at the radius of (9.2) -/

section Circuit

variable {V : Type*} [DecidableEq V] [Fintype V]

open scoped Classical in
/-- **The escape probability of the truncated circuit at every time up to the horizon.** Assumes:
nonnegative rates with row sums at most `D ≥ 0`, `c ≥ 0`, `0 ≤ t ≤ T`, and a radius `ℓ ≥ 1` with
`2 D T ≤ ℓ`. The circuit started from `n` arguments carrying `A` holds a coordinate at directed
distance at least `ℓ` at time `t` with probability at most `radiusEscape (n |A|) D T ℓ`. -/
theorem sum_supportChainLaw_escape_le_radiusEscape {r : V → V → ℝ} {c D t T : ℝ}
    (hr : ∀ i j, 0 ≤ r i j) (hD : ∀ i, ∑ j, r i j ≤ D) (hDnonneg : 0 ≤ D) (hc : 0 ≤ c)
    (A : Finset V) (n M ℓ : ℕ) (ht : 0 ≤ t) (htT : t ≤ T) (hℓ : 1 ≤ ℓ)
    (hradius : 2 * D * T ≤ ℓ) :
    ∑ y, (if univ.val.map y.1 ∈ escapeSet r A ℓ then supportChainLaw r c A n M t y else 0) ≤
      radiusEscape (n * A.card) D T ℓ := by
  have hN : (0 : ℝ) ≤ n * A.card := by positivity
  refine le_trans ?_ (radiusEscape_mono_time hN hDnonneg ht htT ℓ)
  by_cases hDt : D * t = 0
  · rw [sum_supportChainLaw_escape_eq_zero hr hD hc A n M ℓ ht hDt hℓ]
    exact radiusEscape_nonneg hN hDnonneg ht ℓ
  · have hDtPositive : 0 < D * t := lt_of_le_of_ne (mul_nonneg hDnonneg ht) (Ne.symm hDt)
    have hradiusAt : 1 ≤ (ℓ : ℝ) / (2 * D * t) := by
      rw [le_div_iff₀ (by linarith), one_mul]
      have hDtT : 2 * D * t ≤ 2 * D * T := by nlinarith
      linarith
    exact sum_supportChainLaw_escape_le_radius hr hD hc A n M ℓ ht hDt hradiusAt

open scoped Classical in
/-- **The coupling bound on the circuit's own law.** Assumes: nonnegative rates, `c ≥ 0`, `t ≥ 0`,
and two evaluations of the circuit state bounded by `B` that agree on every state that has not
escaped the ball of radius `ℓ`. Their expectations differ by at most `2 B` times the escape
probability. -/
theorem abs_sum_supportChainLaw_sub_le {r : V → V → ℝ} {c t B : ℝ} (hr : ∀ i j, 0 ≤ r i j)
    (hc : 0 ≤ c) (A : Finset V) (n M ℓ : ℕ) (ht : 0 ≤ t) (F G : SupportChainState V n M → ℝ)
    (hF : ∀ y, |F y| ≤ B) (hG : ∀ y, |G y| ≤ B)
    (hagree : ∀ y, univ.val.map y.1 ∉ escapeSet r A ℓ → F y = G y) :
    |∑ y, supportChainLaw r c A n M t y * F y - ∑ y, supportChainLaw r c A n M t y * G y| ≤
      2 * B *
        ∑ y, (if univ.val.map y.1 ∈ escapeSet r A ℓ then supportChainLaw r c A n M t y else 0) := by
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun y _ ↦ ?_)
  have hnonneg := supportChainLaw_nonneg hr hc A n M ht y
  rw [← mul_sub, abs_mul, abs_of_nonneg hnonneg]
  split_ifs with hescape
  · have hdifference : |F y - G y| ≤ 2 * B := by
      obtain ⟨hFlow, hFhigh⟩ := abs_le.mp (hF y)
      obtain ⟨hGlow, hGhigh⟩ := abs_le.mp (hG y)
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    nlinarith
  · simp [hagree y hescape]

open scoped Classical in
/-- **Later members of the exhaustion at the rate (9.2).** Assumes: nonnegative rates with row
sums at most `D ≥ 0`, `c ≥ 0`; the sampling duality of the observable `f` through the truncated
circuit law at every index, genome law and time, with evaluations bounded by `‖f‖`; agreement of
the evaluations of `S m` and every later `S m'` on states that have not escaped the ball of radius
`radius m`; and radii with `1 ≤ radius m` and `2 D T ≤ radius m`. Then for `t ≤ T` and `m ≤ m'`
the operators differ on `f` by at most `2 ‖f‖ · radiusEscape (n |A|) D T (radius m)`. -/
theorem norm_operator_sub_le_radiusEscape {X : Type*} [TopologicalSpace X] [CompactSpace X]
    {S : ℕ → FellerSemigroup X} {r : V → V → ℝ} {c D : ℝ} (hr : ∀ i j, 0 ≤ r i j)
    (hD : ∀ i, ∑ j, r i j ≤ D) (hDnonneg : 0 ≤ D) (hc : 0 ≤ c) (f : C(X, ℝ)) (A : Finset V)
    (n M : ℕ) (radius : ℕ → ℕ) (evaluation : ℕ → X → ℝ≥0 → SupportChainState V n M → ℝ)
    (hbounded : ∀ m p t y, |evaluation m p t y| ≤ ‖f‖)
    (hduality : ∀ m p (t : ℝ≥0),
      (S m).operator t f p = ∑ y, supportChainLaw r c A n M t y * evaluation m p t y)
    (hagree : ∀ m m', m ≤ m' → ∀ p t y,
      univ.val.map y.1 ∉ escapeSet r A (radius m) → evaluation m p t y = evaluation m' p t y)
    {T : ℝ≥0} (hradius : ∀ m, 2 * D * T ≤ radius m) (hradiusPositive : ∀ m, 1 ≤ radius m)
    {t : ℝ≥0} (htT : t ≤ T) {m m' : ℕ} (hmm' : m ≤ m') :
    ‖(S m).operator t f - (S m').operator t f‖ ≤
      2 * ‖f‖ * radiusEscape (n * A.card) D T (radius m) := by
  have hN : (0 : ℝ) ≤ n * A.card := by positivity
  have hbound : 0 ≤ 2 * ‖f‖ * radiusEscape (n * A.card) D T (radius m) :=
    mul_nonneg (by positivity) (radiusEscape_nonneg hN hDnonneg T.coe_nonneg _)
  rw [ContinuousMap.norm_le _ hbound]
  intro p
  rw [ContinuousMap.sub_apply, hduality m p t, hduality m' p t, Real.norm_eq_abs]
  calc |∑ y, supportChainLaw r c A n M t y * evaluation m p t y -
        ∑ y, supportChainLaw r c A n M t y * evaluation m' p t y|
      ≤ 2 * ‖f‖ * ∑ y, (if univ.val.map y.1 ∈ escapeSet r A (radius m) then
          supportChainLaw r c A n M t y else 0) :=
        abs_sum_supportChainLaw_sub_le hr hc A n M (radius m) t.coe_nonneg _ _ (hbounded m p t)
          (hbounded m' p t) (hagree m m' hmm' p t)
    _ ≤ 2 * ‖f‖ * radiusEscape (n * A.card) D T (radius m) :=
        mul_le_mul_of_nonneg_left
          (sum_supportChainLaw_escape_le_radiusEscape hr hD hDnonneg hc A n M (radius m)
            t.coe_nonneg (NNReal.coe_le_coe.mpr htT) (hradiusPositive m) (hradius m))
          (by positivity)

end Circuit

/-! ### The rate at the limit -/

/-- A norm bound on the tail of a convergent sequence holds at its limit. -/
theorem norm_sub_limit_le_of_tail {E : Type*} [NormedAddCommGroup E] {u : ℕ → E} {x : E}
    (hu : Tendsto u atTop (𝓝 x)) {m : ℕ} {B : ℝ} (htail : ∀ m', m ≤ m' → ‖u m - u m'‖ ≤ B) :
    ‖u m - x‖ ≤ B :=
  le_of_tendsto (tendsto_const_nhds.sub hu).norm (eventually_atTop.mpr ⟨m, htail⟩)

open scoped Classical in
/-- **Theorem 9 with an explicit rate.** Assumes: a point-separating subalgebra with a light-cone
approximation for the exhaustion, and the hypotheses of `norm_operator_sub_le_radiusEscape`. Then
for every `m` and `t ≤ T` the finite-genome operator is within
`2 ‖f‖ · min {1, n |A| e^{D T} (2 e D T / ℓ_m)^{ℓ_m}}` of the limit on `f`. -/
theorem norm_operator_sub_limitValue_le_radiusEscape {X V : Type*} [TopologicalSpace X]
    [CompactSpace X] [DecidableEq V] [Fintype V] {S : ℕ → FellerSemigroup X}
    {observables : Subalgebra ℝ C(X, ℝ)} (hseparates : observables.SeparatesPoints)
    (approx : LightConeApproximation S observables) {r : V → V → ℝ} {c D : ℝ}
    (hr : ∀ i j, 0 ≤ r i j) (hD : ∀ i, ∑ j, r i j ≤ D) (hDnonneg : 0 ≤ D) (hc : 0 ≤ c)
    (f : C(X, ℝ)) (A : Finset V) (n M : ℕ) (radius : ℕ → ℕ)
    (evaluation : ℕ → X → ℝ≥0 → SupportChainState V n M → ℝ)
    (hbounded : ∀ m p t y, |evaluation m p t y| ≤ ‖f‖)
    (hduality : ∀ m p (t : ℝ≥0),
      (S m).operator t f p = ∑ y, supportChainLaw r c A n M t y * evaluation m p t y)
    (hagree : ∀ m m', m ≤ m' → ∀ p t y,
      univ.val.map y.1 ∉ escapeSet r A (radius m) → evaluation m p t y = evaluation m' p t y)
    {T : ℝ≥0} (hradius : ∀ m, 2 * D * T ≤ radius m) (hradiusPositive : ∀ m, 1 ≤ radius m)
    {t : ℝ≥0} (htT : t ≤ T) (m : ℕ) :
    ‖(S m).operator t f - limitValue S t f‖ ≤
      2 * ‖f‖ * radiusEscape (n * A.card) D T (radius m) :=
  norm_sub_limit_le_of_tail (tendsto_limitValue hseparates approx t f) fun _ hmm' ↦
    norm_operator_sub_le_radiusEscape hr hD hDnonneg hc f A n M radius evaluation hbounded
      hduality hagree hradius hradiusPositive htT hmm'

/-! ### The genome laws -/

section GenomeLaws

variable {V : Type*} [DecidableEq V] [Fintype V]

open scoped Classical in
/-- **Theorem 9 on the genome laws, with a rate.** For the cylinder sampling polynomial of a
readout of `n` genomes on a window `A`, under the hypotheses of
`norm_operator_sub_le_radiusEscape`, the finite-genome operators converge to the infinite-genome
semigroup at the rate `2 ‖f‖ · min {1, n |A| e^{D T} (2 e D T / ℓ_m)^{ℓ_m}}` for `t ≤ T`. -/
theorem norm_operator_sub_infiniteGenomeSemigroup_le
    {S : ℕ → FellerSemigroup (ProbabilityMeasure (V → Bool))}
    (approx : LightConeApproximation S (samplingAlgebra V)) {r : V → V → ℝ} {c D : ℝ}
    (hr : ∀ i j, 0 ≤ r i j) (hD : ∀ i, ∑ j, r i j ≤ D) (hDnonneg : 0 ≤ D) (hc : 0 ≤ c)
    (A : Finset V) (n M : ℕ) (readout : (Fin n → A → Bool) → ℝ) (radius : ℕ → ℕ)
    (evaluation : ℕ → ProbabilityMeasure (V → Bool) → ℝ≥0 → SupportChainState V n M → ℝ)
    (hbounded : ∀ m p t y, |evaluation m p t y| ≤ ‖samplingPolynomial n A readout‖)
    (hduality : ∀ m p (t : ℝ≥0), (S m).operator t (samplingPolynomial n A readout) p =
      ∑ y, supportChainLaw r c A n M t y * evaluation m p t y)
    (hagree : ∀ m m', m ≤ m' → ∀ p t y,
      univ.val.map y.1 ∉ escapeSet r A (radius m) → evaluation m p t y = evaluation m' p t y)
    {T : ℝ≥0} (hradius : ∀ m, 2 * D * T ≤ radius m) (hradiusPositive : ∀ m, 1 ≤ radius m)
    {t : ℝ≥0} (htT : t ≤ T) (m : ℕ) :
    ‖(S m).operator t (samplingPolynomial n A readout) -
        (infiniteGenomeSemigroup S approx).operator t (samplingPolynomial n A readout)‖ ≤
      2 * ‖samplingPolynomial n A readout‖ * radiusEscape (n * A.card) D T (radius m) := by
  have hvalue : (infiniteGenomeSemigroup S approx).operator t (samplingPolynomial n A readout) =
      limitValue S t (samplingPolynomial n A readout) :=
    rfl
  rw [hvalue]
  exact norm_operator_sub_limitValue_le_radiusEscape samplingAlgebra_separatesPoints approx hr hD
    hDnonneg hc _ A n M radius evaluation hbounded hduality hagree hradius hradiusPositive htT m

open scoped Classical in
/-- **The rate through the window projection.** The cylinder sampling polynomial of `n` genomes
on a window `A` is the pullback of the window polynomial along the window law, so the same rate
holds for the pulled-back window polynomial. -/
theorem norm_windowPullback_operator_sub_infiniteGenomeSemigroup_le
    {S : ℕ → FellerSemigroup (ProbabilityMeasure (V → Bool))}
    (approx : LightConeApproximation S (samplingAlgebra V)) {r : V → V → ℝ} {c D : ℝ}
    (hr : ∀ i j, 0 ≤ r i j) (hD : ∀ i, ∑ j, r i j ≤ D) (hDnonneg : 0 ≤ D) (hc : 0 ≤ c)
    (A : Finset V) (n M : ℕ) (readout : (Fin n → A → Bool) → ℝ) (radius : ℕ → ℕ)
    (evaluation : ℕ → ProbabilityMeasure (V → Bool) → ℝ≥0 → SupportChainState V n M → ℝ)
    (hbounded : ∀ m p t y, |evaluation m p t y| ≤ ‖samplingPolynomial n A readout‖)
    (hduality : ∀ m p (t : ℝ≥0), (S m).operator t (samplingPolynomial n A readout) p =
      ∑ y, supportChainLaw r c A n M t y * evaluation m p t y)
    (hagree : ∀ m m', m ≤ m' → ∀ p t y,
      univ.val.map y.1 ∉ escapeSet r A (radius m) → evaluation m p t y = evaluation m' p t y)
    {T : ℝ≥0} (hradius : ∀ m, 2 * D * T ≤ radius m) (hradiusPositive : ∀ m, 1 ≤ radius m)
    {t : ℝ≥0} (htT : t ≤ T) (m : ℕ) :
    ‖(S m).operator t (windowPullback A (windowPolynomial A n readout)) -
        (infiniteGenomeSemigroup S approx).operator t
          (windowPullback A (windowPolynomial A n readout))‖ ≤
      2 * ‖windowPullback A (windowPolynomial A n readout)‖ *
        radiusEscape (n * A.card) D T (radius m) := by
  rw [windowPullback_windowPolynomial]
  exact norm_operator_sub_infiniteGenomeSemigroup_le approx hr hD hDnonneg hc A n M readout radius
    evaluation hbounded hduality hagree hradius hradiusPositive htT m

end GenomeLaws

end

end Descent.Pangenome.AncestralLocality.InfiniteGenomeRate
