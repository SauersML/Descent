/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.AncestralLocality.LocalityBounds
import Descent.Pangenome.AncestralLocality.LocalityCoupling
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Order.Filter.AtTopBot.Ring

assert_below Descent.PopGen Descent.Spectral Descent.Blindness Descent.Conditionals
assert_below Descent.Portability Descent.Decision Descent.Program

/-!
# The expectation and escape bounds of the genomic light cone

`ANCESTRAL_LOCALITY.md` §8-9, the probabilistic half of Theorems 7 and 8. `LocalityBounds` proves
the generator inequalities `L Z ≤ 3DZ` and `L Z^{(a)} ≤ D(1 + 2a) Z^{(a)}`, and the decision rate
bound `≤ DZ`, on the tagged support state. This module turns them into bounds on expectations and
on the escape probability, and feeds the escape bound into Corollary 8.1.

The corpus has no path law for the backward circuit, so its expectations enter as named
structures. `DriftExpectation K T` is a mean along backward time whose right derivative obeys the
drift inequality `drift ≤ K · mean` on `[0, T)`. That inequality is the Dynkin form of a generator
inequality: for a nonnegative law on finitely many states the expected generator is at most `K`
times the expected functional (`sum_law_mul_le_of_generator_le`), and the three inequalities of
`LocalityBounds` take that form (`sum_law_mul_supportGenerator_le`,
`sum_law_mul_supportGenerator_lightWeight_le`, `sum_law_mul_decisionRate_le`). The extremal
expectation `δ e^{Kt}` meets the drift inequality with equality (`DriftExpectation.exponential`).

By Grönwall's inequality a drift expectation starting at most `δ` stays below `δ e^{Kt}`
(`DriftExpectation.mean_le`); at `K = 3D` and `δ = n|A|` this is (8.2), `E Z_T ≤ n|A| e^{3DT}`
(`supportMean_le`). `BranchingExpectation` adds the expected number of decision branchings, the
integral of an expected decision rate at most `D` times the expected support size, and integrating
(8.2) gives (8.3), `E B_T ≤ (n|A|/3)(e^{3DT} - 1)` (`BranchingExpectation.branchingMean_le`).

Markov's inequality on a finite weighted space (`sum_filter_weight_le_div`), with the light-cone
count, which reaches `a^ℓ` on escape (`pow_le_weightedCount_of_mem_escapeSet`), gives (9.1),
`Pr(E_{ℓ,T}) ≤ min {1, n|A| e^{D(1+2a)T} / a^ℓ}` (`escapeProbability_le_min`). At `a = ℓ/(2DT)`
that bound is exactly `e^{DT} (2eDT/ℓ)^ℓ` (`exp_div_pow_at_lightConeBase`), which is (9.2)
(`escapeProbability_le_lightCone`); when `DT = 0` the escape probability is zero
(`escapeProbability_eq_zero_of_mul_eq_zero`). With (9.2), Corollary 8.1 bounds the total variation
between the sample laws on two inputs whose evaluations agree until escape
(`totalVariation_le_lightCone`).

Scope. The path law of the backward circuit and Dynkin's formula for it are not constructed: the
expectations enter through the structures above, and the law of the tagged state at time `T`
enters as a finite weighted space whose expected light-cone count is the drift expectation at `T`.

## Empirical status

None. The bodies here are Grönwall's inequality, Markov's inequality and real identities: the
rates, the horizon and the expectations are supplied, and no measurement enters any statement.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Pangenome.AncestralLocality

open Finset MeasureTheory Filter Topology

noncomputable section

/-! ### Expectations under a drift inequality -/

/-- An expectation along backward time under a drift inequality: on `[0, T)` the mean has right
derivative `drift t`, and `drift t ≤ K · mean t`. For a law on finitely many states this is the
Dynkin form of a generator inequality `L F ≤ K F` (`sum_law_mul_le_of_generator_le`). -/
structure DriftExpectation (K T : ℝ) where
  /-- The mean `E F(X_t)` along backward time. -/
  mean : ℝ → ℝ
  /-- The right derivative of the mean, `E (L F)(X_t)`. -/
  drift : ℝ → ℝ
  /-- The mean is continuous on the horizon. -/
  continuousOn_mean : ContinuousOn mean (Set.Icc 0 T)
  /-- The mean has the right derivative `drift t` on `[0, T)`. -/
  hasDerivWithinAt_mean : ∀ t ∈ Set.Ico 0 T, HasDerivWithinAt mean (drift t) (Set.Ici t) t
  /-- The drift inequality. -/
  drift_le : ∀ t ∈ Set.Ico 0 T, drift t ≤ K * mean t

/-- The extremal expectation `δ e^{K t}`, which meets the drift inequality with equality. -/
def DriftExpectation.exponential (K T δ : ℝ) : DriftExpectation K T where
  mean t := δ * Real.exp (K * t)
  drift t := K * (δ * Real.exp (K * t))
  continuousOn_mean := by fun_prop
  hasDerivWithinAt_mean t _ := by
    have h := ((hasDerivAt_id t).const_mul K).exp.const_mul δ
    refine (h.congr_deriv ?_).hasDerivWithinAt
    simp only [id_eq, mul_one]
    ring
  drift_le _ _ := le_rfl

/-- Grönwall's inequality for a drift expectation. Assumes: a mean that starts at most `δ`. Then
`mean t ≤ δ e^{K t}` for every `t` in the horizon. -/
theorem DriftExpectation.mean_le {K T : ℝ} (E : DriftExpectation K T) {δ : ℝ}
    (hstart : E.mean 0 ≤ δ) : ∀ t ∈ Set.Icc 0 T, E.mean t ≤ δ * Real.exp (K * t) := by
  intro t ht
  have hbound := le_gronwallBound_of_liminf_deriv_right_le (ε := 0) E.continuousOn_mean
    (fun x hx r hr ↦ ((E.hasDerivWithinAt_mean x hx).liminf_right_slope_le hr).mono
      fun z hz ↦ by rwa [slope_def_module, smul_eq_mul] at hz)
    hstart (fun x hx ↦ by rw [add_zero]; exact E.drift_le x hx) t ht
  rwa [gronwallBound_ε0, sub_zero] at hbound

/-- Spec (8.2). Assumes: a horizon `T ≥ 0` and an expected support size under the drift inequality
of Theorem 7, starting at most `n |A|`. Then `E Z_T ≤ n |A| e^{3DT}`. -/
theorem supportMean_le {V : Type*} (A : Finset V) (n : ℕ) {D T : ℝ}
    (E : DriftExpectation (3 * D) T) (hT : 0 ≤ T) (hstart : E.mean 0 ≤ n * A.card) :
    E.mean T ≤ n * A.card * Real.exp (3 * D * T) :=
  E.mean_le hstart T ⟨hT, le_rfl⟩

/-- The expected number of decision branchings by time `T`: the integral of an expected decision
rate that is at most `D` times the expected support size, the Dynkin form of `decisionRate_le`. -/
structure BranchingExpectation (D T : ℝ) extends DriftExpectation (3 * D) T where
  /-- The expected number of decision branchings by time `T`, `E B_T`. -/
  branchingMean : ℝ
  /-- The expected decision rate at time `t`. -/
  branchingRate : ℝ → ℝ
  /-- The branchings by time `T` are the integral of the expected decision rate. -/
  branchingMean_eq : branchingMean = ∫ u in (0 : ℝ)..T, branchingRate u
  /-- The expected decision rate is integrable on the horizon. -/
  intervalIntegrable_branchingRate : IntervalIntegrable branchingRate volume 0 T
  /-- The expected decision rate is at most `D` times the expected support size. -/
  branchingRate_le : ∀ u ∈ Set.Icc 0 T, branchingRate u ≤ D * mean u

/-- The extremal branching expectation: the support expectation `δ e^{3Dt}` and the decision rate
`D δ e^{3Dt}`. -/
def BranchingExpectation.exponential (D T δ : ℝ) : BranchingExpectation D T where
  toDriftExpectation := DriftExpectation.exponential (3 * D) T δ
  branchingMean := ∫ u in (0 : ℝ)..T, D * (δ * Real.exp (3 * D * u))
  branchingRate u := D * (δ * Real.exp (3 * D * u))
  branchingMean_eq := rfl
  intervalIntegrable_branchingRate :=
    (by fun_prop : Continuous fun u : ℝ ↦ D * (δ * Real.exp (3 * D * u))).intervalIntegrable 0 T
  branchingRate_le _ _ := le_rfl

/-- Spec (8.3). Assumes: a horizon `T ≥ 0`, a nonnegative rate bound `D`, and a branching
expectation whose support expectation starts at most `n |A|`. Then
`E B_T ≤ (n |A| / 3)(e^{3DT} - 1)`. -/
theorem BranchingExpectation.branchingMean_le {V : Type*} (A : Finset V) (n : ℕ) {D T : ℝ}
    (E : BranchingExpectation D T) (hT : 0 ≤ T) (hD : 0 ≤ D) (hstart : E.mean 0 ≤ n * A.card) :
    E.branchingMean ≤ n * A.card / 3 * (Real.exp (3 * D * T) - 1) := by
  have hsupport := E.toDriftExpectation.mean_le hstart
  have hcontinuous : Continuous fun u : ℝ ↦ D * (n * A.card * Real.exp (3 * D * u)) := by
    fun_prop
  have hprimitive : ∀ u ∈ Set.uIcc (0 : ℝ) T,
      HasDerivAt (fun u ↦ n * A.card / 3 * Real.exp (3 * D * u))
        (D * (n * A.card * Real.exp (3 * D * u))) u := by
    intro u _
    have h := ((hasDerivAt_id u).const_mul (3 * D)).exp.const_mul ((n : ℝ) * A.card / 3)
    refine h.congr_deriv ?_
    simp only [id_eq, mul_one]
    ring
  have hintegral : ∫ u in (0 : ℝ)..T, D * (n * A.card * Real.exp (3 * D * u)) =
      n * A.card / 3 * (Real.exp (3 * D * T) - 1) := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hprimitive
      (hcontinuous.intervalIntegrable 0 T)]
    simp only [mul_zero, Real.exp_zero]
    ring
  rw [E.branchingMean_eq, ← hintegral]
  refine intervalIntegral.integral_mono_on hT E.intervalIntegrable_branchingRate
    (hcontinuous.intervalIntegrable 0 T) fun u hu ↦ ?_
  exact (E.branchingRate_le u hu).trans (mul_le_mul_of_nonneg_left (hsupport u hu) hD)

/-! ### The Dynkin form of the generator inequalities -/

/-- The Dynkin form of a generator inequality. Assumes: a nonnegative law on finitely many states
and a generator inequality `G ≤ K F` on every state of the law. The expected generator is at most
`K` times the expected functional, so a mean whose right derivative is the expected generator
obeys the drift inequality. -/
theorem sum_law_mul_le_of_generator_le {σ : Type*} (states : Finset σ) (law F G : σ → ℝ)
    (hlaw : ∀ s ∈ states, 0 ≤ law s) {K : ℝ} (hgenerator : ∀ s ∈ states, G s ≤ K * F s) :
    ∑ s ∈ states, law s * G s ≤ K * ∑ s ∈ states, law s * F s := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun s hs ↦ ?_
  calc law s * G s ≤ law s * (K * F s) := mul_le_mul_of_nonneg_left (hgenerator s hs) (hlaw s hs)
    _ = K * (law s * F s) := by ring

/-- Theorem 7 in Dynkin form. Assumes: nonnegative rates whose rows sum to at most `D`, a
nonnegative coalescence rate and a nonnegative law on finitely many tagged states. The expected
generator of the support size is at most `3D` times the expected support size. -/
theorem sum_law_mul_supportGenerator_le {V : Type*} [Fintype V] [DecidableEq V]
    {r : V → V → ℝ} {c D : ℝ} (hr : ∀ i j, 0 ≤ r i j) (hD : ∀ i, ∑ j, r i j ≤ D) (hc : 0 ≤ c)
    (states : Finset (Multiset (Finset V))) (law : Multiset (Finset V) → ℝ)
    (hlaw : ∀ s ∈ states, 0 ≤ law s) :
    ∑ s ∈ states, law s * supportGenerator r c supportSize s ≤
      3 * D * ∑ s ∈ states, law s * supportSize s :=
  sum_law_mul_le_of_generator_le states law supportSize _ hlaw fun s _ ↦
    supportGenerator_supportSize_le hr hD hc s

/-- Theorem 8 in Dynkin form. Assumes: nonnegative rates whose rows sum to at most `D`, a
nonnegative coalescence rate, a base `a ≥ 1` and a nonnegative law on finitely many tagged states.
The expected generator of the light-cone count is at most `D(1 + 2a)` times the expected count. -/
theorem sum_law_mul_supportGenerator_lightWeight_le {V : Type*} [Fintype V] [DecidableEq V]
    {r : V → V → ℝ} {c D a : ℝ} {A : Finset V} {ℓ : ℕ} (hr : ∀ i j, 0 ≤ r i j)
    (hD : ∀ i, ∑ j, r i j ≤ D) (hc : 0 ≤ c) (ha : 1 ≤ a)
    (states : Finset (Multiset (Finset V))) (law : Multiset (Finset V) → ℝ)
    (hlaw : ∀ s ∈ states, 0 ≤ law s) :
    ∑ s ∈ states, law s * supportGenerator r c (weightedCount (lightWeight r A ℓ a)) s ≤
      D * (1 + 2 * a) * ∑ s ∈ states, law s * weightedCount (lightWeight r A ℓ a) s :=
  sum_law_mul_le_of_generator_le states law _ _ hlaw fun s _ ↦
    supportGenerator_lightWeight_le hr hD hc ha s

/-- The decision rate in Dynkin form. Assumes: rates whose rows sum to at most `D` and a
nonnegative law on finitely many tagged states. The expected decision rate is at most `D` times the
expected support size. -/
theorem sum_law_mul_decisionRate_le {V : Type*} [Fintype V] {r : V → V → ℝ} {D : ℝ}
    (hD : ∀ i, ∑ j, r i j ≤ D) (states : Finset (Multiset (Finset V)))
    (law : Multiset (Finset V) → ℝ) (hlaw : ∀ s ∈ states, 0 ≤ law s) :
    ∑ s ∈ states, law s * decisionRate r s ≤ D * ∑ s ∈ states, law s * supportSize s :=
  sum_law_mul_le_of_generator_le states law supportSize _ hlaw fun s _ ↦ decisionRate_le hD s

/-! ### The escape bounds -/

/-- Markov's inequality on a finite weighted space. Assumes: nonnegative weights, a nonnegative
count, a positive threshold, and an event on which the count reaches the threshold. The weight of
the event is at most the expected count over the threshold. -/
theorem sum_filter_weight_le_div {Ω : Type*} [Fintype Ω] (weight count : Ω → ℝ)
    (hweight : ∀ ω, 0 ≤ weight ω) (hcount : ∀ ω, 0 ≤ count ω) (escape : Ω → Prop)
    [DecidablePred escape] {threshold : ℝ} (hthreshold : 0 < threshold)
    (hescape : ∀ ω, escape ω → threshold ≤ count ω) :
    ∑ ω ∈ univ.filter escape, weight ω ≤ (∑ ω, weight ω * count ω) / threshold := by
  rw [le_div_iff₀ hthreshold, Finset.sum_mul]
  calc ∑ ω ∈ univ.filter escape, weight ω * threshold
      ≤ ∑ ω ∈ univ.filter escape, weight ω * count ω :=
        Finset.sum_le_sum fun ω hω ↦
          mul_le_mul_of_nonneg_left (hescape ω (Finset.mem_filter.mp hω).2) (hweight ω)
    _ ≤ ∑ ω, weight ω * count ω :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          fun ω _ _ ↦ mul_nonneg (hweight ω) (hcount ω)

open scoped Classical in
/-- Spec (9.1). Assumes: nonnegative rates, a base `a > 1`, a horizon `T ≥ 0`, a finite law of the
tagged state at time `T`, and a light-cone expectation under the drift inequality of Theorem 8
that starts at most `n |A|` and at time `T` is the expected light-cone count of that law. The
circuit reaches directed distance `ℓ` with probability at most
`min {1, n |A| e^{D(1+2a)T} / a^ℓ}`. -/
theorem escapeProbability_le_min {V Ω : Type*} [Fintype V] [DecidableEq V] [Fintype Ω]
    (r : V → V → ℝ) (A : Finset V) (ℓ n : ℕ) {a D T : ℝ} (ha : 1 < a) (hT : 0 ≤ T)
    (weight : Ω → ℝ) (hweight : ∀ ω, 0 ≤ weight ω) (htotal : ∑ ω, weight ω = 1)
    (state : Ω → Multiset (Finset V)) (E : DriftExpectation (D * (1 + 2 * a)) T)
    (hstart : E.mean 0 ≤ n * A.card)
    (hmean : ∑ ω, weight ω * weightedCount (lightWeight r A ℓ a) (state ω) = E.mean T) :
    ∑ ω ∈ univ.filter (fun ω ↦ state ω ∈ escapeSet r A ℓ), weight ω ≤
      min 1 (n * A.card * Real.exp (D * (1 + 2 * a) * T) / a ^ ℓ) := by
  have hpositive : 0 < a ^ ℓ := pow_pos (by linarith) ℓ
  refine le_min ?_ ?_
  · calc ∑ ω ∈ univ.filter (fun ω ↦ state ω ∈ escapeSet r A ℓ), weight ω ≤ ∑ ω, weight ω :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            fun ω _ _ ↦ hweight ω
      _ = 1 := htotal
  · calc ∑ ω ∈ univ.filter (fun ω ↦ state ω ∈ escapeSet r A ℓ), weight ω
        ≤ (∑ ω, weight ω * weightedCount (lightWeight r A ℓ a) (state ω)) / a ^ ℓ :=
          sum_filter_weight_le_div weight (fun ω ↦ weightedCount (lightWeight r A ℓ a) (state ω))
            hweight (fun ω ↦ weightedCount_nonneg (lightWeight_nonneg (by linarith)) (state ω))
            (fun ω ↦ state ω ∈ escapeSet r A ℓ) hpositive
            fun ω hω ↦ pow_le_weightedCount_of_mem_escapeSet (by linarith) hω
      _ = E.mean T * (a ^ ℓ)⁻¹ := by rw [hmean, div_eq_mul_inv]
      _ ≤ n * A.card * Real.exp (D * (1 + 2 * a) * T) * (a ^ ℓ)⁻¹ :=
          mul_le_mul_of_nonneg_right (E.mean_le hstart T ⟨hT, le_rfl⟩)
            (inv_nonneg.mpr hpositive.le)
      _ = n * A.card * Real.exp (D * (1 + 2 * a) * T) / a ^ ℓ := (div_eq_mul_inv _ _).symm

/-- The real identity behind (9.2). Assumes: `DT > 0` and a positive radius `ℓ`. At the base
`a = ℓ/(2DT)` the bound of (9.1) is exactly `e^{DT} (2eDT/ℓ)^ℓ`. -/
theorem exp_div_pow_at_lightConeBase {D T : ℝ} (hDT : 0 < D * T) {ℓ : ℕ} (hℓ : 0 < ℓ) :
    Real.exp (D * (1 + 2 * (ℓ / (2 * D * T))) * T) / (ℓ / (2 * D * T)) ^ ℓ =
      Real.exp (D * T) * (2 * Real.exp 1 * D * T / ℓ) ^ ℓ := by
  obtain ⟨hD, hT⟩ := mul_ne_zero_iff.mp hDT.ne'
  have hradius : (ℓ : ℝ) ≠ 0 := by exact_mod_cast hℓ.ne'
  have hexponent : D * (1 + 2 * (ℓ / (2 * D * T))) * T = D * T + ℓ := by
    field_simp
    ring
  have hpower : Real.exp (ℓ : ℝ) = Real.exp 1 ^ ℓ := by
    rw [← Real.exp_nat_mul, mul_one]
  have hbase : 2 * Real.exp 1 * D * T / ℓ = Real.exp 1 * (ℓ / (2 * D * T))⁻¹ := by
    rw [inv_div]
    ring
  rw [hexponent, Real.exp_add, hpower, hbase, mul_pow, inv_pow]
  ring

open scoped Classical in
/-- Spec (9.2). Assumes: the hypotheses of `escapeProbability_le_min` at the base `a = ℓ/(2DT)`,
with `DT > 0` and `ℓ > 2DT`. The circuit reaches directed distance `ℓ` with probability at most
`min {1, n |A| e^{DT} (2eDT/ℓ)^ℓ}`. -/
theorem escapeProbability_le_lightCone {V Ω : Type*} [Fintype V] [DecidableEq V] [Fintype Ω]
    (r : V → V → ℝ) (A : Finset V) (ℓ n : ℕ) {D T : ℝ} (hDT : 0 < D * T) (hℓ : 2 * D * T < ℓ)
    (hT : 0 ≤ T) (weight : Ω → ℝ) (hweight : ∀ ω, 0 ≤ weight ω) (htotal : ∑ ω, weight ω = 1)
    (state : Ω → Multiset (Finset V))
    (E : DriftExpectation (D * (1 + 2 * (ℓ / (2 * D * T)))) T) (hstart : E.mean 0 ≤ n * A.card)
    (hmean : ∑ ω, weight ω * weightedCount (lightWeight r A ℓ (ℓ / (2 * D * T))) (state ω) =
      E.mean T) :
    ∑ ω ∈ univ.filter (fun ω ↦ state ω ∈ escapeSet r A ℓ), weight ω ≤
      min 1 (n * A.card * (Real.exp (D * T) * (2 * Real.exp 1 * D * T / ℓ) ^ ℓ)) := by
  have hbase : 1 < (ℓ : ℝ) / (2 * D * T) := by
    rw [one_lt_div (by linarith)]
    exact hℓ
  have hradius : 0 < ℓ := (Nat.cast_pos (α := ℝ)).mp (by linarith)
  have h := escapeProbability_le_min r A ℓ n hbase hT weight hweight htotal state E hstart hmean
  rwa [mul_div_assoc, exp_div_pow_at_lightConeBase hDT hradius] at h

open scoped Classical in
/-- Spec §9, the degenerate horizon. Assumes: `DT = 0`, a positive radius, a horizon `T ≥ 0`, a
finite law of the tagged state at time `T`, and for every base `a > 1` a light-cone expectation
under the drift inequality of Theorem 8 that starts at most `n |A|` and at time `T` is the expected
light-cone count. Then the escape probability is zero. -/
theorem escapeProbability_eq_zero_of_mul_eq_zero {V Ω : Type*} [Fintype V] [DecidableEq V]
    [Fintype Ω] (r : V → V → ℝ) (A : Finset V) (ℓ n : ℕ) {D T : ℝ} (hDT : D * T = 0)
    (hℓ : 0 < ℓ) (hT : 0 ≤ T) (weight : Ω → ℝ) (hweight : ∀ ω, 0 ≤ weight ω)
    (htotal : ∑ ω, weight ω = 1) (state : Ω → Multiset (Finset V))
    (E : ∀ a : ℝ, 1 < a → DriftExpectation (D * (1 + 2 * a)) T)
    (hstart : ∀ a ha, (E a ha).mean 0 ≤ n * A.card)
    (hmean : ∀ a ha,
      ∑ ω, weight ω * weightedCount (lightWeight r A ℓ a) (state ω) = (E a ha).mean T) :
    ∑ ω ∈ univ.filter (fun ω ↦ state ω ∈ escapeSet r A ℓ), weight ω = 0 := by
  refine le_antisymm ?_ (Finset.sum_nonneg fun ω _ ↦ hweight ω)
  have hbound : ∀ a : ℝ, 1 < a →
      ∑ ω ∈ univ.filter (fun ω ↦ state ω ∈ escapeSet r A ℓ), weight ω ≤
        n * A.card * (a ^ ℓ)⁻¹ := by
    intro a ha
    have h := (escapeProbability_le_min r A ℓ n ha hT weight hweight htotal state (E a ha)
      (hstart a ha) (hmean a ha)).trans (min_le_right _ _)
    have hexponent : D * (1 + 2 * a) * T = 0 := by
      rw [(by ring : D * (1 + 2 * a) * T = (1 + 2 * a) * (D * T)), hDT, mul_zero]
    rwa [hexponent, Real.exp_zero, mul_one, div_eq_mul_inv] at h
  have hlimit : Tendsto (fun a : ℝ ↦ (n * A.card : ℝ) * (a ^ ℓ)⁻¹) atTop (𝓝 0) := by
    have h := (tendsto_inv_atTop_zero.comp (tendsto_pow_atTop hℓ.ne')).const_mul
      ((n : ℝ) * A.card)
    simpa only [mul_zero, Function.comp_def] using h
  exact ge_of_tendsto hlimit ((eventually_gt_atTop 1).mono fun a ha ↦ hbound a ha)

open scoped Classical in
/-- Spec Corollary 8.1 with (9.2). Assumes: the hypotheses of `escapeProbability_le_lightCone`,
and for every circuit randomness `ω` two finite laws on samples, the evaluations of the circuit on
two inputs, which coincide unless the circuit has reached directed distance `ℓ`. The two sample
laws are within total variation `min {1, n |A| e^{DT} (2eDT/ℓ)^ℓ}`. -/
theorem totalVariation_le_lightCone {V Ω S : Type*} [Fintype V] [DecidableEq V] [Fintype Ω]
    [Fintype S] (r : V → V → ℝ) (A : Finset V) (ℓ n : ℕ) {D T : ℝ} (hDT : 0 < D * T)
    (hℓ : 2 * D * T < ℓ) (hT : 0 ≤ T) (weight : Ω → ℝ) (hweight : ∀ ω, 0 ≤ weight ω)
    (htotal : ∑ ω, weight ω = 1) (state : Ω → Multiset (Finset V))
    (E : DriftExpectation (D * (1 + 2 * (ℓ / (2 * D * T)))) T) (hstart : E.mean 0 ≤ n * A.card)
    (hmean : ∑ ω, weight ω * weightedCount (lightWeight r A ℓ (ℓ / (2 * D * T))) (state ω) =
      E.mean T)
    (evaluationP evaluationQ : Ω → S → ℝ) (hnonnegP : ∀ ω s, 0 ≤ evaluationP ω s)
    (hnonnegQ : ∀ ω s, 0 ≤ evaluationQ ω s) (htotalP : ∀ ω, ∑ s, evaluationP ω s = 1)
    (htotalQ : ∀ ω, ∑ s, evaluationQ ω s = 1)
    (hagree : ∀ ω, state ω ∉ escapeSet r A ℓ → evaluationP ω = evaluationQ ω) :
    totalVariation (mixtureLaw weight evaluationP) (mixtureLaw weight evaluationQ) ≤
      min 1 (n * A.card * (Real.exp (D * T) * (2 * Real.exp 1 * D * T / ℓ) ^ ℓ)) :=
  (totalVariation_mixtureLaw_le weight hweight evaluationP evaluationQ hnonnegP hnonnegQ htotalP
    htotalQ (fun ω ↦ state ω ∈ escapeSet r A ℓ) hagree).trans
    (escapeProbability_le_lightCone r A ℓ n hDT hℓ hT weight hweight htotal state E hstart hmean)

end

end Descent.Pangenome.AncestralLocality
