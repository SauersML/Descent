/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Coalescent.ComingDownCriterion
import Mathlib.Analysis.PSeries
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

namespace Descent

/-!
# The Bolthausen-Sznitman coalescent does not come down from infinity

`Descent.Coalescent.ComingDownCriterion` computes the Bolthausen-Sznitman decrease rate --
each `k`-fold merger contributes `b/k`, so `γ_b = b(H_b - 1)` -- and records the one step it
could not take: that `Σ γ_b⁻¹` diverges.  This file takes it.

The obstacle was never genealogical.  `γ_b` grows like `b log b`, and `Σ 1/(b log b)` is
Bertrand's series, whose divergence needs Cauchy condensation: the condensed sum
`Σ 2^k f(2^k)` collapses to `Σ 1/(k log 2)`, a constant multiple of the harmonic series.
Mathlib has the condensation test and the bound `H_n ≤ 1 + log n`; what was missing was the
assembly, and that is what is here.

  `γ_b = b(H_b - 1) ≤ b log b`,   so   `γ_b⁻¹ ≥ (b log b)⁻¹`,   which is not summable.

So the criterion's two sides are now both inhabited by named coalescents rather than by one
named and one hypothetical: Kingman comes down, Bolthausen-Sznitman does not, and the star
coalescent does not.

## A note on what `bertrandTerm` is doing

Condensation needs a function antitone on the whole positive range, and `1/(n log n)` is not
one: at `n = 1` the logarithm vanishes and the term is `1/0 = 0`, below its successor rather
than above it.  `bertrandTerm` therefore takes the value `1` below `n = 2`, which is above
`1/(2 log 2)` because `2 log 2 = log 4 > 1`.  That is the only place the constant `e < 4`
enters, and it enters as an inequality about numbers rather than about series.

## Main results

- `bertrandTerm`, `bertrandTerm_antitone`: the term, made antitone.
- `not_summable_bertrandTerm`: **`Σ 1/(n log n)` diverges**, by condensation.
- `harmonicSum_le_one_add_log`: `H_n ≤ 1 + log n`, from Mathlib's `harmonic`.
- `bsRate_le_mul_log`: hence `γ_b ≤ b log b`.
- `bolthausenSznitman_not_comesDownFromInfinity`: **the conclusion**.
-/

namespace Coalescent

open Filter Finset

/-! ### `2 log 2 > 1` -/

/-- `1 < log 4`, which is `e < 4`.  The only numeric input to the file. -/
theorem one_lt_log_four : (1 : ℝ) < Real.log 4 := by
  have he : Real.exp 1 < 4 := by
    have h := Real.exp_one_lt_d9
    linarith
  rw [show (1 : ℝ) = Real.log (Real.exp 1) by rw [Real.log_exp]]
  exact Real.log_lt_log (Real.exp_pos 1) he

/-- `1 < 2 log 2`, the same fact with the logarithm split. -/
theorem one_lt_two_mul_log_two : (1 : ℝ) < 2 * Real.log 2 := by
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    push_cast
    ring
  rw [← h4]
  exact one_lt_log_four

/-- For `n ≥ 2` the product `n log n` is at least `2 log 2`, hence above one. -/
theorem one_le_mul_log {n : ℕ} (hn : 2 ≤ n) : 1 ≤ (n : ℝ) * Real.log n := by
  have hn' : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hlog : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) hn'
  have hlogpos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hmul : 2 * Real.log 2 ≤ (n : ℝ) * Real.log n := by
    have h1 : 2 * Real.log 2 ≤ (n : ℝ) * Real.log 2 := by nlinarith
    nlinarith
  linarith [one_lt_two_mul_log_two]

/-! ### Bertrand's term -/

/-- `1/(n log n)`, set to `1` below `n = 2` so that it is antitone on the positives -- which
is what the condensation test requires and what `1/(n log n)` on its own is not. -/
noncomputable def bertrandTerm (n : ℕ) : ℝ :=
  if n ≤ 1 then 1 else 1 / ((n : ℝ) * Real.log n)

theorem bertrandTerm_nonneg (n : ℕ) : 0 ≤ bertrandTerm n := by
  unfold bertrandTerm
  by_cases h : n ≤ 1
  · simp [h]
  · simp only [h, if_false]
    have hn : 2 ≤ n := by omega
    have := one_le_mul_log hn
    positivity

theorem bertrandTerm_le_one (n : ℕ) : bertrandTerm n ≤ 1 := by
  unfold bertrandTerm
  by_cases h : n ≤ 1
  · simp [h]
  · simp only [h, if_false]
    have hn : 2 ≤ n := by omega
    have hml := one_le_mul_log hn
    rw [div_le_one (by linarith)]
    linarith

/-- The term is antitone where condensation needs it to be. -/
theorem bertrandTerm_antitone :
    ∀ ⦃m n : ℕ⦄, 0 < m → m ≤ n → bertrandTerm n ≤ bertrandTerm m := by
  intro m n _ hmn
  by_cases hm : m ≤ 1
  · have : bertrandTerm m = 1 := by unfold bertrandTerm; simp [hm]
    rw [this]
    exact bertrandTerm_le_one n
  · have hm2 : 2 ≤ m := by omega
    have hn2 : 2 ≤ n := le_trans hm2 hmn
    have hmR : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm2
    have hmnR : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
    have hlogm : (0 : ℝ) < Real.log m := Real.log_pos (by linarith)
    have hlog : Real.log m ≤ Real.log n := Real.log_le_log (by linarith) hmnR
    have hprod : (m : ℝ) * Real.log m ≤ (n : ℝ) * Real.log n := by nlinarith
    have hpos : (0 : ℝ) < (m : ℝ) * Real.log m := by positivity
    unfold bertrandTerm
    simp only [hm, if_false, show ¬ n ≤ 1 from by omega, if_false]
    exact one_div_le_one_div_of_le hpos hprod

/-! ### Divergence -/

/-- The condensed term: `2^k · f(2^k)` is `1/(k log 2)` once `k ≥ 1`. -/
theorem condensed_bertrandTerm {k : ℕ} (hk : 1 ≤ k) :
    (2 : ℝ) ^ k * bertrandTerm (2 ^ k) = 1 / ((k : ℝ) * Real.log 2) := by
  have h2k : 2 ≤ 2 ^ k := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  have hnot : ¬ (2 ^ k ≤ 1) := by omega
  have hcast : ((2 ^ k : ℕ) : ℝ) = (2 : ℝ) ^ k := by push_cast; ring
  have hlog : Real.log ((2 ^ k : ℕ) : ℝ) = (k : ℝ) * Real.log 2 := by
    rw [hcast, Real.log_pow]
  unfold bertrandTerm
  simp only [hnot, if_false]
  rw [hlog, hcast]
  have hpow : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
  have hlogpos : (0 : ℝ) < (k : ℝ) * Real.log 2 := by
    have hk' : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    have : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    positivity
  field_simp

/-- **Bertrand's series diverges.**  Condensation turns `Σ 1/(n log n)` into
`Σ 1/(k log 2)`, a constant multiple of the harmonic series. -/
theorem not_summable_bertrandTerm : ¬ Summable bertrandTerm := by
  rw [← summable_condensed_iff_of_nonneg bertrandTerm_nonneg bertrandTerm_antitone]
  intro hsum
  have h1 : Summable fun k : ℕ ↦ (2 : ℝ) ^ (k + 1) * bertrandTerm (2 ^ (k + 1)) :=
    (summable_nat_add_iff (f := fun k : ℕ ↦ (2 : ℝ) ^ k * bertrandTerm (2 ^ k)) 1).mpr hsum
  have hharm : Summable fun k : ℕ ↦ 1 / (((k : ℝ) + 1) * Real.log 2) := by
    refine h1.congr fun k ↦ ?_
    rw [condensed_bertrandTerm (k := k + 1) (by omega)]
    push_cast
    ring
  have hl : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have h2e : (2 : ℝ) < Real.exp 1 := by
    have h := Real.exp_one_gt_d9
    linarith
  have hlog2lt : Real.log 2 < 1 := by
    have h := Real.log_lt_log (by norm_num : (0 : ℝ) < 2) h2e
    rwa [Real.log_exp] at h
  have hcmp : ∀ k : ℕ, 1 / ((k : ℝ) + 1) ≤ 1 / (((k : ℝ) + 1) * Real.log 2) := by
    intro k
    have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have hle : ((k : ℝ) + 1) * Real.log 2 ≤ (k : ℝ) + 1 := by nlinarith
    exact one_div_le_one_div_of_le (mul_pos hk hl) hle
  have hfinal : Summable fun k : ℕ ↦ 1 / ((k : ℝ) + 1) :=
    Summable.of_nonneg_of_le (fun k ↦ by positivity) hcmp hharm
  have hno := mt (summable_nat_add_iff (f := fun n : ℕ ↦ 1 / (n : ℝ)) 1).mp
    Real.not_summable_one_div_natCast
  refine hno ?_
  refine hfinal.congr fun k ↦ ?_
  push_cast
  ring

/-! ### The Bolthausen-Sznitman rate -/

/-- The corpus's harmonic sum is Mathlib's `harmonic`, so Mathlib's bound applies to it. -/
theorem harmonicSum_eq_harmonic (n : ℕ) : harmonicSum n = ((harmonic n : ℚ) : ℝ) := by
  unfold harmonicSum harmonic
  push_cast
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [one_div]

/-- **`H_n ≤ 1 + log n`**, Mathlib's bound transported to `harmonicSum`. -/
theorem harmonicSum_le_one_add_log (n : ℕ) : harmonicSum n ≤ 1 + Real.log n := by
  rw [harmonicSum_eq_harmonic]
  exact_mod_cast harmonic_le_one_add_log n

/-- The Bolthausen-Sznitman decrease rate, `γ_b = b(H_b - 1)`, as a function.

Empirical status: DERIVED.  `ComingDownCriterion.bolthausenSznitman_decrease_term` computes
each merger's contribution and `sum_bolthausenSznitman_rate` sums them. -/
noncomputable def bsRate (b : ℕ) : ℝ := (b : ℝ) * (harmonicSum b - 1)

/-- **`γ_b ≤ b log b`.**  The harmonic bound, multiplied by `b`. -/
theorem bsRate_le_mul_log (b : ℕ) : bsRate b ≤ (b : ℝ) * Real.log b := by
  have h := harmonicSum_le_one_add_log b
  have hb : (0 : ℝ) ≤ (b : ℝ) := Nat.cast_nonneg b
  unfold bsRate
  nlinarith

/-- `γ_b` is positive from `b = 2` on, so its reciprocal is a real number and not a
convention about division by zero. -/
theorem bsRate_pos (b : ℕ) : 0 < bsRate (b + 2) := by
  have hmono : harmonicSum 2 ≤ harmonicSum (b + 2) :=
    harmonicSum_strictMono.monotone (by omega)
  have h2 : harmonicSum 2 = 3 / 2 := by
    norm_num [harmonicSum, Finset.sum_range_succ]
  have hb : (0 : ℝ) < (b : ℝ) + 2 := by positivity
  unfold bsRate
  push_cast
  nlinarith

/-- **The Bolthausen-Sznitman coalescent does not come down from infinity.**

`γ_b ≤ b log b`, so `γ_b⁻¹` dominates Bertrand's term, which is not summable.  The criterion
fails, and the family's two sides are now both inhabited by named coalescents. -/
theorem bolthausenSznitman_not_comesDownFromInfinity :
    ¬ comesDownFromInfinity bsRate := by
  unfold comesDownFromInfinity
  intro hsum
  have hshift : ¬ Summable fun b : ℕ ↦ bertrandTerm (b + 2) := by
    intro h
    exact not_summable_bertrandTerm ((summable_nat_add_iff 2).mp h)
  refine hshift ?_
  refine Summable.of_nonneg_of_le (fun b ↦ bertrandTerm_nonneg _) (fun b ↦ ?_) hsum
  have hb2 : 2 ≤ b + 2 := by omega
  have hnot : ¬ (b + 2 ≤ 1) := by omega
  have hpos := bsRate_pos b
  have hle := bsRate_le_mul_log (b + 2)
  have hml := one_le_mul_log hb2
  unfold bertrandTerm
  simp only [hnot, if_false]
  exact one_div_le_one_div_of_le hpos hle

end Coalescent

end Descent
