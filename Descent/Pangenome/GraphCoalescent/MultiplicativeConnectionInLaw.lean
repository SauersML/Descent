/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.GraphCoalescent.MultiplicativeConnectionConvergence
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.Probability.CDF

assert_below Descent.PopGen Descent.Spectral Descent.Blindness Descent.Conditionals
assert_below Descent.Portability Descent.Decision Descent.Program

/-!
# (F3) in law: the scaled connection clock of a compressed pangenome

`Descent.Pangenome.GraphCoalescent.MultiplicativeConnectionConvergence` proves that the probability
that the graph's report is connected at scaled time `U` converges to `Pr(T_p ≤ U)` at every
`U ≥ 0`.  Convergence in law is the statement about the laws themselves: the laws of the scaled
connection times converge to the law of `T_p` in the weak topology on probability measures on `ℝ`.

This file proves the criterion that turns the first into the second: distribution functions that
converge at every point give convergence in law (`tendsto_probabilityMeasure_of_tendsto_cdf`).  The
half-open intervals form a π-system containing arbitrarily small neighborhoods of every point, and
the measure of `(a, b]` is the increment of the distribution function, so Mathlib's π-system form of
the portmanteau theorem applies.

## Main results

- `tendsto_probabilityMeasure_of_tendsto_cdf`: convergence of the distribution functions at every
  point gives convergence in law.

## Empirical status

None.  Every declaration here is a statement about probability measures on the real line and their
distribution functions.
-/

namespace Descent.Pangenome.GraphCoalescent

open Coalescent MeasureTheory ProbabilityTheory Filter Topology Set

open scoped Classical

noncomputable section

/-! ### Distribution functions and convergence in law -/

/-- The measure of a half-open interval is the increment of the distribution function. -/
theorem coe_probabilityMeasure_Ioc (ρ : ProbabilityMeasure ℝ) {a b : ℝ} (hab : a ≤ b) :
    ((ρ (Ioc a b) : NNReal) : ℝ) = cdf (ρ : Measure ℝ) b - cdf (ρ : Measure ℝ) a := by
  rw [← ProbabilityMeasure.measureReal_eq_coe_coeFn, measureReal_def]
  conv_lhs => rw [← measure_cdf (ρ : Measure ℝ)]
  rw [StieltjesFunction.measure_Ioc,
    ENNReal.toReal_ofReal (sub_nonneg.mpr ((cdf (ρ : Measure ℝ)).mono hab))]

/-- **Distribution functions converging at every point give convergence in law.** -/
theorem tendsto_probabilityMeasure_of_tendsto_cdf {ι : Type*} {l : Filter ι}
    [l.IsCountablyGenerated] {μ : ι → ProbabilityMeasure ℝ} {ν : ProbabilityMeasure ℝ}
    (h : ∀ x, Tendsto (fun i ↦ cdf (μ i : Measure ℝ) x) l (𝓝 (cdf (ν : Measure ℝ) x))) :
    Tendsto μ l (𝓝 ν) := by
  refine (isPiSystem_Ioc_mem (univ : Set ℝ) univ).tendsto_probabilityMeasure_of_tendsto_of_mem
    ?_ ?_ ?_
  · rintro s ⟨a, -, b, -, -, rfl⟩
    exact measurableSet_Ioc
  · intro u hu x hx
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hu x hx
    refine ⟨Ioc (x - ε / 2) (x + ε / 2),
      ⟨x - ε / 2, mem_univ _, x + ε / 2, mem_univ _, by linarith, rfl⟩,
      Ioc_mem_nhds (by linarith) (by linarith), fun y hy ↦ hball ?_⟩
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [hy.1, hy.2]
  · rintro s ⟨a, -, b, -, hab, rfl⟩
    rw [← NNReal.tendsto_coe]
    simp only [coe_probabilityMeasure_Ioc _ hab.le]
    exact (h b).sub (h a)

/-! ### Poisson mixtures as functions of the mean

The distribution function of the uniformized connection time at scaled time `U` is a Poisson
mixture `Σ_m Pr(N_U = m) a_m` of the probabilities `a_m` that the skeleton has connected by step
`m`.  Such a mixture is nondecreasing in `U` when `a` is, continuous in `U`, and tends to one
when `a_m` does. -/

/-- **Poisson laws add**: `Pr(N_{U+W} = n) = Σ_{k+l=n} Pr(N_U = k) Pr(N_W = l)`. -/
theorem poissonPMFReal_add (U W : NNReal) (n : ℕ) :
    poissonPMFReal (U + W) n
      = ∑ kl ∈ Finset.antidiagonal n, poissonPMFReal U kl.1 * poissonPMFReal W kl.2 := by
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  dsimp only
  unfold poissonPMFReal
  push_cast
  rw [add_pow, Finset.mul_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  rw [Nat.cast_choose ℝ hkn, neg_add, Real.exp_add]
  have h1 : (k.factorial : ℝ) ≠ 0 := by positivity
  have h2 : ((n - k).factorial : ℝ) ≠ 0 := by positivity
  have h3 : (n.factorial : ℝ) ≠ 0 := by positivity
  field_simp

/-- A Poisson mixture of numbers in `[0, 1]` is summable. -/
theorem summable_poissonPMFReal_mul {a : ℕ → ℝ} (ha0 : ∀ m, 0 ≤ a m) (ha1 : ∀ m, a m ≤ 1)
    (V : NNReal) : Summable fun m ↦ poissonPMFReal V m * a m :=
  Summable.of_nonneg_of_le (fun m ↦ mul_nonneg poissonPMFReal_nonneg (ha0 m))
    (fun m ↦ by
      calc poissonPMFReal V m * a m ≤ poissonPMFReal V m * 1 :=
            mul_le_mul_of_nonneg_left (ha1 m) poissonPMFReal_nonneg
        _ = poissonPMFReal V m := mul_one _)
    (poissonPMFRealSum V).summable

/-- **A Poisson mixture of a nondecreasing sequence grows with the mean.** -/
theorem poissonMixture_le_add {a : ℕ → ℝ} (ha0 : ∀ m, 0 ≤ a m) (ha1 : ∀ m, a m ≤ 1)
    (hmono : Monotone a) (U W : NNReal) : poissonMixture U a ≤ poissonMixture (U + W) a := by
  have hf : Summable fun m ↦ ‖poissonPMFReal U m * a m‖ :=
    (summable_poissonPMFReal_mul ha0 ha1 U).abs
  have hg : Summable fun m ↦ ‖poissonPMFReal W m‖ := (poissonPMFRealSum W).summable.abs
  have hprod := tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hf hg
  rw [(poissonPMFRealSum W).tsum_eq, mul_one] at hprod
  have hcauchy : Summable fun n ↦ ∑ kl ∈ Finset.antidiagonal n,
      poissonPMFReal U kl.1 * a kl.1 * poissonPMFReal W kl.2 :=
    (summable_norm_sum_mul_antidiagonal_of_summable_norm hf hg).of_norm
  unfold poissonMixture
  rw [hprod]
  refine hasSum_le (fun n ↦ ?_) hcauchy.hasSum (summable_poissonPMFReal_mul ha0 ha1 _).hasSum
  rw [poissonPMFReal_add, Finset.sum_mul]
  refine Finset.sum_le_sum fun kl hkl ↦ ?_
  have hle : kl.1 ≤ n := by
    have := Finset.mem_antidiagonal.mp hkl
    omega
  have hπ : 0 ≤ poissonPMFReal U kl.1 * poissonPMFReal W kl.2 :=
    mul_nonneg poissonPMFReal_nonneg poissonPMFReal_nonneg
  calc poissonPMFReal U kl.1 * a kl.1 * poissonPMFReal W kl.2
      = poissonPMFReal U kl.1 * poissonPMFReal W kl.2 * a kl.1 := by ring
    _ ≤ poissonPMFReal U kl.1 * poissonPMFReal W kl.2 * a n :=
        mul_le_mul_of_nonneg_left (hmono hle) hπ

/-- **The mixture is nondecreasing in the mean.** -/
theorem monotone_poissonMixture {a : ℕ → ℝ} (ha0 : ∀ m, 0 ≤ a m) (ha1 : ∀ m, a m ≤ 1)
    (hmono : Monotone a) : Monotone fun U : NNReal ↦ poissonMixture U a := by
  intro U V hUV
  obtain ⟨W, rfl⟩ := exists_add_of_le hUV
  exact poissonMixture_le_add ha0 ha1 hmono U W

/-- The mixture at a nonnegative real mean, written as a series in the mean. -/
theorem poissonMixture_toNNReal {a : ℕ → ℝ} {u : ℝ} (hu : 0 ≤ u) :
    poissonMixture u.toNNReal a
      = ∑' m : ℕ, Real.exp (-u) * (u ^ m / (m.factorial : ℝ)) * a m := by
  unfold poissonMixture
  refine tsum_congr fun m ↦ ?_
  rw [poissonPMFReal, Real.coe_toNNReal u hu]
  ring

/-- **The series in the mean is continuous.** -/
theorem continuous_poissonSeries {a : ℕ → ℝ} (ha : ∀ m, |a m| ≤ 1) :
    Continuous fun u : ℝ ↦ ∑' m : ℕ, Real.exp (-u) * (u ^ m / (m.factorial : ℝ)) * a m := by
  refine continuous_iff_continuousAt.mpr fun x ↦ ?_
  set R : ℝ := |x| + 1 with hR
  have hcont : ContinuousOn
      (fun u : ℝ ↦ ∑' m : ℕ, Real.exp (-u) * (u ^ m / (m.factorial : ℝ)) * a m)
      (Ioo (-R) R) := by
    refine continuousOn_tsum
      (f := fun m u ↦ Real.exp (-u) * (u ^ m / (m.factorial : ℝ)) * a m)
      (u := fun m ↦ Real.exp R * (R ^ m / (m.factorial : ℝ)))
      (fun m ↦ ?_) ((Real.summable_pow_div_factorial R).mul_left (Real.exp R)) fun m u hu ↦ ?_
    · exact (by fun_prop :
        Continuous fun u : ℝ ↦ Real.exp (-u) * (u ^ m / (m.factorial : ℝ)) * a m).continuousOn
    · have hu' : |u| ≤ R := abs_le.mpr ⟨hu.1.le, hu.2.le⟩
      calc ‖Real.exp (-u) * (u ^ m / (m.factorial : ℝ)) * a m‖
          = Real.exp (-u) * (|u| ^ m / (m.factorial : ℝ)) * |a m| := by
            rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_div, abs_pow, Real.abs_exp,
              Nat.abs_cast]
        _ ≤ Real.exp R * (R ^ m / (m.factorial : ℝ)) * 1 := by
            gcongr <;> first | exact ha m | exact hu' | linarith [hu.1]
        _ = Real.exp R * (R ^ m / (m.factorial : ℝ)) := mul_one _
  exact hcont.continuousAt
    (Ioo_mem_nhds (by linarith [neg_abs_le x]) (by linarith [le_abs_self x]))

/-- **A Poisson mixture of a sequence tending to one tends to one as the mean grows.** -/
theorem tendsto_poissonMixture_atTop {a : ℕ → ℝ} (ha0 : ∀ m, 0 ≤ a m) (ha1 : ∀ m, a m ≤ 1)
    (hlim : Tendsto a atTop (𝓝 1)) :
    Tendsto (fun u : ℝ ↦ poissonMixture u.toNNReal a) atTop (𝓝 1) := by
  refine tendsto_order.2 ⟨fun b hb ↦ ?_, fun b hb ↦ Eventually.of_forall fun u ↦
    (poissonMixture_le_one ha0 ha1).trans_lt hb⟩
  set ε : ℝ := (1 - b) / 2 with hε
  have hεpos : 0 < ε := by
    rw [hε]
    linarith
  obtain ⟨M, hM⟩ := eventually_atTop.mp ((tendsto_order.1 hlim).1 (1 - ε) (by linarith))
  have hS : Tendsto (fun x : ℝ ↦ ∑ m ∈ Finset.range M, x ^ m * Real.exp (-x) / (m.factorial : ℝ))
      atTop (𝓝 0) := by
    have h := tendsto_finset_sum (Finset.range M) fun m _ ↦
      (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero m).div_const (m.factorial : ℝ)
    simpa using h
  have hlower : ∀ x : ℝ, 0 ≤ x →
      1 - ε - ∑ m ∈ Finset.range M, x ^ m * Real.exp (-x) / (m.factorial : ℝ)
        ≤ poissonMixture x.toNNReal a := by
    intro x hx
    have hcoe : ((x.toNNReal : NNReal) : ℝ) = x := Real.coe_toNNReal x hx
    have hfin : HasSum (fun m ↦ if m ∈ Finset.range M then poissonPMFReal x.toNNReal m else 0)
        (∑ m ∈ Finset.range M, poissonPMFReal x.toNNReal m) := by
      have h : HasSum (fun m ↦ if m ∈ Finset.range M then poissonPMFReal x.toNNReal m else 0)
          (∑ m ∈ Finset.range M,
            if m ∈ Finset.range M then poissonPMFReal x.toNNReal m else 0) :=
        hasSum_sum_of_ne_finset_zero fun m hm ↦ if_neg hm
      rwa [Finset.sum_congr rfl fun m hm ↦ if_pos hm] at h
    have hB := ((poissonPMFRealSum x.toNNReal).mul_left (1 - ε)).sub hfin
    have hrange : ∑ m ∈ Finset.range M, poissonPMFReal x.toNNReal m
        = ∑ m ∈ Finset.range M, x ^ m * Real.exp (-x) / (m.factorial : ℝ) :=
      Finset.sum_congr rfl fun m _ ↦ by
        rw [poissonPMFReal, hcoe]
        ring
    have hterm : ∀ m, (1 - ε) * poissonPMFReal x.toNNReal m
        - (if m ∈ Finset.range M then poissonPMFReal x.toNNReal m else 0)
        ≤ poissonPMFReal x.toNNReal m * a m := by
      intro m
      have hπ : 0 ≤ poissonPMFReal x.toNNReal m := poissonPMFReal_nonneg
      by_cases hm : m ∈ Finset.range M
      · rw [if_pos hm]
        nlinarith [ha0 m]
      · rw [if_neg hm, sub_zero]
        have hMm : M ≤ m := by
          rw [Finset.mem_range, not_lt] at hm
          exact hm
        nlinarith [hM m hMm]
    have hle := hasSum_le hterm hB (summable_poissonPMFReal_mul ha0 ha1 x.toNNReal).hasSum
    rw [hrange, mul_one] at hle
    exact hle
  filter_upwards [(tendsto_order.1 hS).2 ε hεpos, eventually_ge_atTop 0] with x hx1 hx2
  have := hlower x hx2
  linarith [hε]

/-! ### The uniformized report connects eventually

The probability `a_m` that the report of the uniformized genealogy is connected after `m` steps
is nondecreasing, because the report only coarsens, and tends to one: each step lowers the expected
excess `K - 1` of blocks by the scaled death rate `binom(K, 2)/n² ≥ (K - 1)/n²`. -/

/-- **One uniformized Kingman step lowers the expected excess of blocks by the scaled death
rate.** -/
theorem sum_kingmanStep_mul_blocks_sub_one {n : ℕ} (ξ : ER n) :
    ∑ ξ', kingmanStep n ξ ξ' * ((blocks ξ' : ℝ) - 1)
      = ((blocks ξ : ℝ) - 1) - deathRate (blocks ξ) / (n : ℝ) ^ 2 := by
  have hpoint : ∀ ξ' : ER n, kingmanStep n ξ ξ' * ((blocks ξ' : ℝ) - 1)
      = (if Covers ξ ξ' then 1 / (n : ℝ) ^ 2 * ((blocks ξ : ℝ) - 2) else 0)
        + (if ξ' = ξ then
            (1 - deathRate (blocks ξ) / (n : ℝ) ^ 2) * ((blocks ξ : ℝ) - 1) else 0) := by
    intro ξ'
    unfold kingmanStep
    by_cases h : Covers ξ ξ'
    · have hne : ξ' ≠ ξ := fun heq ↦ by
        have hb := h.2
        rw [heq] at hb
        omega
      have hb : (blocks ξ' : ℝ) + 1 = blocks ξ := by exact_mod_cast h.2
      rw [if_pos h, if_pos h, if_neg hne, if_neg hne, ← hb]
      ring
    · rw [if_neg h, if_neg h]
      by_cases he : ξ' = ξ
      · rw [if_pos he, if_pos he, he]
        ring
      · rw [if_neg he, if_neg he]
        ring
  rw [Finset.sum_congr rfl fun ξ' _ ↦ hpoint ξ', Finset.sum_add_distrib, sum_ite_covers,
    Finset.sum_ite_eq']
  simp only [Finset.mem_univ, if_true]
  ring

/-- The uniformized Kingman law is a probability vector. -/
theorem sum_kingmanLaw (n m : ℕ) : ∑ ξ, kingmanLaw n m ξ = 1 := by
  rw [kingmanLaw, sum_skeletonLaw sum_kingmanStep m]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem kingmanLaw_nonneg (n m : ℕ) (ξ : ER n) : 0 ≤ kingmanLaw n m ξ :=
  skeletonLaw_nonneg (fun a b ↦ kingmanStep_nonneg (blocks_le_card a) b)
    (fun _ ↦ by split_ifs <;> norm_num) m ξ

/-- **The expected excess of blocks decays geometrically.** -/
theorem sum_kingmanLaw_mul_blocks_sub_one_le {n : ℕ} (hn : 0 < n) (m : ℕ) :
    ∑ ξ, kingmanLaw n m ξ * ((blocks ξ : ℝ) - 1)
      ≤ (1 - 1 / (n : ℝ) ^ 2) ^ m * ((n : ℝ) - 1) := by
  haveI : NeZero n := ⟨hn.ne'⟩
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hq : 0 ≤ 1 - 1 / (n : ℝ) ^ 2 := by
    rw [sub_nonneg, div_le_one (by positivity)]
    nlinarith
  induction m with
  | zero =>
    have hpt : ∀ ξ : ER n, (if ξ = ⊥ then (1 : ℝ) else 0) * ((blocks ξ : ℝ) - 1)
        = if ξ = ⊥ then ((blocks ξ : ℝ) - 1) else 0 := fun ξ ↦ by
      split_ifs <;> simp
    have hb0 : blocks (⊥ : ER n) = n := blocks_bot n
    have h0 : ∑ ξ, kingmanLaw n 0 ξ * ((blocks ξ : ℝ) - 1) = (n : ℝ) - 1 := by
      show ∑ ξ : ER n, (if ξ = ⊥ then (1 : ℝ) else 0) * ((blocks ξ : ℝ) - 1) = _
      rw [Finset.sum_congr rfl fun ξ _ ↦ hpt ξ, Finset.sum_ite_eq']
      simp only [Finset.mem_univ, if_true]
      rw [hb0]
    rw [h0, pow_zero, one_mul]
  | succ m ih =>
    have h1 := sum_skeletonLaw_succ (kingmanStep n) (fun ξ ↦ if ξ = ⊥ then 1 else 0) m
      Finset.univ fun ξ ↦ (blocks ξ : ℝ) - 1
    have hstep : ∑ ξ, kingmanLaw n (m + 1) ξ * ((blocks ξ : ℝ) - 1)
        = ∑ ξ, kingmanLaw n m ξ
            * (((blocks ξ : ℝ) - 1) - deathRate (blocks ξ) / (n : ℝ) ^ 2) := by
      rw [kingmanLaw, h1]
      refine Finset.sum_congr rfl fun ξ _ ↦ ?_
      rw [sum_kingmanStep_mul_blocks_sub_one]
      rfl
    rw [hstep]
    have hpoint : ∀ ξ : ER n,
        kingmanLaw n m ξ * (((blocks ξ : ℝ) - 1) - deathRate (blocks ξ) / (n : ℝ) ^ 2)
          ≤ (1 - 1 / (n : ℝ) ^ 2) * (kingmanLaw n m ξ * ((blocks ξ : ℝ) - 1)) := by
      intro ξ
      have hlaw := kingmanLaw_nonneg n m ξ
      have hd : (blocks ξ : ℝ) - 1 ≤ deathRate (blocks ξ) := by
        unfold deathRate Descent.Core.pairCount
        rcases Nat.lt_or_ge (blocks ξ) 2 with h2 | h2
        · have hone : blocks ξ = 1 := by
            have := blocks_pos ξ
            omega
          rw [hone]
          norm_num
        · have h2' : (2 : ℝ) ≤ blocks ξ := by exact_mod_cast h2
          nlinarith
      have hdiv : ((blocks ξ : ℝ) - 1) / (n : ℝ) ^ 2 ≤ deathRate (blocks ξ) / (n : ℝ) ^ 2 :=
        div_le_div_of_nonneg_right hd (by positivity)
      calc kingmanLaw n m ξ * (((blocks ξ : ℝ) - 1) - deathRate (blocks ξ) / (n : ℝ) ^ 2)
          ≤ kingmanLaw n m ξ * (((blocks ξ : ℝ) - 1) - ((blocks ξ : ℝ) - 1) / (n : ℝ) ^ 2) :=
            mul_le_mul_of_nonneg_left (by linarith) hlaw
        _ = (1 - 1 / (n : ℝ) ^ 2) * (kingmanLaw n m ξ * ((blocks ξ : ℝ) - 1)) := by ring
    calc ∑ ξ, kingmanLaw n m ξ * (((blocks ξ : ℝ) - 1) - deathRate (blocks ξ) / (n : ℝ) ^ 2)
        ≤ ∑ ξ, (1 - 1 / (n : ℝ) ^ 2) * (kingmanLaw n m ξ * ((blocks ξ : ℝ) - 1)) :=
          Finset.sum_le_sum fun ξ _ ↦ hpoint ξ
      _ = (1 - 1 / (n : ℝ) ^ 2) * ∑ ξ, kingmanLaw n m ξ * ((blocks ξ : ℝ) - 1) := by
          rw [Finset.mul_sum]
      _ ≤ (1 - 1 / (n : ℝ) ^ 2) * ((1 - 1 / (n : ℝ) ^ 2) ^ m * ((n : ℝ) - 1)) :=
          mul_le_mul_of_nonneg_left ih hq
      _ = (1 - 1 / (n : ℝ) ^ 2) ^ (m + 1) * ((n : ℝ) - 1) := by ring

/-- The report is connected with probability at least one minus the expected excess of blocks. -/
theorem one_sub_sum_kingmanLaw_mul_blocks_le {n : ℕ} (hn : 0 < n) (s : Fin n → Fin n) (m : ℕ) :
    1 - ∑ ξ, kingmanLaw n m ξ * ((blocks ξ : ℝ) - 1)
      ≤ ∑ ξ, kingmanLaw n m ξ * (if observed s ξ = ⊤ then 1 else 0) := by
  haveI : NeZero n := ⟨hn.ne'⟩
  have hrewrite : 1 - ∑ ξ, kingmanLaw n m ξ * ((blocks ξ : ℝ) - 1)
      = ∑ ξ, (kingmanLaw n m ξ - kingmanLaw n m ξ * ((blocks ξ : ℝ) - 1)) := by
    rw [Finset.sum_sub_distrib, sum_kingmanLaw]
  rw [hrewrite]
  refine Finset.sum_le_sum fun ξ _ ↦ ?_
  have hlaw := kingmanLaw_nonneg n m ξ
  by_cases hone : blocks ξ = 1
  · have htop : observed s ξ = ⊤ := by
      rw [(blocks_eq_one_iff ξ).mp hone]
      exact top_sup_eq _
    rw [if_pos htop, hone]
    simp
  · have h2 : (2 : ℝ) ≤ blocks ξ := by
      have := blocks_pos ξ
      exact_mod_cast (by omega : 2 ≤ blocks ξ)
    have hite : (0 : ℝ) ≤ if observed s ξ = ⊤ then 1 else 0 := by split_ifs <;> norm_num
    nlinarith

/-- **The report only coarsens**: its connection probability after `m` steps is nondecreasing. -/
theorem sum_kingmanLaw_mul_top_le_succ {n : ℕ} (s : Fin n → Fin n) (m : ℕ) :
    ∑ ξ, kingmanLaw n m ξ * (if observed s ξ = ⊤ then 1 else 0)
      ≤ ∑ ξ, kingmanLaw n (m + 1) ξ * (if observed s ξ = ⊤ then 1 else 0) := by
  have h1 := sum_skeletonLaw_succ (kingmanStep n) (fun ξ ↦ if ξ = ⊥ then 1 else 0) m
    Finset.univ fun ξ ↦ if observed s ξ = ⊤ then (1 : ℝ) else 0
  rw [kingmanLaw, kingmanLaw, h1]
  refine Finset.sum_le_sum fun ξ _ ↦ mul_le_mul_of_nonneg_left ?_ (kingmanLaw_nonneg n m ξ)
  by_cases htop : observed s ξ = ⊤
  · rw [if_pos htop]
    have hall : ∀ ξ', kingmanStep n ξ ξ' * (if observed s ξ' = ⊤ then (1 : ℝ) else 0)
        = kingmanStep n ξ ξ' := by
      intro ξ'
      by_cases hz : kingmanStep n ξ ξ' = 0
      · rw [hz, zero_mul]
      · have hle : ξ ≤ ξ' := by
          unfold kingmanStep at hz
          by_cases hc : Covers ξ ξ'
          · exact hc.1
          · by_cases he : ξ' = ξ
            · exact le_of_eq he.symm
            · simp [hc, he] at hz
        rw [if_pos (eq_top_iff.mpr ((le_of_eq htop.symm).trans (observed_mono s hle))), mul_one]
    rw [Finset.sum_congr rfl fun ξ' _ ↦ hall ξ', sum_kingmanStep]
  · rw [if_neg htop]
    exact Finset.sum_nonneg fun ξ' _ ↦
      mul_nonneg (kingmanStep_nonneg (blocks_le_card ξ) ξ') (by split_ifs <;> norm_num)

/-- **The uniformized report connects eventually.** -/
theorem tendsto_sum_kingmanLaw_mul_top {n : ℕ} (hn : 0 < n) (s : Fin n → Fin n) :
    Tendsto (fun m ↦ ∑ ξ, kingmanLaw n m ξ * (if observed s ξ = ⊤ then 1 else 0)) atTop
      (𝓝 1) := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hq0 : 0 ≤ 1 - 1 / (n : ℝ) ^ 2 := by
    rw [sub_nonneg, div_le_one (by positivity)]
    nlinarith
  have hq1 : 1 - 1 / (n : ℝ) ^ 2 < 1 := by
    have : 0 < 1 / (n : ℝ) ^ 2 := by positivity
    linarith
  have hgeo : Tendsto (fun m : ℕ ↦ 1 - (1 - 1 / (n : ℝ) ^ 2) ^ m * ((n : ℝ) - 1)) atTop
      (𝓝 1) := by
    have h := (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).mul_const ((n : ℝ) - 1)
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hgeo tendsto_const_nhds (fun m ↦ ?_)
    fun m ↦ ?_
  · exact (sub_le_sub_left (sum_kingmanLaw_mul_blocks_sub_one_le hn m) 1).trans
      (one_sub_sum_kingmanLaw_mul_blocks_le hn s m)
  · exact (sum_mul_ite_mem_unit (kingmanLaw_nonneg n m) (sum_kingmanLaw n m) _).2

end

end Descent.Pangenome.GraphCoalescent
