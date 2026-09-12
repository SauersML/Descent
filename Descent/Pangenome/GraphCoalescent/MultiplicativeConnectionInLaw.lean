/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.GraphCoalescent.MultiplicativeConnectionConvergence
import Descent.Pangenome.GraphCoalescent.MultiplicativeConnectionPerturbation
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

/-! ### The law of `T_p`

`Pr(T_p ≤ u)` is the Poisson mixture, at mean `u`, of the probabilities that the skeleton of `Z_p`
on the labels is connected, so it is nondecreasing; it is a finite sum of exponentials in `u`, so
it is continuous; and with every `p_i > 0` every partition other than the top has a positive
crossing rate, so it tends to one. -/

/-- `Z` only coarsens, pointwise. -/
theorem massStep_eq_zero_of_not_le {n : ℕ} (mass : Fin n → ℝ) {ζ ζ' : ER n} (h : ¬ ζ ≤ ζ') :
    massStep mass ζ ζ' = 0 := by
  unfold massStep
  rw [Finset.sum_eq_zero fun t ht ↦ absurd
    ((Finset.mem_filter.mp ht).2 ▸ le_mergePair ζ t) h, zero_add]
  exact if_neg fun (heq : ζ' = ζ) ↦ h (le_of_eq heq.symm)

theorem sum_massLaw {n : ℕ} (s : Fin n → Fin n) (mass : Fin n → ℝ) (m : ℕ) :
    ∑ ζ, massLaw s mass m ζ = 1 := by
  rw [massLaw, sum_skeletonLaw (sum_massStep mass) m]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem massLaw_nonneg {n : ℕ} (s : Fin n → Fin n) {mass : Fin n → ℝ} (hmass : ∀ i, 0 ≤ mass i)
    (htotal : ∑ i, mass i ≤ 1) (m : ℕ) (ζ : ER n) : 0 ≤ massLaw s mass m ζ :=
  skeletonLaw_nonneg (massStep_nonneg hmass htotal) (fun _ ↦ by split_ifs <;> norm_num) m ζ

/-- **`Z` only coarsens**: its connection probability after `m` steps is nondecreasing. -/
theorem sum_massLaw_mul_top_le_succ {n : ℕ} (s : Fin n → Fin n) {mass : Fin n → ℝ}
    (hmass : ∀ i, 0 ≤ mass i) (htotal : ∑ i, mass i ≤ 1) (m : ℕ) :
    ∑ ζ, massLaw s mass m ζ * (if ζ = ⊤ then 1 else 0)
      ≤ ∑ ζ, massLaw s mass (m + 1) ζ * (if ζ = ⊤ then 1 else 0) := by
  have h1 := sum_skeletonLaw_succ (massStep mass) (fun ζ ↦ if ζ = graphKer s then 1 else 0) m
    Finset.univ fun ζ ↦ if ζ = ⊤ then (1 : ℝ) else 0
  rw [massLaw, massLaw, h1]
  refine Finset.sum_le_sum fun ζ _ ↦
    mul_le_mul_of_nonneg_left ?_ (massLaw_nonneg s hmass htotal m ζ)
  by_cases htop : ζ = ⊤
  · rw [if_pos htop]
    have hall : ∀ ζ',
        massStep mass ζ ζ' * (if ζ' = ⊤ then (1 : ℝ) else 0) = massStep mass ζ ζ' := by
      intro ζ'
      by_cases hz : ζ' = ⊤
      · rw [if_pos hz, mul_one]
      · rw [if_neg hz, mul_zero, massStep_eq_zero_of_not_le mass
          fun hle ↦ hz (eq_top_iff.mpr ((le_of_eq htop.symm).trans hle))]
    rw [Finset.sum_congr rfl fun ζ' _ ↦ hall ζ', sum_massStep]
  · rw [if_neg htop]
    exact Finset.sum_nonneg fun ζ' _ ↦
      mul_nonneg (massStep_nonneg hmass htotal ζ ζ') (by split_ifs <;> norm_num)

/-- **`Pr(T_p ≤ U)` is a Poisson mixture of the connection probabilities of `Z_p`'s skeleton on the
labels.** -/
theorem connectionProbability_eq_poissonMixture {w : ℕ} [NeZero w] (p : Fin w → ℝ)
    (U : NNReal) :
    connectionProbability p U
      = poissonMixture U fun m ↦ ∑ ζ, massLaw id p m ζ * (if ζ = ⊤ then 1 else 0) := by
  rw [poissonMixture, (hasSum_poissonPMFReal_mul_massTop id p U).tsum_eq,
    connectionProbability_eq_mobius_sum]
  refine Finset.sum_congr rfl fun σ _ ↦ ?_
  have hκ : pairProductSum (blockMass p σ) = crossingRate p σ := by
    have h1 := two_mul_pairProductSum_blockMass_crossing p σ
    have h2 := two_mul_crossingRate p σ
    linarith
  rw [if_pos (graphKer_le_of_injective Function.injective_id σ), hκ]

/-- **The distribution function of `T_p`**: the random-graph connection probability, and zero at
negative times.

Empirical status: NOT AN EMPIRICAL CLAIM.  A finite sum of exponentials, extended by zero. -/
def connectionTimeCDF {w : ℕ} (p : Fin w → ℝ) (u : ℝ) : ℝ :=
  if u < 0 then 0 else connectionProbability p u

theorem monotone_connectionTimeCDF {w : ℕ} [NeZero w] {p : Fin w → ℝ} (hp0 : ∀ i, 0 ≤ p i)
    (hp1 : ∑ i, p i ≤ 1) : Monotone (connectionTimeCDF p) := by
  set b : ℕ → ℝ := fun m ↦ ∑ ζ, massLaw id p m ζ * (if ζ = ⊤ then 1 else 0) with hb
  have hunit : ∀ m, 0 ≤ b m ∧ b m ≤ 1 := fun m ↦
    sum_mul_ite_mem_unit (massLaw_nonneg id hp0 hp1 m) (sum_massLaw id p m) _
  have hmono : Monotone b := monotone_nat_of_le_succ (sum_massLaw_mul_top_le_succ id hp0 hp1)
  have heq : ∀ u : ℝ, 0 ≤ u → connectionProbability p u = poissonMixture u.toNNReal b := by
    intro u hu
    have h := connectionProbability_eq_poissonMixture p u.toNNReal
    rwa [Real.coe_toNNReal u hu] at h
  intro u v huv
  unfold connectionTimeCDF
  by_cases hv : v < 0
  · rw [if_pos (lt_of_le_of_lt huv hv), if_pos hv]
  · rw [if_neg hv, heq v (not_lt.mp hv)]
    by_cases hu : u < 0
    · rw [if_pos hu]
      exact tsum_nonneg fun m ↦ mul_nonneg poissonPMFReal_nonneg (hunit m).1
    · rw [if_neg hu, heq u (not_lt.mp hu)]
      exact monotone_poissonMixture (fun m ↦ (hunit m).1) (fun m ↦ (hunit m).2) hmono
        (Real.toNNReal_le_toNNReal huv)

theorem continuous_connectionProbability_in_time {w : ℕ} [NeZero w] (p : Fin w → ℝ) :
    Continuous fun u : ℝ ↦ connectionProbability p u := by
  simp only [connectionProbability_eq_mobius_sum]
  exact continuous_finset_sum _ fun σ _ ↦ continuous_const.mul
    (Real.continuous_exp.comp ((continuous_id.mul continuous_const).neg))

theorem connectionTimeCDF_rightContinuous {w : ℕ} [NeZero w] (p : Fin w → ℝ) (x : ℝ) :
    ContinuousWithinAt (connectionTimeCDF p) (Ici x) x := by
  by_cases hx : x < 0
  · have hev : connectionTimeCDF p =ᶠ[𝓝 x] fun _ ↦ 0 := by
      filter_upwards [Iio_mem_nhds hx] with y hy
      exact if_pos hy
    exact (continuousAt_const.congr hev.symm).continuousWithinAt
  · have hx' : 0 ≤ x := not_lt.mp hx
    refine ((continuous_connectionProbability_in_time p).continuousAt.continuousWithinAt).congr
      (fun y hy ↦ ?_) ?_
    · exact if_neg (not_lt.mpr (hx'.trans hy))
    · exact if_neg hx

theorem tendsto_connectionTimeCDF_atBot {w : ℕ} (p : Fin w → ℝ) :
    Tendsto (connectionTimeCDF p) atBot (𝓝 0) :=
  tendsto_const_nhds.congr' (by
    filter_upwards [eventually_lt_atBot 0] with y hy
    exact (if_pos hy).symm)

/-- With every fiber of positive mass, a partition other than the top has a positive crossing
rate. -/
theorem crossingRate_pos_of_ne_top {w : ℕ} {p : Fin w → ℝ} (hp : ∀ i, 0 < p i) {σ : ER w}
    (hσ : σ ≠ ⊤) : 0 < crossingRate p σ := by
  obtain ⟨i, j, hij⟩ : ∃ i j, ¬ σ.r i j := by
    by_contra hall
    push_neg at hall
    exact hσ (Setoid.ext fun a b ↦ ⟨fun _ ↦ trivial, fun _ ↦ hall a b⟩)
  have hne : i ≠ j := fun h ↦ hij (by rw [← h]; exact σ.iseqv.refl i)
  have hnonneg : ∀ e ∈ (Finset.univ : Finset (FiberPair w)),
      0 ≤ (if σ e.1.1 e.1.2 then (0 : ℝ) else pairRate p e) := fun e _ ↦ by
    split_ifs
    · exact le_rfl
    · exact (mul_pos (hp _) (hp _)).le
  unfold crossingRate
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · refine Finset.sum_pos' hnonneg ⟨⟨(i, j), hlt⟩, Finset.mem_univ _, ?_⟩
    show 0 < (if σ i j then (0 : ℝ) else pairRate p ⟨(i, j), hlt⟩)
    rw [if_neg hij]
    exact mul_pos (hp i) (hp j)
  · refine Finset.sum_pos' hnonneg ⟨⟨(j, i), hlt⟩, Finset.mem_univ _, ?_⟩
    show 0 < (if σ j i then (0 : ℝ) else pairRate p ⟨(j, i), hlt⟩)
    rw [if_neg fun h ↦ hij (σ.iseqv.symm h)]
    exact mul_pos (hp j) (hp i)

theorem tendsto_connectionTimeCDF_atTop {w : ℕ} [NeZero w] {p : Fin w → ℝ}
    (hp : ∀ i, 0 < p i) : Tendsto (connectionTimeCDF p) atTop (𝓝 1) := by
  have hterm : ∀ σ : ER w, Tendsto (fun u : ℝ ↦
      (topMobius (blocks σ) : ℝ) * Real.exp (-(u * crossingRate p σ))) atTop
      (𝓝 (if σ = ⊤ then 1 else 0)) := by
    intro σ
    by_cases htop : σ = ⊤
    · rw [if_pos htop]
      have hκ : crossingRate p σ = 0 := by
        rw [htop]
        unfold crossingRate
        exact Finset.sum_eq_zero fun e _ ↦ if_pos trivial
      have hμ : (topMobius (blocks σ) : ℝ) = 1 := by
        have hb : blocks σ = 1 := by
          rw [htop]
          exact blocks_top w
        rw [hb]
        norm_num [topMobius]
      simp only [hκ, mul_zero, neg_zero, Real.exp_zero, mul_one, hμ]
      exact tendsto_const_nhds
    · rw [if_neg htop]
      have h := (Real.tendsto_exp_neg_atTop_nhds_zero.comp
        (tendsto_id.atTop_mul_const (crossingRate_pos_of_ne_top hp htop))).const_mul
        (topMobius (blocks σ) : ℝ)
      simpa using h
  have hsum := tendsto_finset_sum (Finset.univ : Finset (ER w)) fun σ _ ↦ hterm σ
  rw [Finset.sum_ite_eq'] at hsum
  simp only [Finset.mem_univ, if_true] at hsum
  refine hsum.congr' ?_
  filter_upwards [eventually_ge_atTop 0] with u hu
  rw [connectionTimeCDF, if_neg (not_lt.mpr hu), connectionProbability_eq_mobius_sum]
  exact Finset.sum_congr rfl fun _ _ ↦ rfl

/-- **The distribution function of `T_p`, as a Stieltjes function.**

Empirical status: NOT AN EMPIRICAL CLAIM.  A distribution function. -/
def connectionTimeStieltjes {w : ℕ} [NeZero w] (p : Fin w → ℝ) (hp0 : ∀ i, 0 ≤ p i)
    (hp1 : ∑ i, p i ≤ 1) : StieltjesFunction where
  toFun := connectionTimeCDF p
  mono' := monotone_connectionTimeCDF hp0 hp1
  right_continuous' := connectionTimeCDF_rightContinuous p

/-- **The law of `T_p`**, the connection time of the random graph on the fibers with independent
exponential edge clocks of rates `p_i p_j`.

Empirical status: NOT AN EMPIRICAL CLAIM.  The probability measure of a distribution function. -/
def randomGraphConnectionLaw {w : ℕ} [NeZero w] (p : Fin w → ℝ) (hp : ∀ i, 0 < p i)
    (hp1 : ∑ i, p i ≤ 1) : ProbabilityMeasure ℝ :=
  ⟨(connectionTimeStieltjes p (fun i ↦ (hp i).le) hp1).measure, ⟨by
    rw [StieltjesFunction.measure_univ _ (tendsto_connectionTimeCDF_atBot p)
      (tendsto_connectionTimeCDF_atTop hp), sub_zero, ENNReal.ofReal_one]⟩⟩

/-- The law of `T_p` has the random-graph connection probability as its distribution function. -/
theorem cdf_randomGraphConnectionLaw {w : ℕ} [NeZero w] (p : Fin w → ℝ) (hp : ∀ i, 0 < p i)
    (hp1 : ∑ i, p i ≤ 1) (x : ℝ) :
    cdf (randomGraphConnectionLaw p hp hp1 : Measure ℝ) x = connectionTimeCDF p x := by
  show cdf (connectionTimeStieltjes p (fun i ↦ (hp i).le) hp1).measure x = _
  rw [cdf_measure_stieltjesFunction _ (tendsto_connectionTimeCDF_atBot p)
    (tendsto_connectionTimeCDF_atTop hp)]
  rfl

/-! ### The law of the uniformized scaled connection time -/

/-- **The distribution function of the scaled connection time of the uniformized report**: the
probability that the report is connected at scaled time `u`, and zero at negative times.

Empirical status: NOT AN EMPIRICAL CLAIM.  A Poisson mixture, extended by zero. -/
def reportConnectionCDF {n : ℕ} (s : Fin n → Fin n) (u : ℝ) : ℝ :=
  if u < 0 then 0 else reportConnectionProbability s u.toNNReal

theorem sum_kingmanLaw_mul_top_mem_unit {n : ℕ} (s : Fin n → Fin n) (m : ℕ) :
    0 ≤ ∑ ξ, kingmanLaw n m ξ * (if observed s ξ = ⊤ then 1 else 0)
      ∧ ∑ ξ, kingmanLaw n m ξ * (if observed s ξ = ⊤ then 1 else 0) ≤ 1 :=
  sum_mul_ite_mem_unit (kingmanLaw_nonneg n m) (sum_kingmanLaw n m) _

theorem monotone_reportConnectionCDF {n : ℕ} (s : Fin n → Fin n) :
    Monotone (reportConnectionCDF s) := by
  have hunit := sum_kingmanLaw_mul_top_mem_unit s
  have hmono : Monotone fun m ↦ ∑ ξ, kingmanLaw n m ξ * (if observed s ξ = ⊤ then 1 else 0) :=
    monotone_nat_of_le_succ (sum_kingmanLaw_mul_top_le_succ s)
  intro u v huv
  unfold reportConnectionCDF reportConnectionProbability
  by_cases hv : v < 0
  · rw [if_pos (lt_of_le_of_lt huv hv), if_pos hv]
  · rw [if_neg hv]
    by_cases hu : u < 0
    · rw [if_pos hu]
      exact tsum_nonneg fun m ↦ mul_nonneg poissonPMFReal_nonneg (hunit m).1
    · rw [if_neg hu]
      exact monotone_poissonMixture (fun m ↦ (hunit m).1) (fun m ↦ (hunit m).2) hmono
        (Real.toNNReal_le_toNNReal huv)

theorem reportConnectionCDF_rightContinuous {n : ℕ} (s : Fin n → Fin n) (x : ℝ) :
    ContinuousWithinAt (reportConnectionCDF s) (Ici x) x := by
  have hunit := sum_kingmanLaw_mul_top_mem_unit s
  have habs : ∀ m, |∑ ξ, kingmanLaw n m ξ * (if observed s ξ = ⊤ then 1 else 0)| ≤ 1 :=
    fun m ↦ abs_le.mpr ⟨by linarith [(hunit m).1], (hunit m).2⟩
  by_cases hx : x < 0
  · have hev : reportConnectionCDF s =ᶠ[𝓝 x] fun _ ↦ 0 := by
      filter_upwards [Iio_mem_nhds hx] with y hy
      exact if_pos hy
    exact (continuousAt_const.congr hev.symm).continuousWithinAt
  · have hx' : 0 ≤ x := not_lt.mp hx
    refine ((continuous_poissonSeries habs).continuousAt.continuousWithinAt).congr
      (fun y hy ↦ ?_) ?_
    · rw [reportConnectionCDF, if_neg (not_lt.mpr (hx'.trans hy)), reportConnectionProbability,
        poissonMixture_toNNReal (hx'.trans hy)]
    · rw [reportConnectionCDF, if_neg hx, reportConnectionProbability, poissonMixture_toNNReal hx']

theorem tendsto_reportConnectionCDF_atBot {n : ℕ} (s : Fin n → Fin n) :
    Tendsto (reportConnectionCDF s) atBot (𝓝 0) :=
  tendsto_const_nhds.congr' (by
    filter_upwards [eventually_lt_atBot 0] with y hy
    exact (if_pos hy).symm)

theorem tendsto_reportConnectionCDF_atTop {n : ℕ} (s : Fin n → Fin n) :
    Tendsto (reportConnectionCDF s) atTop (𝓝 1) := by
  have hunit := sum_kingmanLaw_mul_top_mem_unit s
  have hlim : Tendsto (fun m ↦ ∑ ξ, kingmanLaw n m ξ * (if observed s ξ = ⊤ then 1 else 0))
      atTop (𝓝 1) := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have hone : ∀ m, ∑ ξ, kingmanLaw 0 m ξ * (if observed s ξ = ⊤ then 1 else 0) = 1 := by
        intro m
        have htop : ∀ ξ : ER 0, observed s ξ = ⊤ := fun ξ ↦
          Setoid.ext fun a _ ↦ Fin.elim0 a
        simp only [htop, if_true, mul_one]
        exact sum_kingmanLaw 0 m
      simp only [hone]
      exact tendsto_const_nhds
    · exact tendsto_sum_kingmanLaw_mul_top hn s
  refine (tendsto_poissonMixture_atTop (fun m ↦ (hunit m).1) (fun m ↦ (hunit m).2) hlim).congr' ?_
  filter_upwards [eventually_ge_atTop 0] with u hu
  rw [reportConnectionCDF, if_neg (not_lt.mpr hu)]
  rfl

/-- **The distribution function of the uniformized scaled connection time, as a Stieltjes
function.**

Empirical status: NOT AN EMPIRICAL CLAIM.  A distribution function. -/
def reportConnectionStieltjes {n : ℕ} (s : Fin n → Fin n) : StieltjesFunction where
  toFun := reportConnectionCDF s
  mono' := monotone_reportConnectionCDF s
  right_continuous' := reportConnectionCDF_rightContinuous s

/-- **The law of the scaled connection time `n² τ_q` of the uniformized report.**

Empirical status: NOT AN EMPIRICAL CLAIM.  The probability measure of a distribution function. -/
def reportConnectionLaw {n : ℕ} (s : Fin n → Fin n) : ProbabilityMeasure ℝ :=
  ⟨(reportConnectionStieltjes s).measure, ⟨by
    rw [StieltjesFunction.measure_univ _ (tendsto_reportConnectionCDF_atBot s)
      (tendsto_reportConnectionCDF_atTop s), sub_zero, ENNReal.ofReal_one]⟩⟩

theorem cdf_reportConnectionLaw {n : ℕ} (s : Fin n → Fin n) (x : ℝ) :
    cdf (reportConnectionLaw s : Measure ℝ) x = reportConnectionCDF s x := by
  show cdf (reportConnectionStieltjes s).measure x = _
  rw [cdf_measure_stieltjesFunction _ (tendsto_reportConnectionCDF_atBot s)
    (tendsto_reportConnectionCDF_atTop s)]
  rfl

/-! ### (F3) in law -/

/-- **Theorem F, (F3), in law.**  Along panels of sizes `N k → ∞` carrying surjective labellings
into `w` fibers whose proportions converge to `p` with every `p_i > 0`, the laws of the scaled
connection times of the uniformized reports converge in the weak topology to the law of `T_p`. -/
theorem tendsto_reportConnectionLaw {w : ℕ} [NeZero w] {N : ℕ → ℕ}
    (hN : Tendsto N atTop atTop) (label : (k : ℕ) → Fin (N k) → Fin w)
    (hsurj : ∀ k, Function.Surjective (label k)) {p : Fin w → ℝ} (hp : ∀ i, 0 < p i)
    (hp1 : ∑ i, p i ≤ 1) (hlim : Tendsto (fun k ↦ fiberProportion (label k)) atTop (𝓝 p)) :
    Tendsto (fun k ↦ reportConnectionLaw (labelInterface (label k) (hsurj k))) atTop
      (𝓝 (randomGraphConnectionLaw p hp hp1)) := by
  refine tendsto_probabilityMeasure_of_tendsto_cdf fun x ↦ ?_
  simp only [cdf_reportConnectionLaw, cdf_randomGraphConnectionLaw]
  by_cases hx : x < 0
  · simp only [reportConnectionCDF, connectionTimeCDF, if_pos hx]
    exact tendsto_const_nhds
  · simp only [reportConnectionCDF, connectionTimeCDF, if_neg hx]
    have h := tendsto_reportConnectionProbability hN label hsurj hlim x.toNNReal
    rwa [Real.coe_toNNReal x (not_lt.mp hx)] at h

end

end Descent.Pangenome.GraphCoalescent
