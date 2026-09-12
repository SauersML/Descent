/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.GraphCoalescent.MultiplicativeConnectionConvergence
import Descent.Pangenome.GraphCoalescent.MultiplicativePerturbation

assert_below Descent.PopGen Descent.Spectral Descent.Blindness Descent.Conditionals
assert_below Descent.Portability Descent.Decision Descent.Program

/-!
# The limit law of the scaled connection clock, and path functionals under (F2)

Theorem F of the hidden-clock note ends with the limit `n² τ_{q_n} ⇒ T_p`, where `T_p` is the
connection time of the random graph on the `w` fibers whose edge `{i, j}` switches on at rate
`p_i p_j`.  `Descent.Pangenome.GraphCoalescent.MultiplicativeConnectionConvergence` proves that
the distribution functions converge at every scaled time
(`tendsto_reportConnectionProbability`).  This file proves, from (F4)'s Möbius law
`connectionProbability_eq_mobius_sum`, that the limit `u ↦ Pr(T_p ≤ u)` is the continuous
distribution function of a finite positive time, so that the convergence is convergence in law;
and it reduces every bounded functional of the skeleton path to the path total variation of (F1)
and (F2).

## Main results

- `crossingRate_eq_pairProductSum`: `κ_σ = Σ_{C<D} p(C) p(D)`, the note's two readings of the
  crossing rate, for any masses.
- `continuous_connectionProbability_time`: `u ↦ Pr(T_p ≤ u)` is continuous.
- `connectionProbability_mem_Icc`: it is a probability at nonnegative times and masses.
- `connectionProbability_zero`: with two fibers or more nothing is connected at time zero.
- `tendsto_connectionProbability_atTop`: when every `p_i > 0`, `Pr(T_p ≤ u) → 1`, so `T_p` is
  finite.  `crossingRate_top` and `crossingRate_pos` are the two cases of the Möbius sum.
- `abs_sum_mul_sub_sum_mul_le`, `abs_poissonMixture_sub_le`: a total variation bound bounds the
  difference of every functional with values in `[0, 1]`, also after Poisson mixing.
- `abs_poissonMixture_report_sub_spread_le`: **(F2) for every path functional**.  For masses `p`
  on the fibers and any functional of the skeleton path with values in `[0, 1]`, the graph's
  report and `Z_p` differ by at most `min {1, U²/(4n) + U ‖p^(n) - p‖₁}`.

## Scope

Time is the rate-one uniformization in scaled time of `MultiplicativeCoupling`.  Monotonicity of
`u ↦ Pr(T_p ≤ u)` is not proved here.  The identification of the Poisson-mixed connection
probability of `Z_p` with masses `p` with `Pr(T_p ≤ U)` is proved in
`MultiplicativeConnectionConvergence` only at the empirical masses `p^(n)`, so the rate
`U ‖p^(n) - p‖₁` is stated here for path functionals and not yet for `Pr(T_p ≤ U)` itself.

## Empirical status

None.  Every declaration here is a finite sum over the partitions of a finite set, a Poisson
series, or a limit of such sums.  The fiber masses are parameters, not estimates from any
dataset.
-/

namespace Descent.Pangenome.GraphCoalescent

open Coalescent Finset Filter ProbabilityTheory

open scoped Classical Topology

noncomputable section

/-! ### The crossing rate as a pair sum -/

/-- Twice the pair sum of the block masses is the mass of the ordered pairs in different
blocks. -/
theorem two_mul_pairProductSum_blockMass {w : ℕ} (p : Fin w → ℝ) (σ : ER w) :
    2 * pairProductSum (blockMass p σ) = ∑ i, ∑ j, if σ.r i j then 0 else p i * p j := by
  have hsq : ∀ C : Quotient σ, blockMass p σ C ^ 2
      = ∑ i ∈ univ.filter (fun i ↦ Quotient.mk σ i = C),
          ∑ j, if σ.r i j then p i * p j else 0 := by
    intro C
    rw [sq, blockMass, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    rw [← Finset.sum_filter]
    refine Finset.sum_congr (Finset.filter_congr fun j _ ↦ ?_) fun j _ ↦ rfl
    rw [← (Finset.mem_filter.mp hi).2]
    exact ⟨fun h ↦ σ.iseqv.symm (Quotient.exact h), fun h ↦ Quotient.sound (σ.iseqv.symm h)⟩
  rw [two_mul_pairProductSum, sum_blockMass]
  simp only [hsq]
  rw [Finset.sum_fiberwise univ (Quotient.mk σ) fun i ↦ ∑ j, if σ.r i j then p i * p j else 0,
    sq, Finset.sum_mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun j _ ↦ by split_ifs <;> ring

/-- **`κ_σ = Σ_{C<D} p(C) p(D)`**: the total rate of the edges crossing `σ` is the pair sum of
the masses of its blocks. -/
theorem crossingRate_eq_pairProductSum {w : ℕ} (p : Fin w → ℝ) (σ : ER w) :
    crossingRate p σ = pairProductSum (blockMass p σ) := by
  have h := (two_mul_crossingRate p σ).trans (two_mul_pairProductSum_blockMass p σ).symm
  linarith

/-! ### The limit law -/

/-- `Pr(T_p ≤ u)` is continuous in the time `u`. -/
theorem continuous_connectionProbability_time {w : ℕ} [NeZero w] (p : Fin w → ℝ) :
    Continuous fun u ↦ connectionProbability p u := by
  simp only [connectionProbability_eq_mobius_sum]
  exact continuous_finset_sum _ fun σ _ ↦ continuous_const.mul
    (Real.continuous_exp.comp ((continuous_id.mul continuous_const).neg))

/-- The top partition is crossed by no edge. -/
theorem crossingRate_top {w : ℕ} (p : Fin w → ℝ) : crossingRate p ⊤ = 0 :=
  Finset.sum_eq_zero fun _ _ ↦ if_pos trivial

/-- **`Pr(T_p ≤ u)` is a probability** at nonnegative times and masses. -/
theorem connectionProbability_mem_Icc {w : ℕ} {p : Fin w → ℝ} (hp : ∀ i, 0 ≤ p i) {u : ℝ}
    (hu : 0 ≤ u) : connectionProbability p u ∈ Set.Icc 0 1 := by
  have hmass : ∀ G, 0 ≤ configMass p u G := fun G ↦ Finset.prod_nonneg fun e _ ↦ by
    have hrate : 0 ≤ u * pairRate p e := mul_nonneg hu (mul_nonneg (hp _) (hp _))
    have hexp : Real.exp (-(u * pairRate p e)) ≤ 1 := by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr (by linarith)
    split_ifs
    · linarith
    · exact (Real.exp_pos _).le
  have htotal := sum_configMass_componentPartition_le p u ⊤
  rw [crossingRate_top, mul_zero, neg_zero, Real.exp_zero] at htotal
  refine Set.mem_Icc.mpr
    ⟨Finset.sum_nonneg fun G _ ↦ mul_nonneg (hmass G) (by split_ifs <;> norm_num), ?_⟩
  calc ∑ G, configMass p u G * (if componentPartition G = ⊤ then (1 : ℝ) else 0)
      ≤ ∑ G, configMass p u G * (if componentPartition G ≤ ⊤ then (1 : ℝ) else 0) :=
        Finset.sum_le_sum fun G _ ↦ mul_le_mul_of_nonneg_left
          (by rw [if_pos le_top]; split_ifs <;> norm_num) (hmass G)
    _ = 1 := htotal

/-- **With two fibers or more, nothing is connected at time zero.** -/
theorem connectionProbability_zero {w : ℕ} [NeZero w] (hw : 2 ≤ w) (p : Fin w → ℝ) :
    connectionProbability p 0 = 0 := by
  have hbot : (⊥ : ER w) ≠ ⊤ := by
    intro h
    have hb : blocks (⊥ : ER w) = w := blocks_bot w
    have ht : blocks (⊤ : ER w) = 1 := blocks_top w
    rw [h, ht] at hb
    omega
  have h := sum_topMobius_blocks_ge (⊥ : ER w)
  rw [if_neg hbot, Finset.filter_true_of_mem fun σ _ ↦ bot_le] at h
  rw [connectionProbability_eq_mobius_sum]
  simp only [zero_mul, neg_zero, Real.exp_zero, mul_one]
  exact_mod_cast h

/-- A partition other than the top is crossed at a positive rate when every fiber has positive
mass. -/
theorem crossingRate_pos {w : ℕ} {p : Fin w → ℝ} (hp : ∀ i, 0 < p i) {σ : ER w} (hσ : σ ≠ ⊤) :
    0 < crossingRate p σ := by
  obtain ⟨i, j, hij⟩ : ∃ i j, ¬ σ i j := by
    by_contra h
    push_neg at h
    exact hσ (Setoid.ext fun i j ↦ ⟨fun _ ↦ trivial, fun _ ↦ h i j⟩)
  have hne : i ≠ j := fun h ↦ hij (by rw [h])
  have hnonneg : ∀ e ∈ (univ : Finset (FiberPair w)),
      0 ≤ if σ e.1.1 e.1.2 then 0 else pairRate p e := fun e _ ↦ by
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (hp _).le (hp _).le
  rcases lt_or_gt_of_ne hne with h | h
  · refine lt_of_lt_of_le ?_ (Finset.single_le_sum hnonneg (Finset.mem_univ ⟨(i, j), h⟩))
    show 0 < if σ i j then 0 else p i * p j
    rw [if_neg hij]
    exact mul_pos (hp i) (hp j)
  · refine lt_of_lt_of_le ?_ (Finset.single_le_sum hnonneg (Finset.mem_univ ⟨(j, i), h⟩))
    show 0 < if σ j i then 0 else p j * p i
    rw [if_neg fun h' ↦ hij (σ.iseqv.symm h')]
    exact mul_pos (hp j) (hp i)

/-- **When every fiber has positive mass, `T_p` is finite**: `Pr(T_p ≤ u) → 1` as `u → ∞`. -/
theorem tendsto_connectionProbability_atTop {w : ℕ} [NeZero w] {p : Fin w → ℝ}
    (hp : ∀ i, 0 < p i) : Tendsto (fun u ↦ connectionProbability p u) atTop (𝓝 1) := by
  have hterm : ∀ σ : ER w, Tendsto
      (fun u ↦ (topMobius (blocks σ) : ℝ) * Real.exp (-(u * crossingRate p σ))) atTop
      (𝓝 (if σ = ⊤ then 1 else 0)) := by
    intro σ
    by_cases hσ : σ = ⊤
    · subst hσ
      have hmob : (topMobius (blocks (⊤ : ER w)) : ℝ) = 1 := by
        rw [blocks_top]
        norm_num [topMobius]
      simp only [crossingRate_top, hmob, mul_zero, neg_zero, Real.exp_zero, mul_one, if_true]
      exact tendsto_const_nhds
    · rw [if_neg hσ]
      have h := (Real.tendsto_exp_neg_atTop_nhds_zero.comp
        (tendsto_id.atTop_mul_const (crossingRate_pos hp hσ))).const_mul
          (topMobius (blocks σ) : ℝ)
      rw [mul_zero] at h
      exact h
  have hsum := tendsto_finset_sum (univ : Finset (ER w)) fun σ _ ↦ hterm σ
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true] at hsum
  refine hsum.congr fun u ↦ ?_
  rw [connectionProbability_eq_mobius_sum]

/-! ### Path functionals under a total variation bound -/

/-- **A total variation bound bounds every functional with values in `[0, 1]`**: two laws of
equal total mass integrate such a functional to within half their summed absolute
difference. -/
theorem abs_sum_mul_sub_sum_mul_le {X : Type*} [Fintype X] {μ ν : X → ℝ}
    (hμν : ∑ x, μ x = ∑ x, ν x) {g : X → ℝ} (hg : ∀ x, 0 ≤ g x ∧ g x ≤ 1) :
    |∑ x, μ x * g x - ∑ x, ν x * g x| ≤ 1 / 2 * ∑ x, |μ x - ν x| := by
  have hsplit : ∑ x, μ x * g x - ∑ x, ν x * g x
      = ∑ x, (μ x - ν x) * (g x - 1 / 2) + (∑ x, μ x - ∑ x, ν x) * (1 / 2) := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, Finset.sum_mul,
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun x _ ↦ by ring
  rw [hsplit, hμν, sub_self, zero_mul, add_zero, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun x _ ↦ ?_)
  rw [abs_mul]
  have hhalf : |g x - 1 / 2| ≤ 1 / 2 :=
    abs_le.mpr ⟨by linarith [(hg x).1], by linarith [(hg x).2]⟩
  calc |μ x - ν x| * |g x - 1 / 2| ≤ |μ x - ν x| * (1 / 2) :=
        mul_le_mul_of_nonneg_left hhalf (abs_nonneg _)
    _ = 1 / 2 * |μ x - ν x| := mul_comm _ _

/-- A law of total mass one integrates a functional with values in `[0, 1]` to a number in
`[0, 1]`. -/
theorem sum_mul_mem_unit {X : Type*} [Fintype X] {μ g : X → ℝ} (hμ : ∀ x, 0 ≤ μ x)
    (hμ1 : ∑ x, μ x = 1) (hg : ∀ x, 0 ≤ g x ∧ g x ≤ 1) :
    0 ≤ ∑ x, μ x * g x ∧ ∑ x, μ x * g x ≤ 1 := by
  refine ⟨Finset.sum_nonneg fun x _ ↦ mul_nonneg (hμ x) (hg x).1, ?_⟩
  rw [← hμ1]
  exact Finset.sum_le_sum fun x _ ↦
    (mul_le_mul_of_nonneg_left (hg x).2 (hμ x)).trans_eq (mul_one _)

/-- **Poisson mixing preserves a termwise bound**: if `|a m - b m| ≤ c m` for sequences with
values in `[0, 1]`, their Poisson mixtures differ by at most the mixture of `c`. -/
theorem abs_poissonMixture_sub_le {U : NNReal} {a b c : ℕ → ℝ} (ha : ∀ m, 0 ≤ a m ∧ a m ≤ 1)
    (hb : ∀ m, 0 ≤ b m ∧ b m ≤ 1) (hc : ∀ m, 0 ≤ c m ∧ c m ≤ 1)
    (habc : ∀ m, |a m - b m| ≤ c m) :
    |poissonMixture U a - poissonMixture U b| ≤ poissonMixture U c := by
  have hsum : ∀ d : ℕ → ℝ, (∀ m, 0 ≤ d m ∧ d m ≤ 1) →
      HasSum (fun m ↦ poissonPMFReal U m * d m) (poissonMixture U d) := fun d hd ↦
    (Summable.of_nonneg_of_le (fun m ↦ mul_nonneg poissonPMFReal_nonneg (hd m).1)
      (fun m ↦ (mul_le_mul_of_nonneg_left (hd m).2 poissonPMFReal_nonneg).trans_eq (mul_one _))
      (poissonPMFRealSum U).summable).hasSum
  have hA := hsum a ha
  have hB := hsum b hb
  have hC := hsum c hc
  rw [abs_sub_le_iff]
  constructor
  · refine hasSum_le (fun m ↦ ?_) (hA.sub hB) hC
    rw [← mul_sub]
    exact mul_le_mul_of_nonneg_left ((le_abs_self _).trans (habc m)) poissonPMFReal_nonneg
  · refine hasSum_le (fun m ↦ ?_) (hB.sub hA) hC
    rw [← mul_sub]
    refine mul_le_mul_of_nonneg_left ((le_abs_self _).trans ?_) poissonPMFReal_nonneg
    rw [abs_sub_comm]
    exact habc m

/-- **(F2) for every path functional.**  For a mass vector `p` on the fibers and any family of
functionals `g m` of the `m`-step skeleton path with values in `[0, 1]`, run at the rings of a
Poisson clock of mean `U`, the graph's report and `Z_p` from the interface give values within
`min {1, U²/(4n) + U ∑_F |c_F/n - p_F|}`.  The event that the path is connected at its last
step is one such functional.

Assumes: `0 < n`, `p` is nonnegative with total at most one, and every `g m` takes values in
`[0, 1]`. -/
theorem abs_poissonMixture_report_sub_spread_le {n : ℕ} (hn : 0 < n) (s : Fin n → Fin n)
    {p : Quotient (graphKer s) → ℝ} (hp : ∀ F, 0 ≤ p F) (hptotal : ∑ F, p F ≤ 1) (U : NNReal)
    (g : ∀ m : ℕ, (Fin (m + 1) → ER n) → ℝ) (hg : ∀ m y, 0 ≤ g m y ∧ g m y ≤ 1) :
    |poissonMixture U (fun m ↦ ∑ y, reportPathLaw s m y * g m y)
        - poissonMixture U (fun m ↦ ∑ y, massPathLaw s (spreadMass s p) m y * g m y)|
      ≤ min 1 ((U : ℝ) ^ 2 / (4 * n) + U * ∑ F, |(fiberSize s F : ℝ) / n - p F|) := by
  have hmass := spreadMass_nonneg s hp
  have htotal : ∑ i, spreadMass s p i ≤ 1 := (sum_spreadMass s p).trans_le hptotal
  refine le_trans (abs_poissonMixture_sub_le (fun m ↦ ?_) (fun m ↦ ?_) (fun m ↦ ?_)
    fun m ↦ abs_sum_mul_sub_sum_mul_le ?_ (hg m))
    (report_spread_poissonTotalVariation_le hn s hp hptotal U)
  · exact sum_mul_mem_unit (reportPathLaw_nonneg s m) (sum_reportPathLaw s m) (hg m)
  · exact sum_mul_mem_unit (massPathLaw_nonneg s hmass htotal m) (sum_massPathLaw s _ m) (hg m)
  · exact ⟨mul_nonneg (by norm_num) (Finset.sum_nonneg fun _ _ ↦ abs_nonneg _),
      report_mass_pathTotalVariation_le_one s hmass htotal m⟩
  · exact (sum_reportPathLaw s m).trans (sum_massPathLaw s _ m).symm

/-! ### `Z` with any masses, below a partition -/

/-- Two masses of components, expanded over their individuals and weighted by whether the two
individuals lie in different blocks of `σ`. -/
theorem ite_blockMap_mul_blockMass_eq {n : ℕ} (mass : Fin n → ℝ) {ζ σ : ER n} (h : ζ ≤ σ)
    (C D : Quotient ζ) :
    (if blockMap h C = blockMap h D then 0 else blockMass mass ζ C * blockMass mass ζ D)
      = ∑ x ∈ univ.filter (fun x ↦ Quotient.mk ζ x = C),
          ∑ y ∈ univ.filter (fun y ↦ Quotient.mk ζ y = D),
            (if σ.r x y then 0 else mass x * mass y) := by
  unfold blockMass
  rw [Finset.sum_mul_sum]
  by_cases hφ : blockMap h C = blockMap h D
  · rw [if_pos hφ]
    symm
    refine Finset.sum_eq_zero fun x hx ↦ Finset.sum_eq_zero fun y hy ↦ if_pos ?_
    have e1 : Quotient.mk σ x = blockMap h C := by
      rw [← (Finset.mem_filter.mp hx).2]
      rfl
    have e2 : Quotient.mk σ y = blockMap h D := by
      rw [← (Finset.mem_filter.mp hy).2]
      rfl
    exact Quotient.exact (e1.trans (hφ.trans e2.symm))
  · rw [if_neg hφ]
    refine Finset.sum_congr rfl fun x hx ↦ Finset.sum_congr rfl fun y hy ↦ (if_neg ?_).symm
    intro hr
    apply hφ
    rw [← (Finset.mem_filter.mp hx).2, ← (Finset.mem_filter.mp hy).2]
    exact Quotient.sound hr

/-- **The merges of `Z` that leave the partitions below `σ` carry the crossing mass of `σ`**,
for any masses and whatever the state `ζ ≤ σ` they start from. -/
theorem two_mul_sum_crossing_eq_mass {n : ℕ} (mass : Fin n → ℝ) {ζ σ : ER n} (h : ζ ≤ σ) :
    2 * ∑ t ∈ (univ : Finset (Quotient ζ)).powersetCard 2,
        (if mergePair ζ t ≤ σ then 0 else ∏ C ∈ t, blockMass mass ζ C)
      = ∑ x, ∑ y, if σ.r x y then 0 else mass x * mass y := by
  calc 2 * ∑ t ∈ (univ : Finset (Quotient ζ)).powersetCard 2,
        (if mergePair ζ t ≤ σ then 0 else ∏ C ∈ t, blockMass mass ζ C)
      = ∑ C, ∑ D, if C ≠ D then (if mergePair ζ {C, D} ≤ σ then 0
          else ∏ E ∈ ({C, D} : Finset (Quotient ζ)), blockMass mass ζ E) else 0 :=
        two_mul_sum_powersetCard_two_eq _
    _ = ∑ C, ∑ D, if blockMap h C = blockMap h D then 0
          else blockMass mass ζ C * blockMass mass ζ D := by
        refine Finset.sum_congr rfl fun C _ ↦ Finset.sum_congr rfl fun D _ ↦ ?_
        by_cases hCD : C = D
        · rw [if_neg (not_not.mpr hCD), if_pos (congrArg (blockMap h) hCD)]
        · rw [if_pos hCD, mergePair_pair ζ hCD, Finset.prod_pair hCD]
          by_cases hφ : blockMap h C = blockMap h D
          · rw [if_pos ((merge_le_iff_blockMap_eq h hCD).mpr hφ), if_pos hφ]
          · rw [if_neg fun hle ↦ hφ ((merge_le_iff_blockMap_eq h hCD).mp hle), if_neg hφ]
    _ = ∑ C, ∑ D, ∑ x ∈ univ.filter (fun x ↦ Quotient.mk ζ x = C),
          ∑ y ∈ univ.filter (fun y ↦ Quotient.mk ζ y = D),
            (if σ.r x y then 0 else mass x * mass y) :=
        Finset.sum_congr rfl fun C _ ↦ Finset.sum_congr rfl fun D _ ↦
          ite_blockMap_mul_blockMass_eq mass h C D
    _ = ∑ x, ∑ y, if σ.r x y then 0 else mass x * mass y := by
        have hinner : ∀ C : Quotient ζ, ∑ D, ∑ x ∈ univ.filter (fun x ↦ Quotient.mk ζ x = C),
            ∑ y ∈ univ.filter (fun y ↦ Quotient.mk ζ y = D),
              (if σ.r x y then 0 else mass x * mass y)
            = ∑ x ∈ univ.filter (fun x ↦ Quotient.mk ζ x = C),
                ∑ y, (if σ.r x y then 0 else mass x * mass y) := by
          intro C
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun x _ ↦ Finset.sum_fiberwise univ (Quotient.mk ζ)
            fun y ↦ if σ.r x y then 0 else mass x * mass y
        rw [Finset.sum_congr rfl fun C _ ↦ hinner C]
        exact Finset.sum_fiberwise univ (Quotient.mk ζ)
          fun x ↦ ∑ y, if σ.r x y then 0 else mass x * mass y

/-- **`Z` with masses `mass` leaves the partitions below `σ` at the constant rate `κ_σ`**: from
any `ζ ≤ σ` it stays below `σ` with probability `1 - Σ_{B<B'} p(B) p(B')` over the blocks of
`σ`. -/
theorem sum_filter_le_massStep {n : ℕ} (mass : Fin n → ℝ) {ζ σ : ER n} (h : ζ ≤ σ) :
    ∑ ζ' ∈ univ.filter (· ≤ σ), massStep mass ζ ζ'
      = 1 - pairProductSum (blockMass mass σ) := by
  have hA : ∑ ζ' ∈ univ.filter (· ≤ σ), ∑ t ∈ (univ.powersetCard 2).filter
        (fun t ↦ mergePair ζ t = ζ'), ∏ C ∈ t, blockMass mass ζ C
      = ∑ t ∈ (univ : Finset (Quotient ζ)).powersetCard 2,
          if mergePair ζ t ≤ σ then ∏ C ∈ t, blockMass mass ζ C else 0 := by
    rw [Finset.sum_filter]
    have hpoint : ∀ ζ' : ER n, (if ζ' ≤ σ then ∑ t ∈ (univ.powersetCard 2).filter
        (fun t ↦ mergePair ζ t = ζ'), ∏ C ∈ t, blockMass mass ζ C else 0)
        = ∑ t ∈ (univ.powersetCard 2).filter (fun t ↦ mergePair ζ t = ζ'),
            if mergePair ζ t ≤ σ then ∏ C ∈ t, blockMass mass ζ C else 0 := by
      intro ζ'
      by_cases hle : ζ' ≤ σ
      · rw [if_pos hle]
        exact Finset.sum_congr rfl fun t ht ↦ by rw [(Finset.mem_filter.mp ht).2, if_pos hle]
      · rw [if_neg hle]
        exact (Finset.sum_eq_zero fun t ht ↦ by
          rw [(Finset.mem_filter.mp ht).2, if_neg hle]).symm
    rw [Finset.sum_congr rfl fun ζ' _ ↦ hpoint ζ']
    exact Finset.sum_fiberwise _ (mergePair ζ) _
  have hsplit : ∑ t ∈ (univ : Finset (Quotient ζ)).powersetCard 2,
        (if mergePair ζ t ≤ σ then ∏ C ∈ t, blockMass mass ζ C else 0)
      + ∑ t ∈ (univ : Finset (Quotient ζ)).powersetCard 2,
        (if mergePair ζ t ≤ σ then 0 else ∏ C ∈ t, blockMass mass ζ C)
      = pairProductSum (blockMass mass ζ) := by
    rw [← Finset.sum_add_distrib, pairProductSum]
    exact Finset.sum_congr rfl fun t _ ↦ by split_ifs <;> simp
  have hcross := two_mul_sum_crossing_eq_mass mass h
  rw [← two_mul_pairProductSum_blockMass mass σ] at hcross
  have hhold : ∑ ζ' ∈ univ.filter (· ≤ σ),
      (if ζ' = ζ then 1 - pairProductSum (blockMass mass ζ) else 0)
      = 1 - pairProductSum (blockMass mass ζ) := by
    rw [Finset.sum_ite_eq']
    have hmem : ζ ∈ univ.filter (· ≤ σ) := Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩
    exact if_pos hmem
  simp only [massStep]
  rw [Finset.sum_add_distrib, hA, hhold]
  linarith

/-- From a state not below `σ`, `Z` never reaches a state below `σ`. -/
theorem sum_filter_le_massStep_of_not_le {n : ℕ} (mass : Fin n → ℝ) {ζ σ : ER n}
    (h : ¬ ζ ≤ σ) : ∑ ζ' ∈ univ.filter (· ≤ σ), massStep mass ζ ζ' = 0 := by
  refine Finset.sum_eq_zero fun ζ' hζ' ↦ ?_
  have hle := (Finset.mem_filter.mp hζ').2
  unfold massStep
  rw [Finset.sum_eq_zero fun t ht ↦ absurd
    (((Finset.mem_filter.mp ht).2 ▸ le_mergePair ζ t).trans hle) h, zero_add]
  exact if_neg fun (heq : ζ' = ζ) ↦ h (heq ▸ hle)

/-- **The uniformized law of `Z` with masses `mass` after `m` steps from the interface.**

Empirical status: NOT AN EMPIRICAL CLAIM.  A power of a finite kernel applied to a point mass. -/
def massLaw {n : ℕ} (s : Fin n → Fin n) (mass : Fin n → ℝ) (m : ℕ) : ER n → ℝ :=
  skeletonLaw (massStep mass) (fun ζ ↦ if ζ = graphKer s then 1 else 0) m

/-- **`Z` is below `σ` after `m` steps with probability `(1 - κ_σ)^m`**, when the interface is
below `σ`, and never otherwise. -/
theorem sum_filter_le_massLaw {n : ℕ} (s : Fin n → Fin n) (mass : Fin n → ℝ) (σ : ER n)
    (m : ℕ) :
    ∑ ζ ∈ univ.filter (· ≤ σ), massLaw s mass m ζ
      = if graphKer s ≤ σ then (1 - pairProductSum (blockMass mass σ)) ^ m else 0 := by
  induction m with
  | zero =>
    simp only [massLaw, skeletonLaw, pow_zero]
    rw [Finset.sum_ite_eq']
    by_cases hq : graphKer s ≤ σ
    · have hmem : graphKer s ∈ univ.filter (· ≤ σ) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hq⟩
      rw [if_pos hmem, if_pos hq]
    · have hmem : graphKer s ∉ univ.filter (· ≤ σ) := fun hmem ↦
        hq (Finset.mem_filter.mp hmem).2
      rw [if_neg hmem, if_neg hq]
  | succ m ih =>
    have h1 := sum_skeletonLaw_succ (massStep mass)
      (fun ζ ↦ if ζ = graphKer s then 1 else 0) m (univ.filter (· ≤ σ)) fun _ ↦ 1
    simp only [mul_one] at h1
    have hpoint : ∀ ζ : ER n, massLaw s mass m ζ
        * ∑ ζ' ∈ univ.filter (· ≤ σ), massStep mass ζ ζ'
        = (if ζ ≤ σ then massLaw s mass m ζ else 0)
          * (1 - pairProductSum (blockMass mass σ)) := by
      intro ζ
      by_cases hζ : ζ ≤ σ
      · rw [if_pos hζ, sum_filter_le_massStep mass hζ]
      · rw [if_neg hζ, sum_filter_le_massStep_of_not_le mass hζ, mul_zero, zero_mul]
    have hstep : ∑ ζ ∈ univ.filter (· ≤ σ), massLaw s mass (m + 1) ζ
        = ∑ ζ, massLaw s mass m ζ
          * ∑ ζ' ∈ univ.filter (· ≤ σ), massStep mass ζ ζ' := h1
    rw [hstep, Finset.sum_congr rfl fun ζ _ ↦ hpoint ζ, ← Finset.sum_mul, ← Finset.sum_filter,
      ih]
    split_ifs <;> ring

/-- **The connection probability of `Z` after `m` steps**, as a Möbius sum over the partitions
above the interface. -/
theorem sum_massLaw_mul_top {n : ℕ} [NeZero n] (s : Fin n → Fin n) (mass : Fin n → ℝ)
    (m : ℕ) :
    ∑ ζ, massLaw s mass m ζ * (if ζ = ⊤ then 1 else 0)
      = ∑ σ, (topMobius (blocks σ) : ℝ)
          * (if graphKer s ≤ σ then (1 - pairProductSum (blockMass mass σ)) ^ m else 0) := by
  calc ∑ ζ, massLaw s mass m ζ * (if ζ = ⊤ then 1 else 0)
      = ∑ ζ, massLaw s mass m ζ
          * ∑ σ : ER n, (topMobius (blocks σ) : ℝ) * (if ζ ≤ σ then 1 else 0) := by
        simp only [sum_topMobius_ite_le]
    _ = ∑ σ : ER n, (topMobius (blocks σ) : ℝ)
          * ∑ ζ ∈ univ.filter (· ≤ σ), massLaw s mass m ζ := by
        simp only [Finset.mul_sum, Finset.sum_filter]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun σ _ ↦ Finset.sum_congr rfl fun ζ _ ↦ by
          split_ifs <;> ring
    _ = _ := by
        simp only [sum_filter_le_massLaw]

/-- **`Z` with masses `mass` is connected at scaled time `U` with the Möbius probability**
`Σ_{σ ≥ q} (-1)^{|σ|-1} (|σ|-1)! e^{-U κ_σ}`, `κ_σ` the pair sum of the block masses. -/
theorem hasSum_poissonPMFReal_mul_massTop {n : ℕ} [NeZero n] (s : Fin n → Fin n)
    (mass : Fin n → ℝ) (U : NNReal) :
    HasSum (fun m ↦ poissonPMFReal U m * ∑ ζ, massLaw s mass m ζ * (if ζ = ⊤ then 1 else 0))
      (∑ σ, (topMobius (blocks σ) : ℝ)
        * (if graphKer s ≤ σ then Real.exp (-((U : ℝ) * pairProductSum (blockMass mass σ)))
          else 0)) := by
  simp only [sum_massLaw_mul_top, Finset.mul_sum]
  refine hasSum_sum fun σ _ ↦ ?_
  by_cases hq : graphKer s ≤ σ
  · simp only [if_pos hq]
    have h := (hasSum_poissonPMFReal_mul_pow U
      (1 - pairProductSum (blockMass mass σ))).mul_left (topMobius (blocks σ) : ℝ)
    rw [sub_sub_cancel] at h
    convert h using 1
    funext m
    ring
  · simp only [if_neg hq, mul_zero]
    exact hasSum_zero

end

end Descent.Pangenome.GraphCoalescent
