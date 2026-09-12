/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.GraphCoalescent.MultiplicativeConnectionConvergence
import Descent.Pangenome.GraphCoalescent.MultiplicativeConnectionPerturbation
import Descent.Pangenome.GraphCoalescent.MultiplicativeConnectionInLaw

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
- `connectionProbability_mem_Icc`: it is a probability at nonnegative times and masses.
- `connectionProbability_zero`: with two fibers or more nothing is connected at time zero.
- `monotoneOn_connectionProbability`: it does not decrease in time, by superposing independent
  edge configurations (`sum_configMass_add_mul`).
- `tendsto_connectionProbability_atTop`: when every `p_i > 0`, `Pr(T_p ≤ u) → 1`, so `T_p` is
  finite, read off `MultiplicativeConnectionInLaw.tendsto_connectionTimeCDF_atTop`.
- `abs_sum_mul_sub_sum_mul_le`, `abs_poissonMixture_sub_le`: a total variation bound bounds the
  difference of every functional with values in `[0, 1]`, also after Poisson mixing.
- `abs_poissonMixture_report_sub_spread_le`: **(F2) for every path functional**.  For masses `p`
  on the fibers and any functional of the skeleton path with values in `[0, 1]`, the graph's
  report and `Z_p` differ by at most `min {1, U²/(4n) + U ‖p^(n) - p‖₁}`.
- `sum_topMobius_graphKer_spread_eq_connectionProbability`: with the masses `p` spread over the
  fibers of a labelling, the Möbius sum of `MultiplicativeConnectionPerturbation`'s
  `hasSum_poissonPMFReal_mul_massTop` is `Pr(T_p ≤ U)`.
- `abs_reportConnectionProbability_sub_le_min`: **(F3) with the rate of
  (F2)**, `|Pr(n² τ_q ≤ U) - Pr(T_p ≤ U)| ≤ min {1, U²/(4n) + U ‖p^(n) - p‖₁}`.

## Scope

Time is the rate-one uniformization in scaled time of `MultiplicativeCoupling`, and
`n² τ_q ≤ U` is read as the event that the uniformized report is connected at scaled time `U`.
The fibers are the classes of a surjective labelling, through
`MultiplicativeConnectionConvergence.labelInterface`.

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

/-- **`κ_σ = Σ_{C<D} p(C) p(D)`**: the total rate of the edges crossing `σ` is the pair sum of
the masses of its blocks. -/
theorem crossingRate_eq_pairProductSum {w : ℕ} (p : Fin w → ℝ) (σ : ER w) :
    crossingRate p σ = pairProductSum (blockMass p σ) := by
  have h := (two_mul_crossingRate p σ).trans (two_mul_pairProductSum_blockMass_crossing p σ).symm
  linarith

/-! ### The limit law -/

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

/-- **When every fiber has positive mass, `T_p` is finite**: `Pr(T_p ≤ u) → 1` as `u → ∞`.
`MultiplicativeConnectionInLaw.tendsto_connectionTimeCDF_atTop`, read at nonnegative times. -/
theorem tendsto_connectionProbability_atTop {w : ℕ} [NeZero w] {p : Fin w → ℝ}
    (hp : ∀ i, 0 < p i) : Tendsto (fun u ↦ connectionProbability p u) atTop (𝓝 1) := by
  refine (tendsto_connectionTimeCDF_atTop hp).congr' ?_
  filter_upwards [eventually_ge_atTop 0] with u hu
  rw [connectionTimeCDF, if_neg (not_lt.mpr hu)]

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

/-! ### Masses on the fiber labels -/

/-- **The fiber label of a component of a labelling's interface.**

Empirical status: NOT AN EMPIRICAL CLAIM.  A quotient map. -/
def fiberLabel {n w : ℕ} (label : Fin n → Fin w) (hsurj : Function.Surjective label) :
    Quotient (graphKer (labelInterface label hsurj)) → Fin w :=
  Quotient.lift label fun _ _ h ↦ Function.injective_surjInv hsurj (graphKer_rel_iff.mp h)

/-- Two individuals share a component of a labelling's interface exactly when they share a
label. -/
theorem mk_graphKer_labelInterface_eq_iff {n w : ℕ} (label : Fin n → Fin w)
    (hsurj : Function.Surjective label) (x y : Fin n) :
    Quotient.mk (graphKer (labelInterface label hsurj)) x
        = Quotient.mk (graphKer (labelInterface label hsurj)) y ↔ label x = label y :=
  ⟨fun h ↦ Function.injective_surjInv hsurj (graphKer_rel_iff.mp (Quotient.exact h)),
    fun h ↦ Quotient.sound (graphKer_rel_iff.mpr (congrArg (Function.surjInv hsurj) h))⟩

/-- The components of a labelling's interface are its labels. -/
theorem fiberLabel_bijective {n w : ℕ} (label : Fin n → Fin w)
    (hsurj : Function.Surjective label) : Function.Bijective (fiberLabel label hsurj) := by
  constructor
  · intro F G
    refine Quotient.inductionOn₂ F G fun x y h ↦ ?_
    exact (mk_graphKer_labelInterface_eq_iff label hsurj x y).mpr h
  · intro i
    exact ⟨Quotient.mk _ (Function.surjInv hsurj i), Function.surjInv_eq hsurj i⟩

/-- The size of a component of a labelling's interface is the count of its label. -/
theorem fiberSize_labelInterface {n w : ℕ} (label : Fin n → Fin w)
    (hsurj : Function.Surjective label) (F : Quotient (graphKer (labelInterface label hsurj))) :
    fiberSize (labelInterface label hsurj) F
      = (univ.filter fun x ↦ label x = fiberLabel label hsurj F).card := by
  refine Quotient.inductionOn F fun y ↦ ?_
  unfold fiberSize
  congr 1
  exact Finset.filter_congr fun x _ ↦ mk_graphKer_labelInterface_eq_iff label hsurj x y

/-- **Spread masses have the label marginal `p`**: a sum over the individuals, carrying the
masses `p` spread over their fibers, of a function of their label is a sum over the labels
weighted by `p`. -/
theorem sum_spreadMass_mul_comp {n w : ℕ} (label : Fin n → Fin w)
    (hsurj : Function.Surjective label) (p : Fin w → ℝ) (H : Fin w → ℝ) :
    ∑ x, spreadMass (labelInterface label hsurj) (fun F ↦ p (fiberLabel label hsurj F)) x
        * H (label x) = ∑ i, p i * H i := by
  rw [← Finset.sum_fiberwise univ label fun x ↦ spreadMass (labelInterface label hsurj)
    (fun F ↦ p (fiberLabel label hsurj F)) x * H (label x)]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have hpos : (0 : ℝ) < (univ.filter fun x ↦ label x = i).card := by
    obtain ⟨x, hx⟩ := hsurj i
    exact_mod_cast Finset.card_pos.mpr ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩⟩
  calc ∑ x ∈ univ.filter (fun x ↦ label x = i), spreadMass (labelInterface label hsurj)
        (fun F ↦ p (fiberLabel label hsurj F)) x * H (label x)
      = ∑ x ∈ univ.filter (fun x ↦ label x = i),
          p i / (univ.filter fun x ↦ label x = i).card * H i := by
        refine Finset.sum_congr rfl fun x hx ↦ ?_
        have hxi := (Finset.mem_filter.mp hx).2
        show p (fiberLabel label hsurj (Quotient.mk _ x))
            / (fiberSize (labelInterface label hsurj) (Quotient.mk _ x) : ℝ) * H (label x) = _
        rw [fiberSize_labelInterface label hsurj]
        show p (label x) / ((univ.filter fun y ↦ label y = label x).card : ℝ) * H (label x) = _
        rw [hxi]
    _ = p i * H i := by
        rw [Finset.sum_const, nsmul_eq_mul, ← mul_assoc, mul_comm _ (p i / _),
          div_mul_cancel₀ _ hpos.ne']

/-- **The crossing mass of a pulled-back partition is the crossing rate of the label
marginal**: if individual masses have label marginal `p`, the pair sum of the block masses of
`comap label τ` is `κ_τ` at `p`. -/
theorem pairProductSum_blockMass_comap_of_marginal {n w : ℕ} {label : Fin n → Fin w}
    {mass : Fin n → ℝ} {p : Fin w → ℝ}
    (hmarg : ∀ H : Fin w → ℝ, ∑ x, mass x * H (label x) = ∑ i, p i * H i) (τ : ER w) :
    pairProductSum (blockMass mass (Setoid.comap label τ)) = crossingRate p τ := by
  have hinner : ∀ x, ∑ y, (if (Setoid.comap label τ).r x y then 0 else mass x * mass y)
      = mass x * ∑ j, p j * (if τ.r (label x) j then 0 else 1) := by
    intro x
    rw [← hmarg fun j ↦ if τ.r (label x) j then 0 else 1, Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ ↦ ?_
    show (if τ.r (label x) (label y) then 0 else mass x * mass y)
      = mass x * (mass y * if τ.r (label x) (label y) then 0 else 1)
    split_ifs <;> ring
  have hsum : ∑ x, ∑ y, (if (Setoid.comap label τ).r x y then 0 else mass x * mass y)
      = ∑ i, ∑ j, if τ.r i j then 0 else p i * p j := by
    simp only [hinner]
    rw [hmarg fun i ↦ ∑ j, p j * (if τ.r i j then 0 else 1)]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ ↦ by split_ifs <;> ring
  have h := (two_mul_pairProductSum_blockMass_crossing mass (Setoid.comap label τ)).trans
    (hsum.trans (two_mul_crossingRate p τ).symm)
  linarith

/-- **The Möbius sum of `Z` with spread masses is (F4) at the fiber masses**: above a
labelling's interface, `Σ_{σ ≥ q} (-1)^{|σ|-1} (|σ|-1)! e^{-U κ_σ} = Pr(T_p ≤ U)`. -/
theorem sum_topMobius_graphKer_spread_eq_connectionProbability {n w : ℕ} [NeZero w]
    (label : Fin n → Fin w) (hsurj : Function.Surjective label) (p : Fin w → ℝ) (U : NNReal) :
    ∑ σ : ER n, (topMobius (blocks σ) : ℝ)
        * (if graphKer (labelInterface label hsurj) ≤ σ then Real.exp (-((U : ℝ)
            * pairProductSum (blockMass (spreadMass (labelInterface label hsurj)
              fun F ↦ p (fiberLabel label hsurj F)) σ))) else 0)
      = connectionProbability p U := by
  have hq : ∀ σ : ER n, graphKer (labelInterface label hsurj) ≤ σ ↔ Setoid.ker label ≤ σ :=
    fun σ ↦ by rw [graphKer_labelInterface]
  have hleft : ∑ σ : ER n, (topMobius (blocks σ) : ℝ)
        * (if graphKer (labelInterface label hsurj) ≤ σ then Real.exp (-((U : ℝ)
            * pairProductSum (blockMass (spreadMass (labelInterface label hsurj)
              fun F ↦ p (fiberLabel label hsurj F)) σ))) else 0)
      = ∑ σ ∈ univ.filter (Setoid.ker label ≤ ·), (topMobius (blocks σ) : ℝ)
          * Real.exp (-((U : ℝ) * pairProductSum (blockMass (spreadMass
            (labelInterface label hsurj) fun F ↦ p (fiberLabel label hsurj F)) σ))) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun σ _ ↦ ?_
    by_cases h : Setoid.ker label ≤ σ
    · rw [if_pos ((hq σ).mpr h), if_pos h]
    · rw [if_neg fun h' ↦ h ((hq σ).mp h'), if_neg h, mul_zero]
  rw [hleft, connectionProbability_eq_mobius_sum]
  symm
  refine Finset.sum_nbij (fun τ ↦ Setoid.comap label τ) (fun τ _ ↦ ?_) ?_ ?_ fun τ _ ↦ ?_
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ker_le_comap label τ⟩
  · exact (comap_label_injective hsurj).injOn
  · intro σ hσ
    have hle := (Finset.mem_filter.mp (Finset.mem_coe.mp hσ)).2
    exact ⟨Setoid.mapOfSurjective σ label hle hsurj, Finset.mem_coe.mpr (Finset.mem_univ _),
      comap_mapOfSurjective_label hsurj hle⟩
  · rw [blocks_comap_label hsurj τ,
      pairProductSum_blockMass_comap_of_marginal (sum_spreadMass_mul_comp label hsurj p) τ]

/-! ### (F3) with the rate of (F2) -/

/-- The report's skeleton path is connected at its last step with the probability that the
report of the Kingman law is connected. -/
theorem sum_reportPathLaw_mul_last_top {n : ℕ} (s : Fin n → Fin n) (m : ℕ) :
    ∑ y, reportPathLaw s m y * (if y (Fin.last m) = ⊤ then 1 else 0)
      = ∑ ξ, kingmanLaw n m ξ * (if observed s ξ = ⊤ then 1 else 0) := by
  calc ∑ y, reportPathLaw s m y * (if y (Fin.last m) = ⊤ then 1 else 0)
      = ∑ y, ∑ ω ∈ univ.filter (fun ω : Fin (m + 1) → ER n ↦ (fun k ↦ observed s (ω k)) = y),
          skeletonPathWeight (kingmanStep n) (fun ξ ↦ if ξ = ⊥ then 1 else 0) m ω
            * (if observed s (ω (Fin.last m)) = ⊤ then 1 else 0) := by
        refine Finset.sum_congr rfl fun y _ ↦ ?_
        rw [reportPathLaw, Finset.sum_mul]
        refine Finset.sum_congr rfl fun ω hω ↦ ?_
        obtain rfl := (Finset.mem_filter.mp hω).2
        rfl
    _ = ∑ ω : Fin (m + 1) → ER n,
          skeletonPathWeight (kingmanStep n) (fun ξ ↦ if ξ = ⊥ then 1 else 0) m ω
            * (if observed s (ω (Fin.last m)) = ⊤ then 1 else 0) :=
        Finset.sum_fiberwise univ (fun ω : Fin (m + 1) → ER n ↦ fun k ↦ observed s (ω k)) _
    _ = ∑ ξ, kingmanLaw n m ξ * (if observed s ξ = ⊤ then 1 else 0) :=
        sum_skeletonPathWeight_mul _ _ m fun ξ ↦ if observed s ξ = ⊤ then 1 else 0

/-- The skeleton path of `Z` is connected at its last step with the probability that its law is
connected. -/
theorem sum_massPathLaw_mul_last_top {n : ℕ} (s : Fin n → Fin n) (mass : Fin n → ℝ) (m : ℕ) :
    ∑ y, massPathLaw s mass m y * (if y (Fin.last m) = ⊤ then 1 else 0)
      = ∑ ζ, massLaw s mass m ζ * (if ζ = ⊤ then 1 else 0) :=
  sum_skeletonPathWeight_mul _ _ m fun ζ ↦ if ζ = ⊤ then 1 else 0

/-- **(F3) with the rate of (F2).**  For a labelling of `n` individuals by `w` fibers and a mass
vector `p` on the fibers, nonnegative with total at most one, the probability that the graph's
report is connected at scaled time `U` is within `min {1, U²/(4n) + U ‖p^(n) - p‖₁}` of
`Pr(T_p ≤ U)`, where `p^(n)` are the fiber proportions.

Assumes: `0 < n`, the labelling is surjective, and `p` is nonnegative with total at most
one. -/
theorem abs_reportConnectionProbability_sub_le_min {n w : ℕ} [NeZero w]
    (hn : 0 < n) (label : Fin n → Fin w) (hsurj : Function.Surjective label) {p : Fin w → ℝ}
    (hp : ∀ i, 0 ≤ p i) (hptotal : ∑ i, p i ≤ 1) (U : NNReal) :
    |reportConnectionProbability (labelInterface label hsurj) U - connectionProbability p U|
      ≤ min 1 ((U : ℝ) ^ 2 / (4 * n) + U * ∑ i, |fiberProportion label i - p i|) := by
  haveI : NeZero n := ⟨hn.ne'⟩
  have hbij := fiberLabel_bijective label hsurj
  have hP : ∀ F, 0 ≤ p (fiberLabel label hsurj F) := fun F ↦ hp _
  have hPtotal : ∑ F, p (fiberLabel label hsurj F) ≤ 1 := (hbij.sum_comp p).trans_le hptotal
  have h := abs_poissonMixture_report_sub_spread_le hn (labelInterface label hsurj)
    (p := fun F ↦ p (fiberLabel label hsurj F)) hP hPtotal U
    (fun m y ↦ if y (Fin.last m) = ⊤ then 1 else 0) fun m y ↦ by dsimp only; split_ifs <;> norm_num
  simp only [sum_reportPathLaw_mul_last_top, sum_massPathLaw_mul_last_top] at h
  have hZ : poissonMixture U (fun m ↦ ∑ ζ, massLaw (labelInterface label hsurj)
      (spreadMass (labelInterface label hsurj) fun F ↦ p (fiberLabel label hsurj F)) m ζ
        * (if ζ = ⊤ then 1 else 0)) = connectionProbability p U := by
    rw [← sum_topMobius_graphKer_spread_eq_connectionProbability label hsurj p U]
    exact (hasSum_poissonPMFReal_mul_massTop _ _ U).tsum_eq
  have hfib : ∑ F, |(fiberSize (labelInterface label hsurj) F : ℝ) / n
      - p (fiberLabel label hsurj F)| = ∑ i, |fiberProportion label i - p i| := by
    rw [← hbij.sum_comp fun i ↦ |fiberProportion label i - p i|]
    refine Finset.sum_congr rfl fun F _ ↦ ?_
    exact congrArg (fun c : ℕ ↦ |(c : ℝ) / n - p (fiberLabel label hsurj F)|)
      (fiberSize_labelInterface label hsurj F)
  rw [hZ, hfib] at h
  exact h

/-! ### Monotonicity in time, by superposition -/

/-- **The probability of one edge's state at time `v`**: present with probability
`1 - e^{-v p_i p_j}`, absent with the rest.

Empirical status: NOT AN EMPIRICAL CLAIM.  A Bernoulli mass function. -/
def edgeMass {w : ℕ} (p : Fin w → ℝ) (v : ℝ) (e : FiberPair w) (b : Bool) : ℝ :=
  if b then 1 - Real.exp (-(v * pairRate p e)) else Real.exp (-(v * pairRate p e))

/-- A configuration's mass is the product of its edges' masses. -/
theorem configMass_eq_prod_edgeMass {w : ℕ} (p : Fin w → ℝ) (v : ℝ) (G : FiberPair w → Bool) :
    configMass p v G = ∏ e, edgeMass p v e (G e) :=
  rfl

/-- The masses of all configurations add up to one. -/
theorem sum_configMass {w : ℕ} (p : Fin w → ℝ) (u : ℝ) : ∑ G, configMass p u G = 1 := by
  have h := sum_configMass_componentPartition_le p u ⊤
  rw [crossingRate_top, mul_zero, neg_zero, Real.exp_zero] at h
  simp only [le_top, if_true, mul_one] at h
  exact h

/-- A configuration's mass is nonnegative at nonnegative times and masses. -/
theorem configMass_nonneg {w : ℕ} {p : Fin w → ℝ} (hp : ∀ i, 0 ≤ p i) {u : ℝ} (hu : 0 ≤ u)
    (G : FiberPair w → Bool) : 0 ≤ configMass p u G :=
  Finset.prod_nonneg fun e _ ↦ by
    have hrate : 0 ≤ u * pairRate p e := mul_nonneg hu (mul_nonneg (hp _) (hp _))
    have hexp : Real.exp (-(u * pairRate p e)) ≤ 1 := by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr (by linarith)
    split_ifs
    · linarith
    · exact (Real.exp_pos _).le

/-- **Superposition**: the configuration at time `u + t` is the union of independent
configurations at times `u` and `t`, because `e^{-(u+t) r} = e^{-u r} e^{-t r}`. -/
theorem sum_configMass_add_mul {w : ℕ} (p : Fin w → ℝ) (u t : ℝ)
    (f : (FiberPair w → Bool) → ℝ) :
    ∑ K, configMass p (u + t) K * f K
      = ∑ G, ∑ H, configMass p u G * configMass p t H * f (fun e ↦ G e || H e) := by
  have hind : ∀ G H K : FiberPair w → Bool,
      (if (fun e ↦ G e || H e) = K then (1 : ℝ) else 0)
        = ∏ e, if (G e || H e) = K e then (1 : ℝ) else 0 := by
    intro G H K
    by_cases hK : (fun e ↦ G e || H e) = K
    · rw [if_pos hK]
      symm
      exact Finset.prod_eq_one fun e _ ↦ if_pos (congrFun hK e)
    · rw [if_neg hK]
      symm
      obtain ⟨e, he⟩ : ∃ e, (G e || H e) ≠ K e := by
        by_contra hall
        push_neg at hall
        exact hK (funext hall)
      exact Finset.prod_eq_zero (Finset.mem_univ e) (if_neg he)
  have hedge : ∀ (e : FiberPair w) (c : Bool),
      ∑ a, ∑ b, edgeMass p u e a * (edgeMass p t e b * if (a || b) = c then (1 : ℝ) else 0)
        = edgeMass p (u + t) e c := by
    intro e c
    have hexp : Real.exp (-((u + t) * pairRate p e))
        = Real.exp (-(u * pairRate p e)) * Real.exp (-(t * pairRate p e)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    simp only [Fintype.sum_bool, edgeMass, hexp]
    cases c <;> simp <;> ring
  have hinner : ∀ K : FiberPair w → Bool,
      ∑ G, ∑ H, configMass p u G * configMass p t H
          * (if (fun e ↦ G e || H e) = K then (1 : ℝ) else 0)
        = configMass p (u + t) K := by
    intro K
    calc ∑ G, ∑ H, configMass p u G * configMass p t H
          * (if (fun e ↦ G e || H e) = K then (1 : ℝ) else 0)
        = ∑ G : FiberPair w → Bool, ∑ H : FiberPair w → Bool, ∏ e, edgeMass p u e (G e)
            * (edgeMass p t e (H e) * if (G e || H e) = K e then (1 : ℝ) else 0) := by
          refine Finset.sum_congr rfl fun G _ ↦ Finset.sum_congr rfl fun H _ ↦ ?_
          rw [hind G H K, configMass_eq_prod_edgeMass, configMass_eq_prod_edgeMass, mul_assoc,
            ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
      _ = ∑ G : FiberPair w → Bool, ∏ e, ∑ b, edgeMass p u e (G e)
            * (edgeMass p t e b * if (G e || b) = K e then (1 : ℝ) else 0) := by
          refine Finset.sum_congr rfl fun G _ ↦ ?_
          have hexpand := Finset.prod_univ_sum (fun _ : FiberPair w ↦ (univ : Finset Bool))
            fun e b ↦ edgeMass p u e (G e)
              * (edgeMass p t e b * if (G e || b) = K e then (1 : ℝ) else 0)
          rw [Fintype.piFinset_univ] at hexpand
          exact hexpand.symm
      _ = ∏ e, ∑ a, ∑ b, edgeMass p u e a
            * (edgeMass p t e b * if (a || b) = K e then (1 : ℝ) else 0) := by
          have hexpand := Finset.prod_univ_sum (fun _ : FiberPair w ↦ (univ : Finset Bool))
            fun e a ↦ ∑ b, edgeMass p u e a
              * (edgeMass p t e b * if (a || b) = K e then (1 : ℝ) else 0)
          rw [Fintype.piFinset_univ] at hexpand
          exact hexpand.symm
      _ = configMass p (u + t) K := by
          rw [configMass_eq_prod_edgeMass]
          exact Finset.prod_congr rfl fun e _ ↦ hedge e (K e)
  calc ∑ K, configMass p (u + t) K * f K
      = ∑ K, (∑ G, ∑ H, configMass p u G * configMass p t H
          * (if (fun e ↦ G e || H e) = K then (1 : ℝ) else 0)) * f K := by
        simp only [hinner]
    _ = ∑ G, ∑ H, ∑ K, configMass p u G * configMass p t H
          * (if (fun e ↦ G e || H e) = K then (1 : ℝ) else 0) * f K := by
        simp only [Finset.sum_mul]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun G _ ↦ Finset.sum_comm
    _ = ∑ G, ∑ H, configMass p u G * configMass p t H * f (fun e ↦ G e || H e) := by
        refine Finset.sum_congr rfl fun G _ ↦ Finset.sum_congr rfl fun H _ ↦ ?_
        simp only [mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq,
          Finset.mem_univ, if_true]

/-- Adding edges can only merge components. -/
theorem componentPartition_mono {w : ℕ} {G H : FiberPair w → Bool}
    (hGH : ∀ e, G e = true → H e = true) : componentPartition G ≤ componentPartition H :=
  (componentPartition_le_iff G (componentPartition H)).mpr fun e he ↦
    (componentPartition_le_iff H (componentPartition H)).mp le_rfl e (hGH e he)

/-- **`Pr(T_p ≤ u)` does not decrease in time**: the configuration at `u + t` contains an
independent copy of the configuration at `u`, and connection is preserved by adding edges. -/
theorem connectionProbability_le_add {w : ℕ} {p : Fin w → ℝ} (hp : ∀ i, 0 ≤ p i) {u t : ℝ}
    (hu : 0 ≤ u) (ht : 0 ≤ t) :
    connectionProbability p u ≤ connectionProbability p (u + t) := by
  unfold connectionProbability
  rw [sum_configMass_add_mul p u t]
  calc ∑ G, configMass p u G * (if componentPartition G = ⊤ then (1 : ℝ) else 0)
      = ∑ G, ∑ H, configMass p u G * configMass p t H
          * (if componentPartition G = ⊤ then (1 : ℝ) else 0) := by
        refine Finset.sum_congr rfl fun G _ ↦ ?_
        rw [← Finset.sum_mul, ← Finset.mul_sum, sum_configMass, mul_one]
    _ ≤ ∑ G, ∑ H, configMass p u G * configMass p t H
          * (if componentPartition (fun e ↦ G e || H e) = ⊤ then (1 : ℝ) else 0) := by
        refine Finset.sum_le_sum fun G _ ↦ Finset.sum_le_sum fun H _ ↦ ?_
        refine mul_le_mul_of_nonneg_left ?_
          (mul_nonneg (configMass_nonneg hp hu G) (configMass_nonneg hp ht H))
        by_cases hG : componentPartition G = ⊤
        · have hle := componentPartition_mono (G := G) (H := fun e ↦ G e || H e)
            fun e he ↦ by simp [he]
          rw [hG] at hle
          rw [if_pos hG, if_pos (top_unique hle)]
        · rw [if_neg hG]
          split_ifs <;> norm_num

/-- **The limit distribution function is monotone** on nonnegative times.  Weaker in hypotheses
than `MultiplicativeConnectionInLaw.monotone_connectionTimeCDF`: only `p ≥ 0` is assumed, with no
bound on `∑ p_i`. -/
theorem monotoneOn_connectionProbability {w : ℕ} {p : Fin w → ℝ} (hp : ∀ i, 0 ≤ p i) :
    MonotoneOn (fun u ↦ connectionProbability p u) (Set.Ici 0) := by
  intro u hu v _ huv
  have h := connectionProbability_le_add hp hu (sub_nonneg.mpr huv)
  have hv : u + (v - u) = v := by ring
  rw [hv] at h
  exact h

end

end Descent.Pangenome.GraphCoalescent
