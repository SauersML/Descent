/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.GraphCoalescent.MultiplicativeConnectionLimit
import Descent.Pangenome.GraphCoalescent.MultiplicativePerturbation

assert_below Descent.PopGen Descent.Spectral Descent.Blindness Descent.Conditionals
assert_below Descent.Portability Descent.Decision Descent.Program

/-!
# The connection clock against the multiplicative law at any fiber masses

(F3) of the hidden-clock note is the limit `n² τ_{q_n} ⇒ T_p` along interfaces whose fiber
proportions `p^(n) = c/n` converge to `p`.  `MultiplicativeConnectionLimit` proves its
quantitative form at the empirical masses: the probability that the graph's report is connected
at scaled time `U` is within `U²/(4n)` of the Möbius sum of `Z_{p^(n)}`.  This module reads `p` on
the fibers through `MultiplicativePerturbation.spreadMass` and proves the same statement at any
fiber masses `p`, at the price `U ‖p^(n) - p‖₁` of (F2):

  `|Pr(n² τ_q ≤ U) - Σ_{σ ≥ q} (-1)^{|σ|-1} (|σ|-1)! e^{-U κ_σ(p)}|
      ≤ U²/(4n) + U Σ_F |c_F/n - p_F|`.

## The mechanism

The Möbius law of `MultiplicativeConnectionLimit` rests on one property: from any state below a
partition `σ`, `Z` leaves the partitions below `σ` with probability `κ_σ` per step, because the
merges that cross `σ` carry the crossing mass of `σ` whatever the state is.
`two_mul_sum_crossing_eq_mass` and `sum_filter_le_massStep` prove that for every mass vector, so
`Z` with masses `mass` is connected at scaled time `U` with the Möbius probability of `mass`
(`hasSum_poissonPMFReal_mul_massTop`).  The coupling of `MultiplicativePerturbation` then moves
the masses: after `m` steps the connection probabilities of two copies with masses `mass` and
`mass'` differ by at most `m ‖mass - mass'‖₁` (`abs_sub_massConnection_le`).

## Main results

- `sum_filter_le_massStep`, `sum_filter_le_massLaw`, `sum_massLaw_mul_top`: the exit rate, the
  law below `σ` and the connection probability of `Z` with any masses.  Unit masses give the laws
  of `MultiplicativeConnectionLimit` (`multiplicativeLaw_eq_massLaw`).
- `hasSum_poissonPMFReal_mul_massTop`: `Z` with masses `mass` is connected at scaled time `U`
  with the Möbius probability `Σ_{σ ≥ q} (-1)^{|σ|-1} (|σ|-1)! e^{-U κ_σ(mass)}`.
- `abs_reportConnectionProbability_sub_spread_le`: (F3), quantitative, at any fiber masses.

## Scope

As in `MultiplicativeConnectionLimit`, time is the rate-one uniformization in scaled time, and
`Z_p` runs on the partitions of the individuals from the interface, with `p` read on the fibers
through `spreadMass`.  The limit `n → ∞` along a sequence of interfaces, and the transport of the
Möbius sum to the `w` fiber labels, are not formalized here; the bound is explicit at every `n`.

## Empirical status

None.  Every declaration here is a finite sum over equivalence relations on a finite set, a
finite Markov kernel, or a Poisson series.
-/

namespace Descent.Pangenome.GraphCoalescent

open Coalescent Finset ProbabilityTheory

open scoped Classical

noncomputable section

/-! ### The crossing mass at any masses -/

/-- Two masses of components, expanded over their individuals and weighted by whether the two
individuals lie in different blocks of `σ`, for any mass vector. -/
theorem ite_blockMap_mul_blockMass_mass {n : ℕ} (mass : Fin n → ℝ) {ζ σ : ER n} (h : ζ ≤ σ)
    (C D : Quotient ζ) :
    (if blockMap h C = blockMap h D then 0 else blockMass mass ζ C * blockMass mass ζ D)
      = ∑ x ∈ univ.filter (fun x ↦ Quotient.mk ζ x = C),
          ∑ y ∈ univ.filter (fun y ↦ Quotient.mk ζ y = D),
            (if σ.r x y then 0 else mass x * mass y) := by
  have hrel : ∀ x ∈ univ.filter (fun x ↦ Quotient.mk ζ x = C),
      ∀ y ∈ univ.filter (fun y ↦ Quotient.mk ζ y = D),
        (blockMap h C = blockMap h D ↔ σ.r x y) := by
    intro x hx y hy
    have hxy : blockMap h C = Quotient.mk σ x ∧ blockMap h D = Quotient.mk σ y := by
      rw [← (Finset.mem_filter.mp hx).2, ← (Finset.mem_filter.mp hy).2]
      exact ⟨rfl, rfl⟩
    rw [hxy.1, hxy.2]
    exact ⟨Quotient.exact, fun hr ↦ Quotient.sound hr⟩
  by_cases hφ : blockMap h C = blockMap h D
  · simp only [if_pos hφ]
    symm
    exact Finset.sum_eq_zero fun x hx ↦ Finset.sum_eq_zero fun y hy ↦
      if_pos ((hrel x hx y hy).mp hφ)
  · simp only [if_neg hφ, blockMass, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun x hx ↦ Finset.sum_congr rfl fun y hy ↦
      (if_neg fun hr ↦ hφ ((hrel x hx y hy).mpr hr)).symm

/-- **The merges of `Z` that leave the partitions below `σ` carry the crossing mass of `σ`**, for
any mass vector and whatever the state `ζ ≤ σ` they start from. -/
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
        rcases eq_or_ne C D with rfl | hCD
        · simp
        · rw [if_pos hCD, mergePair_pair ζ hCD, Finset.prod_pair hCD]
          exact if_congr (merge_le_iff_blockMap_eq h hCD) rfl rfl
    _ = ∑ C, ∑ D, ∑ x ∈ univ.filter (fun x ↦ Quotient.mk ζ x = C),
          ∑ y ∈ univ.filter (fun y ↦ Quotient.mk ζ y = D),
            (if σ.r x y then 0 else mass x * mass y) :=
        Finset.sum_congr rfl fun C _ ↦ Finset.sum_congr rfl fun D _ ↦
          ite_blockMap_mul_blockMass_mass mass h C D
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

/-- **Twice `κ_σ` is the crossing mass of `σ` between individuals**, for any mass vector. -/
theorem two_mul_pairProductSum_blockMass_crossing {n : ℕ} (mass : Fin n → ℝ) (σ : ER n) :
    2 * pairProductSum (blockMass mass σ)
      = ∑ x, ∑ y, if σ.r x y then 0 else mass x * mass y := by
  rw [← two_mul_sum_crossing_eq_mass mass (le_refl σ), pairProductSum]
  congr 1
  exact Finset.sum_congr rfl fun t ht ↦ (if_neg (not_mergePair_le_self σ ht)).symm

/-! ### `Z` below a partition, at any masses -/

/-- **`Z` with masses `mass` leaves the partitions below `σ` at the constant rate `κ_σ`**: from
any `ζ ≤ σ` it stays below `σ` with probability `1 - κ_σ`. -/
theorem sum_filter_le_massStep {n : ℕ} (mass : Fin n → ℝ) {ζ σ : ER n} (h : ζ ≤ σ) :
    ∑ ζ' ∈ univ.filter (· ≤ σ), massStep mass ζ ζ' = 1 - pairProductSum (blockMass mass σ) := by
  have hA : ∑ ζ' ∈ univ.filter (· ≤ σ), ∑ t ∈ (univ.powersetCard 2).filter
        (fun t ↦ mergePair ζ t = ζ'), ∏ C ∈ t, blockMass mass ζ C
      = ∑ t ∈ (univ : Finset (Quotient ζ)).powersetCard 2,
          if mergePair ζ t ≤ σ then ∏ C ∈ t, blockMass mass ζ C else 0 := by
    rw [Finset.sum_filter, ← Finset.sum_fiberwise ((univ : Finset (Quotient ζ)).powersetCard 2)
      (mergePair ζ) (fun t ↦ if mergePair ζ t ≤ σ then ∏ C ∈ t, blockMass mass ζ C else 0)]
    refine Finset.sum_congr rfl fun ζ' _ ↦ ?_
    split_ifs with hle
    · exact Finset.sum_congr rfl fun t ht ↦
        (if_pos ((Finset.mem_filter.mp ht).2.le.trans hle)).symm
    · symm
      exact Finset.sum_eq_zero fun t ht ↦
        if_neg fun hle' ↦ hle ((Finset.mem_filter.mp ht).2.symm.le.trans hle')
  have hsplit : ∑ t ∈ (univ : Finset (Quotient ζ)).powersetCard 2,
        (if mergePair ζ t ≤ σ then ∏ C ∈ t, blockMass mass ζ C else 0)
      + ∑ t ∈ (univ : Finset (Quotient ζ)).powersetCard 2,
        (if mergePair ζ t ≤ σ then 0 else ∏ C ∈ t, blockMass mass ζ C)
      = pairProductSum (blockMass mass ζ) := by
    rw [← Finset.sum_add_distrib, pairProductSum]
    exact Finset.sum_congr rfl fun t _ ↦ by split_ifs <;> simp
  have hcross := two_mul_sum_crossing_eq_mass mass h
  rw [← two_mul_pairProductSum_blockMass_crossing mass σ] at hcross
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

/-- Unit masses give the law of `MultiplicativeConnectionLimit`. -/
theorem multiplicativeLaw_eq_massLaw {n : ℕ} (s : Fin n → Fin n) (m : ℕ) :
    multiplicativeLaw s m = massLaw s (unitMass n) m :=
  rfl

/-- **`Z` with masses `mass` is below `σ` after `m` steps with probability `(1 - κ_σ)^m`**, when
the interface is below `σ`, and never otherwise. -/
theorem sum_filter_le_massLaw {n : ℕ} (s : Fin n → Fin n) (mass : Fin n → ℝ) (σ : ER n)
    (m : ℕ) :
    ∑ ζ ∈ univ.filter (· ≤ σ), massLaw s mass m ζ
      = if graphKer s ≤ σ then (1 - pairProductSum (blockMass mass σ)) ^ m else 0 := by
  induction m with
  | zero =>
    simp only [massLaw, skeletonLaw, pow_zero]
    rw [Finset.sum_ite_eq']
    exact if_congr (by simp) rfl rfl
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
        = ∑ ζ, massLaw s mass m ζ * ∑ ζ' ∈ univ.filter (· ≤ σ), massStep mass ζ ζ' := h1
    rw [hstep, Finset.sum_congr rfl fun ζ _ ↦ hpoint ζ, ← Finset.sum_mul, ← Finset.sum_filter,
      ih]
    split_ifs <;> ring

/-- **The connection probability of `Z` with masses `mass` after `m` steps**, as a Möbius sum
over the partitions above the interface. -/
theorem sum_massLaw_mul_top {n : ℕ} [NeZero n] (s : Fin n → Fin n) (mass : Fin n → ℝ) (m : ℕ) :
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
`Σ_{σ ≥ q} (-1)^{|σ|-1} (|σ|-1)! e^{-U κ_σ(mass)}`. -/
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

/-! ### Moving the masses -/

/-- A functional of the first copy is a functional of the coupled chain of two mass vectors. -/
theorem sum_massLaw_mul_eq_fst {n : ℕ} (s : Fin n → Fin n) (mass mass' : Fin n → ℝ) (m : ℕ)
    (g : ER n → ℝ) :
    ∑ ζ, massLaw s mass m ζ * g ζ
      = ∑ X, skeletonLaw (perturbedStep mass mass') (perturbedStartLaw s) m X * g X.1 := by
  rw [← Finset.sum_fiberwise univ Prod.fst
    fun X ↦ skeletonLaw (perturbedStep mass mass') (perturbedStartLaw s) m X * g X.1]
  refine Finset.sum_congr rfl fun ζ _ ↦ ?_
  rw [massLaw, ← sum_filter_skeletonLaw_comp_eq (perturbedStep mass mass') (perturbedStartLaw s)
    (massStep mass) (fun ζ ↦ if ζ = graphKer s then 1 else 0) Prod.fst
    (fun X ζ₁ ↦ sum_perturbedStep_fst mass mass' X ζ₁) (sum_filter_fst_perturbedStartLaw s) m ζ,
    Finset.sum_mul]
  exact Finset.sum_congr rfl fun X hX ↦ by rw [(Finset.mem_filter.mp hX).2]

/-- A functional of the second copy is a functional of the coupled chain of two mass vectors. -/
theorem sum_massLaw_mul_eq_snd {n : ℕ} (s : Fin n → Fin n) (mass mass' : Fin n → ℝ) (m : ℕ)
    (g : ER n → ℝ) :
    ∑ ζ, massLaw s mass' m ζ * g ζ
      = ∑ X, skeletonLaw (perturbedStep mass mass') (perturbedStartLaw s) m X * g X.2.1 := by
  rw [← Finset.sum_fiberwise univ (fun X : CoupledState n ↦ X.2.1)
    fun X ↦ skeletonLaw (perturbedStep mass mass') (perturbedStartLaw s) m X * g X.2.1]
  refine Finset.sum_congr rfl fun ζ _ ↦ ?_
  rw [massLaw, ← sum_filter_skeletonLaw_comp_eq (perturbedStep mass mass') (perturbedStartLaw s)
    (massStep mass') (fun ζ ↦ if ζ = graphKer s then 1 else 0) (fun X ↦ X.2.1)
    (fun X ζ₂ ↦ sum_perturbedStep_snd mass mass' X ζ₂) (sum_filter_snd_perturbedStartLaw s) m ζ,
    Finset.sum_mul]
  exact Finset.sum_congr rfl fun X hX ↦ by rw [(Finset.mem_filter.mp hX).2]

/-- **After `m` steps two copies of `Z` from the interface are connected with probabilities at
most `m ‖mass - mass'‖₁` apart.**

Assumes: both mass vectors are nonnegative with total at most one. -/
theorem abs_sub_massConnection_le {n : ℕ} (s : Fin n → Fin n) {mass mass' : Fin n → ℝ}
    (hmass : ∀ i, 0 ≤ mass i) (hmass' : ∀ i, 0 ≤ mass' i) (htotal : ∑ i, mass i ≤ 1)
    (htotal' : ∑ i, mass' i ≤ 1) (m : ℕ) :
    |∑ ζ, massLaw s mass m ζ * (if ζ = ⊤ then 1 else 0)
        - ∑ ζ, massLaw s mass' m ζ * (if ζ = ⊤ then 1 else 0)|
      ≤ (∑ i, |mass i - mass' i|) * m := by
  rw [sum_massLaw_mul_eq_fst s mass mass' m, sum_massLaw_mul_eq_snd s mass mass' m,
    ← Finset.sum_sub_distrib]
  refine le_trans ?_ (separationMass_le_mul (perturbedStep_nonneg hmass hmass' htotal htotal')
    (sum_perturbedStep mass mass') (perturbedStartLaw_nonneg s) (sum_perturbedStartLaw s)
    (Finset.sum_nonneg fun _ _ ↦ abs_nonneg _) (perturbedStep_hazard hmass hmass' htotal htotal')
    (separationMass_perturbedStart s mass mass') m)
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [separationMass, Finset.sum_filter]
  refine Finset.sum_le_sum fun X _ ↦ ?_
  have hlaw := skeletonLaw_nonneg (perturbedStep_nonneg hmass hmass' htotal htotal')
    (perturbedStartLaw_nonneg s) m X
  by_cases hX : perturbedSep X
  · rw [if_pos hX, ← mul_sub, abs_mul, abs_of_nonneg hlaw]
    calc _ ≤ skeletonLaw (perturbedStep mass mass') (perturbedStartLaw s) m X * 1 :=
          mul_le_mul_of_nonneg_left (by split_ifs <;> norm_num) hlaw
      _ = _ := mul_one _
  · have hzero : skeletonLaw (perturbedStep mass mass') (perturbedStartLaw s) m X
          * (if X.1 = ⊤ then (1 : ℝ) else 0)
        - skeletonLaw (perturbedStep mass mass') (perturbedStartLaw s) m X
          * (if X.2.1 = ⊤ then 1 else 0) = 0 := by
      rw [perturbedAgree hX, sub_self]
    rw [if_neg hX, hzero, abs_zero]

/-! ### (F3) at any fiber masses -/

/-- **(F3), quantitative, at any fiber masses.**  For a mass vector `p` on the fibers, nonnegative
with total at most one, the probability that the graph's report is connected at scaled time `U`
is within `U²/(4n) + U Σ_F |c_F/n - p_F|` of the Möbius sum
`Σ_{σ ≥ q} (-1)^{|σ|-1} (|σ|-1)! e^{-U κ_σ(p)}`, the probability that the multiplicative
coalescent with masses `p` started at the interface is connected.

Assumes: `0 < n`, and `p` is nonnegative with total at most one. -/
theorem abs_reportConnectionProbability_sub_spread_le {n : ℕ} (hn : 0 < n) (s : Fin n → Fin n)
    {p : Quotient (graphKer s) → ℝ} (hp : ∀ F, 0 ≤ p F) (hptotal : ∑ F, p F ≤ 1)
    (U : NNReal) :
    |reportConnectionProbability s U
        - ∑ σ, (topMobius (blocks σ) : ℝ)
          * (if graphKer s ≤ σ then
              Real.exp (-((U : ℝ) * pairProductSum (blockMass (spreadMass s p) σ))) else 0)|
      ≤ (U : ℝ) ^ 2 / (4 * n) + U * ∑ F, |(fiberSize s F : ℝ) / n - p F| := by
  haveI : NeZero n := ⟨hn.ne'⟩
  have hF1 := abs_reportConnectionProbability_sub_le hn s U
  have hmass' := spreadMass_nonneg s hp
  have htotal' : ∑ i, spreadMass s p i ≤ 1 := (sum_spreadMass s p).trans_le hptotal
  have hB1 := hasSum_poissonPMFReal_mul_massTop s (unitMass n) U
  have hB2 := hasSum_poissonPMFReal_mul_massTop s (spreadMass s p) U
  have hD := (hasSum_poissonPMFReal_mul_nat U).mul_left
    (∑ i, |unitMass n i - spreadMass s p i|)
  have hterm : ∀ m : ℕ,
      |poissonPMFReal U m * ∑ ζ, massLaw s (unitMass n) m ζ * (if ζ = ⊤ then 1 else 0)
        - poissonPMFReal U m * ∑ ζ, massLaw s (spreadMass s p) m ζ * (if ζ = ⊤ then 1 else 0)|
      ≤ (∑ i, |unitMass n i - spreadMass s p i|) * (poissonPMFReal U m * m) := by
    intro m
    rw [← mul_sub, abs_mul, abs_of_nonneg poissonPMFReal_nonneg]
    calc poissonPMFReal U m
          * |∑ ζ, massLaw s (unitMass n) m ζ * (if ζ = ⊤ then 1 else 0)
            - ∑ ζ, massLaw s (spreadMass s p) m ζ * (if ζ = ⊤ then 1 else 0)|
        ≤ poissonPMFReal U m * ((∑ i, |unitMass n i - spreadMass s p i|) * m) :=
          mul_le_mul_of_nonneg_left (abs_sub_massConnection_le s (unitMass_nonneg n) hmass'
            (sum_unitMass_le_one n) htotal' m) poissonPMFReal_nonneg
      _ = (∑ i, |unitMass n i - spreadMass s p i|) * (poissonPMFReal U m * m) := by ring
  have hmid : |∑ σ, (topMobius (blocks σ) : ℝ)
          * (if graphKer s ≤ σ then
              Real.exp (-((U : ℝ) * pairProductSum (blockMass (unitMass n) σ))) else 0)
        - ∑ σ, (topMobius (blocks σ) : ℝ)
          * (if graphKer s ≤ σ then
              Real.exp (-((U : ℝ) * pairProductSum (blockMass (spreadMass s p) σ))) else 0)|
      ≤ (∑ i, |unitMass n i - spreadMass s p i|) * U := by
    rw [abs_sub_le_iff]
    constructor
    · exact hasSum_le (fun m ↦ (le_abs_self _).trans (hterm m)) (hB1.sub hB2) hD
    · exact hasSum_le (fun m ↦ (le_abs_self _).trans (by rw [abs_sub_comm]; exact hterm m))
        (hB2.sub hB1) hD
  rw [sum_abs_unitMass_sub_spreadMass] at hmid
  calc _ ≤ |reportConnectionProbability s U
          - ∑ σ, (topMobius (blocks σ) : ℝ)
            * (if graphKer s ≤ σ then
                Real.exp (-((U : ℝ) * pairProductSum (blockMass (unitMass n) σ))) else 0)|
        + |∑ σ, (topMobius (blocks σ) : ℝ)
            * (if graphKer s ≤ σ then
                Real.exp (-((U : ℝ) * pairProductSum (blockMass (unitMass n) σ))) else 0)
          - ∑ σ, (topMobius (blocks σ) : ℝ)
            * (if graphKer s ≤ σ then
                Real.exp (-((U : ℝ) * pairProductSum (blockMass (spreadMass s p) σ))) else 0)| :=
        abs_sub_le _ _ _
    _ ≤ (U : ℝ) ^ 2 / (4 * n) + (∑ F, |(fiberSize s F : ℝ) / n - p F|) * U :=
        add_le_add hF1 hmid
    _ = (U : ℝ) ^ 2 / (4 * n) + U * ∑ F, |(fiberSize s F : ℝ) / n - p F| := by ring

end

end Descent.Pangenome.GraphCoalescent
