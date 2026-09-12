/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.GraphCoalescent.MultiplicativeConnectionLaw
import Descent.Pangenome.GraphCoalescent.MultiplicativeCoupling

assert_below Descent.PopGen Descent.Spectral Descent.Blindness Descent.Conditionals
assert_below Descent.Portability Descent.Decision Descent.Program

/-!
# The connection clock of a compressed pangenome, against the multiplicative law

Theorem F of the hidden-clock note ends with the limit

  `n² τ_{q_n} ⇒ T_p`,                                                               (F3)

the reported connection time, on the time scale `n⁻²`, converging to the connection time of
the random graph on the fibers whose edge `{i, j}` switches on at rate `p_i p_j`.  Its law is the
Möbius sum `Pr(T_p ≤ u) = Σ_σ (-1)^{|σ|-1} (|σ|-1)! e^{-u κ_σ}` (F4), proved as
`MultiplicativeConnectionLaw.connectionProbability_eq_mobius_sum`.

This file proves the quantitative form of (F3) for the uniformized processes of
`Descent.Pangenome.GraphCoalescent.MultiplicativeCoupling`: the probability that the graph's
report is connected at scaled time `U` is within `U²/(4n)` of the Möbius sum over the partitions
above the interface.

## The mechanism

`Z_p` only coarsens, and from any state below a partition `σ` it leaves the partitions below `σ`
with probability exactly `κ_σ` per step (`sum_filter_le_multiplicativeStep`): the merges that
cross `σ` carry the crossing mass of `σ` whatever the current state is.  So `Z_p` is below `σ`
after `m` steps with probability `(1 - κ_σ)^m` (`sum_filter_le_multiplicativeLaw`), and at scaled
time `U` with probability `e^{-U κ_σ}` (`hasSum_poissonPMFReal_mul_pow`).  Möbius inversion at
the top of the partition lattice (`MultiplicativeConnectionLaw.sum_topMobius_blocks_ge`) turns
those into the probability that `Z_p` is connected.  The coupling bounds the difference between
the report and `Z_p` by the separation mass.

## Main results

- `two_mul_sum_powersetCard_two_eq`: a sum over two-element sets, twice, is a sum over ordered
  pairs.
- `two_mul_sum_crossing_eq`: the merges of `Z_p` that cross `σ` carry twice `κ_σ` in individuals.
- `sum_filter_le_multiplicativeStep`, `sum_filter_le_multiplicativeLaw`: the constant exit rate
  and the law of the partitions below `σ`.
- `sum_multiplicativeLaw_mul_top`: the connection probability of `Z_p` after `m` steps, as a
  Möbius sum.
- `abs_sub_connectionMass_le`: the report and `Z_p` are connected after `m` steps with
  probabilities at most `m(m-1)/(4n)` apart.
- `abs_reportConnectionProbability_sub_le`: **(F3), quantitative**: at scaled time `U`, within
  `U²/(4n)` of the Möbius sum.

## Scope

As in `MultiplicativeCoupling`, time is the rate-one uniformization in scaled time.  The report
only coarsens, so being connected at scaled time `U` is `n² τ_q ≤ U` for the uniformized
construction.  `Z_p` runs on the partitions of the individuals above the interface with mass
`1/n` each; the transport of the Möbius sum to the `w` fiber labels, and the limit along a
sequence of interfaces whose fiber proportions converge, are not formalized here.

## Empirical status

None.  Every declaration here is a finite sum over equivalence relations on a finite set, a
finite Markov kernel, or a Poisson series.  The reading of `s` as a real graph's interface is
stated in `Descent.Pangenome.GraphCoalescent.Observation` and is not asserted of any dataset.
-/

namespace Descent.Pangenome.GraphCoalescent

open Coalescent Finset ProbabilityTheory

open scoped Classical

noncomputable section

/-! ### Two-element sets and ordered pairs -/

/-- **A sum over two-element sets, twice, is a sum over ordered pairs of distinct elements.** -/
theorem two_mul_sum_powersetCard_two_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : Finset ι → ℝ) :
    2 * ∑ t ∈ (univ : Finset ι).powersetCard 2, G t
      = ∑ a, ∑ b, if a ≠ b then G {a, b} else 0 := by
  have hmaps : ∀ x ∈ (univ : Finset (ι × ι)).filter (fun x ↦ x.1 ≠ x.2),
      ({x.1, x.2} : Finset ι) ∈ (univ : Finset ι).powersetCard 2 := fun x hx ↦
    Finset.mem_powersetCard_univ.mpr (Finset.card_pair (Finset.mem_filter.mp hx).2)
  have hfiber : ∀ t ∈ (univ : Finset ι).powersetCard 2,
      ∑ x ∈ ((univ : Finset (ι × ι)).filter (fun x ↦ x.1 ≠ x.2)).filter
          (fun x ↦ ({x.1, x.2} : Finset ι) = t), G {x.1, x.2} = 2 * G t := by
    intro t ht
    obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp (Finset.mem_powersetCard_univ.mp ht)
    have hset : ((univ : Finset (ι × ι)).filter (fun x ↦ x.1 ≠ x.2)).filter
        (fun x ↦ ({x.1, x.2} : Finset ι) = {a, b}) = {(a, b), (b, a)} := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton]
      constructor
      · rintro ⟨hx, heq⟩
        have h1 : x.1 ∈ ({a, b} : Finset ι) := heq ▸ Finset.mem_insert_self _ _
        have h2 : x.2 ∈ ({a, b} : Finset ι) :=
          heq ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
        simp only [Finset.mem_insert, Finset.mem_singleton] at h1 h2
        rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
        · exact absurd (h1.trans h2.symm) hx
        · exact Or.inl (Prod.ext h1 h2)
        · exact Or.inr (Prod.ext h1 h2)
        · exact absurd (h1.trans h2.symm) hx
      · rintro (rfl | rfl)
        · exact ⟨hab, rfl⟩
        · exact ⟨hab.symm, Finset.pair_comm _ _⟩
    rw [hset, Finset.sum_pair fun h ↦ hab (congrArg Prod.fst h)]
    simp only [Finset.pair_comm b a]
    ring
  calc 2 * ∑ t ∈ (univ : Finset ι).powersetCard 2, G t
      = ∑ t ∈ (univ : Finset ι).powersetCard 2,
          ∑ x ∈ ((univ : Finset (ι × ι)).filter (fun x ↦ x.1 ≠ x.2)).filter
            (fun x ↦ ({x.1, x.2} : Finset ι) = t), G {x.1, x.2} := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun t ht ↦ (hfiber t ht).symm
    _ = ∑ x ∈ (univ : Finset (ι × ι)).filter (fun x ↦ x.1 ≠ x.2), G {x.1, x.2} :=
        Finset.sum_fiberwise_of_maps_to hmaps _
    _ = ∑ a, ∑ b, if a ≠ b then G {a, b} else 0 := by
        rw [Finset.sum_filter, ← Finset.univ_product_univ]
        exact Finset.sum_product' _ _ fun a b ↦ if a ≠ b then G {a, b} else 0

/-! ### The crossing mass -/

/-- The pair `{C, D}` names the merge of `C` and `D`. -/
theorem mergePair_pair {n : ℕ} (ζ : ER n) {C D : Quotient ζ} (hCD : C ≠ D) :
    mergePair ζ {C, D} = merge ζ C D := by
  have hcard := Finset.card_pair hCD
  have hspec := pair_spec hcard
  rw [mergePair, dif_pos hcard]
  exact (merge_eq_merge_iff ζ hspec.1 hCD).mpr hspec.2.symm

/-- `Z_p` only coarsens. -/
theorem le_mergePair {n : ℕ} (ζ : ER n) (t : Finset (Quotient ζ)) : ζ ≤ mergePair ζ t := by
  unfold mergePair
  split_ifs
  · exact le_merge ζ _ _
  · exact le_rfl

/-- A merge of two components stays below `σ` exactly when they lie in one block of `σ`. -/
theorem merge_le_iff_blockMap_eq {n : ℕ} {ζ σ : ER n} (h : ζ ≤ σ) {C D : Quotient ζ}
    (hCD : C ≠ D) : merge ζ C D ≤ σ ↔ blockMap h C = blockMap h D := by
  obtain ⟨x, rfl⟩ := quotient_mk_surjective ζ C
  obtain ⟨y, rfl⟩ := quotient_mk_surjective ζ D
  constructor
  · intro hle
    show Quotient.mk σ x = Quotient.mk σ y
    exact Quotient.sound (hle (merge_rel ζ _ _ rfl rfl))
  · intro heq
    have hr : Quotient.mk σ x = Quotient.mk σ y := heq
    exact merge_le_of_le_of_rel h hCD rfl rfl (Quotient.exact hr)

/-- Two masses of components, expanded over their individuals and weighted by whether the two
individuals lie in different blocks of `σ`. -/
theorem ite_blockMap_mul_blockMass {n : ℕ} {ζ σ : ER n} (h : ζ ≤ σ) (C D : Quotient ζ) :
    (if blockMap h C = blockMap h D then 0
        else blockMass (unitMass n) ζ C * blockMass (unitMass n) ζ D)
      = ∑ x ∈ univ.filter (fun x ↦ Quotient.mk ζ x = C),
          ∑ y ∈ univ.filter (fun y ↦ Quotient.mk ζ y = D),
            (if σ.r x y then 0 else unitMass n x * unitMass n y) := by
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

/-- **The merges of `Z_p` that leave the partitions below `σ` carry the crossing mass of `σ`**,
whatever the state `ζ ≤ σ` they start from. -/
theorem two_mul_sum_crossing_eq {n : ℕ} {ζ σ : ER n} (h : ζ ≤ σ) :
    2 * ∑ t ∈ (univ : Finset (Quotient ζ)).powersetCard 2,
        (if mergePair ζ t ≤ σ then 0 else ∏ C ∈ t, blockMass (unitMass n) ζ C)
      = ∑ x, ∑ y, if σ.r x y then 0 else unitMass n x * unitMass n y := by
  calc 2 * ∑ t ∈ (univ : Finset (Quotient ζ)).powersetCard 2,
        (if mergePair ζ t ≤ σ then 0 else ∏ C ∈ t, blockMass (unitMass n) ζ C)
      = ∑ C, ∑ D, if C ≠ D then (if mergePair ζ {C, D} ≤ σ then 0
          else ∏ E ∈ ({C, D} : Finset (Quotient ζ)), blockMass (unitMass n) ζ E) else 0 :=
        two_mul_sum_powersetCard_two_eq _
    _ = ∑ C, ∑ D, if blockMap h C = blockMap h D then 0
          else blockMass (unitMass n) ζ C * blockMass (unitMass n) ζ D := by
        refine Finset.sum_congr rfl fun C _ ↦ Finset.sum_congr rfl fun D _ ↦ ?_
        by_cases hCD : C = D
        · rw [if_neg (not_not.mpr hCD), if_pos (congrArg (blockMap h) hCD)]
        · rw [if_pos hCD, mergePair_pair ζ hCD, Finset.prod_pair hCD]
          by_cases hφ : blockMap h C = blockMap h D
          · rw [if_pos ((merge_le_iff_blockMap_eq h hCD).mpr hφ), if_pos hφ]
          · rw [if_neg fun hle ↦ hφ ((merge_le_iff_blockMap_eq h hCD).mp hle), if_neg hφ]
    _ = ∑ C, ∑ D, ∑ x ∈ univ.filter (fun x ↦ Quotient.mk ζ x = C),
          ∑ y ∈ univ.filter (fun y ↦ Quotient.mk ζ y = D),
            (if σ.r x y then 0 else unitMass n x * unitMass n y) :=
        Finset.sum_congr rfl fun C _ ↦ Finset.sum_congr rfl fun D _ ↦
          ite_blockMap_mul_blockMass h C D
    _ = ∑ x, ∑ y, if σ.r x y then 0 else unitMass n x * unitMass n y := by
        have hinner : ∀ C : Quotient ζ, ∑ D, ∑ x ∈ univ.filter (fun x ↦ Quotient.mk ζ x = C),
            ∑ y ∈ univ.filter (fun y ↦ Quotient.mk ζ y = D),
              (if σ.r x y then 0 else unitMass n x * unitMass n y)
            = ∑ x ∈ univ.filter (fun x ↦ Quotient.mk ζ x = C),
                ∑ y, (if σ.r x y then 0 else unitMass n x * unitMass n y) := by
          intro C
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun x _ ↦ Finset.sum_fiberwise univ (Quotient.mk ζ)
            fun y ↦ if σ.r x y then 0 else unitMass n x * unitMass n y
        rw [Finset.sum_congr rfl fun C _ ↦ hinner C]
        exact Finset.sum_fiberwise univ (Quotient.mk ζ)
          fun x ↦ ∑ y, if σ.r x y then 0 else unitMass n x * unitMass n y

/-- A merge of two distinct components is never below the state it merges. -/
theorem not_mergePair_le_self {n : ℕ} (ζ : ER n) {t : Finset (Quotient ζ)}
    (ht : t ∈ (univ : Finset (Quotient ζ)).powersetCard 2) : ¬ mergePair ζ t ≤ ζ := by
  have hcard := Finset.mem_powersetCard_univ.mp ht
  intro hle
  rw [mergePair, dif_pos hcard] at hle
  have heq := eq_of_le_of_blocks_eq (le_merge ζ _ _)
    (congrArg blocks (le_antisymm (le_merge ζ _ _) hle))
  have hb := blocks_merge ζ (pair_spec hcard).1
  rw [← heq] at hb
  omega

/-- **Twice `κ_σ` is the crossing mass of `σ` between individuals.** -/
theorem two_mul_pairProductSum_blockMass_unitMass {n : ℕ} (σ : ER n) :
    2 * pairProductSum (blockMass (unitMass n) σ)
      = ∑ x, ∑ y, if σ.r x y then 0 else unitMass n x * unitMass n y := by
  rw [← two_mul_sum_crossing_eq (le_refl σ), pairProductSum]
  congr 1
  exact Finset.sum_congr rfl fun t ht ↦ (if_neg (not_mergePair_le_self σ ht)).symm

/-! ### `Z_p` below a partition -/

/-- **`Z_p` leaves the partitions below `σ` at the constant rate `κ_σ`**: from any `ζ ≤ σ` it
stays below `σ` with probability `1 - κ_σ`. -/
theorem sum_filter_le_multiplicativeStep {n : ℕ} {ζ σ : ER n} (h : ζ ≤ σ) :
    ∑ ζ' ∈ univ.filter (· ≤ σ), multiplicativeStep n ζ ζ'
      = 1 - pairProductSum (blockMass (unitMass n) σ) := by
  have hA : ∑ ζ' ∈ univ.filter (· ≤ σ), ∑ t ∈ (univ.powersetCard 2).filter
        (fun t ↦ mergePair ζ t = ζ'), ∏ C ∈ t, blockMass (unitMass n) ζ C
      = ∑ t ∈ (univ : Finset (Quotient ζ)).powersetCard 2,
          if mergePair ζ t ≤ σ then ∏ C ∈ t, blockMass (unitMass n) ζ C else 0 := by
    rw [Finset.sum_filter]
    have hpoint : ∀ ζ' : ER n, (if ζ' ≤ σ then ∑ t ∈ (univ.powersetCard 2).filter
        (fun t ↦ mergePair ζ t = ζ'), ∏ C ∈ t, blockMass (unitMass n) ζ C else 0)
        = ∑ t ∈ (univ.powersetCard 2).filter (fun t ↦ mergePair ζ t = ζ'),
            if mergePair ζ t ≤ σ then ∏ C ∈ t, blockMass (unitMass n) ζ C else 0 := by
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
        (if mergePair ζ t ≤ σ then ∏ C ∈ t, blockMass (unitMass n) ζ C else 0)
      + ∑ t ∈ (univ : Finset (Quotient ζ)).powersetCard 2,
        (if mergePair ζ t ≤ σ then 0 else ∏ C ∈ t, blockMass (unitMass n) ζ C)
      = pairProductSum (blockMass (unitMass n) ζ) := by
    rw [← Finset.sum_add_distrib, pairProductSum]
    exact Finset.sum_congr rfl fun t _ ↦ by split_ifs <;> simp
  have hcross := two_mul_sum_crossing_eq h
  rw [← two_mul_pairProductSum_blockMass_unitMass σ] at hcross
  have hhold : ∑ ζ' ∈ univ.filter (· ≤ σ),
      (if ζ' = ζ then 1 - pairProductSum (blockMass (unitMass n) ζ) else 0)
      = 1 - pairProductSum (blockMass (unitMass n) ζ) := by
    rw [Finset.sum_ite_eq']
    have hmem : ζ ∈ univ.filter (· ≤ σ) := Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩
    exact if_pos hmem
  simp only [multiplicativeStep]
  rw [Finset.sum_add_distrib, hA, hhold]
  linarith

/-- From a state not below `σ`, `Z_p` never reaches a state below `σ`. -/
theorem sum_filter_le_multiplicativeStep_of_not_le {n : ℕ} {ζ σ : ER n} (h : ¬ ζ ≤ σ) :
    ∑ ζ' ∈ univ.filter (· ≤ σ), multiplicativeStep n ζ ζ' = 0 := by
  refine Finset.sum_eq_zero fun ζ' hζ' ↦ ?_
  have hle := (Finset.mem_filter.mp hζ').2
  unfold multiplicativeStep
  rw [Finset.sum_eq_zero fun t ht ↦ absurd
    (((Finset.mem_filter.mp ht).2 ▸ le_mergePair ζ t).trans hle) h, zero_add]
  exact if_neg fun (heq : ζ' = ζ) ↦ h (heq ▸ hle)

/-- **The uniformized `Z_p` law after `m` steps from the interface.**

Empirical status: NOT AN EMPIRICAL CLAIM.  A power of a finite kernel applied to a point mass. -/
def multiplicativeLaw {n : ℕ} (s : Fin n → Fin n) (m : ℕ) : ER n → ℝ :=
  skeletonLaw (multiplicativeStep n) (fun ζ ↦ if ζ = graphKer s then 1 else 0) m

/-- **`Z_p` is below `σ` after `m` steps with probability `(1 - κ_σ)^m`**, when the interface is
below `σ`, and never otherwise. -/
theorem sum_filter_le_multiplicativeLaw {n : ℕ} (s : Fin n → Fin n) (σ : ER n) (m : ℕ) :
    ∑ ζ ∈ univ.filter (· ≤ σ), multiplicativeLaw s m ζ
      = if graphKer s ≤ σ then (1 - pairProductSum (blockMass (unitMass n) σ)) ^ m else 0 := by
  induction m with
  | zero =>
    simp only [multiplicativeLaw, skeletonLaw, pow_zero]
    rw [Finset.sum_ite_eq']
    by_cases hq : graphKer s ≤ σ
    · have hmem : graphKer s ∈ univ.filter (· ≤ σ) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hq⟩
      rw [if_pos hmem, if_pos hq]
    · have hmem : graphKer s ∉ univ.filter (· ≤ σ) := fun hmem ↦ hq (Finset.mem_filter.mp hmem).2
      rw [if_neg hmem, if_neg hq]
  | succ m ih =>
    have h1 := sum_skeletonLaw_succ (multiplicativeStep n)
      (fun ζ ↦ if ζ = graphKer s then 1 else 0) m (univ.filter (· ≤ σ)) fun _ ↦ 1
    simp only [mul_one] at h1
    have hpoint : ∀ ζ : ER n, multiplicativeLaw s m ζ
        * ∑ ζ' ∈ univ.filter (· ≤ σ), multiplicativeStep n ζ ζ'
        = (if ζ ≤ σ then multiplicativeLaw s m ζ else 0)
          * (1 - pairProductSum (blockMass (unitMass n) σ)) := by
      intro ζ
      by_cases hζ : ζ ≤ σ
      · rw [if_pos hζ, sum_filter_le_multiplicativeStep hζ]
      · rw [if_neg hζ, sum_filter_le_multiplicativeStep_of_not_le hζ, mul_zero, zero_mul]
    have hstep : ∑ ζ ∈ univ.filter (· ≤ σ), multiplicativeLaw s (m + 1) ζ
        = ∑ ζ, multiplicativeLaw s m ζ
          * ∑ ζ' ∈ univ.filter (· ≤ σ), multiplicativeStep n ζ ζ' := h1
    rw [hstep, Finset.sum_congr rfl fun ζ _ ↦ hpoint ζ, ← Finset.sum_mul, ← Finset.sum_filter,
      ih]
    split_ifs <;> ring

/-! ### Möbius inversion at the top -/

/-- **A partition is the top exactly when the Möbius coefficients of the partitions above it add
up to one.**  `MultiplicativeConnectionLaw.sum_topMobius_blocks_ge`, as a weight on states. -/
theorem sum_topMobius_ite_le {n : ℕ} [NeZero n] (ζ : ER n) :
    ∑ σ : ER n, (topMobius (blocks σ) : ℝ) * (if ζ ≤ σ then 1 else 0)
      = if ζ = ⊤ then 1 else 0 := by
  have hsum : ∑ σ ∈ (univ : Finset (ER n)).filter (ζ ≤ ·), topMobius (blocks σ)
      = if ζ = ⊤ then 1 else 0 := by
    convert sum_topMobius_blocks_ge ζ
  have hcast : ((∑ σ ∈ (univ : Finset (ER n)).filter (ζ ≤ ·), topMobius (blocks σ) : ℤ) : ℝ)
      = ((if ζ = ⊤ then 1 else 0 : ℤ) : ℝ) := congrArg _ hsum
  push_cast [Finset.sum_filter] at hcast
  rw [← hcast]
  exact Finset.sum_congr rfl fun σ _ ↦ by split_ifs <;> simp

/-- **The connection probability of `Z_p` after `m` steps**, as a Möbius sum over the partitions
above the interface. -/
theorem sum_multiplicativeLaw_mul_top {n : ℕ} [NeZero n] (s : Fin n → Fin n) (m : ℕ) :
    ∑ ζ, multiplicativeLaw s m ζ * (if ζ = ⊤ then 1 else 0)
      = ∑ σ, (topMobius (blocks σ) : ℝ)
          * (if graphKer s ≤ σ then (1 - pairProductSum (blockMass (unitMass n) σ)) ^ m
            else 0) := by
  calc ∑ ζ, multiplicativeLaw s m ζ * (if ζ = ⊤ then 1 else 0)
      = ∑ ζ, multiplicativeLaw s m ζ
          * ∑ σ : ER n, (topMobius (blocks σ) : ℝ) * (if ζ ≤ σ then 1 else 0) := by
        simp only [sum_topMobius_ite_le]
    _ = ∑ σ : ER n, (topMobius (blocks σ) : ℝ)
          * ∑ ζ ∈ univ.filter (· ≤ σ), multiplicativeLaw s m ζ := by
        simp only [Finset.mul_sum, Finset.sum_filter]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun σ _ ↦ Finset.sum_congr rfl fun ζ _ ↦ by
          split_ifs <;> ring
    _ = _ := by
        simp only [sum_filter_le_multiplicativeLaw]

/-! ### Running at the rings of a Poisson clock -/

/-- **A geometric sequence mixed over a Poisson clock**: `Σ_m Pr(N = m) x^m = e^{-U (1 - x)}`. -/
theorem hasSum_poissonPMFReal_mul_pow (U : NNReal) (x : ℝ) :
    HasSum (fun m : ℕ ↦ poissonPMFReal U m * x ^ m) (Real.exp (-((U : ℝ) * (1 - x)))) := by
  have h := NormedSpace.expSeries_div_hasSum_exp ℝ ((U : ℝ) * x)
  rw [← Real.exp_eq_exp_ℝ] at h
  have h2 := h.mul_left (Real.exp (-(U : ℝ)))
  have hfun : (fun m : ℕ ↦ Real.exp (-(U : ℝ)) * (((U : ℝ) * x) ^ m / (m.factorial : ℝ)))
      = fun m ↦ poissonPMFReal U m * x ^ m := by
    funext m
    unfold poissonPMFReal
    rw [mul_pow]
    ring
  rw [hfun, ← Real.exp_add] at h2
  convert h2 using 2
  ring

/-- **`Z_p` is connected at scaled time `U` with the Möbius probability**
`Σ_{σ ≥ q} (-1)^{|σ|-1} (|σ|-1)! e^{-U κ_σ}`. -/
theorem hasSum_poissonPMFReal_mul_multiplicativeTop {n : ℕ} [NeZero n] (s : Fin n → Fin n)
    (U : NNReal) :
    HasSum (fun m ↦ poissonPMFReal U m
        * ∑ ζ, multiplicativeLaw s m ζ * (if ζ = ⊤ then 1 else 0))
      (∑ σ, (topMobius (blocks σ) : ℝ)
        * (if graphKer s ≤ σ then Real.exp (-((U : ℝ) * pairProductSum (blockMass (unitMass n) σ)))
          else 0)) := by
  simp only [sum_multiplicativeLaw_mul_top, Finset.mul_sum]
  refine hasSum_sum fun σ _ ↦ ?_
  by_cases hq : graphKer s ≤ σ
  · simp only [if_pos hq]
    have h := (hasSum_poissonPMFReal_mul_pow U
      (1 - pairProductSum (blockMass (unitMass n) σ))).mul_left (topMobius (blocks σ) : ℝ)
    rw [sub_sub_cancel] at h
    convert h using 1
    funext m
    ring
  · simp only [if_neg hq, mul_zero]
    exact hasSum_zero

/-! ### The report against `Z_p` -/

/-- **Lumping at a fixed time**: if a kernel's mass into every fiber of `π` depends only on the
image of the source, the image of its law is the law of the lumped kernel. -/
theorem sum_filter_skeletonLaw_comp_eq {S X : Type*} [Fintype S] [Fintype X] [DecidableEq X]
    (P : S → S → ℝ) (μ₀ : S → ℝ) (Q : X → X → ℝ) (ν₀ : X → ℝ) (π : S → X)
    (hlump : ∀ s x, ∑ t ∈ univ.filter (fun t ↦ π t = x), P s t = Q (π s) x)
    (hinit : ∀ x, ∑ s ∈ univ.filter (fun s ↦ π s = x), μ₀ s = ν₀ x) (m : ℕ) (x : X) :
    ∑ t ∈ univ.filter (fun t ↦ π t = x), skeletonLaw P μ₀ m t = skeletonLaw Q ν₀ m x := by
  induction m generalizing x with
  | zero => exact hinit x
  | succ m ih =>
    have h1 := sum_skeletonLaw_succ P μ₀ m (univ.filter fun t ↦ π t = x) fun _ ↦ 1
    simp only [mul_one, hlump] at h1
    rw [h1]
    show _ = ∑ y, skeletonLaw Q ν₀ m y * Q y x
    rw [← Finset.sum_fiberwise univ π fun s ↦ skeletonLaw P μ₀ m s * Q (π s) x]
    refine Finset.sum_congr rfl fun y _ ↦ ?_
    rw [← ih y, Finset.sum_mul]
    exact Finset.sum_congr rfl fun t ht ↦ by rw [(Finset.mem_filter.mp ht).2]

/-- **The uniformized Kingman law after `m` steps from the panel's singletons.**

Empirical status: NOT AN EMPIRICAL CLAIM.  A power of a finite kernel applied to a point mass. -/
def kingmanLaw (n m : ℕ) : ER n → ℝ :=
  skeletonLaw (kingmanStep n) (fun ξ ↦ if ξ = ⊥ then 1 else 0) m

/-- A functional of the Kingman coordinate is a functional of the coupled chain. -/
theorem sum_kingmanLaw_mul_eq {n : ℕ} (s : Fin n → Fin n) (m : ℕ) (g : ER n → ℝ) :
    ∑ ξ, kingmanLaw n m ξ * g ξ
      = ∑ X, skeletonLaw (coupledStep s) (coupledStartLaw s) m X * g X.1 := by
  rw [← Finset.sum_fiberwise univ Prod.fst
    fun X ↦ skeletonLaw (coupledStep s) (coupledStartLaw s) m X * g X.1]
  refine Finset.sum_congr rfl fun ξ _ ↦ ?_
  rw [kingmanLaw, ← sum_filter_skeletonLaw_comp_eq (coupledStep s) (coupledStartLaw s)
    (kingmanStep n) (fun ξ ↦ if ξ = ⊥ then 1 else 0) Prod.fst
    (fun X ξ' ↦ sum_coupledStep_fst s X ξ') (sum_filter_fst_coupledStartLaw s) m ξ,
    Finset.sum_mul]
  exact Finset.sum_congr rfl fun X hX ↦ by rw [(Finset.mem_filter.mp hX).2]

/-- A functional of the `Z_p` coordinate is a functional of the coupled chain. -/
theorem sum_multiplicativeLaw_mul_eq {n : ℕ} (s : Fin n → Fin n) (m : ℕ) (g : ER n → ℝ) :
    ∑ ζ, multiplicativeLaw s m ζ * g ζ
      = ∑ X, skeletonLaw (coupledStep s) (coupledStartLaw s) m X * g X.2.1 := by
  rw [← Finset.sum_fiberwise univ (fun X : CoupledState n ↦ X.2.1)
    fun X ↦ skeletonLaw (coupledStep s) (coupledStartLaw s) m X * g X.2.1]
  refine Finset.sum_congr rfl fun ζ _ ↦ ?_
  rw [multiplicativeLaw, ← sum_filter_skeletonLaw_comp_eq (coupledStep s) (coupledStartLaw s)
    (multiplicativeStep n) (fun ζ ↦ if ζ = graphKer s then 1 else 0) (fun X ↦ X.2.1)
    (fun X ζ' ↦ sum_coupledStep_snd s X ζ') (sum_filter_snd_coupledStartLaw s) m ζ,
    Finset.sum_mul]
  exact Finset.sum_congr rfl fun X hX ↦ by rw [(Finset.mem_filter.mp hX).2]

/-- **After `m` steps the report and `Z_p` are connected with probabilities at most
`m(m-1)/(4n)` apart.**

Assumes: `0 < n`. -/
theorem abs_sub_connectionMass_le {n : ℕ} (hn : 0 < n) (s : Fin n → Fin n) (m : ℕ) :
    |∑ ξ, kingmanLaw n m ξ * (if observed s ξ = ⊤ then 1 else 0)
        - ∑ ζ, multiplicativeLaw s m ζ * (if ζ = ⊤ then 1 else 0)|
      ≤ (m : ℝ) * ((m : ℝ) - 1) / (4 * n) := by
  rw [sum_kingmanLaw_mul_eq s m, sum_multiplicativeLaw_mul_eq s m, ← Finset.sum_sub_distrib]
  refine le_trans ?_ (coupled_separationMass_le hn s m)
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [separationMass, Finset.sum_filter]
  refine Finset.sum_le_sum fun X _ ↦ ?_
  have hlaw := skeletonLaw_nonneg (coupledStep_nonneg hn s) (coupledStartLaw_nonneg s) m X
  by_cases hX : coupledSep s X
  · rw [if_pos hX, ← mul_sub, abs_mul, abs_of_nonneg hlaw]
    calc _ ≤ skeletonLaw (coupledStep s) (coupledStartLaw s) m X * 1 :=
          mul_le_mul_of_nonneg_left (by split_ifs <;> norm_num) hlaw
      _ = _ := mul_one _
  · have hzero : skeletonLaw (coupledStep s) (coupledStartLaw s) m X
          * (if observed s X.1 = ⊤ then (1 : ℝ) else 0)
        - skeletonLaw (coupledStep s) (coupledStartLaw s) m X * (if X.2.1 = ⊤ then 1 else 0)
        = 0 := by
      rw [observed_eq_of_not_coupledSep hX, sub_self]
    rw [if_neg hX, hzero, abs_zero]

/-- **The probability that the graph's report is connected at scaled time `U`**, for the
uniformized genealogy run at the rings of a Poisson clock of rate one.

Empirical status: NOT AN EMPIRICAL CLAIM.  A Poisson mixture of finite sums. -/
def reportConnectionProbability {n : ℕ} (s : Fin n → Fin n) (U : NNReal) : ℝ :=
  poissonMixture U fun m ↦ ∑ ξ, kingmanLaw n m ξ * (if observed s ξ = ⊤ then 1 else 0)

/-- The connection mass of a probability vector is a probability. -/
theorem sum_mul_ite_mem_unit {S : Type*} [Fintype S] {μ : S → ℝ} (hμ : ∀ s, 0 ≤ μ s)
    (hμ1 : ∑ s, μ s = 1) (p : S → Prop) :
    0 ≤ ∑ s, μ s * (if p s then 1 else 0) ∧ ∑ s, μ s * (if p s then 1 else 0) ≤ 1 := by
  refine ⟨Finset.sum_nonneg fun s _ ↦ mul_nonneg (hμ s) (by split_ifs <;> norm_num), ?_⟩
  calc ∑ s, μ s * (if p s then 1 else 0) ≤ ∑ s, μ s :=
        Finset.sum_le_sum fun s _ ↦ by
          split_ifs
          · rw [mul_one]
          · rw [mul_zero]
            exact hμ s
    _ = 1 := hμ1

/-- **(F3), quantitative.**  The probability that the graph's report is connected at scaled time
`U` is within `U²/(4n)` of the Möbius sum `Σ_{σ ≥ q} (-1)^{|σ|-1} (|σ|-1)! e^{-U κ_σ}`, which is
the probability that the multiplicative coalescent started at the interface is connected.

Assumes: `0 < n`. -/
theorem abs_reportConnectionProbability_sub_le {n : ℕ} (hn : 0 < n) (s : Fin n → Fin n)
    (U : NNReal) :
    |reportConnectionProbability s U
        - ∑ σ, (topMobius (blocks σ) : ℝ)
          * (if graphKer s ≤ σ then
              Real.exp (-((U : ℝ) * pairProductSum (blockMass (unitMass n) σ))) else 0)|
      ≤ (U : ℝ) ^ 2 / (4 * n) := by
  haveI : NeZero n := ⟨hn.ne'⟩
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  set a : ℕ → ℝ := fun m ↦ ∑ ξ, kingmanLaw n m ξ * (if observed s ξ = ⊤ then 1 else 0) with ha
  set b : ℕ → ℝ := fun m ↦ ∑ ζ, multiplicativeLaw s m ζ * (if ζ = ⊤ then 1 else 0) with hb
  have haunit : ∀ m, 0 ≤ a m ∧ a m ≤ 1 := fun m ↦
    sum_mul_ite_mem_unit (skeletonLaw_nonneg (fun ξ ξ' ↦ kingmanStep_nonneg (blocks_le_card ξ) ξ')
      (fun ξ ↦ by split_ifs <;> norm_num) m)
      ((sum_skeletonLaw sum_kingmanStep m).trans (by simp)) _
  have hA : HasSum (fun m ↦ poissonPMFReal U m * a m) (reportConnectionProbability s U) := by
    have hsum : Summable fun m ↦ poissonPMFReal U m * a m :=
      Summable.of_nonneg_of_le (fun m ↦ mul_nonneg poissonPMFReal_nonneg (haunit m).1)
        (fun m ↦ by
          calc poissonPMFReal U m * a m ≤ poissonPMFReal U m * 1 :=
                mul_le_mul_of_nonneg_left (haunit m).2 poissonPMFReal_nonneg
            _ = poissonPMFReal U m := mul_one _)
        (poissonPMFRealSum U).summable
    exact hsum.hasSum
  have hB := hasSum_poissonPMFReal_mul_multiplicativeTop s U
  have hD := (hasSum_poissonPMFReal_mul_descFactorial U).div_const (4 * n)
  have hterm : ∀ m, |poissonPMFReal U m * a m - poissonPMFReal U m * b m|
      ≤ poissonPMFReal U m * ((m : ℝ) * ((m : ℝ) - 1)) / (4 * n) := by
    intro m
    rw [← mul_sub, abs_mul, abs_of_nonneg poissonPMFReal_nonneg, mul_div_assoc]
    exact mul_le_mul_of_nonneg_left (abs_sub_connectionMass_le hn s m) poissonPMFReal_nonneg
  rw [abs_sub_le_iff]
  constructor
  · exact hasSum_le (fun m ↦ (le_abs_self _).trans (hterm m)) (hA.sub hB) hD
  · exact hasSum_le (fun m ↦ (le_abs_self _).trans (by rw [abs_sub_comm]; exact hterm m))
      (hB.sub hA) hD

end

end Descent.Pangenome.GraphCoalescent
