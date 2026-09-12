/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.GraphCoalescent.ConnectivityCumulantCorpus
import Descent.Pangenome.GraphCoalescent.ReportedConnectionClock

assert_below Descent.PopGen Descent.Spectral Descent.Blindness Descent.Conditionals
assert_below Descent.Portability Descent.Decision Descent.Program

/-!
# The exact reported connection times of the §6 table

`ReportedConnectionClock` proves (D8), `E τ_q = 2 ∑_b p_b / b - 2/n`, with `p_b = F_b - F_{b+1}`
and `F_k = a_{n,k} [z^k] C_c(z)`, the coefficient counted as `connectionCount s k`.  This file
evaluates that expectation at the five interfaces of the note's table: fiber sizes
`(1,2), (1,3), (2,2), (1,1,2), (2,2,2)` give `2/3, 1/2, 7/18, 17/18, 92/225`.  The fiber sizes
`(1,3)` and `(2,2)` share `n = 4` and width `w = 2` and have different means, so the width does
not determine the clock (`connectionTime_mean_oneThree_ne_twoTwo`).

## Kernel computation

The counts `connectionCount s k` are sums over `𝓔ₙ`, which has no computable enumeration.
`minMaps n` is one: the maps `g : Fin n → Fin n` with `g x ≤ x` that fix their image, which are
the class-minimum maps of the states (`sum_ER_eq_sum_minMaps`, through `classMinOf` and
`Setoid.ker`).  On such a map the block count is the size of the image, Kingman's weight is a
product of rank counts, and a connected report is a finite check: every set of graph states
that no class straddles is empty or everything (`observed_eq_top_iff_saturated`).
`connectionCount_eq_minMapCount` transports the count, and `decide +kernel` evaluates it.  No
`native_decide` is used.

`connectionCount_eq_coeff_connectivityCumulant` ties the count to the corpus cumulant of
`ConnectivityCumulantCorpus`: `connectionCount s k` is the `z^k` coefficient of
`connectivityCumulant (ofSetoid (graphKer s))`.  The polynomials of
`ConnectivityClockTable` are `cumulantOfSizes` over `Fin 2` and `Fin 3`.  That they are these
cumulants is not proved here; the counts computed below agree with their coefficients.

## Empirical status

None.  The interfaces are explicit maps on `Fin n` and the values are finite computations and
rational arithmetic on the theorems of `ReportedConnectionClock`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Pangenome.GraphCoalescent

open Finset Coalescent MeasureTheory Polynomial
open scoped Nat ENNReal

/-! ### A computable enumeration of `𝓔ₙ` -/

/-- The class-minimum maps: every sample goes to a sample at or below it, and the image is
fixed. -/
def minMaps (n : ℕ) : Finset (Fin n → Fin n) :=
  (Fintype.piFinset fun x : Fin n ↦ Iic x).filter fun g ↦ ∀ x, g (g x) = g x

/-- The connected weighted count at `k` blocks, computed over the class-minimum maps. -/
def minMapCount {n : ℕ} (s : Fin n → Fin n) (k : ℕ) : ℕ :=
  ∑ g ∈ (minMaps n).filter (fun g ↦ (univ.image g).card = k ∧
      ∀ V : Finset (Fin n), (∀ x y, g x = g y → (s x ∈ V ↔ s y ∈ V)) →
        (∀ x, s x ∈ V) ∨ ∀ x, s x ∉ V),
    ∏ x, (univ.filter fun y ↦ y ≤ x ∧ g x = g y).card

theorem mem_minMaps {n : ℕ} {g : Fin n → Fin n} :
    g ∈ minMaps n ↔ (∀ x, g x ≤ x) ∧ ∀ x, g (g x) = g x := by
  simp only [minMaps, mem_filter, Fintype.mem_piFinset, mem_Iic]

/-- A state is the kernel of its class-minimum map. -/
theorem ker_classMinOf {n : ℕ} (η : ER n) : Setoid.ker (classMinOf η) = η := by
  refine Setoid.ext fun x y ↦ ?_
  show classMinOf η x = classMinOf η y ↔ η.r x y
  constructor
  · intro h
    have hx := classMinOf_rel η x
    rw [h] at hx
    exact η.iseqv.trans hx (η.iseqv.symm (classMinOf_rel η y))
  · intro h
    exact (classMinOf_eq_iff (classMinOf_mem_classMinima η y)).mpr
      (η.iseqv.trans (η.iseqv.symm (classMinOf_rel η y)) (η.iseqv.symm h))

theorem classMinOf_mem_minMaps {n : ℕ} (η : ER n) : classMinOf η ∈ minMaps n :=
  mem_minMaps.mpr ⟨fun x ↦ classMinOf_le (η.iseqv.refl x),
    fun x ↦ (classMinOf_eq_iff (classMinOf_mem_classMinima η x)).mpr (η.iseqv.refl _)⟩

/-- A class-minimum map is the class-minimum map of its kernel. -/
theorem classMinOf_ker {n : ℕ} {g : Fin n → Fin n} (hg : g ∈ minMaps n) :
    classMinOf (Setoid.ker g) = g := by
  obtain ⟨hle, hidem⟩ := mem_minMaps.mp hg
  funext x
  have hmin : g x ∈ classMinima (Setoid.ker g) := by
    refine mem_classMinima.mpr fun y hy ↦ ?_
    have hy' : g (g x) = g y := hy
    rw [hidem x] at hy'
    exact hy' ▸ hle y
  exact (classMinOf_eq_iff hmin).mpr (hidem x)

/-- **`𝓔ₙ` enumerated by class-minimum maps.** -/
theorem sum_ER_eq_sum_minMaps {n : ℕ} {M : Type*} [AddCommMonoid M] (F : ER n → M) :
    ∑ ξ : ER n, F ξ = ∑ g ∈ minMaps n, F (Setoid.ker g) :=
  sum_nbij' classMinOf Setoid.ker (fun η _ ↦ classMinOf_mem_minMaps η) (fun _ _ ↦ mem_univ _)
    (fun η _ ↦ ker_classMinOf η) (fun _ hg ↦ classMinOf_ker hg) fun η _ ↦ by rw [ker_classMinOf]

/-- The blocks of a kernel are the image of the map. -/
theorem blocks_ker {n : ℕ} (g : Fin n → Fin n) :
    blocks (Setoid.ker g) = (univ.image g).card := by
  rw [blocks, Nat.card_congr (Setoid.quotientKerEquivRange g), Nat.card_eq_fintype_card,
    ← Set.toFinset_card, Set.toFinset_range]

theorem rankWeight_ker {n : ℕ} (g : Fin n → Fin n) :
    rankWeight (Setoid.ker g) = ∏ x, (univ.filter fun y ↦ y ≤ x ∧ g x = g y).card := by
  refine prod_congr rfl fun x _ ↦ ?_
  unfold classRank sampleClass
  congr 1
  ext y
  simp only [mem_filter, mem_univ, true_and]
  exact ⟨fun h ↦ ⟨h.2, h.1⟩, fun h ↦ ⟨h.2, h.1⟩⟩

open scoped Classical in
/-- **A connected report is a finite check.**  The report `π ⊔ graphKer s` is `⊤` exactly when
every set of graph states that no class of `π` straddles is empty or everything. -/
theorem observed_eq_top_iff_saturated {n : ℕ} (hn : 0 < n) (s : Fin n → Fin n) (π : ER n) :
    observed s π = ⊤ ↔ ∀ V : Finset (Fin n), (∀ x y, π.r x y → (s x ∈ V ↔ s y ∈ V)) →
      (∀ x, s x ∈ V) ∨ ∀ x, s x ∉ V := by
  constructor
  · intro htop V hV
    let ζ : ER n := Setoid.ker fun x ↦ decide (s x ∈ V)
    have hle : observed s π ≤ ζ := by
      refine observed_le (fun x y hxy ↦ ?_) (fun x y hxy ↦ ?_)
      · show decide (s x ∈ V) = decide (s y ∈ V)
        rw [decide_eq_decide]
        exact hV x y hxy
      · show decide (s x ∈ V) = decide (s y ∈ V)
        rw [graphKer_rel_iff.mp hxy]
    rw [htop] at hle
    have hall : ∀ x y : Fin n, (s x ∈ V ↔ s y ∈ V) := fun x y ↦
      decide_eq_decide.mp (@hle x y trivial)
    by_cases h0 : s ⟨0, hn⟩ ∈ V
    · exact Or.inl fun x ↦ (hall ⟨0, hn⟩ x).mp h0
    · exact Or.inr fun x hx ↦ h0 ((hall ⟨0, hn⟩ x).mpr hx)
  · intro h
    set ζ := observed s π with hζ
    let x0 : Fin n := ⟨0, hn⟩
    let V : Finset (Fin n) := (univ.filter fun x ↦ ζ.r x0 x).image s
    have hmem : ∀ x, s x ∈ V ↔ ζ.r x0 x := by
      intro x
      constructor
      · intro hx
        obtain ⟨x', hx', hsx⟩ := mem_image.mp hx
        have h1 : ζ.r x0 x' := (mem_filter.mp hx').2
        have h2 : ζ.r x' x := graphKer_le_observed s π (graphKer_rel_iff.mpr hsx)
        exact ζ.iseqv.trans h1 h2
      · intro hx
        exact mem_image.mpr ⟨x, mem_filter.mpr ⟨mem_univ x, hx⟩, rfl⟩
    have hsat : ∀ x y, π.r x y → (s x ∈ V ↔ s y ∈ V) := by
      intro x y hxy
      rw [hmem, hmem]
      have h3 : ζ.r x y := le_observed s π hxy
      exact ⟨fun h ↦ ζ.iseqv.trans h h3, fun h ↦ ζ.iseqv.trans h (ζ.iseqv.symm h3)⟩
    rcases h V hsat with hall | hnone
    · refine eq_top_iff.mpr fun x y _ ↦ ?_
      exact ζ.iseqv.trans (ζ.iseqv.symm ((hmem x).mp (hall x))) ((hmem y).mp (hall y))
    · exact absurd ((hmem x0).mpr (ζ.iseqv.refl x0)) (hnone x0)

/-- **The count of (D5), over class-minimum maps.** -/
theorem connectionCount_eq_minMapCount {n : ℕ} (hn : 0 < n) (s : Fin n → Fin n) (k : ℕ) :
    connectionCount s k = minMapCount s k := by
  unfold connectionCount minMapCount
  rw [sum_filter, sum_filter, sum_ER_eq_sum_minMaps]
  refine sum_congr rfl fun g _ ↦ ?_
  have hiff : (blocks (Setoid.ker g) = k ∧ observed s (Setoid.ker g) = ⊤) ↔
      ((univ.image g).card = k ∧ ∀ V : Finset (Fin n),
        (∀ x y, g x = g y → (s x ∈ V ↔ s y ∈ V)) → (∀ x, s x ∈ V) ∨ ∀ x, s x ∉ V) := by
    rw [blocks_ker]
    exact and_congr Iff.rfl (observed_eq_top_iff_saturated hn s (Setoid.ker g))
  by_cases h : (univ.image g).card = k ∧ ∀ V : Finset (Fin n),
      (∀ x y, g x = g y → (s x ∈ V ↔ s y ∈ V)) → (∀ x, s x ∈ V) ∨ ∀ x, s x ∉ V
  · rw [if_pos (hiff.mpr h), if_pos h, ← rankWeight_eq_blockWeight, rankWeight_ker]
  · rw [if_neg fun h' ↦ h (hiff.mp h'), if_neg h]

open scoped Classical in
/-- **(D5)'s count is the corpus cumulant's coefficient**: `connectionCount s k` is the `z^k`
coefficient of the (D3) polynomial at `graphKer s`, which
`ConnectivityCumulantCorpus.coeff_connectivityCumulant_graphKer` computes as the connected
weighted count. -/
theorem connectionCount_eq_coeff_connectivityCumulant {n : ℕ} (hn : 0 < n) (s : Fin n → Fin n)
    (k : ℕ) :
    (connectionCount s k : ℤ)
      = (connectivityCumulant (Finpartition.ofSetoid (graphKer s))).coeff k :=
  (coeff_connectivityCumulant_graphKer s hn k).symm

/-! ### The interfaces of the table -/

/-- Fiber sizes `(1, 2)`: sample `0` alone, samples `1, 2` sharing a graph state. -/
def interfaceOneTwo : Fin 3 → Fin 3 := ![0, 1, 1]

/-- Fiber sizes `(1, 3)`. -/
def interfaceOneThree : Fin 4 → Fin 4 := ![0, 1, 1, 1]

/-- Fiber sizes `(2, 2)`. -/
def interfaceTwoTwo : Fin 4 → Fin 4 := ![0, 0, 2, 2]

/-- Fiber sizes `(1, 1, 2)`. -/
def interfaceOneOneTwo : Fin 4 → Fin 4 := ![0, 1, 2, 2]

/-- Fiber sizes `(2, 2, 2)`. -/
def interfaceTwoTwoTwo : Fin 6 → Fin 6 := ![0, 0, 2, 2, 4, 4]

/-- **Fiber sizes `(1,2)`: `E τ_q = 2/3`.** -/
theorem connectionTime_mean_oneTwo :
    ∫⁻ p, ENNReal.ofReal (connectionTime interfaceOneTwo p) ∂(trajectoryClockLaw 3)
      = ENNReal.ofReal (2 / 3) := by
  have hw : 2 ≤ Linkage.width interfaceOneTwo := by decide +kernel
  have hc2 : minMapCount interfaceOneTwo 2 = 4 := by decide +kernel
  have hF1 := connectedProb_one interfaceOneTwo (by norm_num)
  have hF2 : connectedProb interfaceOneTwo 2 = 2 / 3 := by
    rw [connectedProb_eq interfaceOneTwo (k := 2) (by norm_num) (by norm_num),
      connectionCount_eq_minMapCount (by norm_num), hc2]
    norm_num [jumpCoeff, Nat.factorial]
  have hF3 := connectedProb_self hw
  have hp1 : stoppingProb interfaceOneTwo 1
      = connectedProb interfaceOneTwo 1 - connectedProb interfaceOneTwo 2 :=
    stoppingProb_eq interfaceOneTwo (b := 1) (by norm_num) (by norm_num)
  have hp2 : stoppingProb interfaceOneTwo 2
      = connectedProb interfaceOneTwo 2 - connectedProb interfaceOneTwo 3 :=
    stoppingProb_eq interfaceOneTwo (b := 2) (by norm_num) (by norm_num)
  have hp3 := stoppingProb_self (by norm_num) interfaceOneTwo
  rw [connectionTime_mean (by norm_num) interfaceOneTwo, show Icc 1 3 = {1, 2, 3} by decide]
  simp (disch := decide) only [sum_insert, sum_singleton, hp1, hp2, hp3, hF1, hF2, hF3]
  norm_num

/-- **Fiber sizes `(1,3)`: `E τ_q = 1/2`.** -/
theorem connectionTime_mean_oneThree :
    ∫⁻ p, ENNReal.ofReal (connectionTime interfaceOneThree p) ∂(trajectoryClockLaw 4)
      = ENNReal.ofReal (1 / 2) := by
  have hw : 2 ≤ Linkage.width interfaceOneThree := by decide +kernel
  have hc2 : minMapCount interfaceOneThree 2 = 30 := by decide +kernel
  have hc3 : minMapCount interfaceOneThree 3 = 6 := by decide +kernel
  have hF1 := connectedProb_one interfaceOneThree (by norm_num)
  have hF2 : connectedProb interfaceOneThree 2 = 5 / 6 := by
    rw [connectedProb_eq interfaceOneThree (k := 2) (by norm_num) (by norm_num),
      connectionCount_eq_minMapCount (by norm_num), hc2]
    norm_num [jumpCoeff, Nat.factorial]
  have hF3 : connectedProb interfaceOneThree 3 = 1 / 2 := by
    rw [connectedProb_eq interfaceOneThree (k := 3) (by norm_num) (by norm_num),
      connectionCount_eq_minMapCount (by norm_num), hc3]
    norm_num [jumpCoeff, Nat.factorial]
  have hF4 := connectedProb_self hw
  have hp1 : stoppingProb interfaceOneThree 1
      = connectedProb interfaceOneThree 1 - connectedProb interfaceOneThree 2 :=
    stoppingProb_eq interfaceOneThree (b := 1) (by norm_num) (by norm_num)
  have hp2 : stoppingProb interfaceOneThree 2
      = connectedProb interfaceOneThree 2 - connectedProb interfaceOneThree 3 :=
    stoppingProb_eq interfaceOneThree (b := 2) (by norm_num) (by norm_num)
  have hp3 : stoppingProb interfaceOneThree 3
      = connectedProb interfaceOneThree 3 - connectedProb interfaceOneThree 4 :=
    stoppingProb_eq interfaceOneThree (b := 3) (by norm_num) (by norm_num)
  have hp4 := stoppingProb_self (by norm_num) interfaceOneThree
  rw [connectionTime_mean (by norm_num) interfaceOneThree,
    show Icc 1 4 = {1, 2, 3, 4} by decide]
  simp (disch := decide) only [sum_insert, sum_singleton, hp1, hp2, hp3, hp4, hF1, hF2, hF3,
    hF4]
  norm_num

/-- **Fiber sizes `(2,2)`: `E τ_q = 7/18`.** -/
theorem connectionTime_mean_twoTwo :
    ∫⁻ p, ENNReal.ofReal (connectionTime interfaceTwoTwo p) ∂(trajectoryClockLaw 4)
      = ENNReal.ofReal (7 / 18) := by
  have hw : 2 ≤ Linkage.width interfaceTwoTwo := by decide +kernel
  have hc2 : minMapCount interfaceTwoTwo 2 = 32 := by decide +kernel
  have hc3 : minMapCount interfaceTwoTwo 3 = 8 := by decide +kernel
  have hF1 := connectedProb_one interfaceTwoTwo (by norm_num)
  have hF2 : connectedProb interfaceTwoTwo 2 = 8 / 9 := by
    rw [connectedProb_eq interfaceTwoTwo (k := 2) (by norm_num) (by norm_num),
      connectionCount_eq_minMapCount (by norm_num), hc2]
    norm_num [jumpCoeff, Nat.factorial]
  have hF3 : connectedProb interfaceTwoTwo 3 = 2 / 3 := by
    rw [connectedProb_eq interfaceTwoTwo (k := 3) (by norm_num) (by norm_num),
      connectionCount_eq_minMapCount (by norm_num), hc3]
    norm_num [jumpCoeff, Nat.factorial]
  have hF4 := connectedProb_self hw
  have hp1 : stoppingProb interfaceTwoTwo 1
      = connectedProb interfaceTwoTwo 1 - connectedProb interfaceTwoTwo 2 :=
    stoppingProb_eq interfaceTwoTwo (b := 1) (by norm_num) (by norm_num)
  have hp2 : stoppingProb interfaceTwoTwo 2
      = connectedProb interfaceTwoTwo 2 - connectedProb interfaceTwoTwo 3 :=
    stoppingProb_eq interfaceTwoTwo (b := 2) (by norm_num) (by norm_num)
  have hp3 : stoppingProb interfaceTwoTwo 3
      = connectedProb interfaceTwoTwo 3 - connectedProb interfaceTwoTwo 4 :=
    stoppingProb_eq interfaceTwoTwo (b := 3) (by norm_num) (by norm_num)
  have hp4 := stoppingProb_self (by norm_num) interfaceTwoTwo
  rw [connectionTime_mean (by norm_num) interfaceTwoTwo, show Icc 1 4 = {1, 2, 3, 4} by decide]
  simp (disch := decide) only [sum_insert, sum_singleton, hp1, hp2, hp3, hp4, hF1, hF2, hF3,
    hF4]
  norm_num

/-- **Fiber sizes `(1,1,2)`: `E τ_q = 17/18`.** -/
theorem connectionTime_mean_oneOneTwo :
    ∫⁻ p, ENNReal.ofReal (connectionTime interfaceOneOneTwo p) ∂(trajectoryClockLaw 4)
      = ENNReal.ofReal (17 / 18) := by
  have hw : 2 ≤ Linkage.width interfaceOneOneTwo := by decide +kernel
  have hc2 : minMapCount interfaceOneOneTwo 2 = 20 := by decide +kernel
  have hc3 : minMapCount interfaceOneOneTwo 3 = 0 := by decide +kernel
  have hF1 := connectedProb_one interfaceOneOneTwo (by norm_num)
  have hF2 : connectedProb interfaceOneOneTwo 2 = 5 / 9 := by
    rw [connectedProb_eq interfaceOneOneTwo (k := 2) (by norm_num) (by norm_num),
      connectionCount_eq_minMapCount (by norm_num), hc2]
    norm_num [jumpCoeff, Nat.factorial]
  have hF3 : connectedProb interfaceOneOneTwo 3 = 0 := by
    rw [connectedProb_eq interfaceOneOneTwo (k := 3) (by norm_num) (by norm_num),
      connectionCount_eq_minMapCount (by norm_num), hc3]
    norm_num
  have hF4 := connectedProb_self hw
  have hp1 : stoppingProb interfaceOneOneTwo 1
      = connectedProb interfaceOneOneTwo 1 - connectedProb interfaceOneOneTwo 2 :=
    stoppingProb_eq interfaceOneOneTwo (b := 1) (by norm_num) (by norm_num)
  have hp2 : stoppingProb interfaceOneOneTwo 2
      = connectedProb interfaceOneOneTwo 2 - connectedProb interfaceOneOneTwo 3 :=
    stoppingProb_eq interfaceOneOneTwo (b := 2) (by norm_num) (by norm_num)
  have hp3 : stoppingProb interfaceOneOneTwo 3
      = connectedProb interfaceOneOneTwo 3 - connectedProb interfaceOneOneTwo 4 :=
    stoppingProb_eq interfaceOneOneTwo (b := 3) (by norm_num) (by norm_num)
  have hp4 := stoppingProb_self (by norm_num) interfaceOneOneTwo
  rw [connectionTime_mean (by norm_num) interfaceOneOneTwo,
    show Icc 1 4 = {1, 2, 3, 4} by decide]
  simp (disch := decide) only [sum_insert, sum_singleton, hp1, hp2, hp3, hp4, hF1, hF2, hF3,
    hF4]
  norm_num

/-- The connected weighted counts of the interface `(2,2,2)`, by kernel evaluation over the
`203` class-minimum maps of `Fin 6`. -/
theorem minMapCount_twoTwoTwo :
    minMapCount interfaceTwoTwoTwo 2 = 1656 ∧ minMapCount interfaceTwoTwoTwo 3 = 928 ∧
      minMapCount interfaceTwoTwoTwo 4 = 144 ∧ minMapCount interfaceTwoTwoTwo 5 = 0 := by
  decide +kernel

/-- `F_2, …, F_5` at the interface `(2,2,2)`. -/
theorem connectedProb_twoTwoTwo :
    connectedProb interfaceTwoTwoTwo 2 = 23 / 25 ∧
      connectedProb interfaceTwoTwoTwo 3 = 58 / 75 ∧
      connectedProb interfaceTwoTwoTwo 4 = 12 / 25 ∧
      connectedProb interfaceTwoTwoTwo 5 = 0 := by
  obtain ⟨h2, h3, h4, h5⟩ := minMapCount_twoTwoTwo
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [connectedProb_eq interfaceTwoTwoTwo (k := 2) (by norm_num) (by norm_num),
      connectionCount_eq_minMapCount (by norm_num), h2]
    norm_num [jumpCoeff, Nat.factorial]
  · rw [connectedProb_eq interfaceTwoTwoTwo (k := 3) (by norm_num) (by norm_num),
      connectionCount_eq_minMapCount (by norm_num), h3]
    norm_num [jumpCoeff, Nat.factorial]
  · rw [connectedProb_eq interfaceTwoTwoTwo (k := 4) (by norm_num) (by norm_num),
      connectionCount_eq_minMapCount (by norm_num), h4]
    norm_num [jumpCoeff, Nat.factorial]
  · rw [connectedProb_eq interfaceTwoTwoTwo (k := 5) (by norm_num) (by norm_num),
      connectionCount_eq_minMapCount (by norm_num), h5]
    norm_num

/-- **Fiber sizes `(2,2,2)`: `E τ_q = 92/225`.** -/
theorem connectionTime_mean_twoTwoTwo :
    ∫⁻ p, ENNReal.ofReal (connectionTime interfaceTwoTwoTwo p) ∂(trajectoryClockLaw 6)
      = ENNReal.ofReal (92 / 225) := by
  have hw : 2 ≤ Linkage.width interfaceTwoTwoTwo := by decide +kernel
  obtain ⟨hF2, hF3, hF4, hF5⟩ := connectedProb_twoTwoTwo
  have hF1 := connectedProb_one interfaceTwoTwoTwo (by norm_num)
  have hF6 := connectedProb_self hw
  have hp1 : stoppingProb interfaceTwoTwoTwo 1
      = connectedProb interfaceTwoTwoTwo 1 - connectedProb interfaceTwoTwoTwo 2 :=
    stoppingProb_eq interfaceTwoTwoTwo (b := 1) (by norm_num) (by norm_num)
  have hp2 : stoppingProb interfaceTwoTwoTwo 2
      = connectedProb interfaceTwoTwoTwo 2 - connectedProb interfaceTwoTwoTwo 3 :=
    stoppingProb_eq interfaceTwoTwoTwo (b := 2) (by norm_num) (by norm_num)
  have hp3 : stoppingProb interfaceTwoTwoTwo 3
      = connectedProb interfaceTwoTwoTwo 3 - connectedProb interfaceTwoTwoTwo 4 :=
    stoppingProb_eq interfaceTwoTwoTwo (b := 3) (by norm_num) (by norm_num)
  have hp4 : stoppingProb interfaceTwoTwoTwo 4
      = connectedProb interfaceTwoTwoTwo 4 - connectedProb interfaceTwoTwoTwo 5 :=
    stoppingProb_eq interfaceTwoTwoTwo (b := 4) (by norm_num) (by norm_num)
  have hp5 : stoppingProb interfaceTwoTwoTwo 5
      = connectedProb interfaceTwoTwoTwo 5 - connectedProb interfaceTwoTwoTwo 6 :=
    stoppingProb_eq interfaceTwoTwoTwo (b := 5) (by norm_num) (by norm_num)
  have hp6 := stoppingProb_self (by norm_num) interfaceTwoTwoTwo
  rw [connectionTime_mean (by norm_num) interfaceTwoTwoTwo,
    show Icc 1 6 = {1, 2, 3, 4, 5, 6} by decide +kernel]
  simp (disch := decide +kernel) only [sum_insert, sum_singleton, hp1, hp2, hp3, hp4, hp5, hp6,
    hF1, hF2, hF3, hF4, hF5, hF6]
  norm_num

/-- **The width does not determine the clock.**  The interfaces with fiber sizes `(1,3)` and
`(2,2)` have the same sample size `n = 4` and the same width `w = 2`, and their mean reported
connection times are `1/2` and `7/18`. -/
theorem connectionTime_mean_oneThree_ne_twoTwo :
    Linkage.width interfaceOneThree = Linkage.width interfaceTwoTwo ∧
      ∫⁻ p, ENNReal.ofReal (connectionTime interfaceOneThree p) ∂(trajectoryClockLaw 4)
        ≠ ∫⁻ p, ENNReal.ofReal (connectionTime interfaceTwoTwo p) ∂(trajectoryClockLaw 4) := by
  refine ⟨by decide +kernel, ?_⟩
  rw [connectionTime_mean_oneThree, connectionTime_mean_twoTwo]
  intro h
  have h' := (ENNReal.ofReal_eq_ofReal_iff (by norm_num) (by norm_num)).mp h
  norm_num at h'

end Descent.Pangenome.GraphCoalescent
