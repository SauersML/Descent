/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.GraphCoalescent.LahWeights

assert_below Descent.PopGen Descent.Spectral Descent.Blindness Descent.Conditionals
assert_below Descent.Portability Descent.Decision Descent.Program

/-!
# The pangenomic connectivity cumulant

The pangenome hidden-clock note (§6, Theorem D) packs the whole reported connection clock of an
interface `q` into one polynomial. Its definition (D2) is an alternating sum over partitions `σ`
of the fibers, with the partition-lattice Möbius coefficient `μ(σ, ⊤) = (-1)^{|σ|-1} (|σ|-1)!`
and the Lah polynomials `A_m` of `LahWeights`. Theorem D (D3) says the alternating sum is a
positive one: the sum over genealogy partitions `π` with `q ⊔ π = ⊤` of `∏_{B ∈ π} |B|! z^{|π|}`.
This module proves (D3), in which the general-order Möbius coefficient that
`Descent.Pangenome.TripleGluing` names but does not prove appears.

Partitions are Mathlib `Finpartition`s of a finite set `s` of individuals, with the refinement
order. `connectivityCumulant q` is (D2) on the upper interval of the interface: a partition of
the fibers is a coarsening `σ ≥ q`, and a component `C` of `σ` has `c(C) = |C|` individuals.
`ReportConnected q π` is `q ⊔ π = ⊤`, stated as "the only common coarsening is the one-part
partition". `connectivityCumulant_eq_sum_connected` is (D3).

The proof has three parts.
1. The Möbius function. `mobiusCoefficient k` is `(-1)^{k-1} (k-1)!`, and
   `mobiusCoefficient_succ_add` is the recurrence `μ(k+1) + k μ(k) = 0`. Through the insertion
   bijection of `LahWeights`, it gives `sum_mobiusCoefficient_finpartition`: the coefficients
   over all partitions of a nonempty set sum to one on a singleton and to zero otherwise. This
   is the defining property of the Möbius function, derived with no appeal to Stirling numbers.
2. The upper interval. `partitionCoarsening` and `coarseningPartition` identify the coarsenings
   of `τ` with the partitions of the set of parts of `τ`, preserving the number of parts, so
   `sum_mobiusCoefficient_upper` evaluates the Möbius sum on every interval `[τ, ⊤]`. Common
   coarsenings of `q` and `π` form the interval above `commonCoarsening q π`, so
   `sum_mobiusCoefficient_common` is `[q ⊔ π = ⊤]`.
3. The refinement product. `restrictToPart` and Mathlib's `Finpartition.bind` identify the
   refinements of `σ` with the families of partitions of its parts, and the weight
   `blockWeight` is multiplicative, so `sum_le_eq_prod_lahPolynomial` gives
   `Σ_{π ≤ σ} ∏|B|! z^{|π|} = ∏_{C ∈ σ} A_{|C|}(z)` from (D1).

Möbius inversion is then an exchange of the two sums.

`connectivityCumulant_eq_map_nat` and `coeff_connectivityCumulant_nonneg` record that the
cumulant has nonnegative integer coefficients. `connectivityCumulant_eq_cumulantOfSizes` shows it
depends on the interface only through its fiber sizes: it is `cumulantOfSizes q.parts card`,
(D2) written over partitions of the fiber set with `c(C) = Σ_{i ∈ C} c_i`.
`cumulantOfSizes_eq_of_equiv` is the equivalence form of that dependence: an equivalence of fiber
sets carrying the sizes of one to the sizes of the other leaves the cumulant unchanged. The
transport is `mapPartition` along an embedding, with inverse `comapPartition`, and
`connectivityCumulant_eq_of_equiv` states it for two interfaces on possibly different sets of
individuals whose fibers correspond one to one with equal sizes.
`connectivityCumulant_eq_of_map_card_eq` is the literal form: interfaces whose fiber sizes form
the same multiset have the same cumulant, through the size-preserving equivalence that
`exists_equiv_sizes_of_map_val_eq` assembles size by size.

The degree bound `n - w + 1` is `ConnectivityCumulantDegree`, the corpus form of (D3) over
`Coalescent.ER n` with `observed` and `graphKer` is `ConnectivityCumulantCorpus`, and the
identification of `mobiusCoefficient` with Mathlib's `IncidenceAlgebra.mu` on the partition
lattice, together with the Stirling identity, is `PartitionLatticeMobius`.

## Empirical status

None. The bodies here are finite combinatorics on the partition lattice of a finite set, so no
measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Pangenome.GraphCoalescent

open Finset Polynomial
open scoped Classical

noncomputable section

/-! ## The Möbius coefficient of the partition lattice -/

/-- The Möbius coefficient `μ(σ, ⊤) = (-1)^{|σ|-1} (|σ|-1)!` of the partition lattice, as a
function of the number `|σ|` of blocks. -/
def mobiusCoefficient (k : ℕ) : ℤ := (-1) ^ (k - 1) * ((k - 1).factorial : ℤ)

/-- The coefficient of the one-block partition is one. -/
theorem mobiusCoefficient_one : mobiusCoefficient 1 = 1 := by
  simp [mobiusCoefficient]

/-- The recurrence that makes it the Möbius function: `μ(k + 1) + k μ(k) = 0` for `k ≥ 1`. -/
theorem mobiusCoefficient_succ_add (k : ℕ) (hk : 1 ≤ k) :
    mobiusCoefficient (k + 1) + (k : ℤ) * mobiusCoefficient k = 0 := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  simp only [mobiusCoefficient, Nat.add_sub_cancel, Nat.factorial_succ]
  push_cast
  ring

variable {α : Type*} [DecidableEq α]

/-- **The Möbius function of the partition lattice.** Summing `μ(σ, ⊤)` over every partition of
a nonempty finite set gives one on a singleton and zero on every larger set. -/
theorem sum_mobiusCoefficient_finpartition (t : Finset α) (ht : t.Nonempty) :
    ∑ ρ : Finpartition t, mobiusCoefficient #ρ.parts = if #t = 1 then 1 else 0 := by
  obtain ⟨a, ha⟩ := ht
  obtain ⟨u, hu, rfl⟩ : ∃ u, a ∉ u ∧ t = insert a u :=
    ⟨t.erase a, notMem_erase a t, (insert_erase ha).symm⟩
  rw [sum_finpartition_insert hu]
  have hterm : ∀ P : Finpartition u,
      ∑ r ∈ insert ∅ P.parts, mobiusCoefficient #(insertAt P hu r).parts
        = mobiusCoefficient (#P.parts + 1) + (#P.parts : ℤ) * mobiusCoefficient #P.parts := by
    intro P
    have hparts : ∀ r ∈ P.parts,
        mobiusCoefficient #(insertAt P hu r).parts = mobiusCoefficient #P.parts := by
      intro r hr
      rw [insertAt, dif_pos hr, (blockWeight_insertIntoPart P hu hr).2]
    rw [sum_insert P.empty_notMem_parts, insertAt, dif_neg P.empty_notMem_parts,
      (blockWeight_insertNewPart P hu).2, sum_congr rfl hparts, sum_const, nsmul_eq_mul]
  rw [sum_congr rfl fun P _ ↦ hterm P]
  by_cases hu0 : u = ∅
  · subst hu0
    rw [sum_eq_single (⊥ : Finpartition (∅ : Finset α))
      (fun P _ hne ↦ absurd (finpartition_empty_eq_bot P) hne) (fun h ↦ absurd (mem_univ _) h)]
    simp [mobiusCoefficient]
  · have hpos : 0 < #u := card_pos.mpr (nonempty_iff_ne_empty.mpr hu0)
    rw [if_neg (by rw [card_insert_of_notMem hu]; omega)]
    refine sum_eq_zero fun P _ ↦ mobiusCoefficient_succ_add _ ?_
    exact card_pos.mpr (P.parts_nonempty (by simpa using hu0))

/-! ## Coarsenings of a partition as partitions of its parts -/

section Coarsening

variable {s : Finset α}

/-- The parts of `τ` contained in `u`. -/
def partsWithin (τ : Finpartition s) (u : Finset α) : Finset (Finset α) :=
  τ.parts.filter (· ⊆ u)

/-- Under `τ ≤ σ`, each part of `τ` lies in exactly one part of `σ`. -/
theorem existsUnique_part_superset {τ σ : Finpartition s} (h : τ ≤ σ) {t : Finset α}
    (ht : t ∈ τ.parts) : ∃! u, u ∈ σ.parts ∧ t ⊆ u := by
  obtain ⟨u, hu, htu⟩ := h ht
  have htu' : t ⊆ u := htu
  refine ⟨u, ⟨hu, htu'⟩, ?_⟩
  rintro u' ⟨hu', htu''⟩
  obtain ⟨x, hx⟩ := τ.nonempty_of_mem_parts ht
  exact σ.eq_of_mem_parts hu' hu (htu'' hx) (htu' hx)

/-- Under `τ ≤ σ`, a part of `σ` is the union of the parts of `τ` inside it. -/
theorem biUnion_partsWithin {τ σ : Finpartition s} (h : τ ≤ σ) {u : Finset α}
    (hu : u ∈ σ.parts) : (partsWithin τ u).biUnion id = u := by
  ext x
  simp only [mem_biUnion, partsWithin, mem_filter, id]
  constructor
  · rintro ⟨t, ⟨-, htu⟩, hxt⟩
    exact htu hxt
  · intro hxu
    obtain ⟨t, ht, hxt⟩ := τ.exists_mem (σ.subset hu hxu)
    obtain ⟨u', hu', htu'⟩ := h ht
    have htu'' : t ⊆ u' := htu'
    have hu'u : u' = u := σ.eq_of_mem_parts hu' hu (htu'' hxt) hxu
    exact ⟨t, ⟨ht, hu'u ▸ htu''⟩, hxt⟩

/-- The parts of `τ` inside the union of a family of its parts are exactly that family. -/
theorem partsWithin_biUnion {τ : Finpartition s} {U : Finset (Finset α)} (hU : U ⊆ τ.parts) :
    partsWithin τ (U.biUnion id) = U := by
  ext t
  simp only [partsWithin, mem_filter]
  constructor
  · rintro ⟨ht, hsub⟩
    obtain ⟨x, hx⟩ := τ.nonempty_of_mem_parts ht
    obtain ⟨t', ht', hxt'⟩ := mem_biUnion.mp (hsub hx)
    have htt' : t = t' := τ.eq_of_mem_parts ht (hU ht') hx hxt'
    exact htt' ▸ ht'
  · intro ht
    exact ⟨hU ht, subset_biUnion_of_mem id ht⟩

/-- A coarsening `σ ≥ τ`, read as a partition of the parts of `τ`. -/
def coarseningPartition (τ σ : Finpartition s) (h : τ ≤ σ) : Finpartition τ.parts :=
  Finpartition.ofExistsUnique (σ.parts.image (partsWithin τ))
    (by
      intro p hp
      obtain ⟨u, -, rfl⟩ := mem_image.mp hp
      exact filter_subset _ _)
    (by
      intro t ht
      obtain ⟨u, ⟨hu, htu⟩, huniq⟩ := existsUnique_part_superset h ht
      refine ⟨partsWithin τ u, ⟨mem_image_of_mem _ hu, mem_filter.mpr ⟨ht, htu⟩⟩, ?_⟩
      rintro p ⟨hp, htp⟩
      obtain ⟨u', hu', rfl⟩ := mem_image.mp hp
      rw [huniq u' ⟨hu', (mem_filter.mp htp).2⟩])
    (by
      intro hempty
      obtain ⟨u, hu, hpu⟩ := mem_image.mp hempty
      have hunion := biUnion_partsWithin h hu
      rw [hpu, biUnion_empty] at hunion
      exact σ.empty_notMem_parts (hunion ▸ hu))

/-- A partition of the parts of `τ`, read as a coarsening of `τ`: each block of parts becomes
their union. -/
def partitionCoarsening (τ : Finpartition s) (ρ : Finpartition τ.parts) : Finpartition s :=
  Finpartition.ofExistsUnique (ρ.parts.image (fun U ↦ U.biUnion id))
    (by
      intro p hp
      obtain ⟨U, hU, rfl⟩ := mem_image.mp hp
      intro x hx
      obtain ⟨t, ht, hxt⟩ := mem_biUnion.mp hx
      exact τ.subset (ρ.subset hU ht) hxt)
    (by
      intro x hx
      obtain ⟨t, ⟨ht, hxt⟩, htuniq⟩ := τ.existsUnique_mem hx
      obtain ⟨U, ⟨hU, htU⟩, hUuniq⟩ := ρ.existsUnique_mem ht
      refine ⟨U.biUnion id, ⟨mem_image_of_mem _ hU, mem_biUnion.mpr ⟨t, htU, hxt⟩⟩, ?_⟩
      rintro p ⟨hp, hxp⟩
      obtain ⟨U', hU', rfl⟩ := mem_image.mp hp
      obtain ⟨t', ht'U', hxt'⟩ := mem_biUnion.mp hxp
      have htt' : t' = t := htuniq t' ⟨ρ.subset hU' ht'U', hxt'⟩
      rw [hUuniq U' ⟨hU', htt' ▸ ht'U'⟩])
    (by
      intro hempty
      obtain ⟨U, hU, hUempty⟩ := mem_image.mp hempty
      obtain ⟨t, htU⟩ := ρ.nonempty_of_mem_parts hU
      obtain ⟨x, hxt⟩ := τ.nonempty_of_mem_parts (ρ.subset hU htU)
      have hx : x ∈ U.biUnion id := mem_biUnion.mpr ⟨t, htU, hxt⟩
      rw [hUempty] at hx
      exact notMem_empty x hx)

/-- The coarsening built from a partition of the parts of `τ` is above `τ`. -/
theorem le_partitionCoarsening (τ : Finpartition s) (ρ : Finpartition τ.parts) :
    τ ≤ partitionCoarsening τ ρ := by
  intro t ht
  obtain ⟨U, hU, htU⟩ := ρ.exists_mem ht
  exact ⟨U.biUnion id, mem_image_of_mem _ hU, subset_biUnion_of_mem id htU⟩

/-- Reading a coarsening as a partition of parts and back returns the coarsening. -/
theorem partitionCoarsening_coarseningPartition (τ σ : Finpartition s) (h : τ ≤ σ) :
    partitionCoarsening τ (coarseningPartition τ σ h) = σ := by
  ext u
  show u ∈ (σ.parts.image (partsWithin τ)).image (fun U ↦ U.biUnion id) ↔ u ∈ σ.parts
  rw [image_image]
  constructor
  · intro hu
    obtain ⟨v, hv, rfl⟩ := mem_image.mp hu
    show (partsWithin τ v).biUnion id ∈ σ.parts
    rw [biUnion_partsWithin h hv]
    exact hv
  · intro hu
    refine mem_image.mpr ⟨u, hu, ?_⟩
    show (partsWithin τ u).biUnion id = u
    exact biUnion_partsWithin h hu

/-- Reading a partition of parts as a coarsening and back returns the partition of parts. -/
theorem coarseningPartition_partitionCoarsening (τ : Finpartition s) (ρ : Finpartition τ.parts) :
    coarseningPartition τ (partitionCoarsening τ ρ) (le_partitionCoarsening τ ρ) = ρ := by
  ext U
  show U ∈ (ρ.parts.image (fun U ↦ U.biUnion id)).image (partsWithin τ) ↔ U ∈ ρ.parts
  rw [image_image]
  constructor
  · intro hU
    obtain ⟨V, hV, rfl⟩ := mem_image.mp hU
    show partsWithin τ (V.biUnion id) ∈ ρ.parts
    rw [partsWithin_biUnion (ρ.subset hV)]
    exact hV
  · intro hU
    refine mem_image.mpr ⟨U, hU, ?_⟩
    show partsWithin τ (U.biUnion id) = U
    exact partsWithin_biUnion (ρ.subset hU)

/-- Distinct blocks of parts of `τ` have distinct unions. -/
theorem biUnion_injOn (τ : Finpartition s) (ρ : Finpartition τ.parts) :
    Set.InjOn (fun U : Finset (Finset α) ↦ U.biUnion id) ρ.parts := by
  intro U hU V hV hUV
  have hUV' : U.biUnion id = V.biUnion id := hUV
  calc U = partsWithin τ (U.biUnion id) := (partsWithin_biUnion (ρ.subset hU)).symm
    _ = partsWithin τ (V.biUnion id) := by rw [hUV']
    _ = V := partsWithin_biUnion (ρ.subset hV)

/-- The coarsening has as many parts as the partition of parts it comes from. -/
theorem card_parts_partitionCoarsening (τ : Finpartition s) (ρ : Finpartition τ.parts) :
    #(partitionCoarsening τ ρ).parts = #ρ.parts :=
  card_image_of_injOn (biUnion_injOn τ ρ)

/-- **The upper interval of a partition.** Summing over the coarsenings `σ ≥ τ` is summing over
the partitions of the parts of `τ`. -/
theorem sum_filter_le_eq_sum_partitionCoarsening {M : Type*} [AddCommMonoid M]
    (τ : Finpartition s) (F : Finpartition s → M) :
    ∑ σ ∈ univ.filter (fun σ ↦ τ ≤ σ), F σ
      = ∑ ρ : Finpartition τ.parts, F (partitionCoarsening τ ρ) := by
  refine sum_nbij' (fun σ ↦ if h : τ ≤ σ then coarseningPartition τ σ h else ⊥)
    (partitionCoarsening τ) ?_ ?_ ?_ ?_ ?_
  · intro σ _
    exact mem_univ _
  · intro ρ _
    exact mem_filter.mpr ⟨mem_univ _, le_partitionCoarsening τ ρ⟩
  · intro σ hσ
    have h := (mem_filter.mp hσ).2
    simp only [dif_pos h, partitionCoarsening_coarseningPartition]
  · intro ρ _
    simp only [dif_pos (le_partitionCoarsening τ ρ), coarseningPartition_partitionCoarsening]
  · intro σ hσ
    have h := (mem_filter.mp hσ).2
    simp only [dif_pos h, partitionCoarsening_coarseningPartition]

/-- **NOTE (D3), the Möbius function on an upper interval.** Over a nonempty set, summing
`μ(σ, ⊤)` over the coarsenings `σ ≥ τ` gives one when `τ` has a single part and zero otherwise:
`μ` is the Möbius function `μ(·, ⊤)` of the partition lattice. -/
theorem sum_mobiusCoefficient_upper (τ : Finpartition s) (hs : s.Nonempty) :
    ∑ σ ∈ univ.filter (fun σ ↦ τ ≤ σ), mobiusCoefficient #σ.parts
      = if #τ.parts = 1 then 1 else 0 := by
  rw [sum_filter_le_eq_sum_partitionCoarsening τ (fun σ ↦ mobiusCoefficient #σ.parts)]
  simp only [card_parts_partitionCoarsening]
  exact sum_mobiusCoefficient_finpartition τ.parts (τ.parts_nonempty (by simpa using hs.ne_empty))

/-! ## Common coarsenings -/

/-- **NOTE (D3): `q ⊔ π = ⊤`.** A genealogy partition `π` connects the interface `q` when the
only common coarsening of the two is the one-part partition. -/
def ReportConnected (q π : Finpartition s) : Prop :=
  ∀ σ : Finpartition s, q ≤ σ → π ≤ σ → σ = ⊤

/-- The finest common coarsening `q ⊔ π` of two partitions. -/
def commonCoarsening (q π : Finpartition s) : Finpartition s :=
  (univ.filter (fun σ ↦ q ≤ σ ∧ π ≤ σ)).inf'
    ⟨⊤, mem_filter.mpr ⟨mem_univ _, le_top, le_top⟩⟩ id

/-- The common coarsenings of `q` and `π` are exactly the partitions above `q ⊔ π`. -/
theorem le_commonCoarsening_iff (q π σ : Finpartition s) :
    commonCoarsening q π ≤ σ ↔ q ≤ σ ∧ π ≤ σ := by
  have hmem : commonCoarsening q π ∈ {σ : Finpartition s | q ≤ σ ∧ π ≤ σ} :=
    inf'_mem {σ : Finpartition s | q ≤ σ ∧ π ≤ σ}
      (fun x hx y hy ↦ ⟨le_inf hx.1 hy.1, le_inf hx.2 hy.2⟩) _ _ id
      (fun σ hσ ↦ (mem_filter.mp hσ).2)
  constructor
  · intro h
    exact ⟨hmem.1.trans h, hmem.2.trans h⟩
  · intro h
    have hσ : σ ∈ univ.filter (fun σ : Finpartition s ↦ q ≤ σ ∧ π ≤ σ) :=
      mem_filter.mpr ⟨mem_univ σ, h⟩
    exact inf'_le id hσ

/-- `q ⊔ π = ⊤` in the sense of `ReportConnected` is the finest common coarsening being `⊤`. -/
theorem reportConnected_iff (q π : Finpartition s) :
    ReportConnected q π ↔ commonCoarsening q π = ⊤ := by
  constructor
  · intro h
    obtain ⟨hq, hπ⟩ := (le_commonCoarsening_iff q π _).mp le_rfl
    exact h _ hq hπ
  · intro h σ hq hπ
    have hle := (le_commonCoarsening_iff q π σ).mpr ⟨hq, hπ⟩
    rw [h] at hle
    exact top_le_iff.mp hle

/-- Over a nonempty set, a partition with exactly one part is the one-part partition. -/
theorem card_parts_eq_one_iff (τ : Finpartition s) (hs : s.Nonempty) :
    #τ.parts = 1 ↔ τ = ⊤ := by
  have hne : s ≠ ⊥ := by simpa using hs.ne_empty
  have htop : (⊤ : Finpartition s).parts = {s} := by
    obtain ⟨u, hu⟩ := (⊤ : Finpartition s).parts_nonempty hne
    have hus : u = s := mem_singleton.mp (Finpartition.parts_top_subset s hu)
    exact eq_singleton_iff_unique_mem.mpr ⟨hus ▸ hu,
      fun v hv ↦ mem_singleton.mp (Finpartition.parts_top_subset s hv)⟩
  constructor
  · intro h1
    obtain ⟨u, hu⟩ := card_eq_one.mp h1
    have hus : u = s := by
      have hsup := τ.sup_parts
      rw [hu, sup_singleton] at hsup
      exact hsup
    ext v
    rw [htop, hu, hus]
  · intro h
    rw [h, htop, card_singleton]

/-- **NOTE (D3), the Möbius sum over common coarsenings.** Over a nonempty set, summing
`μ(σ, ⊤)` over the common coarsenings of `q` and `π` gives `[q ⊔ π = ⊤]`. -/
theorem sum_mobiusCoefficient_common (q π : Finpartition s) (hs : s.Nonempty) :
    ∑ σ ∈ univ.filter (fun σ ↦ q ≤ σ ∧ π ≤ σ), mobiusCoefficient #σ.parts
      = if ReportConnected q π then 1 else 0 := by
  have hfilter : univ.filter (fun σ : Finpartition s ↦ q ≤ σ ∧ π ≤ σ)
      = univ.filter (fun σ ↦ commonCoarsening q π ≤ σ) := by
    ext σ
    simp only [mem_filter, mem_univ, true_and, le_commonCoarsening_iff]
  rw [hfilter, sum_mobiusCoefficient_upper _ hs]
  by_cases h : ReportConnected q π
  · rw [if_pos h, if_pos ((card_parts_eq_one_iff _ hs).mpr ((reportConnected_iff q π).mp h))]
  · rw [if_neg h, if_neg fun h1 ↦
      h ((reportConnected_iff q π).mpr ((card_parts_eq_one_iff _ hs).mp h1))]

/-! ## Refinements of a partition as families of partitions of its parts -/

/-- The restriction of a refinement `π ≤ σ` to a part `u` of `σ`. -/
def restrictToPart {π σ : Finpartition s} (h : π ≤ σ) {u : Finset α} (hu : u ∈ σ.parts) :
    Finpartition u :=
  Finpartition.ofExistsUnique (partsWithin π u)
    (fun p hp ↦ (mem_filter.mp hp).2)
    (by
      intro x hx
      obtain ⟨t, ⟨ht, hxt⟩, htuniq⟩ := π.existsUnique_mem (σ.subset hu hx)
      obtain ⟨u', hu', htu'⟩ := h ht
      have htu'' : t ⊆ u' := htu'
      have hu'u : u' = u := σ.eq_of_mem_parts hu' hu (htu'' hxt) hx
      refine ⟨t, ⟨mem_filter.mpr ⟨ht, hu'u ▸ htu''⟩, hxt⟩, ?_⟩
      rintro p ⟨hp, hxp⟩
      exact htuniq p ⟨(mem_filter.mp hp).1, hxp⟩)
    (fun hempty ↦ π.empty_notMem_parts (mem_filter.mp hempty).1)

/-- Juxtaposing partitions of the parts of `σ` refines `σ`. -/
theorem bind_le (σ : Finpartition s) (fam : ∀ u ∈ σ.parts, Finpartition u) :
    σ.bind fam ≤ σ := by
  intro t ht
  obtain ⟨u, hu, htu⟩ := Finpartition.mem_bind.mp ht
  exact ⟨u, hu, (fam u hu).subset htu⟩

/-- Juxtaposing the restrictions of a refinement returns the refinement. -/
theorem bind_restrictToPart {π σ : Finpartition s} (h : π ≤ σ) :
    σ.bind (fun _ hu ↦ restrictToPart h hu) = π := by
  ext t
  rw [Finpartition.mem_bind]
  constructor
  · rintro ⟨u, hu, ht⟩
    exact (mem_filter.mp ht).1
  · intro ht
    obtain ⟨u, hu, htu⟩ := h ht
    exact ⟨u, hu, mem_filter.mpr ⟨ht, htu⟩⟩

/-- Restricting a juxtaposition to a part returns the partition given on that part. -/
theorem restrictToPart_bind (σ : Finpartition s) (fam : ∀ u ∈ σ.parts, Finpartition u)
    {u : Finset α} (hu : u ∈ σ.parts) : restrictToPart (bind_le σ fam) hu = fam u hu := by
  ext t
  show t ∈ partsWithin (σ.bind fam) u ↔ t ∈ (fam u hu).parts
  simp only [partsWithin, mem_filter, Finpartition.mem_bind]
  constructor
  · rintro ⟨⟨u', hu', ht⟩, htu⟩
    obtain ⟨x, hx⟩ := (fam u' hu').nonempty_of_mem_parts ht
    have hu'u : u' = u := σ.eq_of_mem_parts hu' hu ((fam u' hu').subset ht hx) (htu hx)
    subst hu'u
    exact ht
  · intro ht
    exact ⟨⟨u, hu, ht⟩, (fam u hu).subset ht⟩

/-- The weight of a juxtaposition is the product of the weights of its pieces. -/
theorem blockWeight_bind (σ : Finpartition s) (fam : ∀ u ∈ σ.parts, Finpartition u) :
    blockWeight (σ.bind fam) = ∏ u ∈ σ.parts.attach, blockWeight (fam u.1 u.2) := by
  rw [blockWeight, Finpartition.bind_parts, prod_biUnion]
  · rfl
  · intro u _ v _ huv
    simp only [Function.onFun]
    rw [disjoint_left]
    intro t htu htv
    obtain ⟨x, hx⟩ := (fam u.1 u.2).nonempty_of_mem_parts htu
    exact huv (Subtype.ext (σ.eq_of_mem_parts u.2 v.2 ((fam u.1 u.2).subset htu hx)
      ((fam v.1 v.2).subset htv hx)))

/-- **NOTE (D3), the refinement product.** Summing `∏|B|! z^{|π|}` over the refinements `π ≤ σ`
gives the product of the Lah polynomials of the parts of `σ`. -/
theorem sum_le_eq_prod_lahPolynomial (R : Type*) [CommSemiring R] (σ : Finpartition s) :
    ∑ π ∈ univ.filter (fun π ↦ π ≤ σ), C (blockWeight π : R) * X ^ #π.parts
      = ∏ u ∈ σ.parts, lahPolynomial R #u := by
  have hD1 : ∀ u ∈ σ.parts, lahPolynomial R #u
      = ∑ P ∈ (univ : Finset (Finpartition u)), C (blockWeight P : R) * X ^ #P.parts :=
    fun u _ ↦ (sum_blockWeight_X_pow_eq_lahPolynomial R u).symm
  rw [prod_congr rfl hD1, prod_sum σ.parts (fun u ↦ (univ : Finset (Finpartition u)))
    (fun u P ↦ C (blockWeight P : R) * X ^ #P.parts)]
  refine sum_nbij'
    (fun π ↦ if h : π ≤ σ then (fun u hu ↦ restrictToPart h hu) else (fun _ _ ↦ ⊥))
    (fun fam ↦ σ.bind fam) ?_ ?_ ?_ ?_ ?_
  · intro π _
    exact mem_pi.mpr fun u _ ↦ mem_univ _
  · intro fam _
    exact mem_filter.mpr ⟨mem_univ _, bind_le σ fam⟩
  · intro π hπ
    have h := (mem_filter.mp hπ).2
    simp only [dif_pos h]
    exact bind_restrictToPart h
  · intro fam _
    simp only [dif_pos (bind_le σ fam)]
    funext u hu
    exact restrictToPart_bind σ fam hu
  · intro π hπ
    have h := (mem_filter.mp hπ).2
    simp only [dif_pos h]
    conv_lhs => rw [← bind_restrictToPart h]
    rw [blockWeight_bind, Finpartition.card_bind, Nat.cast_prod, map_prod,
      ← prod_pow_eq_pow_sum, ← prod_mul_distrib]

/-! ## The cumulant -/

/-- **NOTE (D2)**, on the upper interval of the interface partition `q`:
`C_q(z) = Σ_{σ ≥ q} μ(σ, ⊤) ∏_{C ∈ σ} A_{|C|}(z)`. -/
def connectivityCumulant (q : Finpartition s) : Polynomial ℤ :=
  ∑ σ ∈ univ.filter (fun σ ↦ q ≤ σ),
    C (mobiusCoefficient #σ.parts) * ∏ u ∈ σ.parts, lahPolynomial ℤ #u

/-- **NOTE Theorem D, (D3).** The alternating cumulant is the positive sum, over the genealogy
partitions `π` with `q ⊔ π = ⊤`, of `∏_{B ∈ π} |B|! z^{|π|}`. -/
theorem connectivityCumulant_eq_sum_connected (q : Finpartition s) (hs : s.Nonempty) :
    connectivityCumulant q
      = ∑ π ∈ univ.filter (fun π ↦ ReportConnected q π), C (blockWeight π : ℤ) * X ^ #π.parts := by
  unfold connectivityCumulant
  simp only [← sum_le_eq_prod_lahPolynomial ℤ, mul_sum]
  rw [sum_comm' (t' := univ) (s' := fun π ↦ univ.filter (fun σ ↦ q ≤ σ ∧ π ≤ σ))
    (by intro σ π; simp only [mem_filter, mem_univ, true_and, and_true])]
  rw [sum_filter]
  refine sum_congr rfl fun π _ ↦ ?_
  rw [← sum_mul, ← map_sum Polynomial.C (fun σ : Finpartition s ↦ mobiusCoefficient #σ.parts),
    sum_mobiusCoefficient_common q π hs]
  split_ifs <;> simp

/-- **NOTE Theorem D: nonnegative integer coefficients.** The cumulant is the image of a
polynomial with natural-number coefficients. -/
theorem connectivityCumulant_eq_map_nat (q : Finpartition s) (hs : s.Nonempty) :
    connectivityCumulant q
      = (∑ π ∈ univ.filter (fun π ↦ ReportConnected q π),
          C (blockWeight π) * X ^ #π.parts : Polynomial ℕ).map (Nat.castRingHom ℤ) := by
  rw [connectivityCumulant_eq_sum_connected q hs, Polynomial.map_sum]
  simp only [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X,
    Nat.coe_castRingHom]

/-- Every coefficient of the cumulant is nonnegative. -/
theorem coeff_connectivityCumulant_nonneg (q : Finpartition s) (hs : s.Nonempty) (j : ℕ) :
    0 ≤ (connectivityCumulant q).coeff j := by
  rw [connectivityCumulant_eq_map_nat q hs, Polynomial.coeff_map, Nat.coe_castRingHom]
  exact Int.natCast_nonneg _

end Coarsening

/-- **NOTE (D2)** for fibers indexed by a finite set `T` with sizes `c`:
`C_c(z) = Σ_{σ ∈ P_T} (-1)^{|σ|-1} (|σ|-1)! ∏_{C ∈ σ} A_{c(C)}(z)`, `c(C) = Σ_{i ∈ C} c_i`. -/
def cumulantOfSizes {ι : Type*} [DecidableEq ι] (T : Finset ι) (c : ι → ℕ) : Polynomial ℤ :=
  ∑ ρ : Finpartition T,
    C (mobiusCoefficient #ρ.parts) * ∏ U ∈ ρ.parts, lahPolynomial ℤ (∑ i ∈ U, c i)

/-- **NOTE Theorem D: dependence on the fiber sizes only.** The cumulant of an interface is (D2)
over the partitions of its set of fibers, with each fiber weighted by its size. -/
theorem connectivityCumulant_eq_cumulantOfSizes {s : Finset α} (q : Finpartition s) :
    connectivityCumulant q = cumulantOfSizes q.parts (fun t ↦ #t) := by
  unfold connectivityCumulant cumulantOfSizes
  rw [sum_filter_le_eq_sum_partitionCoarsening q
    (fun σ ↦ C (mobiusCoefficient #σ.parts) * ∏ u ∈ σ.parts, lahPolynomial ℤ #u)]
  refine sum_congr rfl fun ρ _ ↦ ?_
  rw [card_parts_partitionCoarsening]
  congr 1
  show ∏ u ∈ ρ.parts.image (fun U ↦ U.biUnion id), lahPolynomial ℤ #u
    = ∏ U ∈ ρ.parts, lahPolynomial ℤ (∑ t ∈ U, #t)
  rw [prod_image (biUnion_injOn q ρ)]
  refine prod_congr rfl fun U hU ↦ ?_
  rw [card_biUnion (fun t ht t' ht' hne ↦ q.disjoint (ρ.subset hU ht) (ρ.subset hU ht') hne)]
  rfl

/-! ## Relabeling the fibers -/

section Relabeling

variable {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]

/-- A partition of `T` carried along an embedding `e`: each part `U` becomes `U.map e`. -/
def mapPartition (e : ι ↪ κ) {T : Finset ι} (P : Finpartition T) : Finpartition (T.map e) :=
  Finpartition.ofExistsUnique (P.parts.image fun U ↦ U.map e)
    (by
      intro p hp
      obtain ⟨U, hU, rfl⟩ := mem_image.mp hp
      exact map_subset_map.mpr (P.subset hU))
    (by
      intro y hy
      obtain ⟨x, hx, rfl⟩ := mem_map.mp hy
      obtain ⟨U, ⟨hU, hxU⟩, hUuniq⟩ := P.existsUnique_mem hx
      refine ⟨U.map e, ⟨mem_image_of_mem _ hU, mem_map_of_mem e hxU⟩, ?_⟩
      rintro p ⟨hp, hxp⟩
      obtain ⟨U', hU', rfl⟩ := mem_image.mp hp
      rw [hUuniq U' ⟨hU', (mem_map' e).mp hxp⟩])
    (by
      intro hempty
      obtain ⟨U, hU, hUempty⟩ := mem_image.mp hempty
      rw [map_eq_empty] at hUempty
      rw [hUempty] at hU
      exact P.empty_notMem_parts hU)

/-- A partition of `T.map e` read back on `T`: each part `V` becomes the elements of `T` that `e`
sends into `V`. -/
def comapPartition (e : ι ↪ κ) {T : Finset ι} (Q : Finpartition (T.map e)) : Finpartition T :=
  Finpartition.ofExistsUnique (Q.parts.image fun V ↦ T.filter fun x ↦ e x ∈ V)
    (by
      intro p hp
      obtain ⟨V, -, rfl⟩ := mem_image.mp hp
      exact filter_subset _ _)
    (by
      intro x hx
      obtain ⟨V, ⟨hV, hxV⟩, hVuniq⟩ := Q.existsUnique_mem (mem_map_of_mem e hx)
      refine ⟨T.filter fun x ↦ e x ∈ V, ⟨mem_image_of_mem _ hV, mem_filter.mpr ⟨hx, hxV⟩⟩, ?_⟩
      rintro p ⟨hp, hxp⟩
      obtain ⟨V', hV', rfl⟩ := mem_image.mp hp
      rw [hVuniq V' ⟨hV', (mem_filter.mp hxp).2⟩])
    (by
      intro hempty
      obtain ⟨V, hV, hVempty⟩ := mem_image.mp hempty
      obtain ⟨y, hy⟩ := Q.nonempty_of_mem_parts hV
      obtain ⟨x, hx, rfl⟩ := mem_map.mp (Q.subset hV hy)
      have hmem : x ∈ T.filter fun x ↦ e x ∈ V := mem_filter.mpr ⟨hx, hy⟩
      rw [hVempty] at hmem
      exact notMem_empty x hmem)

/-- Carrying a partition along `e` and reading it back returns the partition. -/
theorem comapPartition_mapPartition (e : ι ↪ κ) {T : Finset ι} (P : Finpartition T) :
    comapPartition e (mapPartition e P) = P := by
  have hself : ∀ U ∈ P.parts, T.filter (fun x ↦ e x ∈ U.map e) = U := by
    intro U hU
    ext x
    rw [mem_filter, mem_map' e]
    exact ⟨fun h ↦ h.2, fun h ↦ ⟨P.subset hU h, h⟩⟩
  ext U
  show U ∈ (P.parts.image fun U ↦ U.map e).image (fun V ↦ T.filter fun x ↦ e x ∈ V)
    ↔ U ∈ P.parts
  rw [image_image]
  constructor
  · intro h
    obtain ⟨V, hV, rfl⟩ := mem_image.mp h
    show T.filter (fun x ↦ e x ∈ V.map e) ∈ P.parts
    rw [hself V hV]
    exact hV
  · intro hU
    exact mem_image.mpr ⟨U, hU, hself U hU⟩

/-- Reading a partition of `T.map e` back on `T` and carrying it along `e` returns it. -/
theorem mapPartition_comapPartition (e : ι ↪ κ) {T : Finset ι} (Q : Finpartition (T.map e)) :
    mapPartition e (comapPartition e Q) = Q := by
  have hself : ∀ V ∈ Q.parts, (T.filter fun x ↦ e x ∈ V).map e = V := by
    intro V hV
    ext y
    rw [mem_map]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (mem_filter.mp hx).2
    · intro hy
      obtain ⟨x, hx, rfl⟩ := mem_map.mp (Q.subset hV hy)
      exact ⟨x, mem_filter.mpr ⟨hx, hy⟩, rfl⟩
  ext V
  show V ∈ (Q.parts.image fun V ↦ T.filter fun x ↦ e x ∈ V).image (fun U ↦ U.map e)
    ↔ V ∈ Q.parts
  rw [image_image]
  constructor
  · intro h
    obtain ⟨W, hW, rfl⟩ := mem_image.mp h
    show (T.filter fun x ↦ e x ∈ W).map e ∈ Q.parts
    rw [hself W hW]
    exact hW
  · intro hV
    exact mem_image.mpr ⟨V, hV, hself V hV⟩

/-- **Relabeling along an embedding.** Carrying the fibers along an embedding and reading their
sizes back through it leaves the cumulant unchanged. -/
theorem cumulantOfSizes_map (e : ι ↪ κ) (T : Finset ι) (c : κ → ℕ) :
    cumulantOfSizes (T.map e) c = cumulantOfSizes T (fun i ↦ c (e i)) := by
  unfold cumulantOfSizes
  symm
  refine sum_nbij' (mapPartition e) (comapPartition e) (fun _ _ ↦ mem_univ _)
    (fun _ _ ↦ mem_univ _) (fun P _ ↦ comapPartition_mapPartition e P)
    (fun Q _ ↦ mapPartition_comapPartition e Q) fun P _ ↦ ?_
  have hinj : Set.InjOn (fun U : Finset ι ↦ U.map e) P.parts := by
    intro U _ V _ h
    exact map_injective e h
  rw [show (mapPartition e P).parts = P.parts.image fun U ↦ U.map e from rfl,
    card_image_of_injOn hinj, prod_image hinj]
  simp only [sum_map]

/-- The cumulant of a fiber set is the cumulant of its attached copy. -/
theorem cumulantOfSizes_attach (T : Finset ι) (c : ι → ℕ) :
    cumulantOfSizes T c = cumulantOfSizes T.attach (fun i ↦ c i) := by
  conv_lhs => rw [← attach_map_val (s := T)]
  exact cumulantOfSizes_map (Function.Embedding.subtype _) T.attach c

/-- **NOTE Theorem D: the cumulant sees the fiber sizes only as a multiset.** An equivalence
between two fiber sets that carries the sizes of one to the sizes of the other leaves the
cumulant unchanged. -/
theorem cumulantOfSizes_eq_of_equiv {T : Finset ι} {T' : Finset κ} (e : T ≃ T') {c : ι → ℕ}
    {c' : κ → ℕ} (hc : ∀ i : T, c' (e i) = c i) :
    cumulantOfSizes T c = cumulantOfSizes T' c' := by
  have hmap : T.attach.map e.toEmbedding = T'.attach := by
    ext y
    simp only [mem_map, mem_attach, true_and, iff_true]
    exact ⟨e.symm y, e.apply_symm_apply y⟩
  rw [cumulantOfSizes_attach T c, cumulantOfSizes_attach T' c', ← hmap, cumulantOfSizes_map]
  congr 1
  funext i
  exact (hc i).symm

/-- **NOTE Theorem D: the fiber-size multiset of an interface.** Two interfaces, possibly on
different sets of individuals, whose fibers correspond one to one with equal sizes have the same
cumulant. -/
theorem connectivityCumulant_eq_of_equiv {s : Finset ι} {s' : Finset κ} (q : Finpartition s)
    (q' : Finpartition s') (e : q.parts ≃ q'.parts)
    (he : ∀ t : q.parts, #(e t : Finset κ) = #(t : Finset ι)) :
    connectivityCumulant q = connectivityCumulant q' := by
  rw [connectivityCumulant_eq_cumulantOfSizes, connectivityCumulant_eq_cumulantOfSizes]
  exact cumulantOfSizes_eq_of_equiv (c := fun t ↦ #t) (c' := fun t ↦ #t) e he

omit [DecidableEq ι] in
/-- The fibers of `T` of size `n` are as many as the copies of `n` in the size multiset. -/
theorem card_subtype_size_eq_count (T : Finset ι) (c : ι → ℕ) (n : ℕ) :
    Fintype.card {i : T // c i = n} = Multiset.count n (T.val.map c) := by
  have he : {i : T // c i = n} ≃ ↥(T.filter fun a ↦ c a = n) :=
    (Equiv.subtypeSubtypeEquivSubtypeInter (· ∈ T) fun a ↦ c a = n).trans
      (Equiv.subtypeEquivRight fun a ↦ by rw [mem_filter])
  rw [Fintype.card_congr he, Fintype.card_coe, Multiset.count_map]
  exact congrArg Multiset.card (Multiset.filter_congr fun a _ ↦ eq_comm)

omit [DecidableEq ι] [DecidableEq κ] in
/-- **Equal multisets of sizes give a size-preserving equivalence.** When the fibers `T` with
sizes `c` and the fibers `T'` with sizes `c'` carry the same multiset of sizes, the fibers of
each size are equinumerous, and matching them size by size gives an equivalence `T ≃ T'` that
keeps every size. -/
theorem exists_equiv_sizes_of_map_val_eq {T : Finset ι} {T' : Finset κ} {c : ι → ℕ}
    {c' : κ → ℕ} (h : T.val.map c = T'.val.map c') :
    ∃ e : T ≃ T', ∀ i : T, c' (e i) = c i := by
  have hcard : ∀ n, Fintype.card {i : T // c i = n} = Fintype.card {j : T' // c' j = n} :=
    fun n ↦ by rw [card_subtype_size_eq_count, card_subtype_size_eq_count, h]
  let F : ∀ n : ℕ, {i : T // c i = n} ≃ {j : T' // c' j = n} :=
    fun n ↦ Fintype.equivOfCardEq (hcard n)
  refine ⟨(Equiv.sigmaFiberEquiv fun i : T ↦ c i).symm.trans
    ((Equiv.sigmaCongrRight F).trans (Equiv.sigmaFiberEquiv fun j : T' ↦ c' j)), fun i ↦ ?_⟩
  exact (F (c i) ⟨i, rfl⟩).2

/-- **NOTE Theorem D: fibers with one multiset of sizes have one cumulant.** -/
theorem cumulantOfSizes_eq_of_map_val_eq {T : Finset ι} {T' : Finset κ} {c : ι → ℕ}
    {c' : κ → ℕ} (h : T.val.map c = T'.val.map c') :
    cumulantOfSizes T c = cumulantOfSizes T' c' := by
  obtain ⟨e, he⟩ := exists_equiv_sizes_of_map_val_eq h
  exact cumulantOfSizes_eq_of_equiv e he

/-- **NOTE Theorem D: the cumulant depends only on the multiset of fiber sizes.** Two
interfaces, possibly on different sets of individuals, whose fiber sizes form the same multiset
have the same cumulant. -/
theorem connectivityCumulant_eq_of_map_card_eq {s : Finset ι} {s' : Finset κ}
    (q : Finpartition s) (q' : Finpartition s')
    (h : q.parts.val.map Finset.card = q'.parts.val.map Finset.card) :
    connectivityCumulant q = connectivityCumulant q' := by
  rw [connectivityCumulant_eq_cumulantOfSizes, connectivityCumulant_eq_cumulantOfSizes]
  exact cumulantOfSizes_eq_of_map_val_eq h

end Relabeling

end

end Descent.Pangenome.GraphCoalescent
