/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.GraphCoalescent.ConnectivityCumulantCorpus
import Descent.Pangenome.GraphCoalescent.ConnectivityCumulantDegree
import Descent.Pangenome.GraphCoalescent.MinimalHistoryLumping

assert_below Descent.PopGen Descent.Spectral Descent.Blindness Descent.Conditionals
assert_below Descent.Portability Descent.Decision Descent.Program

/-!
# The exact degree of the connectivity cumulant, and the history constant as its top coefficient

Theorem D of the hidden-clock note says that the connectivity cumulant `C_c(z)` of an interface
with `w` fibers on `n` individuals has degree `n - w + 1`.
`Descent.Pangenome.GraphCoalescent.ConnectivityCumulantDegree` proves the upper bound; (E1) of
`LeadingCoefficient` computes the coefficient at `z^{n-w+1}`, which is positive, so the bound is
attained.  §7 of the note ties the minimal connecting histories to that coefficient,
`H_w(c) = (w - 1)! [z^{n-w+1}] C_c(z) / 2^{w-1}`; `MinimalHistoryLumping` identifies `H_w(c)`
with `historyWeight`, and `LeadingCoefficient` identifies `historyWeight` with the coefficient.

## Main results

- `leadingCoefficient_pos`: the top coefficient of (E1) is positive when every fiber is
  nonempty.
- `natDegree_connectivityCumulant_eq`: **(D3), the exact degree**, `deg C_q = n - w + 1` for an
  interface with `w ≥ 2` parts.
- `natDegree_connectivityCumulant_graphKer_eq`: the same in the corpus vocabulary, for
  `graphKer s` of width `w ≥ 2`.
- `minimalHistoryCount_eq_coeff_cumulantOfSizes`: **§7**,
  `H_w(c) = (w - 1)! [z^{n-w+1}] C_c(z) / 2^{w-1}`, with `C_c` the cumulant (D2) of the fiber
  sizes.

## Scope

The exact degree is stated for `w ≥ 2`, the range of (E1).  `H_w(c)` is the count of labeled
minimal connecting histories of `ShortTimeConnectionLaw`, read at the chosen representatives of
the fibers.

## Empirical status

None.  Every declaration here is a statement about the coefficients of integer polynomials
indexed by the partitions of a finite set, or a count of chains of covers.
-/

namespace Descent.Pangenome.GraphCoalescent

open Coalescent Finset Polynomial ShortTimeConnectionLaw MinimalHistoryLumping

open scoped Classical

noncomputable section

/-- **The top coefficient of (E1) is positive** when every fiber is nonempty.

Assumes: every fiber size is at least one. -/
theorem leadingCoefficient_pos {ι : Type*} [DecidableEq ι] {T : Finset ι} {c : ι → ℕ}
    (hc : ∀ i ∈ T, 1 ≤ c i) : 0 < leadingCoefficient T c := by
  unfold leadingCoefficient
  have hprod : 0 < ∏ i ∈ T, (c i : ℚ) := Finset.prod_pos fun i hi ↦ by exact_mod_cast hc i hi
  exact div_pos (mul_pos (mul_pos two_pos hprod) (by positivity)) (by positivity)

/-- **NOTE (D3), the exact degree.** For an interface `q` with `w ≥ 2` parts on `n` individuals,
`deg C_q(z) = n - w + 1`: the bound of `ConnectivityCumulantDegree` is attained, because the top
coefficient of (E1) is positive.

Assumes: `q` has at least two parts. -/
theorem natDegree_connectivityCumulant_eq {α : Type*} [DecidableEq α] {s : Finset α}
    (q : Finpartition s) (hq : 2 ≤ #q.parts) :
    (connectivityCumulant q).natDegree = #s - #q.parts + 1 := by
  have hqs := q.card_parts_le_card
  have hs : s.Nonempty := card_pos.mp (by omega)
  have hle := natDegree_connectivityCumulant_le q hs
  have hcoeff : (connectivityCumulant q).coeff (#s - #q.parts + 1) ≠ 0 := by
    intro h0
    have htop := coeff_connectivityCumulant_top q hq
    rw [h0, Int.cast_zero] at htop
    exact (leadingCoefficient_pos (T := q.parts) (c := fun t ↦ #t)
      fun t ht ↦ card_pos.mpr (q.nonempty_of_mem_parts ht)).ne htop
  exact le_antisymm (by omega) (le_natDegree_of_ne_zero hcoeff)

/-- **NOTE (D3), the exact degree, in the corpus vocabulary.** The cumulant of `graphKer s` has
degree exactly `n - w + 1`, where `w = Linkage.width s ≥ 2`.

Assumes: the interface has width at least two. -/
theorem natDegree_connectivityCumulant_graphKer_eq {n : ℕ} (s : Fin n → Fin n)
    (hw : 2 ≤ Linkage.width s) :
    (connectivityCumulant (Finpartition.ofSetoid (graphKer s))).natDegree
      = n - Linkage.width s + 1 := by
  have h := natDegree_connectivityCumulant_eq (Finpartition.ofSetoid (graphKer s))
    (by rwa [card_parts_ofSetoid, blocks_graphKer])
  rwa [card_parts_ofSetoid, blocks_graphKer, card_univ, Fintype.card_fin] at h

/-- **§7 of the note: the history constant is the top coefficient of the cumulant.**
`H_w(c) = (w - 1)! [z^{n-w+1}] C_c(z) / 2^{w-1}`, with `H_w(c)` the minimal connecting histories
from the singletons and `C_c` the cumulant (D2) of the fiber sizes, read at the chosen individuals.

Assumes: the interface has width at least two. -/
theorem minimalHistoryCount_eq_coeff_cumulantOfSizes {n : ℕ} (s : Fin n → Fin n)
    (hwidth : 2 ≤ Linkage.width s) :
    minimalHistoryCount s = ((((Linkage.width s - 1).factorial : ℚ)
      * ((cumulantOfSizes (representatives s ⊥) (Linkage.fiberCard s)).coeff
        (n - Linkage.width s + 1) : ℚ) / 2 ^ (Linkage.width s - 1) : ℚ) : ℝ) := by
  have hcard : #(representatives s ⊥) = Linkage.width s := by
    rw [(representatives_isRepresentativeSet s ⊥).card_eq, observed_bot, blocks_graphKer]
  rw [minimalHistoryCount_eq_historyWeight s (by omega), ← hcard,
    historyWeight_eq_coeff_cumulantOfSizes (representatives s ⊥) (Linkage.fiberCard s)
      (by omega) fun i _ ↦ Linkage.fiberCard_pos s i,
    sum_fiberCard_representatives]
  congr 1
  ring

end

end Descent.Pangenome.GraphCoalescent
