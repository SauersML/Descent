/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.ReservoirSamplingLaw
import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Finset.Sort

assert_below Descent.Decision Descent.Program

/-!
Finite random design after an eligible genotype stream: ordered reservoir,
ordered causal choice without replacement, and per-deme outer permutations.
The inner fit/selection permutation is a fixed input acting on the sorted
outer fit rows, matching its size-dependent fixed seed in `gen_real_pt.py`.
Uniform sampling here describes ideal random draws; it does not assert
bit-exact equivalence with NumPy's finite PRNG or its seed coupling.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.SamplingDesignLaw

open FiniteReportLaw ReservoirSamplingLaw

noncomputable def uniform (A : Type*) [Fintype A] [Nonempty A] : FiniteReportLaw A where
  mass := fun _ ↦ 1 / (Fintype.card A : ℝ)
  mass_nonneg := fun _ ↦ by positivity
  mass_sum := by
    have h : (Fintype.card A : ℝ) ≠ 0 := by
      exact_mod_cast ne_of_gt (Fintype.card_pos (α := A))
    simp [h]

theorem uniform_expectation {A : Type*} [Fintype A] [Nonempty A] (f : A → ℝ) :
    (uniform A).expectation f = (∑ a, f a) / Fintype.card A := by
  simp only [expectation, uniform, ← Finset.mul_sum]
  ring

/-- Ordered choice without replacement has one outcome for each injection.
This keeps the assignment of independently drawn causal effects to columns. -/
noncomputable def causalChoice (count pool : ℕ) (h : count ≤ pool) :
    FiniteReportLaw (Slots count pool) := by
  letI : Nonempty (Slots count pool) := ⟨Fin.castLEEmb h⟩
  exact uniform _

theorem causalChoice_mass (count pool : ℕ) (h : count ≤ pool) (selected : Slots count pool) :
    (causalChoice count pool h).mass selected = 1 / (pool.descFactorial count : ℝ) := by
  simp [causalChoice, uniform, Fintype.card_embedding_eq]

theorem causalChoice_expectation (count pool : ℕ) (h : count ≤ pool)
    (f : Slots count pool → ℝ) :
    (causalChoice count pool h).expectation f =
      (∑ selected, f selected) / (pool.descFactorial count : ℝ) := by
  letI : Nonempty (Slots count pool) := ⟨Fin.castLEEmb h⟩
  unfold causalChoice
  rw [uniform_expectation]
  simp [Fintype.card_embedding_eq]

/-- Both the retained pool slots and the causal positions within them are
kept in the joint law. A downstream PCA readout can therefore use slot order. -/
noncomputable def reservoirCausalLaw (requested total count : ℕ)
    (h : count ≤ min requested total) :
    FiniteReportLaw (Slots (min requested total) total × Slots count (min requested total)) :=
  (completeLaw requested total).joint (fun _ ↦ causalChoice count (min requested total) h)

theorem reservoirCausalLaw_expectation (requested total count : ℕ)
    (h : count ≤ min requested total)
    (f : Slots (min requested total) total × Slots count (min requested total) → ℝ) :
    (reservoirCausalLaw requested total count h).expectation f =
      (completeLaw requested total).expectation (fun pool ↦
        (∑ selected, f (pool, selected)) / ((min requested total).descFactorial count : ℝ)) := by
  rw [reservoirCausalLaw, expectation_joint]
  simp_rw [causalChoice_expectation]

/-- Causal columns retain their actual stream identities, with no repeats. -/
def causalStream {requested total count : ℕ}
    (draw : Slots (min requested total) total × Slots count (min requested total)) :
    Slots count total := draw.2.trans draw.1

theorem causalStream_in_pool {requested total count : ℕ}
    (draw : Slots (min requested total) total × Slots count (min requested total))
    (i : Fin count) : causalStream draw i ∈ Set.range draw.1 := ⟨draw.2 i, rfl⟩

noncomputable def permutationLaw (n : ℕ) : FiniteReportLaw (Equiv.Perm (Fin n)) :=
  uniform _

theorem permutationLaw_mass (n : ℕ) (permutation : Equiv.Perm (Fin n)) :
    (permutationLaw n).mass permutation = 1 / (n.factorial : ℝ) := by
  simp [permutationLaw, uniform, Fintype.card_perm]

def fitRows {n fit : ℕ} (h : fit ≤ n) (permutation : Equiv.Perm (Fin n)) : Slots fit n :=
  (Fin.castLEEmb h).trans permutation.toEmbedding

def testRows {n fit : ℕ} (h : fit ≤ n) (permutation : Equiv.Perm (Fin n)) :
    Slots (n - fit) n where
  toFun := fun i ↦ permutation ⟨fit + i.val, by omega⟩
  inj' := by
    intro i j hij
    have hval := congrArg Fin.val (permutation.injective hij)
    apply Fin.ext
    simpa using Nat.add_left_cancel hval

theorem fit_test_disjoint {n fit : ℕ} (h : fit ≤ n)
    (permutation : Equiv.Perm (Fin n)) (i : Fin fit) (j : Fin (n - fit)) :
    fitRows h permutation i ≠ testRows h permutation j := by
  intro heq
  have hval := congrArg Fin.val (permutation.injective heq)
  change i.val = fit + j.val at hval
  omega

theorem fit_test_cover {n fit : ℕ} (h : fit ≤ n)
    (permutation : Equiv.Perm (Fin n)) (row : Fin n) :
    row ∈ Set.range (fitRows h permutation) ∨ row ∈ Set.range (testRows h permutation) := by
  let rank := permutation.symm row
  by_cases hr : rank.val < fit
  · left
    refine ⟨⟨rank.val, hr⟩, ?_⟩
    change permutation (Fin.castLE h ⟨rank.val, hr⟩) = row
    convert permutation.apply_symm_apply row using 1
  · right
    have hrn := rank.isLt
    refine ⟨⟨rank.val - fit, by omega⟩, ?_⟩
    change permutation ⟨fit + (rank.val - fit), _⟩ = row
    have heq : (⟨fit + (rank.val - fit), by omega⟩ : Fin n) = rank := by
      apply Fin.ext
      change fit + (rank.val - fit) = rank.val
      omega
    rw [heq]
    exact permutation.apply_symm_apply row

/-- `np.where(split == "train-deme-fit")` enumerates the fit set in sorted
cohort row order before the fixed inner permutation is applied. -/
noncomputable def fitSet {n fit : ℕ} (h : fit ≤ n) (permutation : Equiv.Perm (Fin n)) :
    Finset (Fin n) := Finset.univ.map (fitRows h permutation)

theorem fitSet_card {n fit : ℕ} (h : fit ≤ n) (permutation : Equiv.Perm (Fin n)) :
    (fitSet h permutation).card = fit := by simp [fitSet]

noncomputable def sortedFit {n fit : ℕ} (h : fit ≤ n)
    (permutation : Equiv.Perm (Fin n)) : Slots fit n :=
  ((fitSet h permutation).orderEmbOfFin (fitSet_card h permutation)).toEmbedding

theorem sortedFit_mem {n fit : ℕ} (h : fit ≤ n)
    (permutation : Equiv.Perm (Fin n)) (i : Fin fit) :
    sortedFit h permutation i ∈ Set.range (fitRows h permutation) := by
  have hm := Finset.orderEmbOfFin_mem (fitSet h permutation) (fitSet_card h permutation) i
  simpa only [fitSet, Finset.mem_map, Finset.mem_univ, true_and, Set.mem_range] using hm

/-- The inner permutation is supplied once for the fixed outer fit size;
it is not sampled independently for each realized outer fit set. -/
noncomputable def innerFitRows {n fit inner : ℕ} (h : fit ≤ n) (hi : inner ≤ fit)
    (outer : Equiv.Perm (Fin n)) (fixedInner : Equiv.Perm (Fin fit)) : Slots inner n :=
  (fitRows hi fixedInner).trans (sortedFit h outer)

noncomputable def innerSelectionRows {n fit inner : ℕ} (h : fit ≤ n) (hi : inner ≤ fit)
    (outer : Equiv.Perm (Fin n)) (fixedInner : Equiv.Perm (Fin fit)) :
    Slots (fit - inner) n := (testRows hi fixedInner).trans (sortedFit h outer)

theorem inner_fit_selection_disjoint {n fit inner : ℕ} (h : fit ≤ n) (hi : inner ≤ fit)
    (outer : Equiv.Perm (Fin n)) (fixedInner : Equiv.Perm (Fin fit))
    (i : Fin inner) (j : Fin (fit - inner)) :
    innerFitRows h hi outer fixedInner i ≠ innerSelectionRows h hi outer fixedInner j := by
  intro heq
  exact fit_test_disjoint hi fixedInner i j ((sortedFit h outer).injective heq)

theorem inner_fit_test_disjoint {n fit inner : ℕ} (h : fit ≤ n) (hi : inner ≤ fit)
    (outer : Equiv.Perm (Fin n)) (fixedInner : Equiv.Perm (Fin fit))
    (i : Fin inner) (j : Fin (n - fit)) :
    innerFitRows h hi outer fixedInner i ≠ testRows h outer j := by
  obtain ⟨k, hk⟩ := sortedFit_mem h outer (fitRows hi fixedInner i)
  change sortedFit h outer (fitRows hi fixedInner i) ≠ _
  rw [← hk]
  exact fit_test_disjoint h outer k j

theorem inner_selection_test_disjoint {n fit inner : ℕ} (h : fit ≤ n) (hi : inner ≤ fit)
    (outer : Equiv.Perm (Fin n)) (fixedInner : Equiv.Perm (Fin fit))
    (i : Fin (fit - inner)) (j : Fin (n - fit)) :
    innerSelectionRows h hi outer fixedInner i ≠ testRows h outer j := by
  obtain ⟨k, hk⟩ := sortedFit_mem h outer (testRows hi fixedInner i)
  change sortedFit h outer (testRows hi fixedInner i) ≠ _
  rw [← hk]
  exact fit_test_disjoint h outer k j

/-- Ideal independent per-deme shuffles, including unequal deme sizes. -/
noncomputable def demePermutations {D : Type*} [Fintype D] [DecidableEq D] (size : D → ℕ) :
    FiniteReportLaw ((d : D) → Equiv.Perm (Fin (size d))) := uniform _

theorem demePermutations_mass {D : Type*} [Fintype D] [DecidableEq D] (size : D → ℕ)
    (permutations : (d : D) → Equiv.Perm (Fin (size d))) :
    (demePermutations size).mass permutations =
      1 / (∏ d, ((size d).factorial : ℝ)) := by
  simp [demePermutations, uniform, Fintype.card_pi, Fintype.card_perm, Nat.cast_prod]

/-- Exact finite design law conditional on the eligible causal stream.
A deterministic design decoder can include the separate PCA reservoir and
all numerical preprocessing without discarding the selected slot order. -/
noncomputable def randomDesign {D : Type*} [Fintype D] [DecidableEq D]
    (requested total count : ℕ) (h : count ≤ min requested total) (size : D → ℕ) :
    FiniteReportLaw ((Slots (min requested total) total × Slots count (min requested total)) ×
      ((d : D) → Equiv.Perm (Fin (size d)))) :=
  (reservoirCausalLaw requested total count h).joint (fun _ ↦ demePermutations size)

theorem randomDesign_expectation {D : Type*} [Fintype D] [DecidableEq D]
    (requested total count : ℕ) (h : count ≤ min requested total) (size : D → ℕ)
    (f : (Slots (min requested total) total × Slots count (min requested total)) ×
      ((d : D) → Equiv.Perm (Fin (size d))) → ℝ) :
    (randomDesign requested total count h size).expectation f =
      (completeLaw requested total).expectation (fun pool ↦
        (∑ selected, (∑ permutations, f ((pool, selected), permutations)) /
          (∏ d, ((size d).factorial : ℝ))) /
            ((min requested total).descFactorial count : ℝ)) := by
  rw [randomDesign, expectation_joint, reservoirCausalLaw_expectation]
  simp only [demePermutations, uniform_expectation, Fintype.card_pi, Fintype.card_perm,
    Fintype.card_fin, Nat.cast_prod]

end Descent.Portability.SamplingDesignLaw
