/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.BalancedHWEInteraction
import Descent.Portability.FiniteIndependentMoments
import Mathlib.Logic.Equiv.Fin.Basic

assert_below Descent.Decision Descent.Program

/-!
Admissibility of the concrete balanced HWE counterexample: disjoint polymorphic
locus sets in the repository's original design type, exact unit variance,
growing interaction order, and uniformly vanishing locus influences.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.BalancedHWECounterexample

open scoped BigOperators
open Foundations Blindness HWEInteractionLaw BalancedHWEInteraction FiniteIndependentMoments

/-- The critical disjoint statistic is centered under its actual sampled genotype law. -/
theorem critical_mean (m : ℕ) (hm : 0 < m) :
    (rowLaw m (2 ^ m)).expectation (rowScore 1) = 0 := by
  haveI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  change (independentLaw (fun _ : Fin (2 ^ m) ↦ blockLaw
    (fun _ : Fin m ↦ HardyWeinbergModel.witness))).expectation
    (fun x ↦ ∑ j, 1 * blockCode (x j)) = 0
  simp only [one_mul]
  rw [independent_sum_mean]
  simp only [blockCode_mean, Finset.sum_const_zero]

/-- Exact unit second moment of the whole critical array, obtained by eliminating
actual cross terms under the product genotype law. -/
theorem critical_second_moment (m : ℕ) (hm : 0 < m) :
    (rowLaw m (2 ^ m)).expectation (fun x ↦ rowScore 1 x ^ 2) = 1 := by
  haveI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  change (independentLaw (fun _ : Fin (2 ^ m) ↦ blockLaw
    (fun _ : Fin m ↦ HardyWeinbergModel.witness))).expectation
    (fun x ↦ (∑ j, 1 * blockCode (x j)) ^ 2) = 1
  simp only [one_mul]
  rw [independent_sum_second _ _ (fun _ ↦ blockCode_mean)]
  simp only [blockCode_second_moment, Fintype.card_fin, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
  rw [← mul_pow]
  norm_num

/-- The coordinate embedding of a disjoint block into the complete panel. -/
def blockEmbedding (m N : ℕ) (j : Fin N) : Fin m ↪ Fin (N * m) where
  toFun i := finProdFinEquiv (j, i)
  inj' _ _ h := congrArg Prod.snd (finProdFinEquiv.injective h)

/-- The block's actual finite set of panel loci. -/
def blockSet (m N : ℕ) (j : Fin N) : Finset (Fin (N * m)) :=
  Finset.univ.map (blockEmbedding m N j)

theorem mem_blockSet (m N : ℕ) (j : Fin N) (locus : Fin (N * m)) :
    locus ∈ blockSet m N j ↔ (finProdFinEquiv.symm locus).1 = j := by
  simp only [blockSet, Finset.mem_map, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, rfl⟩
    simp [blockEmbedding]
  · intro h
    refine ⟨(finProdFinEquiv.symm locus).2, ?_⟩
    change finProdFinEquiv (j, (finProdFinEquiv.symm locus).2) = locus
    apply finProdFinEquiv.symm.injective
    simp only [Equiv.symm_apply_apply]
    exact Prod.ext h.symm rfl

/-- The counterexample inside the repository's original `GenotypeDesign` type. -/
noncomputable def design (m N : ℕ) : GenotypeDesign (N * m) (Fin N) where
  model _ := HardyWeinbergModel.witness
  locusSet := blockSet m N
  coefficient _ := 1 / Real.sqrt N
  jointGenotypeProb x := ∏ i, HardyWeinbergModel.witness.genotypeProb (x i)

theorem design_linkage_equilibrium (m N : ℕ) : (design m N).InLinkageEquilibrium :=
  fun _ ↦ rfl

theorem design_polymorphic (m N : ℕ) : (design m N).Polymorphic := by
  intro i
  norm_num [design, HardyWeinbergModel.witness]

theorem design_disjoint (m N : ℕ) : (design m N).VariantDisjoint := by
  intro j k hjk
  apply Finset.disjoint_left.mpr
  intro locus hj hk
  have hj' := (mem_blockSet m N j locus).mp hj
  have hk' := (mem_blockSet m N k locus).mp hk
  exact hjk (hj'.symm.trans hk')

theorem design_order (m N : ℕ) (j : Fin N) : (design m N).interactionOrder j = m := by
  simp [GenotypeDesign.interactionOrder, design, blockSet]

/-- Every locus belongs to exactly one block and has influence exactly 1/N. -/
theorem design_influence (m N : ℕ) (hN : 0 < N) (locus : Fin (N * m)) :
    (design m N).locusInfluence locus = 1 / N := by
  simp only [GenotypeDesign.locusInfluence, design, mem_blockSet]
  rw [show Finset.univ.filter
      (fun j : Fin N ↦ (finProdFinEquiv.symm locus).1 = j) =
      {(finProdFinEquiv.symm locus).1} by ext j; simp [eq_comm]]
  simp only [Finset.sum_singleton, div_pow, one_pow]
  rw [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ N)]

/-- Squared coefficients sum to one, in the same normalization as the original design. -/
theorem design_energy (m N : ℕ) (hN : 0 < N) :
    (∑ j, (design m N).coefficient j ^ 2) = 1 := by
  simp only [design, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    div_pow, one_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ N)]
  have hn : (N : ℝ) ≠ 0 := by positivity
  exact mul_one_div_cancel hn

/-- Relabel the same sampled genotypes as a flat panel without discarding coordinates. -/
def flatten {m N : ℕ} (x : Fin N → Fin m → DiploidGenotype) :
    Fin (N * m) → DiploidGenotype :=
  fun locus ↦ x (finProdFinEquiv.symm locus).1 (finProdFinEquiv.symm locus).2

/-- The original design's joint probability is exactly the previously analyzed row law. -/
theorem flatten_mass (m N : ℕ) (x : Fin N → Fin m → DiploidGenotype) :
    (design m N).jointGenotypeProb (flatten x) = (rowLaw m N).mass x := by
  change (∏ locus, HardyWeinbergModel.witness.genotypeProb
    (x (finProdFinEquiv.symm locus).1 (finProdFinEquiv.symm locus).2)) =
    ∏ j, ∏ i, HardyWeinbergModel.witness.genotypeProb (x j i)
  rw [← Fintype.prod_prod_type
    (fun ji : Fin N × Fin m ↦ HardyWeinbergModel.witness.genotypeProb (x ji.1 ji.2))]
  exact Fintype.prod_equiv finProdFinEquiv.symm _ _ (fun _ ↦ rfl)

/-- The statistic defined by the original design agrees pointwise with the
critical HWE row score whose exact law and variance were derived above. -/
theorem design_statistic_eq (m : ℕ)
    (x : Fin (2 ^ m) → Fin m → DiploidGenotype) :
    (∑ j, (design m (2 ^ m)).coefficient j *
      ∏ locus ∈ (design m (2 ^ m)).locusSet j,
        ((design m (2 ^ m)).model locus).standardizedGenotype (flatten x locus)) =
      rowScore 1 x := by
  have hblock : ∀ j : Fin (2 ^ m),
      (∏ locus ∈ blockSet m (2 ^ m) j,
        HardyWeinbergModel.witness.standardizedGenotype (flatten x locus)) =
      interaction (fun _ : Fin m ↦ HardyWeinbergModel.witness) (x j) := by
    intro j
    simp only [blockSet, Finset.prod_map, blockEmbedding, Function.Embedding.coeFn_mk,
      flatten, Equiv.symm_apply_apply, interaction]
  change (∑ j, (1 / Real.sqrt (2 ^ m : ℕ)) *
    ∏ locus ∈ blockSet m (2 ^ m) j,
      HardyWeinbergModel.witness.standardizedGenotype (flatten x locus)) = _
  simp_rw [hblock, one_div_mul_eq_div]
  rw [← Finset.sum_div]
  exact critical_standardization m x

/-- Uniform influence bound for every locus in the critical panel. -/
theorem critical_influence (m : ℕ) (locus : Fin (2 ^ m * m)) :
    (design m (2 ^ m)).locusInfluence locus = (1 / 2 : ℝ) ^ m := by
  rw [design_influence m (2 ^ m) (by positivity), Nat.cast_pow, Nat.cast_ofNat]
  rw [one_div_pow]

theorem critical_influence_tends_zero :
    Filter.Tendsto (fun m : ℕ ↦ (1 / 2 : ℝ) ^ m) Filter.atTop (nhds 0) :=
  tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)

/-- The expected cosine of the actual critical statistic has the non-Gaussian limit. -/
theorem critical_cosine_limit (t : ℝ) :
    Filter.Tendsto (fun m : ℕ ↦ (rowLaw m (2 ^ m)).expectation
      (fun x ↦ Real.cos (t * rowScore 1 x))) Filter.atTop
      (nhds (Real.exp (Real.cos t - 1))) := by
  apply (critical_characteristic_limit t).congr'
  filter_upwards [Filter.eventually_gt_atTop 0] with m hm
  have h := congrArg Complex.re (row_characteristic m (2 ^ m) hm 1 t)
  simpa only [characteristic_re, mul_one, Complex.ofReal_re] using h.symm

/-- The actual genotype experiment cannot have the bounded-cosine limits of
any centered Gaussian, even a degenerate Gaussian. -/
theorem no_gaussian_cosine_limits (variance : ℝ) :
    ¬ ∀ t : ℝ, Filter.Tendsto (fun m : ℕ ↦ (rowLaw m (2 ^ m)).expectation
      (fun x ↦ Real.cos (t * rowScore 1 x))) Filter.atTop
      (nhds (Real.exp (-variance * t ^ 2 / 2))) := by
  intro h
  apply critical_limit_not_gaussian variance
  intro t
  exact tendsto_nhds_unique (critical_cosine_limit t) (h t)

end Descent.Portability.BalancedHWECounterexample
