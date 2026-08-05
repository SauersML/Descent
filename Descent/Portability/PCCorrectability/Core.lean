/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.Algebra.Module.Pi
import Mathlib.Data.Real.Basic

namespace Descent.Portability

/-!
# Correctability linear-algebra core
-/

structure PCCorrectionModel where
  /-- Number of eigenvalues -/
  p : ℕ
  /-- Eigenvalues of ancestry covariance, in decreasing order -/
  eigenvals : Fin p → ℝ
  /-- All eigenvalues positive -/
  eig_pos : ∀ i, 0 < eigenvals i
  /-- Eigenvalues are decreasing -/
  eig_decreasing : ∀ i j : Fin p, i < j → eigenvals j < eigenvals i
  /-- Proportionality constant relating eigenvalues to bias -/
  c : ℝ
  c_pos : 0 < c
  /-- Number of PCs used for correction -/
  k : Fin p
  /-- At least one eigenvalue remains after correction -/
  k_lt : k.val + 1 < p

/-- The two-component spectrum `(2, 1)`, correcting on the leading PC only.

    This is the smallest model the fields permit: `k_lt` forces at least two
    components, since a retained index must leave a later one uncorrected.
    Eigenvalues `2 > 1` are positive and strictly decreasing, and `k = 0`
    retains the second. -/
noncomputable def PCCorrectionModel.witness : PCCorrectionModel where
  p := 2
  eigenvals := fun i ↦ if i.val = 0 then 2 else 1
  eig_pos := by
    intro i
    by_cases h : i.val = 0 <;> simp [h]
  eig_decreasing := by
    intro i j hij
    have hlt : i.val < j.val := hij
    have hj : j.val < 2 := j.isLt
    have hi0 : i.val = 0 := by omega
    have hj0 : j.val ≠ 0 := by omega
    norm_num [hi0, hj0]
  c := 1
  c_pos := by norm_num
  k := 0
  k_lt := by norm_num

/-- **The class is inhabited**, so the results below are not vacuously true. -/
theorem PCCorrectionModel.nonempty : Nonempty PCCorrectionModel :=
  ⟨PCCorrectionModel.witness⟩

/-- Residual bias after correcting for k PCs -/
noncomputable def PCCorrectionModel.residualBias (m : PCCorrectionModel) : ℝ :=
  m.c * ∑ i : Fin m.p, if m.k.val < i.val then m.eigenvals i else 0

/-- Uncorrected bias (k = 0) -/
noncomputable def PCCorrectionModel.uncorrectedBias (m : PCCorrectionModel) : ℝ :=
  m.c * ∑ i : Fin m.p, m.eigenvals i

/-- **PC correction reduces but doesn't eliminate bias.**
    Residual bias is strictly less than uncorrected bias (because we remove
    at least one positive eigenvalue), but strictly positive (because at
    least one eigenvalue remains). -/
theorem pc_correction_residual_bias (m : PCCorrectionModel) :
    0 < m.residualBias ∧ m.residualBias < m.uncorrectedBias := by
  unfold PCCorrectionModel.residualBias PCCorrectionModel.uncorrectedBias
  constructor
  · apply mul_pos m.c_pos
    apply Finset.sum_pos'
    · intro i _
      split_ifs with h
      · exact le_of_lt (m.eig_pos i)
      · exact le_refl _
    · refine ⟨⟨m.k.val + 1, m.k_lt⟩, Finset.mem_univ _, ?_⟩
      simp only [show m.k.val < m.k.val + 1 from Nat.lt_succ_iff.mpr (le_refl _), ite_true]
      exact m.eig_pos _
  · apply mul_lt_mul_of_pos_left _ m.c_pos
    apply Finset.sum_lt_sum
    · intro i _
      split_ifs with h
      · exact le_refl _
      · exact le_of_lt (m.eig_pos i)
    · have hp : 0 < m.p := by
        exact lt_trans (Nat.succ_pos m.k.val) m.k_lt
      refine ⟨⟨0, hp⟩, Finset.mem_univ _, ?_⟩
      simp only [show ¬(m.k.val < 0) from Nat.not_lt_zero _, ite_false]
      exact m.eig_pos _

/-!
### Fine-scale confounding missed by top-PC correction

`PCCorrectionModel.k` is the index of the last corrected PC, so the corrected
subspace contains coordinates `0, …, k`.  The complementary coordinates are
the low-eigenvalue directions.  A demographic process whose confounding
loading lies there is unchanged by top-PC residualization.
-/

/-- The span of the corrected, high-eigenvalue principal components. -/
def PCCorrectionModel.topPCSpan (m : PCCorrectionModel) :
    Submodule ℝ (Fin m.p → ℝ) where
  carrier := {v | ∀ i, m.k.val < i.val → v i = 0}
  zero_mem' := by
    intro i _
    rfl
  add_mem' := by
    intro x y hx hy i hi
    simp [hx i hi, hy i hi]
  smul_mem' := by
    intro a x hx i hi
    simp [hx i hi]

/-- The low-eigenvalue subspace omitted by top-PC correction. -/
def PCCorrectionModel.fineScaleSubspace (m : PCCorrectionModel) :
    Submodule ℝ (Fin m.p → ℝ) where
  carrier := {v | ∀ i, i.val ≤ m.k.val → v i = 0}
  zero_mem' := by
    intro i _
    rfl
  add_mem' := by
    intro x y hx hy i hi
    simp [hx i hi, hy i hi]
  smul_mem' := by
    intro a x hx i hi
    simp [hx i hi]

/-- Residual confounding after projecting out the corrected top PCs. -/
noncomputable def PCCorrectionModel.removeTopPCs (m : PCCorrectionModel)
    (bias : Fin m.p → ℝ) : Fin m.p → ℝ :=
  fun i ↦ if m.k.val < i.val then bias i else 0

/-- Squared Euclidean magnitude of the confounding left after PC correction. -/
noncomputable def PCCorrectionModel.residualBiasEnergy (m : PCCorrectionModel)
    (bias : Fin m.p → ℝ) : ℝ :=
  ∑ i, (m.removeTopPCs bias i) ^ 2

/-- Top-PC correction removes exactly the confounding vectors in the top-PC span. -/
theorem PCCorrectionModel.mem_topPCSpan_iff_removeTopPCs_eq_zero
    (m : PCCorrectionModel) (bias : Fin m.p → ℝ) :
    bias ∈ m.topPCSpan ↔ m.removeTopPCs bias = 0 := by
  constructor
  · intro hbias
    change ∀ i, m.k.val < i.val → bias i = 0 at hbias
    funext i
    by_cases hi : m.k.val < i.val
    · simp [PCCorrectionModel.removeTopPCs, hi, hbias i hi]
    · simp [PCCorrectionModel.removeTopPCs, hi]
  · intro hzero
    change ∀ i, m.k.val < i.val → bias i = 0
    intro i hi
    have hcoordinate := congrFun hzero i
    simpa [PCCorrectionModel.removeTopPCs, hi] using hcoordinate

/-- Fine-scale confounding is a fixed point of top-PC residualization. -/
theorem PCCorrectionModel.removeTopPCs_eq_self_of_mem_fineScale
    (m : PCCorrectionModel) (bias : Fin m.p → ℝ)
    (hbias : bias ∈ m.fineScaleSubspace) :
    m.removeTopPCs bias = bias := by
  change ∀ i, i.val ≤ m.k.val → bias i = 0 at hbias
  funext i
  by_cases hi : m.k.val < i.val
  · simp [PCCorrectionModel.removeTopPCs, hi]
  · have hle : i.val ≤ m.k.val := Nat.le_of_not_gt hi
    simp [PCCorrectionModel.removeTopPCs, hi, hbias i hle]

/-- A demographic confounding direction supported on omitted, low-eigenvalue PCs. -/
structure RecentFineScaleConfounding where
  pc : PCCorrectionModel
  /-- Confounding loadings in the ancestry-covariance eigenbasis. -/
  direction : Fin pc.p → ℝ
  /-- Recent demographic structure has no loading on the corrected top PCs. -/
  fineScale : direction ∈ pc.fineScaleSubspace
  /-- An omitted direction carrying a quantitatively nontrivial loading. -/
  witness : Fin pc.p
  witness_omitted : pc.k.val < witness.val
  minLoading : ℝ
  minLoading_pos : 0 < minLoading
  loading_ge : minLoading ≤ |direction witness|

/-- **The class is inhabited**, on the two-component model correcting the leading PC.

    The confounding sits entirely on coordinate `1`, which `k = 0` leaves
    uncorrected, so `fineScale` holds and the loading there is `1`. This is the
    smallest configuration in which the omitted direction exists at all: `k_lt`
    is what guarantees a coordinate above `k` for it to live on. -/
noncomputable def RecentFineScaleConfounding.canonical : RecentFineScaleConfounding where
  pc := PCCorrectionModel.witness
  direction := fun i ↦ if i.val = 0 then 0 else 1
  fineScale := by
    intro i hi
    have hi0 : i.val = 0 := by
      simpa [PCCorrectionModel.witness] using Nat.le_zero.mp hi
    simp [hi0]
  witness := ⟨1, by simp [PCCorrectionModel.witness]⟩
  witness_omitted := by simp [PCCorrectionModel.witness]
  minLoading := 1
  minLoading_pos := by norm_num
  loading_ge := by norm_num

theorem RecentFineScaleConfounding.nonempty : Nonempty RecentFineScaleConfounding :=
  ⟨RecentFineScaleConfounding.canonical⟩

/-- Recent fine-scale confounding cannot lie in the span of the corrected top PCs. -/
theorem RecentFineScaleConfounding.not_mem_topPCSpan
    (m : RecentFineScaleConfounding) :
    m.direction ∉ m.pc.topPCSpan := by
  intro htop
  have hremoved : m.pc.removeTopPCs m.direction = 0 :=
    (m.pc.mem_topPCSpan_iff_removeTopPCs_eq_zero m.direction).mp htop
  have hfixed : m.pc.removeTopPCs m.direction = m.direction :=
    m.pc.removeTopPCs_eq_self_of_mem_fineScale m.direction m.fineScale
  have hdirection : m.direction = 0 := hfixed.symm.trans hremoved
  have hwitness : m.direction m.witness = 0 := congrFun hdirection m.witness
  have hloading := m.loading_ge
  rw [hwitness, abs_zero] at hloading
  exact (not_le_of_gt m.minLoading_pos) hloading

/-- **Converse to `pc_correction_residual_bias`.**
If recent demographic confounding has loading at least `δ` in any omitted
low-eigenvalue direction, top-PC correction leaves squared residual bias at
least `δ²`; in fact it leaves the entire fine-scale direction unchanged. -/
theorem pc_correction_recent_structure_lower_bound
    (m : RecentFineScaleConfounding) :
    m.pc.removeTopPCs m.direction = m.direction ∧
      m.minLoading ^ 2 ≤ m.pc.residualBiasEnergy m.direction := by
  have hfixed : m.pc.removeTopPCs m.direction = m.direction :=
    m.pc.removeTopPCs_eq_self_of_mem_fineScale m.direction m.fineScale
  constructor
  · exact hfixed
  · have hloading_sq : m.minLoading ^ 2 ≤ (m.direction m.witness) ^ 2 := by
      rw [sq_le_sq]
      simpa [abs_of_pos m.minLoading_pos] using m.loading_ge
    have hwitness_residual :
        m.pc.removeTopPCs m.direction m.witness = m.direction m.witness := by
      simp [PCCorrectionModel.removeTopPCs, m.witness_omitted]
    have hcoordinate :
        (m.pc.removeTopPCs m.direction m.witness) ^ 2 ≤
          m.pc.residualBiasEnergy m.direction := by
      unfold PCCorrectionModel.residualBiasEnergy
      exact Finset.single_le_sum
        (fun i _ ↦ sq_nonneg (m.pc.removeTopPCs m.direction i)) (by simp)
    rw [hwitness_residual] at hcoordinate
    exact hloading_sq.trans hcoordinate

/-- Squared residual bias for a diagonal spectral correction.  This includes
LMM-style shrinkage when `retention i` is the residual transfer factor in the
ancestry-covariance eigenbasis. -/
noncomputable def spectralResidualBiasEnergy {p : ℕ}
    (retention bias : Fin p → ℝ) : ℝ :=
  ∑ i, (retention i * bias i) ^ 2



/-- Any spectral correction retains a quantifiable amount of confounding
whenever one demographic direction has nonzero loading and nonzero residual
transfer.  For an LMM this is a constraint-induced floor, not a claim that the
LMM shares PCA's BBP cutoff: an LMM can aggregate information across lower
sample PCs even when the leading sample PC is sub-threshold. -/
theorem spectral_correction_residual_bias_lower_bound {p : ℕ}
    (retention bias : Fin p → ℝ) (j : Fin p) (ρ δ : ℝ)
    (hρ : 0 ≤ ρ) (hδ : 0 ≤ δ)
    (hretention : ρ ≤ |retention j|)
    (hloading : δ ≤ |bias j|) :
    (ρ * δ) ^ 2 ≤ spectralResidualBiasEnergy retention bias := by
  have habs_product : ρ * δ ≤ |retention j * bias j| := by
    rw [abs_mul]
    exact mul_le_mul hretention hloading hδ (abs_nonneg (retention j))
  have hcoordinate_sq : (ρ * δ) ^ 2 ≤ (retention j * bias j) ^ 2 := by
    rw [sq_le_sq]
    simpa [abs_of_nonneg (mul_nonneg hρ hδ)] using habs_product
  have hcoordinate :
      (retention j * bias j) ^ 2 ≤ spectralResidualBiasEnergy retention bias := by
    unfold spectralResidualBiasEnergy
    exact Finset.single_le_sum
      (fun i _ ↦ sq_nonneg (retention i * bias i)) (by simp)
  exact hcoordinate_sq.trans hcoordinate

end Descent.Portability
