/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.ArchaicPrediction.Contrast
import Descent.Portability.ArchaicPrediction.Pairing
import Mathlib.Analysis.InnerProductSpace.PiL2

assert_below Descent.Decision Descent.Program

/-!
# Connected measured contrast graphs

This module constructs the graph operator used by the resistance theorem.
Connectedness proves injectivity after fixing the zero-sum gauge; it is not
replaced by an assumed full-rank design. Precision weights whiten the edges.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.ArchaicPrediction

open scoped BigOperators RealInnerProductSpace
variable {V A : Type*} [Fintype V] [Fintype A]

def comparisonAdjacent (source target : A → V) (u v : V) : Prop :=
  ∃ e, (source e = u ∧ target e = v) ∨ (source e = v ∧ target e = u)

lemma PairingWalk.constant {R : V → V → Prop} (f : V → ℝ)
    (he : ∀ u v, R u v → f u = f v) {u v : V} {n : ℕ} (hw : PairingWalk R u v n) :
    f u = f v := by
  induction hw with
  | nil => rfl
  | cons h hp ih => exact (he _ _ h).trans ih

/-- The kernel of a connected difference-incidence map consists of constants. -/
theorem comparison_kernel_constants (source target : A → V)
    (hc : PairingConnected (comparisonAdjacent source target)) (root : V) (f : V → ℝ) :
    (∀ e, f (target e) - f (source e) = 0) ↔ ∀ v, f v = f root := by
  constructor
  · intro h v
    obtain ⟨n, hn⟩ := hc v root
    apply hn.constant f
    intro u v huv
    obtain ⟨e, he | he⟩ := huv
    · obtain ⟨rfl, rfl⟩ := he
      exact (sub_eq_zero.mp (h e)).symm
    · obtain ⟨rfl, rfl⟩ := he
      exact sub_eq_zero.mp (h e)
  · intro h e
    rw [h (target e), h (source e), sub_self]

noncomputable def zeroSumResponses (V : Type*) [Fintype V] : Submodule ℝ (EuclideanSpace ℝ V) where
  carrier := {m | ∑ v, m v = 0}
  zero_mem' := by simp
  add_mem' := by intro a b ha hb; simp_all [Finset.sum_add_distrib]
  smul_mem' := by intro c a ha; simp_all [← Finset.mul_sum]

/-- The actual whitened incidence operator on the zero-sum response space. -/
noncomputable def graphDesign (source target : A → V) (w : A → ℝ) :
    zeroSumResponses V →L[ℝ] EuclideanSpace ℝ A :=
  LinearMap.toContinuousLinearMap
    { toFun := fun m => WithLp.toLp 2 (fun e => Real.sqrt (w e) * (m.val (target e) - m.val (source e)))
      map_add' := by intro a b; ext e; simp; ring
      map_smul' := by intro c a; ext e; simp; ring }

theorem graphDesign_injective (source target : A → V) (w : A → ℝ) (hw : ∀ e, 0 < w e)
    (hc : PairingConnected (comparisonAdjacent source target)) (root : V) :
    Function.Injective (graphDesign source target w) := by
  have hker (m : zeroSumResponses V) (hm : graphDesign source target w m = 0) : m = 0 := by
    have hd : ∀ e, m.val (target e) - m.val (source e) = 0 := by
      intro e
      have he := congrArg (fun f : EuclideanSpace ℝ A => f e) hm
      change Real.sqrt (w e) * (m.val (target e) - m.val (source e)) = 0 at he
      exact (mul_eq_zero.mp he).resolve_left (Real.sqrt_pos.mpr (hw e)).ne'
    have hconst := (comparison_kernel_constants source target hc root m.val).mp hd
    have hsum : (Fintype.card V : ℝ) * m.val root = 0 := by
      have hs := m.property
      change ∑ v, m.val v = 0 at hs
      simpa only [hconst, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using hs
    have hcard : (Fintype.card V : ℝ) ≠ 0 := by
      letI : Nonempty V := ⟨root⟩
      exact_mod_cast Fintype.card_ne_zero
    have hr : m.val root = 0 := (mul_eq_zero.mp hsum).resolve_left hcard
    apply Subtype.ext
    ext v
    simpa only [PiLp.zero_apply] using (hconst v).trans hr
  intro a b hab
  have hz : graphDesign source target w (a - b) = 0 := by simp [hab]
  exact sub_eq_zero.mp (hker (a - b) hz)

/-- The resistance-variance theorem for an explicitly constructed connected graph. -/
theorem graph_contrast_precision {Ω : Type*} [Fintype Ω]
    (source target : A → V) (w : A → ℝ) (hw : ∀ e, 0 < w e)
    (hc : PairingConnected (comparisonAdjacent source target)) (root : V)
    (m c : zeroSumResponses V) (prob : Ω → ℝ) (noise : Ω → EuclideanSpace ℝ A)
    (hmean : ∀ v, weightedMean prob (fun ω => ⟪v, noise ω⟫) = 0)
    (hcov : ∀ v, weightedMean prob (fun ω => ⟪v, noise ω⟫ ^ 2) = ⟪v, v⟫) :
    weightedMean prob (fun ω => ⟪c, contrastFit (graphDesign source target w)
      (graphDesign source target w m + noise ω) - m⟫) = 0 ∧
    weightedMean prob (fun ω => ⟪c, contrastFit (graphDesign source target w)
      (graphDesign source target w m + noise ω) - m⟫ ^ 2) =
        ⟪c, contrastInverse (graphDesign source target w) c⟫ :=
  effective_resistance_variance (graphDesign source target w)
    (graphDesign_injective source target w hw hc root) m c prob noise hmean hcov

end Descent.Portability.ArchaicPrediction
