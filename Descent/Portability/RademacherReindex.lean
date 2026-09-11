/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.RademacherJointLimit

assert_below Descent.Decision Descent.Program

/-!
Relabeling a finite row preserves its actual independent fair-sign law, product
sign, and homogeneous weighted sum. This identifies the sign laws on different
heterozygosity patterns of the same size without assuming exchangeability.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.RademacherReindex

open scoped BigOperators
open HWEInteractionLaw BalancedHWEWeakLimit RademacherArrayWeakLimit RademacherParityLaw

variable {ι κ : Type*}

/-- A bijective relabeling of the realized sign coordinates. -/
def reindex (e : ι ≃ κ) : (ι → Bool) ≃ (κ → Bool) where
  toFun b := fun j ↦ b (e.symm j)
  invFun b := fun i ↦ b (e i)
  left_inv b := by funext i; simp
  right_inv b := by funext j; simp

variable [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- Relabeling preserves the actual product probability of each sign vector. -/
theorem mass_reindex (e : ι ≃ κ) (b : ι → Bool) :
    (independentLaw (fun _ : κ ↦ signLaw)).mass (reindex e b) =
      (independentLaw (fun _ : ι ↦ signLaw)).mass b := by
  change (∏ j : κ, signLaw.mass (b (e.symm j))) = ∏ i : ι, signLaw.mass (b i)
  exact e.symm.prod_comp (fun i ↦ signLaw.mass (b i))

/-- Equality of expectations for every statistic under the actual relabeled finite law. -/
theorem expectation_reindex (e : ι ≃ κ) (f : (κ → Bool) → ℝ) :
    (independentLaw (fun _ : ι ↦ signLaw)).expectation (fun b ↦ f (reindex e b)) =
      (independentLaw (fun _ : κ ↦ signLaw)).expectation f := by
  unfold FiniteReportLaw.expectation
  apply Fintype.sum_equiv (reindex e)
  intro b
  rw [mass_reindex]

omit [DecidableEq ι] [DecidableEq κ] in
/-- The product sign is invariant under relabeling. -/
theorem parity_reindex (e : ι ≃ κ) (b : ι → Bool) : parity (reindex e b) = parity b := by
  exact e.symm.prod_comp (fun i ↦ signValue (b i))

omit [DecidableEq ι] [DecidableEq κ] in
/-- Homogeneous log-profile sums depend only on the number of remaining loci. -/
theorem weightedSum_reindex (e : ι ≃ κ) (a : ℝ) (b : ι → Bool) :
    weightedSum (fun _ : κ ↦ a) (reindex e b) = weightedSum (fun _ : ι ↦ a) b := by
  exact e.symm.sum_comp (fun i ↦ a * signValue (b i))

/-- The complete signed exponential amplitude law is invariant under relabeling. -/
theorem amplitude_expectation_reindex (e : ι ≃ κ) (a c : ℝ) (f : ℝ → ℝ) :
    (independentLaw (fun _ : ι ↦ signLaw)).expectation
      (fun b ↦ f (c * parity b * Real.exp (-weightedSum (fun _ : ι ↦ a) b))) =
        (independentLaw (fun _ : κ ↦ signLaw)).expectation
          (fun b ↦ f (c * parity b * Real.exp (-weightedSum (fun _ : κ ↦ a) b))) := by
  have hh := expectation_reindex e
    (fun b ↦ f (c * parity b * Real.exp (-weightedSum (fun _ : κ ↦ a) b)))
  simpa only [parity_reindex, weightedSum_reindex] using hh

end Descent.Portability.RademacherReindex
