/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.FiniteMixtureKernel
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Matrix.Basic

assert_below Descent.Decision Descent.Program

/-!
# Composing the physical stages of one microscopic step

NOTE1 section 2.3 builds one microscopic step by running finitely many physical stages one
after another, and asserts that composing them gives `K_h φ = φ + h Ã φ + O(h²)` for the sum
`Ã` of the stage generators.  The corpus's first assembly avoided composition by choosing one
stage uniformly at random (`FiniteMixtureKernel.uniformMixture`).  This module supplies the
composition itself.

`compose earlier later` is the probability kernel that runs `earlier` and then `later`; its
branches are pairs of branches, and `apply_compose` says its action is the earlier action of
the later action.  `reindex` relabels branches along an equivalence and changes nothing
(`apply_reindex`).  `composeDependentStages` runs a finite list of stages in order, stage `k`
with its own finite branch type `B k`, so its branch type is `(k : Fin n) → B k`
(`apply_composeDependentStages_zero`, `apply_composeDependentStages_succ`).  Stages need
different branch types: a multinomial resampling stage branches over census vectors, a
deterministic stage over haplotypes.  `composeStages` is the case of a common branch type.

The first-order law needs more than a per-stage estimate.  Composing two stages leaves the
cross term `(K_earlier − 1)(L_later φ)`: the later stage's velocity after the earlier stage has
moved the state.  It is small only if that velocity varies little under the earlier stage.
Here the requirement is met in the form NOTE1 section 2.2 already provides for the two-locus
family, a closed linear system stage by stage: every stage's first-order action on the feature
family is a matrix applied to the features,
`|K_k φ_i − φ_i − h (V_k φ)_i| ≤ h ε_k`.  Then the cross term is a linear combination of
feature displacements under one stage, each `O(h)`, so it is `O(h²)`.
`compose_expansion` is the two-stage law and `composeDependentStages_expansion` the law for any
finite number of stages, both with an explicit remainder (`compositeSlack`): the per-stage
slacks plus `h` times a constant built from a uniform feature bound, a uniform row bound on the
stage matrices, and the stage count.  `abs_compositeSlack_tendsto` says that remainder vanishes
with `h` when the stage slacks do.  `composedMicroscopicApproximation` packages this as the
`MicroscopicApproximation` NOTE1 Theorem 1 consumes, for any target generator that agrees with
the summed stage matrices on the feature vectors.

Scope.  The stages are arbitrary finite mixture kernels on an arbitrary state space; nothing
about haplotypes is used.  The matrix form of each stage's expansion is a hypothesis here.
The two-locus instance, where it is discharged, is
`Descent.Portability.TwoLocusStageComposition`.  Nothing here forms a semigroup or takes a
limit; that is NOTE1 Theorem 1, proved in `Descent.Portability.KernelRealizationPreservation`.

## Empirical status

None.  The bodies here are algebra: finite averages against probability weights, finite linear
combinations and bounds between them.  No measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

namespace Descent.Portability.StageCompositionKernel

open Descent.Portability.FiniteMixtureKernel

noncomputable section

variable {X : Type*}

/-! ## Kernels in sequence -/

/-- The probability kernel that runs `earlier` and then `later`.  A branch is a pair: the
branch drawn by the earlier stage and the branch drawn by the later stage at the moved state. -/
def compose {B₁ B₂ : Type*} [Fintype B₁] [Fintype B₂] (earlier : FiniteMixtureKernel B₁ X)
    (later : FiniteMixtureKernel B₂ X) : FiniteMixtureKernel (B₁ × B₂) X where
  weight x branch :=
    earlier.weight x branch.1 * later.weight (earlier.move branch.1 x) branch.2
  move branch x := later.move branch.2 (earlier.move branch.1 x)
  weight_nonneg x branch :=
    mul_nonneg (earlier.weight_nonneg x branch.1) (later.weight_nonneg _ branch.2)
  weight_sum x := by
    simp only [Fintype.sum_prod_type, ← Finset.mul_sum, later.weight_sum, mul_one,
      earlier.weight_sum]

/-- Running two stages in sequence averages the later stage's action over the earlier stage's
outcome. -/
theorem apply_compose {B₁ B₂ : Type*} [Fintype B₁] [Fintype B₂]
    (earlier : FiniteMixtureKernel B₁ X) (later : FiniteMixtureKernel B₂ X)
    (observable : X → ℝ) (x : X) :
    (compose earlier later).apply observable x = earlier.apply (later.apply observable) x := by
  simp only [FiniteMixtureKernel.apply, compose, Fintype.sum_prod_type, Finset.mul_sum,
    mul_assoc]

/-- The same kernel with its branches relabelled along an equivalence. -/
def reindex {B B' : Type*} [Fintype B] [Fintype B'] (relabel : B ≃ B')
    (kernel : FiniteMixtureKernel B X) : FiniteMixtureKernel B' X where
  weight x branch := kernel.weight x (relabel.symm branch)
  move branch x := kernel.move (relabel.symm branch) x
  weight_nonneg x branch := kernel.weight_nonneg x (relabel.symm branch)
  weight_sum x := (Equiv.sum_comp relabel.symm (kernel.weight x)).trans (kernel.weight_sum x)

/-- Relabelling the branches does not change the action. -/
theorem apply_reindex {B B' : Type*} [Fintype B] [Fintype B'] (relabel : B ≃ B')
    (kernel : FiniteMixtureKernel B X) (observable : X → ℝ) (x : X) :
    (reindex relabel kernel).apply observable x = kernel.apply observable x := by
  simp only [FiniteMixtureKernel.apply, reindex]
  exact Equiv.sum_comp relabel.symm
    (fun branch ↦ kernel.weight x branch * observable (kernel.move branch x))

/-- The step with no stages: a single branch that does not move the state. -/
def idleKernel {B : Fin 0 → Type*} [∀ k, Fintype (B k)] :
    FiniteMixtureKernel ((k : Fin 0) → B k) X where
  weight _ _ := 1
  move _ x := x
  weight_nonneg _ _ := zero_le_one
  weight_sum _ := by simp

/-- The step with no stages leaves every observable alone. -/
theorem apply_idleKernel {B : Fin 0 → Type*} [∀ k, Fintype (B k)] (observable : X → ℝ)
    (x : X) : (idleKernel (B := B) (X := X)).apply observable x = observable x := by
  simp [FiniteMixtureKernel.apply, idleKernel]

/-- The step made of `n` stages run in order, stage `k` with its own finite branch type `B k`:
the first stage, then the step made of the remaining stages.  A branch records the branch drawn
at every stage. -/
def composeDependentStages : (n : ℕ) → (B : Fin n → Type u) → [∀ k, Fintype (B k)] →
    ((k : Fin n) → FiniteMixtureKernel (B k) X) → FiniteMixtureKernel ((k : Fin n) → B k) X
  | 0, _, _, _ => idleKernel
  | n + 1, B, _, stages =>
      reindex (Fin.consEquiv B)
        (compose (stages 0) (composeDependentStages n (fun k ↦ B k.succ) fun k ↦ stages k.succ))

/-- With no stages the composed step does nothing. -/
theorem apply_composeDependentStages_zero (B : Fin 0 → Type u) [∀ k, Fintype (B k)]
    (stages : (k : Fin 0) → FiniteMixtureKernel (B k) X) (observable : X → ℝ) (x : X) :
    (composeDependentStages 0 B stages).apply observable x = observable x :=
  apply_idleKernel observable x

/-- The composed step runs its first stage on the outcome of the remaining stages' action. -/
theorem apply_composeDependentStages_succ (n : ℕ) (B : Fin (n + 1) → Type u)
    [∀ k, Fintype (B k)] (stages : (k : Fin (n + 1)) → FiniteMixtureKernel (B k) X)
    (observable : X → ℝ) (x : X) :
    (composeDependentStages (n + 1) B stages).apply observable x =
      (stages 0).apply
        ((composeDependentStages n (fun k ↦ B k.succ) fun k ↦ stages k.succ).apply observable)
        x := by
  simp only [composeDependentStages]
  rw [apply_reindex, apply_compose]

/-- The step made of `n` stages with a common branch type `B`, run in order. -/
def composeStages {B : Type*} [Fintype B] (n : ℕ) (stages : Fin n → FiniteMixtureKernel B X) :
    FiniteMixtureKernel (Fin n → B) X :=
  composeDependentStages n (fun _ ↦ B) stages

/-- With no stages the composed step does nothing. -/
theorem apply_composeStages_zero {B : Type*} [Fintype B]
    (stages : Fin 0 → FiniteMixtureKernel B X) (observable : X → ℝ) (x : X) :
    (composeStages 0 stages).apply observable x = observable x :=
  apply_composeDependentStages_zero (fun _ ↦ B) stages observable x

/-- The composed step runs its first stage on the outcome of the remaining stages' action. -/
theorem apply_composeStages_succ {B : Type*} [Fintype B] (n : ℕ)
    (stages : Fin (n + 1) → FiniteMixtureKernel B X) (observable : X → ℝ) (x : X) :
    (composeStages (n + 1) stages).apply observable x =
      (stages 0).apply ((composeStages n (Fin.tail stages)).apply observable) x :=
  apply_composeDependentStages_succ n (fun _ ↦ B) stages observable x

/-- The action of a kernel on a finite linear combination of observables is the same linear
combination of the actions. -/
theorem apply_linearCombination {ι B : Type*} [Fintype ι] [Fintype B]
    (kernel : FiniteMixtureKernel B X) (coefficient : ι → ℝ) (observable : ι → X → ℝ)
    (x : X) :
    kernel.apply (fun y ↦ ∑ d, coefficient d * observable d y) x =
      ∑ d, coefficient d * kernel.apply (observable d) x := by
  simp only [FiniteMixtureKernel.apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun d _ ↦ Finset.sum_congr rfl fun branch _ ↦ by ring

/-! ## The first-order law of a composed step -/

/-- A matrix whose rows have absolute sums at most `row` moves a feature vector bounded by
`bound` to a vector bounded by `row * bound`. -/
theorem abs_mulVec_le {ι : Type*} [Fintype ι] (generator : Matrix ι ι ℝ) (row bound : ℝ)
    (hrow : ∀ i, ∑ d, |generator i d| ≤ row) (hboundNonneg : 0 ≤ bound)
    (vector : ι → ℝ) (hvector : ∀ d, |vector d| ≤ bound) (i : ι) :
    |generator.mulVec vector i| ≤ row * bound := by
  simp only [Matrix.mulVec, dotProduct]
  calc |∑ d, generator i d * vector d| ≤ ∑ d, |generator i d * vector d| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d, |generator i d| * bound :=
        Finset.sum_le_sum fun d _ ↦ by
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left (hvector d) (abs_nonneg _)
    _ = (∑ d, |generator i d|) * bound := by rw [Finset.sum_mul]
    _ ≤ row * bound := mul_le_mul_of_nonneg_right (hrow i) hboundNonneg

/-- **Two stages in sequence.**  If each stage advances every feature by `step` times its own
matrix applied to the features, up to `step` times its slack, then the composed step advances
every feature by `step` times the SUM of the two matrices, up to `step` times the two slacks
plus the cross term `step · row_later · (row_earlier · bound + slack_earlier)`.  The cross term
is the later stage's first-order action after the earlier stage has moved the state; the matrix
form makes it a combination of feature displacements under one stage. -/
theorem compose_expansion {ι B₁ B₂ : Type*} [Fintype ι] [Fintype B₁] [Fintype B₂]
    (feature : X → ι → ℝ) (bound : ℝ) (hboundNonneg : 0 ≤ bound)
    (hbound : ∀ x i, |feature x i| ≤ bound)
    (earlier : FiniteMixtureKernel B₁ X) (later : FiniteMixtureKernel B₂ X)
    (earlierGenerator laterGenerator : Matrix ι ι ℝ) (earlierRow laterRow : ℝ)
    (hearlierRow : ∀ i, ∑ d, |earlierGenerator i d| ≤ earlierRow)
    (hlaterRow : ∀ i, ∑ d, |laterGenerator i d| ≤ laterRow)
    (step earlierSlack laterSlack : ℝ) (hstep : 0 ≤ step) (hearlierRowNonneg : 0 ≤ earlierRow)
    (hearlierSlackNonneg : 0 ≤ earlierSlack)
    (hearlier : ∀ x i, |earlier.apply (fun y ↦ feature y i) x - feature x i -
      step * earlierGenerator.mulVec (feature x) i| ≤ step * earlierSlack)
    (hlater : ∀ x i, |later.apply (fun y ↦ feature y i) x - feature x i -
      step * laterGenerator.mulVec (feature x) i| ≤ step * laterSlack)
    (x : X) (i : ι) :
    |(compose earlier later).apply (fun y ↦ feature y i) x - feature x i -
        step * (earlierGenerator + laterGenerator).mulVec (feature x) i| ≤
      step * (earlierSlack + laterSlack +
        step * (laterRow * (earlierRow * bound + earlierSlack))) := by
  have hfactor : 0 ≤ earlierRow * bound + earlierSlack :=
    add_nonneg (mul_nonneg hearlierRowNonneg hboundNonneg) hearlierSlackNonneg
  have hremainder : earlier.apply (fun y ↦ later.apply (fun z ↦ feature z i) y - feature y i -
      step * ∑ d, laterGenerator i d * feature y d) x =
      earlier.apply (later.apply fun z ↦ feature z i) x - earlier.apply (fun y ↦ feature y i) x -
        step * ∑ d, laterGenerator i d * earlier.apply (fun y ↦ feature y d) x := by
    rw [FiniteMixtureKernel.apply_sub, FiniteMixtureKernel.apply_sub,
      FiniteMixtureKernel.apply_smul, apply_linearCombination]
  have hidentity : (compose earlier later).apply (fun y ↦ feature y i) x - feature x i -
      step * (earlierGenerator + laterGenerator).mulVec (feature x) i =
      (earlier.apply (fun y ↦ feature y i) x - feature x i -
          step * earlierGenerator.mulVec (feature x) i) +
        step * ∑ d, laterGenerator i d * (earlier.apply (fun y ↦ feature y d) x - feature x d) +
        earlier.apply (fun y ↦ later.apply (fun z ↦ feature z i) y - feature y i -
          step * ∑ d, laterGenerator i d * feature y d) x := by
    rw [apply_compose, hremainder, Matrix.add_mulVec]
    simp only [Pi.add_apply, Matrix.mulVec, dotProduct, mul_sub, Finset.sum_sub_distrib]
    ring
  have hlaterBound : ∀ y, |later.apply (fun z ↦ feature z i) y - feature y i -
      step * ∑ d, laterGenerator i d * feature y d| ≤ step * laterSlack := fun y ↦ by
    simpa only [Matrix.mulVec, dotProduct] using hlater y i
  have hcontract := earlier.apply_le_of_le _ (step * laterSlack) hlaterBound x
  have hdisplacement : ∀ d, |earlier.apply (fun y ↦ feature y d) x - feature x d| ≤
      step * (earlierRow * bound + earlierSlack) := by
    intro d
    have hgenerator := abs_mulVec_le earlierGenerator earlierRow bound hearlierRow hboundNonneg
      (feature x) (hbound x) d
    have hscaled : |step * earlierGenerator.mulVec (feature x) d| ≤
        step * (earlierRow * bound) := by
      rw [abs_mul, abs_of_nonneg hstep]
      exact mul_le_mul_of_nonneg_left hgenerator hstep
    have hsplit : earlier.apply (fun y ↦ feature y d) x - feature x d =
        (earlier.apply (fun y ↦ feature y d) x - feature x d -
          step * earlierGenerator.mulVec (feature x) d) +
          step * earlierGenerator.mulVec (feature x) d := by ring
    rw [hsplit]
    have htriangle := abs_add_le (earlier.apply (fun y ↦ feature y d) x - feature x d -
      step * earlierGenerator.mulVec (feature x) d) (step * earlierGenerator.mulVec (feature x) d)
    linarith [hearlier x d]
  have hcross : |∑ d, laterGenerator i d * (earlier.apply (fun y ↦ feature y d) x - feature x d)|
      ≤ laterRow * (step * (earlierRow * bound + earlierSlack)) := by
    calc |∑ d, laterGenerator i d * (earlier.apply (fun y ↦ feature y d) x - feature x d)|
        ≤ ∑ d, |laterGenerator i d * (earlier.apply (fun y ↦ feature y d) x - feature x d)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ d, |laterGenerator i d| * (step * (earlierRow * bound + earlierSlack)) :=
          Finset.sum_le_sum fun d _ ↦ by
            rw [abs_mul]
            exact mul_le_mul_of_nonneg_left (hdisplacement d) (abs_nonneg _)
      _ = (∑ d, |laterGenerator i d|) * (step * (earlierRow * bound + earlierSlack)) := by
          rw [Finset.sum_mul]
      _ ≤ laterRow * (step * (earlierRow * bound + earlierSlack)) :=
          mul_le_mul_of_nonneg_right (hlaterRow i) (mul_nonneg hstep hfactor)
  have hcrossScaled : |step * ∑ d, laterGenerator i d *
      (earlier.apply (fun y ↦ feature y d) x - feature x d)| ≤
      step * (step * (laterRow * (earlierRow * bound + earlierSlack))) := by
    rw [abs_mul, abs_of_nonneg hstep]
    have hreshape : laterRow * (step * (earlierRow * bound + earlierSlack)) =
        step * (laterRow * (earlierRow * bound + earlierSlack)) := by ring
    rw [← hreshape]
    exact mul_le_mul_of_nonneg_left hcross hstep
  rw [hidentity]
  have houter := abs_add_le
    ((earlier.apply (fun y ↦ feature y i) x - feature x i -
        step * earlierGenerator.mulVec (feature x) i) +
      step * ∑ d, laterGenerator i d * (earlier.apply (fun y ↦ feature y d) x - feature x d))
    (earlier.apply (fun y ↦ later.apply (fun z ↦ feature z i) y - feature y i -
      step * ∑ d, laterGenerator i d * feature y d) x)
  have hinner := abs_add_le
    (earlier.apply (fun y ↦ feature y i) x - feature x i -
      step * earlierGenerator.mulVec (feature x) i)
    (step * ∑ d, laterGenerator i d * (earlier.apply (fun y ↦ feature y d) x - feature x d))
  have hfinal : step * earlierSlack + step * (step * (laterRow * (earlierRow * bound +
      earlierSlack))) + step * laterSlack = step * (earlierSlack + laterSlack +
        step * (laterRow * (earlierRow * bound + earlierSlack))) := by ring
  linarith [hearlier x i]

/-- The explicit remainder constant of a step composed of `stageCount` stages: the total of the
stage slacks plus `step` times the cross-term constant. -/
def compositeSlack (stageCount : ℕ) (rowBound bound step totalSlack : ℝ) : ℝ :=
  totalSlack + step * ((stageCount : ℝ) * rowBound *
    ((stageCount : ℝ) * rowBound * bound + totalSlack))

/-- The composite remainder vanishes with the step size whenever the total stage slack does. -/
theorem abs_compositeSlack_tendsto (stageCount : ℕ) (rowBound bound : ℝ) (totalSlack : ℝ → ℝ)
    (htotal : Filter.Tendsto totalSlack (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)) :
    Filter.Tendsto (fun step ↦ |compositeSlack stageCount rowBound bound step (totalSlack step)|)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  have hidentityLimit : Filter.Tendsto (fun step : ℝ ↦ step) (nhdsWithin 0 (Set.Ioi 0))
      (nhds 0) :=
    Filter.tendsto_id.mono_left nhdsWithin_le_nhds
  have hconstant : Filter.Tendsto (fun _ : ℝ ↦ (stageCount : ℝ) * rowBound)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds ((stageCount : ℝ) * rowBound)) :=
    tendsto_const_nhds
  have hconstantBound : Filter.Tendsto (fun _ : ℝ ↦ (stageCount : ℝ) * rowBound * bound)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds ((stageCount : ℝ) * rowBound * bound)) :=
    tendsto_const_nhds
  have hcomposite : Filter.Tendsto
      (fun step ↦ compositeSlack stageCount rowBound bound step (totalSlack step))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have hlimit :=
      htotal.add (hidentityLimit.mul (hconstant.mul (hconstantBound.add htotal)))
    simpa [compositeSlack] using hlimit
  have habs := (continuous_abs.tendsto 0).comp hcomposite
  simpa using habs

/-- **NOTE1 equation (11) for a composed step.**  If every one of finitely many stages, each
with its own branch type, advances each feature by `step` times its own matrix applied to the
features, up to `step` times its slack, then running the stages in order advances each feature
by `step` times the sum of the stage matrices, up to `step · compositeSlack`: the total slack
plus a cross term of order `step`. -/
theorem composeDependentStages_expansion {ι : Type*} [Fintype ι]
    (feature : X → ι → ℝ) (bound : ℝ) (hboundNonneg : 0 ≤ bound)
    (hbound : ∀ x i, |feature x i| ≤ bound) (rowBound : ℝ) (hrowNonneg : 0 ≤ rowBound)
    (step : ℝ) (hstep : 0 ≤ step) :
    ∀ (stageCount : ℕ) (B : Fin stageCount → Type u) [∀ k, Fintype (B k)]
      (stages : (k : Fin stageCount) → FiniteMixtureKernel (B k) X)
      (generator : Fin stageCount → Matrix ι ι ℝ) (slack : Fin stageCount → ℝ),
      (∀ k i, ∑ d, |generator k i d| ≤ rowBound) → (∀ k, 0 ≤ slack k) →
      (∀ k x i, |(stages k).apply (fun y ↦ feature y i) x - feature x i -
        step * (generator k).mulVec (feature x) i| ≤ step * slack k) →
      ∀ x i, |(composeDependentStages stageCount B stages).apply (fun y ↦ feature y i) x -
        feature x i - step * (∑ k, generator k).mulVec (feature x) i| ≤
          step * compositeSlack stageCount rowBound bound step (∑ k, slack k) := by
  intro stageCount
  induction stageCount with
  | zero =>
    intro B _ stages generator slack _ _ _ x i
    rw [apply_composeDependentStages_zero]
    simp [compositeSlack]
  | succ n ih =>
    intro B _ stages generator slack hrow hslack hstages x i
    have htail := ih (fun k ↦ B k.succ) (fun k ↦ stages k.succ) (fun k ↦ generator k.succ)
      (fun k ↦ slack k.succ) (fun k j ↦ hrow k.succ j) (fun k ↦ hslack k.succ)
      (fun k y j ↦ hstages k.succ y j)
    have htailRow : ∀ j, ∑ d, |(∑ k : Fin n, generator k.succ) j d| ≤ (n : ℝ) * rowBound := by
      intro j
      calc ∑ d, |(∑ k : Fin n, generator k.succ) j d|
          = ∑ d, |∑ k : Fin n, generator k.succ j d| := by simp only [Matrix.sum_apply]
        _ ≤ ∑ d, ∑ k : Fin n, |generator k.succ j d| :=
            Finset.sum_le_sum fun d _ ↦ Finset.abs_sum_le_sum_abs _ _
        _ = ∑ k : Fin n, ∑ d, |generator k.succ j d| := Finset.sum_comm
        _ ≤ ∑ _k : Fin n, rowBound := Finset.sum_le_sum fun k _ ↦ hrow k.succ j
        _ = (n : ℝ) * rowBound := by simp
    have htailSlackNonneg : 0 ≤ ∑ k : Fin n, slack k.succ :=
      Finset.sum_nonneg fun k _ ↦ hslack k.succ
    have hbinary := compose_expansion feature bound hboundNonneg hbound (stages 0)
      (composeDependentStages n (fun k ↦ B k.succ) fun k ↦ stages k.succ) (generator 0)
      (∑ k : Fin n, generator k.succ) rowBound ((n : ℝ) * rowBound) (hrow 0) htailRow step
      (slack 0) (compositeSlack n rowBound bound step (∑ k : Fin n, slack k.succ)) hstep
      hrowNonneg (hslack 0) (hstages 0) htail x i
    rw [apply_compose] at hbinary
    rw [apply_composeDependentStages_succ, Fin.sum_univ_succ, Fin.sum_univ_succ]
    have hgap : 0 ≤ step * (rowBound * (((n : ℝ) + 1) * rowBound * bound + slack 0 +
        ∑ k : Fin n, slack k.succ)) :=
      mul_nonneg hstep (mul_nonneg hrowNonneg (add_nonneg (add_nonneg
        (mul_nonneg (mul_nonneg (by positivity) hrowNonneg) hboundNonneg) (hslack 0))
        htailSlackNonneg))
    have hidentity : compositeSlack (n + 1) rowBound bound step
        (slack 0 + ∑ k : Fin n, slack k.succ) =
        (slack 0 + compositeSlack n rowBound bound step (∑ k : Fin n, slack k.succ) +
          step * ((n : ℝ) * rowBound * (rowBound * bound + slack 0))) +
        step * (rowBound * (((n : ℝ) + 1) * rowBound * bound + slack 0 +
          ∑ k : Fin n, slack k.succ)) := by
      simp only [compositeSlack]
      push_cast
      ring
    rw [hidentity]
    calc |(stages 0).apply ((composeDependentStages n (fun k ↦ B k.succ)
            (fun k ↦ stages k.succ)).apply fun y ↦ feature y i) x -
          feature x i - step * (generator 0 + ∑ k : Fin n, generator k.succ).mulVec
            (feature x) i|
        ≤ step * (slack 0 + compositeSlack n rowBound bound step (∑ k : Fin n, slack k.succ) +
            step * ((n : ℝ) * rowBound * (rowBound * bound + slack 0))) := hbinary
      _ ≤ step * ((slack 0 + compositeSlack n rowBound bound step (∑ k : Fin n, slack k.succ) +
            step * ((n : ℝ) * rowBound * (rowBound * bound + slack 0))) +
          step * (rowBound * (((n : ℝ) + 1) * rowBound * bound + slack 0 +
            ∑ k : Fin n, slack k.succ))) :=
          mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hgap) hstep

/-- **NOTE1 equation (11) for a composed step whose stages share one branch type.** -/
theorem composeStages_expansion {ι B : Type*} [Fintype ι] [Fintype B]
    (feature : X → ι → ℝ) (bound : ℝ) (hboundNonneg : 0 ≤ bound)
    (hbound : ∀ x i, |feature x i| ≤ bound) (rowBound : ℝ) (hrowNonneg : 0 ≤ rowBound)
    (step : ℝ) (hstep : 0 ≤ step) :
    ∀ (stageCount : ℕ) (stages : Fin stageCount → FiniteMixtureKernel B X)
      (generator : Fin stageCount → Matrix ι ι ℝ) (slack : Fin stageCount → ℝ),
      (∀ k i, ∑ d, |generator k i d| ≤ rowBound) → (∀ k, 0 ≤ slack k) →
      (∀ k x i, |(stages k).apply (fun y ↦ feature y i) x - feature x i -
        step * (generator k).mulVec (feature x) i| ≤ step * slack k) →
      ∀ x i, |(composeStages stageCount stages).apply (fun y ↦ feature y i) x - feature x i -
        step * (∑ k, generator k).mulVec (feature x) i| ≤
          step * compositeSlack stageCount rowBound bound step (∑ k, slack k) := by
  intro stageCount stages generator slack hrow hslack hstages x i
  exact composeDependentStages_expansion feature bound hboundNonneg hbound rowBound hrowNonneg
    step hstep stageCount (fun _ ↦ B) stages generator slack hrow hslack hstages x i

/-- **A composed step is a microscopic approximation.**  Stages indexed by `Fin stageCount`,
each a probability kernel at every step size, each advancing the features by `step` times its
own matrix up to `step` times a slack that vanishes with the step size, compose to a family of
probability kernels satisfying hypothesis (3) of NOTE1 Theorem 1 for any target generator
that agrees with the summed stage matrices on every feature vector.  The error is the absolute
value of `compositeSlack`, so it is explicit, nonnegative and vanishes with the step size. -/
def composedMicroscopicApproximation {ι B : Type*} [Fintype ι] [Fintype B]
    (feature : X → ι → ℝ) (bound : ℝ) (hboundNonneg : 0 ≤ bound)
    (hbound : ∀ x i, |feature x i| ≤ bound) (stageCount : ℕ)
    (stages : Fin stageCount → ℝ → FiniteMixtureKernel B X)
    (generator : Fin stageCount → Matrix ι ι ℝ) (rowBound : ℝ) (hrowNonneg : 0 ≤ rowBound)
    (hrow : ∀ k i, ∑ d, |generator k i d| ≤ rowBound) (slack : Fin stageCount → ℝ → ℝ)
    (hslackNonneg : ∀ k step, 0 ≤ slack k step)
    (hslackTendsto : ∀ k, Filter.Tendsto (slack k) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0))
    (hstages : ∀ k step, 0 < step → ∀ x i,
      |(stages k step).apply (fun y ↦ feature y i) x - feature x i -
        step * (generator k).mulVec (feature x) i| ≤ step * slack k step)
    (target : Matrix ι ι ℝ)
    (htarget : ∀ x i, (∑ k, generator k).mulVec (feature x) i = target.mulVec (feature x) i) :
    MicroscopicApproximation (B := Fin stageCount → B) feature target where
  kernel step := composeStages stageCount fun k ↦ stages k step
  error step := |compositeSlack stageCount rowBound bound step (∑ k, slack k step)|
  error_nonneg _ := abs_nonneg _
  error_tendsto := by
    have hsum : Filter.Tendsto (fun step ↦ ∑ k, slack k step) (nhdsWithin 0 (Set.Ioi 0))
        (nhds 0) := by
      simpa using tendsto_finset_sum Finset.univ fun k _ ↦ hslackTendsto k
    exact abs_compositeSlack_tendsto stageCount rowBound bound
      (fun step ↦ ∑ k, slack k step) hsum
  expansion step hstep x i := by
    have hbase := composeStages_expansion feature bound hboundNonneg hbound rowBound hrowNonneg
      step hstep.le stageCount (fun k ↦ stages k step) generator (fun k ↦ slack k step) hrow
      (fun k ↦ hslackNonneg k step) (fun k ↦ hstages k step hstep) x i
    rw [htarget x i] at hbase
    exact hbase.trans (mul_le_mul_of_nonneg_left (le_abs_self _) hstep.le)

end

end Descent.Portability.StageCompositionKernel
