/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.PopGen.PopulationGeneticsFoundations.FstDefinitions
-- `Portability.pairwiseFstFromBranches` is the right-hand side of `wrightFIT_eq` below.
import Descent.Portability.PortabilityDrift

namespace Descent.PopGen

open MeasureTheory

/-!
# `PopulationGeneticsFoundations.WrightFStatistics`

Part of the split of `Descent/PopGen/PopulationGeneticsFoundations.lean`, which was 2,740 lines.

The parts are a FAN: each imports the parts that declare the symbols it names, and nothing
else. The split first made them a CHAIN -- each importing the one before, in the order the
original text ran -- which preserved every resolution the single file had and charged every
part a dependency on everything written above it, used or not. Recovering the real order is
the work that chain deferred: each part's identifiers were resolved against its siblings'
declarations, and the imports above are the answer, so what a part rests on is readable
from its header instead of inherited from its position in a file that no longer exists.

Where a cut falls inside a section, the section is reopened and reclosed by name. A section
scopes `variable`s and this file declares none at that level, so the reopening is exact.
-/



/-!
## Wright's Fixation Indices

Wright's F-statistics partition genetic variation into hierarchical
levels: individual, subpopulation, total.
-/

section WrightFStatistics

/-- **Wright's hierarchical F-statistics.**
    F_IT = 1 - (1 - F_IS)(1 - F_ST).
    F_IS: inbreeding within subpopulations.
    F_ST: differentiation between subpopulations (= Fst).
    F_IT: overall inbreeding. -/
noncomputable def wrightFIT (f_IS f_ST : ℝ) : ℝ :=
  Descent.Core.complementaryComposition f_IS f_ST

/-- **Wright's `F_IT` compounds the two levels, pinned.** The identity with
`pairwiseFstFromBranches` constrains the two definitions jointly and leaves a shared wrong factor
free. Two independent halves compound to three quarters, not to one -- the inbreeding
coefficients multiply as retained heterozygosities rather than adding. -/
theorem wrightFIT_compounds_two_halves :
    wrightFIT (1 / 2) (1 / 2) = 3 / 4 := by
  unfold wrightFIT Descent.Core.complementaryComposition
  norm_num

/-- Wright's decomposition identity. -/
theorem wright_decomposition (f_IS f_ST : ℝ) :
    wrightFIT f_IS f_ST = f_IS + f_ST - f_IS * f_ST := by
  unfold wrightFIT Descent.Core.complementaryComposition; ring

/-- **Wright's hierarchy, in the form that makes it one**: the RETAINED fractions multiply,
`1 - F_IT = (1 - F_IS)(1 - F_ST)`.

`wright_decomposition` above gives the additive rearrangement, which is the form the
identity is usually quoted in and the form in which the compounding is invisible: reading
`F_IS + F_ST - F_IS·F_ST` it is not obvious why a third nested level would multiply in
rather than add. In the complement form it is, and that is what
`wrightHierarchy_three_levels` below states.

The two `1 -`s are not decoration. `F` is a probability of identity by descent, so `1 - F`
is the probability that two copies are NOT identical at that level, and independence across
nested levels is what makes those probabilities multiply. -/
theorem wrightHierarchy (f_IS f_ST : ℝ) :
    1 - wrightFIT f_IS f_ST = (1 - f_IS) * (1 - f_ST) := by
  unfold wrightFIT Descent.Core.complementaryComposition; ring

/-- **And it composes.** Three nested levels compound in either association, because the
retained fractions simply multiply. A hierarchy that failed this would be an identity about
two levels wearing the name of one about many. -/
theorem wrightHierarchy_three_levels (a b c : ℝ) :
    1 - wrightFIT (wrightFIT a b) c = (1 - a) * (1 - b) * (1 - c) ∧
      wrightFIT (wrightFIT a b) c = wrightFIT a (wrightFIT b c) := by
  constructor <;>
    · unfold wrightFIT Descent.Core.complementaryComposition; ring

/-- **The multiplicative-complement composition `1 - (1-a)(1-b)` occurs twice, and the two
occurrences do not have the same status.**

`wrightFIT` composes `F_IS` with `F_ST` across *nested* levels — individual within
subpopulation within total — and there the composition is exact, because the two
complements are the retention factors of a genuine hierarchy.
`PortabilityDrift.pairwiseFstFromBranches` applies the same algebra to two *sibling*
branches, and `PortabilityDrift` records it as CONDITIONALLY VALID for exactly that
reason: composing multiplicatively in `F_ST` inserts a spurious `tauS * tauT` of divergence
time, because coalescence times add along a path while `F_ST` values do not, and near
`tau = 1` that term doubles the divergence time.

So the shared body is not a coincidence and not an identification either: it is one
algebraic move that is *correct across levels and wrong across branches*.  This theorem
exists so the arithmetic agreement is on the record and cannot drift, and so that anyone
repairing one of the two is forced to look at the other. `pairwiseFstFromBranchTaus` is the
composition PortabilityDrift offers in place of the branch case. -/
theorem wrightFIT_eq_pairwiseFstFromBranches (a b : ℝ) :
    wrightFIT a b = Portability.pairwiseFstFromBranches a b := rfl

/-- **Within-population heterozygosity loss after `t` generations of drift.**
    `1 - (1 - 1/(2 Nₑ))^t`.

    **This is *not* between-population `F_ST` after a split.** Coalescent simulation with
    branch-mode
    divergence, which removes mutational noise analytically, shows the split
    quantity is `coalFst t Ne = t / (t + 2 Nₑ)`: that is unbiased across the
    tested grid, while this formula is biased upward in eleven of twelve cells
    by up to 28 percent. The formula is correct for what it now says, and
    `heterozygosityLossFromDrift_eq_het_loss` is the theorem that says it; only the name and
    docstring were reassigning it to a different observable.

    Regime: closed population, no mutation. See `Descent.PopGen.DriftRegime`.

    Empirical status: VALIDATED as heterozygosity loss against the drift-only
    recurrence it restates (0.9048/0.6065/0.1353 retention at t = 200/1000/4000
    with Ne = 1000); FALSIFIED as split `F_ST`, and FALSIFIED as *measured*
    heterozygosity loss at mutation-drift balance, where the simulated retention
    is 1.025 ± 0.02 at every one of those times. The first clause is an identity
    and carries no empirical weight on its own — a cross-check cannot measure the
    premise it shares, `DriftRegime.crossChecks_blind_to_retention`.

    Denotes: within-population heterozygosity loss. The same formula appears under
    `heterozygosityLossFromDrift` here and `founderHeterozygosityLoss` in
    `DemographicHistory`; all three now name the quantity rather than leaving the
    formula to fix it, which it cannot.

    Power: the retention this formula predicts spans `0.9048`, `0.6065` and
    `0.1353` at `t = 200`, `1000` and `4000` with `Ne = 1000` — nearly the whole
    unit interval — while the measurement at mutation-drift balance stays at
    `1.025` across all three times. The design therefore has the power to
    separate the two regimes, which is how the falsification was reached. -/
noncomputable def heterozygosityLossFromDrift (t : ℕ) (Ne : ℝ) : ℝ :=
  Descent.Core.heterozygosityLoss Ne t

/-- **heterozygosityLossFromDrift at its junk point, named.** An empty population loses all
heterozygosity in one generation. The per-generation retention is junk-one, so the loss is `0` at
every generation count -- no drift at all, reported for the strongest drift possible. Consumers
must exclude the argument that makes the guard vanish. -/
theorem heterozygosityLossFromDrift_empty_population_is_junk (t : ℕ) :
    heterozygosityLossFromDrift t 0 = 0 := by
  unfold heterozygosityLossFromDrift Descent.Core.heterozygosityLoss Descent.Core.complement Descent.Core.geometricDecay
  simp

/-- **One generation of drift in a population of one, pinned.** This definition carries no result
of its own. At `Ne = 1` a single generation loses half the heterozygosity, which fixes the
per-generation rate at `1 / (2 Ne)` against `1 / Ne` and against `1 / (4 Ne)`. -/
theorem heterozygosityLossFromDrift_one_generation :
    heterozygosityLossFromDrift 1 1 = 1 / 2 := by
  unfold heterozygosityLossFromDrift Descent.Core.heterozygosityLoss Descent.Core.complement Descent.Core.geometricDecay
  norm_num

/-- Fst from drift is nonneg. -/
theorem fst_drift_nonneg (t : ℕ) (Ne : ℝ) (h_Ne : 2 ≤ Ne) :
    0 ≤ heterozygosityLossFromDrift t Ne := by
  unfold heterozygosityLossFromDrift Descent.Core.heterozygosityLoss Descent.Core.complement Descent.Core.geometricDecay
  rw [sub_nonneg]
  apply pow_le_one₀
  · rw [sub_nonneg, div_le_one (by linarith)]; linarith
  · rw [sub_le_self_iff]; positivity

/-- Fst from drift increases with time. -/
theorem fst_drift_increases (Ne : ℝ) (t₁ t₂ : ℕ) (h_Ne : 2 < Ne)
    (h_time : t₁ < t₂) :
    heterozygosityLossFromDrift t₁ Ne < heterozygosityLossFromDrift t₂ Ne := by
  unfold heterozygosityLossFromDrift Descent.Core.heterozygosityLoss Descent.Core.complement Descent.Core.geometricDecay
  rw [sub_lt_sub_iff_left]
  have h_base_pos : 0 < 1 - 1 / (2 * Ne) := by
    rw [sub_pos, div_lt_one (by linarith)]; linarith
  have h_base_lt : 1 - 1 / (2 * Ne) < 1 := by
    rw [sub_lt_self_iff]; positivity
  exact pow_lt_pow_right_of_lt_one₀ h_base_pos h_base_lt h_time

end WrightFStatistics

end Descent.PopGen
