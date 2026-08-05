/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Program.Conclusions
import Descent.PopGen.DGP
import Descent.Spectral.CirculationDefect
import Descent.Core.Fst
import Descent.Core.Parameters
import Descent.Core.Moments
import Descent.Portability.PortabilityDrift.MigrationDrift

namespace Descent.Portability

open MeasureTheory

open PopGen.TransportedMetrics (r2FromSignalVariance r2FromSignalVariance_eq_rsquared
  equalVarianceGaussianAUCFromSignalVariance
  equalVarianceGaussianAUCFromSignalVariance_eq_formula_of_ne_noise)

/-!
# `PortabilityDrift.MigrationDriftRecurrence`

Part of the split of `Portability/PortabilityDrift.lean`, which was 9,208 lines and 555
declarations -- the largest file in the corpus by both measures, and large enough that
nothing in it could be read without reading past most of it.

The parts are a CHAIN: each imports the one before, in the order the original was written.
That is the conservative choice, deliberately. A monolith's declarations depend on each
other in whatever order they happen to appear, and cutting it into modules that import only
what they use means discovering that order first -- worth doing, and not what this does.
The chain preserves every resolution the single file had, so the split cannot change what
any proof sees.

Sections are reopened and reclosed by name where a cut falls inside one: the original
opened `section PortabilityDrift` and closed it 8,000 lines later. A section scopes
`variable`s, and this file declares none at that level, so the reopening is exact.
-/


/-! ## Migration-Drift Recurrence: Deriving Fst = 1/(1 + 4Nm) from First Principles

We derive the classical Wright (1931) equilibrium Fst formula from the
migration-drift recurrence relation. The island model with migration rate m
and effective population size Ne yields a linear recurrence on Fst:

  Fst_{t+1} = (1 - 2m - 1/(2Ne)) * Fst_t + 1/(2Ne)

This is the linearized form where (1-m)² ≈ 1 - 2m. At equilibrium
Fst* = Fst_{t+1} = Fst_t, solving the linear equation gives:

  Fst* = 1 / (4*Ne*m + 1)

We prove this closed form satisfies the recurrence, then derive monotonicity
and portability consequences directly from the recurrence structure.
-/

section MigrationDriftRecurrence

/-! ### 1. The migration-drift recurrence -/

/-- **Migration-drift recurrence on Fst.**
    In the island model with migration rate `m` and effective size `Ne`,
    the linearized one-generation update of Fst is:
      Fst_{t+1} = (1 - 2m - 1/(2Ne)) * Fst_t + 1/(2Ne)
    Migration reduces Fst by a factor (1-2m), and drift adds (1-Fst)/(2Ne).
    The linearization replaces (1-m)² with 1-2m (valid for small m).

    Empirical status: **VALIDATED**
    (`validation/empirical/simcov/battery_bulk1.py`,
    `test_one_step_maps`). Same trajectories, same one-step protocol, as
    `ibdRecurrenceStep`:

      Ne     m        this def   simulated            sems
      200    0.002     0.27083   0.27079±0.00365      0.01
      200    0.010     0.10533   0.10530±0.00042      0.07
      500    0.005     0.07604   0.07602±0.00069      0.03

    This and `ibdRecurrenceStep` are two different functions and the corpus
    relates them by no theorem, which is the unresolved-fork pattern. As
    one-step maps they agree to within 0.07 sems on every design tested here, so
    the fork is real in the algebra and immaterial at these rates; it would take
    a design at large `m` to separate them.

    Power: the prediction spans 0.07604 to 0.27083 across the design. -/
noncomputable def fstMigDriftNext (Ne m Fst : ℝ) : ℝ :=
  (1 - 2 * m - 1 / (2 * Ne)) * Fst + 1 / (2 * Ne)

/-- **The migration-drift step at zero effective size, named.** Both `1 / (2 * Ne)` terms are
junk-zero at `Ne = 0`, so the step reduces to `(1 - 2 * m) * Fst`: migration still erodes
differentiation and drift contributes nothing. An empty population is reported as one in which
drift generates no differentiation at all, and iterating the step compounds the error.
Consumers must require `Ne ≠ 0`. -/
theorem fstMigDriftNext_zero_population_is_junk (m Fst : ℝ) :
    fstMigDriftNext 0 m Fst = (1 - 2 * m) * Fst := by
  unfold fstMigDriftNext
  simp

/-- The recurrence can be written as Fst_{t+1} = a * Fst_t + b where
    a = 1 - 2m - 1/(2Ne) and b = 1/(2Ne). -/
theorem fstMigDriftNext_eq (Ne m Fst : ℝ) :
    fstMigDriftNext Ne m Fst =
      (1 - 2 * m - 1 / (2 * Ne)) * Fst + 1 / (2 * Ne) := by
  rfl

/-- The drift term: when m = 0, the recurrence reduces to pure drift. -/
theorem fstMigDriftNext_no_migration (Ne Fst : ℝ) :
    fstMigDriftNext Ne 0 Fst = (1 - 1 / (2 * Ne)) * Fst + 1 / (2 * Ne) := by
  unfold fstMigDriftNext
  ring

/-- With no migration, the recurrence pushes Fst toward 1: the drift-only
    fixed point is Fst = 1. We verify: f(1) = 1. -/
theorem fstMigDriftNext_no_migration_fixedpoint_one (Ne : ℝ) (hNe : Ne ≠ 0) :
    fstMigDriftNext Ne 0 1 = 1 := by
  rw [fstMigDriftNext_no_migration]
  field_simp
  ring_nf

/-! ### 2. The exact equilibrium fixed point -/
/-! ### The migration-drift equilibrium, under one name

`fstMigDriftEquil Ne m = 1 / (4 * Ne * m + 1)` stood here as a third spelling of
`fstMigrationDriftEquilibrium Ne m = 1 / (1 + 4 * Ne * m)`, with its own junk-point
theorem, its own positivity, its own two bounds and its own two monotonicities -- eight
declarations, each the twin of one above, and a ninth proving the two spellings equal.

The prose here said so: "Three definitions of one quantity share a junk branch, so
agreement between them is not evidence about the value." The remedy for that is one
definition, not a theorem tying the copies, because a tie makes the copies consistent and
leaves the reader to find out which of the three names a given theorem happens to use.

What was genuinely this spelling's own -- the drift-over-migration-plus-drift ratio form,
which is the reading that makes the balance explicit -- is stated below on the surviving
name. -/

/-- **Intermediate form of the fixed-point equation.**
    The equilibrium can also be written as
      Fst* = (1/(2Ne)) / (2m + 1/(2Ne))
    which makes the balance between drift (numerator) and
    migration + drift (denominator) explicit. -/
theorem fstMigrationDriftEquilibrium_ratio_form (Ne m : ℝ)
    (hNe : 0 < Ne) (hm : 0 ≤ m) :
    fstMigrationDriftEquilibrium Ne m =
      (1 / (2 * Ne)) / (2 * m + 1 / (2 * Ne)) := by
  unfold fstMigrationDriftEquilibrium Descent.Core.fstFromFlow
  have hNe2 : (0 : ℝ) < 2 * Ne := by positivity
  have hden : 2 * m + 1 / (2 * Ne) ≠ 0 := by
    have : 0 < 2 * m + 1 / (2 * Ne) := by positivity
    linarith
  field_simp [hden]
  ring

/-! ### 6. The full (non-linearized) recurrence and its fixed point -/


/-! ### 7. Migration-to-neutral-benchmark connection derived from the recurrence -/

/-- **Neutral allele-frequency benchmark ratio from the derived Fst formula.**
    The benchmark ratio is `1 - Fst = 1 - 1/(4Nm + 1) = 4Nm/(4Nm + 1)`.
    This is still only the recurrence's coarse allele-frequency benchmark,
    not a mechanistic portability law.

    THIS BODY MUST NOT BE SHARED WITH `sharedLD_from_equilibrium Nₑ m`, however
    close the two spellings look. `1 - Fst` is the right answer for the sharing
    of ALLELE FREQUENCIES, which is what this benchmark is about, and the wrong
    answer for the sharing of LD, which is what `sharedLD_from_equilibrium` is
    about. The complement is written out here so that repairing the LD law
    cannot silently move the frequency benchmark. -/
noncomputable def neutralAFBenchmarkFromRecurrence (Ne m : ℝ) : ℝ :=
  1 - fstMigrationDriftEquilibrium Ne m

/-- The recurrence-derived neutral allele-frequency benchmark equals
`4Nm / (4Nm + 1)`. -/
theorem neutralAFBenchmarkFromRecurrence_eq (Ne m : ℝ)
    (hNe : 0 < Ne) (hm : 0 ≤ m) :
    neutralAFBenchmarkFromRecurrence Ne m = 4 * Ne * m / (4 * Ne * m + 1) := by
  unfold neutralAFBenchmarkFromRecurrence fstMigrationDriftEquilibrium Descent.Core.fstFromFlow
  have hden : 4 * Ne * m + 1 ≠ 0 := by nlinarith
  field_simp [hden]
  ring_nf

/-- **The recurrence-derived neutral benchmark improves with migration rate.**
    From the derived formula `4Nm/(4Nm+1)`, increasing `m` increases the
    recurrence-derived benchmark ratio. -/
theorem neutralAFBenchmarkFromRecurrence_increasing_in_m (Ne m₁ m₂ : ℝ)
    (hNe : 0 < Ne) (hm₁ : 0 < m₁) (hm₂ : 0 < m₂)
    (h_more : m₁ < m₂) :
    neutralAFBenchmarkFromRecurrence Ne m₁ < neutralAFBenchmarkFromRecurrence Ne m₂ := by
  rw [neutralAFBenchmarkFromRecurrence_eq Ne m₁ hNe (le_of_lt hm₁),
      neutralAFBenchmarkFromRecurrence_eq Ne m₂ hNe (le_of_lt hm₂)]
  rw [div_lt_div_iff₀ (by nlinarith) (by nlinarith)]
  nlinarith

/-- **The recurrence-derived neutral benchmark is nonnegative.** -/
theorem neutralAFBenchmarkFromRecurrence_nonneg (Ne m : ℝ) (hNe : 0 < Ne) (hm : 0 ≤ m) :
    0 ≤ neutralAFBenchmarkFromRecurrence Ne m := by
  rw [neutralAFBenchmarkFromRecurrence_eq Ne m hNe hm]
  exact div_nonneg (by nlinarith) (by nlinarith)

/-- **The recurrence-derived neutral benchmark is strictly positive with migration.** -/
theorem neutralAFBenchmarkFromRecurrence_pos (Ne m : ℝ) (hNe : 0 < Ne) (hm : 0 < m) :
    0 < neutralAFBenchmarkFromRecurrence Ne m := by
  rw [neutralAFBenchmarkFromRecurrence_eq Ne m hNe (le_of_lt hm)]
  exact div_pos (by nlinarith) (by nlinarith)

/-- **The recurrence-derived neutral benchmark is strictly less than `1`.** -/
theorem neutralAFBenchmarkFromRecurrence_lt_one (Ne m : ℝ) (hNe : 0 < Ne) (hm : 0 ≤ m) :
    neutralAFBenchmarkFromRecurrence Ne m < 1 := by
  rw [neutralAFBenchmarkFromRecurrence_eq Ne m hNe hm]
  rw [div_lt_one (by nlinarith : 0 < 4 * Ne * m + 1)]
  linarith

/-- **The recurrence-derived benchmark connects back to the file's coarse `R²`
benchmark.**
    Using the recurrence-derived `F_ST`, the benchmark target `R²` is the
    present-day `R²` at `fstMigrationDriftEquilibrium`. More migration yields higher
    benchmark `R²`. -/
theorem recurrence_derived_R2_increases_with_m (V_A V_E Ne m₁ m₂ : ℝ)
    (hVA : 0 < V_A) (hVE : 0 < V_E) (hNe : 0 < Ne)
    (hm₁ : 0 < m₁) (h_more : m₁ < m₂) :
    presentDayR2 V_A V_E (fstMigrationDriftEquilibrium Ne m₁) <
      presentDayR2 V_A V_E (fstMigrationDriftEquilibrium Ne m₂) := by
  exact drift_degrades_R2 V_A V_E
    (fstMigrationDriftEquilibrium Ne m₂) (fstMigrationDriftEquilibrium Ne m₁)
    hVA hVE
    (fstMigrationDriftEquilibrium_decreases_with_m Ne m₁ m₂ hNe hm₁ h_more)
    (le_of_lt (fstMigrationDriftEquilibrium_lt_one Ne m₁ hNe hm₁))

end MigrationDriftRecurrence

end Descent.Portability
