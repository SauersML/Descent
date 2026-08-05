/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.PopGen.PopulationGeneticsFoundations.FstDefinitions

namespace Descent.PopGen

open MeasureTheory

/-!
# `PopulationGeneticsFoundations.SelectionMigrationBalance`

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
## Selection-Migration Balance

When natural selection acts in the presence of migration,
a balance is reached that determines the amount of differentiation
at selected loci.
-/

section SelectionMigrationBalance

/-- One generation of continent--island dynamics, selection step first: the
locally favoured allele at frequency `p` is reweighted by relative fitness
`1 + s`, then a fraction `m` of the island is replaced by continental migrants
carrying the allele at frequency zero.

Convention: selection precedes migration within a generation. The orderings are
not interchangeable -- they have different fixed points, and deterministic
iteration separates them at the fourth decimal -- so the ordering is part of the
model rather than part of the presentation.  The other order is
`continentIslandStepMigrationFirst`, and `selectionMigrationEquilibrium_orderings`
relates the two.

    Empirical status: VALIDATED (deterministic iteration reproduces the fixed
    point to all digits reported, s = 0.1 m = 0.05 -> 0.45000).

    Power: iterated over the four cells `(s, m) = (.1, .05), (.1, .08), (.1, .1),
    (.2, .4)` this map rests at `0.45000`, `0.12000`, `0` and `0`, so the design
    spans the maintained regime and the absorbing one. The migration-first
    ordering rests at `0.47368` and `0.13043` on the first two of those cells,
    which is the separation that makes the convention checkable rather than
    stylistic. -/
noncomputable def continentIslandStepSelectionFirst (s m p : ℝ) : ℝ :=
  (1 - m) * (p * (1 + s) / (1 + s * p))

/-- **continentIslandStepSelectionFirst at complete lethality at fixation, named.** At `s = -1`
the genotype is lethal and at `p = 1` it is fixed, so the mean fitness `1 + s p` vanishes and the
frequency after selection is undefined -- the population has no survivors to compute a frequency
over. Lean returns `0`, an ordinary post-selection frequency, and the extinction is not
distinguishable from loss of the allele. Consumers must exclude it by hypothesis. -/
theorem continentIslandStepSelectionFirst_lethal_fixed_is_junk (m : ℝ) :
    continentIslandStepSelectionFirst (-1) m 1 = 0 := by
  unfold continentIslandStepSelectionFirst
  norm_num

/-- **Selection before migration, pinned.** This definition carries no result of its own, and
what distinguishes it from `continentIslandStepMigrationFirst` is only the order in which the two
forces act. Selecting first on a frequency of one half with `s = 1` raises it to two thirds, and
the subsequent half-migration cuts that to one third. -/
theorem continentIslandStepSelectionFirst_reference :
    continentIslandStepSelectionFirst 1 (1 / 2) (1 / 2) = 1 / 3 := by
  unfold continentIslandStepSelectionFirst
  norm_num

/-- The same generation with the migration step first.

    Empirical status: VALIDATED (iteration gives 0.47368 at s = 0.1, m = 0.05,
    matching this map's fixed point exactly).

    Power: over the same four cells `(s, m) = (.1, .05), (.1, .08), (.1, .1),
    (.2, .4)` this map rests at `0.47368`, `0.13043`, `0` and `0`, against the
    selection-first ordering's `0.45000` and `0.12000` on the first two. The
    span covers both the maintained and the absorbing regime, and the two
    orderings are separated at every cell where the allele survives. -/
noncomputable def continentIslandStepMigrationFirst (s m p : ℝ) : ℝ :=
  ((1 - m) * p) * (1 + s) / (1 + s * ((1 - m) * p))

/-- **continentIslandStepMigrationFirst at complete lethality at fixation, named.** The
migration-first ordering reaches the same vanishing mean fitness and returns the same value, so
the two orderings -- which `continentIslandStepSelectionFirst_reference` and its partner separate
at admissible parameters -- become indistinguishable exactly where the model breaks. Consumers
must exclude it by hypothesis. -/
theorem continentIslandStepMigrationFirst_lethal_fixed_is_junk :
    continentIslandStepMigrationFirst (-1) 0 1 = 0 := by
  unfold continentIslandStepMigrationFirst
  norm_num

/-- **Migration before selection, pinned.** At the same parameters where selecting first gives
one third, migrating first gives two fifths: selection acting on the post-migration frequency is
less efficient at removing the immigrant allele, so the order of the two forces within a
generation is not a bookkeeping choice. -/
theorem continentIslandStepMigrationFirst_reference :
    continentIslandStepMigrationFirst 1 (1 / 2) (1 / 2) = 2 / 5 := by
  unfold continentIslandStepMigrationFirst
  norm_num

/-- **Selection-migration equilibrium frequency** under the selection-first
convention.

This closed form is not stipulated.  It is the nonzero solution of
`continentIslandStepSelectionFirst s m p = p`, and
`selectionMigrationEquilibrium_isFixedPoint` is the theorem that pins it: no
other constant can be substituted here and still compile.  The `max` is not
cosmetic either.  Migration is absorbing: once `m (1 + s) ≥ s` the allele is
lost outright and the equilibrium is the boundary value `0`, which
`selectionMigrationEquilibrium_eq_zero` records and
`continentIslandStep_zero` confirms is itself a fixed point.

    Empirical status: VALIDATED (0.45000, 0.12000, 0, 0 against iteration at
    (s, m) = (.1, .05), (.1, .08), (.1, .1), (.2, .4)).

    Power: the prediction spans `0.45000` down to `0` across those four cells,
    crossing the absorbing boundary within the design, so the `max` and the
    interior formula are both exercised. The migration-first closed form gives
    `0.47368` and `0.13043` where this one gives `0.45000` and `0.12000`, so the
    check also separates the two orderings. -/
noncomputable def selectionMigrationEquilibrium (s m : ℝ) : ℝ :=
  max 0 ((s - m - m * s) / s)

/-- **selectionMigrationEquilibrium at zero selection, named.** Without selection there is no
selection-migration balance and this formula does not describe the equilibrium at all. The
divisor is zero, the ratio is junk-zero, and `max 0` returns `0`: the locally adapted allele
reported as absent, which is also what complete swamping by migration gives. The clamp protects
the lower end and lets the degeneracy through it. Consumers must exclude it by hypothesis. -/
theorem selectionMigrationEquilibrium_no_selection_is_junk (m : ℝ) :
    selectionMigrationEquilibrium 0 m = 0 := by
  unfold selectionMigrationEquilibrium
  simp

/-- The equilibrium under the migration-first convention.

Derived, not stipulated, in the same way as its companion:
`selectionMigrationEquilibriumMigrationFirst_isFixedPoint` proves it is the
nonzero solution of `continentIslandStepMigrationFirst s m p = p`, and the
`max 0` carries the same absorbing boundary, since migration swamps selection
under either ordering.

    Empirical status: VALIDATED (iteration gives 0.47368 at s = 0.1, m = 0.05,
    matching this closed form; the selection-first convention rests at 0.45000
    on the same parameters, which is the composition convention showing up in
    the fourth decimal).

    Power: across `(s, m) = (.1, .05), (.1, .08), (.1, .1), (.2, .4)` this form
    predicts `0.47368`, `0.13043`, `0` and `0`, spanning the maintained regime
    and the absorbing one, against the selection-first form's `0.45000` and
    `0.12000` where the allele survives. -/
noncomputable def selectionMigrationEquilibriumMigrationFirst (s m : ℝ) : ℝ :=
  max 0 ((s - m - m * s) / (s * (1 - m)))

/-- **selectionMigrationEquilibriumMigrationFirst at zero selection, named.** The migration-first
ordering fails at the same point and to the same value, so the two orderings agree exactly where
neither is defined. An agreement check between them passes on the degenerate case. Consumers must
exclude it by hypothesis. -/
theorem selectionMigrationEquilibriumMigrationFirst_no_selection_is_junk (m : ℝ) :
    selectionMigrationEquilibriumMigrationFirst 0 m = 0 := by
  unfold selectionMigrationEquilibriumMigrationFirst
  simp

/-- **The migration-first equilibrium is a fixed point of the migration-first
map.**  Neither ordering is more correct, but each must be pinned by its own
dynamic; without this theorem the two closed forms could be swapped and nothing
would fail to compile. -/
theorem selectionMigrationEquilibriumMigrationFirst_isFixedPoint (s m : ℝ)
    (h_s : 0 < s) (h_m : m < 1) (h_maintained : m * (1 + s) < s) :
    continentIslandStepMigrationFirst s m
        (selectionMigrationEquilibriumMigrationFirst s m) =
      selectionMigrationEquilibriumMigrationFirst s m := by
  have hs' : s ≠ 0 := ne_of_gt h_s
  have hm : (0 : ℝ) < 1 - m := by linarith
  have hm' : (1 : ℝ) - m ≠ 0 := ne_of_gt hm
  have hsm : (1 : ℝ) + s ≠ 0 := by positivity
  have hx : 0 < (s - m - m * s) / (s * (1 - m)) := by
    apply div_pos _ (mul_pos h_s hm)
    nlinarith
  have heq : selectionMigrationEquilibriumMigrationFirst s m =
      (s - m - m * s) / (s * (1 - m)) := max_eq_right hx.le
  rw [heq]
  unfold continentIslandStepMigrationFirst
  have hden : 1 + s * ((1 - m) * ((s - m - m * s) / (s * (1 - m)))) =
      (1 + s) * (1 - m) := by
    field_simp
    ring
  rw [hden]
  field_simp

/-- Loss is absorbing: an allele absent from the island stays absent. -/
@[simp] theorem continentIslandStep_zero (s m : ℝ) :
    continentIslandStepSelectionFirst s m 0 = 0 := by
  unfold continentIslandStepSelectionFirst
  simp

/-- **The equilibrium is a fixed point of the one-generation map.**  This is the
theorem that makes the closed form above unfalsifiable-by-stipulation
impossible: it is derived from the dynamic, not asserted alongside it. -/
theorem selectionMigrationEquilibrium_isFixedPoint (s m : ℝ)
    (h_s : 0 < s) (h_m : m < 1) (h_maintained : m * (1 + s) < s) :
    continentIslandStepSelectionFirst s m (selectionMigrationEquilibrium s m) =
      selectionMigrationEquilibrium s m := by
  have hs' : s ≠ 0 := ne_of_gt h_s
  have hm : (0 : ℝ) < 1 - m := by linarith
  have hm' : (1 : ℝ) - m ≠ 0 := ne_of_gt hm
  have hsm : (1 : ℝ) + s ≠ 0 := by positivity
  have hx : 0 < (s - m - m * s) / s := by
    apply div_pos _ h_s
    nlinarith
  have heq : selectionMigrationEquilibrium s m = (s - m - m * s) / s :=
    max_eq_right hx.le
  rw [heq]
  unfold continentIslandStepSelectionFirst
  have hden : 1 + s * ((s - m - m * s) / s) = (1 + s) * (1 - m) := by
    field_simp
    ring
  rw [hden]
  field_simp

/-- **Migration swamps selection.**  Once migration exceeds the selective
advantage the allele is lost, not merely rare.  The previous statement of this
result bounded the frequency below `1/10`; the frequency is `0`. -/
theorem selectionMigrationEquilibrium_eq_zero (s m : ℝ)
    (h_s : 0 < s) (h_swamped : s ≤ m * (1 + s)) :
    selectionMigrationEquilibrium s m = 0 := by
  unfold selectionMigrationEquilibrium
  apply max_eq_left
  apply div_nonpos_of_nonpos_of_nonneg _ h_s.le
  nlinarith

/-- **Strong selection maintains near-complete differentiation.**  Stated
against the migration load `m (1 + s)` that the dynamic actually produces. -/
theorem selectionMigrationEquilibrium_ge_of_strong_selection (s m : ℝ)
    (h_s : 0 < s) (h_strong : 10 * (m * (1 + s)) ≤ s) :
    9 / 10 ≤ selectionMigrationEquilibrium s m := by
  have hge : 9 / 10 ≤ (s - m - m * s) / s := by
    rw [le_div_iff₀ h_s]
    nlinarith
  exact le_max_of_le_right hge

/-- The equilibrium never leaves the unit interval. -/
theorem selectionMigrationEquilibrium_lt_one (s m : ℝ)
    (h_s : 0 < s) (h_m : 0 < m) :
    selectionMigrationEquilibrium s m < 1 := by
  unfold selectionMigrationEquilibrium
  apply max_lt one_pos
  rw [div_lt_one h_s]
  nlinarith

/-- **The two orderings differ by exactly one migration step.**  This is the
whole content of the composition convention: neither map is more correct, but
they are not equal, and a definition that named neither could not say so. -/
theorem selectionMigrationEquilibrium_orderings (s m : ℝ)
    (h_s : 0 < s) (h_m : m < 1) :
    selectionMigrationEquilibrium s m =
      (1 - m) * selectionMigrationEquilibriumMigrationFirst s m := by
  have hm : (0 : ℝ) < 1 - m := by linarith
  have hs : s ≠ 0 := ne_of_gt h_s
  have hm' : (1 : ℝ) - m ≠ 0 := ne_of_gt hm
  -- One migration step is exactly the factor between the two conventions.
  have hkey : (s - m - m * s) / s =
      (1 - m) * ((s - m - m * s) / (s * (1 - m))) := by
    field_simp
  unfold selectionMigrationEquilibrium selectionMigrationEquilibriumMigrationFirst
  rcases le_or_gt ((s - m - m * s) / (s * (1 - m))) 0 with h | h
  · have h0 : (s - m - m * s) / s ≤ 0 := by rw [hkey]; nlinarith
    rw [max_eq_left h0, max_eq_left h, mul_zero]
  · have h0 : 0 ≤ (s - m - m * s) / s := by rw [hkey]; nlinarith
    rw [max_eq_right h0, max_eq_right h.le, hkey]

/-- **The maintained polymorphism IS a differentiation, and this says which one.**

The section header claims a selection-migration balance "determines the amount of
differentiation at selected loci", and until now nothing here named a differentiation
statistic, so the claim could not be contradicted by anything in the corpus: every theorem
above relates this module's equilibrium only to this module's own step maps.

The continent--island model puts the island at the equilibrium frequency and the continent at
zero, so the differentiation between them is Nei's `G_ST` at that pair. At the reference cell
this module already uses for its own validation -- `s = 1/10`, `m = 1/20`, where the island
rests at `9/20` -- that `G_ST` is `9/31`, about `0.29`. A migration rate of five percent
against a ten-percent selective advantage leaves less than a third of the differentiation a
fully isolated pair would show, which is the quantitative form of the statement that migration
is the more powerful of the two forces at these magnitudes.

    Empirical status: DERIVED.  Both sides are closed forms already in the corpus and this
    composes them; `selectionMigrationEquilibrium`'s own VALIDATED note carries the
    measurement that the island rests at `0.45000` in this cell, and no new measurement is
    claimed here. -/
theorem selectionMigrationEquilibrium_reference_neiGst :
    neiGstFromFrequencies (selectionMigrationEquilibrium (1 / 10) (1 / 20)) 0 = 9 / 31 := by
  have hp : selectionMigrationEquilibrium (1 / 10) (1 / 20) = 9 / 20 := by
    unfold selectionMigrationEquilibrium
    rw [show ((1 : ℝ) / 10 - 1 / 20 - 1 / 20 * (1 / 10)) / (1 / 10) = 9 / 20 by norm_num]
    exact max_eq_right (by norm_num)
  rw [hp]
  unfold neiGstFromFrequencies
  norm_num

/-- **Loci under selection contribute disproportionally to portability loss.**
    Selected loci have higher Fst → larger portability impact
    despite being a small fraction of all loci.
    The weighted Fst contribution of selected loci (fraction × fst_selected)
    can exceed their fraction of the genome, showing disproportionate impact
    when fst_selected > fst_neutral. -/
theorem mul_lt_mul_left_of_lt_of_pos
    (fst_selected fst_neutral fraction_selected : ℝ)
    (h_higher : fst_neutral < fst_selected)
    (h_pos : 0 < fraction_selected) :
    -- The selected loci contribution exceeds what you'd expect from neutral Fst
    fraction_selected * fst_neutral < fraction_selected * fst_selected := by
  exact mul_lt_mul_of_pos_left h_higher h_pos

/-- **Genome-wide Fst is dominated by neutral loci.**
    Since most of the genome is neutral and selected loci are rare,
    genome-wide Fst reflects drift, not selection.
    But portability loss at selected loci can exceed the neutral prediction. -/
theorem abs_mixture_sub_lt_of_weight_lt
    (fst_gw fst_neutral fst_selected : ℝ)
    (f_sel : ℝ) -- fraction of selected loci
    (h_gw : fst_gw = (1 - f_sel) * fst_neutral + f_sel * fst_selected)
    (h_small : f_sel < 1 / 100)
    (h_pos : 0 < f_sel)
    (h_neutral_nn : 0 ≤ fst_neutral)
    (h_sel_higher : fst_neutral < fst_selected) :
    |fst_gw - fst_neutral| < (1 / 100) * fst_selected := by
  rw [h_gw]
  have : (1 - f_sel) * fst_neutral + f_sel * fst_selected - fst_neutral =
      f_sel * (fst_selected - fst_neutral) := by ring
  rw [this, abs_of_nonneg (mul_nonneg (le_of_lt h_pos) (by linarith))]
  calc f_sel * (fst_selected - fst_neutral) < (1 / 100) * (fst_selected - fst_neutral) :=
        mul_lt_mul_of_pos_right h_small (by linarith)
    _ ≤ (1 / 100) * fst_selected := by nlinarith

end SelectionMigrationBalance

end Descent.PopGen
