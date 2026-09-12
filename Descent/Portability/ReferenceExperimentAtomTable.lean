/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.ReferenceExperimentCorners

assert_below Descent.Decision Descent.Program

/-!
# The tabled learner-atom law of the NOTE2 section 9 reference experiment

A corner accumulator `ReferenceExperimentCorners.tableCornerReport` weighs every learner atom by
its mass `ReferenceExperimentLaw.atomMass`, and each atom mass sums the learner over all 216
training and validation draws. A kernel decision of a corner therefore runs the learner for all
fifty atoms before it reads a single report, and does so again in every corner certificate.

This module decides the atom law once per context against a table of the 72 atoms of positive
mass, 18 in each context (`atomMass_table`), and restates every corner accumulator on the table
(`tableCornerReport_eq_atomCornerReport`), so a corner certificate that first rewrites with it
evaluates only its report. Each tabled context law sums to one (`atomTable_sum`).

## Empirical status

None. The bodies here are exact rational arithmetic on a completely specified finite model:
every mass is a finite sum of products of the supplied rationals, so no measurement can bear on
these values.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.ReferenceExperimentAtomTable

open ReferenceExperimentLaw ReferenceExperimentTable ReferenceExperimentCorners

/-- The learner atoms of positive mass with their masses, one entry per context and atom,
decided from the learner in `atomMass_table`. -/
def atomEntries : List ((Bool × Bool) × LearnerAtom × ℚ) :=
  [ ((false, false), (0, 0, 2), 256 / 1125),
    ((false, false), (0, 1, 1), 368 / 3375),
    ((false, false), (0, 1, 3), 8 / 45),
    ((false, false), (0, 2, 0), 44 / 3375),
    ((false, false), (0, 2, 2), 4 / 25),
    ((false, false), (0, 2, 4), 14 / 375),
    ((false, false), (0, 3, 1), 4 / 225),
    ((false, false), (0, 3, 3), 44 / 1125),
    ((false, false), (0, 4, 2), 1 / 125),
    ((false, false), (1, 0, 2), 16 / 3375),
    ((false, false), (1, 1, 1), 128 / 3375),
    ((false, false), (1, 1, 3), 88 / 3375),
    ((false, false), (1, 2, 0), 176 / 3375),
    ((false, false), (1, 2, 2), 28 / 675),
    ((false, false), (1, 2, 4), 64 / 3375),
    ((false, false), (1, 3, 1), 8 / 375),
    ((false, false), (1, 3, 3), 22 / 3375),
    ((false, false), (1, 4, 2), 4 / 3375),
    ((false, true), (0, 0, 2), 88 / 375),
    ((false, true), (0, 1, 1), 94 / 1125),
    ((false, true), (0, 1, 3), 238 / 1125),
    ((false, true), (0, 2, 0), 11 / 1500),
    ((false, true), (0, 2, 2), 23 / 150),
    ((false, true), (0, 2, 4), 343 / 6750),
    ((false, true), (0, 3, 1), 29 / 2250),
    ((false, true), (0, 3, 3), 301 / 6750),
    ((false, true), (0, 4, 2), 17 / 2250),
    ((false, true), (1, 0, 2), 16 / 3375),
    ((false, true), (1, 1, 1), 112 / 3375),
    ((false, true), (1, 1, 3), 32 / 1125),
    ((false, true), (1, 2, 0), 127 / 3375),
    ((false, true), (1, 2, 2), 53 / 1350),
    ((false, true), (1, 2, 4), 317 / 13500),
    ((false, true), (1, 3, 1), 64 / 3375),
    ((false, true), (1, 3, 3), 23 / 3375),
    ((false, true), (1, 4, 2), 4 / 3375),
    ((true, false), (0, 0, 2), 31 / 225),
    ((true, false), (0, 1, 1), 67 / 675),
    ((true, false), (0, 1, 3), 59 / 450),
    ((true, false), (0, 2, 0), 2 / 135),
    ((true, false), (0, 2, 2), 43 / 225),
    ((true, false), (0, 2, 4), 1 / 30),
    ((true, false), (0, 3, 1), 7 / 225),
    ((true, false), (0, 3, 3), 23 / 450),
    ((true, false), (0, 4, 2), 2 / 75),
    ((true, false), (1, 0, 2), 8 / 675),
    ((true, false), (1, 1, 1), 22 / 675),
    ((true, false), (1, 1, 3), 2 / 27),
    ((true, false), (1, 2, 0), 67 / 2700),
    ((true, false), (1, 2, 2), 71 / 1350),
    ((true, false), (1, 2, 4), 167 / 2700),
    ((true, false), (1, 3, 1), 1 / 90),
    ((true, false), (1, 3, 3), 19 / 1350),
    ((true, false), (1, 4, 2), 1 / 1350),
    ((true, true), (0, 0, 2), 17 / 120),
    ((true, true), (0, 1, 1), 17 / 225),
    ((true, true), (0, 1, 3), 7 / 45),
    ((true, true), (0, 2, 0), 1 / 120),
    ((true, true), (0, 2, 2), 41 / 225),
    ((true, true), (0, 2, 4), 49 / 1080),
    ((true, true), (0, 3, 1), 1 / 45),
    ((true, true), (0, 3, 3), 77 / 1350),
    ((true, true), (0, 4, 2), 1 / 40),
    ((true, true), (1, 0, 2), 8 / 675),
    ((true, true), (1, 1, 1), 4 / 135),
    ((true, true), (1, 1, 3), 2 / 25),
    ((true, true), (1, 2, 0), 47 / 2700),
    ((true, true), (1, 2, 2), 13 / 270),
    ((true, true), (1, 2, 4), 101 / 1350),
    ((true, true), (1, 3, 1), 13 / 1350),
    ((true, true), (1, 3, 3), 2 / 135),
    ((true, true), (1, 4, 2), 1 / 1350)]

/-- The tabled mass of a learner atom in one context, zero when the atom is not listed. -/
def atomTable (context : Bool × Bool) (atom : LearnerAtom) : ℚ :=
  ((atomEntries.find? fun entry ↦ entry.1 == context && entry.2.1 == atom).map
    fun entry ↦ entry.2.2).getD 0

theorem atomMass_table_zero_zero :
    ∀ atom, atomMass (false, false) atom = atomTable (false, false) atom := by
  decide +kernel

theorem atomMass_table_zero_one :
    ∀ atom, atomMass (false, true) atom = atomTable (false, true) atom := by
  decide +kernel

theorem atomMass_table_one_zero :
    ∀ atom, atomMass (true, false) atom = atomTable (true, false) atom := by
  decide +kernel

theorem atomMass_table_one_one :
    ∀ atom, atomMass (true, true) atom = atomTable (true, true) atom := by
  decide +kernel

/-- NOTE2 section 9: the learner-atom law of every context is the tabled law, decided context by
context. -/
theorem atomMass_table : ∀ context atom, atomMass context atom = atomTable context atom := by
  rintro ⟨architecture, environment⟩
  cases architecture <;> cases environment
  exacts [atomMass_table_zero_zero, atomMass_table_zero_one, atomMass_table_one_zero,
    atomMass_table_one_one]

/-- Each tabled context law of the learner atoms is a probability law. -/
theorem atomTable_sum : ∀ context, ∑ atom, atomTable context atom = 1 := by
  decide +kernel

/-- The corner accumulator of a report in one context, computed from a tabled terminal law and
the tabled atom law. -/
def atomCornerReport (entries : List ((Bool × Bool) × TerminalTypes × ℚ))
    (report : Bool × Bool → LearnerAtom → TerminalTypes → ℚ) (context : Bool × Bool) : ℚ :=
  ∑ atom, if atomTable context atom = 0 then 0
    else atomTable context atom * ∑ terminal, terminalTable entries context terminal *
      report context atom terminal

/-- Every corner accumulator is the corner accumulator computed from the tabled atom law. -/
theorem tableCornerReport_eq_atomCornerReport
    (entries : List ((Bool × Bool) × TerminalTypes × ℚ))
    (report : Bool × Bool → LearnerAtom → TerminalTypes → ℚ) (context : Bool × Bool) :
    tableCornerReport entries report context = atomCornerReport entries report context := by
  simp only [tableCornerReport, atomCornerReport, atomMass_table]

end Descent.Portability.ReferenceExperimentAtomTable
