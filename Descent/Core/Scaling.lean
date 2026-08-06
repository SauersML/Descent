/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Core.Ratios

assert_below Descent.Meta Descent.Foundations Descent.Coalescent Descent.Pangenome Descent.PopGen
assert_below Descent.Spectral Descent.Blindness Descent.Conditionals Descent.Portability
assert_below Descent.Decision Descent.Program

/-!
# Core: the scaling conventions, as types

**Depth 0-1. Imports `Core.Ratios` and nothing else from this corpus.**

## What this file is for

`Core/Fst.lean` states the principle and applies it to one pair:

> `NeiFst` and `HudsonFst` below are therefore distinct one-field types rather than two
> reals. Substituting one for the other does not typecheck. A documented hazard that the
> compiler enforces is a different object from one a docstring warns about.

That principle was applied to the estimator convention and to nothing else. The corpus
has been burned twice more, in the same way, on the SCALING convention:

* `PopGen.DGP.fstEquilibrium` carried `1/(1 + θ + M)` where the migration term needed the
  deme-count correction. `simcov/battery_bulk38.py` rejected it at 3.30 sems and 57%
  relative. The repair was a factor of two -- `islandDemeCorrection` at `d = 2` -- which
  the corpus had already measured and installed under that name, in a module the wrong
  body could not see.
* `PopGen.fstMigrationMutationEquilibriumManyDemes` carries the many-deme LIMIT
  `1/(1 + 4Ne·m + 4Ne·μ)`. `simcov/battery_falsrepair_c2.py` rejects it at `d = 20` at
  3.92 sems, where the finite-deme form carrying `20/19` matches at 2.47.
  `simcov/adjudications.json` names c2 authoritative.

Both are the same error: **a scaled quantity was passed where a differently-scaled one was
wanted, and every type involved was `ℝ`.** `θ`, `M`, `2M`, `τ` and `ρ` are all reals, all
non-negative, all order one in the regimes of interest, and nothing stopped any of them
standing in for any other. A docstring warned about it. Twice it did not work.

## What is here

Four one-field types -- `Theta`, `BigM`, `Tau`, `Rho` -- and their constructors. Each
constructor carries its own factor, and every factor is `scalingConstant`, which is
`2 * ploidy`. There is one arithmetic site for the four in `4·Ne·μ` and the two in
`t/2Ne`, and a ploidy change is an edit to `ploidy` rather than a census.

`ploidy` itself lives here rather than in `Core/Fst.lean`, where it used to. It is a
scaling convention and this is the file for those; `Core/Fst.lean` imports this one, so
every existing reference to `Descent.Core.ploidy` resolves exactly as before.

## What this file cannot do

**It cannot state, as a theorem, that a wrong conversion fails to typecheck.** A term that
does not elaborate is not a proposition, so there is nothing to prove. Lean gives the
guarantee by construction -- `Theta` and `BigM` are distinct structures with no coercion
between them, so `fstFromFlow (theta + bigM)` with the arguments swapped is a type error
and not a wrong number -- and this file cannot also assert it.

What it CAN do, and does, is the thing `Core/Fst.lean` does for the Nei--Hudson gap with
`hudsonOfNei_at_half`: exhibit the size of the error the types prevent, as a value, so a
reader knows the convention is load-bearing and not decorative. `demeCorrection_at_two`
and `demeCorrection_at_twenty` are those witnesses, and they are the two factors the
ledger actually measured.

## Empirical status

None. The bodies here are conventions: a scaling asserts nothing about a population, and
what carries an empirical status is a named quantity in a subsystem module claiming this
scaling computes something measurable. `Core.scaledMutationRate` and
`Core.scaledMigrationRate` are those names for `θ` and `M`, they are VALIDATED against
`simcov/battery_bulk19.py`, and they keep their own docstrings and ledger rows in
`Core/Fst.lean`.
-/

namespace Descent.Core

/-! ### The constant, written once -/

/-- Ploidy. Two, because every population in this corpus is diploid.

    Empirical status: NOT AN EMPIRICAL CLAIM -- this is a SHAPE, not a quantity.
    A kernel asserts nothing about a population, so no measurement can bear on it.
    What can be measured is a named quantity claiming this shape computes it, and
    those live in the subsystem modules with their own status lines and ledger rows. -/
noncomputable def ploidy : ℝ := 2

/-- Reference evaluation; see `Descent.Core.Ratios` for what these pin and why. -/
theorem ploidy_at_reference_point :
    ploidy = 2 := by
  norm_num [ploidy]

/-- **The four in `4·Ne·μ`, as a name.** It is `2 · ploidy`: two lineages, each diploid.
Every constructor below multiplies by this and no constructor writes a literal, so the
factor has one site and a ploidy change is a one-line edit.

    Empirical status: NOT AN EMPIRICAL CLAIM -- this is a SHAPE, not a quantity.
    A kernel asserts nothing about a population, so no measurement can bear on it.
    What can be measured is a named quantity claiming this shape computes it, and
    those live in the subsystem modules with their own status lines and ledger rows. -/
noncomputable def scalingConstant : ℝ := 2 * ploidy

/-- **The constant is four.** Stated so the numeral appears once, here, and every other
statement about it goes through this. -/
theorem scalingConstant_eq : scalingConstant = 4 := by
  unfold scalingConstant ploidy; norm_num

/-! ### The time scale the rate scalings are measured against

`Tau` divides generations by `ploidy · Nₑ`.  That denominator is a quantity in its own
right -- the mean pairwise coalescence time -- and it is named here so that the `2` in
`Tau.ofGenerations` and the `2` in every `_uses_timeScale` theorem downstream are the same
`ploidy`.  It lived in `Program/Conventions` as `Descent.Program.coalescentTimeScale`,
which put the definition of a scaling convention above the forty modules that consume it. -/

/-- Coalescent time scale: time measured in units of `ploidy · Nₑ`
generations.

    Regime: a single panmictic diploid population; the scale is the MEAN
    PAIRWISE coalescence time, which is what makes it a time and not a rate.

    Empirical status: **VALIDATED** (`simcov/battery_bulk37.py`). Measured in
    BRANCH mode -- straight off the genealogies, with no mutation model, so no
    mutation-rate convention can leak in -- over 2 Mb with recombination so each
    replicate averages many independent trees. Across `Nₑ` = 500, 1000, 2000,
    5000 the worst cell is 1.08 sems at 2.4% relative.

    Power: the `4·Nₑ` reading is carried on the same cells and is FALSIFIED at
    46.96 sems (105% relative). The tenfold `Nₑ` sweep is what provides that
    separation.

    Control: Watterson's `E[S] = θ·∑_{i<n} 1/i` for the expected number of
    segregating sites, computed from tree sequences generated by the same
    demography -- an independent classical result that would break if the
    demography or the mutation placement were wrong. It passes at worst 1.27
    sems (15.33 measured against 14.19 predicted at `Nₑ = 500`, rising to 151.5
    against 141.9 at `Nₑ = 5000`).

    This run replaces `battery_bulk23.py`, which measured the same thing
    correctly but carried a control asserting that the coefficient of variation
    of the replicate means is 1. That holds for a single exponential `T₂`, not
    for a mean over the many genealogies recombination supplies, so that control
    failed and its `4·Nₑ` rejection was recorded VOID. A run whose control fails
    is rightly distrusted even where its headline comparison does not depend on
    it.

    This is the `2·Nₑ` in the corpus that is NOT the other one. The `4·Nₑ` that
    appears throughout -- in `scaledMutationRate`, `scaledMigrationRate`,
    `fstMutationDriftEquilibrium` -- is the scaling of a RATE, `θ = 4·Nₑ·μ` and
    `M = 4·Nₑ·m`, and shares only its shape with this. -/
noncomputable def coalescentTimeScale (Ne : ℝ) : ℝ := ploidy * Ne

@[simp] theorem coalescentTimeScale_eq (Ne : ℝ) :
    coalescentTimeScale Ne = 2 * Ne := by
  unfold coalescentTimeScale ploidy; ring

/-! ### The four scaled quantities

Each is a one-field structure rather than an `abbrev`. An `abbrev` is definitionally the
underlying type, so it would document the convention without enforcing it -- which is the
arrangement that failed twice. The wrapper costs a `.value` at each use site and buys the
property that the two failures above become elaboration errors. -/

/-- **Scaled mutation rate**, `θ = 4 Nₑ μ`. Mutation measured in units of the coalescent
timescale: the expected number of mutations on a pair of lineages before they coalesce. -/
structure Theta where
  /-- The scaled rate. -/
  value : ℝ

/-- **Scaled migration rate**, `M = 4 Nₑ m`, in the same units as `Theta`.

Being in the same units is what makes `θ + 2M` comparable term by term -- and is also
exactly why the two were confusable as reals. The `2` on `M` in the two-deme equilibrium
is not part of this scaling; it is `islandDemeCorrection` at `d = 2`, and it belongs to
the deme count rather than to the rate. Keeping them separate is the point of the type:
`BigM` is `4 Nₑ m` and never `8 Nₑ m`. -/
structure BigM where
  /-- The scaled rate. -/
  value : ℝ

/-- **Scaled time**, `τ = t / (2 Nₑ)`. Generations divided by the coalescent timescale.

`Tau` and `Theta` are both dimensionless, both non-negative, and both order one in every
regime this corpus works in, which is the whole hazard. `Core.fstFromTau` and
`Core.fstFromFlow` are different functions of their arguments -- `τ/(1+τ)` against
`1/(1+x)` -- so passing one where the other is wanted is a complement, not a small error,
and as reals nothing distinguished them. -/
structure Tau where
  /-- The scaled time. -/
  value : ℝ

/-- **Scaled recombination rate**, `ρ = 4 Nₑ r`. Same scaling as `Theta`, different
quantity: a rate per generation of recombination rather than of mutation. -/
structure Rho where
  /-- The scaled rate. -/
  value : ℝ

/-! ### Constructors

Every factor in this section is `scalingConstant` or `ploidy`. No constructor writes a
numeric literal. -/

/-- `θ` from an effective size and a per-generation mutation rate. -/
noncomputable def Theta.ofRate (Ne μ : ℝ) : Theta := ⟨scalingConstant * Ne * μ⟩

/-- `M` from an effective size and a per-generation migration rate. -/
noncomputable def BigM.ofRate (Ne m : ℝ) : BigM := ⟨scalingConstant * Ne * m⟩

/-- `ρ` from an effective size and a per-generation recombination rate. -/
noncomputable def Rho.ofRate (Ne r : ℝ) : Rho := ⟨scalingConstant * Ne * r⟩

/-! ### The boundary constructors

`ofRate` and `ofGenerations` are how a quantity in PER-GENERATION units becomes a scaled
one, and they are the constructors a body inside the corpus should use. The four below are
for the other case: a number that arrives ALREADY SCALED, from a simulation harness, a
published table, or a differential-testing extractor that can only pass reals.

They exist so that case has ONE name each rather than an anonymous `⟨x⟩` at each site.
That is the whole difference, and it is the difference that matters: `Tau.ofScaled` is
greppable and countable, and a linter can ask whether a use of it is at a boundary or is a
body helping itself past the type. `⟨x⟩` is neither.

Every one of them is the identity on the underlying real. None of them carries a factor --
carrying a factor is what `ofRate` is for -- so a caller that reaches for one of these when
it holds a per-generation rate has skipped the scaling entirely, and `value_ofScaled` below
is what makes that visible in a proof. -/

/-- `θ` from a number that is already `4 Nₑ μ`. A boundary constructor; see the note above. -/
def Theta.ofScaled (x : ℝ) : Theta := ⟨x⟩

/-- `M` from a number that is already `4 Nₑ m`. A boundary constructor; see the note above. -/
def BigM.ofScaled (x : ℝ) : BigM := ⟨x⟩

/-- `τ` from a number that is already `t / (2 Nₑ)`. A boundary constructor; see the note
above. -/
def Tau.ofScaled (x : ℝ) : Tau := ⟨x⟩

/-- `ρ` from a number that is already `4 Nₑ r`. A boundary constructor; see the note above. -/
def Rho.ofScaled (x : ℝ) : Rho := ⟨x⟩

@[simp] theorem Theta.value_ofScaled (x : ℝ) : (Theta.ofScaled x).value = x := rfl

@[simp] theorem BigM.value_ofScaled (x : ℝ) : (BigM.ofScaled x).value = x := rfl

@[simp] theorem Tau.value_ofScaled (x : ℝ) : (Tau.ofScaled x).value = x := rfl

@[simp] theorem Rho.value_ofScaled (x : ℝ) : (Rho.ofScaled x).value = x := rfl

/-- `τ` from a time in generations and an effective size, `t / (2 Nₑ)`.

The two here is `ploidy` and not half of `scalingConstant`, because it is a different
two: `2 Nₑ` is the number of gene copies in the population, which is what sets the
coalescent timescale. Writing it as `ploidy * Ne` rather than `scalingConstant * Ne / 2`
is what keeps the two conventions independently adjustable. -/
noncomputable def Tau.ofGenerations (t Ne : ℝ) : Tau := ⟨ratio t (ploidy * Ne)⟩

/-! ### The values, for `simp`

Each of these unwraps one constructor to the arithmetic the corpus already writes by
hand, so a proof stated in the wrapped types reduces to one stated in reals. -/

@[simp] theorem Theta.value_ofRate (Ne μ : ℝ) :
    (Theta.ofRate Ne μ).value = 4 * Ne * μ := by
  unfold Theta.ofRate; rw [scalingConstant_eq]

@[simp] theorem BigM.value_ofRate (Ne m : ℝ) :
    (BigM.ofRate Ne m).value = 4 * Ne * m := by
  unfold BigM.ofRate; rw [scalingConstant_eq]

@[simp] theorem Rho.value_ofRate (Ne r : ℝ) :
    (Rho.ofRate Ne r).value = 4 * Ne * r := by
  unfold Rho.ofRate; rw [scalingConstant_eq]

@[simp] theorem Tau.value_ofGenerations (t Ne : ℝ) :
    (Tau.ofGenerations t Ne).value = t / (2 * Ne) := by
  unfold Tau.ofGenerations ratio ploidy; norm_num

/-! ### The scalings that agree, and the one that does not

`Theta` and `BigM` carry the same constant, so at equal rates they carry equal numbers --
which is precisely why they had to become different types. `Tau` carries a different one. -/

/-- **`θ` and `M` share their constant.** At the same effective size and the same numeric
rate the two scaled quantities are the same number. This is the fact that made them
substitutable as reals, and stating it here is what makes the type distinction visibly
necessary rather than fussy: nothing about the VALUES separates them, so only the types
can. -/
theorem theta_bigM_share_constant (Ne x : ℝ) :
    (Theta.ofRate Ne x).value = (BigM.ofRate Ne x).value := by
  simp

/-- **`ρ` shares it too.** Three of the four scalings are the same arithmetic on different
quantities. -/
theorem rho_bigM_share_constant (Ne x : ℝ) :
    (Rho.ofRate Ne x).value = (BigM.ofRate Ne x).value := by
  simp

/-- **`τ` does not.** Scaled time carries `ploidy · Nₑ` in a DENOMINATOR where the three
rate scalings carry `2 · ploidy · Nₑ` in a numerator, so `Tau` is not merely a fourth name
for the same arithmetic. At `Nₑ = 1` and argument `1` the rates give `4` and the time
gives `1/2`. -/
theorem tau_not_a_rate_scaling :
    (Tau.ofGenerations 1 1).value ≠ (Theta.ofRate 1 1).value := by
  simp; norm_num

/-! ### The deme correction is not part of the migration scaling

The two silent falsifications this file exists to prevent were both a deme-count
correction applied to a scaled migration rate, or not applied when it should have been.
The correction is `d/(d-1)` -- `Core.islandDemeCorrection`, defined in `Core/Fst.lean`
where the equilibrium that uses it lives. What belongs HERE is the size of the factor,
because that is what a reader needs in order to see that the distinction is load-bearing.

These are the two values the ledger measured against. -/

/-- **At two demes the correction is a factor of two**, and this is the factor
`simcov/battery_bulk38.py` measured: the body `1/(1 + θ + M)` was rejected at 3.30 sems
and 57% relative, and `1/(1 + θ + 2M)` matches at 1.10. The free-looking `2` in the
two-deme equilibrium is this number and not a convention. -/
theorem demeCorrection_at_two : ratio 2 (2 - 1) = (2 : ℝ) := by
  unfold ratio; norm_num

/-- **At twenty demes it is `20/19`**, a 5.3% correction -- and
`simcov/battery_falsrepair_c2.py` resolves it: the many-deme limit, which drops the
correction entirely, misses at 3.92 sems and 13% relative, where the finite-deme form
carrying this factor matches at 2.47.

Stated next to `demeCorrection_at_two` because together they are the argument for the
type. A 5.3% correction is small enough that a reader will assume it is absorbed into the
rate, and a 100% correction is large enough that a reader will assume it is not a
correction at all. Both readings were made, and both were wrong. -/
theorem demeCorrection_at_twenty : ratio 20 (20 - 1) = (20 : ℝ) / 19 := by
  unfold ratio; norm_num

/-- **The correction does not tend to one from below, and it never reaches it.**
`d/(d-1) > 1` at every deme count above one, so the many-deme limit is not a conservative
approximation to the finite-deme form -- it is an underestimate of the homogenising flow,
in the same direction at every `d`, which is why a design that only looks at large `d`
sees a bias rather than noise. This is the shape of the `falsrepair_c2` finding. -/
theorem demeCorrection_gt_one (d : ℝ) (hd : 1 < d) : 1 < ratio d (d - 1) := by
  unfold ratio
  rw [lt_div_iff₀ (by linarith)]
  linarith

end Descent.Core
