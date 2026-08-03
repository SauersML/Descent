/-
Copyright (c) 2026 Sauers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sauers
-/
import Calibrator.Probability
import Calibrator.PortabilityDrift
import Calibrator.PopulationGeneticsFoundations
import Calibrator.OpenQuestions
import Calibrator.LDDecayTheory

namespace Calibrator

open MeasureTheory

/-!
# Demographic History Models and PGS Portability

Formalizes how demographic histories (migration, admixture, bottlenecks,
expansion) affect PGS portability through their effects on F_ST and LD.

Provenance: derived here, not imported. Wang et al. (2026), Nature Communications 17:942,
substantiates nothing below. It is an empirical study of the polygenic-score portability
gap and does not treat island, admixture or bottleneck demographic models. Sources for
individual results, where they exist, are cited at those results.
-/


section IslandModel

/-! Island model equilibrium F_ST: `1 / (1 + 4·Ne·m)`.

    Empirical status: CONDITIONALLY VALID. A simulation check was attempted and was
    invalid, because the migration parameter was supplied per pair of demes, so
    total immigration scaled with the number of demes rather than being held
    fixed. The result of that run says nothing about this formula in either
    direction and must not be cited as support.

    Regime: this is the infinite-island limit. Simulation puts it within 2% at
    40 demes, but +17% at 10, +31% at 5 and +95% at 2. The two-deme case is
    in the infinite-island limit the two-ancestry comparison this development is about, so the law
    is off by roughly twofold in its primary application. The finite-deme
    correction `1/(1 + 4 Nₑ m (d/(d-1))²)` repairs the 5-to-10 deme range and
    overshoots at `d = 2` by −40%. No copy of this formula documented the
    assumption, and there are four of them in four files.

    Empirical status: CONDITIONALLY VALID. Accurate in the limit it was derived
    for; frequently violated in use. Neither validated nor falsified.

The theorems below are stated about `fstMigrationDriftEquilibrium` from
`Calibrator.PopulationGeneticsFoundations`, which this file imports. Do not restate
`1/(1 + 4 Nₑ m)` here; the regime caveats above belong to that one definition. -/

/-- More migration → lower equilibrium F_ST. -/
theorem more_migration_lower_fst (Ne m₁ m₂ : ℝ)
    (hNe : 0 < Ne) (hm₁ : 0 < m₁) (hm₂ : 0 < m₂)
    (h_more : m₁ < m₂) :
    fstMigrationDriftEquilibrium Ne m₂ < fstMigrationDriftEquilibrium Ne m₁ := by
  unfold fstMigrationDriftEquilibrium
  apply div_lt_div_of_pos_left one_pos (by positivity) (by nlinarith)

/-! The island-model `F_ST` has one definition, `fstMigrationDriftEquilibrium`. A second
spelling in this module would need its own theorem tying it to that one, which is a
reason not to add it.

The constant is derived, not stipulated. `PortabilityDrift` defines a one-generation
migration-drift map, and `fstMigrationDriftEquilibrium_isFixedPoint` proves the constant is
a fixed point of that map. Without such a theorem the constant would rate only "unverified
but probably true". -/

end IslandModel


section SteppingStone

/-- **The hyperbolic stepping-stone `F_ST`, `d/(d + 4·Ne·m·σ²)` — VERIFIED by simulation.**

    The corpus decided this form against a deleted exponential rival by *derivation*, not
    measurement. Direct two-lineage stepping-stone simulation (circle `D = 64`, `Ne = 25`,
    `m = 0.2`, `σ² = 1`; lineages walk and coalesce with probability `1/(2Ne)` when
    co-located; `F_ST = 1 - T_within/T_between`) now confirms it independently:

    * in its own stated `d ≪ D` regime, RMS relative error **`0.058`**;
    * the best-fitted exponential `1 - exp(-d/L)`, with `L` fitted **freely to the
      measurement**, gives `0.103` — `1.8×` worse in the corpus form's own regime. The
      deletion of `continuousSteppingStoneFst` is corroborated by measurement, not only by
      derivation.

    **A better form exists that the corpus does not carry.** Replacing `d` by `d(D-d)/D` — the
    same coalescent derivation without the `d ≪ D` truncation — drops the RMS error across the
    whole range `d ≤ D/2` from `0.172` to **`0.061`**, removing essentially all of the
    far-field error. Per-`d` relative error of the current form runs `-0.10, -0.02, -0.01,
    +0.05, +0.18, +0.36` at `d = 1, 2, 4, 8, 16, 32`; the untruncated form stays flat.

    **The two compensating omissions this file documents are confirmed quantitatively.**
    Measured `T_within = 3136.9 = 2·D·Ne`, not the per-deme `2·Ne = 50` that `coalFst` is
    handed — a factor of `D = 64`. It cancels against the `(D-d) ≈ D` dropped from the meeting
    time, which is exactly why this definition is right anyway.

    Empirical status: **VALIDATED in its stated regime** (`proofs/validation/empirical/coalescent_diff/`),
    with the untruncated `d(D-d)/D` form recorded as the available improvement. -/
noncomputable def demoSteppingStoneFst (d Ne m σ_sq : ℝ) : ℝ :=
  d / (d + 4 * Ne * m * σ_sq)

/-- **The functional form the previous derivation produced**, retained so that the
indistinguishability recorded in the note above can be stated rather than asserted.

    Empirical status: UNTESTED. -/
noncomputable def steppingStoneFstQuadratic (d Ne m σ_sq : ℝ) : ℝ :=
  d / (d + 4 * Ne * σ_sq ^ 2 * m ^ 2)

/-- **A freely fitted dispersal variance cannot tell the two forms apart.**

The note on `demoSteppingStoneFst` says a refitted `σ²` absorbs the extra power exactly,
and that the fit therefore constrains the product `m·σ²` and nothing else. This is that
claim, proved: at `σ' = √(σ²/m)` the quadratic form takes the same value everywhere, so no
amount of `F_ST` data with `σ²` free can distinguish them.

The consequence is the regime, and it is now enforceable: evidence for the *functional
form* requires `σ²` held at an independently measured dispersal variance while `m` varies.
Evidence gathered with `σ²` free is evidence about `m·σ²`, whatever the fit quality — the
±11% agreement quoted in the note included. -/
theorem demoSteppingStoneFst_indistinguishable_from_quadratic
    (d Ne m σ_sq : ℝ) (hm : 0 < m) (hσ : 0 ≤ σ_sq) :
    demoSteppingStoneFst d Ne m σ_sq
      = steppingStoneFstQuadratic d Ne m (Real.sqrt (σ_sq / m)) := by
  unfold demoSteppingStoneFst steppingStoneFstQuadratic
  have hnn : (0 : ℝ) ≤ σ_sq / m := div_nonneg hσ (le_of_lt hm)
  rw [Real.sq_sqrt hnn]
  have hm' : m ≠ 0 := ne_of_gt hm
  congr 2
  field_simp

/-- Stepping-stone F_ST increases with geographic distance. -/
theorem stepping_stone_fst_increasing (d₁ d₂ Ne m σ_sq : ℝ)
    (hNe : 0 < Ne) (hm : 0 < m) (hσ : 0 < σ_sq)
    (hd₁ : 0 < d₁) (h_farther : d₁ < d₂) :
    demoSteppingStoneFst d₁ Ne m σ_sq < demoSteppingStoneFst d₂ Ne m σ_sq := by
  unfold demoSteppingStoneFst
  have h_C := mul_pos (mul_pos (mul_pos (by norm_num : (0:ℝ) < 4) hNe) hm) hσ
  rw [div_lt_div_iff₀ (by linarith) (by linarith)]
  nlinarith

/-- Stepping-stone F_ST saturates below 1 at any finite distance. -/
theorem stepping_stone_fst_saturates (d Ne m σ_sq : ℝ)
    (hNe : 0 < Ne) (hm : 0 < m) (hσ : 0 < σ_sq)
    (hd : 0 < d) :
    demoSteppingStoneFst d Ne m σ_sq < 1 := by
  unfold demoSteppingStoneFst
  rw [div_lt_one (by nlinarith [mul_pos (mul_pos hNe hm) hσ])]
  linarith [mul_pos (mul_pos (mul_pos (by norm_num : (0:ℝ) < 4) hNe) hm) hσ]

/-! ### Derivation of stepping-stone Fst from the coalescent

In a one-dimensional stepping-stone model with demes of effective size Ne,
migration rate m between adjacent demes, and dispersal variance σ², two
lineages separated by d demes must first meet before they can coalesce. Both
lineages move, so their separation diffuses at twice the single-lineage
coefficient m·σ², and the expected extra time to meet is

  T(d) = d / (2 · σ² · m)

Once in the same deme, coalescence takes an expected 2·Ne generations, so

  Fst(d) = T(d) / (T(d) + 2·Ne)                                     [`coalFst`]
         = [d/(2σ²m)] / ([d/(2σ²m)] + 2·Ne)
         = d / (d + 4·Ne·σ²·m)

which is `demoSteppingStoneFst d Ne m σ_sq`, and is what
`steppingStoneFst_from_coalescence_time` proves. Equivalently
Fst/(1 - Fst) = d/(4·Ne·m·σ²), the standard Malécot/Rousset linear
isolation-by-distance relation in one dimension.

This is a correction. The previous version of this block wrote
T(d) = d/(σ²·m), dropping the factor 2 from the relative diffusion, and then
recovered the factor 4 by passing `2·Ne·σ²·m` as the effective size to
`coalFst` -- which is not an effective size. The result was
d/(d + 4·Ne·σ⁴·m²), a different function of the parameters from the definition
it claimed to derive, and no theorem related the two. The 1/2 belongs in the
meeting time and the effective size argument is Ne.

Cross-check against the island model, which uses the same `T/(T + 2Ne)` map:
two lineages in different demes each migrate at rate m, so they meet at rate
2m, giving T = 1/(2m) and Fst = [1/(2m)]/([1/(2m)] + 2Ne) = 1/(1 + 4·Ne·m),
Wright's result. The factor 4 in both formulas comes from that meeting rate
being 2m (or 2·m·σ²), not from any separate diploid doubling.
-/

/-- **Meeting time at distance d in the stepping-stone model.**
    T(d) = d / (2 · σ² · m), the expected extra time for lineages separated by
    d demes to first occupy the same deme. The 2 is the relative diffusion of
    two independently moving lineages; omitting it was the error in the
    previous derivation (see the block comment above).

    **REGIME: this is a PER-DEME meeting time, not the meeting time.** On a
    finite lattice of `D` demes the expected time for two lineages `d` demes
    apart to first share a deme is `d·(D-d)/(2·σ²·m)`. This body omits the
    factor `(D-d)` entirely, and the omission is not small: at `d = 1`,
    `D = 256` this expression gives `5.0` where the measured meeting time is
    `1344.2`. Read as a standalone number of generations it is wrong by that
    factor. `steppingStoneMeetingTimeOnLattice` states the lattice quantity and
    `steppingStoneMeetingTime_eq_scaled` proves the exact relation between
    them, so the missing factor is now visible rather than implicit.

    **Why no consumer-level check could have caught this, which is the reason
    it survived.** The only thing this feeds is `coalFst _ Ne`, and `coalFst`
    is handed the PER-DEME size `Ne` rather than the metapopulation size
    `D·Ne`. The lattice size therefore cancels between the two arguments, and
    `demoSteppingStoneFst` comes out right to 4.4% despite the meeting time
    being off by `(D-d)`. Two compensating omissions in a ratio look exactly
    like a correct ratio from outside. Anything that consumes this value on its
    own, or pairs it with a metapopulation-scale `Ne`, will be wrong by
    `(D-d)`; that pairing is a load-bearing convention and not an incidental
    choice of argument.

    **This is a diffusion timescale, not a coalescence time.** As the note above
    records, it is MEASURED off by exactly `(D-d)` as a standalone meeting time, and it
    yields a correct `demoSteppingStoneFst` only because that error cancels against a
    per-deme `Nₑ`.

    Empirical status: MEASURED and off by exactly `(D-d)` as a standalone
    meeting time. Its consequence `demoSteppingStoneFst` is CONDITIONALLY
    VALID -- RMS relative error 0.044 with σ² SET rather than fitted, against
    0.622 for a quadratic, 0.335 for a linear and 0.163 for a freely fitted
    exponential form. Note that this is the σ²-held-fixed comparison the
    docstring on `demoSteppingStoneFst` records as not yet done; it has now
    been done and the derived form wins. -/
noncomputable def steppingStoneDiffusionTimescale (d σ_sq m : ℝ) : ℝ :=
  d / (2 * σ_sq * m)

/-- **Expected meeting time on a lattice of `D` demes**, `d·(D-d)/(2·σ²·m)`:
    the quantity `steppingStoneDiffusionTimescale` is a per-deme rescaling of.
    Stated so that the corpus contains the lattice-level time under a name,
    rather than only the rescaled one under a name that does not say it is
    rescaled.

    Denotes: `d` is the lattice separation between the two sampled demes and
    `demeCount` is `D`, the total number of demes, with `0 ≤ d ≤ demeCount`. The
    two are not interchangeable and the formula is not symmetric in them —
    swapping them flips the sign whenever `d < demeCount`, as the guard below
    measures. -/
noncomputable def steppingStoneMeetingTimeOnLattice
    (d demeCount σ_sq m : ℝ) : ℝ :=
  d * (demeCount - d) / (2 * σ_sq * m)

/-- **The guard against the argument swap.**

    A meeting time is nonnegative on the admissible range `0 ≤ d ≤ D`. The omission of such a
    fact has teeth here, because the `d`/`D` arguments differ
    only in case, and a swap **always flips the sign** when `d < D`, so it returns a *negative
    expected time*. In exact rationals at `D = 256`: `d = 1` gives `1275` correct against
    `-326400` swapped, `d = 8` gives `9920` against `-317440`, `d = 128` gives `81920` against
    `-163840`. Nothing in the corpus caught that, because nothing asserted the sign.

    Verified numerically at `D = 64`: measured over predicted is `1.026, 1.027, 1.006, 1.004`
    at `d = 4, 8, 16, 32`.

    **A worse collision remains, and no theorem can guard it.** `σ_sq` and `m` enter only
    through the product `2·σ_sq·m`, so a `σ_sq ↔ m` swap is *exactly invisible* — no test,
    simulation or theorem can detect it — and the three siblings in this file order them
    inconsistently: `demoSteppingStoneFst (d Ne m σ_sq)`, `steppingStoneDiffusionTimescale
    (d σ_sq m)`, and this one `(d D σ_sq m)`. `demoSteppingStoneFst` is symmetric in the two
    as well. That hazard is documentation-only by construction. -/
theorem steppingStoneMeetingTimeOnLattice_nonneg (d demeCount σ_sq m : ℝ)
    (hd : 0 ≤ d) (hdD : d ≤ demeCount) (hσ : 0 < σ_sq) (hm : 0 < m) :
    0 ≤ steppingStoneMeetingTimeOnLattice d demeCount σ_sq m := by
  unfold steppingStoneMeetingTimeOnLattice
  have hden : 0 < 2 * σ_sq * m := by positivity
  apply div_nonneg _ (le_of_lt hden)
  exact mul_nonneg hd (by linarith)

/-- **The exact factor between the two**, which is `(D - d)` and nothing else.
    Proving it as an equation is what stops the per-deme convention from being
    reintroduced silently: any future body for either one that does not differ
    by exactly this factor stops compiling. -/
theorem steppingStoneMeetingTime_eq_scaled (d demeCount σ_sq m : ℝ) :
    steppingStoneMeetingTimeOnLattice d demeCount σ_sq m
      = (demeCount - d) * steppingStoneDiffusionTimescale d σ_sq m := by
  unfold steppingStoneMeetingTimeOnLattice steppingStoneDiffusionTimescale
  ring

/-- **The two agree only when `D - d = 1`**, i.e. essentially never for a
    lattice worth modelling. Stated as the contrapositive of the regime: if a
    reader takes `steppingStoneDiffusionTimescale` for the meeting time, this is
    the assumption they have made without writing it down. -/
theorem steppingStoneMeetingTime_eq_perDeme_iff (d demeCount σ_sq m : ℝ)
    (hd : 0 < d) (hσ : 0 < σ_sq) (hm : 0 < m) :
    steppingStoneMeetingTimeOnLattice d demeCount σ_sq m
      = steppingStoneDiffusionTimescale d σ_sq m ↔ demeCount - d = 1 := by
  rw [steppingStoneMeetingTime_eq_scaled]
  constructor
  · intro h
    have hpos : 0 < steppingStoneDiffusionTimescale d σ_sq m := by
      unfold steppingStoneDiffusionTimescale
      apply div_pos hd; have := mul_pos hσ hm; linarith
    have := mul_right_cancel₀ (ne_of_gt hpos) (by linarith :
      (demeCount - d) * steppingStoneDiffusionTimescale d σ_sq m =
        1 * steppingStoneDiffusionTimescale d σ_sq m)
    linarith
  · intro h; rw [h, one_mul]

/-! **Fst from coalescence time ratio**: `Fst = T/(T + 2Ne)`. This is `coalFst` from
`Calibrator.PopulationGeneticsFoundations`; use it rather than restating it here. -/

/-- **Derivation, and the theorem that pins the definition.**
    With T(d) = d/(2·σ²·m) and effective size Ne:

      Fst = T/(T + 2·Ne) = [d/(2σ²m)] / ([d/(2σ²m)] + 2·Ne)

    Multiplying numerator and denominator by 2·σ²·m:

      = d / (d + 4·Ne·σ²·m)

    which is exactly `demoSteppingStoneFst d Ne m σ_sq`. Stating the conclusion
    as an equation between the derivation and the definition -- rather than as
    a free-standing closed form, which lets the two disagree -- means a
    replacement body for either one stops typechecking.

    A conclusion of `d / (d + 4·Ne·σ⁴·m²)` from `coalFst _ (2·Ne·σ²·m)` feeds a
    non-effective-size into the effective-size slot and compensates for a
    missing 1/2 in the meeting time. That is a different function from the
    definition, and no theorem equates them. -/
theorem steppingStoneFst_from_coalescence_time (d Ne m σ_sq : ℝ)
    (hd : 0 < d) (hNe : 0 < Ne) (hm : 0 < m) (hσ : 0 < σ_sq) :
    coalFst (steppingStoneDiffusionTimescale d σ_sq m) Ne =
      demoSteppingStoneFst d Ne m σ_sq := by
  unfold coalFst steppingStoneDiffusionTimescale demoSteppingStoneFst
  have hσm : (0 : ℝ) < 2 * σ_sq * m := by
    have h := mul_pos hσ hm; linarith
  have hσm' : (2 : ℝ) * σ_sq * m ≠ 0 := ne_of_gt hσm
  have hT : (0 : ℝ) < d / (2 * σ_sq * m) := div_pos hd hσm
  have hTden : d / (2 * σ_sq * m) + 2 * Ne ≠ 0 :=
    ne_of_gt (by linarith)
  have hden : d + 4 * Ne * m * σ_sq ≠ 0 := by
    have h4 : (0 : ℝ) < 4 * Ne * m * σ_sq :=
      mul_pos (mul_pos (mul_pos (by norm_num : (0:ℝ) < 4) hNe) hm) hσ
    exact ne_of_gt (by linarith)
  field_simp
  ring


/-- **The meeting time inherits the indistinguishability of the `F_ST` it produces.**

`steppingStoneDiffusionTimescale` is the only route by which `demoSteppingStoneFst` acquires
its dispersal variance, so the freedom that makes the `F_ST` unidentifiable is freedom in
this quantity. Stated so the meeting time carries the regime rather than borrowing it
silently from a theorem three declarations away: a refitted `σ²` changes the meeting time
and leaves the observable `F_ST` fixed, which is what it means for the data to constrain
`m·σ²` and not the dispersal variance itself. -/
theorem steppingStoneCoalescenceTime_indistinguishable_through_coalFst
    (d Ne m σ_sq : ℝ) (hd : 0 < d) (hNe : 0 < Ne) (hm : 0 < m) (hσ : 0 < σ_sq) :
    coalFst (steppingStoneDiffusionTimescale d σ_sq m) Ne =
      steppingStoneFstQuadratic d Ne m (Real.sqrt (σ_sq / m)) := by
  rw [steppingStoneFst_from_coalescence_time d Ne m σ_sq hd hNe hm hσ]
  exact demoSteppingStoneFst_indistinguishable_from_quadratic d Ne m σ_sq hm (le_of_lt hσ)

/-- The coalescence time is positive for positive distance and dispersal. -/
theorem steppingStoneCoalescenceTime_pos (d σ_sq m : ℝ)
    (hd : 0 < d) (hσ : 0 < σ_sq) (hm : 0 < m) :
    0 < steppingStoneDiffusionTimescale d σ_sq m := by
  unfold steppingStoneDiffusionTimescale
  positivity

/-- Fst from coalescence time is in (0, 1) for positive parameters. -/
theorem fstFromCoalescenceTime_in_unit (T Ne : ℝ)
    (hT : 0 < T) (hNe : 0 < Ne) :
    0 < coalFst T Ne ∧ coalFst T Ne < 1 := by
  unfold coalFst
  constructor
  · positivity
  · rw [div_lt_one (by linarith)]; linarith

end SteppingStone


section AdmixtureModels

/-- Two-way admixed F_ST: (1-α)² × F_ST(A,B).

    **REGIME: the numerator only.** `F_ST` is a ratio, and the derivation
    below computes the NUMERATOR ratio correctly -- simulation confirms it is
    exactly `(1-α)²`, so the algebra in this file survives intact -- and then
    divides by `p̄(1-p̄)` as though the DENOMINATOR were the same for the
    (admixed, A) pair as for the (A, B) pair. It is not. The admixed population
    has its own mean allele frequency, so its heterozygosity term differs, and
    the measured denominator ratio runs from `0.978` at `α = 0.1` down to
    `0.428` at `α = 0.9`. This body assumes that ratio is `1`.

    The consequence is a one-sided bias, never a wash: measured error
    `-2.2%` to `-19.9%` across `α = 0.1 … 0.9` at `F_ST = 0.222`, and `-6.4%`
    to `-57.2%` at `F_ST = 0.633`. It is always NEGATIVE -- this body
    understates admixed `F_ST` -- and `admixedFst_le_exact` below proves that
    sign rather than leaving it as an observation, since a bias whose direction
    is known is a different object from one that merely happened to be negative
    in the runs performed.

    Second, separate assumption: NO POST-ADMIXTURE DRIFT. With 20 generations
    of drift after the admixture event the error reaches `-82.8%`. Nothing in
    the expression carries a time since admixture, so this is an assumption the
    body cannot even express.

    Empirical status: NUMERATOR VALIDATED (exactly `(1-α)²`), DENOMINATOR
    OMITTED. Use `admixedFstExact` when the heterozygosity ratio is available. -/
noncomputable def admixedFst (α fst_AB : ℝ) : ℝ :=
  (1 - α) ^ 2 * fst_AB

/-- **Two-way admixed F_ST with the heterozygosity ratio carried**, rather than
    assumed to be one:

      `F_ST(adm, A) = (1-α)² · F_ST(A,B) / hetRatio`

    where `hetRatio = p̄_adm(1-p̄_adm) / p̄_AB(1-p̄_AB)` is the ratio of the
    denominator heterozygosity of the (admixed, A) pair to that of the (A, B)
    pair. This is the quantity `admixedFst` computes when that ratio is `1`.

    Empirical status: UNTESTED. -/
noncomputable def admixedFstExact (α fst_AB hetRatio : ℝ) : ℝ :=
  (1 - α) ^ 2 * fst_AB / hetRatio

/-- **The regime, made checkable.** `admixedFst` is exactly the `hetRatio = 1`
    case. A future edit that changes either body without preserving this stops
    compiling. -/
theorem admixedFstExact_at_one (α fst_AB : ℝ) :
    admixedFstExact α fst_AB 1 = admixedFst α fst_AB := by
  unfold admixedFstExact admixedFst
  ring

/-- **The sign of the bias is forced, not observed.** The measured
    heterozygosity ratio is below one at every admixture proportion tested, and
    whenever it is, `admixedFst` understates the true admixed `F_ST`. This is
    why every measured error is negative; it is a property of the omission, not
    a fact about which parameter values happened to be simulated. -/
theorem admixedFst_le_exact (α fst_AB hetRatio : ℝ)
    (hfst : 0 ≤ fst_AB) (hpos : 0 < hetRatio) (hle : hetRatio ≤ 1) :
    admixedFst α fst_AB ≤ admixedFstExact α fst_AB hetRatio := by
  unfold admixedFst admixedFstExact
  rw [le_div_iff₀ hpos]
  nlinarith [sq_nonneg (1 - α), mul_nonneg (sq_nonneg (1 - α)) hfst]

/-- Admixed F_ST < parent F_ST for any admixture proportion α ∈ (0,1). -/
theorem admixed_fst_smaller (α fst_AB : ℝ)
    (hα : 0 < α) (hα1 : α < 1) (h_fst : 0 < fst_AB) :
    admixedFst α fst_AB < fst_AB := by
  unfold admixedFst
  have h1 : (1 - α) ^ 2 < 1 := by
    apply (sq_lt_one_iff_abs_lt_one _).mpr
    rw [abs_of_nonneg (by linarith)]; linarith
  calc (1 - α) ^ 2 * fst_AB < 1 * fst_AB := mul_lt_mul_of_pos_right h1 h_fst
    _ = fst_AB := one_mul _

/-- **PGS trained in parent population has intermediate portability to admixed.**
    Better than to the other parent, worse than to itself.
    Model: R² to admixed = α · R²(A→A) + (1-α) · R²(A→B) for admixture
    proportion α from population A. Since R²(A→B) < R²(A→A) and 0 < α < 1,
    the weighted average is strictly between the two parent values. -/
theorem convexCombination_strictly_between
    (r2_AA r2_AB α : ℝ)
    (h_AA_pos : 0 < r2_AA)
    (h_AB_nn : 0 ≤ r2_AB)
    (h_gap : r2_AB < r2_AA)
    (hα : 0 < α) (hα1 : α < 1) :
    r2_AB < α * r2_AA + (1 - α) * r2_AB ∧
      α * r2_AA + (1 - α) * r2_AB < r2_AA := by
  constructor
  · -- r2_AB = 0 · r2_AA + 1 · r2_AB < α · r2_AA + (1-α) · r2_AB
    nlinarith
  · -- α · r2_AA + (1-α) · r2_AB < α · r2_AA + (1-α) · r2_AA = r2_AA
    nlinarith

/-- Optimal admixed PGS (convex combination) is between the two parent values. -/
theorem min_le_convexCombination_le_max
    (pgs_A pgs_B α : ℝ)
    (hα : 0 ≤ α) (hα1 : α ≤ 1) :
    min pgs_A pgs_B ≤ α * pgs_A + (1 - α) * pgs_B ∧
      α * pgs_A + (1 - α) * pgs_B ≤ max pgs_A pgs_B := by
  constructor
  · by_cases h : pgs_A ≤ pgs_B
    · simp [min_eq_left h]; nlinarith
    · push_neg at h; simp [min_eq_right (le_of_lt h)]; nlinarith
  · by_cases h : pgs_A ≤ pgs_B
    · simp [max_eq_right h]; nlinarith
    · push_neg at h; simp [max_eq_left (le_of_lt h)]; nlinarith

/-! ### Derivation of admixed Fst from allele frequency mixing

Consider an admixed population formed as a mixture of population A (proportion α)
and population B (proportion 1-α). The admixed allele frequency is:

  p_adm = α · p_A + (1-α) · p_B

The Fst between the admixed population and its source population A is
defined via the variance of allele frequency differences:

  Fst(adm, A) = Var(p_adm - p_A) / [p̄(1-p̄)]

where p̄ is the mean allele frequency. Computing the numerator:

  p_adm - p_A = α · p_A + (1-α) · p_B - p_A
              = (1-α) · (p_B - p_A)

Therefore:

  Var(p_adm - p_A) = (1-α)² · Var(p_B - p_A)
                    = (1-α)² · Fst(A, B) · p̄(1-p̄)

Dividing by p̄(1-p̄):

  Fst(adm, A) = (1-α)² · Fst(A, B)

This is `admixedFst α fst_AB`.
-/

/-- **Allele frequency in the admixed population.**
    p_adm = α · p_A + (1-α) · p_B.

    Empirical status: UNTESTED. -/
noncomputable def admixedAlleleFreq (α p_A p_B : ℝ) : ℝ :=
  α * p_A + (1 - α) * p_B

/-- **Key algebraic identity**: the difference between admixed and source A
    allele frequencies is (1-α) times the parental difference.
    This is the core of the (1-α)² derivation. -/
theorem admixed_freq_diff (α p_A p_B : ℝ) :
    admixedAlleleFreq α p_A p_B - p_A = (1 - α) * (p_B - p_A) := by
  unfold admixedAlleleFreq
  ring

/-- **Derivation**: If variance of allele frequency differences satisfies
    Var(p_adm - p_A) = (1-α)² · Var(p_B - p_A), and Fst(A,B) is defined as
    Var(p_B - p_A) / [p̄(1-p̄)], then Fst(adm, A) = (1-α)² · Fst(A,B).

    We express this as: for any set of loci, the mean squared frequency
    difference between admixed and source is (1-α)² times the mean squared
    frequency difference between parents. -/
theorem admixedFst_from_freq_variance (α : ℝ) (var_parent pbar_term : ℝ) :
    (1 - α) ^ 2 * var_parent / pbar_term =
      admixedFst α (var_parent / pbar_term) := by
  unfold admixedFst
  ring

/-- **Per-locus derivation**: at a single locus with parental frequencies p_A and p_B,
    the squared frequency difference between admixed and source is (1-α)² times the
    squared parental difference. Summing over loci gives the Fst relationship. -/
theorem admixed_squared_diff (α p_A p_B : ℝ) :
    (admixedAlleleFreq α p_A p_B - p_A) ^ 2 = (1 - α) ^ 2 * (p_B - p_A) ^ 2 := by
  rw [admixed_freq_diff]
  ring

end AdmixtureModels


/-!
### Recent expansion and the singleton spectrum

Removed.  This section defined `singletonProportion N₀ N₁ = 1 - log N₀ / log N₁`
and proved monotonicity and endpoint results about it.  Coalescent simulation
falsifies the identification decisively: the formula does not track the
singleton proportion under exponential growth.  The theorems were correct about
the formula and wrong about the quantity it was named for, which is the failure
this development is trying to eliminate, so they are deleted rather than
weakened.
-/


section ArchaicIntrogression

/-- **Cumulative introgressed variants.**
    Given an ancestral variant mass `N₀` and a constant introgression rate `r`,
    the cumulative introgressed contribution after time `t` is
    `N₀ * (1 - exp(-r * t))`. -/
noncomputable def introgressionVariants (N₀ introgressionRate t : ℝ) : ℝ :=
  N₀ * (1 - Real.exp (-introgressionRate * t))

/-- **Differential introgression creates population-specific variants.**
    When one population has a higher archaic introgression fraction than
    another, the resulting population-specific variants contribute to
    portability loss.

    Worked example: European/Asian ~2% Neanderthal, Melanesian ~2%
    Neanderthal + ~3-5% Denisovan, African ~0-0.3% archaic. -/
theorem introgression_creates_population_specific_variants
    (N₀ t rHigh rLow : ℝ)
    (hN : 0 < N₀)
    (ht : 0 < t)
    (h_diff : rLow < rHigh) :
    introgressionVariants N₀ rLow t < introgressionVariants N₀ rHigh t := by
  unfold introgressionVariants
  have h_exp_arg : -rHigh * t < -rLow * t := by
    nlinarith
  have h_exp_lt : Real.exp (-rHigh * t) < Real.exp (-rLow * t) := by
    exact Real.exp_lt_exp.mpr h_exp_arg
  have h_inner : 1 - Real.exp (-rLow * t) < 1 - Real.exp (-rHigh * t) := by
    linarith
  exact mul_lt_mul_of_pos_left h_inner hN

/-- **Introgression fraction of heritability is bounded.**
    When introgressed heritability is at most a fraction δ of total
    heritability, the introgression share is bounded by δ.

    Worked example: For most traits, introgression contributes < 1%
    of total heritability. -/
theorem introgression_gap_bounded
    (h2_total h2_intro δ : ℝ)
    (h_total : 0 < h2_total)
    (h_small : h2_intro ≤ δ * h2_total) :
    h2_intro / h2_total ≤ δ := by
  exact (div_le_iff₀ h_total).mpr h_small

end ArchaicIntrogression


section FounderEffects

/-- **Within-population heterozygosity loss after `t` generations in a founding
    population of size `k`**: `1 - (1 - 1/(2k))^t`.

    **This is NOT between-population `F_ST`, and the gap is not a convention fork or a
    factor of two -- they are different quantities with different limits.** At
    `Nₑ = 1000`, `t = 4000` this expression's retention factor gives `0.135` against a
    measured `1.025 ± 0.020`, and the `F_ST` its cluster reports is approximately zero
    where the measurable between-population `F_ST` at that design point is `0.50`.
    Reading this as a differentiation measure is not slightly off; it is the wrong axis.

    **For between-population `F_ST` after a split use
    `PopulationGeneticsFoundations.coalFst t Ne = t / (t + 2 Nₑ)`**, which coalescent
    simulation in branch mode -- which removes mutational noise analytically -- finds
    unbiased across the tested grid.

    `heterozygosityLossFromDrift` and `heterozygosityLossDerived` in
    `PopulationGeneticsFoundations` are this same quantity.

    Regime: closed population, no mutation. `founderHeterozygosityLoss_eq_derived`
    below pins it to the `θ = 0` slice of the general transient, which is what makes
    the no-mutation premise explicit rather than implied.

    Empirical status: correct for what it says; FALSIFIED as an `F_ST`. -/
noncomputable def founderHeterozygosityLoss (k : ℕ) (t : ℕ) : ℝ :=
  1 - (1 - 1 / (2 * (k : ℝ))) ^ t

/-- Smaller founding population → larger heterozygosity loss (more drift). -/
theorem smaller_founder_larger_heterozygosity_loss
    (k₁ k₂ : ℕ) (t : ℕ)
    (hk₁ : 2 < k₁) (hk₂ : 2 < k₂)
    (h_smaller : k₂ < k₁) (ht : 0 < t) :
    founderHeterozygosityLoss k₁ t < founderHeterozygosityLoss k₂ t := by
  unfold founderHeterozygosityLoss
  have h_base : 1 - 1 / (2 * (k₂ : ℝ)) < 1 - 1 / (2 * (k₁ : ℝ)) := by
    rw [sub_lt_sub_iff_left]
    apply div_lt_div_of_pos_left one_pos
    · exact Nat.cast_pos.mpr (by omega) |> (fun h ↦ mul_pos (by norm_num : (0:ℝ) < 2) h)
    · exact mul_lt_mul_of_pos_left (Nat.cast_lt.mpr h_smaller) (by norm_num : (0:ℝ) < 2)
  have h_nn : 0 ≤ 1 - 1 / (2 * (k₂ : ℝ)) := by
    rw [sub_nonneg, div_le_one (by positivity)]
    have : (2 : ℝ) ≤ k₂ := by exact Nat.ofNat_le_cast.mpr (by omega)
    linarith
  linarith [pow_lt_pow_left₀ h_base h_nn (by omega : t ≠ 0)]

/-- **Connection to derived formula**: `founderHeterozygosityLoss` equals the pure-drift
    specialization of `fstMutationDriftTransientDiscrete` from
    `PopulationGeneticsFoundations.lean`.

    When θ = 0 (no mutation), the transient Fst formula reduces to:
    - `fstMutationDriftEquilibrium 0 = 1/(1+0) = 1`
    - `hetDecayFactor k 0 = (1 - 1/(2k)) · (1 - 0) = 1 - 1/(2k)`
    - `fstMutationDriftTransientDiscrete 0 k t = 1 · (1 - (1 - 1/(2k))^t)`
                                                = 1 - (1 - 1/(2k))^t

    This is exactly `founderHeterozygosityLoss k t`, confirming that the founder effect
    formula is the pure-drift case of the general heterozygosity recurrence
    derived in `PopulationGeneticsFoundations`. -/
theorem founderHeterozygosityLoss_eq_derived (k : ℕ) (t : ℕ) :
    founderHeterozygosityLoss k t = fstMutationDriftTransientDiscrete 0 (k : ℝ) t := by
  unfold founderHeterozygosityLoss fstMutationDriftTransientDiscrete fstMutationDriftEquilibrium hetDecayFactor hetDecayFromScaled
  simp

end FounderEffects


/-!
## Heterozygosity Loss Under Variable Population Size

When Ne changes over time, the drift-accumulated loss of within-population
heterozygosity is
  L(T) = 1 - exp(-Σ_{t=0}^{T-1} 1/(2·Ne(t)))
replacing the constant-size form L = 1 - exp(-T/(2·Ne)).

**This is heterozygosity loss, not between-population `F_ST`.** See the note on
`founderHeterozygosityLoss` above for the measurement that separates them, and use
`PopulationGeneticsFoundations.coalFst` if differentiation after a split is wanted.
Note that the constant-size form `1 - exp(-T/(2·Ne))` named above is the same
falsified expression, so neither the constant-size nor the variable-`Nₑ` form is an
`F_ST`.
-/

section VariableNeFst

/-- **Cumulative drift** under variable Ne: Σ 1/(2·Ne(t)).

    Empirical status: UNTESTED. -/
noncomputable def cumulativeDrift {T : ℕ} (Ne : Fin T → ℝ) : ℝ :=
  ∑ i, 1 / (2 * Ne i)

/-- **Within-population heterozygosity loss under variable Nₑ**:
    `1 - exp(-Σ 1/(2·Nₑ(t)))`.

    The continuous-time form of `founderHeterozygosityLoss`; see that docstring for
    the measurement showing this family is **not** between-population `F_ST` (`≈ 0`
    here against a measured `0.50` at `Nₑ = 1000`, `t = 4000`) and for
    `coalFst t Ne = t / (t + 2 Nₑ)`, which is the between-population quantity.

    `validation/popgen_defs/battery2.py` checks this body against
    `truth = 1 - H_t/H_0`, drift-only heterozygosity loss, which is what it computes.

    Empirical status: correct for what it now says; FALSIFIED as an `F_ST`. -/
noncomputable def heterozygosityLossVariableNe {T : ℕ} (Ne : Fin T → ℝ) : ℝ :=
  1 - Real.exp (-(cumulativeDrift Ne))

/-- Heterozygosity loss under variable Nₑ is nonneg when all Nₑ are positive. -/
theorem heterozygosityLossVariableNe_nonneg {T : ℕ} (hT : 0 < T)
    (Ne : Fin T → ℝ) (hNe : ∀ i, 0 < Ne i) :
    0 ≤ heterozygosityLossVariableNe Ne := by
  unfold heterozygosityLossVariableNe
  rw [sub_nonneg, ← Real.exp_zero]
  apply Real.exp_le_exp.mpr
  have hcum_nonneg : 0 ≤ cumulativeDrift Ne := by
    unfold cumulativeDrift
    apply Finset.sum_nonneg
    intro i _
    exact le_of_lt (div_pos one_pos (by linarith [hNe i]))
  simpa using hcum_nonneg

/-- Heterozygosity loss under variable Nₑ is strictly less than 1. -/
theorem heterozygosityLossVariableNe_lt_one {T : ℕ} (Ne : Fin T → ℝ) :
    heterozygosityLossVariableNe Ne < 1 := by
  unfold heterozygosityLossVariableNe
  linarith [Real.exp_pos (-(cumulativeDrift Ne))]

/-- Larger cumulative drift yields higher heterozygosity loss. -/
theorem more_drift_higher_heterozygosity_loss {T : ℕ}
    (Ne₁ Ne₂ : Fin T → ℝ)
    (hNe₁ : ∀ i, 0 < Ne₁ i) (hNe₂ : ∀ i, 0 < Ne₂ i)
    (h_more_drift : cumulativeDrift Ne₁ < cumulativeDrift Ne₂) :
    heterozygosityLossVariableNe Ne₁ < heterozygosityLossVariableNe Ne₂ := by
  unfold heterozygosityLossVariableNe
  -- Need: 1 - exp(-d₁) < 1 - exp(-d₂) ↔ exp(-d₂) < exp(-d₁) ↔ -d₂ < -d₁ ↔ d₁ < d₂ ✓
  have h_exp : Real.exp (-(cumulativeDrift Ne₂)) < Real.exp (-(cumulativeDrift Ne₁)) := by
    apply Real.exp_lt_exp.mpr
    linarith
  linarith

/-- Population with uniformly smaller Ne accumulates more drift. -/
theorem smaller_ne_more_drift {T : ℕ} (hT : 0 < T)
    (Ne₁ Ne₂ : Fin T → ℝ)
    (hNe₁ : ∀ i, 0 < Ne₁ i) (hNe₂ : ∀ i, 0 < Ne₂ i)
    (h_smaller : ∀ i, Ne₂ i < Ne₁ i) :
    cumulativeDrift Ne₁ < cumulativeDrift Ne₂ := by
  unfold cumulativeDrift
  apply Finset.sum_lt_sum
  · intro i _
    exact le_of_lt (div_lt_div_of_pos_left one_pos (by linarith [hNe₂ i]) (by linarith [h_smaller i]))
  · let j : Fin T := ⟨0, hT⟩
    exact ⟨j, Finset.mem_univ j,
      div_lt_div_of_pos_left one_pos (by linarith [hNe₂ j]) (by linarith [h_smaller j])⟩

/-- **`1/(2x)` is decreasing in `x` on the positives.**

    The per-generation term of `cumulativeDrift` above, isolated. Read as
    genetics it says a bottleneck generation contributes more drift than a
    normal-sized one, but that reading needs the per-generation drift to BE
    `1/(2Nₑ)`, which is the definition's business and not this statement's:
    here there are two positive reals and no population. -/
theorem one_div_two_mul_lt_one_div_two_mul_of_lt (x y : ℝ)
    (hx : 0 < x) (hy : 0 < y)
    (hxy : x < y) :
    1 / (2 * y) < 1 / (2 * x) :=
  div_lt_div_of_pos_left one_pos (by linarith) (by linarith)

end VariableNeFst


/-!
## Portability Implications of Demographic History

Populations with different demographic histories have different LD structures
even at the same Fst. This leads to different PGS portability properties:
a bottlenecked population has more long-range LD (from drift during the
bottleneck) compared to a stably-sized population at the same Fst.
-/

section BottleneckExcessLD_Derivation

/-!
## Excess LD from a bottleneck

**Do not derive a bottleneck LD excess from additive drift accounting.** That route --
LD created at rate `1/(2 Ne)` per generation, excess creation rate
`1/(2 Ne_b) - 1/(2 Ne_stable)`, cumulative excess the geometric sum under drift-only
decay -- is internally consistent and gives the wrong function. It carries no
recombination rate, so the level rises without bound toward `1` instead of saturating
at the drift-recombination equilibrium. Simulation puts the same defect at up to
3.3-fold high, and no constant repairs a missing argument.

Any closed form of the shape
`(1 - (1-1/(2 Ne_b))^t_b) - (1 - (1-1/(2 Ne_stable))^t_b)` has that error in its first
term. Use `excessLDAfterBottleneck`, which runs the two-locus recurrence and therefore
carries `c`.

Deleted with it: `excessDriftRate`, `cumulativeExcessLD`, `geom_sum_drift`,
`cumulativeExcessLD_eq_closedForm`, and `derivation_matches_bottleneckExcessLD`.
The last of these deserves its own note. It was stated as

    (1 - a) - (1 - b) = b - a

proved `by ring`, under a docstring claiming it confirmed that the drift
derivation produces the `bottleneckExcessLD` formula. It mentions neither
`cumulativeExcessLD` nor `excessDriftRate`; it is a tautology about two real
numbers and connects nothing. A theorem named "derivation matches" that relates
no two things is worse than no theorem, because its name is read as evidence.

`driftLDCreationRate` is retained below because `Conventions.lean` relates it to
the coalescent time scale, and because it is a correct statement about drift in
isolation. It is not a model of LD.

The replacement lives in `LDDecayTheory.lean`: `driftLDStep` (the Sved
drift-recombination recurrence, which does take `c`), `driftLDEquilibrium` with
`driftLDEquilibrium_isFixedPoint`, and `driftLDTrajectory` with
`driftLDTrajectory_closedForm`. `bottleneckExcessLD` below is now defined as a
trajectory of that process and its closed form is proved, not asserted.
-/

/-- **Drift LD creation rate**: In a population of effective size Ne,
    genetic drift creates new LD at rate 1/(2·Ne) per generation.
    This arises from Cov(Δpᵢ, Δpⱼ) for linked loci under drift.

    This is a creation rate only. Accumulating it without a recombination rate
    is what produced the falsified `bottleneckExcessLD` formula deleted above;
    the honest accumulation is `driftLDStep` in `LDDecayTheory.lean`, in which
    this rate appears multiplied by the non-recombinant fraction `(1-c)²`.

    **Identical twin of `LDDecayTheory.driftRatePerGen`**, which was named
    `ldDecayRatePerGen` until its LD reading was FALSIFIED at up to 201x
    (`proofs/validation/empirical/coalescent_diff/`): `1/(2Ne)` is not the fraction of LD lost per
    generation, because recombination dominates it. The same caution applies to any LD
    reading of this body -- the `LD` in this name is about where the rate is *used*, not
    about what it measures. As a bare drift rate it stands.

    Empirical status: UNTESTED as a drift rate; the LD reading of the shared formula is
    FALSIFIED at the twin.

    Denotes: a per-generation rate. Other definitions share this formula under names from a
    different concept family; the formula does not fix which is meant. -/
noncomputable def driftLDCreationRate (Ne : ℝ) : ℝ :=
  1 / (2 * Ne)

/-- **Cross-check: this is the same per-generation drift rate that
`LDDecayTheory` calls `driftRatePerGen`.** One rate under two names.

The "fraction of LD lost per generation" reading is FALSIFIED — recombination dominates
`1/(2Ne)`, by up to 201x — so this equality ties two names for a drift rate, not two
readings of an LD rate. It is worth keeping precisely because the two
names sit in different concept families and identical magnitudes are where a divergence
goes unnoticed. -/
theorem driftLDCreationRate_eq_driftRatePerGen (Ne : ℝ) :
    driftLDCreationRate Ne = driftRatePerGen Ne := by
  unfold driftLDCreationRate driftRatePerGen; ring

end BottleneckExcessLD_Derivation


section DemographicPortability

/-- **LD mismatch from demographic differences.**
    Two populations can reach the same Fst via different paths:
    one through a bottleneck (high LD) and one through stable drift (lower LD).
    The bottlenecked population has additional drift-generated LD of order
    1/(2·N_b) per bottleneck generation.

    We model: pop A has stable Ne_A, pop B had a bottleneck to Ne_b < Ne_A
    for t_b generations then recovered to Ne_A. Even if their Fst values
    match, pop B has excess LD.

    **Derived from the drift-recombination process** in `LDDecayTheory.lean`:
    a population sitting at the equilibrium LD level for its stable size
    `Ne_stable` is bottlenecked to `Ne_b` for `t_b` generations, and this is how
    far above the stable level it ends up.

    The previous body was
    `(1 - (1-1/(2 Ne_b))^t_b) - (1 - (1-1/(2 Ne_stable))^t_b)`, whose first term
    is `bottleneckLDAmplification` verbatim -- the formula deleted from
    `LDDecayTheory.lean` for taking no recombination rate and therefore rising
    to `1` with time rather than saturating at the drift-recombination
    equilibrium (simulation: up to 3.3-fold overstatement). The same objection
    applied here unchanged, so this is now a trajectory of a process that does
    take `c`, and `bottleneckExcessLD_eq_closedForm` proves the closed form
    rather than asserting it.

    Empirical status: UNTESTED. The 3.3-fold falsification of the predecessor is
    not evidence about this body, and neither is anything else: no simulation
    has been run against the two-equilibrium-gap amplitude this predicts. What
    is established is structural -- the level is bounded by the gap between two
    equilibria, each of which is bounded by `1`
    (`driftLDEquilibrium_le_one`). -/
noncomputable def bottleneckExcessLD (Ne_b Ne_stable c : ℝ) (t_b : ℕ) : ℝ :=
  driftLDTrajectory Ne_b c (driftLDEquilibrium Ne_stable c) t_b -
    driftLDEquilibrium Ne_stable c

/-- **Closed form of the bottleneck excess**, proved from the recurrence: the
    gap between the two equilibria, approached geometrically over the
    bottleneck. This is the theorem the deleted `derivation_matches_bottleneckExcessLD`
    was named for and did not state. -/
theorem bottleneckExcessLD_eq_closedForm (Ne_b Ne_stable c : ℝ) (t_b : ℕ)
    (hNb : 1 ≤ Ne_b) (hc : 0 ≤ c) (hc1 : c ≤ 1) :
    bottleneckExcessLD Ne_b Ne_stable c t_b =
      (driftLDEquilibrium Ne_b c - driftLDEquilibrium Ne_stable c) *
        (1 - driftLDRetention Ne_b c ^ t_b) := by
  unfold bottleneckExcessLD
  rw [driftLDTrajectory_closedForm Ne_b c _ hNb hc hc1 t_b]
  ring

/-- **One quantity, one definition**: the bottleneck excess is the zero-recovery
    case of `excessLDAfterBottleneck` in `LDDecayTheory.lean`. Stated so the two
    copies of this construction cannot drift apart the way the two copies of the
    deleted formula did. -/
theorem bottleneckExcessLD_eq_excessLDAfterBottleneck
    (Ne_b Ne_stable c : ℝ) (t_b : ℕ) :
    bottleneckExcessLD Ne_b Ne_stable c t_b =
      excessLDAfterBottleneck Ne_b Ne_stable c t_b 0 := by
  unfold bottleneckExcessLD excessLDAfterBottleneck
  rw [driftLDTrajectory_zero]

/-- The bottlenecked population has strictly more LD than the stable population
    over the same number of generations when bottleneck Ne is smaller.

    The recombination rate must be strictly between 0 and 1: at `c = 0` both
    populations equilibrate at `1` and the excess is zero, and at `c = 1` both
    equilibrate at `0`. The old statement, which had no `c`, reported a strictly
    positive excess in both of those regimes. -/
theorem bottleneck_excess_ld_pos (Ne_b Ne_stable c : ℝ) (t_b : ℕ)
    (hNb : 1 ≤ Ne_b) (h_bottle : Ne_b < Ne_stable)
    (hc : 0 < c) (hc1 : c < 1)
    (ht : 0 < t_b) :
    0 < bottleneckExcessLD Ne_b Ne_stable c t_b := by
  have hc0 : (0 : ℝ) ≤ c := le_of_lt hc
  have hc1' : c ≤ 1 := le_of_lt hc1
  rw [bottleneckExcessLD_eq_closedForm Ne_b Ne_stable c t_b hNb hc0 hc1']
  have h_gap : 0 < driftLDEquilibrium Ne_b c - driftLDEquilibrium Ne_stable c := by
    have := driftLDEquilibrium_strictAnti Ne_b Ne_stable c hNb h_bottle hc hc1
    linarith
  have hLb := driftLDRetention_mem_unit Ne_b c hNb hc0 hc1'
  have hLb_lt : driftLDRetention Ne_b c < 1 :=
    driftLDRetention_lt_one Ne_b c hNb hc hc1'
  have h_amp : 0 < 1 - driftLDRetention Ne_b c ^ t_b := by
    have := pow_lt_one₀ hLb.1 hLb_lt (by omega : t_b ≠ 0)
    linarith
  exact mul_pos h_gap h_amp

/-- **Different demographic histories break the Fst-portability relationship.**
    Derived from `bottleneckExcessLD`: for two source-target pairs with the same Fst,
    the pair where the target went through a bottleneck has worse portability
    because `bottleneckExcessLD > 0` adds additional LD mismatch on top of Fst.
    The total mismatch = Fst-based mismatch + bottleneck excess LD. -/
theorem bottleneck_worsens_portability
    (Ne_b Ne_stable c : ℝ) (t_b : ℕ)
    (hNb : 1 ≤ Ne_b) (h_bottle : Ne_b < Ne_stable)
    (hc : 0 < c) (hc1 : c < 1)
    (ht : 0 < t_b) (fst_mismatch : ℝ) (h_fst_nn : 0 ≤ fst_mismatch) :
    fst_mismatch < fst_mismatch + bottleneckExcessLD Ne_b Ne_stable c t_b := by
  linarith [bottleneck_excess_ld_pos Ne_b Ne_stable c t_b hNb h_bottle hc hc1 ht]

/-- **Portability ratio under bottleneck** is strictly worse than under stable demography.
    Derived: portability ∝ (1 - Fst) for stable populations. For bottlenecked populations,
    portability ∝ (1 - Fst) · (1 - excessLD_correction). Since bottleneckExcessLD > 0,
    the correction factor is < 1, reducing the portability ratio.
    We model: R²_bottleneck = R²_source · ((1-Fst) - excessLD) where
    excessLD = bottleneckExcessLD Ne_b Ne_stable c t_b. -/
theorem bottleneck_reduces_portability_ratio
    (R2_source Ne_b Ne_stable c : ℝ) (t_b : ℕ) (fst : ℝ)
    (hR2 : 0 < R2_source)
    (hNb : 1 ≤ Ne_b) (h_bottle : Ne_b < Ne_stable)
    (hc : 0 < c) (hc1 : c < 1)
    (ht : 0 < t_b)
    (hfst : 0 ≤ fst) (hfst1 : fst < 1) :
    R2_source * ((1 - fst) - bottleneckExcessLD Ne_b Ne_stable c t_b) <
    R2_source * (1 - fst) := by
  apply mul_lt_mul_of_pos_left _ hR2
  linarith [bottleneck_excess_ld_pos Ne_b Ne_stable c t_b hNb h_bottle hc hc1 ht]

/-- Populations that experienced expansion retain more pre-existing LD,
    meaning their LD structure is closer to the source population's LD
    (since both have large modern Ne). We show that if the expanded population
    has LD retention factor closer to the source, the LD distance is smaller.

    Formally: if |ρ_exp - ρ_src| < |ρ_small - ρ_src| where ρ is the LD
    retention, then the PGS accuracy loss (proportional to LD mismatch²)
    is smaller for the expanded population. -/
theorem mul_sq_lt_mul_sq_of_lt_of_nonneg
    (ld_mismatch_exp ld_mismatch_small accuracy_coeff : ℝ)
    (h_coeff_pos : 0 < accuracy_coeff)
    (h_mismatch_exp_nn : 0 ≤ ld_mismatch_exp)
    (h_mismatch_small_nn : 0 ≤ ld_mismatch_small)
    (h_exp_less : ld_mismatch_exp < ld_mismatch_small) :
    accuracy_coeff * ld_mismatch_exp ^ 2 < accuracy_coeff * ld_mismatch_small ^ 2 := by
  apply mul_lt_mul_of_pos_left _ h_coeff_pos
  exact sq_lt_sq' (by linarith) h_exp_less

end DemographicPortability

end Calibrator
