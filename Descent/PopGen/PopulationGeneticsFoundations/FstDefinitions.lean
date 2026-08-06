/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Foundations.TransportIdentities
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Sigmoid
import Mathlib.Data.Matrix.Basic
import Descent.Core.Heterozygosity

assert_below Descent.Spectral Descent.Blindness Descent.Conditionals Descent.Portability
assert_below Descent.Decision Descent.Program

namespace Descent.PopGen

open MeasureTheory

/-!
# `PopulationGeneticsFoundations.FstDefinitions`

Part of the split of `Descent/PopGen/PopulationGeneticsFoundations.lean`, which was 2,740 lines.

This part is the HEAD of the fan. The split first made the parts a CHAIN -- each importing
the one before, in the order the original text ran -- which preserved every resolution the
single file had and charged every part a dependency on everything written above it, used or
not. This part is what the others were resolved against: it declares the definitions they
name and carries the imports they share, and it names no sibling itself.

Where a cut falls inside a section, the section is reopened and reclosed by name. A section
scopes `variable`s and this file declares none at that level, so the reopening is exact.
-/

section FstDefinitions

/-- **Nei's Fst.**
    Fst = (H_T - H_S) / H_T where H_T is total heterozygosity
    and H_S is mean subpopulation heterozygosity.

    Regime: a clean two-population split, no migration, equal sizes; both
    heterozygosities as ratios of averages over segregating sites.

    Empirical status: **MEASURED, and NOT interchangeable with Hudson's
    `F_ST`** (`simcov/battery_bulk25.py`). This body is an identity in `H_T` and
    `H_S`, so comparing it against a transcription of itself decides nothing.
    What a simulation can decide is whether it obeys the split law
    `τ/(1+τ)` that the rest of this corpus writes `F_ST` results in. It does
    not. Over `τ` = 0.1, 0.25, 1, 3 the split law predicts 0.09091, 0.20000,
    0.50000 and 0.75000, while Nei's estimator on the same genotype matrices
    measures 0.05495 ± 0.00453, 0.11904 ± 0.00513, 0.34185 ± 0.00851 and
    0.61182 ± 0.00905 -- FALSIFIED at up to 18.59 sems, low in every cell.

    The control is what makes this a statement about the CONVENTION rather than
    about the simulation: Hudson's estimator, computed from the SAME genotype
    matrices through a separate code path, matches the same split law at 0.03
    sems. One design, one dataset, two estimators, and only one of them follows
    the law. So the oracle is not pinned to either body, and the discrepancy is
    the convention gap and not an artefact.

    The ratio `neiGst / hudsonFst` is not a constant either -- it runs 0.62,
    0.60, 0.68, 0.81 across that sweep -- so no fixed factor converts between
    them and a `1/2` or `1/4` correction is not available. Every `F_ST` result
    in this corpus stated as `τ/(1+τ)`, or derived from it, is a HUDSON result;
    substituting this body into one of them is the factor-of-two-to-four error
    the corpus has already paid for once. -/
noncomputable def neiFst (H_T H_S : ℝ) : Descent.Core.NeiFst :=
  ⟨(H_T - H_S) / H_T⟩

/-- The number inside, so that a proof about this estimator is a proof about `(H_T - H_S)/H_T`
and the wrapper costs a rewrite rather than an argument. -/
@[simp] theorem neiFst_value (H_T H_S : ℝ) :
    (neiFst H_T H_S).value = (H_T - H_S) / H_T := rfl

/-- **This body, typed as a Nei estimate, converts to Hudson by the Möbius map.**

`Core.NeiFst` and `Core.HudsonFst` exist so that a Nei value cannot be passed where a
Hudson one is required, and a guarantee exercised only inside `Core.Fst` protects nothing
outside it.  `neiFst` RETURNS a `Core.NeiFst`, so handing it to something expecting a
Hudson value is a type error rather than a factor-of-two-to-four mistake found later --
which is what the docstring above records this corpus having already paid for once.

The cost is one `.value` at each use, and `neiFst_value` above discharges it in a rewrite,
so the statements below say the same things about the same quotient. -/
theorem neiFst_toHudson (H_T H_S : ℝ) :
    (Descent.Core.hudsonOfNei (neiFst H_T H_S)).value
      = 2 * (neiFst H_T H_S).value / (1 + (neiFst H_T H_S).value) := rfl

/-- **And it differs from its Hudson conversion except at the two degenerate values.**

`Core.hudsonOfNei_eq_iff` says a Nei estimate equals its Hudson conversion only at `0` or
`1`; instantiated here, that is a statement about THIS body. Anywhere a population is
partially differentiated -- every case of interest -- reading this number as a Hudson
`F_ST` reads a different quantity, and the measured ratios (0.62, 0.60, 0.68, 0.81) are
what that difference looks like. -/
theorem neiFst_eq_hudson_iff_degenerate (H_T H_S : ℝ)
    (h : 1 + (neiFst H_T H_S).value ≠ 0) :
    (Descent.Core.hudsonOfNei (neiFst H_T H_S)).value = (neiFst H_T H_S).value
      ↔ (neiFst H_T H_S).value = 0 ∨ (neiFst H_T H_S).value = 1 :=
  Descent.Core.hudsonOfNei_eq_iff _ h

/-- **Nei's `Fst` is a proportion of total heterozygosity, pinned.** This definition carries no
result of its own. Subpopulations holding half the total heterozygosity give `Fst = 1/2`: the
deficit is measured against the total, not against the subpopulation value, and it runs total
minus subpopulation so that structure raises it. -/
theorem neiFst_half_heterozygosity_retained :
    (neiFst 2 1).value = 1 / 2 := by
  norm_num

/-- **Nei's `Fst` at zero total heterozygosity, named.** Two monomorphic populations have no
heterozygosity to partition and `Fst` is undefined, but the divisor is zero and Lean returns `0`
-- reporting perfect genetic identity where the data say nothing at all. The two cases are not
distinguishable downstream. Consumers must require `H_T ≠ 0`. -/
theorem neiFst_monomorphic_is_junk :
    (neiFst 0 0).value = 0 := by
  norm_num

/-- Nei's Fst is in [0, 1] when H_T > 0 and H_S ≤ H_T. -/
theorem nei_fst_in_unit (H_T H_S : ℝ)
    (h_HT : 0 < H_T) (h_HS : 0 ≤ H_S) (h_le : H_S ≤ H_T) :
    0 ≤ (neiFst H_T H_S).value ∧ (neiFst H_T H_S).value ≤ 1 := by
  simp only [neiFst_value]
  constructor
  · exact div_nonneg (by linarith) (le_of_lt h_HT)
  · rw [div_le_one h_HT]; linarith

/-- **Exact fiber of Nei's heterozygosity `F_ST`.**  Once total heterozygosity is nonzero, an
observed `F_ST` value determines the retained within-population heterozygosity exactly. -/
theorem neiFst_eq_iff_within_heterozygosity_eq
    (H_T H_S fst : ℝ) (h_HT : H_T ≠ 0) :
    (neiFst H_T H_S).value = fst ↔ H_S = (1 - fst) * H_T := by
  simp only [neiFst_value]
  rw [div_eq_iff h_HT]
  constructor <;> intro h <;> nlinarith

/-- With nonzero total heterozygosity, Nei's `F_ST` vanishes exactly when subpopulations retain
all of the pooled heterozygosity. -/
theorem neiFst_eq_zero_iff
    (H_T H_S : ℝ) (h_HT : H_T ≠ 0) :
    (neiFst H_T H_S).value = 0 ↔ H_S = H_T := by
  simpa using neiFst_eq_iff_within_heterozygosity_eq H_T H_S 0 h_HT

/-- With nonzero total heterozygosity, Nei's `F_ST` equals one exactly when no within-population
heterozygosity remains. -/
theorem neiFst_eq_one_iff
    (H_T H_S : ℝ) (h_HT : H_T ≠ 0) :
    (neiFst H_T H_S).value = 1 ↔ H_S = 0 := by
  simpa using neiFst_eq_iff_within_heterozygosity_eq H_T H_S 1 h_HT


/-- **Nei's `G_ST` for two equally weighted subgroups, from allele
    frequencies:** `G_ST = (p₁ - p₂)² / (4·p̄·(1-p̄))`.

    THIRD COPY, CORRECTLY NAMED, DO NOT DELETE ON DISCOVERY. This is algebraically
    identical to `Conventions.neiGst`, which is written in the heterozygosity form
    `1 - (p₁(1-p₁) + p₂(1-p₂))/(2·p̄(1-p̄))`. The two agree because
    `p₁(1-p₁) + p₂(1-p₂) = 2p̄(1-p̄) - (p₁-p₂)²/2`, so
    `1 - H_S/H_T = (p₁-p₂)²/(4p̄(1-p̄))` exactly; `Conventions.neiGst_eq_varianceRatio`
    relates the two shapes. A name audit checked both against Nei's definition and
    found both correct, so if a duplication scan reports this pair, the resolution is
    to repoint one at the other, NOT to delete whichever is found second -- and note
    that `Conventions.hudsonFst` is a genuinely different estimator that only looks
    like a third spelling of the same thing.

    This is Nei's `G_ST` -- `1 - H_S/H_T` with `H_T = 2p̄(1-p̄)`
    the total-pool heterozygosity and `H_S` the mean within-subgroup
    heterozygosity -- and it is NOT Hudson's `F_ST`, which divides instead by
    the between-subgroup heterozygosity `p₁(1-p₂) + p₂(1-p₁)`. Derivation:
    `H_T - H_S = 2p̄(1-p̄) - (p₁(1-p₁) + p₂(1-p₂)) = (p₁-p₂)²/2`, and dividing
    by `H_T` gives this body. Hudson's estimator lives in `Conventions` as
    `hudsonFst`, with the exact conversion `Hudson = 2·G/(1 + G)` proved as
    `Conventions.hudsonFst_eq_of_neiGst`. The two differ by up to a factor
    of two -- +71.4% at `p₁ = 0.2, p₂ = 0.6` -- and AGREE ONLY WHERE THIS
    QUANTITY IS `0` OR `1`, i.e. at `p₁ = p₂` or at complete differentiation.
    That is immediate from the conversion: `2·G/(1+G) = G` iff `G = 0` or
    `G = 1`.

    **There is no `p̄ = 1/2` agreement slice. Do not add one.**
    On `p̄ = 1/2` exactly, with `p₁ = 0.9, p₂ = 0.1`, this body gives `0.64`
    and Hudson gives `0.7805`, a ratio of `1.22`; toward the middle the ratio
    approaches `2` (`1.995` at `(0.525, 0.475)`). The trap is that `p̄ = 1/2`
    makes the denominator `4·p̄·(1-p̄)` equal `1`, which looks like it should
    settle the comparison — it only makes `G_ST = (p₁-p₂)²`, while Hudson
    still divides by `1 - 2·p₁·p₂`.

    The arithmetic is unchanged by the rename; only the claim about what the
    number is has been made explicit.

    Empirical status: CONVENTION PINNED as Nei's `G_ST`, confirmed against an
    independent implementation by the differential checks `simpleFst-is-nei`
    and `simpleFst-vs-hudson`, which are retained as the standing checks. -/
noncomputable def neiGstFromFrequencies (p₁ p₂ : ℝ) : ℝ :=
  let p_bar := (p₁ + p₂) / 2
  (p₁ - p₂) ^ 2 / (4 * p_bar * (1 - p_bar))

/-- **neiGstFromFrequencies at two monomorphic populations, named.** With both populations fixed
for the reference allele the mean frequency is zero, so the heterozygosity normaliser `4 p̄ (1 -
p̄)` vanishes and there is no polymorphism to partition. Numerator and denominator vanish
together and Lean returns `0`: no differentiation, which is what two identical polymorphic
populations also give. Consumers must exclude it by hypothesis. -/
theorem neiGstFromFrequencies_monomorphic_is_junk :
    neiGstFromFrequencies 0 0 = 0 := by
  unfold neiGstFromFrequencies
  norm_num

/-- Nei's `G_ST` is nonneg. -/
theorem neiGstFromFrequencies_nonneg (p₁ p₂ : ℝ)
    (h₁ : 0 < p₁) (h₁' : p₁ < 1)
    (h₂ : 0 < p₂) (h₂' : p₂ < 1) :
    0 ≤ neiGstFromFrequencies p₁ p₂ := by
  unfold neiGstFromFrequencies
  apply div_nonneg (sq_nonneg _)
  nlinarith

/-- At strictly polymorphic subgroup frequencies, Nei's `G_ST` is strictly below one.  Complete
differentiation therefore requires a boundary fixation configuration rather than two interior
allele frequencies. -/
theorem neiGstFromFrequencies_lt_one (p₁ p₂ : ℝ)
    (h₁ : 0 < p₁) (h₁' : p₁ < 1)
    (h₂ : 0 < p₂) (h₂' : p₂ < 1) :
    neiGstFromFrequencies p₁ p₂ < 1 := by
  unfold neiGstFromFrequencies
  have h_den : 0 < 4 * ((p₁ + p₂) / 2) * (1 - (p₁ + p₂) / 2) := by
    nlinarith
  rw [div_lt_one h_den]
  have h_within₁ : 0 < p₁ * (1 - p₁) := mul_pos h₁ (sub_pos.mpr h₁')
  have h_within₂ : 0 < p₂ * (1 - p₂) := mul_pos h₂ (sub_pos.mpr h₂')
  nlinarith

/-- **`G_ST` is zero when the subgroups are identical.** -/
theorem neiGstFromFrequencies_zero_same (p : ℝ) :
    neiGstFromFrequencies p p = 0 := by
  unfold neiGstFromFrequencies
  simp [sub_self, zero_pow (by norm_num : 2 ≠ 0)]

/-- **Exact identifiability from Nei's two-population `G_ST`.**  At polymorphic loci, `G_ST`
vanishes if and only if the two subgroup allele frequencies agree.  The polymorphism assumptions
exclude the `0 / 0` endpoint where Lean's totalized division would otherwise manufacture the same
numerical answer. -/
theorem neiGstFromFrequencies_eq_zero_iff
    (p₁ p₂ : ℝ)
    (h₁ : 0 < p₁) (h₁' : p₁ < 1)
    (h₂ : 0 < p₂) (h₂' : p₂ < 1) :
    neiGstFromFrequencies p₁ p₂ = 0 ↔ p₁ = p₂ := by
  have h_den : 0 < 4 * ((p₁ + p₂) / 2) * (1 - (p₁ + p₂) / 2) := by
    nlinarith
  constructor
  · intro h_zero
    unfold neiGstFromFrequencies at h_zero
    rw [div_eq_zero_iff] at h_zero
    rcases h_zero with h_num | h_den_zero
    · nlinarith [sq_nonneg (p₁ - p₂)]
    · exact False.elim (h_den.ne' h_den_zero)
  · intro h_same
    subst p₂
    exact neiGstFromFrequencies_zero_same p₁

/-- At polymorphic loci, Nei's `G_ST` is strictly positive exactly when the subgroup allele
frequencies differ. -/
theorem neiGstFromFrequencies_pos_iff
    (p₁ p₂ : ℝ)
    (h₁ : 0 < p₁) (h₁' : p₁ < 1)
    (h₂ : 0 < p₂) (h₂' : p₂ < 1) :
    0 < neiGstFromFrequencies p₁ p₂ ↔ p₁ ≠ p₂ := by
  have h_nonneg := neiGstFromFrequencies_nonneg p₁ p₂ h₁ h₁' h₂ h₂'
  constructor
  · intro h_pos h_same
    have h_zero :=
      (neiGstFromFrequencies_eq_zero_iff p₁ p₂ h₁ h₁' h₂ h₂').2 h_same
    linarith
  · intro h_different
    have h_nonzero : neiGstFromFrequencies p₁ p₂ ≠ 0 := by
      intro h_zero
      exact h_different
        ((neiGstFromFrequencies_eq_zero_iff p₁ p₂ h₁ h₁' h₂ h₂').1 h_zero)
    exact lt_of_le_of_ne h_nonneg (Ne.symm h_nonzero)

/-- **`G_ST` is symmetric.** -/
theorem neiGstFromFrequencies_symmetric (p₁ p₂ : ℝ) :
    neiGstFromFrequencies p₁ p₂ = neiGstFromFrequencies p₂ p₁ := by
  unfold neiGstFromFrequencies
  ring_nf


end FstDefinitions

/-- **Cross-check: the two spellings of Nei's `G_ST` in this corpus agree.**

What this proves is that two independently written spellings of NEI's `G_ST`
coincide. **Neither side is Hudson's estimator.** That one is `hudsonFst`, and
`neiGst_ne_hudsonFst` exhibits a point where it differs from both of these, so
do not read either name here as Hudson's. -/
theorem neiGstFromFrequencies_eq_neiGst (p₁ p₂ : ℝ)
    (h : Descent.Core.meanAlleleFreq p₁ p₂ * (1 - Descent.Core.meanAlleleFreq p₁ p₂) ≠ 0) :
    PopGen.neiGstFromFrequencies p₁ p₂ = Descent.Core.neiGst p₁ p₂ := by
  rw [Descent.Core.neiGst_eq_varianceRatio p₁ p₂ h]
  change (p₁ - p₂) ^ 2 /
      (4 * Descent.Core.meanAlleleFreq p₁ p₂ * (1 - Descent.Core.meanAlleleFreq p₁ p₂)) =
    ((p₁ - p₂) ^ 2 / 4) /
      (Descent.Core.meanAlleleFreq p₁ p₂ * (1 - Descent.Core.meanAlleleFreq p₁ p₂))
  field_simp [h]

end Descent.PopGen
