import Calibrator.PopulationGeneticsFoundations
import Calibrator.DemographicHistory
import Calibrator.AncestrySpecificArchitecture
import Calibrator.PCCorrectability.Threshold

namespace Calibrator

/-!
# Identifications: making a named quantity carry its obligation

A Lean `def` cannot be wrong internally, so the entire risk of this
development sits in one place: a definition whose *name* claims a
population-genetic meaning that its *formula* does not have. Every theorem
downstream is then machine-checked and misleading. Two instances have now been
found by simulation rather than by proof.

`demographicSpike` carried the wrong constant, `2 F m_eff` where the data give
`3.9920 ± 0.0045`. A cross-check between two independently written formulas
would have caught it, and `four_hudsonFst_eq_standardizedContrastVariance`
below is that cross-check.

`singletonProportion N₀ N₁ = 1 - log N₀ / log N₁` was worse, and no
cross-check of that kind could have caught it. It returns `0` at the null
where the truth is `0.187`, and it takes no sample size at all although the
observable moves from `0.427` to `0.368` when `n` goes from 50 to 200. The
signature cannot express the quantity. That is a type error, not an arithmetic
one, and it is invisible to any argument that only compares formulas to other
formulas.

The two failures therefore need two different mechanisms.

* Against a wrong constant: over-determination. Derive the quantity from a
  primitive so the constant is forced, and relate independently written
  formulas so that drift between them fails to compile. That is this file.

* Against a wrong signature: an obligation attached to the name. A named
  empirical quantity must be introduced together with the observable it claims
  to be, and a proof that the two agree. Then a formula that cannot depend on
  `n` cannot be offered as an observable that does. That is `Identification`
  in `Calibrator.Identification`.
-/

section Ploidy

/-- Number of homologous copies per locus. Every non-exponent factor of two in
this development traces to this constant, and every factor of four to twice
it. The corpus currently restates the convention inline at ninety-nine
definition sites: seventy-eight carrying a two and twenty-one a four. The
theorems in this section tie the independently written ones back here, so that
drift between them is a compile error rather than a silent disagreement. -/
noncomputable def ploidy : ℝ := 2

/-- Genotype variance at a locus in Hardy-Weinberg proportions, for dosage
coded `0, 1, …, ploidy`. -/
noncomputable def hweGenotypeVariance (p : ℝ) : ℝ := ploidy * p * (1 - p)

/-- Coalescent time scale: time measured in units of `ploidy · Nₑ`
generations. -/
noncomputable def coalescentTimeScale (Ne : ℝ) : ℝ := ploidy * Ne

@[simp] theorem coalescentTimeScale_eq (Ne : ℝ) :
    coalescentTimeScale Ne = 2 * Ne := by
  unfold coalescentTimeScale ploidy; ring

/-- **Cross-check: the scaled mutation rate in `PopulationGeneticsFoundations`
is twice the coalescent time scale times the mutation rate**, rather than an
independently chosen `4`. -/
theorem scaledMutationRate_eq_ploidy_form (Ne mu : ℝ) :
    scaledMutationRate Ne mu = 2 * ploidy * Ne * mu := by
  unfold scaledMutationRate ploidy; ring

/-- **Cross-check: the scaled migration rate in `PortabilityDrift` uses the
same convention.** These two were written in different files, each spelling
out its own `4`. -/
theorem scaledMigrationRate_eq_ploidy_form (Ne m : ℝ) :
    scaledMigrationRate Ne m = 2 * ploidy * Ne * m := by
  unfold scaledMigrationRate ploidy; ring

/-- **Cross-check: the drift `F_ST` uses the coalescent time scale**, so the
`2 Nₑ` inside it is the same `ploidy · Nₑ` and not a separate choice. -/
theorem fstFromDrift_uses_coalescentTimeScale (t : ℕ) (Ne : ℝ) :
    fstFromDrift t Ne = 1 - (1 - 1 / coalescentTimeScale Ne) ^ t := by
  unfold fstFromDrift; rw [coalescentTimeScale_eq]

end Ploidy

section Differentiation

/-- Mean allele frequency across two subgroups of equal weight. -/
noncomputable def meanAlleleFreq (p₁ p₂ : ℝ) : ℝ := (p₁ + p₂) / 2

/-- **Hudson's `F_ST` for two subgroups**, as one minus the ratio of mean
within-subgroup heterozygosity to total heterozygosity. Restored as a
definition so that `F` denotes a quantity rather than a name; it had been
deleted as unreferenced, which is precisely why `F` in the spike was free to
mean anything. -/
noncomputable def hudsonFst (p₁ p₂ : ℝ) : ℝ :=
  1 - (p₁ * (1 - p₁) + p₂ * (1 - p₂)) /
    (ploidy * meanAlleleFreq p₁ p₂ * (1 - meanAlleleFreq p₁ p₂))

/-- Between-subgroup allele-frequency variance for an equal-weight split. -/
noncomputable def betweenSubgroupVariance (p₁ p₂ : ℝ) : ℝ := (p₁ - p₂) ^ 2 / 4

/-- **Cross-check: the heterozygosity form and the variance form of `F_ST`
agree.** The corpus contained both shapes and never related them. -/
theorem hudsonFst_eq_varianceRatio (p₁ p₂ : ℝ)
    (h : meanAlleleFreq p₁ p₂ * (1 - meanAlleleFreq p₁ p₂) ≠ 0) :
    hudsonFst p₁ p₂ =
      betweenSubgroupVariance p₁ p₂ /
        (meanAlleleFreq p₁ p₂ * (1 - meanAlleleFreq p₁ p₂)) := by
  unfold hudsonFst betweenSubgroupVariance meanAlleleFreq ploidy at *
  field_simp at h ⊢
  ring

/-- **Cross-check: `simpleFst`, written separately in
`PopulationGeneticsFoundations`, is the same quantity.** -/
theorem simpleFst_eq_hudsonFst (p₁ p₂ : ℝ)
    (h : meanAlleleFreq p₁ p₂ * (1 - meanAlleleFreq p₁ p₂) ≠ 0) :
    simpleFst p₁ p₂ = hudsonFst p₁ p₂ := by
  unfold simpleFst hudsonFst meanAlleleFreq ploidy at *
  field_simp at h ⊢
  ring

/-- **The spike constant is forced, not chosen.**

Four times Hudson `F_ST` is exactly the variance of the standardized subgroup
contrast. Writing `2` in `demographicSpike` asserts that twice `F_ST` equals
that variance, which this theorem refutes, so the old constant is now
unprovable rather than merely differently calibrated. Simulation recovers
`3.9920 ± 0.0045` with `F` measured as Hudson `F_ST`, agreeing with the
derived value. -/
theorem four_hudsonFst_eq_standardizedContrastVariance (p₁ p₂ : ℝ)
    (h : meanAlleleFreq p₁ p₂ * (1 - meanAlleleFreq p₁ p₂) ≠ 0) :
    4 * hudsonFst p₁ p₂ =
      (p₁ - p₂) ^ 2 / (meanAlleleFreq p₁ p₂ * (1 - meanAlleleFreq p₁ p₂)) := by
  rw [hudsonFst_eq_varianceRatio p₁ p₂ h]
  unfold betweenSubgroupVariance
  field_simp
  ring

/-- **The spike written without any free constant.** With `F` pinned to Hudson
`F_ST`, the rank-one signal is the contrast variance times the effective
subgroup size, and no numeral appears on the right. -/
theorem demographicSpike_eq_contrastVariance_mul_effectiveSize
    (n m p₁ p₂ : ℝ)
    (h : meanAlleleFreq p₁ p₂ * (1 - meanAlleleFreq p₁ p₂) ≠ 0) :
    demographicSpike n (hudsonFst p₁ p₂) m =
      ((p₁ - p₂) ^ 2 / (meanAlleleFreq p₁ p₂ * (1 - meanAlleleFreq p₁ p₂))) *
        effectiveSubgroupSize n m := by
  unfold demographicSpike
  rw [← four_hudsonFst_eq_standardizedContrastVariance p₁ p₂ h]
  ring

end Differentiation

section EquilibriumAgreements

/-- **Cross-check: the island-model `F_ST` in `DemographicHistory` and the
architecture-level `equilibriumFst` in `AncestrySpecificArchitecture` are the
same function.** They were written in separate files, each spelling out its own
factor of four. -/
theorem equilibriumFst_eq_demoIslandModelFst (Ne m : ℝ) :
    equilibriumFst m Ne = demoIslandModelFst Ne m := by
  unfold equilibriumFst demoIslandModelFst; ring_nf

end EquilibriumAgreements

end Calibrator
