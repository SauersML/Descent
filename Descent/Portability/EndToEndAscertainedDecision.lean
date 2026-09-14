/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.PortabilityMomentLadderDecision

assert_below Descent.Decision Descent.Program

/-!
# Case-control ascertained decision metrics

`EndToEndDecisionLaw` carries the expected confusion table of a threshold rule through a
demographic history, and `PortabilityMomentLadderDecision` fixes it from degree one under any
process law.  Both read the population law, in which cases arrive at the population prevalence.
Threshold metrics are validated in case-control cohorts that sample cases at a design fraction
`c` instead.  `EndToEndAscertainedLaw` ascertains variants by a panel rule; this module ascertains
individuals by outcome.

The cohort table.  A cohort with case fraction `c` draws its cases from the case column of a
confusion table and its controls from the control column.  Its table reweights the case column
`TP + FN` by `c / (TP + FN)` and the control column `TN + FP` by `(1 - c) / (TN + FP)`
(`tableCaseMass`, `tableControlMass`, `ascertainedTable`), so its columns have masses `c` and
`1 - c` (`tableCaseMass_ascertainedTable`).  On the expected confusion table the case column is the
expected prevalence and the two columns sum to one, so the control weight is
`(1 - c) / (1 - prevalence)` (`tableCaseMass_expectedConfusion`,
`tableCaseMass_add_tableControlMass_expectedConfusion`).  The cohort table of the expected table is
a ratio of expectations (`ascertainedConfusion`).

Invariance.  Sensitivity and specificity are ratios within one column, so the cohort keeps them,
and Youden's J with them (`tableSensitivity_tableSpecificity_ascertainedTable`,
`tableYouden_ascertainedTable`, `ascertainedConfusion_sensitivity_specificity`).

Predictive value.  The positive predictive value at prevalence `p` is
`p · sens / (p · sens + (1 - p)(1 - spec))` (`predictiveValueAt`).  A table whose columns sum to
one has this value at its own prevalence (`tablePPV_eq_predictiveValueAt`).  The cohort has it at
the case fraction, `c · sens / (c · sens + (1 - c)(1 - spec))`, whatever the population prevalence
(`tablePPV_ascertainedTable`).  A predictive value read at one prevalence goes to another by Bayes'
odds rule (`shiftPredictiveValue`, `predictiveValueAt_eq_shiftPredictiveValue`).  So the population
value is the cohort value carried from `c` to the population prevalence, and the cohort value is
the population value carried back (`tablePPV_eq_shiftPredictiveValue`,
`tablePPV_ascertainedTable_eq_shiftPredictiveValue`).  On the expected tables the prevalence is
the expected case probability (`tablePPV_expectedConfusion_ascertainedConfusion_shift`).

Portability.  Two predictive values agree exactly when prevalence odds times the positive
likelihood ratio agree (`predictiveValueAt_eq_iff`).  At one case fraction the cohort value ports
exactly when `sens₁ (1 - spec₂) = sens₂ (1 - spec₁)`, the cross form of equal likelihood ratios
(`tablePPV_ascertainedTable_eq_iff`).  It ports whenever sensitivity and specificity port, whatever
the prevalences (`tablePPV_ascertainedTable_eq_of_rates_eq`).  With ported sensitivity and
specificity the population value ports exactly when the prevalence ports as well
(`tablePPV_eq_iff_tableCaseMass_eq`, and between two demes of a process law
`tablePPV_portability_of_rates_eq`).  On the witness laws of `EndToEndDecisionLaw` the prevalence
falls from one half to one fifth and the population value from four fifths to one half, while the
balanced cohort reads four fifths in both (`ascertainedPrevalenceShift_witness`).

Under any process law.  `ascertainedDecisionReport` collects, at every case fraction, the cohort
table of every deme and the portability of every metric of it.  It is a function of the decision
report (`ascertainedDecisionReport_eq_of_decisionReport_eq`), so degree one fixes it
(`ascertainedDecisionReport_eq_of_polynomialsAgreeAt_one`).  An event history and a rate history
with equal budget-1 moments give one ascertained report
(`ascertainedDecisionReport_historyEvent_eq_rateHistory`).

Scope.  The cohort draws cases and controls from the terminal law of one deme at a fixed fraction,
and the table is the ratio-of-expectations form, not the expectation of per-cohort ratios.  The
negative predictive value is not restated.  Case fractions estimated from the cohort, matching on
covariates and the sampling error of a finite cohort are not covered.

## Empirical status

None.  The bodies here are rational identities of confusion tables, integrals of cell masses
against Markov kernels and arithmetic on explicit finite laws, so no measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.EndToEndAscertainedDecision

open MeasureTheory ProbabilityTheory MvPolynomial Descent.Coalescent PartialHaplotypeCarrier
  PartialHaplotypeDualGenerator PartialHaplotypeDualSemigroup NeutralFellerGenerator
  NeutralPolynomialSemigroup PartialHaplotypeMicroscopicApproximation PartialHaplotypePulseKernel
  NeutralPulseHistoryKernel NeutralRateHistoryRealization NeutralRateHistoryKernel
  ReplicaMetricInstances EndToEndPortabilityLaw EndToEndDiscriminationLaw EndToEndBrierLaw
  EndToEndDecisionLaw PortabilityMomentLadder PortabilityMomentLadderDecision
open scoped Matrix NNReal

noncomputable section

/-! ## The cohort table -/

/-- The case column mass `TP + FN` of a confusion table indexed by call and outcome. -/
def tableCaseMass (table : Bool × Bool → ℝ) : ℝ :=
  table (true, true) + table (false, true)

/-- The control column mass `TN + FP` of a confusion table indexed by call and outcome. -/
def tableControlMass (table : Bool × Bool → ℝ) : ℝ :=
  table (false, false) + table (true, false)

/-- **The case-control table at case fraction `c`**: the case column of a confusion table
reweighted by `c / (TP + FN)` and the control column by `(1 - c) / (TN + FP)`.  It is the table of
a cohort that draws the fraction `c` of its members from the case column and the rest from the
control column. -/
def ascertainedTable (c : ℝ) (table : Bool × Bool → ℝ) : Bool × Bool → ℝ
  | (row, true) => c / tableCaseMass table * table (row, true)
  | (row, false) => (1 - c) / tableControlMass table * table (row, false)

/-- **The cohort has case fraction `c`.**  Its case column has mass `c` and its control column
mass `1 - c`.

Assumes: nonzero case and control columns. -/
theorem tableCaseMass_ascertainedTable (c : ℝ) (table : Bool × Bool → ℝ)
    (hcase : tableCaseMass table ≠ 0) (hcontrol : tableControlMass table ≠ 0) :
    tableCaseMass (ascertainedTable c table) = c
      ∧ tableControlMass (ascertainedTable c table) = 1 - c := by
  constructor
  · simp only [tableCaseMass, ascertainedTable]
    rw [← mul_add]
    exact div_mul_cancel₀ c hcase
  · simp only [tableControlMass, ascertainedTable]
    rw [← mul_add]
    exact div_mul_cancel₀ (1 - c) hcontrol

/-- **The cohort keeps sensitivity and specificity.**  Each is the ratio of a cell to its own
column, and the cohort scales each column by one factor.  A vanishing column reads zero on both
sides.

Assumes: `c ≠ 0` and `c ≠ 1`. -/
theorem tableSensitivity_tableSpecificity_ascertainedTable (c : ℝ) (table : Bool × Bool → ℝ)
    (hc0 : c ≠ 0) (hc1 : c ≠ 1) :
    tableSensitivity (ascertainedTable c table) = tableSensitivity table
      ∧ tableSpecificity (ascertainedTable c table) = tableSpecificity table := by
  have hshare : ∀ scale first second : ℝ, scale ≠ 0 ∨ first + second = 0 →
      scale * first / (scale * first + scale * second) = first / (first + second) := by
    rintro scale first second (hscale | hcolumn)
    · rw [← mul_add, mul_div_mul_left _ _ hscale]
    · rw [← mul_add, hcolumn, mul_zero, div_zero, div_zero]
  constructor
  · simp only [tableSensitivity, ascertainedTable]
    apply hshare
    rcases eq_or_ne (tableCaseMass table) 0 with hcase | hcase
    · exact Or.inr hcase
    · exact Or.inl (div_ne_zero hc0 hcase)
  · simp only [tableSpecificity, ascertainedTable]
    apply hshare
    rcases eq_or_ne (tableControlMass table) 0 with hcontrol | hcontrol
    · exact Or.inr hcontrol
    · exact Or.inl (div_ne_zero (sub_ne_zero.mpr hc1.symm) hcontrol)

/-- **The cohort keeps Youden's J.**

Assumes: `c ≠ 0` and `c ≠ 1`. -/
theorem tableYouden_ascertainedTable (c : ℝ) (table : Bool × Bool → ℝ) (hc0 : c ≠ 0)
    (hc1 : c ≠ 1) : tableYouden (ascertainedTable c table) = tableYouden table := by
  obtain ⟨hsensitivity, hspecificity⟩ :=
    tableSensitivity_tableSpecificity_ascertainedTable c table hc0 hc1
  rw [tableYouden, tableYouden, hsensitivity, hspecificity]

/-! ## Predictive value at a prevalence -/

/-- **The positive predictive value at prevalence `p`** of a rule with sensitivity `sens` and
specificity `spec`: `p · sens / (p · sens + (1 - p)(1 - spec))`. -/
def predictiveValueAt (p sensitivity specificity : ℝ) : ℝ :=
  p * sensitivity / (p * sensitivity + (1 - p) * (1 - specificity))

/-- **Bayes' odds rule for a predictive value**: the value `v` read at prevalence `source`, carried
to prevalence `target`.  Its odds are the odds of `v` times the target prevalence odds over the
source prevalence odds. -/
def shiftPredictiveValue (target source value : ℝ) : ℝ :=
  target * (1 - source) * value
    / (target * (1 - source) * value + source * (1 - target) * (1 - value))

/-- The called cases of the cohort are `c · sens`. -/
theorem ascertainedTable_true_true (c : ℝ) (table : Bool × Bool → ℝ) :
    ascertainedTable c table (true, true) = c * tableSensitivity table := by
  simp only [ascertainedTable, tableSensitivity, tableCaseMass]
  ring

/-- The complement of specificity is the called share of the control column.

Assumes: a nonzero control column. -/
theorem one_sub_tableSpecificity (table : Bool × Bool → ℝ)
    (hcontrol : tableControlMass table ≠ 0) :
    1 - tableSpecificity table = table (true, false) / tableControlMass table := by
  have hsum : table (false, false) / tableControlMass table
      + table (true, false) / tableControlMass table = 1 := by
    rw [← add_div]
    exact div_self hcontrol
  change 1 - table (false, false) / tableControlMass table = _
  linarith

/-- The called controls of the cohort are `(1 - c)(1 - spec)`.

Assumes: a nonzero control column. -/
theorem ascertainedTable_true_false (c : ℝ) (table : Bool × Bool → ℝ)
    (hcontrol : tableControlMass table ≠ 0) :
    ascertainedTable c table (true, false) = (1 - c) * (1 - tableSpecificity table) := by
  rw [one_sub_tableSpecificity table hcontrol]
  simp only [ascertainedTable]
  ring

/-- The called cases of a table are `prevalence · sens`.

Assumes: a nonzero case column. -/
theorem tableCaseMass_mul_tableSensitivity (table : Bool × Bool → ℝ)
    (hcase : tableCaseMass table ≠ 0) :
    tableCaseMass table * tableSensitivity table = table (true, true) :=
  mul_div_cancel₀ (table (true, true)) hcase

/-- The called controls of a table whose columns sum to one are `(1 - prevalence)(1 - spec)`.

Assumes: columns summing to one and a nonzero control column. -/
theorem one_sub_tableCaseMass_mul_one_sub_tableSpecificity (table : Bool × Bool → ℝ)
    (htotal : tableCaseMass table + tableControlMass table = 1)
    (hcontrol : tableControlMass table ≠ 0) :
    (1 - tableCaseMass table) * (1 - tableSpecificity table) = table (true, false) := by
  rw [one_sub_tableSpecificity table hcontrol,
    show 1 - tableCaseMass table = tableControlMass table by linarith]
  exact mul_div_cancel₀ (table (true, false)) hcontrol

/-- **A table has the predictive value at its own prevalence.**

Assumes: columns summing to one and nonzero case and control columns. -/
theorem tablePPV_eq_predictiveValueAt (table : Bool × Bool → ℝ)
    (htotal : tableCaseMass table + tableControlMass table = 1)
    (hcase : tableCaseMass table ≠ 0) (hcontrol : tableControlMass table ≠ 0) :
    tablePPV table
      = predictiveValueAt (tableCaseMass table) (tableSensitivity table)
        (tableSpecificity table) := by
  rw [predictiveValueAt, tableCaseMass_mul_tableSensitivity table hcase,
    one_sub_tableCaseMass_mul_one_sub_tableSpecificity table htotal hcontrol, tablePPV]

/-- **The cohort predictive value is the predictive value at the case fraction**,
`c · sens / (c · sens + (1 - c)(1 - spec))`, whatever the population prevalence.

Assumes: a nonzero control column. -/
theorem tablePPV_ascertainedTable (c : ℝ) (table : Bool × Bool → ℝ)
    (hcontrol : tableControlMass table ≠ 0) :
    tablePPV (ascertainedTable c table)
      = predictiveValueAt c (tableSensitivity table) (tableSpecificity table) := by
  rw [tablePPV, predictiveValueAt, ascertainedTable_true_true,
    ascertainedTable_true_false c table hcontrol]

/-- **Bayes' odds rule carries a predictive value between prevalences.**  The predictive value at
prevalence `target` is the predictive value at prevalence `source` carried to `target`.

Assumes: `source ≠ 0`, `source ≠ 1` and a nonzero predictive denominator at `source`. -/
theorem predictiveValueAt_eq_shiftPredictiveValue (target source sensitivity specificity : ℝ)
    (hsource0 : source ≠ 0) (hsource1 : source ≠ 1)
    (hden : source * sensitivity + (1 - source) * (1 - specificity) ≠ 0) :
    predictiveValueAt target sensitivity specificity
      = shiftPredictiveValue target source (predictiveValueAt source sensitivity specificity) := by
  have hfactor :
      source * (1 - source) / (source * sensitivity + (1 - source) * (1 - specificity)) ≠ 0 :=
    div_ne_zero (mul_ne_zero hsource0 (sub_ne_zero.mpr hsource1.symm)) hden
  have hcomplement : 1 - predictiveValueAt source sensitivity specificity
      = (1 - source) * (1 - specificity)
        / (source * sensitivity + (1 - source) * (1 - specificity)) := by
    have hsum : source * sensitivity / (source * sensitivity + (1 - source) * (1 - specificity))
        + (1 - source) * (1 - specificity)
          / (source * sensitivity + (1 - source) * (1 - specificity)) = 1 := by
      rw [← add_div]
      exact div_self hden
    rw [predictiveValueAt]
    linarith
  rw [shiftPredictiveValue, hcomplement, predictiveValueAt, predictiveValueAt,
    ← mul_div_mul_left (target * sensitivity) _ hfactor]
  congr 1 <;> ring

/-- **The population predictive value from the cohort predictive value.**  It is the cohort value
carried from the case fraction `c` to the population prevalence.

Assumes: columns summing to one, nonzero case and control columns, `c ≠ 0`, `c ≠ 1` and a cohort
calling a nonzero mass. -/
theorem tablePPV_eq_shiftPredictiveValue (c : ℝ) (table : Bool × Bool → ℝ)
    (htotal : tableCaseMass table + tableControlMass table = 1)
    (hcase : tableCaseMass table ≠ 0) (hcontrol : tableControlMass table ≠ 0)
    (hc0 : c ≠ 0) (hc1 : c ≠ 1)
    (hcalled :
      ascertainedTable c table (true, true) + ascertainedTable c table (true, false) ≠ 0) :
    tablePPV table
      = shiftPredictiveValue (tableCaseMass table) c (tablePPV (ascertainedTable c table)) := by
  rw [ascertainedTable_true_true, ascertainedTable_true_false c table hcontrol] at hcalled
  rw [tablePPV_eq_predictiveValueAt table htotal hcase hcontrol,
    tablePPV_ascertainedTable c table hcontrol]
  exact predictiveValueAt_eq_shiftPredictiveValue _ c _ _ hc0 hc1 hcalled

/-- **The cohort predictive value from the population predictive value.**  It is the population
value carried from the population prevalence to the case fraction `c`.

Assumes: columns summing to one, nonzero case and control columns and a rule calling a nonzero
mass. -/
theorem tablePPV_ascertainedTable_eq_shiftPredictiveValue (c : ℝ) (table : Bool × Bool → ℝ)
    (htotal : tableCaseMass table + tableControlMass table = 1)
    (hcase : tableCaseMass table ≠ 0) (hcontrol : tableControlMass table ≠ 0)
    (hcalled : table (true, true) + table (true, false) ≠ 0) :
    tablePPV (ascertainedTable c table)
      = shiftPredictiveValue c (tableCaseMass table) (tablePPV table) := by
  have hprevalence : tableCaseMass table ≠ 1 := fun h ↦ hcontrol (by linarith)
  rw [← tableCaseMass_mul_tableSensitivity table hcase,
    ← one_sub_tableCaseMass_mul_one_sub_tableSpecificity table htotal hcontrol] at hcalled
  rw [tablePPV_eq_predictiveValueAt table htotal hcase hcontrol,
    tablePPV_ascertainedTable c table hcontrol]
  exact predictiveValueAt_eq_shiftPredictiveValue c _ _ _ hcase hprevalence hcalled

/-! ## Portability of predictive values -/

/-- **Predictive values agree exactly when prevalence odds times likelihood ratio agree**, in the
cross form `p₁ (1 - p₂) · sens₁ (1 - spec₂) = p₂ (1 - p₁) · sens₂ (1 - spec₁)`.

Assumes: nonzero predictive denominators. -/
theorem predictiveValueAt_eq_iff (p₁ s₁ f₁ p₂ s₂ f₂ : ℝ)
    (hden₁ : p₁ * s₁ + (1 - p₁) * (1 - f₁) ≠ 0) (hden₂ : p₂ * s₂ + (1 - p₂) * (1 - f₂) ≠ 0) :
    predictiveValueAt p₁ s₁ f₁ = predictiveValueAt p₂ s₂ f₂
      ↔ p₁ * (1 - p₂) * (s₁ * (1 - f₂)) = p₂ * (1 - p₁) * (s₂ * (1 - f₁)) := by
  rw [predictiveValueAt, predictiveValueAt, div_eq_div_iff hden₁ hden₂]
  constructor <;> intro h <;> linear_combination h

/-- **The cohort predictive value ports exactly when the likelihood ratio ports.**  At one case
fraction two tables give cohorts with equal predictive values exactly when
`sens₁ (1 - spec₂) = sens₂ (1 - spec₁)`, whatever their prevalences.

Assumes: `c ≠ 0`, `c ≠ 1`, nonzero control columns and cohorts calling nonzero masses. -/
theorem tablePPV_ascertainedTable_eq_iff (c : ℝ) (first second : Bool × Bool → ℝ)
    (hc0 : c ≠ 0) (hc1 : c ≠ 1)
    (hcontrol₁ : tableControlMass first ≠ 0) (hcontrol₂ : tableControlMass second ≠ 0)
    (hcalled₁ :
      ascertainedTable c first (true, true) + ascertainedTable c first (true, false) ≠ 0)
    (hcalled₂ :
      ascertainedTable c second (true, true) + ascertainedTable c second (true, false) ≠ 0) :
    tablePPV (ascertainedTable c first) = tablePPV (ascertainedTable c second)
      ↔ tableSensitivity first * (1 - tableSpecificity second)
        = tableSensitivity second * (1 - tableSpecificity first) := by
  rw [ascertainedTable_true_true, ascertainedTable_true_false c first hcontrol₁] at hcalled₁
  rw [ascertainedTable_true_true, ascertainedTable_true_false c second hcontrol₂] at hcalled₂
  rw [tablePPV_ascertainedTable c first hcontrol₁, tablePPV_ascertainedTable c second hcontrol₂,
    predictiveValueAt_eq_iff _ _ _ _ _ _ hcalled₁ hcalled₂]
  have hfactor : c * (1 - c) ≠ 0 := mul_ne_zero hc0 (sub_ne_zero.mpr hc1.symm)
  exact ⟨mul_left_cancel₀ hfactor, fun h ↦ by rw [h]⟩

/-- **Ported sensitivity and specificity port the cohort predictive value**, whatever the two
prevalences.

Assumes: nonzero control columns, equal sensitivities and equal specificities. -/
theorem tablePPV_ascertainedTable_eq_of_rates_eq (c : ℝ) (first second : Bool × Bool → ℝ)
    (hcontrol₁ : tableControlMass first ≠ 0) (hcontrol₂ : tableControlMass second ≠ 0)
    (hsensitivity : tableSensitivity first = tableSensitivity second)
    (hspecificity : tableSpecificity first = tableSpecificity second) :
    tablePPV (ascertainedTable c first) = tablePPV (ascertainedTable c second) := by
  rw [tablePPV_ascertainedTable c first hcontrol₁, tablePPV_ascertainedTable c second hcontrol₂,
    hsensitivity, hspecificity]

/-- **With ported sensitivity and specificity, the population predictive value ports exactly when
the prevalence ports.**

Assumes: columns summing to one, nonzero case and control columns, equal sensitivities and
specificities, a nonzero sensitivity, a specificity other than one and rules calling nonzero
masses. -/
theorem tablePPV_eq_iff_tableCaseMass_eq (first second : Bool × Bool → ℝ)
    (htotal₁ : tableCaseMass first + tableControlMass first = 1)
    (htotal₂ : tableCaseMass second + tableControlMass second = 1)
    (hcase₁ : tableCaseMass first ≠ 0) (hcase₂ : tableCaseMass second ≠ 0)
    (hcontrol₁ : tableControlMass first ≠ 0) (hcontrol₂ : tableControlMass second ≠ 0)
    (hsensitivity : tableSensitivity first = tableSensitivity second)
    (hspecificity : tableSpecificity first = tableSpecificity second)
    (hsensitivity0 : tableSensitivity second ≠ 0) (hspecificity1 : tableSpecificity second ≠ 1)
    (hcalled₁ : first (true, true) + first (true, false) ≠ 0)
    (hcalled₂ : second (true, true) + second (true, false) ≠ 0) :
    tablePPV first = tablePPV second ↔ tableCaseMass first = tableCaseMass second := by
  rw [← tableCaseMass_mul_tableSensitivity first hcase₁,
    ← one_sub_tableCaseMass_mul_one_sub_tableSpecificity first htotal₁ hcontrol₁, hsensitivity,
    hspecificity] at hcalled₁
  rw [← tableCaseMass_mul_tableSensitivity second hcase₂,
    ← one_sub_tableCaseMass_mul_one_sub_tableSpecificity second htotal₂ hcontrol₂] at hcalled₂
  rw [tablePPV_eq_predictiveValueAt first htotal₁ hcase₁ hcontrol₁,
    tablePPV_eq_predictiveValueAt second htotal₂ hcase₂ hcontrol₂, hsensitivity, hspecificity,
    predictiveValueAt_eq_iff _ _ _ _ _ _ hcalled₁ hcalled₂]
  have hfactor : tableSensitivity second * (1 - tableSpecificity second) ≠ 0 :=
    mul_ne_zero hsensitivity0 (sub_ne_zero.mpr hspecificity1.symm)
  constructor
  · intro h
    exact mul_left_cancel₀ hfactor (by linear_combination h)
  · intro h
    rw [h]

/-- **A balanced cohort hides a prevalence shift.**  On the witness laws of `EndToEndDecisionLaw`,
read as confusion tables of the identity rule, the prevalence falls from one half to one fifth and
the population predictive value from four fifths to one half.  The balanced cohort, case fraction
one half, reads four fifths in both. -/
theorem ascertainedPrevalenceShift_witness :
    tableCaseMass witnessSourceLaw.mass = 1 / 2 ∧ tableCaseMass witnessTargetLaw.mass = 1 / 5
      ∧ tablePPV witnessSourceLaw.mass = 4 / 5 ∧ tablePPV witnessTargetLaw.mass = 1 / 2
      ∧ tablePPV (ascertainedTable (1 / 2) witnessSourceLaw.mass) = 4 / 5
      ∧ tablePPV (ascertainedTable (1 / 2) witnessTargetLaw.mass) = 4 / 5 := by
  norm_num [tableCaseMass, tableControlMass, tablePPV, ascertainedTable, witnessSourceLaw,
    witnessTargetLaw]

/-! ## The cohort table of the expected confusion table -/

variable {Deme Locus : Type*} {Allele : Locus → Type*}
variable [Fintype Deme] [DecidableEq Deme] [Fintype Locus] [DecidableEq Locus]
  [∀ ℓ, Fintype (Allele ℓ)] [∀ ℓ, DecidableEq (Allele ℓ)]
variable {Score : Type*} [Fintype Score]

/-- **The cohort table of the expected confusion table**: the case-control table at case fraction
`c` of the expected confusion table of a rule in a deme, under a kernel started at `x₀`.  Its cells
are ratios of expectations. -/
def ascertainedConfusion
    (κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele))
    (x0 : FrequencyState Deme Locus Allele) (deme : Deme)
    (report : FullHaplotype Locus Allele → Score × Bool) (called : Score → Bool) (c : ℝ) :
    Bool × Bool → ℝ :=
  ascertainedTable c (expectedConfusion κ x0 deme report called)

/-- **The case column of the expected table is the expected prevalence.** -/
theorem tableCaseMass_expectedConfusion
    (κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele))
    [IsMarkovKernel κ] (x0 : FrequencyState Deme Locus Allele) (deme : Deme)
    (report : FullHaplotype Locus Allele → Score × Bool) (called : Score → Bool) :
    tableCaseMass (expectedConfusion κ x0 deme report called)
      = ∫ y, ((stateLaw y deme).pushforward report).binaryCaseMass Prod.snd ∂(κ x0) := by
  simp only [tableCaseMass, expectedConfusion, ← prevalence_ruleConfusion _ called,
    Foundations.ConfusionMatrix.prevalence, ruleConfusion, calledMass_pushforward,
    clearedMass_pushforward]
  rw [integral_add (integrable_confusionMass κ x0 deme report called (true, true))
    (integrable_confusionMass κ x0 deme report called (false, true))]

/-- **The columns of the expected table sum to one**, so its control column is one minus the
expected prevalence. -/
theorem tableCaseMass_add_tableControlMass_expectedConfusion
    (κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele))
    [IsMarkovKernel κ] (x0 : FrequencyState Deme Locus Allele) (deme : Deme)
    (report : FullHaplotype Locus Allele → Score × Bool) (called : Score → Bool) :
    tableCaseMass (expectedConfusion κ x0 deme report called)
      + tableControlMass (expectedConfusion κ x0 deme report called) = 1 := by
  have hsum : ∫ y, ∑ cell : Bool × Bool,
      ((stateLaw y deme).pushforward (confusionReport report called)).mass cell ∂(κ x0) = 1 := by
    simp only [FiniteReportLaw.mass_sum, integral_const, measureReal_univ_eq_one, smul_eq_mul,
      mul_one]
  rw [integral_finset_sum Finset.univ
    fun cell _ ↦ integrable_confusionMass κ x0 deme report called cell] at hsum
  simp only [Fintype.sum_prod_type, Fintype.sum_bool] at hsum
  simp only [tableCaseMass, tableControlMass, expectedConfusion]
  linarith

/-- **The cohort keeps the expected sensitivity and specificity.**

Assumes: `c ≠ 0` and `c ≠ 1`. -/
theorem ascertainedConfusion_sensitivity_specificity
    (κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele))
    (x0 : FrequencyState Deme Locus Allele) (deme : Deme)
    (report : FullHaplotype Locus Allele → Score × Bool) (called : Score → Bool) {c : ℝ}
    (hc0 : c ≠ 0) (hc1 : c ≠ 1) :
    tableSensitivity (ascertainedConfusion κ x0 deme report called c)
        = tableSensitivity (expectedConfusion κ x0 deme report called)
      ∧ tableSpecificity (ascertainedConfusion κ x0 deme report called c)
        = tableSpecificity (expectedConfusion κ x0 deme report called) :=
  tableSensitivity_tableSpecificity_ascertainedTable c
    (expectedConfusion κ x0 deme report called) hc0 hc1

/-- **The exact transform between population and cohort predictive values.**  In a deme with
expected prevalence `π`, the population predictive value of the expected table is the cohort value
carried from `c` to `π`, and the cohort value is the population value carried from `π` to `c`.

Assumes: an expected prevalence other than zero and one, `c ≠ 0`, `c ≠ 1`, and a rule and a cohort
calling nonzero masses. -/
theorem tablePPV_expectedConfusion_ascertainedConfusion_shift
    (κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele))
    [IsMarkovKernel κ] (x0 : FrequencyState Deme Locus Allele) (deme : Deme)
    (report : FullHaplotype Locus Allele → Score × Bool) (called : Score → Bool) {c : ℝ}
    (hc0 : c ≠ 0) (hc1 : c ≠ 1)
    (hprevalence0 :
      ∫ y, ((stateLaw y deme).pushforward report).binaryCaseMass Prod.snd ∂(κ x0) ≠ 0)
    (hprevalence1 :
      ∫ y, ((stateLaw y deme).pushforward report).binaryCaseMass Prod.snd ∂(κ x0) ≠ 1)
    (hcalled : expectedConfusion κ x0 deme report called (true, true)
      + expectedConfusion κ x0 deme report called (true, false) ≠ 0)
    (hcalledCohort : ascertainedConfusion κ x0 deme report called c (true, true)
      + ascertainedConfusion κ x0 deme report called c (true, false) ≠ 0) :
    tablePPV (expectedConfusion κ x0 deme report called)
        = shiftPredictiveValue
          (∫ y, ((stateLaw y deme).pushforward report).binaryCaseMass Prod.snd ∂(κ x0)) c
          (tablePPV (ascertainedConfusion κ x0 deme report called c))
      ∧ tablePPV (ascertainedConfusion κ x0 deme report called c)
        = shiftPredictiveValue c
          (∫ y, ((stateLaw y deme).pushforward report).binaryCaseMass Prod.snd ∂(κ x0))
          (tablePPV (expectedConfusion κ x0 deme report called)) := by
  have htotal := tableCaseMass_add_tableControlMass_expectedConfusion κ x0 deme report called
  rw [← tableCaseMass_expectedConfusion κ x0 deme report called] at hprevalence0 hprevalence1 ⊢
  have hcontrol : tableControlMass (expectedConfusion κ x0 deme report called) ≠ 0 :=
    fun h ↦ hprevalence1 (by linarith)
  exact ⟨tablePPV_eq_shiftPredictiveValue c (expectedConfusion κ x0 deme report called) htotal
      hprevalence0 hcontrol hc0 hc1 hcalledCohort,
    tablePPV_ascertainedTable_eq_shiftPredictiveValue c
      (expectedConfusion κ x0 deme report called) htotal hprevalence0 hcontrol hcalled⟩

/-- **Between two demes, cohort predictive values port with the rates, and population predictive
values also need the prevalence.**  If the expected sensitivity and specificity of a rule agree in
a source and a target deme, the cohorts at one case fraction have equal predictive values, and the
population predictive values agree exactly when the expected prevalences agree.

Assumes: equal expected sensitivities and specificities, a nonzero sensitivity, a specificity other
than one, expected prevalences other than zero and one and rules calling nonzero masses. -/
theorem tablePPV_portability_of_rates_eq
    (κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele))
    [IsMarkovKernel κ] (x0 : FrequencyState Deme Locus Allele) (source target : Deme)
    (report : FullHaplotype Locus Allele → Score × Bool) (called : Score → Bool) (c : ℝ)
    (hsensitivity : tableSensitivity (expectedConfusion κ x0 target report called)
      = tableSensitivity (expectedConfusion κ x0 source report called))
    (hspecificity : tableSpecificity (expectedConfusion κ x0 target report called)
      = tableSpecificity (expectedConfusion κ x0 source report called))
    (hsensitivity0 : tableSensitivity (expectedConfusion κ x0 source report called) ≠ 0)
    (hspecificity1 : tableSpecificity (expectedConfusion κ x0 source report called) ≠ 1)
    (hsource0 :
      ∫ y, ((stateLaw y source).pushforward report).binaryCaseMass Prod.snd ∂(κ x0) ≠ 0)
    (hsource1 :
      ∫ y, ((stateLaw y source).pushforward report).binaryCaseMass Prod.snd ∂(κ x0) ≠ 1)
    (htarget0 :
      ∫ y, ((stateLaw y target).pushforward report).binaryCaseMass Prod.snd ∂(κ x0) ≠ 0)
    (htarget1 :
      ∫ y, ((stateLaw y target).pushforward report).binaryCaseMass Prod.snd ∂(κ x0) ≠ 1)
    (hcalledSource : expectedConfusion κ x0 source report called (true, true)
      + expectedConfusion κ x0 source report called (true, false) ≠ 0)
    (hcalledTarget : expectedConfusion κ x0 target report called (true, true)
      + expectedConfusion κ x0 target report called (true, false) ≠ 0) :
    tablePPV (ascertainedConfusion κ x0 target report called c)
        = tablePPV (ascertainedConfusion κ x0 source report called c)
      ∧ (tablePPV (expectedConfusion κ x0 target report called)
          = tablePPV (expectedConfusion κ x0 source report called)
        ↔ ∫ y, ((stateLaw y target).pushforward report).binaryCaseMass Prod.snd ∂(κ x0)
          = ∫ y, ((stateLaw y source).pushforward report).binaryCaseMass Prod.snd ∂(κ x0)) := by
  have htotalSource :=
    tableCaseMass_add_tableControlMass_expectedConfusion κ x0 source report called
  have htotalTarget :=
    tableCaseMass_add_tableControlMass_expectedConfusion κ x0 target report called
  rw [← tableCaseMass_expectedConfusion κ x0 source report called] at hsource0 hsource1 ⊢
  rw [← tableCaseMass_expectedConfusion κ x0 target report called] at htarget0 htarget1 ⊢
  have hcontrolSource : tableControlMass (expectedConfusion κ x0 source report called) ≠ 0 :=
    fun h ↦ hsource1 (by linarith)
  have hcontrolTarget : tableControlMass (expectedConfusion κ x0 target report called) ≠ 0 :=
    fun h ↦ htarget1 (by linarith)
  exact ⟨tablePPV_ascertainedTable_eq_of_rates_eq c _ _ hcontrolTarget hcontrolSource
      hsensitivity hspecificity,
    tablePPV_eq_iff_tableCaseMass_eq _ _ htotalTarget htotalSource htarget0 hsource0
      hcontrolTarget hcontrolSource hsensitivity hspecificity hsensitivity0 hspecificity1
      hcalledTarget hcalledSource⟩

/-! ## The ascertained decision report under any process law -/

/-- **An ascertained decision report**: at every case fraction, the cohort confusion table of every
population and the portability of every metric of it between every source and target. -/
structure AscertainedDecisionReport (Population : Type*) where
  /-- The cohort confusion table of each population at each case fraction. -/
  table : ℝ → Population → Bool × Bool → ℝ
  /-- The portability of each metric of the cohort table at each case fraction, from each source
  to each target. -/
  portability : ℝ → Population → Population → ((Bool × Bool → ℝ) → ℝ) → ℝ

/-- **The ascertained decision report** of a rule `called` on a report map `hap ↦ (s, b)` under a
kernel started at `x₀`.  The portability of a metric of the cohort table is the population
portability of that metric read through the cohort reweighting. -/
def ascertainedDecisionReport
    (κ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele))
    (x0 : FrequencyState Deme Locus Allele) (report : FullHaplotype Locus Allele → Score × Bool)
    (called : Score → Bool) : AscertainedDecisionReport Deme where
  table c deme := ascertainedConfusion κ x0 deme report called c
  portability c source target metric :=
    expectedMetricPortability κ x0 source target report called
      fun cells ↦ metric (ascertainedTable c cells)

/-- **The ascertained report is a function of the decision report.**  Two process laws that give a
rule the same decision report give it the same ascertained decision report.

Assumes: equal decision reports. -/
theorem ascertainedDecisionReport_eq_of_decisionReport_eq
    {κ₁ κ₂ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele)}
    {x₁ x₂ : FrequencyState Deme Locus Allele}
    (report : FullHaplotype Locus Allele → Score × Bool) (called : Score → Bool)
    (h : decisionReport κ₁ x₁ report called = decisionReport κ₂ x₂ report called) :
    ascertainedDecisionReport κ₁ x₁ report called
      = ascertainedDecisionReport κ₂ x₂ report called := by
  have hconfusion : ∀ deme : Deme, expectedConfusion κ₁ x₁ deme report called
      = expectedConfusion κ₂ x₂ deme report called := fun deme ↦ by
    have htable := congrFun (congrArg DecisionReport.table h) deme
    exact htable
  simp only [ascertainedDecisionReport, ascertainedConfusion, expectedMetricPortability,
    hconfusion]

/-- **Degree one fixes the ascertained decision report under any process law.**  Two process laws
that agree, from their initial states, on every frequency polynomial of total degree at most one
give every rule on every report map the same cohort table at every case fraction in every deme,
and the same portability of every metric of it.

Assumes: agreement up to degree one. -/
theorem ascertainedDecisionReport_eq_of_polynomialsAgreeAt_one
    {κ₁ κ₂ : Kernel (FrequencyState Deme Locus Allele) (FrequencyState Deme Locus Allele)}
    {x₁ x₂ : FrequencyState Deme Locus Allele} (h : PolynomialsAgreeAt 1 κ₁ κ₂ x₁ x₂)
    (report : FullHaplotype Locus Allele → Score × Bool) (called : Score → Bool) :
    ascertainedDecisionReport κ₁ x₁ report called
      = ascertainedDecisionReport κ₂ x₂ report called :=
  ascertainedDecisionReport_eq_of_decisionReport_eq report called
    (decisionReport_eq_of_polynomialsAgreeAt_one h report called)

/-- **An event history and a rate history with equal budget-1 moments give one ascertained
report.**  If a history of epochs, splits and pulses from `x₁` and a rate history with continuous
dual generator from `x₂` have equal propagated budget-1 moments, every rule on every report map has
the same ascertained decision report under both.

Assumes: equal propagated budget-1 moments. -/
theorem ascertainedDecisionReport_historyEvent_eq_rateHistory (ℓ₀ : Locus)
    (hap₀ : FullHaplotype Locus Allele)
    (events : List ((NeutralRates Deme Locus Allele × ℝ≥0) ⊕ PulseMatrix Deme))
    {rates : ℝ → NeutralRates Deme Locus Allele} {T : ℝ} (hT : 0 ≤ T)
    (hcontinuous : ∀ capacity : Locus → ℕ,
      ContinuousOn (fun t ↦ dualGenerator (rates t) capacity) (Set.Icc 0 T))
    {x₁ x₂ : FrequencyState Deme Locus Allele}
    (hmoments : historyEventPropagator (fun _ ↦ 1) events *ᵥ budgetMomentFeature (fun _ ↦ 1) x₁
      = rateHistoryDualPropagator rates (fun _ ↦ 1) T *ᵥ budgetMomentFeature (fun _ ↦ 1) x₂)
    (report : FullHaplotype Locus Allele → Score × Bool) (called : Score → Bool) :
    ascertainedDecisionReport (historyEventKernel ℓ₀ hap₀ events) x₁ report called
      = ascertainedDecisionReport (rateHistoryKernel rates ℓ₀ hap₀ hT hcontinuous) x₂ report
        called :=
  ascertainedDecisionReport_eq_of_decisionReport_eq report called
    (decisionReport_historyEvent_eq_rateHistory ℓ₀ hap₀ events hT hcontinuous hmoments report
      called)

end

end Descent.Portability.EndToEndAscertainedDecision
