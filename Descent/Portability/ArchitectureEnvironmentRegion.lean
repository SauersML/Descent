/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.UniversalMetricIdentification
import Mathlib.Data.Set.Prod
import Mathlib.Order.Interval.Set.Basic

assert_below Descent.Decision Descent.Program

/-!
# The exact region swept by a binary architecture and a binary environment

This is NOTE2 §3.2, equations (9) and (10). A binary architecture indicator with
`P(A = 1) = α` and an independent binary environment indicator with `P(E = 1) = η` put mass
`cellWeight α η` on the four corners, which is NOTE2 (9). Each reported quantity is a ratio
`conditionalMean num den α η` of two corner-averaged accumulators.

Three things are proved. First, `conditionalMean_eq_corner_combination`: whenever every
corner denominator is strictly positive the report is a convex combination of the four corner
ratios `num c / den c`, with the weights `cornerWeight` proportional to `π_ae d_ae`; hence
`le_conditionalMean` and `conditionalMean_le` bound it by any bound on the corner ratios, and
`conditionalMean_corner` shows the four corners are attained at `α, η ∈ {0, 1}`, so the exact
minimum and maximum over the whole square are corner values.

Second, the determinant characterization of independence: `cellWeight_det` shows a product
table has vanishing determinant, and `det_zero_iff_eq_cellWeight` shows the converse for any
unit-mass table, with the parameters read off as the two marginals. The converse is proved
here without any nonnegativity hypothesis, which is stronger than the note's statement; the
nonnegativity is only needed to know that the recovered marginals lie in the unit interval,
and that is where `mem_unitInterval_of_nonneg` supplies it.

Third, `jointRegion_eq_image` proves that the set (10) — nonnegative unit-mass tables with
vanishing determinant, together with the linear definedness equations `r_j Σ d_j t = Σ n_j t`
for a finite family of reported quantities — is exactly the image of the unit square under
the joint report map. This is an exact region, not an outer bound.

Scope. Only the two-by-two independent case of NOTE2 §3.2 is formalized. The general
semialgebraic statement of NOTE2 Theorem 2 is not: real quantifier elimination and
semialgebraic sets are absent from this Mathlib pin, exactly as the note anticipates.
`architectureLaw` exhibits `cellWeight` as a corpus `FiniteReportLaw` on the four corners.

## Empirical status

None. The bodies here are algebra: `num` and `den` are arbitrary supplied corner
accumulators, and every statement is an identity or inequality in `α` and `η` alone.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.ArchitectureEnvironmentRegion

noncomputable section

/-! ### The independent architecture/environment mixture (9) -/

/-- The four mixture weights of NOTE2 (9): an architecture indicator of mean `α` and an
independent environment indicator of mean `η`. -/
def cellWeight (α η : ℝ) : Bool × Bool → ℝ
  | (false, false) => (1 - α) * (1 - η)
  | (false, true) => (1 - α) * η
  | (true, false) => α * (1 - η)
  | (true, true) => α * η

/-- The mixture weights sum to one for every parameter pair. -/
theorem cellWeight_sum (α η : ℝ) : ∑ c, cellWeight α η c = 1 := by
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, cellWeight]
  ring

/-- The mixture weights are nonnegative on the unit square. -/
theorem cellWeight_nonneg (α η : ℝ) (h0a : 0 ≤ α) (h1a : α ≤ 1) (h0e : 0 ≤ η)
    (h1e : η ≤ 1) (c : Bool × Bool) : 0 ≤ cellWeight α η c := by
  rcases c with ⟨a, e⟩
  cases a <;> cases e <;> simp only [cellWeight] <;>
    exact mul_nonneg (by linarith) (by linarith)

/-- The independent architecture/environment mixture as a corpus finite report law. -/
def architectureLaw (α η : ℝ) (h0a : 0 ≤ α) (h1a : α ≤ 1) (h0e : 0 ≤ η) (h1e : η ≤ 1) :
    FiniteReportLaw (Bool × Bool) where
  mass := cellWeight α η
  mass_nonneg := cellWeight_nonneg α η h0a h1a h0e h1e
  mass_sum := cellWeight_sum α η

/-- The report law of the mixture carries exactly the weights of NOTE2 (9). -/
theorem architectureLaw_mass (α η : ℝ) (h0a : 0 ≤ α) (h1a : α ≤ 1) (h0e : 0 ≤ η)
    (h1e : η ≤ 1) (c : Bool × Bool) :
    (architectureLaw α η h0a h1a h0e h1e).mass c = cellWeight α η c := rfl

/-! ### The mixed ratio and its corner decomposition -/

/-- The mixture-averaged denominator `d_j(α, η)` of NOTE2 (9). -/
def mixtureDenominator (den : Bool × Bool → ℝ) (α η : ℝ) : ℝ :=
  ∑ c, cellWeight α η c * den c

/-- The mixture-averaged numerator `n_j(α, η)` of NOTE2 (9). -/
def mixtureNumerator (num : Bool × Bool → ℝ) (α η : ℝ) : ℝ :=
  ∑ c, cellWeight α η c * num c

/-- The reported conditional mean `n_j(α, η) / d_j(α, η)` of NOTE2 (9). -/
def conditionalMean (num den : Bool × Bool → ℝ) (α η : ℝ) : ℝ :=
  mixtureNumerator num α η / mixtureDenominator den α η

/-- With every corner denominator strictly positive the mixed denominator is strictly
positive, so the reported conditional mean is defined everywhere on the square. -/
theorem mixtureDenominator_pos (den : Bool × Bool → ℝ) (hden : ∀ c, 0 < den c) (α η : ℝ)
    (h0a : 0 ≤ α) (h1a : α ≤ 1) (h0e : 0 ≤ η) (h1e : η ≤ 1) :
    0 < mixtureDenominator den α η := by
  have hnn : ∀ c ∈ (Finset.univ : Finset (Bool × Bool)), 0 ≤ cellWeight α η c * den c :=
    fun c _ ↦ mul_nonneg (cellWeight_nonneg α η h0a h1a h0e h1e c) (hden c).le
  rcases lt_or_eq_of_le (Finset.sum_nonneg hnn) with hpos | heq
  · exact hpos
  · exfalso
    have hzero := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp heq.symm
    have hw : ∀ c, cellWeight α η c = 0 := by
      intro c
      rcases mul_eq_zero.mp (hzero c (Finset.mem_univ c)) with h | h
      · exact h
      · exact absurd h (hden c).ne'
    have hone : (1 : ℝ) = 0 := by
      rw [← cellWeight_sum α η]
      exact Finset.sum_eq_zero fun c _ ↦ hw c
    norm_num at hone

/-- The convex weight that the corner ratio `num c / den c` carries in the mixed report:
`π_ae d_ae / Σ π d`. -/
def cornerWeight (den : Bool × Bool → ℝ) (α η : ℝ) (c : Bool × Bool) : ℝ :=
  cellWeight α η c * den c / mixtureDenominator den α η

/-- The corner weights are nonnegative. -/
theorem cornerWeight_nonneg (den : Bool × Bool → ℝ) (hden : ∀ c, 0 < den c) (α η : ℝ)
    (h0a : 0 ≤ α) (h1a : α ≤ 1) (h0e : 0 ≤ η) (h1e : η ≤ 1) (c : Bool × Bool) :
    0 ≤ cornerWeight den α η c :=
  div_nonneg (mul_nonneg (cellWeight_nonneg α η h0a h1a h0e h1e c) (hden c).le)
    (mixtureDenominator_pos den hden α η h0a h1a h0e h1e).le

/-- The corner weights sum to one. -/
theorem cornerWeight_sum (den : Bool × Bool → ℝ) (hden : ∀ c, 0 < den c) (α η : ℝ)
    (h0a : 0 ≤ α) (h1a : α ≤ 1) (h0e : 0 ≤ η) (h1e : η ≤ 1) :
    ∑ c, cornerWeight den α η c = 1 := by
  have hpos := mixtureDenominator_pos den hden α η h0a h1a h0e h1e
  simp only [cornerWeight]
  rw [← Finset.sum_div]
  exact div_self hpos.ne'

/-- **NOTE2 §3.2, the convex-combination form of (9).** The reported conditional mean is a
convex combination of the four corner ratios, weighted by `π_ae d_ae`. -/
theorem conditionalMean_eq_corner_combination (num den : Bool × Bool → ℝ)
    (hden : ∀ c, 0 < den c) (α η : ℝ) (h0a : 0 ≤ α) (h1a : α ≤ 1) (h0e : 0 ≤ η)
    (h1e : η ≤ 1) :
    conditionalMean num den α η = ∑ c, cornerWeight den α η c * (num c / den c) := by
  have hpos := mixtureDenominator_pos den hden α η h0a h1a h0e h1e
  have hterm : ∀ c : Bool × Bool, cornerWeight den α η c * (num c / den c) =
      cellWeight α η c * num c / mixtureDenominator den α η := by
    intro c
    have hc := (hden c).ne'
    simp only [cornerWeight]
    field_simp
  rw [Finset.sum_congr rfl fun c _ ↦ hterm c, ← Finset.sum_div]
  rfl

/-- Any upper bound on the four corner ratios bounds the report on the whole square. -/
theorem conditionalMean_le (num den : Bool × Bool → ℝ) (hden : ∀ c, 0 < den c) (α η : ℝ)
    (h0a : 0 ≤ α) (h1a : α ≤ 1) (h0e : 0 ≤ η) (h1e : η ≤ 1) (bound : ℝ)
    (hbound : ∀ c, num c / den c ≤ bound) : conditionalMean num den α η ≤ bound := by
  rw [conditionalMean_eq_corner_combination num den hden α η h0a h1a h0e h1e]
  calc ∑ c, cornerWeight den α η c * (num c / den c)
      ≤ ∑ c : Bool × Bool, cornerWeight den α η c * bound :=
        Finset.sum_le_sum fun c _ ↦
          mul_le_mul_of_nonneg_left (hbound c)
            (cornerWeight_nonneg den hden α η h0a h1a h0e h1e c)
    _ = bound := by
        rw [← Finset.sum_mul, cornerWeight_sum den hden α η h0a h1a h0e h1e, one_mul]

/-- Any lower bound on the four corner ratios bounds the report on the whole square. -/
theorem le_conditionalMean (num den : Bool × Bool → ℝ) (hden : ∀ c, 0 < den c) (α η : ℝ)
    (h0a : 0 ≤ α) (h1a : α ≤ 1) (h0e : 0 ≤ η) (h1e : η ≤ 1) (bound : ℝ)
    (hbound : ∀ c, bound ≤ num c / den c) : bound ≤ conditionalMean num den α η := by
  rw [conditionalMean_eq_corner_combination num den hden α η h0a h1a h0e h1e]
  calc bound
      = ∑ c : Bool × Bool, cornerWeight den α η c * bound := by
        rw [← Finset.sum_mul, cornerWeight_sum den hden α η h0a h1a h0e h1e, one_mul]
    _ ≤ ∑ c, cornerWeight den α η c * (num c / den c) :=
        Finset.sum_le_sum fun c _ ↦
          mul_le_mul_of_nonneg_left (hbound c)
            (cornerWeight_nonneg den hden α η h0a h1a h0e h1e c)

/-- **The extremes are attained at corners.** At `α, η ∈ {0, 1}` the report is exactly the
corresponding corner ratio, so the bounds above are sharp. -/
theorem conditionalMean_corner (num den : Bool × Bool → ℝ) (a e : Bool) :
    conditionalMean num den (if a then 1 else 0) (if e then 1 else 0) =
      num (a, e) / den (a, e) := by
  cases a <;> cases e <;>
    norm_num [conditionalMean, mixtureNumerator, mixtureDenominator, Fintype.sum_prod_type,
      Fintype.sum_bool, cellWeight]

/-! ### The determinant characterization of independence (10) -/

/-- The total mass of a two-by-two table written out over its four cells. -/
theorem sum_cells (table : Bool × Bool → ℝ) :
    ∑ c, table c = table (false, false) + table (false, true) +
      (table (true, false) + table (true, true)) := by
  simp only [Fintype.sum_prod_type, Fintype.sum_bool]
  ring

/-- A product table has vanishing determinant. -/
theorem cellWeight_det (α η : ℝ) :
    cellWeight α η (false, false) * cellWeight α η (true, true) =
      cellWeight α η (false, true) * cellWeight α η (true, false) := by
  simp only [cellWeight]
  ring

/-- The two marginals of a product table recover its parameters. -/
theorem cellWeight_marginals (α η : ℝ) :
    cellWeight α η (true, false) + cellWeight α η (true, true) = α ∧
      cellWeight α η (false, true) + cellWeight α η (true, true) = η := by
  constructor <;> · simp only [cellWeight]; ring

/-- **NOTE2 (10), the independence step.** A unit-mass two-by-two table with vanishing
determinant is the product of its marginals. No nonnegativity is needed for this identity. -/
theorem det_zero_iff_eq_cellWeight (table : Bool × Bool → ℝ)
    (hsum : ∑ c, table c = 1) :
    table (false, false) * table (true, true) =
        table (false, true) * table (true, false) ↔
      table = cellWeight (table (true, false) + table (true, true))
        (table (false, true) + table (true, true)) := by
  have hexpand : table (false, false) + table (false, true) +
      (table (true, false) + table (true, true)) = 1 := (sum_cells table).symm.trans hsum
  constructor
  · intro hdet
    funext c
    rcases c with ⟨a, e⟩
    cases a <;> cases e <;> simp only [cellWeight]
    · linear_combination (1 - table (true, true)) * hexpand + hdet
    · linear_combination table (true, true) * hexpand - hdet
    · linear_combination table (true, true) * hexpand - hdet
    · linear_combination (-table (true, true)) * hexpand + hdet
  · intro hprod
    rw [hprod]
    exact cellWeight_det _ _

/-- The marginals of a nonnegative unit-mass table lie in the unit interval, which is what
makes the recovered parameters legitimate architecture and environment probabilities. -/
theorem marginal_mem_unitInterval (table : Bool × Bool → ℝ) (hnn : ∀ c, 0 ≤ table c)
    (hsum : ∑ c, table c = 1) :
    0 ≤ table (true, false) + table (true, true) ∧
      table (true, false) + table (true, true) ≤ 1 ∧
      0 ≤ table (false, true) + table (true, true) ∧
      table (false, true) + table (true, true) ≤ 1 := by
  have hexpand : table (false, false) + table (false, true) +
      (table (true, false) + table (true, true)) = 1 := (sum_cells table).symm.trans hsum
  have h1 := hnn (false, false)
  have h2 := hnn (false, true)
  have h3 := hnn (true, false)
  have h4 := hnn (true, true)
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

/-! ### The joint attainable region (10) -/

/-- **NOTE2 (10).** The joint region: report vectors realized by some nonnegative unit-mass
table with vanishing determinant, through the definedness equations
`r_j Σ d_j t = Σ n_j t`. -/
def jointRegion {J : Type} [Fintype J] (num den : J → Bool × Bool → ℝ) : Set (J → ℝ) :=
  {report | ∃ table : Bool × Bool → ℝ, (∀ c, 0 ≤ table c) ∧ (∑ c, table c = 1) ∧
    table (false, false) * table (true, true) =
      table (false, true) * table (true, false) ∧
    ∀ j, report j * ∑ c, table c * den j c = ∑ c, table c * num j c}

/-- **NOTE2 (10) is exact.** The joint region is precisely the image of the unit square under
the joint report map, so the semialgebraic description and the parametric description agree
in this case. -/
theorem jointRegion_eq_image {J : Type} [Fintype J] (num den : J → Bool × Bool → ℝ)
    (hden : ∀ j c, 0 < den j c) :
    jointRegion num den =
      (fun p : ℝ × ℝ ↦ fun j ↦ conditionalMean (num j) (den j) p.1 p.2) ''
        (Set.Icc 0 1 ×ˢ Set.Icc 0 1) := by
  ext report
  constructor
  · rintro ⟨table, hnn, hsum, hdet, heq⟩
    obtain ⟨alpha, eta, h0a, h1a, h0e, h1e, hprod⟩ :
        ∃ alpha eta : ℝ, 0 ≤ alpha ∧ alpha ≤ 1 ∧ 0 ≤ eta ∧ eta ≤ 1 ∧
          table = cellWeight alpha eta := by
      obtain ⟨ha0, ha1, he0, he1⟩ := marginal_mem_unitInterval table hnn hsum
      exact ⟨_, _, ha0, ha1, he0, he1, (det_zero_iff_eq_cellWeight table hsum).mp hdet⟩
    refine ⟨(alpha, eta), ⟨Set.mem_Icc.mpr ⟨h0a, h1a⟩, Set.mem_Icc.mpr ⟨h0e, h1e⟩⟩, ?_⟩
    funext j
    have hdpos := mixtureDenominator_pos (den j) (hden j) alpha eta h0a h1a h0e h1e
    have hj := heq j
    rw [hprod] at hj
    have hnum : mixtureNumerator (num j) alpha eta =
        report j * mixtureDenominator (den j) alpha eta := hj.symm
    show mixtureNumerator (num j) alpha eta / mixtureDenominator (den j) alpha eta =
      report j
    rw [hnum, mul_div_assoc, div_self hdpos.ne', mul_one]
  · rintro ⟨⟨alpha, eta⟩, hmem, rfl⟩
    obtain ⟨halpha, heta⟩ := hmem
    obtain ⟨h0a, h1a⟩ := Set.mem_Icc.mp halpha
    obtain ⟨h0e, h1e⟩ := Set.mem_Icc.mp heta
    refine ⟨cellWeight alpha eta, cellWeight_nonneg alpha eta h0a h1a h0e h1e,
      cellWeight_sum alpha eta, cellWeight_det alpha eta, fun j ↦ ?_⟩
    have hdpos := mixtureDenominator_pos (den j) (hden j) alpha eta h0a h1a h0e h1e
    show mixtureNumerator (num j) alpha eta / mixtureDenominator (den j) alpha eta *
      mixtureDenominator (den j) alpha eta = mixtureNumerator (num j) alpha eta
    rw [div_mul_eq_mul_div, mul_div_assoc, div_self hdpos.ne', mul_one]

end

end Descent.Portability.ArchitectureEnvironmentRegion
