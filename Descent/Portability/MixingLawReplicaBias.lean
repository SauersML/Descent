/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.EmpiricalLawContinuityBound
import Descent.Portability.ReplicaMomentCompleteness

assert_below Descent.Decision Descent.Program

/-!
# The replica bias bound (31) under an arbitrary mixing law on the simplex

NOTE 2 equation (31) bounds the bias `|E F(Q̂_n) - E F(Q)|` of a functional of the empirical law
of `n` conditionally independent replicas by `L_F √((m - 1)/n)`, where the population law `Q` is
itself random with an arbitrary law. `EmpiricalLawLipschitzBound` proves the bound at one
population law and mixes it over a finite law of study contexts, for functionals Lipschitz on the
whole coordinate space, and `EmpiricalLawContinuityBound` does the same for the
modulus-of-continuity form. This module removes both restrictions.

`LipschitzOnSimplex functional constant` asks for the Lipschitz inequality only between points of
the probability simplex, which is where population laws and empirical laws live.
`lipschitzOnSimplex_sq_coordinate` inhabits it with the squared share of one category, and
`lipschitzOnSimplex_classes` shows that the class is strictly larger than
`EmpiricalLawLipschitzBound.LipschitzInL1`: every globally Lipschitz functional is Lipschitz on the
simplex, while no constant makes the squared share Lipschitz on the coordinate space.
`abs_replicaExpectation_sub_le` is (31) at one population law for the simplex class.

A mixing law is an arbitrary probability measure `μ` on the subtype `stdSimplex ℝ Category` of
population laws. `simplexLaw` reads a simplex point as a finite report law, inverting
`ReplicaMomentCompleteness.simplexPoint`, and `replicaExpectation count functional point` is the
finite-cohort expectation of the functional of the empirical law of `count` replicas drawn from
that point. It is continuous in the point for every functional (`continuous_replicaExpectation`),
because the replica masses are products of coordinates. `abs_integral_replicaExpectation_sub_le`
is NOTE 2 (31) under `μ`, `abs_integral_replicaExpectation_sub_le_modulus` is the
modulus-of-continuity form of section 7.1 under `μ`, and
`exists_count_abs_integral_replicaExpectation_sub_le` shows that for a functional continuous on
the simplex one replica count brings the bias below any tolerance under every mixing law at once.

Scope: the category alphabet is finite, and the mixing law is a Borel probability measure on the
simplex. Equation (31) controls the bias of the finite-cohort expectation; it does not identify
that expectation with the population expectation, and nothing here claims otherwise.

## Empirical status

None. The bodies here are measure theory and algebra: the functional and the mixing law are
supplied inputs, and every bound follows from the corpus replica bound, the Lipschitz or modulus
hypothesis, and integration against a probability measure, so no measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.MixingLawReplicaBias

open MeasureTheory EmpiricalLawLipschitzBound EmpiricalLawContinuityBound

noncomputable section

variable {Category : Type*} [Fintype Category]

/-- **NOTE 2 section 7.1, the Lipschitz class on the simplex.** `functional` is Lipschitz with
`constant` for the total deviation between population laws, over pairs of points of the
probability simplex only. -/
def LipschitzOnSimplex (functional : (Category → ℝ) → ℝ) (constant : ℝ) : Prop :=
  ∀ first ∈ stdSimplex ℝ Category, ∀ second ∈ stdSimplex ℝ Category,
    |functional first - functional second| ≤
      constant * ∑ category, |first category - second category|

/-- The squared share of one category is Lipschitz on the simplex with constant two, because
shares lie in the unit interval. This inhabits the class with no hypothesis. -/
theorem lipschitzOnSimplex_sq_coordinate (category : Category) :
    LipschitzOnSimplex (fun law : Category → ℝ ↦ law category ^ 2) 2 := by
  intro first hfirst second hsecond
  have hfirstLe : first category ≤ 1 := by
    rw [← hfirst.2]
    exact Finset.single_le_sum (fun other _ ↦ hfirst.1 other) (Finset.mem_univ category)
  have hsecondLe : second category ≤ 1 := by
    rw [← hsecond.2]
    exact Finset.single_le_sum (fun other _ ↦ hsecond.1 other) (Finset.mem_univ category)
  have hfirstNonneg := hfirst.1 category
  have hsecondNonneg := hsecond.1 category
  have hfactor : |first category ^ 2 - second category ^ 2| =
      |first category + second category| * |first category - second category| := by
    rw [← abs_mul]
    congr 1
    ring
  have hsumLe : |first category + second category| ≤ 2 := by
    rw [abs_of_nonneg (by linarith)]
    linarith
  calc |first category ^ 2 - second category ^ 2|
      = |first category + second category| * |first category - second category| := hfactor
    _ ≤ 2 * |first category - second category| :=
        mul_le_mul_of_nonneg_right hsumLe (abs_nonneg _)
    _ ≤ 2 * ∑ other, |first other - second other| :=
        mul_le_mul_of_nonneg_left
          (Finset.single_le_sum (f := fun other ↦ |first other - second other|)
            (fun other _ ↦ abs_nonneg _) (Finset.mem_univ category)) (by norm_num)

/-- **The simplex class is strictly larger than the class of `EmpiricalLawLipschitzBound`.** Every
functional Lipschitz on the whole coordinate space is Lipschitz on the simplex with the same
constant, and no constant makes the squared share of one category Lipschitz on the coordinate
space, although it is Lipschitz on the simplex by `lipschitzOnSimplex_sq_coordinate`. -/
theorem lipschitzOnSimplex_classes [DecidableEq Category] (category : Category) :
    (∀ (functional : (Category → ℝ) → ℝ) (constant : ℝ),
        LipschitzInL1 functional constant → LipschitzOnSimplex functional constant) ∧
      ∀ constant : ℝ,
        ¬ LipschitzInL1 (fun law : Category → ℝ ↦ law category ^ 2) constant := by
  refine ⟨fun functional constant hglobal first _ second _ ↦ hglobal first second, ?_⟩
  intro constant hglobal
  have hpositive : 0 < |constant| + 1 := by positivity
  have hsum : ∑ other, |(if other = category then |constant| + 1 else 0) -
      (0 : Category → ℝ) other| = |constant| + 1 := by
    rw [Finset.sum_eq_single category]
    · simp [abs_of_pos hpositive]
    · intro other _ hother
      simp [hother]
    · intro hmissing
      exact absurd (Finset.mem_univ category) hmissing
  have hvalue : |(if category = category then |constant| + 1 else 0) ^ 2 -
      (0 : Category → ℝ) category ^ 2| ≤
      constant * ∑ other, |(if other = category then |constant| + 1 else 0) -
        (0 : Category → ℝ) other| :=
    hglobal (fun other ↦ if other = category then |constant| + 1 else 0) 0
  rw [hsum, if_pos rfl, Pi.zero_apply, zero_pow (by norm_num), sub_zero,
    abs_of_nonneg (by positivity)] at hvalue
  nlinarith [le_abs_self constant, abs_nonneg constant]

/-- A point of the probability simplex, read as a finite report law on the categories. -/
def simplexLaw (point : ↥(stdSimplex ℝ Category)) : FiniteReportLaw Category where
  mass := point
  mass_nonneg := point.2.1
  mass_sum := point.2.2

/-- Reading a finite report law on `Fin m` as a simplex point and back returns the law, so
`simplexLaw` inverts `ReplicaMomentCompleteness.simplexPoint`. -/
theorem simplexLaw_simplexPoint (m : ℕ) (law : FiniteReportLaw (Fin m)) :
    simplexLaw (ReplicaMomentCompleteness.simplexPoint m law) = law := rfl

/-- **NOTE 2 section 7.1.** The finite-cohort expectation of a functional of the empirical law of
`count` conditionally independent replicas drawn from the population law at a simplex point. -/
def replicaExpectation (count : ℕ) (functional : (Category → ℝ) → ℝ)
    (point : ↥(stdSimplex ℝ Category)) : ℝ :=
  (replicaLaw count (simplexLaw point)).expectation fun draw ↦ functional (empiricalMass draw)

/-- The finite-cohort expectation is continuous in the population law for every functional,
because the replica masses are products of coordinates of the population law. -/
theorem continuous_replicaExpectation (count : ℕ) (functional : (Category → ℝ) → ℝ) :
    Continuous (replicaExpectation (Category := Category) count functional) := by
  have hcoordinate : ∀ category : Category,
      Continuous fun point : ↥(stdSimplex ℝ Category) ↦ (point : Category → ℝ) category :=
    fun category ↦ (continuous_apply category).comp continuous_subtype_val
  show Continuous fun point : ↥(stdSimplex ℝ Category) ↦
    ∑ draw : Fin count → Category,
      (∏ replica, (point : Category → ℝ) (draw replica)) * functional (empiricalMass draw)
  exact continuous_finset_sum _ fun draw _ ↦
    (continuous_finset_prod _ fun replica _ ↦ hcoordinate (draw replica)).mul continuous_const

/-- A functional Lipschitz on the simplex is continuous on the simplex subtype, because the total
deviation between two simplex points is at most the category count times their uniform
distance. Assumes: `LipschitzOnSimplex functional constant`. -/
theorem continuous_of_lipschitzOnSimplex {functional : (Category → ℝ) → ℝ} {constant : ℝ}
    (hlipschitz : LipschitzOnSimplex functional constant) :
    Continuous fun point : ↥(stdSimplex ℝ Category) ↦ functional point := by
  refine Metric.continuous_iff.mpr fun point ε hε ↦ ?_
  have hscale : 0 < (Fintype.card Category : ℝ) * |constant| + 1 := by positivity
  refine ⟨ε / ((Fintype.card Category : ℝ) * |constant| + 1), div_pos hε hscale,
    fun other hother ↦ ?_⟩
  have hdeviation :
      ∑ category, |(other : Category → ℝ) category - (point : Category → ℝ) category| ≤
        (Fintype.card Category : ℝ) * dist other point := by
    calc ∑ category, |(other : Category → ℝ) category - (point : Category → ℝ) category|
        ≤ ∑ _category : Category, dist other point :=
          Finset.sum_le_sum fun category _ ↦ by
            have hpi := dist_le_pi_dist (other : Category → ℝ) (point : Category → ℝ) category
            rw [Real.dist_eq] at hpi
            exact hpi
      _ = (Fintype.card Category : ℝ) * dist other point := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hbound := hlipschitz _ other.2 _ point.2
  rw [Real.dist_eq]
  calc |functional other - functional point|
      ≤ constant *
          ∑ category, |(other : Category → ℝ) category - (point : Category → ℝ) category| :=
        hbound
    _ ≤ |constant| * ((Fintype.card Category : ℝ) * dist other point) :=
        mul_le_mul (le_abs_self constant) hdeviation
          (Finset.sum_nonneg fun _ _ ↦ abs_nonneg _) (abs_nonneg _)
    _ ≤ ((Fintype.card Category : ℝ) * |constant| + 1) * dist other point := by
        nlinarith [dist_nonneg (x := other) (y := point), abs_nonneg constant]
    _ < ((Fintype.card Category : ℝ) * |constant| + 1) *
          (ε / ((Fintype.card Category : ℝ) * |constant| + 1)) :=
        mul_lt_mul_of_pos_left hother hscale
    _ = ε := by field_simp

/-- **NOTE 2 (31) at one population law, for the simplex class.** The bias of a functional
Lipschitz on the simplex, read off `count` replicas of the population law at a simplex point, is
at most the constant times the root of `(m - 1) / count`. Assumes:
`LipschitzOnSimplex functional constant` with a nonnegative constant. -/
theorem abs_replicaExpectation_sub_le (count : ℕ) (hcount : 0 < count) (witness : Category)
    {functional : (Category → ℝ) → ℝ} {constant : ℝ} (hconstant : 0 ≤ constant)
    (hlipschitz : LipschitzOnSimplex functional constant) (point : ↥(stdSimplex ℝ Category)) :
    |replicaExpectation count functional point - functional point| ≤
      constant * Real.sqrt (((Fintype.card Category : ℝ) - 1) / count) := by
  calc |replicaExpectation count functional point - functional point|
      = |(replicaLaw count (simplexLaw point)).expectation
          (fun draw ↦ functional (empiricalMass draw) - functional point)| := by
        rw [replicaExpectation, FiniteNumericalCertificate.expectation_difference,
          FiniteIndependentMoments.expectation_const]
    _ ≤ (replicaLaw count (simplexLaw point)).expectation
          (fun draw ↦ |functional (empiricalMass draw) - functional point|) :=
        abs_expectation_le_expectation_abs _ _
    _ ≤ (replicaLaw count (simplexLaw point)).expectation (fun draw ↦
          constant * ∑ category,
            |empiricalMass draw category - (simplexLaw point).mass category|) :=
        BellmanReportBounds.expectation_mono _ _ _ fun draw ↦
          hlipschitz _ (empiricalMass_mem_stdSimplex hcount draw) _ point.2
    _ = constant * (replicaLaw count (simplexLaw point)).expectation (fun draw ↦
          ∑ category, |empiricalMass draw category - (simplexLaw point).mass category|) := by
        simp only [FiniteReportLaw.expectation, Finset.mul_sum]
        exact Finset.sum_congr rfl fun draw _ ↦ by ring
    _ ≤ constant * Real.sqrt (((Fintype.card Category : ℝ) - 1) / count) :=
        mul_le_mul_of_nonneg_left
          (expectation_deviation_sum_le count hcount witness (simplexLaw point)) hconstant

/-- A uniform bound on the difference of two continuous readouts of the simplex bounds the
difference of their expectations under every probability measure on the simplex. -/
theorem abs_integral_sub_le_of_forall (μ : Measure ↥(stdSimplex ℝ Category))
    [IsProbabilityMeasure μ] (first second : ↥(stdSimplex ℝ Category) → ℝ)
    (hfirst : Continuous first) (hsecond : Continuous second) (tolerance : ℝ)
    (hbound : ∀ point, |first point - second point| ≤ tolerance) :
    |∫ point, first point ∂μ - ∫ point, second point ∂μ| ≤ tolerance := by
  have hfirstIntegrable : Integrable first μ :=
    BoundedContinuousFunction.integrable μ
      (BoundedContinuousFunction.mkOfCompact ⟨first, hfirst⟩)
  have hsecondIntegrable : Integrable second μ :=
    BoundedContinuousFunction.integrable μ
      (BoundedContinuousFunction.mkOfCompact ⟨second, hsecond⟩)
  rw [← integral_sub hfirstIntegrable hsecondIntegrable, ← Real.norm_eq_abs]
  calc ‖∫ point, first point - second point ∂μ‖ ≤ tolerance * μ.real Set.univ :=
        norm_integral_le_of_norm_le_const (ae_of_all _ fun point ↦ by
          rw [Real.norm_eq_abs]
          exact hbound point)
    _ = tolerance := by rw [measureReal_univ_eq_one, mul_one]

/-- **NOTE 2 (31) under an arbitrary mixing law.** For every probability measure on the simplex of
population laws and every functional Lipschitz on the simplex, the finite-cohort expectation of
the functional of the empirical law of `count` replicas and the expectation of the functional of
the population law differ by at most the constant times the root of `(m - 1) / count`. Assumes:
`LipschitzOnSimplex functional constant` with a nonnegative constant. -/
theorem abs_integral_replicaExpectation_sub_le (μ : Measure ↥(stdSimplex ℝ Category))
    [IsProbabilityMeasure μ] (count : ℕ) (hcount : 0 < count) (witness : Category)
    {functional : (Category → ℝ) → ℝ} {constant : ℝ} (hconstant : 0 ≤ constant)
    (hlipschitz : LipschitzOnSimplex functional constant) :
    |∫ point, replicaExpectation count functional point ∂μ - ∫ point, functional point ∂μ| ≤
      constant * Real.sqrt (((Fintype.card Category : ℝ) - 1) / count) :=
  abs_integral_sub_le_of_forall μ _ _ (continuous_replicaExpectation count functional)
    (continuous_of_lipschitzOnSimplex hlipschitz) _
    (abs_replicaExpectation_sub_le count hcount witness hconstant hlipschitz)

/-- **NOTE 2 section 7.1 under an arbitrary mixing law.** For a functional continuous on the
simplex, with a modulus of continuity at a positive radius and a bound on the simplex, the bias
under every probability measure on the simplex is at most the modulus plus twice the bound times
the root of `(m - 1) / count` over the radius. Assumes:
`ModulusOfContinuityOn functional radius modulus` and the bound. -/
theorem abs_integral_replicaExpectation_sub_le_modulus (μ : Measure ↥(stdSimplex ℝ Category))
    [IsProbabilityMeasure μ] (count : ℕ) (hcount : 0 < count) (witness : Category)
    {functional : (Category → ℝ) → ℝ} {radius modulus bound : ℝ} (hradius : 0 < radius)
    (hmodulus : ModulusOfContinuityOn functional radius modulus)
    (hbound : ∀ law ∈ stdSimplex ℝ Category, |functional law| ≤ bound)
    (hcontinuous : ContinuousOn functional (stdSimplex ℝ Category)) :
    |∫ point, replicaExpectation count functional point ∂μ - ∫ point, functional point ∂μ| ≤
      modulus + 2 * bound * (Real.sqrt (((Fintype.card Category : ℝ) - 1) / count) / radius) :=
  abs_integral_sub_le_of_forall μ _ _ (continuous_replicaExpectation count functional)
    (hcontinuous.comp_continuous continuous_subtype_val fun point ↦ point.2) _ fun point ↦
      abs_expectation_functional_sub_le_modulus count hcount witness (simplexLaw point) hradius
        hmodulus hbound

/-- **NOTE 2 section 7.1 under every mixing law at once.** For a functional continuous on the
simplex, one replica count brings the bias below any positive tolerance under every probability
measure on the simplex of population laws. -/
theorem exists_count_abs_integral_replicaExpectation_sub_le (witness : Category)
    {functional : (Category → ℝ) → ℝ}
    (hcontinuous : ContinuousOn functional (stdSimplex ℝ Category))
    {tolerance : ℝ} (htolerance : 0 < tolerance) :
    ∃ minimumCount : ℕ, ∀ count, minimumCount ≤ count →
      ∀ (μ : Measure ↥(stdSimplex ℝ Category)) [IsProbabilityMeasure μ],
        |∫ point, replicaExpectation count functional point ∂μ -
          ∫ point, functional point ∂μ| ≤ tolerance := by
  obtain ⟨minimumCount, hminimumCount⟩ :=
    exists_count_abs_expectation_functional_sub_le witness hcontinuous htolerance
  refine ⟨minimumCount, fun count hcount μ _ ↦ ?_⟩
  exact abs_integral_sub_le_of_forall μ _ _ (continuous_replicaExpectation count functional)
    (hcontinuous.comp_continuous continuous_subtype_val fun point ↦ point.2) _ fun point ↦
      hminimumCount count hcount (simplexLaw point)

end

end Descent.Portability.MixingLawReplicaBias
