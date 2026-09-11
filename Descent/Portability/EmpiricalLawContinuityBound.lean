/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.EmpiricalLawLipschitzBound
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.SpecificLimits.Basic

assert_below Descent.Decision Descent.Program

/-!
# A replica bound for every continuous functional of a population law

NOTE2 §7.1 extends the Lipschitz bound (31) to a general continuous functional on the
probability simplex through its modulus of continuity, by splitting on whether the empirical
law of the replica block lies within a radius of the population law. This module proves that
split, the explicit bound it yields, and the uniform convergence it gives for every
continuous functional.

The hypothesis class is `ModulusOfContinuityOn functional radius modulus`: over pairs of
simplex points at total deviation at most `radius`, the functional oscillates by at most
`modulus`. `abs_sub_le_modulus_add_indicator` is the split: between two simplex points the
oscillation is at most the modulus plus twice the bound on the functional times the indicator
that the points are farther apart than the radius. `deviation_probability_le` bounds the
probability of that event by Markov's inequality applied to
`EmpiricalLawLipschitzBound.expectation_deviation_sum_le`, the replica bound behind (31).
Together they give `abs_expectation_functional_sub_le_modulus`: the bias of the functional
read off `count` replicas is at most the modulus plus twice the bound times the root of
`(m - 1) / count` over the radius. Mixing over a shared study context leaves the same bound,
through the corpus `BellmanReportBounds.abs_expectation_sub_le`.

For a functional continuous on the simplex, compactness supplies a bound and a modulus at
every radius, and `exists_count_abs_expectation_functional_sub_le` shows that the bias falls
below any tolerance simultaneously for every population law once the replica count is large
enough. This is the classical Bernstein-type argument; what is new here is only that it runs
on the corpus replica law. The Lipschitz class of (31) is the special case
`modulusOfContinuityOn_of_lipschitzInL1`, with modulus proportional to the radius, and the
coordinate readout inhabits the class with no hypothesis.

Not formalized here: the choice of the radius that optimizes the bound for a specified
modulus, which is left to the caller; functionals that are continuous only off the simplex;
and category spaces beyond a finite alphabet.

## Empirical status

None. The bodies here are algebra and topology: the population law and the functional are
supplied inputs, and every bound follows from a pointwise split, Markov's inequality, the
corpus replica bound and compactness of the simplex, so no measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.EmpiricalLawContinuityBound

open Filter EmpiricalLawLipschitzBound

open scoped BigOperators Topology

noncomputable section

variable {Category : Type*} [Fintype Category]

/-- NOTE2 §7.1: `modulus` bounds the oscillation of a functional over pairs of points of the
probability simplex whose total deviation is at most `radius`. -/
def ModulusOfContinuityOn (functional : (Category → ℝ) → ℝ) (radius modulus : ℝ) : Prop :=
  ∀ first ∈ stdSimplex ℝ Category, ∀ second ∈ stdSimplex ℝ Category,
    ∑ category, |first category - second category| ≤ radius →
      |functional first - functional second| ≤ modulus

/-- Reading off one category share oscillates by at most the radius at every radius, so the
hypothesis class is inhabited by an explicit functional with no hypothesis. -/
theorem modulusOfContinuityOn_coordinate (category : Category) (radius : ℝ) :
    ModulusOfContinuityOn (fun law : Category → ℝ ↦ law category) radius radius := by
  intro first _ second _ hclose
  have hcoordinate := lipschitzInL1_coordinate category first second
  rw [one_mul] at hcoordinate
  exact le_trans hcoordinate hclose

/-- The Lipschitz class of NOTE2 (31) lies inside the continuous class of §7.1: a functional
that is Lipschitz for the total deviation has modulus proportional to the radius. -/
theorem modulusOfContinuityOn_of_lipschitzInL1 {functional : (Category → ℝ) → ℝ}
    {constant : ℝ} (hconstant : 0 ≤ constant)
    (hlipschitz : LipschitzInL1 functional constant) (radius : ℝ) :
    ModulusOfContinuityOn functional radius (constant * radius) := by
  intro first _ second _ hclose
  exact le_trans (hlipschitz first second) (mul_le_mul_of_nonneg_left hclose hconstant)

/-- A population law is a point of the probability simplex. -/
theorem mass_mem_stdSimplex (q : FiniteReportLaw Category) : q.mass ∈ stdSimplex ℝ Category :=
  ⟨q.mass_nonneg, q.mass_sum⟩

/-- The empirical law of a nonempty replica block is a point of the probability simplex. -/
theorem empiricalMass_mem_stdSimplex {count : ℕ} (hcount : 0 < count)
    (draw : Fin count → Category) : empiricalMass draw ∈ stdSimplex ℝ Category := by
  have hne : (count : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hcount.ne'
  refine ⟨fun category ↦ ?_, ?_⟩
  · refine div_nonneg (Finset.sum_nonneg fun replica _ ↦ ?_) (Nat.cast_nonneg count)
    simp only [FiniteReportLaw.singletonMetric]
    split_ifs <;> norm_num
  · have hrow : ∀ replica : Fin count,
        ∑ category, FiniteReportLaw.singletonMetric category (draw replica) = 1 := by
      intro replica
      rw [Finset.sum_eq_single (draw replica)]
      · simp [FiniteReportLaw.singletonMetric]
      · intro category _ hdifferent
        simp [FiniteReportLaw.singletonMetric, Ne.symm hdifferent]
      · intro hnot
        exact absurd (Finset.mem_univ _) hnot
    simp only [empiricalMass, ← Finset.sum_div]
    rw [Finset.sum_comm]
    simp only [hrow]
    simp [hne]

/-- NOTE2 §7.1, the split on the total deviation. When two simplex points lie within the
radius the oscillation is at most the modulus, and otherwise it is at most twice the bound on
the functional. Assumes: `ModulusOfContinuityOn functional radius modulus` at a nonnegative
radius, and a bound on the functional over the simplex. -/
theorem abs_sub_le_modulus_add_indicator {functional : (Category → ℝ) → ℝ}
    {radius modulus bound : ℝ} (hradius : 0 ≤ radius)
    (hmodulus : ModulusOfContinuityOn functional radius modulus)
    (hbound : ∀ law ∈ stdSimplex ℝ Category, |functional law| ≤ bound)
    {first second : Category → ℝ} (hfirst : first ∈ stdSimplex ℝ Category)
    (hsecond : second ∈ stdSimplex ℝ Category) :
    |functional first - functional second| ≤
      modulus + 2 * bound *
        (if radius < ∑ category, |first category - second category| then 1 else 0) := by
  have hmodulusNonneg : 0 ≤ modulus := by
    have hself := hmodulus second hsecond second hsecond (by simpa using hradius)
    simpa using hself
  split_ifs with hfar
  · obtain ⟨hfirstBelow, hfirstAbove⟩ := abs_le.mp (hbound first hfirst)
    obtain ⟨hsecondBelow, hsecondAbove⟩ := abs_le.mp (hbound second hsecond)
    rw [mul_one, abs_le]
    constructor <;> linarith
  · rw [mul_zero, add_zero]
    exact hmodulus first hfirst second hsecond (not_lt.mp hfar)

/-- NOTE2 §7.1, the probability of the split event. By Markov's inequality and the replica
bound behind NOTE2 (31), the empirical law of `count` replicas lies farther than `radius` from
the population law with probability at most the root of `(m - 1) / count` over the radius. -/
theorem deviation_probability_le (count : ℕ) (hcount : 0 < count) (witness : Category)
    (q : FiniteReportLaw Category) {radius : ℝ} (hradius : 0 < radius) :
    (replicaLaw count q).expectation (fun draw ↦
        if radius < ∑ category, |empiricalMass draw category - q.mass category| then 1 else 0) ≤
      Real.sqrt (((Fintype.card Category : ℝ) - 1) / count) / radius := by
  have hscaleNonneg : 0 ≤ 1 / radius := one_div_nonneg.mpr hradius.le
  have hmarkov : ∀ draw : Fin count → Category,
      (if radius < ∑ category, |empiricalMass draw category - q.mass category| then (1 : ℝ)
        else 0) ≤
        1 / radius * ∑ category, |empiricalMass draw category - q.mass category| := by
    intro draw
    split_ifs with hfar
    · rw [one_div, inv_mul_eq_div, le_div_iff₀ hradius, one_mul]
      exact hfar.le
    · exact mul_nonneg hscaleNonneg (Finset.sum_nonneg fun _ _ ↦ abs_nonneg _)
  calc (replicaLaw count q).expectation (fun draw ↦
        if radius < ∑ category, |empiricalMass draw category - q.mass category| then 1 else 0)
      ≤ (replicaLaw count q).expectation (fun draw ↦
          1 / radius * ∑ category, |empiricalMass draw category - q.mass category|) :=
        BellmanReportBounds.expectation_mono _ _ _ hmarkov
    _ = 1 / radius * (replicaLaw count q).expectation (fun draw ↦
          ∑ category, |empiricalMass draw category - q.mass category|) := by
        simp only [FiniteReportLaw.expectation]
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun draw _ ↦ by ring
    _ ≤ 1 / radius * Real.sqrt (((Fintype.card Category : ℝ) - 1) / count) :=
        mul_le_mul_of_nonneg_left (expectation_deviation_sum_le count hcount witness q)
          hscaleNonneg
    _ = Real.sqrt (((Fintype.card Category : ℝ) - 1) / count) / radius := by ring

/-- NOTE2 §7.1: the bias of a functional with a modulus of continuity, read off a block of
`count` conditionally independent replicas, is at most the modulus plus twice the bound on
the functional times the root of `(m - 1) / count` over the radius. The bound is uniform over
population laws. Assumes: `ModulusOfContinuityOn functional radius modulus` at a positive
radius, and a bound on the functional over the simplex. -/
theorem abs_expectation_functional_sub_le_modulus (count : ℕ) (hcount : 0 < count)
    (witness : Category) (q : FiniteReportLaw Category) {functional : (Category → ℝ) → ℝ}
    {radius modulus bound : ℝ} (hradius : 0 < radius)
    (hmodulus : ModulusOfContinuityOn functional radius modulus)
    (hbound : ∀ law ∈ stdSimplex ℝ Category, |functional law| ≤ bound) :
    |(replicaLaw count q).expectation (fun draw ↦ functional (empiricalMass draw)) -
        functional q.mass| ≤
      modulus + 2 * bound *
        (Real.sqrt (((Fintype.card Category : ℝ) - 1) / count) / radius) := by
  have hboundNonneg : 0 ≤ bound :=
    le_trans (abs_nonneg _) (hbound q.mass (mass_mem_stdSimplex q))
  have hsplit : ∀ draw : Fin count → Category,
      |functional (empiricalMass draw) - functional q.mass| ≤
        modulus + 2 * bound *
          (if radius < ∑ category, |empiricalMass draw category - q.mass category| then 1
            else 0) :=
    fun draw ↦ abs_sub_le_modulus_add_indicator hradius.le hmodulus hbound
      (empiricalMass_mem_stdSimplex hcount draw) (mass_mem_stdSimplex q)
  have hdifference : (replicaLaw count q).expectation
      (fun draw ↦ functional (empiricalMass draw)) - functional q.mass =
      (replicaLaw count q).expectation
        (fun draw ↦ functional (empiricalMass draw) - functional q.mass) := by
    rw [FiniteNumericalCertificate.expectation_difference,
      FiniteIndependentMoments.expectation_const]
  have hlinear : (replicaLaw count q).expectation (fun draw ↦ modulus + 2 * bound *
      (if radius < ∑ category, |empiricalMass draw category - q.mass category| then 1
        else 0)) =
      modulus + 2 * bound * (replicaLaw count q).expectation (fun draw ↦
        if radius < ∑ category, |empiricalMass draw category - q.mass category| then 1
          else 0) := by
    simp only [FiniteReportLaw.expectation, mul_add, Finset.sum_add_distrib]
    rw [← Finset.sum_mul, (replicaLaw count q).mass_sum, one_mul, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun draw _ ↦ by ring
  rw [hdifference]
  refine le_trans (abs_expectation_le_expectation_abs _ _)
    (le_trans (BellmanReportBounds.expectation_mono _ _ _ hsplit) ?_)
  rw [hlinear]
  exact add_le_add_left (mul_le_mul_of_nonneg_left
    (deviation_probability_le count hcount witness q hradius) (by linarith)) modulus

/-- NOTE2 §7.1 with a random population law: mixing the bound over a finite law of shared
study contexts leaves the same bound, because the bound does not depend on the population
law. Assumes: `ModulusOfContinuityOn functional radius modulus` at a positive radius, and a
bound on the functional over the simplex. -/
theorem abs_mixed_expectation_functional_sub_le_modulus {Context : Type*} [Fintype Context]
    (count : ℕ) (hcount : 0 < count) (witness : Category)
    (mixing : FiniteReportLaw Context) (population : Context → FiniteReportLaw Category)
    {functional : (Category → ℝ) → ℝ} {radius modulus bound : ℝ} (hradius : 0 < radius)
    (hmodulus : ModulusOfContinuityOn functional radius modulus)
    (hbound : ∀ law ∈ stdSimplex ℝ Category, |functional law| ≤ bound) :
    |mixing.expectation (fun context ↦
        (replicaLaw count (population context)).expectation
          (fun draw ↦ functional (empiricalMass draw))) -
      mixing.expectation (fun context ↦ functional (population context).mass)| ≤
      modulus + 2 * bound *
        (Real.sqrt (((Fintype.card Category : ℝ) - 1) / count) / radius) :=
  BellmanReportBounds.abs_expectation_sub_le mixing _ _ _ fun context ↦
    abs_expectation_functional_sub_le_modulus count hcount witness (population context)
      hradius hmodulus hbound

/-- NOTE2 §7.1 for a functional continuous on the simplex: once the replica count is large
enough, the bias of the functional read off the replica block is below any positive tolerance
for every population law at once. Compactness of the simplex supplies the bound and the
modulus, and the explicit bound supplies the count. -/
theorem exists_count_abs_expectation_functional_sub_le (witness : Category)
    {functional : (Category → ℝ) → ℝ}
    (hcontinuous : ContinuousOn functional (stdSimplex ℝ Category))
    {tolerance : ℝ} (htolerance : 0 < tolerance) :
    ∃ minimumCount : ℕ, ∀ count, minimumCount ≤ count → ∀ q : FiniteReportLaw Category,
      |(replicaLaw count q).expectation (fun draw ↦ functional (empiricalMass draw)) -
        functional q.mass| ≤ tolerance := by
  obtain ⟨bound, hbound⟩ :=
    (isCompact_stdSimplex (ι := Category)).exists_bound_of_continuousOn hcontinuous
  obtain ⟨gap, hgap, hclose⟩ := Metric.uniformContinuousOn_iff.mp
    ((isCompact_stdSimplex (ι := Category)).uniformContinuousOn_of_continuous hcontinuous)
    (tolerance / 2) (half_pos htolerance)
  have hmodulus : ModulusOfContinuityOn functional (gap / 2) (tolerance / 2) := by
    intro first hfirst second hsecond hdeviation
    have hdist : dist first second < gap := by
      rw [dist_pi_lt_iff hgap]
      intro category
      rw [Real.dist_eq]
      calc |first category - second category|
          ≤ ∑ other, |first other - second other| :=
            Finset.single_le_sum (f := fun other ↦ |first other - second other|)
              (fun _ _ ↦ abs_nonneg _) (Finset.mem_univ category)
        _ ≤ gap / 2 := hdeviation
        _ < gap := half_lt_self hgap
    have hvalues := hclose first hfirst second hsecond hdist
    rw [Real.dist_eq] at hvalues
    exact hvalues.le
  have hboundAbs : ∀ law ∈ stdSimplex ℝ Category, |functional law| ≤ bound :=
    fun law hlaw ↦ by simpa only [Real.norm_eq_abs] using hbound law hlaw
  have hroot := (tendsto_const_div_atTop_nhds_zero_nat
    ((Fintype.card Category : ℝ) - 1)).sqrt
  rw [Real.sqrt_zero] at hroot
  have hlimit := (hroot.div_const (gap / 2)).const_mul (2 * bound)
  rw [zero_div, mul_zero] at hlimit
  obtain ⟨minimumCount, hminimumCount⟩ :=
    eventually_atTop.mp (hlimit.eventually (gt_mem_nhds (half_pos htolerance)))
  refine ⟨max minimumCount 1, fun count hcount q ↦ ?_⟩
  have hpositive : 0 < count :=
    lt_of_lt_of_le Nat.zero_lt_one (le_trans (le_max_right minimumCount 1) hcount)
  have hsmall : 2 * bound *
      (Real.sqrt (((Fintype.card Category : ℝ) - 1) / count) / (gap / 2)) < tolerance / 2 :=
    hminimumCount count (le_trans (le_max_left minimumCount 1) hcount)
  have hmain := abs_expectation_functional_sub_le_modulus count hpositive witness q
    (half_pos hgap) hmodulus hboundAbs
  linarith

/-- NOTE2 §7.1 for a functional continuous on the simplex, with a random population law: the
same replica count makes the mixed bias below the tolerance for every finite law of shared
study contexts. -/
theorem exists_count_abs_mixed_expectation_functional_sub_le {Context : Type*}
    [Fintype Context] (witness : Category) {functional : (Category → ℝ) → ℝ}
    (hcontinuous : ContinuousOn functional (stdSimplex ℝ Category))
    {tolerance : ℝ} (htolerance : 0 < tolerance) :
    ∃ minimumCount : ℕ, ∀ count, minimumCount ≤ count →
      ∀ (mixing : FiniteReportLaw Context) (population : Context → FiniteReportLaw Category),
        |mixing.expectation (fun context ↦
            (replicaLaw count (population context)).expectation
              (fun draw ↦ functional (empiricalMass draw))) -
          mixing.expectation (fun context ↦ functional (population context).mass)| ≤
          tolerance := by
  obtain ⟨minimumCount, hminimumCount⟩ :=
    exists_count_abs_expectation_functional_sub_le witness hcontinuous htolerance
  exact ⟨minimumCount, fun count hcount mixing population ↦
    BellmanReportBounds.abs_expectation_sub_le mixing _ _ _ fun context ↦
      hminimumCount count hcount (population context)⟩

end

end Descent.Portability.EmpiricalLawContinuityBound
