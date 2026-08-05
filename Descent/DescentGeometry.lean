/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.FunctionalDescent

namespace Descent

open scoped BigOperators

/-!
# The section map: descent for conditionals that are actually constructed

`Descent.FunctionalDescent` states descent for an abstract section map
`conditionalSection : Population → Context → Conditional`.  Nothing there builds a conditional
from a law, so its interaction and confounding witnesses are arithmetic identities that a reader
must accept as standing for descent statements.  This module supplies the missing construction —
`fiberConditional`, elementary division by a fiber mass — and then proves the descent statements
themselves.

The organizing object is the **section** over a label value `x`: the set of fiber conditionals
`{fiberConditional π (P i) x}` that the family of populations can realize there.  Descent says
exactly that the functional is constant on each section, and every result below is the geometry
of that set against the functional.

## What is proved

* `functionalDescends_iff_descendsAlong` — the abstract formulation is instantiated: for
  nonnegative laws, `FunctionalDescends` over `fiberConditional` is `DescendsAlong`.
* `descendsAlong_iff_pairwiseConsistent` — descent is decided by pairs of populations plus the
  exact witness-space inhabitation condition, for an arbitrary (not necessarily countable)
  family.  For ordinary inhabited value spaces there is no further finite-resolution gluing
  condition, which is exactly what fails for undominated families over a continuum.
* `kernelSufficient_iff_identity_descends` — every functional descends iff the family shares one
  fiber conditional, iff the identity functional descends.  One test settles the whole class.
* `descendsAlong_sectionMean_of_labelFunction` and `labelFunction_of_descends_pointLaws` — the
  affine pole: label-measurable kernels always descend, and against the family of all point laws
  nothing else does.
* `abs_sectionMean_sub_le` with `exists_kernel_attaining_totalVariationGap` — the size of the
  obstruction is the total-variation width of the section, attained, not a slack bound.
* `sectionMean_gap_unbounded_at_small_totalVariationGap` — and for kernels with no bound the
  width in total variation controls nothing at all: two laws at total-variation distance `2ε`
  can differ by any prescribed amount.  A bounded kernel is not a technical convenience in the
  bound above; without it the bound is false.
* `admissible_interaction_join_obstruction`, `admissible_confounding_meet_obstruction` — the two
  order-theoretic failures, stated over genuine probability-law families rather than as
  arithmetic.  The conditional risks driving them are `interactionRisk` and
  `confoundedConditionalRisk` from `Descent.FunctionalDescent`, so these are those witnesses,
  promoted without extending their parameters beyond the probability simplex.
* `kernelSufficient_componentPosterior` — the posterior component vector of a mixture is
  kernel-sufficient for the family of all mixing weights, so *every* functional descends along
  it.  This is `componentMixtureDensity_factorization` turned into a statement about
  conditionals.
* `exampleComponentResidual_eq_neg_one` — the ansatz that is *not* rescued by it.
  In an exact three-genome, two-component model the descended value at a genome is `-1` and the
  posterior-weighted average of the component values is `0`.

## Epistemic boundary

Everything is finite and exact.  Finiteness is what makes every family dominated, and domination
is exactly the hypothesis under which pairwise consistency is equivalent to descent; no statement
here covers undominated gluing over a continuum, and none should be read as evidence about it.
`fiberConditional` is canonical only where the fiber mass is nonzero, and every statement carries
that hypothesis.  No claim is made about measurable disintegration in a general Borel setting.
-/

section Sections

variable {Genome Label Value Population : Type*} [Fintype Genome]
variable [DecidableEq Label]

/-- The mass a finite law `p` puts on the fiber of the label map `π` over `x`. -/
noncomputable def labelMass (π : Genome → Label) (p : Genome → ℝ) (x : Label) : ℝ :=
  ∑ g, if π g = x then p g else 0

/-- The conditional law of `p` on the fiber over `x`.  It is canonical exactly where the fiber
mass is nonzero; the division convention returns zero elsewhere and carries no information. -/
noncomputable def fiberConditional (π : Genome → Label) (p : Genome → ℝ) (x : Label)
    (g : Genome) : ℝ :=
  if π g = x then p g / labelMass π p x else 0

/-- The law concentrated on a single genome. -/
noncomputable def pointLaw [DecidableEq Genome] (g : Genome) : Genome → ℝ :=
  fun g' ↦ if g' = g then 1 else 0

/-- The total-variation gap between two finite laws, in the `ℓ¹` normalisation. -/
noncomputable def totalVariationGap (μ ν : Genome → ℝ) : ℝ := ∑ g, |μ g - ν g|

/-- The finite total-variation gap is nonnegative, including for signed masses. -/
theorem totalVariationGap_nonneg (μ ν : Genome → ℝ) : 0 ≤ totalVariationGap μ ν := by
  exact Finset.sum_nonneg fun g _ ↦ abs_nonneg (μ g - ν g)

/-- In the `ℓ¹` normalization, two finite probability masses are at total-variation gap at most
two.  Nonnegativity and unit mass are explicit: the statement is false for arbitrary signed
masses or unnormalised sections. -/
theorem totalVariationGap_le_two_of_probabilityMasses (μ ν : Genome → ℝ)
    (hμ_nonneg : ∀ g, 0 ≤ μ g) (hν_nonneg : ∀ g, 0 ≤ ν g)
    (hμ_sum : ∑ g, μ g = 1) (hν_sum : ∑ g, ν g = 1) :
    totalVariationGap μ ν ≤ 2 := by
  rw [totalVariationGap]
  calc
    (∑ g, |μ g - ν g|) ≤ ∑ g, (μ g + ν g) := by
      refine Finset.sum_le_sum fun g _ ↦ ?_
      exact abs_le.2 ⟨by linarith [hμ_nonneg g, hν_nonneg g],
        by linarith [hμ_nonneg g, hν_nonneg g]⟩
    _ = 2 := by rw [Finset.sum_add_distrib, hμ_sum, hν_sum]; norm_num

/-- `b` **descends along** the label map `π` over the family `P` when one label function
reproduces the value of `b` on every member's fiber conditional, at every label that member
charges.  This is the property a group-level report claims. -/
abbrev DescendsAlong (π : Genome → Label) (P : Population → Genome → ℝ)
    (b : (Genome → ℝ) → Value) : Prop :=
  DescendsOn (fun i x ↦ labelMass π (P i) x ≠ 0)
    (fun i x ↦ fiberConditional π (P i) x) b

/-- Two populations agree wherever both charge the label: the local layer of descent. -/
abbrev PairwiseConsistent (π : Genome → Label) (P : Population → Genome → ℝ)
    (b : (Genome → ℝ) → Value) : Prop :=
  PairwiseCompatibleOn (fun i x ↦ labelMass π (P i) x ≠ 0)
    (fun i x ↦ fiberConditional π (P i) x) b

/-- The family shares one conditional law on each charged fiber: sufficiency of the label, stated
without reference to any functional. -/
def KernelSufficient (π : Genome → Label) (P : Population → Genome → ℝ) : Prop :=
  ∀ i j x, labelMass π (P i) x ≠ 0 → labelMass π (P j) x ≠ 0 →
    fiberConditional π (P i) x = fiberConditional π (P j) x

/-- A law with nonnegative values puts nonnegative mass on every fiber. -/
theorem labelMass_nonneg (π : Genome → Label) (p : Genome → ℝ) (hp : ∀ g, 0 ≤ p g) (x : Label) :
    0 ≤ labelMass π p x := by
  rw [labelMass]
  refine Finset.sum_nonneg fun g _ ↦ ?_
  by_cases hg : π g = x
  · rw [if_pos hg]
    exact hp g
  · rw [if_neg hg]

/-- **The abstract section map has a construction.**  For nonnegative laws, descent in the sense
of `FunctionalDescent` — carried by the marginal mass and an abstract section — is descent of the
functional along the label over the family of conditional laws. -/
theorem functionalDescends_iff_descendsAlong (π : Genome → Label) (P : Population → Genome → ℝ)
    (hP : ∀ i g, 0 ≤ P i g) (b : (Genome → ℝ) → Value) :
    FunctionalDescends (fun i x ↦ labelMass π (P i) x)
        (fun i x ↦ fiberConditional π (P i) x) b ↔ DescendsAlong π P b := by
  have hpos : ∀ i x, 0 < labelMass π (P i) x ↔ labelMass π (P i) x ≠ 0 := by
    intro i x
    exact ⟨fun h ↦ ne_of_gt h, fun h ↦ lt_of_le_of_ne (labelMass_nonneg π (P i) (hP i) x)
      (Ne.symm h)⟩
  constructor
  · rintro ⟨value, hvalue⟩
    exact ⟨value, fun i x hx ↦ hvalue i x ((hpos i x).mpr hx)⟩
  · rintro ⟨value, hvalue⟩
    exact ⟨value, fun i x hx ↦ hvalue i x ((hpos i x).mp hx)⟩

/-- A conditional law is a law: its own fiber carries all of its mass. -/
theorem labelMass_fiberConditional (π : Genome → Label) (p : Genome → ℝ) (x : Label)
    (h : labelMass π p x ≠ 0) : labelMass π (fiberConditional π p x) x = 1 := by
  have hterm : ∀ g, (if π g = x then fiberConditional π p x g else 0)
      = (if π g = x then p g else 0) / labelMass π p x := by
    intro g
    by_cases hg : π g = x
    · rw [if_pos hg, if_pos hg, fiberConditional, if_pos hg]
    · rw [if_neg hg, if_neg hg, zero_div]
  calc labelMass π (fiberConditional π p x) x
      = (∑ g, if π g = x then p g else 0) / labelMass π p x := by
        rw [Finset.sum_div]
        exact Finset.sum_congr rfl fun g _ ↦ hterm g
    _ = 1 := div_self h

/-- A supported fiber conditional has total mass one, not merely fiber mass one. -/
theorem sum_fiberConditional (π : Genome → Label) (p : Genome → ℝ) (x : Label)
    (h : labelMass π p x ≠ 0) : ∑ g, fiberConditional π p x g = 1 := by
  rw [← labelMass_fiberConditional π p x h]
  unfold labelMass
  apply Finset.sum_congr rfl
  intro g _
  by_cases hg : π g = x
  · simp [hg]
  · simp [fiberConditional, hg]

/-- Conditioning a nonnegative finite law on a charged fiber preserves nonnegativity. -/
theorem fiberConditional_nonneg (π : Genome → Label) (p : Genome → ℝ) (x : Label)
    (hp : ∀ g, 0 ≤ p g) (h : labelMass π p x ≠ 0) (g : Genome) :
    0 ≤ fiberConditional π p x g := by
  have hmass : 0 < labelMass π p x :=
    lt_of_le_of_ne (labelMass_nonneg π p hp x) (Ne.symm h)
  unfold fiberConditional
  by_cases hg : π g = x
  · rw [if_pos hg]
    exact div_nonneg (hp g) (le_of_lt hmass)
  · rw [if_neg hg]

/-- **Exact finite descent characterization.**  A label report exists exactly when any two
populations agree at every label both charge and the total witness-function space is inhabited.
The second conjunct handles the degenerate logical case of an empty value type without imposing
the stronger assumption that `Value` itself is inhabited when `Label` is empty.  For ordinary
biological value spaces it is automatic.  The family is indexed by an arbitrary type: at finite
resolution there is no additional gluing obstruction because counting measure dominates every
member. -/
theorem descendsAlong_iff_pairwiseConsistent (π : Genome → Label)
    (P : Population → Genome → ℝ) (b : (Genome → ℝ) → Value) :
    DescendsAlong π P b ↔ PairwiseConsistent π P b ∧ Nonempty (Label → Value) :=
  descendsOn_iff_pairwiseCompatibleOn _ _ b

/-- For an inhabited codomain, finite descent is precisely pairwise consistency. -/
theorem descendsAlong_iff_pairwiseConsistent_of_nonempty [Nonempty Value]
    (π : Genome → Label) (P : Population → Genome → ℝ) (b : (Genome → ℝ) → Value) :
    DescendsAlong π P b ↔ PairwiseConsistent π P b :=
  descendsOn_iff_pairwiseCompatibleOn_of_nonempty _ _ b

/-- **The sufficiency pole.**  If the family shares one conditional on every charged fiber then
every functional descends: no property of the functional is involved. -/
theorem descendsAlong_of_kernelSufficient (π : Genome → Label)
    (P : Population → Genome → ℝ) (hK : KernelSufficient π P) (b : (Genome → ℝ) → Value)
    (defaultWitness : Label → Value) :
    DescendsAlong π P b := by
  rw [descendsAlong_iff_pairwiseConsistent]
  refine ⟨?_, ⟨defaultWitness⟩⟩
  intro i j x hi hj
  change b (fiberConditional π (P i) x) = b (fiberConditional π (P j) x)
  rw [hK i j x hi hj]

/-- The converse half of the pole: descent of the identity functional *is* kernel sufficiency, so
a single functional decides the whole class. -/
theorem kernelSufficient_iff_identity_descends (π : Genome → Label)
    (P : Population → Genome → ℝ) :
    KernelSufficient π P ↔ DescendsAlong π P (fun μ ↦ μ) := by
  constructor
  · intro hK
    exact descendsAlong_of_kernelSufficient π P hK _ (fun _ _ ↦ 0)
  · rintro ⟨value, hvalue⟩ i j x hi hj
    exact (hvalue i x hi).trans (hvalue j x hj).symm

/-- The fiber mass of a law tilted by a label-measurable factor factors. -/
theorem labelMass_labelFactor (π : Genome → Label) (m : Label → ℝ) (base : Genome → ℝ)
    (x : Label) : labelMass π (fun g ↦ m (π g) * base g) x = m x * labelMass π base x := by
  rw [labelMass, labelMass, Finset.mul_sum]
  refine Finset.sum_congr rfl fun g _ ↦ ?_
  by_cases hg : π g = x
  · rw [if_pos hg, if_pos hg, hg]
  · rw [if_neg hg, if_neg hg, mul_zero]

/-- A label-measurable tilt cancels in the conditional: the tilted law and the base law have the
same fiber conditional wherever the tilted law charges the fiber. -/
theorem fiberConditional_labelFactor (π : Genome → Label) (m : Label → ℝ) (base : Genome → ℝ)
    (x : Label) (h : labelMass π (fun g ↦ m (π g) * base g) x ≠ 0) :
    fiberConditional π (fun g ↦ m (π g) * base g) x = fiberConditional π base x := by
  rw [labelMass_labelFactor] at h
  have hm : m x ≠ 0 := fun hm ↦ h (by rw [hm, zero_mul])
  funext g
  rw [fiberConditional, fiberConditional, labelMass_labelFactor]
  by_cases hg : π g = x
  · rw [if_pos hg, if_pos hg, hg, mul_div_mul_left _ _ hm]
  · rw [if_neg hg, if_neg hg]

/-- **A family that differs only by a label-measurable tilt of one base law is kernel
sufficient.**  This is the mechanism behind both positive results below: the stratum in the
confounded family, and the posterior component vector of a mixture. -/
theorem kernelSufficient_of_labelTilt (π : Genome → Label) (base : Genome → ℝ)
    (tilt : Population → Label → ℝ) (P : Population → Genome → ℝ)
    (hP : ∀ i, P i = fun g ↦ tilt i (π g) * base g) : KernelSufficient π P := by
  intro i j x hi hj
  rw [hP i] at hi ⊢
  rw [hP j] at hj ⊢
  rw [fiberConditional_labelFactor π (tilt i) base x hi,
    fiberConditional_labelFactor π (tilt j) base x hj]

/-- A label that separates a genome from every other genome conditions to the point law there. -/
theorem fiberConditional_of_separating [DecidableEq Genome] (π : Genome → Label)
    (p : Genome → ℝ) (g : Genome)
    (hsep : ∀ g', π g' = π g → g' = g) (hp : p g ≠ 0) :
    fiberConditional π p (π g) = pointLaw g := by
  have hmass : labelMass π p (π g) = p g := by
    rw [labelMass, Finset.sum_eq_single g]
    · rw [if_pos rfl]
    · intro g' _ hne
      by_cases hg : π g' = π g
      · exact absurd (hsep g' hg) hne
      · rw [if_neg hg]
    · intro h
      exact absurd (Finset.mem_univ g) h
  funext g'
  rw [fiberConditional, hmass, pointLaw]
  by_cases hg : π g' = π g
  · rw [if_pos hg, if_pos (hsep g' hg), hsep g' hg, div_self hp]
  · rw [if_neg hg, if_neg]
    intro hgg
    exact hg (by rw [hgg])

end Sections

/-! ## The affine pole and the exact size of the obstruction -/

section AffinePole

variable {Genome Label Population : Type*} [Fintype Genome]
variable [DecidableEq Label]

/-- The value of an affine functional on a fiber conditional is the fiber-restricted mean. -/
theorem conditionalSectionMean_fiberConditional (π : Genome → Label) (p : Genome → ℝ) (x : Label)
    (f : Genome → ℝ) : conditionalSectionMean f (fiberConditional π p x)
      = (∑ g, if π g = x then p g * f g else 0) / labelMass π p x := by
  rw [conditionalSectionMean, Finset.sum_div]
  refine Finset.sum_congr rfl fun g _ ↦ ?_
  by_cases hg : π g = x
  · rw [fiberConditional, if_pos hg, if_pos hg, div_mul_eq_mul_div]
  · rw [fiberConditional, if_neg hg, if_neg hg, zero_mul, zero_div]

/-- A kernel that is already a function of the label returns that function's value at the label,
under every law charging it. -/
theorem conditionalSectionMean_fiberConditional_of_labelFunction (π : Genome → Label)
    (p : Genome → ℝ) (x : Label) (u : Label → ℝ) (h : labelMass π p x ≠ 0) :
    conditionalSectionMean (fun g ↦ u (π g)) (fiberConditional π p x) = u x := by
  rw [conditionalSectionMean_fiberConditional]
  have hnum : (∑ g, if π g = x then p g * u (π g) else 0) = labelMass π p x * u x := by
    rw [labelMass, Finset.sum_mul]
    refine Finset.sum_congr rfl fun g _ ↦ ?_
    by_cases hg : π g = x
    · rw [if_pos hg, if_pos hg, hg]
    · rw [if_neg hg, if_neg hg, zero_mul]
  rw [hnum, mul_comm, mul_div_assoc, div_self h, mul_one]

/-- **The affine pole, easy direction.**  A label-measurable kernel descends along that label over
every family at once. -/
theorem descendsAlong_sectionMean_of_labelFunction (π : Genome → Label)
    (P : Population → Genome → ℝ) (u : Label → ℝ) :
    DescendsAlong π P (conditionalSectionMean (fun g ↦ u (π g))) :=
  ⟨u, fun i x hi ↦ conditionalSectionMean_fiberConditional_of_labelFunction π (P i) x u hi⟩

/-- The fiber mass of a point law at its own label is one. -/
theorem labelMass_pointLaw [DecidableEq Genome] (π : Genome → Label) (g : Genome) :
    labelMass π (pointLaw g) (π g) = 1 := by
  rw [labelMass, Finset.sum_eq_single g]
  · rw [if_pos rfl, pointLaw, if_pos rfl]
  · intro g' _ hne
    by_cases hg : π g' = π g
    · rw [if_pos hg, pointLaw, if_neg hne]
    · rw [if_neg hg]
  · intro h
    exact absurd (Finset.mem_univ g) h

/-- The mean of a kernel under a point law is the kernel's value there. -/
theorem conditionalSectionMean_pointLaw [DecidableEq Genome] (f : Genome → ℝ) (g : Genome) :
    conditionalSectionMean f (pointLaw g) = f g := by
  rw [conditionalSectionMean, Finset.sum_eq_single g]
  · rw [pointLaw, if_pos rfl, one_mul]
  · intro g' _ hne
    rw [pointLaw, if_neg hne, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ g) h

/-- A point law conditioned on its own label is itself. -/
theorem fiberConditional_pointLaw [DecidableEq Genome] (π : Genome → Label) (g : Genome) :
    fiberConditional π (pointLaw g) (π g) = pointLaw g := by
  funext g'
  rw [fiberConditional, labelMass_pointLaw, div_one]
  by_cases hg : π g' = π g
  · rw [if_pos hg]
  · rw [if_neg hg, pointLaw, if_neg]
    intro hgg
    exact hg (by rw [hgg])

/-- **The affine pole, hard direction.**  Against the maximal family of point laws — one member
concentrated on each genome — only label-measurable kernels descend.  The correction space that
descent otherwise permits collapses to zero at this pole. -/
theorem labelFunction_of_descends_pointLaws [DecidableEq Genome] (π : Genome → Label)
    (f : Genome → ℝ)
    (h : DescendsAlong π (pointLaw : Genome → Genome → ℝ) (conditionalSectionMean f)) :
    ∃ u : Label → ℝ, ∀ g, f g = u (π g) := by
  obtain ⟨value, hvalue⟩ := h
  refine ⟨value, fun g ↦ ?_⟩
  have hg := hvalue g (π g) (by
    change labelMass π (pointLaw g) (π g) ≠ 0
    rw [labelMass_pointLaw]
    norm_num)
  change conditionalSectionMean f (fiberConditional π (pointLaw g) (π g)) = value (π g) at hg
  rw [fiberConditional_pointLaw, conditionalSectionMean_pointLaw] at hg
  exact hg

/-- **The obstruction is a width.**  For kernels bounded by `C` the gap between two populations'
values is at most `C` times the total-variation distance between their conditionals. -/
theorem abs_sectionMean_sub_le (f μ ν : Genome → ℝ) (C : ℝ) (hf : ∀ g, |f g| ≤ C) :
    |conditionalSectionMean f μ - conditionalSectionMean f ν| ≤ C * totalVariationGap μ ν := by
  rw [conditionalSectionMean_sub_eq_width, totalVariationGap, Finset.mul_sum]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun g _ ↦ ?_)
  rw [abs_mul, mul_comm C]
  exact mul_le_mul_of_nonneg_left (hf g) (abs_nonneg _)

/-- **Range-sensitive total-variation bound.**  For probability masses, translating a kernel by
the midpoint of its range does not change the difference of its expectations.  Consequently a
kernel valued in `[a,b]` pays only `(b-a)/2` against the `ℓ¹` total-variation gap.  The factor is
sharp (and is the one needed by binary biological readouts); `abs_sectionMean_sub_le` alone loses
a factor of two because it forgets normalization. -/
theorem abs_sectionMean_sub_le_half_range (f μ ν : Genome → ℝ) (a b : ℝ)
    (hf : ∀ g, a ≤ f g ∧ f g ≤ b)
    (hμ : ∑ g, μ g = 1) (hν : ∑ g, ν g = 1) :
    |conditionalSectionMean f μ - conditionalSectionMean f ν| ≤
      ((b - a) / 2) * totalVariationGap μ ν := by
  let c : ℝ := (a + b) / 2
  let centered : Genome → ℝ := fun g ↦ f g - c
  have hcentered : ∀ g, |centered g| ≤ (b - a) / 2 := by
    intro g
    apply abs_le.2
    dsimp [centered, c]
    constructor <;> linarith [(hf g).1, (hf g).2]
  have hzero : ∑ g, (μ g - ν g) = 0 := by
    rw [Finset.sum_sub_distrib, hμ, hν]
    norm_num
  have htranslate :
      conditionalSectionMean centered μ - conditionalSectionMean centered ν =
        conditionalSectionMean f μ - conditionalSectionMean f ν := by
    rw [conditionalSectionMean_sub_eq_width, conditionalSectionMean_sub_eq_width]
    calc
      (∑ g, (μ g - ν g) * centered g) =
          ∑ g, ((μ g - ν g) * f g - (μ g - ν g) * c) := by
            apply Finset.sum_congr rfl
            intro g _
            dsimp [centered]
            ring
      _ = (∑ g, (μ g - ν g) * f g) - (∑ g, (μ g - ν g)) * c := by
            rw [Finset.sum_sub_distrib, Finset.sum_mul]
      _ = ∑ g, (μ g - ν g) * f g := by rw [hzero]; ring
  rw [← htranslate]
  exact abs_sectionMean_sub_le centered μ ν ((b - a) / 2) hcentered

/-- **The width is attained.**  Some kernel of sup-norm one separates two laws by exactly their
total-variation gap, so the bound above is the support-function width of the section in the
worst direction, not a slack inequality. -/
theorem exists_kernel_attaining_totalVariationGap (μ ν : Genome → ℝ) :
    ∃ f : Genome → ℝ, (∀ g, |f g| ≤ 1) ∧
      conditionalSectionMean f μ - conditionalSectionMean f ν = totalVariationGap μ ν := by
  refine ⟨fun g ↦ if 0 ≤ μ g - ν g then 1 else -1, fun g ↦ ?_, ?_⟩
  · show |if 0 ≤ μ g - ν g then (1 : ℝ) else -1| ≤ 1
    by_cases hg : 0 ≤ μ g - ν g
    · rw [if_pos hg, abs_one]
    · rw [if_neg hg, abs_neg, abs_one]
  · rw [conditionalSectionMean_sub_eq_width, totalVariationGap]
    refine Finset.sum_congr rfl fun g _ ↦ ?_
    show (μ g - ν g) * (if 0 ≤ μ g - ν g then (1 : ℝ) else -1) = |μ g - ν g|
    by_cases hg : 0 ≤ μ g - ν g
    · rw [if_pos hg, mul_one, abs_of_nonneg hg]
    · rw [if_neg hg, mul_neg_one, abs_of_neg (lt_of_not_ge hg)]

end AffinePole

/-! ## Total variation controls nothing without a bound on the kernel -/

/-- **The kernel bound in `abs_sectionMean_sub_le` is not removable.**  For any prescribed gap `M`
and any total-variation budget, two laws that far apart in total variation differ by exactly `M`
under an unbounded kernel: moving a mass `ε` onto a genome whose kernel value is `M / ε`.

This is the reason a distributional-similarity check between two cohorts is the wrong diagnostic
for a functional built from unbounded kernels, such as a variance or a covariance operator.  Small
total variation does not bound the disagreement; only moment closeness does. -/
theorem sectionMean_gap_unbounded_at_small_totalVariationGap (eps M : ℝ) (heps : 0 < eps) :
    ∃ μ ν f : Fin 2 → ℝ, totalVariationGap μ ν = 2 * eps ∧
      conditionalSectionMean f μ - conditionalSectionMean f ν = M := by
  have hne : eps ≠ 0 := ne_of_gt heps
  refine ⟨fun g ↦ if g = 0 then 1 - eps else eps, fun g ↦ if g = 0 then 1 else 0,
    fun g ↦ if g = 0 then 0 else M / eps, ?_, ?_⟩
  · simp only [totalVariationGap, Fin.sum_univ_two]
    show |1 - eps - 1| + |eps - 0| = 2 * eps
    rw [show 1 - eps - 1 = -eps by ring, abs_neg, abs_of_pos heps, sub_zero, abs_of_pos heps]
    ring
  · simp only [conditionalSectionMean, Fin.sum_univ_two]
    show (1 - eps) * 0 + eps * (M / eps) - (1 * 0 + 0 * (M / eps)) = M
    field_simp
    ring

/-! ## Effect modification: each margin descends, their join does not -/

section Interaction

/-- A genome carrying two loci and a binary trait: `(u, v, y)`. -/
abbrev TwoLociTrait := Fin 2 × Fin 2 × Fin 2

/-- The joint law whose conditional trait risk is `interactionRisk`: the two loci are independent
and uniform, and the trait risk carries the interaction and no main effect. -/
noncomputable def interactionTraitLaw (theta : ℝ) (g : TwoLociTrait) : ℝ :=
  (1 / 4) * (if g.2.2 = 1 then interactionRisk theta g.1 g.2.1
    else 1 - interactionRisk theta g.1 g.2.1)

/-- The trait indicator, whose mean is the trait frequency. -/
noncomputable def traitIndicator (g : TwoLociTrait) : ℝ := if g.2.2 = 1 then 1 else 0

/-- Reference evaluations: the indicator is one exactly on the affected genotype. -/
theorem traitIndicator_at_reference_point :
    traitIndicator (0, 0, 1) = 1 ∧ traitIndicator (0, 0, 0) = 0 := by
  constructor <;> norm_num [traitIndicator]


/-- The interaction masses are normalized for every algebraic parameter value.  Nonnegativity,
and hence the probability-law interpretation, is recorded separately because it genuinely
requires the biological risk bound `|theta| ≤ 1 / 2`. -/
theorem interactionTraitLaw_sum_eq_one (theta : ℝ) : ∑ g, interactionTraitLaw theta g = 1 := by
  simp [interactionTraitLaw, Fintype.sum_prod_type, Fin.sum_univ_two]
  ring

/-- In the admissible risk range the normalized interaction masses are nonnegative. -/
theorem interactionTraitLaw_nonneg {theta : ℝ} (htheta : |theta| ≤ 1 / 2)
    (g : TwoLociTrait) : 0 ≤ interactionTraitLaw theta g := by
  rcases abs_le.mp htheta with ⟨hlo, hhi⟩
  rcases g with ⟨u, v, y⟩
  fin_cases u <;> fin_cases v <;> fin_cases y <;>
    simp [interactionTraitLaw, interactionRisk] <;> linarith

/-- Thus every parameter in the admissible interaction interval defines an actual finite
probability law, not merely a normalized signed mass. -/
theorem interactionTraitLaw_isProbability {theta : ℝ} (htheta : |theta| ≤ 1 / 2) :
    (∀ g, 0 ≤ interactionTraitLaw theta g) ∧ ∑ g, interactionTraitLaw theta g = 1 :=
  ⟨interactionTraitLaw_nonneg htheta, interactionTraitLaw_sum_eq_one theta⟩

/-- The admissible biological interaction parameters: exactly those for which every conditional
risk, and therefore every joint mass, lies in the probability simplex. -/
abbrev AdmissibleInteractionParameter := {theta : ℝ // |theta| ≤ 1 / 2}

/-- The interaction family restricted to its probability-law parameter space. -/
noncomputable def admissibleInteractionTraitLaw
    (theta : AdmissibleInteractionParameter) (g : TwoLociTrait) : ℝ :=
  interactionTraitLaw theta.1 g

/-- Every member of the admissible interaction family is an actual probability law. -/
theorem admissibleInteractionTraitLaw_isProbability (theta : AdmissibleInteractionParameter) :
    (∀ g, 0 ≤ admissibleInteractionTraitLaw theta g) ∧
      ∑ g, admissibleInteractionTraitLaw theta g = 1 := by
  simpa [admissibleInteractionTraitLaw] using interactionTraitLaw_isProbability theta.2

/-- **Each locus carries half the mass at each of its values.**

One fact about the interaction law -- both margins are uniform -- and the two loci read it
off.  Stated separately, each locus carried its own copy of the same case split. -/
theorem labelMass_interactionTraitLaw_margins (theta : ℝ) (x : Fin 2) :
    labelMass (fun g : TwoLociTrait ↦ g.1) (interactionTraitLaw theta) x = 1 / 2 ∧
      labelMass (fun g : TwoLociTrait ↦ g.2.1) (interactionTraitLaw theta) x = 1 / 2 := by
  constructor <;>
    (fin_cases x <;>
      simp [labelMass, interactionTraitLaw, Fintype.sum_prod_type, Fin.sum_univ_two] <;> ring)

/-- The first locus carries half the mass at each of its values, whatever the interaction. -/
theorem labelMass_interactionTraitLaw_locusOne (theta : ℝ) (x : Fin 2) :
    labelMass (fun g : TwoLociTrait ↦ g.1) (interactionTraitLaw theta) x = 1 / 2 :=
  (labelMass_interactionTraitLaw_margins theta x).1

/-- Conditional on the first locus, the trait frequency is the average of the interaction risk
over the second locus — which `interactionRisk_average_second` computes to be one half,
independently of the population parameter. -/
theorem trait_value_locusOne (theta : ℝ) (x : Fin 2) :
    conditionalSectionMean traitIndicator
      (fiberConditional (fun g : TwoLociTrait ↦ g.1) (interactionTraitLaw theta) x) = 1 / 2 := by
  rw [conditionalSectionMean_fiberConditional, labelMass_interactionTraitLaw_locusOne]
  have hx : (∑ g : TwoLociTrait, if g.1 = x then interactionTraitLaw theta g * traitIndicator g
      else 0) = (interactionRisk theta x 0 + interactionRisk theta x 1) / 4 := by
    fin_cases x <;>
      simp [interactionTraitLaw, traitIndicator, Fintype.sum_prod_type, Fin.sum_univ_two] <;> ring
  rw [hx]
  have haverage := interactionRisk_average_second theta x
  field_simp at haverage ⊢
  linarith

/-- The second locus carries half the mass at each of its values. -/
theorem labelMass_interactionTraitLaw_locusTwo (theta : ℝ) (x : Fin 2) :
    labelMass (fun g : TwoLociTrait ↦ g.2.1) (interactionTraitLaw theta) x = 1 / 2 :=
  (labelMass_interactionTraitLaw_margins theta x).2

/-- The same erasure holds along the second locus, by `interactionRisk_average_first`. -/
theorem trait_value_locusTwo (theta : ℝ) (x : Fin 2) :
    conditionalSectionMean traitIndicator
      (fiberConditional (fun g : TwoLociTrait ↦ g.2.1) (interactionTraitLaw theta) x)
      = 1 / 2 := by
  rw [conditionalSectionMean_fiberConditional, labelMass_interactionTraitLaw_locusTwo]
  have hx : (∑ g : TwoLociTrait, if g.2.1 = x then interactionTraitLaw theta g * traitIndicator g
      else 0) = (interactionRisk theta 0 x + interactionRisk theta 1 x) / 4 := by
    fin_cases x <;>
      simp [interactionTraitLaw, traitIndicator, Fintype.sum_prod_type, Fin.sum_univ_two] <;> ring
  rw [hx]
  have haverage := interactionRisk_average_first theta x
  field_simp at haverage ⊢
  linarith

/-- The pair of loci carries a quarter of the mass at each of its four values. -/
theorem labelMass_interactionTraitLaw_locusPair (theta : ℝ) :
    labelMass (fun g : TwoLociTrait ↦ (g.1, g.2.1)) (interactionTraitLaw theta) (0, 0)
      = 1 / 4 := by
  simp [labelMass, interactionTraitLaw, Fintype.sum_prod_type, Fin.sum_univ_two]
  ring

/-- Conditional on both loci, the trait frequency is the interaction risk itself, which exposes
the population parameter. -/
theorem trait_value_locusPair (theta : ℝ) :
    conditionalSectionMean traitIndicator
      (fiberConditional (fun g : TwoLociTrait ↦ (g.1, g.2.1)) (interactionTraitLaw theta) (0, 0))
      = interactionRisk theta 0 0 := by
  rw [conditionalSectionMean_fiberConditional, labelMass_interactionTraitLaw_locusPair]
  have hnum : (∑ g : TwoLociTrait, if (g.1, g.2.1) = ((0 : Fin 2), (0 : Fin 2)) then
      interactionTraitLaw theta g * traitIndicator g else 0) = interactionRisk theta 0 0 / 4 := by
    simp [interactionTraitLaw, traitIndicator, Fintype.sum_prod_type, Fin.sum_univ_two]
    ring
  rw [hnum]
  field_simp

/-- **Probability-law form of the interaction obstruction.**  Restricting the population index
to the admissible risk interval preserves descent along either locus and failure along their
join.  Thus the obstruction is realized entirely inside the probability simplex. -/
theorem admissible_interaction_join_obstruction :
    DescendsAlong (fun g : TwoLociTrait ↦ g.1) admissibleInteractionTraitLaw
        (conditionalSectionMean traitIndicator) ∧
      DescendsAlong (fun g : TwoLociTrait ↦ g.2.1) admissibleInteractionTraitLaw
        (conditionalSectionMean traitIndicator) ∧
      ¬ DescendsAlong (fun g : TwoLociTrait ↦ (g.1, g.2.1)) admissibleInteractionTraitLaw
        (conditionalSectionMean traitIndicator) := by
  refine ⟨⟨fun _ ↦ 1 / 2, fun theta x _ ↦ ?_⟩,
    ⟨fun _ ↦ 1 / 2, fun theta x _ ↦ ?_⟩, ?_⟩
  · simpa [admissibleInteractionTraitLaw] using trait_value_locusOne theta.1 x
  · simpa [admissibleInteractionTraitLaw] using trait_value_locusTwo theta.1 x
  · rintro ⟨value, hvalue⟩
    let theta0 : AdmissibleInteractionParameter := ⟨0, by norm_num⟩
    let thetaQuarter : AdmissibleInteractionParameter := ⟨1 / 4, by norm_num⟩
    have hmass0 : labelMass (fun g : TwoLociTrait ↦ (g.1, g.2.1))
        (admissibleInteractionTraitLaw theta0) (0, 0) ≠ 0 := by
      simpa [admissibleInteractionTraitLaw, theta0] using
        (show labelMass (fun g : TwoLociTrait ↦ (g.1, g.2.1))
          (interactionTraitLaw 0) (0, 0) ≠ 0 by
            rw [labelMass_interactionTraitLaw_locusPair]
            norm_num)
    have hmassQuarter : labelMass (fun g : TwoLociTrait ↦ (g.1, g.2.1))
        (admissibleInteractionTraitLaw thetaQuarter) (0, 0) ≠ 0 := by
      simpa [admissibleInteractionTraitLaw, thetaQuarter] using
        (show labelMass (fun g : TwoLociTrait ↦ (g.1, g.2.1))
          (interactionTraitLaw (1 / 4)) (0, 0) ≠ 0 by
            rw [labelMass_interactionTraitLaw_locusPair]
            norm_num)
    have h0 := hvalue theta0 (0, 0) hmass0
    have hQuarter := hvalue thetaQuarter (0, 0) hmassQuarter
    have hvalue0 : conditionalSectionMean traitIndicator
        (fiberConditional (fun g : TwoLociTrait ↦ (g.1, g.2.1))
          (admissibleInteractionTraitLaw theta0) (0, 0)) = interactionRisk 0 0 0 := by
      simpa [admissibleInteractionTraitLaw, theta0] using trait_value_locusPair 0
    have hvalueQuarter : conditionalSectionMean traitIndicator
        (fiberConditional (fun g : TwoLociTrait ↦ (g.1, g.2.1))
          (admissibleInteractionTraitLaw thetaQuarter) (0, 0)) =
          interactionRisk (1 / 4) 0 0 := by
      simpa [admissibleInteractionTraitLaw, thetaQuarter] using trait_value_locusPair (1 / 4)
    rw [hvalue0] at h0
    rw [hvalueQuarter] at hQuarter
    exact interactionRisk_joint_separates (theta := 0) (eta := 1 / 4) (by norm_num)
      (h0.trans hQuarter.symm)

end Interaction

/-! ## Confounding: two informative labels descend, their meet does not -/

section Confounding

/-- A genome carrying an exposure coordinate and a stratum coordinate: `(u, v)`. -/
abbrev ExposureStratum := Fin 2 × Fin 2

/-- The within-stratum exposure law, whose exposure probability is
`confoundedConditionalRisk`.  It is the same in every population. -/
noncomputable def exposureGivenStratum (g : ExposureStratum) : ℝ :=
  if g.1 = 1 then confoundedConditionalRisk g.2 else 1 - confoundedConditionalRisk g.2

/-- Reference evaluations: both exposure branches, so the conditional is pinned as a
complementary pair rather than at one stratum. -/
theorem exposureGivenStratum_at_reference_point :
    exposureGivenStratum (1, 0) = 1 / 4 ∧ exposureGivenStratum (0, 0) = 3 / 4 := by
  constructor <;> simp [exposureGivenStratum, confoundedConditionalRisk] <;> norm_num


/-- The stratum frequency, the only thing that varies across the family. -/
noncomputable def stratumFrequency (beta : ℝ) (s : Fin 2) : ℝ := if s = 1 then beta else 1 - beta

/-- Reference evaluations: the stratum frequencies are complementary. -/
theorem stratumFrequency_at_reference_point :
    stratumFrequency (1 / 4) 1 = 1 / 4 ∧ stratumFrequency (1 / 4) 0 = 3 / 4 := by
  constructor <;> norm_num [stratumFrequency]


/-- The confounded family: one within-stratum law, and a stratum composition that drifts. -/
noncomputable def confoundedExposureLaw (beta : ℝ) (g : ExposureStratum) : ℝ :=
  stratumFrequency beta g.2 * exposureGivenStratum g

/-- The confounded masses are normalized for every algebraic parameter value.  Their
probability-law interpretation additionally requires `beta ∈ [0,1]`, proved next. -/
theorem confoundedExposureLaw_sum_eq_one (beta : ℝ) : ∑ g, confoundedExposureLaw beta g = 1 := by
  simp [confoundedExposureLaw, stratumFrequency, exposureGivenStratum, confoundedConditionalRisk,
    Fintype.sum_prod_type, Fin.sum_univ_two]
  ring

/-- A prevalence in `[0,1]` makes every confounded-family mass nonnegative. -/
theorem confoundedExposureLaw_nonneg {beta : ℝ} (hbeta0 : 0 ≤ beta) (hbeta1 : beta ≤ 1)
    (g : ExposureStratum) : 0 ≤ confoundedExposureLaw beta g := by
  rcases g with ⟨u, v⟩
  fin_cases u <;> fin_cases v <;>
    simp [confoundedExposureLaw, stratumFrequency, exposureGivenStratum,
      confoundedConditionalRisk] <;> linarith

/-- Hence the biologically meaningful prevalence interval gives actual probability laws. -/
theorem confoundedExposureLaw_isProbability {beta : ℝ} (hbeta0 : 0 ≤ beta) (hbeta1 : beta ≤ 1) :
    (∀ g, 0 ≤ confoundedExposureLaw beta g) ∧ ∑ g, confoundedExposureLaw beta g = 1 :=
  ⟨confoundedExposureLaw_nonneg hbeta0 hbeta1, confoundedExposureLaw_sum_eq_one beta⟩

/-- Biologically admissible stratum prevalences. -/
abbrev AdmissiblePrevalence := {beta : ℝ // 0 ≤ beta ∧ beta ≤ 1}

/-- The confounding family restricted to genuine prevalence parameters. -/
noncomputable def admissibleConfoundedExposureLaw
    (beta : AdmissiblePrevalence) (g : ExposureStratum) : ℝ :=
  confoundedExposureLaw beta.1 g

/-- Every admissible prevalence produces an actual probability law. -/
theorem admissibleConfoundedExposureLaw_isProbability (beta : AdmissiblePrevalence) :
    (∀ g, 0 ≤ admissibleConfoundedExposureLaw beta g) ∧
      ∑ g, admissibleConfoundedExposureLaw beta g = 1 := by
  simpa [admissibleConfoundedExposureLaw] using
    confoundedExposureLaw_isProbability beta.2.1 beta.2.2

/-- **The stratum label is kernel-sufficient for the confounded family**, because its members
differ only by a stratum-measurable tilt of one within-stratum law.  Every functional of the
genome descends along the stratum: this is what standardization computes. -/
theorem kernelSufficient_confounded_stratum :
    KernelSufficient (fun g : ExposureStratum ↦ g.2) confoundedExposureLaw :=
  kernelSufficient_of_labelTilt _ exposureGivenStratum stratumFrequency confoundedExposureLaw
    fun _ ↦ rfl

/-- The exposure indicator, whose mean is the exposure frequency. -/
noncomputable def exposureIndicator (g : ExposureStratum) : ℝ := if g.1 = 1 then 1 else 0

/-- Reference evaluations: the indicator is one exactly on the exposed stratum. -/
theorem exposureIndicator_at_reference_point :
    exposureIndicator (1, 0) = 1 ∧ exposureIndicator (0, 0) = 0 := by
  constructor <;> norm_num [exposureIndicator]


/-- The trivial label: the meet of the exposure label and the stratum label.  Descent along it
says the crude exposure frequency is the same in every population. -/
def trivialLabel : ExposureStratum → Unit := fun _ ↦ ()

/-- Under the trivial label the whole space is one fiber of mass one. -/
theorem labelMass_trivialLabel (beta : ℝ) :
    labelMass trivialLabel (confoundedExposureLaw beta) () = 1 := by
  rw [labelMass, ← confoundedExposureLaw_sum_eq_one beta]
  exact Finset.sum_congr rfl fun g _ ↦ if_pos rfl

/-- Under the trivial label, conditioning does nothing: the fiber conditional is the law. -/
theorem fiberConditional_trivialLabel (beta : ℝ) :
    fiberConditional trivialLabel (confoundedExposureLaw beta) () = confoundedExposureLaw beta := by
  funext g
  rw [fiberConditional, labelMass_trivialLabel, div_one, if_pos rfl]

/-- The crude exposure frequency is exactly the confounded marginal risk: it moves with the
stratum composition even though the within-stratum law never changes. -/
theorem crude_exposure_frequency (beta : ℝ) :
    conditionalSectionMean exposureIndicator (confoundedExposureLaw beta)
      = confoundedMarginalRisk beta := by
  simp [conditionalSectionMean, confoundedExposureLaw, stratumFrequency, exposureGivenStratum,
    exposureIndicator, confoundedConditionalRisk, confoundedMarginalRisk, Fintype.sum_prod_type,
    Fin.sum_univ_two]

/-- **Probability-law form of the confounding obstruction.**  Even when every member is indexed
by a valid prevalence, exposure and stratum labels each support descent while their common
coarsening does not. -/
theorem admissible_confounding_meet_obstruction :
    DescendsAlong (fun g : ExposureStratum ↦ g.1) admissibleConfoundedExposureLaw
        (conditionalSectionMean exposureIndicator) ∧
      DescendsAlong (fun g : ExposureStratum ↦ g.2) admissibleConfoundedExposureLaw
        (conditionalSectionMean exposureIndicator) ∧
      ¬ DescendsAlong trivialLabel admissibleConfoundedExposureLaw
        (conditionalSectionMean exposureIndicator) := by
  refine ⟨descendsAlong_sectionMean_of_labelFunction _ admissibleConfoundedExposureLaw
      fun x ↦ if x = 1 then 1 else 0, ?_, ?_⟩
  · exact descendsAlong_of_kernelSufficient _ admissibleConfoundedExposureLaw
      (fun i j x hi hj ↦ kernelSufficient_confounded_stratum i.1 j.1 x (by
        simpa [admissibleConfoundedExposureLaw] using hi) (by
        simpa [admissibleConfoundedExposureLaw] using hj)) _ (fun _ ↦ 0)
  · rintro ⟨value, hvalue⟩
    let beta0 : AdmissiblePrevalence := ⟨0, by norm_num⟩
    let beta1 : AdmissiblePrevalence := ⟨1, by norm_num⟩
    have hmass0 : labelMass trivialLabel (admissibleConfoundedExposureLaw beta0) () ≠ 0 := by
      simpa [admissibleConfoundedExposureLaw, beta0] using
        (show labelMass trivialLabel (confoundedExposureLaw 0) () ≠ 0 by
          rw [labelMass_trivialLabel]
          norm_num)
    have hmass1 : labelMass trivialLabel (admissibleConfoundedExposureLaw beta1) () ≠ 0 := by
      simpa [admissibleConfoundedExposureLaw, beta1] using
        (show labelMass trivialLabel (confoundedExposureLaw 1) () ≠ 0 by
          rw [labelMass_trivialLabel]
          norm_num)
    have h0 := hvalue beta0 () hmass0
    have h1 := hvalue beta1 () hmass1
    have hvalue0 : conditionalSectionMean exposureIndicator
        (fiberConditional trivialLabel (admissibleConfoundedExposureLaw beta0) ()) =
          confoundedMarginalRisk 0 := by
      change conditionalSectionMean exposureIndicator
        (fiberConditional trivialLabel (confoundedExposureLaw 0) ()) = confoundedMarginalRisk 0
      rw [fiberConditional_trivialLabel]
      exact crude_exposure_frequency 0
    have hvalue1 : conditionalSectionMean exposureIndicator
        (fiberConditional trivialLabel (admissibleConfoundedExposureLaw beta1) ()) =
          confoundedMarginalRisk 1 := by
      change conditionalSectionMean exposureIndicator
        (fiberConditional trivialLabel (confoundedExposureLaw 1) ()) = confoundedMarginalRisk 1
      rw [fiberConditional_trivialLabel]
      exact crude_exposure_frequency 1
    rw [hvalue0] at h0
    rw [hvalue1] at h1
    exact confoundedMarginalRisk_separates (beta := 0) (gamma := 1) (by norm_num)
      (h0.trans h1.symm)

end Confounding

/-! ## The posterior component vector is a sufficiency pole -/

section ComponentDescent

variable {Genome Component Population : Type*} [Fintype Genome]
variable [Fintype Component]

omit [Fintype Genome] in
/-- The factorization of `componentMixtureDensity_factorization` extended to genomes the
reference mixture does not charge, where nonnegativity forces both sides to vanish.  The
extension is what lets the factorization be read as a statement about conditional laws rather
than about a ratio on a support. -/
theorem componentMixtureDensity_eq_posteriorTilt_mul (q : Component → Genome → ℝ)
    (w0 w : Component → ℝ) (hq : ∀ k g, 0 ≤ q k g) (hw0 : ∀ k, 0 < w0 k) (g : Genome) :
    componentMixtureDensity q w g
      = posteriorTilt q w0 w g * componentMixtureDensity q w0 g := by
  by_cases hZ : componentMixtureDensity q w0 g = 0
  · have hzero : ∀ k, q k g = 0 := by
      intro k
      have hsum : ∑ k, w0 k * q k g = 0 := hZ
      have hnn : ∀ k ∈ Finset.univ, 0 ≤ w0 k * q k g := fun k _ ↦
        mul_nonneg (le_of_lt (hw0 k)) (hq k g)
      have hk := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hsum k (Finset.mem_univ k)
      rcases mul_eq_zero.mp hk with h | h
      · exact absurd h (ne_of_gt (hw0 k))
      · exact h
    rw [hZ, mul_zero, componentMixtureDensity]
    exact Finset.sum_eq_zero fun k _ ↦ by rw [hzero k, mul_zero]
  · rw [componentMixtureDensity_factorization q w0 w g (fun k ↦ ne_of_gt (hw0 k)) hZ, mul_comm]

/-- **The posterior component vector is kernel-sufficient for the family of all mixing
weights.**  Changing the weights tilts the law by a factor that reads the genome only through its
posterior component coordinates, so the conditional law on a posterior fiber is the same in every
population.  Reporting against posterior ancestry is therefore exempt from the join and meet
obstructions above. -/
theorem kernelSufficient_componentPosterior [DecidableEq (Component → ℝ)]
    (q : Component → Genome → ℝ) (w0 : Component → ℝ) (hq : ∀ k g, 0 ≤ q k g)
    (hw0 : ∀ k, 0 < w0 k) (w : Population → Component → ℝ) :
    KernelSufficient (componentPosterior q w0) (fun i ↦ componentMixtureDensity q (w i)) := by
  refine kernelSufficient_of_labelTilt _ (componentMixtureDensity q w0)
    (fun i a ↦ ∑ k, a k * (w i k / w0 k)) _ (fun i ↦ funext fun g ↦ ?_)
  simpa [posteriorTilt] using componentMixtureDensity_eq_posteriorTilt_mul q w0 (w i) hq hw0 g

/-- **Every functional of the genome descends along posterior ancestry** — not merely a mean, and
with no continuity, linearity or moment hypothesis on the functional.  This is the sufficiency
pole realized by a biologically available label. -/
theorem descendsAlong_componentPosterior [DecidableEq (Component → ℝ)]
    (q : Component → Genome → ℝ) (w0 : Component → ℝ) (hq : ∀ k g, 0 ≤ q k g)
    (hw0 : ∀ k, 0 < w0 k) (w : Population → Component → ℝ) (b : (Genome → ℝ) → ℝ) :
    DescendsAlong (componentPosterior q w0) (fun i ↦ componentMixtureDensity q (w i)) b :=
  descendsAlong_of_kernelSufficient _ _ (kernelSufficient_componentPosterior q w0 hq hw0 w) b
    (fun _ ↦ 0)

end ComponentDescent

/-! ## Descent along ancestry does not make the ancestry-weighted ansatz exact -/

section ComponentResidual

/-- Two components over three genomes, with overlapping support. -/
noncomputable def exampleComponent (k : Fin 2) (g : Fin 3) : ℝ :=
  if k = 0 then (if g = 0 then 1 / 2 else 1 / 4) else (if g = 2 then 1 / 2 else 1 / 4)

/-- Reference mixing weights, taken away from the symmetric point so that nothing below turns on
a symmetry of the reference. -/
noncomputable def exampleReference (k : Fin 2) : ℝ := if k = 0 then 1 / 3 else 2 / 3

/-- Reference evaluations: the two reference masses are a third and two thirds. -/
theorem exampleReference_at_reference_point :
    exampleReference 0 = 1 / 3 ∧ exampleReference 1 = 2 / 3 := by
  constructor <;> norm_num [exampleReference]


/-- A trait value carried by each genome. -/
noncomputable def exampleTrait (g : Fin 3) : ℝ := if g = 0 then -1 else if g = 2 then 1 else 0

/-- Reference evaluations: the trait is the centred dosage contrast. -/
theorem exampleTrait_at_reference_point :
    exampleTrait 0 = -1 ∧ exampleTrait 1 = 0 ∧ exampleTrait 2 = 1 := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [exampleTrait]


/-- Both components are probability laws over the three genomes. -/
theorem exampleComponent_sum_eq_one (k : Fin 2) : ∑ g, exampleComponent k g = 1 := by
  fin_cases k <;> norm_num +decide [exampleComponent, Fin.sum_univ_three]

/-- The reference mixture charges the first genome. -/
theorem componentMixtureDensity_example_zero :
    componentMixtureDensity exampleComponent exampleReference 0 = 1 / 3 := by
  norm_num +decide [componentMixtureDensity, exampleComponent, exampleReference,
    Fin.sum_univ_two]

/-- The posterior component vector separates the first genome from the other two, so its
posterior fiber is that genome alone and the descended value is the trait value there. -/
theorem componentPosterior_example_separating (g : Fin 3)
    (h : componentPosterior exampleComponent exampleReference g
      = componentPosterior exampleComponent exampleReference 0) : g = 0 := by
  fin_cases g
  · rfl
  · exfalso
    have hzero := congrFun h 0
    norm_num +decide [componentPosterior, componentMixtureDensity, exampleComponent,
      exampleReference, Fin.sum_univ_two] at hzero
  · exfalso
    have hzero := congrFun h 0
    norm_num +decide [componentPosterior, componentMixtureDensity, exampleComponent,
      exampleReference, Fin.sum_univ_two] at hzero

/-- At the first genome's posterior the two component trait means cancel, so the
posterior-weighted ansatz reports zero there. -/
theorem componentWeighted_example_zero :
    ∑ k, componentPosterior exampleComponent exampleReference 0 k *
      conditionalSectionMean exampleTrait (exampleComponent k) = 0 := by
  norm_num +decide [componentPosterior, componentMixtureDensity, conditionalSectionMean,
    exampleComponent, exampleReference, exampleTrait, Fin.sum_univ_two, Fin.sum_univ_three]

/-- The error the posterior-weighted ansatz makes at the first genome of this model: its
descended trait mean minus the posterior-weighted average of the component trait means. -/
noncomputable def exampleComponentResidual : ℝ :=
  componentRepresentationResidual
    (conditionalSectionMean exampleTrait
      (fiberConditional (componentPosterior exampleComponent exampleReference)
        (componentMixtureDensity exampleComponent exampleReference)
        (componentPosterior exampleComponent exampleReference 0)))
    (componentPosterior exampleComponent exampleReference 0)
    (fun k ↦ conditionalSectionMean exampleTrait (exampleComponent k))

/-- **Descent along ancestry does not make the ancestry-weighted ansatz exact.**  In this model
the trait mean on the posterior fiber of the first genome is `-1`, while the posterior-weighted
average of the two component trait means at the same posterior is `0`: a
`componentRepresentationResidual` of `-1`, a full unit of trait, entirely localization and no
Jensen term, since the functional is affine.

Two shape intuitions both fail here.  The residual does not vanish at a balanced posterior — the
posterior at this genome is exactly balanced and the residual is maximal — and it is not a
small-overlap correction that a nonlinearity budget could absorb. -/
theorem exampleComponentResidual_eq_neg_one : exampleComponentResidual = -1 := by
  rw [exampleComponentResidual, componentRepresentationResidual, componentWeighted_example_zero,
    fiberConditional_of_separating _ _ (0 : Fin 3) componentPosterior_example_separating
      (by rw [componentMixtureDensity_example_zero]; norm_num),
    conditionalSectionMean_pointLaw]
  norm_num [exampleTrait]

end ComponentResidual

end Descent
