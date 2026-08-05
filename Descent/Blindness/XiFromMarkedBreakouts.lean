/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Tactic
import Descent.Blindness.MarkedBreakoutUniversality

namespace Descent

/-!
# A sweep trajectory does not determine the genealogy it leaves

This is the hard-sweep versus soft-sweep distinction, stated as an identifiability theorem.

A beneficial allele rising to frequency `x` can do so from a single origin, or from several
independent origins each carrying part of the final frequency.  The allele-frequency
trajectory is identical in both cases: same times, same increments, same final frequency.  The
genealogies are not, and the difference is not a matter of degree.

`MarkedBreakoutUniversality` proves that the unconditioned genealogy does not determine the
speed-conditioned one, so the displacement mark is indispensable.  This file first constructs
the corresponding measure on countable family-mass partitions, including its exponential speed
tilt and Kingman component.  It then proves the stronger nonidentifiability statement, which cuts
the other way: even the *complete* trajectory — every sweep time, every increment — does not
determine the genealogy.

The gap is that a sweep need not have one origin.  Recording only the total
fraction `x` collapses a mass partition `η = (η₁, η₂, …)` to its first coordinate, and the
genealogy depends on the partition through

  `σ(η) = ∑ᵢ ηᵢ²`,

which is the probability that a specified pair of blocks lands in the same family.  The
Λ-coalescent of `MarkedBreakoutUniversality` is the one-family case `σ((x,0,…)) = x²`; a general
mass partition gives a Ξ-coalescent, and every finite Ξ measure is realisable by taking
`ν = Ξ/σ`.  So the marked-mass-partition picture covers the whole phase diagram, including the
simultaneous-multiple-merger regimes that the one-family theorem cannot reach.

The obstruction is exhibited concretely.  Two mechanisms,

  `η_single = (x, 0, …)`   and   `η_split = (x/2, x/2, 0, …)`,

are a hard sweep and a two-origin soft sweep reaching the same total frequency.  They have the
same trajectory in every detail.  They differ in two ways no frequency statistic sees:

* `paintboxWeight_single_ne_split`: `σ` is `x²` against `x²/2`, so the soft sweep coalesces
  lineages at half the rate -- it leaves twice the diversity for the same frequency change;
* `disjointPairMerge_single_zero` and `disjointPairMerge_split`: four sampled lineages can fall
  into two distinct origin classes, two in each, with probability `6(x/2)⁴` under the soft sweep
  and probability zero under the hard one.  That is not a rate difference.  It is an event of a
  shape a single-origin sweep cannot produce at all, which is why it, and not any diversity
  level, is the separating observable.

`front_does_not_determine_genealogy` is those two facts together, and it fixes what a study can
and cannot conclude.  Sweep multiplicity is not recoverable from allele-frequency data, at any
sample size or sequencing depth, because the trajectories coincide exactly.  It is recoverable
from a four-lineage haplotype statistic, and the biology core records the resulting ladder:
two lineages see nothing, three see the merger rate, four see the number of origins.

The same theorem is the reason front convergence cannot prove a branching-selection genealogy
result: however complete, it does not carry the ancestry-sensitive information.

The final sections sharpen the reduction.  The derivative-martingale tail supplies the
heavy-tailed subtree mark; the model-specific input is instead the normalized selected flux.
`weightedParetoExceedanceMass_eq_flux` turns that flux into the first-order breakout law, while
`distinctPairParetoExceedanceMass_le_flux_sq` makes two breakouts quadratic in the block scale.
`oneSuccessfulAncestor_produces_onePaintboxAtom` then records the pathwise fact that later
branching below one pioneer cannot create a second origin.  What remains independent is the
common-profile estimate: `pioneerCountFraction_eq_of_commonProfile` derives `w/(1+w)` only after
both colours share one amplitude-per-particle conversion.

`pioneerDisplacement_eq_logDisplacement` and `pioneerIntensity_jacobian` are the change of
variables `w ↦ (w/(1+w), γ⁻¹log(1+w))` under which the `w⁻²dw` pioneer intensity becomes exactly
`x⁻²dx` and the response becomes the logarithmic displacement law.  And
`logDisplacement_injOn` is the formulation correction for lattice models: the response map is
injective, so distinct fractions demand distinct displacements, which a lattice-valued
displacement cannot supply across a continuum of fractions.

The exact rank-one response algebra is formalized below.  Not asserted are the probabilistic
concentration needed to apply it through the endogenous selection boundary, the uniform
rare-block marked law, or convergence of the marked point process.  Those need the two-colour tip
estimate that is the open step.
-/

namespace XiFromMarks

open MeasureTheory
open Filter
open scoped BigOperators ENNReal

/-! ## The marked mass-partition measure -/

/-- A countable candidate family-mass sequence.  `IsFamilyMassPartition` supplies the simplex
conditions, while the function carrier supplies Mathlib's product measurable space. -/
abbrev FamilyMassPartition := ℕ → ℝ

/-- The infinite-simplex conditions for macroscopic descendant-family fractions. -/
def IsFamilyMassPartition (eta : FamilyMassPartition) : Prop :=
  (∀ i, 0 ≤ eta i) ∧ Antitone eta ∧ Summable eta ∧ (∑' i, eta i) ≤ 1

/-- The dust point is a mass partition and is the support point of a Kingman component. -/
theorem isFamilyMassPartition_zero :
    IsFamilyMassPartition (0 : FamilyMassPartition) := by
  refine ⟨fun _ ↦ le_rfl, fun _ _ _ ↦ le_rfl, summable_zero, ?_⟩
  simp

/-- Pair-collision mass `σ(η) = ∑ᵢ ηᵢ²`. -/
noncomputable def collisionMass (eta : FamilyMassPartition) : ℝ :=
  ∑' i, eta i ^ 2

/-- A successful event records every macroscopic family fraction and its front displacement. -/
abbrev MarkedMassPartition := FamilyMassPartition × ℝ

/-- The genealogy measure `Ξ(dη) = σ(η) ν(dη, ℝ)`, implemented by weighting the marked event
intensity by collision mass and projecting away the response mark. -/
noncomputable def xiMeasure (ν : Measure MarkedMassPartition) : Measure FamilyMassPartition :=
  Measure.map Prod.fst
    (ν.withDensity fun mark ↦ ENNReal.ofReal (collisionMass mark.1))

/-- Measurable-set form of `Ξ(dη) = σ(η) ν(dη, ℝ)`. -/
theorem xiMeasure_apply (ν : Measure MarkedMassPartition) {s : Set FamilyMassPartition}
    (hs : MeasurableSet s) :
    xiMeasure ν s =
      ∫⁻ mark in Prod.fst ⁻¹' s, ENNReal.ofReal (collisionMass mark.1) ∂ν := by
  rw [xiMeasure, Measure.map_apply measurable_fst hs,
    withDensity_apply _ (measurable_fst hs)]

/-- The exact local-finiteness hypothesis for genealogy at every fixed sample size. -/
def HasFiniteCollisionIntensity (ν : Measure MarkedMassPartition) : Prop :=
  (∫⁻ mark, ENNReal.ofReal (collisionMass mark.1) ∂ν) < ∞

/-- The empty successful-event intensity satisfies the collision-integrability condition. -/
theorem hasFiniteCollisionIntensity_zero :
    HasFiniteCollisionIntensity (0 : Measure MarkedMassPartition) := by
  simp [HasFiniteCollisionIntensity]

/-- Finite collision intensity makes the induced `Ξ` measure finite. -/
theorem xiMeasure_finite_of_collisionIntensity
    {ν : Measure MarkedMassPartition} (hν : HasFiniteCollisionIntensity ν) :
    xiMeasure ν Set.univ < ∞ := by
  rw [xiMeasure_apply ν MeasurableSet.univ]
  simpa [HasFiniteCollisionIntensity] using hν

/-- Union-bound rate controlling every event that can change a sample of `n` ancestral blocks. -/
noncomputable def samplePartitionChangeRateBound
    (n : ℕ) (ν : Measure MarkedMassPartition) : ℝ≥0∞ :=
  (n.choose 2 : ℝ≥0∞) *
    ∫⁻ mark, ENNReal.ofReal (collisionMass mark.1) ∂ν

/-- Collision integrability makes the relevant-event rate finite for every fixed sample. -/
theorem samplePartitionChangeRateBound_lt_top_of_finiteCollision
    (n : ℕ) {ν : Measure MarkedMassPartition} (hν : HasFiniteCollisionIntensity ν) :
    samplePartitionChangeRateBound n ν < ∞ := by
  apply ENNReal.mul_lt_top
  · simp
  · exact hν

/-- Add an independent Kingman binary-merger component at the dust point. -/
noncomputable def addKingmanComponent
    (rate : ℝ≥0∞) (Xi : Measure FamilyMassPartition) : Measure FamilyMassPartition :=
  Xi + rate • Measure.dirac (0 : FamilyMassPartition)

/-- Zero background binary rate leaves the `Ξ` measure unchanged. -/
@[simp] theorem addKingmanComponent_zero (Xi : Measure FamilyMassPartition) :
    addKingmanComponent 0 Xi = Xi := by
  simp [addKingmanComponent]

/-! ## Speed tilting and the one-family boundary -/

/-- Exponential front-response weight for a marked mass partition. -/
noncomputable def xiSpeedTiltWeight (theta : ℝ) (mark : MarkedMassPartition) : ℝ :=
  Real.exp (-(theta * mark.2))

/-- The full conditioned genealogy formula
`Ξθ(dη) = σ(η) ∫ exp(-θr) ν(dη,dr)`. -/
noncomputable def speedTiltedXiMeasure
    (theta : ℝ) (ν : Measure MarkedMassPartition) : Measure FamilyMassPartition :=
  Measure.map Prod.fst
    (ν.withDensity fun mark ↦
      ENNReal.ofReal (collisionMass mark.1 * xiSpeedTiltWeight theta mark))

/-- Measurable-set form of the speed-tilted `Ξ` formula. -/
theorem speedTiltedXiMeasure_apply
    (theta : ℝ) (ν : Measure MarkedMassPartition) {s : Set FamilyMassPartition}
    (hs : MeasurableSet s) :
    speedTiltedXiMeasure theta ν s =
      ∫⁻ mark in Prod.fst ⁻¹' s,
        ENNReal.ofReal (collisionMass mark.1 * Real.exp (-(theta * mark.2))) ∂ν := by
  rw [speedTiltedXiMeasure, Measure.map_apply measurable_fst hs,
    withDensity_apply _ (measurable_fst hs)]
  rfl

/-- Zero front tilt recovers the unconditioned `Ξ` measure exactly. -/
@[simp] theorem speedTiltedXiMeasure_zero (ν : Measure MarkedMassPartition) :
    speedTiltedXiMeasure 0 ν = xiMeasure ν := by
  simp [speedTiltedXiMeasure, xiMeasure, xiSpeedTiltWeight]

/-- Embed a one-family event into the countable mass-partition space. -/
def oneFamilyMassPartition (x : ℝ) : FamilyMassPartition :=
  fun i ↦ if i = 0 then x else 0

/-- A one-family event has collision mass `x²`, recovering the `Λ` weighting. -/
@[simp] theorem collisionMass_oneFamily (x : ℝ) :
    collisionMass (oneFamilyMassPartition x) = x ^ 2 := by
  simp [collisionMass, oneFamilyMassPartition]

/-- Density-level surjectivity behind `ν(dη) = Ξ(dη)/σ(η)`: away from zero collision mass,
weighting the event density by `σ` returns the prescribed `Ξ` density exactly. -/
theorem xi_surjectivity_density (eta : FamilyMassPartition)
    (hsigma : collisionMass eta ≠ 0) :
    collisionMass eta * (collisionMass eta)⁻¹ = 1 := by
  exact mul_inv_cancel₀ hsigma

/-! ## The paintbox weight, and what it does and does not remember -/

/-- Total population fraction reached by all successful families in one breakout.  A front
trajectory sees this scalar but not how it is partitioned among independent origins. -/
noncomputable def totalFamilyFraction {k : ℕ} (η : Fin k → ℝ) : ℝ :=
  ∑ i, η i

/-- A single successful family carries its whole final fraction. -/
@[simp] theorem totalFamilyFraction_single (x : ℝ) :
    totalFamilyFraction ![x] = x := by
  simp [totalFamilyFraction]

/-- Splitting a successful fraction equally between two origins leaves the total fraction
unchanged. -/
@[simp] theorem totalFamilyFraction_split (x : ℝ) :
    totalFamilyFraction ![x / 2, x / 2] = x := by
  simp [totalFamilyFraction, Fin.sum_univ_two]

/-- The hard- and soft-sweep witnesses lie in exactly the same total-frequency fiber. -/
theorem totalFamilyFraction_single_eq_split (x : ℝ) :
    totalFamilyFraction ![x] = totalFamilyFraction ![x / 2, x / 2] := by
  simp

/-- Probability that a specified pair of ancestral blocks lands in the same family at a breakout
with mass partition `η`.  This is `σ(η) = ∑ᵢ ηᵢ²`, and it is the only thing the genealogy sees
about the partition at the pairwise level. -/
noncomputable def paintboxWeight {k : ℕ} (η : Fin k → ℝ) : ℝ :=
  ∑ i, η i ^ 2

@[simp] theorem paintboxWeight_empty (η : Fin 0 → ℝ) : paintboxWeight η = 0 := by
  simp [paintboxWeight]

/-- The one-family case, which is the Λ-coalescent of `MarkedBreakoutUniversality`. -/
@[simp] theorem paintboxWeight_single (x : ℝ) : paintboxWeight ![x] = x ^ 2 := by
  simp [paintboxWeight]

/-- The same total fraction split evenly between two families. -/
@[simp] theorem paintboxWeight_split (x : ℝ) :
    paintboxWeight ![x / 2, x / 2] = x ^ 2 / 2 := by
  simp [paintboxWeight, Fin.sum_univ_two]
  ring

/-- **Splitting a breakout halves the pairwise merger rate**, while leaving the total fraction,
and hence every front statistic, unchanged. -/
theorem paintboxWeight_single_ne_split (x : ℝ) (hx : x ≠ 0) :
    paintboxWeight ![x] ≠ paintboxWeight ![x / 2, x / 2] := by
  rw [paintboxWeight_single, paintboxWeight_split]
  have hsq : 0 < x ^ 2 := by positivity
  intro heq
  linarith

/-- The paintbox weight is nonnegative, so it is a rate. -/
theorem paintboxWeight_nonneg {k : ℕ} (η : Fin k → ℝ) : 0 ≤ paintboxWeight η := by
  unfold paintboxWeight
  positivity

/-- **The integrability condition is the second-moment one.**  For a nonnegative mass partition
the paintbox weight is dominated by the squared total mass, so a partition with total mass at
most one has paintbox weight at most one, and the union bound over pairs is what makes the
event rate finite at a fixed sample size. -/
theorem paintboxWeight_le_sq_total {k : ℕ} (η : Fin k → ℝ) (hη : ∀ i, 0 ≤ η i) :
    paintboxWeight η ≤ (∑ i, η i) ^ 2 := by
  unfold paintboxWeight
  rw [pow_two, Finset.sum_mul_sum]
  refine Finset.sum_le_sum fun i _ ↦ ?_
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
  have : 0 ≤ ∑ j ∈ Finset.univ.erase i, η i * η j :=
    Finset.sum_nonneg fun j _ ↦ mul_nonneg (hη i) (hη j)
  nlinarith [pow_two (η i)]

/-! ## What no front statistic can see: a simultaneous disjoint merger -/

/-- Probability that four specified ancestral blocks merge as two disjoint pairs into two
*distinct* families.  The factor three counts the pairings of four blocks; the ordered sum over
`i ≠ j` supplies the two families.

This event is the signature of a genuine Ξ-coalescent.  A Λ-coalescent has one family per
breakout and therefore assigns it probability zero. -/
noncomputable def disjointPairMergeProbability {k : ℕ} (η : Fin k → ℝ) : ℝ :=
  3 * ∑ i, ∑ j, if i = j then 0 else η i ^ 2 * η j ^ 2

/-- A mass partition has genuine simultaneous-family structure exactly when two distinct
families carry positive mass. -/
def HasTwoPositiveFamilies {k : ℕ} (η : Fin k → ℝ) : Prop :=
  ∃ i j, i ≠ j ∧ 0 < η i ∧ 0 < η j

/-- The simultaneous disjoint-pair event is strictly positive as soon as two distinct families
carry positive mass.  This is the easy direction of the exact Λ/Ξ boundary below. -/
theorem disjointPairMergeProbability_pos_of_hasTwoPositiveFamilies {k : ℕ}
    (η : Fin k → ℝ) (h : HasTwoPositiveFamilies η) :
    0 < disjointPairMergeProbability η := by
  rcases h with ⟨i, j, hij, hi, hj⟩
  unfold disjointPairMergeProbability
  apply mul_pos (by norm_num)
  apply Finset.sum_pos'
  · intro i' _
    exact Finset.sum_nonneg fun j' _ ↦ by positivity
  · refine ⟨i, Finset.mem_univ _, ?_⟩
    apply Finset.sum_pos'
    · intro j' _
      positivity
    · refine ⟨j, Finset.mem_univ _, ?_⟩
      simp only [hij, ↓reduceIte]
      positivity

/-- **Exact Λ/Ξ boundary.**  For a nonnegative finite mass partition, the probability of two
simultaneous disjoint pair mergers vanishes exactly when at most one family has positive mass.
Thus a one-family Λ event is not merely an example with zero probability: it is the whole zero
set.  Any two macroscopic origins force a genuinely Ξ-shaped event. -/
theorem disjointPairMergeProbability_eq_zero_iff_not_hasTwoPositiveFamilies {k : ℕ}
    (η : Fin k → ℝ) (hη : ∀ i, 0 ≤ η i) :
    disjointPairMergeProbability η = 0 ↔ ¬HasTwoPositiveFamilies η := by
  constructor
  · intro hzero htwo
    have hpos := disjointPairMergeProbability_pos_of_hasTwoPositiveFamilies η htwo
    linarith
  · intro hnot
    unfold disjointPairMergeProbability
    rw [Finset.sum_eq_zero]
    · simp
    · intro i _
      apply Finset.sum_eq_zero
      intro j _
      by_cases hij : i = j
      · simp [hij]
      · have hzero : η i = 0 ∨ η j = 0 := by
          by_contra hboth
          push_neg at hboth
          exact hnot ⟨i, j, hij,
            lt_of_le_of_ne (hη i) (Ne.symm hboth.1),
            lt_of_le_of_ne (hη j) (Ne.symm hboth.2)⟩
        rcases hzero with hi | hj
        · simp [hij, hi]
        · simp [hij, hj]

/-- For nonnegative family masses, simultaneous disjoint mergers occur exactly when the
breakout contains two distinct positive-mass families. -/
theorem disjointPairMergeProbability_pos_iff_hasTwoPositiveFamilies {k : ℕ}
    (η : Fin k → ℝ) (hη : ∀ i, 0 ≤ η i) :
    0 < disjointPairMergeProbability η ↔ HasTwoPositiveFamilies η := by
  constructor
  · intro hpos
    by_contra hnot
    rw [(disjointPairMergeProbability_eq_zero_iff_not_hasTwoPositiveFamilies η hη).2 hnot]
      at hpos
    exact lt_irrefl 0 hpos
  · exact disjointPairMergeProbability_pos_of_hasTwoPositiveFamilies η

/-- **Multiplicity is not a function of total sweep frequency.**  A positive fraction reached
from one origin and the same fraction split across two origins have exactly the same front
observable, but lie on opposite sides of the Λ/Ξ boundary.  This is the explicit witness-fiber
statement missing from a merely genealogical comparison. -/
theorem totalFamilyFraction_does_not_determine_multiplicity (x : ℝ) (hx : 0 < x) :
    totalFamilyFraction ![x] = totalFamilyFraction ![x / 2, x / 2] ∧
      ¬HasTwoPositiveFamilies ![x] ∧
      HasTwoPositiveFamilies ![x / 2, x / 2] := by
  refine ⟨totalFamilyFraction_single_eq_split x, ?_, ?_⟩
  · rintro ⟨i, j, hij, hi, hj⟩
    fin_cases i
    fin_cases j
    exact hij rfl
  · exact ⟨0, 1, by decide, by simpa using half_pos hx, by simpa using half_pos hx⟩

/-- A single-family breakout can never produce a simultaneous disjoint merger. -/
@[simp] theorem disjointPairMerge_single_zero (x : ℝ) :
    disjointPairMergeProbability ![x] = 0 := by
  simp [disjointPairMergeProbability]

/-- A breakout split between two families produces one with probability `6(x/2)⁴`. -/
theorem disjointPairMerge_split (x : ℝ) :
    disjointPairMergeProbability ![x / 2, x / 2] = 6 * (x / 2) ^ 4 := by
  simp [disjointPairMergeProbability, Fin.sum_univ_succ]
  ring

/-- **The complete front process does not determine the genealogy.**

The two mechanisms have the same total fraction at every breakout, hence identical breakout
times, weights and front displacements.  They differ in the pairwise merger rate, and they
differ in a way no rate adjustment can repair: one admits simultaneous disjoint mergers of four
lineages and the other assigns that event probability zero.

So a proof that a branching-selection front has a prescribed genealogy cannot be assembled from
front convergence alone, however complete.  It needs a statistic that sees which lineage went
where. -/
theorem front_does_not_determine_genealogy (x : ℝ) (hx : x ≠ 0) :
    paintboxWeight ![x] ≠ paintboxWeight ![x / 2, x / 2] ∧
      disjointPairMergeProbability ![x] = 0 ∧
      0 < disjointPairMergeProbability ![x / 2, x / 2] := by
  refine ⟨paintboxWeight_single_ne_split x hx, disjointPairMerge_single_zero x, ?_⟩
  rw [disjointPairMerge_split]
  have : 0 < (x / 2) ^ 4 := by positivity
  linarith

/-! ## Boundary transform and derivative-subtree mark -/

/-- Exponential mass of the binary one-step boundary transform.  With physical log-mgf
`logMgf`, critical parameter `criticalParameter`, and critical speed `criticalSpeed`, this is
`2 exp(-t⋆v⋆ + Λ(t⋆))`. -/
noncomputable def boundaryTiltMass
    (logMgf criticalParameter criticalSpeed : ℝ) : ℝ :=
  2 * Real.exp (-criticalParameter * criticalSpeed + logMgf)

/-- The branching-random-walk boundary equation makes the transformed additive mass one. -/
theorem boundaryTiltMass_eq_one
    (logMgf criticalParameter criticalSpeed : ℝ)
    (hboundary : criticalParameter * criticalSpeed - logMgf = Real.log 2) :
    boundaryTiltMass logMgf criticalParameter criticalSpeed = 1 := by
  unfold boundaryTiltMass
  rw [show -criticalParameter * criticalSpeed + logMgf = -Real.log 2 by linarith,
    Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  norm_num

/-- Centered first derivative of the transformed one-step mass.  This is the scalar factor left
after differentiating the log-mgf, and is the quantity in the derivative boundary equation. -/
noncomputable def boundaryTiltCenteredFirstMoment
    (logMgf logMgfDerivative criticalParameter criticalSpeed : ℝ) : ℝ :=
  2 * criticalParameter *
    Real.exp (-criticalParameter * criticalSpeed + logMgf) *
      (criticalSpeed - logMgfDerivative)

/-- Choosing the critical speed to be the log-mgf derivative centers the transformed BRW. -/
@[simp] theorem boundaryTiltCenteredFirstMoment_eq_zero
    (logMgf logMgfDerivative criticalParameter criticalSpeed : ℝ)
    (hspeed : criticalSpeed = logMgfDerivative) :
    boundaryTiltCenteredFirstMoment
      logMgf logMgfDerivative criticalParameter criticalSpeed = 0 := by
  simp [boundaryTiltCenteredFirstMoment, hspeed]

/-- Finite-generation derivative contribution of one stopping-line subtree.  `basePotential`
is the transformed position of its root; `additiveMass` and `derivativeMass` are the two
descendant martingales measured relative to that root. -/
noncomputable def derivativeSubtreeContribution
    (basePotential additiveMass derivativeMass : ℝ) : ℝ :=
  Real.exp (-basePotential) *
    (basePotential * additiveMass + derivativeMass)

/-- Once the additive martingale has vanished, the stopping-line vertex carries the derivative
mark `exp(-V(u)) D∞⁽ᵘ⁾`. -/
@[simp] theorem derivativeSubtreeContribution_zero_additive
    (basePotential derivativeLimit : ℝ) :
    derivativeSubtreeContribution basePotential 0 derivativeLimit =
      Real.exp (-basePotential) * derivativeLimit := by
  simp [derivativeSubtreeContribution]

/-- The preceding mark is also the actual limit of the finite-generation decomposition. -/
theorem derivativeSubtreeContribution_tendsto
    (basePotential derivativeLimit : ℝ)
    (additiveMass derivativeMass : ℕ → ℝ)
    (hadditive : Tendsto additiveMass atTop (nhds 0))
    (hderivative : Tendsto derivativeMass atTop (nhds derivativeLimit)) :
    Tendsto
      (fun generation ↦ derivativeSubtreeContribution basePotential
        (additiveMass generation) (derivativeMass generation))
      atTop (nhds (Real.exp (-basePotential) * derivativeLimit)) := by
  unfold derivativeSubtreeContribution
  have hscaled : Tendsto
      (fun generation ↦ basePotential * additiveMass generation)
      atTop (nhds (basePotential * 0)) :=
    tendsto_const_nhds.mul hadditive
  have hinner : Tendsto
      (fun generation ↦
        basePotential * additiveMass generation + derivativeMass generation)
      atTop (nhds (basePotential * 0 + derivativeLimit)) :=
    hscaled.add hderivative
  have houter : Tendsto
      (fun generation ↦ Real.exp (-basePotential) *
        (basePotential * additiveMass generation + derivativeMass generation))
      atTop (nhds (Real.exp (-basePotential) *
        (basePotential * 0 + derivativeLimit))) :=
    tendsto_const_nhds.mul hinner
  simpa using houter

/-! ## Selected weighted flux and automatic rarity of double breakouts -/

/-- Reproductive-value flux through a finite selected stopping line. -/
noncomputable def selectedPioneerFlux {Pioneer : Type*} [Fintype Pioneer]
    (weight : Pioneer → ℝ) : ℝ :=
  ∑ pioneer, weight pioneer

/-- Exact Pareto first-order exceedance mass contributed by a vertex of normalized weight `q`.
The derivative-martingale input says the true tail is asymptotic to this chart. -/
noncomputable def paretoExceedanceMass
    (tailConstant threshold weight : ℝ) : ℝ :=
  tailConstant * weight / threshold

/-- Weighted `1/w` tails add through the selected flux.  This is the deterministic kernel of
weighted heavy-tail Poissonization; the diffuse-weight hypothesis is needed only for upgrading
this first-order identity to point-process convergence. -/
theorem weightedParetoExceedanceMass_eq_flux
    {Pioneer : Type*} [Fintype Pioneer]
    (tailConstant threshold : ℝ) (weight : Pioneer → ℝ) :
    (∑ pioneer, paretoExceedanceMass tailConstant threshold (weight pioneer)) =
      tailConstant / threshold * selectedPioneerFlux weight := by
  unfold paretoExceedanceMass selectedPioneerFlux
  calc
    (∑ pioneer, tailConstant * weight pioneer / threshold) =
        ∑ pioneer, (tailConstant / threshold) * weight pioneer := by
          apply Finset.sum_congr rfl
          intro pioneer _
          ring
    _ = tailConstant / threshold * ∑ pioneer, weight pioneer := by
      rw [Finset.mul_sum]

/-- Ordered distinct-pioneer factorial mass for two exceedances. -/
noncomputable def distinctPairExceedanceMass
    {Pioneer : Type*} [Fintype Pioneer] [DecidableEq Pioneer]
    (mass : Pioneer → ℝ) : ℝ :=
  ∑ first, ∑ second,
    if first = second then 0 else mass first * mass second

/-- The probability-scale contribution of two different pioneers is bounded by the square of
the one-pioneer contribution. -/
theorem distinctPairExceedanceMass_le_sum_sq
    {Pioneer : Type*} [Fintype Pioneer] [DecidableEq Pioneer]
    (mass : Pioneer → ℝ) (hmass : ∀ pioneer, 0 ≤ mass pioneer) :
    distinctPairExceedanceMass mass ≤ (∑ pioneer, mass pioneer) ^ 2 := by
  unfold distinctPairExceedanceMass
  calc
    (∑ first, ∑ second,
      if first = second then 0 else mass first * mass second) ≤
        ∑ first, ∑ second, mass first * mass second := by
          apply Finset.sum_le_sum
          intro first _
          apply Finset.sum_le_sum
          intro second _
          split_ifs
          · exact mul_nonneg (hmass first) (hmass second)
          · exact le_rfl
    _ = (∑ pioneer, mass pioneer) ^ 2 := by
      rw [pow_two, Finset.sum_mul_sum]

/-- Under nonnegative selected weights, the double-breakout factorial mass is bounded by the
square of the selected Pareto flux. -/
theorem distinctPairParetoExceedanceMass_le_flux_sq
    {Pioneer : Type*} [Fintype Pioneer] [DecidableEq Pioneer]
    (tailConstant threshold : ℝ) (weight : Pioneer → ℝ)
    (htail : 0 ≤ tailConstant) (hthreshold : 0 < threshold)
    (hweight : ∀ pioneer, 0 ≤ weight pioneer) :
    distinctPairExceedanceMass
        (fun pioneer ↦ paretoExceedanceMass tailConstant threshold (weight pioneer)) ≤
      (tailConstant / threshold * selectedPioneerFlux weight) ^ 2 := by
  calc
    distinctPairExceedanceMass
        (fun pioneer ↦ paretoExceedanceMass tailConstant threshold (weight pioneer)) ≤
      (∑ pioneer,
        paretoExceedanceMass tailConstant threshold (weight pioneer)) ^ 2 := by
          apply distinctPairExceedanceMass_le_sum_sq
          intro pioneer
          exact div_nonneg (mul_nonneg htail (hweight pioneer)) hthreshold.le
    _ = (tailConstant / threshold * selectedPioneerFlux weight) ^ 2 := by
      rw [weightedParetoExceedanceMass_eq_flux]

/-- If selected flux is `blockScale · fluxConstant`, the two-pioneer contribution is explicitly
quadratic in the block scale. -/
theorem distinctPairParetoExceedanceMass_le_blockScale_sq
    {Pioneer : Type*} [Fintype Pioneer] [DecidableEq Pioneer]
    (tailConstant threshold blockScale fluxConstant : ℝ)
    (weight : Pioneer → ℝ)
    (htail : 0 ≤ tailConstant) (hthreshold : 0 < threshold)
    (hweight : ∀ pioneer, 0 ≤ weight pioneer)
    (hflux : selectedPioneerFlux weight = blockScale * fluxConstant) :
    distinctPairExceedanceMass
        (fun pioneer ↦ paretoExceedanceMass tailConstant threshold (weight pioneer)) ≤
      (blockScale * (tailConstant * fluxConstant / threshold)) ^ 2 := by
  calc
    distinctPairExceedanceMass
        (fun pioneer ↦ paretoExceedanceMass tailConstant threshold (weight pioneer)) ≤
      (tailConstant / threshold * selectedPioneerFlux weight) ^ 2 :=
        distinctPairParetoExceedanceMass_le_flux_sq
          tailConstant threshold weight htail hthreshold hweight
    _ = (blockScale * (tailConstant * fluxConstant / threshold)) ^ 2 := by
      rw [hflux]
      ring

/-- Quadratic double-breakout mass divided by a positive block scale vanishes whenever the
block scale does.  This is the precise `O(h²) = o(h)` step. -/
theorem quadraticBreakoutMass_over_scale_tendsto_zero
    (coefficient : ℝ) (blockScale : ℕ → ℝ)
    (hpositive : ∀ index, 0 < blockScale index)
    (hzero : Tendsto blockScale atTop (nhds 0)) :
    Tendsto (fun index ↦
      (blockScale index * coefficient) ^ 2 / blockScale index)
      atTop (nhds 0) := by
  have heq : (fun index ↦
      (blockScale index * coefficient) ^ 2 / blockScale index) =
      fun index ↦ blockScale index * coefficient ^ 2 := by
    funext index
    field_simp [(hpositive index).ne']
  rw [heq]
  simpa using hzero.mul_const (coefficient ^ 2)

/-- An exogenous full-tree flux decomposes into the flux retained by selection and the flux
pruned before the stopping line. -/
def IsSelectedFluxDecomposition
    (exogenousFlux selectedFlux prunedFlux : ℕ → ℝ) : Prop :=
  ∀ index, exogenousFlux index = selectedFlux index + prunedFlux index

/-- Retaining every full-tree pioneer and pruning zero reproductive flux is a concrete selected
flux decomposition.  This witnesses that the reduction predicate is inhabited without claiming
that an endogenous selected system realizes this special case. -/
theorem IsSelectedFluxDecomposition.self_zero (flux : ℕ → ℝ) :
    IsSelectedFluxDecomposition flux flux 0 := by
  intro index
  simp

/-- The full-tree flux law plus negligible reproductive-value pruning gives the endogenous
selected-flux law.  This is the exact reduction from equations (27)--(28) to (26). -/
theorem selectedFlux_tendsto_of_exogenous_of_pruned
    (exogenousFlux selectedFlux prunedFlux : ℕ → ℝ) (fluxConstant : ℝ)
    (hdecomposition :
      IsSelectedFluxDecomposition exogenousFlux selectedFlux prunedFlux)
    (hexogenous : Tendsto exogenousFlux atTop (nhds fluxConstant))
    (hpruned : Tendsto prunedFlux atTop (nhds 0)) :
    Tendsto selectedFlux atTop (nhds fluxConstant) := by
  have heq : selectedFlux = fun index ↦ exogenousFlux index - prunedFlux index := by
    funext index
    linarith [hdecomposition index]
  rw [heq]
  simpa using hexogenous.sub hpruned

/-! ## One successful ancestor gives one paintbox atom -/

/-- **One successful ancestor produces one paintbox atom.**  The atom records its final
descendant fraction.  Branching below that ancestor changes the number of descendants but
cannot create a second ancestral label, so both the collision weight and the absence of a
simultaneous disjoint merger hold pathwise. -/
theorem oneSuccessfulAncestor_produces_onePaintboxAtom (x : ℝ) :
    totalFamilyFraction ![x] = x ∧
      paintboxWeight ![x] = x ^ 2 ∧
        disjointPairMergeProbability ![x] = 0 := by
  simp

/-! ## The pioneer change of variables -/

/-- Population fraction reached by a pioneer of reproductive weight `w`. -/
noncomputable def pioneerWeightFraction (w : ℝ) : ℝ := w / (1 + w)

/-- With a vanishing denominator Mathlib returns `0`, which is a value this quantity can also
take legitimately, so the branch is named rather than left to be inferred from the result. -/
theorem pioneerWeightFraction_at_zero_denominator_is_junk (w : ℝ)
    (hzero : (1 + w) = 0) :
    pioneerWeightFraction w = 0 := by
  unfold pioneerWeightFraction
  rw [hzero, div_zero]


/-- Front displacement produced by a pioneer of reproductive weight `w`, at rate constant `γ`. -/
noncomputable def pioneerWeightDisplacement (gamma w : ℝ) : ℝ :=
  (1 / gamma) * Real.log (1 + w)

/-- Real-valued front coordinate obtained from reproductive amplitude.  Unlike a literal
particle quantile, this coordinate remains continuous for lattice displacement laws. -/
noncomputable def amplitudeFront (gamma amplitude : ℝ) : ℝ :=
  (1 / gamma) * Real.log amplitude

/-- A zero rate constant sends `1 / gamma` to Mathlib's junk `0`, so a pioneer of any weight is
reported as displacing the front by nothing. -/
theorem pioneerWeightDisplacement_at_zero_rate_is_junk (w : ℝ) :
    pioneerWeightDisplacement 0 w = 0 := by
  simp [pioneerWeightDisplacement]


@[simp] theorem pioneerWeightFraction_zero : pioneerWeightFraction 0 = 0 := by
  simp [pioneerWeightFraction]

/-- Reference value: unit reproductive weight reaches exactly half the population. -/
theorem pioneerWeightFraction_one : pioneerWeightFraction 1 = 1 / 2 := by
  norm_num [pioneerWeightFraction]

@[simp] theorem pioneerWeightDisplacement_zero (gamma : ℝ) :
    pioneerWeightDisplacement gamma 0 = 0 := by
  simp [pioneerWeightDisplacement]

/-- Reference value: at unit rate constant, unit weight displaces the front by `log 2`. -/
theorem pioneerWeightDisplacement_one : pioneerWeightDisplacement 1 1 = Real.log 2 := by
  norm_num [pioneerWeightDisplacement]

/-- Adding pioneer amplitude `w` to a unit background shifts the amplitude front by
`gamma⁻¹ log(1+w)`. -/
theorem amplitudeFront_pioneerShift (gamma w : ℝ) :
    amplitudeFront gamma (1 + w) - amplitudeFront gamma 1 =
      pioneerWeightDisplacement gamma w := by
  simp [amplitudeFront, pioneerWeightDisplacement]

/-- **The response map is exactly the logarithmic displacement law.**  Converting reproductive
weight to population fraction turns `γ⁻¹ log (1 + w)` into `-γ⁻¹ log (1 - x)`, which is the
displacement law whose forward half `MarkedBreakoutUniversality` proves produces the Beta
family.  The converse -- that no other law does -- needs uniqueness of Laplace transforms and
is not formalised.  This identifies the displacement response; the population-fraction response
still requires common-profile relaxation below. -/
theorem pioneerDisplacement_eq_logDisplacement (gamma w : ℝ) (hw : 0 < w) :
    pioneerWeightDisplacement gamma w
      = MarkedBreakout.logDisplacement gamma (pioneerWeightFraction w) := by
  have hpos : (0 : ℝ) < 1 + w := by linarith
  have hne : (1 : ℝ) + w ≠ 0 := ne_of_gt hpos
  have hsub : 1 - pioneerWeightFraction w = (1 + w)⁻¹ := by
    unfold pioneerWeightFraction
    field_simp
    ring
  unfold pioneerWeightDisplacement MarkedBreakout.logDisplacement
  rw [hsub, Real.log_inv]
  ring

/-- **The pioneer intensity becomes the inverse-square family intensity.**  Under
`w = x / (1 - x)` the Jacobian is `(1 - x)⁻²`, and `w⁻²` times it is `x⁻²` on the nose.
The `w⁻²dw` intensity comes from the derivative-martingale tail after the selected weighted-flux
estimate; it is not a second model-specific tail hypothesis. -/
theorem pioneerIntensity_jacobian (x : ℝ) (hx0 : x ≠ 0) (hx1 : x ≠ 1) :
    1 / (x / (1 - x)) ^ 2 * (1 / (1 - x) ^ 2) = 1 / x ^ 2 := by
  have h1 := MarkedBreakout.pioneer_one_sub_ne_zero hx1
  field_simp

/-! ## Rank-one two-colour response algebra -/

/-- Both colours have relaxed to the same spatial profile when one conversion factor maps their
particle counts to their reproductive amplitudes. -/
def HasCommonProfileRelaxation
    (conversion backgroundAmplitude pioneerAmplitude
      backgroundCount pioneerCount : ℝ) : Prop :=
  backgroundAmplitude = conversion * backgroundCount ∧
    pioneerAmplitude = conversion * pioneerCount

/-- Identical amplitude and count coordinates have the unit common profile.  This canonical
algebraic witness does not assert that endogenous hard selection reaches that profile. -/
theorem HasCommonProfileRelaxation.unit (background pioneer : ℝ) :
    HasCommonProfileRelaxation 1 background pioneer background pioneer := by
  simp [HasCommonProfileRelaxation]

/-- Common-profile relaxation converts a count fraction into the corresponding amplitude
fraction.  The hypothesis is load-bearing: uniqueness of the pioneer alone does not supply it. -/
theorem countFraction_eq_amplitudeFraction_of_commonProfile
    (conversion backgroundAmplitude pioneerAmplitude
      backgroundCount pioneerCount : ℝ)
    (hconversion : conversion ≠ 0)
    (hcount : backgroundCount + pioneerCount ≠ 0)
    (hprofile : HasCommonProfileRelaxation conversion backgroundAmplitude pioneerAmplitude
      backgroundCount pioneerCount) :
    pioneerCount / (backgroundCount + pioneerCount) =
      pioneerAmplitude / (backgroundAmplitude + pioneerAmplitude) := by
  rcases hprofile with ⟨hbackground, hpioneer⟩
  have hamplitude : backgroundAmplitude + pioneerAmplitude ≠ 0 := by
    rw [hbackground, hpioneer, ← mul_add]
    exact mul_ne_zero hconversion hcount
  field_simp [hcount, hamplitude]
  rw [hbackground, hpioneer]
  ring

/-- With unit background amplitude and pioneer amplitude `w`, common-profile relaxation gives
the Brunet--Derrida descendant fraction `w/(1+w)`. -/
theorem pioneerCountFraction_eq_of_commonProfile
    (conversion w backgroundCount pioneerCount : ℝ)
    (hconversion : conversion ≠ 0)
    (hcount : backgroundCount + pioneerCount ≠ 0)
    (hprofile : HasCommonProfileRelaxation conversion 1 w
      backgroundCount pioneerCount) :
    pioneerCount / (backgroundCount + pioneerCount) = pioneerWeightFraction w := by
  rw [pioneerWeightFraction]
  exact countFraction_eq_amplitudeFraction_of_commonProfile
    conversion 1 w backgroundCount pioneerCount hconversion hcount hprofile

/-- If both colours share one reproductive conversion factor, their descendant fraction is the
ratio of their reproductive amplitudes.  The open particle-system input is the uniform
probabilistic concentration that permits replacing descendant counts by these amplitudes. -/
theorem spectralResponse_fraction_exact
    (conversion z0 z1 : ℝ) (hconversion : conversion ≠ 0) (hsum : z0 + z1 ≠ 0) :
    conversion * z1 / (conversion * z0 + conversion * z1) = z1 / (z0 + z1) := by
  field_simp

/-- Background amplitude one and pioneer amplitude `w` give family fraction `w/(1+w)`. -/
theorem spectralResponse_pioneerFraction
    (conversion w : ℝ) (hconversion : conversion ≠ 0) (hw : w ≠ -1) :
    conversion * w / (conversion * 1 + conversion * w) = pioneerWeightFraction w := by
  rw [pioneerWeightFraction]
  apply spectralResponse_fraction_exact conversion 1 w hconversion
  intro h
  apply hw
  linarith

/-- The logarithmic translation exactly restores unit reproductive amplitude after a pioneer of
amplitude `w` is added. -/
theorem spectralResponse_shift_restoresAmplitude
    (gamma w : ℝ) (hgamma : gamma ≠ 0) (hw : -1 < w) :
    Real.exp (-(gamma * pioneerWeightDisplacement gamma w)) * (1 + w) = 1 := by
  have hpos : 0 < 1 + w := by linarith
  have hexp : Real.exp (Real.log (1 + w)) = 1 + w := Real.exp_log hpos
  rw [show -(gamma * pioneerWeightDisplacement gamma w) = -Real.log (1 + w) by
    unfold pioneerWeightDisplacement
    field_simp]
  rw [Real.exp_neg, hexp]
  exact inv_mul_cancel₀ (ne_of_gt hpos)

/-! ## The lattice formulation correction -/

/-- **The response map is injective on the admissible range.**  Distinct population fractions
demand distinct front displacements, so a displacement confined to a lattice cannot realise the
response across a continuum of fractions.  For lattice displacement laws the front must be
defined through a real-valued reproductive-amplitude coordinate, or the response replaced by a
phase-dependent kernel; the deterministic continuous graph is not available. -/
theorem logDisplacement_injOn (gamma : ℝ) (hg : gamma ≠ 0) :
    Set.InjOn (MarkedBreakout.logDisplacement gamma) (Set.Iio 1) := by
  intro a ha b hb hab
  have hA : (0 : ℝ) < 1 - a := by simpa using sub_pos.mpr (Set.mem_Iio.mp ha)
  have hB : (0 : ℝ) < 1 - b := by simpa using sub_pos.mpr (Set.mem_Iio.mp hb)
  unfold MarkedBreakout.logDisplacement at hab
  have hlog : Real.log (1 - a) = Real.log (1 - b) := by
    have h3 : (-(1 / gamma)) * Real.log (1 - a) = (-(1 / gamma)) * Real.log (1 - b) := hab
    exact mul_left_cancel₀ (neg_ne_zero.mpr (one_div_ne_zero hg)) h3
  have := Real.log_injOn_pos (Set.mem_Ioi.mpr hA) (Set.mem_Ioi.mpr hB) hlog
  linarith

end XiFromMarks

end Descent
