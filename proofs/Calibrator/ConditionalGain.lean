/-
Copyright (c) 2026 Sauers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sauers
-/
import Calibrator.BundleRigidity
import Calibrator.BundleRigidity.CoverageInvariance
import Calibrator.BundleRigidity.EntropySplit
import Calibrator.BundleRigidity.Freshness
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

namespace Calibrator

open scoped BigOperators

/-!
# Conditional gain under coupled genotype laws

This module is the finite, coupling-safe core for oscillatory decay.  A coupling is a
joint law on a multilocus genotype vector; no product factorization is assumed.  Its
characteristic amplitude is computed from the **joint** score, and the conditional-gain
functional is the negative logarithm of that amplitude (with `⊤` at exact cancellation).

That choice corrects a tempting but false identity.  In general,

`E exp(i s ∑ᵢ h(Xᵢ)) ≠ E ∏ᵢ E[exp(i s h(Xᵢ)) | X₍<i₎]`.

The copied-binary witness below proves the failure exactly.  Conditional factors remain
useful only after they have delivered a genuine contraction of the partial joint
expectation; `BundleRigidity.master_decay_bound` is the already-proved telescope for that
certificate.

Biologically, the distinction is the difference between one-locus randomness and new
multilocus randomness.  Recombination or haplotype innovation may give a contraction at
many steps.  Perfect LD, long IBD tracts, inversions, or deterministic ancestry mosaics
may not.  Marginal Hardy-Weinberg laws alone cannot decide which regime a score occupies.
-/

/-- A finite joint law for `n` loci with `d` possible states per locus, together with the
phase contributed by each locus/state pair.

`mass` is the full multilocus coupling.  It may encode arbitrary LD; only non-negativity
and normalization are imposed. -/
structure FiniteCoupledPhaseLaw (n d : ℕ) where
  mass : (Fin n → Fin d) → ℝ
  mass_nonneg : ∀ x, 0 ≤ mass x
  mass_sum : ∑ x, mass x = 1
  phase : Fin n → Fin d → ℝ

namespace FiniteCoupledPhaseLaw

variable {n d : ℕ} (C : FiniteCoupledPhaseLaw n d)

/-- The additive score phase of one multilocus state. -/
def scorePhase (x : Fin n → Fin d) : ℝ :=
  ∑ i, C.phase i (x i)

/-- Real part of the joint characteristic function. -/
noncomputable def cosPart (s : ℝ) : ℝ :=
  ∑ x, C.mass x * Real.cos (s * C.scorePhase x)

/-- Imaginary part of the joint characteristic function. -/
noncomputable def sinPart (s : ℝ) : ℝ :=
  ∑ x, C.mass x * Real.sin (s * C.scorePhase x)

/-- The modulus of the **actual joint** characteristic function. -/
noncomputable def characteristicAmplitude (s : ℝ) : ℝ :=
  Real.sqrt (C.cosPart s ^ 2 + C.sinPart s ^ 2)

theorem characteristicAmplitude_nonneg (s : ℝ) : 0 ≤ C.characteristicAmplitude s :=
  Real.sqrt_nonneg _

/-- The joint characteristic amplitude is normalized at frequency zero. -/
@[simp] theorem characteristicAmplitude_zero : C.characteristicAmplitude 0 = 1 := by
  simp [characteristicAmplitude, cosPart, sinPart, C.mass_sum]

/-- The conditional-gain functional.  At positive amplitude it is `-log |φ(s)|`; exact
cancellation has infinite gain.  `WithTop` is essential here because `Real.log 0 = 0` in
Lean, which would otherwise assign the wrong value to a vanishing characteristic
function. -/
noncomputable def conditionalGainFunctional (s : ℝ) : WithTop ℝ :=
  if C.characteristicAmplitude s = 0 then ⊤
  else ((-Real.log (C.characteristicAmplitude s) : ℝ) : WithTop ℝ)

@[simp] theorem conditionalGainFunctional_eq_top {s : ℝ}
    (h : C.characteristicAmplitude s = 0) :
    C.conditionalGainFunctional s = ⊤ := by
  simp [conditionalGainFunctional, h]

theorem conditionalGainFunctional_eq_coe {s : ℝ}
    (h : C.characteristicAmplitude s ≠ 0) :
    C.conditionalGainFunctional s =
      ((-Real.log (C.characteristicAmplitude s) : ℝ) : WithTop ℝ) := by
  simp [conditionalGainFunctional, h]

/-- Zero frequency has zero gain. -/
@[simp] theorem conditionalGainFunctional_zero : C.conditionalGainFunctional 0 = 0 := by
  simp [conditionalGainFunctional]

end FiniteCoupledPhaseLaw

/-! ## Support and oscillatory gain are different axes

The compendium's two-dimensional edge can already be seen in the smallest nontrivial
finite model.  The two laws below have the **same two genotype cells**, the same phase
coding, and positive mass on both cells.  Only their probabilities differ.  Coverage is
therefore identical, while the characteristic amplitude at frequency one is zero for the
balanced law and `1/2` for the biased law.

This is the biological distinction between *which genotypes can occur* and *how their
score phases cancel*.  A joint genotype-cell floor protects support-level identifiability;
it does not determine a polygenic score's anti-concentration or local-limit rate.  LD-aware
method design consequently needs both a support diagnostic and a gain diagnostic.
-/

/-- The two one-locus binary configurations, written explicitly so every later finite sum
is checked against the actual function-space Fintype rather than an informal two-cell
enumeration. -/
private theorem binaryOneSite_univ :
    (Finset.univ : Finset (Fin 1 → Fin 2)) = {![0], ![1]} := by
  decide

/-- Balanced binary law with opposite phases `0` and `π`. -/
noncomputable def balancedBinaryOppositePhaseLaw : FiniteCoupledPhaseLaw 1 2 where
  mass := fun _ ↦ 1 / 2
  mass_nonneg := by intro; norm_num
  mass_sum := by
    rw [binaryOneSite_univ]
    norm_num
  phase := fun _ j ↦ if j = 0 then 0 else Real.pi

/-- Biased binary law on the same support and with the same opposite phases. -/
noncomputable def biasedBinaryOppositePhaseLaw : FiniteCoupledPhaseLaw 1 2 where
  mass := fun x ↦ if x 0 = 0 then 3 / 4 else 1 / 4
  mass_nonneg := by
    intro x
    split_ifs <;> norm_num
  mass_sum := by
    rw [binaryOneSite_univ]
    norm_num
  phase := fun _ j ↦ if j = 0 then 0 else Real.pi

/-- The balanced law cancels exactly at frequency one. -/
theorem balancedBinaryOppositePhaseLaw_amplitude_one :
    balancedBinaryOppositePhaseLaw.characteristicAmplitude 1 = 0 := by
  rw [FiniteCoupledPhaseLaw.characteristicAmplitude]
  simp [FiniteCoupledPhaseLaw.cosPart, FiniteCoupledPhaseLaw.sinPart,
    FiniteCoupledPhaseLaw.scorePhase, balancedBinaryOppositePhaseLaw,
    binaryOneSite_univ]

/-- The same phase coding under a `3/4 : 1/4` imbalance leaves amplitude `1/2`. -/
theorem biasedBinaryOppositePhaseLaw_amplitude_one :
    biasedBinaryOppositePhaseLaw.characteristicAmplitude 1 = 1 / 2 := by
  rw [FiniteCoupledPhaseLaw.characteristicAmplitude]
  simp [FiniteCoupledPhaseLaw.cosPart, FiniteCoupledPhaseLaw.sinPart,
    FiniteCoupledPhaseLaw.scorePhase, biasedBinaryOppositePhaseLaw,
    binaryOneSite_univ]
  norm_num

/-- Exact cancellation gives infinite conditional gain. -/
theorem balancedBinaryOppositePhaseLaw_gain_one :
    balancedBinaryOppositePhaseLaw.conditionalGainFunctional 1 = ⊤ :=
  FiniteCoupledPhaseLaw.conditionalGainFunctional_eq_top _
    balancedBinaryOppositePhaseLaw_amplitude_one

/-- The biased law has finite gain at the same frequency. -/
theorem biasedBinaryOppositePhaseLaw_gain_one_ne_top :
    biasedBinaryOppositePhaseLaw.conditionalGainFunctional 1 ≠ ⊤ := by
  rw [FiniteCoupledPhaseLaw.conditionalGainFunctional_eq_coe _]
  · exact WithTop.coe_ne_top
  · rw [biasedBinaryOppositePhaseLaw_amplitude_one]
    norm_num

/-! ## The false conditional-product identity, executed -/

/-- Joint expectation for two copied binary phase factors `Y,Y`, with `Y = ±1` equally
likely.  The product is identically one. -/
noncomputable def copiedBinaryJointExpectation : ℝ :=
  ((1 : ℝ) * 1 + (-1 : ℝ) * (-1)) / 2

/-- The proposed product of conditional factors for the same model.  The first factor is
`E Y = 0`; the second is `Y`, so their product has expectation zero. -/
noncomputable def copiedBinaryConditionalProductExpectation : ℝ :=
  ((((1 : ℝ) + (-1 : ℝ)) / 2) * 1 +
    (((1 : ℝ) + (-1 : ℝ)) / 2) * (-1)) / 2

/-- **Copied dependence refutes the claimed tautology:** the actual joint phase
expectation is one while the product of the proposed conditional factors is zero. -/
theorem copied_binary_refutes_conditional_product_identity :
    copiedBinaryJointExpectation = 1 ∧
      copiedBinaryConditionalProductExpectation = 0 ∧
      copiedBinaryJointExpectation ≠ copiedBinaryConditionalProductExpectation := by
  norm_num [copiedBinaryJointExpectation, copiedBinaryConditionalProductExpectation]

/-! ## Fluctuation collapse -/

/-- A finite weighted family of centered deviations uniformly bounded by `radius`.

This is the exact consequence supplied by Denjoy--Koksma along continued-fraction
denominators: the analytic theorem supplies `bound`; the variance collapse below is then
finite algebra. -/
structure FiniteBoundedDeviation (Ω : Type*) [Fintype Ω] where
  weight : Ω → ℝ
  weight_nonneg : ∀ ω, 0 ≤ weight ω
  weight_sum : ∑ ω, weight ω = 1
  deviation : Ω → ℝ
  radius : ℝ
  radius_nonneg : 0 ≤ radius
  bound : ∀ ω, |deviation ω| ≤ radius

/-- **The class is inhabited**: a point mass, zero deviation, zero radius. -/
noncomputable def FiniteBoundedDeviation.witness (n : ℕ) :
    FiniteBoundedDeviation (Fin (n + 1)) where
  weight := fun ω ↦ if ω = 0 then 1 else 0
  weight_nonneg := fun ω ↦ by by_cases h : ω = 0 <;> simp [h]
  weight_sum := by simp
  deviation := fun _ ↦ 0
  radius := 0
  radius_nonneg := le_rfl
  bound := fun _ ↦ by simp

/-- `FiniteBoundedDeviation` is inhabited by the explicit point-mass witness. -/
theorem FiniteBoundedDeviation.nonempty (n : ℕ) :
    Nonempty (FiniteBoundedDeviation (Fin (n + 1))) :=
  ⟨FiniteBoundedDeviation.witness n⟩

namespace FiniteBoundedDeviation

variable {Ω : Type*} [Fintype Ω] (B : FiniteBoundedDeviation Ω)

/-- The second moment of the centered fluctuation. -/
noncomputable def secondMoment : ℝ :=
  ∑ ω, B.weight ω * B.deviation ω ^ 2

/-- **Bounded deviations have bounded variance proxy.**  Along a Denjoy--Koksma
subsequence this rules out diffusive scaling: the centered second moment stays at most
`radius²`, independently of the score length. -/
theorem secondMoment_le_radius_sq : B.secondMoment ≤ B.radius ^ 2 := by
  unfold secondMoment
  calc
    ∑ ω, B.weight ω * B.deviation ω ^ 2
        ≤ ∑ ω, B.weight ω * B.radius ^ 2 := by
          refine Finset.sum_le_sum fun ω _ ↦ ?_
          have habs := B.bound ω
          have hsq : B.deviation ω ^ 2 ≤ B.radius ^ 2 := by
            rw [abs_le] at habs
            nlinarith [B.radius_nonneg]
          exact mul_le_mul_of_nonneg_left hsq (B.weight_nonneg ω)
    _ = B.radius ^ 2 := by
          rw [← Finset.sum_mul, B.weight_sum, one_mul]

end FiniteBoundedDeviation

/-! ## Symmetric latent cancellation: the Gaussian-copula audit point -/

/-- An odd power of an antisymmetric conditional characteristic factor cancels under a
symmetric two-point latent law.  The same pairing `w ↔ -w` is present for a centered
Gaussian common factor.

This is the parity obstruction missing from the proposed equicorrelated lower bound: if
the one-coordinate conditional factor is odd, every odd panel size has exact cancellation,
so no finite `Θ(log n)` lower bound for the gain can hold without a non-cancellation
hypothesis or a restriction to even `n`. -/
theorem symmetric_latent_odd_cancellation (a : ℝ) (n : ℕ) (hn : Odd n) :
    (a ^ n + (-a) ^ n) / 2 = 0 := by
  have hneg : (-a) ^ n = -(a ^ n) := by
    rw [show -a = (-1 : ℝ) * a by ring, mul_pow, hn.neg_one_pow]
    ring
  rw [hneg]
  ring

/-! ## Coverage is invariant under full support -/

/-- A coupling inside one `k`-slot fiber.  No independence is assumed. -/
structure FiberCoupling (k d : ℕ) where
  mass : (Fin k → Fin d) → ℝ

namespace FiberCoupling

variable {k d : ℕ}

/-- Every atom tuple remains possible.  This is a support condition, not an independence
condition and not a small-LD condition. -/
def FullSupport (J : FiberCoupling k d) : Prop :=
  ∀ x, J.mass x ≠ 0

/-- A coupled fiber covers a tuple of modulus values when a charged atom tuple realizes
those values. -/
def CoversTuple (family : BundleFamily d) (fiber : Fin k → ℝ)
    (J : FiberCoupling k d) (value : Fin k → ℝ) : Prop :=
  ∃ x : Fin k → Fin d, J.mass x ≠ 0 ∧
    ∀ i, family.modulus (x i) (fiber i) = value i

/-- Coverage determined from the Cartesian product of the one-slot supports. -/
def ProductCovers (family : BundleFamily d) (fiber : Fin k → ℝ)
    (value : Fin k → ℝ) : Prop :=
  ∃ x : Fin k → Fin d, ∀ i, family.modulus (x i) (fiber i) = value i

/-- Under full support, coupled coverage is exactly product coverage. -/
theorem coversTuple_iff_productCovers (family : BundleFamily d) (fiber : Fin k → ℝ)
    (J : FiberCoupling k d) (hfull : J.FullSupport) (value : Fin k → ℝ) :
    CoversTuple family fiber J value ↔ ProductCovers family fiber value := by
  constructor
  · rintro ⟨x, _, hx⟩
    exact ⟨x, hx⟩
  · rintro ⟨x, hx⟩
    exact ⟨x, hfull x, hx⟩

/-- **Coverage invariance, finite and non-perturbative.** Any two full-support couplings
charge exactly the same modulus cells.  LD may change their weights arbitrarily; it cannot
change which cells exist until it kills support. -/
theorem coverage_invariant (family : BundleFamily d) (fiber : Fin k → ℝ)
    (J J' : FiberCoupling k d) (hJ : J.FullSupport) (hJ' : J'.FullSupport)
    (value : Fin k → ℝ) :
    CoversTuple family fiber J value ↔ CoversTuple family fiber J' value := by
  rw [coversTuple_iff_productCovers family fiber J hJ value,
    coversTuple_iff_productCovers family fiber J' hJ' value]

/-- A uniform positive joint-mass floor implies full support. -/
theorem fullSupport_of_uniform_floor (J : FiberCoupling k d) (η : ℝ) (hη : 0 < η)
    (hfloor : ∀ x, η ≤ J.mass x) : J.FullSupport := by
  intro x
  exact ne_of_gt (lt_of_lt_of_le hη (hfloor x))

/-! ### The boundary: where coverage invariance stops

`coverage_invariant` says LD cannot change which modulus cells are charged **until it kills
support**. That clause is doing all the work, and until now nothing in this corpus exhibited
the case where it bites. Without a witness the theorem is a statement whose hypothesis has
never been shown capable of failing, which is the standard this corpus imposes on itself.

The witness is the **modulus-copy coupling**: two loci in perfect LD, the second a copy of
the first. Its joint mass sits on the diagonal, so the floor `η` is zero, and a product cell
that both marginals reach is charged by no joint atom at all.

**The genetic reading, with two corrections the simulation forced.** Coverage is a support
property, so it is invariant under couplings of *arbitrary* strength — any amount of linkage
disequilibrium, any correlation length, any haplotype structure — provided every joint
genotype cell retains positive mass. That half is confirmed: a two-locus sweep in exact
rational arithmetic finds charged cells equal to product cells at **every** `r² < 1`, down to
a smallest genotype-cell mass of `6.25e-20` at `r² = 1 - 2e-9`.

The first draft of this note said "`η = 0` is exactly `r² = 1`, so pruning at `r² = 1` removes
the whole obstruction". **Both halves are false**, and the second failed a second time after
being weakened once. Measured over 8 allele-frequency pairs × 10 values of `D`:

* `r² = 1` requires `pA = pB`. On a `0.1` frequency grid only 9 of 81 pairs can reach it at
  all; `pA = 1/2, pB = 1/10` caps at `r²_max = 1/9`.
* **A vanishing haplotype does not need high `r²`.** Of the 72 configurations carrying a zero
  haplotype at `r² < 1`, **56 lose coverage strictly**, the worst at `pA = 1/10, pB = 9/10`
  with **`r² = 1/81 ≈ 0.0123`**. So losses do not sit inside `r² = 1`, and an `r²` cutoff —
  at any threshold — does not certify the positive-floor hypothesis.
* Complete linkage also costs nothing unless the modulus map separates the genotypes. At
  `p = 1/2` all three genotypes share one modulus value, so there is one cell and nothing to
  lose: 1 charged against 1, against 3 charged against 9 at `p = 3/10` and `p = 1/10`. **The
  one frequency at which `r² = 1` is cleanest is precisely where the modulus statistic sees
  nothing.**

The scalar `r²` is therefore the wrong variable for this boundary in both directions. What
the theorem needs is a positive joint-cell floor, and no `r²` threshold implies one.

**The caveat that matters more than the theorem.** This is a statement about *positive* mass,
and positive is not observable. At `pA = pB = 3/10` with `N = 500,000` samples the rarest
genotype cell is missed with probability `0.22` already at `r² = 0.98`, and with probability
`1.00` at `r² ≥ 0.998`, where observing it would need `N ≈ 6.8e7`. **Empirically coverage is
lost far below `r² = 1`**, at a threshold set by sample size rather than by the population
parameter.

**And linkage is not even the dominant driver.** At `pA = pB = 1/20` with `r² = 0` — perfect
linkage *equilibrium* — the rarest genotype cell has probability `6.25e-6` and `N = 500,000`
loses a modulus cell in 5% of runs. Allele frequency alone breaks empirical coverage with no
LD at all. Going the other way, at `p = 1/20` raising `r²` from `0` to `0.81` *increases* the
rarest cell probability, from `6.25e-6` to `2.26e-5`, because the coupling phase inflates the
rare-rare haplotype: **more LD made coverage easier**. Any design rule phrased purely in `r²`
gets both of these backwards.

Empirical status: **VALIDATED** on the population half, with **two claims corrected and one
practical caveat added**. Exact rational sweep and finite-sample arm in
`proofs/validation/ld_coverage_boundary/`. -/

/-- The witness family: two atoms, values `1` and `0`, hence moduli `0` and `1`. -/
noncomputable def copyWitnessFamily : BundleFamily 2 where
  atomValue := fun j _ ↦ if j = 0 then 1 else 0
  atomMass := fun _ _ ↦ 1 / 2

theorem copyWitnessFamily_modulus (j : Fin 2) (t : ℝ) :
    copyWitnessFamily.modulus j t = if j = 0 then 0 else 1 := by
  simp only [BundleFamily.modulus, copyWitnessFamily]
  split_ifs <;> norm_num

/-- **The modulus-copy coupling**: locus two copies locus one, so only the diagonal carries
    mass. This is perfect LD, and it is the `η = 0` boundary of the floor hypothesis. -/
noncomputable def modulusCopyCoupling : FiberCoupling 2 2 where
  mass := fun x ↦ if x 0 = x 1 then 1 / 2 else 0

/-- The modulus-copy coupling fails full support: the off-diagonal cells are empty. -/
theorem modulusCopyCoupling_not_fullSupport : ¬ modulusCopyCoupling.FullSupport := by
  intro hfull
  have h := hfull (fun i ↦ if i = 0 then 0 else 1)
  unfold modulusCopyCoupling at h
  norm_num at h

/-- The target cell: slot one at modulus `0`, slot two at modulus `1`. -/
def copyWitnessValue : Fin 2 → ℝ := fun i ↦ if i = 0 then 0 else 1

/-- **Both marginals reach the cell**: it is covered by the product. -/
theorem copyWitness_productCovers :
    ProductCovers copyWitnessFamily (fun _ ↦ 0) copyWitnessValue := by
  refine ⟨fun i ↦ if i = 0 then 0 else 1, fun i ↦ ?_⟩
  rw [copyWitnessFamily_modulus]
  unfold copyWitnessValue
  by_cases hi : i = 0 <;> simp [hi]

/-- **The coupling reaches it not at all.**

    Every atom tuple carrying mass is diagonal, and a diagonal tuple assigns the two slots
    the same modulus, while the target cell asks for two different ones. So coverage under
    perfect LD is strictly smaller than product coverage — the exact failure that
    `coverage_invariant`'s support hypothesis excludes. -/
theorem copyWitness_not_coversTuple :
    ¬ CoversTuple copyWitnessFamily (fun _ ↦ 0) modulusCopyCoupling copyWitnessValue := by
  rintro ⟨x, hmass, hx⟩
  have hdiag : x 0 = x 1 := by
    unfold modulusCopyCoupling at hmass
    by_contra hne
    simp [hne] at hmass
  have heq : copyWitnessValue 0 = copyWitnessValue 1 := by
    rw [← hx 0, ← hx 1, hdiag]
  norm_num [copyWitnessValue] at heq

/-- **Coverage invariance is sharp.** The perfect-copy witness covers the target cell
    under the product coupling, fails to cover it under the copy coupling, and the copy
    coupling has no full support. So the support hypothesis of `coverage_invariant`
    cannot be dropped: at a zero joint floor, coverage can fall strictly below product
    coverage. The three conjuncts do not assert that every zero-floor coupling loses this
    particular cell, nor do they restate the positive-floor conclusion of
    `coverage_invariant`. -/
theorem coverage_invariance_sharp :
    ProductCovers copyWitnessFamily (fun _ ↦ 0) copyWitnessValue ∧
      ¬ CoversTuple copyWitnessFamily (fun _ ↦ 0) modulusCopyCoupling copyWitnessValue ∧
      ¬ modulusCopyCoupling.FullSupport :=
  ⟨copyWitness_productCovers, copyWitness_not_coversTuple,
    modulusCopyCoupling_not_fullSupport⟩

/-! ### The interpolation landscape: four rows, and they are genuinely four

The conditional gain of a coupling is claimed upstream to land in exactly four growth
classes — `O(1)`, `log n`, `n^β log n` for `β ∈ (0,1)`, and `n` — with a witness on every
row and matched bounds. Two of the rows have surprising occupants: the **Pisot collapse**,
where the gain stays bounded despite a positive exponent for arithmetic rather than
entropic reasons, and the **heavy-tail ghost**, where renewal sharing gives `α log n` rather
than `n^α` (see `Calibrator.CountingInvariantBlindness`).

What a classification claim needs before it means anything is that its rows are **distinct**,
and that is what is proved here: the four rates are strictly ordered past a point, and the
middle two are separated by a genuine power. Without this the landscape could be four names
for one growth class.

The occupancy claims — that each row is attained by an actual coupling, with matched upper
and lower bounds — are **not** proved here and are not asserted. This section establishes
only that there are four places to be.
measurements.

Empirical status: UNTESTED. The separations are analytic facts about the rate functions, not -/

section GainLandscape

/-- Row one: bounded gain. The Pisot collapse lives here. -/
noncomputable def gainBounded : ℝ → ℝ := fun _ ↦ 1

/-- Row two: logarithmic gain. The heavy-tail ghost and the equicorrelated copula live here. -/
noncomputable def gainLog (n : ℝ) : ℝ := Real.log n

/-- Row three: `n^β log n`, the long-range copula row.

    Named for the **power law in `n`**, not for statistical power: this is a conditional-gain
    rate and takes no significance threshold, because none enters it. The earlier name
    `gainPower` invited exactly that misreading. -/
noncomputable def gainPolynomialRow (β n : ℝ) : ℝ := n ^ β * Real.log n

/-- Row four: linear gain, the fully fresh case. -/
noncomputable def gainLinear (n : ℝ) : ℝ := n

/-- Row one is eventually below row two. -/
theorem gainBounded_lt_gainLog :
    ∀ᶠ n : ℝ in Filter.atTop, gainBounded n < gainLog n := by
  filter_upwards [Real.tendsto_log_atTop.eventually_gt_atTop 1] with n hn
  simpa [gainBounded, gainLog] using hn

/-- Row two is eventually below row three, for every positive exponent. -/
theorem gainLog_lt_gainPower (β : ℝ) (hβ : 0 < β) :
    ∀ᶠ n : ℝ in Filter.atTop, gainLog n < gainPolynomialRow β n := by
  filter_upwards [Filter.eventually_gt_atTop (1 : ℝ)] with n hn1
  have hx : (0 : ℝ) < n := by linarith
  have hlog : 0 < Real.log n := Real.log_pos hn1
  have hpow : 1 < n ^ β := by
    rw [Real.rpow_def_of_pos hx, ← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (mul_pos hlog hβ)
  unfold gainLog gainPolynomialRow
  nlinarith [hlog, hpow]

/-- Row three is eventually below row four, for every exponent strictly below one.

    This is the separation that keeps the middle row from collapsing into the linear one:
    `n^β log n < n` needs `log n < n^(1-β)`, which is the same little-o fact that drives the
    certificate gap elsewhere in this corpus. -/
theorem gainPower_lt_gainLinear (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) :
    ∀ᶠ n : ℝ in Filter.atTop, gainPolynomialRow β n < gainLinear n := by
  have hgap : 0 < 1 - β := by linarith
  have hbound := (isLittleO_log_rpow_atTop hgap).bound (by norm_num : (0:ℝ) < 1 / 2)
  filter_upwards [hbound, Filter.eventually_gt_atTop (1 : ℝ)] with n hn hn1
  have hn0 : (0 : ℝ) < n := by linarith
  have hlog : 0 < Real.log n := Real.log_pos hn1
  have hrpow : 0 < n ^ (1 - β) := Real.rpow_pos_of_pos hn0 _
  have hle : Real.log n ≤ 1 / 2 * n ^ (1 - β) := by
    rw [Real.norm_of_nonneg (le_of_lt hlog), Real.norm_of_nonneg (le_of_lt hrpow)] at hn
    exact hn
  have hstrict : Real.log n < n ^ (1 - β) := by linarith
  have hpowpos : 0 < n ^ β := Real.rpow_pos_of_pos hn0 β
  have hsplit : n ^ β * n ^ (1 - β) = n := by
    rw [← Real.rpow_add hn0]
    simp
  unfold gainPolynomialRow gainLinear
  calc n ^ β * Real.log n < n ^ β * n ^ (1 - β) :=
        mul_lt_mul_of_pos_left hstrict hpowpos
    _ = n := hsplit

/-- **The landscape has four distinct rows.** Past a point the four rates are strictly
    ordered, so the classification is a statement about four different growth classes rather
    than four names for one. -/
theorem gainLandscape_strictly_ordered (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) :
    ∀ᶠ n : ℝ in Filter.atTop,
      gainBounded n < gainLog n ∧ gainLog n < gainPolynomialRow β n ∧
        gainPolynomialRow β n < gainLinear n := by
  filter_upwards [gainBounded_lt_gainLog, gainLog_lt_gainPower β hβ0,
    gainPower_lt_gainLinear β hβ0 hβ1] with n h1 h2 h3
  exact ⟨h1, h2, h3⟩

end GainLandscape

end FiberCoupling

namespace FiniteCoupledPhaseLaw

/-- Forget phases while retaining the coupling whose support controls coverage. -/
def toFiberCoupling {n d : ℕ} (C : FiniteCoupledPhaseLaw n d) : FiberCoupling n d where
  mass := C.mass

/-- Both binary witnesses charge every genotype cell. -/
theorem balancedBinaryOppositePhaseLaw_fullSupport :
    balancedBinaryOppositePhaseLaw.toFiberCoupling.FullSupport := by
  intro x
  norm_num [toFiberCoupling, balancedBinaryOppositePhaseLaw]

theorem biasedBinaryOppositePhaseLaw_fullSupport :
    biasedBinaryOppositePhaseLaw.toFiberCoupling.FullSupport := by
  intro x
  simp only [toFiberCoupling, biasedBinaryOppositePhaseLaw]
  split_ifs <;> norm_num

/-- **Support does not determine oscillatory gain.**  The two laws have full support and
hence identical coverage for every one-slot bundle family, fiber, and value.  Nevertheless
one has exact cancellation (infinite gain) and the other finite gain at frequency one.

For genetics this rules out replacing the two-axis diagnostic by a single LD-support
number: a panel may preserve all genotype cells while its score anti-concentration changes
qualitatively under cell reweighting. -/
theorem same_full_support_coverage_different_gain
    (family : BundleFamily 2) (fiber : Fin 1 → ℝ) (value : Fin 1 → ℝ) :
    (FiberCoupling.CoversTuple family fiber
        balancedBinaryOppositePhaseLaw.toFiberCoupling value ↔
      FiberCoupling.CoversTuple family fiber
        biasedBinaryOppositePhaseLaw.toFiberCoupling value) ∧
      balancedBinaryOppositePhaseLaw.conditionalGainFunctional 1 = ⊤ ∧
      biasedBinaryOppositePhaseLaw.conditionalGainFunctional 1 ≠ ⊤ := by
  refine ⟨FiberCoupling.coverage_invariant family fiber _ _
      balancedBinaryOppositePhaseLaw_fullSupport
      biasedBinaryOppositePhaseLaw_fullSupport value, ?_⟩
  exact ⟨balancedBinaryOppositePhaseLaw_gain_one,
    biasedBinaryOppositePhaseLaw_gain_one_ne_top⟩

end FiniteCoupledPhaseLaw

end Calibrator
