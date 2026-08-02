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
          refine Finset.sum_le_sum fun ω _ => ?_
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

end FiberCoupling

end Calibrator
