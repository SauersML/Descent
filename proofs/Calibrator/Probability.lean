import Mathlib.Tactic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Convex.Strict
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Data.NNReal.Basic
import Mathlib.Data.ENNReal.Basic
import Mathlib.Topology.Compactness.Compact
import Mathlib.Data.Matrix.Reflection
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Probability.ConditionalExpectation
import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.CDF
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions

import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Probability.Independence.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Integral
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.Notation
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Logic.Function.Basic

open scoped InnerProductSpace
open InnerProductSpace

open MeasureTheory
open scoped ENNReal

namespace Calibrator

namespace InformationTheoryBridge

/-- Bernoulli PMF on `Bool`, using mathlib's canonical construction. -/
noncomputable def bernoulliPMF (p : NNReal) (hp : p ≤ 1) : PMF Bool :=
  PMF.bernoulli p hp

/-- Bernoulli probability measure induced by `bernoulliPMF`. -/
noncomputable def bernoulliMeasure (p : NNReal) (hp : p ≤ 1) : Measure Bool :=
  (bernoulliPMF p hp).toMeasure

/-- KL divergence between Bernoulli laws, via `InformationTheory.klDiv`. -/
noncomputable def bernoulliKL (p q : NNReal) (hp : p ≤ 1) (hq : q ≤ 1) : ENNReal :=
  InformationTheory.klDiv (bernoulliMeasure p hp) (bernoulliMeasure q hq)

@[simp] theorem bernoulliKL_self (p : NNReal) (hp : p ≤ 1) :
    bernoulliKL p p hp hp = 0 := by
  simp [bernoulliKL, bernoulliMeasure, bernoulliPMF]

theorem bernoulliKL_eq_zero_iff (p q : NNReal) (hp : p ≤ 1) (hq : q ≤ 1)
    [IsFiniteMeasure (bernoulliMeasure p hp)] [IsFiniteMeasure (bernoulliMeasure q hq)] :
    bernoulliKL p q hp hq = 0 ↔
      bernoulliMeasure p hp = bernoulliMeasure q hq := by
  simpa [bernoulliKL] using
    (InformationTheory.klDiv_eq_zero_iff
      (μ := bernoulliMeasure p hp) (ν := bernoulliMeasure q hq))

/-- Unit interval as a subtype, used for Bernoulli probabilities. -/
abbrev UnitProb := Set.Icc (0 : ℝ) 1

/-- Coercion helper from `[0,1]` real probabilities to `NNReal`. -/
def unitProbToNNReal (p : UnitProb) : NNReal :=
  ⟨p.1, p.2.1⟩

lemma unitProbToNNReal_le_one (p : UnitProb) : unitProbToNNReal p ≤ 1 := by
  change (p.1 : ℝ) ≤ 1
  exact p.2.2

/-- KL divergence between Bernoulli laws parameterized by probabilities in `[0,1]`. -/
noncomputable def klBern (p q : UnitProb) : ENNReal :=
  bernoulliKL (unitProbToNNReal p) (unitProbToNNReal q)
    (unitProbToNNReal_le_one p) (unitProbToNNReal_le_one q)

/-- `klBern` is exactly `InformationTheory.klDiv` on Bernoulli measures. -/
theorem klBern_eq_klDiv (p q : UnitProb) :
    klBern p q =
      InformationTheory.klDiv
        (bernoulliMeasure (unitProbToNNReal p) (unitProbToNNReal_le_one p))
        (bernoulliMeasure (unitProbToNNReal q) (unitProbToNNReal_le_one q)) := by
  simp [klBern, bernoulliKL]

/-- Equivalent PMF-level view of `klBern` (via `toMeasure`). -/
theorem klBern_eq_klDiv_pmf (p q : UnitProb) :
    klBern p q =
      InformationTheory.klDiv
        ((PMF.bernoulli (unitProbToNNReal p) (unitProbToNNReal_le_one p)).toMeasure)
        ((PMF.bernoulli (unitProbToNNReal q) (unitProbToNNReal_le_one q)).toMeasure) := by
  simp [klBern, bernoulliKL, bernoulliMeasure, bernoulliPMF]

end InformationTheoryBridge

/-!
=================================================================
## Part 0: Gaussian Measure Integrability
=================================================================

For any natural number n, the function x^n is integrable with respect to the
standard Gaussian measure. This is foundational for all L² projection arguments.
-/

/-- The standard Gaussian measure μ = N(0,1). -/
noncomputable def stdGaussianMeasure : MeasureTheory.Measure Real := ProbabilityTheory.gaussianReal 0 1

/-- Polynomial function x^n. -/
def poly_n (n : Nat) (x : Real) : Real := x ^ n

/-- For any natural number n, x^n is integrable with respect to the standard Gaussian measure.
    This follows from the finiteness of Gaussian moments. -/
theorem integrable_poly_n (n : Nat) : MeasureTheory.Integrable (poly_n n) stdGaussianMeasure := by
  have h_gauss_integral : ∀ n : ℕ, MeasureTheory.IntegrableOn (fun x : ℝ => x^n * Real.exp (-x^2 / 2)) (Set.univ : Set ℝ) := by
    intro n
    have := @integrable_rpow_mul_exp_neg_mul_sq
    simpa [ div_eq_inv_mul ] using @this ( 1 / 2 ) ( by norm_num ) n ( by linarith )
  unfold poly_n
  unfold stdGaussianMeasure
  simp_all +decide [ProbabilityTheory.gaussianReal]
  refine' MeasureTheory.Integrable.mono' _ _ _
  refine' fun x => |x ^ n|
  · refine' MeasureTheory.Integrable.abs _
    rw [ MeasureTheory.integrable_withDensity_iff ]
    · convert h_gauss_integral n |> fun h => h.div_const ( Real.sqrt ( 2 * Real.pi ) ) using 2 ; norm_num [ ProbabilityTheory.gaussianPDF ] ; ring
      norm_num [ ProbabilityTheory.gaussianPDFReal ] ; ring
      rw [ ENNReal.toReal_ofReal ( Real.exp_nonneg _ ) ]
    · fun_prop
    · simp [ProbabilityTheory.gaussianPDF]
  · exact Continuous.aestronglyMeasurable ( by continuity )
  · exact Filter.Eventually.of_forall fun x => Real.norm_eq_abs _ ▸ le_rfl

/-- x^2 is integrable with respect to the standard Gaussian measure. -/
theorem integrable_sq_gaussian : MeasureTheory.Integrable (fun x => x ^ 2) stdGaussianMeasure := by
  apply integrable_poly_n 2

/-- x is integrable with respect to the standard Gaussian measure. -/
theorem integrable_id_gaussian : MeasureTheory.Integrable (fun x => x) stdGaussianMeasure := by
  have h := integrable_poly_n 1
  unfold poly_n at h
  simp only [pow_one] at h
  exact h

/-- x^4 is integrable with respect to the standard Gaussian measure (useful for variance calculations). -/
theorem integrable_pow4_gaussian : MeasureTheory.Integrable (fun x => x ^ 4) stdGaussianMeasure := by
  apply integrable_poly_n 4

/-- If f is integrable on μ and g is integrable on ν, then f(x) * g(y) is integrable on μ.prod ν.
    This is essential for Fubini-type arguments on product measures. -/
theorem integrable_prod_mul {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} [SigmaFinite μ] [SigmaFinite ν]
    (f : X → ℝ) (g : Y → ℝ) (hf : Integrable f μ) (hg : Integrable g ν) :
    Integrable (fun p : X × Y => f p.1 * g p.2) (μ.prod ν) := by
  exact hf.mul_prod hg

/-!
=================================================================
## Part 1: Definitions
=================================================================
-/

variable {Ω : Type*} [MeasureSpace Ω] {ℙ : Measure Ω} [IsProbabilityMeasure ℙ]

def Phenotype := Ω → ℝ
def PGS := Ω → ℝ
def PC (k : ℕ) := Ω → (Fin k → ℝ)

structure RealizedData (n k : ℕ) where
  y : Fin n → ℝ
  p : Fin n → ℝ
  c : Fin n → (Fin k → ℝ)

/-! ### Discrete Genotypes, Hardy-Weinberg Equilibrium, and Score Approximation

This block replaces the "score is Gaussian by assumption" shortcut with a discrete
genotype model. Each locus is diploid with genotype in `{0, 1, 2}` alternative alleles.
Hardy-Weinberg equilibrium determines the one-locus genotype law, and polygenic scores
are finite weighted sums of these bounded random variables.

The Gaussian score formulas are then interpreted as approximations with an explicit
Berry-Esseen-style error term rather than as exact biology.
-/

/-- Diploid genotype state at a biallelic locus. -/
inductive DiploidGenotype
  | homRef
  | het
  | homAlt
  deriving DecidableEq, Fintype, Repr

/-- Concrete enumeration of diploid genotypes by `Fin 3`. -/
def DiploidGenotype.equivFin3 : DiploidGenotype ≃ Fin 3 where
  toFun
    | .homRef => 0
    | .het => 1
    | .homAlt => 2
  invFun
    | ⟨0, _⟩ => .homRef
    | ⟨1, _⟩ => .het
    | ⟨2, _⟩ => .homAlt
  left_inv g := by
    cases g <;> rfl
  right_inv i := by
    fin_cases i <;> rfl

@[simp] theorem DiploidGenotype.equivFin3_symm_apply (i : Fin 3) :
    DiploidGenotype.equivFin3.symm i =
      match i with
      | ⟨0, _⟩ => DiploidGenotype.homRef
      | ⟨1, _⟩ => DiploidGenotype.het
      | ⟨2, _⟩ => DiploidGenotype.homAlt := by
  fin_cases i <;> rfl

@[simp] theorem DiploidGenotype.equivFin3_symm_apply_apply (g : DiploidGenotype) :
    DiploidGenotype.equivFin3.symm (DiploidGenotype.equivFin3 g) = g := by
  exact DiploidGenotype.equivFin3.left_inv g

/-- Number of alternative alleles carried by a diploid genotype. -/
def altAlleleCount : DiploidGenotype → ℝ
  | .homRef => 0
  | .het => 1
  | .homAlt => 2

/-- One-locus Hardy-Weinberg model with alternative-allele frequency `q ∈ [0,1]`. -/
structure HardyWeinbergModel where
  altFreq : ℝ
  altFreq_nonneg : 0 ≤ altFreq
  altFreq_le_one : altFreq ≤ 1

/-- Reference-allele frequency `p = 1 - q`. -/
def HardyWeinbergModel.refFreq (h : HardyWeinbergModel) : ℝ :=
  1 - h.altFreq

theorem HardyWeinbergModel.refFreq_nonneg (h : HardyWeinbergModel) :
    0 ≤ h.refFreq := by
  unfold HardyWeinbergModel.refFreq
  linarith [h.altFreq_le_one]

theorem HardyWeinbergModel.refFreq_le_one (h : HardyWeinbergModel) :
    h.refFreq ≤ 1 := by
  unfold HardyWeinbergModel.refFreq
  linarith [h.altFreq_nonneg]

/-- Hardy-Weinberg genotype probabilities:
`P(AA) = p^2`, `P(Aa) = 2pq`, `P(aa) = q^2`, where `q` is the alternative-allele frequency. -/
def HardyWeinbergModel.genotypeProb (h : HardyWeinbergModel) : DiploidGenotype → ℝ
  | .homRef => h.refFreq ^ 2
  | .het => 2 * h.refFreq * h.altFreq
  | .homAlt => h.altFreq ^ 2

theorem HardyWeinbergModel.genotypeProb_nonneg
    (h : HardyWeinbergModel) (g : DiploidGenotype) :
    0 ≤ h.genotypeProb g := by
  cases g with
  | homRef =>
      simp [HardyWeinbergModel.genotypeProb, sq_nonneg]
  | het =>
      simp [HardyWeinbergModel.genotypeProb]
      nlinarith [h.refFreq_nonneg, h.altFreq_nonneg]
  | homAlt =>
      simp [HardyWeinbergModel.genotypeProb, sq_nonneg]

/-- Hardy-Weinberg genotype probabilities sum to `1`. -/
theorem HardyWeinbergModel.genotypeProb_sum (h : HardyWeinbergModel) :
    (∑ g : DiploidGenotype, h.genotypeProb g) = 1 := by
  have hsum : h.refFreq + h.altFreq = 1 := by
    unfold HardyWeinbergModel.refFreq
    ring
  have hrewrite :
      (∑ g : DiploidGenotype, h.genotypeProb g) =
        ∑ i : Fin 3, h.genotypeProb (DiploidGenotype.equivFin3.symm i) := by
    exact Fintype.sum_equiv DiploidGenotype.equivFin3 _ _ (by
      intro x
      rw [DiploidGenotype.equivFin3_symm_apply_apply])
  rw [hrewrite]
  rw [Fin.sum_univ_three]
  simp [DiploidGenotype.equivFin3, HardyWeinbergModel.genotypeProb]
  calc
    h.refFreq ^ 2 + 2 * h.refFreq * h.altFreq + h.altFreq ^ 2
        = (h.refFreq + h.altFreq) ^ 2 := by ring
    _ = 1 := by rw [hsum]; norm_num

/-- Expected alternative-allele count under Hardy-Weinberg equilibrium. -/
noncomputable def HardyWeinbergModel.expectedAltAlleleCount (h : HardyWeinbergModel) : ℝ :=
  ∑ g : DiploidGenotype, altAlleleCount g * h.genotypeProb g

theorem HardyWeinbergModel.expectedAltAlleleCount_eq
    (h : HardyWeinbergModel) :
    h.expectedAltAlleleCount = 2 * h.altFreq := by
  have hsum : h.refFreq + h.altFreq = 1 := by
    unfold HardyWeinbergModel.refFreq
    ring
  unfold HardyWeinbergModel.expectedAltAlleleCount
  have hrewrite :
      (∑ g : DiploidGenotype, altAlleleCount g * h.genotypeProb g) =
        ∑ i : Fin 3, altAlleleCount (DiploidGenotype.equivFin3.symm i) *
          h.genotypeProb (DiploidGenotype.equivFin3.symm i) := by
    exact Fintype.sum_equiv DiploidGenotype.equivFin3 _ _ (by
      intro x
      rw [DiploidGenotype.equivFin3_symm_apply_apply])
  rw [hrewrite]
  rw [Fin.sum_univ_three]
  simp [DiploidGenotype.equivFin3, HardyWeinbergModel.genotypeProb]
  calc
    altAlleleCount DiploidGenotype.homRef * h.refFreq ^ 2 +
        altAlleleCount DiploidGenotype.het * (2 * h.refFreq * h.altFreq) +
        altAlleleCount DiploidGenotype.homAlt * h.altFreq ^ 2
        = 2 * (h.refFreq * h.altFreq) + 2 * h.altFreq ^ 2 := by
          simp [altAlleleCount]
          ring
    _ 
        = 2 * h.altFreq * (h.refFreq + h.altFreq) := by ring
    _ = 2 * h.altFreq := by rw [hsum]; ring

/-- Centered alternative-allele count at one locus. -/
noncomputable def HardyWeinbergModel.centeredAltAlleleCount
    (h : HardyWeinbergModel) (g : DiploidGenotype) : ℝ :=
  altAlleleCount g - h.expectedAltAlleleCount

/-- One-locus genotype variance under Hardy-Weinberg equilibrium. -/
noncomputable def HardyWeinbergModel.genotypeVariance (h : HardyWeinbergModel) : ℝ :=
  ∑ g : DiploidGenotype,
    h.genotypeProb g * (h.centeredAltAlleleCount g) ^ 2

theorem HardyWeinbergModel.genotypeVariance_eq
    (h : HardyWeinbergModel) :
    h.genotypeVariance = 2 * h.altFreq * h.refFreq := by
  have hsum : h.refFreq + h.altFreq = 1 := by
    unfold HardyWeinbergModel.refFreq
    ring
  unfold HardyWeinbergModel.genotypeVariance HardyWeinbergModel.centeredAltAlleleCount
  rw [h.expectedAltAlleleCount_eq]
  have hrewrite :
      (∑ g : DiploidGenotype, h.genotypeProb g * (altAlleleCount g - 2 * h.altFreq) ^ 2) =
        ∑ i : Fin 3,
          h.genotypeProb (DiploidGenotype.equivFin3.symm i) *
            (altAlleleCount (DiploidGenotype.equivFin3.symm i) - 2 * h.altFreq) ^ 2 := by
    exact Fintype.sum_equiv DiploidGenotype.equivFin3 _ _ (by
      intro x
      rw [DiploidGenotype.equivFin3_symm_apply_apply])
  rw [hrewrite]
  rw [Fin.sum_univ_three]
  simp [DiploidGenotype.equivFin3, HardyWeinbergModel.genotypeProb, altAlleleCount]
  unfold HardyWeinbergModel.refFreq
  ring_nf

/-- Absolute third centered moment at one Hardy-Weinberg locus. This is the term that
enters the Berry-Esseen numerator for weighted sums of bounded genotype variables. -/
noncomputable def HardyWeinbergModel.genotypeThirdAbsMoment
    (h : HardyWeinbergModel) : ℝ :=
  ∑ g : DiploidGenotype,
    h.genotypeProb g * |h.centeredAltAlleleCount g| ^ 3

theorem HardyWeinbergModel.genotypeThirdAbsMoment_nonneg
    (h : HardyWeinbergModel) :
    0 ≤ h.genotypeThirdAbsMoment := by
  unfold HardyWeinbergModel.genotypeThirdAbsMoment
  refine Finset.sum_nonneg ?_
  intro g _
  exact mul_nonneg (h.genotypeProb_nonneg g) (by positivity)

/-- A diploid genome over `m` loci. -/
abbrev DiscreteGenome (m : ℕ) := Fin m → DiploidGenotype

/-- Polygenic score as a weighted sum of discrete allele counts. -/
noncomputable def polygenicScoreOfGenome {m : ℕ} [Fintype (Fin m)]
    (beta : Fin m → ℝ) (genome : DiscreteGenome m) : ℝ :=
  ∑ i : Fin m, beta i * altAlleleCount (genome i)

/-- Locuswise Hardy-Weinberg panel for a polygenic score architecture. -/
structure HWEScoreModel (m : ℕ) where
  alleleFreq : Fin m → HardyWeinbergModel
  effect : Fin m → ℝ

/-- Exact HWE score mean from one-locus expectations. -/
noncomputable def HWEScoreModel.scoreMean {m : ℕ} [Fintype (Fin m)]
    (model : HWEScoreModel m) : ℝ :=
  ∑ i : Fin m, model.effect i * (model.alleleFreq i).expectedAltAlleleCount

/-- Exact HWE score variance under locus independence. -/
noncomputable def HWEScoreModel.scoreVariance {m : ℕ} [Fintype (Fin m)]
    (model : HWEScoreModel m) : ℝ :=
  ∑ i : Fin m, (model.effect i) ^ 2 * (model.alleleFreq i).genotypeVariance

/-- Berry-Esseen numerator for the weighted HWE score under locus independence. -/
noncomputable def HWEScoreModel.scoreThirdAbsMomentBound {m : ℕ} [Fintype (Fin m)]
    (model : HWEScoreModel m) : ℝ :=
  ∑ i : Fin m, |model.effect i| ^ 3 * (model.alleleFreq i).genotypeThirdAbsMoment

theorem HWEScoreModel.scoreVariance_nonneg {m : ℕ} [Fintype (Fin m)]
    (model : HWEScoreModel m) :
    0 ≤ model.scoreVariance := by
  unfold HWEScoreModel.scoreVariance
  refine Finset.sum_nonneg ?_
  intro i _
  have hvar_nonneg : 0 ≤ (model.alleleFreq i).genotypeVariance := by
    rw [(model.alleleFreq i).genotypeVariance_eq]
    exact mul_nonneg (mul_nonneg (by norm_num) (model.alleleFreq i).altFreq_nonneg)
      ((model.alleleFreq i).refFreq_nonneg)
  exact mul_nonneg (sq_nonneg (model.effect i)) hvar_nonneg

theorem HWEScoreModel.scoreThirdAbsMomentBound_nonneg {m : ℕ} [Fintype (Fin m)]
    (model : HWEScoreModel m) :
    0 ≤ model.scoreThirdAbsMomentBound := by
  unfold HWEScoreModel.scoreThirdAbsMomentBound
  refine Finset.sum_nonneg ?_
  intro i _
  exact mul_nonneg (by positivity)
    ((model.alleleFreq i).genotypeThirdAbsMoment_nonneg)

/-- Berry-Esseen error term for a centered score with variance `σ²` and third-moment sum `ρ₃`.
We write the denominator as `σ² * sqrt(σ²)` to stay inside the existing real-analysis library. -/
noncomputable def berryEsseenErrorBound (berryEsseenConstant variance thirdMomentSum : ℝ) : ℝ :=
  berryEsseenConstant * thirdMomentSum / (variance * Real.sqrt variance)

theorem berryEsseenErrorBound_nonneg
    (berryEsseenConstant variance thirdMomentSum : ℝ)
    (hC : 0 ≤ berryEsseenConstant)
    (hVar : 0 ≤ variance)
    (hThird : 0 ≤ thirdMomentSum) :
    0 ≤ berryEsseenErrorBound berryEsseenConstant variance thirdMomentSum := by
  unfold berryEsseenErrorBound
  by_cases hzero : variance * Real.sqrt variance = 0
  · simp [hzero]
  · exact div_nonneg (mul_nonneg hC hThird) (mul_nonneg hVar (Real.sqrt_nonneg _))

/-- Berry-Esseen error bound specialized to the HWE score model. -/
noncomputable def HWEScoreModel.berryEsseenErrorBound {m : ℕ} [Fintype (Fin m)]
    (model : HWEScoreModel m) (berryEsseenConstant : ℝ) : ℝ :=
  Calibrator.berryEsseenErrorBound
    berryEsseenConstant model.scoreVariance model.scoreThirdAbsMomentBound

theorem HWEScoreModel.berryEsseenErrorBound_nonneg {m : ℕ} [Fintype (Fin m)]
    (model : HWEScoreModel m) (berryEsseenConstant : ℝ)
    (hC : 0 ≤ berryEsseenConstant) :
    0 ≤ model.berryEsseenErrorBound berryEsseenConstant := by
  exact Calibrator.berryEsseenErrorBound_nonneg
    berryEsseenConstant model.scoreVariance model.scoreThirdAbsMomentBound
    hC (model.scoreVariance_nonneg) (model.scoreThirdAbsMomentBound_nonneg)

/-- A pointwise CDF-approximation certificate. This is the interface needed to transport
Berry-Esseen bounds into liability-threshold, AUC, and `R²` error envelopes. -/
structure CdfApproximationCertificate where
  exactCdf : ℝ → ℝ
  approxCdf : ℝ → ℝ
  epsilon : ℝ
  epsilon_nonneg : 0 ≤ epsilon
  pointwise_error : ∀ x : ℝ, |exactCdf x - approxCdf x| ≤ epsilon

/-- If a score CDF is within `ε` of an approximating CDF at threshold `t`,
then the corresponding tail probability is also within `ε`. -/
theorem tail_probability_error_of_cdf_error
    (cert : CdfApproximationCertificate) (t : ℝ) :
    |((1 - cert.exactCdf t) - (1 - cert.approxCdf t))| ≤ cert.epsilon := by
  have h := cert.pointwise_error t
  calc
    |((1 - cert.exactCdf t) - (1 - cert.approxCdf t))|
        = |-(cert.exactCdf t - cert.approxCdf t)| := by ring_nf
    _ = |cert.exactCdf t - cert.approxCdf t| := by rw [abs_neg]
    _ ≤ cert.epsilon := h

/-- Closed interval of values consistent with an approximation center and error radius. -/
def approximationInterval (center epsilon : ℝ) : Set ℝ :=
  Set.Icc (center - epsilon) (center + epsilon)

/-- Any quantity within absolute error `ε` belongs to the corresponding approximation interval. -/
theorem mem_approximationInterval_of_abs_sub_le
    (x center epsilon : ℝ)
    (_heps : 0 ≤ epsilon)
    (h : |x - center| ≤ epsilon) :
    x ∈ approximationInterval center epsilon := by
  unfold approximationInterval
  constructor <;> linarith [abs_le.mp h |>.1, abs_le.mp h |>.2]

/-- AUC approximation envelope from a Gaussian center and a Berry-Esseen error radius. -/
def aucApproximationInterval (aucGaussian epsilon : ℝ) : Set ℝ :=
  approximationInterval aucGaussian epsilon

/-- `R²` approximation envelope from a Gaussian center and a Berry-Esseen error radius. -/
def r2ApproximationInterval (r2Gaussian epsilon : ℝ) : Set ℝ :=
  approximationInterval r2Gaussian epsilon

noncomputable def stdNormalProdMeasure (k : ℕ) [Fintype (Fin k)] : Measure (ℝ × (Fin k → ℝ)) :=
  (ProbabilityTheory.gaussianReal 0 1).prod (Measure.pi (fun (_ : Fin k) => ProbabilityTheory.gaussianReal 0 1))

instance stdNormalProdMeasure_is_prob {k : ℕ} [Fintype (Fin k)] : IsProbabilityMeasure (stdNormalProdMeasure k) := by
  unfold stdNormalProdMeasure
  infer_instance

/-! ### Measure-Theoretic Environment and Gaussian Noise

This block sets up a canonical random-variable environment for disease modeling:
- `Ω_k = ℝ × ℝ^k × ℝ`, with coordinates `(S, x, E)`
- `S`: score coordinate, interpreted either as an exact score or as a Gaussian approximation center
- `x`: principal-component coordinates
- `E`: environmental noise

The key assumption is heteroscedastic Gaussian noise:
`E | x ~ N(0, σ²(x))`.
Integrating out `E` then yields conditional probabilities through Gaussian CDFs (`Φ`). -/

/-- Canonical sample space with score `S`, PCs `x`, and environmental noise `E`. -/
abbrev OmegaRV (k : ℕ) := ℝ × (Fin k → ℝ) × ℝ

/-- Score coordinate on `Ω_k`. -/
def scoreRV {k : ℕ} (ω : OmegaRV k) : ℝ := ω.1

/-- PC-coordinate vector on `Ω_k`. -/
def pcRV {k : ℕ} (ω : OmegaRV k) : Fin k → ℝ := ω.2.1

/-- Environmental noise coordinate on `Ω_k`. -/
def envNoiseRV {k : ℕ} (ω : OmegaRV k) : ℝ := ω.2.2

/-- Standard normal CDF, written as `Φ`. -/
noncomputable def Phi : ℝ → ℝ := ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1)

/-- Heteroscedastic Gaussian noise assumption:
for each ancestry coordinate `x`, the environmental noise follows `N(0, σ²(x))`. -/
structure GaussianNoiseAssumption (k : ℕ) where
  sigma2 : (Fin k → ℝ) → NNReal

/-- Conditional noise law `E | x`. -/
noncomputable def noiseMeasureGivenX {k : ℕ}
    (hN : GaussianNoiseAssumption k) (x : Fin k → ℝ) : Measure ℝ :=
  ProbabilityTheory.gaussianReal 0 (hN.sigma2 x)

instance noiseMeasureGivenX_isProb {k : ℕ}
    (hN : GaussianNoiseAssumption k) (x : Fin k → ℝ) :
    IsProbabilityMeasure (noiseMeasureGivenX hN x) := by
  unfold noiseMeasureGivenX
  infer_instance

/-- Integrating out Gaussian environmental noise gives a Gaussian CDF at threshold `t`:
`P(μ + E ≤ t | x) = CDF_{N(μ,σ²(x))}(t)`. -/
theorem noise_integrated_cdf {k : ℕ} (hN : GaussianNoiseAssumption k)
    (x : Fin k → ℝ) (μ t : ℝ) :
    noiseMeasureGivenX hN x {e : ℝ | μ + e ≤ t} =
      ENNReal.ofReal (ProbabilityTheory.cdf
        (ProbabilityTheory.gaussianReal μ (hN.sigma2 x)) t) := by
  calc
    noiseMeasureGivenX hN x {e : ℝ | μ + e ≤ t}
        = ((noiseMeasureGivenX hN x).map (fun e : ℝ => μ + e)) (Set.Iic t) := by
            rw [Measure.map_apply (by fun_prop) measurableSet_Iic]
            rfl
    _ = (ProbabilityTheory.gaussianReal μ (hN.sigma2 x)) (Set.Iic t) := by
          simp [noiseMeasureGivenX, ProbabilityTheory.gaussianReal_map_const_add]
    _ = ENNReal.ofReal (ProbabilityTheory.cdf
          (ProbabilityTheory.gaussianReal μ (hN.sigma2 x)) t) := by
          symm
          simpa using (ProbabilityTheory.ofReal_cdf
            (μ := ProbabilityTheory.gaussianReal μ (hN.sigma2 x)) t)

/-- In particular at threshold `0`, integrating out `E` yields a probit-form conditional probability. -/
theorem noise_integrated_cdf_zero {k : ℕ} (hN : GaussianNoiseAssumption k)
    (x : Fin k → ℝ) (μ : ℝ) :
    noiseMeasureGivenX hN x {e : ℝ | μ + e ≤ 0} =
      ENNReal.ofReal (ProbabilityTheory.cdf
        (ProbabilityTheory.gaussianReal μ (hN.sigma2 x)) 0) := by
  simpa using noise_integrated_cdf hN x μ 0

/-! ### Biological Truth: Liability Threshold Model -/

/-- Latent liability `L = S + E`. -/
def latentLiability (s e : ℝ) : ℝ := s + e

/-- Disease event under an ancestry-dependent threshold: `L > T(x)`. -/
def diseaseEvent {k : ℕ} (T : (Fin k → ℝ) → ℝ) (x : Fin k → ℝ) (s : ℝ) : Set ℝ :=
  {e : ℝ | latentLiability s e > T x}

/-- Indicator form of the binary disease outcome:
`Y = 𝟙(L > T(x))`. -/
noncomputable def diseaseIndicator {k : ℕ} (T : (Fin k → ℝ) → ℝ) (x : Fin k → ℝ) (s e : ℝ) : ℝ :=
  if latentLiability s e > T x then 1 else 0

/-- Exact threshold-event probability after integrating Gaussian environmental noise:
`P(Y=1 | S=s, x) = 1 - P(L ≤ T(x) | S=s, x)`. -/
theorem liability_threshold_probit_raw {k : ℕ} (hN : GaussianNoiseAssumption k)
    (T : (Fin k → ℝ) → ℝ) (x : Fin k → ℝ) (s : ℝ) :
    noiseMeasureGivenX hN x (diseaseEvent T x s) =
      1 - ENNReal.ofReal (ProbabilityTheory.cdf
        (ProbabilityTheory.gaussianReal s (hN.sigma2 x)) (T x)) := by
  have h_le :
      noiseMeasureGivenX hN x {e : ℝ | latentLiability s e ≤ T x} =
        ENNReal.ofReal (ProbabilityTheory.cdf
          (ProbabilityTheory.gaussianReal s (hN.sigma2 x)) (T x)) := by
    simpa [latentLiability] using noise_integrated_cdf hN x s (T x)
  have h_le_set :
      ({e : ℝ | latentLiability s e ≤ T x} : Set ℝ) = Set.Iic (T x - s) := by
    ext e
    constructor
    · intro h
      change e ≤ T x - s
      have hsle : latentLiability s e ≤ T x := by simpa using h
      dsimp [latentLiability] at hsle
      linarith
    · intro h
      change latentLiability s e ≤ T x
      have hle : e ≤ T x - s := by simpa [Set.mem_Iic] using h
      dsimp [latentLiability]
      linarith
  have h_event :
      diseaseEvent T x s = (Set.Iic (T x - s))ᶜ := by
    ext e
    constructor
    · intro h
      change ¬ e ≤ T x - s
      intro hle
      have hsle : s + e ≤ T x := by linarith
      exact (not_le_of_gt h) hsle
    · intro h
      change s + e > T x
      by_contra hnot
      have hsle : s + e ≤ T x := le_of_not_gt hnot
      have hle : e ≤ T x - s := by linarith
      exact h hle
  have h_meas_le : MeasurableSet (Set.Iic (T x - s) : Set ℝ) := measurableSet_Iic
  have h_le' :
      noiseMeasureGivenX hN x (Set.Iic (T x - s)) =
        ENNReal.ofReal (ProbabilityTheory.cdf
          (ProbabilityTheory.gaussianReal s (hN.sigma2 x)) (T x)) := by
    simpa [h_le_set] using h_le
  rw [h_event]
  rw [measure_compl (s := (Set.Iic (T x - s) : Set ℝ)) h_meas_le
    (measure_ne_top (noiseMeasureGivenX hN x) _)]
  rw [measure_univ, h_le']

/-- Real-valued form of the liability-threshold probability:
`P(Y=1 | S=s, x) = 1 - CDF_{N(s,σ²(x))}(T(x))`. -/
theorem liability_threshold_probit_real {k : ℕ} (hN : GaussianNoiseAssumption k)
    (T : (Fin k → ℝ) → ℝ) (x : Fin k → ℝ) (s : ℝ) :
    (noiseMeasureGivenX hN x (diseaseEvent T x s)).toReal =
      1 - ProbabilityTheory.cdf
        (ProbabilityTheory.gaussianReal s (hN.sigma2 x)) (T x) := by
  rw [liability_threshold_probit_raw hN T x s]
  have h_le :
      ENNReal.ofReal
        (ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal s (hN.sigma2 x)) (T x))
      ≤ (1 : ENNReal) := by
    exact_mod_cast
      (ProbabilityTheory.cdf_le_one
        (μ := ProbabilityTheory.gaussianReal s (hN.sigma2 x)) (T x))
  rw [ENNReal.toReal_sub_of_le h_le (by simp)]
  simp [ProbabilityTheory.cdf_nonneg]

/-- Conditional disease probability under the liability-threshold model. -/
noncomputable def etaLiabilityThreshold {k : ℕ} (hN : GaussianNoiseAssumption k)
    (T : (Fin k → ℝ) → ℝ) (s : ℝ) (x : Fin k → ℝ) : ℝ :=
  (noiseMeasureGivenX hN x (diseaseEvent T x s)).toReal

/-- Under `E|X=x ~ N(0,σ²(x))` and `Y = 1{S+E>T(x)}`, the true conditional
probability is the Gaussian-threshold expression. -/
theorem etaLiabilityThreshold_eq_gaussian_threshold {k : ℕ} (hN : GaussianNoiseAssumption k)
    (T : (Fin k → ℝ) → ℝ) (s : ℝ) (x : Fin k → ℝ) :
    etaLiabilityThreshold hN T s x =
      1 - ProbabilityTheory.cdf
        (ProbabilityTheory.gaussianReal s (hN.sigma2 x)) (T x) := by
  exact liability_threshold_probit_real hN T x s

structure PGSBasis (p : ℕ) where
  B : Fin (p + 1) → (ℝ → ℝ)
  B_zero_is_one : B 0 = fun _ => 1

structure SplineBasis (n : ℕ) where
  b : Fin n → (ℝ → ℝ)

def linearPGSBasis : PGSBasis 1 where
  B := fun m => if h : m = 0 then (fun _ => 1) else (fun p_val => p_val)
  B_zero_is_one := by simp

def polynomialSplineBasis (num_basis_funcs : ℕ) : SplineBasis num_basis_funcs where
  b := fun i x => x ^ (i.val + 1)

def SmoothFunction (n : ℕ) := Fin n → ℝ

def evalSmooth {n : ℕ} [Fintype (Fin n)] (s : SplineBasis n) (coeffs : SmoothFunction n) (x : ℝ) : ℝ :=
  ∑ i : Fin n, coeffs i * s.b i x

inductive LinkFunction | logit | identity
inductive DistributionFamily | Bernoulli | Gaussian

structure PhenotypeInformedGAM (p k sp : ℕ) where
  pgsBasis : PGSBasis p
  pcSplineBasis : SplineBasis sp
  γ₀₀ : ℝ
  γₘ₀ : Fin p → ℝ
  f₀ₗ : Fin k → SmoothFunction sp
  fₘₗ : Fin p → Fin k → SmoothFunction sp
  link : LinkFunction
  dist : DistributionFamily

noncomputable def linearPredictor {p k sp : ℕ} [Fintype (Fin p)] [Fintype (Fin k)] [Fintype (Fin sp)] (model : PhenotypeInformedGAM p k sp) (pgs_val : ℝ) (pc_val : Fin k → ℝ) : ℝ :=
  let baseline_effect := model.γ₀₀ + ∑ l, evalSmooth model.pcSplineBasis (model.f₀ₗ l) (pc_val l)
  let pgs_related_effects := ∑ m : Fin p,
    let pgs_basis_val := model.pgsBasis.B ⟨m.val + 1, by linarith [m.isLt]⟩ pgs_val
    let pgs_coeff := model.γₘ₀ m + ∑ l, evalSmooth model.pcSplineBasis (model.fₘₗ m l) (pc_val l)
    pgs_coeff * pgs_basis_val
  baseline_effect + pgs_related_effects

/-! ### Predictor Decomposition for p=1 Models

For models with a single PGS basis function (p=1), we can decompose the linear predictor
into `base(c) + slope(c) * p`, which is the natural form for L² projection / normal equations.
This decomposition is the gateway to proving shrinkage_effect and raw_score_bias theorems. -/

/-- The intercept term of the predictor (not multiplied by p).
    For a p=1 model: base(c) = γ₀₀ + Σₗ evalSmooth(f₀ₗ[l], c[l]) -/
noncomputable def predictorBase {k sp : ℕ} [Fintype (Fin k)] [Fintype (Fin sp)]
    (model : PhenotypeInformedGAM 1 k sp) (pc_val : Fin k → ℝ) : ℝ :=
  model.γ₀₀ + ∑ l, evalSmooth model.pcSplineBasis (model.f₀ₗ l) (pc_val l)

/-- The slope coefficient in front of p.
    For a p=1 model with linear PGS basis: slope(c) = γₘ₀[0] + Σₗ evalSmooth(fₘₗ[0,l], c[l]) -/
noncomputable def predictorSlope {k sp : ℕ} [Fintype (Fin k)] [Fintype (Fin sp)]
    (model : PhenotypeInformedGAM 1 k sp) (pc_val : Fin k → ℝ) : ℝ :=
  model.γₘ₀ 0 + ∑ l, evalSmooth model.pcSplineBasis (model.fₘₗ 0 l) (pc_val l)

/-- Helper: sum over Fin 1 collapses to the single term. -/
lemma Fin1_sum_eq {α : Type*} [AddCommMonoid α] (f : Fin 1 → α) :
    ∑ m : Fin 1, f m = f 0 := by
  simp

/-- **Predictor Decomposition Lemma**: For a p=1 model with linear PGS basis (B[1] = id),
    the linear predictor decomposes as: linearPredictor(p, c) = base(c) + slope(c) * p.

    This is the key lemma that reduces the GAM structure to a 2-parameter linear form in p,
    enabling L² projection / normal equations analysis. -/
theorem linearPredictor_decomp {k sp : ℕ} [Fintype (Fin k)] [Fintype (Fin sp)]
    (model : PhenotypeInformedGAM 1 k sp)
    (h_linear_basis : model.pgsBasis.B ⟨1, by norm_num⟩ = id) :
  ∀ pgs_val pc_val, linearPredictor model pgs_val pc_val =
    predictorBase model pc_val + predictorSlope model pc_val * pgs_val := by
  classical
  intro pgs_val pc_val
  unfold linearPredictor predictorBase predictorSlope
  -- Expand the `let`s and rewrite the `Fin 1` sum to the single `m = 0` term.
  dsimp
  have hsum :
      (∑ m : Fin 1,
          let pgs_basis_val := model.pgsBasis.B ⟨m.val + 1, by linarith [m.isLt]⟩ pgs_val
          let pgs_coeff :=
            model.γₘ₀ m + ∑ l, evalSmooth model.pcSplineBasis (model.fₘₗ m l) (pc_val l)
          pgs_coeff * pgs_basis_val) =
        (let m0 : Fin 1 := 0
         let pgs_basis_val := model.pgsBasis.B ⟨m0.val + 1, by linarith [m0.isLt]⟩ pgs_val
         let pgs_coeff :=
           model.γₘ₀ m0 + ∑ l, evalSmooth model.pcSplineBasis (model.fₘₗ m0 l) (pc_val l)
         pgs_coeff * pgs_basis_val) := by
    simp
  rw [hsum]
  -- Simplify the remaining `let`s, then use the linear-basis hypothesis to rewrite the basis evaluation.
  dsimp
  have hB : model.pgsBasis.B (1 : Fin 2) pgs_val = pgs_val := by
    have hidx1 : (1 : Fin 2) = ⟨1, by norm_num⟩ := by
      ext; simp
    rw [hidx1, h_linear_basis]
    rfl
  -- Replace `B[1] p` by `p`; the remaining goal is definitional.
  rw [hB]


noncomputable def predict {p k sp : ℕ} [Fintype (Fin p)] [Fintype (Fin k)] [Fintype (Fin sp)] (model : PhenotypeInformedGAM p k sp) (pgs_val : ℝ) (pc_val : Fin k → ℝ) : ℝ :=
  let η := linearPredictor model pgs_val pc_val
  match model.link with
  | .logit => 1 / (1 + Real.exp (-η))
  | .identity => η
/-- A data generating process parametrized by k principal components.

    `trueExpectation` stores E[Y|P,C], and `jointMeasure` stores the marginal
    law on `(P,C)`. -/
structure DataGeneratingProcess (k : ℕ) where
  trueExpectation : ℝ → (Fin k → ℝ) → ℝ
  jointMeasure : Measure (ℝ × (Fin k → ℝ))
  is_prob : IsProbabilityMeasure jointMeasure := by infer_instance

instance dgp_is_prob {k : ℕ} (dgp : DataGeneratingProcess k) : IsProbabilityMeasure dgp.jointMeasure := dgp.is_prob

/-! ### Predictor Abstraction and Proper Risk

Working with predictors (functions ℝ → (Fin k → ℝ) → ℝ) rather than model records
avoids identifiability/representation issues: two different `PhenotypeInformedGAM`
parameterizations can yield the same predictor function, but risk depends only on
the predictor. -/

/-- A predictor is a function from (PGS, PCs) → ℝ. Bayes optimality and risk
    should be stated at this level to avoid representation dependence. -/
abbrev Predictor (k : ℕ) := ℝ → (Fin k → ℝ) → ℝ

/-- MSE risk of a predictor relative to the conditional mean E[Y|P,C]. -/
noncomputable def mseRisk {k : ℕ} [Fintype (Fin k)] (dgp : DataGeneratingProcess k) (f : Predictor k) : ℝ :=
  ∫ x, (dgp.trueExpectation x.1 x.2 - f x.1 x.2)^2 ∂dgp.jointMeasure

/-- Upgraded DGP that explicitly names the conditional mean and provides
    the orthogonality characterization of conditional expectation.

    This is the proper statistical framework: `μ` is a joint law on (P, C, Y),
    and `m` satisfies E[(Y - m(P,C)) · φ(P,C)] = 0 for all square-integrable φ.

    Fully deriving E[Y|P,C] via disintegration is heavy in Mathlib; this structure
    captures the *characterizing property* that proofs actually need. -/
structure ConditionalMeanDGP (k : ℕ) where
  /- Joint law on (P, C, Y). -/
  μ : Measure (ℝ × (Fin k → ℝ) × ℝ)
  prob : IsProbabilityMeasure μ := by infer_instance
  /-- Conditional mean function m = E[Y | P, C]. -/
  m : ℝ → (Fin k → ℝ) → ℝ
  /-- Orthogonality characterization: for all square-integrable φ(P,C),
      E[(Y - m(P,C)) · φ(P,C)] = 0. This is the defining property of
      conditional expectation as an L² projection. -/
  m_spec :
    ∀ (φ : ℝ × (Fin k → ℝ) → ℝ),
      Integrable (fun x : ℝ × (Fin k → ℝ) × ℝ => (x.2.2 - m x.1 x.2.1) * φ (x.1, x.2.1)) μ →
      (∫ x, (x.2.2 - m x.1 x.2.1) * φ (x.1, x.2.1) ∂μ) = 0

/-- Full predictive risk under a joint law on `(P,C,Y)`.
    This is the explicit `E[(Y - f(P,C))^2]` objective. -/
noncomputable def predictionRiskY {k : ℕ} [Fintype (Fin k)]
    (dgp : ConditionalMeanDGP k) (f : Predictor k) : ℝ :=
  ∫ x, (x.2.2 - f x.1 x.2.1)^2 ∂dgp.μ

/-- Convert a ConditionalMeanDGP to the simpler DataGeneratingProcess format.
    The marginal on (P,C) is obtained by mapping out Y. -/
noncomputable def ConditionalMeanDGP.toDGP {k : ℕ} (cmdgp : ConditionalMeanDGP k) : DataGeneratingProcess k where
  trueExpectation := cmdgp.m
  jointMeasure := cmdgp.μ.map (fun x => (x.1, x.2.1))
  is_prob := by
    letI : IsProbabilityMeasure cmdgp.μ := cmdgp.prob
    simpa using
      (Measure.isProbabilityMeasure_map (μ := cmdgp.μ)
        (f := fun x : ℝ × (Fin k → ℝ) × ℝ => (x.1, x.2.1))
        (by fun_prop))

/-- Predicate for Bernoulli response data: all y values are in {0, 1}.
    Required for well-posedness of logistic likelihood. Without this,
    `pointwiseNLL .Bernoulli y η` is defined for arbitrary y ∈ ℝ, which
    breaks convexity and proper scoring properties. -/
def IsBinaryResponse {n : ℕ} (y : Fin n → ℝ) : Prop :=
  ∀ i, y i = 0 ∨ y i = 1

noncomputable def pointwiseNLL (dist : DistributionFamily) (y_obs : ℝ) (η : ℝ) : ℝ :=
  match dist with
  | .Gaussian => (y_obs - η)^2
  | .Bernoulli => Real.log (1 + Real.exp η) - y_obs * η

noncomputable def empiricalLoss {p k sp n : ℕ} [Fintype (Fin p)] [Fintype (Fin k)] [Fintype (Fin sp)] [Fintype (Fin n)] (model : PhenotypeInformedGAM p k sp) (data : RealizedData n k) (lambda : ℝ) : ℝ :=
  (1 / (n : ℝ)) * (∑ i, pointwiseNLL model.dist (data.y i) (linearPredictor model (data.p i) (data.c i)))
  + lambda * ((∑ l, ∑ j, (model.f₀ₗ l j)^2) + (∑ m, ∑ l, ∑ j, (model.fₘₗ m l j)^2))

def IsIdentifiable {p k sp n : ℕ} [Fintype (Fin p)] [Fintype (Fin k)] [Fintype (Fin sp)] [Fintype (Fin n)] (m : PhenotypeInformedGAM p k sp) (data : RealizedData n k) : Prop :=
  (∀ l, (∑ i, evalSmooth m.pcSplineBasis (m.f₀ₗ l) (data.c i l)) = 0) ∧
  (∀ mIdx l, (∑ i, evalSmooth m.pcSplineBasis (m.fₘₗ mIdx l) (data.c i l)) = 0)


structure IsRawScoreModel {p k sp : ℕ} [Fintype (Fin p)] [Fintype (Fin k)] [Fintype (Fin sp)] (m : PhenotypeInformedGAM p k sp) : Prop where
  f₀ₗ_zero : ∀ (l : Fin k) (s : Fin sp), m.f₀ₗ l s = 0
  fₘₗ_zero : ∀ (i : Fin p) (l : Fin k) (s : Fin sp), m.fₘₗ i l s = 0

structure IsNormalizedScoreModel {p k sp : ℕ} [Fintype (Fin p)] [Fintype (Fin k)] [Fintype (Fin sp)] (m : PhenotypeInformedGAM p k sp) : Prop where
  fₘₗ_zero : ∀ (i : Fin p) (l : Fin k) (s : Fin sp), m.fₘₗ i l s = 0

/-!
`IsRawScoreModel` and `IsNormalizedScoreModel` are structural subclasses of the GAM
parameterization. This foundational file intentionally does not expose finite-sample
`argmin` selectors for these subclasses.

An unconditional optimizer theorem would need to fix the basis functions, link, and
distribution family, and then prove actual attainment of the corresponding objective.
The previous oracle-style `Classical.choose` wrappers only repackaged an assumed
existence hypothesis and have been removed rather than preserved as a fake fitting API.
Exact finite-sample procedures are derived downstream in `DGP.lean`, where the design
matrix, restricted parameterizations, and Weierstrass/coercivity machinery are all available.
Concretely, the exact existence theorem is
`gaussianPenalizedLoss_exists_min_of_full_rank`, and the downstream restricted fits are
`fitRaw`, `fitRaw_minimizes_loss`, `fitNormalized`, and
`fitNormalized_minimizes_loss`.
-/

/-!
=================================================================
## Part 2: Fully Formalized Theorems and Proofs
=================================================================
-/


/-- **Lemma**: Moments of the standard Gaussian distribution are integrable.
    Specifically, x^n is integrable w.r.t N(0,1). -/
lemma gaussian_moments_integrable (n : ℕ) :
    Integrable (fun x : ℝ => x ^ n) (ProbabilityTheory.gaussianReal 0 1) := by
  simpa [poly_n, stdGaussianMeasure] using (integrable_poly_n n)

/-! ### Gaussian Moment Facts

These lemmas derive standard moments of N(0,1) from the integrability infrastructure.
They let downstream proofs (raw_score_bias_general, optimal_coefficients_for_additive_dgp, etc.)
avoid threading explicit moment hypotheses (hP0, hP2, hPC0) through every theorem statement. -/

/-- E[P] = 0 under the standard Gaussian. -/
theorem gaussian_mean_zero :
    ∫ x, x ∂(ProbabilityTheory.gaussianReal 0 1) = 0 := by
  simp [ProbabilityTheory.integral_id_gaussianReal]

/-- E[P²] = 1 under the standard Gaussian (variance = 1). -/
theorem gaussian_second_moment :
    ∫ x, x ^ 2 ∂(ProbabilityTheory.gaussianReal 0 1) = 1 := by
  have h_var : ProbabilityTheory.variance id (ProbabilityTheory.gaussianReal 0 1) = (1 : ℝ) := by
    norm_num [ProbabilityTheory.variance_id_gaussianReal]
  have h_var_int :
      ProbabilityTheory.variance id (ProbabilityTheory.gaussianReal 0 1) =
        ∫ x, (x - ∫ t, t ∂(ProbabilityTheory.gaussianReal 0 1)) ^ 2
          ∂(ProbabilityTheory.gaussianReal 0 1) := by
    simpa using
      (ProbabilityTheory.variance_eq_integral (μ := ProbabilityTheory.gaussianReal 0 1)
        (X := id) measurable_id.aemeasurable)
  rw [h_var_int] at h_var
  simpa [gaussian_mean_zero] using h_var

/-- E[P · C_l] = 0 when P and C are independent standard normals.
    This is the key fact that eliminates cross-terms in risk calculations. -/
theorem independent_product_mean_zero {k : ℕ} [Fintype (Fin k)] (l : Fin k) :
    ∫ pc, pc.1 * pc.2 l ∂(stdNormalProdMeasure k) = 0 := by
  let μP : Measure ℝ := ProbabilityTheory.gaussianReal 0 1
  let μC : Measure (Fin k → ℝ) :=
    Measure.pi (fun (_ : Fin k) => ProbabilityTheory.gaussianReal 0 1)
  have hPC :
      ∫ pc, pc.1 * pc.2 l ∂(μP.prod μC) =
        (∫ p, p ∂μP) * (∫ c, c l ∂μC) := by
    simpa using
      (MeasureTheory.integral_prod_mul (μ := μP) (ν := μC)
        (f := fun p : ℝ => p) (g := fun c : Fin k → ℝ => c l))
  have hC_map : μC.map (Function.eval l) = ProbabilityTheory.gaussianReal 0 1 := by
    simpa [μC] using
      (MeasureTheory.measurePreserving_eval
        (μ := fun (_ : Fin k) => ProbabilityTheory.gaussianReal 0 1) l).map_eq
  have h_eval_ae : AEMeasurable (Function.eval l) μC := by
    exact
      (MeasureTheory.measurePreserving_eval
        (μ := fun (_ : Fin k) => ProbabilityTheory.gaussianReal 0 1) l).measurable.aemeasurable
  have hC0 : (∫ c, c l ∂μC) = 0 := by
    calc
      ∫ c, c l ∂μC = ∫ x, x ∂(μC.map (Function.eval l)) := by
        simpa using
          (MeasureTheory.integral_map (μ := μC) (φ := Function.eval l)
            (f := fun x : ℝ => x) h_eval_ae aestronglyMeasurable_id).symm
      _ = ∫ x, x ∂(ProbabilityTheory.gaussianReal 0 1) := by rw [hC_map]
      _ = 0 := gaussian_mean_zero
  have h_prod : stdNormalProdMeasure k = μP.prod μC := by
    simp [stdNormalProdMeasure, μP, μC]
  calc
    ∫ pc, pc.1 * pc.2 l ∂(stdNormalProdMeasure k)
        = ∫ pc, pc.1 * pc.2 l ∂(μP.prod μC) := by rw [h_prod]
    _ = (∫ p, p ∂μP) * (∫ c, c l ∂μC) := hPC
    _ = 0 := by simp [hC0]

/-! ### Standardized a.e. → Pointwise Upgrade

For continuous functions on a measure with full support (IsOpenPosMeasure),
a.e. equality implies pointwise equality. This is used repeatedly in
`shrinkage_effect`, `multiplicative_bias_correction`, etc. -/

/-- If two continuous functions agree a.e. on a measure with `IsOpenPosMeasure`,
    they agree everywhere. This replaces ad-hoc upgrades throughout the file. -/
theorem eq_of_ae_eq_of_continuous {α : Type*} [TopologicalSpace α]
    [MeasurableSpace α] {μ : Measure α} [μ.IsOpenPosMeasure] {f g : α → ℝ}
    (hf : Continuous f) (hg : Continuous g)
    (h_ae : f =ᵐ[μ] g) : f = g := by
  exact Measure.eq_of_ae_eq h_ae hf hg


end Calibrator
