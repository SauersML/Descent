/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Portability.SimulationBaselineLaw
import Descent.Portability.SimulationCohortLaw
import Descent.Portability.PThresholdTrainingLaw
import Descent.Portability.DistanceBinnedPortabilityLaw

assert_below Descent.Decision Descent.Program

/-!
Decode the realized simulation inputs into the effect/label portability law.
Causal liability uses raw allele-index dosages, evaluation uses held-out rows,
and phenotype calibration uses the oversampled whole cohort. A full-score
learner is represented by exact row selectors, retaining score sanitization
without assuming that sanitized output is a linear sum of finite SNP weights.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Portability.SimulationDesignDecoder

open FiniteReportLaw SimulationAccuracy TrainingNoiseAccuracy
open SimulationDemographyLaw SimulationCohortLaw StoppedGenotypeLaw
open ReservoirSamplingLaw SamplingDesignLaw GaussianEffectPortabilityLaw
open DistanceBinnedPortabilityLaw PThresholdTrainingLaw

variable {demes length causalCount : ℕ}
  (source : Fin demes)
  (permutations : ∀ deme, Equiv.Perm (Fin (SourceDesignLaw.sampleSize source deme)))
  (genome : WholeGenome length (2 * cohortSize demes))
  (causalSites : Slots causalCount length)
  (baseline : Fin demes → ℝ)
  (hbaseline : ∀ deme, -(7 / 10) ≤ baseline deme ∧ baseline deme ≤ 7 / 10)
  (learner : (Fin (fitCount source source) → Bool) → Option (Individuals demes → ℝ))

noncomputable def causalColumns (individual : Individuals demes) (causal : Fin causalCount) : ℝ :=
  rawDiploidDosage genome (causalSites causal) individual

noncomputable def design :
    FixedDesign (Individuals demes) (Fin (fitCount source source))
      (Individuals demes) (Individuals demes) (Individuals demes) (Fin causalCount) where
  cohort := cohortLaw
  source := evaluationLaw source permutations source
  target := evaluationLaw source permutations source
  causalGenotype := causalColumns genome causalSites
  sourceGenotype := rowSelectors id
  targetGenotype := rowSelectors id
  trainingIndex := SimulationCohortLaw.trainingIndex source permutations
  sourceIndex := id
  targetIndex := id
  baseline := baseline ∘ individualDeme source
  epsilon := SimulationBaselineLaw.epsilon
  epsilon_pos := SimulationBaselineLaw.epsilon_pos
  baseline_bound := fun row ↦ hbaseline (individualDeme source row)
  learn := learner

noncomputable def targets (distance : Fin demes → ℕ) :
    TargetCohorts (Fin demes) (Individuals demes) (Individuals demes) (Individuals demes) where
  law := evaluationLaw source permutations
  genotype := fun _ ↦ rowSelectors id
  index := fun _ ↦ id
  distance := distance

/-- This is the globally standardized genetic liability used by phenoA. -/
noncomputable def geneticLiability (effects : Fin causalCount → ℝ) : Individuals demes → ℝ :=
  standardize cohortLaw SimulationBaselineLaw.epsilon
    (linearScore (causalColumns genome causalSites) effects)

/-- The simulator centers each causal column before multiplying by effects;
that preprocessing gives precisely the same globally standardized liability. -/
theorem geneticLiability_centered (effects : Fin causalCount → ℝ) :
    standardize cohortLaw SimulationBaselineLaw.epsilon
      (linearScore (fun row causal ↦ causalColumns genome causalSites row causal -
        cohortLaw.expectation (fun individual ↦ causalColumns genome causalSites individual causal))
        effects) = geneticLiability genome causalSites effects := by
  exact standardize_linearScore_center_columns _ _ _ _ _

theorem squaredCorrelation_geneticLiability (p : FiniteReportLaw (Individuals demes))
    (score : Individuals demes → ℝ) (effects : Fin causalCount → ℝ) :
    p.squaredCorrelation score (geneticLiability genome causalSites effects) =
      p.squaredCorrelation score (linearScore (causalColumns genome causalSites) effects) := by
  unfold geneticLiability
  rw [standardize_eq_affine]
  have he :
      Real.sqrt (cohortLaw.variance (linearScore (causalColumns genome causalSites) effects)) +
      SimulationBaselineLaw.epsilon ≠ 0 := ne_of_gt
    (add_pos_of_nonneg_of_pos (Real.sqrt_nonneg _) SimulationBaselineLaw.epsilon_pos)
  have hid : affine 1 0 score = score := by funext row; simp [affine]
  simpa only [hid] using squaredCorrelation_affine p 1 0 _ _ one_ne_zero (one_div_ne_zero he)
    score (linearScore (causalColumns genome causalSites) effects)

/-- The decoder's report is the actual squared-correlation quotient of the
returned score vector and the standardized causal liability on held-out rows.
The same learner output and effects are used at source and target. -/
theorem decoded_report (distance : Fin demes → ℕ) (deme : Fin demes)
    (effects : Fin causalCount → ℝ) (labels : Fin (fitCount source source) → Bool) :
    report (targetDesign (design source permutations genome causalSites baseline hbaseline learner)
      (targets source permutations distance) deme) effects labels =
      (learner labels).bind (fun score ↦
        (evaluationLaw source permutations source).squaredCorrelation score
          (geneticLiability genome causalSites effects) |>.bind (fun sourceR2 ↦
            (evaluationLaw source permutations deme).squaredCorrelation score
              (geneticLiability genome causalSites effects) |>.bind (fun targetR2 ↦
                if 0 < sourceR2 then some (targetR2 / sourceR2) else none))) := by
  simp_rw [squaredCorrelation_geneticLiability]
  unfold report targetDesign design targets formRatio
  simp only
  have hs (score : Individuals demes → ℝ) :
      linearScore (rowSelectors (id : Individuals demes → Individuals demes)) score = score := by
    funext row
    exact linearScore_rowSelectors id score row
  simp_rw [← squaredCorrelation_eq_formAccuracy, hs]
  rfl

/-- Sorted source fit rows are the index domain for training labels. The
private fixed permutation partitions those rows into GWAS and selection sets. -/
noncomputable def innerCohorts (inner : ℕ) (hi : inner ≤ fitCount source source)
    (fixedInner : Equiv.Perm (Fin (fitCount source source))) :
    Cohorts (Individuals demes) (Fin (fitCount source source))
      (Fin inner) (Fin (fitCount source source - inner)) where
  fitRow := fun i ↦ SimulationCohortLaw.trainingIndex source permutations (fitRows hi fixedInner i)
  selectionRow := fun i ↦
    SimulationCohortLaw.trainingIndex source permutations (testRows hi fixedInner i)
  fitLabel := fitRows hi fixedInner
  selectionLabel := testRows hi fixedInner

theorem inner_fit_label_consistent (inner : ℕ) (hi : inner ≤ fitCount source source)
    (fixedInner : Equiv.Perm (Fin (fitCount source source))) (row : Fin inner) :
    (innerCohorts source permutations inner hi fixedInner).fitRow row =
      SimulationCohortLaw.trainingIndex source permutations
        ((innerCohorts source permutations inner hi fixedInner).fitLabel row) := rfl

theorem inner_selection_label_consistent (inner : ℕ) (hi : inner ≤ fitCount source source)
    (fixedInner : Equiv.Perm (Fin (fitCount source source)))
    (row : Fin (fitCount source source - inner)) :
    (innerCohorts source permutations inner hi fixedInner).selectionRow row =
      SimulationCohortLaw.trainingIndex source permutations
        ((innerCohorts source permutations inner hi fixedInner).selectionLabel row) := rfl


/-- Build the effect/label design from the explicit P+T scan, clump tables,
and score files. GWAS and numerical preprocessing still produce those tables
and files; threshold selection, score cleanup and row mapping are constructed. -/
noncomputable def tableDesign (inner : ℕ) (hinner : 0 < inner)
    (hbelow : inner < fitCount source source)
    (fixedInner : Equiv.Perm (Fin (fitCount source source)))
    (tables : (Fin (fitCount source source) → Bool) → ClumpedTable (Fin length))
    (files : (Fin (fitCount source source) → Bool) → ℝ → Option (Individuals demes → Option ℝ)) :
    FixedDesign (Individuals demes) (Fin (fitCount source source))
      (Individuals demes) (Individuals demes) (Individuals demes) (Fin causalCount) := by
  letI : NeZero inner := ⟨Nat.ne_zero_of_lt hinner⟩
  letI : NeZero (fitCount source source - inner) := ⟨Nat.ne_zero_of_lt (Nat.sub_pos_of_lt hbelow)⟩
  exact design source permutations genome causalSites baseline hbaseline
    (learnerFromTables (innerCohorts source permutations inner hbelow.le fixedInner) tables files)

/-- The actual source fit size is 2500, and its 80/20 partition is exactly
2000 GWAS and 500 threshold-selection rows. -/
theorem default_inner_counts : 2000 < fitCount source source ∧
    fitCount source source - 2000 = 500 := by
  rw [(source_split_counts source).1]
  norm_num

noncomputable def defaultTableDesign
    (fixedInner : Equiv.Perm (Fin (fitCount source source)))
    (tables : (Fin (fitCount source source) → Bool) → ClumpedTable (Fin length))
    (files : (Fin (fitCount source source) → Bool) → ℝ → Option (Individuals demes → Option ℝ)) :
    FixedDesign (Individuals demes) (Fin (fitCount source source))
      (Individuals demes) (Individuals demes) (Individuals demes) (Fin causalCount) :=
  tableDesign source permutations genome causalSites baseline hbaseline 2000 (by decide)
    (default_inner_counts source).1 fixedInner tables files

/-- Default serial/grid baseline and distance inputs can be inserted without
supplying a bounded-baseline premise or an unrelated distance map. -/
noncomputable def serialTargets (training : Fin 10)
    (outer : ∀ deme, Equiv.Perm (Fin (SourceDesignLaw.sampleSize training deme))) :
    TargetCohorts (Fin 10) (Individuals 10) (Individuals 10) (Individuals 10) :=
  targets training outer (SourceDesignLaw.serialDistance training)

noncomputable def gridTargets (training : Fin 36)
    (outer : ∀ deme, Equiv.Perm (Fin (SourceDesignLaw.sampleSize training deme))) :
    TargetCohorts (Fin 36) (Individuals 36) (Individuals 36) (Individuals 36) :=
  targets training outer (fun deme ↦ SourceDesignLaw.gridDistance
    (finProdFinEquiv.symm training : Fin 6 × Fin 6) (finProdFinEquiv.symm deme))

noncomputable def serialTableDesign (training : Fin 10)
    (outer : ∀ deme, Equiv.Perm (Fin (SourceDesignLaw.sampleSize training deme)))
    (data : WholeGenome length (2 * cohortSize 10)) (causal : Slots causalCount length)
    (fixedInner : Equiv.Perm (Fin (fitCount training training)))
    (tables : (Fin (fitCount training training) → Bool) → ClumpedTable (Fin length))
    (files : (Fin (fitCount training training) → Bool) → ℝ → Option (Individuals 10 → Option ℝ)) :
    FixedDesign (Individuals 10) (Fin (fitCount training training))
      (Individuals 10) (Individuals 10) (Individuals 10) (Fin causalCount) :=
  defaultTableDesign training outer data causal SimulationBaselineLaw.serial
    SimulationBaselineLaw.serial_bounds fixedInner tables files

noncomputable def gridTableDesign (training : Fin 36)
    (outer : ∀ deme, Equiv.Perm (Fin (SourceDesignLaw.sampleSize training deme)))
    (data : WholeGenome length (2 * cohortSize 36)) (causal : Slots causalCount length)
    (fixedInner : Equiv.Perm (Fin (fitCount training training)))
    (tables : (Fin (fitCount training training) → Bool) → ClumpedTable (Fin length))
    (files : (Fin (fitCount training training) → Bool) → ℝ → Option (Individuals 36 → Option ℝ)) :
    FixedDesign (Individuals 36) (Fin (fitCount training training))
      (Individuals 36) (Individuals 36) (Individuals 36) (Fin causalCount) :=
  defaultTableDesign training outer data causal SimulationBaselineLaw.grid
    SimulationBaselineLaw.grid_bounds fixedInner tables files

end Descent.Portability.SimulationDesignDecoder
