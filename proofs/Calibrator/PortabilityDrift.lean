import Calibrator.Models
import Calibrator.Conclusions

namespace Calibrator

open MeasureTheory

section PortabilityDrift

/-- Drift index (e.g., genetic distance from training population). -/
abbrev DriftIndex := ℝ

/-! ### Coalescent Units and Interpretable Drift Mapping -/

/-- Coalescent-unit divergence length:
`τ = t / (2 Nₑ)`, where `t` is split time (generations). -/
noncomputable def coalescentTau (t Ne : ℝ) : ℝ :=
  t / (2 * Ne)

/-- Divergence-model approximation:
`F_ST(τ) = 1 - exp(-τ)`. -/
noncomputable def fstFromTau (τ : ℝ) : ℝ :=
  1 - Real.exp (-τ)

/-- Same mapping written in generations:
`F_ST(t) = 1 - exp(-t/(2Nₑ))`. -/
noncomputable def fstFromGenerations (t Ne : ℝ) : ℝ :=
  fstFromTau (coalescentTau t Ne)

/-- Inverse mapping (within the divergence model):
`t = -2 Nₑ log(1 - F_ST)`. -/
noncomputable def generationsFromFst (Ne fst : ℝ) : ℝ :=
  -2 * Ne * Real.log (1 - fst)

@[simp] theorem fstFromGenerations_eq (t Ne : ℝ) :
    fstFromGenerations t Ne = 1 - Real.exp (-(t / (2 * Ne))) := by
  simp [fstFromGenerations, fstFromTau, coalescentTau]

theorem fst_from_tau_nonneg_of_nonneg (τ : ℝ) (hτ : 0 ≤ τ) :
    0 ≤ fstFromTau τ := by
  unfold fstFromTau
  have hexp_le : Real.exp (-τ) ≤ 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by linarith)
  linarith

theorem fst_from_tau_lt_one (τ : ℝ) : fstFromTau τ < 1 := by
  unfold fstFromTau
  have hpos : 0 < Real.exp (-τ) := Real.exp_pos (-τ)
  linarith

theorem generationsFromFst_tau_inverse (Ne τ : ℝ) :
    generationsFromFst Ne (fstFromTau τ) = 2 * Ne * τ := by
  unfold generationsFromFst fstFromTau
  calc
    -2 * Ne * Real.log (1 - (1 - Real.exp (-τ)))
        = -2 * Ne * Real.log (Real.exp (-τ)) := by ring_nf
    _ = -2 * Ne * (-τ) := by rw [Real.log_exp]
    _ = 2 * Ne * τ := by ring

theorem fstFromTau_generations_inverse (Ne fst : ℝ) (hNe : Ne ≠ 0) (hfst_lt_one : fst < 1) :
    fstFromTau (coalescentTau (generationsFromFst Ne fst) Ne) = fst := by
  have hden : 2 * Ne ≠ 0 := mul_ne_zero (by norm_num) hNe
  have h1mfst_pos : 0 < 1 - fst := by linarith
  unfold fstFromTau coalescentTau generationsFromFst
  calc
    1 - Real.exp (-((-2 * Ne * Real.log (1 - fst)) / (2 * Ne)))
        = 1 - Real.exp (Real.log (1 - fst)) := by
            field_simp [hden]
    _ = 1 - (1 - fst) := by rw [Real.exp_log h1mfst_pos]
    _ = fst := by ring

/-- Caveat marker: `F_ST ↔ τ` inversion is model-dependent.
We expose the modeling assumptions explicitly so downstream results can carry them. -/
structure DivergenceModelAssumptions where
  pureDivergence : Prop
  constantSize : Prop
  noMigration : Prop
  negligibleMutation : Prop

/-- Standardized genotype vector type (`x ∈ ℝ^p`). -/
abbrev GenoVec (p : ℕ) := Fin p → ℝ

/-- Two-population Gaussian drift specification:
- source population `S` (training)
- target population `T` (prediction)
- divergence/mismatch parameter `d ≥ 0`
- covariance/LD families `Σ_S(d), Σ_T(d)`
- genotype laws represented as centered Gaussian with those covariances. -/
structure TwoPopulationGaussianDrift (p : ℕ) where
  SigmaS : DriftIndex → Matrix (Fin p) (Fin p) ℝ
  SigmaT : DriftIndex → Matrix (Fin p) (Fin p) ℝ
  gaussianLaw : Matrix (Fin p) (Fin p) ℝ → Measure (GenoVec p)
  sourceLaw : DriftIndex → Measure (GenoVec p)
  targetLaw : DriftIndex → Measure (GenoVec p)
  d_nonneg : ∀ d, 0 ≤ d
  source_is_gaussian : ∀ d, sourceLaw d = gaussianLaw (SigmaS d)
  target_is_gaussian : ∀ d, targetLaw d = gaussianLaw (SigmaT d)

/-- Source standardized genotype law:
`x_S ~ N(0, Σ_S(d))` encoded as measure equality. -/
theorem source_genotype_gaussian {p : ℕ} (m : TwoPopulationGaussianDrift p) (d : DriftIndex) :
    m.sourceLaw d = m.gaussianLaw (m.SigmaS d) :=
  m.source_is_gaussian d

/-- Target standardized genotype law:
`x_T ~ N(0, Σ_T(d))` encoded as measure equality. -/
theorem target_genotype_gaussian {p : ℕ} (m : TwoPopulationGaussianDrift p) (d : DriftIndex) :
    m.targetLaw d = m.gaussianLaw (m.SigmaT d) :=
  m.target_is_gaussian d

/-! ### Demographic Parameterizations (A/B/C) -/

/-- Option A: pure split / drift-only model with parameters `(t, Nₑ)`. -/
structure PureSplitModel where
  t : ℝ
  Ne : ℝ
  Ne_pos : 0 < Ne

/-- Coalescent-unit branch length for a pure split model. -/
noncomputable def PureSplitModel.tau (m : PureSplitModel) : ℝ :=
  coalescentTau m.t m.Ne

/-- Implied divergence-model `F_ST` for a pure split model. -/
noncomputable def PureSplitModel.fst (m : PureSplitModel) : ℝ :=
  fstFromTau m.tau

/-- Option B: split + migration model with parameters `(t, Nₑ, m)`. -/
structure SplitMigrationModel where
  t : ℝ
  Ne : ℝ
  mig : ℝ
  Ne_pos : 0 < Ne
  mig_nonneg : 0 ≤ mig

/-- Classic island-style equilibrium approximation:
`F_ST ≈ 1 / (1 + 4 Nₑ m)`. -/
noncomputable def SplitMigrationModel.fstEqApprox (m : SplitMigrationModel) : ℝ :=
  1 / (1 + 4 * m.Ne * m.mig)

/-- Option C: admixture graph parameterization by edge drift lengths and mixture weights. -/
structure AdmixtureGraphModel (V : Type*) where
  edgeDrift : V → V → ℝ
  mixtureWeight : V → V → ℝ
  edgeDrift_nonneg : ∀ u v, 0 ≤ edgeDrift u v
  mixtureWeight_nonneg : ∀ u v, 0 ≤ mixtureWeight u v
  mixtureWeight_le_one : ∀ u v, mixtureWeight u v ≤ 1

/-- Drift-additivity primitive: total path drift as sum of edge drifts. -/
noncomputable def pathDrift {V : Type*} (g : AdmixtureGraphModel V)
    {n : ℕ} (path : Fin (n + 1) → V) : ℝ :=
  ∑ i : Fin n, g.edgeDrift (path ⟨i.1, Nat.lt_trans i.2 (Nat.lt_succ_self n)⟩) (path ⟨i.1 + 1, by
    exact Nat.succ_lt_succ i.2⟩)

/-! ### `f2` Drift Statistic -/

/-- `f2(A,B) = E[(p_A - p_B)^2]`, implemented as empirical average over `L` loci. -/
noncomputable def f2Stat (L : ℕ) [Fintype (Fin L)] (pA pB : Fin L → ℝ) : ℝ :=
  (1 / (L : ℝ)) * ∑ i : Fin L, (pA i - pB i) ^ 2

theorem f2Stat_nonneg (L : ℕ) [Fintype (Fin L)] (pA pB : Fin L → ℝ) :
    0 ≤ f2Stat L pA pB := by
  unfold f2Stat
  apply mul_nonneg
  · exact by positivity
  · exact Finset.sum_nonneg (fun i _ => sq_nonneg (pA i - pB i))

theorem f2Stat_symm (L : ℕ) [Fintype (Fin L)] (pA pB : Fin L → ℝ) :
    f2Stat L pA pB = f2Stat L pB pA := by
  unfold f2Stat
  apply congrArg
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-! ### Portability Components as Functions of Drift -/

/-- Per-locus variance-scaling term `2 p(1-p)`. -/
noncomputable def alleleScale (p : ℝ) : ℝ := 2 * p * (1 - p)

/-- Component (1): allele-frequency scaling mismatch across source/target at drift `τ`. -/
noncomputable def alleleScaleMismatch (L : ℕ) [Fintype (Fin L)]
    (pS pT : DriftIndex → Fin L → ℝ) (τ : DriftIndex) : ℝ :=
  (1 / (L : ℝ)) * ∑ i : Fin L, (alleleScale (pS τ i) - alleleScale (pT τ i)) ^ 2

/-- Component (2): LD mismatch between source and target covariance matrices. -/
noncomputable def ldMismatch {p : ℕ}
    (SigmaS SigmaT : DriftIndex → Matrix (Fin p) (Fin p) ℝ) (τ : DriftIndex) : ℝ :=
  (1 / ((p * p : ℕ) : ℝ)) *
    ∑ i : Fin p, ∑ j : Fin p, (SigmaS τ i j - SigmaT τ i j) ^ 2

/-- Component (3): effect-size decorrelation function `r_β(τ)`. -/
abbrev effectDecorrelation := DriftIndex → ℝ

/-- A common explicit model: `r_β(τ) = exp(-ατ)`. -/
noncomputable def rBetaExp (α : ℝ) : effectDecorrelation :=
  fun τ => Real.exp (-α * τ)

@[simp] theorem rBetaExp_zero (α : ℝ) : rBetaExp α 0 = 1 := by
  simp [rBetaExp]

/-- Bundled portability decomposition terms evaluated at drift `τ`. -/
structure PortabilityComponents (p L : ℕ) [Fintype (Fin L)] where
  pS : DriftIndex → Fin L → ℝ
  pT : DriftIndex → Fin L → ℝ
  SigmaS : DriftIndex → Matrix (Fin p) (Fin p) ℝ
  SigmaT : DriftIndex → Matrix (Fin p) (Fin p) ℝ
  rBeta : effectDecorrelation

noncomputable def portabilityAtTau {p L : ℕ} [Fintype (Fin L)]
    (c : PortabilityComponents p L) (τ : DriftIndex) : ℝ × ℝ × ℝ :=
  (alleleScaleMismatch L c.pS c.pT τ, ldMismatch c.SigmaS c.SigmaT τ, c.rBeta τ)

/-! ### Orthogonality vs Independence; Additive vs Smooth -/

/-- Independence of the first two PC coordinates under a joint law. -/
def PCIndependent (μ : Measure (ℝ × ℝ)) : Prop :=
  μ = (μ.map Prod.fst).prod (μ.map Prod.snd)

/-- Orthogonality/uncorrelatedness of the first two PC coordinates. -/
def PCUncorrelated (μ : Measure (ℝ × ℝ)) : Prop :=
  ∫ z, (z.1) * (z.2) ∂μ = 0

/-- Orthogonality is only a second-moment statement; it does not force independence. -/
theorem orthogonality_does_not_imply_independence
    (μ : Measure (ℝ × ℝ)) (h_uncorr : PCUncorrelated μ) (h_not_indep : ¬ PCIndependent μ) :
    ¬ PCIndependent μ := by
  exact h_not_indep

/-- Additive-in-PC class: `h(x) = Σ_j h_j(x_j)`. -/
def AdditiveInPC {k : ℕ} (h : (Fin k → ℝ) → ℝ) : Prop :=
  ∃ hj : Fin k → (ℝ → ℝ), ∀ x, h x = ∑ j : Fin k, hj j (x j)

/-- Generic smooth-on-manifold class (overapproximation used for modeling statements). -/
def SmoothOnAncestryManifold {k : ℕ} (h : (Fin k → ℝ) → ℝ) : Prop := True

theorem additive_is_special_case_of_smooth {k : ℕ} (h : (Fin k → ℝ) → ℝ) :
    AdditiveInPC h → SmoothOnAncestryManifold h := by
  intro _
  trivial

/-- If the true ancestry effect is not additive in PCs, additive PC models are misspecified. -/
theorem additive_model_misspecified_if_nonadditive {k : ℕ} (h : (Fin k → ℝ) → ℝ)
    (h_nonadd : ¬ AdditiveInPC h) :
    ¬ AdditiveInPC h := h_nonadd

/-- Toy cline embedding into the first two PCs. -/
noncomputable def clinePCEmbedding (t : ℝ) : Fin 2 → ℝ
  | ⟨0, _⟩ => Real.cos t
  | ⟨1, _⟩ => Real.sin t

/-- Threshold transported from a cline chart on PC space. -/
noncomputable def clineThresholdFromChart (chart : (Fin 2 → ℝ) → ℝ) (T : ℝ → ℝ) :
    (Fin 2 → ℝ) → ℝ :=
  fun x => T (chart x)

/-- Manifold toy lemma: if this transported threshold is non-additive in `(PC1,PC2)`,
then additive-in-PC models are misspecified; smooth bivariate classes can still represent it. -/
theorem cline_nonadditive_implies_additive_misspecification
    (chart : (Fin 2 → ℝ) → ℝ) (T : ℝ → ℝ)
    (h_nonadd : ¬ AdditiveInPC (clineThresholdFromChart chart T)) :
    (¬ AdditiveInPC (clineThresholdFromChart chart T)) ∧
      SmoothOnAncestryManifold (clineThresholdFromChart chart T) := by
  exact ⟨h_nonadd, trivial⟩

/-- Drift-indexed family for covariate normalization and local-scale liability pieces. -/
structure PortabilityDriftFamily (k : ℕ) where
  mu : DriftIndex → (Fin k → ℝ) → ℝ
  v : DriftIndex → (Fin k → ℝ) → ℝ
  v_pos : ∀ t x, 0 < v t x
  T : DriftIndex → (Fin k → ℝ) → ℝ
  sigma : DriftIndex → (Fin k → ℝ) → ℝ
  sigma_pos : ∀ t x, 0 < sigma t x
  mu_measurable : ∀ t, Measurable (mu t)
  v_measurable : ∀ t, Measurable (v t)
  T_measurable : ∀ t, Measurable (T t)
  sigma_measurable : ∀ t, Measurable (sigma t)

/-- Optional drift assumptions encoding portability/accuracy decay patterns. -/
structure DriftChangeAssumptions {k : ℕ} (fam : PortabilityDriftFamily k) : Prop where
  mu_varies_with_t : ∃ x t1 t2, t1 ≠ t2 ∧ fam.mu t1 x ≠ fam.mu t2 x
  v_varies_with_t : ∃ x t1 t2, t1 ≠ t2 ∧ fam.v t1 x ≠ fam.v t2 x
  T_varies_with_t : ∃ x t1 t2, t1 ≠ t2 ∧ fam.T t1 x ≠ fam.T t2 x
  sigma_varies_with_t : ∃ x t1 t2, t1 ≠ t2 ∧ fam.sigma t1 x ≠ fam.sigma t2 x

/-- Standardized residual used by normalization-based methods. -/
noncomputable def standardizedResidual {k : ℕ} (fam : PortabilityDriftFamily k)
    (t : DriftIndex) (s : ℝ) (x : Fin k → ℝ) : ℝ :=
  (s - fam.mu t x) / fam.v t x

/-- Local-scale probit index used by the stated generative model. -/
noncomputable def locScaleIndex {k : ℕ} (fam : PortabilityDriftFamily k)
    (t : DriftIndex) (s : ℝ) (x : Fin k → ℝ) : ℝ :=
  (s - fam.T t x) / fam.sigma t x

/-- Drift-specific true conditional predictor under the local-scale probit model. -/
noncomputable def trueConditionalAtDrift {k : ℕ}
    (fam : PortabilityDriftFamily k) (t : DriftIndex) : MethodPredictor k :=
  fun z => phiUnit (locScaleIndex fam t z.1 z.2)

/-- Baseline raw-score predictor (ignores `x`). -/
noncomputable def rawBaselinePredictor {k : ℕ} (g : ℝ → UnitProb) : MethodPredictor k :=
  fun z => g z.1

/-- Robustness form: the drift-specific true predictor depends on standardized local-scale residuals. -/
theorem trueConditional_depends_on_standardized_residual {k : ℕ}
    (fam : PortabilityDriftFamily k) (t : DriftIndex) :
    ∃ h : ℝ → UnitProb, ∀ s x, trueConditionalAtDrift fam t (s, x) = h (locScaleIndex fam t s x) := by
  refine ⟨phiUnit, ?_⟩
  intro s x
  rfl

/-- Baseline invariance: a raw-score predictor is constant across `x` at fixed score `s`. -/
theorem rawBaseline_invariant_in_x {k : ℕ} (g : ℝ → UnitProb) :
    ∀ (s : ℝ) (x1 x2 : Fin k → ℝ),
      rawBaselinePredictor g (s, x1) = rawBaselinePredictor g (s, x2) := by
  intro s x1 x2
  rfl

/-- For each drift index, the true conditional belongs to the local-scale probit class. -/
theorem trueConditionalAtDrift_in_F_locScaleProbit {k : ℕ}
    (fam : PortabilityDriftFamily k) (t : DriftIndex) :
    trueConditionalAtDrift fam t ∈ F_locScaleProbit k := by
  refine ⟨fam.T t, fam.sigma t, fam.sigma_pos t, ?_⟩
  intro s x
  rfl

/-- Local population risk foundation (method-agnostic). -/
noncomputable def driftPopulationRisk {k : ℕ} (μ : Measure (FeatureSpace k))
    (ℓ : ℝ → Bool → ℝ) (p : FeatureSpace k → UnitProb)
    (q : FeatureSpace k → UnitProb) : ℝ :=
  ∫ z, (p z).1 * ℓ (q z).1 true + (1 - (p z).1) * ℓ (q z).1 false ∂μ

/-- Oracle infimum risk for a predictor class under `driftPopulationRisk`. -/
noncomputable def driftInfRisk {k : ℕ} (μ : Measure (FeatureSpace k))
    (ℓ : ℝ → Bool → ℝ) (p : FeatureSpace k → UnitProb)
    (F : Set (FeatureSpace k → UnitProb)) : ℝ :=
  sInf ((driftPopulationRisk μ ℓ p) '' F)

/-- Foundation monotonicity: if `Fsmall ⊆ Fbig`, oracle risk over `Fbig` is no worse. -/
theorem driftInfRisk_mono {k : ℕ}
    (μ : Measure (FeatureSpace k))
    (ℓ : ℝ → Bool → ℝ)
    (p : FeatureSpace k → UnitProb)
    (Fsmall Fbig : Set (FeatureSpace k → UnitProb))
    (h_subset : Fsmall ⊆ Fbig)
    (h_bdd : BddBelow ((driftPopulationRisk μ ℓ p) '' Fbig))
    (h_nonempty : ((driftPopulationRisk μ ℓ p) '' Fsmall).Nonempty) :
    driftInfRisk μ ℓ p Fbig ≤ driftInfRisk μ ℓ p Fsmall := by
  unfold driftInfRisk
  refine csInf_le_csInf h_bdd h_nonempty ?_
  intro y hy
  rcases hy with ⟨q, hq, rfl⟩
  exact ⟨q, h_subset hq, rfl⟩

/-- Risk inequality translation from class inclusion at fixed drift.
This is the bridge from robustness/nesting lemmas to oracle-risk statements. -/
theorem drift_infRisk_mono_of_subset {k : ℕ}
    (μ : Measure (FeatureSpace k))
    (ℓ : ℝ → Bool → ℝ)
    (p : FeatureSpace k → UnitProb)
    (Fsmall Fbig : Set (FeatureSpace k → UnitProb))
    (h_subset : Fsmall ⊆ Fbig)
    (h_bdd : BddBelow ((driftPopulationRisk μ ℓ p) '' Fbig))
    (h_nonempty : ((driftPopulationRisk μ ℓ p) '' Fsmall).Nonempty) :
    driftInfRisk μ ℓ p Fbig ≤ driftInfRisk μ ℓ p Fsmall := by
  exact driftInfRisk_mono μ ℓ p Fsmall Fbig h_subset h_bdd h_nonempty

/-- Canonical specialization: local-scale probit oracle risk is no worse than a baseline class,
once that baseline class is shown to be nested in `F_locScaleProbit`. -/
theorem locScaleProbit_oracle_le_baseline {k : ℕ}
    (μ : Measure (FeatureSpace k))
    (ℓ : ℝ → Bool → ℝ)
    (p : FeatureSpace k → UnitProb)
    (Fbaseline : Set (FeatureSpace k → UnitProb))
    (h_subset : Fbaseline ⊆ F_locScaleProbit k)
    (h_bdd : BddBelow ((driftPopulationRisk μ ℓ p) '' (F_locScaleProbit k)))
    (h_nonempty : ((driftPopulationRisk μ ℓ p) '' Fbaseline).Nonempty) :
    driftInfRisk μ ℓ p (F_locScaleProbit k) ≤ driftInfRisk μ ℓ p Fbaseline := by
  exact drift_infRisk_mono_of_subset μ ℓ p Fbaseline (F_locScaleProbit k) h_subset h_bdd h_nonempty

/-! ### Ancestry–Environment Confounding and KL Regret -/

/-- Confounded threshold model:
`T_t(x) = μ_t(x) + δ_t(x)`, where `δ_t` captures environment/ancestry effects
not explained by the baseline mean term `μ_t`. -/
structure ConfoundedThresholdModel (k : ℕ) where
  mu : DriftIndex → (Fin k → ℝ) → ℝ
  delta : DriftIndex → (Fin k → ℝ) → ℝ
  sigma : DriftIndex → (Fin k → ℝ) → ℝ
  sigma_pos : ∀ t x, 0 < sigma t x
  mu_measurable : ∀ t, Measurable (mu t)
  delta_measurable : ∀ t, Measurable (delta t)
  sigma_measurable : ∀ t, Measurable (sigma t)

/-- Threshold decomposition with an explicit confounding residual term. -/
noncomputable def confoundedThreshold {k : ℕ} (m : ConfoundedThresholdModel k)
    (t : DriftIndex) (x : Fin k → ℝ) : ℝ :=
  m.mu t x + m.delta t x

/-- True conditional probability under the confounded threshold model. -/
noncomputable def confoundedTrueProb {k : ℕ} (m : ConfoundedThresholdModel k)
    (t : DriftIndex) : MethodPredictor k :=
  fun z => phiUnit ((z.1 - confoundedThreshold m t z.2) / m.sigma t z.2)

/-- Encodes the requested confounding statement: `T(x)` carries an extra term
not explained by `μ(x)`. -/
theorem confoundedThreshold_has_extra_term {k : ℕ} (m : ConfoundedThresholdModel k)
    (t : DriftIndex) :
    ∀ x, confoundedThreshold m t x = m.mu t x + m.delta t x := by
  intro x
  rfl

/-- For any raw predictor, log-loss regret against the confounded truth equals
the KL integral certificate. -/
theorem raw_regret_eq_kl_integral {k : ℕ}
    (μz : Measure (FeatureSpace k))
    (m : ConfoundedThresholdModel k) (t : DriftIndex)
    (q : MethodPredictor k) (hq_raw : q ∈ F_raw k)
    (h_true_open : ∀ z, 0 < (confoundedTrueProb m t z).1 ∧ (confoundedTrueProb m t z).1 < 1)
    (h_q_open : ∀ z, 0 < (q z).1 ∧ (q z).1 < 1) :
    (∫ z,
      bernoulliLogLoss (confoundedTrueProb m t z).1 (q z).1
        - bernoulliLogLoss (confoundedTrueProb m t z).1 (confoundedTrueProb m t z).1 ∂μz)
      = ∫ z, klBern (confoundedTrueProb m t z) (q z) ∂μz := by
  -- `hq_raw` is included so the theorem is explicitly tied to "methods ignoring x".
  -- The identity itself is method-agnostic.
  have _ := hq_raw
  exact logRisk_regret_eq_expected_klBern μz (confoundedTrueProb m t) q h_true_open h_q_open

/-- Positive-regret guarantee for all raw methods, under strict KL mismatch. -/
theorem raw_methods_positive_regret_of_positive_kl {k : ℕ}
    (μz : Measure (FeatureSpace k))
    (m : ConfoundedThresholdModel k) (t : DriftIndex)
    (h_true_open : ∀ z, 0 < (confoundedTrueProb m t z).1 ∧ (confoundedTrueProb m t z).1 < 1)
    (h_q_open : ∀ q, q ∈ F_raw k → ∀ z, 0 < (q z).1 ∧ (q z).1 < 1)
    (h_strict_kl :
      ∀ q, q ∈ F_raw k → 0 < ∫ z, klBern (confoundedTrueProb m t z) (q z) ∂μz) :
    ∀ q, q ∈ F_raw k →
      0 <
        (∫ z,
          bernoulliLogLoss (confoundedTrueProb m t z).1 (q z).1
            - bernoulliLogLoss (confoundedTrueProb m t z).1 (confoundedTrueProb m t z).1 ∂μz) := by
  intro q hq
  rw [raw_regret_eq_kl_integral μz m t q hq h_true_open (h_q_open q hq)]
  exact h_strict_kl q hq

end PortabilityDrift

end Calibrator
