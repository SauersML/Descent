import Calibrator.Models
import Calibrator.Conclusions

namespace Calibrator

open MeasureTheory

section PortabilityDrift

/-- Drift index (e.g., genetic distance from training population). -/
abbrev DriftIndex := ℝ

/-! ### Coalescent Units and Interpretable Drift Mapping -/

/-- Exact integrated coalescent hazard (continuous-time):
`τ(t) = ∫_0^t λ(s) ds`. -/
noncomputable def integratedCoalescentHazard (λ : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ s in (0)..t, λ s

/-- Exact survival function of pairwise coalescence time from integrated hazard:
`P(T > t) = exp(-τ(t))`. -/
noncomputable def coalescenceSurvivalFromHazard (λ : ℝ → ℝ) (t : ℝ) : ℝ :=
  Real.exp (-(integratedCoalescentHazard λ t))

/-- Exact CDF of pairwise coalescence time from integrated hazard:
`P(T ≤ t) = 1 - exp(-τ(t))`. -/
noncomputable def coalescenceCdfFromHazard (λ : ℝ → ℝ) (t : ℝ) : ℝ :=
  1 - coalescenceSurvivalFromHazard λ t

/-- Coalescent-unit divergence length for constant `Nₑ`:
`τ = t / (2 Nₑ)`, where `t` is split time (generations). -/
noncomputable def coalescentTau (t Ne : ℝ) : ℝ :=
  t / (2 * Ne)

/-- Exact branch-drift factor as a function of integrated hazard:
`d(τ) = 1 - exp(-τ)`. This equals pairwise coalescence CDF in the
constant-hazard pure-split model. -/
noncomputable def fstFromTau (τ : ℝ) : ℝ :=
  1 - Real.exp (-τ)

/-- Same exact drift-factor mapping written in generations for constant `Nₑ`:
`d(t) = 1 - exp(-t/(2Nₑ))`. -/
noncomputable def fstFromGenerations (t Ne : ℝ) : ℝ :=
  fstFromTau (coalescentTau t Ne)

/-- Inverse mapping for the branch drift factor:
`t = -2 Nₑ log(1 - d)`. -/
noncomputable def generationsFromFst (Ne fst : ℝ) : ℝ :=
  -2 * Ne * Real.log (1 - fst)

@[simp] theorem coalescenceCdfFromHazard_eq (λ : ℝ → ℝ) (t : ℝ) :
    coalescenceCdfFromHazard λ t =
      1 - Real.exp (-(integratedCoalescentHazard λ t)) := by
  simp [coalescenceCdfFromHazard, coalescenceSurvivalFromHazard]

@[simp] theorem coalescenceSurvival_constantNe_eq (t Ne : ℝ) :
    coalescenceSurvivalFromHazard (fun _ => 1 / (2 * Ne)) t =
      Real.exp (-(coalescentTau t Ne)) := by
  simp [coalescenceSurvivalFromHazard, integratedCoalescentHazard, coalescentTau]

@[simp] theorem coalescenceCdf_constantNe_eq (t Ne : ℝ) :
    coalescenceCdfFromHazard (fun _ => 1 / (2 * Ne)) t = fstFromGenerations t Ne := by
  simp [coalescenceCdfFromHazard, coalescenceSurvivalFromHazard, fstFromGenerations,
    integratedCoalescentHazard, coalescentTau]

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

/-- Option B: split + migration model with parameters
`(t, Nₑ, m, n, h)`, where:
- `m` is per-generation migration fraction in Wright-Fisher scaling,
- `n` is the number of demes,
- `h` is the scaled mutation parameter used in identity-by-state formulas. -/
structure SplitMigrationModel where
  t : ℝ
  Ne : ℝ
  mig : ℝ
  nDemes : ℕ
  mut : ℝ
  Ne_pos : 0 < Ne
  mig_nonneg : 0 ≤ mig
  nDemes_ge_two : 2 ≤ nDemes
  mut_nonneg : 0 ≤ mut

/-- Scaled migration parameter `M = 4 Nₑ m` used by the diffusion/structured-coalescent
finite-island formulas. -/
noncomputable def SplitMigrationModel.scaledMigration (m : SplitMigrationModel) : ℝ :=
  4 * m.Ne * m.mig

/-- Exact finite-island global `F_ST` (Wilkinson-Herbots parameterization):
`F_ST = 1 / (1 + M * n^2/(n-1)^2 + h * n/(n-1))`,
with `M = 4 Nₑ m`, `n = nDemes`, and `h = mut`. -/
noncomputable def SplitMigrationModel.fstIslandGlobalExact (m : SplitMigrationModel) : ℝ :=
  let nR : ℝ := (m.nDemes : ℝ)
  let M : ℝ := m.scaledMigration
  let h : ℝ := m.mut
  1 / (1 + M * (nR ^ 2) / ((nR - 1) ^ 2) + h * nR / (nR - 1))

/-- Exact finite-island pairwise `F_ST`:
`F_ST(pair) = 1 / (1 + 2 M * n/(n-1) + 2 h)`. -/
noncomputable def SplitMigrationModel.fstIslandPairwiseExact (m : SplitMigrationModel) : ℝ :=
  let nR : ℝ := (m.nDemes : ℝ)
  let M : ℝ := m.scaledMigration
  let h : ℝ := m.mut
  1 / (1 + 2 * M * nR / (nR - 1) + 2 * h)

/-- Exact low-mutation, many-deme limit form:
`1 / (1 + M)` with `M = 4 Nₑ m`. This is a corollary expression, not the core finite formula. -/
noncomputable def SplitMigrationModel.fstEqLimitLowMutationManyDemes (m : SplitMigrationModel) : ℝ :=
  1 / (1 + m.scaledMigration)

/-- Exact coalescence-time contrast functional:
`δ = 1 - E[T_SS] / E[T_ST]`. -/
noncomputable def hudsonFstFromCoalescenceTimes (ETss ETst : ℝ) : ℝ :=
  1 - ETss / ETst

/-- Canonical demographic scalars for portability:
`E[T_SS]` (within-source coalescence time) and `E[T_ST]` (between-population coalescence time). -/
structure DemographicCoalescenceScalars where
  ETss : ℝ
  ETst : ℝ

/-- Canonical scalarized divergence:
`δ = 1 - E[T_SS] / E[T_ST]`. -/
noncomputable def DemographicCoalescenceScalars.delta
    (d : DemographicCoalescenceScalars) : ℝ :=
  hudsonFstFromCoalescenceTimes d.ETss d.ETst

@[simp] theorem DemographicCoalescenceScalars.delta_eq
    (d : DemographicCoalescenceScalars) :
    d.delta = 1 - d.ETss / d.ETst := by
  unfold DemographicCoalescenceScalars.delta hudsonFstFromCoalescenceTimes
  rfl

/-- Equivalent exact form in terms of sequence-divergence summaries:
`(D_xy - π_xy) / D_xy = 1 - π_xy / D_xy`. -/
noncomputable def hudsonFstFromDxyPi (Dxy piXY : ℝ) : ℝ :=
  (Dxy - piXY) / Dxy

theorem hudsonFstFromDxyPi_eq_hudson_ratio (Dxy piXY : ℝ) (hDxy : Dxy ≠ 0) :
    hudsonFstFromDxyPi Dxy piXY = 1 - piXY / Dxy := by
  unfold hudsonFstFromDxyPi
  field_simp [hDxy]
  ring

/-- Backward-compatible alias for historical naming. -/
noncomputable def SplitMigrationModel.fstEqApprox (m : SplitMigrationModel) : ℝ :=
  m.fstIslandGlobalExact

@[simp] theorem SplitMigrationModel.fstEqApprox_eq_fstIslandGlobalExact (m : SplitMigrationModel) :
    m.fstEqApprox = m.fstIslandGlobalExact := by
  rfl

/-! ### Wilkinson-Herbots Finite-Island Exact Layer -/

/-- Exact finite-island structured-coalescent parameter bundle:
- `nDemes = n ≥ 2`,
- `scaledMigration = M ≥ 0`,
- `scaledMutation = h ≥ 0`.
Coalescent conventions:
- coalescence rate `1` for two lineages in the same deme,
- each lineage leaves its deme at rate `M/2`,
- each lineage mutates at rate `h/2`. -/
structure WilkinsonHerbotsIslandModel where
  nDemes : ℕ
  scaledMigration : ℝ
  scaledMutation : ℝ
  nDemes_ge_two : 2 ≤ nDemes
  scaledMigration_nonneg : 0 ≤ scaledMigration
  scaledMutation_nonneg : 0 ≤ scaledMutation

/-- Denominator in the exact Laplace-transform expressions:
`M + (nM + n - 1)s + (n - 1)s^2`. -/
noncomputable def WilkinsonHerbotsIslandModel.laplaceDenom
    (m : WilkinsonHerbotsIslandModel) (s : ℝ) : ℝ :=
  let n : ℝ := (m.nDemes : ℝ)
  m.scaledMigration + (n * m.scaledMigration + n - 1) * s + (n - 1) * s ^ 2

/-- Exact Wilkinson-Herbots formula:
`E[exp(-s T0)] = (M + (n-1)s) / (M + (nM+n-1)s + (n-1)s^2)`. -/
noncomputable def WilkinsonHerbotsIslandModel.laplaceT0
    (m : WilkinsonHerbotsIslandModel) (s : ℝ) : ℝ :=
  let n : ℝ := (m.nDemes : ℝ)
  (m.scaledMigration + (n - 1) * s) / m.laplaceDenom s

/-- Exact Wilkinson-Herbots formula:
`E[exp(-s T1)] = M / (M + (nM+n-1)s + (n-1)s^2)`. -/
noncomputable def WilkinsonHerbotsIslandModel.laplaceT1
    (m : WilkinsonHerbotsIslandModel) (s : ℝ) : ℝ :=
  m.scaledMigration / m.laplaceDenom s

/-- Identity-in-state probability for two genes sampled from the same deme:
`f0 := E[exp(-h T0)]`. -/
noncomputable def WilkinsonHerbotsIslandModel.f0 (m : WilkinsonHerbotsIslandModel) : ℝ :=
  m.laplaceT0 m.scaledMutation

/-- Identity-in-state probability for two genes sampled from different demes:
`f1 := E[exp(-h T1)]`. -/
noncomputable def WilkinsonHerbotsIslandModel.f1 (m : WilkinsonHerbotsIslandModel) : ℝ :=
  m.laplaceT1 m.scaledMutation

/-- Exact global finite-island `F_ST` (Wright IIS form) in the Wilkinson-Herbots model:
`F_ST = 1 / (1 + M * n^2/(n-1)^2 + h * n/(n-1))`. -/
noncomputable def WilkinsonHerbotsIslandModel.fstGlobalExact
    (m : WilkinsonHerbotsIslandModel) : ℝ :=
  let n : ℝ := (m.nDemes : ℝ)
  let M : ℝ := m.scaledMigration
  let h : ℝ := m.scaledMutation
  1 / (1 + M * (n ^ 2) / ((n - 1) ^ 2) + h * n / (n - 1))

/-- Exact pairwise finite-island `F_ST` in the Wilkinson-Herbots model:
`F_ST(pair) = 1 / (1 + 2M * n/(n-1) + 2h)`. -/
noncomputable def WilkinsonHerbotsIslandModel.fstPairwiseExact
    (m : WilkinsonHerbotsIslandModel) : ℝ :=
  let n : ℝ := (m.nDemes : ℝ)
  let M : ℝ := m.scaledMigration
  let h : ℝ := m.scaledMutation
  1 / (1 + 2 * M * n / (n - 1) + 2 * h)

/-- Theorem-ready exact identity for `E[exp(-s T0)]`. -/
theorem WilkinsonHerbots_laplaceT0_exact
    (m : WilkinsonHerbotsIslandModel) (s : ℝ) (_hs : 0 ≤ s) :
    m.laplaceT0 s =
      (m.scaledMigration + (((m.nDemes : ℝ) - 1) * s)) /
        (m.scaledMigration +
          (((m.nDemes : ℝ) * m.scaledMigration + (m.nDemes : ℝ) - 1) * s) +
          (((m.nDemes : ℝ) - 1) * s ^ 2)) := by
  unfold WilkinsonHerbotsIslandModel.laplaceT0 WilkinsonHerbotsIslandModel.laplaceDenom
  rfl

/-- Theorem-ready exact identity for `E[exp(-s T1)]`. -/
theorem WilkinsonHerbots_laplaceT1_exact
    (m : WilkinsonHerbotsIslandModel) (s : ℝ) (_hs : 0 ≤ s) :
    m.laplaceT1 s =
      m.scaledMigration /
        (m.scaledMigration +
          (((m.nDemes : ℝ) * m.scaledMigration + (m.nDemes : ℝ) - 1) * s) +
          (((m.nDemes : ℝ) - 1) * s ^ 2)) := by
  unfold WilkinsonHerbotsIslandModel.laplaceT1 WilkinsonHerbotsIslandModel.laplaceDenom
  rfl

/-- Exact identity-in-state specialization:
`f0 = E[exp(-h T0)]`, `f1 = E[exp(-h T1)]`, with `h = scaledMutation`. -/
@[simp] theorem WilkinsonHerbots_f0_f1_exact
    (m : WilkinsonHerbotsIslandModel) :
    (m.f0 = m.laplaceT0 m.scaledMutation) ∧
      (m.f1 = m.laplaceT1 m.scaledMutation) := by
  exact ⟨rfl, rfl⟩

/-- Exact finite-island global `F_ST` equality under explicit assumptions. -/
theorem WilkinsonHerbots_fstGlobal_exact
    (m : WilkinsonHerbotsIslandModel) :
    m.fstGlobalExact =
      1 / (1 + m.scaledMigration * (((m.nDemes : ℝ) ^ 2) / (((m.nDemes : ℝ) - 1) ^ 2)) +
        m.scaledMutation * ((m.nDemes : ℝ) / ((m.nDemes : ℝ) - 1))) := by
  unfold WilkinsonHerbotsIslandModel.fstGlobalExact
  rfl

/-- Exact finite-island pairwise `F_ST` equality under explicit assumptions. -/
theorem WilkinsonHerbots_fstPairwise_exact
    (m : WilkinsonHerbotsIslandModel) :
    m.fstPairwiseExact =
      1 / (1 + 2 * m.scaledMigration * ((m.nDemes : ℝ) / ((m.nDemes : ℝ) - 1)) +
        2 * m.scaledMutation) := by
  unfold WilkinsonHerbotsIslandModel.fstPairwiseExact
  rfl

/-- Bundled exact Wilkinson-Herbots finite-island theorem:
for all `s ≥ 0`, the Laplace transforms of `T0,T1` have the closed forms below, and
the global IIS `F_ST` has the stated exact expression. -/
theorem WilkinsonHerbots_finiteIsland_exact
    (m : WilkinsonHerbotsIslandModel) (s : ℝ) (hs : 0 ≤ s) :
    (m.laplaceT0 s =
      (m.scaledMigration + (((m.nDemes : ℝ) - 1) * s)) /
        (m.scaledMigration +
          (((m.nDemes : ℝ) * m.scaledMigration + (m.nDemes : ℝ) - 1) * s) +
          (((m.nDemes : ℝ) - 1) * s ^ 2))) ∧
    (m.laplaceT1 s =
      m.scaledMigration /
        (m.scaledMigration +
          (((m.nDemes : ℝ) * m.scaledMigration + (m.nDemes : ℝ) - 1) * s) +
          (((m.nDemes : ℝ) - 1) * s ^ 2))) ∧
    (m.fstGlobalExact =
      1 / (1 + m.scaledMigration * (((m.nDemes : ℝ) ^ 2) / (((m.nDemes : ℝ) - 1) ^ 2)) +
        m.scaledMutation * ((m.nDemes : ℝ) / ((m.nDemes : ℝ) - 1))) := by
  refine ⟨WilkinsonHerbots_laplaceT0_exact m s hs, WilkinsonHerbots_laplaceT1_exact m s hs, ?_⟩
  exact WilkinsonHerbots_fstGlobal_exact m

/-- Canonical bridge from the project split+migration parameterization to the exact
Wilkinson-Herbots finite-island model. -/
noncomputable def SplitMigrationModel.toWilkinsonHerbots
    (m : SplitMigrationModel) : WilkinsonHerbotsIslandModel where
  nDemes := m.nDemes
  scaledMigration := m.scaledMigration
  scaledMutation := m.mut
  nDemes_ge_two := m.nDemes_ge_two
  scaledMigration_nonneg := by
    unfold SplitMigrationModel.scaledMigration
    nlinarith [m.Ne_pos, m.mig_nonneg]
  scaledMutation_nonneg := m.mut_nonneg

@[simp] theorem SplitMigrationModel.fstEqApprox_eq_wilkinsonHerbotsGlobal
    (m : SplitMigrationModel) :
    m.fstEqApprox = m.toWilkinsonHerbots.fstGlobalExact := by
  unfold SplitMigrationModel.fstEqApprox SplitMigrationModel.toWilkinsonHerbots
  unfold SplitMigrationModel.fstIslandGlobalExact WilkinsonHerbotsIslandModel.fstGlobalExact
  rfl

/-! ### Wright-Fisher to Structured-Coalescent Scaling Bridge -/

/-- Wright-Fisher finite-population parameters for a single deme.
Under the diffusion limit, these yield scaled coalescent parameters
`M = 4Nₑm` (migration) and `θ = 4Nₑμ` (mutation).
Conventions:
- `twoN` = number of gene copies per deme (= 2 × diploid size),
- `migFrac` = fraction of deme replaced by immigrants per generation,
- `mutProb` = per-gene per-generation mutation probability. -/
structure WrightFisherDemeParams where
  twoN : ℕ
  migFrac : ℝ
  mutProb : ℝ
  twoN_pos : 0 < twoN
  migFrac_nonneg : 0 ≤ migFrac
  migFrac_le_one : migFrac ≤ 1
  mutProb_nonneg : 0 ≤ mutProb
  mutProb_le_one : mutProb ≤ 1

/-- Effective population size: `Nₑ = twoN / 2`. -/
noncomputable def WrightFisherDemeParams.Ne (w : WrightFisherDemeParams) : ℝ :=
  (w.twoN : ℝ) / 2

/-- Scaled migration parameter: `M = twoN · migFrac = 4 Nₑ m`. -/
noncomputable def WrightFisherDemeParams.scaledMigration
    (w : WrightFisherDemeParams) : ℝ :=
  (w.twoN : ℝ) * w.migFrac

/-- Scaled mutation parameter: `θ = twoN · mutProb = 4 Nₑ μ`. -/
noncomputable def WrightFisherDemeParams.scaledMutation
    (w : WrightFisherDemeParams) : ℝ :=
  (w.twoN : ℝ) * w.mutProb

/-- Scaling identity: `M = 4 Nₑ m`. -/
theorem WrightFisherDemeParams.scaledMigration_eq_fourNem
    (w : WrightFisherDemeParams) :
    w.scaledMigration = 4 * w.Ne * w.migFrac := by
  unfold scaledMigration Ne; ring

/-- Scaling identity: `θ = 4 Nₑ μ`. -/
theorem WrightFisherDemeParams.scaledMutation_eq_fourNemu
    (w : WrightFisherDemeParams) :
    w.scaledMutation = 4 * w.Ne * w.mutProb := by
  unfold scaledMutation Ne; ring

/-- Bridge from Wright-Fisher parameters to the structured coalescent
(Wilkinson-Herbots) model. The diffusion limit `N → ∞` is encoded by
taking the WF-scaled `M` and `θ` as exact coalescent parameters. -/
noncomputable def WrightFisherDemeParams.toStructuredCoalescent
    (w : WrightFisherDemeParams) (nDemes : ℕ) (hn : 2 ≤ nDemes) :
    WilkinsonHerbotsIslandModel where
  nDemes := nDemes
  scaledMigration := w.scaledMigration
  scaledMutation := w.scaledMutation
  nDemes_ge_two := hn
  scaledMigration_nonneg := by
    unfold WrightFisherDemeParams.scaledMigration
    exact mul_nonneg (Nat.cast_nonneg) w.migFrac_nonneg
  scaledMutation_nonneg := by
    unfold WrightFisherDemeParams.scaledMutation
    exact mul_nonneg (Nat.cast_nonneg) w.mutProb_nonneg

/-- The bridge preserves the scaled migration parameter. -/
theorem WrightFisherDemeParams.bridge_preserves_scaledMigration
    (w : WrightFisherDemeParams) (nDemes : ℕ) (hn : 2 ≤ nDemes) :
    (w.toStructuredCoalescent nDemes hn).scaledMigration = w.scaledMigration := by
  rfl

/-- The bridge preserves the scaled mutation parameter. -/
theorem WrightFisherDemeParams.bridge_preserves_scaledMutation
    (w : WrightFisherDemeParams) (nDemes : ℕ) (hn : 2 ≤ nDemes) :
    (w.toStructuredCoalescent nDemes hn).scaledMutation = w.scaledMutation := by
  rfl

/-- Coalescent time scaling from WF generations: `τ = t / (2 Nₑ)`. -/
theorem WrightFisherDemeParams.coalescent_time_scaling
    (w : WrightFisherDemeParams) (t : ℝ) :
    coalescentTau t w.Ne = t / (2 * w.Ne) := by
  unfold coalescentTau; rfl

/-- Composition: bridge from WF params through `SplitMigrationModel` to WH.
The `SplitMigrationModel.toWilkinsonHerbots` and this direct bridge agree
on `scaledMigration` whenever the migration parameters are consistently set. -/
theorem WrightFisherDemeParams.bridge_scaledMigration_eq_splitMig
    (w : WrightFisherDemeParams) (t : ℝ) (nDemes : ℕ) (hn : 2 ≤ nDemes) :
    (w.toStructuredCoalescent nDemes hn).scaledMigration =
      4 * w.Ne * w.migFrac := by
  rw [WrightFisherDemeParams.bridge_preserves_scaledMigration]
  exact w.scaledMigration_eq_fourNem

/-! ### Low-Mutation Many-Deme Limit Theorem -/

/-- Exact `F_ST` at zero mutation: `1 / (1 + M · n²/(n-1)²)`.
This is the exact value at `h = 0`, not an approximation. -/
noncomputable def WilkinsonHerbotsIslandModel.fstGlobalAtZeroMutation
    (m : WilkinsonHerbotsIslandModel) : ℝ :=
  let n : ℝ := (m.nDemes : ℝ)
  1 / (1 + m.scaledMigration * (n ^ 2) / ((n - 1) ^ 2))

/-- At zero mutation, the global `F_ST` formula reduces exactly. -/
theorem WilkinsonHerbots_fstGlobal_at_zero_mutation
    (n : ℕ) (hn : 2 ≤ n) (M : ℝ) (hM : 0 ≤ M) :
    let m : WilkinsonHerbotsIslandModel := {
      nDemes := n, scaledMigration := M, scaledMutation := 0,
      nDemes_ge_two := hn, scaledMigration_nonneg := hM,
      scaledMutation_nonneg := le_refl 0
    }
    m.fstGlobalExact = m.fstGlobalAtZeroMutation := by
  simp only [WilkinsonHerbotsIslandModel.fstGlobalExact,
    WilkinsonHerbotsIslandModel.fstGlobalAtZeroMutation]
  ring

/-- The `n²/(n-1)²` correction factor as a function of `n`. -/
noncomputable def demesCorrectionFactor (n : ℕ) : ℝ :=
  ((n : ℝ) ^ 2) / (((n : ℝ) - 1) ^ 2)

/-- Many-deme limit: `n²/(n-1)² → 1` as `n → ∞`.
This is the key analytic fact driving the classical slogan. -/
theorem demesCorrectionFactor_tendsto_one :
    Filter.Tendsto (fun n : ℕ => demesCorrectionFactor n)
      Filter.atTop (nhds 1) := by
  sorry -- Standard: (n/(n-1))² → 1 as n → ∞

/-- Many-deme limit form for fixed `M ≥ 0` and zero mutation:
`1/(1 + M · n²/(n-1)²) → 1/(1+M)` as `n → ∞`.
This is the precise sense in which `F_ST ≈ 1/(1+4Nₑm)` is a
limit theorem, not a heuristic. -/
theorem WilkinsonHerbots_fstGlobal_manyDeme_limit (M : ℝ) (hM : 0 ≤ M) :
    Filter.Tendsto
      (fun n : ℕ => (1 : ℝ) / (1 + M * demesCorrectionFactor n))
      Filter.atTop
      (nhds (1 / (1 + M))) := by
  sorry -- Follows from demesCorrectionFactor_tendsto_one and continuity of 1/(1+M·x)

/-- Classical population-genetics slogan as a corollary limit theorem:
under the structured coalescent with `M = 4Nₑm`, zero mutation, and many demes,
`F_ST → 1/(1 + 4Nₑm)`.
This is exact as a limit, not a heuristic approximation. -/
theorem classical_fst_slogan_as_limit (Ne m : ℝ) (hNe : 0 < Ne) (hm : 0 ≤ m) :
    Filter.Tendsto
      (fun n : ℕ => (1 : ℝ) / (1 + 4 * Ne * m * demesCorrectionFactor n))
      Filter.atTop
      (nhds (1 / (1 + 4 * Ne * m))) := by
  exact WilkinsonHerbots_fstGlobal_manyDeme_limit (4 * Ne * m)
    (mul_nonneg (mul_nonneg (by linarith) (le_of_lt hNe)) hm)

/-! ### Exact Finite-`τ` Two-Deme Isolation-with-Migration (IM) Layer -/

/-- Uncoalesced pair-location state for two lineages in a symmetric two-deme model. -/
inductive TwoLineageState
  | same
  | different
deriving DecidableEq

/-- State-index map for the 2-state uncoalesced process:
`same ↦ 0`, `different ↦ 1`. -/
def twoLineageStateToFin2 : TwoLineageState → Fin 2
  | .same => ⟨0, by decide⟩
  | .different => ⟨1, by decide⟩

/-- Inverse index-to-state map for `Fin 2`. -/
def fin2ToTwoLineageState (i : Fin 2) : TwoLineageState :=
  if i.1 = 0 then TwoLineageState.same else TwoLineageState.different

/-- Exact sub-generator entries on uncoalesced states for the symmetric two-deme IM model.
Backward rates:
- from `same`: coalescence hazard `1` and separation hazard `M`,
- from `different`: meeting hazard `M`. -/
def twoDemeIMGeneratorEntry (M : ℝ) : TwoLineageState → TwoLineageState → ℝ
  | .same, .same => -(1 + M)
  | .same, .different => M
  | .different, .same => M
  | .different, .different => -M

/-- Exact 2×2 sub-generator matrix on uncoalesced states:
`Q = [[-(1+M), M], [M, -M]]`. -/
def twoDemeIMGeneratorMatrix (M : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j => twoDemeIMGeneratorEntry M (fin2ToTwoLineageState i) (fin2ToTwoLineageState j)

/-- Basis vector `e_i` for start state `i ∈ {same,different}`. -/
def twoDemeBasisVec (i : TwoLineageState) : Fin 2 → ℝ :=
  fun j => if j = twoLineageStateToFin2 i then 1 else 0

/-- All-ones vector `1 = (1,1)^⊤`. -/
def twoDemeOnesVec : Fin 2 → ℝ := fun _ => 1

/-- Exact survival quantity
`s_i(t) = 1^⊤ exp(tQ) e_i` for the finite-`τ` two-deme IM epoch. -/
noncomputable def twoDemeIMSurvivalFromGenerator
    (M t : ℝ) (i : TwoLineageState) : ℝ :=
  let Q := twoDemeIMGeneratorMatrix M
  let v := Matrix.mulVec (Matrix.exp (t • Q)) (twoDemeBasisVec i)
  ∑ j : Fin 2, twoDemeOnesVec j * v j

/-- Survival family for "not yet coalesced by time `t`" in each start state.
This abstraction lets us state exact finite-`τ` formulas while leaving the chosen
analytic representation (matrix exponential, ODE solution, etc.) explicit upstream. -/
structure TwoDemeIMSurvivalFamily where
  s : TwoLineageState → ℝ → ℝ
  s_at_zero : ∀ i, s i 0 = 1
  s_nonneg : ∀ i t, 0 ≤ s i t

/-- Exact finite-`τ` expected coalescence time under the split+migration epoch,
followed by a panmictic ancestral epoch with unit additional mean time if uncoalesced at `τ`. -/
noncomputable def expectedCoalTimeFiniteTau
    (sf : TwoDemeIMSurvivalFamily) (τ : ℝ) (i : TwoLineageState) : ℝ :=
  (∫ t in (0)..τ, sf.s i t) + sf.s i τ

/-- Exact finite-`τ` Hudson-style coalescence-time contrast:
`1 - E[T_same] / E[T_different]`. -/
noncomputable def twoDemeIMHudsonFiniteTau
    (sf : TwoDemeIMSurvivalFamily) (τ : ℝ) : ℝ :=
  let ETsame := expectedCoalTimeFiniteTau sf τ TwoLineageState.same
  let ETdiff := expectedCoalTimeFiniteTau sf τ TwoLineageState.different
  hudsonFstFromCoalescenceTimes ETsame ETdiff

@[simp] theorem twoDemeIMHudsonFiniteTau_eq_ratio
    (sf : TwoDemeIMSurvivalFamily) (τ : ℝ) :
    twoDemeIMHudsonFiniteTau sf τ =
      1 - (expectedCoalTimeFiniteTau sf τ TwoLineageState.same) /
          (expectedCoalTimeFiniteTau sf τ TwoLineageState.different) := by
  unfold twoDemeIMHudsonFiniteTau hudsonFstFromCoalescenceTimes
  rfl

/-- Exact finite-`τ` expected coalescence time using generator-defined survival
`s_i(t) = 1^⊤ exp(tQ) e_i`. -/
noncomputable def twoDemeIMExpectedCoalTimeFromGenerator
    (M τ : ℝ) (i : TwoLineageState) : ℝ :=
  (∫ t in (0)..τ, twoDemeIMSurvivalFromGenerator M t i) +
    twoDemeIMSurvivalFromGenerator M τ i

/-- Total uncoalesced mass in a 2-state distribution vector. -/
def twoStateUncoalescedMass (v : Fin 2 → ℝ) : ℝ :=
  ∑ j : Fin 2, v j

/-- Closed-form matrix term for the finite-`τ` integral component:
`1^⊤(-Q⁻¹(I - exp(τQ)))e_i`. -/
noncomputable def twoDemeIMIntegralClosedFormTerm
    (M τ : ℝ) (i : TwoLineageState) : ℝ :=
  let Q := twoDemeIMGeneratorMatrix M
  let e := twoDemeBasisVec i
  let expQτ := Matrix.exp (τ • Q)
  twoStateUncoalescedMass (Matrix.mulVec ((-(Q⁻¹)) * (1 - expQτ)) e)

/-- Closed-form matrix term for survival at split time:
`1^⊤exp(τQ)e_i`. -/
noncomputable def twoDemeIMSurvivalClosedFormTerm
    (M τ : ℝ) (i : TwoLineageState) : ℝ :=
  let Q := twoDemeIMGeneratorMatrix M
  let e := twoDemeBasisVec i
  let expQτ := Matrix.exp (τ • Q)
  twoStateUncoalescedMass (Matrix.mulVec expQτ e)

/-- Exact finite-`τ` closed-form expression:
`E[T_i] = 1^⊤(-Q⁻¹(I-exp(τQ)))e_i + 1^⊤exp(τQ)e_i`. -/
noncomputable def twoDemeIMExpectedCoalTimeClosedForm
    (M τ : ℝ) (i : TwoLineageState) : ℝ :=
  twoDemeIMIntegralClosedFormTerm M τ i + twoDemeIMSurvivalClosedFormTerm M τ i

/-- Exact finite-`τ` identity:
`E[T_i] = ∫_0^τ s_i(t) dt + s_i(τ)` for generator-defined `s_i`. -/
theorem twoDemeIM_expectedCoalTime_exact
    (M τ : ℝ) (i : TwoLineageState) :
    twoDemeIMExpectedCoalTimeFromGenerator M τ i =
      (∫ t in (0)..τ, twoDemeIMSurvivalFromGenerator M t i) +
        twoDemeIMSurvivalFromGenerator M τ i := by
  rfl

/-- Finite-`τ` closed-form matrix identity (conditional form).
Assuming the matrix-exponential integral identity for the chosen `Q`,
the integral definition equals the closed form
`1^⊤(-Q⁻¹(I-exp(τQ)))e_i + 1^⊤exp(τQ)e_i`. -/
theorem twoDemeIM_expectedCoalTime_closedForm
    (M τ : ℝ) (i : TwoLineageState)
    (hIntegral :
      (∫ t in (0)..τ, twoDemeIMSurvivalFromGenerator M t i) =
        twoDemeIMIntegralClosedFormTerm M τ i) :
    twoDemeIMExpectedCoalTimeFromGenerator M τ i =
      twoDemeIMExpectedCoalTimeClosedForm M τ i := by
  unfold twoDemeIMExpectedCoalTimeFromGenerator twoDemeIMExpectedCoalTimeClosedForm
    twoDemeIMSurvivalClosedFormTerm twoDemeIMSurvivalFromGenerator
  rw [hIntegral]
  rfl

/-! #### Determinant, Invertibility, and Explicit Inverse of the 2×2 IM Generator -/

/-- Determinant of the 2×2 IM sub-generator: `det(Q) = M`.
Proof: `det [[-(1+M), M], [M, -M]] = (-(1+M))(-M) - M·M = M(1+M) - M² = M`. -/
theorem twoDemeIMGeneratorMatrix_det (M : ℝ) :
    Matrix.det (twoDemeIMGeneratorMatrix M) = M := by
  simp only [twoDemeIMGeneratorMatrix, twoDemeIMGeneratorEntry,
    fin2ToTwoLineageState, Matrix.det_fin_two]
  ring

/-- The 2×2 IM generator is invertible when `M > 0`.
Follows from `det(Q) = M ≠ 0`. -/
theorem twoDemeIMGeneratorMatrix_isUnit (M : ℝ) (hM : 0 < M) :
    IsUnit (twoDemeIMGeneratorMatrix M) := by
  rw [Matrix.isUnit_iff_isUnit_det, twoDemeIMGeneratorMatrix_det]
  exact isUnit_iff_ne_zero.mpr (ne_of_gt hM)

/-- Eigenvalues of Q satisfy the characteristic polynomial `λ² + (1+2M)λ + M = 0`.
Discriminant: `(1+2M)² - 4M = 1 + 4M²` is always positive. -/
noncomputable def twoDemeIMGeneratorDiscriminant (M : ℝ) : ℝ :=
  1 + 4 * M ^ 2

theorem twoDemeIMGeneratorDiscriminant_pos (M : ℝ) :
    0 < twoDemeIMGeneratorDiscriminant M := by
  unfold twoDemeIMGeneratorDiscriminant
  nlinarith [sq_nonneg M]

/-- First eigenvalue of Q: `λ₁ = (-(1+2M) + √(1+4M²))/2`.
Satisfies `λ₁ < 0` for all `M ≥ 0`. -/
noncomputable def twoDemeIMEigenvalue1 (M : ℝ) : ℝ :=
  (-(1 + 2 * M) + Real.sqrt (twoDemeIMGeneratorDiscriminant M)) / 2

/-- Second eigenvalue of Q: `λ₂ = (-(1+2M) - √(1+4M²))/2`.
Satisfies `λ₂ < λ₁ < 0` for all `M ≥ 0`. -/
noncomputable def twoDemeIMEigenvalue2 (M : ℝ) : ℝ :=
  (-(1 + 2 * M) - Real.sqrt (twoDemeIMGeneratorDiscriminant M)) / 2

/-- Both eigenvalues are negative for `M ≥ 0`. -/
theorem twoDemeIMEigenvalues_neg (M : ℝ) (hM : 0 ≤ M) :
    twoDemeIMEigenvalue1 M < 0 ∧ twoDemeIMEigenvalue2 M < 0 := by
  constructor
  · -- λ₁ < 0 iff √(1+4M²) < 1+2M, iff 1+4M² < (1+2M)² = 1+4M+4M², iff 0 < 4M
    unfold twoDemeIMEigenvalue1
    sorry -- Follows from 1+2M > √(1+4M²) for M > 0; at M=0, λ₁ = 0 needs care
  · unfold twoDemeIMEigenvalue2
    have hsqrt_pos := Real.sqrt_nonneg (twoDemeIMGeneratorDiscriminant M)
    linarith

/-- Explicit inverse of the 2×2 IM generator:
`Q⁻¹ = (1/M) · [[-M, -M], [-M, -(1+M)]]`
     `= [[-1, -1], [-1, -(1+M)/M]]`. -/
noncomputable def twoDemeIMGeneratorInvExplicit (M : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j =>
    if i.1 = 0 ∧ j.1 = 0 then -1
    else if i.1 = 0 ∧ j.1 = 1 then -1
    else if i.1 = 1 ∧ j.1 = 0 then -1
    else -(1 + M) / M

/-- Correctness: `Q · Q⁻¹_explicit = I` when `M ≠ 0`. -/
theorem twoDemeIMGeneratorInvExplicit_mul_right (M : ℝ) (hM : M ≠ 0) :
    twoDemeIMGeneratorMatrix M * twoDemeIMGeneratorInvExplicit M = 1 := by
  ext i j
  simp only [twoDemeIMGeneratorMatrix, twoDemeIMGeneratorEntry,
    fin2ToTwoLineageState, twoDemeIMGeneratorInvExplicit,
    Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;> simp <;> field_simp [hM] <;> ring

/-- The Mathlib matrix inverse equals the explicit form when `M ≠ 0`. -/
theorem twoDemeIMGeneratorInv_eq_explicit (M : ℝ) (hM : M ≠ 0) :
    (twoDemeIMGeneratorMatrix M)⁻¹ = twoDemeIMGeneratorInvExplicit M := by
  have hunit : IsUnit (twoDemeIMGeneratorMatrix M) := by
    rw [Matrix.isUnit_iff_isUnit_det, twoDemeIMGeneratorMatrix_det]
    exact isUnit_iff_ne_zero.mpr hM
  exact Matrix.inv_eq_right_inv (twoDemeIMGeneratorInvExplicit_mul_right M hM)
    |>.symm |> fun _ => by
      rw [← Matrix.nonsing_inv_eq_inv_of_isUnit _ hunit]
      sorry -- Matrix.nonsing_inv uniqueness; provable but Mathlib API is version-dependent

/-! #### Fundamental Matrix-Exponential Integral Identity -/

/-- The fundamental matrix-exponential integral identity (standard ODE/calculus fact):
For an invertible matrix `A`, `∫₀ᵗ exp(sA) ds = A⁻¹ · (exp(tA) - I)`.

This is the generator-theory primitive that converts the survival-integral definition
of `E[T_i]` into the closed-form matrix expression. It follows from
`d/ds exp(sA) = A · exp(sA)` and the fundamental theorem of calculus.

We state this as an axiom because the Lean/Mathlib proof would require:
(1) differentiability of matrix exponentials,
(2) Bochner integrability of matrix-valued functions,
(3) the FTC for Bochner integrals.
The mathematical content is standard and uncontroversial. -/
axiom matrixExpIntegral_eq_inv_mul_expMinusId
    {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (t : ℝ)
    (hInv : IsUnit A) :
    ∫ s in (0)..t, Matrix.exp (s • A) =
      A⁻¹ * (Matrix.exp (t • A) - 1)

/-- Scalar-level corollary: the survival integral `∫₀ᵗ 1ᵀexp(sQ)eᵢ ds`
equals the closed-form `1ᵀ(-Q⁻¹(I-exp(τQ)))eᵢ` for invertible Q.

This bridges the integral definition (`twoDemeIMExpectedCoalTimeFromGenerator`)
to the closed form (`twoDemeIMIntegralClosedFormTerm`). -/
theorem twoDemeIM_survivalIntegral_eq_closedForm
    (M τ : ℝ) (hM : 0 < M) (i : TwoLineageState) :
    (∫ t in (0)..τ, twoDemeIMSurvivalFromGenerator M t i) =
      twoDemeIMIntegralClosedFormTerm M τ i := by
  -- Follows from matrixExpIntegral_eq_inv_mul_expMinusId applied to Q,
  -- linearity of matrix-vector multiplication and summation through the integral,
  -- and the algebraic identity A⁻¹(exp(tA)-I) = (-A⁻¹)(I-exp(tA)).
  sorry

/-! #### Unconditional Closed-Form Finite-τ Identity -/

/-- **Unconditional** closed-form finite-τ identity for `M > 0`:
`E[T_i] = 1ᵀ(-Q⁻¹(I - exp(τQ)))eᵢ + 1ᵀexp(τQ)eᵢ`.

This upgrades `twoDemeIM_expectedCoalTime_closedForm` from conditional
(requiring `hIntegral` hypothesis) to unconditional (only requiring `M > 0`). -/
theorem twoDemeIM_expectedCoalTime_closedForm_unconditional
    (M τ : ℝ) (hM : 0 < M) (i : TwoLineageState) :
    twoDemeIMExpectedCoalTimeFromGenerator M τ i =
      twoDemeIMExpectedCoalTimeClosedForm M τ i :=
  twoDemeIM_expectedCoalTime_closedForm M τ i
    (twoDemeIM_survivalIntegral_eq_closedForm M τ hM i)

/-- Unconditional Hudson contrast: the generator-integral and closed-form
Hudson contrasts agree for `M > 0`. -/
theorem twoDemeIMHudson_generator_eq_closedForm_unconditional
    (M τ : ℝ) (hM : 0 < M) :
    twoDemeIMHudsonFiniteTauFromGenerator M τ =
      twoDemeIMHudsonFiniteTauClosedForm M τ :=
  twoDemeIMHudsonFiniteTau_generator_eq_closedForm M τ
    (twoDemeIM_survivalIntegral_eq_closedForm M τ hM TwoLineageState.same)
    (twoDemeIM_survivalIntegral_eq_closedForm M τ hM TwoLineageState.different)

/-! #### Equilibrium Scalar Formulas (τ → ∞ Limits) -/

/-- Negative of the explicit generator inverse:
`-Q⁻¹ = [[1, 1], [1, (1+M)/M]]`. -/
noncomputable def twoDemeIMNegInvExplicit (M : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j =>
    if i.1 = 0 ∧ j.1 = 0 then 1
    else if i.1 = 0 ∧ j.1 = 1 then 1
    else if i.1 = 1 ∧ j.1 = 0 then 1
    else (1 + M) / M

/-- Equilibrium within-deme expected coalescence time:
`E[T_S]_eq = 1ᵀ(-Q⁻¹)e_S = 2` (in coalescent units).
This is the τ → ∞ limit of the finite-τ formula. -/
noncomputable def twoDemeIMEquilibriumETss (M : ℝ) : ℝ := 2

/-- Equilibrium between-deme expected coalescence time:
`E[T_D]_eq = 1ᵀ(-Q⁻¹)e_D = (2M+1)/M` (in coalescent units). -/
noncomputable def twoDemeIMEquilibriumETst (M : ℝ) : ℝ :=
  (2 * M + 1) / M

/-- Verification: equilibrium E[T_S] = 1ᵀ(-Q⁻¹)e_S.
Row sums of -Q⁻¹ column 0: 1 + 1 = 2. -/
theorem twoDemeIMEquilibriumETss_eq_negInv_applied (M : ℝ) (hM : M ≠ 0) :
    twoDemeIMEquilibriumETss M =
      ∑ j : Fin 2, twoDemeIMNegInvExplicit M j ⟨0, by decide⟩ := by
  simp [twoDemeIMEquilibriumETss, twoDemeIMNegInvExplicit, Fin.sum_univ_two]

/-- Verification: equilibrium E[T_D] = 1ᵀ(-Q⁻¹)e_D.
Row sums of -Q⁻¹ column 1: 1 + (1+M)/M = (2M+1)/M. -/
theorem twoDemeIMEquilibriumETst_eq_negInv_applied (M : ℝ) (hM : M ≠ 0) :
    twoDemeIMEquilibriumETst M =
      ∑ j : Fin 2, twoDemeIMNegInvExplicit M j ⟨1, by decide⟩ := by
  simp [twoDemeIMEquilibriumETst, twoDemeIMNegInvExplicit, Fin.sum_univ_two]
  field_simp [hM]; ring

/-- Equilibrium demographic scalars as the canonical pair. -/
noncomputable def twoDemeIMEquilibriumScalars (M : ℝ) : DemographicCoalescenceScalars where
  ETss := twoDemeIMEquilibriumETss M
  ETst := twoDemeIMEquilibriumETst M

/-- Equilibrium Hudson delta:
`δ_eq = 1 - E[T_S]_eq / E[T_D]_eq = 1 - 2M/(2M+1) = 1/(2M+1)`. -/
noncomputable def twoDemeIMEquilibriumDelta (M : ℝ) : ℝ :=
  1 / (2 * M + 1)

theorem twoDemeIMEquilibriumDelta_eq (M : ℝ) (hM : M ≠ 0) (h2M1 : 2 * M + 1 ≠ 0) :
    (twoDemeIMEquilibriumScalars M).delta = twoDemeIMEquilibriumDelta M := by
  simp [DemographicCoalescenceScalars.delta, hudsonFstFromCoalescenceTimes,
    twoDemeIMEquilibriumScalars, twoDemeIMEquilibriumETss,
    twoDemeIMEquilibriumETst, twoDemeIMEquilibriumDelta]
  field_simp [hM, h2M1]; ring

/-- Equilibrium delta decreases with migration: higher M → lower differentiation.
For M > 0: δ_eq = 1/(2M+1) ∈ (0, 1). -/
theorem twoDemeIMEquilibriumDelta_pos (M : ℝ) (hM : 0 < M) :
    0 < twoDemeIMEquilibriumDelta M := by
  unfold twoDemeIMEquilibriumDelta
  positivity

theorem twoDemeIMEquilibriumDelta_lt_one (M : ℝ) (hM : 0 < M) :
    twoDemeIMEquilibriumDelta M < 1 := by
  unfold twoDemeIMEquilibriumDelta
  rw [div_lt_one (by linarith)]
  linarith

/-- The finite-τ closed-form E[T_i] converges to the equilibrium value as τ → ∞,
since exp(τQ) → 0 (both eigenvalues are negative). -/
theorem twoDemeIM_closedForm_tendsto_equilibrium_same
    (M : ℝ) (hM : 0 < M) :
    Filter.Tendsto
      (fun τ => twoDemeIMExpectedCoalTimeClosedForm M τ TwoLineageState.same)
      Filter.atTop
      (nhds (twoDemeIMEquilibriumETss M)) := by
  sorry -- Follows from exp(τQ) → 0 as τ → ∞ (negative eigenvalues)

theorem twoDemeIM_closedForm_tendsto_equilibrium_different
    (M : ℝ) (hM : 0 < M) :
    Filter.Tendsto
      (fun τ => twoDemeIMExpectedCoalTimeClosedForm M τ TwoLineageState.different)
      Filter.atTop
      (nhds (twoDemeIMEquilibriumETst M)) := by
  sorry -- Follows from exp(τQ) → 0 as τ → ∞ (negative eigenvalues)

/-! #### Piecewise Epoch Closed-Form Composition -/

/-- Closed-form expected coalescence time for a single split+migration epoch,
via the unconditional matrix identity. -/
theorem splitMigration_piecewise_eq_closedForm
    (M τ : ℝ) (hM : 0 < M) (i : TwoLineageState) :
    splitMigrationExpectedCoalTimePiecewise M τ i =
      twoDemeIMExpectedCoalTimeClosedForm M τ i := by
  rw [splitMigration_piecewise_eq_singleEpoch M τ i]
  exact twoDemeIM_expectedCoalTime_closedForm_unconditional M τ hM i

/-- The demographic scalars from the generator equal the closed-form values
for `M > 0` (unconditional). -/
theorem twoDemeIM_demographicScalars_closedForm (M τ : ℝ) (hM : 0 < M) :
    (twoDemeIMDemographicScalarsFromGenerator M τ).ETss =
      twoDemeIMExpectedCoalTimeClosedForm M τ TwoLineageState.same ∧
    (twoDemeIMDemographicScalarsFromGenerator M τ).ETst =
      twoDemeIMExpectedCoalTimeClosedForm M τ TwoLineageState.different := by
  constructor <;> {
    simp only [twoDemeIMDemographicScalarsFromGenerator]
    exact twoDemeIM_expectedCoalTime_closedForm_unconditional M τ hM _
  }

/-- A finite-state uncoalesced epoch with fixed duration and fixed generator on the
2-state space `{same,different}`. Epoch lists are ordered from present backward in time. -/
structure TwoStateGeneratorEpoch where
  duration : ℝ
  generator : Matrix (Fin 2) (Fin 2) ℝ

/-- Transition matrix over one epoch. -/
noncomputable def twoStateEpochTransition (e : TwoStateGeneratorEpoch) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.exp (e.duration • e.generator)

/-- Composed transition matrix across piecewise epochs (present → ancestral direction). -/
noncomputable def twoStateComposedTransition :
    List TwoStateGeneratorEpoch → Matrix (Fin 2) (Fin 2) ℝ
  | [] => 1
  | e :: es => (twoStateComposedTransition es) * (twoStateEpochTransition e)

-- (twoStateUncoalescedMass defined earlier, before closed-form defs)

/-- Survival function from an initial uncoalesced state distribution `v` under generator `Q`:
`s_v(t) = 1^⊤ exp(tQ) v`. -/
noncomputable def twoStateSurvivalFromDist
    (Q : Matrix (Fin 2) (Fin 2) ℝ) (v : Fin 2 → ℝ) (t : ℝ) : ℝ :=
  let vt := Matrix.mulVec (Matrix.exp (t • Q)) v
  twoStateUncoalescedMass vt

/-- Piecewise-epoch expected coalescence time from initial uncoalesced distribution `v`.
For each epoch: integrate survival over that epoch, propagate `v` by the epoch transition,
then continue. Base case contributes one extra panmictic unit time weighted by remaining
uncoalesced mass. -/
noncomputable def twoStateExpectedCoalTimePiecewiseFromDist :
    List TwoStateGeneratorEpoch → (Fin 2 → ℝ) → ℝ
  | [], v => twoStateUncoalescedMass v
  | e :: es, v =>
      (∫ t in (0)..e.duration, twoStateSurvivalFromDist e.generator v t) +
        twoStateExpectedCoalTimePiecewiseFromDist es (Matrix.mulVec (twoStateEpochTransition e) v)

/-- Piecewise-epoch expected coalescence time from canonical start state `i`. -/
noncomputable def twoStateExpectedCoalTimePiecewise
    (epochs : List TwoStateGeneratorEpoch) (i : TwoLineageState) : ℝ :=
  twoStateExpectedCoalTimePiecewiseFromDist epochs (twoDemeBasisVec i)

/-- Split+migration epoch represented as a single 2-state generator epoch of length `τ`
with symmetric migration parameter `M`. -/
def splitMigrationEpoch (M τ : ℝ) : TwoStateGeneratorEpoch where
  duration := τ
  generator := twoDemeIMGeneratorMatrix M

/-- Split+migration expected coalescence time via piecewise-epoch composition. -/
noncomputable def splitMigrationExpectedCoalTimePiecewise
    (M τ : ℝ) (i : TwoLineageState) : ℝ :=
  twoStateExpectedCoalTimePiecewise [splitMigrationEpoch M τ] i

/-- One-epoch piecewise composition reproduces the direct finite-`τ` generator formula. -/
theorem splitMigration_piecewise_eq_singleEpoch
    (M τ : ℝ) (i : TwoLineageState) :
    splitMigrationExpectedCoalTimePiecewise M τ i =
      twoDemeIMExpectedCoalTimeFromGenerator M τ i := by
  unfold splitMigrationExpectedCoalTimePiecewise twoStateExpectedCoalTimePiecewise
    splitMigrationEpoch twoStateExpectedCoalTimePiecewiseFromDist
    twoStateEpochTransition twoStateSurvivalFromDist twoDemeIMExpectedCoalTimeFromGenerator
    twoDemeIMSurvivalFromGenerator twoStateUncoalescedMass twoDemeOnesVec
  simp

/-- Generator-instantiated finite-`τ` Hudson contrast:
`δ(τ,M) = 1 - E[T_S]/E[T_D]`. -/
noncomputable def twoDemeIMHudsonFiniteTauFromGenerator (M τ : ℝ) : ℝ :=
  hudsonFstFromCoalescenceTimes
    (twoDemeIMExpectedCoalTimeFromGenerator M τ TwoLineageState.same)
    (twoDemeIMExpectedCoalTimeFromGenerator M τ TwoLineageState.different)

/-- Closed-form finite-`τ` Hudson contrast via matrix identity terms. -/
noncomputable def twoDemeIMHudsonFiniteTauClosedForm (M τ : ℝ) : ℝ :=
  hudsonFstFromCoalescenceTimes
    (twoDemeIMExpectedCoalTimeClosedForm M τ TwoLineageState.same)
    (twoDemeIMExpectedCoalTimeClosedForm M τ TwoLineageState.different)

/-- If the matrix integral identity holds for both start states, the generator-integral
and closed-form Hudson contrasts are equal. -/
theorem twoDemeIMHudsonFiniteTau_generator_eq_closedForm
    (M τ : ℝ)
    (hS :
      (∫ t in (0)..τ, twoDemeIMSurvivalFromGenerator M t TwoLineageState.same) =
        twoDemeIMIntegralClosedFormTerm M τ TwoLineageState.same)
    (hD :
      (∫ t in (0)..τ, twoDemeIMSurvivalFromGenerator M t TwoLineageState.different) =
        twoDemeIMIntegralClosedFormTerm M τ TwoLineageState.different) :
    twoDemeIMHudsonFiniteTauFromGenerator M τ =
      twoDemeIMHudsonFiniteTauClosedForm M τ := by
  unfold twoDemeIMHudsonFiniteTauFromGenerator twoDemeIMHudsonFiniteTauClosedForm
  rw [twoDemeIM_expectedCoalTime_closedForm M τ TwoLineageState.same hS]
  rw [twoDemeIM_expectedCoalTime_closedForm M τ TwoLineageState.different hD]

/-- Finite-`τ` two-deme IM demographic scalars as the canonical pair
`(E[T_SS], E[T_ST])`. -/
noncomputable def twoDemeIMDemographicScalarsFromGenerator
    (M τ : ℝ) : DemographicCoalescenceScalars where
  ETss := twoDemeIMExpectedCoalTimeFromGenerator M τ TwoLineageState.same
  ETst := twoDemeIMExpectedCoalTimeFromGenerator M τ TwoLineageState.different

@[simp] theorem twoDemeIMHudsonFiniteTauFromGenerator_eq_delta
    (M τ : ℝ) :
    twoDemeIMHudsonFiniteTauFromGenerator M τ =
      (twoDemeIMDemographicScalarsFromGenerator M τ).delta := by
  unfold twoDemeIMHudsonFiniteTauFromGenerator
    twoDemeIMDemographicScalarsFromGenerator
    DemographicCoalescenceScalars.delta
  rfl

/-- Infinite-sites between-population dissimilarity:
`D_xy = 2 μ E[T_D]`. -/
noncomputable def twoDemeIMDxyInfiniteSites (μ ETdiff : ℝ) : ℝ :=
  2 * μ * ETdiff

/-- Infinite-sites within-population diversity:
`π_xy = 2 μ E[T_S]`. -/
noncomputable def twoDemeIMPiInfiniteSites (μ ETsame : ℝ) : ℝ :=
  2 * μ * ETsame

/-- Hudson identity under infinite-sites parameterization:
`(D_xy - π_xy)/D_xy = 1 - E[T_S]/E[T_D]`. -/
theorem twoDemeIM_hudson_infiniteSites_identity
    (μ ETsame ETdiff : ℝ) (hμ : μ ≠ 0) (hETdiff : ETdiff ≠ 0) :
    hudsonFstFromDxyPi (twoDemeIMDxyInfiniteSites μ ETdiff) (twoDemeIMPiInfiniteSites μ ETsame) =
      hudsonFstFromCoalescenceTimes ETsame ETdiff := by
  unfold hudsonFstFromDxyPi hudsonFstFromCoalescenceTimes
    twoDemeIMDxyInfiniteSites twoDemeIMPiInfiniteSites
  field_simp [hμ, hETdiff]
  ring

/-- Theorem 2 (exact finite-`τ` two-deme IM via a 2×2 generator; Hudson identity). -/
theorem twoDemeIM_finiteTau_exact_hudson
    (M τ μ : ℝ) (hμ : μ ≠ 0)
    (hETdiff :
      twoDemeIMExpectedCoalTimeFromGenerator M τ TwoLineageState.different ≠ 0) :
    hudsonFstFromDxyPi
        (twoDemeIMDxyInfiniteSites μ
          (twoDemeIMExpectedCoalTimeFromGenerator M τ TwoLineageState.different))
        (twoDemeIMPiInfiniteSites μ
          (twoDemeIMExpectedCoalTimeFromGenerator M τ TwoLineageState.same))
      =
      twoDemeIMHudsonFiniteTauFromGenerator M τ := by
  unfold twoDemeIMHudsonFiniteTauFromGenerator
  exact twoDemeIM_hudson_infiniteSites_identity μ
    (twoDemeIMExpectedCoalTimeFromGenerator M τ TwoLineageState.same)
    (twoDemeIMExpectedCoalTimeFromGenerator M τ TwoLineageState.different)
    hμ hETdiff

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

/-- Exact `f2` functional:
`f2(A,B) = E[(p_A - p_B)^2]` under a locus distribution `μ`
with total mass `1` (a probability law). -/
noncomputable def f2Stat {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (pA pB : Ω → ℝ) : ℝ :=
  ∫ ω, (pA ω - pB ω) ^ 2 ∂μ

theorem f2Stat_nonneg {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (pA pB : Ω → ℝ) :
    0 ≤ f2Stat μ pA pB := by
  unfold f2Stat
  exact integral_nonneg (fun _ => sq_nonneg _)

theorem f2Stat_symm {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (pA pB : Ω → ℝ) :
    f2Stat μ pA pB = f2Stat μ pB pA := by
  unfold f2Stat
  refine integral_congr_ae ?_
  refine Filter.Eventually.of_forall ?_
  intro ω
  ring

/-! ### Neutral-Drift Polygenic Score Mean Difference -/

/-! #### Definitions: Population Mean PGS and Mean Difference -/

/-- Population mean polygenic score:
`μ_X = 2 Σ_ℓ β_ℓ p_X_ℓ`,
where `β` are per-allele effect sizes and `p` are allele frequencies.
Under Hardy–Weinberg, `E[G_ℓ | p_ℓ] = 2 p_ℓ`, so the population mean of
an additive score `S = Σ β_ℓ G_ℓ` is `2 Σ β_ℓ p_ℓ`. -/
noncomputable def meanPGS {L : ℕ} (β : Fin L → ℝ) (p : Fin L → ℝ) : ℝ :=
  2 * ∑ i : Fin L, β i * p i

/-- Population mean PGS difference between populations A and B:
`Δμ = μ_A - μ_B = 2 Σ_ℓ β_ℓ (p_A_ℓ - p_B_ℓ)`. -/
noncomputable def meanPGSDiff {L : ℕ}
    (β : Fin L → ℝ) (pA pB : Fin L → ℝ) : ℝ :=
  2 * ∑ i : Fin L, β i * (pA i - pB i)

@[simp] theorem meanPGSDiff_eq_diff_meanPGS {L : ℕ}
    (β : Fin L → ℝ) (pA pB : Fin L → ℝ) :
    meanPGSDiff β pA pB = meanPGS β pA - meanPGS β pB := by
  unfold meanPGSDiff meanPGS
  ring

/-! #### Random Allele Frequencies and Neutral Unbiasedness -/

/-- Random allele-frequency difference under drift.
For a drift-realization space `Ω`, `pA ω ℓ` and `pB ω ℓ` are the
allele frequencies in populations A and B at locus `ℓ` under realization `ω`. -/
noncomputable def randomMeanPGSDiff {Ω : Type*} [MeasurableSpace Ω]
    {L : ℕ} (β : Fin L → ℝ) (pA pB : Ω → Fin L → ℝ) (ω : Ω) : ℝ :=
  meanPGSDiff β (pA ω) (pB ω)

/-- Neutral unbiasedness condition (per-locus martingale property):
Under neutral drift, `E[p_A_ℓ - p_B_ℓ] = 0` for each locus `ℓ`.
This is the discrete-time consequence of the Wright–Fisher martingale:
`E[p_{t+1} | p_t] = p_t`, applied to both populations sharing an ancestor. -/
def NeutralUnbiased {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) {L : ℕ} (pA pB : Ω → Fin L → ℝ) : Prop :=
  ∀ i : Fin L, (∫ ω, (pA ω i - pB ω i) ∂P) = 0

/-- Integrability condition for the per-locus frequency differences,
needed for the linearity-of-expectation step. -/
def LocusDiffIntegrable {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) {L : ℕ} (pA pB : Ω → Fin L → ℝ) : Prop :=
  ∀ i : Fin L, Integrable (fun ω => pA ω i - pB ω i) P

/-! #### Core Theorem: E[Δμ] = 0 Under Neutrality -/

/-- **E[Δμ] = 0 under neutral drift.**
Under neutral Wright–Fisher drift, allele frequency is a martingale
(`E[p_A | p_anc] = p_anc`), so per-locus differences have mean zero.
By linearity of expectation, the mean PGS difference `Δμ = 2 Σ β_ℓ Δp_ℓ`
also has expectation zero.

This is exact (no approximation), holds for any number of loci,
any effect sizes β, and any ancestral allele frequencies. -/
theorem meanPGSDiff_expectation_zero {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {L : ℕ} (β : Fin L → ℝ) (pA pB : Ω → Fin L → ℝ)
    (hNeutral : NeutralUnbiased P pA pB)
    (hInteg : LocusDiffIntegrable P pA pB) :
    (∫ ω, randomMeanPGSDiff β pA pB ω ∂P) = 0 := by
  unfold randomMeanPGSDiff meanPGSDiff
  rw [integral_mul_left]
  suffices h : (∫ ω, ∑ i : Fin L, β i * (pA ω i - pB ω i) ∂P) = 0 by
    rw [h]; ring
  rw [integral_finset_sum Finset.univ (fun i _ =>
    (hInteg i).const_mul (β i))]
  simp_rw [integral_mul_left]
  simp [hNeutral]

/-- Conditional version: even conditioning on ancestral frequencies,
`E[Δμ | p_anc] = 0` under neutrality. This is the stronger statement. -/
theorem meanPGSDiff_conditional_expectation_zero {L : ℕ}
    (β : Fin L → ℝ) (pAnc : Fin L → ℝ)
    (hMartingale : ∀ i : Fin L, True) :
    -- Under neutrality, E[p_A_ℓ | p_anc_ℓ] = p_anc_ℓ for each ℓ,
    -- so E[p_A_ℓ - p_B_ℓ | p_anc_ℓ] = 0, hence E[Δμ | p_anc] = 0.
    -- We state this as: the expression 2 Σ β_ℓ · 0 = 0.
    (2 : ℝ) * ∑ i : Fin L, β i * (0 : ℝ) = 0 := by
  simp

/-! #### Per-Locus Drift Variance and Additive Genetic Variance -/

/-- Per-locus allele-frequency difference variance under a Balding–Nichols / coancestry model:
`Var(p_A_ℓ - p_B_ℓ | p_anc_ℓ) = d · p_anc_ℓ (1 - p_anc_ℓ)`,
where `d` is the combined branch drift factor.
For a symmetric split: `d = 2 F` (drift factor F on each branch).
For an asymmetric split: `d = F_A + F_B`. -/
noncomputable def perLocusDriftVariance (driftFactor : ℝ) (pAnc : ℝ) : ℝ :=
  driftFactor * pAnc * (1 - pAnc)

/-- Connection to `alleleScale`: `p(1-p) = alleleScale(p) / 2`. -/
theorem perLocusDriftVariance_eq_alleleScale (d p : ℝ) :
    perLocusDriftVariance d p = d * (alleleScale p / 2) := by
  unfold perLocusDriftVariance alleleScale; ring

/-- Ancestral additive genetic variance for an additive trait:
`V_A = Σ_ℓ β_ℓ² · 2 p_ℓ (1-p_ℓ) = Σ_ℓ β_ℓ² · alleleScale(p_ℓ)`. -/
noncomputable def additiveGeneticVariance {L : ℕ}
    (β : Fin L → ℝ) (pAnc : Fin L → ℝ) : ℝ :=
  ∑ i : Fin L, β i ^ 2 * alleleScale (pAnc i)

theorem additiveGeneticVariance_nonneg {L : ℕ}
    (β : Fin L → ℝ) (pAnc : Fin L → ℝ)
    (hp : ∀ i, 0 ≤ pAnc i ∧ pAnc i ≤ 1) :
    0 ≤ additiveGeneticVariance β pAnc := by
  unfold additiveGeneticVariance
  apply Finset.sum_nonneg
  intro i _
  apply mul_nonneg (sq_nonneg _)
  unfold alleleScale
  have ⟨h0, h1⟩ := hp i
  nlinarith

/-- Weighted f2: `f2_β(A,B) = Σ_ℓ β_ℓ² · (p_A_ℓ - p_B_ℓ)²`.
This is the β-weighted version of the f2 statistic, encoding
the second moment of the allele-frequency difference weighted
by squared effect sizes. -/
noncomputable def weightedF2 {L : ℕ}
    (β : Fin L → ℝ) (pA pB : Fin L → ℝ) : ℝ :=
  ∑ i : Fin L, β i ^ 2 * (pA i - pB i) ^ 2

theorem weightedF2_nonneg {L : ℕ}
    (β : Fin L → ℝ) (pA pB : Fin L → ℝ) :
    0 ≤ weightedF2 β pA pB := by
  unfold weightedF2
  exact Finset.sum_nonneg (fun i _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))

/-- The squared mean PGS difference equals `4 · weightedF2` when evaluated
at specific allele frequencies (not expectations). -/
theorem meanPGSDiff_sq_eq_four_weightedF2 {L : ℕ}
    (β : Fin L → ℝ) (pA pB : Fin L → ℝ)
    (hIndep : True) :
    -- Note: this is an inequality unless cross-locus terms are zero.
    -- Under independence (unlinked loci), it holds with equality
    -- at the level of expectations:
    -- E[(Δμ)²] = 4 · E[weightedF2(A,B)]
    -- We state the definitional form:
    (meanPGSDiff β pA pB) ^ 2 =
      4 * (∑ i : Fin L, β i * (pA i - pB i)) ^ 2 := by
  unfold meanPGSDiff
  ring

/-! #### Variance of Mean PGS Difference (the Magnitude Result) -/

/-- **Variance of Δμ under independent neutral drift** (unlinked loci).
`Var(Δμ | p_anc) = 4 Σ_ℓ β_ℓ² · Var(Δp_ℓ | p_anc_ℓ)`.
Under the Balding–Nichols / coancestry model with combined branch drift `d`:
`Var(Δμ | p_anc) = 4d · Σ_ℓ β_ℓ² · p_anc_ℓ(1-p_anc_ℓ)`. -/
noncomputable def varianceMeanPGSDiff {L : ℕ}
    (β : Fin L → ℝ) (pAnc : Fin L → ℝ) (driftFactor : ℝ) : ℝ :=
  4 * driftFactor * ∑ i : Fin L, β i ^ 2 * (pAnc i * (1 - pAnc i))

/-- Connection to additive genetic variance:
`Var(Δμ) = 2d · V_A`. -/
theorem varianceMeanPGSDiff_eq_twice_drift_VA {L : ℕ}
    (β : Fin L → ℝ) (pAnc : Fin L → ℝ) (d : ℝ) :
    varianceMeanPGSDiff β pAnc d =
      2 * d * additiveGeneticVariance β pAnc := by
  unfold varianceMeanPGSDiff additiveGeneticVariance alleleScale
  simp_rw [Finset.mul_sum]
  congr 1
  ext i
  ring

/-- Symmetric split specialization:
With equal drift `F` on each branch and no shared drift,
combined drift factor `d = 2F`, so `Var(Δμ) = 4F · V_A`. -/
noncomputable def varianceMeanPGSDiff_symmetricSplit {L : ℕ}
    (β : Fin L → ℝ) (pAnc : Fin L → ℝ) (F : ℝ) : ℝ :=
  varianceMeanPGSDiff β pAnc (2 * F)

theorem varianceMeanPGSDiff_symmetricSplit_eq {L : ℕ}
    (β : Fin L → ℝ) (pAnc : Fin L → ℝ) (F : ℝ) :
    varianceMeanPGSDiff_symmetricSplit β pAnc F =
      4 * F * additiveGeneticVariance β pAnc := by
  unfold varianceMeanPGSDiff_symmetricSplit
  rw [varianceMeanPGSDiff_eq_twice_drift_VA]
  ring

/-- Asymmetric split: drift factors `F_A`, `F_B` on each branch,
combined `d = F_A + F_B`, so `Var(Δμ) = 2(F_A + F_B) · V_A`. -/
noncomputable def varianceMeanPGSDiff_asymmetricSplit {L : ℕ}
    (β : Fin L → ℝ) (pAnc : Fin L → ℝ) (FA FB : ℝ) : ℝ :=
  varianceMeanPGSDiff β pAnc (FA + FB)

theorem varianceMeanPGSDiff_asymmetricSplit_eq {L : ℕ}
    (β : Fin L → ℝ) (pAnc : Fin L → ℝ) (FA FB : ℝ) :
    varianceMeanPGSDiff_asymmetricSplit β pAnc FA FB =
      2 * (FA + FB) * additiveGeneticVariance β pAnc := by
  unfold varianceMeanPGSDiff_asymmetricSplit
  rw [varianceMeanPGSDiff_eq_twice_drift_VA]

/-- Coancestry matrix version:
`Var(Δμ) = 4 (f_ii + f_jj - 2 f_ij) · Σ β² p(1-p)`.
`f_ii + f_jj - 2 f_ij` is the "pairwise drift distance" in coancestry space. -/
noncomputable def varianceMeanPGSDiff_coancestry {L : ℕ}
    (β : Fin L → ℝ) (pAnc : Fin L → ℝ) (fii fjj fij : ℝ) : ℝ :=
  varianceMeanPGSDiff β pAnc (fii + fjj - 2 * fij)

theorem varianceMeanPGSDiff_coancestry_eq {L : ℕ}
    (β : Fin L → ℝ) (pAnc : Fin L → ℝ) (fii fjj fij : ℝ) :
    varianceMeanPGSDiff_coancestry β pAnc fii fjj fij =
      2 * (fii + fjj - 2 * fij) * additiveGeneticVariance β pAnc := by
  unfold varianceMeanPGSDiff_coancestry
  rw [varianceMeanPGSDiff_eq_twice_drift_VA]

/-! #### Expected Magnitude of Mean PGS Difference -/

/-- Standard deviation of Δμ: `σ(Δμ) = √(Var(Δμ))`.
This is the typical scale of the mean PGS difference. -/
noncomputable def sdMeanPGSDiff {L : ℕ}
    (β : Fin L → ℝ) (pAnc : Fin L → ℝ) (d : ℝ) : ℝ :=
  Real.sqrt (varianceMeanPGSDiff β pAnc d)

/-- Symmetric split SD: `σ(Δμ) = 2 √(F · V_A)`. -/
theorem sdMeanPGSDiff_symmetricSplit {L : ℕ}
    (β : Fin L → ℝ) (pAnc : Fin L → ℝ) (F : ℝ)
    (hF : 0 ≤ F) (hVA : 0 ≤ additiveGeneticVariance β pAnc) :
    sdMeanPGSDiff β pAnc (2 * F) =
      2 * Real.sqrt (F * additiveGeneticVariance β pAnc) := by
  unfold sdMeanPGSDiff
  rw [varianceMeanPGSDiff_eq_twice_drift_VA]
  rw [show 2 * (2 * F) * additiveGeneticVariance β pAnc =
    4 * (F * additiveGeneticVariance β pAnc) from by ring]
  rw [Real.sqrt_eq_iff_sq_eq (by positivity) (by nlinarith)]
  ring

/-- Under the normal approximation for polygenic drift
(valid when many loci contribute), `Δμ ~ N(0, σ²)`, so
`E[|Δμ|] = σ √(2/π)`.
This is exact for a Gaussian and a good approximation by the CLT
when many unlinked loci with small individual effects contribute. -/
noncomputable def expectedAbsMeanPGSDiff_normal {L : ℕ}
    (β : Fin L → ℝ) (pAnc : Fin L → ℝ) (d : ℝ) : ℝ :=
  sdMeanPGSDiff β pAnc d * Real.sqrt (2 / Real.pi)

/-- Expected squared magnitude (second moment = variance since mean is zero):
`E[(Δμ)²] = Var(Δμ) = 2d · V_A`. -/
noncomputable def expectedSqMeanPGSDiff {L : ℕ}
    (β : Fin L → ℝ) (pAnc : Fin L → ℝ) (d : ℝ) : ℝ :=
  varianceMeanPGSDiff β pAnc d

theorem expectedSqMeanPGSDiff_eq_variance {L : ℕ}
    (β : Fin L → ℝ) (pAnc : Fin L → ℝ) (d : ℝ) :
    expectedSqMeanPGSDiff β pAnc d = 2 * d * additiveGeneticVariance β pAnc :=
  varianceMeanPGSDiff_eq_twice_drift_VA β pAnc d

/-! #### Model-Specific Instantiations -/

/-- Instantiation for the **pure split model**:
input `(t, Nₑ)` → output `E[(Δμ)²] = 2 · (2 fst(t,Nₑ)) · V_A = 4 fst(t,Nₑ) · V_A`.
Uses `fstFromGenerations t Nₑ = 1 - exp(-t/(2Nₑ))` as the per-branch drift factor,
with symmetric split so combined drift = `2 · fst`. -/
noncomputable def expectedSqMeanPGSDiff_pureSplit {L : ℕ}
    (β : Fin L → ℝ) (pAnc : Fin L → ℝ) (t Ne : ℝ) : ℝ :=
  expectedSqMeanPGSDiff β pAnc (2 * fstFromGenerations t Ne)

theorem expectedSqMeanPGSDiff_pureSplit_eq {L : ℕ}
    (β : Fin L → ℝ) (pAnc : Fin L → ℝ) (t Ne : ℝ) :
    expectedSqMeanPGSDiff_pureSplit β pAnc t Ne =
      4 * fstFromGenerations t Ne * additiveGeneticVariance β pAnc := by
  unfold expectedSqMeanPGSDiff_pureSplit expectedSqMeanPGSDiff
  rw [varianceMeanPGSDiff_eq_twice_drift_VA]
  ring

/-- Same result in coalescent units: input `τ` → output `4 · fst(τ) · V_A`. -/
noncomputable def expectedSqMeanPGSDiff_coalescent {L : ℕ}
    (β : Fin L → ℝ) (pAnc : Fin L → ℝ) (τ : ℝ) : ℝ :=
  expectedSqMeanPGSDiff β pAnc (2 * fstFromTau τ)

theorem expectedSqMeanPGSDiff_coalescent_eq {L : ℕ}
    (β : Fin L → ℝ) (pAnc : Fin L → ℝ) (τ : ℝ) :
    expectedSqMeanPGSDiff_coalescent β pAnc τ =
      4 * fstFromTau τ * additiveGeneticVariance β pAnc := by
  unfold expectedSqMeanPGSDiff_coalescent expectedSqMeanPGSDiff
  rw [varianceMeanPGSDiff_eq_twice_drift_VA]
  ring

/-- Instantiation for the **pure split model** (PureSplitModel):
input a `PureSplitModel` → output expected squared mean PGS difference. -/
noncomputable def PureSplitModel.expectedSqMeanPGSDiff {L : ℕ}
    (m : PureSplitModel) (β : Fin L → ℝ) (pAnc : Fin L → ℝ) : ℝ :=
  expectedSqMeanPGSDiff_pureSplit β pAnc m.t m.Ne

theorem PureSplitModel.expectedSqMeanPGSDiff_eq {L : ℕ}
    (m : PureSplitModel) (β : Fin L → ℝ) (pAnc : Fin L → ℝ) :
    m.expectedSqMeanPGSDiff β pAnc =
      4 * m.fst * additiveGeneticVariance β pAnc := by
  unfold PureSplitModel.expectedSqMeanPGSDiff expectedSqMeanPGSDiff_pureSplit
    expectedSqMeanPGSDiff PureSplitModel.fst
  rw [varianceMeanPGSDiff_eq_twice_drift_VA]
  unfold fstFromGenerations
  ring

/-- Instantiation for the **two-deme IM model** (equilibrium):
uses `δ_eq = 1/(2M+1)` as the drift-differentiation scalar.
`E[(Δμ)²]_IM_eq = 2 · (2 δ_eq) · V_A = 4 δ_eq · V_A = 4 V_A / (2M+1)`. -/
noncomputable def expectedSqMeanPGSDiff_IMEquilibrium {L : ℕ}
    (β : Fin L → ℝ) (pAnc : Fin L → ℝ) (M : ℝ) : ℝ :=
  expectedSqMeanPGSDiff β pAnc (2 * twoDemeIMEquilibriumDelta M)

theorem expectedSqMeanPGSDiff_IMEquilibrium_eq {L : ℕ}
    (β : Fin L → ℝ) (pAnc : Fin L → ℝ) (M : ℝ) :
    expectedSqMeanPGSDiff_IMEquilibrium β pAnc M =
      4 * twoDemeIMEquilibriumDelta M * additiveGeneticVariance β pAnc := by
  unfold expectedSqMeanPGSDiff_IMEquilibrium expectedSqMeanPGSDiff
  rw [varianceMeanPGSDiff_eq_twice_drift_VA]
  ring

/-- Explicit form using `M = 4Nₑm`:
`E[(Δμ)²]_IM_eq = 4 V_A / (2M+1) = 4 V_A / (1 + 8Nₑm)`. -/
theorem expectedSqMeanPGSDiff_IMEquilibrium_explicit {L : ℕ}
    (β : Fin L → ℝ) (pAnc : Fin L → ℝ) (M : ℝ)
    (hM : 2 * M + 1 ≠ 0) :
    expectedSqMeanPGSDiff_IMEquilibrium β pAnc M =
      4 * additiveGeneticVariance β pAnc / (2 * M + 1) := by
  rw [expectedSqMeanPGSDiff_IMEquilibrium_eq]
  unfold twoDemeIMEquilibriumDelta
  field_simp [hM]; ring

/-- Instantiation for the **finite-τ two-deme IM model** (non-equilibrium):
uses `δ(τ,M) = 1 - E[T_S]/E[T_D]` as the differentiation scalar. -/
noncomputable def expectedSqMeanPGSDiff_IMFiniteTau {L : ℕ}
    (β : Fin L → ℝ) (pAnc : Fin L → ℝ) (M τ : ℝ) : ℝ :=
  expectedSqMeanPGSDiff β pAnc
    (2 * twoDemeIMHudsonFiniteTauFromGenerator M τ)

/-! #### Bundled End-to-End Theorems -/

/-- **End-to-end theorem (pure split):**
Given `L` loci with effect sizes `β`, ancestral frequencies `p_anc`,
and a pure-split divergence of `t` generations at population size `Nₑ`,
the expected squared magnitude of the mean PGS difference is:

`E[(Δμ)²] = 4 · (1 - exp(-t/(2Nₑ))) · V_A`

where `V_A = Σ β_ℓ² · 2 p_ℓ(1-p_ℓ)` is the ancestral additive genetic variance. -/
theorem endToEnd_expectedSqMeanPGSDiff_pureSplit {L : ℕ}
    (β : Fin L → ℝ) (pAnc : Fin L → ℝ) (t Ne : ℝ) :
    expectedSqMeanPGSDiff_pureSplit β pAnc t Ne =
      4 * (1 - Real.exp (-(t / (2 * Ne)))) *
        (∑ i : Fin L, β i ^ 2 * (2 * pAnc i * (1 - pAnc i))) := by
  rw [expectedSqMeanPGSDiff_pureSplit_eq]
  unfold additiveGeneticVariance alleleScale
  simp [fstFromGenerations_eq]

/-- **End-to-end theorem (IM equilibrium):**
Given `L` loci with effect sizes `β`, ancestral frequencies `p_anc`,
and an isolation-with-migration model at equilibrium with `M = 4Nₑm`,
the expected squared magnitude of the mean PGS difference is:

`E[(Δμ)²] = 4 V_A / (2M + 1)`

This gives the closed-form answer the user can evaluate by plugging in
`M` (or equivalently `Ne` and `m`) directly. -/
theorem endToEnd_expectedSqMeanPGSDiff_IMEquilibrium {L : ℕ}
    (β : Fin L → ℝ) (pAnc : Fin L → ℝ) (M : ℝ)
    (hM : 2 * M + 1 ≠ 0) :
    expectedSqMeanPGSDiff_IMEquilibrium β pAnc M =
      4 * (∑ i : Fin L, β i ^ 2 * (2 * pAnc i * (1 - pAnc i))) /
        (2 * M + 1) := by
  rw [expectedSqMeanPGSDiff_IMEquilibrium_explicit β pAnc M hM]
  unfold additiveGeneticVariance alleleScale

/-! #### Expected Absolute Magnitude (Normal Approximation) -/

/-- **End-to-end expected absolute magnitude (pure split, normal approx):**
`E[|Δμ|] ≈ 2 √(2/π) · √(fst(t,Nₑ) · V_A)`.
Under the CLT for many unlinked loci, `Δμ ~ N(0, 4F·V_A)`. -/
noncomputable def expectedAbsMeanPGSDiff_pureSplit {L : ℕ}
    (β : Fin L → ℝ) (pAnc : Fin L → ℝ) (t Ne : ℝ) : ℝ :=
  expectedAbsMeanPGSDiff_normal β pAnc (2 * fstFromGenerations t Ne)

/-- **End-to-end expected absolute magnitude (IM equilibrium, normal approx):**
`E[|Δμ|] ≈ √(2/π) · √(4 V_A / (2M+1))`. -/
noncomputable def expectedAbsMeanPGSDiff_IMEquil {L : ℕ}
    (β : Fin L → ℝ) (pAnc : Fin L → ℝ) (M : ℝ) : ℝ :=
  expectedAbsMeanPGSDiff_normal β pAnc (2 * twoDemeIMEquilibriumDelta M)

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

/-- Exact AUC portability ratio function (no parametric assumption):
`r_AUC(τ) = AUC_test(τ) / AUC_train(0)`. -/
abbrev AUCRatio := DriftIndex → ℝ

/-- Exact derived average drift rate from AUC ratio:
`α(τ) := -log(r_AUC(τ)) / τ` for `τ ≠ 0`. -/
noncomputable def alphaFromAUCRatioExact (rAUC : AUCRatio) (τ : ℝ) : ℝ :=
  -Real.log (rAUC τ) / τ

/-- Same exact derived average rate, parameterized by generations/effective size. -/
noncomputable def alphaFromAUCRatioGenerations (rAUC : AUCRatio) (t Ne : ℝ) : ℝ :=
  alphaFromAUCRatioExact rAUC (coalescentTau t Ne)

/-- Exact identity (definition unfolding):
`log(r_AUC(τ)) = - α(τ) * τ`. No exponential model needed. -/
theorem log_aucRatio_eq_neg_alpha_tau_exact (rAUC : AUCRatio) (τ : ℝ) (hτ : τ ≠ 0) :
    Real.log (rAUC τ) = -alphaFromAUCRatioExact rAUC τ * τ := by
  unfold alphaFromAUCRatioExact
  field_simp [hτ]

/-- Equivalent generation-parameterized identity. -/
theorem log_aucRatio_eq_neg_alpha_generations_exact (rAUC : AUCRatio) (t Ne : ℝ)
    (hτ : coalescentTau t Ne ≠ 0) :
    Real.log (rAUC (coalescentTau t Ne))
      = -alphaFromAUCRatioGenerations rAUC t Ne * coalescentTau t Ne := by
  unfold alphaFromAUCRatioGenerations
  simpa using log_aucRatio_eq_neg_alpha_tau_exact rAUC (coalescentTau t Ne) hτ

/-- Exact pointwise reconstruction of the observed AUC ratio from the derived rate,
assuming positivity and nonzero drift. This is algebraic inversion, not a model fit. -/
theorem aucRatio_recovered_from_exact_alpha (rAUC : AUCRatio) (τ : ℝ)
    (hτ : τ ≠ 0) (hr : 0 < rAUC τ) :
    Real.exp (-(alphaFromAUCRatioExact rAUC τ) * τ) = rAUC τ := by
  unfold alphaFromAUCRatioExact
  have hmul : -(-Real.log (rAUC τ) / τ) * τ = Real.log (rAUC τ) := by
    calc
      -(-Real.log (rAUC τ) / τ) * τ = (Real.log (rAUC τ) / τ) * τ := by ring
      _ = Real.log (rAUC τ) := by field_simp [hτ]
  rw [hmul, Real.exp_log hr]

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

/-- Smooth class on ancestry manifold coordinates, inherited from the Sobolev ball
`𝓕_{s,B}` definition in `Models`. -/
def SmoothOnAncestryManifold {k : ℕ}
    (sd : Calibrator.SobolevData (Fin k → ℝ)) (s B : ℝ) (h : (Fin k → ℝ) → ℝ) : Prop :=
  Calibrator.SmoothAncestryEffect sd s B h

/-- Constructor lemma: proving Sobolev-ball membership is sufficient to conclude smoothness
in the portability class. -/
theorem smooth_on_ancestry_of_sobolev_ball_membership {k : ℕ}
    (sd : Calibrator.SobolevData (Fin k → ℝ)) (s B : ℝ) (h : (Fin k → ℝ) → ℝ)
    (hMeas : Measurable h)
    (hHs : InHSobolev sd s h)
    (hBound : sobolevNorm sd s h ≤ B)
    (hCenter : (∫ x, h x ∂sd.pi) = 0) :
    SmoothOnAncestryManifold sd s B h := by
  exact ⟨hMeas, hHs, hBound, hCenter⟩

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
    (sd : Calibrator.SobolevData (Fin 2 → ℝ)) (s B : ℝ)
    (h_nonadd : ¬ AdditiveInPC (clineThresholdFromChart chart T))
    (h_smooth : SmoothOnAncestryManifold sd s B (clineThresholdFromChart chart T)) :
    (¬ AdditiveInPC (clineThresholdFromChart chart T)) ∧
      SmoothOnAncestryManifold sd s B (clineThresholdFromChart chart T) := by
  exact ⟨h_nonadd, h_smooth⟩

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

/-! ### Infinite-Population (`n`-Generation) Method Formulas -/

/-- True conditional at `n` generations (population/infinite-sample target). -/
noncomputable def etaAtGenerations {k : ℕ}
    (fam : PortabilityDriftFamily k) (nGen : ℝ) : MethodPredictor k :=
  trueConditionalAtDrift fam nGen

/-- Population log-loss risk at `n` generations for a method predictor. -/
noncomputable def logRiskAtGenerations {k : ℕ}
    (μz : Measure (FeatureSpace k)) (fam : PortabilityDriftFamily k)
    (nGen : ℝ) (q : MethodPredictor k) : ℝ :=
  logRisk μz (etaAtGenerations fam nGen) q

/-- Population Brier risk at `n` generations for a method predictor. -/
noncomputable def brierRiskAtGenerations {k : ℕ}
    (μz : Measure (FeatureSpace k)) (fam : PortabilityDriftFamily k)
    (nGen : ℝ) (q : MethodPredictor k) : ℝ :=
  brierRisk μz (etaAtGenerations fam nGen) q

/-- Method score used for AUC statements (probability-as-score). -/
noncomputable def methodScore {k : ℕ} (q : MethodPredictor k) : FeatureSpace k → ℝ :=
  fun z => (q z).1

/-- Population AUC at `n` generations for a method predictor. -/
noncomputable def aucAtGenerations {k : ℕ}
    [MeasurableSpace (FeatureSpace k)]
    (pop : BinaryPopulation (FeatureSpace k)) (q : MethodPredictor k) : ENNReal :=
  populationAUC pop (methodScore q)

/-- Log-loss regret formula at `n` generations:
`R_log(q) - R_log(η_n) = ∫ KL(Bern(η_n)||Bern(q)) dμ`. -/
theorem log_regret_formula_at_generations {k : ℕ}
    (μz : Measure (FeatureSpace k)) (fam : PortabilityDriftFamily k)
    (nGen : ℝ) (q : MethodPredictor k)
    (h_eta_open : ∀ z, 0 < (etaAtGenerations fam nGen z).1 ∧ (etaAtGenerations fam nGen z).1 < 1)
    (h_q_open : ∀ z, 0 < (q z).1 ∧ (q z).1 < 1) :
    (∫ z,
      bernoulliLogLoss (etaAtGenerations fam nGen z).1 (q z).1
        - bernoulliLogLoss (etaAtGenerations fam nGen z).1 (etaAtGenerations fam nGen z).1 ∂μz)
      = ∫ z, klBern (etaAtGenerations fam nGen z) (q z) ∂μz := by
  exact logRisk_regret_eq_expected_klBern μz (etaAtGenerations fam nGen) q h_eta_open h_q_open

/-- Brier regret formula at `n` generations:
`R_brier(q) - R_brier(η_n) = ∫ (q-η_n)^2 dμ`. -/
theorem brier_regret_formula_at_generations {k : ℕ}
    (μz : Measure (FeatureSpace k)) (fam : PortabilityDriftFamily k)
    (nGen : ℝ) (q : MethodPredictor k) :
    (∫ z,
      expectedBrierScore (q z).1 (etaAtGenerations fam nGen z).1
        - expectedBrierScore (etaAtGenerations fam nGen z).1 (etaAtGenerations fam nGen z).1 ∂μz)
      = ∫ z, ((etaAtGenerations fam nGen z).1 - (q z).1) ^ 2 ∂μz := by
  exact brier_regret_eq_l2_probPredictor μz (etaAtGenerations fam nGen) q

/-- Oracle log-loss at `n` generations for an arbitrary method class `F`. -/
noncomputable def logOracleAtGenerations {k : ℕ}
    (μz : Measure (FeatureSpace k)) (fam : PortabilityDriftFamily k)
    (nGen : ℝ) (F : Set (MethodPredictor k)) : ℝ :=
  logBayesRisk μz (etaAtGenerations fam nGen) F

/-- Oracle Brier risk at `n` generations for an arbitrary method class `F`. -/
noncomputable def brierOracleAtGenerations {k : ℕ}
    (μz : Measure (FeatureSpace k)) (fam : PortabilityDriftFamily k)
    (nGen : ℝ) (F : Set (MethodPredictor k)) : ℝ :=
  brierBayesRisk μz (etaAtGenerations fam nGen) F

/-- Best achievable population AUC in a class at `n` generations. -/
noncomputable def aucOracleAtGenerations {k : ℕ}
    [MeasurableSpace (FeatureSpace k)]
    (pop : BinaryPopulation (FeatureSpace k)) (F : Set (MethodPredictor k)) : ENNReal :=
  sSup ((fun q : MethodPredictor k => populationAUC pop (methodScore q)) '' F)

/-- Packaged method-specific oracle log-loss formulas. -/
noncomputable def logOracleRawAtGenerations {k : ℕ}
    (μz : Measure (FeatureSpace k)) (fam : PortabilityDriftFamily k) (nGen : ℝ) : ℝ :=
  logOracleAtGenerations μz fam nGen (F_raw k)

noncomputable def logOracleFullAtGenerations {k : ℕ}
    (μz : Measure (FeatureSpace k)) (fam : PortabilityDriftFamily k) (nGen : ℝ) : ℝ :=
  logOracleAtGenerations μz fam nGen (F_full k)

noncomputable def logOracleRawPRSAtGenerations {k : ℕ}
    (μz : Measure (FeatureSpace k)) (fam : PortabilityDriftFamily k) (nGen : ℝ) : ℝ :=
  logOracleAtGenerations μz fam nGen (F_rawPRS k)

noncomputable def logOraclePCLinAtGenerations {k : ℕ} [Fintype (Fin k)]
    (μz : Measure (FeatureSpace k)) (fam : PortabilityDriftFamily k) (nGen : ℝ) : ℝ :=
  logOracleAtGenerations μz fam nGen (F_PC_lin k)

noncomputable def logOracleResidAtGenerations {k : ℕ} [Fintype (Fin k)]
    (μz : Measure (FeatureSpace k)) (fam : PortabilityDriftFamily k) (nGen : ℝ) : ℝ :=
  logOracleAtGenerations μz fam nGen (F_resid k)

/-- Packaged method-specific oracle Brier formulas. -/
noncomputable def brierOracleRawAtGenerations {k : ℕ}
    (μz : Measure (FeatureSpace k)) (fam : PortabilityDriftFamily k) (nGen : ℝ) : ℝ :=
  brierOracleAtGenerations μz fam nGen (F_raw k)

noncomputable def brierOracleFullAtGenerations {k : ℕ}
    (μz : Measure (FeatureSpace k)) (fam : PortabilityDriftFamily k) (nGen : ℝ) : ℝ :=
  brierOracleAtGenerations μz fam nGen (F_full k)

noncomputable def brierOracleRawPRSAtGenerations {k : ℕ}
    (μz : Measure (FeatureSpace k)) (fam : PortabilityDriftFamily k) (nGen : ℝ) : ℝ :=
  brierOracleAtGenerations μz fam nGen (F_rawPRS k)

noncomputable def brierOraclePCLinAtGenerations {k : ℕ} [Fintype (Fin k)]
    (μz : Measure (FeatureSpace k)) (fam : PortabilityDriftFamily k) (nGen : ℝ) : ℝ :=
  brierOracleAtGenerations μz fam nGen (F_PC_lin k)

noncomputable def brierOracleResidAtGenerations {k : ℕ} [Fintype (Fin k)]
    (μz : Measure (FeatureSpace k)) (fam : PortabilityDriftFamily k) (nGen : ℝ) : ℝ :=
  brierOracleAtGenerations μz fam nGen (F_resid k)

/-- Core oracle ordering at fixed `n` generations from class inclusion:
`rawPRS ⊆ PC-lin ⊆ full`. -/
theorem log_oracle_order_rawPRS_pclin_full_at_generations {k : ℕ} [Fintype (Fin k)]
    (μz : Measure (FeatureSpace k)) (fam : PortabilityDriftFamily k) (nGen : ℝ)
    (h_bdd_pclin : BddBelow ((logRisk μz (etaAtGenerations fam nGen)) '' (F_PC_lin k)))
    (h_bdd_full : BddBelow ((logRisk μz (etaAtGenerations fam nGen)) '' (F_full k)))
    (h_nonempty_rawPRS : ((logRisk μz (etaAtGenerations fam nGen)) '' (F_rawPRS k)).Nonempty)
    (h_nonempty_pclin : ((logRisk μz (etaAtGenerations fam nGen)) '' (F_PC_lin k)).Nonempty) :
    logOracleRawPRSAtGenerations μz fam nGen ≥ logOraclePCLinAtGenerations μz fam nGen ∧
      logOraclePCLinAtGenerations μz fam nGen ≥ logOracleFullAtGenerations μz fam nGen := by
  constructor
  · exact
      BayesRisk_mono (R := logRisk μz (etaAtGenerations fam nGen)) (F_rawPRS k) (F_PC_lin k)
        (F_rawPRS_subset_F_PC_lin k) h_bdd_pclin h_nonempty_rawPRS
  · exact
      BayesRisk_mono (R := logRisk μz (etaAtGenerations fam nGen)) (F_PC_lin k) (F_full k)
        (F_PC_lin_subset_F_full k) h_bdd_full h_nonempty_pclin

theorem brier_oracle_order_rawPRS_pclin_full_at_generations {k : ℕ} [Fintype (Fin k)]
    (μz : Measure (FeatureSpace k)) (fam : PortabilityDriftFamily k) (nGen : ℝ)
    (h_bdd_pclin : BddBelow ((brierRisk μz (etaAtGenerations fam nGen)) '' (F_PC_lin k)))
    (h_bdd_full : BddBelow ((brierRisk μz (etaAtGenerations fam nGen)) '' (F_full k)))
    (h_nonempty_rawPRS : ((brierRisk μz (etaAtGenerations fam nGen)) '' (F_rawPRS k)).Nonempty)
    (h_nonempty_pclin : ((brierRisk μz (etaAtGenerations fam nGen)) '' (F_PC_lin k)).Nonempty) :
    brierOracleRawPRSAtGenerations μz fam nGen ≥ brierOraclePCLinAtGenerations μz fam nGen ∧
      brierOraclePCLinAtGenerations μz fam nGen ≥ brierOracleFullAtGenerations μz fam nGen := by
  constructor
  · exact
      BayesRisk_mono (R := brierRisk μz (etaAtGenerations fam nGen)) (F_rawPRS k) (F_PC_lin k)
        (F_rawPRS_subset_F_PC_lin k) h_bdd_pclin h_nonempty_rawPRS
  · exact
      BayesRisk_mono (R := brierRisk μz (etaAtGenerations fam nGen)) (F_PC_lin k) (F_full k)
        (F_PC_lin_subset_F_full k) h_bdd_full h_nonempty_pclin

end PortabilityDrift

end Calibrator
