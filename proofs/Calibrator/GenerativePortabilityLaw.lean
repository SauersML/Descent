/-
Copyright (c) 2026 Sauers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sauers
-/
import Calibrator.ReversibleMarkovSpectrum
import Calibrator.ObservationalCeiling
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

namespace Calibrator

/-!
# A finite-dimensional Poisson-history law

`SpectralHistory` records signal amplitude, memory magnitude, and spectral phase.  The
closed kernel below is the algebraic expression predicted by the Poisson-kernel inner
product calculation. This module proves the exact quadratic decompositions once that
kernel has been identified; the Fourier integral identity itself remains an analytical
input for a stationary-process application.

The resulting law is useful in population genetics because amplitude (fiber contrast) and
memory/phase (local-ancestry or haplotype persistence) interact through self-energy. They
cannot generally be adjusted as independent scalar penalties.
-/

/-- Three coordinates of a one-mode spectral history. -/
structure SpectralHistory where
  amplitude : ℝ
  memory : ℝ
  phase : ℝ

/-- Closed Poisson cross-kernel for two history modes. -/
noncomputable def historyKernel (h h' : SpectralHistory) : ℝ :=
  markovPoissonKernel (h.memory * h'.memory) (Real.cos (h.phase - h'.phase))

/-- Self-energy of one history mode. -/
noncomputable def historySelfEnergy (h : SpectralHistory) : ℝ :=
  historyKernel h h

/-- Squared spectral distance written through self- and cross-kernels. -/
noncomputable def historySpectralDistanceSq (h h' : SpectralHistory) : ℝ :=
  historySelfEnergy h + historySelfEnergy h' - 2 * historyKernel h h'

/-- Leading quadratic degradation between two one-mode histories. -/
noncomputable def historyDegradation (h h' : SpectralHistory) : ℝ :=
  h.amplitude ^ 2 * historySelfEnergy h -
    2 * h.amplitude * h'.amplitude * historyKernel h h' +
    h'.amplitude ^ 2 * historySelfEnergy h'

/-- **Cone identity.** Degradation is a spectral-distance term plus an amplitude-mismatch
term whose coefficients are the two self-energies. -/
theorem historyDegradation_cone_identity (h h' : SpectralHistory) :
    historyDegradation h h' =
      h.amplitude * h'.amplitude * historySpectralDistanceSq h h' +
        (h.amplitude - h'.amplitude) *
          (h.amplitude * historySelfEnergy h -
            h'.amplitude * historySelfEnergy h') := by
  unfold historyDegradation historySpectralDistanceSq
  ring

/-- On an equal-amplitude slice, only spectral distance remains. -/
theorem historyDegradation_equal_amplitude (h h' : SpectralHistory)
    (ha : h.amplitude = h'.amplitude) :
    historyDegradation h h' = h.amplitude ^ 2 * historySpectralDistanceSq h h' := by
  rw [historyDegradation_cone_identity, ha]
  ring

/-- On an equal-spectrum slice, only squared amplitude mismatch remains. -/
theorem historyDegradation_equal_spectrum (h h' : SpectralHistory)
    (hmemory : h.memory = h'.memory) (hphase : h.phase = h'.phase) :
    historyDegradation h h' =
      (h.amplitude - h'.amplitude) ^ 2 * historySelfEnergy h := by
  have hcross : historyKernel h h' = historySelfEnergy h := by
    unfold historySelfEnergy historyKernel
    rw [← hmemory, ← hphase]
  have hself : historySelfEnergy h' = historySelfEnergy h := by
    unfold historySelfEnergy historyKernel
    rw [← hmemory, ← hphase]
  unfold historyDegradation
  rw [hcross, hself]
  ring

/-- Exact self-energy formula away from the unit-memory boundary. -/
theorem historySelfEnergy_closed (h : SpectralHistory) (hmemory : h.memory ^ 2 ≠ 1) :
    historySelfEnergy h = (1 + h.memory ^ 2) / (1 - h.memory ^ 2) := by
  unfold historySelfEnergy historyKernel
  rw [sub_self, Real.cos_zero]
  simpa [pow_two] using markovPoissonKernel_at_one (h.memory ^ 2) hmemory

/-! ## Marginal blindness to dependence -/

/-- The one-time signal amplitude visible from a marginal feature law in the one-mode
model. Memory and phase are absent by construction. -/
def historyMarginalAmplitude (h : SpectralHistory) : ℝ := h.amplitude

/-- Independent driving with a prescribed marginal signal amplitude. -/
def independentHistory (amplitude : ℝ) : SpectralHistory where
  amplitude := amplitude
  memory := 0
  phase := 0

/-- A persistent two-state driving mode with the same marginal signal amplitude. -/
noncomputable def persistentHalfHistory (amplitude : ℝ) : SpectralHistory where
  amplitude := amplitude
  memory := 1 / 2
  phase := 0

/-- **Marginal-data blindness, executed.** The independent and persistent histories have
the same one-locus marginal amplitude, but at unit amplitude their exact history
degradation is `2/3`. This is a realizable reversible two-state witness; no complex
eigenvalue or compact spectral bump is needed.

Biologically, two populations can have the same allele-frequency or feature-frequency marginal while
differing in ancestry-tract or haplotype persistence. A deployment radius containing that
memory direction cannot be inferred from target marginals alone. -/
theorem same_marginal_different_memory_degradation :
    historyMarginalAmplitude (independentHistory 1) =
        historyMarginalAmplitude (persistentHalfHistory 1) ∧
      historyDegradation (independentHistory 1) (persistentHalfHistory 1) = 2 / 3 := by
  norm_num [historyMarginalAmplitude, independentHistory, persistentHalfHistory,
    historyDegradation, historySelfEnergy, historyKernel, markovPoissonKernel]

/-- The assertion that marginal amplitude alone determines all history degradation. -/
def MarginalAmplitudeDeterminesHistoryDegradation : Prop :=
  ∀ h h' : SpectralHistory,
    historyMarginalAmplitude h = historyMarginalAmplitude h' →
      historyDegradation h h' = 0

/-- **Deployment separation is not identifiable from marginal amplitude.** -/
theorem not_marginalAmplitudeDeterminesHistoryDegradation :
    ¬ MarginalAmplitudeDeterminesHistoryDegradation := by
  intro hdetermines
  have hzero := hdetermines (independentHistory 1) (persistentHalfHistory 1)
    same_marginal_different_memory_degradation.1
  rw [same_marginal_different_memory_degradation.2] at hzero
  norm_num at hzero

/-- The independent/persistent pair as an exact blindness witness for the property
"zero spectral-history degradation from the independent source."  The probe retains
only one-locus marginal amplitude.

Biologically, this is the finite realizable obstruction behind the statement that no
re-analysis of order-erased allele- or feature-frequency marginals can determine the
portability loss caused by ancestry-tract or haplotype persistence. -/
noncomputable def marginalAmplitudeHistoryDegradationBlindness :
    ProbeBlindness historyMarginalAmplitude
      (fun h ↦ historyDegradation (independentHistory 1) h = 0) where
  positive := independentHistory 1
  negative := persistentHalfHistory 1
  same_data := same_marginal_different_memory_degradation.1
  holds := by
    norm_num [historyDegradation, historySelfEnergy, historyKernel,
      markovPoissonKernel, independentHistory]
  fails := by
    rw [same_marginal_different_memory_degradation.2]
    norm_num

/-- **No marginal-only portability criterion.** Any report computed solely from the
one-locus marginal amplitude fails to decide whether spectral-history degradation from
the independent source is zero.  A successful completion must retain dependence-sensitive
information such as selected lagged moments. -/
theorem no_marginal_only_history_degradation_criterion
    {Report : Type*} (report : ℝ → Report) :
    ¬ ∃ accept : Report → Prop, ∀ h : SpectralHistory,
      historyDegradation (independentHistory 1) h = 0 ↔
        accept (report (historyMarginalAmplitude h)) :=
  marginalAmplitudeHistoryDegradationBlindness.no_criterion_of_factors report

end Calibrator
