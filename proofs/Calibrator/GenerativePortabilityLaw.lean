import Calibrator.ReversibleMarkovSpectrum

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

end Calibrator
