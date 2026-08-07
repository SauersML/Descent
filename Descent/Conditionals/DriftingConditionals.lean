/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Conditionals.DriftingConditional
-- `Spectral.twoStatePersistence` is named in three theorems below. It used to arrive
-- along a twenty-two module path out through `PopGen.LDDecayTheory`,
-- `Program.OpenQuestions` and the whole `PortabilityDrift` interior; the module that
-- defines it is one line.
import Descent.Spectral.ReversibleMarkovSpectrum
import Descent.Conditionals.DynamicsContrast

assert_below Descent.Decision

/-!
# Drifting conditionals in finite biological state spaces

This module wires the finite, self-contained core of the drifting-conditionals
calculus into the population-genetics development. The state type can represent
ancestry, deme, local haplotype state, or an environmental stratum.

The analytic diffusion, infinite-dimensional realization, and observability
claims from the source derivation are not smuggled in as assumptions here. The
results below need only finite sums and are proved directly:

* a frozen binary mark and the population mass are transported by one kernel;
* row-stochastic transport preserves marked prevalence exactly;
* the transported response curve reconstructs the transported marked mass;
* the imported identification layer separates static threshold gauge from
  dynamically identifiable threshold motion; and
* symmetric two-state ancestry switching acts on the ancestry contrast through
  the persistence eigenvalue already used by `ReversibleMarkovSpectrum`.

These are the pieces used by the biological core. Stronger manifold-rigidity,
backward-parabolic, and cited spectral-rate claims require separate formal
developments and are deliberately absent rather than represented by theorem
parameters.
-/

namespace Descent.Conditionals

open scoped BigOperators

/-! ## Frozen marks under one biological transport kernel -/

variable {ι : Type*} [Fintype ι]

/-- Transport a mass function through a finite kernel. The same operation is
used for total population mass and for the submass carrying a frozen mark. -/
noncomputable def transportMass (P : ι → ι → ℝ) (mass : ι → ℝ) (y : ι) : ℝ :=
  ∑ x, mass x * P x y

/-- Every source state sends total mass one. Nonnegativity is a separate model
condition; mass conservation needs only this normalization equation. -/
def IsMassPreservingKernel (P : ι → ι → ℝ) : Prop :=
  ∀ x, ∑ y, P x y = 1

/-- Every transition weight is nonnegative. Together with `IsMassPreservingKernel`, this is the
finite Markov-kernel condition. -/
def IsNonnegativeKernel (P : ι → ι → ℝ) : Prop :=
  ∀ x y, 0 ≤ P x y

/-- Row-stochastic transport preserves total mass. -/
theorem transportMass_total (P : ι → ι → ℝ) (mass : ι → ℝ)
    (hP : IsMassPreservingKernel P) :
    ∑ y, transportMass P mass y = ∑ x, mass x := by
  unfold transportMass
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  rw [← Finset.mul_sum, hP x, mul_one]

/-- The marked submass induced by a population mass and response curve. -/
noncomputable def markedMass (population response : ι → ℝ) (x : ι) : ℝ :=
  population x * response x

/-- Reference evaluation: the marked mass is the pointwise product. -/
theorem markedMass_at_reference_point (population response : ι → ℝ) (x : ι) :
    markedMass population response x = population x * response x := rfl

/-- Response curve after both population mass and frozen marked mass pass
through the same kernel. Positivity of every transported population cell is an
input because a real-valued conditional probability is undefined on an empty
cell. -/
noncomputable def transportedResponse (P : ι → ι → ℝ)
    (population response : ι → ℝ)
    (_hpositive : ∀ y, 0 < transportMass P population y) (y : ι) : ℝ :=
  transportMass P (markedMass population response) y /
    transportMass P population y

/-- With a vanishing denominator Mathlib returns `0`, which is a value this quantity can also
take legitimately, so the branch is named rather than left to be inferred from the result. -/
theorem transportedResponse_at_zero_denominator_is_junk (P : ι → ι → ℝ)
    (population response : ι → ℝ)
    (_hpositive : ∀ y, 0 < transportMass P population y) (y : ι)
    (hzero : transportMass P population y = 0) :
    transportedResponse P population response _hpositive y = 0 := by
  unfold transportedResponse
  rw [hzero, div_zero]

/-- Multiplying the reconstructed response by its transported population mass
recovers the transported frozen-mark mass exactly. -/
theorem transportedResponse_mul_population
    (P : ι → ι → ℝ) (population response : ι → ℝ)
    (hpositive : ∀ y, 0 < transportMass P population y) (y : ι) :
    transportMass P population y *
        transportedResponse P population response hpositive y =
      transportMass P (markedMass population response) y := by
  unfold transportedResponse
  field_simp [ne_of_gt (hpositive y)]

/-- Frozen-mark transport conserves prevalence. This is the finite biological
form of transporting the joint marked mass and the marginal by the same forward
equation. -/
theorem transportedResponse_prevalence_conserved
    (P : ι → ι → ℝ) (population response : ι → ℝ)
    (hP : IsMassPreservingKernel P)
    (hpositive : ∀ y, 0 < transportMass P population y) :
    ∑ y, transportMass P population y *
        transportedResponse P population response hpositive y =
      ∑ x, markedMass population response x := by
  calc
    ∑ y, transportMass P population y *
        transportedResponse P population response hpositive y =
        ∑ y, transportMass P (markedMass population response) y := by
          apply Finset.sum_congr rfl
          intro y _
          exact transportedResponse_mul_population P population response hpositive y
    _ = ∑ x, markedMass population response x :=
      transportMass_total P (markedMass population response) hP

/-! ## Composition and the reconstruction tower law -/

/-- Composition of two finite transport kernels. -/
noncomputable def composeKernel (P Q : ι → ι → ℝ) (x z : ι) : ℝ :=
  ∑ y, P x y * Q y z

/-- Reference evaluation: composing the all-ones kernel with itself on two states doubles. -/
theorem composeKernel_at_reference_point :
    composeKernel (fun _ _ : Fin 2 ↦ (1 : ℝ)) (fun _ _ : Fin 2 ↦ (1 : ℝ)) 0 0 = 2 := by
  norm_num [composeKernel, Fin.sum_univ_two]

/-- Transporting mass through a composed kernel is the same as transporting it
through the two kernels in sequence. -/
theorem transportMass_compose (P Q : ι → ι → ℝ) (mass : ι → ℝ) (z : ι) :
    transportMass (composeKernel P Q) mass z =
      transportMass Q (transportMass P mass) z := by
  unfold transportMass composeKernel
  calc
    ∑ x, mass x * ∑ y, P x y * Q y z =
        ∑ x, ∑ y, mass x * P x y * Q y z := by
      refine Finset.sum_congr rfl fun x _ ↦ ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun y _ ↦ ?_
      ring
    _ = ∑ y, ∑ x, mass x * P x y * Q y z := Finset.sum_comm
    _ = ∑ y, (∑ x, mass x * P x y) * Q y z := by
      refine Finset.sum_congr rfl fun y _ ↦ ?_
      rw [Finset.sum_mul]

/-- Composition preserves row-mass normalization. -/
theorem composeKernel_mass_preserving (P Q : ι → ι → ℝ)
    (hP : IsMassPreservingKernel P) (hQ : IsMassPreservingKernel Q) :
    IsMassPreservingKernel (composeKernel P Q) := by
  intro x
  unfold composeKernel
  rw [Finset.sum_comm]
  calc
    ∑ y, ∑ z, P x y * Q y z = ∑ y, P x y * ∑ z, Q y z := by
      refine Finset.sum_congr rfl fun y _ ↦ ?_
      rw [Finset.mul_sum]
    _ = ∑ y, P x y := by
      refine Finset.sum_congr rfl fun y _ ↦ ?_
      rw [hQ y, mul_one]
    _ = 1 := hP x

/-- Destination positivity after two steps supplies positivity for the composed
transport without a new model assumption. -/
theorem transportMass_compose_pos (P Q : ι → ι → ℝ) (population : ι → ℝ)
    (hpositive : ∀ z, 0 < transportMass Q (transportMass P population) z) :
    ∀ z, 0 < transportMass (composeKernel P Q) population z := by
  intro z
  rw [transportMass_compose]
  exact hpositive z

/-- **Exact tower law for drifting conditionals.**

    Reconstructing the frozen-mark conditional after the composed transport is
    identical to reconstructing after `P` and then after `Q`. This is the finite
    semigroup/tower-property form of forward time-reversal reconstruction. -/
theorem transportedResponse_compose
    (P Q : ι → ι → ℝ) (population response : ι → ℝ)
    (hPpositive : ∀ y, 0 < transportMass P population y)
    (hQpositive : ∀ z, 0 < transportMass Q (transportMass P population) z)
    (z : ι) :
    transportedResponse (composeKernel P Q) population response
        (transportMass_compose_pos P Q population hQpositive) z =
      transportedResponse Q (transportMass P population)
        (transportedResponse P population response hPpositive) hQpositive z := by
  have hmarked :
      markedMass (transportMass P population)
          (transportedResponse P population response hPpositive) =
        transportMass P (markedMass population response) := by
    funext y
    exact transportedResponse_mul_population P population response hPpositive y
  change
    transportMass (composeKernel P Q) (markedMass population response) z /
          transportMass (composeKernel P Q) population z =
      transportMass Q
          (markedMass (transportMass P population)
            (transportedResponse P population response hPpositive)) z /
        transportMass Q (transportMass P population) z
  rw [transportMass_compose, transportMass_compose, hmarked]

/-! ## The population-built reverse bridge -/

/-- Bayes' reverse transition from destination `y` back to source `x`.

    The observed source population and its transported marginal supply the
    reweighting. Positivity is proof-carrying because no conditional law exists
    at an empty destination cell. -/
noncomputable def reverseBridge (P : ι → ι → ℝ) (population : ι → ℝ)
    (_hpositive : ∀ y, 0 < transportMass P population y) (y x : ι) : ℝ :=
  population x * P x y / transportMass P population y

/-- With a vanishing denominator Mathlib returns `0`, which is a value this quantity can also
take legitimately, so the branch is named rather than left to be inferred from the result. -/
theorem reverseBridge_at_zero_denominator_is_junk (P : ι → ι → ℝ) (population : ι → ℝ)
    (_hpositive : ∀ y, 0 < transportMass P population y) (y x : ι)
    (hzero : transportMass P population y = 0) :
    reverseBridge P population _hpositive y x = 0 := by
  unfold reverseBridge
  rw [hzero, div_zero]

/-- Every row of the population-built reverse bridge has mass one. -/
theorem reverseBridge_mass_preserving
    (P : ι → ι → ℝ) (population : ι → ℝ)
    (hpositive : ∀ y, 0 < transportMass P population y) :
    IsMassPreservingKernel (reverseBridge P population hpositive) := by
  intro y
  have hdenom : ∑ x, population x * P x y ≠ 0 := by
    simpa [transportMass] using ne_of_gt (hpositive y)
  unfold reverseBridge transportMass
  rw [← Finset.sum_div, div_self hdenom]

/-- Nonnegative forward transport and population weights give a nonnegative
reverse bridge. -/
theorem reverseBridge_nonnegative
    (P : ι → ι → ℝ) (population : ι → ℝ)
    (hkernel : IsNonnegativeKernel P) (hpopulation : ∀ x, 0 ≤ population x)
    (hpositive : ∀ y, 0 < transportMass P population y) :
    IsNonnegativeKernel (reverseBridge P population hpositive) := by
  intro y x
  exact div_nonneg (mul_nonneg (hpopulation x) (hkernel x y)) (hpositive y).le

/-- **The reconstructed response is expectation through the reverse bridge.**

    This is the exact finite time-reversal formula. The marginal does not merely
    accompany the conditional: it constructs the bridge that transports the
    earlier response to the destination population. -/
theorem transportedResponse_eq_reverseBridge_average
    (P : ι → ι → ℝ) (population response : ι → ℝ)
    (hpositive : ∀ y, 0 < transportMass P population y) (y : ι) :
    transportedResponse P population response hpositive y =
      ∑ x, reverseBridge P population hpositive y x * response x := by
  unfold transportedResponse reverseBridge transportMass markedMass
  calc
    (∑ x, population x * response x * P x y) / ∑ x, population x * P x y =
        ∑ x, (population x * response x * P x y) /
          ∑ x, population x * P x y := by rw [Finset.sum_div]
    _ = ∑ x, (population x * P x y / ∑ x, population x * P x y) * response x := by
      refine Finset.sum_congr rfl fun x _ ↦ ?_
      ring

/-- **Transported response is a weighted average of source responses.**

    If source responses lie in `[lower, upper]`, nonnegative transport and
    population weights keep every reconstructed response in that same
    interval. This is the finite maximum principle behind stable forward
    reconstruction. -/
theorem transportedResponse_mem_Icc
    (P : ι → ι → ℝ) (population response : ι → ℝ)
    (hkernel : IsNonnegativeKernel P) (hpopulation : ∀ x, 0 ≤ population x)
    (hpositive : ∀ y, 0 < transportMass P population y)
    (lower upper : ℝ) (hlower : ∀ x, lower ≤ response x)
    (hupper : ∀ x, response x ≤ upper) (y : ι) :
    transportedResponse P population response hpositive y ∈ Set.Icc lower upper := by
  -- A transported response is an average through the reverse bridge, and an average of
  -- values in `[lower, upper]` stays in `[lower, upper]`.  Read off the bridge's own two
  -- properties, each direction is one comparison; written directly against the quotient,
  -- the two directions were one summation argument copied and mirrored.
  have hnonneg := reverseBridge_nonnegative P population hkernel hpopulation hpositive
  have hmass := reverseBridge_mass_preserving P population hpositive y
  rw [transportedResponse_eq_reverseBridge_average]
  constructor
  · calc lower = ∑ x, reverseBridge P population hpositive y x * lower := by
          rw [← Finset.sum_mul, hmass, one_mul]
      _ ≤ ∑ x, reverseBridge P population hpositive y x * response x :=
          Finset.sum_le_sum fun x _ ↦ mul_le_mul_of_nonneg_left (hlower x) (hnonneg y x)
  · calc ∑ x, reverseBridge P population hpositive y x * response x
        ≤ ∑ x, reverseBridge P population hpositive y x * upper :=
          Finset.sum_le_sum fun x _ ↦ mul_le_mul_of_nonneg_left (hupper x) (hnonneg y x)
      _ = upper := by rw [← Finset.sum_mul, hmass, one_mul]

/-- Reconstruction is linear in the marked response when the population and
transport kernel are fixed. -/
theorem transportedResponse_sub
    (P : ι → ι → ℝ) (population response₁ response₂ : ι → ℝ)
    (hpositive : ∀ y, 0 < transportMass P population y) (y : ι) :
    transportedResponse P population response₁ hpositive y -
        transportedResponse P population response₂ hpositive y =
      transportedResponse P population (fun x ↦ response₁ x - response₂ x)
        hpositive y := by
  unfold transportedResponse transportMass markedMass
  rw [← sub_div]
  congr 1
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  ring

/-- A spatially constant perturbation is preserved exactly by forward
reconstruction. This witnesses sharpness of the constant in
`transportedResponse_dist_le`. -/
theorem transportedResponse_add_const
    (P : ι → ι → ℝ) (population response : ι → ℝ)
    (hpositive : ∀ y, 0 < transportMass P population y) (shift : ℝ) (y : ι) :
    transportedResponse P population (fun x ↦ response x + shift) hpositive y =
      transportedResponse P population response hpositive y + shift := by
  unfold transportedResponse transportMass markedMass
  have hdenom : ∑ x, population x * P x y ≠ 0 := ne_of_gt (hpositive y)
  apply (div_eq_iff hdenom).2
  rw [add_mul, div_mul_cancel₀ _ hdenom]
  calc
    ∑ x, population x * (response x + shift) * P x y =
        ∑ x, (population x * response x * P x y + shift * (population x * P x y)) := by
      refine Finset.sum_congr rfl fun x _ ↦ ?_
      ring
    _ = (∑ x, population x * response x * P x y) +
        ∑ x, shift * (population x * P x y) := Finset.sum_add_distrib
    _ = (∑ x, population x * response x * P x y) +
        shift * ∑ x, population x * P x y := by rw [Finset.mul_sum]

/-- **Forward reconstruction is sup-norm non-expansive.**

    If two source response curves differ by at most `ε` pointwise, their
    transported reconstructions differ by at most `ε` in every destination
    cell. The constant one is exact: a constant perturbation is preserved. -/
theorem transportedResponse_dist_le
    (P : ι → ι → ℝ) (population response₁ response₂ : ι → ℝ)
    (hkernel : IsNonnegativeKernel P) (hpopulation : ∀ x, 0 ≤ population x)
    (hpositive : ∀ y, 0 < transportMass P population y)
    (ε : ℝ) (hε : ∀ x, |response₁ x - response₂ x| ≤ ε) (y : ι) :
    |transportedResponse P population response₁ hpositive y -
        transportedResponse P population response₂ hpositive y| ≤ ε := by
  rw [transportedResponse_sub]
  have hbounds := transportedResponse_mem_Icc P population
    (fun x ↦ response₁ x - response₂ x) hkernel hpopulation hpositive
    (-ε) ε (fun x ↦ (abs_le.mp (hε x)).1) (fun x ↦ (abs_le.mp (hε x)).2) y
  exact abs_le.mpr hbounds

/-! ## A stationary marginal does not identify the conditional -/

/-- A response concentrated in ancestry state zero. -/
def stateZeroResponse (i : Fin 2) : ℝ := if i = 0 then 1 else 0

/-- Reference evaluations: the indicator of the first state. -/
theorem stateZeroResponse_at_reference_point :
    stateZeroResponse 0 = 1 ∧ stateZeroResponse 1 = 0 := by
  constructor <;> simp [stateZeroResponse]

/-- A response concentrated in ancestry state one. -/
noncomputable def stateOneResponse (i : Fin 2) : ℝ :=
  Descent.Core.kronecker i 1

/-- Reference evaluation; see `Descent.Core.Ratios` for what these pin and why. -/
theorem stateOneResponse_at_reference_point :
    stateOneResponse 0 = 0 ∧ stateOneResponse 1 = 1 := by
  constructor <;> simp [stateOneResponse,
      Descent.Core.kronecker]

/-- The ancestry-state-one response IS `DynamicsContrast.targetAnnotation`.

    Both are the indicator of state one on two states. Stating the identity rather than
    leaving two alpha-equivalent bodies is what makes a later edit to either one a compile
    error instead of a silent divergence: two definitions of one quantity, tied by neither a
    call nor a theorem, cannot disagree loudly. -/
theorem stateOneResponse_eq_targetAnnotation :
    stateOneResponse = targetAnnotation := rfl

/-- The uniform two-state population remains positive under the kernel that
never moves. -/
theorem transportMass_stayKernel_uniformTwo_pos (y : Fin 2) :
    0 < transportMass Portability.stayKernel Portability.uniformTwo y := by
  fin_cases y <;>
    norm_num [transportMass, Portability.stayKernel, Portability.uniformTwo, Fin.sum_univ_two]

/-- **A stationary marginal carries no information about the conditional.**

    The same uniform population and the same stationary transport support two
    opposite response curves. Their transported population marginals agree at
    every state, while their transported responses at state zero are `1` and
    `0`. This is a concrete, non-vacuous counterexample to unconditional
    reconstruction of a conditional from a stationary marginal path. -/
theorem stationaryMarginal_does_not_identify_conditional :
    (∀ y, transportMass Portability.stayKernel Portability.uniformTwo y = Portability.uniformTwo y)
      ∧
      transportedResponse Portability.stayKernel Portability.uniformTwo stateZeroResponse
          transportMass_stayKernel_uniformTwo_pos 0 = 1 ∧
      transportedResponse Portability.stayKernel Portability.uniformTwo stateOneResponse
          transportMass_stayKernel_uniformTwo_pos 0 = 0 := by
  constructor
  · intro y
    fin_cases y <;>
      norm_num [transportMass, Portability.stayKernel, Portability.uniformTwo, Fin.sum_univ_two]
  · constructor <;>
      norm_num [transportedResponse, transportMass, markedMass, Portability.uniformTwo,
        Portability.stayKernel, stateZeroResponse, stateOneResponse, Fin.sum_univ_two,
      Descent.Core.kronecker]

/-! ## Two-state local-ancestry switching -/

/-- Symmetric switching between two local-ancestry or haplotype states. -/
def symmetricTwoStateKernel (switch : ℝ) (i j : Fin 2) : ℝ :=
  if i = j then 1 - switch else switch

/-- **The symmetric switching kernel is a genuine Markov kernel**, so the theorems assuming
`IsNonnegativeKernel` are about something. Without a witness those theorems could hold
vacuously, which is the difference between a maximum principle and an empty statement. -/
theorem symmetricTwoStateKernel_nonneg (switch : ℝ) (h0 : 0 ≤ switch) (h1 : switch ≤ 1) :
    IsNonnegativeKernel (symmetricTwoStateKernel switch) := by
  intro i j
  unfold symmetricTwoStateKernel
  split <;> linarith

theorem symmetricTwoStateKernel_mass_preserving (switch : ℝ) :
    IsMassPreservingKernel (symmetricTwoStateKernel switch) := by
  intro i
  fin_cases i <;>
    norm_num [symmetricTwoStateKernel, Fin.sum_univ_two]

/-- The uniform two-state population is stationary under symmetric switching. -/
theorem uniformTwo_stationary_symmetricTwoStateKernel (switch : ℝ) :
    Portability.IsStationaryKernel Portability.uniformTwo (symmetricTwoStateKernel switch) := by
  intro j
  fin_cases j <;>
    norm_num [Portability.uniformTwo, symmetricTwoStateKernel, Fin.sum_univ_two] <;>
    ring

/-- The centered ancestry contrast. -/
def twoStateContrast (i : Fin 2) : ℝ := if i = 0 then 1 else -1

/-- Reference evaluation; see `Descent.Core.Ratios` for what these pin and why. -/
theorem twoStateContrast_at_reference_point :
    twoStateContrast 0 = 1 ∧ twoStateContrast 1 = -1 := by
  constructor <;> simp [twoStateContrast]

/-- Symmetric ancestry switching damps the centered ancestry contrast by the
same persistence eigenvalue used by the reversible Markov spectral kernel. -/
theorem symmetricTwoStateKernel_contrast (switch : ℝ) (i : Fin 2) :
    ∑ j, symmetricTwoStateKernel switch i j * twoStateContrast j =
      Spectral.twoStatePersistence switch switch * twoStateContrast i := by
  fin_cases i <;>
    norm_num [symmetricTwoStateKernel, twoStateContrast, Spectral.twoStatePersistence,
      Fin.sum_univ_two] <;>
    ring

/-! ## The portability law: which half of a calibration curve survives drift

A response curve on two ancestry states splits into a baseline (its mean) and a
score-dependent part (its contrast component). Repeated ancestry switching fixes the first
exactly and damps the second geometrically. That asymmetry is the portability law, and it
is the structural reason a recalibration that models the score distribution but not the
baseline loses the component with the longer half-life.
-/

/-- Act on a response curve by a transition kernel: `(applyKernel P f) i = ∑ j P i j * f j`.

    This is the action on functions, dual to `transportMass`'s action on masses. -/
noncomputable def applyKernel (P : ι → ι → ℝ) (f : ι → ℝ) (i : ι) : ℝ :=
  ∑ j, P i j * f j

/-- Repeated ancestry switching, `n` steps of drift. -/
noncomputable def applyKernelIter (P : ι → ι → ℝ) : ℕ → (ι → ℝ) → (ι → ℝ)
  | 0, f => f
  | n + 1, f => applyKernel P (applyKernelIter P n f)

/-- **The baseline is exactly conserved.** A row-stochastic kernel fixes constants, at every
    number of steps, so the durable part of a calibration curve is its level. -/
theorem applyKernelIter_const (P : ι → ι → ℝ) (hP : IsMassPreservingKernel P) (c : ℝ) :
    ∀ n, applyKernelIter P n (fun _ ↦ c) = fun _ ↦ c := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      funext i
      simp only [applyKernelIter, ih, applyKernel]
      rw [← Finset.sum_mul, hP i, one_mul]

/-- Two-state response curves decompose as baseline plus a multiple of the ancestry
    contrast. This is the split whose two halves have different fates. -/
noncomputable def twoStateCurve (baseline amplitude : ℝ) (i : Fin 2) : ℝ :=
  baseline + amplitude * twoStateContrast i

/-- **The score-dependent half decays geometrically.** One step of symmetric switching
    multiplies the contrast amplitude by the persistence eigenvalue and leaves the baseline
    alone. -/
theorem applyKernel_twoStateCurve (switch baseline amplitude : ℝ) :
    applyKernel (symmetricTwoStateKernel switch) (twoStateCurve baseline amplitude) =
      twoStateCurve baseline (Spectral.twoStatePersistence switch switch * amplitude) := by
  funext i
  simp only [applyKernel, twoStateCurve]
  fin_cases i <;>
    simp only [symmetricTwoStateKernel, twoStateContrast, Spectral.twoStatePersistence,
      Fin.sum_univ_two] <;>
    norm_num <;>
    ring

/-- **The portability law on two ancestry states.**

    After `n` steps of drift the baseline is untouched and the score-dependent amplitude
    carries a factor `persistence ^ n`. So the two halves of a calibration curve have
    different fates: the level is durable, the slope is perishable, and the curve flattens
    toward local prevalence at a geometric rate set by how fast ancestry mixes.

    The practical reading, which is why this is stated about a curve rather than about an
    eigenvalue: a recalibration that adjusts the score distribution but does not model the
    baseline discards precisely the component that survives longest. Far from training, the
    surviving content of a score is the local base rate. -/
theorem applyKernelIter_twoStateCurve (switch baseline amplitude : ℝ) (n : ℕ) :
    applyKernelIter (symmetricTwoStateKernel switch) n
        (twoStateCurve baseline amplitude) =
      twoStateCurve baseline (Spectral.twoStatePersistence switch switch ^ n * amplitude) := by
  induction n with
  | zero => simp [applyKernelIter]
  | succ n ih =>
      rw [applyKernelIter, ih, applyKernel_twoStateCurve]
      congr 1
      ring

/-! ## Forward spectral contraction -/

/-- **A spectral gap contracts every nonconstant finite spectral mixture.**

    If every active relaxation rate is at least `gap`, advancing by a
    nonnegative horizon `delta` contracts the error energy by at most
    `exp (-2 * gap * delta)`. No division, logarithm, or differentiability is
    hidden in the statement. -/
theorem errorEnergy_forward_le {n : ℕ} (w lam : Fin n → ℝ)
    (gap t delta : ℝ) (hw : ∀ k, 0 ≤ w k) (hgap : ∀ k, gap ≤ lam k)
    (hdelta : 0 ≤ delta) :
    errorEnergy w lam (t + delta) ≤
      Real.exp (-(2 * gap * delta)) * errorEnergy w lam t := by
  unfold errorEnergy
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun k _ ↦ ?_
  have hdecay : Real.exp (-(2 * lam k * delta)) ≤
      Real.exp (-(2 * gap * delta)) := by
    apply Real.exp_le_exp.mpr
    nlinarith [hgap k]
  calc
    w k * Real.exp (-(2 * lam k * (t + delta))) =
        w k * (Real.exp (-(2 * lam k * t)) *
          Real.exp (-(2 * lam k * delta))) := by
      rw [← Real.exp_add]
      congr 2
      ring
    _ ≤ w k * (Real.exp (-(2 * lam k * t)) *
          Real.exp (-(2 * gap * delta))) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hdecay (Real.exp_pos _).le) (hw k)
    _ = Real.exp (-(2 * gap * delta)) *
        (w k * Real.exp (-(2 * lam k * t))) := by ring

/-- A single mode at the gap attains the forward contraction factor exactly. -/
theorem singleMode_errorEnergy_forward_eq (weight gap t delta : ℝ) :
    weight * Real.exp (-(2 * gap * (t + delta))) =
      Real.exp (-(2 * gap * delta)) *
        (weight * Real.exp (-(2 * gap * t))) := by
  rw [show -(2 * gap * (t + delta)) =
    -(2 * gap * t) + -(2 * gap * delta) by ring, Real.exp_add]
  ring

/-! ## The drifting probit index, and the constraint tying its two surfaces

Under Ornstein-Uhlenbeck drift of the covariate the probit single-index family
`Phi (a t * x + b t)` is carried to itself, with `a t = a0 * exp (-lam * t) / sqrt (1 + a0 ^ 2 *
ouVariance lam t)`,
  `b t = b0 / sqrt (1 + a0 ^ 2 * ouVariance lam t)`.

The two surfaces share one denominator. That the family is invariant is an analytic fact
about the Gaussian semigroup which is NOT proved here; what is proved here is the algebraic
consequence, and it is the part a fitted model can be tested against.
-/

/-- A positive Ornstein-Uhlenbeck rate and a nonnegative biological drift
horizon. Keeping the domain facts in the data prevents the variance formula
from silently dividing by zero or describing negative time. -/
structure OUHorizon where
  rate : ℝ
  time : ℝ
  rate_pos : 0 < rate
  time_nonneg : 0 ≤ time

/-- **The class is inhabited by a closed term**: unit relaxation rate, zero elapsed drift.

    A structure whose every construction takes a hypothesis can still be empty, and then
    every theorem quantified over it holds vacuously -- kernel-checked, clean axiom report,
    no content. This is the witness that makes the horizon theorems statements about
    something. -/
def OUHorizon.unit : OUHorizon where
  rate := 1
  time := 0
  rate_pos := one_pos
  time_nonneg := le_refl 0

theorem OUHorizon.nonempty : Nonempty OUHorizon := ⟨OUHorizon.unit⟩

/-- The zero drift horizon at a positive relaxation rate. -/
def OUHorizon.zero (rate : ℝ) (hrate : 0 < rate) : OUHorizon where
  rate := rate
  time := 0
  rate_pos := hrate
  time_nonneg := le_rfl

/-- Variance accumulated by an Ornstein-Uhlenbeck bridge over a valid horizon.

    Empirical status: UNTESTED. -/
noncomputable def ouVariance (horizon : OUHorizon) : ℝ :=
  (1 - Real.exp (-(2 * horizon.rate * horizon.time))) / (2 * horizon.rate)

/-- With a vanishing denominator Mathlib returns `0`, which is a value this quantity can also
take legitimately, so the branch is named rather than left to be inferred from the result. -/
theorem ouVariance_at_zero_denominator_is_junk (horizon : OUHorizon)
    (hzero : (2 * horizon.rate) = 0) :
    ouVariance horizon = 0 := by
  unfold ouVariance
  rw [hzero, div_zero]

/-- A valid OU horizon accumulates nonnegative variance. -/
theorem ouVariance_nonneg (horizon : OUHorizon) : 0 ≤ ouVariance horizon := by
  unfold ouVariance
  apply div_nonneg
  · exact sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by
      nlinarith [horizon.rate_pos, horizon.time_nonneg]))
  · exact mul_nonneg (by norm_num) horizon.rate_pos.le

/-- **The Ornstein-Uhlenbeck variance's timescale, pinned.** `ouVariance_nonneg` is a sign, and
holds for every body of the form `(1 - exp (-c * rate * time)) / (c * rate)`. At relaxation rate
one half over unit time the accumulated variance is `1 - exp (-1)`, which fixes `c = 2` -- the
factor that makes the stationary variance `1 / (2 * rate)` rather than `1 / rate`, and with it the
rate at which a drifting conditional forgets its starting value. -/
theorem ouVariance_unit_relaxation :
    ouVariance ⟨1 / 2, 1, by norm_num, by norm_num⟩ = 1 - Real.exp (-1) := by
  unfold ouVariance
  norm_num

/-- The denominator shared by both surfaces of the drifting probit index.

    Empirical status: UNTESTED. -/
noncomputable def probitScaleFactor (a0 : ℝ) (horizon : OUHorizon) : ℝ :=
  Real.sqrt (1 + a0 ^ 2 * ouVariance horizon)

/-- The shared probit scale is strictly positive on every valid OU horizon;
callers never need to assume away a zero denominator. -/
theorem probitScaleFactor_pos (a0 : ℝ) (horizon : OUHorizon) :
    0 < probitScaleFactor a0 horizon := by
  unfold probitScaleFactor
  apply Real.sqrt_pos.2
  nlinarith [mul_nonneg (sq_nonneg a0) (ouVariance_nonneg horizon)]

/-- Slope surface of the drifting probit index.

    Empirical status: UNTESTED. -/
noncomputable def probitSlope (a0 : ℝ) (horizon : OUHorizon) : ℝ :=
  a0 * Real.exp (-(horizon.rate * horizon.time)) /
    probitScaleFactor a0 horizon

/-- With a vanishing denominator Mathlib returns `0`, which is a value this quantity can also
take legitimately, so the branch is named rather than left to be inferred from the result. -/
theorem probitSlope_at_zero_denominator_is_junk (a0 : ℝ) (horizon : OUHorizon)
    (hzero : probitScaleFactor a0 horizon = 0) :
    probitSlope a0 horizon = 0 := by
  unfold probitSlope
  rw [hzero, div_zero]

/-- Intercept surface of the drifting probit index.

    Empirical status: UNTESTED. -/
noncomputable def probitIntercept (a0 b0 : ℝ) (horizon : OUHorizon) : ℝ :=
  b0 / probitScaleFactor a0 horizon

/-- With a vanishing denominator Mathlib returns `0`, which is a value this quantity can also
take legitimately, so the branch is named rather than left to be inferred from the result. -/
theorem probitIntercept_at_zero_denominator_is_junk (a0 b0 : ℝ) (horizon : OUHorizon)
    (hzero : probitScaleFactor a0 horizon = 0) :
    probitIntercept a0 b0 horizon = 0 := by
  unfold probitIntercept
  rw [hzero, div_zero]

/-- **The intercept and slope surfaces are not independent.**

    Their ratio is a single exponential in drift time with one rate:
    `b t / a t = (b0 / a0) * exp (lam * t)`. The shared `probitScaleFactor` cancels, so
    this needs nothing about the denominator beyond its being nonzero -- in particular it
    does not depend on the analytic invariance claim above.

    Two consequences, and they are the reason this is here rather than in prose.

    Fitting: an intercept surface and a slope surface estimated in separately penalized
    blocks carry one degree of freedom more than the drift model permits. Imposing this
    constraint removes it and leaves one interpretable parameter, the drift rate `lam`.

    Testing: `log (b t / a t)` is affine in `t` with slope `lam`. Curvature in that plot
    refutes Ornstein-Uhlenbeck drift rather than the fit, so this is falsifiable against
    data the corpus already produces.

    Empirical status: UNTESTED, and the test just described is how that changes. -/
theorem probitIntercept_div_probitSlope (a0 b0 : ℝ) (horizon : OUHorizon)
    (ha : a0 ≠ 0) :
    probitIntercept a0 b0 horizon / probitSlope a0 horizon =
      b0 / a0 * Real.exp (horizon.rate * horizon.time) := by
  have hE : Real.exp (horizon.rate * horizon.time) ≠ 0 := Real.exp_ne_zero _
  have hS : probitScaleFactor a0 horizon ≠ 0 := ne_of_gt (probitScaleFactor_pos a0 horizon)
  unfold probitIntercept probitSlope
  rw [Real.exp_neg]
  field_simp

/-- At drift time zero the ratio is the ratio of the initial parameters, so the invariant
    is anchored rather than merely proportional. -/
theorem probitIntercept_div_probitSlope_zero (a0 b0 lam : ℝ) (ha : a0 ≠ 0)
    (hlam : 0 < lam) :
    probitIntercept a0 b0 (OUHorizon.zero lam hlam) /
        probitSlope a0 (OUHorizon.zero lam hlam) = b0 / a0 := by
  simpa [OUHorizon.zero] using
    probitIntercept_div_probitSlope a0 b0 (OUHorizon.zero lam hlam) ha

/-- The scale parameter `A = a ^ (-2)` linearizes the slope dynamics: if
    `a' = -lam * a - a ^ 3 / 2` then `A' = 2 * lam * A + 1`.

    Stated as the algebraic identity the derivative relation reduces to, so it is checkable
    without carrying a derivative. This linearization is what makes the closed form for the
    slope surface integrable in the first place. -/
theorem probit_scale_linearization (lam a da : ℝ) (ha : a ≠ 0)
    (h : da = -lam * a - a ^ 3 / 2) :
    -2 * da / a ^ 3 = 2 * lam / a ^ 2 + 1 := by
  subst h
  field_simp
  ring

end Descent.Conditionals
