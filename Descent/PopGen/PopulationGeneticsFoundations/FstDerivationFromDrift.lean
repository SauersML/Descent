/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.PopGen.PopulationGeneticsFoundations.MigrationDriftFoundations

namespace Descent.PopGen

open MeasureTheory

/-!
# `PopulationGeneticsFoundations.FstDerivationFromDrift`

Part of the split of `Descent/PopGen/PopulationGeneticsFoundations.lean`, which was 2,740 lines.

The parts are a CHAIN: each imports the one before, in the order the original was written.
That is the conservative choice, deliberately. A monolith's declarations depend on each
other in whatever order they happen to appear, and cutting it into modules that import only
what they use means discovering that order first -- worth doing, and not what this does.
The chain preserves every resolution the single file had, so the split cannot change what
any proof sees.

Where a cut falls inside a section, the section is reopened and reclosed by name. A section
scopes `variable`s and this file declares none at that level, so the reopening is exact.
-/



/-!
## Derivation of Fst from Wright-Fisher Drift Dynamics

Rather than *defining* Fst as a formula, we *derive* it from the fundamental
Wright-Fisher recurrence for heterozygosity.  The key identity is:

  H(t+1) = (1 - 1/(2N)) × H(t)

which expresses the fact that two alleles drawn from generation t+1 are
identical by descent with probability 1/(2N), leaving heterozygosity reduced
by that factor each generation.

We then:
1. Solve this recurrence in closed form by induction.
2. Define Fst(t) = 1 - H(t)/H₀ and derive its properties.
3. Introduce mutation, find the equilibrium heterozygosity H* = θ/(1+θ),
   and derive Fst_eq = 1/(1+θ) as a *consequence*.
-/

section FstDerivationFromDrift

/-! ### Pure-drift heterozygosity recurrence -/

/-! **`hetRecurrence` is deleted here.**  It was
`Descent.Core.hetRecurrence` under a second name, and every reference now
calls the kernel.  Nothing referenced the wrapper; `Core.hetRecurrence` is the recurrence, and
`Coalescent.WrightFisher.hetRecurrence_eq_pairDistinct` is where it stops being a stipulation. -/


/-- **Closed-form solution by induction.**
    hetRecurrence Ne H₀ t = (1 - 1/(2Ne))^t × H₀. -/
theorem hetRecurrence_closed_form (Ne H₀ : ℝ) (t : ℕ) :
    Descent.Core.hetRecurrence Ne H₀ t = (1 - 1 / (2 * Ne)) ^ t * H₀ :=
  Descent.Core.hetRecurrence_closed_form Ne H₀ t

/-! ### Fst derived from heterozygosity loss -/

/-! ### `heterozygosityLossDerived` is deleted, again

It was a second definition of `heterozygosityLossFromDrift` -- same body,
`Core.heterozygosityLoss Ne t`, arguments in the other order -- and its own docstring
conceded the consequence: "an agreement check between the two derivations passes on the
wrong value". It was deleted once, in `8f7f5b2`, and came back when this module was split
out of the monolith from content predating that commit. The six facts that had been proved
only on the second copy are restated here on the surviving name, proofs unchanged, because
the bodies were identical.
-/

/-- **Loss matches heterozygosity decay.** When `H₀ ≠ 0`,
`heterozygosityLossFromDrift t Ne = 1 - hetRecurrence Ne H₀ t / H₀`. -/
theorem heterozygosityLossFromDrift_eq_het_loss (Ne H₀ : ℝ) (t : ℕ) (hH₀ : H₀ ≠ 0) :
    heterozygosityLossFromDrift t Ne = 1 - Descent.Core.hetRecurrence Ne H₀ t / H₀ := by
  unfold heterozygosityLossFromDrift Descent.Core.heterozygosityLoss Descent.Core.complement Descent.Core.geometricDecay
  rw [hetRecurrence_closed_form]
  field_simp

/-- **Nothing is lost at time zero.** -/
theorem heterozygosityLossFromDrift_zero (Ne : ℝ) : heterozygosityLossFromDrift 0 Ne = 0 := by
  unfold heterozygosityLossFromDrift Descent.Core.heterozygosityLoss Descent.Core.complement Descent.Core.geometricDecay
  simp

/-- **Loss is monotonically increasing in `t`.** -/
theorem heterozygosityLossFromDrift_mono (Ne : ℝ) (t₁ t₂ : ℕ) (hNe : 2 < Ne)
    (h_lt : t₁ < t₂) :
    heterozygosityLossFromDrift t₁ Ne < heterozygosityLossFromDrift t₂ Ne := by
  unfold heterozygosityLossFromDrift Descent.Core.heterozygosityLoss Descent.Core.complement Descent.Core.geometricDecay
  have h_base_pos : 0 < 1 - 1 / (2 * Ne) := by
    rw [sub_pos, div_lt_one (by linarith)]; linarith
  have h_base_lt : 1 - 1 / (2 * Ne) < 1 := by
    rw [sub_lt_self_iff]; positivity
  linarith [pow_lt_pow_right_of_lt_one₀ h_base_pos h_base_lt h_lt]

/-- **`0 ≤ L(t)` for all `t` when `Nₑ ≥ 2`.** -/
theorem heterozygosityLossFromDrift_nonneg (Ne : ℝ) (t : ℕ) (hNe : 2 ≤ Ne) :
    0 ≤ heterozygosityLossFromDrift t Ne := by
  unfold heterozygosityLossFromDrift Descent.Core.heterozygosityLoss Descent.Core.complement Descent.Core.geometricDecay
  rw [sub_nonneg]
  apply pow_le_one₀
  · rw [sub_nonneg, div_le_one (by linarith)]; linarith
  · rw [sub_le_self_iff]; positivity

/-- **`L(t) < 1` for all `t` when `Nₑ ≥ 2`.** -/
theorem heterozygosityLossFromDrift_lt_one (Ne : ℝ) (t : ℕ) (hNe : 2 ≤ Ne) :
    heterozygosityLossFromDrift t Ne < 1 := by
  unfold heterozygosityLossFromDrift Descent.Core.heterozygosityLoss Descent.Core.complement Descent.Core.geometricDecay
  linarith [pow_pos (show 0 < 1 - 1 / (2 * Ne) by
    rw [sub_pos, div_lt_one (by linarith)]; linarith) t]

/-- **Loss accrues faster in a smaller population.** -/
theorem heterozygosityLossFromDrift_faster_small_Ne (Ne₁ Ne₂ : ℝ) (t : ℕ) (ht : 1 ≤ t)
    (hNe₁ : 2 < Ne₁) (hNe₂ : 2 < Ne₂) (h_lt : Ne₁ < Ne₂) :
    heterozygosityLossFromDrift t Ne₂ < heterozygosityLossFromDrift t Ne₁ := by
  unfold heterozygosityLossFromDrift Descent.Core.heterozygosityLoss Descent.Core.complement Descent.Core.geometricDecay
  have h_base₁_pos : 0 < 1 - 1 / (2 * Ne₁) := by
    rw [sub_pos, div_lt_one (by linarith)]; linarith
  have h_base₂_lt_one : 1 - 1 / (2 * Ne₂) < 1 := by
    rw [sub_lt_self_iff]; positivity
  have h_base_lt : 1 - 1 / (2 * Ne₁) < 1 - 1 / (2 * Ne₂) := by
    rw [sub_lt_sub_iff_left]
    exact div_lt_div_of_pos_left one_pos (by linarith) (by linarith)
  linarith [pow_lt_pow_left₀ h_base_lt (le_of_lt h_base₁_pos)
    (Nat.ne_zero_of_lt (by omega : 0 < t))]

/-! ### Mutation-drift recurrence and equilibrium -/

/-- **Heterozygosity recurrence with mutation.**
    Drift reduces heterozygosity by factor (1 - 1/(2N)), while mutation
    creates new heterozygosity at rate 2μ from homozygous sites.

    Empirical status: **VALIDATED**
    (`validation/empirical/simcov/battery_bulk15.py`). Infinite-alleles
    Wright-Fisher, 220 replicate populations started MONOMORPHIC so the whole
    trajectory sits far from the plateau, where a recurrence's slope is what is
    actually under test. The map is iterated FIFTEEN generations from a measured
    `H_t` and compared against the measured `H_{t+15}`, because a map can be
    right for one step and wrong compounded:

      Ne    theta   from H0    predicted  simulated            sems
      100   0.80    0.0859      0.13136   0.12337 ± 0.00790     1.01
      100   0.80    0.1644      0.19990   0.20650 ± 0.01163     0.57
      100   0.80    0.2830      0.30349   0.30751 ± 0.01443     0.28
       50   1.00    0.0971      0.20241   0.20537 ± 0.01088     0.27
       50   1.00    0.3159      0.36406   0.36316 ± 0.01440     0.06
      200   0.80    0.0991      0.12168   0.12164 ± 0.00789     0.01
      200   0.80    0.2666      0.27820   0.27850 ± 0.01329     0.02

    The ORACLE is the finding here. An earlier run of this same design against a
    BIALLELIC Wright-Fisher missed by 632 sems, and the arithmetic says why:
    under biallelic two-way mutation `p - 1/2` contracts by `1 - 2 mu` and
    `H = 1/2 - 2 (p - 1/2)^2`, so the exact input term there is `2 mu (1 - 2 H)`,
    not the `2 mu (1 - H)` this body carries. The two differ by `2 mu H`, which
    is O(mu) per step. This body's term is the INFINITE-ALLELES one, which is
    what the docstring above declares -- a new mutation is always a novel allele,
    so a homozygote becomes heterozygous with probability `2 mu` -- and on the
    matching oracle it is correct.

    Both candidates were carried through so the data chose rather than the
    argument: the biallelic term reaches 2.84 sems and 11.2% relative on the same
    trajectories where this body reaches 1.01 sems and 6.5%. That is a
    preference, not an exclusion, and it is stated as one.

    The reason this needed iterating to see: an O(mu) error per step hides under
    the noise of a single generation. `hetStepWithMutation` was re-measured on
    the infinite-alleles oracle in the same battery and holds at 0.71 sems, so
    its status survives -- but it survives by re-measurement, not by inheritance.

    A THIRD RECORD, and which oracle it ran against. `simcov/ledger.json` carries
    a FALSIFIED verdict on this name at 65.48 sems, battery `traj`, regime "run
    forward from H_0 for the full trajectory, no re-anchoring on the simulation at
    intermediate generations". Compounding is not what fails it: the run tabulated
    above also compounds, fifteen generations from a measured start, and reaches
    1.01 sems. The oracle is what differs. `battery_traj.py` mutates by
    `p = p (1 - mu) + (1 - p) mu`, which is BIALLELIC two-way mutation, so its
    exact input term is the `2 mu (1 - 2 H)` derived two paragraphs up and not the
    `2 mu (1 - H)` this body carries. The 65.48 is therefore a third measurement of
    the SAME regime mismatch the 632-sems biallelic run found, taken over 50 to 200
    generations where an O(mu) per-step error has room to accumulate -- it is not an
    independent failure, and it is not a falsification of the infinite-alleles claim
    the docstring above makes. Recorded here because the ledger row carries the
    regime but not the mutation model, and the two readings are opposite.

    The engine runs about 1% hot against the known plateau (`H = 0.4489` and
    `0.5044` measured against `theta/(1+theta) = 0.4444` and `0.5000`), which is
    the same systematic `ia_engine.selftest` reports, so it is disclosed rather
    than absorbed: it is a tenth of the gap being resolved here. -/
noncomputable def hetMutationDriftRecurrence (Ne mu : ℝ) (H₀ : ℝ) : ℕ → ℝ
  | 0 => H₀
  | t + 1 => (1 - 1 / (2 * Ne)) * hetMutationDriftRecurrence Ne mu H₀ t +
              2 * mu * (1 - hetMutationDriftRecurrence Ne mu H₀ t)

/-- **Algebraic verification of the fixed point.**
    If we start at H* = θ/(1+θ), one step of the recurrence returns H*.
    This proves H* is indeed a fixed point — the equilibrium heterozygosity. -/
theorem hetMutationDrift_fixed_point (Ne mu : ℝ)
    (hNe : 0 < Ne) (hmu : 0 < mu) :
    hetMutationDriftRecurrence Ne mu (Portability.hetMutationFloor Ne mu) 1 =
      Portability.hetMutationFloor Ne mu := by
  simp [hetMutationDriftRecurrence, Portability.hetMutationFloor]
  -- We need: (1 - 1/(2Ne)) * (4Neμ/(1+4Neμ)) + 2μ * (1 - 4Neμ/(1+4Neμ))
  --        = 4Neμ/(1+4Neμ)
  have hθ : 0 < 4 * Ne * mu := by positivity
  have hden : (1 + 4 * Ne * mu) ≠ 0 := by linarith
  have hNe2 : (2 * Ne) ≠ 0 := by linarith
  field_simp
  ring_nf

/-- **The fixed point is unique in [0,1].**
    For any H in [0,1] satisfying f(H) = H, we must have H = θ/(1+θ).
    We prove this by direct algebra: the fixed-point equation is linear in H. -/
theorem hetMutationDrift_fixed_point_unique (Ne mu H : ℝ)
    (hNe : 0 < Ne) (hmu : 0 < mu)
    (h_fixed : (1 - 1 / (2 * Ne)) * H + 2 * mu * (1 - H) = H) :
    H = Portability.hetMutationFloor Ne mu := by
  unfold Portability.hetMutationFloor
  -- From the fixed-point equation:
  -- H - (1 - 1/(2Ne))H - 2μ(1-H) = 0
  -- H × [1 - (1 - 1/(2Ne)) + 2μ] = 2μ
  -- H × [1/(2Ne) + 2μ] = 2μ
  -- H = 2μ / (1/(2Ne) + 2μ) = 4Neμ / (1 + 4Neμ)
  have hNe2 : (2 * Ne) ≠ 0 := by linarith
  have hθ : 0 < 4 * Ne * mu := by positivity
  have hden : (1 + 4 * Ne * mu) ≠ 0 := by linarith
  have hcoeff : 0 < 1 / (2 * Ne) + 2 * mu := by positivity
  -- Rearrange h_fixed: H * (1/(2Ne) + 2μ) = 2μ
  have h_rearranged : H * (1 / (2 * Ne) + 2 * mu) = 2 * mu := by
    field_simp at h_fixed ⊢
    linarith
  -- Solve for H
  have h_solve : H = 2 * mu / (1 / (2 * Ne) + 2 * mu) := by
    field_simp at h_rearranged ⊢
    linarith
  -- Now show 2μ / (1/(2Ne) + 2μ) = 4Neμ / (1 + 4Neμ)
  rw [h_solve]
  field_simp
  ring

/-- **Derive Fst_eq = 1/(1+θ) from the equilibrium heterozygosity.**
    Since H* = θ/(1+θ) and Fst = 1 - H* (for biallelic loci where H_max = 1),
    we get Fst_eq = 1 - θ/(1+θ) = 1/(1+θ).

    This is Wright's classical result, but *derived* from the recurrence
    rather than postulated. -/
theorem fstEquilibrium_derived (Ne mu : ℝ) (hNe : 0 < Ne) (hmu : 0 < mu) :
    1 - Portability.hetMutationFloor Ne mu = 1 / (1 + 4 * Ne * mu) := by
  unfold Portability.hetMutationFloor
  have hθ : 0 < 4 * Ne * mu := by positivity
  have hden : (1 + 4 * Ne * mu) ≠ 0 := by linarith
  field_simp
  ring

/-- **The equilibrium derived from the recurrence agrees with `fstMutationDriftEquilibrium`.** -/
theorem fstEquilibrium_derived_consistent (Ne mu : ℝ)
    (hNe : 0 < Ne) (hmu : 0 < mu) :
    1 - Portability.hetMutationFloor Ne mu = fstMutationDriftEquilibrium (4 * Ne * mu) := by
  rw [fstEquilibrium_derived Ne mu hNe hmu]
  unfold fstMutationDriftEquilibrium Descent.Core.fstFromFlow
  rfl

/-- **Equilibrium heterozygosity is in (0, 1) for positive parameters.** -/
theorem hetEquilibrium_pos (Ne mu : ℝ) (hNe : 0 < Ne) (hmu : 0 < mu) :
    0 < Portability.hetMutationFloor Ne mu := by
  unfold Portability.hetMutationFloor
  positivity

theorem hetEquilibrium_lt_one (Ne mu : ℝ) (hNe : 0 < Ne) (hmu : 0 < mu) :
    Portability.hetMutationFloor Ne mu < 1 := by
  unfold Portability.hetMutationFloor
  rw [div_lt_one (by positivity)]
  linarith

/-- **Equilibrium Fst is in (0, 1) for positive parameters.** -/
theorem fstEquilibrium_derived_pos (Ne mu : ℝ) (hNe : 0 < Ne) (hmu : 0 < mu) :
    0 < 1 - Portability.hetMutationFloor Ne mu := by
  linarith [hetEquilibrium_lt_one Ne mu hNe hmu]

theorem fstEquilibrium_derived_lt_one (Ne mu : ℝ) (hNe : 0 < Ne) (hmu : 0 < mu) :
    1 - Portability.hetMutationFloor Ne mu < 1 := by
  linarith [hetEquilibrium_pos Ne mu hNe hmu]

/-- **Larger θ → lower equilibrium Fst** (derived version).
    More mutation (or larger Ne) means more diversity maintained against drift. -/
theorem fstEquilibrium_derived_decreases (Ne₁ Ne₂ mu : ℝ)
    (hNe₁ : 0 < Ne₁) (hNe₂ : 0 < Ne₂) (hmu : 0 < mu)
    (h_lt : Ne₁ < Ne₂) :
    1 - Portability.hetMutationFloor Ne₂ mu < 1 - Portability.hetMutationFloor Ne₁ mu := by
  -- Equivalent to hetMutationFloor Ne₁ mu < hetMutationFloor Ne₂ mu
  -- i.e., 4Ne₁μ/(1+4Ne₁μ) < 4Ne₂μ/(1+4Ne₂μ)
  unfold Portability.hetMutationFloor
  have h₁ : 0 < 1 + 4 * Ne₁ * mu := by positivity
  have h₂ : 0 < 1 + 4 * Ne₂ * mu := by positivity
  rw [sub_lt_sub_iff_left]
  rw [div_lt_div_iff₀ h₁ h₂]
  nlinarith

end FstDerivationFromDrift

end Descent.PopGen
