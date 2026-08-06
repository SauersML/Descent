/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.Linkage.Chain

assert_below Descent.PopGen Descent.Spectral Descent.Blindness Descent.Conditionals
assert_below Descent.Portability Descent.Decision Descent.Program

/-!
# The barrier under an arbitrary panel-frequency law

`Descent.Pangenome.Linkage.Barrier` weighs every panel thread equally.  Real panels do not:
haplotype frequencies are wildly uneven, and a builder who wants to know what a graph forgets
about the population wants the population's own law, not the counting measure on the sample.

The law does not depend on the weighting.  For any strictly positive law `p` on the panel,

    H(p) + ∑_j H_p(J ∣ S_j)  ≤  log |Ω|,

and the uniform statement is this one at `p = 1/m`, which `condIdentityLoss_uniform` and
`panelEntropy_uniform` prove rather than assert.

## What replaces what

* `stateMass p s h` — the mass `p` puts on `h`'s graph state.
* `condIdentityLoss p s` — `H_p(J ∣ S)`, the identity the interface forgets when threads are
  weighed by `p`.  At uniform `p` it is `identityLoss`.
* `panelEntropy p` — `H(p)`, which replaces `log m`.
* `stateEntropy p s` — `H(S)`, and `condIdentityLoss_add_stateEntropy` proves the chain rule
  `H(J ∣ S) + H(S) = H(J)` for these definitions, so the name `H(J ∣ S)` the whole group uses
  is discharged rather than asserted.
* `freePotential p v` — `∑ p log (v/p)`, the potential the chain carries.  At `v = 1` it is
  `panelEntropy p`, which is why the induction starts where it does.

## Why this proof is not the uniform proof again

The uniform argument carries a geometric mean and gains an interface's loss by the
arithmetic–geometric mean inequality inside each fiber.  Under a general law the same step is
a relative entropy between `p` and `v`, each renormalised on the fiber, and the inequality
that makes it work is Gibbs — `Descent.Pangenome.Linkage.Interface.sum_mul_log_div_nonneg`,
the same lemma the imbalance tax uses.  Both are the one Jensen inequality of `Interface`
under different weights, which is the sense in which the group has a single analytic input.

## Empirical status

None.  `p` is an arbitrary law on a finite set and every statement is an inequality about it.
Which law a real panel has is a measurement; that the barrier holds for whichever one it is,
is what is proved here.

## What is not claimed

`p` is required strictly positive, which the manuscript's statement handles by restricting to
the support.  Nothing here optimises over `p`: the frequency-aware capacity that maximises the
bound, its uniqueness and its fixed-point equation are not formalised.
-/

namespace Descent.Pangenome.Linkage

open Finset

universe u

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

/-! ### The weighted measurements -/

/-- The mass the law `p` puts on the graph state that `h` occupies. -/
noncomputable def stateMass (p : ι → ℝ) (s : ι → ι) (h : ι) : ℝ := ∑ g ∈ fiber s h, p g

/-- `H_p(J ∣ S)`: the thread identity an interface forgets, weighing threads by `p`. -/
noncomputable def condIdentityLoss (p : ι → ℝ) (s : ι → ι) : ℝ :=
  ∑ h : ι, p h * Real.log (stateMass p s h / p h)

/-- `H(p)`, the identity the panel carries before any interface has merged anything. -/
noncomputable def panelEntropy (p : ι → ℝ) : ℝ := ∑ h : ι, p h * Real.log (1 / p h)

/-- The potential the chain carries: `∑ p log (v/p)`. -/
noncomputable def freePotential (p v : ι → ℝ) : ℝ := ∑ h : ι, p h * Real.log (v h / p h)

theorem stateMass_pos {p : ι → ℝ} (hp : ∀ h, 0 < p h) (s : ι → ι) (h : ι) :
    0 < stateMass p s h :=
  Finset.sum_pos (fun g _ ↦ hp g) ⟨h, self_mem_fiber s h⟩

omit [DecidableEq ι] in
theorem freePotential_one (p : ι → ℝ) : freePotential p (fun _ ↦ 1) = panelEntropy p := rfl

/-! ### One interface, under a general law -/

/-- **Crossing an interface pays its weighted identity loss into the potential.**

Inside one graph state this is Gibbs' inequality between `p` and `v`, each renormalised on
the state's fiber; the fiberwise regrouping that turns per-state statements into per-panel
ones is the same `sum_fiberwise` the width identity uses. -/
theorem freePotential_step {p v : ι → ℝ} (hp : ∀ h, 0 < p h) (hv : ∀ h, 0 < v h)
    (s : ι → ι) :
    freePotential p v + condIdentityLoss p s
      ≤ freePotential p fun h ↦ ∑ g ∈ fiber s h, v g := by
  have hM : ∀ h : ι, 0 < stateMass p s h := stateMass_pos hp s
  have hA : ∀ h : ι, 0 < ∑ g ∈ fiber s h, v g := fun h ↦
    Finset.sum_pos (fun g _ ↦ hv g) ⟨h, self_mem_fiber s h⟩
  -- The gap, term by term.
  have hterm : ∀ h : ι,
      p h * Real.log ((p h / stateMass p s h) / (v h / ∑ g ∈ fiber s h, v g))
        = p h * Real.log ((∑ g ∈ fiber s h, v g) / p h)
          - p h * Real.log (v h / p h) - p h * Real.log (stateMass p s h / p h) := by
    intro h
    rw [Real.log_div (ne_of_gt (div_pos (hp h) (hM h))) (ne_of_gt (div_pos (hv h) (hA h))),
      Real.log_div (ne_of_gt (hp h)) (ne_of_gt (hM h)),
      Real.log_div (ne_of_gt (hv h)) (ne_of_gt (hA h)),
      Real.log_div (ne_of_gt (hA h)) (ne_of_gt (hp h)),
      Real.log_div (ne_of_gt (hv h)) (ne_of_gt (hp h)),
      Real.log_div (ne_of_gt (hM h)) (ne_of_gt (hp h))]
    ring
  -- The gap is nonnegative, one graph state at a time.
  have hstate : ∀ a ∈ Finset.univ.image s,
      0 ≤ ∑ h ∈ stateFiber s a,
        p h * Real.log ((p h / stateMass p s h) / (v h / ∑ g ∈ fiber s h, v g)) := by
    intro a ha
    obtain ⟨h₀, hh₀⟩ := Finset.card_pos.mp (card_stateFiber_pos ha)
    have hfib : ∀ h ∈ stateFiber s a, fiber s h = stateFiber s a := by
      intro h hh
      simp only [mem_stateFiber] at hh
      simp [fiber, hh]
    have hPpos : 0 < ∑ g ∈ stateFiber s a, p g :=
      Finset.sum_pos (fun g _ ↦ hp g) ⟨h₀, hh₀⟩
    have hVpos : 0 < ∑ g ∈ stateFiber s a, v g :=
      Finset.sum_pos (fun g _ ↦ hv g) ⟨h₀, hh₀⟩
    have hrw : ∀ h ∈ stateFiber s a,
        p h * Real.log ((p h / stateMass p s h) / (v h / ∑ g ∈ fiber s h, v g))
          = (∑ g ∈ stateFiber s a, p g)
            * ((p h / ∑ g ∈ stateFiber s a, p g)
              * Real.log ((p h / ∑ g ∈ stateFiber s a, p g)
                / (v h / ∑ g ∈ stateFiber s a, v g))) := by
      intro h hh
      rw [stateMass, hfib h hh]
      field_simp
    rw [Finset.sum_congr rfl hrw, ← Finset.mul_sum]
    refine mul_nonneg hPpos.le ?_
    refine sum_mul_log_div_nonneg (stateFiber s a) _ _
      (fun h _ ↦ div_pos (hp h) hPpos) ?_ (fun h _ ↦ div_pos (hv h) hVpos) ?_
    · simp only [div_eq_mul_inv, ← Finset.sum_mul]
      exact mul_inv_cancel₀ (ne_of_gt hPpos)
    · simp only [div_eq_mul_inv, ← Finset.sum_mul]
      exact mul_inv_cancel₀ (ne_of_gt hVpos)
  have hsum : 0 ≤ ∑ h : ι,
      p h * Real.log ((p h / stateMass p s h) / (v h / ∑ g ∈ fiber s h, v g)) := by
    rw [← sum_fiberwise s fun h ↦
      p h * Real.log ((p h / stateMass p s h) / (v h / ∑ g ∈ fiber s h, v g))]
    exact Finset.sum_nonneg hstate
  rw [Finset.sum_congr rfl fun h _ ↦ hterm h, Finset.sum_sub_distrib,
    Finset.sum_sub_distrib] at hsum
  rw [freePotential, freePotential, condIdentityLoss]
  linarith

omit [DecidableEq ι] in
/-- **The potential is at most the logarithm of the total.**  Jensen, with the law `p` as the
weights and `v/p` as the values. -/
theorem freePotential_le_log_sum {p v : ι → ℝ} (hp : ∀ h, 0 < p h) (hp1 : ∑ h : ι, p h = 1)
    (hv : ∀ h, 0 < v h) : freePotential p v ≤ Real.log (∑ h : ι, v h) := by
  have hJ := sum_mul_log_le_log_sum Finset.univ p (fun h ↦ v h / p h)
    (fun h _ ↦ (hp h).le) hp1 (fun h _ ↦ div_pos (hv h) (hp h))
  have hcancel : ∑ h : ι, p h * (v h / p h) = ∑ h : ι, v h :=
    Finset.sum_congr rfl fun h _ ↦ by
      have hph : p h ≠ 0 := ne_of_gt (hp h)
      field_simp
  rw [hcancel] at hJ
  exact hJ

/-! ### The barrier -/

/-- Linkage-entropy pressure under the law `p`. -/
noncomputable def condLinkagePressure (p : ι → ℝ) (c : Chain ι) : ℝ :=
  (c.map (condIdentityLoss p)).sum

theorem condLinkagePressure_cons (p : ι → ℝ) (s : ι → ι) (c : Chain ι) :
    condLinkagePressure p (s :: c) = condIdentityLoss p s + condLinkagePressure p c := by
  simp [condLinkagePressure]

theorem condLinkagePressure_le_freePotential {p : ι → ℝ} (hp : ∀ h, 0 < p h) (c : Chain ι) :
    panelEntropy p + condLinkagePressure p c
      ≤ freePotential p fun h ↦ (derivationCount c h : ℝ) := by
  induction c with
  | nil => simp [condLinkagePressure, derivationCount, freePotential_one]
  | cons s c ih =>
    have hpos : ∀ h : ι, (0 : ℝ) < (derivationCount c h : ℝ) := fun h ↦ by
      exact_mod_cast derivationCount_pos c h
    have hstep := freePotential_step hp hpos s
    have heq : (fun h ↦ ∑ g ∈ fiber s h, (derivationCount c g : ℝ))
        = fun h ↦ (derivationCount (s :: c) h : ℝ) := by
      funext h
      rw [derivationCount, Nat.cast_sum]
    rw [heq] at hstep
    rw [condLinkagePressure_cons]
    linarith

/-- **The linkage–entropy barrier, under any panel-frequency law.**  This is the manuscript's
statement: for a random thread `J ∼ p` with graph state `S_j` at interface `j`,
`H(J) + ∑_j H(J ∣ S_j) ≤ log |Ω|`. -/
theorem panelEntropy_add_condLinkagePressure_le {p : ι → ℝ} (hp : ∀ h, 0 < p h)
    (hp1 : ∑ h : ι, p h = 1) (c : Chain ι) :
    panelEntropy p + condLinkagePressure p c ≤ Real.log ((mosaics c).card : ℝ) := by
  have hpos : ∀ h : ι, (0 : ℝ) < (derivationCount c h : ℝ) := fun h ↦ by
    exact_mod_cast derivationCount_pos c h
  have hsum : ((mosaics c).card : ℝ) = ∑ h : ι, (derivationCount c h : ℝ) := by
    rw [card_mosaics, Nat.cast_sum]
  have hchain := condLinkagePressure_le_freePotential hp c
  have hJ := freePotential_le_log_sum hp hp1 hpos
  rw [hsum]
  linarith

/-! ### Definitional fidelity

Every docstring in this group reads `identityLoss` and `condIdentityLoss` as the conditional
entropy `H(J ∣ S)`.  That reading is a claim about definitions, and a claim about definitions
left in prose is exactly the kind a formalisation is supposed to stop making.  The two results
here discharge it: what is defined is what it is named for. -/

/-- `H(S)`: the entropy of the graph state a `p`-random thread occupies. -/
noncomputable def stateEntropy (p : ι → ℝ) (s : ι → ι) : ℝ :=
  ∑ a ∈ Finset.univ.image s,
    (∑ g ∈ stateFiber s a, p g) * Real.log (1 / ∑ g ∈ stateFiber s a, p g)

/-- **What is called `H(J ∣ S)` is `H(J ∣ S)`.**  The textbook chain rule for a state that is a
function of the thread, `H(J ∣ S) + H(S) = H(J)`, holds for the definitions actually used in
this group — not for a paraphrase of them. -/
theorem condIdentityLoss_add_stateEntropy {p : ι → ℝ} (hp : ∀ h, 0 < p h) (s : ι → ι) :
    condIdentityLoss p s + stateEntropy p s = panelEntropy p := by
  have hM : ∀ h : ι, 0 < stateMass p s h := stateMass_pos hp s
  have hterm : ∀ h : ι, p h * Real.log (stateMass p s h / p h)
      = p h * Real.log (stateMass p s h) + p h * Real.log (1 / p h) := by
    intro h
    rw [Real.log_div (ne_of_gt (hM h)) (ne_of_gt (hp h)), one_div, Real.log_inv]
    ring
  have hmass : ∑ h : ι, p h * Real.log (stateMass p s h)
      = ∑ a ∈ Finset.univ.image s,
          (∑ g ∈ stateFiber s a, p g) * Real.log (∑ g ∈ stateFiber s a, p g) := by
    rw [← sum_fiberwise s fun h ↦ p h * Real.log (stateMass p s h)]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    have hconst : ∀ h ∈ stateFiber s a, p h * Real.log (stateMass p s h)
        = p h * Real.log (∑ g ∈ stateFiber s a, p g) := by
      intro h hh
      simp only [mem_stateFiber] at hh
      rw [stateMass, fiber, hh]
    rw [Finset.sum_congr rfl hconst, ← Finset.sum_mul]
  have hzero : (∑ a ∈ Finset.univ.image s,
        (∑ g ∈ stateFiber s a, p g) * Real.log (∑ g ∈ stateFiber s a, p g))
      + stateEntropy p s = 0 := by
    rw [stateEntropy, ← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun a _ ↦ ?_
    rw [one_div, Real.log_inv]
    ring
  rw [condIdentityLoss, Finset.sum_congr rfl fun h _ ↦ hterm h, Finset.sum_add_distrib, hmass,
    panelEntropy]
  linarith

/-! ### The uniform statement is this one

`Descent.Pangenome.Linkage.Barrier` is the case `p = 1/m`, and these two identities are the
proof of that reading rather than an assertion of it. -/

omit [DecidableEq ι] in
theorem panelEntropy_uniform [Nonempty ι] :
    panelEntropy (fun _ : ι ↦ (Fintype.card ι : ℝ)⁻¹) = Real.log (Fintype.card ι : ℝ) := by
  have hm : (0 : ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  rw [panelEntropy]
  have hterm : ∀ h : ι, (Fintype.card ι : ℝ)⁻¹ * Real.log (1 / (Fintype.card ι : ℝ)⁻¹)
      = (Fintype.card ι : ℝ)⁻¹ * Real.log (Fintype.card ι : ℝ) := by
    intro h
    have h1 : (1 : ℝ) / (Fintype.card ι : ℝ)⁻¹ = (Fintype.card ι : ℝ) := by
      rw [one_div, inv_inv]
    rw [h1]
  rw [Finset.sum_congr rfl fun h _ ↦ hterm h, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    ← mul_assoc, mul_inv_cancel₀ (ne_of_gt hm), one_mul]

theorem condIdentityLoss_uniform [Nonempty ι] (s : ι → ι) :
    condIdentityLoss (fun _ : ι ↦ (Fintype.card ι : ℝ)⁻¹) s = identityLoss s := by
  have hm : (0 : ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  rw [condIdentityLoss, identityLoss, Finset.mul_sum]
  refine Finset.sum_congr rfl fun h _ ↦ ?_
  have hmass : stateMass (fun _ : ι ↦ (Fintype.card ι : ℝ)⁻¹) s h
      = (fiberCard s h : ℝ) * (Fintype.card ι : ℝ)⁻¹ := by
    rw [stateMass, Finset.sum_const, nsmul_eq_mul, fiberCard]
  have hm0 : (Fintype.card ι : ℝ) ≠ 0 := ne_of_gt hm
  have hcancel : ((fiberCard s h : ℝ) * (Fintype.card ι : ℝ)⁻¹) / (Fintype.card ι : ℝ)⁻¹
      = (fiberCard s h : ℝ) := by
    field_simp
  rw [hmass, hcancel]

/-- **The uniform reading, discharged.**  `identityLoss s + H(S) = log m` — which is the
`H(J ∣ S) = H(J) - H(S)` that `Descent.Pangenome.Linkage.Interface` names it for, at the
uniform panel the rest of the group is stated over. -/
theorem identityLoss_add_stateEntropy [Nonempty ι] (s : ι → ι) :
    identityLoss s + stateEntropy (fun _ : ι ↦ (Fintype.card ι : ℝ)⁻¹) s
      = Real.log (Fintype.card ι : ℝ) := by
  have hm : (0 : ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  rw [← condIdentityLoss_uniform s, ← panelEntropy_uniform]
  exact condIdentityLoss_add_stateEntropy (fun _ ↦ inv_pos.mpr hm) s

end Descent.Pangenome.Linkage
