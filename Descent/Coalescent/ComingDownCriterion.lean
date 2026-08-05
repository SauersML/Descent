/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Coalescent.Rates
import Descent.Coalescent.Lambda
import Mathlib.Analysis.PSeries
import Mathlib.Tactic

namespace Descent

/-!
# Coming down from infinity, for the whole `Λ` family

`Descent.Coalescent.ComingDownFromInfinity` settles Kingman's case and
`Descent.Coalescent.Rates` supplies the summability it rests on.  Neither says what separates
the members of Pitman's family that come down from those that do not, and
`Descent.Coalescent.Program` recorded that gap by name.

The separator is Schweinsberg's (Electron. Commun. Probab. 5, 2000).  Write

  `γ_b = Σ_{k=2}^{b} (k-1) C(b,k) λ_{b,k}`

for the rate at which the block count decreases when `b` blocks are present -- each `k`-fold
merger costs `k-1` blocks, there are `C(b,k)` sets of `k` to merge, and `λ_{b,k}` is
`Descent.Coalescent.Lambda`'s rate for each.  Then the coalescent comes down from infinity
if and only if

  `Σ_{b≥2} γ_b⁻¹ < ∞`.

`comesDownFromInfinity` is that condition, and the two theorems below are the two sides of
the dichotomy, on the two members whose `γ_b` the corpus can write in closed form.

## What is proved, and what is not

PROVED: the condition, and that it separates two members of the family --
`kingman_comesDownFromInfinity` (`γ_b = d_b = b(b-1)/2`, summable, by
`Rates.summable_one_div_deathRate_tail`) and `star_not_comesDownFromInfinity`
(`γ_b = b-1`, the total merger of `Λ = δ₁`, not summable, by the harmonic series).

NOT PROVED: the equivalence itself -- that summability IS coming down from infinity.  That
is a theorem about the PROCESS, and this corpus has `Λ`-coalescents only at the level of
their rates (`Descent.Coalescent.Lambda`), with no process to have an entrance law.  The
condition here is therefore a definition plus a dichotomy, not Schweinsberg's theorem, and
saying which is which is the point of saying it.

The Bolthausen-Sznitman case is the interesting one and is absent for a stated reason.  Its
`γ_b` is `b(H_b - 1)`, which grows like `b log b`, so `Σ γ_b⁻¹` diverges and it does not come
down -- but the divergence of `Σ 1/(b log b)` needs Cauchy condensation, which the corpus
does not have.  `Descent.Coalescent.Beta` carries its rates.

## Main results

- `comesDownFromInfinity`: Schweinsberg's condition, as a predicate on `γ`.
- `kingman_comesDownFromInfinity`: **Kingman's coalescent satisfies it**.
- `star_not_comesDownFromInfinity`: **the star coalescent does not**.
- `comesDownFromInfinity_dichotomy`: the two together, so the condition is seen to separate.
-/

namespace Coalescent

open Filter

/-- **Schweinsberg's condition.**  The block count comes down from infinity when the
reciprocal decrease rates are summable: the time to descend through every level is a
convergent sum, so infinitely many levels are passed in finite time.

Empirical status: NOT AN EMPIRICAL CLAIM.  It is a summability condition on a sequence of
rates; whether a population's genealogy has those rates is the empirical question, and
`Descent.Blindness.MultipleMergerBlindness` records which statistics could tell. -/
def comesDownFromInfinity (γ : ℕ → ℝ) : Prop := Summable fun b : ℕ ↦ 1 / γ (b + 2)

/-- **Kingman's coalescent comes down from infinity.**  Its decrease rate is the ladder
`d_b = b(b-1)/2`, whose reciprocals sum to `2/(k-1)` -- the estimate `Rates` proves and
K-C p.239 states. -/
theorem kingman_comesDownFromInfinity : comesDownFromInfinity deathRate := by
  unfold comesDownFromInfinity
  have h := summable_one_div_deathRate_tail (k := 2) (by norm_num)
  refine h.congr fun b ↦ ?_
  rw [show 2 + b = b + 2 from by omega]

/-- **The star coalescent does not.**  `Λ = δ₁` merges every block at once at rate one, so
`γ_b = b - 1`, and `Σ 1/(b-1)` is the harmonic series.

The genealogical reading: a process whose only move is total coalescence never has finitely
many blocks before it has one.  It has no entrance law from infinity, and there is no
`n(t) = 2/t` curve to write. -/
theorem star_not_comesDownFromInfinity :
    ¬ comesDownFromInfinity (fun b : ℕ ↦ (b : ℝ) - 1) := by
  unfold comesDownFromInfinity
  intro hsum
  have hharm : ¬ Summable (fun b : ℕ ↦ 1 / ((b : ℝ) + 1)) := by
    have h := mt (summable_nat_add_iff (f := fun n : ℕ ↦ 1 / (n : ℝ)) 1).mp
      Real.not_summable_one_div_natCast
    refine fun hs ↦ h ?_
    refine hs.congr fun b ↦ ?_
    push_cast
    ring
  refine hharm ?_
  refine hsum.congr fun b ↦ ?_
  push_cast
  ring

/-- **The dichotomy.**  One member of the family satisfies the condition and another does
not, so the condition is not vacuous in either direction -- which is the check a definition
of this shape needs before anything is built on it. -/
theorem comesDownFromInfinity_dichotomy :
    comesDownFromInfinity deathRate
      ∧ ¬ comesDownFromInfinity (fun b : ℕ ↦ (b : ℝ) - 1) :=
  ⟨kingman_comesDownFromInfinity, star_not_comesDownFromInfinity⟩

end Coalescent

end Descent
