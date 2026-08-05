/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Coalescent.Rates
import Descent.Coalescent.Lambda
import Descent.Coalescent.Beta
import Descent.Coalescent.BranchLength
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

The Bolthausen-Sznitman case is the interesting one, and its rate is now computed rather
than quoted.  `bolthausenSznitman_decrease_term` shows each `k`-fold merger contributes
exactly `b/k` to `γ_b` -- the binomial, the `k-1` blocks lost, and Beta's
`(k-2)!(b-k)!/(b-1)!` collapse to that -- so

  `γ_b = Σ_{k=2}^{b} b/k = b (H_b - 1)`,

which is `sum_bolthausenSznitman_rate` against `BranchLength.harmonicSum`.  It grows like
`b log b`, so `Σ γ_b⁻¹` diverges and the Bolthausen-Sznitman coalescent does not come down
from infinity.  THAT last step is what is still missing: the divergence of `Σ 1/(b log b)`
needs Cauchy condensation and a logarithmic bound on `H_b`, neither of which the corpus
has.  The rate is settled; the summability of its reciprocal is not.

## Main results

- `comesDownFromInfinity`: Schweinsberg's condition, as a predicate on `γ`.
- `kingman_comesDownFromInfinity`: **Kingman's coalescent satisfies it**.
- `star_not_comesDownFromInfinity`: **the star coalescent does not**.
- `comesDownFromInfinity_dichotomy`: the two together, so the condition is seen to separate.
- `bolthausenSznitman_decrease_term`: **each `k`-merger contributes `b/k`**.
- `sum_bolthausenSznitman_rate`: hence `γ_b = b(H_b - 1)`.
-/

namespace Coalescent

open Filter Nat

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

/-! ### The Bolthausen-Sznitman decrease rate -/

/-- **Each `k`-fold merger contributes `b/k` to the decrease rate.**  Written at `k = j+2`
and `b = j+2+r` so no truncated subtraction appears: the `k-1` blocks lost, the `C(b,k)` sets
that could merge, and `Descent.Coalescent.Beta`'s `(k-2)!(b-k)!/(b-1)!` collapse to a single
ratio.

Summing over `k` gives `γ_b = b(H_b - 1)`, which is why the Bolthausen-Sznitman coalescent
sits at the boundary: `b log b` is just fast enough for the reciprocals to diverge. -/
theorem bolthausenSznitman_decrease_term (j r : ℕ) :
    ((j : ℝ) + 1) * (((j + 2 + r).choose (j + 2) : ℕ) : ℝ)
        * betaCoalescentRate 1 (j + 2 + r) (j + 2)
      = ((j : ℝ) + 2 + (r : ℝ)) / ((j : ℝ) + 2) := by
  have hk : 2 ≤ j + 2 := by omega
  have hkb : j + 2 ≤ j + 2 + r := by omega
  have hsub1 : j + 2 - 2 = j := by omega
  have hsub2 : j + 2 + r - (j + 2) = r := by omega
  have hsub3 : j + 2 + r - 1 = j + 1 + r := by omega
  have hrate := bolthausenSznitmanRate_eq hk hkb
  rw [hsub1, hsub2, hsub3] at hrate
  rw [hrate]
  have hC : (((j + 2 + r).choose (j + 2) : ℕ) : ℝ) * (((j + 2)! : ℕ) : ℝ) * ((r ! : ℕ) : ℝ)
      = (((j + 2 + r)! : ℕ) : ℝ) := by
    have h := Nat.choose_mul_factorial_mul_factorial hkb
    rw [hsub2] at h
    exact_mod_cast congrArg (Nat.cast : ℕ → ℝ) h
  have hf2 : (((j + 2)! : ℕ) : ℝ) = ((j : ℝ) + 2) * (((j + 1)! : ℕ) : ℝ) := by
    rw [show j + 2 = (j + 1) + 1 from rfl, Nat.factorial_succ]
    push_cast
    ring
  have hf1 : (((j + 1)! : ℕ) : ℝ) = ((j : ℝ) + 1) * ((j ! : ℕ) : ℝ) := by
    rw [Nat.factorial_succ]
    push_cast
    ring
  have hf3 : (((j + 2 + r)! : ℕ) : ℝ)
      = ((j : ℝ) + 2 + (r : ℝ)) * (((j + 1 + r)! : ℕ) : ℝ) := by
    rw [show j + 2 + r = (j + 1 + r) + 1 from by omega, Nat.factorial_succ]
    push_cast
    ring
  have hposj : (0 : ℝ) < ((j ! : ℕ) : ℝ) := by exact_mod_cast Nat.factorial_pos j
  have hposr : (0 : ℝ) < ((r ! : ℕ) : ℝ) := by exact_mod_cast Nat.factorial_pos r
  have hposN : (0 : ℝ) < (((j + 1 + r)! : ℕ) : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have hj2 : (0 : ℝ) < (j : ℝ) + 2 := by positivity
  rw [hf2, hf1, hf3] at hC
  have hNne : (((j + 1 + r)! : ℕ) : ℝ) ≠ 0 := ne_of_gt hposN
  have hj2ne : ((j : ℝ) + 2) ≠ 0 := ne_of_gt hj2
  field_simp
  linear_combination hC

/-- **`γ_b = b (H_b - 1)`.**  The sum of the per-merger contributions, against
`Descent.Coalescent.BranchLength.harmonicSum` -- the same harmonic number that measures the
tree's total length, appearing now as a rate of descent. -/
theorem sum_bolthausenSznitman_rate (m : ℕ) :
    ∑ j ∈ Finset.range m, ((m : ℝ) + 1) / ((j : ℝ) + 2)
      = ((m : ℝ) + 1) * (harmonicSum (m + 1) - 1) := by
  have hh : harmonicSum (m + 1) = (∑ j ∈ Finset.range m, 1 / ((j : ℝ) + 2)) + 1 := by
    unfold harmonicSum
    rw [Finset.sum_range_succ']
    have hcongr : ∑ j ∈ Finset.range m, (1 : ℝ) / (((j + 1 : ℕ) : ℝ) + 1)
        = ∑ j ∈ Finset.range m, 1 / ((j : ℝ) + 2) := by
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      push_cast
      ring
    rw [hcongr]
    norm_num
  rw [hh]
  have hpull : ((m : ℝ) + 1) * ((∑ j ∈ Finset.range m, 1 / ((j : ℝ) + 2)) + 1 - 1)
      = ((m : ℝ) + 1) * ∑ j ∈ Finset.range m, 1 / ((j : ℝ) + 2) := by ring
  rw [hpull, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  ring

end Coalescent

end Descent
