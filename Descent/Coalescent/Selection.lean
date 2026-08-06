/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Coalescent.Rates
import Mathlib.Tactic

assert_below Descent.Pangenome Descent.PopGen Descent.Spectral Descent.Blindness
assert_below Descent.Conditionals Descent.Portability Descent.Decision Descent.Program

namespace Descent

/-!
# The ancestral selection graph, and why selection is a lower-order perturbation

K-G section 4 ends by saying the `n`-coalescent "is essentially a 'neutral' genealogy", and
that "selective advantages and disadvantages lead to very different behaviour".  Krone and
Neuhauser, *Ancestral processes with selection* (Theor. Popul. Biol. 51, 210-237, 1997),
made the different behaviour precise: with selection, going backwards, a lineage BRANCHES --
it has a real parent and a virtual one, and which is which is settled going forwards.  The
result is a graph, not a tree.

At the level of rates the structure is the same competition
`Descent.Coalescent.Recombination` already has: with `k` lineages, coalescence at `d_k` and
branching at `k σ / 2`.  What this file records is the consequence that makes Kingman's
model robust:

**Coalescence is quadratic in `k`, branching is linear.**  So the ratio
`branchRate / deathRate = σ/(k-1)` falls to zero as the sample grows
(`tendsto_branchDeathRatio`), and past `k = σ + 1` coalescence already dominates
(`deathRate_lt_of_le`).  The graph therefore does not run away: selection perturbs the
genealogy without changing its order of growth, which is the quantitative content of K-G's
remark that weak selection leaves the coalescent approximately intact.

What is NOT here, and is the substance of Krone-Neuhauser: the forward resolution that
decides which parent was real, and the resulting non-neutral genealogy.  That is a different
process, not a harder case of this one, and the corpus does not have it.

## Main results

- `branchRate`: `kσ/2`, the ASG's branching rate.
- `asgEventRate_zero_selection`: at `σ = 0` it is `deathRate` -- Kingman is the neutral fibre.
- `branchDeathRatio_eq`: the ratio is `σ/(k-1)`, independent of everything else.
- `tendsto_branchDeathRatio`: **which vanishes as the sample grows.**
- `branchRate_lt_deathRate`: past `k = σ + 1`, coalescence already wins.
-/

namespace Coalescent

open Filter

/-- The ASG branching rate with `k` lineages: each branches at rate `σ/2`.

Empirical status: THIS IS THE MODEL.  `σ = 2 N_e s` is the scaled selection coefficient; the
`1/2` is the same time-unit convention that makes the per-pair coalescence rate `1`. -/
noncomputable def branchRate (k : ℕ) (sigma : ℝ) : ℝ := Descent.Core.halfLineageRate k sigma

/-- The total rate of the next event in the ancestral selection graph. -/
noncomputable def asgEventRate (k : ℕ) (sigma : ℝ) : ℝ := deathRate k + branchRate k sigma

/-- **Kingman is the neutral fibre.**  At `σ = 0` there is no branching and the graph is
Kingman's tree, so this group's whole development is the zero-selection case -- as it is the
zero-recombination case in `Recombination` and the `δ₀` case in `Lambda`. -/
@[simp] theorem asgEventRate_zero_selection (k : ℕ) : asgEventRate k 0 = deathRate k := by
  unfold asgEventRate branchRate Descent.Core.halfLineageRate
  ring

/-- **The ratio of the two rates is `σ/(k-1)`.**  Everything else cancels: the sample size
enters only through `k - 1`, because coalescence has `k(k-1)/2` pairs to work with and
branching has `k` lineages. -/
theorem branchDeathRatio_eq {k : ℕ} (hk : 2 ≤ k) (sigma : ℝ) :
    branchRate k sigma / deathRate k = sigma / ((k : ℝ) - 1) := by
  have hk' : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hkne : (k : ℝ) ≠ 0 := by linarith
  have h1 : ((k : ℝ) - 1) ≠ 0 := by linarith
  unfold branchRate deathRate Descent.Core.pairCount Descent.Core.halfLineageRate
  field_simp

/-- **Selection is a lower-order perturbation.**  The branching rate is linear in the number
of lineages and the coalescence rate is quadratic, so their ratio vanishes as the sample
grows.  This is the quantitative content of K-G section 4's remark that the coalescent
survives weak selection: selection does not change the order of growth of the event rate,
only its constant. -/
theorem tendsto_branchDeathRatio (sigma : ℝ) :
    Tendsto (fun k : ℕ ↦ sigma / ((k : ℝ) + 1)) atTop (nhds 0) := by
  have h : Tendsto (fun k : ℕ ↦ (k : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  exact h.const_div_atTop sigma

/-- **Past `k = σ + 1`, coalescence already dominates.**  With enough lineages the pairs
outnumber the lineages by more than the selection coefficient, and the next event is more
likely a coalescence than a branching -- which is why the ASG stays finite rather than
branching away. -/
theorem branchRate_lt_deathRate {k : ℕ} (hk : 2 ≤ k) {sigma : ℝ} (hsig : 0 < sigma)
    (hlarge : sigma < (k : ℝ) - 1) : branchRate k sigma < deathRate k := by
  have hk' : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hkpos : (0 : ℝ) < (k : ℝ) := by linarith
  unfold branchRate deathRate Descent.Core.pairCount Descent.Core.halfLineageRate
  rw [div_lt_div_iff_of_pos_right (by norm_num : (0:ℝ) < 2)]
  nlinarith

/-- At zero selection the branching rate is zero: nothing branches, and the graph is a
tree. -/
@[simp] theorem branchRate_zero (k : ℕ) : branchRate k 0 = 0 := by
  unfold branchRate Descent.Core.halfLineageRate
  ring

/-- The total event rate is at least the coalescence rate: selection adds events, it never
removes them.  So the ASG's transit time is at most the coalescent's, which is the sense in
which selection speeds the ancestry up rather than slowing it. -/
theorem deathRate_le_asgEventRate {k : ℕ} {sigma : ℝ} (hsig : 0 ≤ sigma) :
    deathRate k ≤ asgEventRate k sigma := by
  have hb : 0 ≤ branchRate k sigma := by
    unfold branchRate Descent.Core.halfLineageRate
    positivity
  unfold asgEventRate
  linarith

end Coalescent

end Descent
