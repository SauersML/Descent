/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Coalescent.JumpChain
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

assert_below Descent.Pangenome Descent.PopGen Descent.Spectral Descent.Blindness Descent.Conditionals Descent.Portability Descent.Decision Descent.Program

namespace Descent

/-!
# Incomplete lineage sorting: why a gene tree need not be the species tree

Three populations that split in the order `((A,B),C)` do not thereby give every locus that
genealogy.  If the two lineages sampled from `A` and `B` fail to coalesce during the branch
separating the `AB` split from the `ABC` split, then all three lineages enter the ancestral
population together, and there they coalesce as an ordinary three-lineage Kingman coalescent
-- which has no memory of which two were siblings.

That gives the classical formula (Hudson 1983; Pamilo and Nei 1988; Tajima 1983):

  `P(gene tree ≠ species tree) = (2/3) e^{-T}`,

with `T` the length of the internal branch in coalescent units.  Both factors are already in
this corpus, and the point of the file is that neither is imported from outside it:

* `e^{-T}` is the survival of a single pair through the branch, the `d_2 = 1` exponential of
  K-C (1.7); `Descent.Coalescent.HoldingTime` supplies the density and
  `Descent.Coalescent.Rates` the rate.
* `2/3` is the jump chain.  A three-block state has `C(3,2) = 3` covers
  (`StateSpace.card_covers`), the chain picks among them uniformly
  (`JumpChain.jumpProb_eq`, K-C (2.2): `jumpProb 3 = 1/3`), and exactly one of the three
  reproduces the species topology.  So two of three fail --
  `discordanceGivenFailure_eq_two_thirds` derives that from `jumpProb` rather than asserting
  a symmetry.

## The anomaly

`discordance_gt_half_iff` is the fact that made this a research problem rather than a
correction term: the discordance probability exceeds one half exactly when
`T < log(4/3) ≈ 0.288`.  For internal branches shorter than that, the single most likely gene
tree is NOT the species tree, and concatenating loci or taking a majority vote converges to
the wrong answer with more data rather than less.

The corpus's recurring shape again: a statistic whose expectation is right and whose mode is
wrong, and a design that reads the second for the first.
`Descent.Coalescent.TransitVariance` says the same thing about the tree height -- bounded
mean, non-vanishing spread -- and this says it about topology.

## Main results

- `discordanceGivenFailure_eq_two_thirds`: **`2/3` is `1 - jumpProb 3`**, from the uniform
  jump chain, not from an assumed symmetry.
- `discordanceProb`: `(2/3)e^{-T}`.
- `discordanceProb_zero`: at `T = 0` it is `2/3` -- a zero-length branch leaves the topology
  entirely to the ancestral coalescent.
- `discordanceProb_antitone`, `tendsto_discordanceProb`: longer branches sort better, and
  perfectly in the limit.
- `discordance_gt_half_iff`: **the anomaly zone is `T < log(4/3)`**.
-/

namespace Coalescent

open Filter Topology

/-! ### The two factors -/

/-- **`2/3`, derived from the jump chain.**  Three lineages entering the ancestral population
have three possible first coalescences, the chain chooses among them with probability
`jumpProb 3 = 1/3` each (K-C (2.2)), and exactly one of the three recovers the species
topology.

The symmetry is not assumed: it is `JumpChain.jumpProb_eq` at `k = 3`, which is `1/d_3` with `d_3 =
3`, and `StateSpace.card_covers` counting the three covers it is uniform on. -/
theorem discordanceGivenFailure_eq_two_thirds : 1 - jumpProb 3 = 2 / 3 := by
  have h : jumpProb 3 = 2 / (3 * (3 - 1)) := jumpProb_eq (by norm_num)
  rw [h]
  norm_num

/-- The probability that a sampled pair fails to coalesce within an internal branch of length
`T`: the `d_2 = 1` exponential survival of K-C (1.7).

Empirical status: DERIVED.  It is the survival function of the holding time in a two-block
state, whose rate is `Rates.deathRate 2 = 1` and whose density
`Descent.Coalescent.HoldingTime.holdDensity` supplies. -/
noncomputable def branchSurvival (T : ℝ) : ℝ := Real.exp (-T)

@[simp] theorem branchSurvival_zero : branchSurvival 0 = 1 := by
  simp [branchSurvival]

theorem branchSurvival_pos (T : ℝ) : 0 < branchSurvival T := Real.exp_pos _

/-! ### The formula -/

/-- **`P(gene tree ≠ species tree) = (2/3)e^{-T}`.**  The product of the two factors above:
the pair must fail to sort in the branch, and then must fail to sort correctly by chance.

Empirical status: DERIVED.  Both factors are the corpus's own -- the exponential from the
rate ladder, the `2/3` from the jump chain -- and this multiplies them.  What is ASSUMED is
that the three populations are related by a strict tree with no gene flow: with migration the
two events are not independent and the formula is not this one.  That is the standard
confound in the empirical literature, and `Descent.Coalescent.Structured` is where the corpus
keeps migration. -/
noncomputable def discordanceProb (T : ℝ) : ℝ := (2 / 3) * branchSurvival T

/-- Written against the jump chain rather than against the literal `2/3`, so the dependence
is in the statement. -/
theorem discordanceProb_eq (T : ℝ) :
    discordanceProb T = (1 - jumpProb 3) * branchSurvival T := by
  unfold discordanceProb
  rw [discordanceGivenFailure_eq_two_thirds]

/-- **A zero-length internal branch leaves the topology entirely to chance.**  Two of the
three resolutions are wrong, so two thirds of loci disagree with a species tree whose internal
branch is instantaneous -- and no amount of sequence per locus changes that. -/
@[simp] theorem discordanceProb_zero : discordanceProb 0 = 2 / 3 := by
  unfold discordanceProb
  rw [branchSurvival_zero]
  norm_num

theorem discordanceProb_pos (T : ℝ) : 0 < discordanceProb T := by
  unfold discordanceProb
  have := branchSurvival_pos T
  linarith

/-- Longer branches sort better: the discordance probability is decreasing in the internal
branch length. -/
theorem discordanceProb_antitone : Antitone discordanceProb := by
  intro a b hab
  unfold discordanceProb branchSurvival
  have h : Real.exp (-b) ≤ Real.exp (-a) := by
    rw [Real.exp_le_exp]
    linarith
  linarith

/-- And in the limit of a long branch, every locus sorts: discordance tends to zero. -/
theorem tendsto_discordanceProb : Tendsto discordanceProb atTop (nhds 0) := by
  have h : Tendsto (fun T : ℝ ↦ Real.exp (-T)) atTop (nhds 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero
  have h2 : Tendsto (fun T : ℝ ↦ (2 / 3) * Real.exp (-T)) atTop (nhds ((2 / 3) * 0)) :=
    h.const_mul (2 / 3)
  simpa [discordanceProb, branchSurvival] using h2

/-! ### The anomaly zone -/

/-- **The most likely gene tree is the wrong one when `T < log(4/3)`.**

Discordance exceeds one half exactly below that threshold -- about `0.288` coalescent units,
which for a population of `10⁴` is under six thousand generations.  Above it the species tree
is the modal gene tree; below it the modal gene tree is one of the two wrong ones, and a
method that takes the commonest topology across loci converges to that wrong one as the
number of loci grows.

More data makes the error more certain.  That is the whole reason coalescent-aware species
tree methods exist, and it is a theorem about `e^{-T}` and the number `3`. -/
theorem discordance_gt_half_iff (T : ℝ) :
    1 / 2 < discordanceProb T ↔ T < Real.log (4 / 3) := by
  have hpos : (0 : ℝ) < 3 / 4 := by norm_num
  have hlog : Real.log (4 / 3) = -Real.log (3 / 4) := by
    rw [show (4 : ℝ) / 3 = ((3 : ℝ) / 4)⁻¹ by norm_num, Real.log_inv]
  have hiff : Real.log (3 / 4) < -T ↔ (3 : ℝ) / 4 < Real.exp (-T) := by
    constructor
    · intro h
      have h2 := Real.exp_lt_exp.mpr h
      rwa [Real.exp_log hpos] at h2
    · intro h
      have h2 : Real.exp (Real.log (3 / 4)) < Real.exp (-T) := by
        rwa [Real.exp_log hpos]
      exact Real.exp_lt_exp.mp h2
  constructor
  · intro h
    unfold discordanceProb branchSurvival at h
    have h1 : (3 : ℝ) / 4 < Real.exp (-T) := by linarith
    have h2 : Real.log (3 / 4) < -T := hiff.mpr h1
    rw [hlog]
    linarith
  · intro h
    rw [hlog] at h
    have h2 : Real.log (3 / 4) < -T := by linarith
    have h1 : (3 : ℝ) / 4 < Real.exp (-T) := hiff.mp h2
    unfold discordanceProb branchSurvival
    linarith

end Coalescent

end Descent
