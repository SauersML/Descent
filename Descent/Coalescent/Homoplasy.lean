/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Layer
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

assert_below Descent.Pangenome Descent.PopGen Descent.Spectral Descent.Blindness
assert_below Descent.Conditionals Descent.Portability Descent.Decision Descent.Program

namespace Descent

/-!
# Infinite sites is a statement about the size of the mutation alphabet

`Descent.Coalescent.SegregatingSites` computes `E(S_n) = θ a_{n-1}` and records, in
`expectedSegregatingSites`'s own empirical status, that the mutation half of that product is
ASSUMED: mutations Poisson along the tree, and **every mutation visible at a fresh site**.
The second clause is the infinite-sites model.  It is stated there as a modelling premise
with no parameter, which makes it look like a yes-or-no assumption a dataset either satisfies
or does not.

It is not.  It is the `k → ∞` end of a one-parameter family, and this file writes down the
parameter.

## The family

Let a lineage mutate at rate `μ` and let each mutation resample the allele uniformly from an
alphabet of `k`.  Then a lineage observed after time `t` is in the state it started in with
probability

  `returnProb k μ t = e^{-μt} + (1 - e^{-μt}) / k`

-- it never mutated, or it mutated and the last resample came home.  The second term is
`homoplasyProb`, and it is exactly identity in state without identity by descent.  Infinite
sites is the claim that this term is zero, and `tendsto_homoplasyProb_atTop` says that
happens in the limit and nowhere else.

**No finite mutation alphabet is homoplasy-free** (`homoplasyProb_pos`), and the size of the
violation is `1/k` to leading order (`homoplasyProb_le_inv`), uniformly in the mutation rate
and the elapsed time.

## Why this is the right parameter for structural variation

The alphabet size is not a property of a species; it is a property of a VARIANT CLASS, and it
ranges over nine orders of magnitude:

* an **inversion** between fixed inverted repeats has `k = 2` -- two orientations, and a
  second inversion restores the first.  `homoplasyProb 2` approaches `1/2`.
* a **copy-number** state at a segmental duplication or a VNTR has `k` in the tens: the
  stepwise mutation walks a small alphabet and returns to it constantly.
* a **mobile element insertion** has `k` of order the number of insertable positions in the
  genome, and precise excision is essentially rate zero.  `homoplasyProb` is then of order
  `10⁻⁹`, which is why mobile-element insertions are used as homoplasy-free phylogenetic
  markers.

That ordering is usually stated as a fact about the biology of each class.  Below it is a
statement about one number, and the classes differ only in what that number is.  The
folklore that "rare genomic changes are homoplasy-free" is then visibly not about rarity:
`homoplasyProb` does not mention the rate `μ` except through `μt`, and at fixed `μt` it is a
function of `k` alone.

## What is NOT here

The continuous-time chain itself.  `returnProb` is written down as the closed form its
two-case decomposition gives, not derived from a generator, so this file assumes the
parent-independent (Jukes-Cantor) resampling law rather than deriving it.  A stepwise law on
a cycle or a line has a different closed form and a different `k`-dependence; what survives
unchanged is the dichotomy, because the return probability of any walk on a FINITE state
space is bounded below and that of an infinitely-branching one is not.

## Main results

- `returnProb`, `homoplasyProb`: the family and its homoplastic part.
- `returnProb_eq_add`: the decomposition that defines them -- never mutated, or came home.
- `homoplasyProb_pos`: **no finite alphabet is homoplasy-free.**
- `homoplasyProb_le_inv`: and the violation is at most `1/k`, uniformly in `μ` and `t`.
- `homoplasyProb_antitone`: a larger alphabet is always safer.
- `tendsto_homoplasyProb_atTop`: **infinite sites is the `k → ∞` limit**, and is attained
  only there.
- `homoplasyProb_two_le_half`: the biallelic case, which is the worst one.
-/

namespace Coalescent

open Filter Topology

/-! ### The family -/

/-- **The chance a lineage is in the state it started in**, after mutating at rate `μ` for
time `t` over an alphabet of `k` alleles resampled uniformly.

Empirical status: THIS IS THE MODEL.  The two-case decomposition is exact given
parent-independent resampling; that a real variant class resamples that way, and that its
alphabet has size `k`, are the empirical claims, and they are claims about the INPUT. -/
noncomputable def returnProb (k : ℕ) (μ t : ℝ) : ℝ :=
  Real.exp (-(μ * t)) + (1 - Real.exp (-(μ * t))) / k

/-- **Identity in state without identity by descent**: the lineage did mutate and came home
anyway.  This is homoplasy, and infinite sites is the assumption that it is zero.

Empirical status: DERIVED.  It is the second summand of `returnProb`, i.e. the probability of
at least one mutation times the chance the last resample returns the original allele. -/
noncomputable def homoplasyProb (k : ℕ) (μ t : ℝ) : ℝ :=
  (1 - Real.exp (-(μ * t))) / k

/-- The decomposition the two definitions are built from: a lineage is home because it never
left, or because it left and returned.  The second term is the whole of the infinite-sites
violation. -/
theorem returnProb_eq_add (k : ℕ) (μ t : ℝ) :
    returnProb k μ t = Real.exp (-(μ * t)) + homoplasyProb k μ t := rfl

/-! ### No finite alphabet is homoplasy-free -/

/-- The mutated-at-all factor is nonnegative exactly when time runs forwards. -/
theorem one_sub_exp_nonneg {μ t : ℝ} (h : 0 ≤ μ * t) : 0 ≤ 1 - Real.exp (-(μ * t)) := by
  have : Real.exp (-(μ * t)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  linarith

theorem homoplasyProb_nonneg {k : ℕ} {μ t : ℝ} (h : 0 ≤ μ * t) :
    0 ≤ homoplasyProb k μ t :=
  div_nonneg (one_sub_exp_nonneg h) (Nat.cast_nonneg k)

/-- **No finite mutation alphabet is homoplasy-free.**  For any positive alphabet size and
any positive elapsed mutation, the chance of returning to the ancestral state despite having
mutated is strictly positive.

This is the exact sense in which infinite sites is unattainable rather than merely
idealised: the assumption is not approximately true for large `k`, it is false for every
`k`, and `homoplasyProb_le_inv` says by how much.

Assumes: `1 ≤ k` and `0 < μ * t`. -/
theorem homoplasyProb_pos {k : ℕ} {μ t : ℝ} (hk : 1 ≤ k) (h : 0 < μ * t) :
    0 < homoplasyProb k μ t := by
  have hexp : Real.exp (-(μ * t)) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  exact div_pos (by linarith) hkpos

/-- **And the violation is at most `1/k`, uniformly in the rate and the elapsed time.**  The
mutation rate cannot make homoplasy worse than the alphabet allows, so `k` alone bounds it --
which is what lets a variant class be ranked by its alphabet without knowing its rate.

The bound needs no hypothesis on `μ * t` at all: `exp` is positive everywhere, so the
numerator never exceeds `1` whatever the rate and however long the process has run.

Assumes: `1 ≤ k`. -/
theorem homoplasyProb_le_inv {k : ℕ} {μ t : ℝ} (hk : 1 ≤ k) :
    homoplasyProb k μ t ≤ 1 / (k : ℝ) := by
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hexp : 0 < Real.exp (-(μ * t)) := Real.exp_pos _
  unfold homoplasyProb
  rw [div_le_div_iff₀ hkpos hkpos]
  nlinarith

/-- **A larger alphabet is always safer.**  Homoplasy is antitone in the alphabet size, at
every rate and every time -- so the ranking of variant classes by `k` is a ranking by
homoplasy and needs no other input.

Assumes: `1 ≤ k`, `k ≤ k'`, and `0 ≤ μ * t`. -/
theorem homoplasyProb_antitone {k k' : ℕ} {μ t : ℝ} (hk : 1 ≤ k) (hkk : k ≤ k')
    (h : 0 ≤ μ * t) : homoplasyProb k' μ t ≤ homoplasyProb k μ t := by
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hk'pos : (0 : ℝ) < (k' : ℝ) := by exact_mod_cast le_trans hk hkk
  have hle : (k : ℝ) ≤ (k' : ℝ) := by exact_mod_cast hkk
  unfold homoplasyProb
  rw [div_le_div_iff₀ hk'pos hkpos]
  exact mul_le_mul_of_nonneg_left hle (one_sub_exp_nonneg h)

/-! ### Infinite sites is the limit, and only the limit -/

/-- **Infinite sites is the `k → ∞` limit.**  The homoplasy term vanishes as the alphabet
grows, at every fixed rate and time -- so the assumption
`Descent.Coalescent.SegregatingSites.expectedSegregatingSites` rests on is the statement that
the mutation alphabet is unbounded, and `homoplasyProb_pos` says it holds nowhere short of
that.

This is what makes infinite sites a PARAMETER rather than a premise: a study can say which
`k` its variant class has and read the error off, instead of asserting a model. -/
theorem tendsto_homoplasyProb_atTop (μ t : ℝ) :
    Tendsto (fun k : ℕ ↦ homoplasyProb k μ t) atTop (𝓝 0) := by
  unfold homoplasyProb
  exact tendsto_const_div_atTop_nhds_zero_nat _

/-- **The biallelic case is the worst one.**  Two states -- an inversion between fixed
inverted repeats, a presence/absence call -- put the homoplasy ceiling at one half, and the
ceiling is approached as mutation accumulates.

No hypothesis on `μ * t` is needed, for the reason `homoplasyProb_le_inv` records. -/
theorem homoplasyProb_two_le_half (μ t : ℝ) : homoplasyProb 2 μ t ≤ 1 / 2 := by
  simpa using homoplasyProb_le_inv (k := 2) (μ := μ) (t := t) (by norm_num)

end Coalescent

end Descent
