/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Coalescent.SegregatingSites
import Descent.Pangenome.GraphCoalescent.Reduction

assert_below Descent.PopGen Descent.Spectral Descent.Blindness Descent.Conditionals
assert_below Descent.Portability Descent.Decision Descent.Program

/-!
# What entering at `w` instead of `n` costs, and that it is the identity loss

`Descent.Pangenome.GraphCoalescent.Reduction` identifies the pangenome graph coalescent as
Kingman's, entered at `Linkage.width s`.  Every downstream number therefore moves, and this
file computes two of them exactly.

* **The tree is shallower.**  `E(T_n) - E(T_w) = 2/w - 2/n`, from K-G (5.7) at two
  arguments.  The deficit is nonnegative, and it is zero exactly when the interface forgot
  nothing (`transitDeficit_eq_zero_iff`).
* **`θ` is underestimated.**  A study that reads its segregating sites off the graph and its
  sample size off the panel reports `θ · a_{w-1} / a_{n-1}`, strictly below `θ`
  (`graphWatterson_lt`).  The bias factor is a ratio of harmonic numbers that the graph
  determines and the data do not.

## The bridge that makes this a theorem rather than a caution

`transitDeficit_eq_zero_iff` is the point of the file.  `Descent.Pangenome.Linkage.Interface`
measures an interface by `identityLoss s = H(J ∣ S)`, the nats of haplotype identity the
merge destroys; `Descent.Coalescent.Rates` measures a coalescent by `E(T)`, a time.  They
vanish together, and neither development could say so: the entropy has no time in it and the
time has no interface in it.  What connects them is `Observation.blocks_graphKer`, which says
the width the entropy is denominated in IS the lineage count the time is computed from.

So "the graph forgot something" and "the graph reports a shallower tree" are one statement,
and the width law of `Descent.Pangenome.Linkage.Barrier` prices both.

## Its relation to the gauge defect

`Descent.Pangenome.CoalescentGauge` records a different failure of the same estimator:
`θ_W` moves with the reference tree, because `S` counts cotree edges and the tree is a
choice.  That defect is in the NUMERATOR.  This one is in the DENOMINATOR -- `a_{n-1}` is
evaluated at a sample size the graph does not have.  They are independent, they have opposite
sensitivities, and a study carrying both has no reason to expect them to cancel.

## Main results

- `injective_of_width_eq`, `identityLoss_eq_zero_of_width_eq`,
  `width_eq_of_identityLoss_eq_zero`: full width and zero identity loss are the same
  condition.
- `transitDeficit_eq`: `E(T_n) - E(T_w) = 2/w - 2/n`.
- `transitDeficit_nonneg`, `transitDeficit_pos`: the graph's tree is never deeper, and is
  strictly shallower as soon as the interface merged anything.
- `transitDeficit_eq_zero_iff`: **the bridge.**  The deficit vanishes exactly when
  `identityLoss` does.
- `graphWatterson_eq`: the reported `θ` is `θ · a_{w-1} / a_{n-1}`.
- `graphWatterson_lt`: and it is strictly too small.
-/

namespace Descent.Pangenome.GraphCoalescent

/-! ### Full width and zero identity loss are the same condition -/

/-- An interface occupying `n` states separates every pair of panel haplotypes. -/
theorem injective_of_width_eq {n : ℕ} {s : Fin n → Fin n} (h : Linkage.width s = n) :
    Function.Injective s := by
  have hcard : (Finset.univ.image s).card = (Finset.univ : Finset (Fin n)).card := by
    simpa [Linkage.width, Finset.card_univ] using h
  have hinj := Finset.injOn_of_card_image_eq hcard
  intro x y hxy
  exact hinj (Finset.mem_coe.mpr (Finset.mem_univ x)) (Finset.mem_coe.mpr (Finset.mem_univ y)) hxy

/-- **An interface of full width forgets nothing.**  Every fiber is a singleton, so every
term of `identityLoss` is `log 1`. -/
theorem identityLoss_eq_zero_of_width_eq {n : ℕ} {s : Fin n → Fin n}
    (h : Linkage.width s = n) : Linkage.identityLoss s = 0 := by
  have hinj := injective_of_width_eq h
  have hfib : ∀ x : Fin n, Linkage.fiberCard s x = 1 := by
    intro x
    have hsing : Linkage.fiber s x = {x} := by
      ext y
      simp only [Linkage.mem_fiber, Finset.mem_singleton]
      exact ⟨fun hy ↦ hinj hy, fun hy ↦ by rw [hy]⟩
    rw [Linkage.fiberCard, hsing, Finset.card_singleton]
  simp [Linkage.identityLoss, hfib]

/-- **And an interface that forgets nothing has full width.**  This is the width law of
`Descent.Pangenome.Linkage.Interface` read backwards: `log (m/w) ≤ H(J ∣ S)` forces `w = m`
once the right side is zero, because `log` is strictly monotone. -/
theorem width_eq_of_identityLoss_eq_zero {n : ℕ} {s : Fin n → Fin n} (hn : 0 < n)
    (h : Linkage.identityLoss s = 0) : Linkage.width s = n := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hle : Linkage.width s ≤ n := by simpa using Linkage.width_le_card s
  by_contra hne
  have hlt : Linkage.width s < n := lt_of_le_of_ne hle hne
  have hwpos : 0 < Linkage.width s := Linkage.width_pos s
  have hkey := Linkage.log_card_sub_log_width_le_identityLoss s
  rw [h] at hkey
  have hcast : (Fintype.card (Fin n) : ℝ) = (n : ℝ) := by simp
  rw [hcast] at hkey
  have hlog : Real.log (Linkage.width s : ℝ) < Real.log (n : ℝ) :=
    Real.log_lt_log (by exact_mod_cast hwpos) (by exact_mod_cast hlt)
  linarith

/-! ### The transit-time deficit -/

/-- **What the graph's compression costs in tree depth**: the panel's expected time to a
common ancestor, less the graph's.

Empirical status: DERIVED.  Both terms are `Coalescent.meanTransitTime`, K-G (5.7), off the
rate ladder; the only new content is that the second is evaluated at `Linkage.width s`, which
is `Descent.Pangenome.GraphCoalescent.Reduction`'s theorem and not an assumption here. -/
noncomputable def transitDeficit {n : ℕ} (s : Fin n → Fin n) : ℝ :=
  Coalescent.meanTransitTime n - graphMeanTransitTime s

/-- **The deficit, exactly**: `2/w - 2/n`.

Assumes: `1 ≤ n` and `1 ≤ Linkage.width s`, the nondegeneracy under which K-G (5.7) has its
closed form. -/
theorem transitDeficit_eq {n : ℕ} {s : Fin n → Fin n} (hn : 1 ≤ n)
    (hw : 1 ≤ Linkage.width s) :
    transitDeficit s = 2 / (Linkage.width s : ℝ) - 2 / (n : ℝ) := by
  rw [transitDeficit, Coalescent.meanTransitTime_eq_two_sub hn, graphMeanTransitTime_eq hw]
  ring

/-- **A pangenome graph never reports a deeper tree than the panel has.**  Merging haplotypes
removes lineages, and fewer lineages coalesce sooner.

Assumes: `1 ≤ Linkage.width s`. -/
theorem transitDeficit_nonneg {n : ℕ} {s : Fin n → Fin n} (hw : 1 ≤ Linkage.width s) :
    0 ≤ transitDeficit s := by
  have hle : Linkage.width s ≤ n := by simpa using Linkage.width_le_card s
  have hn : 1 ≤ n := le_trans hw hle
  have h1 : (0 : ℝ) < (Linkage.width s : ℝ) := by exact_mod_cast hw
  have h2 : (Linkage.width s : ℝ) ≤ (n : ℝ) := by exact_mod_cast hle
  have h3 : (0 : ℝ) < (n : ℝ) := lt_of_lt_of_le h1 h2
  have hkey : (2 : ℝ) / (n : ℝ) ≤ 2 / (Linkage.width s : ℝ) := by
    rw [div_le_div_iff h3 h1]
    linarith
  rw [transitDeficit_eq hn hw]
  linarith

/-- And strictly shallower as soon as the interface merged anything.

Assumes: `1 ≤ Linkage.width s` and `Linkage.width s < n`. -/
theorem transitDeficit_pos {n : ℕ} {s : Fin n → Fin n} (hw : 1 ≤ Linkage.width s)
    (hlt : Linkage.width s < n) : 0 < transitDeficit s := by
  have hn : 1 ≤ n := le_trans hw (le_of_lt hlt)
  have h1 : (0 : ℝ) < (Linkage.width s : ℝ) := by exact_mod_cast hw
  have h2 : (Linkage.width s : ℝ) < (n : ℝ) := by exact_mod_cast hlt
  have h3 : (0 : ℝ) < (n : ℝ) := lt_trans h1 h2
  have hkey : (2 : ℝ) / (n : ℝ) < 2 / (Linkage.width s : ℝ) := by
    rw [div_lt_div_iff h3 h1]
    linarith
  rw [transitDeficit_eq hn hw]
  linarith

/-- **The bridge.**  A pangenome graph reports the panel's own coalescent time exactly when
the interface it was built at forgot no haplotype identity.  One side is an entropy in nats
and the other is a time in coalescent units; they vanish together because both are read off
the same `w`.

Assumes: `0 < n`, so that the panel is nonempty and both quantities are defined. -/
theorem transitDeficit_eq_zero_iff {n : ℕ} {s : Fin n → Fin n} (hn : 0 < n) :
    transitDeficit s = 0 ↔ Linkage.identityLoss s = 0 := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hw : 1 ≤ Linkage.width s := Linkage.width_pos s
  constructor
  · intro h
    have h1 : (0 : ℝ) < (Linkage.width s : ℝ) := by exact_mod_cast hw
    have h3 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    rw [transitDeficit_eq hn hw] at h
    have h' : (2 : ℝ) / (Linkage.width s : ℝ) = 2 / (n : ℝ) := by linarith
    rw [div_eq_div_iff h1.ne' h3.ne'] at h'
    have hwn : (Linkage.width s : ℝ) = (n : ℝ) := by linarith
    exact identityLoss_eq_zero_of_width_eq (by exact_mod_cast hwn)
  · intro h
    have hwidth := width_eq_of_identityLoss_eq_zero hn h
    rw [transitDeficit, graphMeanTransitTime, hwidth]
    ring

/-! ### The estimator a study actually computes

Watterson's estimator divides the observed segregating sites by `a_{n-1}`.  A study working
from a pangenome graph observes the graph's sites -- there are `E(S_w)` of them, because the
graph's coalescent has `w` lineages -- and divides by the `n` it wrote down for its panel.
The result is `θ` scaled by a ratio of harmonic numbers.

`Descent.Coalescent.SegregatingSites.wattersonEstimator_unbiased` is the statement that this
is exact when the two sample sizes agree.  What follows is what happens when they do not. -/

/-- **What a study reports for `θ`** when it reads its segregating sites off a pangenome
graph and its sample size off the panel that built the graph.

Empirical status: DERIVED.  `Coalescent.expectedSegregatingSites` at the graph's sample size
is `Descent.Pangenome.GraphCoalescent.Reduction`'s identification of that sample size;
`Coalescent.wattersonEstimator` at `n` is what the study does.  This file introduces neither
and composes them. -/
noncomputable def graphWatterson {n : ℕ} (θ : Descent.Core.Theta) (s : Fin n → Fin n) : ℝ :=
  Coalescent.wattersonEstimator (Coalescent.expectedSegregatingSites θ (Linkage.width s)) n

/-- **The bias factor is a ratio of harmonic numbers**: the report is
`θ · a_{w-1} / a_{n-1}`.  Both indices are integers the study has; only one of them is a
property of the data. -/
theorem graphWatterson_eq {n : ℕ} (θ : Descent.Core.Theta) (s : Fin n → Fin n) :
    graphWatterson θ s = θ.value *
      (Coalescent.harmonicSum (Linkage.width s - 1) / Coalescent.harmonicSum (n - 1)) := by
  unfold graphWatterson Coalescent.wattersonEstimator
  rw [Coalescent.expectedSegregatingSites_eq]
  ring

/-- **A study reading its sample size off the panel underestimates `θ`.**  Strictly, whenever
the graph occupies at least two states and fewer than `n` of them -- which is every graph
that compressed anything and did not collapse the panel to a point.

Assumes: `0 < θ.value`, `2 ≤ Linkage.width s`, `Linkage.width s < n`. -/
theorem graphWatterson_lt {n : ℕ} {θ : Descent.Core.Theta} (hθ : 0 < θ.value)
    {s : Fin n → Fin n} (hw : 2 ≤ Linkage.width s) (hlt : Linkage.width s < n) :
    graphWatterson θ s < θ.value := by
  have hn : 2 ≤ n := by omega
  have hpos : 0 < Coalescent.harmonicSum (n - 1) := Coalescent.harmonicSum_pos_of_two_le hn
  have hmono : Coalescent.harmonicSum (Linkage.width s - 1)
      < Coalescent.harmonicSum (n - 1) := Coalescent.harmonicSum_strictMono (by omega)
  have hratio : Coalescent.harmonicSum (Linkage.width s - 1)
      / Coalescent.harmonicSum (n - 1) < 1 := (div_lt_one hpos).mpr hmono
  rw [graphWatterson_eq]
  calc θ.value * (Coalescent.harmonicSum (Linkage.width s - 1)
        / Coalescent.harmonicSum (n - 1))
      < θ.value * 1 := mul_lt_mul_of_pos_left hratio hθ
    _ = θ.value := mul_one _

/-- **The complementary positive result.**  A faithful interface costs nothing: the reported
`θ` is `θ`.  This is `wattersonEstimator_unbiased` reached through the graph, and it says
the bias above is a property of the compression rather than of the estimator.

Assumes: `2 ≤ n` and `Linkage.width s = n`, i.e. the graph merges no two panel
haplotypes. -/
theorem graphWatterson_of_width_eq {n : ℕ} (θ : Descent.Core.Theta) {s : Fin n → Fin n}
    (hn : 2 ≤ n) (h : Linkage.width s = n) : graphWatterson θ s = θ.value := by
  rw [graphWatterson, h]
  exact Coalescent.wattersonEstimator_unbiased hn θ

end Descent.Pangenome.GraphCoalescent
