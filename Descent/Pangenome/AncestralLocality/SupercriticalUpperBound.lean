/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.AncestralLocality.BreadthFirstDomination

assert_below Descent.PopGen Descent.Spectral Descent.Blindness Descent.Conditionals
assert_below Descent.Portability Descent.Decision Descent.Program

/-!
# The supercritical upper bound, without the giant component theorem

For `α > 1` and `s = giantFraction α`, the note's (6.2) says that `|C_m(A)|/m ⇒ s` with probability
`1 - (1 - s)^k`. This file proves the upper half of that statement outright, with no hypothesis
carrying the Erdős–Rényi theorem. For every `ε > 0` and queries of at most `k` features,
`limsup_m P(|Reach(A)| ≥ ε m) ≤ 1 - (1 - s)^k` (`limsup_graphProb_card_reach_ge_le`), and for at
most one feature `limsup_m P(|Reach(i)| ≥ ε m) ≤ s`
(`limsup_graphProb_card_reach_singleton_ge_le`). The eventual forms are
`eventually_graphProb_card_reach_ge_le` and `eventually_graphProb_card_reach_singleton_ge_le`.

**The route.** `Descent.Pangenome.AncestralLocality.BreadthFirstDomination` gives, for every
generation `g`, `P(|Reach(A)| ≥ ε m) ≤ 1 - q_g^|A| + |A| Σ_{t<g} α^t / (ε m)` in `G(m, α/m)`, where
`q_g = gwExtinct m (α/m) g` is the extinction probability by generation `g` of the Galton–Watson
process with `Binomial(m, α/m)` offspring. The Markov term vanishes as `m → ∞`. The binomial
extinction probabilities are eventually at least the Poisson ones `x_g` (`poissonExtinct`,
`eventually_poissonExtinct_sub_le_gwExtinct`), because `(1 + t/m)^m → e^t`. The Poisson iteration
increases (`poissonExtinct_monotone`) and stays at most `1 - s` (`poissonExtinct_mem`). Its limit is
a fixed point of `x ↦ e^{-α (1 - x)}` below `1`, hence `1 - s` by the uniqueness of the positive
root of the survival equation (`tendsto_poissonExtinct`). Finally `a^k - b^k ≤ k (a - b)` on
`[0, 1]` (`pow_sub_pow_le_mul_sub`) turns `q_g ≥ 1 - s - 2δ` into `q_g^k ≥ (1 - s)^k - 2kδ`.

Scope. Only the upper half of (6.2) is proved. The matching lower bounds, that a component of size
near `s m` exists and that `k` roots touch it with probability `1 - (1 - s)^k`, are not, so this
does not discharge `GiantComponentLaw α`; the two-sided limit law in the sibling modules still
assumes it. The comparison is with Galton–Watson survival generation by generation, not with the
total progeny.

## Empirical status

None. The bodies are probabilities under `G(m, α/m)`, extinction iterations and their limits.
Nothing is measured.
-/

namespace Descent.Pangenome.AncestralLocality

open Finset Filter Topology
open scoped Classical

noncomputable section

/-! ### The Poisson extinction iteration -/

/-- **Extinction by generation `g` of the Poisson(`α`) branching process**: `x₀ = 0` and
`x_{g+1} = e^{-α (1 - x_g)}`, the Poisson generating function at `x_g`. -/
def poissonExtinct (α : ℝ) : ℕ → ℝ
  | 0 => 0
  | g + 1 => Real.exp (-(α * (1 - poissonExtinct α g)))

/-- No process is extinct at generation zero. -/
theorem poissonExtinct_zero (α : ℝ) : poissonExtinct α 0 = 0 :=
  rfl

/-- The Poisson extinction recursion. -/
theorem poissonExtinct_succ (α : ℝ) (g : ℕ) :
    poissonExtinct α (g + 1) = Real.exp (-(α * (1 - poissonExtinct α g))) :=
  rfl

/-- **For `α > 1` the Poisson extinction iteration stays in `[0, 1 - s]`**, `s = giantFraction α`:
`1 - s` is a fixed point of `x ↦ e^{-α (1 - x)}` and the map is increasing. -/
theorem poissonExtinct_mem {α : ℝ} (hα : 1 < α) (g : ℕ) :
    0 ≤ poissonExtinct α g ∧ poissonExtinct α g ≤ 1 - giantFraction α := by
  obtain ⟨hs0, hs1⟩ := giantFraction_mem_Ioo hα
  have hfix : Real.exp (-(α * giantFraction α)) = 1 - giantFraction α := by
    have h := survivalMap_giantFraction α
    unfold survivalMap at h
    linarith
  induction g with
  | zero =>
    rw [poissonExtinct_zero]
    exact ⟨le_rfl, by linarith⟩
  | succ g ih =>
    refine ⟨(Real.exp_pos _).le, ?_⟩
    rw [poissonExtinct_succ, ← hfix]
    exact Real.exp_le_exp.mpr (by nlinarith [ih.2])

/-- **The Poisson extinction iteration increases.** -/
theorem poissonExtinct_monotone {α : ℝ} (hα : 0 ≤ α) : Monotone (poissonExtinct α) := by
  refine monotone_nat_of_le_succ fun g ↦ ?_
  induction g with
  | zero =>
    rw [poissonExtinct_succ, poissonExtinct_zero]
    exact (Real.exp_pos _).le
  | succ g ih =>
    show Real.exp (-(α * (1 - poissonExtinct α g))) ≤
      Real.exp (-(α * (1 - poissonExtinct α (g + 1))))
    exact Real.exp_le_exp.mpr (by nlinarith)

/-- **The Poisson extinction iteration tends to `1 - s`** for `α > 1`: its limit is a fixed point
of `x ↦ e^{-α (1 - x)}` at most `1 - s`, and the only one is `1 - s`. -/
theorem tendsto_poissonExtinct {α : ℝ} (hα : 1 < α) :
    Tendsto (poissonExtinct α) atTop (𝓝 (1 - giantFraction α)) := by
  obtain ⟨hs0, hs1⟩ := giantFraction_mem_Ioo hα
  have hmono := poissonExtinct_monotone (by linarith : (0 : ℝ) ≤ α)
  have hbdd : BddAbove (Set.range (poissonExtinct α)) :=
    ⟨1 - giantFraction α, by rintro _ ⟨g, rfl⟩; exact (poissonExtinct_mem hα g).2⟩
  have hL := tendsto_atTop_ciSup hmono hbdd
  have hLle : ⨆ g, poissonExtinct α g ≤ 1 - giantFraction α :=
    ciSup_le fun g ↦ (poissonExtinct_mem hα g).2
  have hcont : Continuous fun x : ℝ ↦ Real.exp (-(α * (1 - x))) := by fun_prop
  have hfix : Real.exp (-(α * (1 - ⨆ g, poissonExtinct α g))) = ⨆ g, poissonExtinct α g := by
    have h1 : Tendsto (fun g ↦ poissonExtinct α (g + 1)) atTop (𝓝 (⨆ g, poissonExtinct α g)) :=
      (tendsto_add_atTop_iff_nat 1).mpr hL
    have h2 : Tendsto (fun g ↦ poissonExtinct α (g + 1)) atTop
        (𝓝 (Real.exp (-(α * (1 - ⨆ g, poissonExtinct α g))))) :=
      (hcont.tendsto _).comp hL
    exact tendsto_nhds_unique h2 h1
  have hs' : survivalMap α (1 - ⨆ g, poissonExtinct α g) = 1 - ⨆ g, poissonExtinct α g := by
    unfold survivalMap
    rw [hfix]
  have heq := eq_giantFraction hα (by linarith) hs'
  rw [← heq, sub_sub_cancel]
  exact hL

/-- **The binomial extinction probabilities are eventually at least the Poisson ones.** For every
generation `g` and `η > 0`, eventually `x_g - η ≤ q_g` for `Binomial(m, α/m)` offspring. -/
theorem eventually_poissonExtinct_sub_le_gwExtinct {α : ℝ} (hα : 1 < α) (g : ℕ) {η : ℝ}
    (hη : 0 < η) : ∀ᶠ m : ℕ in atTop, poissonExtinct α g - η ≤ gwExtinct m (α / m) g := by
  induction g generalizing η with
  | zero =>
    filter_upwards with m
    rw [poissonExtinct_zero, gwExtinct_zero]
    linarith
  | succ g ih =>
    have hα0 : 0 < α := by linarith
    obtain ⟨hx0, hx1⟩ := poissonExtinct_mem hα g
    obtain ⟨hs0, hs1⟩ := giantFraction_mem_Ioo hα
    obtain ⟨η', hη'0, hαη'⟩ : ∃ η' : ℝ, 0 < η' ∧ α * η' = η / 2 :=
      ⟨η / (2 * α), div_pos hη (by linarith), by
        rw [mul_div_assoc', mul_comm 2 α, mul_div_mul_left η 2 hα0.ne']⟩
    have hlim := Real.tendsto_one_add_div_pow_exp (-(α * (1 - poissonExtinct α g + η')))
    have hev1 := (tendsto_order.1 hlim).1
      (Real.exp (-(α * (1 - poissonExtinct α g + η'))) - η / 2) (by linarith)
    have hev3 := tendsto_natCast_atTop_atTop.eventually_ge_atTop
      (α * (1 - poissonExtinct α g + η'))
    filter_upwards [hev1, ih hη'0, hev3, eventually_gt_atTop 0] with m h1 h2 h3 h4
    have hm : (0 : ℝ) < m := Nat.cast_pos.mpr h4
    have hαm : 0 ≤ α / m := div_nonneg hα0.le hm.le
    have hdiv : -(α * (1 - poissonExtinct α g + η')) / m =
        -(α / m * (1 - poissonExtinct α g + η')) := by ring
    have hbase : 1 + -(α * (1 - poissonExtinct α g + η')) / m ≤
        1 - α / m * (1 - gwExtinct m (α / m) g) := by
      have hy : 1 - gwExtinct m (α / m) g ≤ 1 - poissonExtinct α g + η' := by linarith
      have := mul_le_mul_of_nonneg_left hy hαm
      linarith
    have hbase0 : 0 ≤ 1 + -(α * (1 - poissonExtinct α g + η')) / m := by
      have := (div_le_one hm).mpr h3
      have hdiv' : α / m * (1 - poissonExtinct α g + η') = α * (1 - poissonExtinct α g + η') / m :=
        by ring
      linarith
    have hpow : (1 + -(α * (1 - poissonExtinct α g + η')) / m) ^ m ≤
        gwExtinct m (α / m) (g + 1) := by
      rw [gwExtinct_succ]
      exact pow_le_pow_left₀ hbase0 hbase m
    have hexp : Real.exp (-(α * (1 - poissonExtinct α g))) - η / 2 ≤
        Real.exp (-(α * (1 - poissonExtinct α g + η'))) := by
      have hsplit : -(α * (1 - poissonExtinct α g + η')) =
          -(α * (1 - poissonExtinct α g)) + -(α * η') := by ring
      rw [hsplit, Real.exp_add]
      have h5 := Real.add_one_le_exp (-(α * η'))
      have h6 : Real.exp (-(α * (1 - poissonExtinct α g))) ≤ 1 :=
        Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hα0.le (by linarith)))
      have h7 := Real.exp_pos (-(α * (1 - poissonExtinct α g)))
      nlinarith [mul_nonneg (sub_nonneg.mpr h5) h7.le,
        mul_nonneg (sub_nonneg.mpr h6) (mul_pos hα0 hη'0).le]
    rw [poissonExtinct_succ]
    linarith

/-- `a^k - b^k ≤ k (a - b)` for `0 ≤ b ≤ a ≤ 1`. -/
theorem pow_sub_pow_le_mul_sub {a b : ℝ} (hb : 0 ≤ b) (hba : b ≤ a) (ha : a ≤ 1) (k : ℕ) :
    a ^ k - b ^ k ≤ k * (a - b) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h1 : b ^ k ≤ a ^ k := pow_le_pow_left₀ hb hba k
    have h2 : a ^ k ≤ 1 := pow_le_one₀ (hb.trans hba) ha
    have h3 := mul_le_mul_of_nonneg_right h2 (sub_nonneg.mpr hba)
    have h4 := mul_le_mul_of_nonneg_left (hba.trans ha) (sub_nonneg.mpr h1)
    push_cast
    rw [pow_succ, pow_succ]
    nlinarith

/-! ### The upper bound -/

/-- **The supercritical upper bound for `k` roots, eventually.** For `α > 1`, queries `A m` of at
most `k` features, `ε > 0` and `η > 0`, eventually `P(|Reach(A)| ≥ ε m) ≤ 1 - (1 - s)^k + η`, with
`s = giantFraction α`. No giant component theorem is assumed. -/
theorem eventually_graphProb_card_reach_ge_le {α : ℝ} (hα : 1 < α) {k : ℕ}
    (A : ∀ m : ℕ, Finset (Fin m)) (hA : ∀ m, (A m).card ≤ k) {ε : ℝ} (hε : 0 < ε) {η : ℝ}
    (hη : 0 < η) :
    ∀ᶠ m : ℕ in atTop, graphProb m (α / m)
        (fun E ↦ ε * m ≤ ((reach (edgeGraph E) (A m)).card : ℝ)) ≤
      1 - (1 - giantFraction α) ^ k + η := by
  obtain ⟨hs0, hs1⟩ := giantFraction_mem_Ioo hα
  have hα0 : 0 < α := by linarith
  have hk1 : (0 : ℝ) < 3 * (k + 1) := by positivity
  obtain ⟨δ, hδ0, hkδ⟩ : ∃ δ : ℝ, 0 < δ ∧ 2 * (k : ℝ) * δ ≤ 2 * η / 3 :=
    ⟨η / (3 * (k + 1)), div_pos hη hk1, by
      rw [mul_div_assoc', div_le_div_iff₀ hk1 (by norm_num)]
      nlinarith⟩
  obtain ⟨g, hg⟩ := ((tendsto_order.1 (tendsto_poissonExtinct hα)).1
    (1 - giantFraction α - δ) (by linarith)).exists
  have hev2 := (tendsto_order.1 (tendsto_const_div_atTop_nhds_zero_nat
    ((k : ℝ) * (∑ t ∈ range g, α ^ t) / ε))).2 (η / 3) (by linarith)
  filter_upwards [eventually_poissonExtinct_sub_le_gwExtinct hα g hδ0, hev2,
    tendsto_natCast_atTop_atTop.eventually_ge_atTop α, eventually_gt_atTop 0]
    with m h1 h2 h3 h4
  have hm : (0 : ℝ) < m := Nat.cast_pos.mpr h4
  have hp0 : 0 ≤ α / m := div_nonneg hα0.le hm.le
  have hp1 : α / m ≤ 1 := (div_le_one hm).mpr h3
  have hK : 0 < ε * m := mul_pos hε hm
  have hfin := graphProb_card_reach_ge_le hp0 hp1 (A m) g hK
  rw [div_mul_cancel₀ α hm.ne'] at hfin
  obtain ⟨hy0, hy1⟩ := gwExtinct_mem_Icc (m := m) hp0 hp1 g
  have hyk : gwExtinct m (α / m) g ^ k ≤ gwExtinct m (α / m) g ^ (A m).card :=
    pow_le_pow_of_le_one hy0 hy1 (hA m)
  have hyk2 : (1 - giantFraction α) ^ k - 2 * k * δ ≤ gwExtinct m (α / m) g ^ k := by
    have h2kδ : 0 ≤ 2 * (k : ℝ) * δ :=
      mul_nonneg (mul_nonneg zero_le_two (Nat.cast_nonneg k)) hδ0.le
    rcases le_or_gt (1 - giantFraction α) (gwExtinct m (α / m) g) with hle | hlt
    · have := pow_le_pow_left₀ (by linarith) hle k
      linarith
    · have hb := pow_sub_pow_le_mul_sub hy0 hlt.le (by linarith) k
      have hdiff : 1 - giantFraction α - gwExtinct m (α / m) g ≤ 2 * δ := by linarith
      have := mul_le_mul_of_nonneg_left hdiff (Nat.cast_nonneg k)
      linarith
  have hsum : (A m).card * (∑ t ∈ range g, α ^ t) / (ε * m) ≤ η / 3 := by
    have hsum0 : 0 ≤ ∑ t ∈ range g, α ^ t := sum_nonneg fun t _ ↦ pow_nonneg hα0.le t
    have hAk : ((A m).card : ℝ) ≤ k := by exact_mod_cast hA m
    have hle : (A m).card * (∑ t ∈ range g, α ^ t) / (ε * m) ≤
        (k : ℝ) * (∑ t ∈ range g, α ^ t) / ε / m := by
      rw [div_div]
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hAk hsum0) hK.le
    linarith
  linarith

/-- **The supercritical upper bound for one root, eventually**: for queries of at most one
feature, eventually `P(|Reach(i)| ≥ ε m) ≤ s + η`. -/
theorem eventually_graphProb_card_reach_singleton_ge_le {α : ℝ} (hα : 1 < α)
    (A : ∀ m : ℕ, Finset (Fin m)) (hA : ∀ m, (A m).card ≤ 1) {ε : ℝ} (hε : 0 < ε) {η : ℝ}
    (hη : 0 < η) :
    ∀ᶠ m : ℕ in atTop, graphProb m (α / m)
        (fun E ↦ ε * m ≤ ((reach (edgeGraph E) (A m)).card : ℝ)) ≤ giantFraction α + η := by
  filter_upwards [eventually_graphProb_card_reach_ge_le hα A hA hε hη] with m hm
  rw [pow_one, sub_sub_cancel] at hm
  exact hm

/-- **The supercritical upper bound for `k` roots**: for `α > 1` and queries of at most `k`
features, `limsup_m P(|Reach(A)| ≥ ε m) ≤ 1 - (1 - s)^k`, with `s = giantFraction α`. -/
theorem limsup_graphProb_card_reach_ge_le {α : ℝ} (hα : 1 < α) {k : ℕ}
    (A : ∀ m : ℕ, Finset (Fin m)) (hA : ∀ m, (A m).card ≤ k) {ε : ℝ} (hε : 0 < ε) :
    limsup (fun m : ℕ ↦ graphProb m (α / m)
        (fun E ↦ ε * m ≤ ((reach (edgeGraph E) (A m)).card : ℝ))) atTop ≤
      1 - (1 - giantFraction α) ^ k := by
  have hα0 : 0 ≤ α := by linarith
  have hcobdd : IsCoboundedUnder (· ≤ ·) atTop (fun m : ℕ ↦ graphProb m (α / m)
      (fun E ↦ ε * m ≤ ((reach (edgeGraph E) (A m)).card : ℝ))) := by
    refine isCoboundedUnder_le_of_eventually_le atTop (x := 0) ?_
    filter_upwards [tendsto_natCast_atTop_atTop.eventually_ge_atTop α, eventually_gt_atTop 0]
      with m h3 h4
    exact graphProb_nonneg (div_nonneg hα0 (Nat.cast_nonneg m))
      ((div_le_one (Nat.cast_pos.mpr h4)).mpr h3) _
  refine le_of_forall_pos_le_add fun η hη ↦ ?_
  exact limsup_le_of_le hcobdd (eventually_graphProb_card_reach_ge_le hα A hA hε hη)

/-- **The supercritical upper bound for one root**: for queries of at most one feature,
`limsup_m P(|Reach(i)| ≥ ε m) ≤ s`. -/
theorem limsup_graphProb_card_reach_singleton_ge_le {α : ℝ} (hα : 1 < α)
    (A : ∀ m : ℕ, Finset (Fin m)) (hA : ∀ m, (A m).card ≤ 1) {ε : ℝ} (hε : 0 < ε) :
    limsup (fun m : ℕ ↦ graphProb m (α / m)
        (fun E ↦ ε * m ≤ ((reach (edgeGraph E) (A m)).card : ℝ))) atTop ≤ giantFraction α := by
  have h := limsup_graphProb_card_reach_ge_le hα A hA hε
  rwa [pow_one, sub_sub_cancel] at h

end

end Descent.Pangenome.AncestralLocality
