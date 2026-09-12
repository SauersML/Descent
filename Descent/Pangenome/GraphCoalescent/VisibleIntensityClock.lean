/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Coalescent.Process
import Descent.Pangenome.GraphCoalescent.HiddenLoads

assert_below Descent.PopGen Descent.Spectral Descent.Blindness Descent.Conditionals
assert_below Descent.Portability Descent.Decision Descent.Program

/-!
# The report's connection clock, bounded by Kingman's clock at the report width

`Descent.Pangenome.GraphCoalescent.Reduction` computes `E(T_w) = 2 - 2/w` for the Kingman
coalescent started AT the interface kernel `graphKer s`. A study that reads ancestry off a graph
built from a panel does not watch that process. It watches `Y_t = observed s Π_t` with
`Π_0 = ⊥`, the panel's own coalescent seen through the interface, and the time it waits is the
first time the report connects, `τ_q = inf {t : Y_t = ⊤}`. This file bounds that clock: it is
the corrected-clock half of `PANGENOME_HIDDEN_CLOCK.md` §5, Theorem C.

## What is proved

* `visibleIntensity s ξ` counts the Kingman covers of `ξ` whose report is a cover of the report,
  so with Kingman's unit rate per cover it is `λ_vis(ξ)`. The report map from visible covers onto
  the covers of the report is onto (`exists_visible_cover`), which gives `λ_vis ≥ d_r`
  (`deathRate_le_visibleIntensity`), and it is not injective as soon as some component hides two
  lineages and the report has two components (`deathRate_lt_visibleIntensity`).
* `kingmanGenerator_meanTransitTime_observed`: Kingman's generator, unit rate on every cover,
  applied to the clock function `f(r) = meanTransitTime r = 2 - 2/r` of the report width. An
  invisible cover contributes `0`, a visible one `-1/d_r` (`meanTransitTime_sub_of_covers`), so
  `𝓛 f = -λ_vis/d_r`.
* `connectionValue s t b g ξ` is the first-step solution of the backward equation
  `V(ξ) = (g(ξ) + Σ_{ξ ⋖ η} V(η)) / (d_K + t)` with boundary value `b` on connected reports, the
  equation satisfied by `E_ξ[∫_0^{τ_q} e^{-tu} g(Π_u) du + e^{-t τ_q} b(Π_{τ_q})]`. It is
  defined by recursion along covers, which lose a block each. `meanConnectionTime` is its value
  at `t = 0, b = 0, g = 1`, `connectionLaplace` at `b = 1, g = 0`.
* **(C3), in first-step form**: `connectionValue_generator` is Dynkin's formula for the backward
  equation, `V(F, tF - 𝓛F) = F`, for every function `F` on `𝓔ₙ`. With `F = f ∘ r` it becomes
  `meanTransitTime_sub_meanConnectionTime`:
  `f(r(ξ)) - E_ξ τ_q = V(0, λ_vis/d_r - 1)(ξ)`.
* **The upper bound**: `meanConnectionTime_bot_le_two_sub`, `E τ_q ≤ 2 - 2/w`, and
  `meanConnectionTime_bot_lt`, strict when `n > w ≥ 2`, both tied to
  `Reduction.graphMeanTransitTime`.
* **(C4), the lower bound**: `two_div_sub_two_div_le_meanConnectionTime_bot`,
  `2/(n - w + 1) - 2/n ≤ E τ_q`, from the invariant that `r - 1` visible mergers must precede
  connection (`meanTransitTime_sub_le_meanConnectionTime`).
* **The entrance at `q` is Kingman's**: `meanConnectionTime_graphKer` recovers
  `graphMeanTransitTime s = 2 - 2/w` when the chain is started at `graphKer s`, so the recursion
  reproduces `Reduction` where `Reduction` applies and departs from it at `⊥`.
* **(C2), in Laplace-transform order**: `kingmanLaplace_le_connectionLaplace`,
  `E_ξ e^{-t τ_q} ≥ ∏_{k=2}^{r} d_k/(d_k + t)`, the transform of the independent sum
  `Σ_{k=2}^r Exp(d_k)`.

## What is narrower than the note

The note states (C3) as Dynkin's formula for the continuous-time chain. The corpus has Kingman's
jump law (`Descent.Coalescent.Process.jumpStep`) and holding law
(`Descent.Coalescent.HoldingTime`) separately but no path-space law of the continuous-time
chain, and no Dynkin formula for one. So `connectionValue` is DEFINED as the solution of the
backward equation, and what is proved is Dynkin's identity for that equation. The identification
of `connectionValue` with the path expectation it solves for is not formalized.

(C2) is stochastic domination `τ_q ≤_st Σ_{r=2}^w Exp(d_r)` through conditional quantile
couplings. What is proved is the Laplace-transform order it implies. The coupling is not
formalized, and the transform order does not imply the stochastic order.

## Empirical status

None. Every declaration is a count of equivalence relations on a finite set or a finite
recursion along their covering order; the interface `s` is supplied, and no measurement can
bear on a cardinality or on the value of a recursion.
-/

set_option autoImplicit false

namespace Descent.Pangenome.GraphCoalescent

open Coalescent Finset
open scoped Classical

noncomputable section

/-! ### The visible intensity -/

/-- **The visible intensity `λ_vis(ξ)`**: the Kingman covers of `ξ` whose report is a cover of
the report of `ξ`. With Kingman's unit rate on every cover (K-C (1.3)) it is the rate at which
the graph sees anything happen. -/
def visibleIntensity {n : ℕ} (s : Fin n → Fin n) (ξ : ER n) : ℕ :=
  (univ.filter fun η : {η : ER n // Covers ξ η} ↦ Covers (observed s ξ) (observed s η.1)).card

/-- **Every step of the report is taken by some cover of the truth.** A cover of the report
merges two report components; merging one true block of each is a cover of `ξ` with that
report. -/
theorem exists_visible_cover {n : ℕ} (s : Fin n → Fin n) (ξ : ER n) {Z : ER n}
    (hZ : Covers (observed s ξ) Z) : ∃ η : ER n, Covers ξ η ∧ observed s η = Z := by
  obtain ⟨A, B, hAB, rfl⟩ := (covers_iff_exists_merge _ Z).mp hZ
  obtain ⟨x, rfl⟩ := quotient_mk_surjective (observed s ξ) A
  obtain ⟨y, rfl⟩ := quotient_mk_surjective (observed s ξ) B
  have hxy : ¬ (observed s ξ).r x y := fun h ↦ hAB (Quotient.sound h)
  have hab : Quotient.mk ξ x ≠ Quotient.mk ξ y :=
    fun hq ↦ hxy (le_observed s ξ (Quotient.exact hq))
  exact ⟨merge ξ (Quotient.mk ξ x) (Quotient.mk ξ y), merge_covers ξ hab,
    observed_merge_of_not_rel hab hxy⟩

/-- The report of a visible cover, as a cover of the report. -/
def visibleReport {n : ℕ} (s : Fin n → Fin n) (ξ : ER n) :
    (univ.filter fun η : {η : ER n // Covers ξ η} ↦ Covers (observed s ξ) (observed s η.1))
      → {Z : ER n // Covers (observed s ξ) Z} :=
  fun η ↦ ⟨observed s η.1.1, (mem_filter.mp η.2).2⟩

/-- The report map from visible covers onto the covers of the report is onto. -/
theorem visibleReport_surjective {n : ℕ} (s : Fin n → Fin n) (ξ : ER n) :
    Function.Surjective (visibleReport s ξ) := by
  intro Z
  obtain ⟨η, hη, hobs⟩ := exists_visible_cover s ξ Z.2
  refine ⟨⟨⟨η, hη⟩, mem_filter.mpr ⟨mem_univ _, ?_⟩⟩, Subtype.ext hobs⟩
  rw [hobs]
  exact Z.2

/-- **`λ_vis ≥ C(r, 2)`, counted.** The report has `C(r, 2)` covers and each is the report of a
visible cover. -/
theorem choose_two_le_visibleIntensity {n : ℕ} (s : Fin n → Fin n) (ξ : ER n) :
    (blocks (observed s ξ)).choose 2 ≤ visibleIntensity s ξ := by
  rw [← card_covers_fintype, visibleIntensity, ← Fintype.card_coe]
  exact Fintype.card_le_of_surjective _ (visibleReport_surjective s ξ)

/-- **`λ_vis(ξ) ≥ d_r`**: the graph's visible intensity is at least Kingman's death rate at the
report width, `Descent.Coalescent.Rates.deathRate`. -/
theorem deathRate_le_visibleIntensity {n : ℕ} (s : Fin n → Fin n) (ξ : ER n) :
    deathRate (blocks (observed s ξ)) ≤ (visibleIntensity s ξ : ℝ) := by
  rw [← card_covers_eq_deathRate, card_covers]
  exact_mod_cast choose_two_le_visibleIntensity s ξ

/-- **A component hiding two lineages makes the bound strict.** If the report has at least two
components and fewer blocks than the truth, some component holds two true blocks `x, x'`, and
merging each with a block `y` outside gives two distinct visible covers with one report. -/
theorem choose_two_lt_visibleIntensity {n : ℕ} (s : Fin n → Fin n) {ξ : ER n}
    (hr : 2 ≤ blocks (observed s ξ)) (hK : blocks (observed s ξ) < blocks ξ) :
    (blocks (observed s ξ)).choose 2 < visibleIntensity s ξ := by
  have hninj : ¬ Function.Injective (reportComponent s ξ) := by
    intro hinj
    have hcard := Nat.card_eq_of_bijective _ ⟨hinj, blockMap_surjective (le_observed s ξ)⟩
    unfold blocks at hK
    omega
  obtain ⟨a, a', haa', hne⟩ := Function.not_injective_iff.mp hninj
  obtain ⟨x, rfl⟩ := quotient_mk_surjective ξ a
  obtain ⟨x', rfl⟩ := quotient_mk_surjective ξ a'
  have hmk : Quotient.mk (observed s ξ) x = Quotient.mk (observed s ξ) x' := haa'
  have hxx' : (observed s ξ).r x x' := Quotient.exact hmk
  haveI : Nontrivial (Quotient (observed s ξ)) :=
    Finite.one_lt_card_iff_nontrivial.mp (by unfold blocks at hr; omega)
  obtain ⟨B, hB⟩ := exists_ne (Quotient.mk (observed s ξ) x)
  obtain ⟨y, rfl⟩ := quotient_mk_surjective (observed s ξ) B
  have hxy : ¬ (observed s ξ).r x y := fun h ↦ hB (Quotient.sound h).symm
  have hx'y : ¬ (observed s ξ).r x' y := fun h ↦ hxy ((observed s ξ).iseqv.trans hxx' h)
  have hab : Quotient.mk ξ x ≠ Quotient.mk ξ y :=
    fun hq ↦ hxy (le_observed s ξ (Quotient.exact hq))
  have ha'b : Quotient.mk ξ x' ≠ Quotient.mk ξ y :=
    fun hq ↦ hx'y (le_observed s ξ (Quotient.exact hq))
  have hmem : ∀ {u : Fin n} (hu : ¬ (observed s ξ).r u y)
      (hub : Quotient.mk ξ u ≠ Quotient.mk ξ y),
      (⟨merge ξ (Quotient.mk ξ u) (Quotient.mk ξ y), merge_covers ξ hub⟩ :
        {η : ER n // Covers ξ η}) ∈
      univ.filter fun η : {η : ER n // Covers ξ η} ↦
        Covers (observed s ξ) (observed s η.1) := by
    intro u hu hub
    refine mem_filter.mpr ⟨mem_univ _, ?_⟩
    show Covers (observed s ξ) (observed s (merge ξ (Quotient.mk ξ u) (Quotient.mk ξ y)))
    rw [observed_merge_of_not_rel hub hu]
    exact merge_covers _ fun hq ↦ hu (Quotient.exact hq)
  rw [← card_covers_fintype, visibleIntensity, ← Fintype.card_coe]
  refine Fintype.card_lt_of_surjective_not_injective _ (visibleReport_surjective s ξ) ?_
  intro hinj
  have hrep : visibleReport s ξ ⟨_, hmem hxy hab⟩ = visibleReport s ξ ⟨_, hmem hx'y ha'b⟩ := by
    apply Subtype.ext
    show observed s (merge ξ (Quotient.mk ξ x) (Quotient.mk ξ y))
      = observed s (merge ξ (Quotient.mk ξ x') (Quotient.mk ξ y))
    rw [observed_merge_of_not_rel hab hxy, observed_merge_of_not_rel ha'b hx'y, hmk]
  have hmerge : merge ξ (Quotient.mk ξ x) (Quotient.mk ξ y)
      = merge ξ (Quotient.mk ξ x') (Quotient.mk ξ y) :=
    congrArg (fun η ↦ η.1.1) (hinj hrep)
  have hpair := (merge_eq_merge_iff ξ hab ha'b).mp hmerge
  have hxmem : Quotient.mk ξ x ∈ ({Quotient.mk ξ x', Quotient.mk ξ y} : Finset (Quotient ξ)) := by
    rw [← hpair]
    exact mem_insert_self _ _
  rcases mem_insert.mp hxmem with h | h
  · exact hne h
  · exact hab (mem_singleton.mp h)

/-- **`λ_vis(ξ) > d_r`** when some report component hides two lineages and the report has two
components. -/
theorem deathRate_lt_visibleIntensity {n : ℕ} (s : Fin n → Fin n) {ξ : ER n}
    (hr : 2 ≤ blocks (observed s ξ)) (hK : blocks (observed s ξ) < blocks ξ) :
    deathRate (blocks (observed s ξ)) < (visibleIntensity s ξ : ℝ) := by
  rw [← card_covers_eq_deathRate, card_covers]
  exact_mod_cast choose_two_lt_visibleIntensity s hr hK

/-- **On the graph's own stratum every cover is visible**: at or above `graphKer s` the report is
the truth, so `λ_vis = C(K, 2)` and the correction below vanishes.

Assumes: `GraphState s ξ`. -/
theorem visibleIntensity_of_graphState {n : ℕ} {s : Fin n → Fin n} {ξ : ER n}
    (h : GraphState s ξ) : visibleIntensity s ξ = (blocks ξ).choose 2 := by
  rw [visibleIntensity, filter_true_of_mem, card_univ, card_covers_fintype]
  intro η _
  rw [observed_eq_of_graphState h, observed_eq_of_graphState (graphState_of_covers h η.2)]
  exact η.2

/-- The visible covers, summed with a constant weight. -/
theorem sum_ite_visible {n : ℕ} (s : Fin n → Fin n) (ξ : ER n) (c : ℝ) :
    ∑ η : {η : ER n // Covers ξ η}, (if Covers (observed s ξ) (observed s η.1) then c else 0)
      = (visibleIntensity s ξ : ℝ) * c := by
  rw [sum_ite, sum_const_zero, add_zero, sum_const, nsmul_eq_mul]
  rfl

/-! ### Kingman's generator on the clock function -/

/-- **Kingman's generator**, K-C (1.3): unit rate on every cover,
`𝓛F(ξ) = Σ_{ξ ⋖ η} (F(η) - F(ξ))`. -/
def kingmanGenerator {n : ℕ} (F : ER n → ℝ) (ξ : ER n) : ℝ :=
  ∑ η : {η : ER n // Covers ξ η}, (F η.1 - F ξ)

/-- **One more lineage adds one holding mean**: `f(m + 1) - f(m) = 1/d_{m+1}` for
`f = meanTransitTime`, K-G (5.7). -/
theorem meanTransitTime_succ_sub {m : ℕ} (hm : 1 ≤ m) :
    meanTransitTime (m + 1) - meanTransitTime m = 1 / deathRate (m + 1) := by
  rw [meanTransitTime_eq_two_sub (show 1 ≤ m + 1 by omega), meanTransitTime_eq_two_sub hm,
    one_div_deathRate_eq (show 2 ≤ m + 1 by omega), Nat.cast_add, Nat.cast_one,
    add_sub_cancel_right]
  ring

/-- **One report step costs the clock `1/d_r`**: `f(r - 1) - f(r) = -1/d_r`. -/
theorem meanTransitTime_sub_of_covers {n : ℕ} {Y Z : ER n} (h : Covers Y Z)
    (hY : 2 ≤ blocks Y) :
    meanTransitTime (blocks Z) - meanTransitTime (blocks Y) = -(1 / deathRate (blocks Y)) := by
  have hZ := h.2
  rw [← hZ, ← meanTransitTime_succ_sub (show 1 ≤ blocks Z by omega)]
  ring

/-- **The generator on the clock function**: invisible covers contribute `0`, visible covers
`-1/d_r`, so `𝓛 f(r)(ξ) = -λ_vis(ξ)/d_r` with `f(r) = 2 - 2/r`. -/
theorem kingmanGenerator_meanTransitTime_observed {n : ℕ} (s : Fin n → Fin n) {ξ : ER n}
    (hr : 2 ≤ blocks (observed s ξ)) :
    kingmanGenerator (fun ζ ↦ meanTransitTime (blocks (observed s ζ))) ξ
      = -((visibleIntensity s ξ : ℝ) / deathRate (blocks (observed s ξ))) := by
  have hterm : ∀ η : {η : ER n // Covers ξ η},
      meanTransitTime (blocks (observed s η.1)) - meanTransitTime (blocks (observed s ξ))
        = if Covers (observed s ξ) (observed s η.1)
          then -(1 / deathRate (blocks (observed s ξ))) else 0 := by
    intro η
    by_cases hvis : Covers (observed s ξ) (observed s η.1)
    · rw [if_pos hvis]
      exact meanTransitTime_sub_of_covers hvis hr
    · rw [if_neg hvis]
      rcases observed_eq_or_covers s η.2 with heq | hcov
      · rw [heq, sub_self]
      · exact absurd hcov hvis
  simp only [kingmanGenerator]
  rw [sum_congr rfl fun η _ ↦ hterm η, sum_ite_visible]
  ring

/-! ### First-step values -/

/-- The backward-equation recursion with `k` steps of fuel. -/
def discountedStep {n : ℕ} (s : Fin n → Fin n) (t : ℝ) (b g : ER n → ℝ) :
    ℕ → ER n → ℝ
  | 0, ξ => b ξ
  | k + 1, ξ =>
      if blocks (observed s ξ) ≤ 1 then b ξ
      else (g ξ + ∑ η : {η : ER n // Covers ξ η}, discountedStep s t b g k η.1)
        / (deathRate (blocks ξ) + t)

theorem discountedStep_succ {n : ℕ} (s : Fin n → Fin n) (t : ℝ) (b g : ER n → ℝ) (k : ℕ)
    (ξ : ER n) :
    discountedStep s t b g (k + 1) ξ =
      if blocks (observed s ξ) ≤ 1 then b ξ
      else (g ξ + ∑ η : {η : ER n // Covers ξ η}, discountedStep s t b g k η.1)
        / (deathRate (blocks ξ) + t) := rfl

/-- **The first-step value of a connection functional.** The solution of the backward equation
`V(ξ) = (g(ξ) + Σ_{ξ ⋖ η} V(η)) / (d_K + t)` on states whose report is not connected, with
`V = b` on states whose report is connected. It is the equation solved by
`E_ξ[∫_0^{τ_q} e^{-tu} g(Π_u) du + e^{-t τ_q} b(Π_{τ_q})]`: a holding time of rate
`d_K = C(K, 2)` (K-C (1.7)) followed by a uniform jump to a cover (K-C (2.2)). The fuel is the
block count, which every cover lowers by one. -/
def connectionValue {n : ℕ} (s : Fin n → Fin n) (t : ℝ) (b g : ER n → ℝ) (ξ : ER n) : ℝ :=
  discountedStep s t b g (blocks ξ) ξ

/-- **The backward equation.** -/
theorem connectionValue_eq {n : ℕ} (s : Fin n → Fin n) (t : ℝ) (b g : ER n → ℝ) (ξ : ER n) :
    connectionValue s t b g ξ =
      if blocks (observed s ξ) ≤ 1 then b ξ
      else (g ξ + ∑ η : {η : ER n // Covers ξ η}, connectionValue s t b g η.1)
        / (deathRate (blocks ξ) + t) := by
  rcases Nat.eq_zero_or_pos (blocks ξ) with h0 | hpos
  · have hr : blocks (observed s ξ) ≤ 1 := by
      have := blocks_antitone (le_observed s ξ)
      omega
    rw [if_pos hr, connectionValue, h0]
    rfl
  · obtain ⟨k, hk⟩ : ∃ k, blocks ξ = k + 1 := ⟨blocks ξ - 1, by omega⟩
    have hsum : ∑ η : {η : ER n // Covers ξ η}, discountedStep s t b g k η.1
        = ∑ η : {η : ER n // Covers ξ η}, connectionValue s t b g η.1 := by
      refine sum_congr rfl fun η _ ↦ ?_
      have hη : blocks η.1 = k := by
        have := η.2.2
        omega
      rw [connectionValue, hη]
    calc connectionValue s t b g ξ = discountedStep s t b g (k + 1) ξ := by
          rw [connectionValue, hk]
      _ = _ := by rw [discountedStep_succ, hsum]

/-- **Induction along the coalescent**: a property every state inherits from all of its covers
holds everywhere, because every cover loses a block. -/
theorem covers_induction {n : ℕ} {P : ER n → Prop}
    (step : ∀ ξ, (∀ η, Covers ξ η → P η) → P ξ) (ξ : ER n) : P ξ := by
  suffices H : ∀ k, ∀ ζ : ER n, blocks ζ = k → P ζ from H _ ξ rfl
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro ζ hζ
    exact step ζ fun η hη ↦ ih (blocks η) (by have := hη.2; omega) η rfl

/-- A state whose report is not connected has at least two true blocks, so its holding rate is
positive. -/
theorem deathRate_add_pos {n : ℕ} (s : Fin n → Fin n) {ξ : ER n} {t : ℝ} (ht : 0 ≤ t)
    (hr : ¬ blocks (observed s ξ) ≤ 1) : 0 < deathRate (blocks ξ) + t := by
  have := blocks_antitone (le_observed s ξ)
  linarith [deathRate_pos (show 2 ≤ blocks ξ by omega)]

/-- The first-step value is linear in the boundary value and the running cost. -/
theorem connectionValue_sub {n : ℕ} (s : Fin n → Fin n) (t : ℝ) (b₁ b₂ g₁ g₂ : ER n → ℝ)
    (ξ : ER n) :
    connectionValue s t (b₁ - b₂) (g₁ - g₂) ξ
      = connectionValue s t b₁ g₁ ξ - connectionValue s t b₂ g₂ ξ := by
  induction ξ using covers_induction with
  | step ξ ih =>
    rw [connectionValue_eq s t (b₁ - b₂), connectionValue_eq s t b₁, connectionValue_eq s t b₂]
    by_cases hr : blocks (observed s ξ) ≤ 1
    · simp only [if_pos hr, Pi.sub_apply]
    · simp only [if_neg hr, Pi.sub_apply]
      rw [sum_congr rfl fun η _ ↦ ih η.1 η.2, sum_sub_distrib]
      ring

/-- The first-step value sees the boundary value only on connected reports and the running cost
only on unconnected ones. -/
theorem connectionValue_congr {n : ℕ} (s : Fin n → Fin n) (t : ℝ) {b b' g g' : ER n → ℝ}
    (hb : ∀ ζ, blocks (observed s ζ) ≤ 1 → b ζ = b' ζ)
    (hg : ∀ ζ, 2 ≤ blocks (observed s ζ) → g ζ = g' ζ) (ξ : ER n) :
    connectionValue s t b g ξ = connectionValue s t b' g' ξ := by
  induction ξ using covers_induction with
  | step ξ ih =>
    rw [connectionValue_eq s t b g, connectionValue_eq s t b' g']
    by_cases hr : blocks (observed s ξ) ≤ 1
    · rw [if_pos hr, if_pos hr, hb ξ hr]
    · rw [if_neg hr, if_neg hr, hg ξ (by omega), sum_congr rfl fun η _ ↦ ih η.1 η.2]

/-- A nonnegative boundary value and running cost give a nonnegative first-step value. -/
theorem connectionValue_nonneg {n : ℕ} (s : Fin n → Fin n) {t : ℝ} (ht : 0 ≤ t)
    {b g : ER n → ℝ} (hb : ∀ ζ, blocks (observed s ζ) ≤ 1 → 0 ≤ b ζ)
    (hg : ∀ ζ, 2 ≤ blocks (observed s ζ) → 0 ≤ g ζ) (ξ : ER n) :
    0 ≤ connectionValue s t b g ξ := by
  induction ξ using covers_induction with
  | step ξ ih =>
    rw [connectionValue_eq]
    by_cases hr : blocks (observed s ξ) ≤ 1
    · rw [if_pos hr]
      exact hb ξ hr
    · rw [if_neg hr]
      exact div_nonneg (add_nonneg (hg ξ (by omega)) (sum_nonneg fun η _ ↦ ih η.1 η.2))
        (deathRate_add_pos s ht hr).le

/-- **The first holding period already accrues `g(ξ)/(d_K + t)`.** -/
theorem div_le_connectionValue {n : ℕ} (s : Fin n → Fin n) {t : ℝ} (ht : 0 ≤ t)
    {b g : ER n → ℝ} (hb : ∀ ζ, blocks (observed s ζ) ≤ 1 → 0 ≤ b ζ)
    (hg : ∀ ζ, 2 ≤ blocks (observed s ζ) → 0 ≤ g ζ) {ξ : ER n}
    (hr : 2 ≤ blocks (observed s ξ)) :
    g ξ / (deathRate (blocks ξ) + t) ≤ connectionValue s t b g ξ := by
  have hr' : ¬ blocks (observed s ξ) ≤ 1 := by omega
  rw [connectionValue_eq, if_neg hr']
  exact div_le_div_of_nonneg_right
    (le_add_of_nonneg_right (sum_nonneg fun η _ ↦ connectionValue_nonneg s ht hb hg η.1))
    (deathRate_add_pos s ht hr').le

/-- **Dynkin's formula for the backward equation.** For every function `F` on `𝓔ₙ`, the first-step
value with boundary value `F` and running cost `tF - 𝓛F` is `F` itself. At `t = 0` this is
`F(ξ) - E_ξ F(Π_{τ_q}) = E_ξ ∫_0^{τ_q} (-𝓛F)(Π_u) du` in first-step form. -/
theorem connectionValue_generator {n : ℕ} (s : Fin n → Fin n) {t : ℝ} (ht : 0 ≤ t)
    (F : ER n → ℝ) (ξ : ER n) :
    connectionValue s t F (fun ζ ↦ t * F ζ - kingmanGenerator F ζ) ξ = F ξ := by
  induction ξ using covers_induction with
  | step ξ ih =>
    rw [connectionValue_eq]
    by_cases hr : blocks (observed s ξ) ≤ 1
    · rw [if_pos hr]
    · rw [if_neg hr, sum_congr rfl fun η _ ↦ ih η.1 η.2]
      have hd := deathRate_add_pos s ht hr
      have hcount : ∑ η : {η : ER n // Covers ξ η}, (F η.1 - F ξ)
          = ∑ η : {η : ER n // Covers ξ η}, F η.1 - deathRate (blocks ξ) * F ξ := by
        rw [sum_sub_distrib, sum_const, nsmul_eq_mul, card_univ, ← Nat.card_eq_fintype_card,
          card_covers_eq_deathRate]
      simp only [kingmanGenerator]
      rw [hcount, div_eq_iff hd.ne']
      ring

/-! ### The mean connection time and the correction identity -/

/-- **`E_ξ τ_q`**: the mean time until the report connects, as the first-step value with no
boundary value, unit running cost and no discount. -/
def meanConnectionTime {n : ℕ} (s : Fin n → Fin n) (ξ : ER n) : ℝ :=
  connectionValue s 0 0 1 ξ

/-- The backward equation for the mean connection time. -/
theorem meanConnectionTime_eq {n : ℕ} (s : Fin n → Fin n) (ξ : ER n) :
    meanConnectionTime s ξ =
      if blocks (observed s ξ) ≤ 1 then 0
      else (1 + ∑ η : {η : ER n // Covers ξ η}, meanConnectionTime s η.1)
        / deathRate (blocks ξ) := by
  have h := connectionValue_eq s 0 0 1 ξ
  simp only [Pi.zero_apply, Pi.one_apply, add_zero] at h
  exact h

/-- **The correction rate** `λ_vis(ξ)/d_r - 1` of (C3): the relative excess of the visible
intensity over Kingman's death rate at the report width. -/
def clockCorrectionRate {n : ℕ} (s : Fin n → Fin n) (ξ : ER n) : ℝ :=
  (visibleIntensity s ξ : ℝ) / deathRate (blocks (observed s ξ)) - 1

/-- The clock function vanishes on connected reports. -/
theorem meanTransitTime_eq_zero_of_le_one {m : ℕ} (hm : m ≤ 1) : meanTransitTime m = 0 := by
  interval_cases m <;> simp [meanTransitTime]

/-- **(C3), in first-step form.** The Kingman clock at the report width exceeds the mean
connection time by the first-step value of the correction rate:
`f(r(ξ)) - E_ξ τ_q = V(0, λ_vis/d_r - 1)(ξ)`. -/
theorem meanTransitTime_sub_meanConnectionTime {n : ℕ} (s : Fin n → Fin n) (ξ : ER n) :
    meanTransitTime (blocks (observed s ξ)) - meanConnectionTime s ξ
      = connectionValue s 0 0 (clockCorrectionRate s) ξ := by
  have hdyn : connectionValue s 0 (fun ζ ↦ meanTransitTime (blocks (observed s ζ)))
      (fun ζ ↦ 0 * meanTransitTime (blocks (observed s ζ))
        - kingmanGenerator (fun ζ ↦ meanTransitTime (blocks (observed s ζ))) ζ) ξ
      = meanTransitTime (blocks (observed s ξ)) :=
    connectionValue_generator s le_rfl (fun ζ ↦ meanTransitTime (blocks (observed s ζ))) ξ
  have hcongr : connectionValue s 0 (fun ζ ↦ meanTransitTime (blocks (observed s ζ)))
      (fun ζ ↦ 0 * meanTransitTime (blocks (observed s ζ))
        - kingmanGenerator (fun ζ ↦ meanTransitTime (blocks (observed s ζ))) ζ) ξ
      = connectionValue s 0 0
          (fun ζ ↦ (visibleIntensity s ζ : ℝ) / deathRate (blocks (observed s ζ))) ξ := by
    refine connectionValue_congr s 0 (fun ζ hζ ↦ ?_) (fun ζ hζ ↦ ?_) ξ
    · simp only [meanTransitTime_eq_zero_of_le_one hζ, Pi.zero_apply]
    · show 0 * meanTransitTime (blocks (observed s ζ))
          - kingmanGenerator (fun ζ ↦ meanTransitTime (blocks (observed s ζ))) ζ
        = (visibleIntensity s ζ : ℝ) / deathRate (blocks (observed s ζ))
      rw [kingmanGenerator_meanTransitTime_observed s hζ]
      ring
  have hsub := connectionValue_sub s 0 0 0
    (fun ζ ↦ (visibleIntensity s ζ : ℝ) / deathRate (blocks (observed s ζ))) 1 ξ
  rw [sub_self] at hsub
  rw [← hdyn, hcongr]
  unfold meanConnectionTime
  rw [← hsub]
  rfl

/-- The correction rate is nonnegative wherever the report is not connected, because
`λ_vis ≥ d_r`. -/
theorem clockCorrectionRate_nonneg {n : ℕ} (s : Fin n → Fin n) {ξ : ER n}
    (hr : 2 ≤ blocks (observed s ξ)) : 0 ≤ clockCorrectionRate s ξ := by
  rw [clockCorrectionRate, sub_nonneg, le_div_iff₀ (deathRate_pos hr), one_mul]
  exact deathRate_le_visibleIntensity s ξ

/-! ### The upper bound -/

/-- **From any state, the report connects no later on average than Kingman's clock at the report
width.** -/
theorem meanConnectionTime_le_meanTransitTime {n : ℕ} (s : Fin n → Fin n) (ξ : ER n) :
    meanConnectionTime s ξ ≤ meanTransitTime (blocks (observed s ξ)) := by
  have h := meanTransitTime_sub_meanConnectionTime s ξ
  have hnn := connectionValue_nonneg s (t := 0) (b := 0) (g := clockCorrectionRate s) le_rfl
    (fun _ _ ↦ le_refl (0 : ℝ)) (fun ζ hζ ↦ clockCorrectionRate_nonneg s hζ) ξ
  linarith

/-- **`E τ_q ≤ E(T_w)`**: the panel's coalescent, read through the interface from `⊥`, connects
the report no later on average than the Kingman `w`-coalescent of
`Descent.Pangenome.GraphCoalescent.Reduction` reaches its root. -/
theorem meanConnectionTime_bot_le {n : ℕ} (s : Fin n → Fin n) :
    meanConnectionTime s ⊥ ≤ graphMeanTransitTime s := by
  have h := meanConnectionTime_le_meanTransitTime s ⊥
  rw [observed_bot, blocks_graphKer] at h
  exact h

/-- **`E τ_q ≤ 2 - 2/w`.**

Assumes: `1 ≤ Linkage.width s`, as in `Reduction.graphMeanTransitTime_eq`. -/
theorem meanConnectionTime_bot_le_two_sub {n : ℕ} (s : Fin n → Fin n)
    (hw : 1 ≤ Linkage.width s) : meanConnectionTime s ⊥ ≤ 2 - 2 / (Linkage.width s : ℝ) := by
  rw [← graphMeanTransitTime_eq hw]
  exact meanConnectionTime_bot_le s

/-- The bound is strict at any state whose report has two components and hides a lineage. -/
theorem meanConnectionTime_lt_meanTransitTime {n : ℕ} (s : Fin n → Fin n) {ξ : ER n}
    (hr : 2 ≤ blocks (observed s ξ)) (hK : blocks (observed s ξ) < blocks ξ) :
    meanConnectionTime s ξ < meanTransitTime (blocks (observed s ξ)) := by
  have h := meanTransitTime_sub_meanConnectionTime s ξ
  have hpos : 0 < clockCorrectionRate s ξ := by
    rw [clockCorrectionRate, sub_pos, lt_div_iff₀ (deathRate_pos hr), one_mul]
    exact deathRate_lt_visibleIntensity s hr hK
  have hfirst := div_le_connectionValue s (t := 0) (b := 0) (g := clockCorrectionRate s) le_rfl
    (fun _ _ ↦ le_refl (0 : ℝ)) (fun ζ hζ ↦ clockCorrectionRate_nonneg s hζ) hr
  have hdiv := div_pos hpos (deathRate_add_pos s (ξ := ξ) (le_refl (0 : ℝ)) (by omega))
  linarith

/-- **`E τ_q < 2 - 2/w` when `n > w ≥ 2`**: an interface that merged anything and did not
collapse the panel to one state gives a strictly faster report clock than the Kingman
`w`-coalescent started at its kernel. -/
theorem meanConnectionTime_bot_lt {n : ℕ} (s : Fin n → Fin n) (hw : 2 ≤ Linkage.width s)
    (hlt : Linkage.width s < n) : meanConnectionTime s ⊥ < graphMeanTransitTime s := by
  have hr : 2 ≤ blocks (observed s ⊥) := by
    rw [observed_bot, blocks_graphKer]
    exact hw
  have hK : blocks (observed s ⊥) < blocks (⊥ : ER n) := by
    rw [observed_bot, blocks_graphKer, blocks_bot]
    exact hlt
  have h := meanConnectionTime_lt_meanTransitTime s hr hK
  rw [observed_bot, blocks_graphKer] at h
  exact h

/-! ### The lower bound -/

/-- `meanTransitTime` is monotone: more lineages never wait less. -/
theorem meanTransitTime_mono {a b : ℕ} (h : a ≤ b) : meanTransitTime a ≤ meanTransitTime b := by
  unfold meanTransitTime
  exact sum_le_sum_of_subset_of_nonneg (range_subset_range.mpr (by omega))
    fun k _ _ ↦ (div_pos one_pos (deathRate_add_two_pos k)).le

/-- **The report cannot connect before `r - 1` visible mergers**, and each merger waits a
holding time of the current true block count. So from `ξ` with `K` true blocks and `r`
components, `E_ξ τ_q ≥ Σ_{k=K-r+2}^{K} 1/d_k = f(K) - f(K - r + 1)`. -/
theorem meanTransitTime_sub_le_meanConnectionTime {n : ℕ} (s : Fin n → Fin n) (ξ : ER n) :
    meanTransitTime (blocks ξ) - meanTransitTime (blocks ξ - blocks (observed s ξ) + 1)
      ≤ meanConnectionTime s ξ := by
  induction ξ using covers_induction with
  | step ξ ih =>
    have hrK := blocks_antitone (le_observed s ξ)
    rw [meanConnectionTime_eq]
    by_cases hr : blocks (observed s ξ) ≤ 1
    · rw [if_pos hr]
      have := meanTransitTime_mono
        (show blocks ξ ≤ blocks ξ - blocks (observed s ξ) + 1 by omega)
      linarith
    · rw [if_neg hr]
      have hd := deathRate_pos (show 2 ≤ blocks ξ by omega)
      have hstep : ∀ η : {η : ER n // Covers ξ η},
          meanTransitTime (blocks ξ - 1)
              - meanTransitTime (blocks ξ - blocks (observed s ξ) + 1)
            ≤ meanConnectionTime s η.1 := by
        intro η
        have hbη : blocks η.1 + 1 = blocks ξ := η.2.2
        have hrη : blocks (observed s ξ) ≤ blocks (observed s η.1) + 1 := by
          rcases observed_eq_or_covers s η.2 with heq | hcov
          · rw [heq]
            omega
          · have := hcov.2
            omega
        have hrηK := blocks_antitone (le_observed s η.1)
        have hih := ih η.1 η.2
        rw [show blocks η.1 = blocks ξ - 1 by omega] at hih hrηK
        have hmono := meanTransitTime_mono
          (show blocks ξ - 1 - blocks (observed s η.1) + 1
            ≤ blocks ξ - blocks (observed s ξ) + 1 by omega)
        linarith
      have hsum := sum_le_sum fun η (_ : η ∈ (univ : Finset {η : ER n // Covers ξ η})) ↦
        hstep η
      rw [sum_const, nsmul_eq_mul, card_univ, ← Nat.card_eq_fintype_card,
        card_covers_eq_deathRate] at hsum
      have hsucc := meanTransitTime_succ_sub (show 1 ≤ blocks ξ - 1 by omega)
      rw [show blocks ξ - 1 + 1 = blocks ξ by omega] at hsucc
      have h2 : meanTransitTime (blocks ξ - 1)
          - meanTransitTime (blocks ξ - blocks (observed s ξ) + 1)
          ≤ (∑ η : {η : ER n // Covers ξ η}, meanConnectionTime s η.1) / deathRate (blocks ξ) := by
        rw [le_div_iff₀ hd]
        linarith
      rw [add_div]
      linarith

/-- **(C4)**: `2/(n - w + 1) - 2/n ≤ E τ_q`, the mean of `Σ_{k=n-w+2}^{n} Exp(d_k)`.

Assumes: `1 ≤ n`. -/
theorem two_div_sub_two_div_le_meanConnectionTime_bot {n : ℕ} (s : Fin n → Fin n)
    (hn : 1 ≤ n) :
    2 / ((n : ℝ) - Linkage.width s + 1) - 2 / (n : ℝ) ≤ meanConnectionTime s ⊥ := by
  have h := meanTransitTime_sub_le_meanConnectionTime s ⊥
  have hw : Linkage.width s ≤ n := by simpa using Linkage.width_le_card s
  rw [observed_bot, blocks_graphKer, blocks_bot, meanTransitTime_eq_two_sub hn,
    meanTransitTime_eq_two_sub (show 1 ≤ n - Linkage.width s + 1 by omega), Nat.cast_add,
    Nat.cast_sub hw, Nat.cast_one] at h
  linarith

/-! ### Started at the interface kernel, the clock is Kingman's -/

/-- **On the graph's stratum the connection clock is K-G (5.7)**: every cover is visible, and the
recursion returns `2 - 2/K`.

Assumes: `GraphState s ξ`. -/
theorem meanConnectionTime_of_graphState {n : ℕ} {s : Fin n → Fin n} {ξ : ER n}
    (h : GraphState s ξ) : meanConnectionTime s ξ = meanTransitTime (blocks ξ) := by
  induction ξ using covers_induction with
  | step ξ ih =>
    rw [meanConnectionTime_eq, observed_eq_of_graphState h]
    by_cases hK : blocks ξ ≤ 1
    · rw [if_pos hK, meanTransitTime_eq_zero_of_le_one hK]
    · rw [if_neg hK]
      have hd := deathRate_pos (show 2 ≤ blocks ξ by omega)
      have hterm : ∀ η : {η : ER n // Covers ξ η},
          meanConnectionTime s η.1 = meanTransitTime (blocks ξ - 1) := by
        intro η
        have hbη : blocks η.1 + 1 = blocks ξ := η.2.2
        rw [ih η.1 η.2 (graphState_of_covers h η.2), show blocks η.1 = blocks ξ - 1 by omega]
      rw [sum_congr rfl fun η _ ↦ hterm η, sum_const, nsmul_eq_mul, card_univ,
        ← Nat.card_eq_fintype_card, card_covers_eq_deathRate, add_div,
        mul_div_cancel_left₀ _ hd.ne']
      have hsucc := meanTransitTime_succ_sub (show 1 ≤ blocks ξ - 1 by omega)
      rw [show blocks ξ - 1 + 1 = blocks ξ by omega] at hsucc
      linarith

/-- **Entered at `graphKer s`, the report clock is `Reduction`'s**: the recursion reproduces
`graphMeanTransitTime s = 2 - 2/w` exactly where `Reduction` applies, and departs from it at `⊥`
by `meanConnectionTime_bot_lt`. -/
theorem meanConnectionTime_graphKer {n : ℕ} (s : Fin n → Fin n) :
    meanConnectionTime s (graphKer s) = graphMeanTransitTime s := by
  rw [meanConnectionTime_of_graphState (graphState_graphKer s), blocks_graphKer]
  rfl

/-! ### The Laplace-transform order -/

/-- **Kingman's transit transform at `m` lineages**, `E e^{-t T_m} = ∏_{k=2}^{m} d_k/(d_k + t)`,
K-G (5.9). -/
def kingmanLaplace (t : ℝ) (m : ℕ) : ℝ :=
  ∏ k ∈ range (m - 1), deathRate (k + 2) / (deathRate (k + 2) + t)

/-- **`E_ξ e^{-t τ_q}`**, as the first-step value with boundary value `1` and no running cost. -/
def connectionLaplace {n : ℕ} (s : Fin n → Fin n) (t : ℝ) (ξ : ER n) : ℝ :=
  connectionValue s t 1 0 ξ

theorem kingmanLaplace_nonneg {t : ℝ} (ht : 0 ≤ t) (m : ℕ) : 0 ≤ kingmanLaplace t m :=
  prod_nonneg fun k _ ↦ div_nonneg (deathRate_add_two_pos k).le
    (add_nonneg (deathRate_add_two_pos k).le ht)

theorem kingmanLaplace_eq_one_of_le_one (t : ℝ) {m : ℕ} (hm : m ≤ 1) :
    kingmanLaplace t m = 1 := by
  rw [kingmanLaplace, show m - 1 = 0 by omega, range_zero, prod_empty]

/-- One more lineage multiplies the transform by the new level's factor `d_{m+1}/(d_{m+1} + t)`. -/
theorem kingmanLaplace_succ (t : ℝ) {m : ℕ} (hm : 1 ≤ m) :
    kingmanLaplace t (m + 1)
      = kingmanLaplace t m * (deathRate (m + 1) / (deathRate (m + 1) + t)) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hm
  rw [kingmanLaplace, kingmanLaplace, show 1 + j + 1 - 1 = j + 1 by omega,
    show 1 + j - 1 = j by omega, prod_range_succ, show j + 2 = 1 + j + 1 by omega]

/-- **(C2), in Laplace-transform order**: `E_ξ e^{-t τ_q} ≥ ∏_{k=2}^{r} d_k/(d_k + t)`, the
transform of `Σ_{k=2}^{r} Exp(d_k)` with `r` the report width. A visible cover multiplies the
Kingman transform by `(d_r + t)/d_r`, and there are at least `d_r` of them. -/
theorem kingmanLaplace_le_connectionLaplace {n : ℕ} (s : Fin n → Fin n) {t : ℝ} (ht : 0 ≤ t)
    (ξ : ER n) : kingmanLaplace t (blocks (observed s ξ)) ≤ connectionLaplace s t ξ := by
  induction ξ using covers_induction with
  | step ξ ih =>
    unfold connectionLaplace at ih ⊢
    rw [connectionValue_eq]
    by_cases hr : blocks (observed s ξ) ≤ 1
    · simp only [if_pos hr, kingmanLaplace_eq_one_of_le_one t hr, Pi.one_apply, le_refl]
    · rw [if_neg hr, Pi.zero_apply, zero_add]
      have hr2 : 2 ≤ blocks (observed s ξ) := by omega
      have hdr := deathRate_pos hr2
      have hψ := kingmanLaplace_nonneg ht (blocks (observed s ξ))
      have hstep : ∀ η : {η : ER n // Covers ξ η},
          deathRate (blocks (observed s ξ)) * kingmanLaplace t (blocks (observed s ξ))
              + (if Covers (observed s ξ) (observed s η.1)
                then kingmanLaplace t (blocks (observed s ξ)) * t else 0)
            ≤ deathRate (blocks (observed s ξ)) * connectionValue s t 1 0 η.1 := by
        intro η
        have hih := mul_le_mul_of_nonneg_left (ih η.1 η.2) hdr.le
        by_cases hvis : Covers (observed s ξ) (observed s η.1)
        · rw [if_pos hvis]
          have hrη : blocks (observed s η.1) + 1 = blocks (observed s ξ) := hvis.2
          have hsucc := kingmanLaplace_succ t (show 1 ≤ blocks (observed s η.1) by omega)
          rw [hrη] at hsucc
          have hdt : deathRate (blocks (observed s ξ)) + t ≠ 0 := by linarith
          have hkey : kingmanLaplace t (blocks (observed s ξ))
                * (deathRate (blocks (observed s ξ)) + t)
              = kingmanLaplace t (blocks (observed s η.1)) * deathRate (blocks (observed s ξ)) := by
            rw [hsucc, mul_assoc, div_mul_cancel₀ _ hdt]
          linarith
        · rw [if_neg hvis, add_zero]
          rcases observed_eq_or_covers s η.2 with heq | hcov
          · rw [heq] at hih
            exact hih
          · exact absurd hcov hvis
      have hsum := sum_le_sum fun η (_ : η ∈ (univ : Finset {η : ER n // Covers ξ η})) ↦
        hstep η
      rw [sum_add_distrib, sum_const, nsmul_eq_mul, card_univ, ← Nat.card_eq_fintype_card,
        card_covers_eq_deathRate, sum_ite_visible, ← mul_sum] at hsum
      have hmid := mul_le_mul_of_nonneg_right (deathRate_le_visibleIntensity s ξ)
        (mul_nonneg hψ ht)
      rw [le_div_iff₀ (deathRate_add_pos s ht hr)]
      refine le_of_mul_le_mul_left ?_ hdr
      linarith

end

end Descent.Pangenome.GraphCoalescent
