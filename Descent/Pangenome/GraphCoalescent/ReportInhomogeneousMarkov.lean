/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.GraphCoalescent.HiddenStateChain
import Descent.Pangenome.GraphCoalescent.MarkovCompressions
import Descent.Pangenome.GraphCoalescent.ReportNonMarkovFromSingletons

assert_below Descent.PopGen Descent.Spectral Descent.Blindness Descent.Conditionals
assert_below Descent.Portability Descent.Decision Descent.Program

/-!
# When the report from the singletons is Markov in the jump count

`ReportNonMarkovFromSingletons` refutes a time-homogeneous transition law for the report sequence
of Kingman's jump chain from the singletons when `2 ≤ w < n`. A transition law that may depend on
the jump count `k` is a weaker requirement, and this module decides it.

**The object.** `IsReportInhomogeneousMarkov s` says that some `Q k x y` gives every report history
step by step, `P(R₀, …, R_k, R_{k+1}) = P(R₀, …, R_k) · Q_k(R_k, R_{k+1})`.

**The step identity.** The probability of a report history extended by one report is a sum over
the labeled trajectories carrying the history, each weighted by the law of the next report from
its current state (`reportLaw_succ_apply`). So a transition law exists as soon as that next-report
law, `reportJumpLaw s ξ`, is the same for all states the chain can occupy after `k` jumps with one
report (`reportLaw_succ_eq_mul`). After `k` jumps every such state has one block count
(`blocks_eq_of_chainLaw_ne_zero`), so it suffices that the next-report law is a function of the
block count and the report (`isReportInhomogeneousMarkov_of_blocks`).

**At most one heavy graph state.** If at most one graph state holds two or more haplotypes, every
report component without it holds exactly one hidden lineage (`hiddenLoad_eq_one_of_not_heavy`,
from `MarkovCompressions.hiddenLoad_add_componentWidth_le`), and the remaining component holds
`K + 1 - |report|` (`hiddenLoad_heavy`). The hidden state is then a function of the block count and
the report (`hiddenState_eq_of_atMostOneHeavy`), and the report is Markov in the jump count
(`isReportInhomogeneousMarkov_of_atMostOneHeavy`).

**Width two.** Reports are monotone along a trajectory and never below `Y₀ = graphKer s`, so the
only history of positive probability that ends at `Y₀` is the constant one
(`eq_replicate_of_reportLaw_ne_zero`). Above `Y₀` a width-two report has one block and is absorbing
(`reportJumpLaw_eq_pure`). The explicit law `widthTwoLaw` is the conditional law after the constant
history at `Y₀` and the point mass elsewhere, and it gives every history
(`reportLaw_succ_eq_widthTwoLaw`, `isReportInhomogeneousMarkov_of_width_eq_two`). On three
haplotypes with `0` and `1` in one graph state it stays at `Y₀` with probability `1/3` after one
jump and `0` after two (`example_widthTwoLaw_zero`, `example_widthTwoLaw_one`), the two values no
single homogeneous law can take.

Scope. The process is the jump chain's report sequence, one report per merger, from the
singletons; holding times are not used.

## Empirical status

None. The bodies here are probabilities of finite trajectories of the jump chain, which Kingman's
unit rates force; the interface is supplied, and no measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Pangenome.GraphCoalescent.ReportInhomogeneousMarkov

open Coalescent Finset ReportNonMarkovFromSingletons MarkovCompressions
open scoped Classical

noncomputable section

variable {n : ℕ}

/-! ### The step identity of the report law -/

/-- **The report after one jump**: the law of the report of the next state of the jump chain
from `ξ`. -/
def reportJumpLaw (s : Fin n → Fin n) (ξ : ER n) : PMF (ER n) :=
  (jumpLaw ξ).map (observed s)

/-- The report law as a sum over labeled trajectories. -/
theorem reportLaw_apply (s : Fin n → Fin n) (k : ℕ) (L : List (ER n)) :
    reportLaw s k L =
      ∑' l : List (ER n), chainLaw n k l * if l.map (observed s) = L then 1 else 0 := by
  rw [reportLaw, PMF.map_apply]
  refine tsum_congr fun l ↦ ?_
  by_cases hl : l.map (observed s) = L
  · rw [if_pos hl.symm, if_pos hl, mul_one]
  · rw [if_neg fun h ↦ hl h.symm, if_neg hl, mul_zero]

/-- **The step identity.** A report history extended by one report has the probability of the
trajectories carrying the history, each weighted by the law of the next report from its current
state. -/
theorem reportLaw_succ_apply (s : Fin n → Fin n) (k : ℕ) (x y : ER n) (H : List (ER n)) :
    reportLaw s (k + 1) (y :: x :: H) =
      ∑' l : List (ER n), chainLaw n k l *
        if l.map (observed s) = x :: H then reportJumpLaw s (l.headD ⊥) y else 0 := by
  rw [reportLaw, chainLaw, PMF.map_bind, PMF.bind_apply]
  refine tsum_congr fun l ↦ ?_
  congr 1
  match l with
  | [] =>
    show (PMF.pure []).map (List.map (observed s)) (y :: x :: H) = _
    rw [PMF.pure_map, List.map_nil, PMF.pure_apply, if_neg (List.cons_ne_nil _ _),
      if_neg (List.cons_ne_nil x H).symm]
  | ξ :: rest =>
    show ((jumpLaw ξ).map fun η ↦ η :: ξ :: rest).map (List.map (observed s)) (y :: x :: H) = _
    rw [PMF.map_comp, PMF.map_apply]
    by_cases hl : (ξ :: rest).map (observed s) = x :: H
    · rw [if_pos hl, List.headD_cons, reportJumpLaw, PMF.map_apply]
      refine tsum_congr fun η ↦ ?_
      by_cases hη : y = observed s η
      · rw [if_pos hη, if_pos]
        show y :: x :: H = observed s η :: (ξ :: rest).map (observed s)
        rw [hl, hη]
      · rw [if_neg hη, if_neg]
        intro h
        exact hη (List.cons.inj h).1
    · rw [if_neg hl]
      refine ENNReal.tsum_eq_zero.mpr fun η ↦ ?_
      rw [if_neg]
      intro h
      exact hl (List.cons.inj h).2.symm

/-- **A history of probability zero stays of probability zero.** -/
theorem reportLaw_succ_eq_zero {s : Fin n → Fin n} {k : ℕ} {x : ER n} {H : List (ER n)}
    (h : reportLaw s k (x :: H) = 0) (y : ER n) : reportLaw s (k + 1) (y :: x :: H) = 0 := by
  rw [reportLaw_apply] at h
  rw [reportLaw_succ_apply]
  refine ENNReal.tsum_eq_zero.mpr fun l ↦ ?_
  have hl := ENNReal.tsum_eq_zero.mp h l
  by_cases hmap : l.map (observed s) = x :: H
  · rw [if_pos hmap, mul_one] at hl
    rw [hl, zero_mul]
  · rw [if_neg hmap, mul_zero]

/-- **One step of a transition law.** If every state the chain can occupy after `k` jumps with
report `x` has the next-report law `q`, every history ending at `x` after `k` jumps is extended
by `q`. -/
theorem reportLaw_succ_eq_mul {s : Fin n → Fin n} {k : ℕ} {x : ER n} (q : ER n → ENNReal)
    (hq : ∀ (ξ : ER n) (H : List (ER n)), chainLaw n k (ξ :: H) ≠ 0 → observed s ξ = x →
      ∀ y, reportJumpLaw s ξ y = q y) (y : ER n) (H : List (ER n)) :
    reportLaw s (k + 1) (y :: x :: H) = reportLaw s k (x :: H) * q y := by
  rw [reportLaw_succ_apply, reportLaw_apply, ← ENNReal.tsum_mul_right]
  refine tsum_congr fun l ↦ ?_
  by_cases hl : l.map (observed s) = x :: H
  · rw [if_pos hl, if_pos hl, mul_one]
    by_cases h0 : chainLaw n k l = 0
    · rw [h0, zero_mul, zero_mul]
    · obtain ⟨ξ, rest, rfl⟩ : ∃ ξ rest, l = ξ :: rest := by
        cases l with
        | nil => exact absurd hl (List.cons_ne_nil x H).symm
        | cons ξ rest => exact ⟨ξ, rest, rfl⟩
      rw [List.headD_cons, hq ξ rest h0 (List.cons.inj hl).1 y]
  · rw [if_neg hl, if_neg hl, mul_zero, zero_mul]

/-! ### Markov in the jump count -/

/-- **The report sequence is Markov in the jump count**: some transition law, allowed to depend
on the number of jumps made, gives the probability of every report history step by step. -/
def IsReportInhomogeneousMarkov (s : Fin n → Fin n) : Prop :=
  ∃ Q : ℕ → ER n → ER n → ENNReal, ∀ (k : ℕ) (x y : ER n) (H : List (ER n)),
    reportLaw s (k + 1) (y :: x :: H) = reportLaw s k (x :: H) * Q k x y

/-- A time-homogeneous transition law is one that ignores the jump count. -/
theorem isReportInhomogeneousMarkov_of_isReportMarkovFromBot {s : Fin n → Fin n}
    (h : IsReportMarkovFromBot s) : IsReportInhomogeneousMarkov s := by
  obtain ⟨Q, hQ⟩ := h
  exact ⟨fun _ ↦ Q, hQ⟩

/-- The identity interface reports a chain that is Markov in the jump count. -/
theorem isReportInhomogeneousMarkov_id : IsReportInhomogeneousMarkov (id : Fin n → Fin n) :=
  isReportInhomogeneousMarkov_of_isReportMarkovFromBot isReportMarkovFromBot_id

/-- **After `k` jumps all reachable states have one block count.** -/
theorem blocks_eq_of_chainLaw_ne_zero {k : ℕ} {ξ ξ' : ER n} {H H' : List (ER n)}
    (h : chainLaw n k (ξ :: H) ≠ 0) (h' : chainLaw n k (ξ' :: H') ≠ 0) :
    blocks ξ = blocks ξ' := by
  induction k generalizing ξ ξ' H H' with
  | zero =>
    rw [← PMF.mem_support_iff, chainLaw, PMF.mem_support_pure_iff] at h h'
    rw [(List.cons.inj h).1, (List.cons.inj h').1]
  | succ k ih =>
    rw [← PMF.mem_support_iff] at h h'
    obtain ⟨x, y, rest, hl, hprev, hy⟩ := mem_support_chainLaw_succ h
    obtain ⟨x', y', rest', hl', hprev', hy'⟩ := mem_support_chainLaw_succ h'
    rw [(List.cons.inj hl).1, (List.cons.inj hl').1]
    have hb : blocks x = blocks x' :=
      ih (ξ := x) (ξ' := x') (H := rest) (H' := rest') ((PMF.mem_support_iff _ _).mp hprev)
        ((PMF.mem_support_iff _ _).mp hprev')
    rcases lt_or_ge (blocks x) 2 with hx | hx
    · have hx' : blocks x' < 2 := hb ▸ hx
      rw [(mem_support_jumpLaw_of_absorbed hx).mp hy, (mem_support_jumpLaw_of_absorbed hx').mp hy']
      exact hb
    · have hx' : 2 ≤ blocks x' := hb ▸ hx
      have hc := ((mem_support_jumpLaw hx).mp hy).2
      have hc' := ((mem_support_jumpLaw hx').mp hy').2
      omega

/-- The next-report law read off a state the chain can occupy after `k` jumps with report `x`,
and zero where there is none. -/
def reachableLaw (s : Fin n → Fin n) (k : ℕ) (x y : ER n) : ENNReal :=
  if hx : ∃ (ξ : ER n) (H : List (ER n)), chainLaw n k (ξ :: H) ≠ 0 ∧ observed s ξ = x then
    reportJumpLaw s hx.choose y else 0

/-- **A criterion.** If the next-report law depends on a state only through its block count and
its report, the report sequence is Markov in the jump count, with `reachableLaw` as law.

Assumes: the next-report laws of two states with one block count and one report agree. -/
theorem isReportInhomogeneousMarkov_of_blocks {s : Fin n → Fin n}
    (h : ∀ ξ ξ' : ER n, blocks ξ = blocks ξ' → observed s ξ = observed s ξ' →
      reportJumpLaw s ξ = reportJumpLaw s ξ') : IsReportInhomogeneousMarkov s := by
  refine ⟨reachableLaw s, fun k x y H ↦
    reportLaw_succ_eq_mul (reachableLaw s k x) (fun ξ H' h0 hobs y' ↦ ?_) y H⟩
  have hx : ∃ (ξ' : ER n) (H'' : List (ER n)), chainLaw n k (ξ' :: H'') ≠ 0 ∧
      observed s ξ' = x := ⟨ξ, H', h0, hobs⟩
  obtain ⟨H'', h0', hobs'⟩ := hx.choose_spec
  rw [reachableLaw, dif_pos hx,
    h ξ hx.choose (blocks_eq_of_chainLaw_ne_zero h0 h0') (hobs.trans hobs'.symm)]

/-- Two states with one hidden state have one next-report law. -/
theorem reportJumpLaw_eq_of_hiddenState_eq (s : Fin n → Fin n) {ξ ξ' : ER n}
    (h : hiddenState s ξ = hiddenState s ξ') : reportJumpLaw s ξ = reportJumpLaw s ξ' := by
  rw [reportJumpLaw, reportJumpLaw, show observed s = Prod.fst ∘ hiddenState s from rfl,
    ← PMF.map_comp, ← PMF.map_comp]
  exact congrArg (PMF.map Prod.fst) (hiddenJumpLaw_eq_of_hiddenState_eq s h)

/-! ### At most one heavy graph state -/

/-- **At most one graph state holds two or more haplotypes.** -/
def AtMostOneHeavy (s : Fin n → Fin n) : Prop :=
  ∀ a b : Fin n, 2 ≤ Linkage.fiberCard s a → 2 ≤ Linkage.fiberCard s b → s a = s b

/-- The identity interface has no heavy graph state. -/
theorem atMostOneHeavy_id : AtMostOneHeavy (id : Fin n → Fin n) := by
  intro a _ ha _
  have hle : Linkage.fiberCard (id : Fin n → Fin n) a ≤ 1 :=
    card_le_one.mpr fun g hg g' hg' ↦
      (Linkage.mem_fiber.mp hg).trans (Linkage.mem_fiber.mp hg').symm
  omega

/-- The example of Theorem A has one heavy graph state. -/
theorem atMostOneHeavy_example : AtMostOneHeavy exampleInterface := by
  unfold AtMostOneHeavy
  decide

/-- **A component without a heavy graph state holds one hidden lineage.** -/
theorem hiddenLoad_eq_one_of_not_heavy {s : Fin n → Fin n} (ξ : ER n) (z : Fin n)
    (hz : ∀ a, (observed s ξ).r a z → Linkage.fiberCard s a ≤ 1) :
    hiddenLoad s ξ (Quotient.mk (observed s ξ) z) = 1 := by
  have hwidth : componentWidth s ξ z = componentSize s ξ z := by
    rw [componentWidth, componentSize]
    refine card_image_of_injOn fun a ha b hb hab ↦ ?_
    have ha' : (observed s ξ).r a z := (mem_filter.mp (mem_coe.mp ha)).2
    by_contra hne
    have h2 : 2 ≤ Linkage.fiberCard s a := by
      rw [Linkage.fiberCard]
      exact one_lt_card.mpr ⟨a, Linkage.self_mem_fiber s a, b, Linkage.mem_fiber.mpr hab.symm, hne⟩
    have h1 := hz a ha'
    omega
  have hbound := hiddenLoad_add_componentWidth_le s ξ z
  have hpos := hiddenLoad_pos s ξ (Quotient.mk (observed s ξ) z)
  omega

/-- **The heavy component holds the rest.** With at most one heavy graph state, the component of
a heavy haplotype holds `K + 1 - |report|` hidden lineages.

Assumes: at most one graph state holds two or more haplotypes. -/
theorem hiddenLoad_heavy {s : Fin n → Fin n} (hs : AtMostOneHeavy s) (ξ : ER n) {a : Fin n}
    (ha : 2 ≤ Linkage.fiberCard s a) :
    hiddenLoad s ξ (Quotient.mk (observed s ξ) a) + blocks (observed s ξ) = blocks ξ + 1 := by
  have hsum := sum_hiddenLoad s ξ
  rw [← add_sum_erase univ _ (mem_univ (Quotient.mk (observed s ξ) a))] at hsum
  have hrest : ∑ C ∈ univ.erase (Quotient.mk (observed s ξ) a), hiddenLoad s ξ C =
      ∑ C ∈ univ.erase (Quotient.mk (observed s ξ) a), 1 := by
    refine sum_congr rfl fun C hC ↦ ?_
    obtain ⟨z, rfl⟩ := quotient_mk_surjective _ C
    refine hiddenLoad_eq_one_of_not_heavy ξ z fun a' ha' ↦ ?_
    by_contra h2
    have hrel : (observed s ξ).r a' a :=
      graphKer_le_observed s ξ (graphKer_rel_iff.mpr (hs a' a (by omega) ha))
    exact ne_of_mem_erase hC
      (Quotient.sound ((observed s ξ).iseqv.trans ((observed s ξ).iseqv.symm ha') hrel))
  have hcard : 0 < Fintype.card (Quotient (observed s ξ)) :=
    Fintype.card_pos_iff.mpr ⟨Quotient.mk _ a⟩
  rw [hrest, sum_const, card_erase_of_mem (mem_univ _), card_univ, smul_eq_mul, mul_one] at hsum
  rw [blocks, Nat.card_eq_fintype_card]
  omega

/-- **The hidden state is read off the block count and the report** when at most one graph state
is heavy.

Assumes: at most one graph state holds two or more haplotypes. -/
theorem hiddenState_eq_of_atMostOneHeavy {s : Fin n → Fin n} (hs : AtMostOneHeavy s)
    {ξ ξ' : ER n} (hb : blocks ξ = blocks ξ') (hobs : observed s ξ = observed s ξ') :
    hiddenState s ξ = hiddenState s ξ' := by
  refine Prod.ext hobs (funext fun z ↦ ?_)
  show hiddenLoad s ξ (Quotient.mk (observed s ξ) z) =
    hiddenLoad s ξ' (Quotient.mk (observed s ξ') z)
  have hblocks : blocks (observed s ξ) = blocks (observed s ξ') := by
    rw [hobs]
  by_cases hz : ∃ a, (observed s ξ).r a z ∧ 2 ≤ Linkage.fiberCard s a
  · obtain ⟨a, haz, ha⟩ := hz
    have haz' : (observed s ξ').r a z := hobs ▸ haz
    have hq : Quotient.mk (observed s ξ) z = Quotient.mk (observed s ξ) a :=
      Quotient.sound ((observed s ξ).iseqv.symm haz)
    have hq' : Quotient.mk (observed s ξ') z = Quotient.mk (observed s ξ') a :=
      Quotient.sound ((observed s ξ').iseqv.symm haz')
    have h1 := hiddenLoad_heavy hs ξ ha
    have h2 := hiddenLoad_heavy hs ξ' ha
    rw [hq, hq']
    omega
  · have hz1 : ∀ a, (observed s ξ).r a z → Linkage.fiberCard s a ≤ 1 := fun a ha ↦ by
      by_contra h
      exact hz ⟨a, ha, by omega⟩
    rw [hiddenLoad_eq_one_of_not_heavy ξ z hz1,
      hiddenLoad_eq_one_of_not_heavy ξ' z fun a ha ↦ hz1 a (hobs ▸ ha)]

/-- **With at most one heavy graph state the report is Markov in the jump count.**

Assumes: at most one graph state holds two or more haplotypes. -/
theorem isReportInhomogeneousMarkov_of_atMostOneHeavy {s : Fin n → Fin n}
    (hs : AtMostOneHeavy s) : IsReportInhomogeneousMarkov s :=
  isReportInhomogeneousMarkov_of_blocks fun _ _ hb hobs ↦
    reportJumpLaw_eq_of_hiddenState_eq s (hiddenState_eq_of_atMostOneHeavy hs hb hobs)

/-! ### Width two -/

/-- **Every state of a trajectory lies below its current state.** -/
theorem le_of_mem_tail {k : ℕ} {ξ ζ : ER n} {H : List (ER n)} (h : chainLaw n k (ξ :: H) ≠ 0)
    (hζ : ζ ∈ H) : ζ ≤ ξ := by
  induction k generalizing ξ H with
  | zero =>
    rw [← PMF.mem_support_iff, chainLaw, PMF.mem_support_pure_iff] at h
    rw [(List.cons.inj h).2] at hζ
    simp at hζ
  | succ k ih =>
    rw [← PMF.mem_support_iff] at h
    obtain ⟨x, y, rest, hl, hprev, hy⟩ := mem_support_chainLaw_succ h
    obtain ⟨hξ, hH⟩ := List.cons.inj hl
    rw [hH] at hζ
    rw [hξ]
    have hxy : x ≤ y := by
      rcases lt_or_ge (blocks x) 2 with hx | hx
      · exact le_of_eq ((mem_support_jumpLaw_of_absorbed hx).mp hy).symm
      · exact ((mem_support_jumpLaw hx).mp hy).1
    rcases List.mem_cons.mp hζ with rfl | hmem
    · exact hxy
    · exact le_trans (ih (ξ := x) (H := rest) ((PMF.mem_support_iff _ _).mp hprev) hmem) hxy

/-- **A history of positive probability ending at the report of `Δ` is constant.** Reports are
monotone along a trajectory and never below the report of `Δ`. -/
theorem eq_replicate_of_reportLaw_ne_zero {s : Fin n → Fin n} {k : ℕ} {H : List (ER n)}
    (h : reportLaw s k (observed s ⊥ :: H) ≠ 0) : H = List.replicate k (observed s ⊥) := by
  rw [reportLaw_apply] at h
  obtain ⟨l, hl⟩ : ∃ l : List (ER n), chainLaw n k l *
      (if l.map (observed s) = observed s ⊥ :: H then 1 else 0) ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact h (ENNReal.tsum_eq_zero.mpr hcon)
  have hmap : l.map (observed s) = observed s ⊥ :: H := by
    by_contra hne
    rw [if_neg hne, mul_zero] at hl
    exact hl rfl
  have h0 : chainLaw n k l ≠ 0 := by
    intro hz
    rw [hz, zero_mul] at hl
    exact hl rfl
  obtain ⟨ξ, rest, rfl⟩ : ∃ ξ rest, l = ξ :: rest := by
    cases l with
    | nil => exact absurd hmap (List.cons_ne_nil _ _).symm
    | cons ξ rest => exact ⟨ξ, rest, rfl⟩
  have hlen := chainLaw_length k ((PMF.mem_support_iff _ _).mpr h0)
  obtain ⟨hhead, htail⟩ := List.cons.inj hmap
  rw [← htail, List.eq_replicate_iff, List.length_map]
  refine ⟨by simpa using hlen, fun b hb ↦ ?_⟩
  obtain ⟨ζ, hζ, rfl⟩ := List.mem_map.mp hb
  refine le_antisymm ?_ (observed_mono s bot_le)
  rw [← hhead]
  exact observed_mono s (le_of_mem_tail h0 hζ)

/-- **A report with one block is absorbing.** -/
theorem reportJumpLaw_eq_pure {s : Fin n → Fin n} [NeZero n] {ξ : ER n}
    (h : blocks (observed s ξ) ≤ 1) : reportJumpLaw s ξ = PMF.pure (observed s ξ) := by
  have hsupp : ∀ η ∈ (jumpLaw ξ).support, observed s η = observed s ξ := by
    intro η hη
    have hle : ξ ≤ η := by
      rcases lt_or_ge (blocks ξ) 2 with hk | hk
      · exact le_of_eq ((mem_support_jumpLaw_of_absorbed hk).mp hη).symm
      · exact ((mem_support_jumpLaw hk).mp hη).1
    have hmono := observed_mono s hle
    have hb : blocks (observed s η) ≤ blocks (observed s ξ) :=
      Nat.card_le_card_of_surjective (blockMap hmono) (blockMap_surjective hmono)
    have hpos := blocks_pos (observed s η)
    exact (eq_of_le_of_blocks_eq hmono (by omega)).symm
  refine PMF.ext fun y ↦ ?_
  rw [reportJumpLaw, PMF.map_apply, PMF.pure_apply]
  by_cases hy : y = observed s ξ
  · rw [if_pos hy, ← PMF.tsum_coe (jumpLaw ξ)]
    refine tsum_congr fun η ↦ ?_
    by_cases hη : jumpLaw ξ η = 0
    · rw [hη, ite_self]
    · rw [if_pos (hy.trans (hsupp η ((PMF.mem_support_iff _ _).mpr hη)).symm)]
  · rw [if_neg hy]
    refine ENNReal.tsum_eq_zero.mpr fun η ↦ ?_
    by_cases hη : jumpLaw ξ η = 0
    · rw [hη, ite_self]
    · rw [if_neg fun h ↦ hy (h.trans (hsupp η ((PMF.mem_support_iff _ _).mpr hη)))]

/-- **The width-two law.** At the report of `Δ` after `k` jumps, the conditional law of the next
report after the constant history; at any other report, the point mass at that report. -/
def widthTwoLaw (s : Fin n → Fin n) (k : ℕ) (x y : ER n) : ENNReal :=
  if x = observed s ⊥ then
    reportLaw s (k + 1) (y :: List.replicate (k + 1) x) / reportLaw s k (List.replicate (k + 1) x)
  else if y = x then 1 else 0

/-- **The width-two law gives every report history.**

Assumes: the interface occupies exactly two graph states. -/
theorem reportLaw_succ_eq_widthTwoLaw {s : Fin n → Fin n} (hw : Linkage.width s = 2) (k : ℕ)
    (x y : ER n) (H : List (ER n)) :
    reportLaw s (k + 1) (y :: x :: H) = reportLaw s k (x :: H) * widthTwoLaw s k x y := by
  have hn : 2 ≤ n := by
    have h := Linkage.width_le_card s
    rw [Fintype.card_fin, hw] at h
    exact h
  haveI : NeZero n := ⟨by omega⟩
  by_cases hx : x = observed s ⊥
  · subst hx
    rw [widthTwoLaw, if_pos rfl]
    by_cases hH : H = List.replicate k (observed s ⊥)
    · subst hH
      rw [← List.replicate_succ]
      by_cases h0 : reportLaw s k (List.replicate (k + 1) (observed s ⊥)) = 0
      · rw [h0, zero_mul, List.replicate_succ]
        rw [List.replicate_succ] at h0
        exact reportLaw_succ_eq_zero h0 y
      · rw [div_eq_mul_inv, mul_left_comm, ENNReal.mul_inv_cancel h0 (PMF.apply_ne_top _ _),
          mul_one]
    · have hzero : reportLaw s k (observed s ⊥ :: H) = 0 := by
        by_contra hne
        exact hH (eq_replicate_of_reportLaw_ne_zero hne)
      rw [reportLaw_succ_eq_zero hzero y, hzero, zero_mul]
  · rw [widthTwoLaw, if_neg hx]
    refine reportLaw_succ_eq_mul (fun y ↦ if y = x then 1 else 0) (fun ξ _ _ hobs y' ↦ ?_) y H
    have hlt : blocks (observed s ξ) ≤ 1 := by
      have hle : observed s ⊥ ≤ observed s ξ := observed_mono s bot_le
      have hb : blocks (observed s ξ) ≤ blocks (observed s ⊥) :=
        Nat.card_le_card_of_surjective (blockMap hle) (blockMap_surjective hle)
      have hne : blocks (observed s ⊥) ≠ blocks (observed s ξ) := fun hbe ↦
        hx (hobs.symm.trans (eq_of_le_of_blocks_eq hle hbe).symm)
      rw [observed_bot, blocks_graphKer, hw] at hb hne
      omega
    rw [reportJumpLaw_eq_pure hlt, PMF.pure_apply, hobs]

/-- **At width two the report is Markov in the jump count**, with `widthTwoLaw` as law.

Assumes: the interface occupies exactly two graph states. -/
theorem isReportInhomogeneousMarkov_of_width_eq_two {s : Fin n → Fin n}
    (hw : Linkage.width s = 2) : IsReportInhomogeneousMarkov s :=
  ⟨widthTwoLaw s, reportLaw_succ_eq_widthTwoLaw hw⟩

/-- **The smallest instance, first step**: the width-two law stays at the report of `Δ` with
probability `1/3` after no jump. -/
theorem example_widthTwoLaw_zero :
    widthTwoLaw exampleInterface 0 (observed exampleInterface ⊥) (observed exampleInterface ⊥) =
      3⁻¹ := by
  rw [widthTwoLaw, if_pos rfl]
  exact example_stay_given_one

/-- **The smallest instance, second step**: after one jump it stays with probability zero. -/
theorem example_widthTwoLaw_one :
    widthTwoLaw exampleInterface 1 (observed exampleInterface ⊥) (observed exampleInterface ⊥) =
      0 := by
  rw [widthTwoLaw, if_pos rfl]
  exact example_stay_given_two

/-- The smallest instance is Markov in the jump count, though not time-homogeneous. -/
theorem example_isReportInhomogeneousMarkov : IsReportInhomogeneousMarkov exampleInterface :=
  isReportInhomogeneousMarkov_of_width_eq_two example_width

end

end Descent.Pangenome.GraphCoalescent.ReportInhomogeneousMarkov
