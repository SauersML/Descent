/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.GraphCoalescent.HiddenLumpability
import Descent.Pangenome.GraphCoalescent.RankedHistoryLaw

assert_below Descent.PopGen Descent.Spectral Descent.Blindness Descent.Conditionals
assert_below Descent.Portability Descent.Decision Descent.Program

/-!
# The hidden state of the labeled jump chain is a Markov chain

The spec is `PANGENOME_HIDDEN_CLOCK.md` §3, Theorem A: the report together with its loads is a
strong lumping of the labeled coalescent. `Descent.Pangenome.GraphCoalescent.HiddenLumpability`
proves the counting form, equal numbers of covers into every hidden state
(`card_covers_hiddenState_eq`). This file turns it into the probabilistic statement under the
corpus jump chain `Coalescent.jumpLaw`, the uniform law on covers, and its trajectory law
`Coalescent.chainLaw`.

The hidden jump law `hiddenJumpLaw s ξ` is the law of the hidden state after one jump from `ξ`.
Away from absorption its mass on a hidden state is the number of covers landing there divided by
`C(K, 2)` (`hiddenJumpLaw_apply`). The block count `K` is read off the hidden state
(`blocks_eq_sum_hiddenState`), so two labeled states with the same hidden state have the same
hidden jump law (`hiddenJumpLaw_eq_of_hiddenState_eq`). The hidden kernel `hiddenKernel s X` is
therefore a function of the hidden state alone, and it is the hidden jump law of every labeled
state carrying `X` (`hiddenKernel_hiddenState`). Its jump probabilities are `C(L_C, 2) / C(K, 2)`
into an invisible target and `L_C L_D / C(K, 2)` into a visible one
(`hiddenKernel_invisibleTarget`, `hiddenKernel_visibleTarget`, and their real forms).

The Markov property. The hidden trajectory `hiddenChainLaw s j`, the labeled trajectory after `j`
jumps with every state replaced by its hidden state, satisfies the trajectory recursion of a
Markov chain with kernel `hiddenKernel s` (`hiddenChainLaw_succ`), from the single hidden state
of the singletons (`hiddenChainLaw_zero`). The head law satisfies the one-step recursion
(`blockLaw_map_hiddenState_succ`).

Scope. The chain here is the jump chain in discrete time, with Kingman's unit rate per cover
giving its uniform steps. The continuous-time holding times are not constructed, as in
`Descent.Coalescent.Trajectory`.

## Empirical status

None. The bodies here are probability mass functions on a finite state space and counts of covers,
so no measurement can bear on them.
-/

namespace Descent.Pangenome.GraphCoalescent

open Coalescent Finset
open scoped Classical

noncomputable section

/-! ### The law of the hidden state after one jump -/

/-- **The hidden jump law**: the law of the hidden state after one jump of the labeled chain from
`ξ`. -/
def hiddenJumpLaw {n : ℕ} (s : Fin n → Fin n) (ξ : ER n) : PMF (ER n × (Fin n → ℕ)) :=
  (jumpLaw ξ).map (hiddenState s)

/-- Away from absorption the hidden jump law puts on a hidden state the number of covers landing
there, divided by `C(K, 2)`. -/
theorem hiddenJumpLaw_apply {n : ℕ} (s : Fin n → Fin n) {ξ : ER n} (hk : 2 ≤ blocks ξ)
    (v : ER n × (Fin n → ℕ)) :
    hiddenJumpLaw s ξ v =
      (Nat.card {η : ER n // Covers ξ η ∧ hiddenState s η = v} : ENNReal) *
        (((blocks ξ).choose 2 : ℕ) : ENNReal)⁻¹ := by
  have hcount : (Nat.card {η : ER n // Covers ξ η ∧ hiddenState s η = v} : ENNReal) *
      (((blocks ξ).choose 2 : ℕ) : ENNReal)⁻¹ =
        ∑ a : ER n, if Covers ξ a ∧ hiddenState s a = v then
          (((blocks ξ).choose 2 : ℕ) : ENNReal)⁻¹ else 0 := by
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul,
      Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [hiddenJumpLaw, PMF.map_apply, tsum_fintype, hcount]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  by_cases hcov : Covers ξ a
  · by_cases hv : hiddenState s a = v
    · rw [if_pos (show v = hiddenState s a from hv.symm),
        if_pos (show Covers ξ a ∧ hiddenState s a = v from ⟨hcov, hv⟩),
        jumpLaw_apply_cover hk hcov]
    · rw [if_neg (show ¬ v = hiddenState s a from fun h ↦ hv h.symm),
        if_neg (show ¬ (Covers ξ a ∧ hiddenState s a = v) from fun h ↦ hv h.2)]
  · have hzero : jumpLaw ξ a = 0 :=
      (PMF.apply_eq_zero_iff _ _).mpr fun hmem ↦ hcov ((mem_support_jumpLaw hk).mp hmem)
    rw [hzero, ite_self,
      if_neg (show ¬ (Covers ξ a ∧ hiddenState s a = v) from fun h ↦ hcov h.1)]

/-- An absorbed labeled state keeps its hidden state. -/
theorem hiddenJumpLaw_of_absorbed {n : ℕ} (s : Fin n → Fin n) {ξ : ER n} (hk : blocks ξ < 2) :
    hiddenJumpLaw s ξ = PMF.pure (hiddenState s ξ) := by
  rw [hiddenJumpLaw, jumpLaw, dif_neg (by omega), PMF.pure_map]

/-- **The block count is read off the hidden state**: it is the sum, over the report classes, of
the load at a representative. -/
theorem blocks_eq_sum_hiddenState {n : ℕ} (s : Fin n → Fin n) (ξ : ER n) :
    blocks ξ = ∑ C : Quotient (hiddenState s ξ).1, (hiddenState s ξ).2 C.out := by
  rw [← sum_hiddenLoad s ξ]
  refine Finset.sum_congr rfl fun C _ ↦ ?_
  show hiddenLoad s ξ C = hiddenLoad s ξ (Quotient.mk (observed s ξ) C.out)
  rw [Quotient.out_eq]

/-- Two labeled states with the same hidden state have the same number of blocks. -/
theorem blocks_eq_of_hiddenState_eq {n : ℕ} (s : Fin n → Fin n) {ξ ξ' : ER n}
    (h : hiddenState s ξ = hiddenState s ξ') : blocks ξ = blocks ξ' := by
  rw [blocks_eq_sum_hiddenState s ξ, blocks_eq_sum_hiddenState s ξ', h]

/-- **Strong lumpability (spec Theorem A), probabilistic form.** Two labeled states with the same
hidden state have the same hidden jump law. -/
theorem hiddenJumpLaw_eq_of_hiddenState_eq {n : ℕ} (s : Fin n → Fin n) {ξ ξ' : ER n}
    (h : hiddenState s ξ = hiddenState s ξ') : hiddenJumpLaw s ξ = hiddenJumpLaw s ξ' := by
  have hblocks := blocks_eq_of_hiddenState_eq s h
  by_cases hk : 2 ≤ blocks ξ
  · have hk' : 2 ≤ blocks ξ' := hblocks ▸ hk
    refine PMF.ext fun v ↦ ?_
    rw [hiddenJumpLaw_apply s hk, hiddenJumpLaw_apply s hk', card_covers_hiddenState_eq s h v,
      hblocks]
  · have hk' : blocks ξ' < 2 := by omega
    rw [hiddenJumpLaw_of_absorbed s (by omega), hiddenJumpLaw_of_absorbed s hk', h]

/-! ### The hidden kernel -/

/-- **The hidden jump kernel**, a function of the hidden state alone: the hidden jump law of any
labeled state carrying the hidden state, and the point mass at a hidden state no labeled state
carries. -/
def hiddenKernel {n : ℕ} (s : Fin n → Fin n) (X : ER n × (Fin n → ℕ)) :
    PMF (ER n × (Fin n → ℕ)) :=
  if h : ∃ ξ : ER n, hiddenState s ξ = X then hiddenJumpLaw s h.choose else PMF.pure X

/-- The hidden kernel at a labeled state's hidden state is that state's hidden jump law. -/
theorem hiddenKernel_hiddenState {n : ℕ} (s : Fin n → Fin n) (ξ : ER n) :
    hiddenKernel s (hiddenState s ξ) = hiddenJumpLaw s ξ := by
  have hex : ∃ ζ : ER n, hiddenState s ζ = hiddenState s ξ := ⟨ξ, rfl⟩
  rw [hiddenKernel, dif_pos hex]
  exact hiddenJumpLaw_eq_of_hiddenState_eq s hex.choose_spec

/-- **Spec Theorem A, the invisible jump probability** `C(L_C, 2) / C(K, 2)`. -/
theorem hiddenKernel_invisibleTarget {n : ℕ} (s : Fin n → Fin n) {ξ : ER n}
    (hk : 2 ≤ blocks ξ) (x : Fin n) :
    hiddenKernel s (hiddenState s ξ) (invisibleTarget (hiddenState s ξ) x) =
      (((hiddenLoad s ξ (Quotient.mk (observed s ξ) x)).choose 2 : ℕ) : ENNReal) *
        (((blocks ξ).choose 2 : ℕ) : ENNReal)⁻¹ := by
  rw [hiddenKernel_hiddenState, hiddenJumpLaw_apply s hk, card_covers_invisibleTarget]

/-- **Spec Theorem A, the visible jump probability** `L_C L_D / C(K, 2)`. -/
theorem hiddenKernel_visibleTarget {n : ℕ} (s : Fin n → Fin n) {ξ : ER n}
    (hk : 2 ≤ blocks ξ) {x y : Fin n} (hxy : ¬ (observed s ξ).r x y) :
    hiddenKernel s (hiddenState s ξ) (visibleTarget (hiddenState s ξ) x y) =
      ((hiddenLoad s ξ (Quotient.mk (observed s ξ) x) *
          hiddenLoad s ξ (Quotient.mk (observed s ξ) y) : ℕ) : ENNReal) *
        (((blocks ξ).choose 2 : ℕ) : ENNReal)⁻¹ := by
  rw [hiddenKernel_hiddenState, hiddenJumpLaw_apply s hk, card_covers_visibleTarget s ξ hxy]

/-- The invisible jump probability as a real number, `C(L_C, 2) / C(K, 2)`. -/
theorem hiddenKernel_invisibleTarget_toReal {n : ℕ} (s : Fin n → Fin n) {ξ : ER n}
    (hk : 2 ≤ blocks ξ) (x : Fin n) :
    (hiddenKernel s (hiddenState s ξ) (invisibleTarget (hiddenState s ξ) x)).toReal =
      ((hiddenLoad s ξ (Quotient.mk (observed s ξ) x)).choose 2 : ℝ) /
        ((blocks ξ).choose 2 : ℝ) := by
  rw [hiddenKernel_invisibleTarget s hk x, ENNReal.toReal_mul, ENNReal.toReal_inv,
    ENNReal.toReal_natCast, ENNReal.toReal_natCast, div_eq_mul_inv]

/-- The visible jump probability as a real number, `L_C L_D / C(K, 2)`. -/
theorem hiddenKernel_visibleTarget_toReal {n : ℕ} (s : Fin n → Fin n) {ξ : ER n}
    (hk : 2 ≤ blocks ξ) {x y : Fin n} (hxy : ¬ (observed s ξ).r x y) :
    (hiddenKernel s (hiddenState s ξ) (visibleTarget (hiddenState s ξ) x y)).toReal =
      ((hiddenLoad s ξ (Quotient.mk (observed s ξ) x) *
          hiddenLoad s ξ (Quotient.mk (observed s ξ) y) : ℕ) : ℝ) /
        ((blocks ξ).choose 2 : ℝ) := by
  rw [hiddenKernel_visibleTarget s hk hxy, ENNReal.toReal_mul, ENNReal.toReal_inv,
    ENNReal.toReal_natCast, ENNReal.toReal_natCast, div_eq_mul_inv]

/-! ### The Markov chain of hidden states -/

/-- The hidden trajectory law after `j` jumps: the labeled trajectory with every state replaced by
its hidden state. -/
def hiddenChainLaw {n : ℕ} (s : Fin n → Fin n) (j : ℕ) : PMF (List (ER n × (Fin n → ℕ))) :=
  (chainLaw n j).map (List.map (hiddenState s))

/-- The hidden trajectory starts at the hidden state of the singletons. -/
theorem hiddenChainLaw_zero {n : ℕ} (s : Fin n → Fin n) :
    hiddenChainLaw s 0 = PMF.pure [hiddenState s ⊥] := by
  rw [hiddenChainLaw, chainLaw, PMF.pure_map]
  rfl

/-- **The hidden state is a Markov chain with kernel `hiddenKernel`**: the hidden trajectory
after `j + 1` jumps extends the hidden trajectory after `j` jumps by a draw from the hidden kernel
at its current hidden state, which depends on nothing else. -/
theorem hiddenChainLaw_succ {n : ℕ} (s : Fin n → Fin n) (j : ℕ) :
    hiddenChainLaw s (j + 1) = (hiddenChainLaw s j).bind fun L ↦
      match L with
      | [] => PMF.pure []
      | X :: rest => (hiddenKernel s X).map fun Y ↦ Y :: X :: rest := by
  rw [hiddenChainLaw, hiddenChainLaw, chainLaw, PMF.map_bind, PMF.bind_map]
  congr 1
  funext l
  cases l with
  | nil =>
    show (PMF.pure []).map (List.map (hiddenState s)) = PMF.pure []
    rw [PMF.pure_map]
    rfl
  | cons x rest =>
    show ((jumpLaw x).map fun y ↦ y :: x :: rest).map (List.map (hiddenState s)) =
      (hiddenKernel s (hiddenState s x)).map
        fun Y ↦ Y :: hiddenState s x :: rest.map (hiddenState s)
    rw [PMF.map_comp, hiddenKernel_hiddenState, hiddenJumpLaw, PMF.map_comp]
    rfl

/-- **The head law of the hidden chain**: the law of the hidden state after `j + 1` jumps is the
law after `j` jumps propagated by the hidden kernel. -/
theorem blockLaw_map_hiddenState_succ {n : ℕ} (s : Fin n → Fin n) (j : ℕ) :
    (blockLaw n (j + 1)).map (hiddenState s) =
      ((blockLaw n j).map (hiddenState s)).bind (hiddenKernel s) := by
  rw [blockLaw_succ, PMF.map_bind, PMF.bind_map]
  congr 1
  funext ξ
  exact (hiddenKernel_hiddenState s ξ).symm

end

end Descent.Pangenome.GraphCoalescent
