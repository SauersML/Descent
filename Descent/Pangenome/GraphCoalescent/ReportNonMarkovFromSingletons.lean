/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Coalescent.Trajectory
import Descent.Pangenome.GraphCoalescent.HiddenLumpability
import Descent.Pangenome.GraphCoalescent.Visibility

assert_below Descent.PopGen Descent.Spectral Descent.Blindness Descent.Conditionals
assert_below Descent.Portability Descent.Decision Descent.Program

/-!
# From the singletons, a compressed report is not a Markov chain

`MarkovCompressions` classifies the interfaces whose report is a strong lumping of Kingman's
coalescent, a criterion over every pair of states with one report. This module proves a sharper
statement for the one starting point the coalescent actually has. Run the jump chain from the
singletons and read each state through the graph. For every interface of width `w` with
`2 ≤ w < n`, the resulting report sequence is not a Markov chain: no transition law on reports
reproduces the probabilities of its histories.

**The object.** `Coalescent.chainLaw n k` is the law of the jump chain's first `k` jumps from `Δ`,
newest state first. `reportLaw s k` is its image under reading every state through `observed s`:
the law of the report history. `IsReportMarkovFromBot s` says that some transition function `Q` on
reports gives every history step by step,
`P(R₀, …, R_k, R_{k+1}) = P(R₀, …, R_k) · Q(R_k, R_{k+1})`. This says the report sequence is a
time-homogeneous Markov chain started at the report of `Δ`, which is weak lumpability of the jump
chain for this initial state.

**The theorem.** `not_isReportMarkovFromBot`: for `2 ≤ w < n` no such `Q` exists, because two
report histories that end at the same report `Y₀ = graphKer s` predict different next reports.
- After the history `(Y₀)` the report stays at `Y₀` with positive probability, since an invisible
  merger is available (`reportLaw_one_ne_zero`).
- After the history of `n - w + 1` copies of `Y₀` it stays with probability zero. A chain that has
  made that many jumps has fewer than `w` blocks, so it cannot report `Y₀`
  (`reportLaw_replicate_eq_zero`).

A transition function would give both histories the same probability `Q(Y₀, Y₀)` of staying. By
iteration, the history of `k + 1` copies of `Y₀` would have probability `Q(Y₀, Y₀)^k`, which is
positive at every depth.

**Where it is exact.** Take three haplotypes with `0` and `1` in one graph state, the example of
Theorem A. The report of `Δ` stays after one jump with probability `1/3` (`example_reportLaw_one`)
and after two jumps with probability zero (`example_reportLaw_two`). So the conditional probability
of staying is `1/3` given `(Y₀)` and `0` given `(Y₀, Y₀)` (`example_stay_given_one`,
`example_stay_given_two`), and the report sequence is not Markov
(`example_not_isReportMarkovFromBot`).

**The faithful case.** An injective interface reports the chain itself, and the report sequence is
Markov with the jump law as transition function (`isReportMarkovFromBot_of_injective`). This rests
on the step identity of the trajectory law (`chainLaw_succ_apply`).

Significance. Before any correction for hidden lineages, the ancestry a compressed pangenome
reports is not a Markov process for any interface that merges something without collapsing the
panel. The failure is not an artefact of states the chain never visits: it already occurs along
the jump chain from the singletons.

Scope. The process here is the jump chain's report sequence, one report per merger, and Markov
means a transition law that does not depend on the jump count. The jump count is the length of the
history, so a law allowed to depend on it is not refuted here, and for `w = 2` such a law exists.
The holding times of the continuous-time chain are not used.

## Empirical status

None. The bodies here are probabilities of finite trajectories of the jump chain, which Kingman's
unit rates force; the interface is supplied, and no measurement can bear on them.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Pangenome.GraphCoalescent.ReportNonMarkovFromSingletons

open Coalescent

noncomputable section

variable {n : ℕ}

/-! ### The report histories of the jump chain -/

/-- **The step identity of the trajectory law.** A trajectory of `k + 1` jumps is a trajectory of
`k` jumps followed by one draw from the jump law of its current state. -/
theorem chainLaw_succ_apply (k : ℕ) (x y : ER n) (H : List (ER n)) :
    chainLaw n (k + 1) (y :: x :: H) = chainLaw n k (x :: H) * jumpLaw x y := by
  rw [chainLaw, PMF.bind_apply, tsum_eq_single (x :: H)]
  · show chainLaw n k (x :: H) * ((jumpLaw x).map fun y' ↦ y' :: x :: H) (y :: x :: H) = _
    rw [PMF.map_apply, tsum_eq_single y]
    · rw [if_pos rfl]
    · intro y' hy'
      rw [if_neg]
      intro h
      exact hy' (List.cons.inj h).1.symm
  · intro l hl
    match l with
    | [] =>
      show chainLaw n k [] * PMF.pure [] (y :: x :: H) = 0
      rw [PMF.pure_apply, if_neg (List.cons_ne_nil _ _), mul_zero]
    | x' :: rest =>
      show chainLaw n k (x' :: rest) *
        ((jumpLaw x').map fun y' ↦ y' :: x' :: rest) (y :: x :: H) = 0
      rw [PMF.map_apply]
      refine mul_eq_zero_of_right _ (ENNReal.tsum_eq_zero.mpr fun y' ↦ ?_)
      rw [if_neg]
      intro h
      exact hl (List.cons.inj h).2.symm

/-- **The law of the report history** after `k` jumps from the singletons, newest report
first. -/
def reportLaw (s : Fin n → Fin n) (k : ℕ) : PMF (List (ER n)) :=
  (chainLaw n k).map (List.map (observed s))

/-- Before any jump the report history is the report of `Δ`. -/
theorem reportLaw_zero (s : Fin n → Fin n) : reportLaw s 0 = PMF.pure [observed s ⊥] := by
  rw [reportLaw, chainLaw, PMF.pure_map, List.map_cons, List.map_nil]

/-- **The report sequence is a Markov chain from the singletons**: some transition function on
reports gives the probability of every report history step by step. -/
def IsReportMarkovFromBot (s : Fin n → Fin n) : Prop :=
  ∃ Q : ER n → ER n → ENNReal, ∀ (k : ℕ) (x y : ER n) (H : List (ER n)),
    reportLaw s (k + 1) (y :: x :: H) = reportLaw s k (x :: H) * Q x y

/-- **The faithful case.** An injective interface reports the chain itself, and the report
sequence is a Markov chain with the jump law as transition function. -/
theorem isReportMarkovFromBot_of_injective {s : Fin n → Fin n} (hs : Function.Injective s) :
    IsReportMarkovFromBot s := by
  have hobs : observed s = id := funext (observed_eq_of_injective hs)
  have hmap : List.map (id : ER n → ER n) = id := funext List.map_id
  have hid : ∀ k, reportLaw s k = chainLaw n k := fun k ↦ by
    rw [reportLaw, hobs, hmap, PMF.map_id]
  refine ⟨fun x y ↦ jumpLaw x y, fun k x y H ↦ ?_⟩
  rw [hid, hid]
  exact chainLaw_succ_apply k x y H

/-- The identity interface reports a Markov chain. -/
theorem isReportMarkovFromBot_id : IsReportMarkovFromBot (id : Fin n → Fin n) :=
  isReportMarkovFromBot_of_injective Function.injective_id

/-! ### Two histories, two predictions -/

/-- **After one jump the report can stay.** If the interface merges two haplotypes, the first
jump is invisible with positive probability, so the report history `(Y₀, Y₀)` has positive
probability. -/
theorem reportLaw_one_ne_zero {s : Fin n → Fin n} {a b : Fin n} (hab : a ≠ b)
    (hsab : s a = s b) : reportLaw s 1 [observed s ⊥, observed s ⊥] ≠ 0 := by
  have hn : 2 ≤ n := by
    have ha := a.isLt
    have hb := b.isLt
    have hne : a.val ≠ b.val := fun h ↦ hab (Fin.ext h)
    omega
  have hAB : Quotient.mk (⊥ : ER n) a ≠ Quotient.mk (⊥ : ER n) b :=
    fun hq ↦ hab (Quotient.exact hq)
  have hrel : (observed s ⊥).r a b := by
    rw [observed_bot, graphKer_rel_iff]
    exact hsab
  have hblocks : 2 ≤ blocks (Delta n) := by
    rw [blocks_bot]
    exact hn
  rw [← PMF.mem_support_iff, reportLaw, PMF.mem_support_map_iff]
  refine ⟨[merge ⊥ (Quotient.mk ⊥ a) (Quotient.mk ⊥ b), ⊥], ?_, ?_⟩
  · rw [chainLaw, chainLaw, PMF.mem_support_bind_iff]
    refine ⟨[Delta n], ?_, ?_⟩
    · rw [PMF.mem_support_pure_iff]
    · show [merge ⊥ (Quotient.mk ⊥ a) (Quotient.mk ⊥ b), ⊥] ∈
        ((jumpLaw (Delta n)).map fun y ↦ y :: [Delta n]).support
      rw [PMF.mem_support_map_iff]
      exact ⟨merge ⊥ (Quotient.mk ⊥ a) (Quotient.mk ⊥ b),
        (mem_support_jumpLaw hblocks).mpr (merge_covers ⊥ hAB), rfl⟩
  · rw [List.map_cons, List.map_cons, List.map_nil, observed_merge_of_rel hAB hrel]

/-- **Too many jumps to stay.** After `k` jumps with `n - k < w`, the chain has fewer blocks than
the report of `Δ` has components, so the history of `k + 1` copies of that report has probability
zero. -/
theorem reportLaw_replicate_eq_zero {s : Fin n → Fin n} {k : ℕ} (hk : n < Linkage.width s + k)
    (hkn : k < n) : reportLaw s k (List.replicate (k + 1) (observed s ⊥)) = 0 := by
  rw [PMF.apply_eq_zero_iff, reportLaw, PMF.support_map]
  rintro ⟨l, hl, hmap⟩
  obtain ⟨x, rest, rfl⟩ : ∃ x rest, l = x :: rest := by
    cases l with
    | nil => exact absurd rfl (chainLaw_ne_nil k hl)
    | cons x rest => exact ⟨x, rest, rfl⟩
  have hblocks : blocks x + k = n := chainLaw_head_blocks k hkn hl rfl
  have hreport : observed s x = observed s ⊥ := by
    rw [List.replicate_succ, List.map_cons] at hmap
    exact (List.cons.inj hmap).1
  have hcoarse : blocks (observed s x) ≤ blocks x :=
    Nat.card_le_card_of_surjective (blockMap (le_observed s x)) (blockMap_surjective _)
  rw [hreport, observed_bot, blocks_graphKer] at hcoarse
  omega

/-- **From the singletons, a compressed report is not a Markov chain.** For an interface of width
`w` with `2 ≤ w < n`, no transition function on reports gives the probabilities of the report
histories of the jump chain from `Δ`. The report of `Δ` stays after the history `(Y₀)` with
positive probability, and after `n - w + 1` copies of `Y₀` with probability zero. -/
theorem not_isReportMarkovFromBot {s : Fin n → Fin n} (hw : 2 ≤ Linkage.width s)
    (hlt : Linkage.width s < n) : ¬ IsReportMarkovFromBot s := by
  rintro ⟨Q, hQ⟩
  obtain ⟨a, b, c, hab, hsab, -⟩ := exists_witness_of_width hw hlt
  have hiter : ∀ k, reportLaw s k (List.replicate (k + 1) (observed s ⊥)) =
      Q (observed s ⊥) (observed s ⊥) ^ k := by
    intro k
    induction k with
    | zero =>
      rw [pow_zero, reportLaw_zero]
      exact PMF.pure_apply_self _
    | succ k ih =>
      rw [List.replicate_succ, List.replicate_succ, hQ k, ← List.replicate_succ, ih, pow_succ]
  have hstay : Q (observed s ⊥) (observed s ⊥) ≠ 0 := by
    have h1 := hiter 1
    rw [pow_one] at h1
    rw [← h1]
    exact reportLaw_one_ne_zero hab hsab
  have hzero := reportLaw_replicate_eq_zero (s := s) (k := n - Linkage.width s + 1)
    (by omega) (by omega)
  rw [hiter] at hzero
  exact hstay ((pow_eq_zero_iff (by omega)).mp hzero)

/-! ### The smallest instance -/

/-- The example interface occupies two graph states. -/
theorem example_width : Linkage.width exampleInterface = 2 := by
  decide

/-- **The only cover of `Δ` that keeps the example's report is the merger of `0` and `1`.** -/
theorem example_eq_of_covers_observed {η : ER 3} (hcov : Covers ⊥ η)
    (hobs : observed exampleInterface η = observed exampleInterface ⊥) :
    η = merge ⊥ (Quotient.mk ⊥ 0) (Quotient.mk ⊥ 1) := by
  obtain ⟨A, B, hAB, rfl⟩ := (covers_iff_exists_merge ⊥ η).mp hcov
  obtain ⟨u, rfl⟩ := quotient_mk_surjective ⊥ A
  obtain ⟨v, rfl⟩ := quotient_mk_surjective ⊥ B
  have hrel : (observed exampleInterface ⊥).r u v := by
    rw [← hobs]
    exact le_observed _ _ (merge_rel ⊥ _ _ rfl rfl)
  rw [observed_bot, graphKer_rel_iff] at hrel
  fin_cases u <;> fin_cases v
  all_goals first
    | exact absurd rfl hAB
    | exact absurd hrel (by decide)
    | rfl
    | exact merge_comm ⊥ hAB

/-- **The smallest instance, one jump.** From the singletons of three haplotypes with `0` and `1`
in one graph state, the report stays at the report of `Δ` with probability `1/3`. -/
theorem example_reportLaw_one :
    reportLaw exampleInterface 1
      [observed exampleInterface ⊥, observed exampleInterface ⊥] = 3⁻¹ := by
  have hblocks : 2 ≤ blocks (Delta 3) := by
    rw [blocks_bot]
    norm_num
  have hchain : chainLaw 3 1 = (jumpLaw (Delta 3)).map fun y ↦ [y, Delta 3] := by
    rw [chainLaw, chainLaw, PMF.pure_bind]
  rw [reportLaw, hchain, PMF.map_comp, PMF.map_apply,
    tsum_eq_single (merge ⊥ (Quotient.mk ⊥ 0) (Quotient.mk ⊥ 1))]
  · have hcond : [observed exampleInterface ⊥, observed exampleInterface ⊥] =
        (List.map (observed exampleInterface) ∘ fun y ↦ [y, Delta 3])
          (merge ⊥ (Quotient.mk ⊥ 0) (Quotient.mk ⊥ 1)) := by
      rw [Function.comp_apply, List.map_cons, List.map_cons, List.map_nil,
        observed_merge_of_rel example_ne_zero_one example_rel_zero_one]
    have hchoose : Nat.choose 3 2 = 3 := by
      decide
    rw [if_pos hcond, jumpLaw_apply_cover hblocks (merge_covers ⊥ example_ne_zero_one)]
    norm_num [blocks_bot, hchoose]
  · intro y hy
    split_ifs with hcond
    · rw [PMF.apply_eq_zero_iff, mem_support_jumpLaw hblocks]
      intro hcov
      apply hy
      refine example_eq_of_covers_observed hcov ?_
      exact (List.cons.inj hcond).1.symm
    · rfl

/-- **The smallest instance, two jumps.** After two jumps the report of three haplotypes is no
longer the report of `Δ`. -/
theorem example_reportLaw_two :
    reportLaw exampleInterface 2
      [observed exampleInterface ⊥, observed exampleInterface ⊥, observed exampleInterface ⊥] =
      0 :=
  reportLaw_replicate_eq_zero (by rw [example_width]; norm_num) (by norm_num)

/-- **Staying after one jump, given the report of `Δ`**: probability `1/3`. -/
theorem example_stay_given_one :
    reportLaw exampleInterface 1 [observed exampleInterface ⊥, observed exampleInterface ⊥] /
      reportLaw exampleInterface 0 [observed exampleInterface ⊥] = 3⁻¹ := by
  rw [example_reportLaw_one, reportLaw_zero, PMF.pure_apply_self, div_one]

/-- **Staying after two jumps, given two reports of `Δ`**: probability zero. -/
theorem example_stay_given_two :
    reportLaw exampleInterface 2
        [observed exampleInterface ⊥, observed exampleInterface ⊥, observed exampleInterface ⊥] /
      reportLaw exampleInterface 1 [observed exampleInterface ⊥, observed exampleInterface ⊥] =
      0 := by
  rw [example_reportLaw_two, ENNReal.zero_div]

/-- **The smallest instance is not Markov.** The example's report sequence from the singletons
has no transition function. -/
theorem example_not_isReportMarkovFromBot : ¬ IsReportMarkovFromBot exampleInterface :=
  not_isReportMarkovFromBot example_width.ge (by rw [example_width]; norm_num)

end

end Descent.Pangenome.GraphCoalescent.ReportNonMarkovFromSingletons
