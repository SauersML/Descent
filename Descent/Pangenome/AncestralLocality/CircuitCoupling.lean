/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.AncestralLocality.LocalityCoupling
import Descent.Pangenome.AncestralLocality.SupportChainDynkin

assert_below Descent.PopGen Descent.Spectral Descent.Blindness Descent.Conditionals
assert_below Descent.Portability Descent.Decision Descent.Program

/-!
# Corollary 8.1 for the circuit's own laws

`ANCESTRAL_LOCALITY.md` §9. `LocalityCoupling` proves Corollary 8.1 as a coupling inequality: two
evaluations on one probability space that coincide off an escape event have sample laws within
total variation the probability of escape. This module shows that the backward circuit supplies
such couplings for its own laws, on the support chain truncated after `M` decisions of
`SupportChainDynkin`.

Two inputs. The probability space is the law `supportChainLaw r c A n M T` of the chain itself. A
state that has not reached directed distance `ℓ` holds only coordinates of the ball `B_{ℓ-1}(A)`
(`mem_lightBall_of_not_escaped`), so an evaluation that reads its input only on the supports takes
the same value on two inputs that agree on the ball. The two sample laws are therefore within total
variation the escape probability, and with `sum_supportChainLaw_escape_le` this is (9.3) with the
explicit bound `min {1, n|A| e^{D(1+2a)T} / a^ℓ}` (`totalVariation_supportChainLaw_inputs_le`), or
`min {1, n|A| e^{DT} (2eDT/ℓ)^ℓ}` at the radius of (9.2)
(`totalVariation_supportChainLaw_inputs_le_radius`).

The truncated checking graph. Events drive the chain: a decision along `i → j` on a slot, taken when
the slot's support contains `i` (`supportChainBranch`), and a coalescence of two occupied slots
(`coalesceTags`), with the jumps of `supportChainRate` (`supportChainStep`). On the induced checking
graph of a ball a decision along an edge leaving the ball never happens, with no renormalization
(`truncatedSupportChainStep`). The slots not yet filled by a decision stay empty
(`unfilledSlotsEmpty_supportChainStart`, `unfilledSlotsEmpty_supportChainStep`), so escape is
permanent along the full circuit (`supportChainStep_escaped`, `foldl_supportChainStep_escaped`). A
full step whose result has not escaped runs along an edge inside the ball, and the truncated step
is the same step (`truncatedSupportChainStep_eq`). Driven by the same events from `n` arguments
carrying `A`, the two circuits end in the same state unless the full circuit has escaped
(`foldl_truncatedSupportChainStep_eq`); applied to every prefix, they agree until the first escape.
Their own sample laws on one finite space of driving events are within total variation the weight
of escape (`totalVariation_truncatedSupportChain_le`). When the events give the full circuit the law
`supportChainLaw r c A n M T`, that weight is bounded by (9.1)
(`totalVariation_truncatedSupportChain_le_exp`).

Scope. The chain has no path space: the space of driving events, and the statement that it gives
the full circuit the law `supportChainLaw`, are hypotheses of the truncated-graph bounds. The
two-input bounds need neither, because their probability space is the chain law. The chain is the
circuit truncated after `M` decisions, as in `SupportChainDynkin`.

## Empirical status

None. The bodies here are finite sums, list recursions and a chain of stated bounds: the rates,
the events and the evaluations are supplied, and no measurement enters any statement.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Descent.Pangenome.AncestralLocality

open Finset

noncomputable section

/-! ### The event-driven circuit -/

/-- An event driving the support chain: a decision along the checking edge `source → target` on the
argument in a slot, or the coalescence of the arguments in two slots. -/
inductive SupportChainEvent (n M : ℕ) (V : Type*)
  | decision (slot : Fin (n + M)) (source target : V)
  | coalescence (first second : Fin (n + M))

section Circuit

variable {V : Type*} [DecidableEq V] {n M : ℕ}

/-- One event of the full circuit, with the jumps of `supportChainRate`: a decision on a slot whose
support contains the source is `supportChainBranch`, a coalescence of two occupied slots, the first
before the second, is `coalesceTags`, and every other event leaves the state unchanged. -/
def supportChainStep (x : SupportChainState V n M) :
    SupportChainEvent n M V → SupportChainState V n M
  | .decision slot source target =>
    if source ∈ x.1 slot then supportChainBranch x slot source target else x
  | .coalescence first second =>
    if first < second ∧ (x.1 first).Nonempty ∧ (x.1 second).Nonempty then
      (coalesceTags first second x.1, x.2)
    else x

/-- One event of the circuit on the induced checking graph of `ball`: a decision along an edge
leaving the ball never happens, and every other event is as in the full circuit. -/
def truncatedSupportChainStep (ball : Finset V) (x : SupportChainState V n M) :
    SupportChainEvent n M V → SupportChainState V n M
  | .decision slot source target =>
    if source ∈ ball ∧ target ∈ ball then supportChainStep x (.decision slot source target)
    else x
  | .coalescence first second => supportChainStep x (.coalescence first second)

/-- The slots not yet filled by a decision are empty: every slot at or after `n + k`, with `k` the
number of decisions taken, carries the empty support. -/
def UnfilledSlotsEmpty (x : SupportChainState V n M) : Prop :=
  ∀ slot : Fin (n + M), n + (x.2 : ℕ) ≤ slot → x.1 slot = ∅

omit [DecidableEq V] in
/-- The initial state has empty unfilled slots. -/
theorem unfilledSlotsEmpty_supportChainStart (A : Finset V) (n M : ℕ) :
    UnfilledSlotsEmpty (supportChainStart A n M) := by
  intro slot hslot
  change n + ((0 : Fin (M + 1)) : ℕ) ≤ slot at hslot
  rw [Fin.val_zero, add_zero] at hslot
  have hbound : (slot : ℕ) - n < M := by omega
  have hsplit : slot = Fin.natAdd n ⟨(slot : ℕ) - n, hbound⟩ := by
    ext
    simp only [Fin.coe_natAdd]
    omega
  change Fin.append (fun _ : Fin n ↦ A) (fun _ : Fin M ↦ (∅ : Finset V)) slot = ∅
  rw [hsplit, Fin.append_right]

/-- Assumes: a state whose unfilled slots are empty. A step of the full circuit keeps them empty. -/
theorem unfilledSlotsEmpty_supportChainStep {x : SupportChainState V n M}
    (hx : UnfilledSlotsEmpty x) (event : SupportChainEvent n M V) :
    UnfilledSlotsEmpty (supportChainStep x event) := by
  cases event with
  | decision slot source target =>
    simp only [supportChainStep]
    split_ifs with hsource
    · unfold supportChainBranch
      split_ifs with hcount
      · intro other hother
        change n + ((x.2 : ℕ) + 1) ≤ other at hother
        have hnew : other ≠ ⟨n + (x.2 : ℕ), by omega⟩ := by
          intro h
          have hval : (other : ℕ) = n + (x.2 : ℕ) := congrArg Fin.val h
          omega
        have hold : other ≠ slot := by
          intro h
          have hempty := hx slot (by rw [← h]; omega)
          rw [hempty] at hsource
          simp at hsource
        change Function.update (Function.update x.1 slot (insert target (x.1 slot)))
          ⟨n + (x.2 : ℕ), _⟩ {source, target} other = ∅
        rw [Function.update_apply, if_neg hnew, Function.update_apply, if_neg hold]
        exact hx other (by omega)
      · exact hx
    · exact hx
  | coalescence first second =>
    simp only [supportChainStep]
    split_ifs with hcoalesce
    · intro other hother
      change n + (x.2 : ℕ) ≤ other at hother
      have hfirst : (first : ℕ) < n + (x.2 : ℕ) := by
        by_contra hlate
        have hempty := hx first (by omega)
        rw [hempty] at hcoalesce
        simp at hcoalesce
      have hsecond : (second : ℕ) < n + (x.2 : ℕ) := by
        by_contra hlate
        have hempty := hx second (by omega)
        rw [hempty] at hcoalesce
        simp at hcoalesce
      have hne₁ : other ≠ first := fun h ↦ by rw [h] at hother; omega
      have hne₂ : other ≠ second := fun h ↦ by rw [h] at hother; omega
      change coalesceTags first second x.1 other = ∅
      rw [coalesceTags_apply, if_neg hne₁, if_neg hne₂]
      exact hx other hother
    · exact hx

variable [Fintype V]

/-- The escape event of a chain state, on the multiset of its slot supports: some slot holds a
coordinate outside every ball of radius below `ℓ`. -/
theorem mem_escapeSet_map_iff {r : V → V → ℝ} {A : Finset V} {ℓ : ℕ}
    (x : SupportChainState V n M) :
    univ.val.map x.1 ∈ escapeSet r A ℓ ↔ ∃ slot, ∃ v ∈ x.1 slot, ∀ k < ℓ, v ∉ lightBall r A k := by
  constructor
  · rintro ⟨S, hS, v, hv, hfar⟩
    obtain ⟨slot, -, rfl⟩ := Multiset.mem_map.mp hS
    exact ⟨slot, v, hv, hfar⟩
  · rintro ⟨slot, v, hv, hfar⟩
    exact ⟨x.1 slot, Multiset.mem_map.mpr ⟨slot, Finset.mem_univ slot, rfl⟩, v, hv, hfar⟩

/-- A state that has not reached directed distance `ℓ` holds only coordinates of the ball
`B_{ℓ-1}(A)`. Assumes: a state outside the escape event. -/
theorem mem_lightBall_of_not_escaped {r : V → V → ℝ} {A : Finset V} {ℓ : ℕ}
    {x : SupportChainState V n M} (hx : univ.val.map x.1 ∉ escapeSet r A ℓ) {slot : Fin (n + M)}
    {v : V} (hv : v ∈ x.1 slot) : v ∈ lightBall r A (ℓ - 1) := by
  by_contra hout
  exact hx ((mem_escapeSet_map_iff x).mpr
    ⟨slot, v, hv, fun k hk hin ↦ hout (lightBall_mono r A (by omega : k ≤ ℓ - 1) hin)⟩)

/-- Escape is permanent under a step of the full circuit. Assumes: a state with empty unfilled
slots that has reached directed distance `ℓ`. -/
theorem supportChainStep_escaped {r : V → V → ℝ} {A : Finset V} {ℓ : ℕ}
    {x : SupportChainState V n M} (hx : UnfilledSlotsEmpty x)
    (hescaped : univ.val.map x.1 ∈ escapeSet r A ℓ) (event : SupportChainEvent n M V) :
    univ.val.map (supportChainStep x event).1 ∈ escapeSet r A ℓ := by
  obtain ⟨slot, v, hv, hfar⟩ := (mem_escapeSet_map_iff x).mp hescaped
  refine (mem_escapeSet_map_iff _).mpr ?_
  cases event with
  | decision a source target =>
    simp only [supportChainStep]
    split_ifs with hsource
    · unfold supportChainBranch
      split_ifs with hcount
      · have hnew : slot ≠ ⟨n + (x.2 : ℕ), by omega⟩ := by
          intro h
          have hval : (slot : ℕ) = n + (x.2 : ℕ) := congrArg Fin.val h
          have hempty := hx slot (by omega)
          rw [hempty] at hv
          simp at hv
        refine ⟨slot, v, ?_, hfar⟩
        change v ∈ Function.update (Function.update x.1 a (insert target (x.1 a)))
          ⟨n + (x.2 : ℕ), _⟩ {source, target} slot
        rw [Function.update_apply, if_neg hnew, Function.update_apply]
        split_ifs with hslot
        · rw [hslot] at hv
          exact Finset.mem_insert_of_mem hv
        · exact hv
      · exact ⟨slot, v, hv, hfar⟩
    · exact ⟨slot, v, hv, hfar⟩
  | coalescence first second =>
    simp only [supportChainStep]
    split_ifs with hcoalesce
    · have hsecond : second ≠ first := hcoalesce.1.ne'
      change ∃ other, ∃ u ∈ coalesceTags first second x.1 other, ∀ k < ℓ, u ∉ lightBall r A k
      by_cases hfirst : slot = first
      · refine ⟨second, v, ?_, hfar⟩
        rw [coalesceTags_apply, if_neg hsecond, if_pos (rfl : second = second)]
        rw [hfirst] at hv
        exact Finset.mem_union_left _ hv
      · by_cases hlast : slot = second
        · refine ⟨second, v, ?_, hfar⟩
          rw [coalesceTags_apply, if_neg hsecond, if_pos (rfl : second = second)]
          rw [hlast] at hv
          exact Finset.mem_union_right _ hv
        · refine ⟨slot, v, ?_, hfar⟩
          rw [coalesceTags_apply, if_neg hfirst, if_neg hlast]
          exact hv
    · exact ⟨slot, v, hv, hfar⟩

/-- Escape is permanent along the full circuit. Assumes: a state with empty unfilled slots that has
reached directed distance `ℓ`. -/
theorem foldl_supportChainStep_escaped {r : V → V → ℝ} {A : Finset V} {ℓ : ℕ}
    (events : List (SupportChainEvent n M V)) :
    ∀ x : SupportChainState V n M, UnfilledSlotsEmpty x →
      univ.val.map x.1 ∈ escapeSet r A ℓ →
        univ.val.map (events.foldl supportChainStep x).1 ∈ escapeSet r A ℓ := by
  induction events with
  | nil => intro x _ hescaped; exact hescaped
  | cons event rest ih =>
    intro x hx hescaped
    exact ih _ (unfilledSlotsEmpty_supportChainStep hx event)
      (supportChainStep_escaped hx hescaped event)

/-- Assumes: a step of the full circuit whose result has not reached directed distance `ℓ`. The
circuit on the induced checking graph of `B_{ℓ-1}(A)` takes the same step. -/
theorem truncatedSupportChainStep_eq {r : V → V → ℝ} {A : Finset V} {ℓ : ℕ}
    {x : SupportChainState V n M} {event : SupportChainEvent n M V}
    (hresult : univ.val.map (supportChainStep x event).1 ∉ escapeSet r A ℓ) :
    truncatedSupportChainStep (lightBall r A (ℓ - 1)) x event = supportChainStep x event := by
  cases event with
  | decision slot source target =>
    by_cases hsource : source ∈ x.1 slot
    · by_cases hcount : (x.2 : ℕ) < M
      · have hparent : (supportChainStep x (.decision slot source target)).1
            ⟨n + (x.2 : ℕ), by omega⟩ = {source, target} := by
          simp only [supportChainStep, if_pos hsource, supportChainBranch, dif_pos hcount,
            Function.update_self]
        have hsourceMem : source ∈ (supportChainStep x (.decision slot source target)).1
            ⟨n + (x.2 : ℕ), by omega⟩ := by
          rw [hparent]
          exact Finset.mem_insert_self source {target}
        have htargetMem : target ∈ (supportChainStep x (.decision slot source target)).1
            ⟨n + (x.2 : ℕ), by omega⟩ := by
          rw [hparent]
          exact Finset.mem_insert_of_mem (Finset.mem_singleton_self target)
        have hin : source ∈ lightBall r A (ℓ - 1) ∧ target ∈ lightBall r A (ℓ - 1) :=
          ⟨mem_lightBall_of_not_escaped hresult hsourceMem,
            mem_lightBall_of_not_escaped hresult htargetMem⟩
        simp only [truncatedSupportChainStep, if_pos hin]
      · simp only [truncatedSupportChainStep, supportChainStep, if_pos hsource, supportChainBranch,
          dif_neg hcount, ite_self]
    · simp only [truncatedSupportChainStep, supportChainStep, if_neg hsource, ite_self]
  | coalescence first second => rfl

/-- Spec Corollary 8.1, the runs agree until escape. Assumes: a state with empty unfilled slots, and
a list of events along which the full circuit ends outside the escape event. The circuit on the
induced checking graph of `B_{ℓ-1}(A)`, driven by the same events, ends in the same state. Applied
to every prefix of a run, the two circuits agree until the first escape. -/
theorem foldl_truncatedSupportChainStep_eq (r : V → V → ℝ) (A : Finset V) (ℓ : ℕ)
    (events : List (SupportChainEvent n M V)) :
    ∀ x : SupportChainState V n M, UnfilledSlotsEmpty x →
      univ.val.map (events.foldl supportChainStep x).1 ∉ escapeSet r A ℓ →
        events.foldl (truncatedSupportChainStep (lightBall r A (ℓ - 1))) x =
          events.foldl supportChainStep x := by
  induction events with
  | nil => intro x _ _; rfl
  | cons event rest ih =>
    intro x hx hfinal
    have hstep : univ.val.map (supportChainStep x event).1 ∉ escapeSet r A ℓ := fun hescaped ↦
      hfinal (foldl_supportChainStep_escaped rest _ (unfilledSlotsEmpty_supportChainStep hx event)
        hescaped)
    show rest.foldl (truncatedSupportChainStep (lightBall r A (ℓ - 1)))
        (truncatedSupportChainStep (lightBall r A (ℓ - 1)) x event) =
      rest.foldl supportChainStep (supportChainStep x event)
    rw [truncatedSupportChainStep_eq hstep]
    exact ih _ (unfilledSlotsEmpty_supportChainStep hx event) hfinal

end Circuit

/-! ### The circuit's own sample laws -/

section Laws

variable {V : Type*} [DecidableEq V] [Fintype V]

open scoped Classical in
/-- Spec (9.3) with explicit numbers. Assumes: nonnegative rates with row sums at most `D`, a
coalescence rate `c ≥ 0`, a base `a ≥ 1`, a horizon `T ≥ 0`, an evaluation of the circuit state as
a finite law on samples that reads its input only on the coordinates of the supports, and two
inputs that agree on the ball `B_{ℓ-1}(A)`. The sample laws on the two inputs, averaged over the law
of the truncated support chain at time `T`, are within total variation
`min {1, n|A| e^{D(1+2a)T} / a^ℓ}`. -/
theorem totalVariation_supportChainLaw_inputs_le {S X : Type*} [Fintype S] {r : V → V → ℝ}
    {c D T a : ℝ} (hr : ∀ i j, 0 ≤ r i j) (hD : ∀ i, ∑ j, r i j ≤ D) (hc : 0 ≤ c) (ha : 1 ≤ a)
    (hT : 0 ≤ T) (A : Finset V) (n M ℓ : ℕ)
    (evaluation : SupportChainState V n M → (V → X) → S → ℝ)
    (hnonneg : ∀ x input s, 0 ≤ evaluation x input s)
    (htotal : ∀ x input, ∑ s, evaluation x input s = 1)
    (hlocal : ∀ x (first second : V → X), (∀ slot, ∀ v ∈ x.1 slot, first v = second v) →
      evaluation x first = evaluation x second)
    (p q : V → X) (hball : ∀ v ∈ lightBall r A (ℓ - 1), p v = q v) :
    totalVariation (mixtureLaw (supportChainLaw r c A n M T) fun x ↦ evaluation x p)
        (mixtureLaw (supportChainLaw r c A n M T) fun x ↦ evaluation x q) ≤
      min 1 (n * A.card * Real.exp (D * (1 + 2 * a) * T) / a ^ ℓ) := by
  refine (totalVariation_mixtureLaw_le (supportChainLaw r c A n M T)
    (supportChainLaw_nonneg hr hc A n M hT) _ _ (fun x ↦ hnonneg x p) (fun x ↦ hnonneg x q)
    (fun x ↦ htotal x p) (fun x ↦ htotal x q) (fun x ↦ univ.val.map x.1 ∈ escapeSet r A ℓ)
    fun x hx ↦ hlocal x p q fun slot v hv ↦ hball v (mem_lightBall_of_not_escaped hx hv)).trans ?_
  rw [Finset.sum_filter]
  exact sum_supportChainLaw_escape_le hr hD hc ha A n M ℓ hT

open scoped Classical in
/-- Spec (9.3) at the radius of (9.2). Assumes: the hypotheses of
`totalVariation_supportChainLaw_inputs_le` without the base, `D T ≠ 0`, and `ℓ ≥ 2DT`. The sample
laws on the two inputs are within total variation `min {1, n|A| e^{DT} (2eDT/ℓ)^ℓ}`. -/
theorem totalVariation_supportChainLaw_inputs_le_radius {S X : Type*} [Fintype S]
    {r : V → V → ℝ} {c D T : ℝ} (hr : ∀ i j, 0 ≤ r i j) (hD : ∀ i, ∑ j, r i j ≤ D) (hc : 0 ≤ c)
    (hT : 0 ≤ T) (hDT : D * T ≠ 0) (A : Finset V) (n M ℓ : ℕ)
    (hradius : 1 ≤ (ℓ : ℝ) / (2 * D * T))
    (evaluation : SupportChainState V n M → (V → X) → S → ℝ)
    (hnonneg : ∀ x input s, 0 ≤ evaluation x input s)
    (htotal : ∀ x input, ∑ s, evaluation x input s = 1)
    (hlocal : ∀ x (first second : V → X), (∀ slot, ∀ v ∈ x.1 slot, first v = second v) →
      evaluation x first = evaluation x second)
    (p q : V → X) (hball : ∀ v ∈ lightBall r A (ℓ - 1), p v = q v) :
    totalVariation (mixtureLaw (supportChainLaw r c A n M T) fun x ↦ evaluation x p)
        (mixtureLaw (supportChainLaw r c A n M T) fun x ↦ evaluation x q) ≤
      min 1 (n * A.card * Real.exp (D * T) * (2 * Real.exp 1 * D * T / ℓ) ^ ℓ) := by
  refine (totalVariation_mixtureLaw_le (supportChainLaw r c A n M T)
    (supportChainLaw_nonneg hr hc A n M hT) _ _ (fun x ↦ hnonneg x p) (fun x ↦ hnonneg x q)
    (fun x ↦ htotal x p) (fun x ↦ htotal x q) (fun x ↦ univ.val.map x.1 ∈ escapeSet r A ℓ)
    fun x hx ↦ hlocal x p q fun slot v hv ↦ hball v (mem_lightBall_of_not_escaped hx hv)).trans ?_
  rw [Finset.sum_filter]
  exact sum_supportChainLaw_escape_le_radius hr hD hc A n M ℓ hT hDT hradius

open scoped Classical in
/-- Spec Corollary 8.1 for the truncated checking graph, driven by one family of events. Assumes: a
finite space of driving events with nonnegative weights, and an evaluation of the final circuit
state as a finite law on samples. The sample laws of the full circuit and of the circuit on the
induced checking graph of `B_{ℓ-1}(A)`, both started from `n` arguments carrying `A` and driven by
the same events, are within total variation the weight of the events along which the full circuit
ends escaped. -/
theorem totalVariation_truncatedSupportChain_le {Ω S : Type*} [Fintype Ω] [Fintype S]
    (r : V → V → ℝ) (A : Finset V) (n M ℓ : ℕ) (weight : Ω → ℝ) (hweight : ∀ ω, 0 ≤ weight ω)
    (events : Ω → List (SupportChainEvent n M V))
    (evaluation : SupportChainState V n M → S → ℝ) (hnonneg : ∀ x s, 0 ≤ evaluation x s)
    (htotal : ∀ x, ∑ s, evaluation x s = 1) :
    totalVariation
        (mixtureLaw weight fun ω ↦
          evaluation ((events ω).foldl supportChainStep (supportChainStart A n M)))
        (mixtureLaw weight fun ω ↦ evaluation ((events ω).foldl
          (truncatedSupportChainStep (lightBall r A (ℓ - 1))) (supportChainStart A n M))) ≤
      ∑ ω ∈ univ.filter (fun ω ↦
        univ.val.map ((events ω).foldl supportChainStep (supportChainStart A n M)).1 ∈
          escapeSet r A ℓ), weight ω :=
  totalVariation_mixtureLaw_le weight hweight _ _ (fun _ ↦ hnonneg _) (fun _ ↦ hnonneg _)
    (fun _ ↦ htotal _) (fun _ ↦ htotal _) _ fun ω hω ↦ by
      simp only [foldl_truncatedSupportChainStep_eq r A ℓ (events ω) _
        (unfilledSlotsEmpty_supportChainStart A n M) hω]

open scoped Classical in
/-- Spec Corollary 8.1 for the truncated checking graph with explicit numbers. Assumes: the
hypotheses of `totalVariation_truncatedSupportChain_le` and of `sum_supportChainLaw_escape_le`, and
driving events that give the full circuit the law `supportChainLaw r c A n M T`: averaging any
function of its final state over the events is averaging it against that law. The two sample laws
are within total variation `min {1, n|A| e^{D(1+2a)T} / a^ℓ}`. -/
theorem totalVariation_truncatedSupportChain_le_exp {Ω S : Type*} [Fintype Ω] [Fintype S]
    {r : V → V → ℝ} {c D T a : ℝ} (hr : ∀ i j, 0 ≤ r i j) (hD : ∀ i, ∑ j, r i j ≤ D)
    (hc : 0 ≤ c) (ha : 1 ≤ a) (hT : 0 ≤ T) (A : Finset V) (n M ℓ : ℕ) (weight : Ω → ℝ)
    (hweight : ∀ ω, 0 ≤ weight ω) (events : Ω → List (SupportChainEvent n M V))
    (hlaw : ∀ F : SupportChainState V n M → ℝ,
      ∑ ω, weight ω * F ((events ω).foldl supportChainStep (supportChainStart A n M)) =
        ∑ y, supportChainLaw r c A n M T y * F y)
    (evaluation : SupportChainState V n M → S → ℝ) (hnonneg : ∀ x s, 0 ≤ evaluation x s)
    (htotal : ∀ x, ∑ s, evaluation x s = 1) :
    totalVariation
        (mixtureLaw weight fun ω ↦
          evaluation ((events ω).foldl supportChainStep (supportChainStart A n M)))
        (mixtureLaw weight fun ω ↦ evaluation ((events ω).foldl
          (truncatedSupportChainStep (lightBall r A (ℓ - 1))) (supportChainStart A n M))) ≤
      min 1 (n * A.card * Real.exp (D * (1 + 2 * a) * T) / a ^ ℓ) := by
  refine (totalVariation_truncatedSupportChain_le r A n M ℓ weight hweight events evaluation
    hnonneg htotal).trans ?_
  have hescape := hlaw fun y ↦ if univ.val.map y.1 ∈ escapeSet r A ℓ then 1 else 0
  simp only [mul_ite, mul_one, mul_zero] at hescape
  rw [Finset.sum_filter, hescape]
  exact sum_supportChainLaw_escape_le hr hD hc ha A n M ℓ hT

end Laws

end

end Descent.Pangenome.AncestralLocality
