/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.Linkage.Chain

assert_below Descent.PopGen Descent.Spectral Descent.Blindness Descent.Conditionals Descent.Portability Descent.Decision Descent.Program

/-!
# The linkage–entropy barrier

Forgotten thread identity at each separator becomes additive entropy, and additive entropy
becomes multiplicative mosaic capacity.  This file proves that sentence.

## The argument

The potential carried along the chain is the mean logarithm of the dynamic program's vector,
`meanLog`.  Two facts about it suffice:

* `meanLog_step` — crossing one interface raises the potential by at least that interface's
  `identityLoss`.  Inside a fiber this is the arithmetic–geometric mean inequality; the
  bookkeeping that turns per-thread fiber means into a per-panel statement is
  `sum_inv_fiberCard_mul_sum_fiber`, the same fiberwise regrouping the width identity uses.
* `meanLog_le_log_sum` — the potential is at most the logarithm of the total, again by
  arithmetic–geometric mean.

Chaining the first and then applying the second gives
`log m + ∑ H(J ∣ S_j) ≤ log |Ω|`.  No entropy machinery is developed to state it: the
conditional entropies are `identityLoss`, which is a mean of logarithms, and the whole
argument is `sum_mul_log_le_log_sum` applied first inside fibers and then across the panel.

## The results

* `log_card_add_linkagePressure_le` — the barrier in logarithmic form.
* `pow_card_le_prod_width_mul_card_mosaics` — the same statement as an inequality between
  natural numbers, `m ^ (r+1) ≤ (∏ w_j) · |Ω|`, with no logarithms left in it.
* `prod_width_mul_card_mosaics_of_balanced` — the same statement as an EQUALITY for a
  balanced chain, so the bound is exact and not merely true.
* `width_eq_card_of_card_mosaics_eq` — the topology-only exactness barrier: a chain whose
  compatible language is exactly the panel has `w_j = m` at every interface.  Identity can
  leave the topology only by being carried somewhere else.
* `card_phantoms`, `pow_card_le_prod_width_mul_phantoms_add` — the panel-phantom count that
  the width budget forces to exist.

## What is not claimed

A panel-phantom derivation is one the panel does not contain.  Nothing here says it is
biologically impossible; an unsampled recombinant is a phantom by this definition.  The
statement is about what a topology can represent, measured against a finite panel.

## Empirical status

None.  Every result is an inequality between counts and logarithms of counts, and its
hypotheses are properties of a finite partition.  The empirical question these results
sharpen — how much identity real graph builders discard at real separators — is a
measurement of `identityLoss` on a graph, not of any statement proved here.
-/

namespace Descent.Pangenome.Linkage

open Finset

universe u

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

/-! ### The potential -/

/-- The mean logarithm of a positive vector on the panel: the logarithm of its geometric
mean.  This is the quantity the chain carries. -/
noncomputable def meanLog (v : ι → ℝ) : ℝ :=
  (Fintype.card ι : ℝ)⁻¹ * ∑ h : ι, Real.log (v h)

/-- **Fiber means, counted per thread, are panel sums.**  Weighting each thread's fiber sum
by the reciprocal fiber size counts every thread exactly once. -/
theorem sum_inv_fiberCard_mul_sum_fiber (s : ι → ι) (f : ι → ℝ) :
    ∑ h : ι, ((fiberCard s h : ℝ))⁻¹ * ∑ g ∈ fiber s h, f g = ∑ g : ι, f g := by
  rw [← sum_fiberwise s fun h ↦ ((fiberCard s h : ℝ))⁻¹ * ∑ g ∈ fiber s h, f g,
    ← sum_fiberwise s f]
  refine Finset.sum_congr rfl fun a ha ↦ ?_
  have hne : ((stateFiber s a).card : ℝ) ≠ 0 := by
    exact_mod_cast Nat.pos_iff_ne_zero.mp (card_stateFiber_pos ha)
  have hconst : ∀ h ∈ stateFiber s a,
      ((fiberCard s h : ℝ))⁻¹ * ∑ g ∈ fiber s h, f g
        = (((stateFiber s a).card : ℝ))⁻¹ * ∑ g ∈ stateFiber s a, f g := by
    intro h hh
    simp only [mem_stateFiber] at hh
    simp [fiberCard, fiber, hh]
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul, ← mul_assoc,
    mul_inv_cancel₀ hne, one_mul]

/-- **Crossing an interface pays its identity loss into the potential.** -/
theorem meanLog_step [Nonempty ι] (s : ι → ι) (v : ι → ℝ) (hv : ∀ h, 0 < v h) :
    meanLog v + identityLoss s ≤ meanLog fun h ↦ ∑ g ∈ fiber s h, v g := by
  have hlocal : ∀ h : ι,
      ((fiberCard s h : ℝ))⁻¹ * ∑ g ∈ fiber s h, Real.log (v g)
          + Real.log (fiberCard s h : ℝ)
        ≤ Real.log (∑ g ∈ fiber s h, v g) := by
    intro h
    have hn : (0 : ℝ) < (fiberCard s h : ℝ) := by exact_mod_cast fiberCard_pos s h
    have hsumpos : 0 < ∑ g ∈ fiber s h, v g :=
      Finset.sum_pos (fun g _ ↦ hv g) ⟨h, self_mem_fiber s h⟩
    have hw1 : ∑ _g ∈ fiber s h, ((fiberCard s h : ℝ))⁻¹ = 1 := by
      rw [Finset.sum_const, nsmul_eq_mul]
      show ((fiberCard s h : ℝ)) * ((fiberCard s h : ℝ))⁻¹ = 1
      exact mul_inv_cancel₀ (ne_of_gt hn)
    have hJ := sum_mul_log_le_log_sum (fiber s h) (fun _ ↦ ((fiberCard s h : ℝ))⁻¹) v
      (fun _ _ ↦ by positivity) hw1 (fun g _ ↦ hv g)
    rw [← Finset.mul_sum, ← Finset.mul_sum,
      Real.log_mul (by positivity) (ne_of_gt hsumpos), Real.log_inv] at hJ
    linarith
  have hLHS : ∑ h : ι, (((fiberCard s h : ℝ))⁻¹ * ∑ g ∈ fiber s h, Real.log (v g)
      + Real.log (fiberCard s h : ℝ))
      = (∑ g : ι, Real.log (v g)) + ∑ h : ι, Real.log (fiberCard s h : ℝ) := by
    rw [Finset.sum_add_distrib, sum_inv_fiberCard_mul_sum_fiber]
  have hmono : (Fintype.card ι : ℝ)⁻¹ * ((∑ g : ι, Real.log (v g))
      + ∑ h : ι, Real.log (fiberCard s h : ℝ))
      ≤ (Fintype.card ι : ℝ)⁻¹ * ∑ h : ι, Real.log (∑ g ∈ fiber s h, v g) := by
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rw [← hLHS]
    exact Finset.sum_le_sum fun h _ ↦ hlocal h
  simpa [meanLog, identityLoss, mul_add] using hmono

omit [DecidableEq ι] in
/-- **The potential is at most the logarithm of the total.** -/
theorem meanLog_le_log_sum [Nonempty ι] (v : ι → ℝ) (hv : ∀ h, 0 < v h) :
    meanLog v + Real.log (Fintype.card ι : ℝ) ≤ Real.log (∑ h : ι, v h) := by
  have htot : (0 : ℝ) < ∑ h : ι, v h := Finset.sum_pos (fun h _ ↦ hv h) Finset.univ_nonempty
  have hAM := mean_log_le_log_mean v hv
  rw [Real.log_mul (by positivity) (ne_of_gt htot), Real.log_inv] at hAM
  rw [meanLog]
  linarith

/-! ### The barrier -/

/-- **Linkage-entropy pressure**: the identity a chain of separators forgets, summed. -/
noncomputable def linkagePressure (c : Chain ι) : ℝ := (c.map identityLoss).sum

theorem linkagePressure_nil : linkagePressure ([] : Chain ι) = 0 := by simp [linkagePressure]

theorem linkagePressure_cons (s : ι → ι) (c : Chain ι) :
    linkagePressure (s :: c) = identityLoss s + linkagePressure c := by
  simp [linkagePressure]

theorem linkagePressure_le_meanLog [Nonempty ι] (c : Chain ι) :
    linkagePressure c ≤ meanLog fun h ↦ (derivationCount c h : ℝ) := by
  induction c with
  | nil => simp [linkagePressure, meanLog, derivationCount]
  | cons s c ih =>
    have hpos : ∀ h : ι, (0 : ℝ) < (derivationCount c h : ℝ) := fun h ↦ by
      exact_mod_cast derivationCount_pos c h
    have hstep := meanLog_step s (fun h ↦ (derivationCount c h : ℝ)) hpos
    have heq : (fun h ↦ ∑ g ∈ fiber s h, (derivationCount c g : ℝ))
        = fun h ↦ (derivationCount (s :: c) h : ℝ) := by
      funext h
      rw [derivationCount, Nat.cast_sum]
    rw [heq] at hstep
    rw [linkagePressure_cons]
    linarith

/-- **The linkage–entropy barrier.**  Every bit of thread identity forgotten at every
interface reappears additively as logarithmic mosaic capacity. -/
theorem log_card_add_linkagePressure_le [Nonempty ι] (c : Chain ι) :
    Real.log (Fintype.card ι : ℝ) + linkagePressure c
      ≤ Real.log ((mosaics c).card : ℝ) := by
  have hpos : ∀ h : ι, (0 : ℝ) < (derivationCount c h : ℝ) := fun h ↦ by
    exact_mod_cast derivationCount_pos c h
  have hsum : ((mosaics c).card : ℝ) = ∑ h : ι, (derivationCount c h : ℝ) := by
    rw [card_mosaics, Nat.cast_sum]
  have hAM := meanLog_le_log_sum (fun h ↦ (derivationCount c h : ℝ)) hpos
  have hchain := linkagePressure_le_meanLog c
  rw [hsum]
  linarith

/-! ### The width law, with the logarithms removed

The logarithmic barrier is sharpest, but the statement a graph builder can check is an
inequality between natural numbers.  Getting there needs only that `log` is monotone. -/

omit [Fintype ι] [DecidableEq ι] in
theorem prod_map_pos (f : (ι → ι) → ℕ) (hf : ∀ s, 0 < f s) (c : Chain ι) :
    0 < (c.map f).prod := by
  induction c with
  | nil => exact Nat.one_pos
  | cons s c ih =>
    rw [List.map_cons, List.prod_cons]
    exact Nat.mul_pos (hf s) ih

omit [Fintype ι] [DecidableEq ι] in
theorem log_prod_map (f : (ι → ι) → ℕ) (hf : ∀ s, 0 < f s) (c : Chain ι) :
    Real.log (((c.map f).prod : ℕ) : ℝ) = (c.map fun s ↦ Real.log (f s : ℝ)).sum := by
  induction c with
  | nil => simp
  | cons s c ih =>
    have h1 : ((f s : ℕ) : ℝ) ≠ 0 := by
      exact_mod_cast Nat.pos_iff_ne_zero.mp (hf s)
    have h2 : (((c.map f).prod : ℕ) : ℝ) ≠ 0 := by
      exact_mod_cast Nat.pos_iff_ne_zero.mp (prod_map_pos f hf c)
    rw [List.map_cons, List.prod_cons, Nat.cast_mul, Real.log_mul h1 h2, ih, List.map_cons,
      List.sum_cons]

omit [Fintype ι] [DecidableEq ι] in
theorem sum_map_sub (c : Chain ι) (a : ℝ) (g : (ι → ι) → ℝ) :
    (c.map fun s ↦ a - g s).sum = c.length * a - (c.map g).sum := by
  induction c with
  | nil => simp
  | cons s c ih =>
    rw [List.map_cons, List.sum_cons, ih, List.map_cons, List.sum_cons, List.length_cons]
    push_cast
    ring

theorem sum_log_width_le_linkagePressure [Nonempty ι] (c : Chain ι) :
    (c.map fun s ↦ Real.log (Fintype.card ι : ℝ) - Real.log (width s : ℝ)).sum
      ≤ linkagePressure c := by
  induction c with
  | nil => simp [linkagePressure]
  | cons s c ih =>
    rw [List.map_cons, List.sum_cons, linkagePressure_cons]
    have := log_card_sub_log_width_le_identityLoss s
    linarith

theorem card_mosaics_pos [Nonempty ι] (c : Chain ι) : 0 < (mosaics c).card := by
  rw [card_mosaics]
  exact Finset.sum_pos (fun h _ ↦ derivationCount_pos c h) Finset.univ_nonempty

/-- **The width law.**  A chain of `r` separators of occupied widths `w_1, …, w_r` over a
panel of `m` threads admits at least `m ^ (r+1) / ∏ w_j` ancestry-resolved derivations,
stated without division.

`Descent.Pangenome.Linkage.Chain.card_mosaics_of_balanced` attains this with equality, so the
inequality cannot be improved. -/
theorem pow_card_le_prod_width_mul_card_mosaics [Nonempty ι] (c : Chain ι) :
    Fintype.card ι ^ (c.length + 1) ≤ (c.map width).prod * (mosaics c).card := by
  have hmpos : (0 : ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  have hwpos : 0 < (c.map width).prod := prod_map_pos width (fun s ↦ width_pos s) c
  have hOpos : 0 < (mosaics c).card := card_mosaics_pos c
  have hwR : (0 : ℝ) < (((c.map width).prod : ℕ) : ℝ) := by exact_mod_cast hwpos
  have hOR : (0 : ℝ) < (((mosaics c).card : ℕ) : ℝ) := by exact_mod_cast hOpos
  have hbar := log_card_add_linkagePressure_le c
  have hpress := sum_log_width_le_linkagePressure c
  have hsplit := sum_map_sub c (Real.log (Fintype.card ι : ℝ))
    (fun s ↦ Real.log (width s : ℝ))
  have hlog : Real.log (((Fintype.card ι ^ (c.length + 1) : ℕ) : ℝ))
      ≤ Real.log ((((c.map width).prod * (mosaics c).card : ℕ) : ℝ)) := by
    rw [Nat.cast_pow, Real.log_pow, Nat.cast_mul,
      Real.log_mul (ne_of_gt hwR) (ne_of_gt hOR),
      log_prod_map width (fun s ↦ width_pos s) c]
    push_cast
    linarith
  exact_mod_cast (Real.log_le_log_iff (by positivity) (by positivity)).mp hlog

/-- **The width law is exact.**  A balanced chain turns the previous inequality into an
equality, so no sharper bound holds — and it does so whatever the partitions at different
interfaces are, since balance at each interface is the only hypothesis. -/
theorem prod_width_mul_card_mosaics_of_balanced {c : Chain ι} {bs : List ℕ}
    (hb : Balanced c bs) :
    (c.map width).prod * (mosaics c).card = Fintype.card ι ^ (c.length + 1) := by
  rw [card_mosaics_of_balanced hb]
  induction hb with
  | nil => simp
  | @cons s c b bs hfib _ ih =>
    have hw := width_mul_of_balanced hfib
    rw [List.map_cons, List.prod_cons, List.prod_cons, List.length_cons]
    calc width s * (c.map width).prod * (Fintype.card ι * (b * bs.prod))
        = width s * b * ((c.map width).prod * (Fintype.card ι * bs.prod)) := by ring
      _ = Fintype.card ι * Fintype.card ι ^ (c.length + 1) := by rw [hw, ih]
      _ = Fintype.card ι ^ (c.length + 1 + 1) := by rw [pow_succ]; ring

/-- **The width a path-language cap demands.**  A chain required to admit at most `F`
derivations must satisfy `m ^ (r+1) ≤ (∏ w_j) · F`.  With `F` close to `m`, the geometric
mean of the widths is forced close to `m`: near-exactness across many linkage-bearing
separators permits almost no average merging. -/
theorem pow_card_le_prod_width_mul_of_card_le [Nonempty ι] (c : Chain ι) (F : ℕ)
    (hF : (mosaics c).card ≤ F) :
    Fintype.card ι ^ (c.length + 1) ≤ (c.map width).prod * F :=
  le_trans (pow_card_le_prod_width_mul_card_mosaics c) (Nat.mul_le_mul_left _ hF)

/-! ### The exactness barrier -/

theorem prod_le_pow_of_le {w : ℕ} (c : Chain ι) (hw : ∀ s ∈ c, width s ≤ w) :
    (c.map width).prod ≤ w ^ c.length := by
  induction c with
  | nil => simp
  | cons s c ih =>
    rw [List.map_cons, List.prod_cons, List.length_cons, pow_succ, mul_comm (w ^ c.length) w]
    exact Nat.mul_le_mul (hw s (List.mem_cons_self ..))
      (ih fun t ht ↦ hw t (List.mem_cons_of_mem s ht))

/-- **The width budget.**  A bound on every occupied width bounds the whole product, so a
constant compression repeated over `r` separators forces a language exponential in `r`:
`m · (m/w) ^ r` derivations, stated without division. -/
theorem pow_card_le_pow_width_mul_card_mosaics [Nonempty ι] (c : Chain ι) (w : ℕ)
    (hw : ∀ s ∈ c, width s ≤ w) :
    Fintype.card ι ^ (c.length + 1) ≤ w ^ c.length * (mosaics c).card :=
  le_trans (pow_card_le_prod_width_mul_card_mosaics c)
    (Nat.mul_le_mul_right _ (prod_le_pow_of_le c hw))

theorem prod_le_pow {m : ℕ} : ∀ (l : List ℕ), (∀ x ∈ l, x ≤ m) → l.prod ≤ m ^ l.length := by
  intro l
  induction l with
  | nil => intro _; simp
  | cons a t ih =>
    intro hle
    rw [List.prod_cons, List.length_cons, pow_succ, mul_comm (m ^ t.length) m]
    exact Nat.mul_le_mul (hle a (List.mem_cons_self ..))
      (ih fun x hx ↦ hle x (List.mem_cons_of_mem a hx))

/-- A list of naturals, each at most `m`, whose product is at least `m ^ length`, has every
entry equal to `m`. -/
theorem eq_of_pow_le_prod {m : ℕ} (hm : 0 < m) :
    ∀ (l : List ℕ), (∀ x ∈ l, x ≤ m) → m ^ l.length ≤ l.prod → ∀ x ∈ l, x = m := by
  intro l
  induction l with
  | nil => intro _ _ x hx; cases hx
  | cons a t ih =>
    intro hle hpow
    rw [List.length_cons, pow_succ, mul_comm (m ^ t.length) m, List.prod_cons] at hpow
    have hta : ∀ x ∈ t, x ≤ m := fun x hx ↦ hle x (List.mem_cons_of_mem a hx)
    have htp : t.prod ≤ m ^ t.length := prod_le_pow t hta
    have ham : a ≤ m := hle a (List.mem_cons_self ..)
    have h1 : m * t.prod ≤ m * m ^ t.length := Nat.mul_le_mul_left m htp
    have h2 : a * t.prod ≤ m * t.prod := Nat.mul_le_mul_right t.prod ham
    have htpos : 0 < t.prod := by
      rcases Nat.eq_zero_or_pos t.prod with h | h
      · rw [h, mul_zero] at hpow
        have hpos : 0 < m * m ^ t.length := Nat.mul_pos hm (pow_pos hm t.length)
        omega
      · exact h
    have haeq : a = m := by
      have : a * t.prod = m * t.prod := le_antisymm h2 (by omega)
      exact Nat.eq_of_mul_eq_mul_right htpos this
    have hteq : m ^ t.length ≤ t.prod := by
      have : m * m ^ t.length ≤ m * t.prod := by
        rw [haeq] at hpow
        omega
      exact Nat.le_of_mul_le_mul_left this hm
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hxt
    · exact haeq
    · exact ih hta hteq x hxt

/-- **The topology-only exactness barrier.**  If a chain's compatible language is exactly the
panel — no phantom derivation at all — then every interface leaves all `m` thread identities
in distinct graph states.  A topology that merges identity at a linkage-bearing separator has
only two options left: admit the phantoms, or carry the missing identity outside the
topology. -/
theorem width_eq_card_of_card_mosaics_eq [Nonempty ι] {c : Chain ι}
    (hex : (mosaics c).card = Fintype.card ι) : ∀ s ∈ c, width s = Fintype.card ι := by
  have hm : 0 < Fintype.card ι := Fintype.card_pos
  have hb := pow_card_le_prod_width_mul_card_mosaics c
  rw [hex, pow_succ] at hb
  have hstep : Fintype.card ι ^ c.length ≤ (c.map width).prod :=
    Nat.le_of_mul_le_mul_right hb hm
  have hle : ∀ x ∈ c.map width, x ≤ Fintype.card ι := by
    intro x hx
    obtain ⟨s, -, rfl⟩ := List.mem_map.mp hx
    exact width_le_card s
  have hlen : (c.map width).length = c.length := by simp
  intro s hs
  exact eq_of_pow_le_prod hm (c.map width) hle (by rw [hlen]; exact hstep) (width s)
    (List.mem_map.mpr ⟨s, hs, rfl⟩)

/-! ### Why the law is Shannon, and not one exact factor per interface

`Descent.Pangenome.Linkage.Chain.card_mosaics_singleton` gives ONE interface's count exactly:
`∑ n_a²`, which is `m²/w` inflated by the fibers' imbalance and is strictly better than the
width bound.  It is tempting to divide that by `m` and multiply the resulting factor over the
interfaces of a chain.

That is false, and the two interfaces below show it.  Over three threads, `{0,1} | {2}` and
`{0,2} | {1}` each admit `5` derivations on their own, so the per-interface factor is `5/3`
and the product would predict `3 · (5/3)² = 25/3 > 8`.  The true count is `8`.

The Shannon construction survives precisely because conditional entropy obeys a chain rule
and the couplings glue along a tree, which is why the multi-interface term in
`Descent.Pangenome.Linkage.Interface.identityLoss_eq_width_add_imbalance` is a
Kullback–Leibler divergence and not an order-2 Rényi one. -/

/-- The interface separating `{0,1}` from `{2}`. -/
def witnessLeft : Fin 3 → Fin 3 := ![0, 0, 2]

/-- The interface separating `{0,2}` from `{1}`, which cuts the panel the other way. -/
def witnessRight : Fin 3 → Fin 3 := ![0, 1, 0]

theorem card_mosaics_witnessLeft : (mosaics [witnessLeft]).card = 5 := by
  rw [card_mosaics]; decide

theorem card_mosaics_witnessRight : (mosaics [witnessRight]).card = 5 := by
  rw [card_mosaics]; decide

theorem card_mosaics_witness : (mosaics [witnessLeft, witnessRight]).card = 8 := by
  rw [card_mosaics]; decide

theorem width_witnessLeft : width witnessLeft = 2 := by decide

theorem width_witnessRight : width witnessRight = 2 := by decide

/-- **The exact per-interface factors do not multiply.**  Their product, cleared of
denominators, strictly exceeds the true count, so it is not a lower bound on anything. -/
theorem card_mosaics_witness_lt_renyi_product :
    (mosaics [witnessLeft, witnessRight]).card * Fintype.card (Fin 3) ^ 2
      < (mosaics [witnessLeft]).card * (mosaics [witnessRight]).card
        * Fintype.card (Fin 3) := by
  rw [card_mosaics_witness, card_mosaics_witnessLeft, card_mosaics_witnessRight]
  decide

/-- The width law, by contrast, holds on the same witness: `3³ ≤ (2·2)·8`. -/
theorem width_law_holds_on_witness :
    Fintype.card (Fin 3) ^ (([witnessLeft, witnessRight] : Chain (Fin 3)).length + 1)
      ≤ (([witnessLeft, witnessRight] : Chain (Fin 3)).map width).prod
        * (mosaics [witnessLeft, witnessRight]).card :=
  pow_card_le_prod_width_mul_card_mosaics _

/-! ### The phantoms the width budget forces -/

/-- The `m` panel threads, as the derivations that never switch donor. -/
def diagonals (c : Chain ι) : Finset (List ι) :=
  Finset.univ.image fun h ↦ List.replicate (c.length + 1) h

theorem replicate_mem_mosaicsFrom (c : Chain ι) (h : ι) :
    List.replicate (c.length + 1) h ∈ mosaicsFrom c h := by
  induction c generalizing h with
  | nil => simp [mosaicsFrom]
  | cons s c ih =>
    simp only [mosaicsFrom, Finset.mem_biUnion, Finset.mem_image]
    exact ⟨h, self_mem_fiber s h, List.replicate (c.length + 1) h, ih h, by
      simp [List.replicate_succ]⟩

theorem diagonals_subset (c : Chain ι) : diagonals c ⊆ mosaics c := by
  intro x hx
  obtain ⟨h, -, rfl⟩ := Finset.mem_image.mp hx
  exact Finset.mem_biUnion.mpr ⟨h, Finset.mem_univ h, replicate_mem_mosaicsFrom c h⟩

theorem card_diagonals (c : Chain ι) : (diagonals c).card = Fintype.card ι := by
  have hinj : Function.Injective fun h : ι ↦ List.replicate (c.length + 1) h := by
    intro h₁ h₂ hEq
    simp only [List.replicate_succ] at hEq
    injection hEq with hh _
  rw [diagonals, Finset.card_image_of_injective _ hinj, Finset.card_univ]

/-- **The panel-phantom derivations**: compatible mosaics the panel does not contain. -/
def phantoms (c : Chain ι) : Finset (List ι) := mosaics c \ diagonals c

/-- **A derivation is a panel thread exactly when it never switches donor.**  The switch
grading of `Descent.Pangenome.Linkage.Chain` and the phantom count here are two readings of
one partition of the compatible language. -/
theorem mem_diagonals_iff_switches_eq_zero {c : Chain ι} {x : List ι} (hx : x ∈ mosaics c) :
    x ∈ diagonals c ↔ switches x = 0 := by
  obtain ⟨h, -, hmem⟩ := Finset.mem_biUnion.mp hx
  obtain ⟨t, rfl⟩ := mem_mosaicsFrom_head hmem
  have hlen : (h :: t).length = c.length + 1 := length_of_mem_mosaics hx
  constructor
  · intro hd
    obtain ⟨g, -, hg⟩ := Finset.mem_image.mp hd
    rw [← hg]
    exact switches_replicate g c.length
  · intro hs
    refine Finset.mem_image.mpr ⟨h, Finset.mem_univ h, ?_⟩
    have hrep := eq_replicate_of_switches_eq_zero t hs
    have : t.length + 1 = c.length + 1 := by simpa using hlen
    rw [← this, ← hrep]

/-- **The phantoms are exactly the recombinant derivations.** -/
theorem phantoms_eq_filter (c : Chain ι) :
    phantoms c = (mosaics c).filter fun x ↦ switches x ≠ 0 := by
  ext x
  rw [phantoms, Finset.mem_sdiff, Finset.mem_filter]
  constructor
  · rintro ⟨hx, hnd⟩
    exact ⟨hx, fun hz ↦ hnd ((mem_diagonals_iff_switches_eq_zero hx).mpr hz)⟩
  · rintro ⟨hx, hne⟩
    exact ⟨hx, fun hd ↦ hne ((mem_diagonals_iff_switches_eq_zero hx).mp hd)⟩

theorem card_phantoms (c : Chain ι) :
    (phantoms c).card = (mosaics c).card - Fintype.card ι := by
  have hin : diagonals c ∩ mosaics c = diagonals c :=
    Finset.inter_eq_left.mpr (diagonals_subset c)
  rw [phantoms, Finset.card_sdiff, hin, card_diagonals]

/-- **The width budget forces phantoms.**  Whatever the interface partitions are, the panel
plus the phantoms it generates must fill the width bound — so a chain whose widths leave
`m ^ (r+1) / ∏ w_j` above `m` cannot avoid admitting derivations the panel never contained. -/
theorem pow_card_le_prod_width_mul_phantoms_add [Nonempty ι] (c : Chain ι) :
    Fintype.card ι ^ (c.length + 1)
      ≤ (c.map width).prod * ((phantoms c).card + Fintype.card ι) := by
  have hsub : Fintype.card ι ≤ (mosaics c).card := by
    rw [← card_diagonals c]
    exact Finset.card_le_card (diagonals_subset c)
  rw [card_phantoms, Nat.sub_add_cancel hsub]
  exact pow_card_le_prod_width_mul_card_mosaics c

end Descent.Pangenome.Linkage
