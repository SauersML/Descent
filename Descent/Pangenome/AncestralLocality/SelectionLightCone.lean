/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.AncestralLocality.SelectionDecisions
import Descent.Pangenome.AncestralLocality.SupportChainDynkin

assert_below Descent.PopGen Descent.Spectral Descent.Blindness Descent.Conditionals
assert_below Descent.Portability Descent.Decision Descent.Program

/-!
# The genomic light cone under selection

`Descent.Pangenome.AncestralLocality.SupportChainDynkin` proves the expectation bounds (8.2),
(8.3), (9.1) and (9.2) of the research note "Ancestral locality" for the support circuit of neutral
decisions, truncated after `M` decisions, with constants that do not depend on `M`. Selection adds a
second kind of branching (`Descent.Pangenome.AncestralLocality.SelectionDecisions`): at rate `σ` an
argument with a nonempty tag `A_a` meets a selective event, and the new parent reads `A_a ∪ S`,
where `S` is the set of coordinates the fitness reads (`tagDetermined_selectionBranch`). This file
adds that event to the truncated chain and proves the four bounds under decisions and selection
together.

**The chain.** The state space is `SupportChainState V n M`, and decisions and selections share
the budget of `M` new slots. `selectionChainBranch S x a` fills the next slot with `x.1 a ∪ S`,
while fewer than `M` branchings have been taken. `selectionChainRate r c σ S` adds rate `σ` per
nonempty argument to `supportChainRate r c`, and `selectionChainGenerator` and `selectionChainLaw`
are the generator and the law `δ_{x₀} e^{tQ}`. Without selection the chain is the neutral one
(`selectionChainLaw_zero`).

**The drift.** A selective branching raises a nonnegative tag weight by at most `w(A_a) + w(S)`
(`tagWeight_selectionChainBranch_le`). For weights at least one on every coordinate, the generator
obeys `Q Z^{(w)} ≤ (D (1 + 2κ) + σ (1 + w(S))) Z^{(w)}` (`selectionChainGenerator_tagWeight_le`),
and the branching count has drift at most `decisionRate + σ Z` (`selectionChainGenerator_count_le`).

**The bounds.** For every truncation `M`, with `K = 3D + σ (1 + |S|)`:

* (8.2): `E Z_T ≤ n |A| e^{K T}` (`sum_selectionChainLaw_mul_tagCount_le`);
* (8.3): the expected number of branchings by time `T` is at most
  `n |A| (D + σ) (e^{K T} - 1) / K` (`sum_selectionChainLaw_mul_count_le`, through the general
  integrated bound `le_mul_div_mul_exp_sub_one`);
* the light-cone count relative to the query together with the fitness support,
  `E Z^{(a)}_T ≤ n |A| e^{(D (1 + 2a) + σ (1 + |S|)) T}`
  (`sum_selectionChainLaw_mul_lightWeight_le`);
* (9.1): the probability of holding a coordinate at distance at least `ℓ` from `A ∪ S` is at most
  `min {1, n |A| e^{(D (1 + 2a) + σ (1 + |S|)) T} / a^ℓ}` (`sum_selectionChainLaw_escape_le`), hence
  at most the neutral bound with `D` replaced by `D' = D + σ (1 + |S|) / 3`
  (`sum_selectionChainLaw_escape_le_shift`);
* (9.2): at the radius `a = ℓ / (2 D' T)` the escape bound is
  `min {1, n |A| e^{D' T} (2 e D' T / ℓ)^ℓ}` (`sum_selectionChainLaw_escape_le_radius`), and
  there is no escape when `D' T = 0` (`sum_selectionChainLaw_escape_eq_zero`).

So selection keeps the light cone, with the rate `D` raised by `σ (1 + |S|) / 3` and the cone
centered on the query and the fitness support: selection copies whole genomes, and a fitness locus
far from the query is inspected at once.

Scope. The chain is truncated after `M` branchings, decisions and selections together; the
truncated laws are not shown to converge as `M → ∞`, and no path space is constructed. The fitness
support `S` is a fixed finite set, and every argument with a nonempty tag meets selective events at
rate `σ ≥ 0`. (8.3) assumes `K > 0`. The circuit records supports only, not the function of the
sampling dual.

## Empirical status

None. The bodies here are finite sums, matrix exponentials and calculus on supplied rates, fitness
support and query, so no measurement can bear on them.
-/

namespace Descent.Pangenome.AncestralLocality

open Finset
open scoped Matrix

noncomputable section

section SelectionChain

variable {V : Type*} [DecidableEq V] {n M : ℕ}

/-! ### Selective branching in the truncated chain -/

/-- **A selective branching in the truncated chain.** While fewer than `M` branchings have been
taken, the new parental argument fills slot `n + k` with the support `A_a ∪ S`, and the argument in
slot `a` keeps its support. After `M` branchings the state is left unchanged. -/
def selectionChainBranch (S : Finset V) (x : SupportChainState V n M) (a : Fin (n + M)) :
    SupportChainState V n M :=
  if h : (x.2 : ℕ) < M then
    (Function.update x.1 ⟨n + (x.2 : ℕ), by omega⟩ (x.1 a ∪ S), ⟨(x.2 : ℕ) + 1, by omega⟩)
  else x

/-- **A selective branching raises a nonnegative tag weight by at most `w(A_a) + w(S)`.** -/
theorem tagWeight_selectionChainBranch_le {w : V → ℝ} (hw : ∀ v, 0 ≤ w v) (S : Finset V)
    (x : SupportChainState V n M) (a : Fin (n + M)) :
    tagWeight w (selectionChainBranch S x a).1 ≤
      tagWeight w x.1 + (∑ v ∈ x.1 a, w v + ∑ v ∈ S, w v) := by
  have h1 : 0 ≤ ∑ v ∈ x.1 a, w v := Finset.sum_nonneg fun v _ ↦ hw v
  have h2 : 0 ≤ ∑ v ∈ S, w v := Finset.sum_nonneg fun v _ ↦ hw v
  unfold selectionChainBranch
  split_ifs with h
  · dsimp only
    refine (tagWeight_update_le hw _ _ _).trans ?_
    linarith [sum_union_le_add hw (x.1 a) S]
  · linarith

/-- A selective branching raises the branching count by at most one. -/
theorem selectionChainBranch_count_le (S : Finset V) (x : SupportChainState V n M)
    (a : Fin (n + M)) : (((selectionChainBranch S x a).2 : ℕ) : ℝ) ≤ ((x.2 : ℕ) : ℝ) + 1 := by
  unfold selectionChainBranch
  split_ifs with h
  · simp
  · linarith

variable [Fintype V]

/-- **The jump rates of the truncated chain with selection**: the decisions and coalescences of
`supportChainRate`, and a selective branching at rate `σ` on every argument with a nonempty tag. -/
def selectionChainRate (r : V → V → ℝ) (c σ : ℝ) (S : Finset V) (x y : SupportChainState V n M) :
    ℝ :=
  supportChainRate r c x y +
    ∑ a, if selectionChainBranch S x a = y then (if (x.1 a).Nonempty then σ else 0) else 0

/-- **The generator matrix of the truncated chain with selection.** -/
def selectionChainGenerator (r : V → V → ℝ) (c σ : ℝ) (S : Finset V) :
    Matrix (SupportChainState V n M) (SupportChainState V n M) ℝ :=
  jumpRateGenerator (selectionChainRate r c σ S)

/-- Without selection the rates are those of the neutral chain. -/
theorem selectionChainRate_zero (r : V → V → ℝ) (c : ℝ) (S : Finset V) :
    selectionChainRate (n := n) (M := M) r c 0 S = supportChainRate r c := by
  funext x y
  simp [selectionChainRate]

/-- The chain with selection has nonnegative rates. -/
theorem selectionChainRate_nonneg {r : V → V → ℝ} {c σ : ℝ} (hr : ∀ i j, 0 ≤ r i j) (hc : 0 ≤ c)
    (hσ : 0 ≤ σ) (S : Finset V) (x y : SupportChainState V n M) :
    0 ≤ selectionChainRate r c σ S x y := by
  refine add_nonneg (supportChainRate_nonneg hr hc x y) (Finset.sum_nonneg fun a _ ↦ ?_)
  split_ifs <;> linarith

/-- The generator of the chain with selection is Metzler. -/
theorem selectionChainGenerator_apply_nonneg {r : V → V → ℝ} {c σ : ℝ} (hr : ∀ i j, 0 ≤ r i j)
    (hc : 0 ≤ c) (hσ : 0 ≤ σ) (S : Finset V) {x y : SupportChainState V n M} (hxy : x ≠ y) :
    0 ≤ selectionChainGenerator r c σ S x y :=
  jumpRateGenerator_apply_nonneg (selectionChainRate_nonneg hr hc hσ S) hxy

/-- **The generator acts by decisions, coalescences and selective branchings.** -/
theorem selectionChainGenerator_mulVec (r : V → V → ℝ) (c σ : ℝ) (S : Finset V)
    (f : SupportChainState V n M → ℝ) (x : SupportChainState V n M) :
    (selectionChainGenerator r c σ S *ᵥ f) x = (supportChainGenerator r c *ᵥ f) x +
      ∑ a, (if (x.1 a).Nonempty then σ else 0) * (f (selectionChainBranch S x a) - f x) := by
  rw [selectionChainGenerator, jumpRateGenerator_mulVec, supportChainGenerator,
    jumpRateGenerator_mulVec]
  simp only [selectionChainRate, add_mul, Finset.sum_add_distrib, Finset.sum_mul]
  congr 1
  refine Finset.sum_comm.trans (Finset.sum_congr rfl fun a _ ↦ ?_)
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]

/-- **The drift inequality with selection.** If every row of decision rates sums to at most `D`,
the weight grows by at most the factor `κ` along every edge of positive rate, and the weight is at
least one on every coordinate, then `Q Z^{(w)} ≤ (D (1 + 2κ) + σ (1 + w(S))) Z^{(w)}`. -/
theorem selectionChainGenerator_tagWeight_le {r : V → V → ℝ} {c D κ σ : ℝ} {w : V → ℝ}
    (hr : ∀ i j, 0 ≤ r i j) (hD : ∀ i, ∑ j, r i j ≤ D) (hc : 0 ≤ c) (hσ : 0 ≤ σ)
    (hw1 : ∀ v, 1 ≤ w v) (hκ : 0 ≤ κ) (hedge : ∀ i j, 0 < r i j → w j ≤ κ * w i)
    (S : Finset V) (x : SupportChainState V n M) :
    (selectionChainGenerator r c σ S *ᵥ fun y ↦ tagWeight w y.1) x ≤
      (D * (1 + 2 * κ) + σ * (1 + ∑ v ∈ S, w v)) * tagWeight w x.1 := by
  have hw : ∀ v, 0 ≤ w v := fun v ↦ zero_le_one.trans (hw1 v)
  rw [selectionChainGenerator_mulVec]
  have hdec := supportChainGenerator_tagWeight_le hr hD hc hw hκ hedge x
  have hsel : ∑ a, (if (x.1 a).Nonempty then σ else 0) *
      (tagWeight w (selectionChainBranch S x a).1 - tagWeight w x.1) ≤
        σ * (1 + ∑ v ∈ S, w v) * tagWeight w x.1 := by
    calc ∑ a, (if (x.1 a).Nonempty then σ else 0) *
          (tagWeight w (selectionChainBranch S x a).1 - tagWeight w x.1)
        ≤ ∑ a, (if (x.1 a).Nonempty then σ * (∑ v ∈ x.1 a, w v + ∑ v ∈ S, w v) else 0) := by
          refine Finset.sum_le_sum fun a _ ↦ ?_
          split_ifs
          · exact mul_le_mul_of_nonneg_left
              (by linarith [tagWeight_selectionChainBranch_le hw S x a]) hσ
          · rw [zero_mul]
      _ = σ * ∑ a ∈ univ.filter (fun a ↦ (x.1 a).Nonempty),
            (∑ v ∈ x.1 a, w v + ∑ v ∈ S, w v) := by
          rw [Finset.mul_sum, Finset.sum_filter]
      _ ≤ σ * (1 + ∑ v ∈ S, w v) * tagWeight w x.1 := selectionWeightRate_le hw1 hσ S x.1
  linarith

/-- **The branching count has drift at most `decisionRate + σ Z`**: decisions at their rate, and
selective branchings at rate `σ` on at most `Z` nonempty arguments. -/
theorem selectionChainGenerator_count_le {r : V → V → ℝ} {c σ : ℝ} (hr : ∀ i j, 0 ≤ r i j)
    (hσ : 0 ≤ σ) (S : Finset V) (x : SupportChainState V n M) :
    (selectionChainGenerator r c σ S *ᵥ fun y ↦ ((y.2 : ℕ) : ℝ)) x ≤
      decisionRate r x.1 + σ * tagCount x.1 := by
  rw [selectionChainGenerator_mulVec]
  have hdec := supportChainGenerator_count_le (c := c) hr x
  have hsel : ∑ a, (if (x.1 a).Nonempty then σ else 0) *
      ((((selectionChainBranch S x a).2 : ℕ) : ℝ) - ((x.2 : ℕ) : ℝ)) ≤ σ * tagCount x.1 := by
    calc ∑ a, (if (x.1 a).Nonempty then σ else 0) *
          ((((selectionChainBranch S x a).2 : ℕ) : ℝ) - ((x.2 : ℕ) : ℝ))
        ≤ ∑ a, (if (x.1 a).Nonempty then σ * ((x.1 a).card : ℝ) else 0) := by
          refine Finset.sum_le_sum fun a _ ↦ ?_
          split_ifs with ha
          · refine mul_le_mul_of_nonneg_left ?_ hσ
            have h1 : (1 : ℝ) ≤ (x.1 a).card := Nat.one_le_cast.mpr ha.card_pos
            linarith [selectionChainBranch_count_le S x a]
          · rw [zero_mul]
      _ ≤ ∑ a, σ * ((x.1 a).card : ℝ) := Finset.sum_le_sum fun a _ ↦ by
          split_ifs
          · exact le_rfl
          · exact mul_nonneg hσ (Nat.cast_nonneg _)
      _ = σ * tagCount x.1 := by rw [← Finset.mul_sum, tagCount, Nat.cast_sum]
  linarith

/-! ### The law of the chain -/

/-- **The law at time `t` of the truncated chain with selection**, started from `n` arguments
carrying `A`: `μ_t = δ_{x₀} e^{tQ}`. -/
def selectionChainLaw (r : V → V → ℝ) (c σ : ℝ) (S A : Finset V) (n M : ℕ) (t : ℝ)
    (y : SupportChainState V n M) : ℝ :=
  jumpChainLaw (selectionChainGenerator r c σ S) (supportChainStart A n M) t y

/-- **Without selection the law is the neutral one** of `SupportChainDynkin`. -/
theorem selectionChainLaw_zero (r : V → V → ℝ) (c : ℝ) (S A : Finset V) (n M : ℕ) :
    selectionChainLaw r c 0 S A n M = supportChainLaw r c A n M := by
  funext t y
  simp only [selectionChainLaw, supportChainLaw, selectionChainGenerator, supportChainGenerator,
    selectionChainRate_zero]

/-- **Dynkin's formula for the chain with selection**: `d/dt ∫ f dμ_t = ∫ Q f dμ_t`. -/
theorem hasDerivAt_sum_selectionChainLaw_mul (r : V → V → ℝ) (c σ : ℝ) (S A : Finset V)
    (n M : ℕ) (f : SupportChainState V n M → ℝ) (t : ℝ) :
    HasDerivAt (fun u ↦ ∑ y, selectionChainLaw r c σ S A n M u y * f y)
      (∑ y, selectionChainLaw r c σ S A n M t y * (selectionChainGenerator r c σ S *ᵥ f) y) t :=
  hasDerivAt_sum_jumpChainLaw_mul _ _ f t

/-- The chain with selection has a nonnegative law at every time `t ≥ 0`. -/
theorem selectionChainLaw_nonneg {r : V → V → ℝ} {c σ : ℝ} (hr : ∀ i j, 0 ≤ r i j) (hc : 0 ≤ c)
    (hσ : 0 ≤ σ) (S A : Finset V) (n M : ℕ) {t : ℝ} (ht : 0 ≤ t) (y : SupportChainState V n M) :
    0 ≤ selectionChainLaw r c σ S A n M t y :=
  jumpChainLaw_nonneg (fun _ _ hxy ↦ selectionChainGenerator_apply_nonneg hr hc hσ S hxy) _ ht y

/-- The chain with selection keeps total mass one. -/
theorem sum_selectionChainLaw (r : V → V → ℝ) (c σ : ℝ) (S A : Finset V) (n M : ℕ) (t : ℝ) :
    ∑ y, selectionChainLaw r c σ S A n M t y = 1 :=
  sum_jumpChainLaw (sum_jumpRateGenerator _) _ t

/-! ### Theorem 7 under selection -/

/-- **(8.2) under selection**: for the chain truncated after any number `M` of branchings,
`E Z_T ≤ n |A| e^{(3D + σ (1 + |S|)) T}`. -/
theorem sum_selectionChainLaw_mul_tagCount_le {r : V → V → ℝ} {c D σ T : ℝ}
    (hr : ∀ i j, 0 ≤ r i j) (hD : ∀ i, ∑ j, r i j ≤ D) (hc : 0 ≤ c) (hσ : 0 ≤ σ)
    (S A : Finset V) (n M : ℕ) (hT : 0 ≤ T) :
    ∑ y, selectionChainLaw r c σ S A n M T y * (tagCount y.1 : ℝ) ≤
      n * A.card * Real.exp ((3 * D + σ * (1 + S.card)) * T) := by
  have hunit : (fun y : SupportChainState V n M ↦ (tagCount y.1 : ℝ)) =
      fun y ↦ tagWeight (fun _ ↦ 1) y.1 := funext fun y ↦ (tagWeight_one y.1).symm
  have hdrift : ∀ x : SupportChainState V n M,
      (selectionChainGenerator r c σ S *ᵥ fun y ↦ (tagCount y.1 : ℝ)) x ≤
        (3 * D + σ * (1 + S.card)) * (tagCount x.1 : ℝ) := by
    intro x
    have h := selectionChainGenerator_tagWeight_le (w := fun _ ↦ 1) (κ := 1) hr hD hc hσ
      (fun _ ↦ le_rfl) zero_le_one (fun _ _ _ ↦ by norm_num) S x
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at h
    rw [hunit, ← tagWeight_one]
    linarith
  have h := sum_jumpChainLaw_mul_le_exp (Q := selectionChainGenerator r c σ S)
    (fun _ _ hxy ↦ selectionChainGenerator_apply_nonneg hr hc hσ S hxy) hdrift
    (supportChainStart A n M) hT
  have hstart : (tagCount (supportChainStart A n M).1 : ℝ) = n * A.card := by
    rw [← tagWeight_one, tagWeight_supportChainStart]
    simp
  beta_reduce at h
  rw [hstart] at h
  exact h

/-- **The integrated exponential bound at any rate.** If `m t ≤ C e^{K t}` on `[0, T]` with `K > 0`
and `b ≤ ρ ∫_0^T m`, then `b ≤ C ρ (e^{K T} - 1) / K`. -/
theorem le_mul_div_mul_exp_sub_one {m : ℝ → ℝ} {b C ρ K T : ℝ} (hρ : 0 ≤ ρ) (hK : 0 < K)
    (hT : 0 ≤ T) (hcont : ContinuousOn m (Set.Icc 0 T))
    (hm : ∀ t ∈ Set.Icc 0 T, m t ≤ C * Real.exp (K * t))
    (hb : b ≤ ρ * ∫ t in (0 : ℝ)..T, m t) : b ≤ C * ρ / K * (Real.exp (K * T) - 1) := by
  have hK0 : K ≠ 0 := hK.ne'
  have hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) T,
      HasDerivAt (fun t ↦ C * ρ / K * (Real.exp (K * t) - 1)) (ρ * (C * Real.exp (K * t))) t :=
    fun t _ ↦ ((((hasDerivAt_id' (x := t)).const_mul K).exp.sub_const 1).const_mul
      (C * ρ / K)).congr_deriv (by field_simp <;> ring)
  have hprimitive : ∫ t in (0 : ℝ)..T, ρ * (C * Real.exp (K * t)) =
      C * ρ / K * (Real.exp (K * T) - 1) := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
      (Continuous.intervalIntegrable (by fun_prop) 0 T)]
    simp
  have hmono : ∫ t in (0 : ℝ)..T, m t ≤ ∫ t in (0 : ℝ)..T, C * Real.exp (K * t) :=
    intervalIntegral.integral_mono_on hT (hcont.intervalIntegrable_of_Icc hT)
      (Continuous.intervalIntegrable (by fun_prop) 0 T) hm
  calc b ≤ ρ * ∫ t in (0 : ℝ)..T, m t := hb
    _ ≤ ρ * ∫ t in (0 : ℝ)..T, C * Real.exp (K * t) := mul_le_mul_of_nonneg_left hmono hρ
    _ = ∫ t in (0 : ℝ)..T, ρ * (C * Real.exp (K * t)) :=
      (intervalIntegral.integral_const_mul _ _).symm
    _ = C * ρ / K * (Real.exp (K * T) - 1) := hprimitive

/-- **(8.3) under selection**: for the chain truncated after any number `M` of branchings, the
expected number of branchings by time `T` is at most `n |A| (D + σ) (e^{K T} - 1) / K`, with
`K = 3D + σ (1 + |S|) > 0`. -/
theorem sum_selectionChainLaw_mul_count_le {r : V → V → ℝ} {c D σ T : ℝ} (hr : ∀ i j, 0 ≤ r i j)
    (hD : ∀ i, ∑ j, r i j ≤ D) (hD0 : 0 ≤ D) (hc : 0 ≤ c) (hσ : 0 ≤ σ) (S A : Finset V)
    (n M : ℕ) (hT : 0 ≤ T) (hK : 0 < 3 * D + σ * (1 + S.card)) :
    ∑ y, selectionChainLaw r c σ S A n M T y * ((y.2 : ℕ) : ℝ) ≤
      n * A.card * (D + σ) / (3 * D + σ * (1 + S.card)) *
        (Real.exp ((3 * D + σ * (1 + S.card)) * T) - 1) := by
  have hcomp := sum_jumpChainLaw_mul_sub_eq_integral (selectionChainGenerator r c σ S)
    (supportChainStart A n M) (fun y ↦ ((y.2 : ℕ) : ℝ)) T
  have hzero : (((supportChainStart A n M).2 : ℕ) : ℝ) = 0 := by
    simp [supportChainStart]
  simp only [hzero, sub_zero] at hcomp
  have hcont : ContinuousOn
      (fun t ↦ ∑ y, selectionChainLaw r c σ S A n M t y * (tagCount y.1 : ℝ)) (Set.Icc 0 T) :=
    fun t _ ↦ (hasDerivAt_sum_selectionChainLaw_mul r c σ S A n M
      (fun y ↦ (tagCount y.1 : ℝ)) t).continuousAt.continuousWithinAt
  have hrate : Continuous fun t ↦ ∑ y, selectionChainLaw r c σ S A n M t y *
      (selectionChainGenerator r c σ S *ᵥ fun y ↦ ((y.2 : ℕ) : ℝ)) y :=
    continuous_iff_continuousAt.mpr fun t ↦ (hasDerivAt_sum_selectionChainLaw_mul r c σ S A n M
      (selectionChainGenerator r c σ S *ᵥ fun y ↦ ((y.2 : ℕ) : ℝ)) t).continuousAt
  refine le_mul_div_mul_exp_sub_one (add_nonneg hD0 hσ) hK hT hcont
    (fun t ht ↦ sum_selectionChainLaw_mul_tagCount_le hr hD hc hσ S A n M ht.1) ?_
  calc ∑ y, selectionChainLaw r c σ S A n M T y * ((y.2 : ℕ) : ℝ)
      = ∫ t in (0 : ℝ)..T, ∑ y, selectionChainLaw r c σ S A n M t y *
          (selectionChainGenerator r c σ S *ᵥ fun y ↦ ((y.2 : ℕ) : ℝ)) y := hcomp
    _ ≤ ∫ t in (0 : ℝ)..T,
          (D + σ) * ∑ y, selectionChainLaw r c σ S A n M t y * (tagCount y.1 : ℝ) := by
        refine intervalIntegral.integral_mono_on hT (hrate.intervalIntegrable 0 T)
          ((hcont.intervalIntegrable_of_Icc hT).const_mul (D + σ)) fun t ht ↦ ?_
        calc ∑ y, selectionChainLaw r c σ S A n M t y *
              (selectionChainGenerator r c σ S *ᵥ fun y ↦ ((y.2 : ℕ) : ℝ)) y
            ≤ ∑ y, selectionChainLaw r c σ S A n M t y * ((D + σ) * (tagCount y.1 : ℝ)) :=
              Finset.sum_le_sum fun y _ ↦ mul_le_mul_of_nonneg_left
                ((selectionChainGenerator_count_le hr hσ S y).trans
                  (by linarith [decisionRate_le hD y.1]))
                (selectionChainLaw_nonneg hr hc hσ S A n M ht.1 y)
          _ = (D + σ) * ∑ y, selectionChainLaw r c σ S A n M t y * (tagCount y.1 : ℝ) := by
              rw [Finset.mul_sum]
              exact Finset.sum_congr rfl fun y _ ↦ by ring
    _ = (D + σ) *
          ∫ t in (0 : ℝ)..T, ∑ y, selectionChainLaw r c σ S A n M t y * (tagCount y.1 : ℝ) :=
        intervalIntegral.integral_const_mul _ _

/-! ### Theorem 8 under selection -/

/-- **The light-cone count under selection**: for `a ≥ 1` and weights measured from the query
together with the fitness support, `E Z^{(a)}_T ≤ n |A| e^{(D (1 + 2a) + σ (1 + |S|)) T}`. -/
theorem sum_selectionChainLaw_mul_lightWeight_le {r : V → V → ℝ} {c D σ T a : ℝ}
    (hr : ∀ i j, 0 ≤ r i j) (hD : ∀ i, ∑ j, r i j ≤ D) (hc : 0 ≤ c) (hσ : 0 ≤ σ) (ha : 1 ≤ a)
    (S A : Finset V) (n M ℓ : ℕ) (hT : 0 ≤ T) :
    ∑ y, selectionChainLaw r c σ S A n M T y * tagWeight (lightWeight r (A ∪ S) ℓ a) y.1 ≤
      n * A.card * Real.exp ((D * (1 + 2 * a) + σ * (1 + S.card)) * T) := by
  have hS : ∑ v ∈ S, lightWeight r (A ∪ S) ℓ a v = S.card := by
    calc ∑ v ∈ S, lightWeight r (A ∪ S) ℓ a v = ∑ _v ∈ S, (1 : ℝ) :=
          Finset.sum_congr rfl fun v hv ↦ by
            rw [lightWeight, lightDepth_eq_zero (Finset.mem_union_right A hv), pow_zero]
      _ = S.card := by simp
  have hdrift : ∀ x : SupportChainState V n M,
      (selectionChainGenerator r c σ S *ᵥ fun y ↦ tagWeight (lightWeight r (A ∪ S) ℓ a) y.1) x ≤
        (D * (1 + 2 * a) + σ * (1 + S.card)) * tagWeight (lightWeight r (A ∪ S) ℓ a) x.1 := by
    intro x
    have h := selectionChainGenerator_tagWeight_le (w := lightWeight r (A ∪ S) ℓ a) (κ := a)
      hr hD hc hσ (fun _ ↦ one_le_pow₀ ha) (by linarith) (fun _ _ hij ↦ lightWeight_le_mul ha hij)
      S x
    rwa [hS] at h
  have h := sum_jumpChainLaw_mul_le_exp (Q := selectionChainGenerator r c σ S)
    (fun _ _ hxy ↦ selectionChainGenerator_apply_nonneg hr hc hσ S hxy) hdrift
    (supportChainStart A n M) hT
  have hstart : tagWeight (lightWeight r (A ∪ S) ℓ a) (supportChainStart A n M).1 =
      n * A.card := by
    rw [tagWeight_supportChainStart]
    congr 1
    calc ∑ v ∈ A, lightWeight r (A ∪ S) ℓ a v = ∑ _v ∈ A, (1 : ℝ) :=
          Finset.sum_congr rfl fun v hv ↦ by
            rw [lightWeight, lightDepth_eq_zero (Finset.mem_union_left S hv), pow_zero]
      _ = A.card := by simp
  beta_reduce at h
  rw [hstart] at h
  exact h

open scoped Classical in
/-- **(9.1) under selection.** For the chain truncated after any number `M` of branchings and every
`a ≥ 1`, the probability that the circuit holds a coordinate at distance at least `ℓ` from `A ∪ S`
at time `T` is at most `min {1, n |A| e^{(D (1 + 2a) + σ (1 + |S|)) T} / a^ℓ}`. -/
theorem sum_selectionChainLaw_escape_le {r : V → V → ℝ} {c D σ T a : ℝ} (hr : ∀ i j, 0 ≤ r i j)
    (hD : ∀ i, ∑ j, r i j ≤ D) (hc : 0 ≤ c) (hσ : 0 ≤ σ) (ha : 1 ≤ a) (S A : Finset V)
    (n M ℓ : ℕ) (hT : 0 ≤ T) :
    ∑ y, (if univ.val.map y.1 ∈ escapeSet r (A ∪ S) ℓ then selectionChainLaw r c σ S A n M T y
        else 0) ≤
      min 1 (n * A.card * Real.exp ((D * (1 + 2 * a) + σ * (1 + S.card)) * T) / a ^ ℓ) := by
  have hnonneg : ∀ y, 0 ≤ selectionChainLaw r c σ S A n M T y :=
    selectionChainLaw_nonneg hr hc hσ S A n M hT
  have hpos : 0 < a ^ ℓ := pow_pos (by linarith) ℓ
  refine le_min ?_ ?_
  · calc ∑ y, (if univ.val.map y.1 ∈ escapeSet r (A ∪ S) ℓ then
          selectionChainLaw r c σ S A n M T y else 0)
        ≤ ∑ y, selectionChainLaw r c σ S A n M T y := Finset.sum_le_sum fun y _ ↦ by
          split_ifs
          · exact le_rfl
          · exact hnonneg y
      _ = 1 := sum_selectionChainLaw r c σ S A n M T
  · rw [le_div_iff₀ hpos, Finset.sum_mul]
    refine (Finset.sum_le_sum fun y _ ↦ ?_).trans
      (sum_selectionChainLaw_mul_lightWeight_le hr hD hc hσ ha S A n M ℓ hT)
    split_ifs with hy
    · have h := pow_le_weightedCount_of_mem_escapeSet (a := a) (by linarith) hy
      rw [weightedCount_map_univ] at h
      exact mul_le_mul_of_nonneg_left h (hnonneg y)
    · rw [zero_mul]
      exact mul_nonneg (hnonneg y) (tagWeight_nonneg (lightWeight_nonneg (by linarith)) y.1)

open scoped Classical in
/-- **(9.1) under selection as the neutral bound at a raised rate**: with
`D' = D + σ (1 + |S|) / 3`, the escape probability is at most
`min {1, n |A| e^{D' (1 + 2a) T} / a^ℓ}`, the bound of `SupportChainDynkin` at the rate `D'`. -/
theorem sum_selectionChainLaw_escape_le_shift {r : V → V → ℝ} {c D σ T a : ℝ}
    (hr : ∀ i j, 0 ≤ r i j) (hD : ∀ i, ∑ j, r i j ≤ D) (hc : 0 ≤ c) (hσ : 0 ≤ σ) (ha : 1 ≤ a)
    (S A : Finset V) (n M ℓ : ℕ) (hT : 0 ≤ T) :
    ∑ y, (if univ.val.map y.1 ∈ escapeSet r (A ∪ S) ℓ then selectionChainLaw r c σ S A n M T y
        else 0) ≤
      min 1 (n * A.card * Real.exp ((D + σ * (1 + S.card) / 3) * (1 + 2 * a) * T) / a ^ ℓ) := by
  refine (sum_selectionChainLaw_escape_le hr hD hc hσ ha S A n M ℓ hT).trans
    (min_le_min le_rfl ?_)
  have hs : 0 ≤ σ * (1 + (S.card : ℝ)) := mul_nonneg hσ (by positivity)
  have hK : (D * (1 + 2 * a) + σ * (1 + S.card)) * T ≤
      (D + σ * (1 + S.card) / 3) * (1 + 2 * a) * T := by
    linarith [mul_nonneg (mul_nonneg hs (sub_nonneg.mpr ha)) hT]
  have hpos : 0 < a ^ ℓ := pow_pos (by linarith) ℓ
  have hN : 0 ≤ (n : ℝ) * A.card := by positivity
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hK) hN)
    hpos.le

open scoped Classical in
/-- **(9.2) under selection**: with `D' = D + σ (1 + |S|) / 3` and at the radius
`a = ℓ / (2 D' T) ≥ 1`, the escape bound is `min {1, n |A| e^{D' T} (2 e D' T / ℓ)^ℓ}`. -/
theorem sum_selectionChainLaw_escape_le_radius {r : V → V → ℝ} {c D σ T : ℝ}
    (hr : ∀ i j, 0 ≤ r i j) (hD : ∀ i, ∑ j, r i j ≤ D) (hc : 0 ≤ c) (hσ : 0 ≤ σ)
    (S A : Finset V) (n M ℓ : ℕ) (hT : 0 ≤ T) (hDT : (D + σ * (1 + S.card) / 3) * T ≠ 0)
    (hradius : 1 ≤ (ℓ : ℝ) / (2 * (D + σ * (1 + S.card) / 3) * T)) :
    ∑ y, (if univ.val.map y.1 ∈ escapeSet r (A ∪ S) ℓ then selectionChainLaw r c σ S A n M T y
        else 0) ≤
      min 1 (n * A.card * Real.exp ((D + σ * (1 + S.card) / 3) * T) *
        (2 * Real.exp 1 * (D + σ * (1 + S.card) / 3) * T / ℓ) ^ ℓ) := by
  have h := sum_selectionChainLaw_escape_le_shift hr hD hc hσ hradius S A n M ℓ hT
  rwa [exp_div_pow_eq_of_radius hDT] at h

open scoped Classical in
/-- **No escape under selection when `D' T = 0`**: the truncated chain holds no coordinate at
distance `ℓ ≥ 1` from `A ∪ S`. -/
theorem sum_selectionChainLaw_escape_eq_zero {r : V → V → ℝ} {c D σ T : ℝ}
    (hr : ∀ i j, 0 ≤ r i j) (hD : ∀ i, ∑ j, r i j ≤ D) (hc : 0 ≤ c) (hσ : 0 ≤ σ)
    (S A : Finset V) (n M ℓ : ℕ) (hT : 0 ≤ T) (hDT : (D + σ * (1 + S.card) / 3) * T = 0)
    (hℓ : 1 ≤ ℓ) :
    ∑ y, (if univ.val.map y.1 ∈ escapeSet r (A ∪ S) ℓ then selectionChainLaw r c σ S A n M T y
        else 0) = 0 :=
  eq_zero_of_forall_escape_bound hDT hℓ
    (Finset.sum_nonneg fun y _ ↦ by
      split_ifs
      · exact selectionChainLaw_nonneg hr hc hσ S A n M hT y
      · exact le_rfl)
    fun a ha ↦ sum_selectionChainLaw_escape_le_shift hr hD hc hσ ha.le S A n M ℓ hT

end SelectionChain

end

end Descent.Pangenome.AncestralLocality
