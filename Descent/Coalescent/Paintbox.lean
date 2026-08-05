/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Coalescent.Restriction
import Descent.Coalescent.JumpChain
import Mathlib.Tactic

namespace Descent

/-!
# The paintbox, and Watterson's restriction formula

Kingman (1982), *The coalescent* (**K-C**), section 3, constructs exchangeable random
equivalence relations on `ℕ` by the paintbox: colours `0, 1, 2, …` are present in
proportions `x₀, x₁, x₂, …`, balls are painted independently, and

  `R = {(i, j) ; i = j or Z_i = Z_j ≥ 1}`                                       K-C (3.4)

with colour `0` special -- every ball painted with it is its own class.  Theorem 2 of K-C is
a de Finetti theorem saying every exchangeable random equivalence relation is a mixture of
paintboxes; that theorem is a statement about laws and is not formalised here.  What IS
formalised is the construction itself and the structural reason it is exchangeable:

* `paintboxRel` builds the relation and proves it an equivalence relation, colour `0`
  included -- the special role of `0` is the only fiddly part and it is discharged once.
* `paintboxRel_perm` shows the construction is EQUIVARIANT: permuting the balls permutes
  the colouring.  Exchangeability of the law is then the statement that the colouring is
  i.i.d., which is the probabilistic half; the combinatorial half is this identity, and it
  is exact.

The second half of the file is Watterson's formula K-C (3.19) for the uniform paintbox
`𝒫_k` -- `k` colours with uniform frequencies on the simplex --

  `P{ρ_n R = ξ} = (k!(k-1)! / ((k-l)!(n+k-1)!)) λ₁! ⋯ λ_l!`, for `|ξ| = l ≤ k,`

and its two corollaries.  K-C (3.20), the probability that a sample of `n` still shows all
`k` colours, comes out as `n!(n-1)!/((n+k-1)!(n-k)!)`, and K-C (4.3), the probability that
two given balls share a colour, comes out as `2/(k+1)`.

One cross-link is worth stating because it is not a coincidence and the corpus can now see
it: `restrictionFullProb n 2 = (n-1)/(n+1) = survivalFactor n`.  The probability that a
sample of `n` from a two-colour paintbox still shows both colours is the same function of
`n` as the `θ = 1` absorption factor of K-G (5.11) that
`Descent.Coalescent.Rates.survivalFactor` telescopes.  Both are `2/(k+1)`-type quantities
attached to the same jump chain, which is why Kingman's (4.3) computation and his
martingale share an answer.

## Main results

- `paintboxRel`: K-C (3.4), an equivalence relation, colour `0` handled.
- `paintboxRel_perm`: the paintbox construction is permutation-equivariant.
- `wattersonProb`: K-C (3.19).
- `wattersonProb_pair_merged`: K-C (4.3), `2/(k+1)`.
- `restrictionFullProb_two`: K-C (3.20) at `k = 2` is `(n-1)/(n+1)`.
- `restrictionFullProb_two_eq_survivalFactor`: and that is the absorption factor.
- `tendsto_restrictionFullProb_two`: K-C's "tends to 1 as `n → ∞`", which is his ground for
  calling `𝒫_k` the limiting form of the jump chain's law.
-/

namespace Coalescent

open Filter Nat

/-! ### The paintbox construction -/

/-- **K-C (3.4): the paintbox relation.**  Two balls are related when they are the same ball,
or when they carry the same colour and that colour is not the special colour `0`.  Colour `0`
is the "all different" paint: balls painted with it are singletons.

Empirical status: NOT AN EMPIRICAL CLAIM.  This is a construction of equivalence relations
from colourings. -/
def paintboxRel (Z : ℕ → ℕ) : Setoid ℕ where
  r i j := i = j ∨ (Z i = Z j ∧ 1 ≤ Z i)
  iseqv := by
    constructor
    · intro i
      exact Or.inl rfl
    · rintro i j (h | ⟨h, hz⟩)
      · exact Or.inl h.symm
      · exact Or.inr ⟨h.symm, h ▸ hz⟩
    · rintro i j k (hij | ⟨hij, hzi⟩) (hjk | ⟨hjk, hzj⟩)
      · exact Or.inl (hij.trans hjk)
      · exact Or.inr (hij ▸ ⟨hjk, hzj⟩)
      · exact Or.inr ⟨hjk ▸ hij, hzi⟩
      · exact Or.inr ⟨hij.trans hjk, hzi⟩

theorem paintboxRel_rel (Z : ℕ → ℕ) (i j : ℕ) :
    (paintboxRel Z).r i j ↔ i = j ∨ (Z i = Z j ∧ 1 ≤ Z i) := Iff.rfl

/-- Distinct balls in colour `0` are never related: the special colour makes singletons. -/
theorem paintboxRel_zero {Z : ℕ → ℕ} {i j : ℕ} (hi : Z i = 0) (hij : i ≠ j) :
    ¬ (paintboxRel Z).r i j := by
  rintro (h | ⟨-, hz⟩)
  · exact hij h
  · omega

/-- Distinct balls sharing a non-zero colour are related. -/
theorem paintboxRel_of_eq {Z : ℕ → ℕ} {i j : ℕ} (h : Z i = Z j) (hz : 1 ≤ Z i) :
    (paintboxRel Z).r i j := Or.inr ⟨h, hz⟩

/-- The permutation action of K-C (3.1): `π̂R` relates `x` and `y` when `R` relates their
preimages. -/
def permAction (σ : Equiv.Perm ℕ) (R : Setoid ℕ) : Setoid ℕ := Setoid.comap σ.symm R

/-- **The paintbox construction is equivariant.**  Permuting the balls is the same as
permuting the colouring, exactly.  Exchangeability of the paintbox LAW is then just the
statement that an i.i.d. colouring is exchangeable; this identity is the part that has
nothing to do with probability, and it is where the special colour `0` would break things
if it were not handled uniformly -- it is not, so it does not. -/
theorem paintboxRel_perm (σ : Equiv.Perm ℕ) (Z : ℕ → ℕ) :
    permAction σ (paintboxRel Z) = paintboxRel (Z ∘ σ.symm) := by
  refine Setoid.ext fun x y => ⟨fun hxy => ?_, fun hxy => ?_⟩
  · rcases hxy with h | ⟨h, hz⟩
    · exact Or.inl (σ.symm.injective h)
    · exact Or.inr ⟨h, hz⟩
  · rcases hxy with h | ⟨h, hz⟩
    · exact Or.inl (by rw [h])
    · exact Or.inr ⟨h, hz⟩

/-! ### Watterson's formula for the uniform paintbox

K-C (3.18) takes `x₀ = 0` and the remaining `k` frequencies uniform on the simplex, giving
the law `𝒫_k`, and computes the law of the restriction to a sample of `n`.  The Dirichlet
integral evaluates to (3.19).  The integral itself is not redone here; what is recorded is
the formula and the two corollaries K-C draws from it, both of which are pure factorial
arithmetic and both of which are checked. -/

/-- **K-C (3.19), Watterson's formula.**  The `𝒫_k`-probability that a sample of `n` shows
the relation with class sizes `lam`, where `l = |lam| ≤ k`. -/
noncomputable def wattersonProb (k n : ℕ) (lam : Multiset ℕ) : ℝ :=
  (((k)! * (k - 1)! : ℕ) : ℝ) / ((((k - Multiset.card lam))! * (n + k - 1)! : ℕ) : ℝ)
    * (((lam.map Nat.factorial).prod : ℕ) : ℝ)

/-- **K-C (4.3): two balls share a colour with probability `2/(k+1)`.**

Kingman uses this to show `R_t → Δ` as `t ↓ 0`: with `k` classes the chance that any given
pair is already merged is `2/(k+1)`, which vanishes as the death process comes down from
infinity.  It is the `n = 2`, `l = 1` case of Watterson's formula, and it is exact. -/
theorem wattersonProb_pair_merged {k : ℕ} (hk : 1 ≤ k) :
    wattersonProb k 2 {2} = 2 / ((k : ℝ) + 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have hfac : ((m + 1 + 1)! : ℕ) = (m + 2) * (m + 1)! := Nat.factorial_succ (m + 1)
  have hpos : (((m + 1)! : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hidx : 2 + (m + 1) - 1 = m + 2 := by omega
  have hsub : (m + 1) - Multiset.card ({2} : Multiset ℕ) = m := by simp
  unfold wattersonProb
  rw [hsub, hidx]
  simp only [Multiset.map_singleton, Multiset.prod_singleton]
  rw [show ((m + 2)! : ℕ) = (m + 2) * (m + 1)! from Nat.factorial_succ (m + 1)]
  rw [show ((m + 1)! : ℕ) = (m + 1) * m ! from Nat.factorial_succ m]
  have hm : ((m ! : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  push_cast
  field_simp
  ring

/-- **K-C (3.20).**  The `𝒫_k`-probability that a sample of `n` still shows all `k` colours:
the ratio of the normalising constants of K-C (2.3) and (3.19). -/
noncomputable def restrictionFullProb (n k : ℕ) : ℝ :=
  (((n)! * (n - 1)! : ℕ) : ℝ) / ((((n + k - 1))! * (n - k)! : ℕ) : ℝ)

/-- Two colours, sample of `n`: both colours appear with probability `(n-1)/(n+1)`. -/
theorem restrictionFullProb_two {n : ℕ} (hn : 2 ≤ n) :
    restrictionFullProb n 2 = ((n : ℝ) - 1) / ((n : ℝ) + 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have hidx : m + 2 + 2 - 1 = m + 3 := by omega
  have hsub : m + 2 - 2 = m := by omega
  have hn1 : m + 2 - 1 = m + 1 := by omega
  have hm : ((m ! : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hm2 : (((m + 2)! : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  unfold restrictionFullProb
  rw [hidx, hsub, hn1]
  rw [show ((m + 3)! : ℕ) = (m + 3) * (m + 2)! from Nat.factorial_succ (m + 2)]
  rw [show ((m + 1)! : ℕ) = (m + 1) * m ! from Nat.factorial_succ m]
  push_cast
  field_simp
  ring

/-- **The paintbox restriction probability is the absorption factor.**  K-C's (3.20) at
`k = 2` and K-G's `φ₁` of (5.11) are the same function of `n`.  Both are properties of the
same jump chain -- the first is `P{both colours survive in a sample of n}`, the second is
`∏_{r>n}(1 - d_r⁻¹)` -- and the corpus can now state that they coincide rather than
rediscovering `(n-1)/(n+1)` twice. -/
theorem restrictionFullProb_two_eq_survivalFactor {n : ℕ} (hn : 2 ≤ n) :
    restrictionFullProb n 2 = survivalFactor n := by
  rw [restrictionFullProb_two hn, survivalFactor]

/-- **K-C: "the right-hand side of (3.20) tends to 1 as `n → ∞`".**  This is Kingman's
stated ground for calling `𝒫_k` the limiting form of the jump chain's absolute law: a large
enough sample sees every colour. -/
theorem tendsto_restrictionFullProb_two :
    Tendsto (fun n : ℕ => restrictionFullProb (n + 2) 2) atTop (nhds 1) := by
  have hcongr : ∀ n : ℕ, restrictionFullProb (n + 2) 2 = survivalFactor (n + 2) := by
    intro n
    exact restrictionFullProb_two_eq_survivalFactor (by omega)
  have hform : ∀ n : ℕ, survivalFactor (n + 2) = 1 - 2 / ((n : ℝ) + 3) := by
    intro n
    have hne : ((n : ℝ) + 3) ≠ 0 := by positivity
    unfold survivalFactor
    push_cast
    field_simp
    ring
  have hzero : Tendsto (fun n : ℕ => 2 / ((n : ℝ) + 3)) atTop (nhds 0) := by
    have h2 : (2 : ℝ) ≤ 3 := by norm_num
    have := tendsto_two_div_shift (c := 3) (by norm_num)
    have hshift : ∀ n : ℕ, (3 : ℝ) + (n : ℝ) - 1 = (n : ℝ) + 2 := by
      intro n
      ring
    have hbound : Tendsto (fun n : ℕ => 2 / ((n : ℝ) + 2)) atTop (nhds 0) := by
      simpa [hshift] using this
    refine squeeze_zero (fun n => by positivity) (fun n => ?_) hbound
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    gcongr
    · linarith
    · linarith
  simpa only [hcongr, hform, sub_zero] using tendsto_const_nhds.sub hzero

end Coalescent

end Descent
