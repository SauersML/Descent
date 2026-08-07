/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Coalescent.WrightFisher
import Descent.Coalescent.Restriction
import Mathlib.Tactic

assert_below Descent.Pangenome Descent.PopGen Descent.Spectral Descent.Blindness
assert_below Descent.Conditionals Descent.Portability Descent.Decision Descent.Program

namespace Descent

/-!
# The pedigree, and the chain `ℛ_s` it induces on a sample

K-G section 2 defines the object the whole theory is about in one sentence: *"select `n`
particular individuals `I₁, …, I_n` from `G_r`; the family tree of these and their ancestors
may be described by means of a sequence of equivalence relations `ℛ_s` on `{1, …, n}`, where
`ℛ_s` contains a pair `(i,j)` if `I_i` and `I_j` have a common ancestor in `G_{r-s}`."*

The corpus has had the chain's LAW since `Descent.Coalescent.Kernel` and its rates since
`Descent.Coalescent.WrightFisher`, but it has never had the sentence: an explicit pedigree,
an explicit sample, and `ℛ_s` defined off them.  Without it, every statement about `ℛ_s` is a
statement about a chain that was *declared* to have those rates, and the genealogical reading
of the state -- "these two share an ancestor" -- is a gloss on a symbol rather than a
provable property.

This file supplies it, and it is deliberately free of probability.  A `Pedigree N` is a
sequence of parent maps, one per generation; `ancestor P s` traces a line of descent back `s`
generations; `ancestralRel P sample s` is Kingman's `ℛ_s`.  All of K-G's structural claims
about `ℛ_s` -- (2.5), (2.6), (2.7), and the restriction consistency of (7.1)-(7.2) -- are
then true of EVERY pedigree, random or not:

* `ancestralRel_zero`: `ℛ_0 = Δ` for a sample of distinct individuals (2.5).
* `ancestralRel_le_succ`: `ℛ_s ⊆ ℛ_{s+1}` (2.6) -- once two lines meet they never separate,
  which is a fact about composing functions and needs no model.
* `ancestralRel_eq_top_iff`: `ℛ_s = Θ` exactly when the whole sample has a common ancestor
  (2.7), which is the event `γ(N,s)` measures.
* `restrict_ancestralRel`: **sub-sampling commutes with the mechanism** (7.1).  Kingman
  checks `ρ_{mn}` maps `n`-coalescents to `m`-coalescents at the level of the limit process;
  here it holds one level down, at the pedigree, for every realisation -- discarding
  `I_{m+1}, …, I_n` before tracing ancestry gives the same relation as tracing first and
  restricting after.

The randomness enters exactly one place: which pedigree.  `Descent.Coalescent.WrightFisher`
puts the uniform law on a single generation's parent map and counts the rates off it, and
that law composed over generations is the law on `Pedigree N`.  Separating the two means the
structural facts do not have to be re-proved for each reproduction model -- Moran, Cannings,
or Wright-Fisher -- because they were never about the law.

## Main results

- `ancestor`, `ancestralRel`: the mechanism and Kingman's `ℛ_s`, defined.
- `ancestralRel_zero`, `ancestralRel_le_succ`, `ancestralRel_monotone`: **K-G (2.5)-(2.6)**.
- `ancestralRel_eq_top_iff`: **K-G (2.7)**, `Θ` is "the sample has a common ancestor".
- `restrict_ancestralRel`: **K-G (7.1)**, restriction commutes with the mechanism.
- `ancestralRel_one_eq_ancestralPartition`: at one generation this IS
  `WrightFisher.ancestralPartition`, so the counted rates apply to this chain and not to a
  parallel one.
-/

namespace Coalescent

/-! ### The mechanism -/

/-- **A pedigree.**  `P s` is the parent map from generation `r - s` to generation
`r - s - 1`: individual `x` alive `s` generations back had parent `P s x`.  Nothing is
assumed about how the maps were chosen, and in particular they need not be independent or
identically distributed.

Empirical status: THIS IS THE MODEL's carrier, not a claim.  Which pedigrees are likely is
the modelling question, and `Descent.Coalescent.WrightFisher.parentAssignment` is one
answer -- the uniform one, K-G (2.2). -/
abbrev Pedigree (N : ℕ) : Type := ℕ → Fin N → Fin N

/-- The ancestor of `x` exactly `s` generations back. -/
def ancestor {N : ℕ} (P : Pedigree N) : ℕ → Fin N → Fin N
  | 0 => id
  | s + 1 => fun x ↦ P s (ancestor P s x)

@[simp] theorem ancestor_zero {N : ℕ} (P : Pedigree N) (x : Fin N) :
    ancestor P 0 x = x := rfl

@[simp] theorem ancestor_succ {N : ℕ} (P : Pedigree N) (s : ℕ) (x : Fin N) :
    ancestor P (s + 1) x = P s (ancestor P s x) := rfl

/-! ### Kingman's `ℛ_s` -/

/-- **K-G section 2: `ℛ_s`.**  Two sample members are related when their lines of descent
have met within `s` generations.  This is the kernel of "who is your ancestor", which is what
makes it an equivalence relation with no argument: having a common ancestor is transitive
because equality is.

Empirical status: NOT AN EMPIRICAL CLAIM.  It defines "common ancestor" rather than
asserting one; whether a real sample's relation looks like a coalescent's is the empirical
question, and it is a question about the pedigree, not about this definition. -/
def ancestralRel {n N : ℕ} (P : Pedigree N) (sample : Fin n → Fin N) (s : ℕ) : ER n :=
  Setoid.ker fun i ↦ ancestor P s (sample i)

theorem ancestralRel_rel {n N : ℕ} (P : Pedigree N) (sample : Fin n → Fin N) (s : ℕ)
    (i j : Fin n) :
    (ancestralRel P sample s).r i j
      ↔ ancestor P s (sample i) = ancestor P s (sample j) := Iff.rfl

/-- **`ℛ_s` at any depth is the ONE-generation ancestral partition, applied to the
`s`-generation ancestor map.**

`Descent.Coalescent.WrightFisher.ancestralPartition` is the object Kingman's `R_1` names:
who shares a parent, one step back.  This says the whole pedigree theory adds no second
construction on top of it -- `ancestralRel` at depth `s` is that same partition, taken of
`ancestor P s ∘ sample` instead of of the parent map.  The depth lives entirely in the map
being kernelled, and none of it in the kernelling.

That is why every structural fact about `ℛ_s` in this file is proved by `congrArg` and none
of them by probability: `ancestralPartition` is a `Setoid.ker`, kernels are equivalence
relations for free, and a coarsening of the map coarsens its kernel.  It is also what lets
`Descent.Pangenome.GraphCoalescent.Observation.graphKer` be the same object under a
different reading of the map -- there the map is a graph's interface rather than a
generation of reproduction, and nothing else changes. -/
theorem ancestralRel_eq_ancestralPartition {n N : ℕ} (P : Pedigree N)
    (sample : Fin n → Fin N) (s : ℕ) :
    ancestralRel P sample s = ancestralPartition fun i ↦ ancestor P s (sample i) := rfl

/-- **K-G (2.5): `ℛ_0 = Δ`.**  At the moment of sampling nobody shares an ancestor with anybody but
themselves -- provided the `n` individuals sampled are distinct, which is the
hypothesis, and is what "select `n` particular individuals" means. -/
theorem ancestralRel_zero {n N : ℕ} (P : Pedigree N) {sample : Fin n → Fin N}
    (hs : Function.Injective sample) : ancestralRel P sample 0 = Delta n := by
  refine Setoid.ext fun i j ↦ ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have hij : sample i = sample j := h
    exact hs hij
  · show ancestor P 0 (sample i) = ancestor P 0 (sample j)
    rw [show i = j from h]

/-- **K-G (2.6): `ℛ_s ⊆ ℛ_{s+1}`.**  Lines of descent that have met stay met.  The proof is
that applying one more parent map to two equal ancestors leaves them equal, which is
`congrArg` -- there is no probability in it, and so no reproduction model can fail it. -/
theorem ancestralRel_le_succ {n N : ℕ} (P : Pedigree N) (sample : Fin n → Fin N) (s : ℕ) :
    ancestralRel P sample s ≤ ancestralRel P sample (s + 1) := by
  intro i j hij
  show ancestor P (s + 1) (sample i) = ancestor P (s + 1) (sample j)
  simp only [ancestor_succ]
  exact congrArg (P s) hij

/-- The genealogy coarsens monotonically: going further back can only merge lineages. -/
theorem ancestralRel_monotone {n N : ℕ} (P : Pedigree N) (sample : Fin n → Fin N) :
    Monotone (ancestralRel P sample) := by
  refine monotone_nat_of_le_succ fun s ↦ ?_
  exact ancestralRel_le_succ P sample s

/-- **K-G (2.7): `Θ` is exactly the event that the sample has a common ancestor.**  Kingman's
`γ(N,s)` is the probability of this at `n = N`, and the state `Θ` of the coalescent is not a
formal absorbing symbol but this statement about the pedigree. -/
theorem ancestralRel_eq_top_iff {n N : ℕ} (P : Pedigree N) (sample : Fin n → Fin N) (s : ℕ) :
    ancestralRel P sample s = Theta n
      ↔ ∀ i j : Fin n, ancestor P s (sample i) = ancestor P s (sample j) := by
  constructor
  · intro h i j
    have : (ancestralRel P sample s).r i j := by
      rw [h]
      trivial
    exact this
  · intro h
    exact Setoid.ext fun i j ↦ ⟨fun _ ↦ trivial, fun _ ↦ h i j⟩

/-- Once the sample has coalesced it stays coalesced: `Θ` is absorbing, as a fact about
pedigrees rather than a property imposed on a chain. -/
theorem ancestralRel_eq_top_of_le {n N : ℕ} (P : Pedigree N) (sample : Fin n → Fin N)
    {s t : ℕ} (hst : s ≤ t) (h : ancestralRel P sample s = Theta n) :
    ancestralRel P sample t = Theta n := by
  refine Setoid.ext fun i j ↦ ⟨fun _ ↦ trivial, fun _ ↦ ?_⟩
  have hmono := ancestralRel_monotone P sample hst
  refine hmono ?_
  rw [h]
  trivial

/-! ### Restriction, at the level of the mechanism -/

/-- **K-G (7.1): discarding sample members commutes with tracing ancestry.**  Restricting
`ℛ_s` to the first `m` of the sample gives the `ℛ_s` of the sub-sample -- for every pedigree,
pathwise, with no distributional hypothesis.

This is the reason `ρ_{mn}` maps coalescents to coalescents, one level below where Kingman
states it.  He checks the property of the LIMIT process (7.2); it holds already of the finite
mechanism, and so survives any limit that preserves finite-dimensional distributions. -/
theorem restrict_ancestralRel {m n N : ℕ} (h : m ≤ n) (P : Pedigree N)
    (sample : Fin n → Fin N) (s : ℕ) :
    restrict h (ancestralRel P sample s) = ancestralRel P (sample ∘ Fin.castLE h) s :=
  Setoid.ext fun _ _ ↦ Iff.rfl

/-- The sub-sample of a coalesced sample is coalesced -- `restrict_ancestralRel` and
`Restriction.restrict_top` combined, recorded because it is the direction a reader checking
consistency will want. -/
theorem ancestralRel_restrict_eq_top {m n N : ℕ} (h : m ≤ n) (P : Pedigree N)
    (sample : Fin n → Fin N) (s : ℕ) (htop : ancestralRel P sample s = Theta n) :
    ancestralRel P (sample ∘ Fin.castLE h) s = Theta m := by
  rw [← restrict_ancestralRel h P sample s, htop, restrict_top]

/-! ### The join with the counted rates

`Descent.Coalescent.WrightFisher.ancestralPartition` is the kernel of a single parent map,
and the rates of that module are counted off it.  The chain defined here has that partition
as its one-generation state, so the counting applies to `ℛ_s` and not to a parallel object
that happens to satisfy the same recursion. -/

/-- **One generation of `ℛ` is `WrightFisher.ancestralPartition`.**  The two developments
meet here: what `WrightFisher` counts the law of is the first step of what this file defines
the trajectory of. -/
theorem ancestralRel_one_eq_ancestralPartition {n N : ℕ} (P : Pedigree N)
    (sample : Fin n → Fin N) :
    ancestralRel P sample 1 = ancestralPartition (fun i ↦ P 0 (sample i)) :=
  Setoid.ext fun _ _ ↦ Iff.rfl

/-- And `ℛ_{s+1}` is the one-generation partition of the ancestors at time `s`: the chain is
generated by iterating a single mechanism, which is the statement that makes it Markov once
the pedigree's generations are independent.  The independence is NOT supplied here -- see
`WrightFisher.pairDistinct`, where the corpus flags it as the one premise counting cannot
give. -/
theorem ancestralRel_succ_eq {n N : ℕ} (P : Pedigree N) (sample : Fin n → Fin N) (s : ℕ) :
    ancestralRel P sample (s + 1)
      = ancestralPartition (fun i ↦ P s (ancestor P s (sample i))) :=
  Setoid.ext fun _ _ ↦ Iff.rfl

end Coalescent

end Descent
