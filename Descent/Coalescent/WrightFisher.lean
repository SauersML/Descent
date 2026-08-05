/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Coalescent.Rates
import Descent.Core.Heterozygosity
import Descent.Core.Moments
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Tactic

namespace Descent

/-!
# The Wright-Fisher mechanism, and the rates that come out of it

The corpus has, until this file, proved statements of the form *given this formula, these
consequences follow*.  `Descent.Core.hetRecurrence` posits a per-generation factor `1 - 1/(2Nₑ)` and
solves the recurrence; `lambdaCoalescentMergerRate` posits a merger-rate integral and works
out its algebra; `deathRate` in `Descent.Coalescent.Rates` posits the ladder `k(k-1)/2` and
telescopes it.  None of them says where the number came from.

This file supplies the missing layer for the Wright-Fisher model of Kingman (1982),
*On the genealogy of large populations* (J. Appl. Prob. 19A, 27-43; **K-G**), section 2.
The mechanism is defined explicitly and probabilistically -- `parentAssignment` is the
uniform law on parent maps, which is exactly K-G's "each member of `G_{r+1}` chooses its
parent at random, independently and uniformly from the `N` individuals of `G_r`" -- and
every number below is then COUNTED off that law rather than assumed.

What is derived, and what is still assumed, is stated exactly:

* DERIVED, by counting: the probability that `k` sampled lineages have `k` distinct parents
  is `(N)_k / N^k` (`noCoalescenceProb_eq_card_ratio`), hence `1 - 1/N` for a pair
  (`noCoalescenceProb_two`), and hence lies within `(d_k/N)²/2` of `1 - d_k/N`
  (`coalescenceProb_le`, `le_coalescenceProb`).  That is where `d_k = k(k-1)/2` comes
  from: it is `Σ_{i<k} i/N · N`, the first-order term of a product of parent-collision
  probabilities, and nothing about it is posited.
* ASSUMED, and marked where it enters: that generations are independent, which is the
  single recursive step in `pairDistinct`.  K-G gets this from the Wright-Fisher model's
  independent multinomial reproduction; it is the one modelling premise the counting
  cannot supply.

The last section closes the loop on the corpus's own scalars: `Descent.Core.hetRecurrence`, which
`Descent.PopGen.PopulationGeneticsFoundations` posits, is proved equal to the
mechanism-derived `pairDistinct` at `N = 2 Nₑ`.  The recurrence is no longer a stipulation.

## Main results

- `parentAssignment_apply`: the mechanism is the uniform law on parent maps.
- `noCoalescenceProb_eq_card_ratio`: `(N)_k/N^k` is the uniform measure of the event that
  no two of `k` lineages share a parent.
- `noCoalescenceProb_two`: `1 - 1/N` for a pair, exactly, from the count.
- `coalescenceProb_le` and `le_coalescenceProb`: the two-sided Bonferroni sandwich putting
  the one-generation coalescence probability within `(d_k/N)²/2` of `d_k/N`, which is
  K-G (2.9)-(2.11) for the block-count chain.
- `pairDistinct_eq_pow`: `(1 - 1/N)^s`, K-G section 2.
- `hetRecurrence_eq_pairDistinct`: the corpus's posited drift recurrence IS the
  mechanism-derived pair-survival probability.
-/

namespace Coalescent

open Finset

/-! ### The mechanism

A Wright-Fisher reproduction step, viewed backwards, is a map from the `k` lineages under
consideration to the `N` individuals of the previous generation: lineage `i` came from
individual `f i`.  K-G (2.2) says exactly that this map is uniform on `Fin k → Fin N`.  -/

/-- **The Wright-Fisher parent choice.**  Each of `k` lineages independently and uniformly
picks one of the `N` members of the previous generation.  This is the uniform probability
mass function on parent maps, and it is the ONLY probabilistic input in this file.

Empirical status: THIS IS THE MODEL, not a claim about a population.  K-G (2.2) shows the
symmetric multinomial family-size law is equivalent to this backwards prescription, and
K-G section 4 shows the same limit follows from any exchangeable family-size law with bounded moments, with the family-size variance `σ²` rescaling time.  Whether a given
population reproduces this way is the empirical question, and `Descent.Blindness` records
which statistics could tell. -/
noncomputable def parentAssignment (N k : ℕ) [NeZero N] : PMF (Fin k → Fin N) :=
  PMF.uniformOfFintype (Fin k → Fin N)

/-- The mechanism assigns every parent map the same mass `N^{-k}`. -/
theorem parentAssignment_apply (N k : ℕ) [NeZero N] (f : Fin k → Fin N) :
    parentAssignment N k f = (Fintype.card (Fin k → Fin N) : ENNReal)⁻¹ :=
  PMF.uniformOfFintype_apply f

/-- **The ancestral partition.**  Two lineages fall in the same block exactly when they
chose the same parent.  This is Kingman's `R_1`: the relation on `{1, …, k}` holding of
`(i, j)` when `i` and `j` have a common ancestor one generation back (K-G (2.5)-(2.6)).

Empirical status: NOT AN EMPIRICAL CLAIM.  It is the kernel of the parent map, i.e. a
definition of "common ancestor", not an assertion about one. -/
def ancestralPartition {k N : ℕ} (f : Fin k → Fin N) : Setoid (Fin k) := Setoid.ker f

/-- **The partition-valued step.**  Pushing the mechanism forward through the ancestral
partition gives a genuine law on equivalence relations -- the object the corpus previously
lacked, and the one Kingman's whole theory is about.

Empirical status: NOT AN EMPIRICAL CLAIM.  It is the pushforward of `parentAssignment`
along `ancestralPartition`, and both of those carry that verdict for the same reason: a
kernel of a map is a definition of "common ancestor", not an assertion about one.  What
is empirically at stake is whether a population reproduces by `parentAssignment`, which
`parentAssignment`'s own docstring states and `Descent.Blindness` records the statistics
for. -/
noncomputable def ancestralPartitionLaw (N k : ℕ) [NeZero N] : PMF (Setoid (Fin k)) :=
  (parentAssignment N k).map ancestralPartition

/-- **The law is a pushforward, and that is its whole content.**

`ancestralPartitionLaw` is `parentAssignment` mapped through `ancestralPartition`, so
every probability it assigns is a probability the parent assignment already assigned to
a fibre. Stated because a definition nothing says anything about is a definition nothing
can be wrong about: the empirical claim lives in `parentAssignment`, and this records that
the partition law adds no assumption of its own on top of it. -/
theorem ancestralPartitionLaw_eq_map (N k : ℕ) [NeZero N] :
    ancestralPartitionLaw N k = (parentAssignment N k).map ancestralPartition := rfl

/-- No coalescence in the step means the parent map was injective: `k` lineages, `k`
distinct parents.  This is what makes the counting below a counting of embeddings. -/
theorem ancestralPartition_eq_bot_iff {k N : ℕ} (f : Fin k → Fin N) :
    ancestralPartition f = ⊥ ↔ Function.Injective f := by
  constructor
  · intro h x y hxy
    have hr : (ancestralPartition f).r x y := hxy
    rw [h] at hr
    exact hr
  · intro hf
    refine Setoid.ext fun x y => ⟨fun hxy => hf hxy, fun hxy => ?_⟩
    show f x = f y
    rw [hxy]

/-- The block count of the ancestral partition is the number of distinct parents actually
used.  K-G: each equivalence class of `R_s` corresponds to a member of `G_{r-s}`, but not
conversely. -/
theorem card_quotient_ancestralPartition {k N : ℕ} (f : Fin k → Fin N) :
    Nat.card (Quotient (ancestralPartition f)) = Nat.card (Set.range f) :=
  Nat.card_congr (Setoid.quotientKerEquivRange f)

/-- The genealogy never un-coalesces: composing one more generation of parent choice can
only coarsen the ancestral partition.  K-G (2.6), `R_s ⊆ R_{s+1}`. -/
theorem ancestralPartition_le_comp {k N M : ℕ} (f : Fin k → Fin N) (g : Fin N → Fin M) :
    ancestralPartition f ≤ ancestralPartition (g ∘ f) := by
  intro x y hxy
  show g (f x) = g (f y)
  exact congrArg g hxy

/-! ### Counting the mechanism

Everything from here to the end of the section is a count on the finite space
`Fin k → Fin N`, which carries the uniform law by `parentAssignment_apply`.  The uniform
probability of an event is its cardinality over `N^k`, so the counts ARE the
probabilities. -/

/-- The size of the mechanism's sample space. -/
theorem card_parentMaps (N k : ℕ) : Fintype.card (Fin k → Fin N) = N ^ k := by
  simp

/-- **The count that produces every rate below.**  The number of parent maps under which
no two of the `k` lineages share a parent is the falling factorial `(N)_k`, because such a
map is exactly an embedding of the sample into the previous generation. -/
theorem card_injective_parentMaps (N k : ℕ) :
    Fintype.card {f : Fin k → Fin N // Function.Injective f} = N.descFactorial k := by
  rw [Fintype.card_congr (Equiv.subtypeInjectiveEquivEmbedding (Fin k) (Fin N)),
    Fintype.card_embedding_eq]
  simp

/-- The probability that `k` lineages have `k` distinct parents in one Wright-Fisher
generation.

Empirical status: DERIVED, not posited -- `noCoalescenceProb_eq_card_ratio` identifies it
as the uniform measure of the injectivity event under `parentAssignment`. -/
noncomputable def noCoalescenceProb (N k : ℕ) : ℝ :=
  (N.descFactorial k : ℝ) / (N : ℝ) ^ k

/-- **The mechanism gives the formula.**  `(N)_k / N^k` is the cardinality of the
no-collision event divided by the cardinality of the sample space, which is its probability
under the uniform law `parentAssignment`. -/
theorem noCoalescenceProb_eq_card_ratio (N k : ℕ) :
    noCoalescenceProb N k
      = (Fintype.card {f : Fin k → Fin N // Function.Injective f} : ℝ)
          / (Fintype.card (Fin k → Fin N) : ℝ) := by
  rw [card_injective_parentMaps, card_parentMaps]
  unfold noCoalescenceProb
  push_cast
  ring

@[simp] theorem noCoalescenceProb_zero (N : ℕ) : noCoalescenceProb N 0 = 1 := by
  simp [noCoalescenceProb]

/-- A single lineage cannot collide with anything. -/
theorem noCoalescenceProb_one {N : ℕ} (hN : 0 < N) : noCoalescenceProb N 1 = 1 := by
  have hN' : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  simp [noCoalescenceProb, Nat.descFactorial]
  field_simp

/-- **K-G section 2, exactly: two lineages have the same parent with probability `1/N`.**
Counted off the mechanism -- there are `N(N-1)` ordered pairs of distinct parents among the
`N²` parent maps of a two-lineage sample. -/
theorem noCoalescenceProb_two {N : ℕ} (hN : 0 < N) :
    noCoalescenceProb N 2 = 1 - 1 / (N : ℝ) := by
  have hN' : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hdesc : N.descFactorial 2 = (N - 1) * N := by
    simp [Nat.descFactorial]
  have hcast : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by
    have : (1 : ℕ) ≤ N := hN
    push_cast [Nat.cast_sub this]
    ring
  unfold noCoalescenceProb
  rw [hdesc]
  push_cast [hcast]
  field_simp

/-- The no-collision probability as a product of per-lineage survival factors: the `i`-th
lineage to be placed avoids the `i` parents already used with probability `1 - i/N`. -/
theorem noCoalescenceProb_eq_prod {N k : ℕ} (hN : 0 < N) (hkN : k ≤ N) :
    noCoalescenceProb N k = ∏ i ∈ range k, (1 - (i : ℝ) / (N : ℝ)) := by
  have hN' : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hcast : ∀ i ∈ range k, ((N - i : ℕ) : ℝ) = (N : ℝ) - (i : ℝ) := by
    intro i hi
    have hiN : i ≤ N := le_trans (le_of_lt (mem_range.mp hi)) hkN
    push_cast [Nat.cast_sub hiN]
    ring
  have hstep : ∀ i ∈ range k, ((N : ℝ) - (i : ℝ)) / (N : ℝ) = 1 - (i : ℝ) / (N : ℝ) := by
    intro i _
    field_simp
  calc noCoalescenceProb N k
      = (∏ i ∈ range k, ((N - i : ℕ) : ℝ)) / (N : ℝ) ^ k := by
        unfold noCoalescenceProb
        rw [Nat.descFactorial_eq_prod_range]
        push_cast
        ring
    _ = (∏ i ∈ range k, ((N : ℝ) - (i : ℝ))) / (∏ _i ∈ range k, (N : ℝ)) := by
        rw [prod_const, card_range, prod_congr rfl hcast]
    _ = ∏ i ∈ range k, (((N : ℝ) - (i : ℝ)) / (N : ℝ)) := by
        rw [← prod_div_distrib]
    _ = ∏ i ∈ range k, (1 - (i : ℝ) / (N : ℝ)) := prod_congr rfl hstep

/-! ### From the count to the death rate

The one-generation coalescence probability is `1 - ∏_{i<k}(1 - i/N)`.  Two elementary
product inequalities, proved here by induction, sandwich it between `Σ i/N` and
`Σ i/N - (Σ i/N)²/2`.  Since `Σ_{i<k} i/N = d_k/N`, this is K-G (2.9): the transition
probability is `q_{ξη} N⁻¹ + O(N⁻²)` with `q` the coalescent generator, and the `O(N⁻²)`
is here an explicit `(d_k/N)²/2` rather than an asymptotic gesture. -/

/-- Weierstrass's product inequality, the first Bonferroni bound. -/
theorem one_sub_sum_le_prod {k : ℕ} (a : ℕ → ℝ) (h0 : ∀ i, 0 ≤ a i) (h1 : ∀ i < k, a i ≤ 1) :
    1 - ∑ i ∈ range k, a i ≤ ∏ i ∈ range k, (1 - a i) := by
  induction k with
  | zero => simp
  | succ m ih =>
      have ihm := ih fun i hi => h1 i (by omega)
      have hnn : 0 ≤ ∑ i ∈ range m, a i := sum_nonneg fun i _ => h0 i
      have hfac : (0 : ℝ) ≤ 1 - a m := by linarith [h1 m (by omega)]
      have hmul : (1 - ∑ i ∈ range m, a i) * (1 - a m)
          ≤ (∏ i ∈ range m, (1 - a i)) * (1 - a m) :=
        mul_le_mul_of_nonneg_right ihm hfac
      rw [sum_range_succ, prod_range_succ]
      nlinarith [h0 m, hnn]

/-- The second Bonferroni bound: the product exceeds its linear approximation by at most the
square of the total. -/
theorem prod_le_one_sub_sum_add_sq {k : ℕ} (a : ℕ → ℝ) (h0 : ∀ i, 0 ≤ a i)
    (h1 : ∀ i < k, a i ≤ 1) :
    ∏ i ∈ range k, (1 - a i)
      ≤ 1 - ∑ i ∈ range k, a i + (∑ i ∈ range k, a i) ^ 2 / 2 := by
  induction k with
  | zero => simp
  | succ m ih =>
      have ihm := ih fun i hi => h1 i (by omega)
      have hnn : 0 ≤ ∑ i ∈ range m, a i := sum_nonneg fun i _ => h0 i
      have hfac : (0 : ℝ) ≤ 1 - a m := by linarith [h1 m (by omega)]
      have hmul : (∏ i ∈ range m, (1 - a i)) * (1 - a m)
          ≤ (1 - ∑ i ∈ range m, a i + (∑ i ∈ range m, a i) ^ 2 / 2) * (1 - a m) :=
        mul_le_mul_of_nonneg_right ihm hfac
      rw [sum_range_succ, prod_range_succ]
      nlinarith [h0 m, hnn]

/-- The per-lineage collision probabilities sum to `d_k/N`: this is where `k(k-1)/2` comes
from, and it comes from counting pairs, not from a postulate. -/
theorem sum_range_div_eq_deathRate (N k : ℕ) :
    ∑ i ∈ range k, (i : ℝ) / (N : ℝ) = deathRate k / (N : ℝ) := by
  have hsum : ∑ i ∈ range k, (i : ℝ) = (k : ℝ) * ((k : ℝ) - 1) / 2 := by
    induction k with
    | zero => norm_num
    | succ m ih =>
        rw [sum_range_succ, ih]
        push_cast
        ring
  rw [← sum_div, hsum]
  unfold deathRate Descent.Core.pairCount
  ring

/-- **Upper bound: the one-generation coalescence probability is at most `d_k/N`.**  The
union bound over the `d_k = k(k-1)/2` pairs of lineages, each of which collides with probability `1/N`. -/
theorem coalescenceProb_le {N k : ℕ} (hN : 0 < N) (hkN : k ≤ N) :
    1 - noCoalescenceProb N k ≤ deathRate k / (N : ℝ) := by
  have hN' : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have h0 : ∀ i : ℕ, (0 : ℝ) ≤ (i : ℝ) / (N : ℝ) := fun i => by positivity
  have h1 : ∀ i < k, (i : ℝ) / (N : ℝ) ≤ 1 := by
    intro i hi
    rw [div_le_one hN']
    have : i ≤ N := le_trans (le_of_lt hi) hkN
    exact_mod_cast this
  have := one_sub_sum_le_prod (k := k) (fun i => (i : ℝ) / (N : ℝ)) h0 h1
  rw [noCoalescenceProb_eq_prod hN hkN, sum_range_div_eq_deathRate] at *
  linarith

/-- **Lower bound: and by no more than `(d_k/N)²/2` less.**  Together with `coalescenceProb_le` this is the `q N⁻¹ + O(N⁻²)` of K-G (2.9), with the error constant
exhibited. -/
theorem le_coalescenceProb {N k : ℕ} (hN : 0 < N) (hkN : k ≤ N) :
    deathRate k / (N : ℝ) - (deathRate k / (N : ℝ)) ^ 2 / 2 ≤ 1 - noCoalescenceProb N k := by
  have hN' : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have h0 : ∀ i : ℕ, (0 : ℝ) ≤ (i : ℝ) / (N : ℝ) := fun i => by positivity
  have h1 : ∀ i < k, (i : ℝ) / (N : ℝ) ≤ 1 := by
    intro i hi
    rw [div_le_one hN']
    have : i ≤ N := le_trans (le_of_lt hi) hkN
    exact_mod_cast this
  have := prod_le_one_sub_sum_add_sq (k := k) (fun i => (i : ℝ) / (N : ℝ)) h0 h1
  rw [noCoalescenceProb_eq_prod hN hkN, sum_range_div_eq_deathRate] at *
  linarith

/-- The pair case of the sandwich is exact: `d_2 = 1`, and the collision probability is
`1/N` on the nose.  The `O(N⁻²)` error is genuinely absent at `k = 2`, which is why the
pairwise theory of the corpus was able to get by without a mechanism. -/
theorem coalescenceProb_two {N : ℕ} (hN : 0 < N) :
    1 - noCoalescenceProb N 2 = deathRate 2 / (N : ℝ) := by
  rw [noCoalescenceProb_two hN, deathRate_two]
  ring

/-! ### Iterating the mechanism

One generation is a count.  Many generations need one further premise -- that successive
generations reproduce independently -- and this is the only place it is used.  It enters as
the recursive step of `pairDistinct`, and is flagged there rather than buried. -/

/-- The probability that two sampled lineages still have distinct ancestors `s` generations
back.

Empirical status: MIXED.  The per-step factor is DERIVED (`noCoalescenceProb_two`, counted
off the mechanism); the RECURSION -- multiplying one step's factor by the previous total --
is the Wright-Fisher independence-between-generations assumption of K-G (2.2), and is the
one premise this file does not derive.  The head is `MIXED` because that is the closed-
vocabulary term for a definition whose parts carry different verdicts, and because a head
that opens with lower-case prose is a head no scanner can read: the two halves below are
the two verdicts the term promises.  K-G section 4 is the statement that the conclusion
survives replacing multinomial reproduction by any exchangeable family-size law with bounded moments and variance `σ²`, at the cost of rescaling time by `σ⁻²`. -/
noncomputable def pairDistinct (N : ℕ) : ℕ → ℝ
  | 0 => 1
  | s + 1 => noCoalescenceProb N 2 * pairDistinct N s

/-- **K-G section 2: `(1 - 1/N)^s`.**  "The probability that they have distinct ancestors in
`G_{r-s}` is `(1 - N⁻¹)^s`" -- now with the `1 - N⁻¹` counted rather than asserted. -/
theorem pairDistinct_eq_pow {N : ℕ} (hN : 0 < N) (s : ℕ) :
    pairDistinct N s = (1 - 1 / (N : ℝ)) ^ s := by
  induction s with
  | zero => simp [pairDistinct]
  | succ m ih =>
      rw [pairDistinct, ih, noCoalescenceProb_two hN]
      ring

theorem pairDistinct_nonneg {N : ℕ} (hN : 0 < N) (s : ℕ) : 0 ≤ pairDistinct N s := by
  have hN' : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hfac : (0 : ℝ) ≤ 1 - 1 / (N : ℝ) := by
    have : 1 / (N : ℝ) ≤ 1 := by
      rw [div_le_one (by linarith)]
      exact hN'
    linarith
  rw [pairDistinct_eq_pow hN]
  positivity

theorem pairDistinct_one {N : ℕ} (hN : 0 < N) : pairDistinct N 1 = 1 - 1 / (N : ℝ) := by
  rw [pairDistinct_eq_pow hN]
  ring

/-- **The mean pair-coalescence time is `N` generations.**

The pair coalescence time is geometric with success probability `N⁻¹`, and the expectation
of a `ℕ`-valued waiting time is the sum of its survival probabilities -- which is exactly
`∑_s pairDistinct N s`, no separate probability space required.  The geometric series then
gives `(1 - (1 - N⁻¹))⁻¹ = N`.

This sentence was already in the corpus, as prose attached to `pairDistinct_one`: "the mean
number of generations back to the common ancestor of two lineages is `N`".  Nothing stated
it, so nothing could depend on it, and the `2·Nₑ` that converts coalescent time to
generations was chosen independently in `Program.Conventions` under the name
`coalescentTimeScale`.  Stated, it is what that convention now reads off -- see
`Descent.Program.Conventions.coalescentTimeScale_eq_meanPairCoalescenceTime`. -/
theorem tsum_pairDistinct {N : ℕ} (hN : 0 < N) :
    ∑' s : ℕ, pairDistinct N s = (N : ℝ) := by
  have hpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hinv : (0 : ℝ) < 1 / (N : ℝ) := by positivity
  have hone : 1 / (N : ℝ) ≤ 1 := by
    rw [div_le_one hpos]
    exact_mod_cast hN
  have hnonneg : (0 : ℝ) ≤ 1 - 1 / (N : ℝ) := by linarith
  have hlt : (1 : ℝ) - 1 / (N : ℝ) < 1 := by linarith
  calc ∑' s : ℕ, pairDistinct N s
      = ∑' s : ℕ, (1 - 1 / (N : ℝ)) ^ s := tsum_congr fun s ↦ pairDistinct_eq_pow hN s
    _ = (1 - (1 - 1 / (N : ℝ)))⁻¹ := tsum_geometric_of_lt_one hnonneg hlt
    _ = (N : ℝ) := by
        rw [show (1 : ℝ) - (1 - 1 / (N : ℝ)) = 1 / (N : ℝ) by ring, one_div, inv_inv]

/-- **In a diploid population of `Nₑ` individuals the mean is `2·Nₑ` generations.**

The `2` is the ploidy: `Nₑ` individuals carry `2·Nₑ` gene copies, and it is gene copies
that choose parents.  This is the `2·Nₑ` of `Program.Conventions.coalescentTimeScale`, and
it is NOT the `4·Nₑ` of `θ = 4·Nₑ·μ` -- that one scales a RATE and picks up a further
factor of two from the two lineages that can mutate. -/
theorem tsum_pairDistinct_diploid {Ne : ℕ} (hNe : 0 < Ne) :
    ∑' s : ℕ, pairDistinct (2 * Ne) s = 2 * (Ne : ℝ) := by
  have h2 : 0 < 2 * Ne := by omega
  rw [tsum_pairDistinct h2]
  push_cast
  ring

/-! ### The corpus's drift recurrence, derived

`Descent.PopGen.PopulationGeneticsFoundations.hetRecurrence` posits that heterozygosity
falls by a factor `1 - 1/(2Nₑ)` per generation and solves the recurrence.  The factor is
now a theorem: it is the probability that two gene copies fail to choose the same parent
among the `2Nₑ` gene copies of the previous generation, which is `noCoalescenceProb (2Nₑ) 2`.

This is the concrete form of the general point.  The recurrence was never wrong; it was
unanchored, and an unanchored recurrence cannot say which population it describes.  Anchored,
it says: a haploid population of `2Nₑ` gene copies reproducing by uniform parent choice. -/

/-- **The posited drift factor is the counted parent-collision factor.** -/
theorem hetRecurrence_factor_eq_mechanism {Ne : ℕ} (hNe : 0 < Ne) :
    noCoalescenceProb (2 * Ne) 2 = 1 - 1 / (2 * (Ne : ℝ)) := by
  have h2 : 0 < 2 * Ne := by omega
  rw [noCoalescenceProb_two h2]
  push_cast
  ring

/-- **The corpus's heterozygosity recurrence is the Wright-Fisher pair-survival
probability.**  `Descent.Core.hetRecurrence Nₑ H₀ t = pairDistinct (2 Nₑ) t · H₀`: the scalar model and
the mechanism agree at every generation, and the mechanism is what says why. -/
theorem hetRecurrence_eq_pairDistinct {Ne : ℕ} (hNe : 0 < Ne) (H₀ : ℝ) (t : ℕ) :
    Descent.Core.hetRecurrence (Ne : ℝ) H₀ t = pairDistinct (2 * Ne) t * H₀ := by
  have h2 : 0 < 2 * Ne := by omega
  rw [Descent.Core.hetRecurrence_closed_form, pairDistinct_eq_pow h2]
  push_cast
  ring

/-- The same statement for the heterozygosity-loss scalar: the loss is the probability that
two lineages HAVE met within `t` generations, under the mechanism. -/
theorem heterozygosityLossDerived_eq_pairCoalesced {Ne : ℕ} (hNe : 0 < Ne) (t : ℕ) :
    Descent.Core.heterozygosityLoss (Ne : ℝ) t = 1 - pairDistinct (2 * Ne) t := by
  have h2 : 0 < 2 * Ne := by omega
  unfold Descent.Core.heterozygosityLoss Descent.Core.complement Descent.Core.geometricDecay
  rw [pairDistinct_eq_pow h2]
  push_cast
  ring

/-! ### The mechanism reaching the deployed metric

The chain the corpus is about runs: parents are chosen uniformly, so two lineages collide
with probability `1/N` per generation, so heterozygosity decays, so the between-population
differentiation an analyst measures is what it is, so the polygenic score's `R²` in the
target population is what it is.  Every link but the last was stated somewhere; the last
was not, in this direction, and a chain missing its final link is a chain nothing can be
pulled with.  `Descent.Core.Moments.momentsUnderDrift` is the deployed metric's home, and
it is imported here rather than the reverse because the metric layer sits above the
mechanism -- which is the direction the whole file exists to establish. -/

/-- **The deployed `R²` at the counted differentiation is the deployed `R²` at the corpus's
scalar one.**

`momentsUnderDrift V_A V_E fst |>.r2` is what a polygenic score achieves in a population
differentiated by `fst`.  Feeding it the differentiation COUNTED off the Wright-Fisher
parent choice, rather than the one `Descent.Core.heterozygosityLoss` posits, gives the same
number -- and that is the statement that the deployed metric depends on the mechanism, not
merely on a formula that happens to agree with it.

Before this, no module outside `Descent/Coalescent/` used the coalescent for anything, and
no theorem inside it mentioned a deployed metric: 12,214 lines whose conclusions could not
reach the quantity the development is named for. -/
theorem deployedR2_at_counted_differentiation {Ne : ℕ} (hNe : 0 < Ne) (V_A V_E : ℝ)
    (t : ℕ) :
    (Descent.Core.momentsUnderDrift V_A V_E (1 - pairDistinct (2 * Ne) t)).r2
      = (Descent.Core.momentsUnderDrift V_A V_E
          (Descent.Core.heterozygosityLoss (Ne : ℝ) t)).r2 := by
  rw [heterozygosityLossDerived_eq_pairCoalesced hNe]

/-- **The same for the whole moment record**, not only its `R²`: mean, variance and slope
all read off the counted differentiation. -/
theorem momentsUnderDrift_at_counted_differentiation {Ne : ℕ} (hNe : 0 < Ne)
    (V_A V_E : ℝ) (t : ℕ) :
    Descent.Core.momentsUnderDrift V_A V_E (1 - pairDistinct (2 * Ne) t)
      = Descent.Core.momentsUnderDrift V_A V_E
          (Descent.Core.heterozygosityLoss (Ne : ℝ) t) := by
  rw [heterozygosityLossDerived_eq_pairCoalesced hNe]

end Coalescent

end Descent
