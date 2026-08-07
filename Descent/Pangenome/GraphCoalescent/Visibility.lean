/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.GraphCoalescent.Observation

assert_below Descent.PopGen Descent.Spectral Descent.Blindness Descent.Conditionals
assert_below Descent.Portability Descent.Decision Descent.Program

/-!
# The graph's report of a coalescent is not itself a coalescent

`Descent.Coalescent.Lumping` records Kingman's use of Rosenblatt's criterion, K-G (5.1): a
function `f` of the coalescent is again a Markov chain when

  `Σ_{f(η) = v} q_{ξη}`

depends on `ξ` only through `f(ξ)`.  Applied to `f(R) = |R|` the criterion holds, because
the number of available mergers depends on nothing but the block count, and that is why the
block count is a death process at all.

Applied to a pangenome graph's report `f(R) = observed s R` it FAILS, and this file gives
the exact reason.  The states `⊥` and `graphKer s` produce the same report
(`observed_bot_eq_observed_graphKer`), so lumpability would require them to reach every
report by equally many transitions.  They do not:

* from `graphKer s` every coalescence is visible and no two of them look alike
  (`eq_of_covers_graphKer`), so each report is reached at most once;
* from `⊥` a report is reached TWICE, because the interface has already identified two
  haplotypes and the coalescent has not (`exists_pair_of_covers_bot`).  Coalescing `a` with
  `c` and coalescing `b` with `c` are two events of the coalescent and one event to a graph
  that cannot tell `a` from `b`.

So a graph reporting ancestry at its own resolution reports a process whose next step
depends on how many un-coalesced lineages are hiding behind each node -- which is exactly
the information the graph deleted.  A process whose rates depend on deleted information has
no rates.

## What this does NOT say

It does not say the ancestry is unknowable, and it does not say the graph is wrong.
`Descent.Pangenome.GraphCoalescent.Reduction` shows that the SAME report, entered at
`graphKer s` rather than at `⊥`, is an honest Kingman coalescent -- on `Linkage.width s`
lineages.  What fails here is the naive object: the panel's coalescent read off the graph.
The repair is to stop calling the panel's `n` lineages the graph's.

## Main results

- `ObservablyMarkov`: K-G (5.1) for the report, stated as equinumerosity of the transition
  sets rather than as an equality of counts, so that nothing here needs `𝓔ₙ` to be finite.
- `observablyMarkov_of_injective`: **the witness.**  A faithful interface -- one that merges
  no two panel haplotypes -- satisfies the criterion, because its report is the identity.
- `eq_of_covers_graphKer`: from the graph's own floor, distinct coalescences report
  distinctly.
- `exists_pair_of_covers_bot`: from `⊥` they need not.
- `not_observablyMarkov`: **the theorem.**  One merged pair and one haplotype outside it
  defeat the criterion.
- `not_observablyMarkov_of_width_lt`: the same, in the vocabulary of the width law.
-/

namespace Descent.Pangenome.GraphCoalescent

/-! ### Two lemmas about merging at the bottom

Every construction below merges two singleton classes of `⊥` and then asks what a relation
`ζ` above the merge must contain.  `Coalescent.mergeMap_eq_iff` says a merge identifies the
named pair and nothing else, so `ζ` contains the merge as soon as it relates that pair. -/

/-- **A merge at the bottom is below anything that relates its pair.**  The merge identifies
`x` with `z` and nothing else, so a relation containing that one fact contains the merge. -/
theorem merge_le_of_rel {n : ℕ} {ζ : Coalescent.ER n} {x z : Fin n} (hxz : x ≠ z)
    (h : ζ.r x z) :
    Coalescent.merge (⊥ : Coalescent.ER n) (Quotient.mk ⊥ x) (Quotient.mk ⊥ z) ≤ ζ := by
  have hXZ : Quotient.mk (⊥ : Coalescent.ER n) x ≠ Quotient.mk (⊥ : Coalescent.ER n) z :=
    fun hq ↦ hxz (Quotient.exact hq)
  intro u v huv
  have huv' : Coalescent.mergeMap (⊥ : Coalescent.ER n) (Quotient.mk ⊥ x)
        (Quotient.mk ⊥ z) (Quotient.mk ⊥ u)
      = Coalescent.mergeMap (⊥ : Coalescent.ER n) (Quotient.mk ⊥ x)
        (Quotient.mk ⊥ z) (Quotient.mk ⊥ v) := huv
  rcases (Coalescent.mergeMap_eq_iff (⊥ : Coalescent.ER n) hXZ
    (Quotient.mk ⊥ u) (Quotient.mk ⊥ v)).mp huv' with hh | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have huv : u = v := Quotient.exact hh
    subst huv
    exact ζ.iseqv.refl u
  · have hu : u = x := Quotient.exact h1
    have hv : v = z := Quotient.exact h2
    subst hu
    subst hv
    exact h
  · have hu : u = z := Quotient.exact h1
    have hv : v = x := Quotient.exact h2
    subst hu
    subst hv
    exact ζ.iseqv.symm h

/-- The two-step form: `ζ` relates `x` to `y` and `y` to `z`, so it contains the merge of `x`
with `z`.  This is where the interface's own identification enters -- the first step is a
fact about the graph, the second a fact about the coalescent. -/
theorem merge_le_of_rel_trans {n : ℕ} {ζ : Coalescent.ER n} {x y z : Fin n} (hxz : x ≠ z)
    (h1 : ζ.r x y) (h2 : ζ.r y z) :
    Coalescent.merge (⊥ : Coalescent.ER n) (Quotient.mk ⊥ x) (Quotient.mk ⊥ z) ≤ ζ :=
  merge_le_of_rel hxz (ζ.iseqv.trans h1 h2)

/-! ### Two coalescences, one report -/

/-- Merging `x` with `z` reports no more than merging `y` with `z` does, whenever the
interface has already identified `x` with `y`. -/
theorem observed_merge_le {n : ℕ} {s : Fin n → Fin n} {x y z : Fin n} (hxz : x ≠ z)
    (hxy : s x = s y) :
    observed s (Coalescent.merge (⊥ : Coalescent.ER n) (Quotient.mk ⊥ x) (Quotient.mk ⊥ z))
      ≤ observed s (Coalescent.merge (⊥ : Coalescent.ER n)
        (Quotient.mk ⊥ y) (Quotient.mk ⊥ z)) :=
  observed_le
    (merge_le_of_rel_trans hxz (graphKer_le_observed s _ (graphKer_rel_iff.mpr hxy))
      (le_observed s _ (Coalescent.merge_rel ⊥ (Quotient.mk ⊥ y) (Quotient.mk ⊥ z) rfl rfl)))
    (graphKer_le_observed s _)

/-- **The graph cannot tell the two coalescences apart.**  If the interface merges `x` with
`y`, then the coalescence of `x` with `z` and the coalescence of `y` with `z` have the same
report -- although they are different states of the coalescent. -/
theorem observed_merge_eq {n : ℕ} {s : Fin n → Fin n} {x y z : Fin n} (hxz : x ≠ z)
    (hyz : y ≠ z) (hxy : s x = s y) :
    observed s (Coalescent.merge (⊥ : Coalescent.ER n) (Quotient.mk ⊥ x) (Quotient.mk ⊥ z))
      = observed s (Coalescent.merge (⊥ : Coalescent.ER n)
        (Quotient.mk ⊥ y) (Quotient.mk ⊥ z)) :=
  le_antisymm (observed_merge_le hxz hxy) (observed_merge_le hyz hxy.symm)

/-! ### The criterion

K-G (5.1) is an equality of sums of rates.  Every rate out of a coalescent state is `1` per
pair of blocks, so the sum into a lump is the NUMBER of covers landing in it, and the
criterion says two states with a common report have equally many covers per report.  Stated
as `Nonempty (_ ≃ _)` rather than as an equality of `Nat.card`, it needs no finiteness
hypothesis, and refuting it needs no counting: an equivalence between a type with two
distinct elements and a subsingleton is already impossible. -/

/-- **Rosenblatt's criterion, K-G (5.1), for a pangenome graph's report.**  Two coalescent
states the graph cannot tell apart must offer equally many transitions into each report, or
the report is not a Markov chain.

Empirical status: NOT AN EMPIRICAL CLAIM.  It is a property of the pair `(s, 𝓔ₙ)` decided by
combinatorics, and `observablyMarkov_of_injective` and `not_observablyMarkov` decide it. -/
def ObservablyMarkov {n : ℕ} (s : Fin n → Fin n) : Prop :=
  ∀ ξ ξ' : Coalescent.ER n, observed s ξ = observed s ξ' → ∀ v : Coalescent.ER n,
    Nonempty ({η : Coalescent.ER n // Coalescent.Covers ξ η ∧ observed s η = v} ≃
      {η : Coalescent.ER n // Coalescent.Covers ξ' η ∧ observed s η = v})

/-- **The witness.**  An interface that merges no two panel haplotypes reports the coalescent
itself, so the criterion holds for the trivial reason: states with the same report are the
same state.  By `not_observablyMarkov_of_width_lt` this is essentially the only case, and it
is the case in which the graph has compressed nothing. -/
theorem observablyMarkov_of_injective {n : ℕ} {s : Fin n → Fin n}
    (hs : Function.Injective s) : ObservablyMarkov s := by
  intro ξ ξ' h v
  rw [observed_eq_of_injective hs ξ, observed_eq_of_injective hs ξ'] at h
  subst h
  exact ⟨Equiv.refl _⟩

/-- **At or above the graph's own merge, the report is a faithful record.**  Two covers of
`graphKer s` with the same report are the same cover, so each report is reached at most once
and the transition set out of `graphKer s` is a subsingleton per report. -/
theorem eq_of_covers_graphKer {n : ℕ} {s : Fin n → Fin n} {η η' : Coalescent.ER n}
    (h : Coalescent.Covers (graphKer s) η) (h' : Coalescent.Covers (graphKer s) η')
    (hobs : observed s η = observed s η') : η = η' := by
  rwa [observed_of_le h.1, observed_of_le h'.1] at hobs

/-- **Two coalescences, one report.**  Given a pair the interface has merged and a third
haplotype outside their state, the coalescent has two distinct covers of `⊥` that the graph
reports identically.  Nothing about pangenomes is used beyond `s a = s b`, which is what an
interface of width less than `n` is. -/
theorem exists_pair_of_covers_bot {n : ℕ} {s : Fin n → Fin n} {a b c : Fin n}
    (hab : a ≠ b) (hsab : s a = s b) (hc : s c ≠ s a) :
    ∃ η η' : Coalescent.ER n, η ≠ η' ∧ Coalescent.Covers ⊥ η ∧
      Coalescent.Covers ⊥ η' ∧ observed s η = observed s η' := by
  have hne_ac : a ≠ c := fun h ↦ hc (by rw [← h])
  have hne_bc : b ≠ c := fun h ↦ hc (by rw [← h, ← hsab])
  have hAC : Quotient.mk (⊥ : Coalescent.ER n) a ≠ Quotient.mk (⊥ : Coalescent.ER n) c :=
    fun h ↦ hne_ac (Quotient.exact h)
  have hBC : Quotient.mk (⊥ : Coalescent.ER n) b ≠ Quotient.mk (⊥ : Coalescent.ER n) c :=
    fun h ↦ hne_bc (Quotient.exact h)
  refine ⟨Coalescent.merge ⊥ (Quotient.mk ⊥ a) (Quotient.mk ⊥ c),
    Coalescent.merge ⊥ (Quotient.mk ⊥ b) (Quotient.mk ⊥ c), ?_,
    Coalescent.merge_covers ⊥ hAC, Coalescent.merge_covers ⊥ hBC,
    observed_merge_eq hne_ac hne_bc hsab⟩
  intro heq
  have hrel : (Coalescent.merge (⊥ : Coalescent.ER n)
      (Quotient.mk ⊥ a) (Quotient.mk ⊥ c)).r a c :=
    Coalescent.merge_rel ⊥ (Quotient.mk ⊥ a) (Quotient.mk ⊥ c) rfl rfl
  rw [heq] at hrel
  have hrel' : Coalescent.mergeMap (⊥ : Coalescent.ER n) (Quotient.mk ⊥ b)
        (Quotient.mk ⊥ c) (Quotient.mk ⊥ a)
      = Coalescent.mergeMap (⊥ : Coalescent.ER n) (Quotient.mk ⊥ b)
        (Quotient.mk ⊥ c) (Quotient.mk ⊥ c) := hrel
  rcases (Coalescent.mergeMap_eq_iff (⊥ : Coalescent.ER n) hBC
    (Quotient.mk ⊥ a) (Quotient.mk ⊥ c)).mp hrel' with h | ⟨h, -⟩ | ⟨h, -⟩
  · exact hAC h
  · exact hab (Quotient.exact h)
  · exact hAC h

/-! ### The theorem -/

/-- **A pangenome graph's report of the coalescent is not a Markov chain.**  One pair of
haplotypes merged by the interface, and one haplotype outside their state, already defeat
Rosenblatt's criterion: `⊥` and `graphKer s` have the same report, but `⊥` reaches a report
by two distinct coalescences and `graphKer s` reaches it by at most one.

The two states differ in how many un-coalesced lineages hide behind a node, and that number
is precisely what the interface deleted.  The obstruction is therefore not an artefact of
the encoding: it is the width law of `Descent.Pangenome.Linkage.Barrier` showing up as a
failure of the Markov property rather than as a count of phantom derivations. -/
theorem not_observablyMarkov {n : ℕ} {s : Fin n → Fin n} {a b c : Fin n} (hab : a ≠ b)
    (hsab : s a = s b) (hc : s c ≠ s a) : ¬ ObservablyMarkov s := by
  intro hM
  obtain ⟨η, η', hne, hcov, hcov', hobs⟩ := exists_pair_of_covers_bot hab hsab hc
  obtain ⟨e⟩ := hM ⊥ (graphKer s) (observed_bot_eq_observed_graphKer s) (observed s η)
  have h1 : Coalescent.Covers ⊥ η ∧ observed s η = observed s η := ⟨hcov, rfl⟩
  have h2 : Coalescent.Covers ⊥ η' ∧ observed s η' = observed s η := ⟨hcov', hobs.symm⟩
  have hsub : ∀ x y : {ζ : Coalescent.ER n //
      Coalescent.Covers (graphKer s) ζ ∧ observed s ζ = observed s η}, x = y := by
    rintro ⟨x, hx1, hx2⟩ ⟨y, hy1, hy2⟩
    exact Subtype.ext (eq_of_covers_graphKer hx1 hy1 (hx2.trans hy2.symm))
  have hmap : e ⟨η, h1⟩ = e ⟨η', h2⟩ := hsub _ _
  exact hne (congrArg Subtype.val (e.injective hmap))

/-! ### The same, in the vocabulary of the width law

`Descent.Pangenome.Linkage.Interface` measures an interface by its occupied `width`.  An
interface of width `n` is faithful and satisfies the criterion; an interface of width less
than `n` has merged something, and if it occupies at least two states there is a haplotype
outside the merged one.  The criterion therefore partitions interfaces at exactly the place
the width law charges them. -/

/-- An interface occupying at least two states and fewer than `n` of them supplies the
witness `not_observablyMarkov` needs: a merged pair, and a haplotype outside it. -/
theorem exists_witness_of_width {n : ℕ} {s : Fin n → Fin n} (hw : 2 ≤ Linkage.width s)
    (hlt : Linkage.width s < n) : ∃ a b c : Fin n, a ≠ b ∧ s a = s b ∧ s c ≠ s a := by
  have hninj : ¬ Function.Injective s := by
    intro hinj
    have hcard : Linkage.width s = n := by
      have h := Finset.card_image_of_injective (Finset.univ : Finset (Fin n)) hinj
      simpa [Linkage.width, Finset.card_univ] using h
    omega
  obtain ⟨a, b, hsab, hab⟩ : ∃ a b : Fin n, s a = s b ∧ a ≠ b := by
    by_contra hcon
    push_neg at hcon
    exact hninj fun x y hxy ↦ hcon x y hxy
  have h1 : 1 < (Finset.univ.image s).card := by
    simpa [Linkage.width] using hw
  obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp h1
  by_cases hxa : x = s a
  · obtain ⟨c, -, hcy⟩ := Finset.mem_image.mp hy
    refine ⟨a, b, c, hab, hsab, ?_⟩
    rw [hcy, ← hxa]
    exact Ne.symm hxy
  · obtain ⟨c, -, hcx⟩ := Finset.mem_image.mp hx
    refine ⟨a, b, c, hab, hsab, ?_⟩
    rw [hcx]
    exact hxa

/-- **The width law's threshold is the Markov property's threshold.**  Any interface that
occupies at least two graph states and fewer than `n` of them -- that is, any interface that
compressed the panel at all and did not collapse it to a point -- reports a process with no
transition rates. -/
theorem not_observablyMarkov_of_width_lt {n : ℕ} {s : Fin n → Fin n}
    (hw : 2 ≤ Linkage.width s) (hlt : Linkage.width s < n) : ¬ ObservablyMarkov s := by
  obtain ⟨a, b, c, hab, hsab, hc⟩ := exists_witness_of_width hw hlt
  exact not_observablyMarkov hab hsab hc

end Descent.Pangenome.GraphCoalescent
