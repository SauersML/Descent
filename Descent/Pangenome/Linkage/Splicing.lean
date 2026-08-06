/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.Linkage.Barrier
import Descent.Pangenome.GaugeInvariance

assert_below Descent.PopGen Descent.Spectral Descent.Blindness Descent.Conditionals Descent.Portability Descent.Decision Descent.Program

/-!
# From donor histories to sequences and walks

`Descent.Pangenome.Linkage.Barrier` counts DERIVATIONS: which donor supplies which module.
A graph does not spell donor labels, it spells sequence, and two derivations can spell one
word when the donors they name contribute the same block.  This file supplies the hypothesis
under which that cannot happen, and then says what the barrier becomes.

## Spelling

`spell code x` concatenates the block each donor of `x` contributes.  What makes that
concatenation parseable is `PrefixFree`: no donor's block begins another's.  Under it,
`spell_injOn_of_prefixFree` gives unique decodability with NO hypothesis on lengths, so
distinct derivations spell distinct words and every count of
`Descent.Pangenome.Linkage.Chain` transfers verbatim to distinct sequences:
`card_spelledWords`, and with it `pow_card_le_prod_width_mul_card_spelledWords`.

Prefix-freeness rather than one fixed length is the hypothesis a pangenome can actually
meet.  Segments between consecutive separators differ in length wherever the panel carries
an indel, and prefix-free parsing is already the standard preprocessing applied to a
haplotype collection before an index is built over it.  `prefixFree_of_length` shows fixed
length is a special case; `combCode` — donor `i` contributing `A^i C` — is prefix-free with
`i + 1` distinct lengths, so the weakening is strict and not a restatement.

When blocks do NOT identify their donor the correction is bounded rather than fatal:
`card_mosaics_le_pow_mul_card_spelledWords` says at most `μ` donors per block leaves at most
`μ ^ (r+1)` derivations behind any one word, so segment ambiguity divides the derivation
count instead of destroying it, and exponential inflation in distinct sequences survives
whenever the forgotten linkage outruns the ambiguity.

`snpCode` shows the hypothesis is not a strong one.  Over two DNA letters, with each donor's
block the all-`A` reference carrying a single `C` at that donor's own coordinate — a
biallelic SNP and nothing else — the blocks are distinct and equally long.  So the width law
is attained as a count of distinct DNA words by a panel whose only variation is one marker
per block: `card_spelledWords_snpCode_of_balanced`.

## Walks

`spliceWalk` sends a derivation to the walk that traverses each donor's segment in turn, in
the traversal-count representation of `Descent.Pangenome.Gauge`.  `sum_weighted_spliceWalk`
says a mosaic's weighted holonomy is the sum of its donors' — so a phantom path's sequence
length is bookkeeping over the donors that spliced it.  Weighted holonomy is one of the
functionals `Descent.Pangenome.Gauge.gaugeInvariant_of_treeFree` certifies, which is the
point of stating the bridge in that vocabulary: the quantity the linkage law forces to
exist survives a change of reference tree, so the phantoms are not an artifact of how the
catalogue was written down.

## What is proved and what is assumed

The equality construction of the manuscript builds a layered graph whose paths are exactly
the compatible splices.  What is formalised here is the counting half of that: given blocks
that identify their donor, the compatible splices number exactly `|Ω|` and spell exactly
`|Ω|` distinct words.  No graph is constructed, and no claim is made here that a particular
graph realises a particular block system.

## Empirical status

None.  The results are statements about concatenating lists and adding traversal counts.
`snpCode` and `combCode` are constructions, not models of any locus: they exhibit block
systems meeting the decodability hypothesis — one at fixed length, one not — and assert
nothing about how often real panels meet it.
-/

namespace Descent.Pangenome.Linkage

open Finset

universe u v

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

/-! ### Spelling a derivation -/

section Spelling

variable {α : Type v}

omit [Fintype ι] [DecidableEq ι] in
/-- The word a derivation spells: each module contributes its donor's block. -/
def spell (code : ι → List α) (x : List ι) : List α := (x.map code).flatten

omit [Fintype ι] [DecidableEq ι] in
theorem spell_nil (code : ι → List α) : spell code ([] : List ι) = [] := rfl

omit [Fintype ι] [DecidableEq ι] in
theorem spell_cons (code : ι → List α) (h : ι) (x : List ι) :
    spell code (h :: x) = code h ++ spell code x := rfl

/-! ### Prefix-free blocks are uniquely decodable

Blocks of one fixed length are decodable, and are not what a pangenome has: the segments
between consecutive separators differ in length whenever the panel carries an indel.  What
actually makes a concatenation parseable is the classical prefix-code condition — no block
begins another block — which is also the condition prefix-free parsing imposes on a
haplotype collection before an index is built over it.  Everything below is stated on that
hypothesis, and the fixed-length case enters through `prefixFree_of_length`. -/

omit [Fintype ι] [DecidableEq ι] in
/-- A block system is PREFIX-FREE when no donor's block begins another donor's block. -/
def PrefixFree (code : ι → List α) : Prop := ∀ g h : ι, g ≠ h → ¬ code g <+: code h

omit [Fintype ι] [DecidableEq ι] in
/-- **Distinct blocks of one length are prefix-free.**  So the hypothesis used below is
weaker than the fixed-length one, and `combCode` shows it is strictly weaker. -/
theorem prefixFree_of_length (code : ι → List α) (L : ℕ) (hlen : ∀ h, (code h).length = L)
    (hinj : Function.Injective code) : PrefixFree code := by
  intro g h hgh hpre
  exact hgh (hinj (hpre.sublist.eq_of_length (by rw [hlen, hlen])))

omit [Fintype ι] [DecidableEq ι] in
/-- **Prefix-free blocks are uniquely decodable.**  Two blocks that both begin one word are
comparable, so prefix-freeness pins the first donor, and the rest follows by induction.  No
length hypothesis is used, which is the point: variable-length segments are decodable too. -/
theorem spell_injOn_of_prefixFree (code : ι → List α) (hpf : PrefixFree code) :
    ∀ x y : List ι, x.length = y.length → spell code x = spell code y → x = y := by
  intro x
  induction x with
  | nil =>
    intro y hxy _
    cases y with
    | nil => rfl
    | cons b y => simp at hxy
  | cons a x ih =>
    intro y hxy hsp
    cases y with
    | nil => simp at hxy
    | cons b y =>
      rw [spell_cons, spell_cons] at hsp
      have hab : a = b := by
        by_contra hne
        have h1 : code a <+: code b ++ spell code y := by
          rw [← hsp]
          exact List.prefix_append _ _
        rcases List.prefix_or_prefix_of_prefix h1
          (List.prefix_append (code b) (spell code y)) with hc | hc
        · exact hpf a b hne hc
        · exact hpf b a (Ne.symm hne) hc
      subst hab
      have htail : spell code x = spell code y := List.append_cancel_left hsp
      have hxy' : x.length = y.length := by simpa using hxy
      rw [ih y hxy' htail]

variable [DecidableEq α]

/-- The distinct words the compatible language spells. -/
def spelledWords (code : ι → List α) (c : Chain ι) : Finset (List α) :=
  (mosaics c).image (spell code)

/-- The words the panel itself spells. -/
def panelWords (code : ι → List α) (c : Chain ι) : Finset (List α) :=
  (diagonals c).image (spell code)

/-- The words the topology spells that the panel does not contain. -/
def phantomWords (code : ι → List α) (c : Chain ι) : Finset (List α) :=
  spelledWords code c \ panelWords code c

/-- **Donor-identifying blocks lose nothing.**  With uniquely decodable blocks the number of
distinct spelled words is the number of derivations. -/
theorem card_spelledWords (code : ι → List α) (hpf : PrefixFree code) (c : Chain ι) :
    (spelledWords code c).card = (mosaics c).card := by
  refine Finset.card_image_of_injOn fun x hx y hy hxy ↦ ?_
  exact spell_injOn_of_prefixFree code hpf x y
    (by rw [length_of_mem_mosaics hx, length_of_mem_mosaics hy]) hxy

theorem card_panelWords (code : ι → List α) (hpf : PrefixFree code) (c : Chain ι) :
    (panelWords code c).card = Fintype.card ι := by
  rw [panelWords, Finset.card_image_of_injOn, card_diagonals]
  intro x hx y hy hxy
  exact spell_injOn_of_prefixFree code hpf x y
    (by rw [length_of_mem_mosaics (diagonals_subset c hx),
      length_of_mem_mosaics (diagonals_subset c hy)]) hxy

theorem panelWords_subset (code : ι → List α) (c : Chain ι) :
    panelWords code c ⊆ spelledWords code c :=
  Finset.image_subset_image (diagonals_subset c)

/-- **The phantom word count.**  Everything the topology spells beyond the panel. -/
theorem card_phantomWords (code : ι → List α) (hpf : PrefixFree code) (c : Chain ι) :
    (phantomWords code c).card = (mosaics c).card - Fintype.card ι := by
  have hin : panelWords code c ∩ spelledWords code c = panelWords code c :=
    Finset.inter_eq_left.mpr (panelWords_subset code c)
  rw [phantomWords, Finset.card_sdiff, hin, card_spelledWords code hpf c,
    card_panelWords code hpf c]

/-! ### When blocks do not identify their donor

Injectivity is the clean case.  When a block is contributed by several donors, distinct
derivations can spell one word and the derivation count overstates the sequence count.  The
correction is bounded rather than unbounded: at most `μ` donors per block means at most `μ`
choices per module, so a word has at most `μ ^ (r+1)` derivations behind it. -/

/-- With every block of one length and at most `μ` donors carrying any one block, the
derivations spelling a given word number at most `μ ^ (r+1)`, whatever set of first donors
they are drawn from. -/
theorem sum_ite_spell_le (code : ι → List α) (L μ : ℕ) (hlen : ∀ h, (code h).length = L)
    (hμ : ∀ b : List α, (Finset.univ.filter fun g ↦ code g = b).card ≤ μ) :
    ∀ (c : Chain ι) (y : List α) (S : Finset ι),
      ∑ h ∈ S, ∑ x ∈ mosaicsFrom c h, (if spell code x = y then 1 else 0)
        ≤ μ ^ (c.length + 1) := by
  intro c
  induction c with
  | nil =>
    intro y S
    have hone : ∀ h : ι,
        ∑ x ∈ mosaicsFrom ([] : Chain ι) h, (if spell code x = y then 1 else 0)
          = if code h = y then 1 else 0 := by
      intro h
      have hsp : spell code [h] = code h := by simp [spell]
      rw [show mosaicsFrom ([] : Chain ι) h = {[h]} from rfl, Finset.sum_singleton, hsp]
    rw [Finset.sum_congr rfl fun h _ ↦ hone h, ← Finset.card_filter]
    calc (S.filter fun h ↦ code h = y).card
        ≤ (Finset.univ.filter fun h ↦ code h = y).card :=
          Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ S))
      _ ≤ μ := hμ y
      _ = μ ^ (([] : Chain ι).length + 1) := by simp
  | cons s c ih =>
    intro y S
    have htake : ∀ u v : List α, (u ++ v).take u.length = u := by
      intro u v
      induction u with
      | nil => rfl
      | cons a u ihu => simp [ihu]
    have hrw : ∀ h : ι,
        ∑ x ∈ mosaicsFrom (s :: c) h, (if spell code x = y then 1 else 0)
          = ∑ g ∈ fiber s h, ∑ z ∈ mosaicsFrom c g,
              (if code h ++ spell code z = y then 1 else 0) := by
      intro h
      rw [sum_mosaicsFrom]
      exact Finset.sum_congr rfl fun g _ ↦ Finset.sum_congr rfl fun z _ ↦ by rw [spell_cons]
    rw [Finset.sum_congr rfl fun h _ ↦ hrw h]
    have hvanish : ∀ h ∈ S, h ∉ S.filter (fun h ↦ code h = y.take L) →
        ∑ g ∈ fiber s h, ∑ z ∈ mosaicsFrom c g,
          (if code h ++ spell code z = y then 1 else 0) = 0 := by
      intro h hS hnot
      refine Finset.sum_eq_zero fun g _ ↦ Finset.sum_eq_zero fun z _ ↦ ?_
      by_cases hy : code h ++ spell code z = y
      · exact absurd (Finset.mem_filter.mpr ⟨hS, by rw [← hy, ← hlen h, htake]⟩) hnot
      · simp [hy]
    rw [← Finset.sum_subset (Finset.filter_subset _ S) hvanish]
    have hbound : ∀ h ∈ S.filter (fun h ↦ code h = y.take L),
        ∑ g ∈ fiber s h, ∑ z ∈ mosaicsFrom c g,
          (if code h ++ spell code z = y then 1 else 0) ≤ μ ^ (c.length + 1) := by
      intro h _
      by_cases hpre : ∃ y' : List α, y = code h ++ y'
      · obtain ⟨y', rfl⟩ := hpre
        have hcancel : ∀ g ∈ fiber s h, ∑ z ∈ mosaicsFrom c g,
            (if code h ++ spell code z = code h ++ y' then 1 else 0)
            = ∑ z ∈ mosaicsFrom c g, (if spell code z = y' then 1 else 0) := by
          intro g _
          refine Finset.sum_congr rfl fun z _ ↦ ?_
          by_cases hz : spell code z = y'
          · simp [hz]
          · have hne : ¬(code h ++ spell code z = code h ++ y') := fun hc ↦
              hz (List.append_cancel_left hc)
            simp [hne, hz]
        rw [Finset.sum_congr rfl hcancel]
        exact ih y' (fiber s h)
      · push_neg at hpre
        refine le_of_eq_of_le
          (Finset.sum_eq_zero fun g _ ↦ Finset.sum_eq_zero fun z _ ↦ ?_) (Nat.zero_le _)
        have hne : ¬(code h ++ spell code z = y) := fun hc ↦ hpre (spell code z) hc.symm
        simp [hne]
    calc ∑ h ∈ S.filter (fun h ↦ code h = y.take L),
          ∑ g ∈ fiber s h, ∑ z ∈ mosaicsFrom c g,
            (if code h ++ spell code z = y then 1 else 0)
        ≤ ∑ _h ∈ S.filter (fun h ↦ code h = y.take L), μ ^ (c.length + 1) :=
          Finset.sum_le_sum hbound
      _ = (S.filter (fun h ↦ code h = y.take L)).card * μ ^ (c.length + 1) := by
          rw [Finset.sum_const, smul_eq_mul]
      _ ≤ μ * μ ^ (c.length + 1) :=
          Nat.mul_le_mul_right _ (le_trans (Finset.card_le_card
            (Finset.filter_subset_filter _ (Finset.subset_univ S))) (hμ _))
      _ = μ ^ ((s :: c).length + 1) := by rw [List.length_cons]; ring

/-- A spelled word has at most `μ ^ (r+1)` derivations behind it. -/
theorem card_filter_spell_le (code : ι → List α) (L μ : ℕ) (hlen : ∀ h, (code h).length = L)
    (hμ : ∀ b : List α, (Finset.univ.filter fun g ↦ code g = b).card ≤ μ) (c : Chain ι)
    (y : List α) :
    ((mosaics c).filter fun x ↦ spell code x = y).card ≤ μ ^ (c.length + 1) := by
  rw [Finset.card_filter, sum_mosaics]
  exact sum_ite_spell_le code L μ hlen hμ c y Finset.univ

/-- **The collision-corrected count.**  Segment ambiguity divides the derivation count rather
than destroying it: with at most `μ` donors per block, the distinct-word count is at least
`|Ω| / μ ^ (r+1)`, stated without division.  Exponential inflation in distinct sequences is
therefore guaranteed whenever the linkage the interfaces forget outruns the ambiguity the
blocks introduce. -/
theorem card_mosaics_le_pow_mul_card_spelledWords (code : ι → List α) (L μ : ℕ)
    (hlen : ∀ h, (code h).length = L)
    (hμ : ∀ b : List α, (Finset.univ.filter fun g ↦ code g = b).card ≤ μ) (c : Chain ι) :
    (mosaics c).card ≤ μ ^ (c.length + 1) * (spelledWords code c).card :=
  Finset.card_le_mul_card_image _ _ fun y _ ↦ card_filter_spell_le code L μ hlen hμ c y

/-- **The width law, counted in distinct sequences.** -/
theorem pow_card_le_prod_width_mul_card_spelledWords [Nonempty ι] (code : ι → List α)
    (hpf : PrefixFree code) (c : Chain ι) :
    Fintype.card ι ^ (c.length + 1) ≤ (c.map width).prod * (spelledWords code c).card := by
  rw [card_spelledWords code hpf c]
  exact pow_card_le_prod_width_mul_card_mosaics c

/-- **The exactness barrier, in distinct sequences.**  If the topology spells exactly the
`m` panel words and no more, then with donor-identifying blocks every interface keeps all `m`
thread identities in distinct states.  This is the barrier of
`Descent.Pangenome.Linkage.Barrier.width_eq_card_of_card_mosaics_eq` stated where a graph
builder can check it: on the sequences the graph spells, not on donor histories. -/
theorem width_eq_card_of_card_spelledWords_eq [Nonempty ι] (code : ι → List α)
    (hpf : PrefixFree code) {c : Chain ι}
    (hex : (spelledWords code c).card = Fintype.card ι) :
    ∀ s ∈ c, width s = Fintype.card ι := by
  refine width_eq_card_of_card_mosaics_eq ?_
  rw [← card_spelledWords code hpf c]
  exact hex

end Spelling

/-! ### A biallelic single-SNP block system

The decodability hypothesis is cheap.  Two letters and one marker per block meet it, so the
lower bound is not an artifact of rich blocks that happen to name their donor. -/

omit [Fintype ι] [DecidableEq ι] in
/-- A list of single-marker words determines its marker, wherever the marker is in range. -/
theorem eq_of_map_ite_eq {β : Type u} {γ : Type v} [DecidableEq β] {u v : γ} (huv : u ≠ v)
    {h₁ h₂ : β} (l : List β) (hmem : h₁ ∈ l)
    (hEq : (l.map fun g ↦ if g = h₁ then u else v)
      = l.map fun g ↦ if g = h₂ then u else v) : h₁ = h₂ := by
  induction l with
  | nil => cases hmem
  | cons a t ih =>
    rw [List.map_cons, List.map_cons] at hEq
    injection hEq with hhead htail
    rcases List.mem_cons.mp hmem with rfl | hmt
    · by_contra hne
      rw [if_pos rfl, if_neg hne] at hhead
      exact huv hhead
    · exact ih hmt htail

/-- The block donor `h` contributes: the all-`A` reference word carrying a single `C` at
`h`'s own coordinate.  One biallelic SNP per block, and nothing else. -/
noncomputable def snpCode (h : ι) : List Allele :=
  (Finset.univ : Finset ι).toList.map fun g ↦ if g = h then Allele.C else Allele.A

theorem length_snpCode (h : ι) : (snpCode h).length = Fintype.card ι := by
  simp [snpCode, Finset.length_toList, Finset.card_univ]

theorem snpCode_injective : Function.Injective (snpCode (ι := ι)) := by
  intro h₁ h₂ hEq
  exact eq_of_map_ite_eq (by simp) (Finset.univ : Finset ι).toList
    (Finset.mem_toList.mpr (Finset.mem_univ h₁)) hEq

theorem snpCode_prefixFree : PrefixFree (snpCode (ι := ι)) :=
  prefixFree_of_length snpCode (Fintype.card ι) length_snpCode snpCode_injective

/-- A block system of VARIABLE length: donor `i` contributes `A^i C`.  This is the unary comb
code, the smallest witness that prefix-freeness is strictly weaker than fixed length — the
blocks have `i + 1` distinct lengths, so no fixed-length hypothesis reaches them, and
`combCode_prefixFree` shows the decodability results here do. -/
def combCode (n : ℕ) (i : Fin n) : List Allele :=
  List.replicate i.val Allele.A ++ [Allele.C]

theorem length_combCode (n : ℕ) (i : Fin n) : (combCode n i).length = i.val + 1 := by
  simp [combCode]

/-- **The comb code is prefix-free.**  A shorter comb word puts its `C` where a longer one
still has an `A`, so neither begins the other. -/
theorem combCode_prefixFree (n : ℕ) : PrefixFree (combCode n) := by
  intro g h hgh hpre
  obtain ⟨t, ht⟩ := hpre
  have hle : g.val ≤ h.val := by
    have hlen := congrArg List.length ht
    simp [combCode] at hlen
    omega
  have hne : g.val ≠ h.val := fun hv ↦ hgh (Fin.ext hv)
  have hlt : g.val < h.val := lt_of_le_of_ne hle hne
  obtain ⟨d, hd⟩ : ∃ d, h.val = g.val + (d + 1) := ⟨h.val - g.val - 1, by omega⟩
  rw [combCode, combCode, hd, List.replicate_add, List.append_assoc,
    List.append_assoc] at ht
  have htail := List.append_cancel_left ht
  rw [List.replicate_succ, List.cons_append] at htail
  injection htail with hhead _
  exact Allele.noConfusion hhead

/-- **The width law is attained as a count of distinct DNA words.**  A balanced chain over
biallelic single-SNP blocks spells exactly `m · ∏ b_j` distinct words, which is the value the
width bound of `Descent.Pangenome.Linkage.Barrier` gives.  So no sharper bound holds, and the
extremal example needs nothing richer than one marker per block. -/
theorem card_spelledWords_snpCode_of_balanced {c : Chain ι} {bs : List ℕ}
    (hb : Balanced c bs) :
    (spelledWords snpCode c).card = Fintype.card ι * bs.prod := by
  rw [card_spelledWords snpCode snpCode_prefixFree c, card_mosaics_of_balanced hb]

/-- And all but the `m` panel words are words the panel never contained. -/
theorem card_phantomWords_snpCode_of_balanced {c : Chain ι} {bs : List ℕ}
    (hb : Balanced c bs) :
    (phantomWords snpCode c).card = Fintype.card ι * bs.prod - Fintype.card ι := by
  rw [card_phantomWords snpCode snpCode_prefixFree c, card_mosaics_of_balanced hb]

/-! ### Splicing donor segments into a walk -/

section Walks

variable {E : Type v}

omit [Fintype ι] [DecidableEq ι] in
theorem gaugeSum_zero (edges : List E) : Gauge.sum (fun _ ↦ 0) edges = 0 := by
  induction edges with
  | nil => rfl
  | cons e es ih => simp [Gauge.sum, ih]

omit [Fintype ι] [DecidableEq ι] in
theorem gaugeSum_add (f g : E → ℕ) (edges : List E) :
    Gauge.sum (fun e ↦ f e + g e) edges = Gauge.sum f edges + Gauge.sum g edges := by
  induction edges with
  | nil => rfl
  | cons e es ih =>
    simp only [Gauge.sum, ih]
    omega

/-- The walk a derivation traverses: each module contributes its donor's segment, and
traversal counts add.  This is the walk-level datum of `Descent.Pangenome.Gauge`, which
mentions no reference tree. -/
def spliceWalk (seg : ι → Gauge.Walk E) (x : List ι) : Gauge.Walk E :=
  fun e ↦ (x.map fun h ↦ seg h e).sum

omit [Fintype ι] [DecidableEq ι] in
theorem spliceWalk_cons (seg : ι → Gauge.Walk E) (h : ι) (x : List ι) :
    spliceWalk seg (h :: x) = fun e ↦ seg h e + spliceWalk seg x e := rfl

omit [Fintype ι] [DecidableEq ι] in
/-- **A mosaic's weighted holonomy is the sum of its donors' holonomies.**  With `ℓ` the
allele length this says the sequence length of a spliced path is the total length of the
blocks that spliced it — and weighted holonomy is gauge-invariant, so this is a statement
about the graph rather than about the reference tree a catalogue was written against. -/
theorem sum_weighted_spliceWalk (edges : List E) (ℓ : E → ℕ) (seg : ι → Gauge.Walk E)
    (x : List ι) :
    Gauge.sum (fun e ↦ ℓ e * spliceWalk seg x e) edges
      = (x.map fun h ↦ Gauge.sum (fun e ↦ ℓ e * seg h e) edges).sum := by
  induction x with
  | nil =>
    have hfun : (fun e ↦ ℓ e * spliceWalk seg ([] : List ι) e) = fun _ : E ↦ 0 := by
      funext e
      simp [spliceWalk]
    rw [hfun, gaugeSum_zero]
    simp
  | cons h x ih =>
    have hfun : (fun e ↦ ℓ e * spliceWalk seg (h :: x) e)
        = fun e ↦ ℓ e * seg h e + ℓ e * spliceWalk seg x e := by
      funext e
      rw [spliceWalk_cons, Nat.mul_add]
    rw [hfun, gaugeSum_add, ih, List.map_cons, List.sum_cons]

end Walks

end Descent.Pangenome.Linkage
