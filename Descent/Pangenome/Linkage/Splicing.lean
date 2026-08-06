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

`spell code x` concatenates the block each donor of `x` contributes.  When the blocks are
distinct and all of one length, `spell_injOn` makes the concatenation uniquely decodable, so
distinct derivations spell distinct words and every count of
`Descent.Pangenome.Linkage.Chain` transfers verbatim to distinct sequences:
`card_spelledWords`, and with it `pow_card_le_prod_width_mul_card_spelledWords`.

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
`snpCode` is a construction, not a model of any locus: it exhibits a block system meeting
the decodability hypothesis, and asserts nothing about how often real panels meet it.
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

omit [Fintype ι] [DecidableEq ι] in
/-- **Fixed-length blocks are uniquely decodable.**  Distinct donors contributing distinct
blocks of one length means a spelled word determines the derivation that spelled it. -/
theorem spell_injOn (code : ι → List α) (L : ℕ) (hlen : ∀ h, (code h).length = L)
    (hinj : Function.Injective code) :
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
      have hL : (code a).length = (code b).length := by rw [hlen, hlen]
      obtain ⟨hhead, htail⟩ := List.append_inj hsp hL
      have hab : a = b := hinj hhead
      subst hab
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
theorem card_spelledWords (code : ι → List α) (L : ℕ) (hlen : ∀ h, (code h).length = L)
    (hinj : Function.Injective code) (c : Chain ι) :
    (spelledWords code c).card = (mosaics c).card := by
  refine Finset.card_image_of_injOn fun x hx y hy hxy ↦ ?_
  exact spell_injOn code L hlen hinj x y
    (by rw [length_of_mem_mosaics hx, length_of_mem_mosaics hy]) hxy

theorem card_panelWords (code : ι → List α) (L : ℕ) (hlen : ∀ h, (code h).length = L)
    (hinj : Function.Injective code) (c : Chain ι) :
    (panelWords code c).card = Fintype.card ι := by
  rw [panelWords, Finset.card_image_of_injOn, card_diagonals]
  intro x hx y hy hxy
  exact spell_injOn code L hlen hinj x y
    (by rw [length_of_mem_mosaics (diagonals_subset c hx),
      length_of_mem_mosaics (diagonals_subset c hy)]) hxy

theorem panelWords_subset (code : ι → List α) (c : Chain ι) :
    panelWords code c ⊆ spelledWords code c :=
  Finset.image_subset_image (diagonals_subset c)

/-- **The phantom word count.**  Everything the topology spells beyond the panel. -/
theorem card_phantomWords (code : ι → List α) (L : ℕ) (hlen : ∀ h, (code h).length = L)
    (hinj : Function.Injective code) (c : Chain ι) :
    (phantomWords code c).card = (mosaics c).card - Fintype.card ι := by
  have hin : panelWords code c ∩ spelledWords code c = panelWords code c :=
    Finset.inter_eq_left.mpr (panelWords_subset code c)
  rw [phantomWords, Finset.card_sdiff, hin, card_spelledWords code L hlen hinj c,
    card_panelWords code L hlen hinj c]

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
theorem pow_card_le_prod_width_mul_card_spelledWords [Nonempty ι] (code : ι → List α) (L : ℕ)
    (hlen : ∀ h, (code h).length = L) (hinj : Function.Injective code) (c : Chain ι) :
    Fintype.card ι ^ (c.length + 1) ≤ (c.map width).prod * (spelledWords code c).card := by
  rw [card_spelledWords code L hlen hinj c]
  exact pow_card_le_prod_width_mul_card_mosaics c

/-- **The exactness barrier, in distinct sequences.**  If the topology spells exactly the
`m` panel words and no more, then with donor-identifying blocks every interface keeps all `m`
thread identities in distinct states.  This is the barrier of
`Descent.Pangenome.Linkage.Barrier.width_eq_card_of_card_mosaics_eq` stated where a graph
builder can check it: on the sequences the graph spells, not on donor histories. -/
theorem width_eq_card_of_card_spelledWords_eq [Nonempty ι] (code : ι → List α) (L : ℕ)
    (hlen : ∀ h, (code h).length = L) (hinj : Function.Injective code) {c : Chain ι}
    (hex : (spelledWords code c).card = Fintype.card ι) :
    ∀ s ∈ c, width s = Fintype.card ι := by
  refine width_eq_card_of_card_mosaics_eq ?_
  rw [← card_spelledWords code L hlen hinj c]
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

/-- **The width law is attained as a count of distinct DNA words.**  A balanced chain over
biallelic single-SNP blocks spells exactly `m · ∏ b_j` distinct words, which is the value the
width bound of `Descent.Pangenome.Linkage.Barrier` gives.  So no sharper bound holds, and the
extremal example needs nothing richer than one marker per block. -/
theorem card_spelledWords_snpCode_of_balanced {c : Chain ι} {bs : List ℕ}
    (hb : Balanced c bs) :
    (spelledWords snpCode c).card = Fintype.card ι * bs.prod := by
  rw [card_spelledWords snpCode (Fintype.card ι) length_snpCode snpCode_injective c,
    card_mosaics_of_balanced hb]

/-- And all but the `m` panel words are words the panel never contained. -/
theorem card_phantomWords_snpCode_of_balanced {c : Chain ι} {bs : List ℕ}
    (hb : Balanced c bs) :
    (phantomWords snpCode c).card = Fintype.card ι * bs.prod - Fintype.card ι := by
  rw [card_phantomWords snpCode (Fintype.card ι) length_snpCode snpCode_injective c,
    card_mosaics_of_balanced hb]

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
