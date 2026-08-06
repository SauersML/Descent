/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Descent.Pangenome.Linkage.Barrier
import Descent.Pangenome.Linkage.Frequency
import Descent.Pangenome.Linkage.Metadata
import Descent.Pangenome.Linkage.Splicing
import Descent.Pangenome.Linkage.Tree

assert_below Descent.PopGen Descent.Spectral Descent.Blindness Descent.Conditionals
assert_below Descent.Portability Descent.Decision Descent.Program

/-!
# The group's statements, pinned

A theorem can be weakened without anything noticing.  Add a hypothesis, drop a factor from an
exponent, turn an equality into the inequality it implies, narrow a quantifier — the file
still compiles, every guard still passes, and the corpus now claims less than it says it
does.  `validation/code/check.py --only laundering` screens the SOURCE TEXT for names that
promise more than their signature delivers, which catches the case where the name stays put;
it cannot catch a statement that was quietly made smaller along with everything that reads
it.

This module closes that by restating each of the group's load-bearing results independently
and discharging the restatement with the theorem.  Every `example` below is written out from
what the result is supposed to say rather than copied from what it does say, so weakening the
theorem stops this file typechecking, and `lake build Descent` is the thing that fails.

Nothing here is new mathematics and nothing here may be cited: these are `example`s, so they
have no names and cannot become load-bearing themselves.  That is the point — a pin that
could be depended on would be a second copy of the corpus rather than a check on it.

The technique is taken from the statement-pinning section of `scripts/Audit.lean` in
`SauersML/nonsofic_existence`, where the headline theorems are restated as `example`s for the
same reason.

## Empirical status

None.  Every statement here is a restatement of one proved elsewhere in the group, and the
originals carry the group's verdict: the mathematics is about finite partitions and their
logarithms, and no measurement bears on it.
-/

namespace Descent.Pangenome.Linkage

open Finset

/-! ### One interface

The split of what a separator forgets into a width term and a nonnegative imbalance term,
and the monotonicity that makes merging a one-way street. -/

example {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι] (s : ι → ι) :
    identityLoss s
      = Real.log (Fintype.card ι : ℝ) - Real.log (width s : ℝ) + imbalance s :=
  identityLoss_eq_width_add_imbalance s

example {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι] (s : ι → ι) :
    0 ≤ imbalance s :=
  imbalance_nonneg s

example {ι : Type} [Fintype ι] [DecidableEq ι] (s φ : ι → ι) :
    identityLoss s ≤ identityLoss (φ ∘ s) :=
  identityLoss_le_comp s φ

/-! ### The barrier

The logarithmic form, and the integer form with the exponent and the direction both pinned. -/

example {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι] (c : Chain ι) :
    Real.log (Fintype.card ι : ℝ) + linkagePressure c
      ≤ Real.log ((mosaics c).card : ℝ) :=
  log_card_add_linkagePressure_le c

example {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι] (c : Chain ι) :
    Fintype.card ι ^ (c.length + 1) ≤ (c.map width).prod * (mosaics c).card :=
  pow_card_le_prod_width_mul_card_mosaics c

/-- The bound is attained, so it cannot be sharpened: an EQUALITY, not the inequality it
implies. -/
example {ι : Type} [Fintype ι] [DecidableEq ι] {c : Chain ι} {bs : List ℕ}
    (hb : Balanced c bs) :
    (c.map width).prod * (mosaics c).card = Fintype.card ι ^ (c.length + 1) :=
  prod_width_mul_card_mosaics_of_balanced hb

/-- The exact balanced count, with no hypothesis relating the partitions at different
interfaces. -/
example {ι : Type} [Fintype ι] [DecidableEq ι] {c : Chain ι} {bs : List ℕ}
    (hb : Balanced c bs) :
    (mosaics c).card = Fintype.card ι * bs.prod :=
  card_mosaics_of_balanced hb

/-- The exactness barrier: EVERY interface, not almost every one. -/
example {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι] {c : Chain ι}
    (hex : (mosaics c).card = Fintype.card ι) :
    ∀ s ∈ c, width s = Fintype.card ι :=
  width_eq_card_of_card_mosaics_eq hex

/-- The phantoms are exactly the recombinant derivations — set equality, not inclusion. -/
example {ι : Type} [Fintype ι] [DecidableEq ι] (c : Chain ι) :
    phantoms c = (mosaics c).filter fun x ↦ switches x ≠ 0 :=
  phantoms_eq_filter c

/-- One interface counts exactly. -/
example {ι : Type} [Fintype ι] [DecidableEq ι] (s : ι → ι) :
    (mosaics [s]).card = ∑ a ∈ Finset.univ.image s, (stateFiber s a).card ^ 2 :=
  card_mosaics_singleton s

/-! ### The generalities

Each of these drops a restriction, and the pin records which one. -/

/-- Any strictly positive frequency law, not the uniform one. -/
example {ι : Type} [Fintype ι] [DecidableEq ι] {p : ι → ℝ} (hp : ∀ h, 0 < p h)
    (hp1 : ∑ h : ι, p h = 1) (c : Chain ι) :
    panelEntropy p + condLinkagePressure p c ≤ Real.log ((mosaics c).card : ℝ) :=
  panelEntropy_add_condLinkagePressure_le hp hp1 c

/-- What is called `H(J ∣ S)` satisfies the chain rule `H(J ∣ S) + H(S) = H(J)`. -/
example {ι : Type} [Fintype ι] [DecidableEq ι] {p : ι → ℝ} (hp : ∀ h, 0 < p h) (s : ι → ι) :
    condIdentityLoss p s + stateEntropy p s = panelEntropy p :=
  condIdentityLoss_add_stateEntropy hp s

/-- Any tree of modules, with unrelated relations on its edges. -/
example {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι] (a : Arbor ι) :
    Fintype.card ι ^ (a.size + 1) ≤ arborWidthProd a * (arborMosaics a).card :=
  pow_card_le_arborWidthProd_mul_card_arborMosaics a

example {ι : Type} [Fintype ι] [DecidableEq ι] {a : Arbor ι} {b : ℕ}
    (hb : ArborBalanced a b) :
    arborWidthProd a * (arborMosaics a).card = Fintype.card ι ^ (a.size + 1) :=
  arborWidthProd_mul_card_arborMosaics_of_balanced hb

/-! ### Sequences, and the metadata trade -/

/-- Unique decodability from prefix-freeness ALONE: no hypothesis on block lengths. -/
example {ι : Type} [Fintype ι] [DecidableEq ι] {α : Type} (code : ι → List α)
    (hpf : PrefixFree code) (x y : List ι) (hlen : x.length = y.length)
    (hsp : spell code x = spell code y) : x = y :=
  spell_injOn_of_prefixFree code hpf x y hlen hsp

/-- Distinct derivations spell distinct sequences, so the whole count transfers. -/
example {ι : Type} [Fintype ι] [DecidableEq ι] {α : Type} [DecidableEq α] (code : ι → List α)
    (hpf : PrefixFree code) (c : Chain ι) :
    (spelledWords code c).card = (mosaics c).card :=
  card_spelledWords code hpf c

/-- The width law attained in distinct DNA words by a single-SNP block system. -/
example {ι : Type} [Fintype ι] [DecidableEq ι] {c : Chain ι} {bs : List ℕ}
    (hb : Balanced c bs) :
    (spelledWords snpCode c).card = Fintype.card ι * bs.prod :=
  card_spelledWords_snpCode_of_balanced hb

/-- An exact controller at an interface of width `w` needs an alphabet of at least `m / w`. -/
example {ι : Type} [Fintype ι] [DecidableEq ι] {A : Type} [Fintype A] [DecidableEq A]
    {R : Type} (s : ι → ι) (aux : ι → A) (ρ : ι → R) (hres : Resolves s aux ρ)
    (hρ : ∀ g h : ι, s g = s h → ρ g = ρ h → g = h) :
    Fintype.card ι ≤ width s * Fintype.card A :=
  card_le_width_mul_card_aux s aux ρ hres hρ

end Descent.Pangenome.Linkage
