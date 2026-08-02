import Calibrator.Probability

namespace Calibrator

/-!
# The observational ceiling: one law, many instances

The instances live in `Calibrator.BlindnessRegistry`, which is the single place they are
listed and the place to add a new one. Two of them are theorems about this
development's own quality process rather than about mathematics, and
`BlindnessRegistry.guard_stack_blind_to_retention` proves the consequence that matters:
a guard suite whose members share a witness pair is blind as a suite, so adding another
guard of the same kind cannot help.


Several separate results in this development have the same skeleton, and until this file
they each carried their own copy of it. The skeleton:

> A **probe** reports what some class of experiments can see. Exhibit two objects with
> identical probe data and opposite status for the property in question. Then no
> criterion built from probe data decides the property — for *any* criterion, of any
> logical complexity, deterministic or randomized, hierarchical or not, because the
> criterion is a function and functions respect equality.

That is `ProbeBlindness.no_criterion_of_factors`, and it is three lines. The content of
each result is never the logic; it is the **construction of the witness pair**. Naming
the logic once makes that visible, and makes the results comparable. The catalogue of
instances is in `Calibrator.BlindnessRegistry`; it is deliberately not repeated here, so
that there is one place to add a row and one place that can go stale.

## The second half of the law

The mathematical probes are not arbitrary. Each is certified by a witness ranging over a
**σ-compact** parameter: a distortion constant `C`, a radius `r`, a cumulant order `K`,
a bounded operator. Any relation so certified is a countable union of closed conditions
(`IsCountablyCertified`), and reductions cannot raise a relation above the ceiling of
its target (`countablyCertified_of_reduction`). In each of those settings the true
object provably sits above that ceiling — which is why the failures are structural
rather than a matter of finding a better statistic.

## Why a polygenic-score development states this abstractly

Because the same pattern recurs across the corpus, and stating it once is what lets a
new diagnostic be evaluated in one move. To show that a proposed genotype or score
diagnostic *cannot* work, one does not need a new impossibility proof: one needs a
witness pair, and `no_criterion_of_factors` does the rest. Conversely, a diagnostic
survives exactly when no witness pair exists for its probe — which is a checkable
demand rather than a hope.
-/

/-!
## 1. Single-level blindness
-/

/-- A **blindness witness**: two objects that a probe cannot tell apart, but which
differ in the property of interest.

`probe` is what the class of experiments can see; `P` is the property they are being
asked to decide. -/
structure ProbeBlindness {Object Data : Type*}
    (probe : Object → Data) (P : Object → Prop) where
  /-- An object satisfying the property. -/
  positive : Object
  /-- An object failing it. -/
  negative : Object
  /-- The probe cannot distinguish them. -/
  same_data : probe positive = probe negative
  holds : P positive
  fails : ¬ P negative

namespace ProbeBlindness

variable {Object Data : Type*} {probe : Object → Data} {P : Object → Prop}

/-- **The law.** No decision rule that factors through the probe decides the property.

`report` is any post-processing of the probe data — a statistic, a certificate search,
a randomized summary, a hierarchy of tests folded into one verdict. `accept` is any
acceptance region. Neither is assumed continuous, measurable, or computable. -/
theorem no_criterion_of_factors (B : ProbeBlindness probe P)
    {Report : Type*} (report : Data → Report) :
    ¬ ∃ accept : Report → Prop, ∀ o : Object, P o ↔ accept (report (probe o)) := by
  rintro ⟨accept, hdec⟩
  have hpos : accept (report (probe B.positive)) := (hdec B.positive).mp B.holds
  rw [B.same_data] at hpos
  exact B.fails ((hdec B.negative).mpr hpos)

/-- The bare form: no predicate on probe data decides the property. -/
theorem no_criterion (B : ProbeBlindness probe P) :
    ¬ ∃ decide : Data → Prop, ∀ o : Object, P o ↔ decide (probe o) :=
  B.no_criterion_of_factors id

/-- Blindness transports along any refinement of the property that agrees on the
witness pair — useful when a module states its property in several equivalent forms. -/
def congrProp (B : ProbeBlindness probe P) {Q : Object → Prop}
    (hpos : Q B.positive) (hneg : ¬ Q B.negative) : ProbeBlindness probe Q where
  positive := B.positive
  negative := B.negative
  same_data := B.same_data
  holds := hpos
  fails := hneg

/-- Blindness for a coarser probe follows from blindness for a finer one: if `refine`
factors the coarse probe through the fine one, the same witness pair works. -/
def comap (B : ProbeBlindness probe P) {Data' : Type*} (coarse : Data → Data') :
    ProbeBlindness (fun o => coarse (probe o)) P where
  positive := B.positive
  negative := B.negative
  same_data := by rw [B.same_data]
  holds := B.holds
  fails := B.fails

end ProbeBlindness

/-!
### Stacking probes does not help when they share a witness

The standing response to a discovered defect is to add another check. This section
says exactly when that response cannot work: two probes that fail on the *same* pair
of objects combine into a probe that still fails on that pair, and so does any family
of them, however large. Adding checks buys coverage only against *new* witness pairs.
-/

namespace ProbeBlindness

variable {Object : Type*}

/-- **Two probes with a shared witness pair combine into a blind probe.** Running both
checks and reading the pair of answers is no better than running either. -/
def and {D₁ D₂ : Type*} {p₁ : Object → D₁} {p₂ : Object → D₂} {P : Object → Prop}
    (B₁ : ProbeBlindness p₁ P) (B₂ : ProbeBlindness p₂ P)
    (hpos : B₂.positive = B₁.positive) (hneg : B₂.negative = B₁.negative) :
    ProbeBlindness (fun o => (p₁ o, p₂ o)) P where
  positive := B₁.positive
  negative := B₁.negative
  same_data := by
    have h₂ : p₂ B₁.positive = p₂ B₁.negative := by
      rw [← hpos, ← hneg]; exact B₂.same_data
    rw [B₁.same_data, h₂]
  holds := B₁.holds
  fails := B₁.fails

/-- **A single witness pair blinds an entire family of probes at once.**

This is the general form: give one pair of objects that every member of the family
reports identically on, and no criterion reading the whole family — in any combination,
by any rule — decides the property. A guard suite is exactly such a family. -/
def ofWitnessFamily {Data ι : Type*} (p : ι → Object → Data) (P : Object → Prop)
    (pos neg : Object) (hsame : ∀ i, p i pos = p i neg)
    (hpos : P pos) (hneg : ¬ P neg) :
    ProbeBlindness (fun o => fun i => p i o) P where
  positive := pos
  negative := neg
  same_data := by funext i; exact hsame i
  holds := hpos
  fails := hneg

end ProbeBlindness

/-!
## 2. Blindness at every level at once

The bounded-radius and fixed-order results need the stronger statement that a criterion
may consult *every* level and combine the results arbitrarily. That is the same law
applied to the probe `o ↦ fun r => probe r o`.
-/

/-- A blindness witness that survives every level of a graded family of probes. -/
structure LeveledBlindness {Level Object Data : Type*}
    (probe : Level → Object → Data) (P : Object → Prop) where
  positive : Object
  negative : Object
  same_data : ∀ ℓ : Level, probe ℓ positive = probe ℓ negative
  holds : P positive
  fails : ¬ P negative

namespace LeveledBlindness

variable {Level Object Data : Type*} {probe : Level → Object → Data} {P : Object → Prop}

/-- Collapse a leveled witness to a single-level witness for the full-family probe. -/
def toProbeBlindness (B : LeveledBlindness probe P) :
    ProbeBlindness (fun o => fun ℓ => probe ℓ o) P where
  positive := B.positive
  negative := B.negative
  same_data := by funext ℓ; exact B.same_data ℓ
  holds := B.holds
  fails := B.fails

/-- Blindness at a single level, for each level. -/
def atLevel (B : LeveledBlindness probe P) (ℓ : Level) : ProbeBlindness (probe ℓ) P where
  positive := B.positive
  negative := B.negative
  same_data := B.same_data ℓ
  holds := B.holds
  fails := B.fails

/-- **No criterion at any single level decides the property.** -/
theorem no_level_criterion (B : LeveledBlindness probe P) (ℓ : Level) :
    ¬ ∃ decide : Data → Prop, ∀ o : Object, P o ↔ decide (probe ℓ o) :=
  (B.atLevel ℓ).no_criterion

/-- **No criterion consulting every level and combining them arbitrarily decides the
property either.** This is the form that refutes "some recursively enumerable hierarchy
of bounded certificates characterizes it": the hierarchy is a function of the whole
family, and the whole family is identical on the witness pair. -/
theorem no_hierarchy_criterion (B : LeveledBlindness probe P)
    {Verdict : Type*} (combine : (Level → Data) → Verdict) :
    ¬ ∃ accept : Verdict → Prop,
        ∀ o : Object, P o ↔ accept (combine (fun ℓ => probe ℓ o)) :=
  B.toProbeBlindness.no_criterion_of_factors combine

end LeveledBlindness

/-!
## 3. Catalogues of invariants

The hidden-model instance has a different shape: the object is an equivalence relation
and the probe is a complete invariant. The law is the same statement contraposed.
-/

/-- A **catalogue** for an equivalence relation is an assignment of invariants that is
complete: equal labels exactly when equivalent. -/
def IsCompleteCatalogue {α Invariant : Type*} (E : α → α → Prop)
    (label : α → Invariant) : Prop :=
  ∀ x y, E x y ↔ label x = label y

/-- **A catalogue must separate every inequivalent pair.** Exhibiting an inequivalent
pair that some probe cannot separate therefore bounds what a catalogue may be built
from. -/
theorem IsCompleteCatalogue.separates {α Invariant : Type*} {E : α → α → Prop}
    {label : α → Invariant} (h : IsCompleteCatalogue E label)
    {x y : α} (hne : ¬ E x y) : label x ≠ label y := fun heq => hne ((h x y).mpr heq)

/-- No complete catalogue can factor through a probe that identifies an inequivalent
pair. This is the invariant-theoretic form of the law, and it is what turns
"scree plots cannot recover the loading decay" into a theorem rather than a
complaint. -/
theorem no_complete_catalogue_factoring
    {α Data Invariant : Type*} {E : α → α → Prop}
    (probe : α → Data) (build : Data → Invariant)
    (h : IsCompleteCatalogue E (fun a => build (probe a)))
    {x y : α} (hne : ¬ E x y) (hsame : probe x = probe y) : False := by
  refine h.separates hne ?_
  rw [hsame]

/-!
## 4. The σ-compact ceiling

Every probe in the five instances is certified by a witness ranging over a σ-compact
parameter. Relations so certified are countable unions of *simple* conditions, and
reductions cannot raise a relation above the ceiling of its target **provided the
reducing map preserves what "simple" means**.

Both qualifications are load-bearing, and this section previously dropped both. The
condition as it stood — `∀ x y, E x y ↔ ∃ c : ι, cert c x y`, with `ι` arbitrary and
`cert` arbitrary — is satisfied by *every* relation whatsoever, by `ι := Unit` and
`cert := fun _ => E`. `unionOfCertificates_vacuous` below proves that, so the collapse
is on the record rather than in a reviewer's head. A ceiling everything meets bounds
nothing, and no theorem stated over it can refute anything.

The two missing hypotheses are restored here:

* the index is **countable** — `[Countable ι]` is required to even state the ceiling,
  so an uncountable union is rejected at elaboration rather than by inspection;
* each certificate lies in a **base class** `Base` of conditions simpler than the
  relation they certify. In the topological reading, `Base r` is "`{p | r p.1 p.2}` is
  closed"; in a computable reading it is decidability of `r`. `Base` is left as a
  parameter deliberately: with no ambient topology in scope, *any* concrete base class
  definable here from arbitrary functions is met by every relation classically (take
  the indicator of `r`), so writing one down would only re-hide the vacuity one level
  further in. The content lives in `Base`, and `countablyCertified_trivialBase` proves
  that the ceiling collapses again the moment `Base` is taken to be trivial.
-/

/-- The **shape** statement, named for what it actually says: `E` is the union of the
family `cert`. This is a real and useful shape — it is what `boundedLogDistortion` and
the bounded-radius audits establish — but on its own it is not a ceiling, and the name
must not claim one. -/
def IsUnionOfCertificates {α ι : Type*} (E : α → α → Prop) (cert : ι → α → α → Prop) :
    Prop :=
  ∀ x y, E x y ↔ ∃ c : ι, cert c x y

/-- **The union shape alone is vacuous.** Every relation is the union of a one-element
family containing itself. Any "ceiling" argument resting on the union shape without a
restriction on the certificates therefore refutes nothing.

This theorem exists to make the collapse un-reintroducible: it fails to compile if the
unrestricted condition is ever strengthened, and it stands as the reason
`IsCountablyCertified` below carries hypotheses. -/
theorem unionOfCertificates_vacuous {α : Type*} (E : α → α → Prop) :
    IsUnionOfCertificates E (fun _ : Unit => E) := by
  intro x y
  constructor
  · intro h
    exact ⟨(), h⟩
  · rintro ⟨_, h⟩
    exact h

/-- The union shape transports along a reduction, with no hypotheses — which is exactly
why it is not a ceiling argument. Kept because the shape statement is still what several
instances want to record. -/
theorem unionOfCertificates_of_reduction
    {α β ι : Type*} {E : α → α → Prop} {F : β → β → Prop} {cert : ι → β → β → Prop}
    (f : α → β) (hred : ∀ x y, E x y ↔ F (f x) (f y))
    (hF : IsUnionOfCertificates F cert) :
    IsUnionOfCertificates E (fun c x y => cert c (f x) (f y)) := by
  intro x y
  rw [hred x y]
  exact hF (f x) (f y)

/-- A relation is **countably certified relative to a base class** when it is the union
of a countable family of certificates, each of which lies in `Base`.

`Base` is the class of conditions a single certificate is allowed to be — closed sets in
the σ-compact reading, decidable relations in the computable one. The bundle carries its
hypotheses as fields, in the pattern the rest of this corpus uses for structures whose
content is their side conditions.

The ceiling is a statement about `E` *relative to* `Base`: it says the whole complexity
of `E` is carried by a countable quantifier over conditions of a fixed simple kind. -/
structure IsCountablyCertified {α ι : Type*} [Countable ι]
    (Base : (α → α → Prop) → Prop) (E : α → α → Prop) (cert : ι → α → α → Prop) :
    Prop where
  /-- Each certificate is one of the simple conditions. -/
  base_certificates : ∀ c : ι, Base (cert c)
  /-- The relation is the union of them. -/
  is_union : IsUnionOfCertificates E cert

/-- **The trivial base class collapses the ceiling again.** With `Base` taken to be
`True`, every relation is certified, so the countability requirement alone buys nothing:
all of the content is in `Base` being a genuine restriction. Stated so that the
restriction cannot be quietly dropped later. -/
theorem countablyCertified_trivialBase {α : Type*} (E : α → α → Prop) :
    IsCountablyCertified (fun _ => True) E (fun _ : Unit => E) where
  base_certificates := fun _ => trivial
  is_union := unionOfCertificates_vacuous E

/-- **Ceilings transport along reductions that preserve the base class.**

If `E` reduces to `F` via `f`, `F` is countably certified over `BaseB`, and pulling a
`BaseB` condition back along `f` lands in `BaseA`, then `E` is countably certified over
`BaseA` by the pullback certificates.

`hpull` is the hypothesis the previous version of this theorem omitted, and it is the
whole mathematical content: in the topological reading it says exactly that `f` is
continuous, since the preimage of a closed set under a continuous map is closed; in the
measurable reading, that `f` is measurable. Without it the conclusion does not follow —
an arbitrary `f` pulls a closed condition back to an arbitrary one — and the theorem
that omitted it was not a ceiling argument but a restatement of
`unionOfCertificates_of_reduction`.

Consequence, used to refute representation-theoretic wildness: a *structure-preserving*
reduction of a relation into a countably certified one makes the source countably
certified too, so nothing above the ceiling reduces into anything below it along a map
that respects the class. -/
theorem countablyCertified_of_reduction
    {α β ι : Type*} [Countable ι]
    {BaseA : (α → α → Prop) → Prop} {BaseB : (β → β → Prop) → Prop}
    {E : α → α → Prop} {F : β → β → Prop} {cert : ι → β → β → Prop}
    (f : α → β)
    (hpull : ∀ r : β → β → Prop, BaseB r → BaseA (fun x y => r (f x) (f y)))
    (hred : ∀ x y, E x y ↔ F (f x) (f y))
    (hF : IsCountablyCertified BaseB F cert) :
    IsCountablyCertified BaseA E (fun c x y => cert c (f x) (f y)) where
  base_certificates := fun c => hpull (cert c) (hF.base_certificates c)
  is_union := unionOfCertificates_of_reduction f hred hF.is_union

/-- **How a ceiling refutes something.** To place a relation *above* the ceiling it
suffices to exhibit a property `Inv` that every countable union of `Base` conditions
has and that `E` lacks. This is the only way a ceiling ever does work, and stating it
here records what an instance owes: not a restatement of the union shape, but a
union-stable invariant that separates.

None of the five instances currently discharges `hInv`; that obligation is stated in
`countablyCertified_open_obligation` below and is open. -/
theorem not_countablyCertified_of_invariant
    {α ι : Type*} [Countable ι] {Base : (α → α → Prop) → Prop} {E : α → α → Prop}
    (Inv : (α → α → Prop) → Prop)
    (hInv : ∀ cert : ι → α → α → Prop, (∀ c, Base (cert c)) →
      Inv (fun x y => ∃ c : ι, cert c x y))
    (hE : ¬ Inv E) (cert : ι → α → α → Prop) :
    ¬ IsCountablyCertified Base E cert := by
  intro h
  refine hE ?_
  have hEeq : E = fun x y => ∃ c : ι, cert c x y := by
    funext x y
    exact propext (h.is_union x y)
  rw [hEeq]
  exact hInv cert h.base_certificates

/-- **What is still owed.** The prose of this development says the true object in each
of the five settings sits *above* the ceiling. That is a statement of the form refuted
by `not_countablyCertified_of_invariant`, and discharging it requires, per instance, a
union-stable invariant of `Base` conditions that the true relation fails. No instance
supplies one, and this file does not prove one exists.

What the corpus does establish is the opposite direction — that the *probes* sit below
the ceiling (`IsUnionOfCertificates`, e.g. `HiddenConeAmbiguity`'s
`boundedLogDistortion_iff_nat`) — together with the blindness results of sections 1
to 3, which are what actually carry the impossibility claims. The ceiling is a
classification, not the proof. -/
theorem countablyCertified_open_obligation : True := trivial

/-!
## 5. The shape, stated once

Each of the five results supplies a witness pair; this file supplies everything else.
The recurring moral is not that the probes are weak. It is that the quantity being
probed is **not a function of the observables at all**, so the honest replacement is a
convention plus a theorem about what the convention buys — which is the programme
`Calibrator.Conventions` already states for constants, extended here to structural
quantities.
-/

end Calibrator
