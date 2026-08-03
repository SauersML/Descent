/-
Copyright (c) 2026 Sauers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sauers
-/
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
a bounded operator. Section 4 says what that buys and — as of this revision — what it
does not. A relation that is a countable union of conditions from a base class of simple
sets is *below* the ceiling (`IsCountablyCertified`), and a reduction cannot raise a
relation above the ceiling of its target **provided the reducing map preserves the base
class** (`countablyCertified_of_reduction`). The preservation hypothesis is the whole
content of that theorem, and a version without it proves nothing.

Two limits on what this section claims. First, the bare union shape
with no restriction on the certificates is satisfied by every relation whatsoever —
`unionOfCertificates_vacuous` proves it — so nothing can be read off it. Second, the
claim that in each setting the true object *provably* sits above the ceiling is not
established anywhere in this development: doing so requires, per instance, a
union-stable invariant that the true relation fails, in the shape of
`not_countablyCertified_of_invariant`, and no instance supplies one. What the corpus
does prove is the blindness half — sections 1 to 3 — and it is the blindness half that
carries the impossibility results. The ceiling is a classification of the probes, not
the proof.

## What "structural" means here, exactly

`ProbeBlindness.same_data` is exact equality of probe output, so
`no_criterion_of_factors` rules out criteria that factor through the probe *exactly*.
That alone does not speak to a criterion resolving arbitrarily small differences in
probe data. `ApproxProbeBlindness.no_stable_criterion` extends it to the approximate
setting: if the two witnesses' probe outputs are close at a noise scale, then no
criterion whose verdict is stable at that scale decides the property either — including
every thresholded statistic with a decision margin wider than the gap. That is the
precise sense in which the failures are structural rather than a matter of finding a
better statistic: better statistics do not help unless they resolve below the noise
scale, which is a question about the witness pair, not about the logic.

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

end ProbeBlindness

/-!
### Equality of observable laws is an absolute wall for downstream statistics

`ProbeBlindness` is deliberately more general than probability.  In an explicitly
statistical experiment the corresponding obstruction is equality of pushforward laws.
The theorem below records the exact data-processing statement needed by the permeability
program: if two populations induce the same law on the retained observable, every
measurable statistic of that observable also has the same law.  A vanishing derivative
does not imply this premise; an exact gauge or support obstruction can.
-/

/-- **Observable-law obstruction.** Exact equality after the observation map propagates
through every measurable downstream statistic, at every output dimension.  Escaping the
wall requires enlarging the observable sigma-algebra, not changing the downstream
algorithm. -/
theorem identical_observable_law_implies_identical_statistic_law
    {Sample Observable Report : Type*}
    [MeasurableSpace Sample] [MeasurableSpace Observable] [MeasurableSpace Report]
    (source target : MeasureTheory.Measure Sample)
    (observe : Sample → Observable) (statistic : Observable → Report)
    (hobserve : Measurable observe) (hstatistic : Measurable statistic)
    (hsame : MeasureTheory.Measure.map observe source =
      MeasureTheory.Measure.map observe target) :
    MeasureTheory.Measure.map (statistic ∘ observe) source =
      MeasureTheory.Measure.map (statistic ∘ observe) target := by
  rw [← MeasureTheory.Measure.map_map hstatistic hobserve,
    ← MeasureTheory.Measure.map_map hstatistic hobserve, hsame]

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
    ProbeBlindness (fun o ↦ (p₁ o, p₂ o)) P where
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
    ProbeBlindness (fun o ↦ fun i ↦ p i o) P where
  positive := pos
  negative := neg
  same_data := by funext i; exact hsame i
  holds := hpos
  fails := hneg

end ProbeBlindness

/-!
### 1a. Approximate blindness, and criteria with a margin

`ProbeBlindness.same_data` is exact equality, so `no_criterion_of_factors` says nothing
about a criterion that resolves arbitrarily small differences in probe data. The
witness pairs in practice are only *close* — probe outputs agreeing to within a noise
scale, a sampling error, a finite precision — and the criteria in practice are only
required to be stable at that scale.

`close` is any relation on data: a metric ball of radius `ε`, agreement to `k` digits,
equality up to measurement noise. Nothing is assumed of it — not reflexivity, not
symmetry, not transitivity — because nothing is needed.
-/

/-- An **approximate blindness witness**: two objects whose probe outputs are close at
the noise scale `close`, but which differ in the property of interest. -/
structure ApproxProbeBlindness {Object Data : Type*}
    (close : Data → Data → Prop) (probe : Object → Data) (P : Object → Prop) where
  /-- An object satisfying the property. -/
  positive : Object
  /-- An object failing it. -/
  negative : Object
  /-- The probe separates them by less than the noise scale. -/
  close_data : close (probe positive) (probe negative)
  holds : P positive
  fails : ¬ P negative

namespace ApproxProbeBlindness

variable {Object Data : Type*} {close : Data → Data → Prop} {probe : Object → Data}
  {P : Object → Prop}

/-- **The approximate law.** No criterion whose verdict is stable at the noise scale
decides the property.

`hstable` is the whole hypothesis: the report must agree on data it cannot distinguish
at scale `close`. Every thresholded statistic with a decision margin wider than the gap
between the two witnesses satisfies it, as does any procedure that rounds, bins, or
quantizes its input before deciding. The conclusion is the same as the exact law, and
so is the proof — a stable report is a function of the data modulo the noise. -/
theorem no_stable_criterion (B : ApproxProbeBlindness close probe P)
    {Report : Type*} (report : Data → Report)
    (hstable : ∀ d d' : Data, close d d' → report d = report d') :
    ¬ ∃ accept : Report → Prop, ∀ o : Object, P o ↔ accept (report (probe o)) := by
  rintro ⟨accept, hdec⟩
  have hpos : accept (report (probe B.positive)) := (hdec B.positive).mp B.holds
  rw [hstable _ _ B.close_data] at hpos
  exact B.fails ((hdec B.negative).mpr hpos)

/-- The concrete reading, for a real-valued probe and an explicit tolerance: if the two
witnesses' probe values differ by at most `ε`, no `ε`-stable summary of that value
decides the property. -/
theorem no_stable_criterion_of_tolerance {Object : Type*} {probe : Object → ℝ}
    {P : Object → Prop} {ε : ℝ}
    (B : ApproxProbeBlindness (fun a b ↦ |a - b| ≤ ε) probe P)
    {Report : Type*} (report : ℝ → Report)
    (hstable : ∀ a b : ℝ, |a - b| ≤ ε → report a = report b) :
    ¬ ∃ accept : Report → Prop, ∀ o : Object, P o ↔ accept (report (probe o)) :=
  B.no_stable_criterion report hstable

end ApproxProbeBlindness

/-!
## 2. Blindness at every level at once

The bounded-radius and fixed-order results need the stronger statement that a criterion
may consult *every* level and combine the results arbitrarily. That is the same law
applied to the probe `o ↦ fun r ↦ probe r o`.
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
    ProbeBlindness (fun o ↦ fun ℓ ↦ probe ℓ o) P where
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
        ∀ o : Object, P o ↔ accept (combine (fun ℓ ↦ probe ℓ o)) :=
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
    {x y : α} (hne : ¬ E x y) : label x ≠ label y := fun heq ↦ hne ((h x y).mpr heq)

/-- No complete catalogue can factor through a probe that identifies an inequivalent
pair. This is the invariant-theoretic form of the law, and it is what turns
"scree plots cannot recover the loading decay" into a theorem rather than a
complaint. -/
theorem no_complete_catalogue_factoring
    {α Data Invariant : Type*} {E : α → α → Prop}
    (probe : α → Data) (build : Data → Invariant)
    (h : IsCompleteCatalogue E (fun a ↦ build (probe a)))
    {x y : α} (hne : ¬ E x y) (hsame : probe x = probe y) : False := by
  refine h.separates hne ?_
  rw [hsame]

/-!
## 4. The σ-compact ceiling

Every probe in the five instances is certified by a witness ranging over a σ-compact
parameter. Relations so certified are countable unions of *simple* conditions, and
reductions cannot raise a relation above the ceiling of its target **provided the
reducing map preserves what "simple" means**.

Both qualifications are load-bearing, and dropping either empties the claim. The
condition without them — `∀ x y, E x y ↔ ∃ c : ι, cert c x y`, with `ι` arbitrary and
`cert` arbitrary — is satisfied by *every* relation whatsoever, by `ι := Unit` and
`cert := fun _ ↦ E`. `unionOfCertificates_vacuous` below proves that, so the collapse
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
    IsUnionOfCertificates E (fun _ : Unit ↦ E) := by
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
    IsUnionOfCertificates E (fun c x y ↦ cert c (f x) (f y)) := by
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
    IsCountablyCertified (fun _ ↦ True) E (fun _ : Unit ↦ E) where
  base_certificates := fun _ ↦ trivial
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
    (hpull : ∀ r : β → β → Prop, BaseB r → BaseA (fun x y ↦ r (f x) (f y)))
    (hred : ∀ x y, E x y ↔ F (f x) (f y))
    (hF : IsCountablyCertified BaseB F cert) :
    IsCountablyCertified BaseA E (fun c x y ↦ cert c (f x) (f y)) where
  base_certificates := fun c ↦ hpull (cert c) (hF.base_certificates c)
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
      Inv (fun x y ↦ ∃ c : ι, cert c x y))
    (hE : ¬ Inv E) (cert : ι → α → α → Prop) :
    ¬ IsCountablyCertified Base E cert := by
  intro h
  refine hE ?_
  have hEeq : E = fun x y ↦ ∃ c : ι, cert c x y := by
    funext x y
    exact propext (h.is_union x y)
  rw [hEeq]
  exact hInv cert h.base_certificates

/-!
### What section 4 still owes

The prose of this development says the true object in each setting sits *above* the
ceiling. That is a statement of the form refuted by
`not_countablyCertified_of_invariant`, and discharging it requires, per instance, a
union-stable invariant of `Base` conditions that the true relation fails. No instance
supplies one, and nothing here proves one exists. It is stated as an open obligation
rather than carried as a `sorry`, because no theorem in this file depends on it: the
impossibility results rest on sections 1 to 3.

What the corpus does establish is the opposite direction — that the *probes* sit below
the ceiling as unions of certificates (`IsUnionOfCertificates`, e.g.
`HiddenConeAmbiguity.boundedLogDistortion_iff_nat`) — together with the blindness
results, which are what actually carry the claims. The ceiling classifies the probes;
it does not do the refuting.
-/

/-!
## 5. The shape, stated once

Each of the five results supplies a witness pair; this file supplies everything else.
The recurring moral is not that the probes are weak. It is that the quantity being
probed is **not a function of the observables at all**, so the honest replacement is a
convention plus a theorem about what the convention buys — which is the programme
`Calibrator.Conventions` already states for constants, extended here to structural
quantities.
-/

/-!
## The other end of the scale: separation, and why injectivity is not enough

Every instance in `Calibrator.BlindnessRegistry` is exact. `same_data` is an equality, so
each says the probe assigns *identical* data to two objects. That is the `σ = 0` endpoint
of a scale, and it is the only point on the scale the development can currently speak
about.

The endpoint is not where measurement lives. A probe can be injective — no blindness
witness exists at all — and still be useless, if the data it assigns to distinguishable
objects differ by less than the resolution available. What decides that is not injectivity
but a *modulus*: how far apart the probe pushes objects that are far apart.

`ProbeSeparation` is that modulus, and `recovery` is what it buys: an object is pinned by
its probe value to within `resolution / σ`. The two structures are incompatible
(`no_blindness`), which is the formal content of "identifiable or blind" — but the
practical content is in the constant, because `1 / σ` is unbounded over families of probes
that are each individually injective. A separating probe with small `σ` is identifiable in
principle and hopeless in practice, and nothing about `ProbeBlindness` distinguishes that
case from a good one.

`Calibrator.BlindnessRegistry.averageEffect_separation` is the instance with a genotypic
referent: there `σ = |1 - 2p|`, which vanishes exactly at the allele frequency where
instance 8 exhibits outright blindness, and degrades linearly on the way in. -/

section EffectiveSeparation

variable {Object Data : Type*} [MetricSpace Object] [MetricSpace Data]
variable {probe : Object → Data}

/-- **The modulus by which a probe separates objects.**

`σ` is a lower bound on how much probe data must move when the object moves. It is the
quantitative form of injectivity, and unlike injectivity it has a size. -/
structure ProbeSeparation (probe : Object → Data) where
  /-- The separation modulus. -/
  sigma : ℝ
  sigma_pos : 0 < sigma
  /-- Objects far apart have data far apart, at rate `sigma`. -/
  separates : ∀ o o' : Object, sigma * dist o o' ≤ dist (probe o) (probe o')

/-- **What separation buys: an object is pinned by its data to within `resolution / σ`.**

This is the modulus of continuity of the inverse. It is the only statement in this file
with a number in it, and the number is what an experiment has to beat. -/
theorem ProbeSeparation.recovery (S : ProbeSeparation probe) (o o' : Object) :
    dist o o' ≤ dist (probe o) (probe o') / S.sigma := by
  rw [le_div_iff₀ S.sigma_pos, mul_comm]
  exact S.separates o o'

/-- A probe with positive separation cannot be blind: the witness pair would have to be
one object. -/
theorem ProbeSeparation.witness_collapses (S : ProbeSeparation probe) {P : Object → Prop}
    (B : ProbeBlindness probe P) : B.positive = B.negative := by
  have h := S.separates B.positive B.negative
  rw [B.same_data, dist_self] at h
  have hd : dist B.positive B.negative ≤ 0 := by
    by_contra hpos
    push_neg at hpos
    nlinarith [S.sigma_pos]
  exact dist_le_zero.mp hd

/-- **Separation and blindness are incompatible.** The scale has two ends and nothing in
this development yet describes the middle, which is where measurement happens. -/
theorem ProbeSeparation.no_blindness (S : ProbeSeparation probe) {P : Object → Prop}
    (B : ProbeBlindness probe P) : False :=
  B.fails ((S.witness_collapses B) ▸ B.holds)

/-! ### Reading a coordinate twice is reading it once

The separation modulus answers "how well does this probe resolve objects". The next
question is what *more coordinates* buy, and the answer is not "more", because coordinates
can repeat each other.

`duplicate_dist` is the degenerate case in full: a probe that reports the same channel
twice moves exactly as far as the single channel. The pair carries the information of one.
Nothing here is deep — the content is that the corpus's separation machinery already
measures this, so the count that matters downstream is not the number of channels but the
number of *fresh* ones.

The genotypic instance is linkage. Two markers in complete linkage disequilibrium have
identical dosage in every individual, so a score reading both is the duplicated probe, and
`duplicate_separation` says its modulus is that of a single marker. A panel of `k` markers
in perfect LD blocks of size `ℓ` separates like `k / ℓ` markers, and it is the effective
count rather than `k` that appears in any resolution bound obtained from `recovery`.

This is why the independence assumptions elsewhere in the development are load-bearing
rather than decorative: results that count markers are counting fresh ones, and LD is
exactly the gap between the two counts. -/

/-- A probe reporting one channel twice moves exactly as far as that channel. -/
@[simp] theorem duplicate_dist {Object : Type*} (f : Object → ℝ) (o o' : Object) :
    dist ((f o, f o) : ℝ × ℝ) (f o', f o') = dist (f o) (f o') := by
  rw [Prod.dist_eq]
  exact max_self _

/-- **Duplicating a channel buys no separation.** The modulus of the doubled probe is the
modulus of the original, so a perfectly redundant coordinate contributes nothing to
resolving objects.

Declared `def` rather than `theorem`: `ProbeSeparation` is a STRUCTURE carrying a real
modulus, so this returns data, not a proof, and `theorem` requires a `Prop`. Declaring it
`theorem` makes the elaborator report "type of theorem
`Calibrator.duplicate_separation` is not a proposition". The keyword is the only thing at
stake, since the body builds the witness with `where` either way. Keeping it as data is
also strictly stronger than the
`Nonempty (ProbeSeparation _)` a `theorem` forces: the duplicated probe's
modulus is available, and `duplicate_separation f S |>.sigma` is definitionally
`S.sigma`, which is the content the surrounding prose claims. -/
def duplicate_separation {Object : Type*} [MetricSpace Object] (f : Object → ℝ)
    (S : ProbeSeparation f) :
    ProbeSeparation (fun o ↦ ((f o, f o) : ℝ × ℝ)) where
  sigma := S.sigma
  sigma_pos := S.sigma_pos
  separates := by
    intro o o'
    rw [duplicate_dist]
    exact S.separates o o'

end EffectiveSeparation

end Calibrator
