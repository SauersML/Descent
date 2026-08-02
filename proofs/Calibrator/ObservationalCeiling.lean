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


Five separate results in this development have the same skeleton, and until this file
they each carried their own copy of it. The skeleton:

> A **probe** reports what some class of experiments can see. Exhibit two objects with
> identical probe data and opposite status for the property in question. Then no
> criterion built from probe data decides the property — for *any* criterion, of any
> logical complexity, deterministic or randomized, hierarchical or not, because the
> criterion is a function and functions respect equality.

That is `ProbeBlindness.no_criterion_of_factors`, and it is three lines. The content of
each result is never the logic; it is the **construction of the witness pair**. Naming
the logic once makes that visible, and makes the five results comparable.

## The five instances

| instance | probe | witness pair | module |
|---|---|---|---|
| fixed-order cumulants | joint cumulant tensors of order `≤ K` | Gaussian vs. `tanh`-tilted blocks | `CumulantBlindness` |
| all-order contractions | normalized cumulant contractions, every order | Gaussian vs. i.i.d. Rademacher | `CumulantBlindness` |
| bounded-radius audits | data on unions of `≤ r` cover elements | bipartite vs. non-bipartite Ramanujan twins | `LocalToGlobalCoherence` |
| independent designs | limits of disjoint-support chaos | Gaussian vs. a chameleon law | `JetBarrier` |
| bounded-distortion witnesses | any complete invariant of the fiber relation | `ℓ∞`-divergent coded decay profiles | `HiddenConeAmbiguity` |

## The second half of the law

The four probes above are not arbitrary. Each is certified by a witness ranging over a
**σ-compact** parameter: a distortion constant `C`, a radius `r`, a cumulant order `K`,
a bounded operator. Any relation so certified is a countable union of closed conditions
(`IsCountablyCertified`), and reductions cannot raise a relation above the ceiling of
its target (`countablyCertified_of_reduction`). In each of the five settings the true
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
parameter. Relations so certified are countable unions of closed conditions, and
reductions cannot raise a relation above the ceiling of its target.
-/

/-- A relation is **countably certified** by `cert` when membership is witnessed by a
single index — a distortion constant, a radius, an order. -/
def IsCountablyCertified {α ι : Type*} (E : α → α → Prop) (cert : ι → α → α → Prop) :
    Prop :=
  ∀ x y, E x y ↔ ∃ c : ι, cert c x y

/-- **Ceilings transport along reductions.** If `E` reduces to `F` via `f` and `F` is
countably certified, then so is `E`, by the pullback certificates.

Consequence, used to refute representation-theoretic wildness: a reduction of a
relation into a countably certified one makes the source countably certified too, so
nothing above the ceiling reduces into anything below it. -/
theorem countablyCertified_of_reduction
    {α β ι : Type*} {E : α → α → Prop} {F : β → β → Prop} {cert : ι → β → β → Prop}
    (f : α → β) (hred : ∀ x y, E x y ↔ F (f x) (f y))
    (hF : IsCountablyCertified F cert) :
    IsCountablyCertified E (fun c x y => cert c (f x) (f y)) := by
  intro x y
  rw [hred x y]
  exact hF (f x) (f y)

/-- A countably certified relation with an increasing certificate family is the union
of its levels; this is the form in which the Borel ceiling is read off. -/
theorem countablyCertified_iff_exists
    {α ι : Type*} {E : α → α → Prop} {cert : ι → α → α → Prop}
    (h : IsCountablyCertified E cert) (x y : α) :
    E x y ↔ ∃ c : ι, cert c x y := h x y

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
