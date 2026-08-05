# Descent

A Lean 4 formalization of population-genetic theory and its consequences for
deployed polygenic scores: roughly 6,600 theorems over 286 modules, built on
Mathlib.

The mathematics is only half of what this repository is. The other half is a set
of guards that check the corpus's *shape* — that its files depend on each other
for reasons, that its subsystems are joined to its results, and that its headline
claim is stated rather than described. This README is where those are written
down, because the shape is not visible from any one file.

## The layer contract

A module may import its own layer and any layer below it, and nothing above.

    0  Core          the kernels every layer shares: ratios, scaling conventions,
                     genome and heterozygosity, F_ST, the parameter record, the
                     moment tuple and the metrics computed from it
    1  Foundations   probability, covariance structure, transport identities
    2  Coalescent    the genealogical process, from state space to the frequency
                     spectrum
    3  PopGen        the data-generating process and the population genetics of
                     real histories
    4  Portability   subsystems over that base: the portability of a score, and
       Spectral      alongside it the spectral, blindness, conditional-structure
       Blindness     and pangenome developments. These five share a rank because
       Conditionals  none is built on another; an import between them is a
       Pangenome     coupling, not a layer violation
    5  Decision      what a decision-maker may conclude
    6  Program       what the corpus as a whole claims, and what it does not

`validation/code/importreach.py` holds this table and is the authority on it —
the copy above is prose. Run it to see where the corpus stands:

    python3 validation/code/importreach.py layers

**The contract is not yet met.** There are 24 import lines pointing upward, and
they cast 415 transitive violations between them. The direct list is the work
list; the transitive number is what those 24 lines cost. Enforcement belongs in
`assert_not_exists` at the head of each file, where a violation is a build error
at the file that commits it, and it will move there.

## The spine

The corpus exists to make one composite claim, and it is a chain of named maps
rather than a chapter about each link:

    PopGenParameters  →  fstEquilibrium  →  momentsUnderDrift  →  a deployed metric
    (Ne, mu, mig,        differentiation     the score's mean,      R², calibration
     t_div, recomb,      at equilibrium      variance and           slope, Brier,
     V_A, with its                          covariance with        AUC
     admissibility                          the phenotype
     proofs)

In Lean, `Descent/Core/Moments.lean`:

    noncomputable def deployedR2 (p : PopGenParameters) (V_E : ℝ) : ℝ :=
      (momentsUnderDrift p.V_A V_E p.fstEquilibrium).r2

Every part of that signature is load-bearing. The demography arrives as one
record carrying its own admissibility proofs — `Ne_pos`, `recomb_le_half` — so a
constraint added to the record reaches every caller. `F_ST` is *computed* from
the record rather than supplied as a free real, which is the difference between a
theorem about a population and a theorem about arithmetic that a reader has to
supply the population genetics for. And the metric at the end is the number a
deployment reports.

Before this chain existed, the population genetics and the deployed metrics were
two developments sharing a namespace: two theorems in the whole corpus named a
demographic quantity and a metric together. There are now nineteen theorems
stating a claim across the full chain — and all nineteen of them are in
`Core/Moments.lean`. No subsystem has yet stated one. That is the largest single
gap in the corpus and `shape-spine` is the guard that measures it.

## The gates

The corpus keeps organising itself by **narrative** — by the order a person would
read it in — rather than by **dependency**. A directory gets split into the order
its chapters were written; a subsystem gets started as an island; a metric gets a
second entry point taking its demography as loose reals. Each of these was found
by an audit, fixed by hand, and back one release later somewhere else. It recurs
because a reading order is invisible to a build: `A` imports `B` because `B` was
written first, an unused import compiles, and nothing anywhere fails.

The root file states the rule these gates apply to the repository itself:

> When two places must agree, make one of them call the other; a note explaining
> why they must agree is not a mechanism.

A measurement that is printed is a note. A measurement with an exit code is a
mechanism. Everything below fails a build.

    python3 validation/code/check.py             # every gated guard
    python3 validation/code/check.py --list      # which are gated, which diagnostic
    python3 validation/code/check.py --only shape-depth
    python3 validation/code/architecture.py --gate --verbose

### Shape

| guard | what fails the build |
| --- | --- |
| `shape-depth` | the longest import chain, tables of contents removed, exceeding 12. The audit that prompted this measured a chain of 38 modules, each importing the one written before it: a manuscript order compiled into the build graph |
| `shape-chains` | a module whose *one* internal import is a sibling in its own directory that it names nothing from. The finding prints where the symbols it does name actually live — that is the import it wanted |
| `shape-components` | a module outside the corpus's single weak component. `Coalescent` was an island one release ago and `Pangenome` was one in this release; both were wired in by hand, which is the argument for the guard rather than against it |
| `shape-spine` | cross-module theorem reuse below 20%, or fewer than 80 theorems joining `PopGenParameters` to a metric computed from the `Core/Moments` kernel |
| `shape-routes` | a definition taking four or more bare reals that shares a name stem with a record-typed one — two routes to one metric, of which only one carries the record's constraints |

`shape-routes` is gated. The other four are **diagnostic**: they report their
findings in full and do not fail the build, because their repairs are in flight
and gating them today would break the build for everyone. The budgets are zero
and do not move, and each one's entry in the `GUARDS` table names exactly what
must land before it flips.

### Soundness and honesty

| guard | what fails the build |
| --- | --- |
| `laundering` | a valid proof of a weaker, conditional, vacuous or circular statement shipped under the intended theorem's name |
| `identifications` | `sorry` reported and `admit` forbidden; convention drift; equilibria with no dynamic |
| `duplication`, `mathlib` | the same mathematics written twice, or re-proved from Mathlib |
| `regimes` | a scientific conclusion accepted from a caller and re-exported by field projection |
| `conventions` | a quantity used under an unstated convention, or a constant that has drifted from its source paper |
| `ledger`, `core-empirics` | a declaration the simulations refute whose docstring does not say so. `core-empirics` holds `Descent/Core/` to a stricter standard, because at depth 0–1 an unstated verdict is an unstated premise |
| `heads`, `closure`, `wiring` | a module the build cannot reach, or one adjacent to the corpus rather than wired into it |

A `sorry` is preferred to every pattern these detect. A `sorry` is an honest,
machine-visible, kernel-tracked hole. A laundered theorem is an invisible hole
that every automated report calls green.

### Architecture

`validation/code/architecture.py --gate` holds ten defect counts at zero, with no
baseline file and no ratchet: a duplicate body, an orphan definition, an
uninhabited structure, a foundation that depends on what it reconciles, or a
falsification no docstring mentions fails the build. There is deliberately no
allowance for the state the corpus happens to be in, because that state is the
thing being repaired.

## Building

```sh
lake exe cache get
lake build Descent ValidationShared
```

## Contributing

All contributions are welcome. Before opening a pull request, run
`python3 validation/code/check.py`; if you add a module, `heads` will tell you
which directory head is missing it.

## License

Apache-2.0. See [LICENSE](LICENSE).
