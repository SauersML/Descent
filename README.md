# Descent

A Lean 4 formalization of polygenic score portability: how demographic history
degrades a score trained in one population and deployed in another.

There is no `sorry` in any proof and one custom axiom. Soundness is not this
corpus's failure mode. Fragmentation is — the same quantity re-derived under a
fourth name in a module that imports nothing relating it to the first three — and
most of the structure below exists to make that a compile error rather than a
census finding.

## The layer contract

```
  Core/            depth 0-2, Mathlib only.  Shapes, not quantities.
    Ratios         proportionalReduction, convexCombination, geometricDecay,
                   saturation, oddsLike, share, survivalWeightedMix, …
    Fst            one island-model equilibrium + its specialisation lattice;
                   NeiFst and HudsonFst as DISTINCT types
    Parameters     one PopGenParameters record  (Ne, mu, mig, t_div, recomb, V_A)
    Moments        ScoreMoments — the interface between the two layers below

  PopGen/          a demographic history produces a moment tuple
  Portability/     a moment tuple produces R², a calibration slope, a Brier score
  Coalescent/      Kingman (1982), from the rate ladder to Ewens sampling
  Blindness/  Spectral/  Conditionals/  Decision/  Program/
```

**The rule the layout enforces**, taken from the root file:

> When two places must agree, make one of them call the other; a note explaining
> why they must agree is not a mechanism.

A kernel in `Core` is a *shape*: `proportionalReduction a b = 1 - a/b` is not
`F_ST`, not `R²`, and not PC-correction efficacy — it is the construction all
three instantiate. Kernels carry **no empirical status**, because they assert
nothing about a population. The named biological quantities live in the subsystem
modules, keep their own docstrings and regimes, and *call* the kernel.

**Wrap, never replace.** Four names for `(1-r)^t` is not four copies of one
thing: `admixtureLDDecay` carries a measured `+0.24%`–`+0.37%` one-sided bias
against finite-population retention and a theorem proving that sign, which a bare
primitive has nowhere to put.

## Two conventions that cost real accuracy to get wrong

**Every `F_ST` written in `τ/(1+τ)` coordinates is a Hudson `F_ST`.** Nei's
estimator is FALSIFIED at up to 18.59 sems against the split law on genotype
matrices where Hudson's matches at 0.03, and the ratio between them moves with
the data (0.62, 0.60, 0.68, 0.81) — so no correction factor converts one to the
other. `Core.NeiFst` and `Core.HudsonFst` are distinct one-field types;
substituting one for the other does not typecheck.

**`fstEquilibrium`'s `1/(1 + θ + 2M)` is not the many-deme law.** Its migration
flow is `8Nₑm` against the island law's `4Nₑm·d/(d−1)`. Those agree *exactly* at
`d = 2` — the `2` **is** the two-deme correction — and nowhere else. See
`Core.PopGenParameters.fstEquilibrium_eq_island_two_demes` and its companion
`_ne_island_manyDemes`.

## The empirical ledger

`validation/empirical/simcov/ledger.json` holds every simulation verdict, with
the regime, the battery, and the worst distance in standard errors. A MATCH with
no rejected competitor is recorded as UNINFORMATIVE, not as a pass: a design that
could not have rejected anything measured nothing.

A declaration the ledger records as FALSIFIED must say so in its own docstring.
That is checked, not trusted — see the architecture gates below.

Read a ledger row through the declaration's docstring, not on its own. Rows carry
a `freshness` field; `UNVERIFIED (no recorded source hash)` means nothing checked
the row against the Lean when the source last changed, and several such rows are
stale against bodies that were subsequently corrected.

## Building

```sh
lake exe cache get
lake build Descent ValidationShared
```

## Checking

```sh
python3 validation/code/check.py                     # source-text rules
lake env lean validation/code/Check.lean             # elaborated environment
python3 validation/code/architecture.py --verbose    # the shape of the corpus
python3 validation/code/architecture.py --gate       # …and fail on regression
```

The architecture gates are a **ratchet**, not a threshold. They compare against
`validation/code/architecture_baseline.json` and fail on regression — and also on
an unrecorded improvement, so a number cannot quietly drift back down. Absolute
targets would fail on the day they were written and teach everyone to ignore the
gate. What they measure:

| gate | what a regression means |
|---|---|
| `foundation_position_offenders` | a module claiming to be a foundation while sitting in a leaf, where nothing can depend on it |
| `duplicate_body_groups` | a definition that re-types a shared body instead of wrapping the kernel |
| `cross_module_reuse_pct` | theorems drifting back toward independent monographs |
| `composition_theorems` | the demography→metric spine thinning out |
| `silent_falsifications` | a FALSIFIED ledger row no docstring mentions |

`scripts/ci-mirror.sh` runs the whole GitHub Actions gate list on a machine that
can build. `.github/workflows/prover.yml` is the authority; that script is a
mirror of it, and a step present in one and not the other is a defect.

## Contributing

All contributions are welcome. Two things to know before editing a definition:

1. If your change makes two spellings of one quantity agree, make one call the
   other. A theorem saying they agree, stated above both, is not a mechanism.
2. If a definition has an `Empirical status:` line, it is load-bearing. Changing
   the body without re-measuring detaches a recorded regime from the formula it
   describes.

## License

Apache-2.0. See [LICENSE](LICENSE).
