# Population genetics and selection cells

Five corpus claims that had no empirical verdict, each measured with a
competitor on the same cells, a declared `argument_source`, and a positive
control that could have failed.

| file | cells | guard |
| --- | --- | --- |
| `popgensel.py` | A `driftLDCreationRate`, B `bottleneckExcessLD`, C `freeRecombinationStep`, D `selectionPortabilityTimescale` | `PGSEL_V1` |
| `selcell.py` | E `effectCorrelationStabilizing`, divergence-time axis | `PGSEL_E1` |
| `selpower.py` | E's positive control: the selection axis, where the design must move | `PGSEL_E2` |
| `results.json` | the committed output of all three | |

## Verdicts

| cell | def | verdict |
| --- | --- | --- |
| A | `DemographicHistory.driftLDCreationRate` | VALIDATED as a drift rate; `1/(4Nₑ)` rejected at 102 sems, `1/Nₑ` at 199-206 |
| B | `DemographicHistory.bottleneckExcessLD` | VALIDATED; deleted predecessor rejected at 10-20 sems |
| C | `EpistaticChaos.freeRecombinationStep` | FALSIFIED as a one-generation step: `D' = (1-r) D`, so free recombination halves `D` rather than removing it |
| D | `SelectionArchitecture.selectionPortabilityTimescale` | FALSIFIED by a factor of two: the e-folding time is `1/log(1+s)`, not `1/(2s)` |
| E | `SelectionArchitecture.effectCorrelationStabilizing` | FALSIFIED twice: the quantity depends on divergence time and the body has none, and the `Ns` dependence has the wrong sign |

## Discipline

**Selection is not in the coalescent.** Cell E is forward and individual-based
because Gaussian stabilizing selection toward a shared optimum has no coalescent
representation. Ne is scaled DOWN and the compound parameter `N·s` swept, so the
whole battery runs in minutes.

**Every cell carries a competitor and a `PLANTED` arm.** An oracle pinned to the
body under test cannot reject a rival, so a MATCH with no rival rejected is
worthless. Cells A, B and D reject their `PLANTED` arm at 9.7 sems or better.

**The positive control on the axis the claim is about.** Cell E's headline
result is that the correlation does not move with `Ns`. That reads as a
falsification only if the design CAN move along that axis, so `selpower.py`
sweeps `s` to 2.0 at 60 loci and shows a 12-sem move. Without it the flatness
would have been the instrument's blindness, not the corpus's error.

**A broken instrument reported cell B as a flat zero.** The first version
tracked per-locus founder labels; with no mutation those fix, `Q` goes to `1` in
both arms and the excess is identically `0.000` with zero variance. The fix is
in `wf_two_locus`: a recombinant offspring gets a FRESH id, because its two loci
no longer descend together. A cell reading exactly `0.00 ± 0.00` is an
instrument failure, not a finding.

## Running (MSI)

```sh
cd /projects/standard/hsiehph/sauer354/xsim
taskset -c 0-15 ./fwenv/bin/python popgensel.py ABCD
taskset -c 16-31 ./fwenv/bin/python selcell.py 40
taskset -c 32-47 ./fwenv/bin/python selpower.py 150
```

Calibrated against msprime 1.4.2, numpy 2.5.1, Python 3.12.13. Every run prints
`FRESHNESS=OK` with its guard string; a run that does not print it is stale.
