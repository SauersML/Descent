# Cluster runbook — invariants tier

All jobs are pure Python + numpy, single process, no builds, no tree copies.
Peak memory is a few hundred MB (one simulated haplotype pool of 1.5e6 int8).
Nothing here writes outside `proofs/validation/invariants/`.

```
module load python3/3.10.9_anaconda2023.03_libmamba
cd <repo>/proofs/validation/invariants
```

Written against Python 3.10, numpy. scipy is available but **deliberately not
used yet** — see "one change at a time" below. z3 is absent; job 2 handles that.

## Job 1 — seed-stability sweep (PRIORITY, run first)

```
python3 cluster/run_stability.py --seeds 8 > cluster/out_stability.txt 2>&1
```

Runtime: a few minutes. Send back `cluster/out_stability.txt` and
`results_simulation_stability.json`.

**Why first.** This tier seeded point-sets with `hash(name) % 10000`, and
Python salts string hashing per process, so its verdicts were not reproducible
between runs. Every external verdict it has issued is of unknown
reproducibility until this lands. A local eight-seed sweep found 2 of 20 specs
agreeing on only 4/8 and 5/8 while being reported as agreeing; the cause was
estimating the oracle's standard error from two seeds, which is chi-square with
one degree of freedom. That is fixed (five seeds, standard error of the mean),
and this job re-establishes stability on the cluster after the fix.

Any spec reported `FLICKERS` is withdrawn, not counted. A smaller honest number
is the goal.

## Job 2 — full tier re-run

```
python3 cluster/run_all.py > cluster/out_all.txt 2>&1
```

Runtime: roughly 10-20 minutes, dominated by the theorem sweep and the
mutation loops. Send back `cluster/out_all.txt` and every `results_*.json`
plus `coverage.json` and `unreachable.json`.

Answers the question still outstanding: how many verdicts move after the
binder fix, and whether any of the 18 totality defects or the range escapes
evaporate. Prints an explicit before/after diff against the committed results
rather than just new totals.

**z3 is absent on the cluster.** `z3backend.decide_range` returns `no-z3` and
the tier falls back to interval branch-and-bound plus sampling. Every verdict
records `decided_by`, so a sampling negative is visibly not a proof — the
result is less precise and no less honest. Expect roughly 25 verdicts to move
from `proved` back to `inconclusive`. I do not think provisioning z3 is worth a
round trip against the stability sweep; if it becomes cheap, `pip install
z3-solver` into a user environment is all it needs.

## One change at a time

scipy being available may let some hand-rolled numerics go, but **do not swap
oracle implementations in the same run as a stability sweep.** The sweep exists
to isolate seed dependence, and a simultaneous numerics change would confound
it. Numerics changes go in a later, separate run.

## What each job reads and writes

| job | reads | writes |
| --- | --- | --- |
| `run_stability.py` | `sim_engines.py`, `check_simulation.py`, `defs.json` | `results_simulation_stability.json` |
| `run_all.py` | the Lean corpus, `defs.json` | `results_*.json`, `coverage.json`, `unreachable.json` |

Neither reads outside the repo, opens a network connection, or spawns
subprocesses.

## If a job fails

`run_all.py` prints a stage banner before each stage, so the last banner names
the stage that died. Send the tail of the output; every stage is independently
re-runnable via the module it wraps (`python3 check_ranges.py` and so on).
