# Cluster runbook — invariants tier

All jobs are pure Python + numpy, single process, no builds, no tree copies.
Peak memory is a few hundred MB (one simulated haplotype pool of 1.5e6 int8).
Nothing here writes outside `proofs/validation/invariants/`.

## Getting the clone current — GIT MUST NEVER EDIT

Runs happen in a private clone at `/projects/standard/hsiehph/sauer354/ranges_wt`
so they do not race other agents' merges in the shared checkout. A private
clone that never updates diverges silently and starts testing a revision
nobody else has, so it must be brought current before every run — but **not
with a command that mutates tracked content.**

```
cd /projects/standard/hsiehph/sauer354/ranges_wt
git fetch origin
git merge origin/main          # NEVER `git reset --hard`
```

**`git reset --hard` is forbidden, with any argument, on any tree.** So are
`git checkout -- <path>`, `git restore`, `git clean`, `git stash` and
`git revert`. Git is for commit, push, and reading history. To change a file,
edit the file. `git show <rev>:<path>` to READ old content is fine.

I used `git reset --hard origin/main` here earlier and it was wrong. It is the
leading suspect for a new module file that vanished from the shared cluster
tree today: a hard reset against a stale ref deletes exactly the files added
after that ref while sparing established ones, so it looks harmless right up
until it isn't.

Recording the revision with every result (below) is the other half of the
defence, and it is now the only one that does not involve git touching files.

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

## Results do not come back on their own

**The cluster is write-only compute.** Its checkout has no push credentials, so
anything produced there exists in exactly one place until it is pulled back
deliberately. Another agent had seven result files living only on MSI for an
entire session, surviving repeated hard resets purely because untracked files
are spared.

```
bash cluster/fetch_results.sh      # -> cluster/runs/, plus REVISION.txt
```

Run it after every job, and commit what it brings back. "It is on the cluster"
is one copy, not a backup.

Note what it reports ABSENT: a job that writes its results only at the end has
nothing to retrieve until it finishes, so a crash loses everything it did. The
stability sweep has this shape and the next version writes per spec.

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
