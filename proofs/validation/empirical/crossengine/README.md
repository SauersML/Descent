# Cross-engine differential testing

Every empirical verdict in this corpus before this directory existed was
produced by **msprime**, a coalescent simulator. That is a single point of
failure twice over:

1. msprime's modelling assumptions — neutrality, the coalescent approximation,
   its particular demographic-model semantics — are baked into every verdict.
   A corpus claim that is wrong *in the same way msprime is idealised* reads as
   VALIDATED forever.
2. Most of the false verdicts this project has caught came from misusing
   msprime's API (`recombination_rate=0` giving one genealogy per replicate;
   `InfiniteAlleles()` without `discrete_genome=True`; heterozygosity divided
   by segregating sites rather than by the sequence). A second engine with a
   different API does not reproduce those in the same way.

This harness runs corpus claims under **forward, individual-based** simulators,
which realise selection, dominance, finite population size and drift — none of
which the neutral coalescent contains.

## What is here

| file | role |
| --- | --- |
| `engines.py` | engine adapters. Each declares its `kind` (`coalescent`/`forward`) and whether it can simulate `selection` and a `finite_population`. Adding a third engine is a class, not a rewrite. |
| `claims.py` | corpus bodies under test, each with **competitors on the same cells**, one of them (`PLANTED`) known-wrong by construction. |
| `run.py` | the battery. Writes `results.json` with engine provenance on every row. |
| `control.py` | the **neutrality control**. Writes `control.json`. |
| `provenance.py` | the deterministic, dependency-free source-text check. This is the only part that is gate-eligible. |

## This is not, and must not become, a CI gate

`run.py` and `control.py` are Monte-Carlo. Their verdicts are statistical, so at
any sample size they carry a false-failure rate, and a required check that fails
at random gets ignored — see the "WHAT IS NOT WIRED UP, and why" comment in
`.github/workflows/prover.yml`, whose first excluded bucket is exactly this one.
A forward simulator is slower and noisier than any suite listed there.

What *is* gate-eligible is the deterministic consequence: `provenance.py` reads
the committed `results.json` and the Lean sources and fails when a claim that
cross-engine measurement showed to be **restricted** has silently dropped its
restriction. That check is fast, deterministic, dependency-free, and it fails on
a real defect rather than on a random draw.

## Discipline these scripts enforce

* **Competitor on the same cells.** A body that agrees with a simulation proves
  nothing unless a *different* body, on the same cells, is rejected. If both
  match, or no competitor was carried, the MATCH is worthless.
* **Calibration in both directions.** `PLANTED` is the corpus body inflated 40
  percent; `run.py` exits nonzero if the instrument fails to reject it. Clean
  cells must produce no findings at gating severity.
* **The neutrality control.** Where a forward and a coalescent simulator *must*
  agree, a disagreement means the harness is broken, not the corpus. Run
  `control.py` before believing anything `run.py` prints.
* **Freshness.** Every engine's output must carry the `XSIM_CE_V1` guard string,
  which exists only in this source. A run that does not print it raises rather
  than returning a number, because an instrument that cannot report its own
  absence will report someone else's answer as its own.
* **Ne scaled down, compound parameters held fixed.** A forward simulation at
  `Ne = 10000` is a design error here. The cells sweep `4 N h s` by shrinking
  `N`, so the whole battery runs in seconds.
* **Carrier frequency, not summed mutation frequencies.** Under recurrent
  forward mutation at one site, infinite-sites frequencies double-count a gamete
  hit twice and exceed 1 once the site fixes — which is exactly the regime being
  probed. Carrier frequency is also what the corpus recursion models, since its
  `mu * (1 - p)` term makes new carriers only out of non-carriers.

## Environment recipe (MSI)

Nothing here runs on a laptop. On the cluster, under
`/projects/standard/hsiehph/sauer354/xsim`:

### SLiM 4.3 — built from source, about two minutes

```sh
cd /projects/standard/hsiehph/sauer354 && mkdir -p xsim && cd xsim
curl -sSL -o slim.zip https://github.com/MesserLab/SLiM/archive/refs/tags/v4.3.zip
unzip -q slim.zip
mkdir -p build && cd build
cmake -DCMAKE_BUILD_TYPE=Release ../SLiM-4.3
taskset -c 0-11 make -j 12          # binary at build/slim
```

Stock `cmake 3.26.5` and `gcc 8.5.0` on the compute nodes are sufficient; no
modules need loading. Point the harness elsewhere with `XSIM_SLIM=/path/to/slim`.

### fwdpy11 — a wheel, no compilation

```sh
cd /projects/standard/hsiehph/sauer354/xsim
/usr/bin/python3.12 -m venv fwenv
./fwenv/bin/pip install fwdpy11 msprime tskit scipy
```

Versions this harness was calibrated against: **fwdpy11 0.24.7, msprime 1.4.2,
numpy 2.5.1, scipy 1.18.0, SLiM 4.3**, Python 3.12.13.

The pre-existing `popgen_venv` has msprime but not fwdpy11; use `fwenv`.

### Running

```sh
cd /projects/standard/hsiehph/sauer354/xsim
taskset -c 0-19 ./fwenv/bin/python crossengine/control.py --engines msprime,slim,fwdpy11
taskset -c 0-19 ./fwenv/bin/python crossengine/run.py --engines slim,fwdpy11 --reps 8 --workers 20
```

`acn112`/`acn116` are shared; cap at ~24 cores or submit to a general partition.
