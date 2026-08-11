# The two-locus cross-deme LD derivation: sources, forms, and run records

These are the working artifacts behind the exact two-locus LD results the
`ldRetentionAt` slot is owed. They are committed because a docstring cannot cite
a scratch directory on a cluster, and because a pre-registration's checksum means
nothing if the file it pins is not in history.

## READ THIS BEFORE CITING ANYTHING HERE

**Not everything in this directory is runnable as it stands, and the difference
matters.** Files are one of three kinds and the kind is stated per file below:

* **RUNNABLE, no special dependencies** — re-derives its result on any machine.
  There is exactly one, and it is the one to cite when a reader must be able to
  follow the citation: `../ldchain_reduction.py` (in the parent directory, with
  its `../ldchain_reduction.json`). Pure standard library, exact rational
  arithmetic, vendors the state space it needs.
* **SOURCE, as run** — the exact file that produced the log beside it, kept
  unedited so the log has a provenance. These import `argcore` and variously
  require `sympy`, `numpy`, `scipy`, `msprime` or `moments`. `argcore.py` is now
  committed one directory up (`../argcore.py`, byte-identical to the MSI original
  at md5 `d2861c207fe7ff9779c01cc8a47f5f14`), so the import is satisfiable — but
  these files still carry the absolute `sys.path.insert` of the cluster working
  directory they were run from, and that line is deliberately **not** edited,
  because a file kept as the provenance of a log must stay the file that produced
  it. To run one, point that path at `..` yourself. They are committed as the
  record of what was executed, not as a turnkey reproduction path.
* **RECORD** — output. A log or a set of forms. Nothing to run.

If you need a followable citation for the falsified two-deme reduction, cite
`../ldchain_reduction.py` and `../ldchain_reduction.json`, which recompute the
same system with no dependencies beyond the standard library.

The shared machinery both live above this directory: `../lumping.py` (the
enumeration, the symmetry lumping, and the verification that makes lumping a
proof — standard library only, with a self test) and `../argcore.py` (the
original numpy/scipy implementation, kept as authored). `../lumping.py`'s self
test checks the two enumerations agree, so the duplication cannot drift.

## The files

### The closed form and its evidence
* `ld2evidence.py` (SOURCE) / `ld2evidence.log` (RECORD) — **the single traceable
  evidence file** for the exact two-deme equilibrium closed form. One run
  produces the derivation, 18 gated assertions, and both checks with their
  figures. Supersedes `ld2deme2.py`'s split evidence. The gates include the
  Strobeck/Nagylaki invariance falling out rather than being imposed, exact
  lumpability on all 56 ancestral configurations, an exactly-zero residual on the
  full 56-equation system, and the Ohta-Kimura limit recovered symbolically as
  `M -> oo`. Headline figures in the log: solve check 5.686e-12, moments.LD
  agreement 1.001e-08.
* `ld2deme2.py` (SOURCE) / `ld2deme_forms.txt` (RECORD) — the earlier derivation
  run and the closed forms it wrote: `sigma_d^2` within and across demes and the
  LD correlation `rD`, as ratios of explicit integer polynomials in `(rho, M)`,
  in both `srepr` and readable form.

### The stepping-stone extension
* `ldchain.py` (SOURCE) — the same system on an `n`-deme linear stepping stone,
  with `M` optionally specialised to an exact rational so the answer stays an
  exact rational function of `rho` alone. The two-symbol solve stalls on
  expression swell at `n >= 3`; the specialisation is what makes it tractable.
* `ldchain{3,4}_M{12,18over5}_forms.txt` (RECORD) — the resulting exact forms at
  serial1d's per-edge `4Nm = 12` and grid2d's `18/5 = 3.6`.
* `reduction.py` (SOURCE) — the two structural tests: the geometric distance law
  and the F_ST-matched two-deme surrogate. **Its conclusions are the ones
  reimplemented dependency-free in `../ldchain_reduction.py`; prefer that file.**

### The post-split (non-equilibrium) law
* `ldtransient.py` (SOURCE) / `ldtransient.log` (RECORD) — the closed-form
  post-split law. A split supplies an exact initial condition, so no integration
  is needed. Both endpoint gates pass: `rD = 1` at zero split age and the
  equilibrium rational function recovered at infinite age. **This answers the
  TIME axis only** — how far a split of finite age sits from its equilibrium —
  and says nothing about whether a two-deme law describes a many-deme lattice,
  which is the separate structure axis and is open.

### The two dimensional question
* `ld2d_prereg.md` (RECORD, **do not edit**) — the pre-registration of the pass
  criteria for whether the two-locus object inherits the one-locus
  isolation-by-distance operator in 2-D. md5 `ae7c6da9739b718ba348a5a60c7dc5e2`.
  Filed before any 4x4 or 5x5 output existed; the filing command printed the
  contemporaneous log tail as proof. Any edit to this file destroys its purpose.
* `ld2d.py` (SOURCE) / `ld2d.log` (RECORD) — the 2-D lattice solves. **The
  Bessel column in the 3x3 block of this log is uninformative and must not be
  quoted**: a 3x3 lattice measured from the centre yields two distances against a
  two-parameter form, so the fit has zero degrees of freedom and cannot fail
  (scipy says so in the log — "Covariance of the parameters could not be
  estimated"). The geometric column over the same points *is* informative,
  because it fits one parameter to `d=1` and then predicts `d=2` with no freedom
  left; it fails by 26-57%, which is the result.

### The exact pairwise tables for the gnomon demographies
* `pairF.py` (SOURCE) — integrates the structured pair coalescent through each
  demography's real event schedule, reading the demography constructors from the
  gnomon generator.
* `pairF_serial1d.csv`, `pairF_grid2d.csv` (RECORD) — Hudson `F_ST` for **every
  deme pair**, 10x10 and 36x36. These are the shared asset: a per-distance mean
  is not an edge property, and anything nonlinear in divergence must be evaluated
  per pair on these tables and mixed afterwards, never evaluated at a mixed mean.
* `pairT2_serial1d.csv`, `pairT2_grid2d.csv` (RECORD) — the mean pairwise
  coalescence times, in generations, that those `F_ST` are computed from.

## Conventions, used identically everywhere above

Deme diploid size `N`; time in units of `2N` generations; `rho = 4*N*c` and a
block carrying units of both loci splits at `rho/2`; `M = 4*N*m` per edge and a
block hops to each adjacent deme at `M/2`; two blocks in one deme coalesce at
rate 1.

## What this directory does not contain

A law for the 2-D lattice. The 1-D geometric law is falsified there and the
Bessel replacement is untested; `ld2d_prereg.md` states what would settle it.
