# The coverage denominator, measured

Every number below was measured on 2026-08-03 against the working tree at

    source digest  sha256:af040c1051389bba03057a9a4519c119
    source files   116  (115 under proofs/Calibrator/ plus proofs/Calibrator.lean)

**The corpus moved three times while this was being measured.** The digest went
`73b56b2e` (the committed-adjacent `defs.json`) → `d8335639` → `fb3d1263` →
`af040c10` within about fifteen minutes, and the definition count went 1352 →
1356. Other agents are editing `proofs/Calibrator/` right now. Every count here
is therefore a count *at that digest*, and anyone quoting it must say so. A
denominator without a digest attached is not a measurement.

## Method, and what could not be measured

The extraction tables under `proofs/validation/empirical/extract/` (`defs.json`,
`lean_defs.py`, `classes.json`) were **stale**: the copy on disk carried
`source_digest sha256:73b56b2e…` over 115 files against a live tree of 116.
`api.require_fresh()` would have refused them, correctly.

`emit.py`, however, **does not need a built corpus**. It imports only `json`,
`math`, `pathlib`, `collections`, `random`, `re`, `sys`, plus the local
`admissible`, `lean_parse` and `translate`. There is no `subprocess`, no `lake`,
no `.olean`. It is a pure text parser over `proofs/Calibrator/*.lean`.

So rather than consume the stale table, and rather than run `emit.py` (which
writes `lean_defs.py` and `defs.json` into a shared checkout that another agent
already has modified), the census below **replicates `emit.py` main() in
memory** — `lean_parse.build` → `lean_parse.to_json` → `emit.build_context` →
`translate_def` per definition — and writes nothing into the worktree. It
reproduces the coverage tooling's own published split exactly (212 / 68), which
is the check that the replication is faithful.

**What could not be measured here, and why:**

* The **3031 hand-written theorems** figure. That string appears nowhere under
  `proofs/`. It is not reproducible from the tree and this document does not
  adopt it. If it came from a Lean-side detector walking the `Environment`
  through `Shared.DeclFilter.userWritten`, it counts a different population than
  a source parse does — the environment contains declarations from `import`ed
  modules and from `deriving` clauses that never appear as a keyword in a
  `.lean` file. **Resolving the 2755-versus-3031 gap requires a Lean build**,
  which this workstation may not do. The measurement that would settle it: run
  the existing detector and have it print, per declaration, the file it came
  from, then diff that name set against the source parse.
* The **1219 definitions across 105 modules** figure. Also appears nowhere
  under `proofs/`. Not adopted.
* Two declarations fail the parser (`TransportIdentities.lean:40` and
  `Calibrator.lean:270`, both anonymous `instance`s). Both are instances, not
  definitions or theorems, so neither belongs in any denominator below.

---

## 1. What exactly is the slice?

**File:** `proofs/validation/empirical/differential/coverage.py:29`, and the identical
list at `proofs/validation/empirical/differential/cluster/families.py:63`.

**Predicate:** `d.get("file") in SLICE_FILES` — `coverage.py:118`
(`slice_definitions`) and `families.py:1598` (`in_slice_fq`).

**The inclusion rule in one sentence:** a statement is *in the slice* if and
only if it is a `def` or `abbrev` declared in one of seven hard-coded Lean
source files.

The seven files, with their live declaration counts:

| file | defs | theorems |
|---|---:|---:|
| Calibrator/PortabilityDrift.lean | 161 | 226 |
| Calibrator/DGP.lean | 83 | 72 |
| Calibrator/PopulationGeneticsFoundations.lean | 26 | 103 |
| Calibrator/LDDecayTheory.lean | 16 | 53 |
| Calibrator/DemographicHistory.lean | 13 | 35 |
| Calibrator/PhenomeWidePortability.lean | 5 | 23 |
| Calibrator/PortabilityBounds.lean | 1 | 13 |
| **total** | **305–306** | **525** |

The definition column measured 305 at digest `fb3d1263` and 306 at `af040c10`
minutes later; the theorem column was measured once, at `fb3d1263`. The file
counts are being edited under the measurement. This is the drift warning, made
concrete.

Three things follow, and each one invalidates a class of percentage that has
been quoted:

1. **The slice is a file list, not a property.** Nothing about a declaration
   decides its membership. Seven filenames do. A definition making exactly the
   same claim in `Conventions.lean` is out.
2. **The slice contains no theorems.** `coverage.py` iterates
   `api.definition_table()`; `families.py` iterates `blob["definitions"]`.
   The 525 theorems in the same seven files are outside every published
   coverage percentage.
3. **The reported 302 is this number at an earlier digest.** Live it is
   305–306. So "302 in-slice statements" is not a filtered subset of anything —
   it is the raw definition count of seven files, and the 212/68/22 split
   partitions exactly those.

---

## 2. How many declarations does the corpus contain?

Fresh source parse, all 116 files:

| kind | count |
|---|---:|
| `def` | 1341 |
| `abbrev` | 11 |
| **definitions** | **1356** |
| `theorem` | 2747 |
| `lemma` | 8 |
| **theorems** | **2755** |
| `structure` | 117 |
| `inductive` | 5 |
| **structures** | **122** |
| **total declarations** | **4233** |

**All 4233 are hand-written**, and this is not an assumption — it follows from
`proofs/validation/Shared/DeclFilter.lean`, whose definition of hand-written is
used here rather than a new one. `Shared.isGenerated` excludes exactly six
things: `Name.isInternalDetail`, `Environment.isProjectionFn`, the `proof_`
prefix, the `match_` prefix, `isEquationLemma`, and the eighteen
`generatedComponents` (`mk`, `injEq`, `rec`, `casesOn`, `noConfusion`, …).
**Every one of those six is a name Lean synthesises into the environment; none
of them can appear after a `def`, `theorem` or `structure` keyword in a source
file.** A source-level census is therefore already the hand-written census, and
`Shared.DeclFilter` is what licenses saying so. The corollary is that the 122
`structure` declarations generate field projections that `DeclFilter` excludes
and the source parse never sees — the two agree.

The one population where source parsing and `DeclFilter` can genuinely diverge
is the environment-only declarations noted above, which is the unresolved
2755-vs-3031 gap.

---

## 3. How many make an empirically checkable claim at all?

**This is the number that matters. It is the true denominator for "100 per cent
of every claim covered by simulation."**

### The rule

A declaration makes an empirically checkable claim if **it denotes a real
number, a vector or matrix of reals, or a structure whose fields are reals** —
because only then is there a quantity that a generative process could produce a
*different* value for.

This is the corpus's own rule, not a new one: it is test **F1** in
`families.py:1446` (`falsify_unsimulatable`), whose marker set is
`("ℝ", "Matrix", "Profile", "Set ℝ")`. It is applied here structure-aware —
a definition returning `HardyWeinbergModel` or `CalibrationProfile` counts as
real-valued, because the structure's fields are reals — which the flat string
match approximates with the ad-hoc `"Profile"` entry.

**Theorems are deliberately excluded from the denominator, and this is a
substantive choice.** A Lean theorem is proven; its truth is not in question.
What is in question is whether the *definitions* it relates describe the world.
The empirical content of `hudsonFst_eq_of_neiGst` is entirely the empirical
content of `hudsonFst` and `neiGst`. Counting the 2755 theorems into the
denominator would double-count the 1229 definitions they are about, and would
make the target unreachable by construction. If a future revision wants a
theorem-level denominator, the defensible subset is theorems asserting a
numeric bound with literal constants against an assumed model — that subset is
measurable from the same parse and has not been measured here.

### The count

| | defs |
|---|---:|
| total definitions | 1356 |
| **REAL — carries a real-valued claim** | **1229** |
| NONE — `Prop`, `ℕ`, `Bool`, `Type`, `Set`, `Finset`, `Fin` | 85 |
| UNKNOWN — needs a human call | 42 |

The 85 in NONE are the category errors the brief anticipated: 65 return `Prop`,
the rest return naturals, index types or finite sets. Demanding a simulator for
`Calibrator.Covers` or a `Fin t` index construction is asking what population a
proposition is a claim about, and there isn't one.

The 42 UNKNOWN are mostly `ProbeBlindness …` instances and equivalences
(`≃`) — structural witnesses. They should be adjudicated by hand; they cannot
move the headline by more than 3 per cent either way.

### A second, stricter reading, and why it is a floor rather than the answer

Of the 1356 definitions, `emit.py`'s translator can currently turn **954** into
an evaluable Python function; **398** it refuses. Intersecting with
real-valuedness gives **929**.

**929 is a floor, not the denominator.** The refusal reasons are translator
limitations, not absence of empirical content — 116 are "trailing tokens after
expression", 37 "matrix/vector literal", 16 "unrecognised character `.`", 9
"unsupported token `{`". Only the 24 "measure-theoretic integral" refusals and
the 4 "∑ over an unannotated index" are arguably about the claim rather than
about the parser. So:

> **The empirically checkable set is 1229 definitions.** 929 of them are
> evaluable by the existing extraction today; the 300-definition gap is
> translator work, not claim triage.

### What this does to the published percentages

Of those 1229, the slice holds **297**. The 212 in-slice statements that sit in
a simulated family are therefore

* **71 per cent** of the empirically checkable statements *in the slice*, and
* **17 per cent** of the empirically checkable statements *in the corpus*.

Any percentage quoted against 302 or 306 is a percentage of seven filenames.

---

## 4. Outside the slice, inside the empirically checkable set

**932 definitions across 100 modules.** This is the uncovered surface. Nothing
in `coverage.py` or `families.py` looks at any of it; it is not "unaccounted",
it has never been in a denominator at all.

The top of the distribution — the first eleven modules are a third of the work:

| module | checkable defs | cumulative |
|---|---:|---:|
| PGSCalibrationTheory.lean | 71 | 71 |
| TransferLearningPGS.lean | 50 | 121 |
| Permeability.lean | 35 | 156 |
| PCCorrectability/ImitationCapacity.lean | 28 | 184 |
| Probability.lean | 26 | 210 |
| TransportIdentities.lean | 26 | 236 |
| MetricSpecificPortability.lean | 25 | 261 |
| EpistaticChaos.lean | 24 | 285 |
| PolygenicArchitecture.lean | 24 | 309 |
| StratificationConfounding.lean | 24 | 333 |
| Conclusions.lean | 23 | 356 |

then, in descending order: ImitationRigidity 19, SimulationValidation 19,
ConditionalGain 18, CertificateGrading 16, CondensationUnification 16,
EnsembleChannel 16, FoldedSpectrum 16, GeneticArchitectureDiscovery 16,
AssortativeMatingPGS 14, HaplotypeTheory 14, ProjectionShiftBounds 14,
BayesianPGSTheory 13, and a long tail: 75 of the 100 modules hold 12 or fewer
checkable definitions, and 47 hold 5 or fewer.

The full 100-row table is reproducible in about eight seconds from the script
described in the Method section; it is not pasted here because it goes stale
within the hour.

**How to divide this.** The eleven modules above are 356 of the 932, and each
is large enough to be one agent's family-assignment job. The 51 modules with
five or fewer checkable definitions should be swept in one pass rather than
assigned individually (47 modules, 5 or fewer each) — at that size the
per-module overhead exceeds the work.
`Conclusions.lean` (23) deserves priority out of proportion to its size: a
definition in a file called Conclusions is one that gets quoted.

---

## 5. The statements in no family at all

**They are inside the slice.** `families.py:1658` computes them as
`in_slice_fq - claimed_fq - unsim_fq` — in-slice by construction, minus those
claimed by a family, minus those parked as un-simulatable. At the measured
digest there are **26**, not 22; the count moved with the corpus.

Note also that the "parked as un-simulatable" term is now **zero**: all four
entries on `families.py`'s `UNSIMULATABLE` list have had their falsifiers fire
and are recorded as LOST. That list is currently doing no work, and the
un-simulatable category is empty. That is the honest state, and it is what the
falsifier was written to expose.

The 26, and what assigning each would take:

**(a) Eight structure-instance witnesses** — `CrossPopulationMetricModel.witness`,
`EvolutionaryParameters.witness`, `HWEPolygenicScoreDGP.witness`,
`MutationDriftModelAssumptions.witness`, `PGSEvolutionaryModel.witness`,
`PrevalenceDGP.witness`, `SplitMigrationModel.witness`,
`TransportedMetrics.IrreducibleTargetPenalty.witness`. Each pins concrete real
parameter values proving its model's assumptions are inhabitable. **Assignment
is mechanical: each belongs to whichever family owns its structure.** They are
unassigned only because family membership is keyed on short names and nothing
matches `witness`.

**(b) Ten liability-threshold definitions** — `liabilityThreshold`,
`liabilityCaseMean`, `liabilityCaseVariance`, `liabilityControlMean`,
`liabilityControlVariance`, `standardNormalPdf`,
**`liabilityThresholdAUCFromExplainedR2`**,
**`TransportedMetrics.equalVarianceGaussianAUCFromSignalVariance`**,
`neutralAFBenchmarkLiabilityMetricProfile`,
`targetLiabilityAUCFromNeutralAFBenchmark`. Every one belongs to
**`liability_threshold_metrics`, which already has a simulator**
(`cluster/fam_metrics.py`, liability arm) that already measures both the
equal-variance Gaussian AUC and the liability-threshold AUC across prevalence.
The two the brief names are in this group. Assigning them is a membership-list
edit, not new simulator work — though the simulator must then be re-run so the
credit is earned rather than asserted.

**(c) Three finite-deme island corrections** — `finiteIslandCorrection`,
`islandDemeCorrection`, `islandFstFiniteDemes`. These belong to
**`island_migration_fst`**, whose simulator `cluster/fam_coalescent.py` already
varies the deme count. Sharper than that: the standing complaint against that
family is that the simulator varies a deme count *no member takes as an
argument* — and these three are precisely the members that do take it. They are
the missing link, and they are unassigned.

**(d) `admixedFstExact`** → **`admixture`** (simulated). The family already
covers `admixedFst`, and `admixedFstExact` is that quantity divided by the
heterozygosity ratio — the denominator correction the family's own status note
says the simulator now decomposes.

**(e) `steppingStoneMeetingTimeOnLattice`** → **`stepping_stone`** (simulated).

**(f) Three DGP moment definitions** — `signalVariance`, `outcomeMeanVariance`,
`signalOutcomeCovariance` → **`estimator_moments`** (simulated).

**The finding: all 26 route to families that already have simulators.** None of
them needs a new generative process. What they need is membership entries and a
re-run. That is a day of work, not a research programme — and until it is done
those 26 are counted as blind spots when they are bookkeeping.

---

## What 100 per cent would actually require

**1229 empirically checkable definitions, of which 212 are currently in a
simulated family — so 1017 remain, and they need roughly 30 more simulators:
the 26 unfamilied and 68 unsimulated-family statements are absorbed by the 6
existing families that lack one plus a membership pass costing nothing new,
while the 932 checkable definitions outside the slice across 100 modules have
never been classified at all and will need on the order of 25 new families with
one simulator each.**
