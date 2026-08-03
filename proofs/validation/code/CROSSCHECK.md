# Cross-check: Inflation.lean vs RflScan.lean / AxiomScan.lean

> **The four files this document compares no longer exist separately.**
> `Inflation.lean`, `RflScan.lean`, `AxiomScan.lean` and `LaunderingScan.lean`
> were merged into `proofs/validation/code/Check.lean`, where they are the
> INFLATION, RFL, AXIOMS and LAUNDERING scans of one `run_cmd`.
>
> The text below is left exactly as it was written, including its file names and
> its line-number citations. It is the RECORD OF A MEASUREMENT, and rewriting a
> measurement's subject to match a later tree is how a result comes to describe
> something nobody checked — which is the failure §3 of this very document is
> about. Read it as a description of the tree it names.
>
> §4 is the reason the merge happened. It records that the four detectors carried
> three disagreeing copies of the declaration filter; `Shared.DeclFilter` fixed
> two of them, and the merge fixed the rest by leaving exactly one caller of
> `Shared.userWritten`. The one behavioural change is noted in `Check.lean`'s
> header: the private copies did not exclude `eq_unfold`, so the AXIOMS and
> LAUNDERING denominators drop by a handful of generated lemmas.

Read-only comparison, 2026-08-03. No build was run and neither detector was
executed; this is source and stored output only.

## Summary

**The two detectors do not measure the same property, and their headline counts
were never comparable.** No theorem can appear in both Inflation's Pattern 1 and
RflScan's output — not as an empirical finding but as a fact about the code:
both strip lambdas and test the head constant of the proof term, and one demands
that head be a `Calibrator` Prop-field projection while the other demands it be
`Eq.refl`. The intersection is empty by construction. So the three requested
lists (found by both / only by first / only by second) do not exist, and no
member-level reconciliation is possible.

The cross-check that *is* possible is between the parts the three files
duplicate: the "was this written by a person" filter. There they disagree, and
the disagreement is real.

## 1. What each one actually detects

`proofs/validation/code/Check.lean` (committed 6e47789b) reports four
things over `Calibrator` declarations:

- **Pattern 1** — after stripping lambdas, the proof term's head is a projection
  of a `Prop`-valued field of a locally-declared structure. "The theorem is
  discharged by handing back the hypothesis it was given."
- **Patterns 2/3** — the proof term *mentions* such a projection anywhere, via
  `Expr.getUsedConstants`.
- **Pattern 4** — an assumption-carrying structure whose constructor `S.mk`
  appears in no user-written `def` or theorem value; i.e. nothing in the corpus
  exhibits an inhabitant.

`proofs/validation/code/Check.lean` reports theorems whose proof term,
under its binders, is headed by `Eq.refl` — the theorem closes by reflexivity.

`proofs/validation/code/Check.lean` (untracked, non-empty, complete)
reports the transitive axiom closure of every `Calibrator` theorem, `def` and
`opaque`, and fails on anything outside `propext`, `Classical.choice`,
`Quot.sound`. Its targets are `sorryAx`, `native_decide`, and locally declared
axioms.

Three distinct properties: *proof is the hypothesis*, *proof is reflexivity*,
*proof rests on an unpermitted axiom*. A theorem can have any combination.

## 2. The filter that took 332 to 12

`Inflation.userWritten` (Inflation.lean:66). It excludes a declaration when
`Name.isInternal` holds, when `Environment.isProjectionFn` holds, or when the
last name component is one of `mk, injEq, eta, sizeOf, noConfusion,
noConfusionType, rec, recOn, casesOn, brecOn, below, ndrec, toCtorIdx, ofNat,
sizeOf_spec, mk.sizeOf_spec, ext, ext_iff`.

The 320 excluded by it are, on the commit message's own account, Lean's
generated projection functions. The grounds are sound and not a matter of taste:
`R2DecompositionData.hVarYhat_pos` is a constant whose value *is* the projection
`hVarYhat_pos`, because that is the definition of a projection. It is not a
corpus author asserting a hypothesis as a theorem, and counting it as one is a
category error. The same filter took Pattern 4 from `0 of 104` to `2 of 104`,
for the symmetric reason: every structure receives `S.mk.injEq` and `S.eta`,
each of which mentions `S.mk`, so an unfiltered constructor scan marks every
structure as inhabited.

The filter is right. Its *calibration* against the other two files is not — see
§4.

## 3. Evidence status of every quoted count

**No stored output file exists for any of the three detectors.** A repo-wide
search for their own output markers (`PATTERN 1`, `theorems examined`,
`TOTAL_RFL_THEOREMS`, `AXIOM_SCAN_SCANNED`) matches only the source files that
print them. Every number in circulation — 3393, 104, 12, 354, 2 of 104, and
RflScan's 8 — lives in a commit message or a docstring and nothing else.

Two consequences, both load-bearing:

**(a) Three of the nine named specimens in commit 6e47789b did not exist in the
tree that commit describes.** `ObservableTower.vertex_weight`,
`ObservableTower.higher_cumulants_need_divergent_hub` and
`LDBandIntegralIdentification` appear nowhere in the repository at 6e47789b, nor
at HEAD, under those names or looser spellings (`vertex_weight`,
`divergent_hub`, `ldband`). Inflation.lean can only print names it read out of
the environment, so the result list in that commit message is not a transcript of
a run. The other six do check out at 6e47789b —
`GenotypeChaosLimits.geneBurden_gaussian_null`,
`gaussian_null_licensed_of_disjoint`, `CycleDeterminacy.cycles_determine`,
`divergence_phase`, the assumed field `disjoint_segment` (all in
`proofs/Calibrator/EpistaticChaos.lean`), and `LiabilityThresholdRegime`
(`proofs/Calibrator/PortabilityDrift.lean:2982`, then a real structure).

**(b) The surviving names have since been deleted.** `EpistaticChaos.lean` lost
those theorems in eda0f7e0, and `LiabilityThresholdRegime` is now only a prose
note at `proofs/Calibrator/PortabilityDrift.lean:2944` recording its removal.
55 commits separate 6e47789b from HEAD. The 12/354/2 figures describe a tree
that no longer exists and should not be quoted as current.

RflScan's own quoted result is stale in a different way: commit 5bef0c52's
"8 of 8 classified" was measured with the module allow-list
`rflScanModules`, ten popgen modules. The working tree has **deleted that
list** (uncommitted change), so the current file scans all of `Calibrator`. The
number 8 does not describe the file now on disk.

## 4. Where the two implementations genuinely disagree

Not on theorem membership — there is none to share. On the generated-declaration
filter, which all three files reimplement independently and none of which is a
superset of the other.

| | Inflation.userWritten | RflScan.rflScanIsGenerated / AxiomScan.isGenerated |
|---|---|---|
| internal test | `Name.isInternal` | `Name.isInternalDetail` (strictly broader) |
| equation lemmas `f.eq_1`, `f.eq_def` | **not excluded** | excluded (`startsWith "eq_"`) |
| `proof_*`, `match_*` | **not excluded** | excluded |
| projection functions | excluded (`env.isProjectionFn`) | **not excluded** |
| `mk`, `rec`, `recOn`, `casesOn`, `eta`, `ext`, `ext_iff`, `toCtorIdx`, `ofNat` | excluded | **not excluded** |
| `ndrec`, `noConfusion` | excluded | AxiomScan only; RflScan misses both |

**Which is right, per row.** Inflation is right about projections and
constructors, and RflScan's own docstring concedes the point it is missing:
eleven of its nineteen unfiltered hits were equation lemmas and friends, and its
author had to add `startsWith "eq_"` *alongside* `isInternalDetail` — meaning
`isInternalDetail` does not catch them, and Inflation's weaker `isInternal`
certainly does not either. So Inflation's 3393 "user-written theorems"
denominator includes every equation lemma in the corpus and is inflated. The
effect on Pattern 1 is nil (an equation lemma's proof is headed by `Eq.refl`,
not by a projection, so it cannot be a Pattern-1 hit); the effect is on the
denominator, and on Patterns 2/3 to whatever extent a `def` body mentions an
assumed field.

Conversely RflScan and AxiomScan will report `Foo.rec`, `Foo.casesOn` and
`Foo.ext_iff` as hand-written, which they are not. AxiomScan's is the milder
case, since those declarations have clean axiom closures and will not offend.

**Neither list is correct.** The union is closer to right than either, and the
fact that three files in one repository maintain three different answers to
"did a person write this" is the actual defect this comparison surfaces.

## 5. Two further defects in Inflation.lean, from source alone

- **`usesHits.size` is a count of pairs, not theorems.** The inner loop
  (Inflation.lean:140) pushes one `(theorem, projection)` entry per assumed
  field the proof mentions, so a theorem citing three assumed fields contributes
  three entries. The printed label says `354 theorem(s)` and the commit message
  repeats it. The true count of distinct theorems is ≤ 354 and unknown. Pattern 1
  is not affected: it pushes at most once per theorem, so 12 is a real theorem
  count.
- **The Pattern 2/3 list is truncated at 80** (`usesHits.toList.take 80`,
  Inflation.lean:163). The 354 can never be enumerated from the tool's own
  output, which is precisely the "a total with no members" failure this
  cross-check was asked to guard against.

## 6. Recommendation

Keep all three. They are complements, not competitors, and each catches a class
the others structurally cannot:

- **Inflation.lean** — *is the conclusion just an assumption handed back, and is
  the assumption bundle ever inhabited?* The only one that looks at semantic
  content. Sole detector of vacuity.
- **RflScan.lean** — *is the equality definitional?* Feeds `rfl_triage.py`,
  which is the only thing here with a pre-registered criterion. Note that
  rfl-provable is explicitly *not* the same predicate as vacuous, and
  `rfl_triage.py` says so at length; RflScan is a candidate generator, not a
  verdict.
- **AxiomScan.lean** — *did the kernel accept it, and on what?* The only guard
  against `sorryAx` and `native_decide`, and the only one of the three that
  belongs in CI: it exits nonzero, it has a fixed allow-list, and its failures
  are unambiguous. `proofs/validation/code/check.py` greps for the word
  `sorry`, which cannot see error-recovered sorries.

Three things to fix, in order:

1. **Make each detector write a stored output file** listing every hit by name,
   untruncated, with the commit it was measured at. Until then no count here is
   citable and this cross-check cannot be redone at the member level.
2. **Factor the generated-declaration filter into one shared definition** and
   use the union of the three current lists. Three answers to one question is
   how two tools reach different totals while looking equally authoritative.
3. **Relabel Pattern 2/3** as a pair count, or deduplicate it, and remove the
   `take 80`.

Until (1) is done, the correct statement about the 12/354/2 figures is that they
are unbacked and describe a 55-commit-old tree, and about RflScan's 8 that it was
measured over a module slice the current file no longer restricts to.
