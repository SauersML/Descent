# Symbolic checks over `proofs/Calibrator`

Reads definition bodies and theorem statements and asks whether the algebra
says what the names claim. Where the other tiers sample a definition's
behaviour, these read its body — so a quantity that is invisible to every
admissible measurement is still reachable here if any theorem mentions it.

## Running

Never locally. On the cluster, via the relay:

    /Users/user/msi-node/msi 'cd /projects/standard/hsiehph/sauer354/gnomon \
      && git pull -q --ff-only origin main \
      && bash proofs/validation/symbolic/cluster_run.sh smoke'   # ~2 min

    ... cluster_run.sh          # full pipeline, ~15 min

`smoke` runs the 21 regression assertions and decides in two minutes whether
the interpreter and sympy version behave as the checks expect. Run it first.

## Where the results go

**Generated JSONs are not in git.** They are build products: derived,
regenerable, and large. They are written to

    /projects/standard/hsiehph/sauer354/gnomon-artifacts/symbolic/

which every tier can read, since every tier runs on the cluster. Override with
`$GNOMON_ARTIFACTS`; a run on a machine without the shared path falls back to
this directory so a local run still works and is visibly local.

This replaced committing them. The cluster checkout has no push credentials, so
the in-repo copies went stale on every run — and a stale artifact that still
parses is indistinguishable from a current one. Putting credentials on a shared
node to fix that would be a standing security cost for a one-time convenience.

For a comparison against a fixed point in time, copy a snapshot deliberately
with the revision in the filename. Do not commit it.

| artifact | contents |
| --- | --- |
| `slice_ledger.json` | every definition claiming a derivation, equilibrium or closed form: VERIFIED / REFUTED / UNREACHABLE-with-reason, keyed by fully-qualified name |
| `reconciled_coverage.json` | the cross-tier union, overlap and complement; `single_tier` is the list others join against |
| `findings.json` | every disagreement and gap, keyed by fully-qualified name, with severity |
| `results_check1..7.json` | per-check detail |
| `results_homonyms.json` | duplicate fully-qualified declarations |

## The guard that needs no build

    python3 homonyms.py     # exits 1 if a name is declared twice

One second, no sympy, no Lean. A duplicate fully-qualified declaration does not
compile. It must read raw declaration headers rather than any name-keyed table,
because a dict keyed by name cannot represent a collision — the count is zero by
construction. This is why the scan is not folded into the shared extract API.

## The rule the numbers obey

A definition counts as covered only where a check **can fail**, demonstrated by
a perturbed body the check rejects. A check that passes but survives every
mutation is recorded UNREACHABLE with that reason, never VERIFIED. Perturbations
include a shape-changing argument transposition, because every value-moving
perturbation is rejected by a theorem that pins a single point while
constraining nothing about the form.

## Join keys

Fully-qualified `name` primary, `decl_name` secondary. Short names and line
numbers are **not** keys: several agents edit continuously, so a line-based join
produces what looks like a parse disagreement and is revision skew.
