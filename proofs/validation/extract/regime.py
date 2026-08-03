"""The SECOND coverage metric: model validation, not internal consistency.

There are two different questions, and reporting one as though it answered both
is how a corpus ends up fully covered and still wrong.

  INTERNAL CONSISTENCY (coverage_v2.py)
      Does a check notice if the body is perturbed?  Catches transcription
      errors, algebra errors, range escapes, broken derivations.  It is
      DEFINITIONALLY BLIND to a body that is exactly what its author intended
      and answers the wrong question: every mutant is wrong in the coordinate
      the definition is right in, so every mutant dies and the check passes.

  MODEL VALIDATION (this script)
      Does the quantity computed match something measured outside the
      development, and under what modelling assumptions is it claimed to hold?
      This is the metric `hetRecurrence` fails.  That definition is
      algebraically correct everywhere; its docstring quotes 0.9048 / 0.6065 /
      0.1353 as VALIDATED, and those numbers ARE correct -- for a closed
      population with no mutation.  It is cited about a population at
      mutation-drift equilibrium, where the true retention is 1.0.  No amount of
      mutation testing reaches that.

Two facts are mined per definition:

  REGIME   the modelling assumptions under which the definition is claimed to
           hold -- closed population, no mutation, linkage equilibrium, weak
           selection, large Ne.  NOT the `Empirical status:` marker: that
           records whether a NUMBER was checked, the regime records which WORLD
           it was checked in.  A definition can be `VALIDATED` and carry no
           regime at all, which is precisely the failure above.

  EXTERNAL an outside reference the definition has been compared against -- a
           simulation, an analytic expectation from an independent derivation,
           or a published estimator -- and under which regime.

The cell that matters is INTERNALLY VALIDATED AND NO DECLARED REGIME: bodies
that pass every mutant, look healthy on the dashboard, and carry no recorded
statement of the world they describe.  That cell is a defect inventory.

    python3 validation/extract/regime.py [--json regime.json]
"""

# REGENERATE WITH:  python3 proofs/validation/extract/regime.py
#
# This produces regime.json, which are NOT IN GIT.
# They are generated from proofs/Calibrator/, which changes every few
# minutes, and a committed snapshot drifts by six figures -- defs.json
# measured 122994 changed lines against its last committed copy. A cache
# that far from its source is not a cache, it is a second source of truth
# that disagrees with the first. Run this in your own worktree
# immediately before use, so your numbers are pinned to the revision you
# are standing on.
from __future__ import annotations

import argparse
import collections
import json
import pathlib
import re
import sys

HERE = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))

import api                                                # noqa: E402

PROOFS = HERE.parent.parent

# An explicit marker, on the pattern of `Empirical status:`.  Nothing in the
# corpus writes this yet; recognising it means the corpus CAN start declaring
# regimes explicitly instead of relying on prose being mined.
EXPLICIT_RE = re.compile(r"(?:Regime|Model|Assumes|Valid under|Modelling assumptions)\s*:\s*"
                         r"([^\n]+)", re.I)

# Modelling assumptions this corpus actually makes, as they are written in the
# docstrings.  Mined from prose, so this is a LOWER bound on how many
# definitions have a regime in the author's head and an upper bound on how many
# have one a reader can find.
REGIME_PATTERNS = [
    ("closed-population", r"closed population|no migration|isolated population|"
                          r"without migration|single population"),
    ("no-mutation", r"no mutation|without mutation|mutation[- ]free|ignoring mutation|"
                    r"absent mutation"),
    ("mutation-drift-equilibrium", r"mutation[- ]drift (?:balance|equilibrium)|"
                                   r"infinite[- ]alleles|stationary distribution"),
    ("neutral", r"\bneutral(?:ity)?\b|no selection|absence of selection"),
    ("weak-selection", r"weak selection|small s\b|selection coefficient is small"),
    ("linkage-equilibrium", r"linkage equilibrium|\bLE\b|unlinked|independent loci"),
    ("linkage-disequilibrium", r"linkage disequilibrium|\bLD\b"),
    ("hardy-weinberg", r"hardy[- ]weinberg|\bHWE\b|random mating"),
    ("additive", r"\badditive\b|no dominance|no epistasis|purely additive"),
    ("large-Ne", r"large N_?e|infinite population|diffusion (?:limit|approximation)|"
                 r"large[- ]sample"),
    ("biallelic", r"biallelic|two alleles|\bSNP\b"),
    ("gaussian", r"gaussian|normal(?:ly)? distributed|normality"),
    ("equal-variance", r"equal[- ]variance|homoscedastic"),
    ("island-model", r"island model|stepping[- ]stone|migration matrix"),
    ("constant-Ne", r"constant (?:N_?e|population size)|stationary demography"),
    ("discrete-generations", r"discrete generations?|non[- ]overlapping generations?"),
    ("large-effect-approximation", r"first[- ]order|linearis|linearz|small[- ]angle|"
                                   r"leading order|to first order"),
]

# Words indicating a comparison against something OUTSIDE the development.
EXTERNAL_MARKERS = [
    ("simulation", r"\bslim\b|\bmsprime\b|simulat|forward[- ]time|coalescent simulation|"
                   r"monte[- ]carlo"),
    ("analytic-reference", r"closed[- ]form|exact (?:expression|value|solution|trajectory)|"
                           r"analytic(?:al)? (?:reference|expectation|result)"),
    ("published-estimate", r"\bet al\.|\b(19|20)\d\d\)|published|reported in|"
                           r"catalogue|catalog|empirical(?:ly)? (?:observed|measured)"),
]


def mine_regime(d):
    doc = d["docstring"] or ""
    explicit = [m.group(1).strip() for m in EXPLICIT_RE.finditer(doc)]
    mined = [name for name, pat in REGIME_PATTERNS if re.search(pat, doc, re.I)]
    return explicit, mined


def mine_external_claim(d):
    doc = d["docstring"] or ""
    return [name for name, pat in EXTERNAL_MARKERS if re.search(pat, doc, re.I)]


# Which checking layers produce EXTERNAL evidence and which produce INTERNAL.
# This distinction is the whole point of the metric, so it is recorded in code
# rather than inferred: a layer that checks a definition against the corpus's
# own theorems is doing internal consistency, however rigorously, and counting
# it here would fold metric one back into metric two.
EXTERNAL_TIERS = {
    "differential": "analytic-reference",   # closed forms derived independently
    "popgen_defs": "simulation",            # SLiM / coalescent simulation
    "pc_correctability": "simulation",
    "condensation": "simulation",
    "imitation_rigidity": "simulation",
}
INTERNAL_TIERS = {"extract", "invariants", "symbolic"}

# Verdicts that record an absence of checking rather than a check.
NON_VERDICTS = {"not-transpiled", "no-range", "inconclusive", "skipped",
                "unavailable", "not-extractable", "uncovered", "n/a", "none",
                "NOT-EXTRACTABLE", "UNCOVERED", "not_extractable"}


# Evidence classes a producing tier may declare per record, in `evidence_class`
# (or `demonstration`).  An explicit declaration always beats the directory
# heuristic below, because a directory is a guess about a tier and this is a
# statement about one record -- and a tier can produce several kinds at once.
EXTERNAL_EVIDENCE = {
    "simulation", "simulation-mutant-rejected", "analytic-reference",
    "published-estimate", "external-reference",
}
INTERNAL_EVIDENCE = {
    "internal-consistency", "theorem-derived", "self-property",
    "range", "invariant", "mutation",
}


def _declared_class(node):
    """The evidence class a record declares for itself, if any.

    Returns (class_name, is_external) or None when the record says nothing.
    An UNRECOGNISED declaration is treated as NOT external: a name I do not
    know is not a licence to count it as contact with reality.
    """
    for key in ("evidence_class", "demonstration", "evidence"):
        v = node.get(key)
        if isinstance(v, str):
            return v, v in EXTERNAL_EVIDENCE
    return None


def external_checks():
    """Definitions actually compared against an OUTSIDE reference.

    Evidence is a machine-readable verdict naming the definition, not a mention:
    a name appearing in a source file proves nothing, which is the flaw in the
    old coverage script.  And only evidence that compares against something
    outside the development counts -- a range check against the corpus's own
    theorems, or a theorem-derived property test, is internal consistency
    however rigorous, and counting it here folds metric one back into metric
    two.  That mistake put this figure at 42.3% instead of 4.0% once already.

    Two sources of truth, in priority order:
      1. a per-record `evidence_class` / `demonstration` declared by the tier
         that produced it -- authoritative, because a tier can produce several
         kinds of evidence and only it knows which is which;
      2. failing that, the directory heuristic below, which is a guess about a
         whole tier and is wrong the moment a tier adds a second kind.
    Anything unrecognised is NOT counted as external.
    """
    hits = collections.defaultdict(set)
    declared_internal = collections.defaultdict(set)
    seed_state = collections.defaultdict(set)
    for path in (PROOFS / "validation").rglob("*.json"):
        if path.is_relative_to(HERE):
            continue
        tier = None
        for part in path.parts:
            if part in EXTERNAL_TIERS:
                tier = EXTERNAL_TIERS[part]
            elif part in INTERNAL_TIERS:
                tier = None
                break
        try:
            blob = json.loads(path.read_text())
        except Exception:                                       # noqa: BLE001
            continue
        tag = path.parent.name

        def walk(node, depth=0, key=None):
            if depth > 6:
                return
            if isinstance(node, dict):
                # The definition name may be a FIELD of the record, or the KEY
                # the record is filed under (invariants/coverage.json does the
                # latter, with no name inside the record at all).
                name = (node.get("definition") or node.get("name")
                        or node.get("def") or key)
                verdict = (node.get("verdict") or node.get("status")
                           or node.get("result") or node.get("class")
                           or node.get("demonstration"))
                if verdict is None and node.get("covered") is True:
                    verdict = "covered"
                # A Monte Carlo verdict that depends on the seed is not a
                # verdict.  A tier may attest that it re-ran the check across
                # independent point-sets:
                #     "seed_stability": {"seeds_tried": 8, "seeds_agreeing": 8}
                # Unequal counts mean the result flickers and nobody should
                # count it, the producing tier included.  Absent means the
                # question was not asked -- reported separately from "asked and
                # answered", never merged with it.
                stab = node.get("seed_stability")
                if isinstance(stab, dict):
                    tried = stab.get("seeds_tried")
                    agree = stab.get("seeds_agreeing")
                    if isinstance(tried, int) and isinstance(agree, int):
                        stability = "stable" if (tried > 1 and agree == tried) \
                            else "flickers"
                    else:
                        stability = "malformed"
                else:
                    stability = "unchecked"
                declared = _declared_class(node)
                if isinstance(name, str) and isinstance(verdict, str) \
                        and verdict not in NON_VERDICTS:
                    short = name.split(".")[-1]
                    if declared is not None:
                        cls, is_ext = declared
                        if is_ext:
                            hits[short].add(f"{tag}[{cls}]:{verdict}")
                            seed_state[short].add(stability)
                        else:
                            declared_internal[short].add(f"{tag}[{cls}]:{verdict}")
                    elif tier is not None:
                        hits[short].add(f"{tag}[{tier}?]:{verdict}")  # ? = inferred
                        seed_state[short].add(stability)
                for k, v in node.items():
                    walk(v, depth + 1, k)
            elif isinstance(node, list):
                for v in node[:5000]:
                    walk(v, depth + 1, key)

        walk(blob)
    return hits, declared_internal, seed_state


def main(argv=None):
    ap = argparse.ArgumentParser()
    ap.add_argument("--json", default=str(HERE / "regime.json"))
    a = ap.parse_args(argv)

    api.refresh()
    table = api.definition_table()
    classes = json.loads((HERE / "classes.json").read_text())
    cov_path = HERE / "coverage.json"
    coverage = json.loads(cov_path.read_text()) if cov_path.exists() else {}
    ext, ext_internal, ext_seed = external_checks()

    rows = {}
    for name, d in table.items():
        explicit, mined = mine_regime(d)
        claimed = mine_external_claim(d)
        checked = sorted(ext.get(name.split(".")[-1], ()))
        internally = coverage.get(name, {}).get("status") == "COVERED"
        rows[name] = {
            "file": d["file"], "line": d["line"],
            "class": classes.get(name, {}).get("class"),
            "empirical_status": d["empirical_status"],
            "regime_explicit": explicit,
            "regime_mined": mined,
            "has_regime": bool(explicit or mined),
            "external_claimed_in_docstring": claimed,
            "external_checked_by": checked,
            "external_seed_stability": sorted(
                ext_seed.get(name.split(".")[-1], ())),
            "has_external": bool(checked),
            "internally_validated": internally,
        }

    total = len(rows)
    have_regime = sum(1 for r in rows.values() if r["has_regime"])
    have_ext = sum(1 for r in rows.values() if r["has_external"])
    internal = sum(1 for r in rows.values() if r["internally_validated"])

    print("=" * 74)
    print("MODEL VALIDATION -- the second coverage metric")
    print("=" * 74)
    print("Internal consistency asks whether a check notices a perturbed body.")
    print("Model validation asks whether the right quantity is computed at all.")
    print("The first cannot substitute for the second at any level.\n")
    print(f"definitions                                   : {total}")
    print(f"carry a declared REGIME (explicit or mined)   : {have_regime}"
          f"  ({100*have_regime/total:.1f}%)")
    print(f"  of which declared EXPLICITLY (`Regime:`)    : "
          f"{sum(1 for r in rows.values() if r['regime_explicit'])}")
    print(f"compared against an EXTERNAL reference        : {have_ext}"
          f"  ({100*have_ext/total:.1f}%)")
    inferred = sum(1 for r in rows.values()
                   if any("?]" in e for e in r["external_checked_by"]))
    print(f"  of which the tier DECLARED as external     : {have_ext - inferred}")
    print(f"  of which inferred from the directory       : {inferred}"
          + ("   <- ask that tier to declare evidence_class" if inferred else ""))
    # A Monte Carlo verdict that moves with the seed is not evidence.  Report
    # stability-checked, flickering and unchecked as three separate things --
    # merging "asked and answered" with "never asked" is the same move as
    # merging a mention with a check.
    stable = sum(1 for r in rows.values()
                 if r["has_external"] and "stable" in r["external_seed_stability"]
                 and "flickers" not in r["external_seed_stability"])
    flick = sum(1 for r in rows.values()
                if "flickers" in r["external_seed_stability"])
    unchecked = have_ext - stable - flick
    print(f"  of which SEED-STABLE (re-run across point-sets): {stable}")
    print(f"  of which FLICKER with the seed                 : {flick}"
          + ("   <- nobody should count these" if flick else ""))
    print(f"  of which not stability-checked                 : {unchecked}")
    print(f"definitions whose only evidence is DECLARED internal: "
          f"{len({n for n in ext_internal})}"
          f"  (correctly excluded from the figure above)")
    print(f"internally validated (falsifiable check)      : {internal}"
          f"  ({100*internal/total:.1f}%)")

    # ---- the cross-tabulation
    cell = collections.Counter()
    for r in rows.values():
        cell[(r["internally_validated"], r["has_regime"], r["has_external"])] += 1
    print("\ncross-tabulation  (internal x regime x external):")
    print(f"  {'internal':>9} {'regime':>7} {'external':>9} {'count':>7}")
    for (i, g, e), n in sorted(cell.items(), key=lambda kv: -kv[1]):
        print(f"  {str(i):>9} {str(g):>7} {str(e):>9} {n:7d}")

    danger = [n for n, r in rows.items()
              if r["internally_validated"] and not r["has_regime"]]
    print(f"\n{'=' * 74}")
    print(f"THE DEFECT INVENTORY: internally validated, NO declared regime "
          f"-- {len(danger)}")
    print("=" * 74)
    print("These pass every mutant, read as healthy, and carry no recorded")
    print("statement of the world they describe.  `hetRecurrence` is this class.")
    for n in sorted(danger)[:30]:
        r = rows[n]
        print(f"  {n}  ({r['file']}:{r['line']})"
              + (f"  [{r['empirical_status']}]" if r["empirical_status"] else ""))
    if len(danger) > 30:
        print(f"  ... and {len(danger) - 30} more (full list in regime.json)")

    worst = [n for n, r in rows.items()
             if r["internally_validated"] and not r["has_regime"]
             and r["empirical_status"] in ("VALIDATED", "DERIVED")]
    print(f"\nWORST CELL -- also marked `Empirical status: VALIDATED/DERIVED`, i.e. a")
    print(f"number was checked but the world it was checked in is unrecorded: {len(worst)}")
    for n in sorted(worst)[:20]:
        print(f"  {n}  ({rows[n]['file']}:{rows[n]['line']})"
              f"  [{rows[n]['empirical_status']}]")

    noext = [n for n, r in rows.items()
             if r["empirical_status"] == "VALIDATED" and not r["has_external"]]
    print(f"\nmarked VALIDATED but no external check names them in any results "
          f"file: {len(noext)}")
    for n in sorted(noext)[:12]:
        print(f"  {n}")

    print("\nregimes found, by frequency:")
    freq = collections.Counter(g for r in rows.values() for g in r["regime_mined"])
    for g, n in freq.most_common():
        print(f"  {n:5d}  {g}")

    pathlib.Path(a.json).write_text(json.dumps(
        {"summary": {"total": total, "have_regime": have_regime,
                     "have_external": have_ext, "internally_validated": internal,
                     "internally_validated_no_regime": len(danger),
                     "worst_cell": len(worst)},
         "definitions": rows}, indent=1, ensure_ascii=False))
    print(f"\nwritten: {a.json}")


if __name__ == "__main__":
    main()
