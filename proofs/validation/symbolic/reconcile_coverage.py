"""Reconcile every coverage tier into one table, keyed by fully-qualified name.

Four tiers have been quoting four numbers with unknown overlap.  Adding them is
wrong (a definition covered twice would be counted twice) and so is taking the
maximum (it discards the others).  This computes the union, the overlap
structure, and the complement, and it keeps the EXTERNAL tiers separable from
the INTERNAL ones, because "the formula matches a simulation" and "the formula
is internally consistent" are different claims and pooling them would overstate
what is known.

Tier semantics, declared rather than inferred, since each tier's ledger uses
its own vocabulary:

  popgen_defs   EXTERNAL  named by a validation script that compares the Lean
                          formula against msprime / SLiM / exact Wright-Fisher
  differential  EXTERNAL  ledger state COVERED, differential test against an
                          independent analytic or simulated reference
  invariants    INTERNAL  `covered` AND carrying falsifiability_evidence
  extract       INTERNAL  coverage_v2 status COVERED (range/witness checks
                          mined from theorem hypotheses)
  symbolic      INTERNAL  this directory: slice ledger VERIFIED, which already
                          requires a rejected mutation

KNOWN WEAKNESS IN ONE INPUT.  `popgen_defs.tested_names` decides coverage by
regex-scanning its own scripts for any quoted lowercase identifier of five or
more characters.  That matches string literals which are not definition names,
so its count is an upper bound and its membership is approximate.  It is the
tier the project's headline 5.0% comes from, so this matters: the agreement
between it and the lead's figure is agreement about the same heuristic, not two
independent measurements.  Reported as-is and flagged rather than silently
adjusted, because tightening someone else's ledger from outside is how numbers
stop being comparable across reports.

THE FALSIFIABILITY RULE, applied uniformly.  A tier's count is only admitted
where that tier records evidence its check can fail.  `invariants` publishes
falsifiability_evidence and `symbolic` publishes a rejected mutation, so both
are filtered on it.  `extract` and `differential` do not publish a per-
definition falsifiability field; their counts are taken at face value and
flagged as UNGATED in the output, because a number that cannot distinguish a
check that can fail from one that cannot is not the same kind of number.
"""

from __future__ import annotations

import json
import re
import sys
from collections import Counter, defaultdict
from pathlib import Path

from paths import VALIDATION, require  # noqa: E402, ARTIFACTS as ART

require(VALIDATION, "proofs/validation")
HERE = VALIDATION / "symbolic"
sys.path.insert(0, str(VALIDATION / "extract"))
import api  # noqa: E402

TIER_KIND = {"popgen_defs": "EXTERNAL", "differential": "EXTERNAL",
             "invariants": "INTERNAL", "extract": "INTERNAL",
             "symbolic": "INTERNAL"}
GATED = {"invariants": True, "symbolic": True,
         "extract": False, "differential": False, "popgen_defs": False}


def universe():
    """The denominator: every definition in the shared table."""
    return {fq: d for fq, d in api.definition_table().items()}


def _resolve(name, uni, by_short):
    """Map a tier's key into the canonical fully-qualified space."""
    if name in uni:
        return name
    short = name.split(".")[-1]
    cands = by_short.get(short) or []
    if len(cands) == 1:
        return cands[0]
    return None


def tier_popgen(uni, by_short):
    sys.path.insert(0, str(VALIDATION / "popgen_defs"))
    import coverage as pg  # noqa
    tested = pg.tested_names(str(VALIDATION / "popgen_defs"))
    out, unmapped = set(), set()
    for fq, d in uni.items():
        if d["short"] in tested:
            out.add(fq)
    return out, unmapped


def tier_differential(uni, by_short):
    p = VALIDATION / "differential" / "coverage_ledger.json"
    if not p.exists():
        return set(), set()
    out, unmapped = set(), set()
    for r in json.loads(p.read_text()):
        if r.get("state") != "COVERED":
            continue
        fq = _resolve(r["definition"], uni, by_short)
        (out.add(fq) if fq else unmapped.add(r["definition"]))
    return out, unmapped


def tier_invariants(uni, by_short):
    p = VALIDATION / "invariants" / "coverage.json"
    if not p.exists():
        return set(), set()
    out, unmapped = set(), set()
    for k, v in json.loads(p.read_text()).items():
        if not v.get("covered"):
            continue
        if GATED["invariants"] and not v.get("falsifiability_evidence"):
            continue
        fq = _resolve(k, uni, by_short)
        (out.add(fq) if fq else unmapped.add(k))
    return out, unmapped


def tier_extract(uni, by_short):
    p = VALIDATION / "extract" / "coverage.json"
    if not p.exists():
        return set(), set()
    out, unmapped = set(), set()
    for k, v in json.loads(p.read_text()).items():
        if v.get("status") != "COVERED":
            continue
        fq = _resolve(k, uni, by_short)
        (out.add(fq) if fq else unmapped.add(k))
    return out, unmapped


def tier_symbolic(uni, by_short):
    out, unmapped = set(), set()
    p = ART / "slice_ledger.json"
    if p.exists():
        for fq, r in json.loads(p.read_text()).items():
            if r.get("status") == "VERIFIED":
                f = _resolve(fq, uni, by_short)
                (out.add(f) if f else unmapped.add(fq))
    return out, unmapped


TIERS = {"popgen_defs": tier_popgen, "differential": tier_differential,
         "invariants": tier_invariants, "extract": tier_extract,
         "symbolic": tier_symbolic}


def run():
    uni = universe()
    by_short = defaultdict(list)
    for fq, d in uni.items():
        by_short[d["short"]].append(fq)

    covered, unmapped = {}, {}
    for name, fn in TIERS.items():
        try:
            c, u = fn(uni, by_short)
        except Exception as e:  # a tier that will not load must not fake a zero
            covered[name], unmapped[name] = None, {f"LOAD FAILED: {e}"}
            continue
        covered[name], unmapped[name] = c, u

    live = {k: v for k, v in covered.items() if v is not None}
    per_def = defaultdict(set)
    for tier, s in live.items():
        for fq in s:
            per_def[fq].add(tier)

    union = set(per_def)
    external = {fq for fq, ts in per_def.items()
                if any(TIER_KIND[t] == "EXTERNAL" for t in ts)}
    internal = {fq for fq, ts in per_def.items()
                if any(TIER_KIND[t] == "INTERNAL" for t in ts)}
    depth = Counter(len(ts) for ts in per_def.values())
    single = {fq: sorted(ts) for fq, ts in per_def.items() if len(ts) == 1}

    return {
        "universe": len(uni),
        "tiers": {k: (len(v) if v is not None else None) for k, v in covered.items()},
        "tier_kind": TIER_KIND,
        "tier_falsifiability_gated": GATED,
        "unmapped_keys": {k: sorted(v)[:20] for k, v in unmapped.items() if v},
        "union": len(union),
        "external_union": len(external),
        "internal_union": len(internal),
        "external_and_internal": len(external & internal),
        "external_only": len(external - internal),
        "internal_only": len(internal - external),
        "depth_histogram": {str(k): v for k, v in sorted(depth.items())},
        "single_tier_count": len(single),
        "single_tier_by_tier": Counter(ts[0] for ts in single.values()),
        "uncovered": len(uni) - len(union),
        "per_definition": {fq: sorted(ts) for fq, ts in sorted(per_def.items())},
        "single_tier": single,
    }


def main():
    r = run()
    (ART / "reconciled_coverage.json").write_text(
        json.dumps({k: (dict(v) if isinstance(v, Counter) else v)
                    for k, v in r.items()}, indent=1, ensure_ascii=False))
    u = r["universe"]

    def pct(n):
        return f"{100*n/u:5.1f}%"

    print(f"RECONCILED COVERAGE   denominator = {u} definitions "
          f"(the shared extract table)\n")
    print(f"{'tier':<14} {'kind':<9} {'gated':<6} {'covered':>8} {'of corpus':>10}")
    print("-" * 52)
    for t, n in r["tiers"].items():
        g = "yes" if r["tier_falsifiability_gated"][t] else "NO"
        print(f"{t:<14} {r['tier_kind'][t]:<9} {g:<6} "
              f"{(n if n is not None else 'FAILED'):>8} {pct(n) if n is not None else '':>10}")
    print()
    print("COLUMN MEANINGS")
    print("  covered   = definitions this tier reports as checked, after applying")
    print("              that tier's own falsifiability evidence where published")
    print("  gated     = whether the tier publishes per-definition evidence that")
    print("              its check CAN FAIL. 'NO' means the count may include")
    print("              checks that hold trivially and cannot be compared like")
    print("              for like with a gated tier.")
    print()
    print(f"{'UNION (any tier)':<34} {r['union']:>5}  {pct(r['union'])}")
    print(f"{'  EXTERNAL union (vs ground truth)':<34} {r['external_union']:>5}  "
          f"{pct(r['external_union'])}")
    print(f"{'  INTERNAL union (consistency)':<34} {r['internal_union']:>5}  "
          f"{pct(r['internal_union'])}")
    print(f"{'  both external and internal':<34} {r['external_and_internal']:>5}")
    print(f"{'  external only':<34} {r['external_only']:>5}")
    print(f"{'  internal only':<34} {r['internal_only']:>5}")
    print(f"{'COMPLEMENT (no tier at all)':<34} {r['uncovered']:>5}  {pct(r['uncovered'])}")
    print()
    print("OVERLAP STRUCTURE -- how many tiers cover each covered definition")
    for k, v in r["depth_histogram"].items():
        label = "tier" if k == "1" else "tiers"
        note = "   <- single point of failure" if k == "1" else ""
        print(f"  covered by {k} {label:<5} {v:>5}{note}")
    print()
    print("SINGLE-TIER DEFINITIONS BY TIER (each rests on one check only)")
    for t, n in sorted(r["single_tier_by_tier"].items(), key=lambda kv: -kv[1]):
        print(f"  {t:<14} {n:>5}")
    if r["unmapped_keys"]:
        print()
        print("KEYS THAT DID NOT MAP INTO THE CANONICAL NAME SPACE (excluded)")
        for t, ks in r["unmapped_keys"].items():
            print(f"  {t}: {len(ks)} e.g. {ks[:5]}")


if __name__ == "__main__":
    main()
