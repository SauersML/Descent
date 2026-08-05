"""Emit the committed verdict ledger from the battery result files.

    python3 ledger.py <dir-of-battery_*_results.json> [-o ledger.json]

WHY THIS FILE EXISTS. Coverage was a docstring property and the verdicts lived
in sixty-odd JSON files nobody's guard read, so the two drifted: definitions
carried a real battery verdict and still read `Empirical status: UNTESTED`, and
definitions read VALIDATED off a MATCH that no competing formula was ever run
against. `ledger.json` is the single committed record that `check.py`'s `ledger`
guard reads, so a disagreement between a docstring and the evidence behind it is
a build failure rather than something a person has to notice.

THE SCHEMA IS ANCHORED ON DECLARATION NAMES, never on line numbers. Line numbers
move every time anyone edits a file above the declaration, which is what made
`extract/test_parser.py` a permanently failing check.

THE COMPETITOR GATE IS APPLIED HERE, at emit time, not left to a battery author
to remember. A record is a CORPUS row if its `source` matches the bare-named
row's source and a COMPETITOR row otherwise -- classifying on the transcribed
formula rather than on the bracket tag, because there are 118 distinct tags and
tag-parsing is guesswork. A corpus MATCH with no competitor REJECTED in the same
battery becomes `UNINFORMATIVE`, because that is what it is: the design never
showed it could reject anything. That rule applies retroactively to every result
file already on disk, which is the point -- the `driftVariance` class of fake
verdict cannot be banked again, and the ones already banked are relabelled.

FRESHNESS is a required field. A battery that does not report `FRESHNESS=OK` in
its own run log cannot have its verdicts cited by a docstring; a stale run read
as a fresh one is how this harness has reported somebody else's answer as its
own.
"""
from __future__ import annotations

import argparse
import glob
import json
import os
import re

SCHEMA_VERSION = 1

# The verdict vocabulary, most specific first: a verdict string is matched
# against these in order, so "VOID (control failed)" is VOID and not MATCH.
VOCAB = ("GENERATIVE SELF-TEST", "SELF-TEST", "VOID", "NO POWER",
         "DEGENERATE ORACLE", "LEAD", "FALSIFIED", "REFUTED", "UNINFORMATIVE",
         "MATCH", "VALIDATED", "CONVENTION", "REGIME")

# Verdicts that assert the corpus body agrees with a measurement.
AGREES = {"MATCH", "VALIDATED"}
# Verdicts that assert it disagrees.
DISAGREES = {"FALSIFIED", "REFUTED"}
# Verdicts that assert nothing.
NULL = {"UNINFORMATIVE", "SELF-TEST", "GENERATIVE SELF-TEST", "VOID",
        "NO POWER", "DEGENERATE ORACLE", "LEAD", "CONVENTION", "REGIME"}


def headline(v: str) -> str:
    """The vocabulary word a free-text verdict carries."""
    u = (v or "").upper()
    for w in VOCAB:
        if w in u:
            return w
    return "UNKNOWN"


def split_name(raw: str) -> tuple[str, str]:
    """(declaration short name, bracket tag) from a battery's record name."""
    raw = (raw or "").strip()
    head = re.split(r"[ \[(]", raw)[0]
    return head.split(".")[-1], raw[len(head):].strip()


def freshness_of(directory: str, battery: str,
                 recorded_sha: str | None) -> tuple[str, str | None]:
    """(freshness, source sha256) for one battery.

    THE ONLY TRUSTWORTHY SIGNAL IS A RECORDED HASH, and this function used to
    trust mtime instead. That was wrong, and the way it went wrong is worth
    keeping: fetching `battery_bulk20.py` a moment after its results file --
    an ordinary copy, changing nothing -- inverted the two timestamps and the
    ledger declared twelve batteries STALE that were not. Neither `tar`, nor
    `git`, nor a file transfer preserves the relative order of two mtimes, and
    the repository is now the source of truth precisely BECAUSE files move
    between machines. A freshness test that a copy can flip is not a freshness
    test.

    So the rule is evidentiary rather than heuristic:

      STALE      the results file records the SHA of the source that produced
                 it and that SHA is not the source's. Proof of staleness.
      OK         the recorded SHA matches, or the battery's own log carries the
                 `FRESHNESS=OK` token it prints only when its source contains a
                 string that exists nowhere else.
      UNVERIFIED no recorded hash and no token. Absence of evidence, reported
                 as such and NOT gated on -- most batteries predate the
                 requirement, and calling them stale on no evidence would be
                 the same error in the other direction.

    `battery_core.dump_results` writes the hash. Batteries that dump `RESULTS`
    by hand do not, which is why UNVERIFIED exists and why it should shrink.
    """
    src = os.path.join(directory, "battery_%s.py" % battery)
    sha = None
    if os.path.exists(src):
        import hashlib
        sha = hashlib.sha256(open(src, "rb").read()).hexdigest()[:16]
    if recorded_sha and sha and recorded_sha != sha:
        return "STALE (recorded source hash does not match the source)", sha
    if recorded_sha and sha and recorded_sha == sha:
        return "OK (recorded source hash matches)", sha
    for cand in ("%s.log" % battery, "b%s.log" % battery.replace("bulk", "")):
        path = os.path.join(directory, cand)
        if os.path.exists(path):
            txt = open(path, errors="ignore").read()
            if "FRESHNESS=STALE" in txt:
                return "STALE (self-reported)", sha
            if "FRESHNESS=OK" in txt:
                return "OK (self-reported token)", sha
    if sha is None:
        return "STALE (battery source absent)", None
    return "UNVERIFIED (no recorded source hash)", sha


def build(directory: str) -> dict:
    records = []
    for path in sorted(glob.glob(os.path.join(directory,
                                              "battery_*_results.json"))):
        battery = os.path.basename(path)[len("battery_"):-len("_results.json")]
        try:
            rows = json.load(open(path))
        except Exception as exc:                       # noqa: BLE001
            records.append(dict(battery=battery, unreadable=str(exc)))
            continue
        recorded = (rows.get("_battery_sha") if isinstance(rows, dict) else None)
        fresh, sha = freshness_of(directory, battery, recorded)
        if isinstance(rows, dict) and "results" not in rows:
            # A results file that is a dict of raw arrays, not a list of
            # `record()` outputs. `battery_correct.py` is one: it produces real
            # numbers and calls `record()` nowhere, so it carries evidence but
            # no verdicts. That distinction has to survive into the ledger,
            # because two docstrings cite it as though it carried verdicts, and
            # a citation that resolves to a data dump is not the same thing as
            # a citation that resolves to nothing.
            records.append(dict(
                declaration=None, against=None, battery=battery,
                battery_sha=sha, role="data", tag="",
                source=", ".join(sorted(rows)[:6]),
                verdict_raw="", verdict="DATA ONLY (no verdict records)",
                downgraded_because=None, competitors_carried=0,
                competitors_rejected=0, worst_sems=None, cells=0,
                freshness=fresh, regime="", note="",
            ))
            continue
        if isinstance(rows, dict):
            rows = rows.get("results", [])

        parsed = []
        for row in rows:
            if not isinstance(row, dict) or not row.get("name"):
                continue
            short, tag = split_name(row["name"])
            if not short:
                continue
            parsed.append(dict(
                short=short, tag=tag, bare=not tag,
                source=(row.get("source") or "").strip(),
                verdict=str(row.get("verdict", "")),
                note=(row.get("note") or "")[:400],
                regime=(row.get("regime") or "")[:400],
                worst_sems=(row.get("worst") or {}).get("sems_off"),
                cells=len(row.get("cells") or []),
            ))

        # ROLE. A row is a CORPUS row only if its name is bare, or if it is
        # tagged but transcribes the SAME `source` as a bare row of the same
        # declaration -- that is a regime split of the corpus body, not a rival.
        # Everything else is a competitor. Deciding on the transcribed formula
        # rather than on the bracket tag matters: there are 118 distinct tags
        # and no grammar, so tag-parsing is guesswork; and a tagged row with no
        # bare sibling used to be filed as a corpus row, which is how
        # `calibratedBrier` and `islandFstFiniteDemes` came to carry
        # falsifications that were really their competitors' verdicts.
        canon: dict[str, set[str]] = {}
        for p in parsed:
            if p["bare"]:
                canon.setdefault(p["short"], set()).add(p["source"])
        for p in parsed:
            p["role"] = ("corpus"
                         if p["bare"] or p["source"] in canon.get(p["short"], ())
                         else "competitor")

        # ASSOCIATION. A competitor is recorded under a name of the battery
        # author's choosing -- `equalVarianceGaussianAUC [factor 2 dropped]`
        # against a corpus row named `equalVarianceGaussianAUCFromSignalVariance`
        # -- so exact-name grouping orphans it and the corpus row then looks
        # uncompeted. Attach each competitor to the corpus declaration in the
        # same battery with the longest shared prefix.
        corpus_names = sorted({p["short"] for p in parsed
                               if p["role"] == "corpus"})

        def attach(name: str) -> str | None:
            best, best_len = None, 0
            for cn in corpus_names:
                n = 0
                for a, b in zip(name, cn):
                    if a != b:
                        break
                    n += 1
                if n > best_len:
                    best, best_len = cn, n
            return best if best_len >= 5 else None

        rejected: dict[str, int] = {}
        carried: dict[str, int] = {}
        for p in parsed:
            if p["role"] != "competitor":
                p["against"] = None
                continue
            target = p["short"] if p["short"] in corpus_names else attach(p["short"])
            p["against"] = target
            if target is None:
                continue
            carried[target] = carried.get(target, 0) + 1
            if headline(p["verdict"]) in DISAGREES:
                rejected[target] = rejected.get(target, 0) + 1

        for p in parsed:
            head = headline(p["verdict"])
            key = p["short"] if p["role"] == "corpus" else p.get("against")
            nrej = rejected.get(key, 0)
            ncar = carried.get(key, 0)
            gated = head
            downgraded = None
            if p["role"] == "corpus" and head in AGREES and nrej == 0:
                gated = "UNINFORMATIVE"
                downgraded = ("no competing formula was rejected on these "
                              "cells, so the design never showed it could "
                              "reject anything")
            records.append(dict(
                declaration=p["short"], against=p.get("against"),
                battery=battery, battery_sha=sha,
                role=p["role"], tag=p["tag"], source=p["source"],
                verdict_raw=p["verdict"], verdict=gated,
                downgraded_because=downgraded,
                competitors_carried=ncar, competitors_rejected=nrej,
                worst_sems=p["worst_sems"], cells=p["cells"],
                freshness=fresh, regime=p["regime"], note=p["note"],
            ))

    return dict(schema_version=SCHEMA_VERSION, records=records)


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("directory", nargs="?", default=".")
    ap.add_argument("-o", "--out", default="ledger.json")
    args = ap.parse_args()

    led = build(args.directory)
    # `adjudications.json` is HAND-WRITTEN and lives beside this file, not in
    # the results directory: it is a judgement about the evidence, not part of
    # it, and regenerating the ledger must never silently discard it.
    adj_path = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                            "adjudications.json")
    if os.path.exists(adj_path):
        adj = json.load(open(adj_path))
        led["adjudications"] = {k: v for k, v in adj.items()
                                if not k.startswith("_")}
    with open(args.out, "w") as fh:
        json.dump(led, fh, indent=1, sort_keys=True)

    recs = led["records"]
    corpus = [r for r in recs if r.get("role") == "corpus"]
    down = [r for r in corpus if r.get("downgraded_because")]
    by_head: dict[str, int] = {}
    for r in corpus:
        by_head[r["verdict"]] = by_head.get(r["verdict"], 0) + 1
    print("wrote %s: %d records over %d batteries, %d corpus rows"
          % (args.out, len(recs),
             len({r.get("battery") for r in recs}), len(corpus)))
    print("corpus verdicts after the competitor gate:")
    for k, v in sorted(by_head.items(), key=lambda kv: -kv[1]):
        print("  %-22s %4d" % (k, v))
    print("MATCHes downgraded to UNINFORMATIVE by the gate: %d" % len(down))
    fr: dict[str, int] = {}
    for r in recs:
        fr[r.get("freshness", "?")] = fr.get(r.get("freshness", "?"), 0) + 1
    print("freshness: " + ", ".join("%s=%d" % kv for kv in sorted(fr.items())))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
