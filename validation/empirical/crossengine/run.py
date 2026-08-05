#!/usr/bin/env python3
"""Cross-engine differential battery.  FRESHNESS GUARD: XSIM_CE_V1

    python run.py --engines slim,fwdpy11 --reps 8 --workers 20
    python run.py --claim mutationSelectionBalanceRecessive --engines slim

Runs each claim's cells under every requested engine, carries a competing body
on the same cells, and writes results.json with ENGINE PROVENANCE attached to
every verdict -- which engines produced it, of which kind, and whether any
forward simulator has ever seen the claim.  `provenance.py` reads that file.

This is NOT a CI gate and must not become one: its verdicts are statistical, so
at any sample size they carry a false-failure rate, and a required check that
fails at random gets ignored.  See the "WHAT IS NOT WIRED UP" comment in
.github/workflows/prover.yml.  The deterministic consequence -- a claim that
drops its coalescent-only restriction -- is what `provenance.py` gates.
"""

from __future__ import annotations

import argparse
import json
import math
import os
import pathlib
import sys
from concurrent.futures import ThreadPoolExecutor

HERE = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))

import claims as claims_mod          # noqa: E402
import engines as eng_mod            # noqa: E402

# A body is REJECTED at this many sems.  Deliberately loose: the point is to
# separate a factor-of-two error from a one-percent one, not to resolve the
# fifth digit.
REJECT_SEMS = 5.0

# Two engines simulating the same model must agree with each other to within
# this many sems.  Beyond it the harness is broken, not the corpus.
ENGINE_AGREE_SEMS = 5.0


def seed_for(claim, cell, rep):
    h = abs(hash((claim, cell))) % 99991
    return 100003 * (rep + 1) + 7919 * h + 17


def run_claim(key, spec, engines, reps, workers):
    obs = spec["observable"]
    usable = []
    for e in engines:
        if not hasattr(e, obs):
            continue
        need = spec.get("needs", {})
        if any(getattr(e, k, False) != v for k, v in need.items()):
            print(f"  [skip] {e.name}: cannot simulate "
                  f"{', '.join(k for k in need)}")
            continue
        usable.append(e)
    if not usable:
        return []

    tasks = {}
    with ThreadPoolExecutor(max_workers=workers) as ex:
        for c in spec["cells"]:
            for e in usable:
                for r in range(reps):
                    fut = ex.submit(getattr(e, obs), c,
                                    seed_for(key, c["name"], r))
                    tasks[fut] = (c["name"], e.name, r)
        raw = {}
        for fut, (cname, ename, r) in tasks.items():
            try:
                raw.setdefault((cname, ename), []).append(fut.result())
            except Exception as exc:
                print(f"  !! {key}/{cname}/{ename} rep{r}: "
                      f"{type(exc).__name__}: {exc}", file=sys.stderr)

    names = list(spec["bodies"])
    rows = []
    print(f"\n=== {key} ({spec['def_name']}) ===")
    print(f"{'cell':14s} {'engine':9s} {'measured':>11s} {'sem':>10s} "
          + " ".join(f"{n:>10s}" for n in names))
    for c in spec["cells"]:
        args = tuple(c[a] for a in spec["args"])
        preds = {n: spec["bodies"][n](*args) for n in names}
        for e in usable:
            xs = raw.get((c["name"], e.name), [])
            if not xs:
                print(f"{c['name']:14s} {e.name:9s} {'FAILED':>11s}")
                continue
            m = sum(xs) / len(xs)
            sd = eng_mod.sem(xs)
            sems = {n: (m - preds[n]) / sd for n in names}
            print(f"{c['name']:14s} {e.name:9s} {m:11.6g} {sd:10.4g} "
                  + " ".join(f"{preds[n]:10.5g}" for n in names))
            print(f"{'':14s} {'sems':9s} {'':11s} {'':10s} "
                  + " ".join(f"{sems[n]:10.1f}" for n in names))
            rows.append({
                "claim": key,
                "lean_file": spec["lean_file"],
                "def_name": spec["def_name"],
                "cell": c["name"],
                "params": {k: v for k, v in c.items() if k != "name"},
                "engine": e.name,
                "engine_kind": e.kind,
                "engine_version": e.version,
                "nreps": len(xs),
                "measured": m,
                "sem": sd,
                "predictions": preds,
                "sems": sems,
                "corpus_rejected": abs(sems["corpus"]) > REJECT_SEMS,
                "planted_rejected": abs(sems["PLANTED"]) > REJECT_SEMS,
            })
    return rows


def summarise(rows):
    """Per-claim provenance and verdict, machine-readable.

    The provenance block is the part that outlives this run: it records which
    engines produced the verdict and of which kind, so that "this MATCH came
    from one coalescent simulator and has never seen a forward sim" is a
    property of the data rather than something a reader has to remember.
    """
    out = {}
    for r in rows:
        s = out.setdefault(r["claim"], {
            "lean_file": r["lean_file"], "def_name": r["def_name"],
            "engines": {}, "cells_run": [], "cells_corpus_rejected": [],
            "calibration_ok": True,
        })
        s["engines"][r["engine"]] = {"kind": r["engine_kind"],
                                     "version": r["engine_version"]}
        if r["cell"] not in s["cells_run"]:
            s["cells_run"].append(r["cell"])
        if r["corpus_rejected"]:
            s["cells_corpus_rejected"].append(
                {"cell": r["cell"], "engine": r["engine"],
                 "sems": r["sems"]["corpus"], "measured": r["measured"],
                 "corpus": r["predictions"]["corpus"],
                 "ratio": (r["measured"] / r["predictions"]["corpus"]
                           if r["predictions"]["corpus"] else None)})
        # CALIBRATION applies to the cells that return a MATCH, because those
        # are the cells whose agreement has to be earned.  On a cell where the
        # corpus body is already rejected by two orders of magnitude, "was the
        # 40-percent-inflated body also rejected" is not a test of anything.
        # A MATCH cell that cannot reject PLANTED is a worthless MATCH.
        if not r["corpus_rejected"]:
            if r["planted_rejected"]:
                s.setdefault("match_cells_with_power", []).append(
                    {"cell": r["cell"], "engine": r["engine"],
                     "planted_sems": r["sems"]["PLANTED"]})
            else:
                # NOT a calibration failure by itself: it means this cell had
                # too few replicates to resolve a 40 percent error, so its
                # agreement is simply worth nothing.  A MATCH is credited only
                # to cells that could have rejected the planted body.
                s.setdefault("underpowered_match_cells", []).append(
                    {"cell": r["cell"], "engine": r["engine"],
                     "planted_sems": r["sems"]["PLANTED"]})
    # ENGINE AGREEMENT.  Two engines simulating the SAME model must agree with
    # each other whatever the corpus body says.  When they do not, the harness
    # is broken and no verdict from it may be believed -- that is how the
    # fwdpy11 `Multiplicative` scaling mismatch was found.  Recorded per cell
    # so the evidence survives the run.
    by_cell = {}
    for r in rows:
        by_cell.setdefault((r["claim"], r["cell"]), []).append(r)
    for (key, cell), rs in by_cell.items():
        worst = 0.0
        for i in range(len(rs)):
            for j in range(i + 1, len(rs)):
                a, b = rs[i], rs[j]
                denom = math.hypot(a["sem"], b["sem"])
                if denom > 0:
                    worst = max(worst, abs(a["measured"] - b["measured"]) / denom)
        if len(rs) > 1:
            s = out[key]
            s.setdefault("engine_agreement", []).append(
                {"cell": cell, "worst_pairwise_sems": worst,
                 "agree": worst <= ENGINE_AGREE_SEMS})
            if worst > ENGINE_AGREE_SEMS:
                s["engines_disagree"] = True

    for key, s in out.items():
        s.setdefault("engines_disagree", False)
        # The claim is calibrated if ANY matching cell had the power to reject
        # the planted body.  A claim whose every MATCH is underpowered has
        # measured nothing, and that is the failure worth shouting about.
        s["calibration_ok"] = bool(s.get("match_cells_with_power")) or not (
            s.get("underpowered_match_cells"))
        kinds = {v["kind"] for v in s["engines"].values()}
        s["engine_kinds"] = sorted(kinds)
        s["saw_forward_simulator"] = "forward" in kinds
        s["single_engine"] = len(s["engines"]) < 2
        s["verdict"] = ("HARNESS-BROKEN-ENGINES-DISAGREE" if s["engines_disagree"]
                        else "CORPUS-REJECTED-ON-SOME-CELLS"
                        if s["cells_corpus_rejected"] else "SURVIVES")
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--engines", default="slim,fwdpy11")
    ap.add_argument("--claim", default=None)
    ap.add_argument("--reps", type=int, default=8)
    ap.add_argument("--workers", type=int, default=20)
    ap.add_argument("--out", default=str(HERE / "results.json"))
    a = ap.parse_args()

    engines = eng_mod.load(a.engines.split(","))
    print("engines: " + ", ".join(f"{e.name}({e.kind}, {e.version})"
                                  for e in engines))
    keys = [a.claim] if a.claim else list(claims_mod.CLAIMS)
    rows = []
    for k in keys:
        rows += run_claim(k, claims_mod.CLAIMS[k], engines, a.reps, a.workers)

    summary = summarise(rows)
    doc = {"guard": eng_mod.GUARD, "reject_sems": REJECT_SEMS,
           "engines": {e.name: {"kind": e.kind, "version": e.version}
                       for e in engines},
           "claims": summary, "rows": rows}
    with open(a.out, "w") as fh:
        json.dump(doc, fh, indent=1)

    print("\n--- calibration (the PLANTED body must be rejected everywhere) ---")
    bad = [k for k, s in summary.items() if not s["calibration_ok"]]
    for k, s in summary.items():
        print(f"  {k:36s} calibration={'OK' if s['calibration_ok'] else 'FAILED'}"
              f"  verdict={s['verdict']}"
              f"  engines={','.join(sorted(s['engines']))}")
    print("GUARD " + eng_mod.GUARD)
    if bad:
        print(f"CALIBRATION FAILED for {bad}: the instrument could not reject a "
              "body it is known to disagree with, so its MATCHes are worthless.",
              file=sys.stderr)
        return 2
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
