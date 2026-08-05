"""Stamp every artifact with where and when it came from, and check it.

An artifact at a FIXED shared path is always populated, so no consumer can tell
"this run has not written yet" from "a previous run wrote this". Existence is
not evidence of currency. My own fallback bug was the same shape one level up: a
predicate that could not be false on first use, so the run wrote beside the
source while looking compliant.

So every artifact carries, inside the file:

    _provenance: {revision, dirty, generated_utc, generator, corpus_defs, host}

and a consumer checks the REVISION rather than the file's existence. The extract
tier's staleness check was found comparing generated files against each other
and never against the Lean sources, so a coherent snapshot of a corpus that no
longer exists reported clean. Comparing against the revision the corpus was at
is what makes that detectable.

A measurement that cannot report its own absence will eventually report someone
else's answer as its own.
"""

from __future__ import annotations

import json
import subprocess
import time
from pathlib import Path

from paths import REPO, ARTIFACTS


def _git(*args, default=""):
    try:
        return subprocess.run(["git", "-C", str(REPO), *args],
                              capture_output=True, text=True, timeout=30).stdout.strip()
    except Exception:
        return default


def stamp(generator: str, extra: dict | None = None) -> dict:
    dirty = bool(_git("status", "--porcelain", "--", "Descent"))
    return {
        "revision": _git("rev-parse", "HEAD", default="unknown"),
        "revision_short": _git("rev-parse", "--short", "HEAD", default="unknown"),
        "dirty_corpus": dirty,
        "generated_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "generator": generator,
        **(extra or {}),
    }


def write(name: str, payload, generator: str, extra: dict | None = None) -> Path:
    """Write an artifact with its provenance attached.

    Lists are wrapped so the stamp has somewhere to live; readers that want the
    bare list take payload["data"].
    """
    obj = ({"_provenance": stamp(generator, extra), "data": payload}
           if isinstance(payload, list)
           else {"_provenance": stamp(generator, extra), **payload})
    p = ARTIFACTS / name
    p.write_text(json.dumps(obj, indent=1, ensure_ascii=False))
    return p


def read(name: str, expect_revision: str | None = None):
    """Read an artifact, refusing one generated from a different revision."""
    p = ARTIFACTS / name
    if not p.exists():
        raise SystemExit(f"FATAL: {p} ABSENT. Nothing has written it; a missing "
                         f"artifact must not be read as an empty result.")
    obj = json.loads(p.read_text())
    prov = obj.get("_provenance") if isinstance(obj, dict) else None
    if expect_revision and prov and prov.get("revision") != expect_revision:
        raise SystemExit(
            f"FATAL: {p} was generated from revision {prov.get('revision_short')} "
            f"but the corpus is at {expect_revision[:8]}. A coherent snapshot of "
            f"a corpus that no longer exists reports clean; regenerate it.")
    return obj


def describe(name: str) -> str:
    p = ARTIFACTS / name
    if not p.exists():
        return f"{name:32s} ABSENT"
    try:
        prov = (json.loads(p.read_text()) or {}).get("_provenance") or {}
    except Exception:
        return f"{name:32s} UNREADABLE"
    return (f"{name:32s} rev {prov.get('revision_short', '?'):>10}  "
            f"{prov.get('generated_utc', '?')}"
            f"{'  [corpus dirty]' if prov.get('dirty_corpus') else ''}")


def main():
    names = ["decls.json", "results_check1.json", "results_check1b.json",
             "results_check2.json", "results_check3.json", "results_check4.json",
             "results_check5.json", "results_check6.json", "results_check7.json",
             "results_check8.json", "results_homonyms.json", "coverage.json",
             "findings.json", "slice_ledger.json", "reconciled_coverage.json"]
    print(f"artifacts at {ARTIFACTS}")
    print(f"corpus revision {_git('rev-parse', '--short', 'HEAD')}")
    print()
    for n in names:
        print("  " + describe(n))


if __name__ == "__main__":
    main()
