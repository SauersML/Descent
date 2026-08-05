"""Permanent guard on the Lean corpus <-> shipped implementation correspondence.

The corpus states and proves properties of what `gnomon` does.  Nothing checked
that the two agree, and a theorem about a model the shipped code does not
implement is worse than no theorem: it is a false assurance, invisible to every
other guard in `proofs/validation/`.  The correspondence also rots on every
commit to either side, which is what makes it a guard rather than a one-off
audit.

Six checks, all at budget 0, all of which genuinely fail:

  CORPUS-MISSING   a mapped Lean declaration is not in the corpus
  CORPUS-STALE     a mapped Lean body changed since the mapping was verified
  CODE-MISSING     a mapped Rust function is not in the file it is mapped to
  CODE-STALE       a mapped Rust body changed since the mapping was verified
  REFPOINT         the transcription disagrees with a value the corpus proves
  EXPECTED-STALE   expected.json is not what lean_bodies.py computes today
  GUARD-SURFACE    a numerical guard appeared in mapped code with no entry

STALE is deliberately not the same finding as "wrong".  A changed body means the
correspondence is unverified, and the repair is to re-read the two sides and
re-bless the table (`--bless`), not to assume the mathematics broke.

The numeric differential itself -- every Lean body evaluated against the shipped
implementation on a shared fixture grid -- runs on the Rust side, inside the
already-required `cargo test` for `correctability_calculator`, because that is
where the shipped code can be executed.  This module owns the Lean half of that
comparison (`expected.json`) and refuses to let it drift.

Stdlib only.  Deterministic.  No line numbers anywhere: everything is anchored
to declaration names plus a content hash.
"""

import argparse
import json
import math
import pathlib
import sys

HERE = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(HERE.parent / "extract"))

import lean_bodies  # noqa: E402
import rustsrc  # noqa: E402

TABLE_PATH = HERE / "correspondence.json"
FIXTURES_PATH = HERE / "fixtures.json"
EXPECTED_PATH = HERE / "expected.json"

# Every budget is 0.  Pinning one of these to the current count to make a check
# pass would convert the guard into a record of how much drift was tolerated on
# the day someone was in a hurry.
BUDGETS = {
    "CORPUS-MISSING": 0,
    "CORPUS-STALE": 0,
    "CODE-MISSING": 0,
    "CODE-STALE": 0,
    "REFPOINT": 0,
    "EXPECTED-STALE": 0,
    "GUARD-SURFACE": 0,
}


def repo_root():
    """The directory holding `map/` and `proofs/`.

    Searched for, not counted in `..`s.  `extract/` hardcoded its depth, the
    directory moved one level down, and the whole extraction tier then parsed
    zero definitions and reported success; the executable correctability
    contract had the same defect in a `#[path]` and never compiled at all.
    """
    for candidate in (HERE, *HERE.parents):
        if (candidate / "map").is_dir() and (candidate / "proofs").is_dir():
            return candidate
    raise RuntimeError(
        f"no ancestor of {HERE} contains both map/ and proofs/; the repository "
        f"root could not be located")


def corpus_names():
    """{fully-qualified name: body checksum or None} for the Lean corpus.

    Uses `extract/api.py`, which is the one sanctioned parse of
    `proofs/Calibrator/`.  A second, disagreeing extractor is how two checks end
    up with two ideas of what the corpus contains.

    An EMPTY table raises rather than returning `{}`.  Those two outcomes are
    indistinguishable downstream, and the difference is the whole verdict: an
    empty table would make every CORPUS-MISSING finding fire at once, or -- far
    worse if the polarity were reversed -- would make the check pass while
    seeing nothing.
    """
    import api

    # A table that no longer describes the corpus on disk would produce
    # CORPUS-STALE findings about the cache rather than about the mapping.
    api.require_fresh()
    definitions = api.definition_table()
    theorems = api.theorems()
    if not definitions:
        raise RuntimeError(
            "the extracted definition table is EMPTY; the corpus could not be "
            "read, so this check has no evidence and must not report success")
    names = {}
    for name in definitions:
        names[name] = api.body_checksum(name)
    for name in theorems:
        names.setdefault(name, None)
    return names


def load_sources():
    """Everything the checks read, in one injectable bundle.

    The calibration in `test_map_check.py` perturbs this bundle rather than
    editing tracked files, so it can assert both directions -- a clean bundle is
    silent, a bundle with one planted defect is not -- without a mutable copy of
    the repository.
    """
    root = repo_root()
    table = json.loads(TABLE_PATH.read_text())
    code_text = {}
    for entry in table["entries"]:
        code = entry.get("code")
        if code:
            path = code["file"]
            if path not in code_text:
                code_text[path] = (root / path).read_text()
    return {
        "table": table,
        "corpus": corpus_names(),
        "code_text": code_text,
        "fixtures": json.loads(FIXTURES_PATH.read_text()),
        "expected": json.loads(EXPECTED_PATH.read_text()),
    }


def findings(sources):
    """The list of findings.  Empty means the correspondence is verified."""
    out = []
    table = sources["table"]
    corpus = sources["corpus"]
    code_text = sources["code_text"]

    bodies_by_file = {path: rustsrc.function_bodies(text)
                      for path, text in code_text.items()}

    for entry in table["entries"]:
        klass = entry["correspondence"]
        lean = entry.get("lean")
        code = entry.get("code")

        if lean is not None:
            if lean["name"] not in corpus:
                out.append(("CORPUS-MISSING", lean["name"],
                            f"mapped to {code['file']}::{code['symbol']} but no such "
                            f"declaration is in the corpus"))
            else:
                recorded = lean.get("body_checksum")
                live = corpus[lean["name"]]
                if recorded is not None and live is not None and recorded != live:
                    out.append(("CORPUS-STALE", lean["name"],
                                f"Lean body changed since the correspondence was "
                                f"verified ({recorded} -> {live}); re-read it against "
                                f"{code['file']}::{code['symbol']} and re-bless"))

        if code is not None:
            bodies = bodies_by_file.get(code["file"], {})
            symbol = code["symbol"]
            if symbol not in bodies:
                out.append(("CODE-MISSING", f"{code['file']}::{symbol}",
                            "mapped function is not in that file"))
            else:
                live = rustsrc.body_sha256(bodies[symbol])
                if code.get("body_sha256") != live:
                    who = lean["name"] if lean else f"({klass})"
                    out.append(("CODE-STALE", f"{code['file']}::{symbol}",
                                f"implementation body changed since the correspondence "
                                f"with {who} was verified; re-read both sides and "
                                f"re-bless"))
                recorded_guards = code.get("guard_surface")
                if recorded_guards is not None:
                    live_guards = rustsrc.guard_surface(bodies[symbol])
                    if [list(g) for g in recorded_guards] != [list(g) for g in live_guards]:
                        out.append(("GUARD-SURFACE", f"{code['file']}::{symbol}",
                                    f"numerical-guard surface changed "
                                    f"{recorded_guards} -> {live_guards}; a new clamp, "
                                    f"epsilon, fallback or division needs an invariant "
                                    f"in the corpus or an explicit absent-class entry"))

    for theorem, computed, expected in lean_bodies.REFERENCE_POINTS:
        if theorem not in corpus:
            out.append(("CORPUS-MISSING", theorem,
                        "reference point names a theorem that is not in the corpus, "
                        "so it is no longer evidence that the transcription is faithful"))
            continue
        got = computed()
        if not math.isclose(got, expected, rel_tol=1e-12, abs_tol=1e-12):
            out.append(("REFPOINT", theorem,
                        f"transcription gives {got!r} where the corpus proves {expected!r}"))

    fixtures = sources["fixtures"]
    expected_rows = sources["expected"]
    if len(fixtures) != len(expected_rows):
        out.append(("EXPECTED-STALE", "expected.json",
                    f"{len(expected_rows)} rows for {len(fixtures)} fixtures"))
    else:
        for fixture, recorded in zip(fixtures, expected_rows):
            live = lean_bodies.report(fixture)
            if not _same(live, recorded):
                out.append(("EXPECTED-STALE", fixture["tag"],
                            "lean_bodies.py no longer computes the committed "
                            "expected value; regenerate with gen_fixtures.py after "
                            "checking the change was intended"))
    return out


def _same(a, b):
    if isinstance(a, dict):
        return isinstance(b, dict) and a.keys() == b.keys() and \
            all(_same(a[k], b[k]) for k in a)
    if isinstance(a, list):
        return isinstance(b, list) and len(a) == len(b) and \
            all(_same(x, y) for x, y in zip(a, b))
    if isinstance(a, bool) or isinstance(b, bool) or a is None or b is None:
        return a is b or a == b
    if isinstance(a, (int, float)) and isinstance(b, (int, float)):
        if math.isnan(a) and math.isnan(b):
            return True
        return a == b
    return a == b


def bless():
    """Rewrite the recorded checksums and guard surfaces from what is on disk.

    This is the deliberate act of saying "I have re-read both sides and they
    still correspond".  It is never run by CI.
    """
    import api

    root = repo_root()
    table = json.loads(TABLE_PATH.read_text())
    cache = {}
    for entry in table["entries"]:
        lean = entry.get("lean")
        if lean is not None:
            # Deliberately NOT wrapped in a try. Recording `None` for a name
            # that could not be checksummed would switch CORPUS-STALE off for
            # that entry, and a guard that quietly stops guarding is the exact
            # failure this directory exists to prevent. A Prop-valued
            # declaration has no numeric body but still has a checksum; if a
            # name genuinely cannot be resolved, that is a finding about the
            # table, so let it raise here rather than at check time.
            lean["body_checksum"] = api.body_checksum(lean["name"])
        code = entry.get("code")
        if code is not None:
            path = code["file"]
            if path not in cache:
                cache[path] = rustsrc.function_bodies((root / path).read_text())
            body = cache[path].get(code["symbol"])
            if body is None:
                raise RuntimeError(f"cannot bless: {path}::{code['symbol']} not found")
            code["body_sha256"] = rustsrc.body_sha256(body)
            code["guard_surface"] = rustsrc.guard_surface(body)
    TABLE_PATH.write_text(json.dumps(table, indent=1, sort_keys=True) + "\n")
    print(f"blessed {len(table['entries'])} entries")


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--bless", action="store_true",
                        help="re-record checksums after re-reading both sides")
    args = parser.parse_args(argv)

    if args.bless:
        bless()
        return 0

    sources = load_sources()
    table = sources["table"]
    counts = {}
    for klass in (entry["correspondence"] for entry in table["entries"]):
        counts[klass] = counts.get(klass, 0) + 1

    results = findings(sources)
    by_kind = {}
    for kind, subject, detail in results:
        by_kind.setdefault(kind, []).append((subject, detail))

    print("LEAN <-> IMPLEMENTATION CORRESPONDENCE")
    print(f"  entries: {len(table['entries'])}  "
          + "  ".join(f"{klass}={count}" for klass, count in sorted(counts.items())))
    print(f"  fixtures: {len(sources['fixtures'])}  "
          f"corpus declarations seen: {len(sources['corpus'])}")
    print()

    failed = False
    for kind, budget in sorted(BUDGETS.items()):
        rows = by_kind.get(kind, [])
        status = "OK" if len(rows) <= budget else "FAIL"
        if len(rows) > budget:
            failed = True
        print(f"  {kind:<16} {len(rows):>3}, budget {budget}   {status}")
        for subject, detail in rows:
            print(f"      {subject}: {detail}")

    print()
    if failed:
        print("FAIL: the corpus and the implementation are not verified to agree.")
        return 1
    print("PASS: every mapped declaration still describes the code it is mapped to.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
