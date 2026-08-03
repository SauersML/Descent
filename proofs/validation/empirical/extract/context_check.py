"""Arm (b): a repoint that landed in a tactic argument list.

    python3 validation/extract/context_check.py [--self-test]

THE HAZARD, from a live instance.  `fstDriftMutation p` was a wrapper with body
`fstMutationDriftEquilibrium p.theta`.  It was removed as a duplicate and its
call sites repointed BY NAME, TEXTUALLY.  Where the occurrence sat in an
`unfold` list -- a context that takes BARE CONSTANT NAMES -- the substitution
produced

    unfold fstEquilibrium fstMutationDriftEquilibrium fstMutationDriftEquilibrium.theta

with the ` p.theta` argument glued onto the constant name.  Lean rejected it
because `Calibrator.fstMutationDriftEquilibrium.theta` is not a constant.

IT WAS CAUGHT ONLY BECAUSE THE MANGLING HAPPENED TO PRODUCE A NON-CONSTANT.  A
textual repoint that stays well-formed compiles silently.  So the general defect
is that TEXTUAL SUBSTITUTION IS NOT SHAPE-AWARE: a source position that held an
APPLICATION was rewritten into a position that requires a NAME.  `unfold`,
`simp only [...]` and `rw [...]` are those positions.

WHY THIS ARM IS WORTH MORE THAN THE PERMUTATION ARM.  The permutation hazard
needs an ASYMMETRIC body to bite, and this corpus's one real permutation had a
symmetric body, so it was harmless.  This hazard bites whenever the SHAPES
differ, which is common -- every wrapper whose body is an application is a
candidate.  It also needs no body evaluation at all: it is decidable from the
text plus the definition table.

THE RULE.  In a tactic argument list, a token `X.y` where `X` is a DEFINITION is
a defect: you cannot project a field out of a function.  `X.y` where `X` is a
STRUCTURE or a namespace is ordinary and correct -- `HardyWeinbergModel.genotypeProb`
is a real constant.  The definition table is what tells the two apart, which is
why this check lives here rather than in a linter.

READ-ONLY.  This reports; it does not repair.  It never edits a file and never
recommends a git operation as a remedy.  Output goes to whoever owns the file.
"""
from __future__ import annotations

import argparse
import json
import pathlib
import re
import sys

HERE = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))

import api                                                # noqa: E402

PROOFS = HERE.parent.parent

# Tactic positions that require a bare constant name.
UNFOLD_RE = re.compile(r"\bunfold\s+([^\n;]+)")
BRACKET_RE = re.compile(r"\b(?:simp only|simp|rw|rewrite|unfold_let)\s*\[([^\]]*)\]")
TOKEN_RE = re.compile(r"[A-Za-z_][A-Za-z0-9_'₀-₉ₐ-ₜ.]*")


def tactic_name_positions(src):
    """(line_no, tactic, token) for every token in a name-only tactic position."""
    out = []
    for i, line in enumerate(src.splitlines(), 1):
        for m in UNFOLD_RE.finditer(line):
            for t in TOKEN_RE.findall(m.group(1)):
                out.append((i, "unfold", t))
        for m in BRACKET_RE.finditer(line):
            for t in TOKEN_RE.findall(m.group(1)):
                out.append((i, "simp/rw", t))
    return out


def classify_token(tok, defs_short, struct_short):
    """Why this token in a name position is suspect, or None."""
    if "." not in tok:
        return None
    head, rest = tok.split(".", 1)
    if head in struct_short:
        return None                     # a real projection: Structure.field
    if head in defs_short:
        return (f"`{head}` is a DEFINITION, so `{tok}` cannot be a constant -- "
                f"this looks like an argument glued onto a name by a textual "
                f"repoint")
    return None                         # unknown head: Mathlib, namespace, local


def scan(defs_short, struct_short):
    findings = []
    # `rglob` under Calibrator/ does NOT reach `proofs/Calibrator.lean`, the corpus
    # ROOT, which sits one level above it. A scan blind to the root reported two
    # definitions as unreferenced and they were deleted; their only consumer was a
    # theorem in the root. `lean_parse.build` already carries this `extra` idiom --
    # keep the three in step.
    _root = PROOFS / "Calibrator.lean"
    _paths = sorted((PROOFS / "Calibrator").rglob("*.lean"))
    if _root.exists():
        _paths.append(_root)
    for path in _paths:
        src = path.read_text(errors="ignore")
        rel = str(path.relative_to(PROOFS))
        for line_no, tactic, tok in tactic_name_positions(src):
            why = classify_token(tok, defs_short, struct_short)
            if why:
                findings.append({"file": rel, "line": line_no,
                                 "tactic": tactic, "token": tok, "why": why})
    return findings


def self_test(defs_short, struct_short):
    """Positive AND negative control. Both must hold or the scan is meaningless."""
    ok = True

    a_def = next(iter(sorted(defs_short)), None)
    a_struct = next(iter(sorted(struct_short)), None)
    if a_def is None or a_struct is None:
        print("  SELF-TEST FAIL: no definitions or no structures in the table")
        return False

    # POSITIVE: an argument glued onto a definition name must be flagged.
    synth = f"  unfold fstEquilibrium {a_def} {a_def}.theta"
    toks = tactic_name_positions(synth)
    hits = [t for _, _, t in toks if classify_token(t, defs_short, struct_short)]
    if f"{a_def}.theta" in hits:
        print(f"  ok  positive control: `{a_def}.theta` in an unfold list flagged")
    else:
        print(f"  SELF-TEST FAIL: `{a_def}.theta` not flagged; got {hits}")
        ok = False

    # NEGATIVE: a real structure projection must NOT be flagged.
    synth2 = f"  simp only [{a_struct}.someField, mul_comm]"
    toks2 = tactic_name_positions(synth2)
    hits2 = [t for _, _, t in toks2 if classify_token(t, defs_short, struct_short)]
    if hits2:
        print(f"  SELF-TEST FAIL: real projection `{a_struct}.someField` flagged: {hits2}")
        ok = False
    else:
        print(f"  ok  negative control: `{a_struct}.someField` correctly not flagged")

    # NEGATIVE: a bare name must never be flagged.
    if [t for _, _, t in tactic_name_positions(f"  unfold {a_def}")
            if classify_token(t, defs_short, struct_short)]:
        print("  SELF-TEST FAIL: a bare definition name was flagged")
        ok = False
    else:
        print("  ok  negative control: a bare definition name not flagged")
    return ok


def main(argv=None):
    ap = argparse.ArgumentParser()
    ap.add_argument("--self-test", action="store_true")
    a = ap.parse_args(argv)

    api.refresh()
    defs_short = {n.split(".")[-1] for n in api.definition_table()}
    struct_short = {n.split(".")[-1] for n in api.structures()}
    # A name that is BOTH is treated as a structure: the projection is legal.
    defs_short -= struct_short

    print("=" * 74)
    print("TACTIC-POSITION REPOINT DETECTOR  (arm b)")
    print("=" * 74)
    print("controls:")
    if not self_test(defs_short, struct_short):
        print("\nDETECTOR NOT KNOWN CAPABLE OF FIRING -- results below mean nothing")
        return 2
    if a.self_test:
        return 0

    findings = scan(defs_short, struct_short)
    print(f"\ndefinitions in table: {len(defs_short)}   structures: {len(struct_short)}")
    print(f"\nSUSPECT tactic-position tokens: {len(findings)}")
    for f in findings:
        print(f"  {f['file']}:{f['line']}  [{f['tactic']}]  {f['token']}")
        print(f"      {f['why']}")
    if not findings:
        print("  none. The controls above show the check can fire, so this is a")
        print("  result rather than a silence -- but it only covers the CURRENT")
        print("  corpus, and only the case where the mangling produced a")
        print("  projection onto a definition. A repoint that stayed well-formed")
        print("  is invisible to this and to the compiler alike.")

    (HERE / "context_check.json").write_text(json.dumps(
        {"findings": findings, "n_definitions": len(defs_short),
         "n_structures": len(struct_short)}, indent=1))
    print(f"\nwritten: {HERE / 'context_check.json'}")
    return 1 if findings else 0


if __name__ == "__main__":
    sys.exit(main())
