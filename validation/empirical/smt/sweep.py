"""Corpus-wide sweep for VACUOUS and TAUTOLOGICAL theorem statements.

    python3 sweep.py selftest     # both-directions calibration; run this first
    python3 sweep.py scan         # sweep Descent/

STATUS: DIAGNOSTIC.  Needs z3, and the scan is a minute rather than the ~20s
the gated empirical steps get in total, so it is not wired into prover.yml.
`selftest` alone is fast and dependency-light enough to promote later.

WHAT THIS IS FOR.  The corpus has no `sorry` and no custom `axiom`, so every
statement in it is kernel-checked and none of them can be FALSE.  Counterexample
search therefore has nothing to find, and the two defects that can still hide
behind a valid proof are:

    VACUOUS      the hypotheses contradict each other, so the theorem is true
                 and says nothing about anything;
    TAUTOLOGICAL the conclusion holds with no hypotheses at all, so every
                 biological premise in the statement is decoration.

SOUNDNESS, which is the entire design.  There is no verified Lean-to-SMT
translator here and there is not going to be one.  Instead every construct that
cannot be translated is replaced by something STRICTLY MORE PERMISSIVE:

    unknown definition  f a b     ->  an uninterpreted real function
    unparseable hypothesis        ->  DROPPED entirely
    unparseable subterm           ->  a fresh unconstrained real

Relaxing or dropping hypotheses can only ENLARGE the set of models.  So:

    z3 says UNSAT on the hypotheses
      => the real hypothesis set is unsatisfiable too
      => VACUOUS, soundly.

and symmetrically, UNSAT on a negated conclusion with no hypotheses asserted
means the conclusion is valid under every interpretation, hence a tautology.
SAT carries NO information under this encoding and is never reported.  That
asymmetry is what makes the sweep trustworthy without a verified translation --
and it is also its limitation: the sweep cannot tell you a statement is fine,
only that it failed to prove it degenerate.

A SECOND LIMITATION, stated because a reader will otherwise over-read the
redundancy output: the redundancy probe removes ONE hypothesis at a time.
Hypotheses that are each individually redundant are frequently not JOINTLY
redundant, so this output does not license removing several at once.  The
sound way to drop premises is to scan the kernel-accepted proof term for
binders that do not occur in it -- and even that is only valid against the
statement it was computed on, which is how a correct trim and a correct
inversion combined into a false theorem in AssortativeMatingPGS.lean.

Measured 2026-08-04 on the whole corpus: 0 vacuous of 1861 checkable
hypothesis-carrying theorems, 0 tautological of 1065 checkable conclusions.
"""
from __future__ import annotations

import json
import os
import re
import sys

try:
    from z3 import Solver, Real, Not, And, sat, unsat, unknown
except ImportError:                                        # pragma: no cover
    print("z3 is not installed; this is a DIAGNOSTIC check. "
          "Install with: pip install z3-solver")
    raise SystemExit(0)

import leansmt
from leansmt import parse_prop

HERE = os.path.dirname(os.path.abspath(__file__))
CORPUS = os.path.normpath(
    os.path.join(HERE, "..", "..", "..", "Descent"))
TIMEOUT_MS = 4000

HYPBIND = re.compile(r"\(\s*h[A-Za-z0-9_'₀-₉]*\s*:")


# --------------------------------------------------------------------------
# statement extraction
# --------------------------------------------------------------------------
def _match_close(s, i, op, cl):
    d = 0
    for k in range(i, len(s)):
        if s[k] == op:
            d += 1
        elif s[k] == cl:
            d -= 1
            if d == 0:
                return k
    return None


def strip_comments(t):
    return re.sub(r"--[^\n]*", " ", t)


def split_binders(stmt):
    """(real var names, [(hyp name, prop text)], conclusion text)."""
    m = re.match(r"(theorem|lemma)\s+[A-Za-z0-9_'.₀-₉]+\s*", stmt)
    body = stmt[m.end():] if m else stmt
    reals, hyps, i = [], [], 0
    while i < len(body):
        if body[i] == "{":
            j = _match_close(body, i, "{", "}")
        elif body[i] == "(":
            j = _match_close(body, i, "(", ")")
        elif body[i].isspace():
            i += 1
            continue
        else:
            break
        if j is None:
            break
        inner = body[i + 1:j]
        if ":" in inner:
            lhs, rhs = inner.split(":", 1)
            names = lhs.split()
            if rhs.strip() == "ℝ":
                reals.extend(names)
            elif names and all(n[0] == "h" for n in names):
                for n in names:
                    hyps.append((n, rhs.strip()))
        i = j + 1
    concl = body[i:].lstrip()
    if concl.startswith(":"):
        concl = concl[1:].strip()
    return reals, hyps, concl


def theorems(path):
    src = open(path, encoding="utf-8", errors="replace").read()
    out = []
    for m in re.finditer(r"^(theorem|lemma)\s+([A-Za-z0-9_'.₀-₉]+)",
                         src, re.M):
        rest = src[m.start():]
        e = re.search(r":=\s*(by\b|\n)", rest)
        if not e:
            continue
        stmt = rest[:e.start()]
        if len(stmt) > 4000:
            continue
        out.append((m.group(2), " ".join(stmt.split())))
    return out


# --------------------------------------------------------------------------
# probes.  Only UNSAT is ever reported.
# --------------------------------------------------------------------------
def _build(stmt):
    leansmt.UNINTERP.clear()
    leansmt.SQRT_FACTS.clear()
    reals, hyps, concl = split_binders(strip_comments(stmt))
    env = {n: Real(n) for n in reals}
    kept, dropped = [], 0
    for _n, prop in hyps:
        try:
            kept.append(parse_prop(prop, env))
        except Exception:
            dropped += 1                 # DROPPING IS SOUND: over-approximation
    try:
        C = parse_prop(concl, env)
    except Exception:
        C = None
    return kept, dropped, C, list(leansmt.SQRT_FACTS)


def _ask(assertions):
    s = Solver()
    s.set("timeout", TIMEOUT_MS)
    for a in assertions:
        s.add(a)
    return s.check()


def vacuity(stmt):
    kept, dropped, _C, facts = _build(stmt)
    if not kept:
        return "SKIP", dropped
    r = _ask(kept + facts)
    if r == unsat:
        return "VACUOUS", dropped
    if r == unknown:
        return "UNKNOWN", dropped        # never folded into "clean"
    return "SAT", dropped


def tautology(stmt):
    kept, _dropped, C, facts = _build(stmt)
    if C is None or not kept:
        return "SKIP"
    r = _ask([Not(C)] + facts)
    if r == unsat:
        return "TRIVIAL"
    if r == unknown:
        return "UNKNOWN"
    return "OK"


# --------------------------------------------------------------------------
# calibration: both directions, planted defects and clean input
# --------------------------------------------------------------------------
SELFTEST = [
    # (label, statement, expected vacuity, expected tautology)
    ("clean-arithmetic",
     "theorem t (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : a * b > 0",
     "SAT", "OK"),
    ("vacuous-direct",
     "theorem t (f : ℝ) (h1 : 0 < f) (h2 : f < 0) : f = 12345",
     "VACUOUS", None),
    ("vacuous-chain",
     "theorem t (x y z : ℝ) (h1 : x < y) (h2 : y < z) (h3 : z < x) : x = 0",
     "VACUOUS", None),
    ("vacuous-nonlinear",
     "theorem t (r : ℝ) (h1 : 0 ≤ r) (h2 : r ≤ 1) "
     "(h3 : r * r > r + 1) : r = 0",
     "VACUOUS", None),
    ("satisfiable-but-tight",
     "theorem t (p : ℝ) (hp : 0 < p) (hp1 : p < 1) "
     "(hq : p * (1 - p) = 1/4) : p = 0",
     "SAT", None),
    ("unknown-def-must-not-invent-a-contradiction",
     "theorem t (a b : ℝ) (ha : 0 < a) (hd : epistaticVariance a b = 7) "
     ": a > 0",
     "SAT", None),
    ("unknown-def-applied-twice-is-consistent",
     "theorem t (a b : ℝ) (h1 : epistaticVariance a b = 7) "
     "(h2 : epistaticVariance a b = 9) : a > 0",
     "VACUOUS", None),
    ("dropped-hypothesis-must-not-create-vacuity",
     "theorem t (a : ℝ) (h1 : ∀ i, 0 ≤ a) (h2 : 0 < a) : a > 0",
     "SAT", None),
    ("tautology-plain",
     "theorem t (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : a * a ≥ 0",
     None, "TRIVIAL"),
    ("tautology-dressed-in-biology",
     "theorem t (h2 port fst : ℝ) (hh : 0 ≤ h2) (hp : 0 ≤ port) "
     "(hf : 0 ≤ fst) : h2 * port ≤ h2 * port",
     None, "TRIVIAL"),
    ("tautology-over-an-unknown-def",
     "theorem t (a b : ℝ) (ha : 0 < a) "
     ": epistaticVariance a b = epistaticVariance a b",
     None, "TRIVIAL"),
    ("real-claim-about-a-def-is-not-a-tautology",
     "theorem t (a b : ℝ) (ha : 0 < a) : epistaticVariance a b > 0",
     None, "OK"),
    ("genuine-content-is-not-a-tautology",
     "theorem t (r : ℝ) (h0 : 0 ≤ r) (h1 : r ≤ 1) : r * r ≤ r",
     None, "OK"),
]


def selftest() -> int:
    bad = []
    for label, stmt, want_vac, want_taut in SELFTEST:
        if want_vac is not None:
            got, _ = vacuity(stmt)
            if got != want_vac:
                bad.append(f"{label}: vacuity expected {want_vac}, got {got}")
        if want_taut is not None:
            got = tautology(stmt)
            if got != want_taut:
                bad.append(f"{label}: tautology expected {want_taut}, got {got}")
    for line in bad:
        print("  * " + line)
    n = sum(1 for _l, _s, v, t in SELFTEST for x in (v, t) if x is not None)
    if bad:
        print(f"SWEEP CALIBRATION FAILED ({len(bad)} of {n} assertions)")
        return 1
    print(f"sweep calibration OK: {n} assertions, both directions "
          f"(planted vacuous/tautological statements are caught; clean "
          f"statements and unknown definitions are not flagged)")
    return 0


def scan() -> int:
    counts_v, counts_t = {}, {}
    vacuous, trivial, unknowns = [], [], []
    n_thm = 0
    for dirpath, _d, files in os.walk(CORPUS):
        for f in sorted(files):
            if not f.endswith(".lean"):
                continue
            path = os.path.join(dirpath, f)
            rel = os.path.relpath(path, CORPUS)
            for name, stmt in theorems(path):
                n_thm += 1
                if not HYPBIND.search(stmt):
                    continue
                v, _dropped = vacuity(stmt)
                counts_v[v] = counts_v.get(v, 0) + 1
                if v == "VACUOUS":
                    vacuous.append((rel, name))
                elif v == "UNKNOWN":
                    unknowns.append((rel, name, "vacuity"))
                elif v == "SAT":
                    t = tautology(stmt)
                    counts_t[t] = counts_t.get(t, 0) + 1
                    if t == "TRIVIAL":
                        trivial.append((rel, name))
                    elif t == "UNKNOWN":
                        unknowns.append((rel, name, "tautology"))

    print(f"{n_thm} theorems scanned")
    print("vacuity:   " + json.dumps(counts_v))
    print("tautology: " + json.dumps(counts_t))
    for rel, name in vacuous:
        print(f"VACUOUS   {rel}  {name}")
    for rel, name in trivial:
        print(f"TRIVIAL   {rel}  {name}")
    for rel, name, which in unknowns:
        print(f"UNKNOWN   {rel}  {name}  ({which} probe: z3 returned unknown; "
              f"this is NOT a clean result)")
    if unknowns:
        print(f"\n{len(unknowns)} probes returned unknown. A timeout is "
              f"reported as a timeout, never as clean.")
    return 1 if (vacuous or trivial or unknowns) else 0


if __name__ == "__main__":
    mode = sys.argv[1] if len(sys.argv) > 1 else "selftest"
    raise SystemExit(selftest() if mode == "selftest" else scan())
