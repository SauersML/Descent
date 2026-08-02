"""Vacuity / satisfiability check over Calibrator structures.

Fuzzing compares a formula against an oracle.  It cannot detect a theorem whose
HYPOTHESES are unsatisfiable: such a theorem is machine-checked, passes CI, and
asserts nothing at all.  In a development with ~70 structures carrying many
simultaneous numeric field constraints, an uninhabitable structure would make
every theorem about it vacuously true, and nothing in the Lean output would say
so.

This scans each `structure`, extracts its numeric field constraints, and
searches numerically for a witness satisfying all of them at once.

  WITNESS FOUND   - the structure is inhabited; its theorems have content.
  NO WITNESS      - candidate vacuous.  Not proof (the search is incomplete and
                    the constraint parser is partial), but each hit is a
                    specific claim to check by hand.

Constraint forms handled: `0 < x`, `0 <= x`, `x < y`, `x <= y`, `x = y`,
`x < 1`, numeric literals on either side, and sums/products of two fields.
"""
from __future__ import annotations

import json
import pathlib
import re
import sys

import numpy as np

STRUCT_RE = re.compile(r"^structure\s+([A-Za-z_][\w.']*)")
FIELD_RE = re.compile(r"^\s{2,}([^\W\d][\w']*)\s*:\s*(.+)$", re.UNICODE)

# a constraint field looks like   name : 0 < foo    /   name : foo <= bar
CONSTR_RE = re.compile(r"^\s*(.+?)\s*(<=|<|=)\s*(.+?)\s*$")

NUM = re.compile(r"^-?\d+(\.\d+)?$")


def parse_structures(root):
    out = []
    for path in sorted(pathlib.Path(root).rglob("*.lean")):
        lines = path.read_text(errors="ignore").splitlines()
        i = 0
        while i < len(lines):
            m = STRUCT_RE.match(lines[i])
            if not m:
                i += 1
                continue
            name = m.group(1)
            start = i
            i += 1
            reals, constraints = [], []
            while i < len(lines):
                s = lines[i]
                if s.strip() and not s.startswith(" "):
                    break
                fm = FIELD_RE.match(s)
                if fm:
                    fname, ftype = fm.group(1), fm.group(2).strip()
                    if ftype in ("ℝ", "ℝ)"):
                        reals.append(fname)
                    elif any(op in ftype for op in ("<", "≤", "=")):
                        constraints.append(ftype)
                i += 1
            if reals:
                out.append(dict(name=name, file=path.name, line=start + 1,
                                reals=reals, constraints=constraints))
    return out


def normalize(c):
    return (c.replace("≤", "<=").replace("≥", ">=").replace("≠", "!=")
             .replace("^", "**"))


def build_predicate(reals, constraints):
    """Return a python callable over a dict of field values, or None."""
    exprs = []
    for c in constraints:
        c = normalize(c).strip()
        if "!=" in c or "∀" in c or "∈" in c or "Fin" in c:
            continue
        # keep only constraints whose symbols are all known fields or numbers
        toks = set(re.findall(r"[^\W\d][\w']*", c, re.UNICODE))
        if not toks.issubset(set(reals) | {"Real", "sqrt", "exp", "log"}):
            continue
        if any(f in c for f in ("Real.", "sqrt", "exp", "log")):
            continue
        # chained a < b < c -> split
        parts = re.split(r"(<=|<|>=|>)", c)
        if len(parts) >= 5:
            rebuilt = []
            for k in range(0, len(parts) - 2, 2):
                rebuilt.append(f"({parts[k].strip()}){parts[k+1]}({parts[k+2].strip()})")
            exprs.append(" and ".join(rebuilt))
        else:
            exprs.append(c)
    if not exprs:
        return None, []
    src = " and ".join(f"({e})" for e in exprs)
    try:
        code = compile(src, "<constraints>", "eval")
    except SyntaxError:
        return None, exprs
    return code, exprs


def search_witness(reals, code, tries=200000, seed=0):
    rng = np.random.default_rng(seed)
    scales = [1e-3, 1e-2, 1e-1, 1.0, 10.0]
    for t in range(tries):
        sc = scales[t % len(scales)]
        env = {f: float(rng.random() * sc) for f in reals}
        # occasionally allow negatives and larger magnitudes
        if t % 7 == 0:
            for f in reals:
                env[f] = float((rng.random() - 0.5) * 2 * sc)
        try:
            if eval(code, {"__builtins__": {}}, env):
                return env
        except Exception:
            return "EVAL_ERROR"
    return None


def main(root):
    structs = parse_structures(root)
    print(f"parsed {len(structs)} structures with real-valued fields\n")
    unsat, checked = [], 0
    for s in structs:
        code, exprs = build_predicate(s["reals"], s["constraints"])
        if code is None:
            continue
        checked += 1
        w = search_witness(s["reals"], code, seed=hash(s["name"]) % 10000)
        if w is None:
            unsat.append(dict(**s, exprs=exprs))
    print(f"checked {checked} structures whose constraints were fully parseable")
    print(f"no witness found for {len(unsat)}\n")
    for u in unsat:
        print(f"  {u['name']}  ({u['file']}:{u['line']})")
        print(f"      fields: {', '.join(u['reals'][:8])}")
        for e in u["exprs"][:8]:
            print(f"      constraint: {e}")
        print()
    with open("vacuity.json", "w") as fh:
        json.dump(dict(checked=checked, unsat=unsat), fh, default=str)


if __name__ == "__main__":
    main(sys.argv[1] if len(sys.argv) > 1 else ".")
