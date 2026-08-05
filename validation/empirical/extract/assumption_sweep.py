"""What this corpus ASSUMES, counted rather than asserted.

    python3 validation/extract/assumption_sweep.py

There are no `sorry`s and no `axiom`s in `Descent` -- both verified by
this script, not taken on trust.  That is the badge the corpus wears, and it is
true.  It is also not the same claim as "no assumptions": MATH_LEDGER.md records
the house style of carrying unverifiable analytic inputs as NAMED STRUCTURE
FIELDS instead, "which is honest, but means a theorem name does not imply a
proof of the mathematics."  A `sorry` is greppable and CI counts it.  A
structure field looks like an ordinary parameter and nothing flags it.

So this counts them, and -- more importantly -- SEPARATES FOUR THINGS THAT LOOK
IDENTICAL in a field list and mean entirely different things:

  VACUOUS-TYPE   the field's type is bare `Prop`.  It states NOTHING: it is a
                 variable ranging over propositions, satisfiable by `True`.
                 `strongClosure : Prop` does not assert that closure holds; it
                 asserts nothing at all, and a docstring beside it is prose.
                 Not dischargeable (no proposition to prove), not external
                 (names no theorem), and possibly threaded through signatures
                 so not unused either.  It needs its own bin or every one of
                 them is filed wrongly.

  DOMAIN         a proposition relating only the structure's own data and
                 numerals: `0 < K`, `K < 1`, `V_A < V_P`, `∑ mass = 1`.  This is
                 NOT an assumed theorem.  It is what a hypothesis in a theorem
                 statement does -- it says which instances the result is about.
                 It cannot be "discharged from Mathlib" because it is not true
                 in general, and deleting it makes theorems FALSE rather than
                 unconditional.

  ASSERTION      a proposition invoking a definition of the corpus or of
                 Mathlib: `Phi (liabilityThreshold K) = 1 - K`.  These are the
                 dischargeable candidates -- statements ABOUT the development's
                 own functions, which someone could prove.

  EXTERNAL       an assumed theorem: a field named `theorem1`, a structure named
                 `Assumed*`, a characterisation stated as an `↔`.  Every result
                 downstream of one is conditional.

It also reports theorems whose own binder names begin with `_`.  That is Lean's
admission that the proof does not use the hypothesis, and it is a sharper defect
than an unused field: the signature advertises a premise doing work while no
part of the term depends on it, so the theorem is not merely carrying a spare
argument, it is claiming to be a different theorem.  Leave-one-out will not
catch these -- removing them leaves the build green, which files them as merely
unused and undersells what they were doing.

  A USED HYPOTHESIS IS A TYPED ARGUMENT OF THE THEOREM THAT NEEDS IT.
  AN UNUSED ONE IN A RECORD IS DECORATION.  The first cannot be overlooked;
  the second cannot be checked.

Nothing here deletes anything.  It produces the counts and the lists.
"""
from __future__ import annotations

import collections
import json
import pathlib
import re
import sys

HERE = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))

import lean_parse                                          # noqa: E402

CALIB = lean_parse.find_proofs_root(HERE) / "Descent"

REL = re.compile(r"[∀∃≤≥≠∧∨¬∈↔]|(?<![:<>=!])=(?!=)|<|>")
THEOREM_NAME = re.compile(r"^(theorem\d*|characterization|axiom|assum|premise|"
                          r"conjecture|law\d*|claim)", re.I)
ASSUMED_STRUCT = re.compile(r"^(Assumed|.*Conjecture|.*Premise)", re.I)
DECL = re.compile(r"^\s*(theorem|lemma)\s+([A-Za-z_][\w'.₀-₉]*)")
BIND = re.compile(r"[({]\s*(_[A-Za-z0-9_'₀-₉]*)\s*:\s*([^)}]*)[)}]")


def sweep():
    blob = json.loads((HERE / "defs.json").read_text())
    defnames = {d["short"] for d in blob["definitions"]}
    structs = {s["short"] for s in blob["structures"]}
    bare, domain, assertion, external = [], [], [], []
    for s in blob["structures"]:
        if s["kind"] not in ("structure", "class"):
            continue
        own = {f["name"] for f in s["fields"]}
        params = {n for a in s.get("args", []) for n in a["names"]}
        for f in s["fields"]:
            ty = " ".join(f["type"].split())
            rec = {"struct": s["short"], "field": f["name"], "type": ty,
                   "file": s["file"]}
            if ty == "Prop":
                bare.append(rec)
                continue
            if not REL.search(ty):
                continue                        # ordinary carried data
            if (THEOREM_NAME.match(f["name"]) or ASSUMED_STRUCT.match(s["short"])
                    or "↔" in ty):
                external.append(rec)
                continue
            toks = re.findall(r"[A-Za-z_][\w'₀-₉]*(?:\.[A-Za-z_][\w'₀-₉]*)*", ty)
            binders = set(re.findall(r"[∀∃]\s*([A-Za-z_][\w'₀-₉]*)", ty))
            invoked = {t for t in toks
                       if t.split(".")[0] not in own | params | binders
                       and (t.split(".")[0] in defnames or t.split(".")[0] in structs)}
            (assertion if invoked else domain).append(rec)
    return bare, domain, assertion, external


def unused_hypotheses():
    hits = []
    for fp in sorted(CALIB.rglob("*.lean")):
        lines = fp.read_text().splitlines()
        for i, ln in enumerate(lines):
            m = DECL.match(ln)
            if not m:
                continue
            sig, j = ln, i + 1
            while j < len(lines) and ":=" not in sig and j - i < 25:
                sig += " " + lines[j].strip()
                j += 1
            for b, ty in BIND.findall(sig.split(":=")[0]):
                if REL.search(ty):
                    hits.append((str(fp.relative_to(CALIB.parent)), i + 1,
                                 m.group(2), b, " ".join(ty.split())))
    return hits


def greppable_escape_hatches():
    """`sorry` and `axiom`, counted from the source rather than assumed absent."""
    # BLOCK-COMMENT AWARE, and it has to be.  A line-prefix filter reported 9
    # `sorry`s in this corpus and every one of them was PROSE -- continuation
    # lines inside `/-- ... -/` docstrings that discuss the house style of
    # carrying assumptions as fields "rather than as `sorry`s".  Those lines do
    # not begin with a comment marker, so a prefix test counts them as code.
    # Reporting 9 would have been a false finding of exactly the kind this file
    # exists to prevent, in the file that prevents it.
    n_sorry = n_axiom = 0
    for fp in sorted(CALIB.rglob("*.lean")):
        depth = 0
        for ln in fp.read_text().splitlines():
            code, i = [], 0
            while i < len(ln):
                if depth == 0 and ln.startswith("--", i):
                    break
                if ln.startswith("/-", i):
                    depth += 1
                    i += 2
                    continue
                if ln.startswith("-/", i):
                    depth = max(0, depth - 1)
                    i += 2
                    continue
                if depth == 0:
                    code.append(ln[i])
                i += 1
            line = "".join(code)
            if re.search(r"(?<![\w'])sorry(?![\w'])", line):
                n_sorry += 1
            if line.strip().startswith("axiom "):
                n_axiom += 1
    return n_sorry, n_axiom


def main():
    print(f"corpus : {CALIB}")
    print(f"table  : {(HERE / 'defs.json').resolve()}\n")
    n_sorry, n_axiom = greppable_escape_hatches()
    bare, domain, assertion, external = sweep()
    hits = unused_hypotheses()
    tot = len(bare) + len(domain) + len(assertion) + len(external)
    print("=" * 74)
    print("WHAT IS GREPPABLE (what CI already counts)")
    print("=" * 74)
    print(f"  sorry : {n_sorry}")
    print(f"  axiom : {n_axiom}")
    print("\n" + "=" * 74)
    print("WHAT IS NOT GREPPABLE: propositions carried as structure fields")
    print("=" * 74)
    print(f"  VACUOUS-TYPE  bare `Prop`, states nothing : {len(bare):4d}")
    print(f"  DOMAIN        restricts the caller's data : {len(domain):4d}")
    print(f"  ASSERTION     about a definition          : {len(assertion):4d}")
    print(f"  EXTERNAL      an assumed theorem          : {len(external):4d}")
    print(f"  {'total':<41}: {tot:4d}")
    for label, rows in (("VACUOUS-TYPE", bare), ("EXTERNAL", external)):
        print(f"\n--- {label}")
        for r in rows:
            print(f"    {r['struct']}.{r['field']}  [{r['file'].split('/')[-1]}]")
            if r["type"] != "Prop":
                print(f"        {r['type'][:110]}")
    print("\n" + "=" * 74)
    print("THEOREMS WHOSE OWN BINDER SAYS THE PROOF DOES NOT USE THE HYPOTHESIS")
    print("=" * 74)
    print(f"  hypotheses: {len(hits)}   distinct theorems: "
          f"{len({(h[0], h[2]) for h in hits})}")
    for k, v in collections.Counter(h[0].split('/')[-1] for h in hits).most_common(12):
        print(f"    {v:3d}  {k}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
