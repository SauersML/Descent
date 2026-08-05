"""Structure field tables, so a definition that takes a model can be checked.

WHY THIS EXISTS

`compile_defs.transpile_all` accepts a definition only when its return type and
every parameter type is `ℝ` or `ℕ`.  That rejected 422 definitions -- by far the
largest single block of the coverage gap -- and the recorded reason was
`non-scalar signature (ℝ)`, which reads as though the return type were at fault.
It is not.  These are structure methods:

    AssortativeMatingPGS.AssortativeMatingModel.observedH2   params ['m']   ret ℝ

The parameter is a model, the return type is exactly the scalar the checker
wants, and the message printed the return type because that is what the check
had to hand.  A third of the corpus was filed under a reason that pointed at the
wrong half of the signature.

WHAT THIS DOES

Reads the `structure` declarations out of the Lean source and records, per
structure:

  * `fields` -- the `ℝ` and `ℕ` valued fields, which are the data;
  * `constraints` -- the `Prop` valued fields, which are the domain.

Both halves are needed and the second is the one it would be tempting to drop.
A structure like `MRInstrumentModel` carries `n_pos : 0 < n` alongside `n : ℝ`.
Flattening the model to its numeric fields and forgetting the constraints would
let the sampler evaluate at `n = -1000`, and every range check downstream would
then report an escape that the Lean statement excludes by construction.  That is
manufacturing defects, which the totality scan's own docstring names as the
failure a checking tool must not commit.  So the constraints travel with the
fields and are attached as hypotheses of the flattened definition.

WHAT IT DOES NOT DO

Nothing here evaluates or transpiles.  It is a table.  Whether a given structure
method can then be transpiled depends on its body: a body that only projects
fields flattens, and a body that calls another structure method does not until
that method is itself flattened.  `compile_defs` decides that and records its own
reason.

Run:  python3 structures.py            # summary
      python3 structures.py --json     # the table
"""

from __future__ import annotations

import json
import pathlib
import re
import sys

CAL = pathlib.Path(__file__).resolve().parents[3] / "Descent"

# `structure Name ... where`, possibly with parameters and a `extends` clause.
STRUCT_RE = re.compile(r"^structure\s+([\w.'₀-₉]+)[^\n]*\bwhere\s*$")

# An indented `name : type` line inside a structure block.  Field names in this
# corpus are plain identifiers; the type runs to end of line.
FIELD_RE = re.compile(r"^\s{2,}([\w'₀-₉]+)\s*:\s*(\S.*?)\s*$")

# A line that ends a structure block: anything at column zero that starts a new
# declaration, or a blank-line-then-unindented run.
END_RE = re.compile(
    r"^(?:@\[|/--|/-!|noncomputable\s|def\s|theorem\s|lemma\s|abbrev\s|structure\s|"
    r"inductive\s|instance\s|namespace\s|end\s|section\s|open\s|variable\s|#)"
)

SCALAR = {"ℝ", "ℕ"}


def extract(root: pathlib.Path | None = None) -> dict:
    """`{structure name: {"fields": [[name, type]], "constraints": [str], ...}}`."""
    root = root or CAL
    table: dict[str, dict] = {}
    for path in sorted(root.rglob("*.lean")):
        lines = path.read_text(encoding="utf-8", errors="replace").splitlines()
        i = 0
        while i < len(lines):
            m = STRUCT_RE.match(lines[i])
            if not m:
                i += 1
                continue
            name = m.group(1)
            fields: list[list[str]] = []
            constraints: list[str] = []
            j = i + 1
            while j < len(lines):
                line = lines[j]
                if line.strip() == "":
                    j += 1
                    continue
                if not line.startswith(" ") or END_RE.match(line):
                    break
                fm = FIELD_RE.match(line)
                if fm:
                    fname, ftype = fm.group(1), fm.group(2)
                    # A docstring line inside the block is not a field.
                    if ftype.startswith("--") or fname.startswith("--"):
                        j += 1
                        continue
                    if ftype in SCALAR:
                        fields.append([fname, ftype])
                    else:
                        # Everything else in a structure body is a proof
                        # obligation: the domain the data has to live in.
                        constraints.append(ftype)
                j += 1
            table[name] = dict(
                module=path.stem,
                fields=fields,
                constraints=constraints,
                all_scalar=bool(fields) and len(fields) + len(constraints)
                == len(fields) + len(constraints),
            )
            i = j
    return table


def flattenable(table: dict) -> dict:
    """Structures with at least one scalar field, keyed by name."""
    return {k: v for k, v in table.items() if v["fields"]}


def main(argv: list[str]) -> int:
    table = extract()
    if "--json" in argv:
        print(json.dumps(table, ensure_ascii=False, indent=1))
        return 0
    flat = flattenable(table)
    nfields = sum(len(v["fields"]) for v in flat.values())
    ncons = sum(len(v["constraints"]) for v in flat.values())
    print(f"structures found ........ {len(table)}")
    print(f"with scalar fields ...... {len(flat)}")
    print(f"scalar fields total ..... {nfields}")
    print(f"constraint fields ....... {ncons}")
    print()
    print("largest, by scalar field count:")
    for name, v in sorted(flat.items(), key=lambda kv: -len(kv[1]["fields"]))[:12]:
        fs = ", ".join(f for f, _ in v["fields"])
        print(f"  {len(v['fields']):2d}  {name:44s} {fs[:60]}")
    return 0


if __name__ == "__main__":
    out = pathlib.Path(__file__).with_name("structures.json")
    table = extract()
    out.write_text(json.dumps(table, ensure_ascii=False, indent=1), encoding="utf-8")
    raise SystemExit(main(sys.argv[1:]))
