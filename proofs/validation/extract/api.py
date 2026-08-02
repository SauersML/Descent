"""Canonical, stable interface to the Calibrator definition table.

This is the one parse of proofs/Calibrator/ that every checker should consume.
Import it; do not re-parse Lean.

    import sys; sys.path.insert(0, "proofs/validation/extract")
    import api

    api.definition_table()                 -> dict[str, Definition]
    api.definition("Calibrator.coalFst")   -> Definition
    api.callable_for("Calibrator.coalFst") -> (fn, ["t", "Ne"])
    api.body_checksum("Calibrator.coalFst")-> "sha256:..."
    api.stamp()                            -> corpus-wide fingerprint

Everything is keyed by FULLY-QUALIFIED Lean name (`Calibrator.coalFst`,
`Calibrator.R2DecompositionData.calibration`).  `api.resolve("coalFst")` maps a
bare name to its fully-qualified form and raises if it is ambiguous.

Definition fields (see also defs.json, which is this table serialised):

    name            str    fully-qualified, e.g. "Calibrator.coalFst"
    short           str    last component, e.g. "coalFst"
    kind            str    "def" | "abbrev"
    noncomputable   bool
    file            str    repo-relative, e.g. "Calibrator/PopulationGeneticsFoundations.lean"
    line            int    1-based line of the declaration header
    signature       str    source text between the name and the top-level ":="
    args            list   ORDERED binder groups, each:
                             {"names": [str], "type": str, "binder": "()"|"{}"|"[]",
                              "implicit": bool}
                           Explicit parameter order = [n for a in args
                                                       if not a["implicit"]
                                                       for n in a["names"]]
                           Types are Lean source text: "ℝ", "ℕ", "Fin q → ℝ", ...
    ret_type        str    Lean source text of the return type
    body            str    RAW Lean body source, exactly as written
    equations       list   for equation-compiler defs: [{"pattern","rhs"}]
    docstring       str    the `/-- ... -/` text, comment markers stripped
    empirical_status str   the "Empirical status:" marker, or ""
    namespace       str
    fields          list   structures only: [{"name","type"}]
    mentioned_by    list   fully-qualified names of theorems mentioning this def
    constraints     dict   mined domain/range facts:
                             hypotheses     [str]  UNION of the hypotheses of every
                                                   theorem mentioning this def.  NOT a
                                                   domain -- do not read it as a
                                                   conjunction.  coalFst carries
                                                   "100 * Ne < t" from one asymptotic
                                                   lemma; conjoining it would discard
                                                   almost every sensible F_ST point.
                             hypotheses_by_theorem
                                            dict   {theorem_name: [hypothesis, ...]}.
                                                   THIS is what a check should enforce:
                                                   the preconditions of the one theorem
                                                   whose claim is being tested.
                             range_lo/hi    float  bound PROVED by a theorem
                             range_lo_thm   [thm_name, n_hypotheses_of_that_thm]
                             range_hi_thm   [thm_name, n_hypotheses_of_that_thm]
                             declared_lo/hi float  bound merely IMPLIED by the
                                                   name/docstring -- a conjecture
                             declared_kind  str    "probability" | "F_ST" | ...
                             units          str    if the docstring states one

A theorem-proved bound and a docstring-implied bound are different kinds of
evidence and are stored separately on purpose.  Do not merge them: violating the
first is a defect, violating the second is a lead.  `admissible.declared_range`
returns both with provenance.
"""
from __future__ import annotations

import functools
import hashlib
import json
import pathlib
import sys

HERE = pathlib.Path(__file__).resolve().parent
if str(HERE) not in sys.path:
    sys.path.insert(0, str(HERE))

DEFS_JSON = HERE / "defs.json"
CLASSES_JSON = HERE / "classes.json"

__all__ = ["definition_table", "definition", "structures", "resolve",
           "callable_for", "classification", "body_checksum", "stamp",
           "admissible_box", "hypotheses", "refresh"]


# --------------------------------------------------------------- the table

@functools.lru_cache(maxsize=1)
def _blob():
    if not DEFS_JSON.exists():
        raise RuntimeError("defs.json missing; run: python3 "
                           "validation/extract/emit.py")
    return json.loads(DEFS_JSON.read_text())


@functools.lru_cache(maxsize=1)
def definition_table():
    """All `def`/`abbrev` declarations, keyed by fully-qualified name."""
    return {d["name"]: d for d in _blob()["definitions"]}


@functools.lru_cache(maxsize=1)
def structures():
    """All `structure`/`class`/`inductive` declarations, keyed by name."""
    return {s["name"]: s for s in _blob()["structures"]}


def parse_failures():
    """Declarations this parser could not read.  Should stay near-empty."""
    return _blob()["parse_failures"]


def definition(name: str):
    """One definition, by fully-qualified or unambiguous bare name."""
    t = definition_table()
    return t[name] if name in t else t[resolve(name)]


@functools.lru_cache(maxsize=1)
def _by_short():
    out = {}
    for n in definition_table():
        out.setdefault(n.split(".")[-1], []).append(n)
    return out


def resolve(short: str) -> str:
    """Bare name -> fully-qualified name.  Raises if absent or ambiguous."""
    cands = _by_short().get(short, [])
    if not cands:
        raise KeyError(f"no definition named {short!r}")
    if len(cands) > 1:
        raise KeyError(f"{short!r} is ambiguous: {cands}")
    return cands[0]


# ------------------------------------------------------------- callables

@functools.lru_cache(maxsize=1)
def _classes():
    if not CLASSES_JSON.exists():
        raise RuntimeError("classes.json missing; run: python3 "
                           "validation/extract/emit.py")
    return json.loads(CLASSES_JSON.read_text())


def classification(name: str):
    """{"class": NUMERIC|STRUCTURAL|WRAPPER|NOT-EXTRACTABLE, "note": reason, ...}."""
    c = _classes()
    return c[name] if name in c else c[resolve(name)]


class NotExtractable(Exception):
    """Raised instead of guessing.  `.reason` says what defeated the translator."""

    def __init__(self, name, reason):
        super().__init__(f"{name}: {reason}")
        self.name, self.reason = name, reason


def callable_for(name: str):
    """Return (fn, ordered_argnames) for a definition, or raise NotExtractable.

    The function is generated from the parsed Lean body and evaluates under
    Mathlib's totality conventions (x/0 = 0, Real.log 0 = 0, Real.sqrt of a
    negative = 0, ...) -- see lean_rt.py.  Argument order matches the Lean
    signature's explicit binders.  Lean identifiers illegal in Python (p₁, H₀,
    x') are renamed by translate.pyname; `ordered_argnames` gives the names the
    function actually takes, in order.

    Structure-typed arguments are passed as dicts keyed by Lean field name;
    `admissible.struct_value(api.structures()[T], rng)` builds an admissible one.
    """
    fq = name if name in definition_table() else resolve(name)
    entry = _classes()[fq]
    if entry["python"] is None:
        raise NotExtractable(fq, entry["note"] or "no executable form emitted")
    import lean_defs
    fn = getattr(lean_defs, entry["python"], None)
    if fn is None:
        raise NotExtractable(fq, f"generated symbol {entry['python']} missing; "
                                 "re-run emit.py")
    return fn, list(entry["args"])


def admissible_box(name: str):
    """{argname: (lo, hi)} mined from theorem hypotheses and quantity kinds.

    Per-argument bounds only.  Inter-argument constraints live in
    `hypotheses(name)`; use `admissible.hypothesis_predicates` to enforce them,
    because sampling outside the corpus's own preconditions manufactures false
    defects.
    """
    import admissible
    return admissible.box_for(definition(name))


def hypotheses(name: str, theorem: str | None = None):
    """(enforceable_predicates, their_source_text, hypotheses_we_could_not_model).

    Pass `theorem` to get ONE theorem's preconditions, which is what a check
    testing that theorem's claim must run under.  With `theorem=None` you get
    the union over every mentioning theorem, which is not a domain: read
    conjunctively it excludes points the corpus considers admissible.  See
    `definition(name)["constraints"]["hypotheses_by_theorem"]`.

    The third element is the honest part: if it is non-empty, a point drawn from
    the box may be inadmissible, and a violation found there is a lead, not a
    verdict.
    """
    import admissible
    return admissible.hypothesis_predicates(definition(name), theorem)


# ------------------------------------------------------------ provenance

def body_checksum(name: str) -> str:
    """sha256 over (fully-qualified name + raw Lean body + explicit signature).

    Pin this next to a result.  If the Lean is edited, the checksum changes and
    the stale result invalidates instead of silently passing.
    """
    d = definition(name)
    argsig = ";".join(f"{n}:{a['type']}" for a in d["args"]
                      if not a["implicit"] for n in a["names"])
    payload = f"{d['name']}\x00{argsig}\x00{d['ret_type']}\x00{d['body']}"
    for e in d["equations"]:
        payload += f"\x00{e['pattern']}=>{e['rhs']}"
    return "sha256:" + hashlib.sha256(payload.encode()).hexdigest()[:32]


def stamp() -> dict:
    """Corpus-wide fingerprint: pin it in any results file you publish."""
    names = sorted(definition_table())
    h = hashlib.sha256()
    for n in names:
        h.update(body_checksum(n).encode())
    return {"n_definitions": len(names),
            "n_structures": len(structures()),
            "n_parse_failures": len(parse_failures()),
            "corpus_digest": "sha256:" + h.hexdigest()[:32]}


def refresh():
    """Drop caches after re-running emit.py in the same process."""
    for f in (_blob, definition_table, structures, _by_short, _classes):
        f.cache_clear()


if __name__ == "__main__":
    import pprint
    print("stamp:")
    pprint.pprint(stamp())
    fn, args = callable_for("Calibrator.coalFst")
    print(f"\ncoalFst{tuple(args)} = {fn(100.0, 1000.0)}")
    print("checksum:", body_checksum("Calibrator.coalFst"))
    print("box:", admissible_box("Calibrator.coalFst"))
