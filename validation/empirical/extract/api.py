"""Canonical, stable interface to the Descent definition table.

This is the one parse of Descent/ that every checker should consume.
Import it; do not re-parse Lean.

    import sys; sys.path.insert(0, "validation/extract")
    import api

    api.definition_table()                 -> dict[str, Definition]
    api.definition("Descent.coalFst")   -> Definition
    api.callable_for("Descent.coalFst") -> (fn, ["t", "Ne"])
    api.vector_args(name)                  -> sequence-valued args, or None
    api.numeric_standins(name)             -> provenance caveat, or None
    api.satisfies("Descent.coalFst", {"t": 10.0, "Ne": 100.0})
    api.body_checksum("Descent.coalFst")-> "sha256:..."
    api.stamp()                            -> corpus-wide fingerprint

Everything is keyed by FULLY-QUALIFIED Lean name (`Descent.coalFst`,
`Descent.R2DecompositionData.calibration`).  `api.resolve("coalFst")` maps a
bare name to its fully-qualified form and raises if it is ambiguous.

Definition fields (see also defs.json, which is this table serialised):

    name            str    fully-qualified, e.g. "Descent.coalFst"
    short           str    last component, e.g. "coalFst"
    kind            str    "def" | "abbrev"
    noncomputable   bool
    file            str    repo-relative, e.g. "Descent/PopGen/PopulationGeneticsFoundations.lean"
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
           "admissible_box", "hypotheses", "satisfies", "vector_args",
           "numeric_standins", "refresh", "staleness", "collisions",
           "all_rows", "theorems", "theorems_mentioning", "require_fresh",
           "ARG_CONVENTION"]

# Bumped whenever the calling convention changes.  Consumers should assert on
# this rather than discovering a convention change from a TypeError.
ARG_CONVENTION = 2      # 1 = scalars only; 2 = adds sequence-valued arguments


# --------------------------------------------------------------- the table

@functools.lru_cache(maxsize=1)
def _blob():
    if not DEFS_JSON.exists():
        raise RuntimeError("defs.json missing; run: python3 "
                           "validation/extract/emit.py")
    return json.loads(DEFS_JSON.read_text())


@functools.lru_cache(maxsize=1)
def definition_table():
    """All `def`/`abbrev` declarations, keyed by fully-qualified name.

    A fully-qualified name declared twice is a Lean BUILD FAILURE, and keying a
    dict by name would silently drop one of the two -- a consumer would then
    compute against a corpus with a declaration missing and a namesake standing
    in its place, which is worse than not representing the collision at all.
    Colliding names are therefore EXCLUDED from this table and listed by
    `collisions()`; `definition()` on one of them raises.  Use `all_rows()` for
    the complete list including collided declarations.
    """
    bad = set(collisions())
    return {d["name"]: d for d in _blob()["definitions"]
            if d["name"] not in bad}


def all_rows():
    """Every parsed declaration, including both sides of a name collision."""
    return list(_blob()["definitions"])


@functools.lru_cache(maxsize=1)
def collisions():
    """{fully-qualified name: [{file, line, signature}, ...]} for duplicates.

    Non-empty means the corpus does not compile.  Report it; do not model it.
    """
    return _blob().get("collisions", {})


@functools.lru_cache(maxsize=1)
def structures():
    """All `structure`/`class`/`inductive` declarations, keyed by name."""
    return {s["name"]: s for s in _blob()["structures"]}


@functools.lru_cache(maxsize=1)
def theorems():
    """All theorem/lemma statements, keyed by fully-qualified name.

    Each row: {name, kind, file, line, statement, mentions}.  `statement` is the
    signature only -- the proof is Lean's business.  `mentions` lists the
    definitions the statement names, i.e. the definitions that theorem
    discriminates if used as a property test.
    """
    return {t["name"]: t for t in _blob().get("theorems", [])}


def theorems_mentioning(name: str):
    """Theorem rows whose statement names this definition."""
    short = name.split(".")[-1]
    return [t for t in theorems().values() if short in t["mentions"]]


def parse_failures():
    """Declarations this parser could not read.  Should stay near-empty."""
    return _blob()["parse_failures"]


def definition(name: str):
    """One definition, by fully-qualified or unambiguous bare name.

    Raises if `name` is declared more than once: there is no correct answer,
    and returning either row would be a silent substitution.
    """
    t = definition_table()
    if name in t:
        return t[name]
    if name in collisions():
        raise KeyError(
            f"{name!r} is DECLARED TWICE and the corpus cannot compile: "
            f"{collisions()[name]}. This table refuses to pick one.")
    return t[resolve(name)]


@functools.lru_cache(maxsize=1)
def _by_short():
    out = {}
    for n in definition_table():
        out.setdefault(n.split(".")[-1], []).append(n)
    return out


def resolve(short: str) -> str:
    """Bare name -> fully-qualified name.  Raises if absent or ambiguous.

    A NAME RECORDED UNDER AN OLD NAMESPACE STILL NAMES ITS DECLARATION.  The
    corpus was one flat `Descent` namespace and is being split per subsystem,
    so `Descent.cumulativeDrift` is now `Descent.PopGen.cumulativeDrift`.  Every
    fully-qualified name stored in a results file before the split went stale at
    once -- 56 of the 62 in `differential/results.json` -- and `verify.py` died
    on the first one it looked up. Those results are measurements that were
    actually taken; the declaration they were taken against still exists and has
    only moved.

    So a qualified name that does not resolve is retried on its LAST component.
    Ambiguity is still an error, which is what keeps this from silently picking
    the wrong declaration when a split puts the same short name in two
    namespaces, and a name matching nothing is still an error, which is what
    keeps a DELETED declaration from being quietly forgiven.
    """
    cands = _by_short().get(short, [])
    if not cands and "." in short:
        cands = _by_short().get(short.split(".")[-1], [])
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
    if entry["class"] == "NOT-EXTRACTABLE":
        # A body can translate and still be unusable -- an untranslated
        # dependency, an argument type we do not model.  The accounting already
        # knows; handing the callable out anyway lets a consumer build on
        # something this table has already judged broken.
        raise NotExtractable(fq, entry["note"] or "classified NOT-EXTRACTABLE")
    import lean_defs
    fn = getattr(lean_defs, entry["python"], None)
    if fn is None:
        raise NotExtractable(fq, f"generated symbol {entry['python']} missing; "
                                 "re-run emit.py")
    return fn, list(entry["args"])


def vector_args(name: str):
    """{argname: {"dim": str, "rank": 1|2}} for sequence-valued arguments, or None.

    Rank 1 arguments (`Fin n → ℝ`) are passed as a flat Python sequence of
    floats; rank 2 (`Matrix (Fin p) (Fin q) ℝ`) as a sequence of sequences.  The
    finite dimension is whatever length you pass -- `∑ i, …` ranges over it.
    Definitions with only scalar arguments return None and are unaffected by
    this convention; ask here rather than inferring from a crash.
    """
    return classification(name).get("vector_args")


def numeric_standins(name: str):
    """Why this definition is NOT purely derived from the Lean body, or None.

    Non-None means some part of it was substituted with a numerically
    equivalent implementation (currently only `Descent.Phi`, Mathlib's
    Gaussian CDF).  A disagreement in such a definition can be a defect in the
    definition OR a mismatch with the intended stand-in; the reader needs to
    know which is possible.
    """
    return classification(name).get("numeric_standins")


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


def satisfies(name: str, point: dict, theorem: str | None = None) -> bool:
    """Is `point` admissible for this definition (under `theorem` if given)?

    USE THIS rather than evaluating the predicates from `hypotheses()` yourself.
    Those are exec-mode code objects that leave their verdict in `__r` and need
    `_rt` in the namespace; `eval`-ing one returns None, which reads as False,
    so every point looks inadmissible and every check manufactures a violation.
    `point` maps python-level argument names (see `callable_for`) to values.
    A point that does not cover every argument RAISES rather than returning
    False: an unbound name inside a predicate degrades to a falsy verdict, so a
    misnamed grid axis would silently mark every point inadmissible and discard
    real findings.  Malformed input is a bug, not a verdict.
    """
    import admissible
    d = definition(name)
    try:
        _fn, argnames = callable_for(name)
    except NotExtractable:
        argnames = [_tr().pyname(n) for a in d["args"]
                    if not a["implicit"] for n in a["names"]]
    missing = [a for a in argnames if a not in point]
    if missing:
        raise ValueError(
            f"satisfies({name!r}): point is missing {missing}; it has "
            f"{sorted(point)}. Keys must be the definition's argument names "
            f"({argnames}), not an experiment's axis names. Safest source is "
            f"dict(zip(api.callable_for(name)[1], the_actual_positional_args)).")
    preds, _texts, _dropped = admissible.hypothesis_predicates(d, theorem)
    return admissible.satisfies(preds, point)


def _tr():
    import translate
    return translate


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
    import lean_parse
    live, nfiles = lean_parse.source_digest(lean_parse.find_proofs_root(HERE) / "Descent")
    return {"arg_convention": ARG_CONVENTION,
            "source_digest_of_table": _blob().get("source_digest"),
            "source_digest_on_disk": live,
            "source_files": nfiles,
            "table_is_current": _blob().get("source_digest") == live,
            "n_collisions": len(collisions()),
            "n_definitions": len(names),
            "n_structures": len(structures()),
            "n_parse_failures": len(parse_failures()),
            "corpus_digest": "sha256:" + h.hexdigest()[:32]}


def refresh():
    """Drop this process's in-memory caches.

    READ-ONLY.  It clears `lru_cache`s so a later call re-reads defs.json and
    classes.json from disk.  It does NOT run emit.py, does not regenerate
    anything, and does not touch a single file -- calling it while someone else
    is editing this directory is safe.  (If you have seen artifacts change
    across a refresh, the cause was someone running emit.py, not this.)
    """
    for f in (_blob, definition_table, structures, _by_short, _classes,
              collisions, theorems):
        f.cache_clear()


def require_fresh():
    """Raise unless the table describes the corpus on disk RIGHT NOW.

    A checker must not rebuild its own inputs mid-run: the numbers it then
    produces have a provenance nobody can reconstruct afterwards.  Refusing is
    louder, cheaper, and leaves the operator in control of when the table moves.
    Call this at the top of anything that reports a number.
    """
    bad = staleness()
    if bad:
        raise RuntimeError(
            "extraction table is not current: " + "; ".join(bad)
            + ".  Run `python3 validation/extract/emit.py` and re-run. "
            "Refusing rather than regenerating, so the numbers you get have a "
            "revision you can name.")


def staleness():
    """Is the generated module older than the table it was generated from?

    Two ways to read a lie: `lean_defs.py` older than `defs.json` means emit.py
    has not been re-run since the table changed; a `__pycache__` entry newer
    than neither means Python may serve stale bytecode across a regeneration,
    whose symptom is indistinguishable from "the fix was never applied".
    Returns a list of complaints, empty when clean.
    """
    import os
    out = []
    # THE CHECK THAT MATTERS: does the table describe the Lean on disk?
    # Everything below this compares derived artifacts against each other,
    # which is uninformative by construction -- they were written by one run,
    # so they agree whether or not they match the source.  A table that is a
    # perfectly coherent snapshot of a corpus that no longer exists passes
    # every one of those checks and yields confident wrong numbers.
    try:
        import lean_parse
        stored = _blob().get("source_digest")
        live, n = lean_parse.source_digest(lean_parse.find_proofs_root(HERE) / "Descent")
        if stored is None:
            out.append("table predates source-digest recording; regenerate to "
                       "make freshness checkable at all")
        elif stored != live:
            out.append(
                f"table was generated from DIFFERENT Lean sources "
                f"(table {stored}, on disk {live} over {n} files) -- every "
                f"count from it describes a corpus that is no longer there")
    except Exception as e:                                       # noqa: BLE001
        out.append(f"could not compare against the Lean sources: {e!r}")

    defs_m = DEFS_JSON.stat().st_mtime if DEFS_JSON.exists() else 0
    mod = HERE / "lean_defs.py"
    mod_m = mod.stat().st_mtime if mod.exists() else 0
    if not mod.exists():
        out.append("lean_defs.py missing; run emit.py")
    elif mod_m < defs_m - 1:
        out.append("lean_defs.py is older than defs.json; run emit.py")
    for pyc in (HERE / "__pycache__").glob("lean_defs.*.pyc"):
        if pyc.stat().st_mtime < mod_m - 1:
            out.append(f"stale bytecode {pyc.name}; delete __pycache__ "
                       "(Python may serve the pre-regeneration module)")
    if os.environ.get("EXTRACT_STRICT") and out:
        raise RuntimeError("; ".join(out))
    return out


if __name__ == "__main__":
    import pprint
    print("stamp:")
    pprint.pprint(stamp())
    fn, args = callable_for("Descent.coalFst")
    print(f"\ncoalFst{tuple(args)} = {fn(100.0, 1000.0)}")
    print("checksum:", body_checksum("Descent.coalFst"))
    print("box:", admissible_box("Descent.coalFst"))
