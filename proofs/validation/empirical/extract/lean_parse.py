"""Parser for the Calibrator Lean corpus.

Produces a machine-readable table of every declaration under proofs/Calibrator/,
so that downstream validation never has to re-transcribe a Lean formula by hand.

The parser is deliberately syntactic (no Lean elaboration): it tokenises far
enough to find declaration boundaries, split header from body at the top-level
`:=`, attach docstrings, track the namespace stack, and mine constraints out of
docstrings and out of the theorems that mention each definition.

Usage:
    python3 lean_parse.py [--root Calibrator] [--out defs.json]
"""
from __future__ import annotations

import argparse
import hashlib
import json
import pathlib
import re
import sys
from dataclasses import dataclass, field, asdict

# --------------------------------------------------------------------------
# comment / docstring stripping
# --------------------------------------------------------------------------

DOC_OPEN = "/--"
MOD_OPEN = "/-!"
BLK_OPEN = "/-"
BLK_CLOSE = "-/"


def strip_comments(src: str):
    """Blank out every comment, preserving offsets and newlines.

    Returns (clean, docs) where docs maps the *end offset* of a `/-- ... -/`
    docstring to its text.  Nested block comments are handled.
    """
    out = list(src)
    docs = {}
    i, n = 0, len(src)
    while i < n:
        c = src[i]
        if c == '"':                                  # string literal
            j = i + 1
            while j < n and src[j] != '"':
                j += 2 if src[j] == "\\" else 1
            i = j + 1
            continue
        if src.startswith("--", i) and not src.startswith("-/", i):
            j = src.find("\n", i)
            j = n if j < 0 else j
            for k in range(i, j):
                out[k] = " "
            i = j
            continue
        if src.startswith(BLK_OPEN, i):
            is_doc = src.startswith(DOC_OPEN, i)
            depth, j = 1, i + 3 if (is_doc or src.startswith(MOD_OPEN, i)) else i + 2
            while j < n and depth:
                if src.startswith(BLK_OPEN, j):
                    depth += 1
                    j += 2
                elif src.startswith(BLK_CLOSE, j):
                    depth -= 1
                    j += 2
                else:
                    j += 1
            if is_doc:
                docs[j] = src[i + 3:j - 2].strip()
            for k in range(i, min(j, n)):
                if out[k] != "\n":
                    out[k] = " "
            i = j
            continue
        i += 1
    return "".join(out), docs


# --------------------------------------------------------------------------
# declaration scanning
# --------------------------------------------------------------------------

DECL_KINDS = ("def", "theorem", "lemma", "structure", "inductive", "abbrev",
              "instance", "example", "class", "opaque", "axiom")
MODIFIERS = ("noncomputable", "private", "protected", "partial", "unsafe",
             "scoped", "local", "nonrec", "@[simp]")

DECL_RE = re.compile(
    # An INLINE attribute must be skipped, not treated as a non-declaration.
    # `@[simp] theorem foo : ...` on one line is extremely common here, and
    # without this group the whole declaration is invisible: it never becomes a
    # theorem, so every definition it mentions loses it from `mentioned_by`.
    # Sampled 4 for 4 wrong -- `coalescenceCdfFromHazard`, `tagAlleleFreqTargetAt`,
    # `causalAlleleFreqTargetAt` and `expectedSqMeanPGSDiff_pureSplit` each
    # looked theorem-less while carrying an inline `@[simp] theorem`. The same
    # shape independently broke a free-definition scan and a
    # tautological-restatement scan, both of which read `mentioned_by`, so the
    # fix belongs here rather than in each consumer. Note `MODIFIERS` above
    # already listed `@[simp]`; this regex had drifted from it.
    r"^(?P<attrs>(?:@\[[^\]]*\]\s*)*)"
    r"(?P<mods>(?:(?:noncomputable|private|protected|partial|unsafe|scoped|local|nonrec)\s+)*)"
    r"(?P<kind>def|theorem|lemma|structure|inductive|abbrev|instance|example|class|opaque|axiom)"
    r"(?:\s+(?P<name>[^\s:({\[⦃]+))?",
)
BOUNDARY_RE = re.compile(
    r"^(?:namespace|end|section|open|import|variable|universe|attribute|set_option|@\[|"
    r"noncomputable|private|protected|partial|unsafe|scoped|local|nonrec|"
    r"def|theorem|lemma|structure|inductive|abbrev|instance|example|class|opaque|axiom)\b")

IDENT_CH = re.compile(r"[A-Za-z0-9_'!?.À-￿]")
IDENT_RE = re.compile(r"[A-Za-z_Ͱ-Ͽᴀ-ᶿ℀-⅏]"
                      r"[A-Za-z0-9_'Ͱ-Ͽᴀ-ᶿ₀-ₜÀ-￿]*"
                      r"(?:\.[A-Za-z_Ͱ-Ͽ℀-⅏][A-Za-z0-9_'₀-ₜÀ-￿]*)*")


@dataclass
class Decl:
    name: str            # fully qualified: namespace stack + declaration name
    decl_name: str       # the declaration name EXACTLY as written in the source
    short: str           # last dotted component only -- NOT unique, see below
    kind: str            # def | theorem | structure | ...
    noncomputable: bool
    file: str
    line: int
    signature: str       # everything between name and the top-level `:=`
    args: list           # [{"names": [...], "type": str, "binder": "()"|"{}"|"[]"}]
    ret_type: str
    body: str
    docstring: str
    empirical_status: str
    namespace: str
    fields: list = field(default_factory=list)      # structures
    equations: list = field(default_factory=list)   # equation-compiler alternatives
    constraints: dict = field(default_factory=dict)
    mentioned_by: list = field(default_factory=list)


def _split_top(s: str, marker: str):
    """Index of first `marker` at bracket depth 0, else -1."""
    depth = 0
    opens, closes = "([{⟨⦃⁅", ")]}⟩⦄⁆"
    i, n = 0, len(s)
    while i < n:
        c = s[i]
        if c in opens:
            depth += 1
        elif c in closes:
            depth -= 1
        elif depth == 0 and s.startswith(marker, i):
            return i
        i += 1
    return -1


def parse_binders(sig: str):
    """Split a Lean binder list into structured arguments plus the return type."""
    args, i, n = [], 0, len(sig)
    while i < n:
        while i < n and sig[i] in " \n\t":
            i += 1
        if i >= n:
            break
        c = sig[i]
        if c in "({[⦃⁅":                     # (, {, [, ⦃, ⁅
            close = {"(": ")", "{": "}", "[": "]", "⦃": "⦄", "⁅": "⁆"}[c]
            depth, j = 1, i + 1
            while j < n and depth:
                if sig[j] == c:
                    depth += 1
                elif sig[j] == close:
                    depth -= 1
                j += 1
            inner = sig[i + 1:j - 1]
            k = _split_top(inner, ":")
            if k >= 0:
                names = inner[:k].split()
                ty = inner[k + 1:].strip()
            else:
                names, ty = inner.split(), ""
            args.append({"names": names, "type": " ".join(ty.split()),
                         "binder": c + close, "implicit": c != "("})
            i = j
            continue
        if c == ":":                                   # start of return type
            return args, " ".join(sig[i + 1:].split())
        # bare binder or something we do not model; consume one token
        m = IDENT_RE.match(sig, i)
        i = m.end() if m else i + 1
    return args, ""


def parse_file(path: pathlib.Path, root: pathlib.Path):
    src = path.read_text(errors="ignore")
    clean, docs = strip_comments(src)
    lines = clean.splitlines(keepends=True)
    offsets, off = [], 0
    for ln in lines:
        offsets.append(off)
        off += len(ln)

    # namespace stack, computed per line
    ns_at, stack = [], []
    for ln in lines:
        s = ln.strip()
        ns_at.append(".".join(x for x in stack if x is not None))
        if s.startswith("namespace "):
            stack.append(s.split()[1])
        elif s.startswith("section"):
            stack.append(None)
        elif s == "end" or s.startswith("end "):
            tail = s[3:].strip()
            if stack:
                if not tail:
                    stack.pop()
                elif stack and stack[-1] == tail:
                    stack.pop()
                elif tail in stack:
                    while stack and stack.pop() != tail:
                        pass

    # declaration start lines
    starts = []
    for i, ln in enumerate(lines):
        if ln[:1] in (" ", "\t", "\n") or not ln.strip():
            continue
        m = DECL_RE.match(ln)
        if m:
            starts.append((i, m))

    decls, failures = [], []
    for idx, (i, m) in enumerate(starts):
        # body extends until the next top-level boundary line
        j = i + 1
        while j < len(lines):
            ln = lines[j]
            if ln[:1] not in (" ", "\t") and ln.strip() and BOUNDARY_RE.match(ln):
                break
            j += 1
        chunk_clean = "".join(lines[i:j]).rstrip()
        chunk_raw = src[offsets[i]:offsets[j] if j < len(lines) else len(src)].rstrip()

        kind, name = m.group("kind"), m.group("name")
        if name is None:
            failures.append({"file": str(path.relative_to(root.parent)), "line": i + 1,
                             "reason": "no name in declaration header",
                             "head": lines[i].rstrip()[:120]})
            continue

        # docstring: the `/-- -/` whose end offset lands just before this decl
        doc = ""
        for end, text in docs.items():
            if end <= offsets[i] and not src[end:offsets[i]].strip():
                doc = text
        # header / body split
        after_name = chunk_clean[m.end():]
        cut = _split_top(after_name, ":=")
        equations = []
        if cut < 0:
            # equation-compiler form:  def f (args) : T\n  | pat => rhs ...
            mbar = re.search(r"^\s*\|", after_name, re.M)
            if mbar:
                sig, eqtext = after_name[:mbar.start()], after_name[mbar.start():]
                for alt in re.split(r"^\s*\|", eqtext, flags=re.M):
                    if not alt.strip():
                        continue
                    if "=>" in alt:
                        pat, rhs = alt.split("=>", 1)
                        equations.append({"pattern": " ".join(pat.split()),
                                          "rhs": " ".join(rhs.split())})
                body = eqtext.strip()
            elif kind in ("structure", "class", "inductive"):
                sig, body = after_name, ""
            else:
                sig, body = after_name, ""
                failures.append({"file": str(path.relative_to(root.parent)),
                                 "line": i + 1, "name": name,
                                 "reason": "no top-level ':=' found",
                                 "head": lines[i].rstrip()[:120]})
        else:
            sig, body = after_name[:cut], after_name[cut + 2:]

        args, ret = parse_binders(sig)
        ns = ns_at[i]
        fq = f"{ns}.{name}" if ns else name

        est = ""
        # Leading `**` must be skipped: docstrings write the verdict in markdown
        # bold (`Empirical status: **MEASURED ...**`), and requiring [A-Z] right
        # after the colon silently yielded "" for every one of them -- reading a
        # measured definition as unmarked. `check.py`'s own empirical-claim
        # screen already parses bold statuses, so this regex was the odd one out
        # and the two instruments disagreed about which defs carry a verdict.
        mest = re.search(r"Empirical status:\s*\*{0,2}\s*([A-Z][A-Z_\- ]*)", doc)
        if mest:
            est = mest.group(1).strip().rstrip(".")

        d = Decl(name=fq, decl_name=name, short=name.split(".")[-1], kind=kind,
                 noncomputable="noncomputable" in m.group("mods"),
                 file=str(path.relative_to(root.parent)), line=i + 1,
                 signature=" ".join(sig.split()), args=args, ret_type=ret,
                 body=body.strip("\n").rstrip(), docstring=doc,
                 empirical_status=est, namespace=ns, equations=equations)
        if kind in ("structure", "class"):
            d.fields = parse_struct_fields(chunk_clean, m.end())
        d.constraints = {"raw_chunk_lines": j - i}
        d._chunk = chunk_clean       # type: ignore[attr-defined]
        decls.append(d)
    return decls, failures


FIELD_RE = re.compile(r"^\s{1,}([A-Za-z_][\w'₀-ₜ]*)\s*:\s*(.+?)\s*$")


def parse_struct_fields(chunk: str, hdr_end: int):
    fields = []
    tail = chunk[hdr_end:]
    if "where" in tail:
        tail = tail.split("where", 1)[1]
    elif ":=" in tail:
        tail = tail.split(":=", 1)[1]
    for ln in tail.splitlines():
        m = FIELD_RE.match(ln)
        if m:
            fields.append({"name": m.group(1), "type": " ".join(m.group(2).split())})
    return fields


# --------------------------------------------------------------------------
# constraint mining
# --------------------------------------------------------------------------

RANGE_BY_KEYWORD = [
    (r"\bfst\b|f_?st\b|fixation index", (0.0, 1.0), "F_ST"),
    (r"\bprobabilit|\bprevalence|\bpower\b|\bauc\b|\bsensitivit|\bspecificit",
     (0.0, 1.0), "probability"),
    (r"frequenc", (0.0, 1.0), "frequency"),
    (r"heritabilit|\bh2\b|h²", (0.0, 1.0), "heritability"),
    (r"\br2\b|r²|r-squared|variance explained", (0.0, 1.0), "R-squared"),
    (r"correlation|\brg\b|genetic correlation", (-1.0, 1.0), "correlation"),
    (r"heterozygosit", (0.0, 1.0), "heterozygosity"),
    (r"portabilit.*ratio|retention", (0.0, 1.0), "ratio"),
    (r"varian|\bmse\b|\bsquared\b|\bne\b|sample size|generation", (0.0, None), "nonnegative"),
]

# `0 ≤ f x y`, `f x y ≤ 1`, `0 < f x`, `f x < 1`
LE, LT = "≤", "<"


def mine_from_theorems(defs, theorems):
    """For each def: which theorems mention it, and what bounds/hypotheses they assert."""
    by_short = {}
    for d in defs:
        by_short.setdefault(d.short, []).append(d)
    for t in theorems:
        text = t._chunk                        # type: ignore[attr-defined]
        stmt = text.split(":=", 1)[0].split(":= by")[0]
        # Bounds must come from what the theorem PROVES, not from what it
        # ASSUMES.  Strip the hypothesis binders before mining ranges.
        concl = re.sub(r"\([^()]*?h[\w'₀-ₜ]*\s*:[^()]*\)", " ", stmt)
        names = set(IDENT_RE.findall(text))
        for nm in names:
            base = nm.split(".")[-1]
            for d in by_short.get(base, []):
                if d.name == t.name:
                    continue
                d.mentioned_by.append(t.name)
                # bounds
                lo, hi = d.constraints.get("range_lo"), d.constraints.get("range_hi")
                # `<lit> ≤ NAME <simple args>` / `NAME <simple args> ≤ <lit>`,
                # where "simple args" excludes any arithmetic operator, so the
                # bound really is a bound on this definition's own value.
                simple = r"(?:[A-Za-z0-9_'₀-ₜ.\s]|\([A-Za-z0-9_'₀-ₜ.\s]*\))*"
                for pat, which in (
                    (rf"(-?[\d./]+)\s*[{LE}<]\s*{re.escape(base)}\b{simple}(?=[,∧)\n]|$)", "lo"),
                    (rf"(?<![\w'])(?<![-+*/^]\s){re.escape(base)}\b{simple}[{LE}<]\s*(-?[\d./]+)", "hi"),
                ):
                # KNOWN FALSE POSITIVE, NOT YET FIXED.  A numeral that is an
                # ARGUMENT is read here as a BOUND.  In
                # `target_ld_shift_changes_explainedR2_under_fixed_source_weights`
                # the definition is compared against itself and both sides pass
                # `4` as the outcome variance:
                #
                #   explainedR2FromTransportMoments (…) (…) 4 <
                #     explainedR2FromTransportMoments (…) (…) 4
                #
                # The `lo` pattern matches the `4 <` sitting immediately left of
                # the right-hand occurrence and records
                # `4 ≤ explainedR2FromTransportMoments`, which no theorem proves.
                # The definition then evaluates to 1.0 at cov = varS = varY = 0.05
                # -- its correct value, a perfect R^2 -- and is reported as the
                # corpus's only DEFECT, the tool's strongest verdict, reserved for
                # a body that leaves a range a Lean THEOREM proves.
                #
                # An attempted fix (reject the match when this definition's own
                # name appears between the last relational operator and the
                # literal, so the literal is inside an application of it) did NOT
                # clear this case and could not be A/B'd honestly, because the
                # corpus moved underneath two consecutive runs of the tool. It is
                # recorded here rather than shipped unverified. Whoever fixes it:
                # the check is that DEFECT falls to 2 with NO other status moving,
                # measured against a baseline run at the SAME revision.
                    for mm in re.finditer(pat, concl):
                        try:
                            v = eval(mm.group(1), {"__builtins__": {}})  # numeric literal only
                        except Exception:
                            continue
                        nh = len(re.findall(r"\(\s*h[\w'₀-ₜ]*\s*:", stmt))
                        if which == "lo":
                            if lo is None or v < lo:
                                lo = v
                                d.constraints["range_lo_thm"] = [t.name, nh]
                        else:
                            if hi is None or v > hi:
                                hi = v
                                d.constraints["range_hi_thm"] = [t.name, nh]
                if lo is not None:
                    d.constraints["range_lo"] = lo
                if hi is not None:
                    d.constraints["range_hi"] = hi
                # hypothesis constraints on the def's own argument names
                argnames = {n for a in d.args for n in a["names"]}
                # NOTE ON SEMANTICS: `hypotheses` is the UNION over every
                # theorem mentioning this definition, so it is NOT a domain and
                # must not be read as a conjunction -- one asymptotic lemma's
                # `100 * Ne < t` would otherwise exclude every sensible
                # evaluation.  `hypotheses_by_theorem` keeps the grouping, and
                # that is what a check should enforce: the preconditions of the
                # ONE theorem whose claim is being tested.
                hyps = d.constraints.setdefault("hypotheses", [])
                per = d.constraints.setdefault("hypotheses_by_theorem", {})
                mine = per.setdefault(t.name, [])
                for mm in re.finditer(r"\(\s*h[\w'₀-ₜ]*\s*:\s*([^)]*)\)", stmt):
                    h = " ".join(mm.group(1).split())
                    if any(re.search(rf"(?<![\w']){re.escape(a)}(?![\w'])", h) for a in argnames):
                        if h not in hyps:
                            hyps.append(h)
                        if h not in mine:
                            mine.append(h)


def mine_from_docstring(d: Decl):
    hay = (d.docstring + " " + d.short + " " + d.name).lower()
    for pat, (lo, hi), label in RANGE_BY_KEYWORD:
        if re.search(pat, hay):
            d.constraints.setdefault("declared_kind", label)
            d.constraints.setdefault("declared_lo", lo)
            d.constraints.setdefault("declared_hi", hi)
            break
    m = re.search(r"\b(per generation|per year|generations?|years?|per sample|per snp)\b", hay)
    if m:
        d.constraints["units"] = m.group(1)


# --------------------------------------------------------------------------

_SOURCE_DIGEST = (None, 0)


class CorpusNotFound(Exception):
    """The Lean corpus is not where a caller said it was.

    Raised rather than returning an empty parse, because those two outcomes are
    indistinguishable downstream and the difference is the whole verdict.
    """


def find_proofs_root(start: pathlib.Path) -> pathlib.Path:
    """Walk up from `start` to the directory that actually holds `Calibrator/`.

    Every module under validation/ used to hardcode its own depth
    (`HERE.parent.parent`).  When this directory moved from
    `proofs/validation/extract` to `proofs/validation/empirical/extract` those
    constants all became one level short, so `root` pointed at
    `proofs/validation/Calibrator`, which does not exist.  `rglob` on a missing
    directory yields nothing, so the whole extraction tier parsed zero
    definitions and reported success.  Searching for the corpus instead of
    counting `..`s cannot go stale when a file is moved again.
    """
    start = start.resolve()
    for cand in (start, *start.parents):
        if (cand / "Calibrator").is_dir():
            return cand
    raise CorpusNotFound(
        f"no ancestor of {start} contains a Calibrator/ directory; the Lean "
        f"corpus could not be located")


def build(root: pathlib.Path):
    global _SOURCE_DIGEST
    root = pathlib.Path(root)
    if not root.is_dir():
        raise CorpusNotFound(f"corpus root {root} does not exist")
    _SOURCE_DIGEST = source_digest(root)
    all_decls, failures = [], []
    files = sorted(root.rglob("*.lean"))
    if not files:
        raise CorpusNotFound(f"corpus root {root} contains no .lean files")
    extra = root.parent / (root.name + ".lean")
    if extra.exists():
        files.append(extra)
    for p in files:
        try:
            ds, fs = parse_file(p, root)
        except Exception as e:                                   # noqa: BLE001
            failures.append({"file": str(p), "reason": f"parser exception: {e!r}"})
            continue
        all_decls.extend(ds)
        failures.extend(fs)
    defs = [d for d in all_decls if d.kind in ("def", "abbrev")]
    thms = [d for d in all_decls if d.kind in ("theorem", "lemma", "example")]
    structs = [d for d in all_decls if d.kind in ("structure", "class", "inductive")]
    for d in defs:
        mine_from_docstring(d)
    mine_from_theorems(defs, thms)
    for d in defs:
        d.constraints.pop("raw_chunk_lines", None)
        d.mentioned_by = sorted(set(d.mentioned_by))
    return defs, thms, structs, failures


def source_digest(root):
    """A content hash of every Lean source the table is derived from.

    The point of comparison for staleness.  Comparing generated artifacts
    against EACH OTHER only detects an internally incoherent snapshot; it
    cannot detect a perfectly coherent snapshot of a corpus that no longer
    exists, which is the more likely and more dangerous failure once
    definitions are being repaired continuously.  Content rather than mtime,
    so a checkout or a touch does not read as a change.
    """
    h = hashlib.sha256()
    files = sorted(pathlib.Path(root).rglob("*.lean"))
    extra = pathlib.Path(root).parent / (pathlib.Path(root).name + ".lean")
    if extra.exists():
        files.append(extra)
    for f in files:
        h.update(str(f.name).encode())
        h.update(f.read_bytes())
    return f"sha256:{h.hexdigest()[:32]}", len(files)


def find_collisions(defs):
    """Fully-qualified names declared more than once.

    Lean rejects a second declaration of the same fully-qualified name whatever
    its signature, so a collision here is a BUILD FAILURE in the corpus, not a
    modelling problem for this table.  It is surfaced rather than resolved: any
    resolution silently drops a real declaration, and a consumer keyed by name
    would then compute against a corpus with a definition missing.
    """
    seen = {}
    for d in defs:
        seen.setdefault(d.name, []).append(d)
    return {n: [{"file": x.file, "line": x.line, "signature": x.signature}
                for x in rows]
            for n, rows in seen.items() if len(rows) > 1}


def theorem_rows(thms, defs):
    """Theorem statements, in a form another tier can diff against its own.

    Statement only, never the proof: the proof is Lean's business and the
    statement is the shared object.  `mentions` is the set of definitions the
    statement names, which is what makes a theorem usable as a property test --
    it is the list of definitions that theorem discriminates.
    """
    shorts = {d.short for d in defs}
    rows = []
    for t in thms:
        stmt = " ".join(t.signature.split())
        names = {n.split(".")[-1] for n in IDENT_RE.findall(stmt)}
        rows.append({
            "name": t.name, "kind": t.kind, "file": t.file, "line": t.line,
            "statement": stmt,
            "mentions": sorted(names & shorts),
        })
    return rows


def to_json(defs, structs, failures, thms=()):
    def clean(d):
        r = {k: v for k, v in asdict(d).items()}
        return r
    return {
        "_NOT_AUTHORITATIVE": (
            "The committed copy of this file is STALE BY CONSTRUCTION: the Lean "
            "corpus moves every few minutes and this is a cache of it. Do not "
            "consume a committed copy -- run validation/extract/emit.py in your "
            "own worktree immediately before use, and call api.require_fresh(), "
            "which raises if the table does not describe the Lean on disk."),
        "source_digest": _SOURCE_DIGEST[0],
        "source_files": _SOURCE_DIGEST[1],
        "collisions": find_collisions(defs),
        "theorems": theorem_rows(thms, defs),
        "definitions": [clean(d) for d in defs],
        "structures": [clean(d) for d in structs],
        "parse_failures": failures,
    }


def main(argv=None):
    ap = argparse.ArgumentParser()
    ap.add_argument("--root", default="Calibrator")
    ap.add_argument("--out", default=None)
    a = ap.parse_args(argv)
    root = pathlib.Path(a.root).resolve()
    defs, thms, structs, failures = build(root)
    blob = to_json(defs, structs, failures, thms)
    text = json.dumps(blob, indent=1, ensure_ascii=False)
    if a.out:
        pathlib.Path(a.out).write_text(text)
    print(f"definitions: {len(defs)}   theorems: {len(thms)}   "
          f"structures/inductives: {len(structs)}   parse failures: {len(failures)}",
          file=sys.stderr)
    if not a.out:
        print(text)
    return blob


if __name__ == "__main__":
    main()
