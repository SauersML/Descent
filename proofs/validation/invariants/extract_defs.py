"""Extract Lean definitions from proofs/Calibrator into a machine-readable table.

Standalone fallback extractor: the `extract` agent is building a richer table
under proofs/validation/extract/.  This module produces the subset that the
range and metamorphic checkers need, and switches over automatically if the
richer table appears (see `load_table`).

Per definition we capture:
  name, module (Lean file), line, params [(name, type)], return type,
  docstring, raw body, and -- where the body is in the arithmetic fragment --
  a Python source string that evaluates it.

Nothing here executes Lean.  It is pure text.
"""
from __future__ import annotations

import json
import pathlib
import re


def _lean_sources(_r):
    # `rglob` under Calibrator/ does NOT reach `proofs/Calibrator.lean`, the corpus
    # ROOT, which sits one level above it. A scan blind to the root reported
    # `decaySlope` unreferenced; it was deleted, and `LDDecayMechanism` was then
    # deleted for having lost its only consumer. Both consumers were in the root.
    # `lean_parse.build` carries this `extra` idiom -- keep every scanner in step.
    _r = pathlib.Path(_r)
    _fs = sorted(_r.rglob("*.lean"))
    _x = _r.parent / (_r.name + ".lean")
    if _x.exists():
        _fs.append(_x)
    return _fs


CAL = pathlib.Path(__file__).resolve().parents[2] / "Calibrator"

DEF_RE = re.compile(
    r"^(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+)?(?:noncomputable\s+)?def\s+"
    r"([A-Za-z_][\w.'₀-₉]*)\s*(.*)$"
)
# a top-level declaration terminates the previous body
STOP_RE = re.compile(
    r"^\s*(?:@\[|/--|/-|--|(?:private\s+|protected\s+)?(?:noncomputable\s+)?def\s|"
    r"theorem\s|lemma\s|example\s|"
    r"abbrev\s|structure\s|inductive\s|instance\s|namespace\s|end\s|section\s|"
    r"open\s|import\s|variable\s|class\s|axiom\s|#|\.\.\.)"
)

def _binder_groups(sig: str):
    """Split a signature into top-level bracket groups, paren-depth aware.

    A regex cannot do this.  `(T : (Fin k → ℝ) → ℝ)` has parentheses INSIDE
    the type, and a pattern like `\(([^():]*):\s*([^()]*)\)` simply fails to
    match it -- so the binder was dropped, silently, and every argument after
    it shifted by one in the generated callable.  The definition then either
    took the wrong number of arguments or, where the arities happened to line
    up, computed a different function under the right name.
    """
    groups, depth, start = [], 0, None
    for i, ch in enumerate(sig):
        if ch in "({[":
            if depth == 0:
                start = i
            depth += 1
        elif ch in ")}]":
            depth -= 1
            if depth == 0 and start is not None:
                groups.append(sig[start:i + 1])
                start = None
    return groups


def _params(sig: str):
    """Parse `(a b : ℝ) (n : ℕ) : ℝ` into ([(a,ℝ),(b,ℝ),(n,ℕ)], [], 'ℝ')."""
    params, implicit = [], []
    for g in _binder_groups(sig):
        inner = g[1:-1]
        # split on the FIRST top-level colon only; the type may contain more
        depth, cut = 0, -1
        for i, ch in enumerate(inner):
            if ch in "({[":
                depth += 1
            elif ch in ")}]":
                depth -= 1
            elif ch == ":" and depth == 0:
                cut = i
                break
        if cut < 0:
            continue
        names, ty = inner[:cut], inner[cut + 1:].strip()
        if g[0] in "{[":
            # Implicit and instance binders are INFERRED by Lean and do not
            # appear at call sites, so they must not count toward arity --
            # including them makes every call to the definition look like it
            # is missing an argument.  They are recorded separately because
            # the BODY may still reference them, and a body that does is one
            # this tier cannot evaluate.
            for nm in names.split():
                implicit.append((nm, ty or "instance"))
            continue
        for nm in names.split():
            params.append((nm, ty))
    # return type = after the LAST top-level colon
    depth = 0
    ret = None
    for i, ch in enumerate(sig):
        if ch in "([{":
            depth += 1
        elif ch in ")]}":
            depth -= 1
        elif ch == ":" and depth == 0:
            ret = sig[i + 1 :]
    if ret is not None:
        ret = ret.split(":=")[0].strip()
    return params, implicit, ret


def _docstring(lines, i):
    """Collect the /-- ... -/ block immediately preceding line i."""
    j = i - 1
    while j >= 0 and (lines[j].strip() == "" or lines[j].strip().startswith("@[")):
        j -= 1
    if j < 0 or not lines[j].strip().endswith("-/"):
        return ""
    k = j
    while k >= 0 and "/--" not in lines[k]:
        k -= 1
    if k < 0:
        return ""
    doc = "\n".join(lines[k : j + 1])
    return doc.replace("/--", "").replace("-/", "").strip()


def extract_file(path: pathlib.Path):
    lines = path.read_text(errors="ignore").splitlines()
    out = []
    i = 0
    while i < len(lines):
        m = DEF_RE.match(lines[i])
        if not m:
            i += 1
            continue
        name, rest = m.group(1), m.group(2)
        # signature may wrap across lines until `:=` or end-of-equation
        sig = rest
        start = i
        while ":=" not in sig and i + 1 < len(lines) and not lines[i + 1].startswith(
            ("theorem", "def", "/--")
        ):
            i += 1
            sig += " " + lines[i].strip()
            if i - start > 8:
                break
        head_line = i
        body_lines = []
        if ":=" in sig:
            tail = sig.split(":=", 1)[1].strip()
            sig = sig.split(":=", 1)[0]
            if tail:
                body_lines.append(tail)
        i = head_line + 1
        while i < len(lines):
            ln = lines[i]
            if ln.strip() == "":
                # blank line ends the body only if what follows is a new decl
                j = i
                while j < len(lines) and lines[j].strip() == "":
                    j += 1
                if j >= len(lines) or STOP_RE.match(lines[j]):
                    break
                i = j
                continue
            if not ln.startswith((" ", "\t", "|")) and STOP_RE.match(ln):
                break
            if re.match(r"^(theorem |lemma |(private |protected )?(noncomputable )?def )", ln):
                break
            body_lines.append(ln.strip())
            i += 1
        params, implicit, ret = _params(sig)
        out.append(
            dict(
                name=name,
                module=path.stem,
                path=str(path.relative_to(CAL.parent.parent)),
                line=start + 1,
                params=params,
                implicit_params=implicit,
                ret=ret,
                doc=_docstring(lines, start),
                body="\n".join(body_lines).strip(),
            )
        )
    return out


def extract_all():
    defs = []
    for p in _lean_sources(CAL):
        defs.extend(extract_file(p))
    return defs


# --------------------------------------------------------------------------
# hypothesis harvesting: theorems that mention a definition constrain its box

THM_RE = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)?(?:theorem|lemma)\s+([\w.'₀-₉]+)")
HYP_RE = re.compile(r"\(\s*[\w'₀-₉]*\s*:\s*([^()]*(?:\([^()]*\)[^()]*)*)\)")


APP_ARG = re.compile(r"[A-Za-z_][\w'₀-₉.]*|\(|[\d.]+")


def _argmap(d, stmt):
    """Theorem-local name -> the definition's own parameter name.

    Theorems routinely rename: `proportion_mediated_in_unit (ie te : ℝ)` proves
    a bound on `proportionMediated ie te`.  Read off the application site so
    the hypothesis `ie ≤ te` can be translated into the definition's own
    vocabulary; without this the hypothesis mentions no parameter of the
    definition and is silently discarded, and every such definition is then
    reported as unguarded.
    """
    k = len(d["params"])
    if k == 0:
        return {}
    for m in re.finditer(r"\b" + re.escape(d["name"]) + r"\b((?:\s+[A-Za-z_][\w'₀-₉]*)+)",
                         stmt):
        args = m.group(1).split()
        if len(args) < k:
            continue
        out = {}
        for a, (p, _) in zip(args[:k], d["params"]):
            if a != p:
                out[a] = p
        return out
    return {}


def harvest_hypotheses(defs):
    """For each def, gather the hypothesis atoms of theorems that name it.

    A theorem `foo_in_unit (p : ℝ) (h : 0 < p) (h2 : p < 1) : 0 <= foo p` tells
    us the author's own admissible box for `foo`.  We take the UNION over
    theorems of hypotheses that mention a parameter name, which is deliberately
    generous: a range escape inside the union is a real escape only if it also
    lies inside some single theorem's box, so the checkers re-filter per box.
    """
    by_name = {d["name"]: d for d in defs}
    boxes = {d["name"]: [] for d in defs}
    for p in _lean_sources(CAL):
        text = p.read_text(errors="ignore")
        blocks = re.split(r"\n(?=(?:@\[[^\]]*\]\n)?(?:theorem|lemma)\s)", text)
        for b in blocks:
            m = THM_RE.match(b)
            if not m:
                continue
            stmt = b.split(":= by")[0].split(":=\n")[0]
            hyps = [h.strip() for h in HYP_RE.findall(stmt)]
            for nm in set(re.findall(r"\b([a-z][\w'₀-₉]*)\b", stmt)):
                if nm not in boxes:
                    continue
                boxes[nm].append(dict(thm=m.group(1), hyps=hyps,
                                      argmap=_argmap(by_name[nm], stmt)))
    for d in defs:
        d["theorem_hyps"] = boxes[d["name"]]
        d["n_theorems"] = len(boxes[d["name"]])
    return defs


if __name__ == "__main__":
    ds = harvest_hypotheses(extract_all())
    out = pathlib.Path(__file__).with_name("defs.json")
    out.write_text(json.dumps(ds, ensure_ascii=False, indent=1))
    print(f"{len(ds)} definitions -> {out}")
