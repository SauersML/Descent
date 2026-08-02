"""Parse Lean 4 declarations out of proofs/Calibrator into a structured table.

Deliberately shallow: it recovers the *surface* of each declaration (name,
binders, body text, docstring, proof text) and does not attempt to elaborate
Lean.  Everything downstream that needs meaning goes through `leansym.py`,
which converts a body to sympy and refuses anything it does not understand.
"""

from __future__ import annotations

import json
import re
from dataclasses import dataclass, field, asdict
from pathlib import Path

from paths import CALIBRATOR, require, ARTIFACTS as ART  # noqa: E402

require(CALIBRATOR, "proofs/Calibrator")

# A new top-level declaration starts at column 0 with one of these.
DECL_START = re.compile(
    r"^(/--|/-!|/-|@\[|noncomputable\s+def\b|private\s+def\b|def\b|abbrev\b|"
    r"theorem\b|lemma\b|structure\b|class\b|instance\b|inductive\b|"
    r"namespace\b|end\b|open\b|import\b|variable\b|example\b|section\b|"
    r"universe\b|attribute\b|set_option\b|macro\b|notation\b|deriving\b)"
)

DEF_HEAD = re.compile(
    r"^(?:noncomputable\s+|private\s+|protected\s+|partial\s+)*"
    r"(def|abbrev)\s+([A-Za-z_][A-Za-z0-9_.'₀-₉!?]*)"
)
THM_HEAD = re.compile(
    r"^(?:private\s+|protected\s+|@\[[^\]]*\]\s*)*"
    r"(theorem|lemma)\s+([A-Za-z_][A-Za-z0-9_.'₀-₉!?]*)"
)


@dataclass
class Decl:
    kind: str  # "def" | "theorem"
    name: str
    module: str  # e.g. Calibrator.PortabilityDrift
    file: str
    line: int
    docstring: str = ""
    signature: str = ""  # text between name and ':=' / ':' body separator
    body: str = ""  # RHS of ':=' for defs; statement for theorems
    proof: str = ""  # theorems only
    binders: list = field(default_factory=list)  # [(names, type)]
    raw: str = ""

    @property
    def fqn(self) -> str:
        return f"{self.module}.{self.name}"


def _strip_block_comments(text: str) -> str:
    """Blank out /- ... -/ comments but keep /-- docstrings and line offsets."""
    out = list(text)
    i, n = 0, len(text)
    while i < n - 1:
        if text[i] == "/" and text[i + 1] == "-":
            # keep docstrings (/--) and section headers (/-!)
            if i + 2 < n and text[i + 2] in "-!":
                i += 2
                continue
            depth, j = 1, i + 2
            while j < n - 1 and depth:
                if text[j] == "/" and text[j + 1] == "-":
                    depth += 1
                    j += 2
                elif text[j] == "-" and text[j + 1] == "/":
                    depth -= 1
                    j += 2
                else:
                    j += 1
            for k in range(i, min(j, n)):
                if out[k] != "\n":
                    out[k] = " "
            i = j
        else:
            i += 1
    return "".join(out)


def _split_blocks(lines: list[str]) -> list[tuple[int, list[str]]]:
    """Split into (start_line_index, block_lines) at column-0 declaration starts."""
    starts = [i for i, ln in enumerate(lines) if DECL_START.match(ln)]
    blocks = []
    for a, b in zip(starts, starts[1:] + [len(lines)]):
        blocks.append((a, lines[a:b]))
    return blocks


def _merge_docstrings(blocks):
    """Attach a /-- ... -/ block to the declaration that follows it."""
    merged, pending = [], None
    for start, blk in blocks:
        head = blk[0]
        if head.startswith("/--"):
            text = "\n".join(blk)
            # a docstring block may itself contain the decl if -/ is mid-block
            if "-/" in text:
                idx = text.index("-/") + 2
                doc, rest = text[:idx], text[idx:]
                doc_body = doc[3:-2].strip()
                if rest.strip():
                    merged.append((start, rest.lstrip("\n").split("\n"), doc_body))
                    pending = None
                else:
                    pending = doc_body
                continue
            pending = text
            continue
        if head.startswith("/-!") or head.startswith("/-"):
            pending = None
            continue
        merged.append((start, blk, pending or ""))
        pending = None
    return merged


def _split_binders(sig: str) -> list[tuple[list[str], str]]:
    """Parse `(a b : ℝ) (h : 0 < a) {n : ℕ}` into [(['a','b'],'ℝ'), ...]."""
    binders, depth, cur, opener = [], 0, "", ""
    for ch in sig:
        if ch in "({[":
            if depth == 0:
                opener, cur = ch, ""
                depth += 1
                continue
            depth += 1
        elif ch in ")}]":
            depth -= 1
            if depth == 0:
                if ":" in cur:
                    names, ty = cur.split(":", 1)
                    binders.append((names.split(), ty.strip(), opener))
                continue
        if depth:
            cur += ch
    return [(n, t, o) for n, t, o in binders]


def _find_top_level(s: str, tok: str) -> int:
    """Index of `tok` at bracket depth 0, or -1."""
    depth = 0
    i = 0
    while i < len(s):
        c = s[i]
        if c in "({[⟨":
            depth += 1
        elif c in ")}]⟩":
            depth -= 1
        elif depth == 0 and s.startswith(tok, i):
            # require token boundary for word-ish tokens
            return i
        i += 1
    return -1


def parse_file(path: Path) -> list[Decl]:
    raw = path.read_text(encoding="utf-8")
    text = _strip_block_comments(raw)
    lines = text.split("\n")
    module = "Calibrator." + str(path.relative_to(CALIBRATOR)).replace(".lean", "").replace("/", ".")
    decls: list[Decl] = []

    for start, blk, doc in _merge_docstrings(_split_blocks(lines)):
        head = blk[0]
        block_text = "\n".join(blk).rstrip()
        m = DEF_HEAD.match(head)
        if m:
            name = m.group(2)
            after = block_text[m.end():]
            # attribute lines before def are rare at col 0; ignore
            eq = _find_top_level(after, ":=")
            if eq >= 0:
                sig, body = after[:eq], after[eq + 2:]
            else:
                sig, body = after, ""  # pattern-matching def (| 0 => ...)
            decls.append(
                Decl("def", name, module, str(path), start + 1, doc,
                     sig.strip(), body.strip(), "", _split_binders(sig), block_text)
            )
            continue
        m = THM_HEAD.match(head)
        if m:
            name = m.group(2)
            after = block_text[m.end():]
            eq = _find_top_level(after, ":= by")
            if eq < 0:
                eq = _find_top_level(after, ":=")
            if eq >= 0:
                stmt, proof = after[:eq], after[eq + 2:]
            else:
                stmt, proof = after, ""
            # statement is binders then ':' then the proposition
            colon = _find_top_level(stmt, ":")
            if colon >= 0:
                sig, prop = stmt[:colon], stmt[colon + 1:]
            else:
                sig, prop = stmt, ""
            decls.append(
                Decl("theorem", name, module, str(path), start + 1, doc,
                     sig.strip(), prop.strip(), proof.strip(),
                     _split_binders(sig), block_text)
            )
    return decls


def parse_all(root: Path = CALIBRATOR) -> list[Decl]:
    out = []
    for p in sorted(root.rglob("*.lean")):
        if ".lake" in p.parts:
            continue
        out.extend(parse_file(p))
    top = root.parent / "Calibrator.lean"
    if top.exists():
        out.extend(parse_file_top(top))
    return out


def parse_file_top(path: Path) -> list[Decl]:
    return []


def main():
    decls = parse_all()
    defs = [d for d in decls if d.kind == "def"]
    thms = [d for d in decls if d.kind == "theorem"]
    print(f"parsed {len(defs)} defs, {len(thms)} theorems")
    out = ART / "decls.json"
    out.write_text(json.dumps([asdict(d) for d in decls], ensure_ascii=False, indent=1))
    print(f"wrote {out}")


if __name__ == "__main__":
    main()
