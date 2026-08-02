"""Mechanical Lean -> Python translation for the arithmetic subset.

Why this exists
---------------
Every existing validator in `proofs/validation/popgen_defs` re-types a Lean
formula into Python by hand.  That step is unvalidated, and it is where a false
validation entered the corpus.  This module removes the hand from the loop for
the subset of definitions that are pure real arithmetic -- which is almost all
of the coalescent/drift/LD corpus.

Design rule: **refuse, never guess.**  The tokenizer and parser accept a small
whitelisted grammar.  Anything outside it (dependent types, `Finset.sum`,
pattern-matching recursors, `if .. then ..`, unknown identifiers) raises
`Unsupported` and the definition is reported as NOT MECHANICALLY EXTRACTABLE
rather than silently mistranslated.

Supported grammar
-----------------
    expr    := term (('+' | '-') term)*
    term    := factor (('*' | '/') factor)*
    factor  := unary ('^' factor)?          -- right associative, binds tightest
    unary   := ('-')* atom
    atom    := number | ident | '(' expr ')' | app
    app     := qualified_ident atom+        -- Real.exp x, Real.sqrt x, f a b
    let     := 'let' ident ':=' expr ';'? expr

Recursive definitions (`| 0 => ..` / `| t + 1 => ..`) are handled separately by
`parse_nat_recursion`, which produces an iterative Python closure.
"""

from __future__ import annotations

import hashlib
import math
import re
from dataclasses import dataclass, field


class Unsupported(Exception):
    """The Lean body is outside the whitelisted arithmetic subset."""


# --------------------------------------------------------------------------
# Lean identifiers that map onto Python.  Nothing else is callable.
# --------------------------------------------------------------------------
BUILTINS = {
    "Real.exp": ("math.exp", 1),
    "Real.log": ("math.log", 1),
    "Real.sqrt": ("math.sqrt", 1),
    "Real.pi": ("math.pi", 0),
    "Real.cos": ("math.cos", 1),
    "Real.sin": ("math.sin", 1),
    "abs": ("abs", 1),
    "max": ("max", 2),
    "min": ("min", 2),
}

# Unicode subscripts and Greek letters that appear in Lean binder names.
_IDENT_EXTRA = "₀₁₂₃₄₅₆₇₈₉_'ₐₑₙₜᵢⱼₖ"
_GREEK = "αβγδεζηθικλμνξορστυφχψωΔΣΩμσρθλαπ"

_TOKEN_RE = re.compile(
    r"""
      (?P<ws>\s+)
    | (?P<num>\d+\.\d+|\d+)
    | (?P<ident>[A-Za-z%s%s][A-Za-z0-9.%s%s]*)
    | (?P<op>:=|=>|\^|\*|/|\+|-|\(|\)|,|;)
    """
    % (_GREEK, _IDENT_EXTRA, _GREEK, _IDENT_EXTRA),
    re.VERBOSE,
)


@dataclass
class Tok:
    kind: str
    text: str
    pos: int


def tokenize(src: str) -> list[Tok]:
    toks: list[Tok] = []
    i = 0
    while i < len(src):
        m = _TOKEN_RE.match(src, i)
        if not m:
            raise Unsupported(f"unlexable at offset {i}: {src[i:i + 30]!r}")
        i = m.end()
        kind = m.lastgroup
        if kind == "ws":
            continue
        toks.append(Tok(kind, m.group(), m.start()))
    return toks


# --------------------------------------------------------------------------
# Parser -> Python source string
# --------------------------------------------------------------------------
class Parser:
    def __init__(self, toks: list[Tok], binders: set[str]):
        self.toks = toks
        self.i = 0
        self.binders = set(binders)
        self.locals: set[str] = set()
        # Non-builtin, non-binder identifiers applied to arguments: these are
        # calls to *other* corpus definitions.  Recorded so the caller can wire
        # them up (and so we never invent a meaning for them).
        self.deps: set[str] = set()

    def peek(self) -> Tok | None:
        return self.toks[self.i] if self.i < len(self.toks) else None

    def eat(self, text: str) -> Tok:
        t = self.peek()
        if t is None or t.text != text:
            raise Unsupported(f"expected {text!r}, found {t.text if t else 'EOF'!r}")
        self.i += 1
        return t

    def at(self, text: str) -> bool:
        t = self.peek()
        return t is not None and t.text == text

    # ---- grammar ---------------------------------------------------------
    def parse(self) -> str:
        out = self.expr()
        if self.peek() is not None:
            raise Unsupported(f"trailing tokens from {self.peek().text!r}")
        return out

    def expr(self) -> str:
        if self.at("let"):
            return self.let_expr()
        out = self.term()
        while self.peek() and self.peek().text in ("+", "-"):
            op = self.toks[self.i].text
            self.i += 1
            out = f"({out} {op} {self.term()})"
        return out

    def let_expr(self) -> str:
        # `let x := e` followed (optionally after ';') by the body.
        self.eat("let")
        t = self.peek()
        if t is None or t.kind != "ident":
            raise Unsupported("let without identifier")
        name = t.text
        self.i += 1
        self.eat(":=")
        # The bound expression ends at ';' or at the start of the body.  Lean
        # source here is newline-delimited; we normalise to ';' before parsing.
        value = self.expr_until_semicolon()
        self.locals.add(name)
        body = self.expr()
        return f"({body.replace(_pyname(name), f'({value})')})" if False else \
            f"(lambda {_pyname(name)}: {body})({value})"

    def expr_until_semicolon(self) -> str:
        depth = 0
        start = self.i
        while self.i < len(self.toks):
            t = self.toks[self.i]
            if t.text == "(":
                depth += 1
            elif t.text == ")":
                depth -= 1
            elif t.text == ";" and depth == 0:
                break
            self.i += 1
        if self.i >= len(self.toks):
            raise Unsupported("let binding has no body separator")
        sub = Parser(self.toks[start:self.i], self.binders | self.locals)
        sub.locals = set(self.locals)
        out = sub.parse()
        self.deps |= sub.deps
        self.eat(";")
        return out

    def term(self) -> str:
        out = self.factor()
        while self.peek() and self.peek().text in ("*", "/"):
            op = self.toks[self.i].text
            self.i += 1
            rhs = self.factor()
            # Lean's `/` on ℝ is total with x/0 = 0; we keep Python semantics
            # and let division by zero surface as an error rather than a
            # silently different value.
            out = f"({out} {op} {rhs})"
        return out

    def factor(self) -> str:
        base = self.unary()
        if self.at("^"):
            self.i += 1
            return f"({base} ** {self.factor()})"
        return base

    def unary(self) -> str:
        if self.at("-"):
            self.i += 1
            return f"(-{self.unary()})"
        return self.atom()

    def atom(self) -> str:
        t = self.peek()
        if t is None:
            raise Unsupported("unexpected end of expression")
        if t.text == "(":
            self.i += 1
            inner = self.expr()
            if self.at(":"):
                # Type ascription / numeric cast, e.g. `(k : ℝ)`.  ℝ and ℕ are
                # the only targets in this subset; a ℕ cast would truncate, so
                # it is refused rather than approximated.
                self.i += 1
                ty = self.peek()
                if ty is None or ty.text not in ("ℝ",):
                    raise Unsupported(f"cast to {ty.text if ty else 'EOF'!r}")
                self.i += 1
            self.eat(")")
            return f"({inner})"
        if t.kind == "num":
            self.i += 1
            return f"({t.text} if False else float({t.text}))" if False else f"{float(t.text)!r}"
        if t.kind == "ident":
            return self.ident_or_app()
        raise Unsupported(f"unexpected token {t.text!r}")

    def ident_or_app(self) -> str:
        t = self.toks[self.i]
        name = t.text
        self.i += 1
        if name in ("fun", "if", "then", "else", "match", "with", "do"):
            raise Unsupported(f"control construct {name!r} not in subset")
        if name in BUILTINS:
            py, arity = BUILTINS[name]
            if arity == 0:
                return py
            args = [self.atom() for _ in range(arity)]
            return f"{py}({', '.join(args)})"
        if name in self.binders or name in self.locals:
            return _pyname(name)
        # Unknown identifier.  If arguments follow it is an application of
        # another corpus definition; otherwise it is a free variable we cannot
        # resolve.  Either way we record it and emit a call the caller binds.
        args = []
        while True:
            nxt = self.peek()
            if nxt is None:
                break
            if nxt.text == "(" or nxt.kind == "num" or (
                nxt.kind == "ident" and nxt.text not in ("let",)
            ):
                args.append(self.atom())
            else:
                break
        self.deps.add(name)
        if not args:
            raise Unsupported(f"free variable {name!r} is not a binder")
        return f"_dep[{name!r}]({', '.join(args)})"


def _pyname(lean_name: str) -> str:
    """Map a Lean binder to a legal Python identifier, injectively."""
    out = []
    for ch in lean_name:
        if ch.isascii() and (ch.isalnum() or ch == "_"):
            out.append(ch)
        else:
            out.append("_u%04x" % ord(ch))
    s = "".join(out)
    return "v_" + s


# --------------------------------------------------------------------------
# Definition extraction from a .lean file
# --------------------------------------------------------------------------
_DEF_RE = re.compile(
    r"^(?:noncomputable\s+)?def\s+(?P<name>[A-Za-z_][A-Za-z0-9_'!?]*)\s*(?P<binders>.*?):=\s*$",
    re.MULTILINE,
)


@dataclass
class LeanDef:
    name: str
    module: str
    line: int
    binders: list[str]
    body_src: str
    sha256: str
    py_src: str | None = None
    deps: set[str] = field(default_factory=set)
    error: str | None = None

    @property
    def fqn(self) -> str:
        return f"Calibrator.{self.module}.{self.name}"


_BINDER_RE = re.compile(r"\(([^:()]+):\s*([^()]+)\)")


def _parse_binders(sig: str) -> list[str]:
    names: list[str] = []
    for group, ty in _BINDER_RE.findall(sig):
        ty = ty.strip()
        if ty not in ("ℝ", "ℕ"):
            raise Unsupported(f"binder type {ty!r} not in subset")
        names.extend(group.split())
    if "{" in sig or "[" in sig:
        raise Unsupported("implicit/instance binders not in subset")
    return names


def _body_lines(lines: list[str], start: int) -> list[str]:
    """Collect the indented continuation lines that form a def body."""
    body: list[str] = []
    for ln in lines[start:]:
        if ln.strip() == "":
            if body:
                break
            continue
        if not ln.startswith((" ", "\t", "|")) and ln.strip():
            break
        body.append(ln)
    return body


def extract_file(path: str, module: str) -> list[LeanDef]:
    text = open(path, encoding="utf-8").read()
    lines = text.split("\n")
    out: list[LeanDef] = []
    for m in _DEF_RE.finditer(text):
        line_no = text[: m.start()].count("\n") + 1
        body = _body_lines(lines, line_no)
        body_src = "\n".join(body)
        d = LeanDef(
            name=m.group("name"),
            module=module,
            line=line_no,
            binders=[],
            body_src=body_src,
            sha256=hashlib.sha256(
                (m.group(0) + "\n" + body_src).encode()
            ).hexdigest()[:16],
        )
        try:
            d.binders = _parse_binders(m.group("binders"))
            if "|" in body_src:
                raise Unsupported("recursive/match body -- use parse_nat_recursion")
            flat = re.sub(r"\s*--.*", "", body_src)
            flat = re.sub(r"\n\s*", "\n", flat).strip()
            # A `let` line ends at the newline; make that explicit for the parser.
            flat = re.sub(r"(?m)^(let\s+[^\n]*?)$", r"\1;", flat)
            flat = flat.replace("\n", " ")
            p = Parser(tokenize(flat), set(d.binders))
            d.py_src = p.parse()
            d.deps = p.deps
        except Unsupported as e:
            d.error = str(e)
        out.append(d)
    return out


def compile_def(d: LeanDef, dep_table: dict) -> callable:
    """Turn an extracted definition into a Python callable.

    `dep_table` supplies callables for any other corpus definitions the body
    references.  A missing dependency raises at call time, never silently.
    """
    if d.py_src is None:
        raise Unsupported(d.error or "not extractable")
    args = ", ".join(_pyname(b) for b in d.binders)
    src = f"def _f({args}):\n    return {d.py_src}\n"
    ns = {"math": math, "_dep": dep_table}
    exec(compile(src, f"<lean:{d.fqn}>", "exec"), ns)
    fn = ns["_f"]
    fn.lean_fqn = d.fqn
    fn.lean_source = f"{d.module}.lean:{d.line}"
    fn.lean_sha = d.sha256
    fn.lean_body = d.body_src
    return fn
