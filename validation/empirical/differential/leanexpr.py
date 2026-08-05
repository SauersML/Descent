"""Mechanical Lean -> Python translation for the arithmetic subset.

Why this exists
---------------
Every existing validator in `validation/popgen_defs` re-types a Lean
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
_GREEK = "αβγδεζηθικλμνξορστυφχψωΔΣΩμσρθλαπℝℕℤℚ"

_TOKEN_RE = re.compile(
    r"""
      (?P<ws>\s+)
    | (?P<num>\d+\.\d+|\d+)
    | (?P<ident>[A-Za-z%s%s][A-Za-z0-9.%s%s]*)
    | (?P<op>:=|=>|:|\^|\*|/|\+|-|\(|\)|,|;)
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
    r"^(?:noncomputable\s+)?def\s+(?P<name>[A-Za-z_][A-Za-z0-9_'!?]*)\s*"
    r"(?P<binders>[^\n]*?):=(?P<inline>[^\n]*)$",
    re.MULTILINE,
)

# `def f (a b : ℝ) : ℕ → ℝ` followed by `| 0 => ..` / `| t + 1 => ..`
_REC_DEF_RE = re.compile(
    r"^(?:noncomputable\s+)?def\s+(?P<name>[A-Za-z_][A-Za-z0-9_'!?]*)\s*"
    r"(?P<binders>.*?)\s*:\s*ℕ\s*→\s*ℝ\s*$",
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
    base_src: str | None = None
    is_recursion: bool = False
    namespace: str = ""

    @property
    def fqn(self) -> str:
        return f"Descent.{self.module}.{self.name}"

    @property
    def lean_name(self) -> str:
        """The name Lean gives this declaration -- namespace, not module path.

        `fqn` above is the MODULE path and is only ever printed.  Resolution
        must use this one: `Descent.Core.ploidy` lives in `Core/Fst.lean`, so
        the module path and the Lean name disagree about both the middle
        component and its meaning.
        """
        return f"{self.namespace}.{self.name}" if self.namespace else self.name


def _blank_comments(text: str) -> str:
    """Replace comment characters with spaces, preserving every newline.

    The namespace scan below must agree with the line numbers the definition
    scan produces, so comments cannot be deleted -- only emptied.  It matters
    because `end` appears in prose constantly, and one stray `end` read as code
    pops a namespace and misfiles every declaration after it.
    """
    out = list(text)

    def blank(a, b):
        for k in range(a, min(b, len(out))):
            if out[k] != "\n":
                out[k] = " "

    i, n = 0, len(text)
    while i < n:
        if text.startswith("/-", i):
            depth, j = 1, i + 2
            while j < n and depth:
                if text.startswith("/-", j):
                    depth, j = depth + 1, j + 2
                elif text.startswith("-/", j):
                    depth, j = depth - 1, j + 2
                else:
                    j += 1
            blank(i, j)
            i = j
        elif text.startswith("--", i):
            j = text.find("\n", i)
            j = n if j < 0 else j
            blank(i, j)
            i = j
        else:
            i += 1
    return "".join(out)


_NS_RE = re.compile(r"^namespace\s+([A-Za-z_][A-Za-z0-9_.'₀-₉]*)\s*$")
_SECTION_RE = re.compile(r"^section\b")
_END_RE = re.compile(r"^end\b")


def namespaces_by_line(text: str) -> list[str]:
    """The namespace in effect at each 1-based line, as a dotted string.

    `section` and `namespace` share the `end` keyword, so only a stack that
    carries both can tell which one an `end` closes.
    """
    stack: list[str | None] = []
    out = [""]
    for line in _blank_comments(text).split("\n"):
        out.append(".".join(s for s in stack if s))
        m = _NS_RE.match(line)
        if m:
            stack.append(m.group(1))
        elif _SECTION_RE.match(line):
            stack.append(None)
        elif _END_RE.match(line) and stack:
            stack.pop()
    return out


class Scope:
    """Resolve a name the way Lean does: relative to the caller's namespace.

    A body in `Descent.Core` that writes `ploidy` means `Descent.Core.ploidy`,
    and a body anywhere that writes `Descent.Core.ploidy` means the same thing.
    A table keyed by SHORT name cannot express either: it collapses
    `Descent.Core.scaledMutationRate` and `Descent.scaledMutationRate` onto one
    entry, and it has no entry at all for a name written with its prefix.

    That second failure is what put 81,131 rows in the cross-validation report.
    Every body calling into the `Core` kernel raised `KeyError` on the written
    name, `leanexpr` produced nothing, and the comparison recorded a
    disagreement -- 80,939 of them from `ibdRecurrenceStep` alone.  None was a
    disagreement about a value: not one row had two numbers in it.

    Longest enclosing prefix first, then outward, then the bare name.  That is
    Lean's rule, so a kernel is preferred to a wrapper over it from inside the
    kernel's own namespace, and the wrapper is still reachable from outside.
    """

    def __init__(self, table: dict, namespace: str):
        self.table, self.namespace = table, namespace

    def __getitem__(self, key: str):
        parts = self.namespace.split(".") if self.namespace else []
        for i in range(len(parts), -1, -1):
            cand = ".".join(parts[:i] + [key])
            if cand in self.table:
                return self.table[cand]
        raise KeyError(key)

    def __contains__(self, key: str) -> bool:
        try:
            self[key]
        except KeyError:
            return False
        return True


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
    nsline = namespaces_by_line(text)
    out: list[LeanDef] = []
    for m in _DEF_RE.finditer(text):
        line_no = text[: m.start()].count("\n") + 1
        # The signature may wrap across lines; the body begins after the match.
        body_start = text[: m.end()].count("\n") + 1
        inline = m.group("inline").strip()
        # A def is either `... :=` with an indented body, or `... := body` on
        # one line (possibly with indented continuations).
        body_src = (
            inline + "\n" + "\n".join(_body_lines(lines, body_start))
            if inline
            else "\n".join(_body_lines(lines, body_start))
        ).strip()
        d = LeanDef(
            name=m.group("name"),
            module=module,
            line=line_no,
            binders=[],
            body_src=body_src,
            sha256=hashlib.sha256(
                (m.group(0) + "\n" + body_src).encode()
            ).hexdigest()[:16],
            namespace=nsline[line_no],
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


def extract_recursions(path: str, module: str) -> list[LeanDef]:
    """Extract `ℕ → ℝ` primitive recursions of the shape

        | 0     => <base>
        | t + 1 => <step in which `f <binders> t` occurs>

    The recursive call is rewritten to a bound variable `prev`, giving a step
    function that the caller iterates.  Anything that recurses on more than the
    immediately preceding value, or that mentions `t` outside the recursive
    call, is refused: those are not simple iterations and translating them by
    eye is exactly the risk this module exists to remove.
    """
    text = open(path, encoding="utf-8").read()
    lines = text.split("\n")
    nsline = namespaces_by_line(text)
    out: list[LeanDef] = []
    for m in _REC_DEF_RE.finditer(text):
        line_no = text[: m.start()].count("\n") + 1
        # The signature may wrap across lines; the body begins after the match.
        body_start = text[: m.end()].count("\n") + 1
        body = _body_lines(lines, body_start)
        body_src = "\n".join(body)
        name = m.group("name")
        d = LeanDef(
            name=name, module=module, line=line_no, binders=[],
            body_src=body_src,
            sha256=hashlib.sha256((m.group(0) + "\n" + body_src).encode()).hexdigest()[:16],
            namespace=nsline[line_no],
        )
        try:
            d.binders = _parse_binders(m.group("binders"))
            flat = re.sub(r"\s*--.*", "", body_src)
            flat = re.sub(r"\s+", " ", flat).strip()
            mm = re.match(r"\|\s*0\s*=>\s*(.*?)\s*\|\s*(\w+)\s*\+\s*1\s*=>\s*(.*)$", flat)
            if not mm:
                raise Unsupported("not a two-branch ℕ recursion")
            base_src, ivar, step_src = mm.group(1), mm.group(2), mm.group(3)
            # Rewrite `name b1 b2 .. bk t` -> `prev`.
            call = re.escape(name) + r"\s+" + r"\s+".join(
                re.escape(b) for b in d.binders
            ) + r"\s+" + re.escape(ivar) + r"\b"
            step_src, n_sub = re.subn(call, "prev", step_src)
            if n_sub == 0:
                raise Unsupported("no recognised recursive call")
            if re.search(r"\b" + re.escape(ivar) + r"\b", step_src):
                raise Unsupported("index variable used outside the recursive call")
            if name in step_src:
                raise Unsupported("unrewritten recursive occurrence")
            pb = Parser(tokenize(base_src), set(d.binders))
            ps = Parser(tokenize(step_src), set(d.binders) | {"prev"})
            d.py_src = ps.parse()
            d.deps = pb.deps | ps.deps
            d.base_src = pb.parse()
            d.is_recursion = True
        except Unsupported as e:
            d.error = str(e)
        out.append(d)
    return out


def compile_recursion(d: LeanDef, dep_table: dict) -> callable:
    """Compile a recursion into `f(*binders, t)` evaluated by iteration."""
    if d.py_src is None:
        raise Unsupported(d.error or "not extractable")
    args = ", ".join(_pyname(b) for b in d.binders)
    src = (
        f"def _f({args}, _t):\n"
        f"    {_pyname('prev')} = {d.base_src}\n"
        f"    for _ in range(int(_t)):\n"
        f"        {_pyname('prev')} = {d.py_src}\n"
        f"    return {_pyname('prev')}\n"
    )
    ns = {"math": math, "_dep": dep_table}
    exec(compile(src, f"<lean:{d.fqn}>", "exec"), ns)
    fn = ns["_f"]
    fn.lean_fqn, fn.lean_source = d.fqn, f"{d.module}.lean:{d.line}"
    fn.lean_sha, fn.lean_body = d.sha256, d.body_src
    return fn


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
