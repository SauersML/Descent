"""Lean expression -> Python source, generated from the parsed body.

Nothing here is hand transcription: the input is the exact body text captured by
`lean_parse.py`, and the output is Python that evaluates it under Mathlib's
totality conventions (see `lean_rt.py`).  Anything outside the supported subset
raises `Untranslatable` with a reason, which is recorded rather than guessed at.
"""
from __future__ import annotations

import re

class Untranslatable(Exception):
    pass


SUBS = {ord(c): f"_{i}" for i, c in enumerate("₀₁₂₃₄₅₆₇₈₉")}
SUBS[ord("'")] = "_p"
SUBS.update({ord(c): f"_{n}" for c, n in
             zip("ₐₑₕᵢⱼₖₗₘₙₒₚᵣₛₜᵤᵥₓ", "aehijklmnoprstuvx")})
# Greek identifiers are legal Python identifiers, but normalise the few that
# collide with Python builtins or with our own runtime alias.
SUBS.update({ord("λ"): "lam"})


def pyname(name: str) -> str:
    """A Python-legal identifier for a Lean identifier (subscripts, primes)."""
    out = name.translate(SUBS).replace(".", "_")
    if not out.isidentifier():
        out = re.sub(r"\W", "_", out)
    if out in ("lambda", "def", "class", "if", "else", "return", "and", "or",
               "not", "in", "is", "for", "while", "import", "from", "None"):
        out += "_"
    return out


# ---------------------------------------------------------------- tokeniser

TOKEN_RE = re.compile(r"""
    (?P<ws>\s+)
  | (?P<num>\d+\.\d+(?:[eE][-+]?\d+)?|\d+(?:[eE][-+]?\d+)?)
  | (?P<ident>[A-Za-z_Α-ωϑ-ϵᴀ-ᵿ℀-⅏Ḁ-ỿ][A-Za-z0-9_'Α-ωϑ-ϵ₀-₉ₐ-ₜḀ-ỿ]*(?:\.[A-Za-z0-9_'₀-₉]+)*)
  | (?P<op><=|>=|!=|:=|=>|<\||\|>|\.\.|[-+*/%^()\[\]{},:;<>=|↦→←≤≥≠∧∨¬⁻¹↑√⌊⌋‖∑∏∫∘⟨⟩·×∙∈∉⊆∩∪ℝℕℤ∞πΦ⁻¹])
  | (?P<other>.)
""", re.X)

BINOPS = {
    "∨": (30, "left", "or"),
    "∧": (35, "left", "and"),
    "=": (50, "none", "=="), "≠": (50, "none", "!="),
    "<": (50, "none", "<"), ">": (50, "none", ">"),
    "≤": (50, "none", "<="), "≥": (50, "none", ">="),
    "<=": (50, "none", "<="), ">=": (50, "none", ">="),
    "+": (65, "left", "+"), "-": (65, "left", "-"),
    "*": (70, "left", "*"),
    "/": (70, "left", "DIV"),
    "%": (70, "left", "%"),
    "^": (75, "right", "POW"),
}

FUNCS = {
    "Real.exp": ("_rt.rexp", 1), "Real.log": ("_rt.rlog", 1),
    "Real.sqrt": ("_rt.rsqrt", 1), "Real.cos": ("_rt.cos", 1),
    "Real.sin": ("_rt.sin", 1), "Real.tan": ("_rt.tan", 1),
    "Real.cosh": ("_rt.cosh", 1), "Real.sinh": ("_rt.sinh", 1),
    "Real.tanh": ("_rt.tanh", 1), "Real.arctan": ("_rt.arctan", 1),
    "Real.arcsin": ("_rt.arcsin", 1), "Real.arccos": ("_rt.arccos", 1),
    "Real.logb": ("_rt.logb", 2), "Real.rpow": ("_rt.lpow", 2),
    "Real.nnabs": ("_rt.rabs", 1),
    "abs": ("_rt.rabs", 1), "max": ("_rt.rmax", 2), "min": ("_rt.rmin", 2),
    "Nat.cast": ("float", 1), "Int.cast": ("float", 1), "id": ("(lambda _x: _x)", 1),
}
CONSTS = {"Real.pi": "_rt.pi", "π": "_rt.pi"}

# tokens whose presence means the body is outside the arithmetic fragment
HARD_STOP = {
    "∑": "Finset/indexed sum", "∏": "indexed product", "∫": "integral",
    "√": "notation √ (use Real.sqrt)", "⌊": "floor", "⌋": "floor",
    "‖": "norm of a vector/matrix", "∘": "function composition",
    "∈": "set membership", "∉": "set membership", "⊆": "set inclusion",
    "∩": "set operation", "∪": "set operation", "×": "product type",
    "⟨": "anonymous constructor", "⟩": "anonymous constructor",
}


class Tok:
    __slots__ = ("kind", "text", "line", "col")

    def __init__(self, kind, text, line, col):
        self.kind, self.text, self.line, self.col = kind, text, line, col

    def __repr__(self):
        return f"{self.kind}:{self.text}"


def tokenize(src: str):
    toks, line, col = [], 0, 0
    for m in TOKEN_RE.finditer(src):
        kind = m.lastgroup
        text = m.group()
        if kind == "ws":
            nl = text.count("\n")
            if nl:
                line += nl
                col = len(text) - text.rfind("\n") - 1
            else:
                col += len(text)
            continue
        if kind == "other":
            raise Untranslatable(f"unrecognised character {text!r}")
        toks.append(Tok(kind, text, line, col))
        col += len(text)
    return toks


# ------------------------------------------------------------------ parser

class Parser:
    def __init__(self, toks, struct_args):
        self.t = toks
        self.i = 0
        self.stop_cols = []            # layout barriers introduced by `let`
        self.struct_args = struct_args  # names bound to structures/tuples

    def peek(self, k=0):
        j = self.i + k
        return self.t[j] if j < len(self.t) else None

    def next(self):
        tok = self.t[self.i]
        self.i += 1
        return tok

    def at(self, *texts):
        p = self.peek()
        return p is not None and p.text in texts

    def expect(self, text):
        if not self.at(text):
            raise Untranslatable(f"expected {text!r}, found {self.peek()!r}")
        return self.next()

    def blocked(self):
        """True when the next token falls outside the current layout block."""
        p = self.peek()
        if p is None or not self.stop_cols:
            return p is None
        prev = self.t[self.i - 1] if self.i else None
        return prev is not None and p.line > prev.line and p.col <= self.stop_cols[-1]

    # ---- expressions

    def expr(self, min_prec=0):
        left = self.unary()
        while True:
            p = self.peek()
            if p is None or self.blocked():
                break
            op = BINOPS.get(p.text)
            if op is None or op[0] < min_prec:
                break
            prec, assoc, pyop = op
            self.next()
            right = self.expr(prec + (0 if assoc == "right" else 1))
            if pyop == "DIV":
                left = f"_rt.rdiv({left}, {right})"
            elif pyop == "POW":
                left = f"_rt.lpow({left}, {right})"
            elif pyop in ("and", "or"):
                left = f"({left} {pyop} {right})"
            else:
                left = f"({left} {pyop} {right})"
        return left

    def unary(self):
        p = self.peek()
        if p is None:
            raise Untranslatable("unexpected end of body")
        if p.text == "-":
            self.next()
            return f"(-{self.unary()})"
        if p.text == "¬":
            self.next()
            return f"(not {self.unary()})"
        if p.text == "↑":
            self.next()
            return self.unary()
        return self.app()

    def app(self):
        head = self.atom()
        args = []
        while True:
            p = self.peek()
            if p is None or self.blocked():
                break
            if p.text in BINOPS or p.text in (")", "]", "}", ",", ":", ";", "then",
                                              "else", "=>", "↦", "|"):
                break
            if p.text == "⁻¹":
                self.next()
                head = f"_rt.rinv({head})"
                continue
            if p.kind in ("ident", "num") or p.text in ("(", "-", "↑", "|"):
                args.append(self.atom())
                continue
            break
        if not args:
            return head
        if head.startswith("_FN:"):
            fn, arity = head[4:].split("|")
            arity = int(arity)
            if len(args) != arity:
                raise Untranslatable(f"arity mismatch for {fn}: got {len(args)}")
            return f"{fn}({', '.join(args)})"
        return f"{head}({', '.join(args)})"

    def atom(self):
        p = self.peek()
        if p is None:
            raise Untranslatable("unexpected end of body")
        if p.text in HARD_STOP:
            raise Untranslatable(HARD_STOP[p.text])
        if p.text == "|":                       # |e|  absolute value
            self.next()
            e = self.expr()
            self.expect("|")
            return f"_rt.rabs({e})"
        if p.text == "(":
            self.next()
            if self.at(")"):
                raise Untranslatable("unit / empty parentheses")
            e = self.expr()
            if self.at(":"):                    # type ascription (e : T)
                self.next()
                depth = 1
                while depth:
                    q = self.next()
                    if q.text == "(":
                        depth += 1
                    elif q.text == ")":
                        depth -= 1
                return f"({e})"
            if self.at(","):
                raise Untranslatable("tuple literal")
            self.expect(")")
            return f"({e})"
        if p.text == "if":
            self.next()
            cond = self.expr()
            self.expect("then")
            a = self.expr()
            self.expect("else")
            b = self.expr()
            return f"({a} if {cond} else {b})"
        if p.text == "fun":
            self.next()
            names = []
            while self.peek() and self.peek().text not in ("=>", "↦"):
                tok = self.next()
                if tok.kind == "ident":
                    names.append(pyname(tok.text))
            self.next()
            body = self.expr()
            return f"(lambda {', '.join(names)}: {body})"
        if p.kind == "num":
            self.next()
            return p.text if "." in p.text or "e" in p.text.lower() else f"{p.text}.0"
        if p.kind == "ident":
            self.next()
            name = p.text
            if name in ("let",):
                return self.let_tail()
            if name in CONSTS:
                return CONSTS[name]
            if name in FUNCS:
                fn, ar = FUNCS[name]
                return f"_FN:{fn}|{ar}"
            if "." in name:                     # projection or qualified name
                base, *flds = name.split(".")
                if base in self.struct_args or (flds and flds[0].isdigit()):
                    out = pyname(base)
                    for f in flds:
                        out = f"_rt._proj({out}, {f!r})"
                    return out
                raise Untranslatable(f"qualified name {name}")
            return pyname(name)
        raise Untranslatable(f"unsupported token {p.text!r}")

    def let_tail(self):
        raise Untranslatable("internal: let handled at statement level")


# ------------------------------------------------------------- entry point

LET_RE = re.compile(r"^(\s*)let\s+([A-Za-z_][\w'₀-₉ₐ-ₜ]*)\s*(?::[^:=]*)?:=\s*(.*)$")


def translate_body(body: str, struct_args=()):
    """Translate a Lean body into (statements, return_expression)."""
    toks = tokenize(body)
    if not toks:
        raise Untranslatable("empty body")
    stmts = []
    p = Parser(toks, set(struct_args))
    while p.at("let"):
        letcol = p.peek().col
        p.next()
        name_tok = p.next()
        if name_tok.kind != "ident":
            raise Untranslatable("unsupported let pattern")
        if p.at(":"):                                    # let x : T := e
            while not p.at(":="):
                p.next()
        p.expect(":=")
        p.stop_cols.append(letcol)
        val = p.expr()
        p.stop_cols.pop()
        stmts.append(f"{pyname(name_tok.text)} = {val}")
        if p.at(";"):
            p.next()
    ret = p.expr()
    if p.peek() is not None:
        raise Untranslatable(f"trailing tokens after expression: {p.peek()!r}")
    return stmts, ret


def translate_def(d, struct_arg_names=(), fname=None):
    """Return (python_source, argnames) or raise Untranslatable."""
    argnames = [pyname(n) for a in d["args"] if not a["implicit"] for n in a["names"]]
    if not argnames and not d["body"].strip():
        raise Untranslatable("no explicit arguments and no body")
    stmts, ret = translate_body(d["body"], struct_arg_names)
    lines = [f"def {fname or pyname(d['short'])}({', '.join(argnames)}):"]
    for s in stmts:
        lines.append(f"    {s}")
    lines.append(f"    return {ret}")
    return "\n".join(lines), argnames
