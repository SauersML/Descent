"""Lean -> Python transpiler for the arithmetic fragment of Calibrator bodies.

Deliberately narrow.  It accepts numerals, identifiers, `+ - * / ^ ⁻¹`, `|x|`,
`max`/`min`, the `Real.*` transcendentals, `let ... := ...`, `if ... then ...
else ...`, and juxtaposition application of known-arity functions.  ANYTHING
else raises `Untranspilable`, which is a reported outcome, not a silent skip:
a definition we cannot transpile is a definition this tier does not cover, and
the residue is the number the simulation tiers inherit.

The emitted Python is written against a backend module supplying `sqrt`, `exp`,
`log`, `mx`, `mn`, `absv`, ... so the SAME source can be evaluated over floats,
over intervals, or over z3 terms.  That is what lets one transpilation serve
interval arithmetic, SMT and sampling.
"""
from __future__ import annotations

import re
import unicodedata


class Untranspilable(Exception):
    pass


# ---------------------------------------------------------------- tokenizer

SUBS = {c: str(i) for i, c in enumerate("₀₁₂₃₄₅₆₇₈₉")}
GREEK_OK = True

TOKEN_RE = re.compile(
    r"""
    (?P<ws>\s+)
  | (?P<num>\d+\.\d+|\d+)
  | (?P<ident>[A-Za-z_Ͱ-Ͽᵪ-ᵿ][A-Za-z_0-9'Ͱ-Ͽ₀-₉ᵢ-ᵪ.]*)
  | (?P<inv>⁻¹)
  | (?P<op>\*\*|<=|>=|==|≤|≥|≠|∧|∨|[-+*/^()<>,|])
    """,
    re.X,
)

KEYWORDS = {"let", "if", "then", "else", "fun", "with", "match", "do", "have", "in"}

# name -> (python_callable_name, arity)
BUILTINS = {
    "Real.sqrt": ("_b.sqrt", 1),
    "Real.exp": ("_b.exp", 1),
    "Real.log": ("_b.log", 1),
    "Real.sin": ("_b.sin", 1),
    "Real.cos": ("_b.cos", 1),
    "Real.tanh": ("_b.tanh", 1),
    "Real.arctan": ("_b.atan", 1),
    "Real.exp'": ("_b.exp", 1),
    "Real.rpow": ("_b.rpow", 2),
    "Real.logb": ("_b.logb", 2),
    "max": ("_b.mx", 2),
    "min": ("_b.mn", 2),
    "abs": ("_b.absv", 1),
    "Real.pi": ("_b.pi", 0),
    "Real.exp1": ("_b.e", 0),
    # Calibrator/Probability.lean:487 -- standard normal CDF, used in 8 files
    "Phi": ("_b.Phi", 1),
    "phiPdf": ("_b.phi", 1),
    "probitInv": ("_b.probit", 1),
}
CONSTANTS = {"Real.pi": "_b.pi"}


def _tokens(src: str):
    out = []
    i = 0
    while i < len(src):
        m = TOKEN_RE.match(src, i)
        if not m:
            raise Untranspilable(f"bad char {src[i]!r}")
        i = m.end()
        if m.lastgroup == "ws":
            continue
        out.append((m.lastgroup, m.group()))
    return out


def pyname(lean: str) -> str:
    """Sanitize a Lean identifier into a valid, collision-free Python name."""
    s = "".join(SUBS.get(c, c) for c in lean)
    s = s.replace("'", "_p").replace(".", "_")
    out = []
    for c in s:
        if c.isalnum() or c == "_":
            out.append(c)
        else:
            out.append("_u%04x" % ord(c))
    s = "".join(out)
    if s[0].isdigit():
        s = "v" + s
    return s


# ---------------------------------------------------------------- parser


class Parser:
    """Recursive-descent over the token list, emitting Python source strings."""

    def __init__(self, toks, arity, locals_):
        self.t = toks
        self.i = 0
        self.arity = arity  # name -> int, for user-defined callables
        self.locals = locals_  # set of bound variable names (arity 0)

    def peek(self, k=0):
        return self.t[self.i + k] if self.i + k < len(self.t) else (None, None)

    def eat(self, val=None):
        kind, v = self.peek()
        if kind is None:
            raise Untranspilable("unexpected end")
        if val is not None and v != val:
            raise Untranspilable(f"expected {val!r} got {v!r}")
        self.i += 1
        return v

    # expr := let | if | comparison
    def expr(self):
        kind, v = self.peek()
        if v == "let":
            return self.let_()
        if v == "if":
            return self.if_()
        return self.cmp_()

    def let_(self):
        self.eat("let")
        name = self.eat()
        if self.peek()[1] == ":":
            raise Untranspilable("typed let")
        # `:=` arrives as ':' '=' or as op '='? tokenizer has no ':=', handle:
        if self.peek()[1] not in (":=",):
            # ':' is not in our op set, so ':=' must have been split; bail
            raise Untranspilable("let syntax")
        self.eat()
        val = self.cmp_()
        self.locals.add(name)
        body = self.expr()
        return f"(lambda {pyname(name)}: {body})({val})"

    def if_(self):
        self.eat("if")
        c = self.cmp_()
        self.eat("then")
        a = self.expr()
        self.eat("else")
        b = self.expr()
        return f"_b.ite({c}, {a}, {b})"

    CMPS = {"<": "<", ">": ">", "≤": "<=", "≥": ">=", "=": "==", "≠": "!=",
            "<=": "<=", ">=": ">=", "==": "=="}

    def cmp_(self):
        left = self.add()
        kind, v = self.peek()
        if v in self.CMPS:
            self.eat()
            right = self.add()
            return f"_b.cmp({left}, '{self.CMPS[v]}', {right})"
        if v in ("∧", "∨"):
            self.eat()
            right = self.cmp_()
            op = "_b.land" if v == "∧" else "_b.lor"
            return f"{op}({left}, {right})"
        return left

    def add(self):
        e = self.mul()
        while self.peek()[1] in ("+", "-"):
            op = self.eat()
            e = f"({e} {op} {self.mul()})"
        return e

    def mul(self):
        e = self.unary()
        while self.peek()[1] in ("*", "/"):
            op = self.eat()
            r = self.unary()
            e = f"_b.div({e}, {r})" if op == "/" else f"({e} * {r})"
        return e

    def unary(self):
        if self.peek()[1] == "-":
            self.eat()
            return f"(- {self.unary()})"
        return self.power()

    def power(self):
        base = self.app()
        if self.peek()[1] in ("^", "**"):
            self.eat()
            exp = self.unary()  # right-assoc, binds tighter than * /
            return f"_b.pow({base}, {exp})"
        return base

    def app(self):
        head = self.atom()
        n = self._pending_arity
        args = []
        while n > 0:
            args.append(self.atom())  # application binds tighter than ^ in Lean
            n -= 1
        if args:
            return f"{head}({', '.join(args)})"
        return head

    def atom(self):
        self._pending_arity = 0
        kind, v = self.peek()
        if kind is None:
            raise Untranspilable("unexpected end in atom")
        if kind == "num":
            self.eat()
            return f"{float(v)!r}"
        if v == "(":
            self.eat()
            e = self.expr()
            if self.peek()[1] == ",":
                raise Untranspilable("tuple")
            self.eat(")")
            return self._postfix(f"({e})")
        if v == "|":
            self.eat()
            e = self.expr()
            self.eat("|")
            return self._postfix(f"_b.absv({e})")
        if v == "-":
            self.eat()
            return f"(- {self.atom()})"
        if kind == "ident":
            if v in KEYWORDS:
                raise Untranspilable(f"keyword {v}")
            self.eat()
            if v in CONSTANTS:
                return self._postfix(CONSTANTS[v])
            if v in BUILTINS:
                fn, ar = BUILTINS[v]
                self._pending_arity = ar
                return fn
            if v in self.locals:
                return self._postfix(pyname(v))
            if v in self.arity:
                self._pending_arity = self.arity[v]
                if self._pending_arity == 0:
                    return self._postfix(pyname(v))
                return pyname(v)
            raise Untranspilable(f"unknown identifier {v}")
        raise Untranspilable(f"unexpected token {v!r}")

    def _postfix(self, s):
        while self.peek()[1] == "⁻¹":
            self.eat()
            s = f"_b.div(1.0, {s})"
        return s


def transpile(body: str, params, arity, name=""):
    """Return Python source for `body` given parameter names and known arities.

    `arity` maps callable names (user definitions) to argument counts.
    """
    src = body
    # strip Lean noise we can safely drop
    src = re.sub(r"--.*", "", src)
    src = re.sub(r"\(\s*([\d.]+)\s*:\s*ℝ\s*\)", r"\1", src)  # (2 : ℝ)
    src = re.sub(r"\(\s*([A-Za-z_][\w'₀-₉]*)\s*:\s*ℝ\s*\)", r"\1", src)
    src = src.replace("ℤ", "").replace("ℕ", "")
    if re.search(r"[∫∑∏⟨⟩∀∃λ]|fun |match |\bby\b|\bwhere\b|\bdo\b|\|", src):
        raise Untranspilable("non-arithmetic construct")
    if ":=" in src:
        # only `let x := e` is supported; mark the token explicitly
        src = src.replace(":=", " ≔ ")
    if ";" in src:
        src = src.replace(";", " ")
    src2 = src.replace("≔", "\x00")
    raw = []
    for part in src2.split("\x00"):
        raw.append(part)
    # rebuild token list manually so ':=' survives
    toks = []
    for k, part in enumerate(raw):
        if k:
            toks.append(("op", ":="))
        toks.extend(_tokens(part))
    locals_ = {p for p, _ in params}
    p = Parser(toks, arity, set(locals_))
    out = p.expr()
    if p.i != len(p.t):
        raise Untranspilable(f"trailing tokens at {p.t[p.i:][:4]}")
    return out


def build_arity(defs, module=None):
    """Arity map for identifier resolution.

    Names are reused across Lean files with DIFFERENT arities (e.g. two
    `hetDecayFactor`s).  When transpiling a body from `module`, that module's
    own definition wins, matching Lean's own resolution order.
    """
    ar = {}
    for d in defs:
        if d["module"] != module:
            ar.setdefault(d["name"], len(d["params"]))
    for d in defs:
        if d["module"] == module:
            ar[d["name"]] = len(d["params"])
    return ar
