"""Lean real-valued expression -> sympy, with recursive inlining of definitions.

The converter is deliberately *total or loud*: any construct it does not model
exactly raises `Unsupported`.  A validator that silently guesses at a body it
cannot parse is worse than no validator, because it manufactures agreement.
Nothing here transcribes a formula by hand; every expression compared
downstream comes from the Lean source text via this module.
"""

from __future__ import annotations

import re
import sympy as sp


class Unsupported(Exception):
    pass


# ---------------------------------------------------------------- tokenizer

IDENT = r"[A-Za-z_][A-Za-z0-9_.'₀-₉ₐ-ₜ]*"
GREEK = "αβγδεζηθικλμνξοπρστυφχψωΓΔΘΛΞΠΣΦΨΩ"
TOKEN_RE = re.compile(
    r"""
      (?P<num>\d+\.\d+|\d+)
    | (?P<ident>[A-Za-z_""" + GREEK + r"""][A-Za-z0-9_.'₀-₉ₐ-ₜ""" + GREEK + r"""]*)
    | (?P<op>\*\*|\^|\*|/|\+|-|=|≤|≥|<|>|≠|\(|\)|,|\||⁻¹|·|→|=>|:)
    | (?P<ws>\s+)
    """,
    re.VERBOSE,
)

# Constructs that mean the expression is not a closed-form real function.
POISON = {
    "Finset", "Matrix", "Set", "Filter", "Polynomial", "deriv", "∫", "∑", "∏",
    "Classical", "Function", "List", "Vector", "EuclideanSpace", "Measure",
    "PMF", "fun", "if", "then", "else", "match", "with", "let", "Nat", "Int",
    "Option", "Prod", "Sigma", "Quotient", "Ideal", "Module", "LinearMap",
    "iSup", "iInf", "sSup", "sInf", "Real.rpow",
}


def tokenize(s: str):
    toks, i = [], 0
    while i < len(s):
        m = TOKEN_RE.match(s, i)
        if not m:
            raise Unsupported(f"lex error at {s[i:i+20]!r}")
        i = m.end()
        if m.lastgroup == "ws":
            continue
        toks.append((m.lastgroup, m.group()))
    return toks


# ---------------------------------------------------------------- functions

UNARY = {
    "Real.sqrt": sp.sqrt,
    "Real.exp": sp.exp,
    "Real.log": sp.log,
    "Real.sin": sp.sin,
    "Real.cos": sp.cos,
    "Real.tan": sp.tan,
    "Real.arctan": sp.atan,
    "Real.sinh": sp.sinh,
    "Real.cosh": sp.cosh,
    "Real.tanh": sp.tanh,
    "abs": sp.Abs,
    "Real.toNNReal": None,
}
BINARY = {"min": sp.Min, "max": sp.Max}
CONSTS = {"Real.pi": sp.pi, "π": sp.pi}


class Converter:
    """Convert one Lean expression to sympy, inlining defs from `table`.

    `table` maps a bare definition name to (binder_names, body_text).
    """

    MAX_DEPTH = 12

    def __init__(self, table: dict[str, tuple[list[str], str]] | None = None,
                 opaque_defs: bool = False, opaque_fallback: bool = False,
                 must_inline: frozenset | None = None):
        """`opaque_defs` turns every user definition into an uninterpreted
        function symbol instead of inlining its body.  A theorem whose two
        sides are still equal under that reading uses nothing about the
        definitions it names -- it is pure algebra wearing a derivation's
        name."""
        self.table = table or {}
        self.opaque_defs = opaque_defs
        # A definition this converter cannot inline -- wrong arity, recursive,
        # unsupported body -- used to abort the WHOLE statement, so one
        # unreachable subterm made every theorem containing it unusable. Reading
        # the failure reasons showed that is where most of my "converter limit"
        # bucket came from: `Phi expects 0 args`, the recursion index of every
        # equation-compiler definition, and structure field access. With
        # opaque_fallback such a term becomes an uninterpreted function and the
        # rest of the statement still converts.
        #
        # `must_inline` is the guard that keeps this honest: the definition
        # being MUTATED must never go opaque, or its perturbation would be
        # invisible and the definition would be filed as unconstrained.
        self.opaque_fallback = opaque_fallback
        self.must_inline = must_inline or frozenset()

    # -- entry point
    def convert(self, text: str, env: dict[str, sp.Expr] | None = None,
                depth: int = 0, stack: tuple = ()):
        text = text.strip()
        if not text:
            raise Unsupported("empty expression")
        for bad in POISON:
            if re.search(rf"(?<![A-Za-z0-9_.]){re.escape(bad)}(?![A-Za-z0-9_])", text):
                raise Unsupported(f"non-closed-form construct: {bad}")
        self.toks = tokenize(text)
        self.pos = 0
        self.env = env or {}
        self.depth = depth
        self.stack = stack
        e = self.p_cmp()
        if self.pos != len(self.toks):
            raise Unsupported(f"trailing tokens at {self.toks[self.pos:][:4]}")
        return e

    # -- token helpers
    def peek(self):
        return self.toks[self.pos] if self.pos < len(self.toks) else (None, None)

    def eat(self, val=None):
        k, v = self.peek()
        if val is not None and v != val:
            raise Unsupported(f"expected {val!r}, got {v!r}")
        self.pos += 1
        return v

    # -- grammar
    def p_cmp(self):
        left = self.p_add()
        k, v = self.peek()
        if v in ("=", "≤", "≥", "<", ">", "≠"):
            self.eat()
            right = self.p_add()
            return {"=": sp.Eq, "≤": sp.Le, "≥": sp.Ge, "<": sp.Lt,
                    ">": sp.Gt, "≠": sp.Ne}[v](left, right)
        return left

    def p_add(self):
        e = self.p_mul()
        while self.peek()[1] in ("+", "-"):
            op = self.eat()
            r = self.p_mul()
            e = e + r if op == "+" else e - r
        return e

    def p_mul(self):
        e = self.p_unary()
        while self.peek()[1] in ("*", "/", "·"):
            op = self.eat()
            r = self.p_unary()
            e = e / r if op == "/" else e * r
        return e

    def p_unary(self):
        if self.peek()[1] == "-":
            self.eat()
            return -self.p_unary()
        return self.p_pow()

    def p_pow(self):
        base = self.p_app()
        if self.peek()[1] in ("^", "**"):
            self.eat()
            return base ** self.p_unary()  # right-assoc, binds unary minus
        if self.peek()[1] == "⁻¹":
            self.eat()
            return 1 / base
        return base

    def p_app(self):
        head_tok = self.peek()
        atom = self.p_atom()
        # gather juxtaposed arguments
        args = []
        while True:
            k, v = self.peek()
            if k == "num" or (k == "ident" and v not in ("then", "else")) or v == "(":
                args.append(self.p_atom_pow())
            else:
                break
        if not args:
            if isinstance(atom, _Def) and atom.arity == 0:
                return atom.apply([], self)
            if isinstance(atom, _Callable):
                raise Unsupported(f"partial/bare application of {atom.name}")
            return atom
        if not isinstance(atom, _Callable):
            if self.opaque_fallback and getattr(atom, "is_Symbol", False):
                return sp.Function(str(atom))(*args)
            raise Unsupported(f"applied non-function {atom}")
        return atom.apply(args, self)

    def p_atom_pow(self):
        """An argument atom, allowing a postfix ^ (Lean: `f x^2` = `f (x^2)`?  No —
        Lean parses `f x ^ 2` as `(f x) ^ 2`, so arguments take no exponent here."""
        return self.p_atom()

    def p_atom(self):
        k, v = self.peek()
        if k == "num":
            self.eat()
            return sp.Rational(v) if "." not in v else sp.Rational(v)
        if v == "(":
            self.eat("(")
            e = self.p_cmp()
            # `(x : ℝ)` type ascription
            if self.peek()[1] == ":":
                self.eat(":")
                self.eat()  # the type token
            self.eat(")")
            return e
        if v == "|":
            self.eat("|")
            e = self.p_cmp()
            self.eat("|")
            return sp.Abs(e)
        if k == "ident":
            self.eat()
            return self.resolve(v)
        raise Unsupported(f"unexpected token {v!r}")

    # -- name resolution
    def resolve(self, name: str):
        if name in self.env:
            return self.env[name]
        if name in CONSTS:
            return CONSTS[name]
        short = name.split(".")[-1]
        if name in UNARY or short in UNARY:
            fn = UNARY.get(name) or UNARY[short]
            if fn is None:
                raise Unsupported(f"unsupported function {name}")
            return _Callable(name, 1, lambda a: fn(a[0]))
        if name in BINARY or short in BINARY:
            fn = BINARY.get(name) or BINARY[short]
            return _Callable(name, 2, lambda a: fn(a[0], a[1]))
        if short in self.table:
            return _Def(short, self.table[short])
        if name in self.table:
            return _Def(name, self.table[name])
        # a plain variable
        if re.fullmatch(r"[A-Za-z_" + GREEK + r"][A-Za-z0-9_'₀-₉ₐ-ₜ" + GREEK + r"]*", name):
            return sp.Symbol(name, real=True)
        if self.opaque_fallback and re.fullmatch(r"[A-Za-z_][A-Za-z0-9_'₀-₉]*"
                                                 r"(\.[A-Za-z_][A-Za-z0-9_'₀-₉]*)+",
                                                 name):
            # a structure field access such as `g.Ne`: opaque, but a value
            return sp.Symbol(name.replace(".", "_"), real=True)
        raise Unsupported(f"unresolved name {name}")


class _Callable:
    def __init__(self, name, arity, fn):
        self.name, self.arity, self.fn = name, arity, fn

    def apply(self, args, conv):
        if len(args) != self.arity:
            raise Unsupported(f"{self.name} expects {self.arity} args, got {len(args)}")
        return self.fn(args)


class _Def(_Callable):
    """A user definition: inline its body with binders bound to the arguments."""

    def __init__(self, name, entry):
        self.name = name
        self.binders, self.body = entry
        self.arity = len(self.binders)
        self.fn = None

    def _opaque(self, args):
        return sp.Function(self.name)(*args)

    def apply(self, args, conv):
        if conv.opaque_defs:
            if len(args) != self.arity:
                raise Unsupported(
                    f"{self.name} expects {self.arity} args, got {len(args)}")
            return sp.Function(self.name)(*args)
        def bail(msg):
            if conv.opaque_fallback and self.name not in conv.must_inline:
                return self._opaque(args)
            raise Unsupported(msg)

        if conv.depth >= Converter.MAX_DEPTH:
            return bail(f"inlining depth exceeded at {self.name}")
        if self.name in conv.stack:
            return bail(f"recursive definition {self.name}")
        if len(args) != self.arity:
            return bail(
                f"{self.name} expects {self.arity} args {self.binders}, got {len(args)}")
        env = dict(zip(self.binders, args))
        sub = Converter(conv.table, opaque_fallback=conv.opaque_fallback,
                        must_inline=conv.must_inline)
        try:
            return sub.convert(self.body, env, conv.depth + 1, conv.stack + (self.name,))
        except Unsupported as e:
            return bail(f"{self.name} body unsupported: {e}")


# ---------------------------------------------------------------- table

def build_table(decls) -> dict[str, tuple[list[str], str]]:
    """Bare-name -> (binder names, body text) for real-valued defs.

    Names that are ambiguous across modules are recorded under their fully
    qualified name only, so an inlining never silently picks one of two
    different bodies.
    """
    seen: dict[str, list] = {}
    for d in decls:
        if d["kind"] != "def" or not d["body"]:
            continue
        names = []
        for grp, ty, opener in d["binders"]:
            if opener != "(":
                continue
            if ty.strip() not in ("ℝ", "ℕ", "ℚ"):
                continue
            names.extend(grp)
        seen.setdefault(d["name"], []).append((names, d["body"], d["module"]))
    table = {}
    for name, entries in seen.items():
        bodies = {(tuple(b), body) for b, body, _ in entries}
        if len(bodies) == 1:
            table[name] = (entries[0][0], entries[0][1])
        # ambiguous: leave out; check3 reports these separately
    return table


def simp(e):
    return sp.simplify(sp.together(sp.expand(e)))


def equal(a, b) -> bool | None:
    """True/False if decidable, None if sympy cannot tell."""
    try:
        d = sp.simplify(sp.together(a - b))
        if d == 0:
            return True
        d2 = sp.simplify(sp.radsimp(sp.cancel(sp.expand(d))))
        if d2 == 0:
            return True
        # numeric fallback: random probe on the free symbols
        return _numeric_differs(a, b)
    except Exception:
        return None


def _numeric_differs(a, b, trials=40):
    import random
    syms = sorted(a.free_symbols | b.free_symbols, key=str)
    if not syms:
        try:
            return bool(sp.N(a - b) == 0)
        except Exception:
            return None
    rng = random.Random(20260801)
    seen_ok = 0
    for _ in range(trials):
        sub = {s: sp.Rational(rng.randint(1, 40), rng.randint(1, 17)) / 10 for s in syms}
        try:
            va, vb = complex(sp.N(a.subs(sub))), complex(sp.N(b.subs(sub)))
        except Exception:
            continue
        if any(map(lambda z: z != z or abs(z) == float("inf"), (va, vb))):
            continue
        if abs(va - vb) > 1e-9 * max(1.0, abs(va), abs(vb)):
            return False
        seen_ok += 1
    return True if seen_ok >= 5 else None
