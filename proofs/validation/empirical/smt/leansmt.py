r"""Lean-subset -> z3 translator, built for SOUND vacuity detection.

GUARD=LEANSMT_V4_GNOMON

SOUNDNESS CONTRACT (the whole point):
  Every construct we cannot translate is turned into something STRICTLY MORE
  PERMISSIVE than the Lean original:
    * an unknown function application  f a b   -> an uninterpreted Real fn
    * an unparseable hypothesis                -> DROPPED entirely
    * an unparseable subterm                   -> a fresh unconstrained Real
  Dropping/relaxing hypotheses can only ENLARGE the model set.  Therefore:

      z3 says UNSAT on the hypothesis conjunction
        => the real hypothesis set is also unsatisfiable
        => the theorem is VACUOUS (proves nothing about anything).

  The converse direction (SAT) carries NO information, and we never report it
  as a result.  This asymmetry is what makes the scan trustworthy without a
  verified Lean->SMT translation.

  `Real.sqrt` is modelled as an uninterpreted fn with the *valid* side
  condition sqrt(x) >= 0 (true in Lean's `Real.sqrt` for all inputs, including
  negatives, where it is 0), so adding it preserves soundness.
"""
import re
from z3 import *

GUARD = "LEANSMT_V4_GNOMON"


class Unparseable(Exception):
    pass


# ---------------------------------------------------------------- tokenizer
TOKEN_RE = re.compile(r"""
    (?P<ws>\s+)
  | (?P<num>\d+(\.\d+)?)
  | (?P<ident>[A-Za-z_][A-Za-z0-9_'!?.₀-₉]*)
  | (?P<op>≤|≥|≠|<|>|=|\+|-|\*|/|\^|\(|\)|\||∧|∨|¬|,)
""", re.X)


def tokenize(s):
    toks, i = [], 0
    while i < len(s):
        m = TOKEN_RE.match(s, i)
        if not m:
            raise Unparseable(f"bad char {s[i]!r}")
        i = m.end()
        if m.lastgroup == "ws":
            continue
        toks.append(m.group())
    return toks


COMPARE = {"≤", "≥", "<", ">", "=", "≠"}


class Parser:
    """Pratt parser for the arithmetic/comparison fragment of Lean."""

    def __init__(self, toks, env):
        self.t = toks
        self.i = 0
        self.env = env          # name -> z3 Real  (bound variables)
        self.fresh = 0

    def peek(self):
        return self.t[self.i] if self.i < len(self.t) else None

    def next(self):
        tok = self.peek()
        if tok is None:
            raise Unparseable("eof")
        self.i += 1
        return tok

    def expect(self, tok):
        if self.next() != tok:
            raise Unparseable(f"expected {tok}")

    # --- propositions -----------------------------------------------------
    def prop(self):
        lhs = self.prop_atom()
        while self.peek() in ("∧", "∨"):
            op = self.next()
            rhs = self.prop_atom()
            lhs = And(lhs, rhs) if op == "∧" else Or(lhs, rhs)
        return lhs

    def prop_atom(self):
        if self.peek() == "¬":
            self.next()
            return Not(self.prop_atom())
        # a parenthesised proposition, or an arithmetic comparison
        save = self.i
        if self.peek() == "(":
            try:
                self.next()
                p = self.prop()
                self.expect(")")
                return p
            except Unparseable:
                self.i = save
        a = self.expr()
        op = self.peek()
        if op not in COMPARE:
            raise Unparseable(f"not a comparison at {op!r}")
        self.next()
        b = self.expr()
        return {"≤": lambda: a <= b, "≥": lambda: a >= b,
                "<": lambda: a < b, ">": lambda: a > b,
                "=": lambda: a == b, "≠": lambda: a != b}[op]()

    # --- arithmetic -------------------------------------------------------
    def expr(self):
        return self.additive()

    def additive(self):
        lhs = self.multiplicative()
        while self.peek() in ("+", "-"):
            op = self.next()
            rhs = self.multiplicative()
            lhs = lhs + rhs if op == "+" else lhs - rhs
        return lhs

    def multiplicative(self):
        lhs = self.power()
        while self.peek() in ("*", "/"):
            op = self.next()
            rhs = self.power()
            lhs = lhs * rhs if op == "*" else lhs / rhs
        return lhs

    def power(self):
        base = self.unary()
        if self.peek() == "^":
            self.next()
            e = self.unary()
            # only literal integer exponents are safe to expand
            if is_int_value(e) or (is_rational_value(e) and e.denominator_as_long() == 1):
                n = e.as_long() if is_int_value(e) else e.numerator_as_long()
                if 0 <= n <= 8:
                    out = RealVal(1)
                    for _ in range(n):
                        out = out * base
                    return out
            raise Unparseable("non-literal exponent")
        return base

    def unary(self):
        if self.peek() == "-":
            self.next()
            return -self.unary()
        return self.application()

    def application(self):
        head = self.atom()
        # juxtaposition = application; only meaningful when head is a symbol
        args = []
        while True:
            nxt = self.peek()
            if nxt is None or nxt in COMPARE or nxt in (
                    "+", "-", "*", "/", "^", ")", "∧", "∨", ",", "|"):
                break
            args.append(self.atom())
        if not args:
            return head if not isinstance(head, str) else self.var(head)
        if not isinstance(head, str):
            raise Unparseable("application of non-symbol")
        return self.uninterpreted(head, args)

    def atom(self):
        tok = self.next()
        if tok == "(":
            e = self.expr()
            self.expect(")")
            return e
        if tok == "|":
            e = self.expr()
            self.expect("|")
            return If(e >= 0, e, -e)
        if re.fullmatch(r"\d+(\.\d+)?", tok):
            return RealVal(tok)
        if re.fullmatch(r"[A-Za-z_][A-Za-z0-9_'!?.₀-₉]*", tok):
            return tok          # symbol: caller decides var vs application head
        raise Unparseable(f"atom {tok!r}")

    def var(self, name):
        if name in self.env:
            return self.env[name]
        # An unbound bare symbol is a nullary constant of unknown value:
        # a fresh unconstrained Real is the correct over-approximation.
        v = Real(f"_free_{name}")
        self.env[name] = v
        return v

    def uninterpreted(self, head, args):
        args = [a if not isinstance(a, str) else self.var(a) for a in args]
        key = (head, len(args))
        fn = UNINTERP.get(key)
        if fn is None:
            fn = Function(f"{head}_{len(args)}".replace(".", "_"),
                          *([RealSort()] * (len(args) + 1)))
            UNINTERP[key] = fn
        t = fn(*args)
        if head in ("Real.sqrt",):
            SQRT_FACTS.append(t >= 0)      # valid in Lean for ALL inputs
        return t


UNINTERP = {}
SQRT_FACTS = []


def parse_prop(text, env):
    """Parse one Lean proposition. Raises Unparseable on anything unsupported."""
    # reject constructs we deliberately do not model
    if re.search(r"(∀|∃|→|↔|Real\.log|Real\.exp|Real\.pi|Set|Finset|fun\b|"
                 r"if\b|match\b|let\b|Matrix|Polynomial|∑|∏|∫)", text):
        raise Unparseable("unsupported construct")
    p = Parser(tokenize(text), env)
    out = p.prop()
    if p.peek() is not None:
        raise Unparseable(f"trailing {p.peek()!r}")
    return out
