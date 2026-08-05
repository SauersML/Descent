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


def uniquify(argnames):
    """Make a Python parameter list out of names Lean allows to repeat.

    Lean permits several anonymous `_` binders in one signature, and Python does
    not ("duplicate argument '_' in function definition") -- a whole generated
    module fails to import over one such definition.  `_` is anonymous, so no
    body can refer to it and renaming is always safe.  Non-anonymous duplicates
    should not occur; suffix them too rather than emit a module that will not
    parse, since a silent collision would bind the wrong value.
    """
    seen, out = {}, []
    for n in argnames:
        if n in seen:
            seen[n] += 1
            out.append(f"{n}_{seen[n]}" if n != "_" else f"_{seen[n]}")
        else:
            seen[n] = 0
            out.append(n)
    return out


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
  | (?P<proj>\.[A-Za-z_][A-Za-z0-9_'₀-₉]*|\.[0-9]+)
  | (?P<matlit>!!\[)
  | (?P<veclit>!\[)
  | (?P<op>⁻¹|<=|>=|!=|:=|=>|<\||\|>|\.\.|[-+*/%^()\[\]{},:;<>=|↦→←≤≥≠∧∨¬⁻¹↑√⌊⌋‖∑∏∫∘⟨⟩·×∙•∈∉⊆∩∪ℝℕℤ∞πΦ∀∃↔⁻¹!])
  | (?P<other>.)
""", re.X)

BINOPS = {
    "↔": (25, "none", "=="),
    "∨": (30, "left", "or"),
    "∧": (35, "left", "and"),
    "=": (50, "none", "=="), "≠": (50, "none", "!="),
    "<": (50, "none", "<"), ">": (50, "none", ">"),
    "≤": (50, "none", "<="), "≥": (50, "none", ">="),
    "<=": (50, "none", "<="), ">=": (50, "none", ">="),
    "+": (65, "left", "+"), "-": (65, "left", "-"),
    "*": (70, "left", "*"),
    # `a • b` is Mathlib's scalar multiplication. It is `*` for the cases this
    # corpus writes -- a real scaling a real, a vector or a matrix -- and
    # `lift_arith` already routes `*` through `_rt.mul`, which multiplies a
    # scalar into a vector elementwise. Same precedence, because `•` binds like
    # multiplication in Lean too.
    "•": (70, "left", "*"),
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
    # Mathlib's finite linear algebra.  These were NOT missing because they are
    # hard -- `dotProduct` alone was the reported cause on 12 definitions, and
    # each of those blocked everything that called it in turn.  The runtime
    # versions refuse on a shape mismatch rather than zipping to the shorter
    # argument, because in Lean both sides live in one `Fin n` by construction.
    "dotProduct": ("_rt.dotProduct", 2),
    "Matrix.dotProduct": ("_rt.dotProduct", 2),
    "Matrix.mulVec": ("_rt.mulVec", 2), "Matrix.vecMul": ("_rt.vecMul", 2),
    "Matrix.trace": ("_rt.trace", 1),
}

# The same operations written in Lean's dot notation on a matrix-valued binder:
# `B.mulVec v`, `A.trace`.  The base is an ordinary argument, not a structure,
# so the projection path does not apply and the old parser refused it as a
# "qualified name".
MATRIX_METHODS = {
    "mulVec": ("_rt.mulVec", 2), "vecMul": ("_rt.vecMul", 2),
    "trace": ("_rt.trace", 1), "dotProduct": ("_rt.dotProduct", 2),
    "transpose": ("_rt.transpose", 1),
}
CONSTS = {"Real.pi": "_rt.pi", "π": "_rt.pi"}

# tokens whose presence means the body is outside the arithmetic fragment
HARD_STOP = {
    ".card": "Finset cardinality", "∂": "integral / derivative",
    "∏": "indexed product", "∫": "integral",
    "√": "notation √ (use Real.sqrt)", "⌊": "floor", "⌋": "floor",
    "‖": "norm of a vector/matrix", "∘": "function composition",
    "∈": "set membership", "∉": "set membership", "⊆": "set inclusion",
    "∩": "set operation", "∪": "set operation", "×": "product type",
    "⟨": "anonymous constructor", "⟩": "anonymous constructor",
}


# Characters that mean the body lives outside real arithmetic entirely.  Naming
# the mathematics rather than the byte keeps the NOT-EXTRACTABLE reasons
# actionable: "measure-theoretic integral" tells you no translator will help,
# "unrecognised character '∂'" does not.
NONARITH = {
    "∂": "measure-theoretic integral (∫ … ∂μ)",
    "μ": "measure argument", "σ": "sigma-algebra / measure argument",
    "ω": "sample-space argument", "η": "measure-theoretic predictor",
    "β": "vector-valued effect argument",
}


class Tok:
    __slots__ = ("kind", "text", "line", "col", "col_off")

    def __init__(self, kind, text, line, col, col_off=0):
        self.kind, self.text, self.line, self.col = kind, text, line, col
        self.col_off = col_off          # absolute offset in the source string

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
            raise Untranslatable(NONARITH.get(text, f"unrecognised character {text!r}"))
        toks.append(Tok(kind, text, line, col, m.start()))
        col += len(text)
    return toks


# ------------------------------------------------------------------ parser

def _dedup(pairs):
    out = []
    for x in pairs:
        if x not in out:
            out.append(x)
    return out


class Parser:
    def __init__(self, toks, struct_args, locals_=(), resolver=None,
                 struct_types=None, fields_of=None, dot_resolver=None,
                 vector_args=None, dims=None, lift_arith=False,
                 enums=None, qualified_resolver=None):
        self.t = toks
        self.i = 0
        self.stop_cols = []            # layout barriers introduced by `let`
        self.struct_args = struct_args  # names bound to structures/tuples
        self.locals = set(locals_)      # binders: never a cross-definition call
        self.resolver = resolver        # (short, n_args) -> python name, or None
        self.struct_types = struct_types or {}   # arg name -> structure type name
        self.fields_of = fields_of or {}         # structure type -> set of fields
        self.dot_resolver = dot_resolver         # (Type, method, n_args) -> pyname
        self.vector_args = vector_args or {}     # arg name -> (dim var, rank)
        self.dims = dims or {}                   # dim var -> python length expr
        self.sum_vars = []                       # indices bound by an enclosing ∑
        # {type: {constructor: ordinal}} for the corpus's enumerations (`Pop`,
        # `DiploidGenotype`).  The corpus uses them as INDEX SETS -- `Pop → Fin
        # q → ℝ`, `∑ g : DiploidGenotype, …` -- so a constructor is an index
        # and an enum-annotated sum has a known, fixed length.
        self.enums = enums or {}
        self.qualified_resolver = qualified_resolver
        # Every application of an enclosing ∑'s index: {idx: [(head, argpos)]}.
        # `∑ i, freq i` has no type annotation and no `Fin n` argument to read a
        # dimension from, but Lean infers `i`'s type from `freq`'s domain, and
        # so can we: the sum ranges over the length of what it indexes.  All
        # uses are kept, not just the first, so that the generated code can
        # CHECK they agree at runtime instead of trusting one of them.
        self.index_apply = {}
        # Only definitions that actually take a vector need elementwise
        # arithmetic.  Scalar-only definitions keep plain Python operators, so
        # their generated source is unchanged by this feature.
        self.lift_arith = lift_arith

    def _dot(self, x, nargs):
        """Resolve `base.method` now that its application arity is known.

        `_DOT2:` markers are already resolved (a Mathlib matrix method on an
        ordinary binder) and pass straight through as (function, base).

        Lean's dot notation means `m.foo a` = `T.foo m a` when `m : T`.  Treating
        it as a field access silently turns a method call into a KeyError, or
        worse, into a projection that happens to exist.
        """
        if isinstance(x, str) and x.startswith("_DOT2:"):
            fn, base = x[6:].split("|")
            return (fn, base)
        if isinstance(x, str) and x.startswith("_QUAL:"):
            return x[6:]
        if not isinstance(x, str) or not x.startswith("_DOT:"):
            return x
        base, ty, meth = x[5:].split("|")
        if self.dot_resolver is None:
            raise Untranslatable(f"dot-notation call {ty}.{meth}")
        return self.dot_resolver(ty, meth, nargs), pyname(base)

    def _dep(self, x, nargs):
        """Resolve a `_DEP:` marker now that its application arity is known."""
        if isinstance(x, str) and x.startswith("_DOT2:"):
            fn, base = x[6:].split("|")
            return (fn, base)                  # app() emits fn(base, *args)
        if isinstance(x, str) and x.startswith("_QUAL:"):
            return x[6:]
        x = self._dot(x, nargs)
        if isinstance(x, tuple):                 # dot-call with no extra args
            return f"{x[0]}({x[1]})"
        if isinstance(x, str) and x.startswith("_VEC:"):
            return pyname(x[5:].split("|")[0])   # passed whole, not indexed
        if not isinstance(x, str) or not x.startswith("_DEP:"):
            return x
        short = x[5:]
        if self.resolver is None:
            return pyname(short)
        return self.resolver(short, nargs)

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
            elif self.lift_arith and pyop in ("+", "-", "*"):
                fn = {"+": "add", "-": "sub", "*": "mul"}[pyop]
                left = f"_rt.{fn}({left}, {right})"
            else:
                left = f"({left} {pyop} {right})"
        return left

    def unary(self):
        p = self.peek()
        if p is None:
            raise Untranslatable("unexpected end of body")
        if p.text == "-":
            self.next()
            inner = self.unary()
            return f"_rt.neg({inner})" if self.lift_arith else f"(-{inner})"
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
                head = f"_rt.rinv({self._dep(head, 0)})"
                continue
            if p.text == "!":
                # POSTFIX FACTORIAL, `(n)!`. `Nat.factorial` is what `ewensWeight`
                # and `ewensProb` multiply over their blocks, and it is a suffix
                # operator rather than a bracket -- which is why it survived the
                # vector- and matrix-literal work and still read as an
                # unrecognised character.
                self.next()
                head = f"_rt.factorial({self._dep(head, 0)})"
                continue
            if p.kind == "proj":                      # (e).1 / (e).field
                self.next()
                head = f"_rt._proj({self._dep(head, 0)}, {p.text[1:]!r})"
                continue
            if p.kind in ("ident", "num") or p.text in ("(", "-", "↑", "|"):
                args.append(self._dep(self.atom(), 0))
                continue
            break
        if not args:
            if isinstance(head, str) and head.startswith("_VEC:"):
                return pyname(head[5:].split("|")[0])
            return self._dep(head, 0)
        if isinstance(head, str) and head.startswith("_VEC:"):
            name, dim, rank = head[5:].split("|")
            if len(args) != int(rank):
                raise Untranslatable(
                    f"{name}: indexed with {len(args)} of {rank} indices "
                    "(partial application of a vector is not modelled)")
            # A DECLARED vector is also a place a binder's range can be read
            # from, and it was the one place that was not recorded -- so
            # `∀ i, 0 ≤ w i` over a declared `w : Fin n → ℝ` refused for want of
            # a range that was sitting right there in the argument.
            for pos, a in enumerate(args):
                for i in self.sum_vars:
                    if a == pyname(i):
                        self.index_apply.setdefault(i, []).append(
                            (pyname(name), pos))
            idx = "".join(f"[int({a})]" for a in args)
            return f"{pyname(name)}{idx}"
        dot = self._dot(head, len(args))
        if isinstance(dot, tuple):
            fn, base = dot
            return f"{fn}({', '.join([base] + args)})"
        if head.startswith("_FN:"):
            fn, arity = head[4:].split("|")
            arity = int(arity)
            if len(args) != arity:
                raise Untranslatable(f"arity mismatch for {fn}: got {len(args)}")
            return f"{fn}({', '.join(args)})"
        fn = self._dep(head, len(args))
        # A ∑ index applied to something records where its dimension can be
        # read from.  Only a LOCAL head counts: `∑ i, someOtherDef i` applies a
        # function, and `len` of a function is not a dimension -- taking one
        # there would invent a range and hand back a plausible wrong sum.
        if self.sum_vars and not head.startswith("_DEP:"):
            for pos, a in enumerate(args):
                for idx in self.sum_vars:
                    if a == pyname(idx):
                        self.index_apply.setdefault(idx, []).append((fn, pos))
        return f"{fn}({', '.join(args)})"

    def atom(self):
        p = self.peek()
        if p is None:
            raise Untranslatable("unexpected end of body")
        if p.text in HARD_STOP:
            raise Untranslatable(HARD_STOP[p.text])
        if p.kind == "matlit":
            # `!![a, b; c, d]` is Mathlib's MATRIX literal: comma within a row,
            # semicolon between rows. It becomes a `VecFn` of `VecFn`s, which is
            # what `mulVec` and `dotProduct` in the runtime already consume.
            # Lexed before the vector literal because `!![` starts with `![`'s
            # first character and the longer token has to win.
            self.next()
            rows, row = [], []
            if not self.at("]"):
                while True:
                    row.append(self.expr(0))
                    if self.at(","):
                        self.next()
                        continue
                    if self.at(";"):
                        self.next()
                        rows.append(row)
                        row = []
                        continue
                    break
            rows.append(row)
            if not self.at("]"):
                raise Untranslatable("matrix literal with no closing `]`")
            self.next()
            body = ", ".join("_rt.VecFn([" + ", ".join(r) + "])" for r in rows)
            return "_rt.VecFn([" + body + "])"
        if p.kind == "veclit":
            # `![a, b, c]` is Mathlib's vector literal, and it translates: the
            # runtime's `VecFn` is a list that also answers to `v i`, which is
            # exactly what `![…]` is. This used to be refused outright as
            # "Matrix/vector literal", which took 68 definitions with it --
            # every explicit witness vector in the corpus, and those are the
            # objects the witness theorems are ABOUT.
            self.next()
            items = []
            if not self.at("]"):
                while True:
                    items.append(self.expr(0))
                    if self.at(","):
                        self.next()
                        continue
                    break
            if not self.at("]"):
                raise Untranslatable("vector literal with no closing `]`")
            self.next()
            return "_rt.VecFn([" + ", ".join(items) + "])"
        if p.text in ("∀", "∃"):
            return self.bounded_quantifier(p.text)
        if p.text == "∑":
            self.next()
            if self.peek() is None or self.peek().kind != "ident":
                raise Untranslatable("∑ without a simple index binder")
            idx = self.next().text
            dimexpr, annot = None, ""
            if self.at(":"):                       # ∑ i : Fin t, …
                self.next()
                toks = []
                while self.peek() and self.peek().text != ",":
                    toks.append(self.next().text)
                if len(toks) >= 2 and toks[0] == "Fin":
                    dimexpr = self.dims.get(toks[1]) or (
                        toks[1] if toks[1].isdigit() else None)
                elif len(toks) == 1 and toks[0].split(".")[-1] in self.enums:
                    # `∑ g : DiploidGenotype, …`.  The index set is the
                    # enumeration's constructors, so its size is fixed by the
                    # Lean declaration -- read, not assumed.
                    dimexpr = str(len(self.enums[toks[0].split(".")[-1]]))
                annot = " ".join(toks)          # kept for the refusal message
            elif self.at("∈"):                     # ∑ i ∈ Finset.univ, …
                self.next()
                toks = []
                while self.peek() and self.peek().text != ",":
                    toks.append(self.next().text)
                if "".join(toks) not in ("Finset.univ", "Finset.univ()"):
                    raise Untranslatable(
                        f"∑ over the Finset `{' '.join(toks)}`, not `Finset.univ`")
            if dimexpr is None:
                cand = {d for d, _ in self.vector_args.values()}
                if len(cand) == 1:
                    dimexpr = self.dims.get(next(iter(cand)))
            self.expect(",")
            self.locals.add(idx)
            self.sum_vars.append(idx)
            outer_uses = self.index_apply.pop(idx, None)
            body = self.expr()
            uses = self.index_apply.pop(idx, [])
            if outer_uses is not None:
                self.index_apply[idx] = outer_uses
            self.sum_vars.pop()
            self.locals.discard(idx)
            if dimexpr is None:
                # INFERRED FROM USE.  Lean elaborates `∑ i, freq i` by reading
                # `i`'s type off `freq`'s domain; the same information is in the
                # body here.  Every place the index is applied contributes a
                # length, and `_rt.sumdim` RAISES if they disagree, so a wrong
                # inference becomes a loud failure rather than a sum over the
                # wrong range -- which would be a plausible number, and the one
                # outcome worse than refusing.
                if not uses:
                    raise Untranslatable(
                        f"∑ over {annot or 'an unannotated index'} whose index "
                        "is never applied to a local value: there is nothing in "
                        "the body to read a dimension from")
                lens = ", ".join(
                    f"len({h}{'[0]' * pos})" for h, pos in _dedup(uses))
                dimexpr = f"_rt.sumdim({pyname(idx)!r}, {lens})"
            return f"sum(({body}) for {pyname(idx)} in range(int({dimexpr})))"
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
            # A BINDER SHADOWS A CONSTANT.  `π` is Real.pi in most bodies, but
            # `expectedBrierScore (p π : ℝ)` binds it as the PREVALENCE, and
            # this branch used to rewrite it to 3.14159 anyway -- silently, with
            # the arity still correct, so every caller got a number and none got
            # an error.  `expectedBrierScore 0.7 0.3` returned -0.7666 where the
            # Lean body gives 0.37, which is `math.pi*(1-0.7)^2 +
            # (1-math.pi)*0.7^2` exactly.  `self.locals` already holds the
            # definition's own binders (translate_def passes them as `locals_`)
            # and `let`-bound names, and line 555 below already honours it for
            # cross-definition calls; the constant table simply got consulted
            # first.  Found by the metamorphic gate: brierRegretPoint failed the
            # quadratic scaling relation that its Lean body plainly satisfies.
            if name in CONSTS and name not in self.locals:
                return CONSTS[name]
            # Same shadowing rule for FUNCS, one line below where it was needed
            # for CONSTS.  Currently LATENT -- the 37 definitions that bind a
            # table name all bind `π` -- but `max`, `min`, `id` and `trace` are
            # ordinary mathematical binder names, and the failure mode is the
            # one that took 23 definitions silently: a plausible number of the
            # right sign and magnitude, no error, every consumer affected.
            # Closed before it is reached rather than after.
            if name in FUNCS and name not in self.locals:
                fn, ar = FUNCS[name]
                return f"_FN:{fn}|{ar}"
            if "." in name:                     # projection or qualified name
                base, *flds = name.split(".")
                # An enumeration CONSTRUCTOR is a value of a finite index type,
                # and the corpus uses it as an index (`m.beta Pop.target`).  Its
                # ordinal is the honest translation: it is exactly the position
                # the shape-directed inhabitant in admissible.type_value keys on.
                if len(flds) == 1 and base in self.enums \
                        and flds[0] in self.enums[base]:
                    return str(self.enums[base][flds[0]])
                # `B.mulVec v`, `A.trace` -- Lean dot notation on a matrix-valued
                # BINDER.  Not a structure projection and not a qualified name;
                # it is Mathlib's method on a value we already hold.
                if len(flds) == 1 and flds[0] in MATRIX_METHODS \
                        and base not in self.struct_args \
                        and (base in self.locals or base in self.vector_args):
                    return f"_DOT2:{MATRIX_METHODS[flds[0]][0]}|{pyname(base)}"
                if base in self.struct_args or (flds and flds[0].isdigit()):
                    ty = self.struct_types.get(base)
                    known = self.fields_of.get(ty, set())
                    if len(flds) == 1 and ty and flds[0] not in known \
                            and not flds[0].isdigit():
                        # not a field of this structure: Lean dot notation, so
                        # this is the method `ty.flds[0]` applied to `base`
                        return f"_DOT:{base}|{ty}|{flds[0]}"
                    out = pyname(base)
                    for f in flds:
                        out = f"_rt._proj({out}, {f!r})"
                    return out
                # Last resort before refusing: the dotted name may simply BE a
                # definition of this corpus (`Pop.pair`, `TransportedMetrics.
                # calibratedBrier`).  Resolving it is not a guess -- the
                # resolver only answers when exactly one declaration bears that
                # fully-qualified name.
                if self.qualified_resolver is not None:
                    got = self.qualified_resolver(name)
                    if got is not None:
                        return f"_QUAL:{got}"
                raise Untranslatable(f"qualified name {name}")
            if name in self.vector_args:
                dim, rank = self.vector_args[name]
                return f"_VEC:{name}|{dim}|{rank}"
            if name in self.locals:
                return pyname(name)
            return f"_DEP:{name}"
        raise Untranslatable(f"unsupported token {p.text!r}")

    def bounded_quantifier(self, sym):
        """`∀ i, P i` and `∃ i, P i` over a FINITE index set, or refuse.

        Decidable by enumeration exactly when the index set is finite and its
        size is known: an annotation (`Fin n`, an enumeration), or -- as for `∑`
        -- the length of whatever the index is applied to.

        A QUANTIFIER OVER AN INFINITE DOMAIN IS REFUSED, and this is the whole
        safety property of the feature.  `∀ r : ℝ, P r` cannot be settled by
        sampling: checking a hundred points and reporting True would state that
        a universally quantified proposition holds when all that was observed is
        that no counterexample was drawn.  That is a plausible verdict with
        nothing behind it, which is worse than refusing to answer.  So an index
        whose range cannot be pinned to a finite set raises `Untranslatable`,
        and the definition stays NOT-EXTRACTABLE with the reason.
        """
        self.next()
        idxs = []
        while self.peek() is not None and self.peek().kind == "ident":
            idxs.append(self.next().text)
        if not idxs:
            raise Untranslatable(f"{sym} without a simple index binder")
        annot_dim, annot = None, ""
        if self.at(":"):
            self.next()
            toks = []
            while self.peek() and self.peek().text not in (",",):
                toks.append(self.next().text)
            annot = " ".join(toks)
            # EXACTLY `Fin n`, not merely starting with it: the annotation on
            # `∃ x : Fin k → Fin d` also begins with `Fin`, and reading its
            # first two tokens would quantify over `Fin k` -- k integers -- in
            # place of the d^k functions the Lean actually ranges over.
            if len(toks) == 2 and toks[0] == "Fin":
                annot_dim = self.dims.get(toks[1]) or (
                    toks[1] if toks[1].isdigit() else None)
            elif len(toks) == 1 and toks[0].split(".")[-1] in self.enums:
                annot_dim = str(len(self.enums[toks[0].split(".")[-1]]))
            elif len(toks) == 1 and toks[0] in ("ℝ", "ℕ", "ℤ", "ℚ"):
                raise Untranslatable(
                    f"{sym} over the infinite domain {annot!r}: sampling it "
                    "would report a verdict no finite check can support")
            if annot_dim is None and len(toks) == 2 and toks[0] == "Fin":
                # `∀ i : Fin n` where `n` is an implicit binder no argument
                # pins down.  `Fin n` IS a finite index set -- we simply do not
                # know its size from the annotation -- so falling through to
                # the use-inference below (the length of whatever the index is
                # applied to) is sound, and is what `∑` already does.  This is
                # NOT the function-space or infinite-domain case: those stay
                # refusals, because there no finite length exists at all.
                pass
            elif annot_dim is None:
                # THE ANNOTATION IS AUTHORITATIVE.  If it is present and names
                # something we cannot enumerate, REFUSE -- do not fall through
                # to the range-inference below.  `∀ x : ι → ℝ, 0 ≤ quadForm A x`
                # quantifies over every real vector; falling back to "the length
                # of the one declared vector argument" would enumerate FOUR
                # vectors and report True, which states positive-semidefiniteness
                # on the strength of four samples.  A predicate handed an
                # invalid inhabitant looks decisive while testing nothing, and
                # that is worse than leaving the definition unreached.
                raise Untranslatable(
                    f"{sym} over {annot!r}: "
                    + ("a function space, which has no finite enumeration"
                       if "→" in annot else
                       "not a finite index set this translator can enumerate"))
        if annot_dim is None:
            cand = {dv for dv, _ in self.vector_args.values()}
            if len(cand) == 1:
                annot_dim = self.dims.get(next(iter(cand)))
        self.expect(",")
        saved = {i: self.index_apply.pop(i, None) for i in idxs}
        for i in idxs:
            self.locals.add(i)
        self.sum_vars.extend(idxs)
        body = self.expr()
        uses = {i: self.index_apply.pop(i, []) for i in idxs}
        for i in idxs:
            self.sum_vars.remove(i)
            self.locals.discard(i)
            if saved[i] is not None:
                self.index_apply[i] = saved[i]
        agg = "all" if sym == "∀" else "any"
        out = f"({body})"
        for i in reversed(idxs):
            rng = annot_dim
            if rng is None:
                if not uses[i]:
                    raise Untranslatable(
                        f"{sym} over {annot or 'an unannotated index'} whose "
                        f"index {i!r} is never applied to a local value: its "
                        "range is unknown, and a quantifier with an unknown "
                        "range cannot be decided by enumeration")
                lens = ", ".join(f"len({h}{'[0]' * pos})"
                                 for h, pos in _dedup(uses[i]))
                rng = f"_rt.sumdim({pyname(i)!r}, {lens})"
            out = f"{agg}({out} for {pyname(i)} in range(int({rng})))"
        return out

    def let_tail(self):
        raise Untranslatable("internal: let handled at statement level")


# ------------------------------------------------------------- entry point

LET_RE = re.compile(r"^(\s*)let\s+([A-Za-z_][\w'₀-₉ₐ-ₜ]*)\s*(?::[^:=]*)?:=\s*(.*)$")


def translate_body(body: str, struct_args=(), locals_=(), resolver=None,
                   struct_types=None, fields_of=None, dot_resolver=None,
                   vector_args=None, dims=None, lift_arith=False,
                   enums=None, qualified_resolver=None):
    """Translate a Lean body into (statements, return_expression)."""
    toks = tokenize(body)
    if not toks:
        raise Untranslatable("empty body")
    stmts = []
    p = Parser(toks, set(struct_args), locals_, resolver,
               struct_types, fields_of, dot_resolver, vector_args, dims,
               lift_arith, enums, qualified_resolver)
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
        stmts.append(f"{pyname(name_tok.text)} = {p._dep(val, 0)}")
        p.locals.add(name_tok.text)          # let-bound: shadows any definition
        if p.at(";"):
            p.next()
    ret = p._dep(p.expr(), 0)
    if p.peek() is not None:
        raise Untranslatable(f"trailing tokens after expression: {p.peek()!r}")
    return stmts, ret


def _enum_of(patterns, enums):
    """The enumeration whose constructors are exactly these patterns, or None."""
    if not patterns:
        return None
    for ty, ctors in enums.items():
        got = []
        for pat in patterns:
            base, _, ctor = pat.rpartition(".")
            # `continue to the next enum`, NOT `return None`: `enums` holds each
            # enumeration twice, under its short and its fully-qualified name,
            # so the first key tried is often `Descent.Pop` while the pattern
            # says `Pop.source`.  Bailing out on that mismatch rejected every
            # enum-defined function in the corpus.
            if (base and base.split(".")[-1] != ty.split(".")[-1]) \
                    or ctor not in ctors:
                got = None
                break
            got.append(ctors[ctor])
        if got is not None and sorted(got) == list(range(len(ctors))):
            return ty
    return None


def translate_enum_match(d, enums, struct_arg_names=(), fname=None,
                         resolver=None, **kw):
    """A def defined by cases on an enumeration becomes a dispatch table.

        def Pop.pair (s t : α) : Pop → α
          | Pop.source => s
          | Pop.target => t

    The enumeration is an index type here (see `Parser.enums`), so the branches
    are just the entries of a table read at the constructor's ordinal.  Every
    constructor must be covered -- `_enum_of` checks the patterns are exactly
    the constructors, once each -- so there is no default branch to get wrong.
    """
    ty = _enum_of([e["pattern"].strip() for e in d["equations"]], enums)
    ctors = enums[ty]
    explicit = [n for a in d["args"] if not a["implicit"] for n in a["names"]]
    binders = [n for a in d["args"] for n in a["names"]]
    # DO NOT INVENT A SCRUTINEE THE DEFINITION ALREADY HAS.  In the
    # pipe-equation form the matched value is the unnamed final argument and a
    # fresh name is needed for it. In the `match p with` form `p` is a declared
    # parameter, and appending `_e` beside it made the table take FOUR arguments
    # where Lean's `Pop.pair` takes three -- so `Pop.pair 0 x P` supplied three,
    # fell into the partial-application branch, and returned a lambda. Callers
    # then tried to add that lambda to a float: `residualBurden` and the whole
    # cone above it, eighteen definitions, died on "unsupported operand type(s)
    # for +: 'float' and 'function'". Nothing was wrong with any of them.
    scrut_arg = d.get("_scrut_is_arg")
    if scrut_arg and explicit and explicit[-1] == scrut_arg:
        scrut, extra = scrut_arg, []
    else:
        scrut, extra = "_e", None
        while pyname(scrut) in {pyname(n) for n in binders}:
            scrut += "_"
        extra = [pyname(scrut)]
    branches = {}
    for e in d["equations"]:
        _base, _, ctor = e["pattern"].strip().rpartition(".")
        stmts, ret = translate_body(e["rhs"], struct_arg_names, binders,
                                    resolver, enums=enums, **kw)
        if stmts:
            raise Untranslatable("enum branch needs `let`, not supported here")
        branches[ctors[ctor]] = ret
    args = [pyname(n) for n in explicit] + extra
    fn = fname or pyname(d["short"])
    # PARTIAL APPLICATION IS NOT AN ERROR IN LEAN, and this dispatch table is a
    # function like any other.  `Pop.withTarget f t = Pop.pair (f Pop.source) t`
    # supplies two of `pair`'s three arguments and leaves the scrutinee for the
    # caller; a fixed-arity Python def raises TypeError on that and takes every
    # dependent down with it.  Collecting arguments until there are enough is
    # what the Lean means, not a convenience.
    lines = [f"def {fn}(*_a):",
             f"    if len(_a) < {len(args)}:",
             f"        return lambda *_b: {fn}(*(_a + _b))",
             # The trailing comma matters: with one argument `s = _a[:1]`
             # binds a TUPLE, and every branch then computes on a tuple.
             f"    {', '.join(args)}, = _a[:{len(args)}]"
             if len(args) == 1 else
             f"    {', '.join(args)} = _a[:{len(args)}]",
             f"    _t = [{', '.join(branches[i] for i in range(len(ctors)))}]",
             f"    return _t[_rt._ix({pyname(scrut)}, {len(ctors)}, "
             f"{d['short']!r})]"]
    return "\n".join(lines), args


def translate_recursion(d, struct_arg_names=(), fname=None, resolver=None):
    """Compile a two-branch `ℕ`-recursion into an iteration, or refuse.

        def f (a b : ℝ) : ℕ → ℝ
          | 0     => <base>
          | t + 1 => <step mentioning `f a b t` exactly once>

    becomes a loop carrying the previous value.  This is only sound when the
    recursion is a simple iteration: the step may use the recursive value but
    NOT the index `t` itself, and may recurse only on `t`.  Anything else --
    a step that reads `t`, a call on `t - 1` or on different arguments, more
    than two branches -- is refused, because it is a different computation.
    """
    eqs = d.get("equations") or []
    if len(eqs) != 2:
        raise Untranslatable(f"recursion with {len(eqs)} branches, expected 2")
    base_eq = next((e for e in eqs if e["pattern"].strip() in ("0", "Nat.zero")), None)
    step_eq = next((e for e in eqs if e is not base_eq), None)
    if base_eq is None or step_eq is None:
        raise Untranslatable("recursion has no `0` branch")
    m = re.match(r"^([A-Za-z_][\w'₀-₉]*)\s*\+\s*1$", step_eq["pattern"].strip())
    if not m:
        raise Untranslatable(f"step pattern {step_eq['pattern']!r} is not `n + 1`")
    var = m.group(1)

    explicit = [n for a in d["args"] if not a["implicit"] for n in a["names"]]
    short = d["short"]
    toks = tokenize(step_eq["rhs"])
    want = [short] + explicit + [var]
    hits = [i for i in range(len(toks) - len(want) + 1)
            if [t.text for t in toks[i:i + len(want)]] == want]
    # Every occurrence must be the SAME call `f <same args> t`, so they all
    # denote one value; a call on other arguments would be a different function.
    step_src, cut = "", 0
    for i in hits:
        step_src += step_eq["rhs"][cut:toks[i].col_off] + " _prev "
        last = toks[i + len(want) - 1]
        cut = last.col_off + len(last.text)
    step_src += step_eq["rhs"][cut:]

    if not hits:
        # No recursive call: the step is a closed formula in the predecessor
        # index, so this is a case split rather than an iteration.
        if re.search(rf"(?<![\w'])({re.escape(short)})(?![\w'])", step_eq["rhs"]):
            raise Untranslatable("recursive call is not of the expected shape")
        binders0 = [n for a in d["args"] for n in a["names"]] + [var]
        b_stmts, b_ret = translate_body(base_eq["rhs"], struct_arg_names,
                                        binders0, resolver)
        s_stmts, s_ret = translate_body(step_eq["rhs"], struct_arg_names,
                                        binders0, resolver)
        args0 = [pyname(n) for n in explicit] + [pyname(var)]
        out = [f"def {fname or pyname(short)}({', '.join(args0)}):"]
        out += [f"    {st}" for st in b_stmts]
        out.append(f"    if {pyname(var)} == 0:")
        out.append(f"        return {b_ret}")
        out.append(f"    {pyname(var)} = {pyname(var)} - 1     # the `n + 1` pattern")
        out += [f"    {st}" for st in s_stmts]
        out.append(f"    return {s_ret}")
        return "\n".join(out), args0

    if re.search(rf"(?<![\w'])(?:{re.escape(var)})(?![\w'])", step_src):
        raise Untranslatable(
            f"step uses the index {var!r} outside the recursive call; "
            "not a simple iteration")

    binders = [n for a in d["args"] for n in a["names"]] + ["_prev"]
    b_stmts, b_ret = translate_body(base_eq["rhs"], struct_arg_names,
                                    binders, resolver)
    s_stmts, s_ret = translate_body(step_src, struct_arg_names, binders, resolver)
    args = [pyname(n) for n in explicit] + [pyname(var)]
    lines = [f"def {fname or pyname(short)}({', '.join(args)}):"]
    for st in b_stmts:
        lines.append(f"    {st}")
    lines.append(f"    _prev = {b_ret}")
    lines.append(f"    for _ in range(int({pyname(var)})):")
    for st in s_stmts:
        lines.append(f"        {st}")
    lines.append(f"        _prev = {s_ret}")
    lines.append("    return _prev")
    return "\n".join(lines), args


def structure_literal_fields(body: str):
    """[(field, expression_text)] if this body is a structure literal, else None.

    The corpus writes structure values three ways, and the translator refused
    all three -- `{` was an unsupported token, and the brace-less `where` form
    parsed its first field as a whole expression and then reported "trailing
    tokens after expression: op::=".  Together those two messages accounted for
    86 STRUCTURAL definitions.

        { f := e, g := e2 }          brace literal
        { base with f := e }         update literal
        f := e  g := e2              the `where` form, braces omitted

    A field expression is ordinary arithmetic, so once the literal is split each
    field is a body this translator already handles.  The split is done on the
    TOKEN stream, not with a regex: a field expression can itself contain `:=`
    inside a `let`, and it can contain commas inside parentheses, so neither
    delimiter is safe textually.
    """
    src = body.strip()
    base = None
    if src.startswith("{"):
        if not src.endswith("}"):
            return None
        inner = src[1:-1].strip()
        m = re.match(r"^([A-Za-z_][\w'₀-₉.]*)\s+with\s+", inner)
        if m:
            base, inner = m.group(1), inner[m.end():]
    else:
        inner = src
    try:
        toks = tokenize(inner)
    except Untranslatable:
        return None
    starts = []
    depth = 0
    for i, t in enumerate(toks):
        if t.text in ("(", "[", "{"):
            depth += 1
        elif t.text in (")", "]", "}"):
            depth -= 1
        elif (depth == 0 and t.text == ":=" and i >= 1
                and toks[i - 1].kind == "ident"
                and (i == 1 or toks[i - 2].text in (",", ";"))):
            starts.append(i - 1)
    if not starts:
        return None
    out = []
    for j, si in enumerate(starts):
        name = toks[si].text
        lo = toks[si + 2].col_off if si + 2 < len(toks) else len(inner)
        if j + 1 < len(starts):
            end = toks[starts[j + 1]].col_off
            hi = end
        else:
            hi = len(inner)
        expr = inner[lo:hi].strip().rstrip(",").strip()
        if expr:
            out.append((name, expr))
    return (base, out) if out else None


def translate_structure_literal(d, lit, struct_arg_names, fname, kw):
    """A structure literal becomes a function returning a dict of its fields.

    FIELD BY FIELD, AND PARTIAL ON PURPOSE.  A field whose expression this
    translator cannot handle is LEFT OUT of the dict rather than defaulted, so
    that a body which later projects it raises KeyError and the definition is
    judged NOT-EXTRACTABLE for a stated reason.  Substituting a value would make
    a wrong field silently computable, which is the failure this package exists
    to prevent.  The omissions are recorded under `__uninhabited__`, the same
    key `admissible.struct_value` uses, so `lean_rt._proj` reports them the same
    way whether the structure was sampled or computed.
    """
    base, fields = lit
    binders = [n for a in d["args"] for n in a["names"]]
    argnames = uniquify([pyname(n) for a in d["args"] if not a["implicit"]
                         for n in a["names"]])
    parts, refused, pre = [], {}, []
    for name, expr in fields:
        try:
            stmts, ret = translate_body(expr, struct_arg_names, binders, **kw)
        except Untranslatable as e:
            refused[name] = str(e)
            continue
        except Exception as e:                                    # noqa: BLE001
            refused[name] = f"translator error: {e!r}"
            continue
        pre.extend(stmts)
        parts.append(f"{name!r}: {ret}")
    if not parts:
        raise Untranslatable(
            "structure literal: not one field expression could be translated ("
            + "; ".join(f"{k}: {v}" for k, v in list(refused.items())[:3]) + ")")
    if refused:
        parts.append("'__uninhabited__': " + repr(refused))
    lines = [f"def {fname}({', '.join(argnames)}):"]
    for st in pre:
        lines.append(f"    {st}")
    body = "{" + ", ".join(parts) + "}"
    if base is not None:
        # `{ base with f := e }`: start from the base record and override.
        lines.append(f"    _b = dict({pyname(base)})")
        lines.append(f"    _b.update({body})")
        lines.append("    return _b")
    else:
        lines.append(f"    return {body}")
    return "\n".join(lines), argnames


def translate_def(d, struct_arg_names=(), fname=None, resolver=None,
                  struct_types=None, fields_of=None, dot_resolver=None,
                  vector_args=None, dims=None, lift_arith=False,
                  enums=None, qualified_resolver=None):
    """Return (python_source, argnames) or raise Untranslatable.

    `resolver(short, n_args) -> python_name` decides which definition an
    unqualified call refers to.  Lean resolves such a call by namespace and by
    type; we approximate with file/namespace locality plus arity, and REFUSE
    rather than pick when that is not decisive -- a silently wrong pick produces
    a callable that computes a different function than the Lean says.
    """
    # A `match` EXPRESSION BODY is the same object as a pipe-equation body, and
    # the parser only recognised the latter.  `Pop.pair` is written
    #
    #     def Pop.pair (s t : α) (p : Pop) : α :=
    #       match p with
    #       | Pop.source => s
    #       | Pop.target => t
    #
    # which parsed as an expression, choked on the first `|`, and was reported
    # `trailing tokens after expression: op:|`.  Twelve declarations then failed
    # in turn with `calls untranslated definition pair`.  Rewriting the body into
    # equations hands it to the enum-match compiler that already exists, and the
    # scrutinee must be the LAST explicit binder for that compiler's dispatch --
    # which it is here and is checked rather than assumed.
    if not d.get("equations"):
        body = (d.get("body") or "").strip()
        m = re.match(r"match\s+([A-Za-z_][\w'₀-₉]*)\s+with\s+(\|.*)\Z", body, re.S)
        if m:
            scrut, rest = m.group(1), m.group(2)
            explicit = [n for a in d["args"] if not a["implicit"] for n in a["names"]]
            branches = [b.strip() for b in rest.split("|") if b.strip()]
            parsed = []
            for b in branches:
                if "=>" not in b:
                    parsed = []
                    break
                pat, _, rhs = b.partition("=>")
                parsed.append({"pattern": pat.strip(), "rhs": rhs.strip()})
            if parsed and explicit and explicit[-1] == scrut:
                d = dict(d)
                d["equations"] = parsed
                # The scrutinee is a DECLARED PARAMETER here, unlike the
                # pipe-equation form where it is the unnamed final argument.
                # Recording which one it is stops the dispatch compiler from
                # appending a second scrutinee beside it -- see below.
                d["_scrut_is_arg"] = scrut
                d["args"] = [a for a in d["args"]
                             if a["implicit"] or scrut not in a["names"]] + \
                            [a for a in d["args"]
                             if not a["implicit"] and scrut in a["names"]]

    if d.get("equations"):
        pats = [e["pattern"].strip() for e in d.get("equations") or []]
        if enums and _enum_of(pats, enums):
            # `struct_types`, `fields_of` and `dot_resolver` MUST be forwarded.
            # Without them a branch of an enum match sees no structure types, so
            # `ty` is None at the dot-notation test below and every `h.foo`
            # becomes `_proj(h, 'foo')` -- a structure projection -- even when
            # `foo` is a DERIVED definition and not a field. The inhabitant then
            # has no such key and the definition dies with a KeyError at
            # self-check. `HardyWeinbergModel.genotypeProb` reading `h.refFreq`
            # is the case that showed it: `refFreq` is `1 - h.altFreq`, a def,
            # and `fields_of` correctly does not list it.
            return translate_enum_match(d, enums, struct_arg_names, fname,
                                        resolver,
                                        qualified_resolver=qualified_resolver,
                                        struct_types=struct_types,
                                        fields_of=fields_of,
                                        dot_resolver=dot_resolver)
        return translate_recursion(d, struct_arg_names, fname, resolver)
    argnames = uniquify([pyname(n) for a in d["args"] if not a["implicit"]
                         for n in a["names"]])
    if not argnames and not d["body"].strip():
        raise Untranslatable("no explicit arguments and no body")
    lit = structure_literal_fields(d["body"])
    if lit is not None:
        return translate_structure_literal(
            d, lit, struct_arg_names, fname or pyname(d["short"]),
            dict(resolver=resolver, struct_types=struct_types,
                 fields_of=fields_of, dot_resolver=dot_resolver,
                 vector_args=vector_args, dims=dims,
                 lift_arith=bool(vector_args), enums=enums,
                 qualified_resolver=qualified_resolver))
    binders = [n for a in d["args"] for n in a["names"]]      # incl. implicit
    stmts, ret = translate_body(d["body"], struct_arg_names, binders, resolver,
                                struct_types, fields_of, dot_resolver,
                                vector_args, dims, bool(vector_args),
                                enums, qualified_resolver)
    lines = [f"def {fname or pyname(d['short'])}({', '.join(argnames)}):"]
    # BUG A fix: a dimension variable is an IMPLICIT binder, so it is correctly
    # absent from the signature -- but the body may still use it (`(T : ℝ) / ∑ i,
    # …`).  Bind each referenced dimension to the length of the argument that
    # carries it, before any other statement.
    for dimvar, lenexpr in (dims or {}).items():
        # A dimension key is not always a NAME.  `Fin 3 → ℝ` keys on the literal
        # "3", and binding it emitted `3 = float(len(f))`, a SyntaxError that
        # took the whole generated module down with it -- every definition in
        # the corpus became unavailable because one had a fixed dimension.
        # A literal needs no binding: it already denotes itself in the body.
        if not dimvar.isidentifier():
            continue
        if re.search(rf"(?<![\w']){re.escape(dimvar)}(?![\w'])", d["body"]):
            lines.append(f"    {pyname(dimvar)} = float({lenexpr})")
    for s in stmts:
        lines.append(f"    {s}")
    lines.append(f"    return {ret}")
    return "\n".join(lines), argnames
