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
  | (?P<proj>\.[A-Za-z_][A-Za-z0-9_'₀-₉]*|\.[0-9]+)
  | (?P<op>⁻¹|<=|>=|!=|:=|=>|<\||\|>|\.\.|[-+*/%^()\[\]{},:;<>=|↦→←≤≥≠∧∨¬⁻¹↑√⌊⌋‖∑∏∫∘⟨⟩·×∙∈∉⊆∩∪ℝℕℤ∞πΦ⁻¹])
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
    "∀": "universal quantifier", "∃": "existential quantifier",
    "!": "Matrix/vector literal (![…])",
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

class Parser:
    def __init__(self, toks, struct_args, locals_=(), resolver=None,
                 struct_types=None, fields_of=None, dot_resolver=None,
                 vector_args=None, dims=None, lift_arith=False):
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
        # Only definitions that actually take a vector need elementwise
        # arithmetic.  Scalar-only definitions keep plain Python operators, so
        # their generated source is unchanged by this feature.
        self.lift_arith = lift_arith

    def _dot(self, x, nargs):
        """Resolve `base.method` now that its application arity is known.

        Lean's dot notation means `m.foo a` = `T.foo m a` when `m : T`.  Treating
        it as a field access silently turns a method call into a KeyError, or
        worse, into a projection that happens to exist.
        """
        if not isinstance(x, str) or not x.startswith("_DOT:"):
            return x
        base, ty, meth = x[5:].split("|")
        if self.dot_resolver is None:
            raise Untranslatable(f"dot-notation call {ty}.{meth}")
        return self.dot_resolver(ty, meth, nargs), pyname(base)

    def _dep(self, x, nargs):
        """Resolve a `_DEP:` marker now that its application arity is known."""
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
        return f"{self._dep(head, len(args))}({', '.join(args)})"

    def atom(self):
        p = self.peek()
        if p is None:
            raise Untranslatable("unexpected end of body")
        if p.text in HARD_STOP:
            raise Untranslatable(HARD_STOP[p.text])
        if p.text == "∑":
            self.next()
            if self.peek() is None or self.peek().kind != "ident":
                raise Untranslatable("∑ without a simple index binder")
            idx = self.next().text
            dimexpr = None
            if self.at(":"):                       # ∑ i : Fin t, …
                self.next()
                toks = []
                while self.peek() and self.peek().text != ",":
                    toks.append(self.next().text)
                if len(toks) >= 2 and toks[0] == "Fin":
                    dimexpr = self.dims.get(toks[1]) or (
                        toks[1] if toks[1].isdigit() else None)
                if dimexpr is None:
                    raise Untranslatable(
                        f"∑ over {' '.join(toks)}: not a `Fin n` index set")
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
                if len(cand) != 1:
                    raise Untranslatable(
                        "∑ with an unannotated index and "
                        f"{len(cand)} candidate dimensions: cannot tell which")
                dimexpr = self.dims.get(next(iter(cand)))
            if dimexpr is None:
                raise Untranslatable("∑ over a dimension with no runtime length")
            self.expect(",")
            self.locals.add(idx)
            self.sum_vars.append(idx)
            body = self.expr()
            self.sum_vars.pop()
            self.locals.discard(idx)
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
            if name in CONSTS:
                return CONSTS[name]
            if name in FUNCS:
                fn, ar = FUNCS[name]
                return f"_FN:{fn}|{ar}"
            if "." in name:                     # projection or qualified name
                base, *flds = name.split(".")
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
                raise Untranslatable(f"qualified name {name}")
            if name in self.vector_args:
                dim, rank = self.vector_args[name]
                return f"_VEC:{name}|{dim}|{rank}"
            if name in self.locals:
                return pyname(name)
            return f"_DEP:{name}"
        raise Untranslatable(f"unsupported token {p.text!r}")

    def let_tail(self):
        raise Untranslatable("internal: let handled at statement level")


# ------------------------------------------------------------- entry point

LET_RE = re.compile(r"^(\s*)let\s+([A-Za-z_][\w'₀-₉ₐ-ₜ]*)\s*(?::[^:=]*)?:=\s*(.*)$")


def translate_body(body: str, struct_args=(), locals_=(), resolver=None,
                   struct_types=None, fields_of=None, dot_resolver=None,
                 vector_args=None, dims=None, lift_arith=False):
    """Translate a Lean body into (statements, return_expression)."""
    toks = tokenize(body)
    if not toks:
        raise Untranslatable("empty body")
    stmts = []
    p = Parser(toks, set(struct_args), locals_, resolver,
               struct_types, fields_of, dot_resolver, vector_args, dims,
               lift_arith)
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


def translate_def(d, struct_arg_names=(), fname=None, resolver=None,
                  struct_types=None, fields_of=None, dot_resolver=None,
                 vector_args=None, dims=None, lift_arith=False):
    """Return (python_source, argnames) or raise Untranslatable.

    `resolver(short, n_args) -> python_name` decides which definition an
    unqualified call refers to.  Lean resolves such a call by namespace and by
    type; we approximate with file/namespace locality plus arity, and REFUSE
    rather than pick when that is not decisive -- a silently wrong pick produces
    a callable that computes a different function than the Lean says.
    """
    if d.get("equations"):
        return translate_recursion(d, struct_arg_names, fname, resolver)
    argnames = [pyname(n) for a in d["args"] if not a["implicit"] for n in a["names"]]
    if not argnames and not d["body"].strip():
        raise Untranslatable("no explicit arguments and no body")
    binders = [n for a in d["args"] for n in a["names"]]      # incl. implicit
    stmts, ret = translate_body(d["body"], struct_arg_names, binders, resolver,
                                struct_types, fields_of, dot_resolver,
                                vector_args, dims, bool(vector_args))
    lines = [f"def {fname or pyname(d['short'])}({', '.join(argnames)}):"]
    # BUG A fix: a dimension variable is an IMPLICIT binder, so it is correctly
    # absent from the signature -- but the body may still use it (`(T : ℝ) / ∑ i,
    # …`).  Bind each referenced dimension to the length of the argument that
    # carries it, before any other statement.
    for dimvar, lenexpr in (dims or {}).items():
        if re.search(rf"(?<![\w']){re.escape(dimvar)}(?![\w'])", d["body"]):
            lines.append(f"    {pyname(dimvar)} = float({lenexpr})")
    for s in stmts:
        lines.append(f"    {s}")
    lines.append(f"    return {ret}")
    return "\n".join(lines), argnames
