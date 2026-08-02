"""Admissible input boxes, derived from the corpus rather than assumed.

The box for a definition's arguments comes, in priority order, from
  1. hypotheses of theorems that mention the definition (`0 < Ne`, `p < 1`, ...),
     as mined by `lean_parse.py`;
  2. the declared kind of the quantity (probability, frequency, F_ST, ...)
     inferred from the argument name;
  3. a conservative default.

A box is what makes a check falsifiable: it is the set of inputs over which an
invariant is asserted, so a wrong body can be caught by exhibiting a point in it.
"""
from __future__ import annotations

import random
import re

# Names that carry a unit-interval convention throughout this corpus.  Matched
# as a substring, because the corpus writes `h2_true`, `avg_r2_tag`, `fstTarget`.
UNIT_NAMES = re.compile(
    r"(^p$|^q$|^p[₀-₉0-9']?$|^q[₀-₉0-9']?$|freq|prob|prevalence|fst|"
    r"\br2\b|r2|h2|heritab|rg\b|ratio|rate|fraction|share|proportion|"
    r"correlation|sens|spec|auc|power|accuracy|coverage|retention|portab)", re.I)
COUNT_NAMES = re.compile(r"^(n|N|m|Ne|N₀|N₁|nEff|nSource|nTarget|\w*Size|\w*Count|"
                         r"\w*Samples?|t|gen\w*|generations?)$")

# (lo, hi, open_lo, open_hi)
DEFAULT_BOX = (0.05, 3.0)


def _num(tok):
    try:
        return float(eval(tok, {"__builtins__": {}}))       # numeric literal only
    except Exception:
        return None


HYP_RE = re.compile(r"^\s*(-?[\d./]+|\w[\w'₀-₉]*)\s*(<|≤|>|≥)\s*(-?[\d./]+|\w[\w'₀-₉]*)\s*$")


def box_for(d):
    """Return {argname: (lo, hi)} for the explicit real arguments of a def."""
    args = [n for a in d["args"] if not a["implicit"] and a["type"] in ("ℝ", "ℕ")
            for n in a["names"]]
    nat = {n for a in d["args"] if a["type"] == "ℕ" for n in a["names"]}
    box = {}
    for n in args:
        if n in nat:
            box[n] = (1.0, 20.0)
        elif UNIT_NAMES.match(n):
            box[n] = (0.02, 0.98)
        elif COUNT_NAMES.match(n):
            box[n] = (1.0, 1000.0)
        else:
            box[n] = DEFAULT_BOX

    for h in d.get("constraints", {}).get("hypotheses", []):
        m = HYP_RE.match(h)
        if not m:
            continue
        a, op, b = m.groups()
        va, vb = _num(a), _num(b)
        if vb is None and va is not None and b in box:          # c < x
            lo, hi = box[b]
            box[b] = (max(lo, va + (1e-3 if op in "<" else 0.0)), hi)
        elif va is None and vb is not None and a in box:        # x < c
            lo, hi = box[a]
            box[a] = (lo, min(hi, vb - (1e-3 if op in "<" else 0.0)))
    # repair degenerate boxes
    for n, (lo, hi) in box.items():
        if not (hi > lo):
            box[n] = (lo, lo + 1.0)
    return box


def hypothesis_predicates(d, theorem=None):
    """Mined theorem hypotheses, compiled into Python predicates over the args.

    `theorem` selects ONE theorem's preconditions, which is almost always what
    you want: a check tests a particular theorem's claim, so it must be run
    under that theorem's hypotheses.  With `theorem=None` you get the union over
    every theorem mentioning the definition, which is NOT a domain -- read
    conjunctively it excludes points the corpus considers perfectly admissible
    (`coalFst` picks up `100 * Ne < t` from one asymptotic lemma).
    """
    import translate
    preds, texts, dropped = [], [], []
    if theorem is not None:
        src_hyps = d.get("constraints", {}).get(
            "hypotheses_by_theorem", {}).get(theorem, [])
    else:
        src_hyps = d.get("constraints", {}).get("hypotheses", [])
    argnames = {translate.pyname(n) for a in d["args"] for n in a["names"]}
    for h in src_hyps:
        try:
            stmts, ret = translate.translate_body(h)
        except Exception:                                        # noqa: BLE001
            dropped.append(h)
            continue
        if stmts:
            dropped.append(h)
            continue
        src = "\n".join(stmts + [f"__r = {ret}"])
        used = set(re.findall(r"[A-Za-z_][A-Za-z0-9_]*", ret)) - {"_rt"}
        if not used or not used <= argnames:
            dropped.append(h)          # constrains something we do not model
            continue
        try:
            code = compile(src, "<hyp>", "exec")
        except SyntaxError:
            dropped.append(h)
            continue
        preds.append(code)
        texts.append(h)
    return preds, texts, dropped


def satisfies(preds, pt):
    import lean_rt as _rt
    for code in preds:
        ns = dict(pt)
        ns["_rt"] = _rt
        try:
            exec(code, {"__builtins__": {}}, ns)
        except Exception:                                        # noqa: BLE001
            return False
        if ns.get("__r") is not True:
            return False
    return True


def sample(box, rng: random.Random):
    return {n: rng.uniform(lo, hi) for n, (lo, hi) in box.items()}


def corners(box, limit=32):
    """Deterministic corner + midpoint points of the box."""
    names = list(box)
    pts = [{n: (box[n][0] + box[n][1]) / 2 for n in names}]
    for k in range(min(limit, 1 << max(len(names), 1))):
        pt = {}
        for j, n in enumerate(names):
            lo, hi = box[n]
            eps = (hi - lo) * 1e-6
            pt[n] = lo + eps if (k >> j) & 1 else hi - eps
        pts.append(pt)
    return pts


def declared_range(d):
    """Bounds on the definition's value, each with its own provenance.

    A bound proved by a theorem is authoritative; a bound merely implied by the
    docstring or by the quantity's name is a conjecture.  They must never be
    conflated: a violated conjecture is a lead, a violated theorem is a defect.
    """
    c = d.get("constraints", {})
    kind = c.get("declared_kind")
    if "range_lo" in c:
        lo, src_lo = c["range_lo"], "theorem"
    else:
        lo, src_lo = c.get("declared_lo"), ("docstring/name" if kind else None)
    if "range_hi" in c:
        hi, src_hi = c["range_hi"], "theorem"
    else:
        hi, src_hi = c.get("declared_hi"), ("docstring/name" if kind else None)
    return lo, hi, kind, src_lo, src_hi


# ------------------------------------------------------------ structures

FIELD_HYP = re.compile(r"^\s*(-?[\d./]+|\w[\w'\u2080-\u2089]*)\s*(<|\u2264|>|\u2265)"
                       r"\s*(-?[\d./]+|\w[\w'\u2080-\u2089]*)\s*$")


# ------------------------------------------- shape-directed inhabitants
#
# WHY THIS EXISTS.  A definition is classified NOT-EXTRACTABLE when it cannot be
# evaluated at a single admissible point.  Before this, "an admissible point"
# was built by matching argument and field types as TEXT: `ℝ`/`ℕ` got a float,
# a type whose first word named a structure got a dict, a type whose text ended
# in `→ ℝ` got a lambda, and everything else got nothing at all.  That is wrong
# in three ways at once, and each way was visible in the failure histogram:
#
#   * `Pop → Matrix (Fin p) (Fin q) ℝ` begins with `Pop`, an inductive, so the
#     field was given a *dict* and `m.directCausal P` raised "'dict' object is
#     not callable" -- 16 definitions;
#   * a field with no inhabitant at all raised KeyError on projection -- 14;
#   * a `Fin m → ℝ` field became a lambda with no length, so `∑ j, s.weight j`
#     had no dimension to range over -- a large share of the 37 unannotated-∑
#     refusals;
#   * an argument of a function type that was not literally `Fin n → ℝ` got the
#     scalar default 1.0, and applying it raised "'float' object is not
#     callable" -- 5 more, plus the "value is not a real number: function" band.
#
# In total 194 of the 376 NOT-EXTRACTABLE definitions took a structure argument
# with at least one field this could not inhabit.  Those definitions were
# TRANSLATED CORRECTLY and then failed on an argument value the harness built
# wrong; the coverage number was measuring the harness, not the corpus.
#
# `type_value` replaces the text matching with a reading of the type's SHAPE,
# and -- this is the part that keeps it safe -- REFUSES by raising
# `Uninhabitable` when the shape is not one it models.  It must never fall back
# to a scalar.  A float standing in for a vector does not make the definition
# fail; it makes it return a plausible wrong number, which is the one outcome
# worse than NOT-EXTRACTABLE.


class Uninhabitable(Exception):
    """No inhabitant of this Lean type is modelled.  Refusing, not guessing."""


SCALAR_TYPES = {"ℝ", "ℕ", "ℤ", "ℚ", "Real", "Nat", "Int",
                "NNReal", "ℝ≥0", "ℝ≥0∞", "ENNReal"}
PROP_TYPES = {"Prop", "Bool"}

# Domains with infinitely many inhabitants.  A function out of one is a genuine
# function and must NOT be given a length: `profile : ℝ → ℝ` is evaluated at
# `F.location j`, a real, not at an index.
CONTINUOUS_DOMAINS = {"ℝ", "ℤ", "ℚ", "Real", "Int", "NNReal", "ℝ≥0", "ℝ≥0∞"}
# `ℕ` is countable, and the corpus indexes `ℕ → ℝ` fields by generation number,
# which is unbounded.  Treat it as continuous: a table would raise IndexError at
# generation 30 and misreport a working definition as broken.
CONTINUOUS_DOMAINS.add("ℕ")


def _norm(ty):
    ty = " ".join(str(ty).split())
    while ty.startswith("(") and _matching(ty, 0) == len(ty) - 1:
        ty = " ".join(ty[1:-1].split())
    return ty


def _matching(s, i):
    depth = 0
    for j in range(i, len(s)):
        if s[j] == "(":
            depth += 1
        elif s[j] == ")":
            depth -= 1
            if depth == 0:
                return j
    return -1


def _split_arrow(ty):
    """Split at the FIRST top-level `→`, or return None."""
    depth = 0
    for j, ch in enumerate(ty):
        if ch in "([{":
            depth += 1
        elif ch in ")]}":
            depth -= 1
        elif ch == "→" and depth == 0:
            return _norm(ty[:j]), _norm(ty[j + 1:])
    return None


_ENUM_CACHE = {}


def enum_cards(structs):
    """{inductive name: number of constructors} for the corpus's enumerations.

    `Pop` (`| source | target`) and `DiploidGenotype` (`| homRef | het |
    homAlt`) are index types: the corpus writes `Pop → Fin q → ℝ` for "the
    effect vector in each population" and `∑ g : DiploidGenotype, …` for a sum
    over genotype states.  Modelling them as finite index sets is what lets a
    `Pop`-indexed field be inhabited at all.  Only constructor-only inductives
    qualify -- one carrying arguments is not an index set.
    """
    key = id(structs)
    if key in _ENUM_CACHE:
        return _ENUM_CACHE[key]
    out = {}
    for name, s in (structs or {}).items():
        if s.get("kind") != "inductive":
            continue
        ctors = [ln.strip()[1:].strip() for ln in s.get("body", "").splitlines()
                 if ln.strip().startswith("|")]
        if ctors and all(c and " " not in c.split("--")[0].strip() for c in ctors):
            out[name] = len(ctors)
            out[name.split(".")[-1]] = len(ctors)
    _ENUM_CACHE[key] = out
    return out


def type_value(ty, rng, structs=None, dim=None, lo=0.05, hi=1.0, _depth=0):
    """An inhabitant of the Lean type `ty`, or raise `Uninhabitable`.

    `dim` is the size used for every finite index type whose cardinality is not
    fixed by the type itself (`Fin n` for a symbolic `n`, an abstract `ι`).  A
    fixed cardinality -- an enumeration's constructor count -- always wins over
    it, so a `Pop`-indexed table has exactly 2 entries and reading entry 2 of it
    raises instead of returning a fabricated third population.
    """
    if dim is None:
        dim = VECTOR_DIM
    ty = _norm(ty)
    if _depth > 5:
        raise Uninhabitable(f"type nests deeper than 5 levels: {ty!r}")
    if not ty:
        raise Uninhabitable("empty type")
    if ty in SCALAR_TYPES:
        return rng.uniform(lo, hi)
    if ty in PROP_TYPES:
        return True                     # a structure invariant, not a value
    import lean_rt as _rt

    arrow = _split_arrow(ty)
    if arrow is not None:
        dom, cod = arrow
        n = _index_card(dom, structs, dim)
        if n is None:                   # infinite domain: a genuine function
            if _norm(cod) not in SCALAR_TYPES:
                raise Uninhabitable(
                    f"function out of the infinite domain {dom!r} into the "
                    f"non-scalar {cod!r}: no finite table represents it")
            a, b = rng.uniform(lo, hi), rng.uniform(lo, hi)
            return lambda *xs: a + b / (1.0 + sum(
                x for x in xs if isinstance(x, (int, float))))
        return _rt.VecFn(type_value(cod, rng, structs, dim, lo, hi, _depth + 1)
                         for _ in range(n))

    head = ty.split()[0].split(".")[-1]
    if head == "Matrix":
        # `Matrix I J α`: two index arguments then the entry type.  Only real
        # matrices are modelled; anything else is refused rather than assumed.
        tail = ty.split()[-1]
        if tail not in SCALAR_TYPES:
            raise Uninhabitable(f"matrix over {tail!r}, not a scalar")
        return _rt.VecFn(_rt.VecFn(rng.uniform(lo, hi) for _ in range(dim))
                         for _ in range(dim))
    if head == "Fin":
        return rng.randrange(_index_card(ty, structs, dim) or dim)
    cards = enum_cards(structs)
    if head in cards:
        return rng.randrange(cards[head])       # an enumeration VALUE, an index
    sd = (structs or {}).get(head)
    if sd is not None and sd.get("fields"):
        return struct_value(sd, rng, structs, _depth + 1, dim=dim)
    raise Uninhabitable(f"no inhabitant modelled for the type {ty!r}")


def _index_card(dom, structs, dim):
    """Cardinality to use for a function domain, or None if it is infinite."""
    dom = _norm(dom)
    if dom in CONTINUOUS_DOMAINS:
        return None
    head = dom.split()[0].split(".")[-1] if dom.split() else ""
    if head == "Fin":
        rest = dom.split(None, 1)[1].strip() if " " in dom else ""
        return int(rest) if rest.isdigit() else dim
    cards = enum_cards(structs)
    if head in cards:
        return cards[head]
    if _split_arrow(dom) is not None:
        # `(Fin n → Fin d) → ℝ`: the domain is itself a finite function space.
        # Its cardinality is d^n, which we do not enumerate; a table of `dim`
        # entries is a legitimate finite function on SOME index set, but it is
        # not this one, so refuse rather than pretend.
        raise Uninhabitable(
            f"function whose domain is itself a function space ({dom!r}); its "
            "index set is not enumerated here")
    if re.fullmatch(r"[A-Za-zα-ωΑ-Ωι][\w'₀-₉]*", dom) and dom not in SCALAR_TYPES:
        return dim                      # abstract `Fintype` index (`α`, `ι`, `V`)
    raise Uninhabitable(f"cannot tell whether the domain {dom!r} is finite")


_PROP_MARK = re.compile(r"[∀∃=≤≥<>≠∧∨¬∈]")


def _nondata_field(ty):
    """Is this 'field' actually one of the structure's stated invariants?

    Lean writes them as fields (`weight_nonneg : ∀ j, 0 ≤ weight j`), so they
    arrive here looking like types.  They carry no data, they are enforced
    separately below, and trying to inhabit one would refuse noisily for no
    reason.
    """
    return bool(_PROP_MARK.search(ty))


def arg_types(d):
    """{python argname: Lean type text} for the explicit arguments of a def."""
    import translate
    return {translate.pyname(n): a["type"]
            for a in d["args"] if not a["implicit"] for n in a["names"]}


def struct_value(sdecl, rng, structs=None, _depth=0, dim=None):
    """An admissible inhabitant of a Lean structure, as a dict of its ℝ/ℕ fields.

    The structure's own Prop fields are its stated invariants (`0 < varY`,
    `varCondE ≤ varYhat`); they are enforced here so that the sampled witness is
    actually admissible and a range violation downstream means something.
    """
    props = [f["type"] for f in sdecl["fields"] if f["type"] not in ("\u211d", "\u2115")]
    # EVERY field is inhabited by reading its type's SHAPE (see `type_value`).
    # A field whose type is not modelled is LEFT OUT: projecting it then raises
    # KeyError and the definition stays NOT-EXTRACTABLE with a reason, which is
    # the outcome we want.  It must not get a scalar placeholder -- that would
    # let a body which reads a vector field compute a plausible wrong number.
    val, refused = {}, {}
    for f in sdecl["fields"]:
        if f["name"] in val:
            continue
        if _norm(f["type"]) in PROP_TYPES or FIELD_HYP.match(f["type"]) \
                or _nondata_field(f["type"]):
            continue                     # a proof obligation, not data
        head = f["type"].split()[0].split(".")[-1] if f["type"].split() else ""
        if (structs or {}).get(head) is sdecl:
            continue                     # self-reference: no finite inhabitant
        try:
            val[f["name"]] = type_value(f["type"], rng, structs,
                                        dim=dim, _depth=_depth + 1)
        except (Uninhabitable, RecursionError) as e:
            refused[f["name"]] = str(e) or type(e).__name__
    if refused:
        # Carried, not raised: a definition that never touches the offending
        # field is still perfectly evaluable, and refusing the whole structure
        # would lose it.  A definition that DOES touch it gets a KeyError out
        # of `_proj`, which is the loud failure we want.
        val["__uninhabited__"] = refused
    for _ in range(6):                       # fixed-point repair of the invariants
        changed = False
        for h in props:
            m = FIELD_HYP.match(h)
            if not m:
                continue
            a, op, b = m.groups()
            if a in val and b in val:
                lo, hi = (a, b) if op in ("<", "\u2264") else (b, a)
                if val[lo] > val[hi]:
                    val[lo], val[hi] = val[hi], val[lo]
                    changed = True
            elif b in val and _num(a) is not None and val[b] <= _num(a):
                val[b] = _num(a) + 0.1
                changed = True
            elif a in val and _num(b) is not None and val[a] >= _num(b):
                val[a] = _num(b) - 0.1
                changed = True
        if not changed:
            break
    return val


# ------------------------------------------------------- vector arguments

VECTOR_DIM = 4          # the finite dimension used when evaluating `Fin n` sums


def vector_value(spec, lo, hi, rng, dim=VECTOR_DIM):
    """An inhabitant of `Fin n → ℝ` (rank 1) or a `Fin p × Fin q` matrix (rank 2).

    Entries are drawn from the same admissible interval the scalar arguments
    use, so a range invariant means the same thing for a vector argument as for
    a scalar one.
    """
    if spec["rank"] == 1:
        return [rng.uniform(lo, hi) for _ in range(dim)]
    return [[rng.uniform(lo, hi) for _ in range(dim)] for _ in range(dim)]


def build_args(argnames, pt, structval, vecspec, rng, structs=None,
               argtypes=None):
    """Positional arguments for a generated callable, in signature order.

    `argtypes` ({argname: Lean type text}, from `arg_types(d)`) is what lets an
    argument that is neither a declared vector nor a structure -- `profile : ℝ →
    ℝ`, `freq : α → ℝ`, `P : Pop` -- be given an inhabitant of its actual type
    instead of the scalar 1.0.  Passing 1.0 for a function argument is how
    "'float' object is not callable" became a NOT-EXTRACTABLE verdict on
    definitions that were translated perfectly well.

    Pass it wherever you have the definition row.  Omitting it keeps the old
    scalar-default behaviour, which is wrong but not newly wrong; every caller
    inside this package passes it, so `emit.py`'s self-check and a downstream
    check see the SAME argument values and cannot disagree about whether a
    definition evaluates.
    """
    out = []
    for a in argnames:
        if vecspec and a in vecspec:
            out.append(vector_value(vecspec[a], 0.05, 1.0, rng))
        elif structval and a in structval:
            out.append(struct_value(structval[a], rng, structs))
        elif a in pt:
            out.append(pt[a])           # a sampled scalar, box-constrained
        elif argtypes and a in argtypes:
            # Raises Uninhabitable if the type is not modelled.  Deliberately
            # NOT caught here: the caller records it as the reason the
            # definition could not be evaluated, which is true and specific.
            out.append(type_value(argtypes[a], rng, structs))
        else:
            out.append(1.0)
    return out
