#!/usr/bin/env python3
"""Import-graph analysis for the proof corpus.

WHAT THIS IS FOR.  Six directories of this corpus were produced by splitting a
monolith, and the split was made by CHAINING: part `n` imports part `n-1`, in
the order the original file happened to be written.  The header of
`Descent/Portability/MetricSpecificPortability/GeneticFrontier.lean` says so in
as many words -- "The parts are a CHAIN: each imports the one before, in the
order the original was written" -- and calls the alternative, "modules that
import only what they use", worth doing and not what the split did.

A chain is conservative for correctness and expensive for everything else.  It
makes the import DAG as deep as the monolith was long: at the time this file was
written the root sat at depth 39 and `Descent.Program` at 38, almost all of it
chain.  Depth is not cosmetic.  Lean elaborates a module only after every
transitive import is elaborated, so a chain of length `k` is `k` sequential
build steps that cannot overlap no matter how many cores the build has; and a
one-line edit to the head of a chain invalidates every link below it.

WHAT IT COMPUTES.  For each module, the set of `Descent.*` modules its BODY
actually needs, by:

  1.  building a symbol table of every declaration in the corpus, fully
      qualified, from the `namespace` stack in force where it is declared --
      including structure/class projections and inductive constructors, which
      are referenced by names that appear nowhere as a declaration keyword;

  2.  tokenising each module's code (comments, docstrings and string literals
      removed) into dotted identifiers, and resolving each one the way Lean
      does: against the enclosing namespaces innermost-first, then against the
      `open`ed namespaces, then as an absolute name;

  3.  reducing the resulting module set to its ⊆-minimal antichain under the
      import order -- if `A` already imports `B`, naming `B` too is noise.

WHAT IT DELIBERATELY WILL NOT DO.  A name reference is not the only reason an
import can be load-bearing.  An import can also carry

    an INSTANCE, found by typeclass resolution and named nowhere;
    a `@[simp]` (or `@[ext]`, `@[norm_cast]`, ...) lemma that a `simp` call in
      the importing module closes a goal with, named nowhere;
    an `attribute [...]` applied after the fact, likewise;
    a `deriving` clause, whose generated declarations are named nowhere;
    a NAMESPACE that an `open` line mentions, which fails to elaborate if
      nothing in scope declares into it.

None of the five appears as an identifier.  So this file never reports a
"minimal" set as safe on its own: `analyze` computes the name-driven set and
then re-admits every module that would leave the transitive closure while
carrying one of the five, and reports the readmission as a REASON.  A module
this file cannot clear stays imported.  The corpus's own record of what happens
when a mechanical edit is trusted because it exited zero is in
`validation/code/check.py`; this file is written to be checkable the same way,
by effect.

  python3 validation/code/imports.py depth          # DAG depth, deepest paths
  python3 validation/code/imports.py chains         # necklace detection
  python3 validation/code/imports.py analyze        # per-module minimal set
  python3 validation/code/imports.py analyze --dir Descent/Portability/PortabilityDrift
  python3 validation/code/imports.py verify         # names with no import providing them
  python3 validation/code/imports.py rewrite --dir ... [--apply]

`rewrite` without `--apply` prints the diff it would make and changes nothing.
`verify` is the gate: run it before and after, and the count must not rise.

`--keep-head-imports` holds back one class of edit -- see `plan`.  31 modules
import a directory HEAD to reach one or two declarations, and naming the module
instead is strictly less build work; but `check.py --only shape-depth` deletes
tables of contents from the graph before measuring, so those edges are scored as
free and making them honest reads as a depth regression from 12 to 18.  The flag
exists so the other 105 edits can land while that is settled.

NOT A COMPILER.  This reads source text.  It cannot see what Lean's elaborator
sees, and on this corpus it CANNOT be checked against `#min_imports` today
because every MSI partition is in maintenance.  Treat its output as a proposal
that a build must still confirm.
"""

from __future__ import annotations

import argparse
import os
import re
import sys
from collections import defaultdict

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
CORPUS = "Descent"


# --------------------------------------------------------------------------
# reading modules
# --------------------------------------------------------------------------

def module_paths():
    """Every `Descent.*` module on disk, as (module name, path), sorted."""
    out = []
    root_file = os.path.join(ROOT, CORPUS + ".lean")
    if os.path.exists(root_file):
        out.append((CORPUS, root_file))
    for dirpath, _dirs, files in os.walk(os.path.join(ROOT, CORPUS)):
        for name in files:
            if not name.endswith(".lean"):
                continue
            path = os.path.join(dirpath, name)
            rel = os.path.relpath(path, ROOT)
            out.append((rel[: -len(".lean")].replace(os.sep, "."), path))
    return sorted(out)


BLOCK_COMMENT = re.compile(r"/-.*?-/", re.S)
LINE_COMMENT = re.compile(r"--[^\n]*")
STRING_LIT = re.compile(r'"(?:[^"\\]|\\.)*"')


def strip_noncode(text: str) -> str:
    """Drop block comments (docstrings included), line comments, string literals.

    Newlines inside a removed span are preserved so line numbers survive.  A
    docstring MENTIONING a declaration is not a dependency on it: the corpus's
    docstrings cite theorems in other directories constantly, and honouring
    those citations as imports would chain the corpus back together through
    prose.  Code is what needs an import.
    """
    def blank(match):
        return re.sub(r"[^\n]", " ", match.group(0))

    text = BLOCK_COMMENT.sub(blank, text)
    text = STRING_LIT.sub(blank, text)
    text = LINE_COMMENT.sub(blank, text)
    return text


IMPORT_RE = re.compile(r"^import\s+([A-Za-z0-9_.«»]+)", re.M)


def read_imports(text: str):
    return [m for m in IMPORT_RE.findall(text) if m == CORPUS or m.startswith(CORPUS + ".")]


# --------------------------------------------------------------------------
# declarations
# --------------------------------------------------------------------------

DECL_KEYWORDS = (
    "theorem", "lemma", "def", "abbrev", "structure", "inductive", "class",
    "instance", "axiom", "opaque", "example",
)
MODIFIERS = (
    "private", "protected", "noncomputable", "partial", "unsafe", "nonrec",
    "scoped", "local", "@[.*?]",
)

DECL_RE = re.compile(
    r"^(?P<indent>\s*)"
    # `@[simp] theorem foo` puts the attribute and the declaration on ONE line.
    # Without this the line matched neither branch: not a declaration, because
    # it does not start with a keyword, and not an attribute pairing, because
    # the pairing looked only at the NEXT line.  Every same-line `@[simp]`
    # lemma in the corpus was invisible to both the symbol table and the
    # ambient-reach test, which is the failure mode that made the test say
    # "0 ambient declarations" for a module full of them.
    r"(?:@\[[^\]]*\]\s*)*"
    r"(?:(?:private|protected|noncomputable|partial|unsafe|nonrec|scoped|local)\s+)*"
    r"(?P<kw>theorem|lemma|def|abbrev|structure|inductive|class\s+inductive|class|instance|axiom|opaque)"
    r"(?:\s+(?P<name>[A-Za-z_«][A-Za-z0-9_.'!?«»]*))?"
    r"(?=\s|$|\(|\{|\[|:)",
    re.M,
)

NAMESPACE_RE = re.compile(r"^\s*namespace\s+([A-Za-z0-9_.«»]+)", re.M)
END_RE = re.compile(r"^\s*end(?:\s+([A-Za-z0-9_.«»]+))?\s*$", re.M)
SECTION_RE = re.compile(r"^\s*section(?:\s+([A-Za-z0-9_.«»]+))?\s*$", re.M)
OPEN_RE = re.compile(r"^\s*open\s+(?:scoped\s+)?(?P<body>[^\n]*)", re.M)
FIELD_RE = re.compile(r"^\s{1,}(?P<name>[a-zA-Z_][A-Za-z0-9_']*)\s*:(?!=)")
CTOR_RE = re.compile(r"^\s*\|\s*(?P<name>[a-zA-Z_][A-Za-z0-9_']*)\b")


ATTR_RE = re.compile(
    r"@\[[^\]]*\b(?:simp|ext|norm_cast|push_cast|reducible|instance|aesop|fun_prop"
    r"|gcongr|positivity|bound|simps|elab_as_elim|nolint|coe|mono)\b")


class Module:
    def __init__(self, name, path):
        self.name = name
        self.path = path
        self.raw = open(path, encoding="utf-8").read()
        self.code = strip_noncode(self.raw)
        self.imports = read_imports(self.raw)
        self.decls = set()          # fully qualified names declared here
        self.namespaces = set()     # namespaces this module declares into
        self.opens = set()          # namespace names this module `open`s
        self.def_bodies = {}        # def/abbrev name -> its source span
        self.decl_stmts = {}        # every decl name -> its source span
        # AMBIENT declarations: the ones that act on a goal without being
        # named.  Each maps to the source span whose identifiers decide
        # whether it can reach a given module's goals at all.
        self.ambient = []           # (kind, span)
        self.has_attribute_cmd = False
        self._scan()

    # -- scanning ---------------------------------------------------------

    def _scan(self):
        lines = self.code.split("\n")
        stack = []          # ("ns", name) or ("section", name)
        pending_attr = None  # an `@[...]` line waiting for its declaration
        for i, line in enumerate(lines):
            m = NAMESPACE_RE.match(line)
            if m:
                stack.append(("ns", m.group(1)))
                self.namespaces.add(self._current_ns(stack))
                continue
            if SECTION_RE.match(line):
                stack.append(("section", SECTION_RE.match(line).group(1)))
                continue
            m = END_RE.match(line)
            if m:
                if stack:
                    stack.pop()
                continue
            m = OPEN_RE.match(line)
            if m:
                for tok in self._open_targets(m.group("body")):
                    self.opens.add(tok)
                # fall through: `open X in` lines can carry nothing else
            if re.match(r"^\s*attribute\s*\[", line):
                self.has_attribute_cmd = True
                self.ambient.append(("attribute command", self._span(lines, i)))
            if ATTR_RE.search(line):
                pending_attr = i
            if re.search(r"\bderiving\b", line):
                self.ambient.append(("deriving clause", self._span(lines, i)))

            m = DECL_RE.match(line)
            if m:
                kw = m.group("kw").split()[0]
                name = m.group("name")
                span = self._span(lines, i)
                if kw == "instance":
                    self.ambient.append(("instance", span))
                elif pending_attr is not None and pending_attr >= i - 1:
                    # `pending_attr == i` is the same-line `@[simp] theorem`
                    # form; `i - 1` is the attribute on its own line above.
                    self.ambient.append(("simp-set attribute", span))
                pending_attr = None
                if name is None:
                    continue
                ns = self._current_ns(stack)
                full = f"{ns}.{name}" if ns else name
                self.decls.add(full)
                self.decl_stmts[full] = span
                if kw in ("def", "abbrev"):
                    self.def_bodies[full] = span
                if kw in ("structure", "class"):
                    self._scan_fields(lines, i, full)
                    # A projection unfolds to the structure it projects from,
                    # so seeing the field exposes the parent.
                    for f in list(self.decls):
                        if f.startswith(full + "."):
                            self.def_bodies[f] = span
                elif kw == "inductive":
                    self._scan_ctors(lines, i, full)

    @staticmethod
    def _span(lines, start):
        """The declaration beginning at `start`, to the next top-level command.

        Over-approximate on purpose.  The span is fed to the ambient-reach test
        below, where including too much makes the test say KEEP more often, not
        less; erring long is erring safe.
        """
        base = len(lines[start]) - len(lines[start].lstrip())
        out = [lines[start]]
        for line in lines[start + 1:]:
            if line.strip() and (len(line) - len(line.lstrip())) <= base and \
                    not line.lstrip().startswith(("|", ")", "]", "}")):
                break
            out.append(line)
        return "\n".join(out)

    @staticmethod
    def _current_ns(stack):
        return ".".join(n for kind, n in stack if kind == "ns")

    @staticmethod
    def _open_targets(body):
        """The namespace names an `open` line brings into scope.

        `open A B in`, `open A (x y)` and `open scoped A` all appear here.  Only
        the namespace heads matter; the parenthesised selectors are names inside
        them and resolve through the namespace anyway.
        """
        body = re.sub(r"\([^)]*\)?", " ", body)
        body = re.sub(r"\bin\b.*$", " ", body)
        out = []
        for tok in body.split():
            if re.fullmatch(r"[A-Za-z_][A-Za-z0-9_.'«»]*", tok):
                out.append(tok)
        return out

    def _scan_fields(self, lines, start, owner):
        """Projections of a `structure`/`class`, which are referenced as
        `Owner.field` and never appear after a declaration keyword."""
        base = len(lines[start]) - len(lines[start].lstrip())
        for line in lines[start + 1:]:
            if not line.strip():
                continue
            indent = len(line) - len(line.lstrip())
            if indent <= base:
                break
            m = FIELD_RE.match(line)
            if m:
                self.decls.add(f"{owner}.{m.group('name')}")

    def _scan_ctors(self, lines, start, owner):
        base = len(lines[start]) - len(lines[start].lstrip())
        for line in lines[start + 1:]:
            if not line.strip():
                continue
            indent = len(line) - len(line.lstrip())
            if indent <= base and not line.lstrip().startswith("|"):
                break
            m = CTOR_RE.match(line)
            if m:
                self.decls.add(f"{owner}.{m.group('name')}")

    # -- references -------------------------------------------------------

    IDENT = re.compile(r"(?<![A-Za-z0-9_.'«»])([A-Za-z_][A-Za-z0-9_'!?]*(?:\.[A-Za-z_][A-Za-z0-9_'!?]*)*)")

    def references(self):
        """Every dotted identifier in the code, minus the import block."""
        body = IMPORT_RE.sub("", self.code)
        return set(self.IDENT.findall(body))

    def enclosing_namespaces(self):
        """Namespace prefixes in force somewhere in this module, longest first."""
        out = set()
        for ns in self.namespaces:
            parts = ns.split(".")
            for k in range(len(parts), 0, -1):
                out.add(".".join(parts[:k]))
        return out


def load_corpus():
    mods = {}
    for name, path in module_paths():
        mods[name] = Module(name, path)
    return mods


# --------------------------------------------------------------------------
# graph
# --------------------------------------------------------------------------

def transitive(mods, start, seen=None):
    """Every module reachable from `start` through imports, `start` excluded."""
    if seen is None:
        seen = set()
    for imp in mods[start].imports if start in mods else ():
        if imp in seen:
            continue
        seen.add(imp)
        transitive(mods, imp, seen)
    return seen


def depths(mods):
    memo = {}

    def d(m):
        if m in memo:
            return memo[m]
        memo[m] = 0
        memo[m] = 1 + max([d(x) for x in mods[m].imports if x in mods], default=-1)
        return memo[m]

    return {m: d(m) for m in mods}


def deepest_path(mods, start):
    dep = depths(mods)
    path = [start]
    cur = start
    while mods[cur].imports:
        nxt = max((x for x in mods[cur].imports if x in mods), key=lambda x: dep[x], default=None)
        if nxt is None:
            break
        path.append(nxt)
        cur = nxt
    return path


# --------------------------------------------------------------------------
# resolution
# --------------------------------------------------------------------------

class Symbols:
    """Fully-qualified name -> the modules that declare it."""

    def __init__(self, mods):
        self.owner = defaultdict(set)
        self.ns_owner = defaultdict(set)
        self.spans = {}
        for m in mods.values():
            for d in m.decls:
                self.owner[d].add(m.name)
            for d, span in m.decl_stmts.items():
                self.spans.setdefault(d, span)
            for ns in m.namespaces:
                parts = ns.split(".")
                for k in range(1, len(parts) + 1):
                    self.ns_owner[".".join(parts[:k])].add(m.name)
        self._cache = {}

    def span(self, full):
        return self.spans.get(full)

    def home(self, full):
        return sorted(self.owner[full])[0]

    def canonical(self, ident, mod):
        """The fully-qualified corpus names `ident` could denote inside `mod`.

        Empty when the identifier is Mathlib's, a local hypothesis, a tactic or
        a binder -- which is most of them.
        """
        key = (ident, mod.name)
        hit = self._cache.get(key)
        if hit is None:
            hit = self._canonical(ident, mod)
            self._cache[key] = hit
        return hit

    def _canonical(self, ident, mod):
        prefixes = sorted(mod.enclosing_namespaces(), key=len, reverse=True)
        candidates = [ident] + [f"{p}.{ident}" for p in prefixes]
        for op in mod.opens:
            candidates.append(f"{op}.{ident}")
            candidates += [f"{p}.{op}.{ident}" for p in prefixes]
        parts = ident.split(".")
        for k in range(len(parts) - 1, 0, -1):
            head = ".".join(parts[:k])
            candidates.append(head)
            candidates += [f"{p}.{head}" for p in prefixes]
        for cand in candidates:
            if cand in self.owner:
                return {cand}
        return set()

    def resolve(self, ident, mod):
        """Candidate defining modules for `ident` as written inside `mod`.

        Lean resolves a name against the enclosing namespaces innermost-first,
        then the `open`ed ones, then absolutely.  This returns the FIRST
        nonempty candidate set in that order, which is the set of modules any
        one of which could be the definition site.
        """
        prefixes = sorted(mod.enclosing_namespaces(), key=len, reverse=True)
        for pre in prefixes:
            cand = self.owner.get(f"{pre}.{ident}")
            if cand:
                return cand
        for op in mod.opens:
            for pre in [op] + [f"{p}.{op}" for p in prefixes]:
                cand = self.owner.get(f"{pre}.{ident}")
                if cand:
                    return cand
        cand = self.owner.get(ident)
        if cand:
            return cand
        # A prefix of a dotted name can be the declaration and the rest
        # projections applied to it (`panel.retainedMarkers`, `h.mp`), so try
        # the heads too.
        parts = ident.split(".")
        for k in range(len(parts) - 1, 0, -1):
            head = ".".join(parts[:k])
            for pre in prefixes:
                cand = self.owner.get(f"{pre}.{head}")
                if cand:
                    return cand
            cand = self.owner.get(head)
            if cand:
                return cand
        return set()


def minimal_antichain(mods, modules):
    """Drop any module already implied by another in the set."""
    modules = set(modules)
    implied = set()
    for m in modules:
        implied |= transitive(mods, m) & modules
    return sorted(modules - implied)


# --------------------------------------------------------------------------
# the analysis
# --------------------------------------------------------------------------

# --------------------------------------------------------------------------
# the ambient-reach test
# --------------------------------------------------------------------------
#
# THE PROBLEM THIS SOLVES.  Four kinds of declaration act on a module that
# never names them: an instance, a `@[simp]`-tagged lemma, an `attribute [...]`
# command, and a `deriving` clause.  A first pass simply refused to drop any
# import whose module contained one -- and 92 of the corpus's 283 modules carry
# a `@[simp]`, so that rule re-admitted essentially every chain link and the
# depth did not move.  A guard that never says yes is not conservative, it is
# inert.
#
# The sharper rule uses the fact that all four are LOCAL to the symbols they
# mention.  A `simp` lemma rewrites a subterm only if the goal contains that
# subterm's head symbol; an instance is found only for a class applied to a type
# that appears in the goal.  So a dropped module is safe exactly when NONE of
# the corpus names in its ambient declarations can appear in the importing
# module's goals.
#
# "Can appear" is the part that has to be got right, because a goal contains
# more than what the module wrote.  `unfold f` and `simp [f]` replace `f` with
# its body, exposing every name the body mentions; `rw [thm]` replaces one side
# of `thm` with the other, exposing everything in its statement.  So the test
# runs against a CLOSURE: seed with the names the module writes, then repeatedly
# add the names in the body of every `def` reached and in the statement of every
# theorem reached, to a fixed point.  A name is out of reach only if no chain of
# unfolding can put it in front of a tactic.

def exposed_names(mods, syms, name):
    """Every corpus declaration that could appear in a goal inside `name`.

    Seeded with what the module writes; closed under `def` bodies (what
    `unfold` and `simp [f]` expose) and under the statements of theorems the
    module names (what `rw` and `exact` expose).
    """
    mod = mods[name]
    frontier = set()
    for ident in mod.references():
        frontier |= syms.canonical(ident, mod)

    seen = set()
    while frontier:
        cur = frontier.pop()
        if cur in seen:
            continue
        seen.add(cur)
        span = syms.span(cur)
        if span is None:
            continue
        owner = mods[syms.home(cur)]
        for ident in Module.IDENT.findall(span):
            for full in syms.canonical(ident, owner):
                if full not in seen:
                    frontier.add(full)
    return seen


def ambient_reaches(mods, syms, dropped, exposed):
    """Why `dropped`'s ambient declarations could still act on the goal.

    Returns a reason string, or None if none of them can.
    """
    d = mods[dropped]
    for kind, span in d.ambient:
        for ident in Module.IDENT.findall(span):
            for full in syms.canonical(ident, d):
                if full in exposed:
                    return f"{kind} over `{full.split('.')[-1]}`, which is in reach"
    return None


def plan(mods, syms, verbose=False, keep_head_imports=False):
    """The whole corpus's new import lists, as a fixed point.

    WHY THIS IS NOT PER-MODULE.  The first version of this analysis reduced each
    module's import list on its own, dropping any module a SIBLING import
    already reached.  That is correct for one edit and wrong for a batch: the
    sibling's list is being reduced in the same pass, so the reachability the
    drop relied on can disappear underneath it.  It did.  `MigrationDrift`
    dropped `Definitions` because `MutationDrift` reached it, `MutationDrift`
    dropped `Definitions` in the same batch, and `SplitMigrationModel` -- a
    structure `MigrationDrift` extends by declaring into its namespace -- was
    left with no import providing it.  Eight modules were cut loose that way
    and `verify` went from 13 failures to 21.

    So the reduction is computed against the graph the reduction PRODUCES, not
    the graph it consumes.  Name-driven requirements first; then the ambient
    re-admission against the new closure, iterated because a re-admission
    changes the closure and can spare a later one; then a single transitive
    reduction, which preserves reachability exactly and so cannot orphan
    anything the fixed point admitted.
    """
    # -- 1. what each module names ---------------------------------------
    required = {}
    by_name = {}
    unresolved = {}
    old_closures = {name: transitive(mods, name) for name in mods}
    for name in mods:
        mod = mods[name]
        old_closure = old_closures[name]
        alternatives = []
        misses = set()
        for ident in mod.references():
            cand = {c for c in syms.resolve(ident, mod) if c != name}
            if not cand:
                continue
            inside = cand & old_closure
            if inside:
                alternatives.append(frozenset(inside))
            else:
                misses.add(ident)
        forced = {next(iter(s)) for s in alternatives if len(s) == 1}
        for s in alternatives:
            if len(s) > 1 and not (s & forced):
                forced.add(sorted(s)[0])
        # `open Descent.X` needs SOMETHING in scope declaring into `X`.
        for op in mod.opens:
            owners = set()
            for pre in [op] + [f"{p}.{op}" for p in mod.enclosing_namespaces()]:
                owners |= syms.ns_owner.get(pre, set())
            owners = (owners & old_closure) - {name}
            if owners and not (owners & forced):
                forced.add(sorted(owners)[0])
        by_name[name] = set(forced)
        # A head's import list is its directory, not its dependencies, and
        # `rewrite` will not touch it.  Pinning it here keeps the graph this
        # function reasons about the graph the edit actually produces -- a plan
        # computed against a reduced head would justify drops that the real
        # tree, with the head unchanged, never supports.
        required[name] = set(mods[name].imports) if is_head(name) else set(forced)
        if keep_head_imports and not is_head(name):
            # A module that imports a directory HEAD to reach one declaration is
            # paying for the whole directory, and replacing that with the module
            # it names is the right edit -- 31 modules in this corpus do it.
            # But `check.py --only shape-depth` deletes tables of contents from
            # the graph before measuring, so a `module -> head` edge is scored
            # as free and the replacement, which strictly reduces build work,
            # reads as a depth REGRESSION (12 to 18 when all 31 are done).
            # This flag holds those 31 back so the rest can land while that
            # disagreement is settled, and is not a claim that keeping them is
            # better.
            required[name] |= {h for h in mods[name].imports if is_head(h)}
        unresolved[name] = sorted(misses)

    # -- 2. ambient re-admission, to a fixed point ------------------------
    exposed = {name: exposed_names(mods, syms, name) for name in mods}
    readmitted = {name: {} for name in mods}
    for _round in range(6):
        new_closures = closures_of(mods, required)
        added = 0
        for name in mods:
            for gone in sorted(old_closures[name] - new_closures[name]):
                if gone in readmitted[name]:
                    continue
                why = ambient_reaches(mods, syms, gone, exposed[name])
                if why:
                    readmitted[name][gone] = why
                    required[name].add(gone)
                    added += 1
        if verbose:
            print(f"  round {_round}: {added} re-admission(s)", file=sys.stderr)
        if not added:
            break

    # -- 3. Mathlib must not fall out from under the module ---------------
    #
    # Only 152 of the corpus's 284 modules write an `import Mathlib...` line.
    # The other 132 reach Mathlib THROUGH a `Descent` import -- which means an
    # import that looks like dead weight by the name test can be the only thing
    # supplying `ℝ`, or `Real.log`, or the tactic a proof closes with.  Nothing
    # in this file resolves a Mathlib name, so it cannot tell which Mathlib
    # module a proof needs, and there is no Mathlib source on disk to ask.
    #
    # Measured before this step existed, the plan took Mathlib coverage away
    # from 144 of 285 modules, up to 35 modules' worth from a single file.
    # That is not a marginal risk, it is most of the corpus.
    #
    # So the invariant is simply that the set of non-`Descent` modules a file
    # can see never shrinks.  Where a reduction would shrink it, old imports
    # are re-admitted, greediest-first, until it does not.  The alternative --
    # writing the lost Mathlib imports into the file directly -- needs the
    # Mathlib import graph to reduce them to something a person would want to
    # read, and that graph is not here.
    mathlib_of = {name: {i for i in IMPORT_RE.findall(mods[name].raw)
                         if not (i == CORPUS or i.startswith(CORPUS + "."))}
                  for name in mods}

    def mathlib_seen(name, closure):
        out = set(mathlib_of[name])
        for x in closure:
            out |= mathlib_of[x]
        return out

    mathlib_readmitted = {name: {} for name in mods}
    for _round in range(12):
        new_closures = closures_of(mods, required)
        added = 0
        for name in mods:
            lost = (mathlib_seen(name, old_closures[name])
                    - mathlib_seen(name, new_closures[name]))
            if not lost:
                continue
            pool = old_closures[name] - required[name] - {name}
            while lost and pool:
                best = max(pool, key=lambda c: (
                    len(mathlib_seen(c, closures_of_one(mods, required, c)) & lost),
                    -len(old_closures[c])))
                covered = mathlib_seen(best, closures_of_one(mods, required, best)) & lost
                if not covered:
                    break
                required[name].add(best)
                mathlib_readmitted[name][best] = (
                    f"carries {len(covered)} non-Descent import(s) nothing else "
                    f"supplies, e.g. {sorted(covered)[0]}")
                lost -= covered
                pool.discard(best)
                added += 1
        if verbose:
            print(f"  mathlib round {_round}: {added} re-admission(s)", file=sys.stderr)
        if not added:
            break

    for name in mods:
        readmitted[name].update(mathlib_readmitted[name])

    # -- 4. transitive reduction, against the graph this produces ---------
    final_closures = closures_of(mods, required)
    proposed = {}
    for name in mods:
        if is_head(name):
            proposed[name] = sorted(mods[name].imports)
            continue
        implied = set()
        for m in required[name]:
            implied |= final_closures[m] & required[name]
        proposed[name] = sorted(required[name] - implied)

    out = {}
    for name in mods:
        closure = final_closures[name]
        out[name] = {
            "old": sorted(mods[name].imports),
            "proposed": proposed[name],
            "by_name": sorted(by_name[name]),
            "readmitted": readmitted[name],
            "unresolved": unresolved[name],
            "lost": sorted(old_closures[name] - closure),
            "orphaned": sorted(m for m in by_name[name] if m not in closure),
        }
    return out


def closures_of_one(mods, imports, start):
    """`start`'s reachable set under `imports`, plus `start` itself."""
    seen = {start}
    stack = [start]
    while stack:
        cur = stack.pop()
        for i in imports.get(cur, ()):
            if i not in seen:
                seen.add(i)
                stack.append(i)
    return seen


def closures_of(mods, imports):
    """Transitive closure of every module under a given import assignment."""
    memo = {}

    def go(m):
        if m in memo:
            return memo[m]
        memo[m] = set()
        acc = set()
        for i in imports.get(m, ()):
            acc.add(i)
            acc |= go(i)
        memo[m] = acc
        return acc

    return {m: go(m) for m in mods}


def analyze_module(mods, syms, name):
    """Return (proposed imports, needed-by-name modules, readmitted {module: reason})."""
    mod = mods[name]
    old_closure = transitive(mods, name)

    needed = set()
    unresolved = set()
    for ident in mod.references():
        cand = syms.resolve(ident, mod)
        cand = {c for c in cand if c != name}
        if not cand:
            continue
        # Prefer a candidate already in the closure; a name resolving to a
        # module this file cannot see is this analysis being wrong, not the
        # corpus being wrong.
        inside = cand & old_closure
        if inside:
            # If exactly one, that is the definition site.  If several declare
            # the same full name, keep them all as alternatives -- resolved
            # below by preferring one already required.
            needed.add(frozenset(inside))
        else:
            unresolved.add(ident)

    # Collapse the alternative-sets: a singleton is forced; a larger set is
    # satisfied if any member is already forced.
    forced = {next(iter(s)) for s in needed if len(s) == 1}
    for s in needed:
        if len(s) > 1 and not (s & forced):
            forced.add(sorted(s)[0])

    # `open Descent.X` needs X to be a namespace something in scope declares in.
    for op in mod.opens:
        owners = set()
        for pre in [op] + [f"{p}.{op}" for p in mod.enclosing_namespaces()]:
            owners |= syms.ns_owner.get(pre, set())
        owners = (owners & old_closure) - {name}
        if owners and not any(o in forced or o in transitive_of_set(mods, forced) for o in owners):
            forced.add(sorted(owners)[0])

    by_name = set(forced)
    proposed = set(minimal_antichain(mods, by_name))

    # Re-admit anything that would leave the closure while carrying an ambient
    # declaration that can still reach this module's goals.  This is the
    # conservative half and it is not optional: see `ambient_reaches`.
    readmitted = {}
    exposed = exposed_names(mods, syms, name)
    for _ in range(8):
        new_closure = transitive_of_set(mods, proposed) | proposed
        fresh = {}
        for gone in sorted(old_closure - new_closure - set(readmitted)):
            why = ambient_reaches(mods, syms, gone, exposed)
            if why:
                fresh[gone] = why
        if not fresh:
            break
        readmitted.update(fresh)
        proposed = set(minimal_antichain(mods, proposed | set(readmitted)))

    new_closure = transitive_of_set(mods, proposed) | proposed
    return {
        "old": sorted(mod.imports),
        "proposed": sorted(proposed),
        "by_name": sorted(by_name),
        "readmitted": readmitted,
        "unresolved": sorted(unresolved),
        # Modules that leave the transitive closure.  An import line that
        # disappears while its module stays reachable is pure redundancy and
        # costs nothing to remove; THIS is the set where a mistake bites.
        "lost": sorted(old_closure - new_closure),
        # Everything the module names, still reachable?  If a name's home is
        # not in the new closure the proposal is wrong on its face.
        "orphaned": sorted(m for m in by_name if m not in new_closure),
    }


def transitive_of_set(mods, names):
    seen = set()
    for n in names:
        if n in mods:
            transitive(mods, n, seen)
    return seen


# --------------------------------------------------------------------------
# rewriting
# --------------------------------------------------------------------------

def rewrite_import_block(text: str, keep_nondescent, new_descent):
    """Replace the `Descent.*` import lines with `new_descent`, sorted.

    Non-`Descent` imports (Mathlib) keep their place and their order.  The block
    is contiguous in every module of this corpus and the style guard requires
    it, so this rewrites the span from the first import to the last.
    """
    lines = text.split("\n")
    idx = [i for i, l in enumerate(lines) if IMPORT_RE.match(l)]
    if not idx:
        return None
    lo, hi = idx[0], idx[-1]
    block = [l for l in lines[lo:hi + 1] if IMPORT_RE.match(l)]
    non_descent = [l for l in block
                   if not IMPORT_RE.match(l).group(1).startswith(CORPUS)]
    new_block = non_descent + [f"import {m}" for m in sorted(new_descent)]
    return "\n".join(lines[:lo] + new_block + lines[hi + 1:])


# --------------------------------------------------------------------------
# commands
# --------------------------------------------------------------------------

def cmd_depth(mods, args):
    dep = depths(mods)
    print(f"{len(mods)} modules; DAG depth {max(dep.values())}")
    print()
    for m, d in sorted(dep.items(), key=lambda x: (-x[1], x[0]))[:args.top]:
        print(f"  {d:3d}  {m}")
    if args.path:
        print()
        print(f"deepest path from {args.path}:")
        for step in deepest_path(mods, args.path):
            print(f"    {step}")
    return 0


def cmd_chains(mods, args):
    """Directories where every non-head file imports exactly one sibling."""
    by_dir = defaultdict(list)
    for name in mods:
        if "." not in name:
            continue
        by_dir[name.rsplit(".", 1)[0]].append(name)
    rows = []
    for d, members in sorted(by_dir.items()):
        links = [m for m in members
                 if len(mods[m].imports) == 1 and mods[m].imports[0] in members]
        if len(members) > 2 and links:
            rows.append((len(links), len(members), d))
    single = sum(1 for m in mods.values() if len(m.imports) == 1)
    print(f"{single} of {len(mods)} modules have exactly one `import Descent.*` line")
    print()
    for links, total, d in sorted(rows, reverse=True):
        print(f"  {links:3d}/{total:<3d} chain links  {d}")
    return 0


def is_head(name):
    """A directory head, whose import list is not a dependency list at all.

    `Descent/Portability.lean` beside `Descent/Portability/` imports every file
    in that directory whether or not it names anything in it, and
    `check.py --only heads` FAILS if the two ever disagree -- that is the whole
    point of the head, and the root docstring records the module that went
    unbuilt for a day before heads existed.  So a head is not a candidate for
    minimisation; minimising one would delete the coverage guarantee and the
    guard would catch it, which is a guard doing its job over an edit that
    should never have been proposed.
    """
    return os.path.isdir(os.path.join(ROOT, name.replace(".", os.sep)))


def selected(mods, args):
    if args.dir:
        pre = args.dir.rstrip("/").replace("/", ".")
        return [m for m in sorted(mods) if m.startswith(pre + ".")]
    if args.module:
        return [args.module]
    return sorted(mods)


def cmd_analyze(mods, args):
    syms = Symbols(mods)
    table = plan(mods, syms, verbose=args.verbose,
                 keep_head_imports=args.keep_head_imports)
    lines_changed = kept = lost = orphaned = 0
    for name in selected(mods, args):
        if is_head(name):
            continue
        r = table[name]
        old, proposed = r["old"], r["proposed"]
        if proposed == old and not args.verbose:
            continue
        gained = [m for m in proposed if m not in old]
        dropped = [m for m in old if m not in proposed]
        lines_changed += len(gained) + len(dropped)
        kept += len(r["readmitted"])
        lost += len(r["lost"])
        orphaned += len(r["orphaned"])
        print(f"\n{name}")
        print(f"  now:      {', '.join(old) or '(none)'}")
        print(f"  proposed: {', '.join(proposed) or '(none)'}")
        if gained:
            print(f"  ADD:      {', '.join(gained)}")
        if dropped:
            print(f"  DROP:     {', '.join(dropped)}")
        if r["lost"]:
            print(f"  LEAVES CLOSURE ({len(r['lost'])}): {', '.join(r['lost'])}")
        for m, why in sorted(r["readmitted"].items()):
            print(f"  KEPT:     {m} -- {why}")
        if r["orphaned"]:
            print(f"  ORPHANED: {', '.join(r['orphaned'])}   <<< PROPOSAL IS WRONG")
        if r["unresolved"] and args.verbose:
            print(f"  unresolved: {', '.join(r['unresolved'][:12])}")
    print(f"\n{lines_changed} import line(s) would change; {lost} module(s) leave a "
          f"closure; {kept} re-admitted for an ambient declaration in reach; "
          f"{orphaned} orphaned reference(s)")
    return 1 if orphaned else 0


def cmd_verify(mods, args):
    """Hold the CURRENT tree to the standard the rewrite must meet.

    Every corpus name a module writes must have its defining module inside that
    module's transitive import closure.  Run before a rewrite it should be
    silent; run after, it is the check that the rewrite did not cut a name
    loose.  It is a lower bound on correctness, not a build.
    """
    syms = Symbols(mods)
    bad = 0
    for name in selected(mods, args):
        mod = mods[name]
        closure = transitive(mods, name)
        missing = defaultdict(set)
        for ident in mod.references():
            for full in syms.canonical(ident, mod):
                home = syms.owner[full]
                if name in home or (home & closure):
                    continue
                missing[sorted(home)[0]].add(full)
        if missing:
            bad += 1
            print(f"\n{name}: {len(missing)} module(s) named but not imported")
            for home, names in sorted(missing.items()):
                shown = sorted(names)[:4]
                print(f"    {home}: {', '.join(shown)}"
                      f"{' ...' if len(names) > 4 else ''}")
    print(f"\nverify: {bad} module(s) reference a name no import provides")
    return 1 if bad else 0


def cmd_rewrite(mods, args):
    syms = Symbols(mods)
    table = plan(mods, syms, keep_head_imports=args.keep_head_imports)
    changed = 0
    for name in selected(mods, args):
        if is_head(name):
            continue
        mod = mods[name]
        r = table[name]
        if r["orphaned"]:
            print(f"{name}: SKIPPED, proposal orphans {r['orphaned']}")
            continue
        if r["proposed"] == sorted(mod.imports):
            continue
        new_text = rewrite_import_block(mod.raw, None, r["proposed"])
        if new_text is None or new_text == mod.raw:
            continue
        changed += 1
        print(f"{name}: {sorted(mod.imports)} -> {r['proposed']}")
        if args.apply:
            with open(mod.path, "w", encoding="utf-8") as fh:
                fh.write(new_text)
    print(f"{changed} module(s) {'rewritten' if args.apply else 'would change'}")
    return 0


def main(argv=None):
    p = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    sub = p.add_subparsers(dest="cmd", required=True)

    d = sub.add_parser("depth")
    d.add_argument("--top", type=int, default=20)
    d.add_argument("--path", default=None)
    d.set_defaults(fn=cmd_depth)

    c = sub.add_parser("chains")
    c.set_defaults(fn=cmd_chains)

    for nm, fn in (("analyze", cmd_analyze), ("rewrite", cmd_rewrite),
                   ("verify", cmd_verify)):
        s = sub.add_parser(nm)
        s.add_argument("--dir", default=None)
        s.add_argument("--module", default=None)
        s.add_argument("--verbose", action="store_true")
        s.add_argument("--keep-head-imports", action="store_true",
                       dest="keep_head_imports",
                       help="do not replace an import of a directory head with the "
                            "modules under it; see `plan`")
        if nm == "rewrite":
            s.add_argument("--apply", action="store_true")
        s.set_defaults(fn=fn)

    args = p.parse_args(argv)
    mods = load_corpus()
    return args.fn(mods, args)


if __name__ == "__main__":
    sys.exit(main())
