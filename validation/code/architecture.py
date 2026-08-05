#!/usr/bin/env python3
"""Architecture gates: the shape of the corpus, checked rather than described.

WHY THIS EXISTS.  Every mechanism this corpus reached for to keep its repeated
quantities in step -- identity theorems in `Foundations/Conventions`, identity
theorems in the root, a master theorem naming an interface -- was placed ABOVE the
things it related.  An identity stated in a leaf can only describe agreement;
nothing below it can depend on the agreement, so a divergence is caught only if
someone re-runs a census by hand.  The root file states the rule:

    When two places must agree, make one of them call the other; a note
    explaining why they must agree is not a mechanism.

These gates are that rule applied to the architecture itself.  Each measures a
property the corpus has been repaired to have, and fails the build if it is lost
again.

ZERO TOLERANCE.  Every defect count must be ZERO.  There is no baseline file and
no allowance for the state the corpus happens to be in: a duplicate body, an
orphan definition, an uninhabited structure, a foundation that depends on what it
reconciles, or a falsification no docstring mentions fails the build.

This replaces an earlier ratchet that compared against a recorded baseline and
failed only on regression.  A ratchet makes the current state the standard, and
the current state is the thing being repaired -- so it licenses every defect that
already exists and asks only that no new ones appear.  The counts below are what
is left to fix, and the gate says so by failing.

    python3 validation/code/architecture.py            # report
    python3 validation/code/architecture.py --gate     # exit nonzero unless every count is zero
    python3 validation/code/architecture.py --verbose  # name every offender
"""

from __future__ import annotations

import argparse
import collections
import json
import os
import re
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
LEAN_ROOT = os.path.join(ROOT, "Descent")

# A declaration head at column zero.  Continuation lines and `where` fields are
# deliberately not matched: this counts declarations, not identifiers.
DECL = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+)*"
    r"(def|abbrev|theorem|lemma|structure|inductive|instance|class)\s+"
    r"([A-Za-z_][A-Za-z0-9_.'!?₀-₉]*)")
IMPORT = re.compile(r"^import\s+(\S+)$", re.M)
IDENT = re.compile(r"[A-Za-z_][A-Za-z0-9_'₀-₉]*")


def strip_comments(text: str) -> str:
    """Remove block comments (which includes every docstring) and line comments.

    Prose mentions a declaration by name constantly -- that is the corpus working
    as intended -- so a reference count that reads docstrings measures how much
    was written about a name, not whether anything depends on it.  Every count
    below runs on the stripped text.
    """
    text = re.sub(r"/-.*?-/", " ", text, flags=re.S)
    text = re.sub(r"--[^\n]*", " ", text)
    return text


def load():
    """Return (module -> raw source, module -> code-only source)."""
    raw, code = {}, {}
    for dirpath, _, filenames in os.walk(LEAN_ROOT):
        for fn in sorted(filenames):
            if not fn.endswith(".lean"):
                continue
            path = os.path.join(dirpath, fn)
            mod = os.path.relpath(path, ROOT)[:-len(".lean")].replace(os.sep, ".")
            with open(path, encoding="utf-8", errors="ignore") as fh:
                text = fh.read()
            raw[mod] = text
            code[mod] = strip_comments(text)
    root_lean = os.path.join(ROOT, "Descent.lean")
    if os.path.exists(root_lean):
        with open(root_lean, encoding="utf-8", errors="ignore") as fh:
            text = fh.read()
        raw["Descent"] = text
        code["Descent"] = strip_comments(text)
    return raw, code


def import_graph(raw):
    """Direct internal imports, module -> set of modules."""
    graph = {}
    for mod, text in raw.items():
        deps = {m for m in IMPORT.findall(text) if m in raw and m != mod}
        graph[mod] = deps
    return graph


def depths(graph):
    """Longest path from a leaf, computed iteratively so a cycle cannot hang us."""
    depth, visiting = {}, set()

    def go(mod):
        if mod in depth:
            return depth[mod]
        if mod in visiting:          # import cycles are impossible in Lean, but
            return 0                 # a malformed tree must not spin forever
        visiting.add(mod)
        d = 0
        for dep in graph.get(mod, ()):
            d = max(d, go(dep) + 1)
        visiting.discard(mod)
        depth[mod] = d
        return d

    for mod in graph:
        go(mod)
    return depth


def in_degrees(graph):
    deg = collections.Counter({mod: 0 for mod in graph})
    for mod, deps in graph.items():
        for dep in deps:
            deg[dep] += 1
    return deg


def declarations(code):
    """module -> list of (kind, short name)."""
    out = {}
    for mod, text in code.items():
        found = []
        for line in text.split("\n"):
            m = DECL.match(line)
            if m:
                found.append((m.group(1), m.group(2).split(".")[-1]))
        out[mod] = found
    return out


# --------------------------------------------------------------------------
# The gates
# --------------------------------------------------------------------------

# A module claims a foundational role by SITTING in Core/ or Foundations/, or by
# saying so in a strong, deliberate phrase in its header.  An earlier version of
# this gate matched any header containing "convention" or "kernel" and flagged 82
# modules, most of which merely discuss one -- a gate that fires on almost
# everything teaches everyone to ignore it, which is worse than no gate.
FOUNDATION_HINT = re.compile(
    r"(this module is depth|is the reconciliation|the entire risk of this"
    r"|shared primitive|must be imported by|the hub\b)", re.I)


def claims_foundation(mod: str, header: str) -> bool:
    if mod.startswith("Descent.Core.") or mod.startswith("Descent.Foundations."):
        return True
    return bool(FOUNDATION_HINT.search(header))


def gate_foundation_position(raw, graph, depth, indeg):
    """A module that CLAIMS to be a foundation must be positioned as one.

    `Foundations/Conventions.lean` opened by declaring itself the place where the
    whole risk of the development sits, then imported twenty-two modules and was
    imported by three -- depth 12 of 13, and a leaf.  A file cannot reconcile
    what it depends on.

    The claim is read from the module path and from the header docstring, so the
    gate cannot be satisfied by renaming a file while leaving the prose.
    """
    inverted, thin = [], []
    for mod in sorted(graph):
        header = raw[mod][:4000]
        if not claims_foundation(mod, header):
            continue
        d, deg = depth[mod], indeg[mod]
        # THE DEFECT is not depth as such -- a foundation may rest on other
        # foundations, and Core is four layers deep by design (Ratios, Fst,
        # Parameters, Moments).  It is depending on the SUBSYSTEMS you claim to
        # reconcile: an identity stated above PopGen and Portability can only
        # describe their agreement, and nothing below it can be made to respect
        # the agreement.  So the test is what a foundation imports, not how deep
        # it sits.
        outside = sorted(m for m in graph[mod]
                         if not (m.startswith("Descent.Core.")
                                 or m.startswith("Descent.Foundations.")))
        if outside:
            inverted.append({"module": mod, "depth": d, "in_degree": deg,
                             "imports_subsystems": len(outside),
                             "example": outside[0]})
        elif deg < 5:
            # NOT THE SAME THING.  Correctly positioned, not yet load-bearing --
            # a new Core module starts here and earns consumers as callers move
            # over.  Tracked separately so that adding a foundation at depth 0
            # does not read as the inversion this gate exists to catch.
            thin.append({"module": mod, "depth": d, "in_degree": deg})
    return inverted, thin


def gate_duplicate_bodies(code):
    """Alpha-equivalent definition bodies: the same map under a second name.

    Binder names are replaced positionally, so `1 - a/b` and `1 - x/y` collide.

    A collision is not automatically a defect: four names for `(1-r)^t` is four
    REFERENTS, and the corpus is right to keep them -- `admixtureLDDecay` carries
    a measured one-sided bias a bare primitive has nowhere to put. What matters
    is whether the shared shape is in the BODIES or only in a census.

    So a body that calls a `Core` kernel is not counted. Three definitions whose
    bodies all read `Core.geometricDecay r t` are the repaired state, not the
    defect -- an edit to the kernel reaches all three by construction. An earlier
    version of this gate counted them, which would have penalised exactly the fix
    it exists to encourage. What is counted is a body that RE-TYPES a shape some
    other body also re-types, with nothing joining them.
    """
    bodies = collections.defaultdict(list)
    head = re.compile(
        r"^\s*(?:noncomputable\s+)?(def|abbrev)\s+([A-Za-z_][\w.'₀-₉]*)")
    stop = re.compile(
        r"^\s*(noncomputable |def |abbrev |theorem |lemma |structure |inductive "
        r"|instance |class |end |namespace |section |@\[)")
    for mod, text in code.items():
        lines = text.split("\n")
        i = 0
        while i < len(lines):
            m = head.match(lines[i])
            if not m:
                i += 1
                continue
            block = [lines[i]]
            j = i + 1
            while j < len(lines) and lines[j].strip() and not stop.match(lines[j]):
                block.append(lines[j])
                j += 1
            i = j
            joined = "\n".join(block)
            if ":=" not in joined:
                continue
            sig, rhs = joined.split(":=", 1)
            name = m.group(2)
            rhs = " ".join(rhs.split())
            if not rhs:
                continue
            binders = []
            for grp in re.findall(r"\(([^()]*?):[^()]*?\)", sig):
                binders += [b for b in grp.split() if IDENT.fullmatch(b)]
            norm = rhs
            for k, b in enumerate(binders):
                norm = re.sub(r"(?<![\w'.])" + re.escape(b) + r"(?![\w'])",
                              "@%d" % k, norm)
            # Two bodies of the same SHAPE at different TYPES are not the same map.
            # `seqDist : Hap → Hap → Nat` and `antiKronecker : α → α → ℝ` both read
            # `if a = b then 0 else 1`, and collapsing them would be a type error
            # wearing an arithmetic coincidence. The result type joins the key.
            result = sig.rsplit(":", 1)[-1].strip() if ":" in sig else ""
            if "@" in norm and "Descent.Core." not in norm:
                bodies[(norm, result)].append((name, mod))
    groups = [v for v in bodies.values() if len(v) > 1]
    return sum(len(v) - 1 for v in groups), len(groups)


def gate_cross_module_reuse(code, decls):
    """Fraction of theorems cited by CODE in some other module.

    A corpus of independent monographs and a corpus with a spine are the same
    size and the same soundness; this is the number that tells them apart.
    """
    owner = {}
    for mod, found in decls.items():
        for kind, name in found:
            if kind in ("theorem", "lemma"):
                owner.setdefault(name, mod)
    cited = set()
    for mod, text in code.items():
        for w in IDENT.findall(text):
            home = owner.get(w)
            if home is not None and home != mod:
                cited.add(w)
    total = len(owner)
    return len(cited), total


# A demographic quantity is one that takes a population history -- an effective
# size, a rate, a divergence time, a deme count -- and a metric is one a
# deployment reports.  A theorem naming both is a link in the chain; a theorem
# naming only the second takes `fst` as a free real and says nothing about
# where that number came from.
DEMOG = ("fstIslandEquilibrium", "fstEquilibrium", "fstMigrationDriftEquilibrium",
         "fstMutationDriftEquilibrium", "fstMigrationMutationEquilibriumManyDemes",
         "fstIslandEquilibriumFiniteDemes", "scaledMigrationRate",
         "scaledMutationRate", "heterozygosityLossFromDrift", "hetRecurrence",
         "fstFromTau", "fstTransientAt", "PopGenParameters", "islandDemeCorrection",
         "momentsUnderDrift", "deployedR2", "fstTransient", "coalFst",
         "hetMutationDriftRecurrence", "fstFromGenerations")
METRIC = ("r2", "R2", "calibrationSlope", "presentDayR2", "deployedR2", "auc",
          "AUC", "brier", "Brier", "ScoreMoments", "momentsUnderDrift",
          "portabilityStatistic", "r2OfStatistic", "slopeOfStatistic",
          "presentDaySignalToNoise", "presentDayPGSVariance", "targetR2",
          "pgsVariance", "sharedLD")


def gate_composition_count(code, decls):
    """Theorems whose statement mentions BOTH a demographic quantity and a metric.

    Before the Core layer this stood at 2 out of 5,852: the population genetics
    and the deployed metrics were two developments sharing a namespace, joined by
    a rope bridge.  Everything else took `fst` as a free real.
    """
    hits = []
    for mod, text in code.items():
        for m in re.finditer(
                r"^\s*(?:@\[[^\]]*\]\s*)?(?:theorem|lemma)\s+([\w.'₀-₉]+)"
                r"(.*?):=", text, re.S | re.M):
            stmt = m.group(2)
            if any(d in stmt for d in DEMOG) and any(k in stmt for k in METRIC):
                hits.append((m.group(1), mod))
    return hits


def gate_falsified_acknowledged(raw):
    """Every FALSIFIED ledger row must be acknowledged in its declaration's docstring.

    The corpus is mostly honest about its failures -- but "mostly" is a
    convention, and a convention is what this file exists to replace.  A
    declaration the simulation refutes and the prose does not mention is the one
    failure mode that costs a reader nothing to miss.
    """
    ledger = os.path.join(ROOT, "validation", "empirical", "simcov", "ledger.json")
    if not os.path.exists(ledger):
        return []
    with open(ledger, encoding="utf-8") as fh:
        rows = json.load(fh).get("records", [])
    falsified = {r["declaration"] for r in rows
                 if r.get("verdict") == "FALSIFIED" and r.get("role") == "corpus"}
    silent = []
    for name in sorted(falsified):
        # find the module that declares it, then look at the whole file: the
        # acknowledgement may sit on a sibling or in a section header, and
        # either is a reader reaching it.
        acknowledged = False
        declared = False
        for mod, text in raw.items():
            if re.search(r"^\s*(?:noncomputable\s+)?(?:def|abbrev)\s+" +
                         re.escape(name) + r"\b", text, re.M):
                declared = True
                if re.search(r"FALSIFIED|falsif", text) and name in text:
                    acknowledged = True
        if declared and not acknowledged:
            silent.append(name)
    return silent


def gate_orphans(code, decls):
    """Definitions and structures nothing in the CODE refers to, and structures with no
    constructed witness.

    Both counts are much smaller than a naive census suggests, and the difference is the
    point. Counting references in the raw source finds every declaration "used", because
    the prose mentions names constantly; counting in stripped code and matching short
    names against a declaration index finds the real orphans. The corpus's own note on
    deleting a definition -- grep the full tree INCLUDING the root and the validation
    Python, and grep the prose, before removing anything -- is why this reports rather
    than removes.

    A structure with no constructed witness is the other half: a theorem quantified over
    an uninhabited structure is true, kernel-checked, and empty.

    `Prop`-valued structures are excluded, and the exclusion is not a convenience. A
    `structure ... : Prop` is a bundle of HYPOTHESES -- `DynamicsObstructions` bundles
    eight independent obstruction claims, `PolygenicContinuumCalibrationLaw` is
    parameterised over arbitrary weight and posterior families. Demanding a constructed
    inhabitant of each would demand discharging every theorem the corpus states
    conditionally, which is not what this gate is about. What it is about is a DATA
    record with fields no value ever fills: there, the fields describe a thing that has
    never been exhibited.
    """
    owner = {}
    for mod, found in decls.items():
        for kind, name in found:
            if kind in ("def", "abbrev", "structure", "inductive", "class"):
                owner.setdefault(name, (mod, kind))
    used = collections.Counter()
    for mod, text in code.items():
        for w in IDENT.findall(text):
            if w in owner:
                used[w] += 1
    # one occurrence is the declaration itself
    orphans = sorted(n for n, (m, k) in owner.items() if used[n] <= 1 and n)

    # A structure header may wrap over several lines before its `: Prop where`.
    # Scan line-wise from each header rather than with a multi-line regex: the
    # obvious backtracking pattern for this is exponential on real headers.
    prop_structures = set()
    for mod, text in code.items():
        lines = text.split("\n")
        for i, line in enumerate(lines):
            m = re.match(r"\s*structure\s+([A-Za-z_][\w.'₀-₉]*)", line)
            if not m:
                continue
            header = " ".join(lines[i:i + 6])
            head = header.split(" where")[0]
            if re.search(r":\s*Prop\b", head):
                prop_structures.add(m.group(1).split(".")[-1])
    structures = {n for n, (m, k) in owner.items()
                  if k == "structure" and n not in prop_structures}
    # Scan declaration blocks rather than the flat text.  A witness declaration
    # routinely wraps -- `def N.witness :` on one line, `N (args) where` on the next --
    # so a per-line match misses it, and a flat regex either crosses into the next
    # declaration or trips over the colons inside a type ascription.  Both failure modes
    # were live: one reported an inhabited structure as empty, the other the reverse.
    witnessed = set()
    starter = re.compile(r"^\s*(?:noncomputable\s+)?(?:def|abbrev|instance)\b")
    ender = re.compile(r"^\s*(?:@\[|noncomputable |def |abbrev |theorem |lemma |structure "
                       r"|inductive |instance |class |end |namespace |section )")
    for mod, text in code.items():
        lines = text.split("\n")
        i = 0
        while i < len(lines):
            if not starter.match(lines[i]):
                i += 1
                continue
            j = i + 1
            while j < len(lines) and lines[j].strip() and not ender.match(lines[j]):
                j += 1
            block = " ".join(" ".join(lines[i:j]).split())
            head = block.split(":=")[0]
            for n in structures:
                if re.search(r"(?<![\w.'])" + re.escape(n) + r"(?![\w'])", head) and \
                   ("where" in block or re.search(r":=\s*[⟨{]", block)):
                    witnessed.add(n)
            i = j
    witnessless = sorted(structures - witnessed)
    return orphans, witnessless


# --------------------------------------------------------------------------


def measure():
    raw, code = load()
    graph = import_graph(raw)
    depth = depths(graph)
    indeg = in_degrees(graph)
    decls = declarations(code)

    dup_extra, dup_groups = gate_duplicate_bodies(code)
    reused, total_thms = gate_cross_module_reuse(code, decls)
    comps = gate_composition_count(code, decls)
    inverted, thin = gate_foundation_position(raw, graph, depth, indeg)
    silent = gate_falsified_acknowledged(raw)
    orphans, witnessless = gate_orphans(code, decls)

    return {
        "modules": len(graph),
        "theorems": total_thms,
        "cross_module_reuse_pct": round(100.0 * reused / total_thms, 2) if total_thms else 0.0,
        "duplicate_body_groups": dup_groups,
        "duplicate_body_extras": dup_extra,
        "composition_theorems": len(comps),
        "foundation_inverted": len(inverted),
        "foundation_not_yet_load_bearing": len(thin),
        "silent_falsifications": len(silent),
        "orphan_definitions": len(orphans),
        "witnessless_structures": len(witnessless),
        "_offenders": inverted,
        "_thin": thin,
        "_silent": silent,
        "_orphans": orphans,
        "_witnessless": witnessless,
        "_compositions": [f"{n}  ({m})" for n, m in sorted(comps)],
    }


# Every one of these must be ZERO.  There is no direction and no allowance: a
# non-zero count is a defect the corpus still carries.
DEFECTS = {
    "foundation_inverted":
        "modules claiming to reconcile subsystems while depending on them",
    "duplicate_body_groups":
        "shapes written out under more than one name instead of wrapping a kernel",
    "duplicate_body_extras":
        "definitions that re-type a shared body",
    "orphan_definitions":
        "definitions no code refers to",
    "witnessless_structures":
        "structures with no constructed inhabitant, over which theorems are empty",
    "silent_falsifications":
        "FALSIFIED ledger rows no docstring mentions",
}

# Reported, never gated.  These are properties of the corpus, not defect counts:
# there is no value of "theorems cited across modules" that is correct, and a
# threshold on one would be a number someone picked.
REPORTED = ("cross_module_reuse_pct", "composition_theorems", "modules", "theorems",
            # Correct position, few consumers.  A new foundation starts here and
            # earns callers as they move over; it is not the inversion above.
            "foundation_not_yet_load_bearing")


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--gate", action="store_true",
                    help="exit nonzero unless every defect count is zero")
    ap.add_argument("--verbose", action="store_true",
                    help="name every offender behind every count")
    args = ap.parse_args()

    now = measure()

    print("architecture")
    for k in sorted(now):
        if k.startswith("_"):
            continue
        mark = "" if k in REPORTED else ("  OK" if now[k] == 0 else "  <- must be 0")
        print(f"  {k:34} {now[k]}{mark}")

    if args.verbose:
        if now["_offenders"]:
            print("\nINVERTED -- claims a foundational role from above what it reconciles:")
            for o in now["_offenders"]:
                print(f"  depth {o['depth']:>2}  in-degree {o['in_degree']:>2}  "
                      f"imports {o['imports_subsystems']} subsystem module(s), "
                      f"e.g. {o['example']}\n      {o['module']}")
        if now["_thin"]:
            print("\npositioned correctly, not yet load-bearing (in-degree < 5):")
            for o in now["_thin"]:
                print(f"  depth {o['depth']:>2}  in-degree {o['in_degree']:>2}  {o['module']}")
        if now["_silent"]:
            print("\nFALSIFIED with no acknowledgement in the declaring file:")
            for n in now["_silent"]:
                print("  " + n)
        if now["_orphans"]:
            print("\ndefinitions no code refers to:")
            for n in now["_orphans"]:
                print("  " + n)
        if now["_witnessless"]:
            print(f"\nstructures with no constructed inhabitant ({len(now['_witnessless'])}):")
            for n in now["_witnessless"]:
                print("  " + n)
        print(f"\ncomposition theorems ({len(now['_compositions'])}):")
        for c in now["_compositions"]:
            print("  " + c)

    if not args.gate:
        return 0

    failures = [(k, now[k], what) for k, what in DEFECTS.items() if now[k] != 0]
    for k, n, what in sorted(failures):
        print(f"FAIL  {k}: {n}  ({what})", file=sys.stderr)
    if failures:
        print("\nrun with --verbose to name every offender", file=sys.stderr)
        return 1
    print("\nevery defect count is zero")
    return 0


if __name__ == "__main__":
    sys.exit(main())
