#!/usr/bin/env python3
"""Check the regime obligation stated in Calibrator/Conventions.lean.

A closed form whose docstring reads `Empirical status: FALSIFIED` or
`CONDITIONALLY VALID` makes two claims: an algebraic one, which Lean checks, and a
claim about the conditions under which the algebra describes a population, which
Lean checks only if someone writes it down. `DriftRegime.lean` records why that
matters: a formula carrying its regime in prose can be moved into a regime where it
is false, and every internal cross-check still passes, because the identities are
identities *in* the shared premise.

This script checks that every such closed form carries its regime in one of the four
forms Conventions.lean names:

  signature       the definition takes a structure with an assumption field
  regime-tie      a theorem identifies it with a quantity of a named regime object
  obligation      the claimed quantity is a caller-supplied field (PowerAgreement shape)
  proved-failure  the departure from the regime is itself a theorem

It is a structural check, not a proof check: it confirms a witness of the right shape
exists and is named, not that the witness type-checks. Compilation is what establishes
the latter. Exit status is 1 if any closed form is uncovered.

Run:  python3 proofs/validation/invariants/check_regimes.py
"""

import os
import re
import sys

ROOT = os.path.join(os.path.dirname(__file__), "..", "..", "Calibrator")

# `→` is deliberately excluded: it appears in every function type and would make
# any data field look like an assumption.
PROP = r"[=≤<≥>≠∀∃↔]"
REGIME_OBJECT = (
    r"(closedPopulation|mutationDriftBalance|Regime|Limit\b|Agreement"
    r"|FittedSelectionLaw|MomentReading|processAUC)"
)
FAILURE = (
    r"(cannot_reach|_excess|indistinguishable|negative_of|vacuous|_lt_"
    r"|_le_inv|not_reach|_eq_of_lt_one)"
)


def strip_comments(text):
    """Remove docstrings and block comments so prose cannot look like a declaration."""
    return re.sub(r"/-[-!]?(?:.|\n)*?-/", "", text)


def load():
    sources = {}
    for base, _, names in os.walk(ROOT):
        for name in names:
            if name.endswith(".lean"):
                path = os.path.join(base, name)
                with open(path, encoding="utf-8") as handle:
                    sources[path] = handle.read()
    return sources


def collect(sources):
    code = {p: strip_comments(s) for p, s in sources.items()}

    carriers = {}
    for text in code.values():
        for m in re.finditer(
            r"^structure\s+([\w.']+)[^\n]*\swhere\n((?:[ \t]+[^\n]*\n|\n)*)", text, re.M
        ):
            fields = re.findall(r"^[ \t]+([\w']+)\s*:[^\n]*" + PROP, m.group(2), re.M)
            if fields:
                carriers[m.group(1)] = fields[0]

    theorems = []
    for text in code.values():
        for m in re.finditer(
            r"^(?:@\[[^\]]*\]\s*)?theorem\s+([\w.']+)((?:.|\n)*?):=", text, re.M
        ):
            theorems.append((m.group(1), m.group(2)))

    forms = []
    for path, text in sources.items():
        for m in re.finditer(
            r"(/--(?:.|\n)*?-/)\n"
            r"((?:noncomputable |private |protected )*(?:def|abbrev)\s+([\w.']+))"
            r"((?:.|\n)*?):=",
            text,
        ):
            doc = m.group(1)
            if "FALSIFIED" in doc or "CONDITIONALLY VALID" in doc:
                forms.append((m.group(3), m.group(4), os.path.basename(path)))
    return carriers, theorems, sorted(set(forms))


def witness(name, signature, carriers, theorems, forms, depth=0, seen=None):
    seen = seen or set()
    if name in seen or depth > 2:
        return None
    seen.add(name)
    last = name.split(".")[-1]

    for struct, field in carriers.items():
        if struct in signature or name.startswith(struct + "."):
            return "signature %s.%s" % (struct, field)

    mentions = re.compile(r"(?<![\w'])" + re.escape(last) + r"(?![\w'])")
    for tname, tstmt in theorems:
        if (mentions.search(tname) or mentions.search(tstmt)) and re.search(
            REGIME_OBJECT, tname + tstmt
        ):
            return "regime-tie %s" % tname
    for tname, tstmt in theorems:
        if (mentions.search(tname) or mentions.search(tstmt)) and re.search(
            FAILURE, tname
        ):
            return "proved-failure %s" % tname

    # One closed form may inherit its regime from another it is equated to.
    for tname, tstmt in theorems:
        if not (mentions.search(tname) or mentions.search(tstmt)):
            continue
        for other, other_sig, _ in forms:
            if other == name:
                continue
            if re.search(
                r"(?<![\w'])" + re.escape(other.split(".")[-1]) + r"(?![\w'])", tstmt
            ):
                found = witness(
                    other, other_sig, carriers, theorems, forms, depth + 1, seen
                )
                if found:
                    return "via %s: %s" % (other, found)
    return None


def main():
    sources = load()
    if not sources:
        print("no Lean sources found under %s" % ROOT)
        return 1
    carriers, theorems, forms = collect(sources)

    uncovered = []
    print("%-46s %s" % ("closed form", "regime carrier"))
    print("-" * 104)
    for name, signature, _ in forms:
        found = witness(name, signature, carriers, theorems, forms)
        if not found:
            uncovered.append(name)
        print("%-46s %s" % (name, found or "*** NONE ***"))

    print(
        "\n%d closed forms marked FALSIFIED or CONDITIONALLY VALID; %d without a carrier"
        % (len(forms), len(uncovered))
    )
    if uncovered:
        print(
            "\nEach of these asserts a regime no theorem states. Give it one of the four\n"
            "forms above, or drop the empirical-status claim from its docstring."
        )
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
