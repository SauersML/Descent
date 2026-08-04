"""Find definitions the corpus itself declares cannot be measured as stated.

`selectedDriftFactor` cost a battery before its docstring was read:

    `s_correction` is a free knob, not a derived quantity. Nothing in this file
    or the corpus defines it in terms of a selection coefficient, a fitness
    function, or a stabilizing-selection model.

A parameter with no operational definition cannot be set in a simulation without
inventing a meaning for it, and whatever the simulation then measures is a
property of the invention. Battery 20 invented a per-generation restoring term,
and the cells where that invention bit disagreed at nine sems while the cell
where it did not bite agreed at 0.02 -- a perfect signature of a design testing
itself rather than the definition.

Such a definition is not UNTESTED in the sense of awaiting a measurement. It is
UNMEASURABLE until the missing derivation is supplied, and the difference
matters for the coverage denominator: counting it as an outstanding measurement
overstates what remains to be done, exactly as counting witnesses did.

This scan finds the ones whose own docstrings say so. It reports rather than
edits, and it prints the sentence it matched on so every hit can be checked
against the text that produced it -- a screen that summarises without quoting is
one nobody can audit.
"""
import os
import re
import sys

ROOT = sys.argv[1] if len(sys.argv) > 1 else "proofs/Calibrator"

# Phrases in which the corpus admits a quantity is not pinned down. Each is
# taken from text that actually appears; none is speculative.
ADMISSION = re.compile(
    r"free knob|not a derived quantity|has not been done|"
    r"nothing in this file or the corpus defines it|"
    r"is assumed rather than derived|conditional on the assumption|"
    r"no operational definition|not identifiable from|"
    r"cannot be measured|is a modelling choice|is an ansatz|"
    r"stipulated rather than derived", re.I)


def lean_files(root):
    import glob
    fs = (glob.glob(os.path.join(root, "*.lean")) +
          glob.glob(os.path.join(root, "*", "*.lean")))
    extra = root.rstrip("/") + ".lean"
    if os.path.exists(extra):
        fs.append(extra)
    return sorted(fs)


def main():
    hits = []
    for f in lean_files(ROOT):
        raw = open(f, errors="ignore").read()
        for m in re.finditer(
                r"/--((?:(?!-/).)*)-/\s*\n(?:noncomputable )?def ([A-Za-z_0-9'.]+)",
                raw, re.S):
            doc, name = m.group(1), m.group(2).split(".")[-1]
            a = ADMISSION.search(doc)
            if not a:
                continue
            untested = "Empirical status: UNTESTED" in doc
            # the sentence containing the admission, so the hit is auditable
            start = max(0, a.start() - 160)
            frag = " ".join(doc[start:a.end() + 120].split())
            hits.append((name, os.path.basename(f), untested, a.group(0), frag))

    print("definitions whose docstring admits a quantity is not pinned down: %d\n"
          % len(hits))
    still_untested = [h for h in hits if h[2]]
    for name, f, untested, phrase, frag in hits:
        mark = "UNTESTED" if untested else "already marked otherwise"
        print("  %-38s %-34s [%s]" % (name, f, mark))
        print("      matched: \"%s\"" % phrase)
        print("      context: ...%s..." % frag[:150])
    print("\nof these, still carrying Empirical status: UNTESTED: %d"
          % len(still_untested))
    print("Those are the ones counted as an outstanding measurement that no")
    print("measurement can supply until the missing derivation is done.")


if __name__ == "__main__":
    main()
