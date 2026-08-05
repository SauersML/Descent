"""Inventory of the empirical-claim surface in proofs/Calibrator.

Enumerates every `def`, its Empirical status marker, its signature and body, and
whether check.py's own DOMAIN screen considers it an empirical claim.  The point
is a single machine-readable ledger the simulation harness can drive from, so
"coverage" is a computed number over a fixed denominator rather than a grep.
"""
import json
import os
import re
import sys

ROOT = sys.argv[1] if len(sys.argv) > 1 else "proofs/Calibrator"


def lean_files(root):
    """check.py's `ident_lean_files`: top level plus exactly one subdir level,
    plus the corpus root `Calibrator.lean`.  Kept identical on purpose -- a
    denominator that disagrees with the guard's is a coverage number nobody can
    check against the build."""
    import glob as _glob
    fs = (_glob.glob(os.path.join(root, "*.lean")) +
          _glob.glob(os.path.join(root, "*", "*.lean")))
    extra = root.rstrip("/") + ".lean"
    if os.path.exists(extra):
        fs.append(extra)
    return sorted(fs)


# check.py's screen, transcribed verbatim so the denominator matches the guard.
DOMAIN = re.compile(
    r"fst|drift|selection|herit|linkage|allele|geno|migrat|coalesc|mutation|"
    r"epistat|domin|recomb|ancestr|spike|admix|haplo|polygenic|prevalence|"
    r"liability|penetrance|pgs|gwas|singleton|winners|power|ncp|effect", re.I)
DOMAIN_CASED = re.compile(r"^ld|(?:^|[a-z0-9])LD(?=[A-Z_]|$)")
# check.py's `mult`: a ploidy convention is a 2 or a 4 ADJACENT to a
# population-genetic parameter, not any decimal anywhere in a body.  The loose
# reading counted 164 extra defs as undeclared empirical claims that the guard
# never screens -- a denominator the build would contradict.
POP = (r"(?:Ne|N|N_b|N₀|N₁|mu|μ|m|m_rate|m_into|mig|p|p0|p₁|p₂|p_bar|maf|fst|"
       r"freq|theta|θ|sigma_sq)")
MULT = re.compile(r"(?<![\^A-Za-z_0-9.])[24]\s*\*\s*(?:\([^)]*\)|[A-Za-z_0-9.]*\.)?" + POP + r"\b"
                  r"|/\s*\(\s*[24]\s*\*\s*(?:[A-Za-z_0-9.]*\.)?" + POP + r"\b"
                  r"|\b(?:[A-Za-z_0-9]+\.)?" + POP + r"\s*\*\s*[24]\b")

DEF_RE = re.compile(r"^(?:noncomputable\s+)?def\s+([A-Za-z_][\w.']*)")
# Statuses are written with markdown emphasis (`Empirical status: **VALIDATED**`)
# and a docstring may carry two of them ("VALIDATED at linkage equilibrium; the
# unconditional reading is FALSIFIED").  A parser that stops at the first
# `[A-Za-z]+` after the colon reads `**VALIDATED**` as no status at all, which is
# how nine measured definitions looked undeclared.
STATUS_RE = re.compile(r"Empirical status:\s*[*_ ]*([A-Za-z_]+)")
STATE_WORDS = ("UNTESTED", "VALIDATED", "FALSIFIED", "DERIVED", "MEASURED",
               "VACUOUS", "CONVENTION", "TESTED", "REFUTED")


def strip_comments(src):
    """Remove block comments but keep line count, so indices stay aligned."""
    out, i, depth = [], 0, 0
    while i < len(src):
        if src.startswith("/-", i):
            depth += 1
            i += 2
        elif src.startswith("-/", i) and depth:
            depth -= 1
            i += 2
        elif depth:
            out.append("\n" if src[i] == "\n" else " ")
            i += 1
        else:
            out.append(src[i])
            i += 1
    return "".join(out)


def preceding_doc(lines, i):
    """The /-- ... -/ docstring immediately above line i, if any."""
    j = i - 1
    while j >= 0 and (not lines[j].strip() or lines[j].lstrip().startswith("@[")):
        j -= 1
    if j < 0 or not lines[j].rstrip().endswith("-/"):
        return ""
    end = j
    while j >= 0 and "/--" not in lines[j]:
        # A `/-! -/` section header is not this declaration's docstring.
        if "/-!" in lines[j] or ("-/" in lines[j] and j != end):
            return ""
        j -= 1
    return "\n".join(lines[max(0, j):end + 1])


def main():
    records = []
    for f in lean_files(ROOT):
        raw = open(f, errors="ignore").read()
        raw_lines = raw.split("\n")
        stripped_lines = strip_comments(raw).split("\n")
        for i, line in enumerate(stripped_lines):
            # NOT `line.strip()`: check.py anchors at column 0, so only
            # top-level defs are in the guard's screen.  Stripping pulls in
            # `let`-scoped and section-indented defs the guard never sees and
            # inflates the denominator (measured: 1566 vs 604).
            m = DEF_RE.match(line)
            if not m:
                continue
            name = m.group(1)
            short = name.split(".")[-1]
            body = "\n".join(stripped_lines[i:i + 6])
            body = body.split(":=", 1)[1] if ":=" in body else ""
            doc = preceding_doc(raw_lines, i)
            declared = "Empirical status:" in doc
            sm = STATUS_RE.search(doc)
            status = sm.group(1).upper() if sm else None
            # The tail after the marker may qualify or reverse the headline
            # ("VALIDATED at linkage equilibrium; the unconditional reading is
            # FALSIFIED"), so record every state word the note uses, not just
            # the first.  A definition both validated and falsified is a
            # different object from one that is merely validated.
            tail = doc[doc.index("Empirical status:"):] if declared else ""
            states = [w for w in STATE_WORDS if re.search(r"\b" + w + r"\b", tail)]
            if status not in STATE_WORDS:
                # "NOT ..." / "CONDITIONALLY ..." / free prose: not a state on
                # its own, but the note may still name one further along.
                status = states[0] if states else (
                    "FREETEXT:" + status if status else None)
            empirical = bool(DOMAIN.search(short) or DOMAIN_CASED.search(short)
                             or MULT.search(re.sub(r"\^\s*[0-9]+", "", body)))
            records.append({
                "name": name,
                "short": short,
                "file": f,
                "line": i + 1,
                "status": status,
                "states": states,
                "declared": declared,
                "empirical_claim": empirical,
                # Read off the FULL docstring, not the truncated `doc` below.
                # The truncation keeps the last 1200 characters for JSON size,
                # and a status marker sits at the TOP of a docstring, so any
                # declaration whose evidence paragraph runs past 1200 characters
                # had its verdict silently cropped out of the record.
                # `PolygenicArchitecture.spikeAndSlabVariance` was the one that
                # showed it: declared NOT AN EMPIRICAL CLAIM, counted as a
                # FALSIFIED measurement, because the only state word left inside
                # the window came from a retracted battery quoted in its history.
                "nonclaim": "NOT AN EMPIRICAL CLAIM" in doc,
                "doc": doc[-1200:],
                "body": body.strip()[:600],
            })

    json.dump(records, open("inventory.json", "w"), indent=1)

    total = len(records)
    emp = [r for r in records if r["empirical_claim"]]
    by_status = {}
    for r in emp:
        by_status[r["status"]] = by_status.get(r["status"], 0) + 1
    print("defs total:                %d" % total)
    print("defs making empirical claim: %d" % len(emp))
    print("\nempirical-claim defs by status:")
    for k, v in sorted(by_status.items(), key=lambda kv: -kv[1]):
        print("  %-22s %4d" % (k, v))

    measured = sum(v for k, v in by_status.items()
                   if k in {"VALIDATED", "FALSIFIED", "MEASURED", "TESTED"})
    # A definition that declares itself NOT AN EMPIRICAL CLAIM is not owed a
    # measurement, so counting it in the denominator understates what has been
    # established. The screen that builds `emp` reads names and bodies, not
    # status, so the exclusion has to happen here -- and both numbers are
    # printed, because a denominator that moved is a denominator a reader must
    # be able to audit.
    nonclaim = [r for r in emp if r["nonclaim"]]
    # A declaration cannot be both not-a-claim and measured; the `status` of a
    # non-claim is whatever state word its prose quotes, which is history and
    # not a verdict.  Counting one in the numerator credits the corpus with a
    # measurement nobody made.
    measured -= sum(1 for r in nonclaim
                    if r["status"] in {"VALIDATED", "FALSIFIED", "MEASURED", "TESTED"})
    claimable = len(emp) - len(nonclaim)
    print("\ndeclared NOT AN EMPIRICAL CLAIM (witnesses): %d" % len(nonclaim))
    for r in nonclaim:
        print("    %s  (%s)" % (r["short"], r["file"].split("/")[-1]))
    print("\nMEASURED / all screened:        %d / %d  (%.1f%%)"
          % (measured, len(emp), 100.0 * measured / max(len(emp), 1)))
    print("MEASURED / measurable claims:   %d / %d  (%.1f%%)"
          % (measured, claimable, 100.0 * measured / max(claimable, 1)))
    print("wrote inventory.json")


if __name__ == "__main__":
    main()
