"""Inventory of the empirical-claim surface in Descent.

Enumerates every `def`, its Empirical status marker, its signature and body, and
whether check.py's own DOMAIN screen considers it an empirical claim.  The point
is a single machine-readable ledger the simulation harness can drive from, so
"coverage" is a computed number over a fixed denominator rather than a grep.
"""
import json
import os
import re
import sys

ROOT = sys.argv[1] if len(sys.argv) > 1 else "Descent"


def lean_files(root):
    """check.py's `ident_lean_files`: every corpus file at ANY depth, plus the
    corpus root `Descent.lean`.  Kept identical on purpose -- a denominator that
    disagrees with the guard's is a coverage number nobody can check against the
    build.

    THIS USED TO GLOB EXACTLY TWO LEVELS, and kept doing so after
    `ident_lean_files` was fixed to recurse.  The two then disagreed in the one
    direction that is invisible: 68 of the corpus's 291 files sit at depth three
    or more, every declaration in them dropped out of BOTH the numerator and the
    denominator, and the metric read 100% over a corpus with a quarter of its
    files missing.  A denominator can only be trusted when the walk that builds
    it is the walk the guard uses, so the exclusions are transcribed too:
    AppleDouble `._*` files and dotfiles (`.lake/` is the vendored Mathlib
    checkout) are not corpus, and `lakefile.lean` is build configuration.
    """
    fs = []
    for dirpath, subdirs, names in os.walk(root):
        subdirs[:] = [d for d in subdirs if not d.startswith(".")]
        for name in names:
            if name.endswith(".lean") and not name.startswith(".") \
                    and name != "lakefile.lean":
                fs.append(os.path.join(dirpath, name))
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
# A module-level `## Empirical status` section inside a `/-! ... -/` header.
MODULE_STATUS = re.compile(r"(?:^|\n)##+[ \t]*Empirical status\b")
# Statuses are written with markdown emphasis (`Empirical status: **VALIDATED**`)
# and a docstring may carry two of them ("VALIDATED at linkage equilibrium; the
# unconditional reading is FALSIFIED").  A parser that stops at the first
# `[A-Za-z]+` after the colon reads `**VALIDATED**` as no status at all, which is
# how nine measured definitions looked undeclared.
# A QUOTED MENTION IS NOT A DECLARATION. `Empirical status:` also occurs inside
# ordinary prose -- `Descent/Core/Ratios.lean` said "This file must never
# acquire an `Empirical status:` line" -- and reading the characters after it as
# a status counted a docstring that declares it has no status as one that owes a
# measurement, and reported "` line" as a verdict outside the closed vocabulary.
#
# The discriminator is the BACKTICK, and only the backtick. Anchoring at the
# start of a line instead was tried and is wrong in both directions: a real
# marker sits on the `/--` opening line in `integratedCoalescentHazard` and
# mid-line after a bolded sentence in `freeRecombinationStep`, and both are
# genuine verdicts. The corpus quotes the phrase when talking ABOUT it and
# never when asserting one.
DECLARES_STATUS = re.compile(r"(?<!`)Empirical status:")
STATUS_RE = re.compile(r"(?<!`)Empirical status:\s*[*_ ]*([A-Za-z_]+)")
STATE_WORDS = ("UNTESTED", "VALIDATED", "FALSIFIED", "DERIVED", "MEASURED",
               "VACUOUS", "CONVENTION", "TESTED", "REFUTED")

# `CONVENTION PINNED` is a TWO-WORD head from the closed vocabulary, and
# `CONVENTION` on its own is not a term at all. Reading only the first word
# files it under the bare state word, which is in neither the measured set nor
# the owed set, so `neiGstFromFrequencies` and `neiContrastSpike` -- both of
# which state a pinned convention and cite the differential checks that confirm
# it -- were counted as coverage debt. The head is matched before the state
# words, longest first.
VOCAB_MULTIWORD = ("CONVENTION PINNED",)

# Complete verdicts from the closed vocabulary that are NOT single state words.
# A docstring leading with one of these has already classified itself, so the
# prose after it must not be mined for a state word: the note is explaining the
# verdict, and it very often names the state it is REFUTING.  Kept in sync with
# `empirical_status_vocabulary` in `validation/conventions.json`.
VOCAB_NONSTATE = (
    "NOT AN EMPIRICAL CLAIM",
    "NOT EMPIRICALLY TESTABLE",
    "NOT TESTED BY THE DESIGN THAT LOOKED LIKE IT WAS",
    "CONDITIONALLY VALID",
    "EXACT BY CONSTRUCTION",
    "AN IDENTITY",
    "DISAGREES WITH AN EXISTING MEASUREMENT",
    "CONVENTION PINNED",
    "ASSERTED",
    "MIXED",
)


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


def skip_attribute_block(lines, j):
    """check.py's `skip_attribute_block`, transcribed: walk `j` back past blank
    lines and whole `@[...]` blocks, which are NOT always one line.

    Skipping only lines that themselves begin with `@[` catches every `@[simp]`
    and no `@[withdrawn "tag" "a sentence of justification"]`; that form wraps,
    so the line above the declaration is the tail of a string argument, the
    docstring above it fails the `-/` test, and a declaration that documents its
    status in detail is read as declaring none.
    """
    while j >= 0:
        if not lines[j].strip() or lines[j].lstrip().startswith("@["):
            j -= 1
            continue
        if not lines[j].rstrip().endswith("]"):
            break
        depth, k = 0, j
        while k >= 0:
            depth += lines[k].count("]") - lines[k].count("[")
            if depth <= 0:
                break
            k -= 1
        if k < 0 or depth != 0 or not lines[k].lstrip().startswith("@["):
            break
        j = k - 1
    return j


def preceding_doc(lines, i):
    """The /-- ... -/ docstring immediately above line i, if any."""
    j = skip_attribute_block(lines, i - 1)
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
        # A MODULE MAY DECLARE ONE FOR ALL OF ITS DECLARATIONS. `Descent/Core/
        # Fst.lean` opens with a `## Empirical status` section saying "None. The
        # bodies here are algebra ... what carries an empirical status is a
        # named quantity in a subsystem module", which is the right verdict,
        # stated once where it belongs. Nothing could see it, so five
        # declarations that share it were counted as coverage debt.
        #
        # `check.py`'s `ident` guard was taught the same rule in the same
        # commit. A denominator that disagrees with the guard is a coverage
        # number nobody can check, and that is the whole reason this file
        # transcribes the guard's screen rather than inventing one.
        module_declared = bool(MODULE_STATUS.search(raw))
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
            declared = bool(DECLARES_STATUS.search(doc))
            sm = STATUS_RE.search(doc)
            status = sm.group(1).upper() if sm else None
            # The tail after the marker may qualify or reverse the headline
            # ("VALIDATED at linkage equilibrium; the unconditional reading is
            # FALSIFIED"), so record every state word the note uses, not just
            # the first.  A definition both validated and falsified is a
            # different object from one that is merely validated.
            tail = doc[DECLARES_STATUS.search(doc).start():] if declared else ""
            head_text = re.sub(r"^[\s*_]*Empirical status:\s*[*_ ]*", "",
                               tail).upper()
            multiword = any(head_text.startswith(v) for v in VOCAB_MULTIWORD)
            states = [w for w in STATE_WORDS if re.search(r"\b" + w + r"\b", tail)]
            # `multiword` first: a two-word head whose first word happens to be
            # a state word (`CONVENTION PINNED` against `CONVENTION`) would
            # otherwise never reach the vocabulary branch below at all.
            if multiword or status not in STATE_WORDS:
                # "NOT ..." / "CONDITIONALLY ..." / free prose: not a state on
                # its own, but the note may still name one further along.
                #
                # UNLESS the headline is itself a COMPLETE verdict from the
                # closed vocabulary.  Scanning the tail then reads a state word
                # the note MENTIONS rather than asserts, and the two are not
                # distinguishable to a regex.  That is not hypothetical: every
                # `ldWitness*` in DGP declares `NOT AN EMPIRICAL CLAIM` and then
                # explains "an UNTESTED marker here reads as an unpaid debt and
                # is not one" -- so the word it is REFUTING became its status,
                # and nine definitions that can never receive a measurement were
                # counted as owing one.  A docstring is penalised for arguing
                # its own case.
                if any(head_text.startswith(v) for v in VOCAB_NONSTATE):
                    status = "FREETEXT:" + status
                else:
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
                "module_declared": module_declared,
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

    # A verdict from the closed vocabulary counts as measured even when it is
    # not a single state word.  CONDITIONALLY VALID, MIXED, AN IDENTITY and
    # DISAGREES WITH AN EXISTING MEASUREMENT are all the OUTCOME of a
    # measurement -- a regime-restricted validation is a validation, and a
    # two-part verdict is two findings, not none.  Only the NOT-family is
    # outside this, and that family leaves the denominator entirely rather than
    # sitting in it unmeasured.
    MEASURED_STATES = {"VALIDATED", "FALSIFIED", "MEASURED", "TESTED",
                       "FREETEXT:CONDITIONALLY", "FREETEXT:MIXED",
                       "FREETEXT:AN", "FREETEXT:DISAGREES",
                       "FREETEXT:EXACT", "FREETEXT:CONVENTION"}
    # VERDICTS THAT SETTLE A DEFINITION WITHOUT A MEASUREMENT, and the reason
    # they are not coverage debt. `validation/conventions.json` defines the
    # closed vocabulary, and it says of these in as many words:
    #
    #   DERIVED   "Follows from other results in the corpus; no measurement is
    #             claimed or needed."
    #   VACUOUS   "The measurement was an algebraic identity and carries no
    #             information about the world."
    #   ASSERTED  "An input taken from external literature rather than derived
    #             or measured here."
    #
    # A denominator that counts them as owed says the corpus is 88.7% covered
    # when the honest reading is that the remaining 11.3% is mostly definitions
    # the vocabulary already settles. But this is exactly the kind of exclusion
    # that can be abused, so it is not free: see `unsubstantiated` below. A
    # DERIVED docstring that names nothing it is derived FROM is an assertion,
    # not a derivation, and stays in the denominator.
    SETTLED_WITHOUT_MEASUREMENT = {"DERIVED", "VACUOUS", "FREETEXT:ASSERTED",
                                   # `THIS IS THE MODEL`: the definition
                                   # CONSTITUTES the model rather than asserting
                                   # anything about a population, so no
                                   # measurement of IT is owed -- the empirical
                                   # question is whether a population is
                                   # described by it, and the term requires the
                                   # docstring to name where that is asked.
                                   # Adjudicated into
                                   # `empirical_status_vocabulary` after turning
                                   # up four times in four files for one meaning
                                   # the other terms cannot express.
                                   "FREETEXT:THIS"}
    measured = sum(v for k, v in by_status.items() if k in MEASURED_STATES)
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
    measured -= sum(1 for r in nonclaim if r["status"] in MEASURED_STATES)
    claimable = len(emp) - len(nonclaim)
    print("\ndeclared NOT AN EMPIRICAL CLAIM (witnesses): %d" % len(nonclaim))
    for r in nonclaim:
        print("    %s  (%s)" % (r["short"], r["file"].split("/")[-1]))

    # THE EXCLUSION HAS A PRICE, and this is it. A DERIVED or VACUOUS marker
    # says "this follows from something else that carries the evidence" -- so
    # the docstring has to NAME that something. A backticked identifier is the
    # weakest check that has any content at all, and it is enough: it is what
    # separates `DERIVED from `ldRetentionPerGen`, which is VALIDATED` from a
    # bare `DERIVED.` that means only that nobody measured it.
    NAMES_A_REFERENT = re.compile(r"`[A-Za-z_][\w.']*`")
    # A declaration inheriting its MODULE's declaration is settled by it, and
    # the module note is the referent -- so it does not need to name one of its
    # own the way a bare `DERIVED` does.
    module_settled = [r for r in emp
                      if not r["nonclaim"] and not r["declared"]
                      and r.get("module_declared")]
    settled = [r for r in emp
               if not r["nonclaim"] and r["status"] in SETTLED_WITHOUT_MEASUREMENT]
    settled = settled + [r for r in module_settled if r not in settled]
    unsubstantiated = [
        r for r in settled
        if r not in module_settled
        and not NAMES_A_REFERENT.search(
            r["doc"][r["doc"].index("Empirical status:"):]
            if "Empirical status:" in r["doc"] else "")]
    # Owed a measurement: everything screened, minus the non-claims, minus the
    # ones the vocabulary settles -- but the unsubstantiated ones come back.
    owed_denominator = (claimable - len(settled) + len(unsubstantiated))

    print("\nsettled without a measurement (DERIVED / VACUOUS / ASSERTED / "
          "THIS IS THE MODEL): %d, of which %d inherit their MODULE's "
          "declaration" % (len(settled), len(module_settled)))
    if unsubstantiated:
        print("  of which UNSUBSTANTIATED -- the marker names nothing it "
              "follows from, so it stays in the denominator: %d"
              % len(unsubstantiated))
        for r in unsubstantiated:
            print("    %s  (%s)" % (r["short"], r["file"].split("/")[-1]))

    owed = [r for r in emp
            if not r["nonclaim"]
            and r["status"] not in MEASURED_STATES
            and (r not in settled or r in unsubstantiated)]
    print("\nOWED A MEASUREMENT AND NOT PAID: %d" % len(owed))
    for r in owed:
        print("    %-46s %-40s status=%s"
              % (r["short"], r["file"].split("/")[-1], r["status"]))

    print("\nMEASURED / all screened:        %d / %d  (%.1f%%)"
          % (measured, len(emp), 100.0 * measured / max(len(emp), 1)))
    print("MEASURED / measurable claims:   %d / %d  (%.1f%%)"
          % (measured, claimable, 100.0 * measured / max(claimable, 1)))
    print("MEASURED / OWED a measurement:  %d / %d  (%.1f%%)"
          % (measured, owed_denominator,
             100.0 * measured / max(owed_denominator, 1)))
    print("wrote inventory.json")


if __name__ == "__main__":
    main()
