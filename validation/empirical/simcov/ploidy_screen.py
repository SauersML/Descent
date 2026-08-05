"""A screen for the missing-ploidy defect that DOES NOT WORK, and why.

Three of the last four defects found by simulation were one mistake: a quantity
on the dosage scale computed without the ploidy factor the score carries.

  polygenicAdaptationShift    sum beta * dp   should be sum beta * ploidy * dp
  pgsDriftVariance_one_pop    fst * V_A       should be 2 * fst * V_A
  expectedPGSDiffVariance     V_A * 2 * fst   should be V_A * 4 * fst

Three instances of one mechanism looks like something a screen could catch
faster than measuring definitions one at a time, so this was written to try.
IT DOES NOT WORK, and the reason is worth keeping rather than rediscovering.

  WITHOUT the `CARRIER` exemption below, the screen flags eight definitions on
  this corpus and seven are false positives. The corpus mostly DELEGATES the
  factor correctly: `additiveVariance` is `sum 2 p (1-p) alpha^2`,
  `expectedAltAlleleCount` is `2p`, `pgsVarianceFromHet` takes the
  heterozygosity as an argument. Flagging those trains a reader to ignore the
  screen, which is the failure `check.py`'s `ld` pattern comment records.

  WITH the exemption, it catches none of the three. `pgsDriftVariance_one_pop`
  is `fst * V_A`, and `V_A` is on the exemption list -- correctly, since `V_A`
  really does carry a ploidy. What that body needed was a SECOND factor, beyond
  the one `V_A` already has, because the variance of a MEAN score picks up
  `ploidy^2` from the effects against `ploidy` inside `V_A`.

The two failures are the same fact from both sides: whether a given occurrence
of `V_A` still owes a ploidy factor depends on WHICH QUANTITY is being
computed -- a genotype variance, a score variance, or the variance of a score's
mean. That is semantics, and no pattern over the body text can recover it.

So this defect class is not screenable, and the way to find the rest of it is
the way the three were found: measure the definition against a simulation that
knows what scale it is on. Kept as a record of the attempt, not as a guard; it
is not wired into `check.py` and should not be.
"""
import os
import re
import sys

ROOT = sys.argv[1] if len(sys.argv) > 1 else "Descent"


def lean_files(root):
    import glob
    fs = (glob.glob(os.path.join(root, "*.lean")) +
          glob.glob(os.path.join(root, "*", "*.lean")))
    extra = root.rstrip("/") + ".lean"
    if os.path.exists(extra):
        fs.append(extra)
    return sorted(fs)


def strip_comments(src):
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


# A name that says the quantity lives on the dosage scale.
DOSAGE_NAME = re.compile(
    r"pgs|score|meanShift|Shift|driftVariance|DiffVariance|geneticVariance|"
    r"additiveVariance|adaptationShift|dosage", re.I)
# An effect-size symbol and a frequency symbol appearing together.
EFFECT = re.compile(r"\bβ\b|\bbeta\b|\beffect\b|V_A", re.I)
FREQ = re.compile(r"\bp\b|\bp_?[a-z]?\b|freq|Δp|dp\b|fst", re.I)
# The ploidy factor, however written. `4` counts because ploidy squared is what
# a variance of a dosage-scale score carries.
PLOIDY = re.compile(r"\bploidy\b|(?<![\w.])[24]\s*\*|\*\s*[24](?![\w.])|\^\s*2")

# Definitions that already carry the ploidy factor inside themselves. A body
# that reaches a frequency ONLY through one of these has delegated the factor
# correctly and is not a defect. Measured: without this list the screen is seven
# false positives out of eight on this corpus, because the corpus does delegate
# -- `additiveVariance` is `sum 2 p (1-p) alpha^2`, `expectedAltAlleleCount` is
# `2p`, and `pgsVarianceFromHet` takes the heterozygosity as an argument. The
# two real defects are exactly the two that computed the quantity INLINE from a
# raw frequency instead of calling one of these.
CARRIER = re.compile(
    r"V_A|additiveVariance|pgsVarianceFromHet|expectedAltAlleleCount|"
    r"Var_Delta_Mu|hweGenotypeVariance|genotypeVarianceHWE|hweHeterozygosity|"
    r"genotypeVariance|genotypeThirdAbsMoment|\bhet\b|pgsDriftVariance_one_pop|"
    r"covarianceDivergence")

DEF_RE = re.compile(r"^(?:noncomputable\s+)?def\s+([A-Za-z_][\w.']*)")

# The three definitions whose status is known, used to calibrate the screen.
KNOWN_BAD = {"polygenicAdaptationShift", "pgsDriftVariance_one_pop",
             "expectedPGSDiffVariance"}
KNOWN_GOOD = {"pgsMean", "pgsVariance", "pgsMeanShift", "pgsVarianceFromHet",
              "Var_Delta_Mu", "hweGenotypeVariance", "additiveVariance"}


def main():
    flagged, checked = [], []
    for f in lean_files(ROOT):
        src = strip_comments(open(f, errors="ignore").read())
        lines = src.split("\n")
        for i, line in enumerate(lines):
            m = DEF_RE.match(line)
            if not m:
                continue
            short = m.group(1).split(".")[-1]
            body = "\n".join(lines[i:i + 6])
            body = body.split(":=", 1)[1] if ":=" in body else ""
            if not body.strip():
                continue
            if not DOSAGE_NAME.search(short):
                continue
            if not (EFFECT.search(body) and FREQ.search(body)):
                continue
            if CARRIER.search(body):
                continue          # the factor lives in the callee, correctly
            checked.append(short)
            if not PLOIDY.search(body):
                flagged.append((short, os.path.basename(f), i + 1,
                                " ".join(body.split())[:64]))

    print("dosage-scale definitions computing INLINE from a raw frequency: %d"
          % len(checked))
    print("flagged as missing a ploidy factor:       %d\n" % len(flagged))
    for n, f, ln, b in flagged:
        mark = "  <-- KNOWN DEFECT" if n in KNOWN_BAD else ""
        print("  %-40s %-32s %s%s" % (n, "%s:%d" % (f, ln), b, mark))

    names = {n for n, _, _, _ in flagged}
    print("\ncalibration against definitions whose status is already known:")
    print("  known defects caught:      %d / %d  (%s)"
          % (len(names & KNOWN_BAD), len(KNOWN_BAD),
             ", ".join(sorted(names & KNOWN_BAD)) or "none"))
    missed = KNOWN_BAD - names
    if missed:
        print("  known defects MISSED:      %s" % ", ".join(sorted(missed)))
    fp = names & KNOWN_GOOD
    print("  validated-correct flagged: %d  (%s)"
          % (len(fp), ", ".join(sorted(fp)) or "none"))
    if fp:
        print("  ^ these are false positives; a screen that fires on correct")
        print("    definitions is one every reader learns to discount.")


if __name__ == "__main__":
    main()
