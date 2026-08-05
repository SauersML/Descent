"""DIAGNOSTIC -- split the ledger's UNINFORMATIVE MATCHes into the two kinds,
because the repair is different and the ledger cannot tell them apart.

`ledger.py` applies the competitor gate and downgrades every MATCH that carried
no competing formula to UNINFORMATIVE. That is right, and it is where the
question stops: the ledger says "this verdict is not evidence" but not "here is
what to do about it". There are two answers and they are not interchangeable.

  ADD A COMPETITOR.  The body is a claim about a generating process -- it names
      a population size, a rate, an elapsed time -- so a simulation CAN reject a
      wrong functional form. It just was not asked to. Re-run the same design
      carrying a competing reading and the verdict becomes evidence.

  REDESIGN, A COMPETITOR WILL NOT HELP.  The body is a pure function of
      quantities the simulator computes directly from the realised sample, with
      no model parameter anywhere in it. Then the oracle and the body are the
      same aggregate over the same numbers, agreement is the law of large
      numbers rather than a property of the population, and a competing formula
      is rejected by an oracle that was never able to reject the body either. A
      competitor added to such a design manufactures the APPEARANCE of
      discrimination. This is the `driftVariance` failure mode in its general
      form, and it is the one that costs a redesign rather than a re-run.

THE SCREEN, and its limits, stated plainly. A body is classed
PARAMETER-FREE when it mentions none of the model parameters below. That is a
NECESSARY condition for the second kind and not a sufficient one, so this file
reports a PARTITION TO REVIEW and not a verdict:

  * FALSE POSITIVES are real. `fisherAverageEffect = a + d(1-2p)` is
    parameter-free by this screen, but a simulation that REGRESSES phenotype on
    genotype and recovers it has tested Fisher's decomposition, which is a
    theorem about the generating process and not an aggregate identity. Same for
    `additiveGeneticVariance = sum beta^2`, which is a claim about linkage
    equilibrium -- `battery_bulk41` shows the NO POWER cell that proves the
    regime is a condition and not decoration.
  * FALSE NEGATIVES are also real. A body can name `Ne` and still be an
    identity if the design feeds `Ne` back in through a sample estimate, which
    is exactly what `battery_bulk21` did to `driftVariance`. That case is
    handled by the `argument_source` declaration in `verdict.py`, not here.

So: this is a worklist, ordered so the expensive repairs surface first. It does
not gate, it does not write verdicts back, and nothing in it should be quoted as
a finding without reading the battery that produced the row.

Run:  python3 uninformative_triage.py [ledger.json]
"""
from __future__ import annotations

import json
import re
import sys

# Model parameters: a symbol whose value comes from the SIMULATION SETUP rather
# than from the realised sample. A body mentioning one of these is making a
# claim a simulation can falsify.
# Single-letter patterns are deliberately NARROW. A first version listed `g`,
# `c`, `K` and `M` as bare word-boundary matches and they fired inside summation
# indices -- `sum_g genotypeProb g * centered^2` was classed as parameterised
# because of its index variable, which is the opposite of the truth. An index is
# not a model parameter, and a screen that cannot tell them apart puts the
# expensive repairs in the cheap pile.
MODEL_PARAMS = [
    r"\bNe\b", r"\bN_b\b", r"\bNanc\b", r"\bN\b",
    r"\bt\b", r"\bt_div\b", r"\btmrca\b", r"\btAnc\b", r"\bt_since\b",
    r"\bm\b", r"\bmig\b", r"\bm12\b", r"\bm21\b", r"\bmu\b",
    r"\bs\b", r"\br\b", r"\brate\b", r"\brecomb(?:Rate)?\b",
    r"\btheta\b", r"\bbigM\b", r"\bgenerations(?:_since)?\b",
    r"\btau\b", r"\blam\b", r"\bh2\b", r"\bv_mutation\b",
    # Setup parameters that are not rates or sizes but are still CHOSEN by the
    # design rather than realised by it. Omitting them put the LD-band spectral
    # results in the redesign pile, where they do not belong: `kappa` is a
    # retention fraction the design picks and `decay`/`rho` is the LD decay it
    # simulates, so a wrong functional form of either is rejectable.
    r"\balpha\b", r"\bkappa\b", r"\bdecay\b", r"\brho\b", r"\brhoSq\b",
    r"\bn\b", r"\bn_eff\b", r"\bK\b", r"\bpi\b", r"\bprevalence\b",
]
PARAM_RE = re.compile("|".join(MODEL_PARAMS))

# Index and dummy variables that a `sum_x` or `prod_x` binds. Stripped before the
# parameter screen runs, so a bound `t` or `g` is never read as elapsed time.
BOUND_RE = re.compile(r"\b(?:sum|prod|iterate)_(\w+)")

# Bodies that are a bare forward to another definition. The ledger already has a
# duplicate screen; these are called out separately because "add a competitor"
# is meaningless for them -- the competitor belongs on the callee.
FORWARD_RE = re.compile(r"^\s*forwards to |^\s*[A-Za-z_][\w.]*\s+[\w.\s]+$")


def load(path):
    d = json.load(open(path))
    return d["records"] if isinstance(d, dict) and "records" in d else d


def main() -> int:
    path = sys.argv[1] if len(sys.argv) > 1 else "ledger.json"
    rows = load(path)
    unin = [r for r in rows
            if isinstance(r, dict)
            and str(r.get("verdict", "")).startswith("UNINFORMATIVE")]

    add_competitor, redesign, forwards = [], [], []
    for r in unin:
        src = str(r.get("source", "") or "")
        name = str(r.get("declaration", "") or "?")
        for bound in BOUND_RE.findall(src):
            src_screen = re.sub(r"\b%s\b" % re.escape(bound), "_idx", src)
            src = src_screen
        if FORWARD_RE.match(src) and not PARAM_RE.search(src):
            forwards.append((name, src))
        elif PARAM_RE.search(src):
            add_competitor.append((name, src))
        else:
            redesign.append((name, src))

    print("UNINFORMATIVE rows in the ledger: %d" % len(unin))
    print()
    print("=" * 78)
    print("A. REDESIGN -- parameter-free body: a competitor cannot rescue this")
    print("=" * 78)
    print("The body mentions no model parameter, so the oracle can only be the")
    print("same aggregate over the same realised numbers. REVIEW EACH: a body")
    print("recovered by a REGRESSION or constrained by a REGIME (linkage")
    print("equilibrium, HWE) is a real claim and belongs in B despite the screen.")
    for name, src in sorted(redesign):
        print("  %-44s %s" % (name[:44], src[:60]))
    print("  (%d rows)" % len(redesign))

    print()
    print("=" * 78)
    print("B. ADD A COMPETITOR -- the design can discriminate, it was not asked")
    print("=" * 78)
    print("The body names a model parameter, so a wrong functional form of that")
    print("parameter is rejectable on the same cells. Re-run carrying one.")
    for name, src in sorted(add_competitor):
        print("  %-44s %s" % (name[:44], src[:60]))
    print("  (%d rows)" % len(add_competitor))

    print()
    print("=" * 78)
    print("C. FORWARDS -- the competitor belongs on the callee")
    print("=" * 78)
    for name, src in sorted(forwards):
        print("  %-44s %s" % (name[:44], src[:60]))
    print("  (%d rows)" % len(forwards))

    print()
    print("PARTITION: %d redesign / %d add-competitor / %d forward = %d"
          % (len(redesign), len(add_competitor), len(forwards), len(unin)))
    print("DIAGNOSTIC: a worklist, not a verdict. The screen is a NECESSARY and "
          "not a sufficient condition; see this file's header for the false "
          "positives and false negatives it is known to have.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
