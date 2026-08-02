SCRIPTS FOR THE CLUSTER -- written under a no-local-execution rule
==================================================================

I could not run any of these. Everything in this directory is UNTESTED by me.
That is stated up front because the last thing I handed over that I could not
run turned out to have a stale-bytecode trap in it, and because two of the
three bugs I have found in other agents' work this session were in code its
author had verified only on examples they chose.

RUN THIS FIRST, ALWAYS:

    python3 preflight.py

It exits non-zero and prints exactly what is wrong if the environment cannot
support the other scripts. It checks Python version, numpy presence, and
whether the generated Lean callables import and evaluate. It runs in about a
second and computes nothing. If it fails, send me its output rather than
working around it -- a workaround here silently changes what is being tested.

ORDER, and why:

  1. preflight.py          environment + import check. Seconds.
  2. sweep_inlined.py      level-set invariance over four suspect closed forms.
                           Pure arithmetic, no sampling, ~10 s. Highest value
                           per second in the directory.
  3. dgp_batch.py          the DGP.lean coverage batch. Needs structure-valued
                           arguments, which is the part I am least able to
                           verify blind -- see its header.

MODEL-FAMILY LAYER (added later; these are the coverage-expansion scripts)

  families.py              the inventory itself. Reads defs.json only, no
                           sampling, seconds. Prints the family table, the
                           un-simulatable list WITH its falsifier executed on
                           every entry, and the statements still in no family.
                           Run it before and after any corpus change: the
                           membership lists go stale inside a session.
  fam_metrics.py           liability-threshold metrics, HWE genotype score,
                           estimator moments. ~50 in-slice statements, pure
                           numpy, ~1 min. Contains an INVERTED positive control
                           (L4, vNoise=0) that is SUPPOSED to come back red;
                           if it comes back green the harness is not comparing
                           anything and the rest of that arm is void.
  fam_fst_estimators.py    F_ST estimator conventions under finite sampling,
                           and the identity-by-descent recurrence read as
                           mutation versus as migration. ~15 statements.
                           Positive control E3 must show Nei and Hudson
                           DISAGREEING; if it does not, the arm's agreements
                           mean nothing.
  fam_ld_decay.py          two-locus Wright-Fisher, the LD family.
  fam_coalescent.py        split and island F_ST. Needs msprime.

PYTHON 3.6.8 CONSTRAINTS OBSERVED THROUGHOUT
  no `from __future__ import annotations`
  no f-strings at all (not just the `=` form)
  no dataclasses, no walrus, no `dict | dict`, no `math.prod`
  no variable annotations in signatures
  numpy only; no scipy, no popgen stack

WHAT TO SEND BACK
  Each script writes a JSON file next to itself and prints a summary. Send the
  JSON. The summaries are for your eye; the JSON is what I read.
