#!/usr/bin/env python3
"""Which theorems carry their content in a hypothesis that nothing ever discharges?

WHAT THIS IS FOR

A Lean corpus with no `sorry` and no axioms is sound: every theorem follows from
its hypotheses.  That says nothing about whether the hypotheses are ever met.  A
theorem of the shape

    theorem headline (hard : <the substantive claim>) : <the conclusion> := ...

is a true theorem and an honest conditional, and it is also the standard way to
launder an unproved input into a corpus: the reader sees a named theorem whose
docstring states the headline, and the fact that `hard` is never established
anywhere is invisible from the theorem alone.

This script does not decide honesty.  It measures one thing that honesty depends
on: for each theorem whose binders include a genuine hypothesis (a `Prop`-valued
argument, especially a universally quantified one over parameters the theorem
itself introduces), is the theorem ever APPLIED anywhere else in the corpus?  An
applied theorem has had its hypotheses discharged at least once by whoever
applied it.  A theorem that is never applied, and whose hypotheses quantify over
abstract parameters that appear nowhere else, is carrying an assumption that no
part of the development has ever had to pay for.

WHAT A HIT MEANS, AND WHAT IT DOES NOT

A hit is not a defect.  General lemmas stated for reuse, results kept as the
statement of a known theorem, and abstract results whose instances live outside
the corpus are all legitimately never-applied.  A hit means only this: nothing
in the corpus has ever satisfied these hypotheses, so their satisfiability is
untested here, and if the docstring asserts the conclusion unconditionally then
the docstring is ahead of the mathematics.

The output is ranked by how much of the statement sits in the hypotheses, since
that is the quantity that decides how much a conditional is really claiming.

Run:  python3 proofs/validation/empirical/invariants/hypothetical.py
      python3 proofs/validation/empirical/invariants/hypothetical.py --json
      python3 proofs/validation/empirical/invariants/hypothetical.py --min-score 3
"""

from __future__ import annotations

import argparse
import json
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
# Three levels up, not two: this file sits at proofs/validation/empirical/
# invariants/, so `../..` is validation/ and yields a path that does not exist.
# Its siblings here use `parents[3]`, which is the same distance counted from
# the file rather than from the directory.
CALIBRATOR = os.path.normpath(os.path.join(HERE, "..", "..", "..", "Calibrator"))

# A declaration header: the token, the name, then everything up to the `:` that
# opens the statement.  Lean lets binders span lines, so the header is taken up
# to the first `:=` or the end of the signature block.
DECL_START = re.compile(
    r"^(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+)*"
    r"(theorem|lemma)\s+([A-Za-z_][A-Za-z0-9_.']*)",
    re.M,
)

# A hypothesis binder: a parenthesised argument whose name starts with `h` (the
# corpus's convention) or whose type is visibly a Prop-former.
HYP_BINDER = re.compile(r"\((h[A-Za-z0-9_']*)\s*:\s*([^)]*)\)")
FORALL_BINDER = re.compile(r"\((h[A-Za-z0-9_']*)\s*:\s*∀")
PRED_PARAM = re.compile(r"\(([A-Za-z_][A-Za-z0-9_']*)\s*:\s*[^)]*→\s*Prop\)")

# A BOUNDED quantifier ranges over an already-given index set and states a domain
# condition: `∀ i ∈ s, 0 ≤ w i`.  Those are the hypotheses a theorem needs in order
# to be true at all, and they are discharged by whoever supplies the data.  They are
# not imports and must not be scored as such -- scoring them is what turned the first
# version of this file into a number nobody could act on.
BOUNDED_FORALL = re.compile(r"∀\s*[^,]*?∈")


def strip_comments(text: str) -> str:
    text = re.sub(r"/-.*?-/", " ", text, flags=re.S)
    text = re.sub(r"--[^\n]*", " ", text)
    return text


def load(root: str) -> dict[str, str]:
    out = {}
    for dirpath, _, filenames in os.walk(root):
        for fn in filenames:
            if fn.endswith(".lean"):
                p = os.path.join(dirpath, fn)
                with open(p, encoding="utf-8", errors="replace") as fh:
                    out[p] = fh.read()
    return out


def signature_of(body: str, start: int) -> str:
    """Text from a declaration's name to the `:=` that opens its proof."""
    cut = body.find(":=", start)
    nxt = DECL_START.search(body, start + 1)
    if nxt and (cut == -1 or nxt.start() < cut):
        cut = nxt.start()
    if cut == -1:
        cut = len(body)
    return body[start:cut]


def analyze(files: dict[str, str]) -> list[dict]:
    stripped = {p: strip_comments(t) for p, t in files.items()}

    # Every theorem, with its signature.
    decls: list[tuple[str, str, str]] = []  # (module, name, signature)
    for p, body in stripped.items():
        module = os.path.basename(p)[:-5]
        for m in DECL_START.finditer(body):
            decls.append((module, m.group(2), signature_of(body, m.end())))

    # Reference counts: how often each name appears outside its own module.
    all_text = {os.path.basename(p)[:-5]: t for p, t in stripped.items()}
    names = {name for _, name, _ in decls}
    counts = {name: 0 for name in names}
    for mod, text in all_text.items():
        for m in re.finditer(r"(?<![A-Za-z0-9_.'])([A-Za-z_][A-Za-z0-9_.']*)", text):
            n = m.group(1)
            if n in counts:
                counts[n] += 1

    findings = []
    for module, name, sig in decls:
        hyps = HYP_BINDER.findall(sig)
        if not hyps:
            continue
        preds = PRED_PARAM.findall(sig)
        # Count only universal hypotheses that ASSERT SOMETHING ABOUT AN ABSTRACT
        # PREDICATE the theorem itself introduces.  This is the third and last
        # narrowing of this criterion, and each narrowing was forced by reading the
        # top of the previous ranking:
        #
        #   * scoring every ∀-hypothesis gave 552 hits, dominated by domain
        #     conditions like `∀ i ∈ s, 0 ≤ w i`;
        #   * excluding bounded quantifiers gave 125, still topped by
        #     `qalyLoss_le_componentwise_calibration_bound`, whose eight
        #     hypotheses are `∀ t, |predicted t - true t| ≤ ε t` -- unbounded only
        #     because `Fin T` needs no `∈`, and quantitative conditions on supplied
        #     data, not imports.
        #
        # What distinguishes an import is not the quantifier.  It is that the
        # hypothesis constrains a PREDICATE PARAMETER, because a predicate parameter
        # has no content of its own: whatever the hypothesis says about it is
        # assumed outright rather than derived.  A numeric bound on given data is
        # discharged by whoever supplies the data; `∀ F, admitsDim F 1` is not
        # discharged by anyone.
        unbounded = 0
        for hname, htype in hyps:
            if not htype.lstrip().startswith("∀"):
                continue
            if BOUNDED_FORALL.search(htype):
                continue
            if any(re.search(rf"(?<![A-Za-z0-9_.']){re.escape(p)}(?![A-Za-z0-9_'])",
                             htype) for p in preds):
                unbounded += 1
        # One occurrence is the declaration itself.
        uses = counts.get(name, 1) - 1
        if uses > 0:
            continue
        score = unbounded * 2 + len(preds) * 2
        if score == 0:
            continue
        findings.append(
            {
                "module": module,
                "name": name,
                "score": score,
                "hypotheses": len(hyps),
                "unbounded_forall_hypotheses": unbounded,
                "predicate_parameters": preds,
                "uses_outside_declaration": uses,
            }
        )
    findings.sort(
        key=lambda f: (-f["score"], -f["unbounded_forall_hypotheses"], f["module"])
    )
    return findings


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--json", action="store_true")
    ap.add_argument("--min-score", type=int, default=1)
    args = ap.parse_args()

    if not os.path.isdir(CALIBRATOR):
        print(f"cannot find {CALIBRATOR}", file=sys.stderr)
        return 2

    findings = [f for f in analyze(load(CALIBRATOR)) if f["score"] >= args.min_score]

    if args.json:
        print(json.dumps(findings, indent=1))
        return 0

    print(f"never-applied hypothetical theorems: {len(findings)}")
    print()
    for f in findings[:60]:
        preds = (
            "  preds=" + ",".join(f["predicate_parameters"])
            if f["predicate_parameters"]
            else ""
        )
        print(
            f"  score={f['score']:2d}  {f['module']}.{f['name']}"
            f"  (hyps={f['hypotheses']}, unbounded-forall={f['unbounded_forall_hypotheses']}){preds}"
        )
    if len(findings) > 60:
        print(f"  ... and {len(findings) - 60} more")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
