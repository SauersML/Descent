"""Census of degenerate reference evaluations across the whole corpus.

A reference evaluation states the VALUE of a definition at a point, on the
reasoning that a value pins a body where an inequality or an invariance would
leave a family of them satisfied.  That reasoning holds only where the value
depends on the part of the body under test.

The error such a theorem is meant to catch is almost always a wrong constant
factor, which is a RESCALING of the body.  `Calibrator.scale_competitor_ne_iff`
proves that a rescaled competitor is rejected at a point if and only if the body
is nonzero there.  So the test is mechanical and exact:

    body(reference point) == 0   =>   the reference point rejects no rescaling

That is what happened to `demographicSpike_at_reference_point`, which stated
`demographicSpike 1 1 1 = 0` -- at `m = n` the effective subgroup size is zero,
the product collapses, and a body with `2` in place of `4` satisfies the theorem
exactly.  It disagreed with the shipped implementation on 7275 of 30624 compared
outputs.

This module evaluates every reference point it can read, using the corpus's own
executable forms from `extract/api.py`.  It never re-transcribes a body: a
second transcription is a second source of truth, which is the hazard that let
the extraction tier report an empty corpus as success.

Anything it cannot read is reported as UNREADABLE, never as clean.  A census
that silently drops what it cannot parse reports a small number and looks like
good news.
"""

import re
import sys
import pathlib

HERE = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / "extract"))

SUFFIX = "_at_reference_point"

# A numeric literal as the corpus writes one in a reference point: an integer, a
# decimal, a negation, or a parenthesised rational like `(1 / 2)`.
_INT = r"-?\d+(?:\.\d+)?"
_LITERAL = re.compile(
    rf"^\(\s*({_INT})\s*/\s*({_INT})\s*\)$|^\(\s*({_INT})\s*\)$|^({_INT})$")


def _literal(token):
    """The float a literal token denotes, or None if it is not a literal."""
    match = _LITERAL.match(token.strip())
    if not match:
        return None
    numerator, denominator, parenthesised, bare = match.groups()
    if numerator is not None:
        return float(numerator) / float(denominator)
    return float(parenthesised if parenthesised is not None else bare)


def _split_arguments(text):
    """Split an application into head and argument tokens, respecting nesting."""
    tokens, depth, current = [], 0, ""
    for char in text:
        if char in "([":
            depth += 1
        elif char in ")]":
            depth -= 1
        if char == " " and depth == 0:
            if current:
                tokens.append(current)
            current = ""
        else:
            current += char
    if current:
        tokens.append(current)
    return tokens


def _proposition(statement):
    """The proposition of a theorem signature, with its binders stripped.

    `api.theorems()` stores the signature, so a nullary theorem reads
    `': innerAtom 0 = 1'` and one with binders reads
    `'(P : FinitePrior n) : E.targetGap P P = 0'`.  The separator is the first
    `:` at depth zero.
    """
    depth = 0
    for index, char in enumerate(statement):
        if char in "([{":
            depth += 1
        elif char in ")]}":
            depth -= 1
        elif char == ":" and depth == 0:
            return statement[index + 1:].strip()
    return None


def _conjuncts(proposition):
    """Split a proposition on top-level `∧`.

    A reference evaluation is often a conjunction of several evaluations, and
    the unit that discriminates is the THEOREM, not the conjunct: `innerAtom 0 =
    1 ∧ innerAtom 1 = 0` pins the body perfectly well even though its second
    half is zero.  Splitting here, and requiring EVERY readable conjunct to be
    zero before calling the theorem degenerate, is what keeps that from being a
    false positive.
    """
    parts, depth, current = [], 0, ""
    for char in proposition:
        if char in "([{":
            depth += 1
        elif char in ")]}":
            depth -= 1
        if char == "∧" and depth == 0:
            parts.append(current)
            current = ""
        else:
            current += char
    parts.append(current)
    return [part.strip() for part in parts if part.strip()]


def _equation_lhs(conjunct):
    """The left-hand side of a top-level `=`, or None."""
    depth = 0
    for index, char in enumerate(conjunct):
        if char in "([{":
            depth += 1
        elif char in ")]}":
            depth -= 1
        elif char == "=" and depth == 0:
            following = conjunct[index + 1:index + 2]
            preceding = conjunct[index - 1:index]
            if following != "=" and preceding not in ("<", ">", "!", "=", "≠"):
                return conjunct[:index].strip()
    return None


def scan():
    """[(theorem, verdict, detail, corpus file)] per `*_at_reference_point` theorem.

    verdict is LIVE, DEGENERATE or UNREADABLE.  The file comes from the
    extracted table, so a caller can scope a gate to the modules it owns
    without computing a path of its own.
    """
    import api

    api.require_fresh()
    theorems = api.theorems()
    if not theorems:
        raise RuntimeError(
            "the extracted theorem table is EMPTY; this census has no evidence "
            "and must not report a clean result")

    rows = []
    for name in sorted(theorems):
        if not name.split(".")[-1].endswith(SUFFIX):
            continue
        source_file = theorems[name].get("file")
        proposition = _proposition(theorems[name].get("statement", ""))
        if proposition is None:
            rows.append((name, "UNREADABLE", "no proposition in the signature", source_file))
            continue

        evaluated, reasons = [], []
        for conjunct in _conjuncts(proposition):
            value, reason = _evaluate_conjunct(api, conjunct)
            if value is None:
                reasons.append(reason)
            else:
                evaluated.append((reason, value))

        if not evaluated:
            rows.append((name, "UNREADABLE", "; ".join(reasons[:2]) or "unparsed", source_file))
        elif all(value == 0 for _, value in evaluated):
            heads = ", ".join(head for head, _ in evaluated)
            rows.append((name, "DEGENERATE",
                         f"every readable evaluation in this theorem is 0 ({heads}), "
                         f"so the stated value rejects no rescaling of the body", source_file))
        else:
            live = ", ".join(f"{head}={value!r}" for head, value in evaluated
                             if value != 0)
            rows.append((name, "LIVE", live, source_file))
    return rows


def _evaluate_conjunct(api, conjunct):
    """(value, head) if the conjunct is an evaluation at numeric literals.

    Returns `(None, reason)` when it is not, so the caller can distinguish "read
    and found live" from "could not read", which are the two outcomes a census
    must never conflate.
    """
    lhs = _equation_lhs(conjunct)
    if lhs is None:
        return None, "no top-level equation"
    tokens = _split_arguments(" ".join(lhs.split()))
    if not tokens:
        return None, "empty left-hand side"
    head, arguments = tokens[0], tokens[1:]
    values = [_literal(token) for token in arguments]
    if not arguments or any(value is None for value in values):
        return None, f"arguments of `{head}` are not all numeric literals"
    try:
        resolved = head if "." in head else api.resolve(head)
        function, parameters = api.callable_for(resolved)
    except Exception as error:                                   # noqa: BLE001
        return None, f"no executable form for `{head}`: {error}"
    if len(parameters) != len(values):
        return None, (f"`{head}` takes {len(parameters)} explicit arguments, the "
                      f"reference point supplies {len(values)}")
    try:
        result = function(*values)
    except Exception as error:                                   # noqa: BLE001
        return None, f"`{head}` evaluation raised {error!r}"
    if isinstance(result, bool) or not isinstance(result, (int, float)):
        return None, f"`{head}` evaluated to {type(result).__name__}, not a number"
    return result, head


def main():
    rows = scan()
    counts = {}
    for _, verdict, _, _ in rows:
        counts[verdict] = counts.get(verdict, 0) + 1
    print(f"reference evaluations scanned: {len(rows)}")
    for verdict in ("LIVE", "DEGENERATE", "UNREADABLE"):
        print(f"  {verdict:<11} {counts.get(verdict, 0)}")
    print()
    for name, verdict, detail, source_file in rows:
        if verdict == "DEGENERATE":
            print(f"  DEGENERATE  {source_file}  {name}: {detail}")
    # A census that read nothing is not a clean census. `readable == 0` is the
    # state the extraction tier was actually in, and it has to fail here rather
    # than print zero findings and exit 0.
    readable = counts.get("LIVE", 0) + counts.get("DEGENERATE", 0)
    if readable == 0:
        print("\nFAIL: no reference evaluation could be read; this census has no evidence")
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
