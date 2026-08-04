"""List definitions that can hit a junk value and say nothing about it.

WHAT A JUNK VALUE IS

Mathlib totalises partial operations: `x / 0 = 0`, `Real.log 0 = 0`,
`Real.sqrt x = 0` for `x < 0`, `x⁻¹` at `0`.  Nothing errors.  A definition
built from these therefore returns a number at every point of its type, and at
some of those points the number is not the modelled quantity but the totality
convention showing through.

`totality.py` finds the exact points by instrumenting the backend: it records
every guard (divisor, `log` argument, `sqrt` argument) at each evaluation, looks
for guards that CHANGE SIGN along a coordinate, and bisects to the crossing.
That is the authority, and it applies the three-part test that makes a junk
point a DEFECT rather than a curiosity:

  * the point is attainable inside the definition's own admissible box, and
  * the modelled quantity has a defined limit there, and
  * the junk value differs from that limit.

WHAT THIS SCRIPT DOES INSTEAD

The same reason `eval_gap.py` exists: `totality.py` needs a compiled corpus and
a full instrumented sweep, and this needs only the sources.  It reports every
definition containing a junk-capable operation together with the guard it
depends on, and whether the module states a theorem naming that definition's
junk branch.

It is a NECESSARY-CONDITION scan, not a defect list.  Most entries are fine:
the divisor cannot vanish inside the admissible box, or the junk value happens
to agree with the limit.  What the entries share is that nothing in the corpus
SAYS so, and the corpus convention is to say so -- see
`stabilizingNsFromObservedCorrelation_perfect_is_junk`, which names the branch,
states the wrong value, and records what consumers must require.  That pattern
is the deliverable for a real one:

    theorem NAME_at_POINT_is_junk : NAME <args> = <the wrong value> := by ...

with a docstring saying what the modelled quantity does at that point and what
hypothesis consumers must carry.  A junk branch that is named cannot be reached
by accident; one that is not is a wrong answer inside the domain, returned
silently, that no type error will ever reveal.

MECHANICAL ENTRIES

`--mechanical` narrows the list to the entries where the junk theorem writes
itself: the body is a single top-level quotient, the denominator is a product of
numerals and exactly one parameter, and the signature carries no positivity
hypothesis.  Setting that parameter to zero makes the denominator vanish, so the
value is zero by `simp` and nothing has to be worked out.  What still has to be
written is the part that matters -- what the modelled quantity does at that
point, and what consumers must require.

The rule is narrow on purpose, and its limits are the interesting cases: it
cannot see a body with a sum, an integral, a structure argument or a
conditional, and it cannot see a denominator that vanishes anywhere other than
at zero.  Those need reading.

    python3 junk_gap.py                  # counts, and the worst files
    python3 junk_gap.py --list           # every entry with its guards
    python3 junk_gap.py --file NAME      # one module
    python3 junk_gap.py --mechanical     # entries whose junk theorem is one line
"""

from __future__ import annotations

import collections
import pathlib
import re
import sys

HERE = pathlib.Path(__file__).resolve()
CORPUS = HERE.parents[3] / "Calibrator"

DEF_RE = re.compile(
    r"^\s*(?:noncomputable\s+)?def\s+([a-z][A-Za-z0-9_']*)"
    r"((?:.|\n)*?):=\s*\n?((?:.|\n)*?)(?=\n\n)", re.M)
THM_RE = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)?(?:theorem|lemma)\s+([A-Za-z0-9_']+)", re.M)

# `/-` opens a doc comment, so a division must not be followed by `-`.
DIV_RE = re.compile(r"/(?!-)")
LOG_RE = re.compile(r"Real\.log")
SQRT_RE = re.compile(r"Real\.sqrt")
INV_RE = re.compile(r"⁻¹")
# `x ^ (n : ℤ)` is junk at `x = 0` for negative `n`, and Lean will not say so.
ZPOW_RE = re.compile(r"\^\s*\(\s*-|\^\s*\([A-Za-z_][A-Za-z0-9_']*\s*:\s*ℤ")

LETTER = re.compile(r"[A-Za-zͰ-Ͽ]")


def _argument_after(body: str, pos: int) -> str:
    """The operand starting at `pos`: a parenthesised group, or one token."""
    while pos < len(body) and body[pos] in " \t\n":
        pos += 1
    if pos >= len(body):
        return ""
    if body[pos] == "(":
        depth, start = 0, pos
        while pos < len(body):
            if body[pos] == "(":
                depth += 1
            elif body[pos] == ")":
                depth -= 1
                if depth == 0:
                    return body[start:pos + 1]
            pos += 1
        return body[start:]
    end = pos
    while end < len(body) and body[end] not in " \t\n)+*-/^,":
        end += 1
    return body[pos:end]


def _argument_before(body: str, pos: int) -> str:
    """The operand ending at `pos`, for the postfix inverse."""
    end = pos
    while end > 0 and body[end - 1] in " \t\n":
        end -= 1
    if end > 0 and body[end - 1] == ")":
        depth, i = 0, end - 1
        while i >= 0:
            if body[i] == ")":
                depth += 1
            elif body[i] == "(":
                depth -= 1
                if depth == 0:
                    return body[i:end]
            i -= 1
        return body[:end]
    start = end
    while start > 0 and body[start - 1] not in " \t\n(+*-/^,":
        start -= 1
    return body[start:end]


def guards(body: str) -> list[str]:
    """Which junk-capable operations this body performs on a NON-CONSTANT operand.

    A denominator, logarithm or square-root argument built only from numerals
    cannot reach the junk point, so `p / 2` and `(1 : ℝ) / 3` are not reported.
    This is what keeps the count meaningful: without it every weight vector
    defined as `fun _ => 1 / 2` lands on the list.
    """
    kinds = []
    if any(LETTER.search(_argument_after(body, m.end()))
           for m in DIV_RE.finditer(body)):
        kinds.append("division")
    if any(LETTER.search(_argument_before(body, m.start()))
           for m in INV_RE.finditer(body)):
        kinds.append("inverse")
    if any(LETTER.search(_argument_after(body, m.end()))
           for m in LOG_RE.finditer(body)):
        kinds.append("log")
    if any(LETTER.search(_argument_after(body, m.end()))
           for m in SQRT_RE.finditer(body)):
        kinds.append("sqrt")
    if ZPOW_RE.search(body):
        kinds.append("zpow")
    return kinds


def structures_carrying_domain_facts() -> set[str]:
    """Structures with a positivity or nonzero field.

    A definition taking one of these cannot reach the junk point however it is
    called -- `OUHorizon` carries `rate_pos`, so `ouVariance` never divides by
    zero. Treating those as open work is the scanner's own false positive, and
    it was the largest one: 58 entries.
    """
    out: set[str] = set()
    for f in CORPUS.rglob("*.lean"):
        txt = f.read_text(encoding="utf-8")
        for m in re.finditer(r"^structure\s+([A-Za-z0-9_']+)((?:.|\n)*?)(?=\n\n)",
                             txt, re.M):
            if re.search(r"0\s*<|≠\s*0|0\s*≤|_pos\b|_nonneg\b", m.group(2)):
                out.add(m.group(1))
    return out


# A hypothesis binder in the definition's own signature that rules the junk
# point out before the body runs.
GUARDED_SIG = re.compile(r"0\s*<|≠\s*0|0\s*≠|_pos\b|positive")

# Definitions checked by hand whose guard cannot vanish anywhere in the type,
# so there is no branch to name. Kept as an explicit list with reasons rather
# than as a pattern, because every attempt to generalise these into a rule also
# swallowed entries whose guard genuinely can vanish -- `scalarRowResolvent`
# divides by `1 + latent ^ 2 * quadraticForm`, which looks like `sigmoid`'s
# denominator and is not, because `quadraticForm` may be negative.
UNREACHABLE_BY_HAND = {
    "sigmoid": "1 + Real.exp (-x) ≥ 1",
    "gaussianPosteriorShrinkage": "n * h + 1 = 0 needs n * h = -1, outside the domain",
    "chain": "2 * k + 1 ≠ 0 for k : ℕ",
    "gaussianCriticalMultiplier": "condensationConstant is proved positive",
    "squaringFixedPoint": "scale ^ 2 + 4 ≥ 4",
    "characteristicAmplitude": "a sum of squares is nonnegative",
    "fstMutationDriftEquilibrium": "1 + θ = 0 needs θ = -1, outside the domain",
}


def _toplevel_div(s: str):
    """Split on the last top-level `/`, or None if the body is not a quotient."""
    depth, pos = 0, None
    for i, c in enumerate(s):
        if c in "([{":
            depth += 1
        elif c in ")]}":
            depth -= 1
        elif depth == 0 and c == "/" and (i + 1 >= len(s) or s[i + 1] != "-"):
            pos = i
    return None if pos is None else (s[:pos].strip(), s[pos + 1:].strip())


def _toplevel_addsub(s: str) -> bool:
    depth = 0
    for i, c in enumerate(s):
        if c in "([{":
            depth += 1
        elif c in ")]}":
            depth -= 1
        elif (depth == 0 and c in "+-" and 0 < i < len(s) - 1
              and s[i - 1] == " " and s[i + 1] == " "):
            return True
    return False


BINDER = re.compile(r"\(([A-Za-z_][A-Za-z0-9_'\s]*?)\s*:\s*ℝ\)")


def mechanical(name: str, sig: str, body: str):
    """`(parameter, call arguments)` if the one-line junk theorem applies."""
    sig = " ".join(sig.split())
    b = " ".join(body.split())
    if len(b) > 110 or any(k in b for k in ("if ", "let ", "fun ", "∑", "∫")):
        return None
    if GUARDED_SIG.search(sig):
        return None
    if BINDER.sub("", sig).strip() not in ("", ": ℝ"):
        return None
    split = _toplevel_div(b)
    if not split or _toplevel_addsub(b):
        return None
    den = split[1]
    names = [w for g in BINDER.findall(sig) for w in g.split()]
    hit = [p for p in names if re.search(r"\b" + re.escape(p) + r"\b", den)]
    if len(hit) != 1:
        return None
    skeleton = re.sub(r"\b" + re.escape(hit[0]) + r"\b", "P", den)
    if not re.fullmatch(r"[\d\s\*\(\)\^\.P]+", skeleton) or "P" not in skeleton:
        return None
    return hit[0], " ".join("0" if n == hit[0] else n for n in names)


def scan() -> tuple[collections.Counter, list[tuple[str, str, str]]]:
    struct_guard = structures_carrying_domain_facts()
    tally: collections.Counter = collections.Counter()
    gap: list[tuple[str, str, str]] = []
    for f in sorted(CORPUS.rglob("*.lean")):
        txt = f.read_text(encoding="utf-8")
        junk_thms = {t for t in THM_RE.findall(txt) if "junk" in t.lower()}
        for m in DEF_RE.finditer(txt):
            name, sig, body = m.group(1), m.group(2), m.group(3)
            kinds = guards(body)
            if not kinds:
                continue
            tally["can hit a junk value"] += 1
            if any(name in t for t in junk_thms):
                tally["branch named"] += 1
            elif GUARDED_SIG.search(sig):
                tally["ruled out by its own hypothesis"] += 1
            elif any(t in struct_guard for t in
                     re.findall(r":\s*([A-Za-z][A-Za-z0-9_'.]*)", " ".join(sig.split()))):
                tally["ruled out by a structure field"] += 1
            elif name in UNREACHABLE_BY_HAND:
                tally["guard cannot vanish (checked by hand)"] += 1
            elif re.search(r"\bif\b", body):
                tally["degenerate case already branched"] += 1
            else:
                mech = mechanical(name, sig, body)
                note = f"junk at {mech[0]} = 0" if mech else ",".join(kinds)
                gap.append((name, f.relative_to(CORPUS).as_posix(), note))
                tally["OPEN"] += 1
    return tally, gap


def main(argv: list[str]) -> int:
    if not CORPUS.is_dir():
        print(f"corpus not found at {CORPUS}", file=sys.stderr)
        return 2
    tally, gap = scan()
    for key in ("can hit a junk value", "branch named",
                "ruled out by its own hypothesis", "ruled out by a structure field",
                "guard cannot vanish (checked by hand)",
                "degenerate case already branched", "OPEN"):
        print(f"  {tally[key]:5d}  {key}")

    if "--mechanical" in argv:
        gap = [g for g in gap if g[2].startswith("junk at ")]
        print(f"{len(gap)} of those have a one-line junk theorem")

    want = None
    if "--file" in argv:
        want = argv[argv.index("--file") + 1]
        gap = [g for g in gap if want in g[1]]
        print(f"{len(gap)} of those are in {want}")
    if want is None:
        print()
        by_file = collections.Counter(f for _, f, _ in gap)
        for f, c in by_file.most_common(15):
            print(f"  {c:4d}  {f}")
    if "--list" in argv or want is not None or "--mechanical" in argv:
        print()
        for name, f, kinds in gap:
            print(f"  {name:44s} {kinds:18s} {f}")
    print()
    print("A necessary condition, not a defect list: totality.py decides, by")
    print("testing whether the junk point is attainable and disagrees with the")
    print("limit. What these share is that nothing in the corpus says either way.")

    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
