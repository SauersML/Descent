"""CHECK 6 -- the constraining power of certificates.

THIS CHECK IS NOT AN AUDIT OF THE CERTIFICATE SYSTEM.  IT IS THE CERTIFICATE
SYSTEM, IN THE ONLY FORM THAT HAS REACH.  Read that before assuming the record
types in `Identification.lean` are load-bearing, because they are not:

    In 1001 definitions the corpus contains exactly ONE `Identification` record
    instance -- `neiContrastSpikeIdentification`, Conventions.lean -- and ZERO
    `Approximation` instances.  One `derivation :=` field, one
    `evidence := Evidence.derived`.  Against that, 493 theorems claim a
    derivation by name or docstring.

`Identification` and `Approximation` are structures whose docstrings argue at
length that the derivation obligation cannot be omitted -- "its whole purpose
is that the third field cannot be omitted"; "an `Approximation` cannot be
introduced without naming the target and bounding the distance to it".  The
discipline was designed, argued for, and then not adopted.  And because
adoption is voluntary, the machinery cannot report its own non-use: nothing in
the corpus would tell a reader that the structure is a singleton.  A convention
that cannot detect that it is unused will always report success.  That is a
defect in the design rather than in anyone's diligence, and it is the same
shape as a guard that never fires, a check that cannot fail, and a count of
mentions standing in for a count of evaluations.

Hence this check tests any theorem that CLAIMS to pin a definition, whether or
not it wears the record type -- which is the only way to get coverage over a
discipline that was adopted once.

A theorem that certifies a definition should fail if the definition changes.
Nothing in this project measured that, so the over-determination programme
rested on certificates whose grip had never been tested.  This check applies
mutation testing to the CERTIFICATES rather than to the checkers: for every
theorem that claims to derive or pin a definition, perturb each definition the
theorem mentions and record whether the theorem notices.

The verdict is per (theorem, definition) pair, because a theorem can constrain
one factor of a definition and not another:

    CONSTRAINS    at least one perturbation of that definition breaks it
    VACUOUS_FOR   every perturbation survives -- the theorem holds for any body
                  whatsoever and certifies nothing about this definition

AND THE ONE INSTANCE THAT EXISTS IS THE ONE THAT OVERCLAIMS.
`neiContrastSpikeIdentification`'s `derivation` field is discharged by the theorem below,
in which `effectiveSubgroupSize` occurs on both sides and cancels.  So the
single use of the machinery built to make obligations unskippable certifies one
factor of its definition and not the other, in the file written to prevent
exactly that.

`Conventions.neiContrastSpike_eq_contrastVariance_mul_effectiveSize` is the
motivating case, and the nuance is worth preserving: it CONSTRAINS
`neiContrastSpike` and `neiGst`, and pins the exact contrast normalization.
It deliberately does not claim to validate the distinct Hudson-calibrated BBP
law; that separation prevents the historical estimator-convention error.
It is VACUOUS_FOR `effectiveSubgroupSize`, which occurs on both sides and
cancels.  That is an overclaim of scope in a certificate, not a false
certificate.

The aggregate at the bottom is the coverage-relevant number: definitions that
are mentioned by a derivation theorem but constrained by none of them.
"""

from __future__ import annotations

import json
import re
from collections import Counter, defaultdict
from pathlib import Path

import sympy as sp

import leansym as L
import hyps as H
import shared
from paths import ARTIFACTS as ART

HERE = Path(__file__).parent

NUM = re.compile(r"(?<![A-Za-z0-9_.])(\d+)(?![A-Za-z0-9_.])")


def mutate(body: str, argnames=()):
    """Perturbations of a definition body.

    The scalar perturbations (bump a literal, scale, shift, negate) all move the
    value at EVERY point, so a theorem pinning a single point rejects all of
    them and scores full strength while constraining almost nothing about the
    shape: `effectiveSubgroupSize n (n/2) = n/4` is satisfied by the constant
    `n/4`. Transposing two arguments changes the function while often preserving
    such a point, so it separates a theorem that pins a value from one that pins
    a form."""
    out = []
    m = NUM.search(body)
    if m:
        n = int(m.group(1))
        out.append((f"literal {n}->{n+1}", body[:m.start()] + str(n + 1) + body[m.end():]))
    out.append(("scale by 2", f"2 * ({body})"))
    out.append(("shift by 1", f"1 + ({body})"))
    out.append(("negate", f"-({body})"))
    if len(argnames) >= 2:
        a, b = argnames[0], argnames[1]
        swapped = re.sub(r"(?<![A-Za-z0-9_])(%s|%s)(?![A-Za-z0-9_])" %
                         (re.escape(a), re.escape(b)),
                         lambda m: b if m.group(1) == a else a, body)
        if swapped != body:
            out.append((f"transpose {a}<->{b}", swapped))
    # Scaling and negation both preserve 0, so for a theorem asserting `f = 0`
    # they are degenerate and cannot distinguish a weak certificate from a
    # strong one.  An additive perturbation is the one that bites there.
    out.append(("add 1/3", f"(1/3) + ({body})"))
    return out


def run():
    decls = json.load(open(ART / "decls.json"))
    base_table = shared.build_table()
    sdefs = {d["name"]: d for d in shared.def_records()}
    thms = {t["name"]: t for t in decls if t["kind"] == "theorem"}

    c2 = json.load(open(ART / "results_check2.json"))
    # every theorem that claims a derivation and whose statement we can evaluate
    population = [r for r in c2 if r["status"] in
                  ("derivation_verified", "VACUOUS_DERIVATION",
                   "VACUOUS_DERIVATION_NO_DEFS")]

    pairs = []
    for r in population:
        thm = thms.get(r["name"])
        if thm is None:
            continue
        stmt = thm["body"]
        mentioned = sorted({n.split(".")[-1] for n in
                            re.findall(r"[A-Za-z_][A-Za-z0-9_.']*", stmt)
                            if n.split(".")[-1] in base_table})
        for short in mentioned:
            d = sdefs.get(short)
            if d is None or not d["body"]:
                continue
            rejected, survived = [], []
            for label, mbody in mutate(d["body"], base_table[short][0]):
                table = dict(base_table)
                table[short] = (table[short][0], mbody)
                conv = L.Converter(table)
                try:
                    eq = conv.convert(stmt)
                    if eq is sp.false or eq is sp.true:
                        # sympy constant-folded the mutated statement.  `false`
                        # means the certificate NOTICED; recording it as
                        # "survived" (an earlier version's bug) inverts the
                        # verdict and invents vacuity.
                        v = bool(eq is sp.true)
                    elif not isinstance(eq, sp.Eq):
                        v = None  # cannot decide; not evidence of vacuity
                    else:
                        v, _ = H.verdict_for(eq.lhs, eq.rhs, thm["binders"], conv)
                except Exception:
                    v = False  # perturbed body no longer converts: noticed
                (survived if v is True else rejected).append(label)
            pairs.append({
                "check": "check6_certificate_power",
                "theorem": r["fqn"], "theorem_file": r["file"],
                "theorem_line": r["line"],
                "definition": d["fq"], "definition_short": short,
                "definition_file": d["file"], "definition_line": d["line"],
                "status": "CONSTRAINS" if rejected else "VACUOUS_FOR",
                "mutations_rejected": rejected,
                "mutations_survived": survived,
            })
    return pairs


def main():
    pairs = run()
    # per-definition aggregate
    by_def = defaultdict(list)
    for p in pairs:
        by_def[p["definition"]].append(p)
    unconstrained = {d: ps for d, ps in by_def.items()
                     if all(p["status"] == "VACUOUS_FOR" for p in ps)}

    out = {"pairs": pairs,
           "definitions_mentioned": len(by_def),
           "definitions_constrained": len(by_def) - len(unconstrained),
           "definitions_unconstrained": sorted(unconstrained)}
    (ART / "results_check6.json").write_text(json.dumps(out, indent=1, ensure_ascii=False))

    c = Counter(p["status"] for p in pairs)
    print("CHECK 6: constraining power of derivation certificates")
    print(f"  (theorem, definition) pairs tested : {len(pairs)}")
    print(f"    CONSTRAINS                       : {c['CONSTRAINS']}")
    print(f"    VACUOUS_FOR                      : {c['VACUOUS_FOR']}")
    print(f"  definitions mentioned by a certificate : {len(by_def)}")
    print(f"    constrained by at least one          : {len(by_def) - len(unconstrained)}")
    print(f"    constrained by NONE                  : {len(unconstrained)}")
    print()
    print("=== definitions no certificate constrains ===")
    for d, ps in sorted(unconstrained.items()):
        print(f"  {d}  ({ps[0]['definition_file']}:{ps[0]['definition_line']})")
        for p in ps:
            print(f"      certified by {p['theorem'].split('.')[-1]} "
                  f"-- all {len(p['mutations_survived'])} mutations survived")
    print()
    print("=== partial certificates (constrain some definitions, not others) ===")
    by_thm = defaultdict(list)
    for p in pairs:
        by_thm[p["theorem"]].append(p)
    for t, ps in sorted(by_thm.items()):
        vac = [p for p in ps if p["status"] == "VACUOUS_FOR"]
        con = [p for p in ps if p["status"] == "CONSTRAINS"]
        if vac and con:
            print(f"  {t}")
            print(f"      constrains : {sorted(p['definition_short'] for p in con)}")
            print(f"      vacuous for: {sorted(p['definition_short'] for p in vac)}")


if __name__ == "__main__":
    main()
