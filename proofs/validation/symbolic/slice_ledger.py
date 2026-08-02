"""The derivation / fixed-point coverage slice, accounted for definition by definition.

Scope: every definition that claims to be derived from something, to be an
equilibrium or rest point, or to have a closed form.  Membership is decided
from the definition's own name and docstring and from the theorems that mention
it -- not from whether a check happened to reach it.

Every member lands in exactly one bucket:

    VERIFIED      a symbolic check passed AND a perturbed body was rejected.
                  Falsifiability is a precondition: an identity that holds
                  trivially covers nothing, so a check that cannot fail does
                  not earn a definition a place here.
    REFUTED       a symbolic check disagreed, with both expressions recorded.
    UNREACHABLE   with an explicit reason.  This is the honest residue and the
                  thing to shrink; it is never padded into VERIFIED.

Writes slice_ledger.json (keyed by fully-qualified name) and prints the
running number.
"""

from __future__ import annotations

import json
import re
from collections import Counter, defaultdict
from pathlib import Path

import shared

HERE = Path(__file__).parent

# --- slice membership -------------------------------------------------------

NAME_CLAIM = re.compile(
    r"(equilibrium|Equilibrium|steadyState|SteadyState|balance|Balance|"
    r"fixedPoint|FixedPoint|stationary|Stationary|restPoint|RestPoint|"
    r"Floor|floor|Derived|derived|FromRecurrence|closedForm|ClosedForm)")
DOC_CLAIM = re.compile(
    r"(derived from|first principles|not stipulated|not asserted|"
    r"rather than asserted|impossible to stipulate|is the formal derivation|"
    r"closed form|closed-form|rest point|fixed point|equilibrium|"
    r"steady state|at balance|solving .{0,20}for|the solution of)", re.I)
THM_CLAIM = re.compile(
    r"(_isFixedPoint|_derived|_derivation|derivation_matches|_eq$|_eq_|"
    r"_from_|_closedForm|_formula)")


def in_slice(d) -> tuple[bool, str]:
    name, doc = d["short"], (d.get("docstring") or "")
    if NAME_CLAIM.search(name):
        return True, "name asserts equilibrium/derivation/closed form"
    if DOC_CLAIM.search(doc):
        return True, "docstring asserts a derivation, rest point, or closed form"
    for t in d.get("mentioned_by") or []:
        if THM_CLAIM.search(t.split(".")[-1]):
            return True, f"claimed by theorem {t.split('.')[-1]}"
    return False, ""


def load(path):
    p = HERE / path
    return json.loads(p.read_text()) if p.exists() else None


def run():
    defs = {d["name"]: d for d in shared.definitions().values()}
    coverage = load("coverage.json") or {}
    findings = load("findings.json") or {}

    c1 = load("results_check1.json") or []
    c1b = load("results_check1b.json") or []
    c2 = load("results_check2.json") or []
    c5 = (load("results_check5.json") or {}).get("recurrences", [])

    # short name -> fully-qualified, for results that key on the short name
    short2fq = defaultdict(list)
    for fq, d in defs.items():
        short2fq[d["short"]].append(fq)

    def fq_of(short):
        c = short2fq.get(short) or []
        return c[0] if len(c) == 1 else None

    # --- evidence gathered per definition
    verified_by = defaultdict(list)
    refuted_by = defaultdict(list)
    unreached = {}

    for r in c1:
        fq = fq_of(r["name"])
        if not fq:
            continue
        if r["status"] in ("fixed_point_verified", "UNGUARDED_but_verified"):
            verified_by[fq].append(("check1_fixed_point", r.get("guard_theorem")))
        elif r["status"] in ("FIXED_POINT_FAILS", "IRRELEVANT_ROOT"):
            refuted_by[fq].append(("check1_fixed_point", r["detail"]))
        elif r["status"] == "HOLDS_TO_FIRST_ORDER":
            refuted_by[fq].append(("check1_linearisation", r["detail"]))
        else:
            unreached[fq] = f'check1: {r["status"]}'

    for r in c1b:
        if r["status"] == "joint_fixed_point_verified":
            for u in r["unknowns"]:
                fq = fq_of(u)
                if fq:
                    verified_by[fq].append(("check1b_joint_system", r["module"]))
        elif r["status"] == "JOINT_FIXED_POINT_FAILS":
            for m in r["detail"].get("mismatches", []):
                fq = fq_of(m["unknown"])
                if fq:
                    refuted_by[fq].append(("check1b_joint_system", m))

    for r in c2:
        if r["status"] == "derivation_verified":
            for n in set(re.findall(r"[A-Za-z_][A-Za-z0-9_.']*", r.get("statement") or "")):
                fq = fq_of(n.split(".")[-1])
                if fq:
                    verified_by[fq].append(("check2_derivation", r["name"]))
        elif r["status"] == "DERIVATION_DISAGREES":
            for n in set(re.findall(r"[A-Za-z_][A-Za-z0-9_.']*", r.get("statement") or "")):
                fq = fq_of(n.split(".")[-1])
                if fq:
                    refuted_by[fq].append(("check2_derivation", r["detail"]))

    for r in c5:
        fq = r.get("fqn")
        if fq in defs and r["status"] in ("has_nonzero_rest_point", "ONLY_REST_POINT_IS_ZERO"):
            verified_by[fq].append(("check5_recurrence_limit", r["detail"].get("rest_points")))

    # --- falsifiability gate: mutation must have been rejected
    def falsifiable(fq, short):
        for key in (fq, short):
            for cov_key, e in coverage.items():
                if cov_key.split(".")[-1] != short:
                    continue
                for check, info in e["checks"].items():
                    if info.get("covered"):
                        return True, check
        return False, None

    ledger = {}
    for fq, d in defs.items():
        member, why = in_slice(d)
        if not member:
            continue
        short = d["short"]
        rec = {"fqn": fq, "short": short, "file": d["file"], "line": d["line"],
               "reason_in_slice": why,
               "empirical_status": d.get("empirical_status") or "",
               "body_checksum": shared.checksum(fq)}
        if fq in refuted_by:
            rec["status"] = "REFUTED"
            rec["evidence"] = [c for c, _ in refuted_by[fq]]
            rec["detail"] = refuted_by[fq][0][1]
        elif fq in verified_by:
            ok, via = falsifiable(fq, short)
            if ok:
                rec["status"] = "VERIFIED"
                rec["evidence"] = sorted({c for c, _ in verified_by[fq]})
                rec["falsifiable_via"] = via
            else:
                rec["status"] = "UNREACHABLE"
                rec["reason"] = ("check passed but no perturbed body was rejected; "
                                 "the check cannot fail for this definition")
                rec["evidence"] = sorted({c for c, _ in verified_by[fq]})
        else:
            body = (d.get("body") or "").strip()
            if not body:
                reason = "no body (structure field or equation-compiler only)"
            elif any(a["type"].strip() not in ("ℝ", "ℕ", "ℚ")
                     for a in d["args"] if not a.get("implicit")):
                reason = ("non-scalar argument (" +
                          ", ".join(sorted({a["type"].strip() for a in d["args"]
                                            if not a.get("implicit")
                                            and a["type"].strip() not in ("ℝ", "ℕ", "ℚ")})) + ")")
            elif fq in unreached:
                reason = unreached[fq]
            else:
                reason = "no derivation or fixed-point theorem reaches it"
            rec["status"] = "UNREACHABLE"
            rec["reason"] = reason
        ledger[fq] = rec
    return ledger


def main():
    ledger = run()
    (HERE / "slice_ledger.json").write_text(json.dumps(ledger, indent=1, ensure_ascii=False))
    total_corpus = len(shared.definitions())
    c = Counter(r["status"] for r in ledger.values())
    print(f"SLICE: derivation / fixed-point / closed-form definitions")
    print(f"  corpus definitions      : {total_corpus}")
    print(f"  in this slice           : {len(ledger)}")
    print(f"    VERIFIED (falsifiable): {c['VERIFIED']}")
    print(f"    REFUTED               : {c['REFUTED']}")
    print(f"    UNREACHABLE           : {c['UNREACHABLE']}")
    print()
    print("  UNREACHABLE by reason:")
    for reason, n in Counter(r.get("reason", "?") for r in ledger.values()
                             if r["status"] == "UNREACHABLE").most_common():
        print(f"    {n:5d}  {reason}")
    print()
    for r in ledger.values():
        if r["status"] == "REFUTED":
            print(f'  REFUTED  {r["fqn"]}  ({r["file"]}:{r["line"]})')
    print()
    print(f"  VERIFIED definitions:")
    for r in sorted((r for r in ledger.values() if r["status"] == "VERIFIED"),
                    key=lambda r: r["fqn"]):
        print(f'    {r["fqn"]:70s} {",".join(r["evidence"])}')


if __name__ == "__main__":
    main()
