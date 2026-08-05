"""Falsifiability demonstration: prove every registered check can FAIL.

A check that accepts every possible body covers nothing, and coverage claimed
that way is worse than no coverage -- it converts an unknown into a false
known.  So no definition is counted as covered here until a MUTANT of its body
has been exhibited that the check rejects.

Method: perturb the Lean body (double a constant, flip a sign, drop a `max 0`
guard, swap two arguments, ...), retranspile only that body against the
existing namespace, and rerun the definition's own checks.  If some mutant is
rejected, the check discriminates and the definition is covered.  If every
mutant survives, the definition is reported as NOT covered together with the
mutants that got through, and it joins the residue.

Run:  python demo_falsifiable.py  ->  results_falsifiability.json
"""
from __future__ import annotations

import json
import pathlib
import sys

import backends
import compile_defs as C
import invariants as INV
from check_ranges import check_one as range_check
from transpile import Untranspilable, build_arity, pyname, transpile

HERE = pathlib.Path(__file__).resolve().parent


def compile_mutant(defs, ns, d, body):
    """Recompile ONE body against the already-built namespace.

    Rebuilding all 400 definitions per mutant would cost about a second each;
    only the mutated definition changes, so only it is recompiled.
    """
    ar, rn, amb = build_arity(defs, d["module"])
    src = transpile(body, d["params"], ar, d["name"], rn, amb)
    args = ", ".join(pyname(p) for p, _ in d["params"])
    sig = f"_b, {args}" if args else "_b"
    text = f"def _mutant({sig}):\n    return {src}"
    emitted = set(ns)
    import re

    text = re.sub(r"\b([A-Za-z_]\w*)\(",
                  lambda m: f"{m.group(1)}(_b, " if m.group(1) in emitted
                  else m.group(0), text)
    text = text.replace("def _mutant(_b, _b, ", "def _mutant(_b, ")
    text = text.replace("def _mutant(_b, _b)", "def _mutant(_b)")
    local = dict(ns)
    exec(compile(text, "<mutant>", "exec"), local)
    return C.Compiled(d, src, [p for p, _ in d["params"]], local["_mutant"])


def arg_swap_mutants(d):
    """Swap two same-typed arguments -- the mutation symmetry must catch."""
    out = []
    ps = d["params"]
    for i in range(len(ps)):
        for j in range(i + 1, len(ps)):
            if ps[i][1] != ps[j][1]:
                continue
            a, b = ps[i][0], ps[j][0]
            import re

            body = re.sub(r"\b(" + re.escape(a) + r"|" + re.escape(b) + r")\b",
                          lambda m: b if m.group() == a else a, d["body"])
            if body != d["body"]:
                out.append((f"swap-args({a},{b})", body))
    return out


def range_verdict_rejects(before, after):
    """Did the range check change from accepting to rejecting?"""
    good = ("proved",)
    bad = ("escape", "escape-unguarded", "escape-outside-theorem")
    return before in good and after in bad


def main(argv):
    defs = C.load_defs()
    cs, why_not, text = C.compile_all(defs)
    ns = {"backends": backends}
    exec(compile(text, "<corpus>", "exec"), ns)

    results = {}
    for k in sorted(cs):
        c = cs[k]
        d = c.d
        # The BASE verdict uses the solver, so a containment z3 proved counts
        # as a registered check.  Only the mutant sweep skips it: there we
        # merely need to see the verdict flip, which sampling decides, and a
        # solver call per mutant would cost hours.
        base_range = range_check(c, defs, use_z3=True)
        base_checks, _ = INV.derive(c)
        base_inv = []
        for ch in base_checks:
            try:
                ok, _ = ch["run"](c)
            except Exception:
                ok = None
            base_inv.append(ok)

        # A check that already REJECTS the definition as written has proved
        # its own falsifiability on the spot -- no mutant is needed, the real
        # body is the counterexample.
        fires = []
        if base_range["verdict"] in ("escape", "escape-unguarded",
                                     "escape-outside-theorem"):
            fires.append("range")
        for ch, ok in zip(base_checks, base_inv):
            if ok is False:
                fires.append(ch["kind"])

        registered = list(fires)
        if base_range["verdict"] == "proved":
            registered.append("range")
        for ch, ok in zip(base_checks, base_inv):
            if ok is True:
                registered.append(ch["kind"])
        if fires:
            results[k] = dict(
                name=d["name"], module=d["module"], line=d["line"],
                registered=sorted(set(registered)), covered=True,
                demonstration="rejects-as-written",
                rejected_by=sorted(set(fires)),
                reason="the check rejects the definition as it stands, which "
                       "is itself the demonstration that it can fail")
            continue
        if not registered:
            results[k] = dict(name=d["name"], module=d["module"], line=d["line"],
                              registered=[], covered=False,
                              reason="no check on this definition currently "
                                     "holds, so there is nothing to falsify")
            continue

        muts = C.mutants(d["body"]) + arg_swap_mutants(d)
        killed, survived = [], []
        for tag, body in muts:
            try:
                mc = compile_mutant(defs, ns, d, body)
                mc(backends.FLOAT, *[0.3] * len(c.names))
            except Exception:
                continue
            kills = []
            if "range" in registered:
                try:
                    mr = range_check(mc, defs, use_z3=False)
                    if range_verdict_rejects(base_range["verdict"], mr["verdict"]):
                        kills.append("range")
                except Exception:
                    pass
            for ch, ok in zip(base_checks, base_inv):
                if ok is not True:
                    continue
                try:
                    mok, _ = ch["run"](mc)
                except Exception:
                    mok = None
                if mok is False:
                    kills.append(ch["kind"])
            if kills:
                killed.append(dict(mutation=tag, body=body, rejected_by=sorted(set(kills))))
            else:
                survived.append(tag)

        results[k] = dict(
            name=d["name"], module=d["module"], line=d["line"],
            registered=sorted(set(registered)),
            n_mutants=len(muts),
            covered=bool(killed),
            demonstration="mutant-rejected" if killed else None,
            killed=killed[:4],
            n_killed=len(killed),
            survived=survived,
            reason=None if killed else
            "every mutant of this body survived every registered check, so "
            "the checks do not discriminate and this definition is NOT covered",
        )

    out = HERE / "results_falsifiability.json"
    out.write_text(json.dumps(results, indent=1, default=str))
    reg = [r for r in results.values() if r["registered"]]
    cov = [r for r in reg if r["covered"]]
    fired = [r for r in cov if r.get("demonstration") == "rejects-as-written"]
    print(f"{len(results)} transpiled definitions -> {out}")
    print(f"  {len(reg)} have at least one currently-holding check")
    print(f"  {len(cov)} are DEMONSTRABLY covered")
    print(f"     of which {len(fired)} because a check rejects the body as "
          "written")
    print(f"     and {len(cov) - len(fired)} because a mutant is rejected")
    print(f"  {len(reg) - len(cov)} have checks that no mutant could break "
          "-- reported as uncovered")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
