"""Find definitions that are functions of a falsified closed form, by what they COMPUTE.

WHY THIS EXISTS
---------------
`hetRecurrence` was measured against simulation and its premise -- a closed
population with no mutation -- is false for the populations it is cited about.
But no definition in the corpus consumes `hetRecurrence` by name. The exposure
is in definitions that INLINE its closed form `(1 - 1/(2 Ne))^t` under names
that mention neither heterozygosity nor drift. A grep for the name finds none
of them, and reading docstrings finds only the ones that happen to say so --
and the whole problem is that they do not say so.

THE TECHNIQUE: LEVEL-SET INVARIANCE
-----------------------------------
Let R(p) be the suspect closed form. Pick two parameter points p1 != p2 with
R(p1) = R(p2) exactly. Any quantity that depends on p only through R must take
the same value at both. So:

    evaluate a definition along a level set of R;
    if it does not move, it is a function of R alone.

This finds definitions by what they compute, not by what they are called or
what they import. It is the mechanical form of the corpus's own observation
that every cross-check among the cluster holds at every value of the retention
factor, correct or not.

Two guards make the verdict mean something:

  NON-CONSTANCY. A definition that ignores its arguments entirely is trivially
  invariant along every level set. It is required to VARY across level sets
  before invariance within one counts, otherwise constants would be reported as
  members of every cluster.

  MULTIPLE LEVEL SETS. Invariance is required on several different values of R,
  not one. A single level set can be matched by coincidence, especially for
  definitions whose output saturates.

REUSE
-----
Add an entry to REFERENCES. Any closed form of two or more real parameters
works, provided one parameter can be solved for given the others and a target
value. This generalises to every falsified closed form in the corpus: state the
form, get the list of definitions computing it under other names.
"""

import json
import math
import sys

import corpus

api = corpus.api


# ---------------------------------------------------------------------------
# Suspect closed forms. Each entry gives the parameters, the form, and a solver
# that returns the value of the LAST parameter placing the point on a target
# level set. `aliases` lists argument names in the corpus that mean each
# parameter.
# ---------------------------------------------------------------------------
REFERENCES = {
    "drift_retention": {
        "doc": "(1 - 1/(2 Ne))^t -- the closed-population, no-mutation retention "
               "factor. Root of the heterozygosity cluster; measured against "
               "simulation in heavy/h0_heterozygosity_cluster.py, where the true "
               "retention at mutation-drift equilibrium is 1.0, not 0.135.",
        "params": ["Ne", "t"],
        "form": lambda Ne, t: (1.0 - 1.0 / (2.0 * Ne)) ** t,
        # t such that (1-1/(2Ne))^t == rho
        "solve_last": lambda Ne, rho: math.log(rho) / math.log(1.0 - 1.0 / (2.0 * Ne)),
        "aliases": {
            "Ne": ["Ne", "N", "N_e", "Ne_b", "Ne_stable", "N_b", "N_r", "Ne_source",
                   "Ne_target", "NeA", "NeB"],
            "t": ["t", "t_b", "t_r", "gens", "generations", "horizon", "t_div",
                  "t_since", "generations_since"],
        },
        "levels": [0.9, 0.6, 0.3, 0.1],
        "ne_values": [50.0, 200.0, 1000.0, 5000.0],
    },
}

# Filler values for arguments that are not part of the reference. Several, so a
# definition that is invariant only at one filler is not mistaken for a member.
FILLERS = [0.3, 0.7, 1.5]

RTOL = 1e-9


def _match(argnames, aliases):
    """Map reference parameters onto this definition's argument names."""
    out = {}
    for param, names in aliases.items():
        hit = next((a for a in argnames if a in names), None)
        if hit is None:
            return None
        out[param] = hit
    if len(set(out.values())) != len(out):
        return None
    return out


def _evaluate(fn, argnames, assignment):
    return fn(*[assignment[a] for a in argnames])


def scan(ref_name, ref):
    """Definitions that are functions of `ref` alone, on the arguments it names."""
    members, varying, skipped = [], 0, 0
    for fq in sorted(api.definition_table()):
        try:
            fn, argnames = api.callable_for(fq)
        except Exception:
            continue
        if api.vector_args(fq):
            continue
        m = _match(argnames, ref["aliases"])
        if m is None:
            continue
        ne_arg, t_arg = m["Ne"], m["t"]
        others = [a for a in argnames if a not in (ne_arg, t_arg)]

        ok_all = True
        moved_across = False
        detail = []
        for filler in FILLERS:
            base = {a: filler for a in others}
            per_level = []
            for rho in ref["levels"]:
                vals = []
                for ne in ref["ne_values"]:
                    try:
                        t = ref["solve_last"](ne, rho)
                    except Exception:
                        continue
                    asg = dict(base); asg[ne_arg] = ne; asg[t_arg] = t
                    try:
                        v = _evaluate(fn, argnames, asg)
                    except Exception:
                        v = None
                    if v is None or not isinstance(v, (int, float)) or not math.isfinite(v):
                        continue
                    vals.append(v)
                if len(vals) < 2:
                    continue
                spread = max(vals) - min(vals)
                scale = max(1.0, max(abs(v) for v in vals))
                invariant = spread <= RTOL * scale
                per_level.append((rho, vals[0], invariant))
                ok_all = ok_all and invariant
            if len(per_level) < 2:
                ok_all = False
                continue
            # must actually move between level sets, else it is a constant
            outs = [p[1] for p in per_level]
            if max(outs) - min(outs) > RTOL * max(1.0, max(abs(o) for o in outs)):
                moved_across = True
            detail.append({"filler": filler,
                           "levels": [{"rho": r, "value": v, "invariant": i}
                                      for r, v, i in per_level]})

        if not detail:
            skipped += 1
            continue
        if ok_all and moved_across:
            d = api.definition(fq)
            members.append({
                "definition": fq,
                "source": f"{d['file']}:{d['line']}",
                "args": argnames,
                "mapped": m,
                "empirical_status": d.get("empirical_status"),
                "detail": detail[0],
            })
        elif moved_across:
            varying += 1
    return members, varying, skipped


if __name__ == "__main__":
    report = {}
    for name, ref in REFERENCES.items():
        members, varying, skipped = scan(name, ref)
        report[name] = {
            "reference": ref["doc"],
            "form": "(1 - 1/(2 Ne))^t",
            "n_members": len(members),
            "members": members,
            "n_arg_compatible_but_not_members": varying,
            "n_skipped": skipped,
        }
        print(f"REFERENCE {name}: {ref['form'].__doc__ or ''}")
        print(f"  {ref['doc']}\n")
        print(f"  {len(members)} definitions are functions of this form ALONE:")
        for m in members:
            print(f"    {m['definition']:<52} {m['source']}")
            print(f"        args={m['args']}  status={m['empirical_status']}")
        print(f"\n  {varying} definitions take compatible arguments but are NOT "
              f"functions of it (correctly excluded)")
    json.dump(report, open("inlined.json", "w"), indent=1)
    print("\n-> inlined.json")
