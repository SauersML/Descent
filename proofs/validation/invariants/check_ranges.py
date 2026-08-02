"""FAMILY 1 -- range escapes.

For every definition whose NAME forces a range (a probability in [0,1], a
correlation in [-1,1], a variance nonnegative, ...), search its admissible box
for a point where the transcribed Lean body leaves that range.

Three verdicts, and the difference between them is the whole value of the file:

  ESCAPE       a concrete input point is exhibited.  This is a positive
               finding and it is exact -- the point is printed and can be
               pasted into Lean.
  PROVED       interval branch-and-bound covered the entire box with the
               result inside the range.  A proof, not a sample.
  INCONCLUSIVE the search found nothing and the interval proof did not close.
               NOT a pass.  Sampling misses thin escapes.

Run:  python check_ranges.py  ->  results_ranges.json
"""
from __future__ import annotations

import json
import math
import pathlib
import sys

import backends
import compile_defs as C
from backends import FLOAT, INTERVAL, Iv
from search import maximize, prove_contained
from semantics import admissible_box, required_range

HERE = pathlib.Path(__file__).resolve().parent
INF = math.inf


def _viol(v, lo, hi):
    """Signed violation: positive means outside [lo, hi]."""
    return max(lo - v, v - hi)


def check_one(c, budget=8000, bnb=1500):
    d = c.d
    rng = required_range(d)
    if rng is None:
        return dict(verdict="no-range", reason="name and docstring commit the "
                    "definition to no particular range")
    lo, hi, why = rng
    box, unguarded = admissible_box(d)
    names = c.names
    if not names:
        val = c(FLOAT)
        return dict(verdict="escape" if _viol(val, lo, hi) > 0 else "proved",
                    range=[lo, hi], range_why=why, value=val, witness={})

    def f(*xs):
        return _viol(c(FLOAT, *xs), lo, hi)

    best, x = maximize(f, box, names, budget=budget)
    out = dict(range=[lo, hi], range_why=why,
               box={n: [box[n]["lo"], box[n]["hi"], box[n]["source"]] for n in names},
               unguarded=unguarded,
               box_provenance={n: box[n]["why"] for n in names})
    if best is not None and best > 1e-12 and x is not None:
        val = c(FLOAT, *x)
        # An escape that needs a coordinate whose meaning we could not read is
        # a WEAKER claim than one reachable inside a box every coordinate of
        # which is pinned by a theorem or by an unambiguous parameter name.
        # The two are reported as different verdicts and never pooled.
        blind = [n for n in names if box[n]["source"] == "none"]
        out.update(verdict="escape-unguarded" if blind else "escape",
                   witness={n: v for n, v in zip(names, x)},
                   value=val, overshoot=best,
                   blind_coordinates=blind,
                   side="above" if val > hi else "below")
        return out

    def fiv(*xs):
        return c(INTERVAL, *xs)

    status, worst, used = prove_contained(fiv, box, names, lo, hi, max_boxes=bnb)
    out.update(verdict="proved" if status == "proved" else "inconclusive",
               bnb_boxes=used,
               searched=budget)
    if status != "proved":
        out["inconclusive_reason"] = (
            "no escape found by sampling+pattern search, and interval "
            f"branch-and-bound did not close the box within {bnb} subdivisions"
        )
    return out


def severity(r):
    """Rank escapes.  Ordering criteria, most important first.

    1. an escape reachable with EVERY coordinate unguarded outranks one that
       needs a coordinate the author explicitly bounded;
    2. sign errors (a probability going negative, a variance going negative)
       outrank magnitude errors;
    3. larger relative overshoot outranks smaller.
    """
    if r.get("verdict") not in ("escape", "escape-unguarded"):
        return -1.0
    lo, hi = r["range"]
    span = (hi - lo) if math.isfinite(hi - lo) else 1.0
    over = r.get("overshoot", 0.0)
    rel = min(over / span, 1e6) if span > 0 else over
    s = math.log10(1 + max(rel, 0.0)) * 10
    if r.get("side") == "below" and lo == 0.0:
        s += 30  # a nonnegative quantity going negative is a sign error
    if r.get("side") == "above" and hi == 1.0:
        s += 20  # a probability exceeding one
    if r["verdict"] == "escape-unguarded":
        # discount: the witness uses a coordinate whose admissible values we
        # could not determine, so the escape may not be physically reachable.
        s -= 25
    return s


def main(argv):
    cs, why_not, _ = C.compile_all()
    results = {}
    for k in sorted(cs):
        try:
            r = check_one(cs[k])
        except Exception as e:  # never let one definition abort the sweep
            r = dict(verdict="error", reason=f"{type(e).__name__}: {e}")
        r.update(name=cs[k].d["name"], module=cs[k].d["module"],
                 line=cs[k].d["line"], family="range", py=cs[k].py)
        r["severity"] = severity(r)
        results[k] = r
    for k, w in why_not.items():
        results.setdefault(k, dict(verdict="not-transpiled", reason=w,
                                   family="range", severity=-1.0))
    out = HERE / "results_ranges.json"
    out.write_text(json.dumps(results, indent=1, default=str))

    tally = {}
    for r in results.values():
        tally[r["verdict"]] = tally.get(r["verdict"], 0) + 1
    print(f"{len(results)} definitions ->", out)
    for v, n in sorted(tally.items(), key=lambda kv: -kv[1]):
        print(f"  {n:5d}  {v}")
    esc = sorted((r for r in results.values()
                  if r["verdict"] in ("escape", "escape-unguarded")),
                 key=lambda r: -r["severity"])
    print(f"\nTop escapes ({len(esc)} total):")
    for r in esc[:25]:
        w = ", ".join(f"{k}={v:.6g}" for k, v in r["witness"].items())
        tag = "!" if r["verdict"] == "escape" else "?"
        print(f"  {tag}[{r['severity']:5.1f}] {r['module']}.{r['name']}:{r['line']}"
              f"  -> {r['value']:.6g} outside [{r['range'][0]}, {r['range'][1]}]"
              f"   at {w}")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
